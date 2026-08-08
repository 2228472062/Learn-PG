/*-------------------------------------------------------------------------
 *
 * freelist.c
 *	  routines for managing the buffer pool's replacement strategy.
 *
 * 【模块总览(中文)】
 * 本文件实现了共享缓冲池的"替换策略"(replacement strategy),即:
 * 当需要把新的磁盘页调入共享缓冲池、而池中已没有空闲缓冲区时,应该
 * 踢掉哪个旧页。这是数据库缓存管理最核心的决策之一。
 *
 * 包含两套互补的机制:
 * 1) 全局时钟扫描算法(Clock Sweep):所有后端共享一个"时钟指针"
 *    (nextVictimBuffer),循环扫描缓冲区数组,挑选引用计数为 0 且使用
 *    次数(usage_count)最小的缓冲区作为牺牲者。这是近似 LRU、但实现
 *    开销极小的经典方案,详见 README 的 "Normal Buffer Replacement
 *    Strategy" 一节。
 * 2) 每后端私有的"缓冲环"(buffer ring):当某个操作(顺序扫描、VACUUM、
 *    COPY 大批量写入)只需要一次性使用大量页面时,分配一个小缓冲环
 *    (BufferAccessStrategy)只在这些缓冲区中循环复用,避免把整个缓冲池
 *    冲垮、也不去抢占其他查询常用的页面。
 *
 * 并发设计要点:
 * - 全局扫描状态由自旋锁 buffer_strategy_lock + 原子变量保护;
 * - 缓冲环对象是本进程 palloc 出来的私有内存,完全不需要加锁;
 * - 挑选牺牲者使用 CAS(compare-and-swap)循环直接修改缓冲区头的 state
 *   字段(把 refcount 加 1 完成"pin"),避免对缓冲区头加锁。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/buffer/freelist.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "pgstat.h"
#include "port/atomics.h"
#include "storage/buf_internals.h"
#include "storage/bufmgr.h"
#include "storage/proc.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"

#define INT_ACCESS_ONCE(var)	((int)(*((volatile int *)&(var))))


/*
 * The shared freelist control information.
 */
/* 共享的替换策略控制结构(BufferStrategyControl):
 * 位于共享内存,所有后端进程共用,由 buffer_strategy_lock 自旋锁保护
 * (原子变量除外)。
 *
 * 字段含义:
 * - buffer_strategy_lock : 保护下面各字段的自旋锁(原子变量本身不需要它,
 *   但"两个普通字段的一致性读取/写入"需要它,见 ClockSweepTick /
 *   StrategySyncStart 的用法);
 * - nextVictimBuffer     : 时钟扫描指针。注意它存储的是"累计扫描计数"
 *   (只增不减),要取实际缓冲区下标必须模 NBuffers。用原子 fetch_add
 *   递增,多个进程可并发推进,只是可能使返回顺序略有偏差。
 * - completePasses       : 时钟指针完整绕圈次数(相当于 nextVictimBuffer
 *   的高位);与 nextVictimBuffer 组合可给出全局扫描进度,供后台写进程
 *   (bgwriter)决定从何处开始同步写出;
 * - numBufferAllocs      : 自上次读取以来分配的缓冲区数量,后台写进程用它
 *   估算缓冲池消耗速率,决定是否唤醒/休眠;
 * - bgwprocno            : 需要被唤醒的 bgwriter 的进程号(PGPROC 数组下标),
 *   没有则为 -1。后端发现缓冲紧张时可置位,让 StrategyGetBuffer 顺手
 *   唤醒 bgwriter,把脏页写出腾出空间。 */
typedef struct
{
	/* Spinlock: protects the values below */
	slock_t		buffer_strategy_lock;

	/*
	 * clock-sweep hand: index of next buffer to consider grabbing. Note that
	 * this isn't a concrete buffer - we only ever increase the value. So, to
	 * get an actual buffer, it needs to be used modulo NBuffers.
	 */
	pg_atomic_uint32 nextVictimBuffer;

	/*
	 * Statistics.  These counters should be wide enough that they can't
	 * overflow during a single bgwriter cycle.
	 */
	uint32		completePasses; /* Complete cycles of the clock-sweep */
	pg_atomic_uint32 numBufferAllocs;	/* Buffers allocated since last reset */

	/*
	 * Bgworker process to be notified upon activity or -1 if none. See
	 * StrategyNotifyBgWriter.
	 */
	int			bgwprocno;
} BufferStrategyControl;

/* Pointers to shared state */
/* 指向共享内存中上述控制结构的指针,启动阶段由 StrategyCtlShmemInit 初始化 */
static BufferStrategyControl *StrategyControl = NULL;

static void StrategyCtlShmemRequest(void *arg);
static void StrategyCtlShmemInit(void *arg);

/* 向共享内存子系统注册 request/init 回调:request 阶段声明需要 sizeof
 * (BufferStrategyControl) 字节;init 阶段对该结构做初始清零/置初值。 */
const ShmemCallbacks StrategyCtlShmemCallbacks = {
	.request_fn = StrategyCtlShmemRequest,
	.init_fn = StrategyCtlShmemInit,
};

/*
 * Private (non-shared) state for managing a ring of shared buffers to re-use.
 * This is currently the only kind of BufferAccessStrategy object, but someday
 * we might have more kinds.
 */
/* 缓冲环(BufferAccessStrategy)数据结构 —— 后端进程私有,不进共享内存:
 * 用于"一次性使用大量页面"的场景(顺序扫描 / VACUUM / 大批量写入),
 * 只在环内循环复用少量缓冲区,避免污染整个缓冲池。
 *
 * 字段含义:
 * - btype    : 策略类型(BAS_BULKREAD / BAS_BULKWRITE / BAS_VACUUM),
 *              决定了环的大小与脏页处理方式;
 * - nbuffers : 环内缓冲区槽位数;
 * - current  : 最近一次 GetBufferFromRing 返回的槽位下标(环是循环的);
 * - buffers[]: 环内各槽位存放的缓冲区编号(Buffer,1 基);值为
 *              InvalidBuffer(即 0)表示该槽还没填过(首次分配时,
 *              先走正常时钟算法拿到缓冲区,再通过 AddBufferToRing 填入)。
 *
 * 【设计思想】整个对象用一次 palloc0 分配:固定字段 + 紧随其后的
 * buffers 柔性数组一次成型,简单且不产生碎片。
 *
 * Private (non-shared) state for managing a ring of shared buffers to re-use.
 * This is currently the only kind of BufferAccessStrategy object, but someday
 * we might have more kinds.
 */
typedef struct BufferAccessStrategyData
{
	/* Overall strategy type */
	BufferAccessStrategyType btype;
	/* Number of elements in buffers[] array */
	int			nbuffers;

	/*
	 * Index of the "current" slot in the ring, ie, the one most recently
	 * returned by GetBufferFromRing.
	 */
	int			current;

	/*
	 * Array of buffer numbers.  InvalidBuffer (that is, zero) indicates we
	 * have not yet selected a buffer for this ring slot.  For allocation
	 * simplicity this is palloc'd together with the fixed fields of the
	 * struct.
	 */
	Buffer		buffers[FLEXIBLE_ARRAY_MEMBER];
}			BufferAccessStrategyData;


/* Prototypes for internal functions */
static BufferDesc *GetBufferFromRing(BufferAccessStrategy strategy,
									 uint64 *buf_state);
static void AddBufferToRing(BufferAccessStrategy strategy,
							BufferDesc *buf);

/*
 * ClockSweepTick - Helper routine for StrategyGetBuffer()
 *
 * Move the clock hand one buffer ahead of its current position and return the
 * id of the buffer now under the hand.
 */
/*
 * ClockSweepTick - (中文)时钟扫描:把"时钟指针"向前拨一格,返回指针所指的缓冲区下标
 *
 * 【作用】时钟扫描算法的核心推进动作。把全局共享的 nextVictimBuffer 计数
 * 原子地加 1,返回"指针新指向的缓冲区编号"。
 *
 * 【设计思想】nextVictimBuffer 不是"下标"而是"累计扫描次数"(只增不减),
 * 取实际缓冲区用 victim % NBuffers 折算:
 * - 多个后端可以并发地用 pg_atomic_fetch_add 推进指针,互不阻塞,代价是
 *   返回的缓冲区顺序可能略有交错,但这不影响正确性;
 * - 把"绕圈"次数完整保存在 completePasses(在自旋锁保护下递增),这样
 *   StrategySyncStart() 能一次性读出"指针位置 + 绕圈次数"的一致快照,
 *   供 bgwriter 决定从哪儿开始写脏页。
 *
 * 实现细节:当某个进程的递增把计数从 N 推过 N+1 造成"回绕"时,由它负责
 * 在持自旋锁的情况下通过 CAS 把 nextVictimBuffer 折回 [0, NBuffers) 并
 * 递增 completePasses。折回必须与 completePasses 的递增在锁内原子完成,
 * 否则读方会看到指针与绕圈数不一致。极端情况下此循环会自旋,但概率极低。
 *
 * 【参数】无。
 * 【返回值】时钟指针新指向的缓冲区编号(已模 NBuffers)。
 */
static inline uint32
ClockSweepTick(void)
{
	uint32		victim;

	/*
	 * Atomically move hand ahead one buffer - if there's several processes
	 * doing this, this can lead to buffers being returned slightly out of
	 * apparent order.
	 */
	victim =
		pg_atomic_fetch_add_u32(&StrategyControl->nextVictimBuffer, 1);

	if (victim >= NBuffers)
	{
		uint32		originalVictim = victim;

		/* always wrap what we look up in BufferDescriptors */
		victim = victim % NBuffers;

		/*
		 * If we're the one that just caused a wraparound, force
		 * completePasses to be incremented while holding the spinlock. We
		 * need the spinlock so StrategySyncStart() can return a consistent
		 * value consisting of nextVictimBuffer and completePasses.
		 */
		if (victim == 0)
		{
			uint32		expected;
			uint32		wrapped;
			bool		success = false;

			expected = originalVictim + 1;

			while (!success)
			{
				/*
				 * Acquire the spinlock while increasing completePasses. That
				 * allows other readers to read nextVictimBuffer and
				 * completePasses in a consistent manner which is required for
				 * StrategySyncStart().  In theory delaying the increment
				 * could lead to an overflow of nextVictimBuffers, but that's
				 * highly unlikely and wouldn't be particularly harmful.
				 */
				SpinLockAcquire(&StrategyControl->buffer_strategy_lock);

				wrapped = expected % NBuffers;

				success = pg_atomic_compare_exchange_u32(&StrategyControl->nextVictimBuffer,
														 &expected, wrapped);
				if (success)
					StrategyControl->completePasses++;
				SpinLockRelease(&StrategyControl->buffer_strategy_lock);
			}
		}
	}
	return victim;
}

/*
 * StrategyGetBuffer
 *
 *	Called by the bufmgr to get the next candidate buffer to use in
 *	GetVictimBuffer(). The only hard requirement GetVictimBuffer() has is that
 *	the selected buffer must not currently be pinned by anyone.
 *
 *	strategy is a BufferAccessStrategy object, or NULL for default strategy.
 *
 *	It is the callers responsibility to ensure the buffer ownership can be
 *	tracked via TrackNewBufferPin().
 *
 *	The buffer is pinned and marked as owned, using TrackNewBufferPin(),
 *	before returning.
 */
/*
 * StrategyGetBuffer
 *      (中文)为缓冲管理器挑选一个可用的牺牲缓冲区(全局时钟扫描 + 缓冲环)
 *
 * 【作用】被 bufmgr 的 GetVictimBuffer() 调用,返回一个"没人 pin、可以
 * 直接占用"的缓冲区。返回时该缓冲区已被本进程 pin(引用计数 +1)并登记
 * 到资源所有者(resource owner,通过 TrackNewBufferPin),确保后续出错
 * 回滚时能被自动释放,不会泄漏 pin。
 *
 * 【执行流程】
 * 1. 若给了 strategy(缓冲环)且环中有可用缓冲区,直接复用环里的(不走
 *    全局算法,不计数,不唤醒 bgwriter);
 * 2. 读取 bgwprocno,若需要唤醒 bgwriter(说明缓冲池紧张),先把它置为
 *    -1 再 SetLatch 唤醒(先清零再唤醒的顺序避免"唤醒后立刻又被设置
 *    通知、漏掉唤醒");
 * 3. 原子累加 numBufferAllocs,供 bgwriter 估算缓冲消耗速率;
 * 4. 时钟扫描主循环:ClockSweepTick() 拨指针,检查指针所指缓冲区:
 *    - 已被 pin(引用计数 != 0):换下一个;若扫满一整圈仍无收获,说明
 *      所有缓冲区都被 pin,直接报错(继续空转可能死循环,不如快速失败);
 *    - 有使用计数 usage_count:把 usage_count 减 1(给它一次"缓刑",
 *      这是时钟算法近似 LRU 的关键——被多次使用的页更值得留在内存),
 *      重置 trycounter 后换下一个;
 *    - 空闲:用 CAS 把 refcount 从 0 改成 1 完成 pin(不锁缓冲区头),
 *      若 CAS 失败说明并发竞争,重读 state 再来。
 *
 * 【设计思想】整个循环不使用任何系统级锁(只用自旋锁级原子操作 + 缓冲区
 * 头 CAS),使"挑选牺牲者"这条热路径可被所有后端高度并发地执行。环的复用
 * 完全绕过全局状态,进一步避免争用。
 *
 * 【参数】
 *   strategy  —— 缓冲环策略对象;NULL 表示默认策略(纯时钟扫描);
 *   buf_state —— 输出参数,返回被选中缓冲区的 state 字段新值
 *                (已含 refcount+1),供调用者直接使用,省去重读;
 *   from_ring —— 输出参数,true 表示选中的缓冲区来自缓冲环。
 * 【返回值】选中的缓冲区描述符指针。
 */
BufferDesc *
StrategyGetBuffer(BufferAccessStrategy strategy, uint64 *buf_state, bool *from_ring)
{
	BufferDesc *buf;
	int			bgwprocno;
	int			trycounter;

	*from_ring = false;

	/*
	 * If given a strategy object, see whether it can select a buffer. We
	 * assume strategy objects don't need buffer_strategy_lock.
	 */
	if (strategy != NULL)
	{
		buf = GetBufferFromRing(strategy, buf_state);
		if (buf != NULL)
		{
			*from_ring = true;
			return buf;
		}
	}

	/*
	 * If asked, we need to waken the bgwriter. Since we don't want to rely on
	 * a spinlock for this we force a read from shared memory once, and then
	 * set the latch based on that value. We need to go through that length
	 * because otherwise bgwprocno might be reset while/after we check because
	 * the compiler might just reread from memory.
	 *
	 * This can possibly set the latch of the wrong process if the bgwriter
	 * dies in the wrong moment. But since PGPROC->procLatch is never
	 * deallocated the worst consequence of that is that we set the latch of
	 * some arbitrary process.
	 */
	bgwprocno = INT_ACCESS_ONCE(StrategyControl->bgwprocno);
	if (bgwprocno != -1)
	{
		/* reset bgwprocno first, before setting the latch */
		StrategyControl->bgwprocno = -1;

		/*
		 * Not acquiring ProcArrayLock here which is slightly icky. It's
		 * actually fine because procLatch isn't ever freed, so we just can
		 * potentially set the wrong process' (or no process') latch.
		 */
		SetLatch(&GetPGProcByNumber(bgwprocno)->procLatch);
	}

	/*
	 * We count buffer allocation requests so that the bgwriter can estimate
	 * the rate of buffer consumption.  Note that buffers recycled by a
	 * strategy object are intentionally not counted here.
	 */
	pg_atomic_fetch_add_u32(&StrategyControl->numBufferAllocs, 1);

	/* Use the "clock sweep" algorithm to find a free buffer */
	trycounter = NBuffers;
	for (;;)
	{
		uint64		old_buf_state;
		uint64		local_buf_state;

		buf = GetBufferDescriptor(ClockSweepTick());

		/*
		 * Check whether the buffer can be used and pin it if so. Do this
		 * using a CAS loop, to avoid having to lock the buffer header.
		 */
		old_buf_state = pg_atomic_read_u64(&buf->state);
		for (;;)
		{
			local_buf_state = old_buf_state;

			/*
			 * If the buffer is pinned or has a nonzero usage_count, we cannot
			 * use it; decrement the usage_count (unless pinned) and keep
			 * scanning.
			 */

			if (BUF_STATE_GET_REFCOUNT(local_buf_state) != 0)
			{
				if (--trycounter == 0)
				{
					/*
					 * We've scanned all the buffers without making any state
					 * changes, so all the buffers are pinned (or were when we
					 * looked at them). We could hope that someone will free
					 * one eventually, but it's probably better to fail than
					 * to risk getting stuck in an infinite loop.
					 */
					elog(ERROR, "no unpinned buffers available");
				}
				break;
			}

			/* See equivalent code in PinBuffer() */
			if (unlikely(local_buf_state & BM_LOCKED))
			{
				old_buf_state = WaitBufHdrUnlocked(buf);
				continue;
			}

			if (BUF_STATE_GET_USAGECOUNT(local_buf_state) != 0)
			{
				local_buf_state -= BUF_USAGECOUNT_ONE;

				if (pg_atomic_compare_exchange_u64(&buf->state, &old_buf_state,
												   local_buf_state))
				{
					trycounter = NBuffers;
					break;
				}
			}
			else
			{
				/* pin the buffer if the CAS succeeds */
				local_buf_state += BUF_REFCOUNT_ONE;

				if (pg_atomic_compare_exchange_u64(&buf->state, &old_buf_state,
												   local_buf_state))
				{
					/* Found a usable buffer */
					if (strategy != NULL)
						AddBufferToRing(strategy, buf);
					*buf_state = local_buf_state;

					TrackNewBufferPin(BufferDescriptorGetBuffer(buf));

					return buf;
				}
			}
		}
	}
}

/*
 * StrategySyncStart -- tell BgBufferSync where to start syncing
 *
 * The result is the buffer index of the best buffer to sync first.
 * BgBufferSync() will proceed circularly around the buffer array from there.
 *
 * In addition, we return the completed-pass count (which is effectively
 * the higher-order bits of nextVictimBuffer) and the count of recent buffer
 * allocs if non-NULL pointers are passed.  The alloc count is reset after
 * being read.
 */
/*
 * StrategySyncStart
 *      (中文)告诉后台写进程(bgwriter)应从哪个缓冲区开始同步写出
 *
 * 【作用】bgwriter 循环调度时调用,取得一个一致快照:
 *   1) 返回"时钟指针当前所指缓冲区下标"——bgwriter 从那里开始,循环向后
 *      扫描脏页写出(指针本身不动,仍由时钟算法单独推进);
 *   2) 通过输出参数返回两个统计值:
 *      - complete_passes:指针完整绕圈次数。注意要把 nextVictimBuffer /
 *        NBuffers(即"已回绕但 completePasses 还没来得及递增"的部分)也
 *        加上,与 ClockSweepTick 的延迟递增逻辑严格对应,否则统计会偏小;
 *      - num_buf_alloc:自上次读取以来分配(占用)的缓冲区总数,读取后清零,
 *        供 bgwriter 估算缓冲池消耗速率,决定下轮休眠多久。
 *
 * 【并发设计】在自旋锁内一次读出全部字段,保证三者相互一致
 * (clock-sweep 的推进者也在同一把锁下修改,见 ClockSweepTick)。
 *
 * 【参数】
 *   complete_passes —— 输出参数(可空):时钟扫描绕圈次数;
 *   num_buf_alloc   —— 输出参数(可空):近期的缓冲区分配数,读后清零。
 * 【返回值】推荐 bgwriter 开始同步写出的缓冲区下标(0 ~ NBuffers-1)。
 */
int
StrategySyncStart(uint32 *complete_passes, uint32 *num_buf_alloc)
{
	uint32		nextVictimBuffer;
	int			result;

	SpinLockAcquire(&StrategyControl->buffer_strategy_lock);
	nextVictimBuffer = pg_atomic_read_u32(&StrategyControl->nextVictimBuffer);
	result = nextVictimBuffer % NBuffers;

	if (complete_passes)
	{
		*complete_passes = StrategyControl->completePasses;

		/*
		 * Additionally add the number of wraparounds that happened before
		 * completePasses could be incremented. C.f. ClockSweepTick().
		 */
		*complete_passes += nextVictimBuffer / NBuffers;
	}

	if (num_buf_alloc)
	{
		*num_buf_alloc = pg_atomic_exchange_u32(&StrategyControl->numBufferAllocs, 0);
	}
	SpinLockRelease(&StrategyControl->buffer_strategy_lock);
	return result;
}

/*
 * StrategyNotifyBgWriter -- set or clear allocation notification latch
 *
 * If bgwprocno isn't -1, the next invocation of StrategyGetBuffer will
 * set that latch.  Pass -1 to clear the pending notification before it
 * happens.  This feature is used by the bgwriter process to wake itself up
 * from hibernation, and is not meant for anybody else to use.
 */
/*
 * StrategyNotifyBgWriter
 *      (中文)设置/清除"分配通知":让下一次 StrategyGetBuffer 唤醒 bgwriter
 *
 * 【作用】后台写进程休眠前调用 StrategyNotifyBgWriter(自身进程号)登记
 * 自己;此后只要有后端申请缓冲区,StrategyGetBuffer 就会顺手给它 SetLatch,
 * 把它从休眠中唤醒去写脏页。传 -1 则撤销该登记(例如 bgwriter 即将退出)。
 *
 * 【背景】bgwriter 平时处于休眠状态(靠惰性定时唤醒),但若缓冲池压力大,
 * 每次分配都等它睡醒再写就太慢了;此机制让"有分配发生"这个信号能及时
 * 传到 bgwriter,实现按需唤醒。
 *
 * 【设计思想】此函数只在自旋锁保护下写入一个 int,保证 StrategyGetBuffer
 * 读到的值不会撕裂;bgwriter 调用频率很低,这点锁开销无足轻重。
 *
 * 【参数】bgwprocno —— PGPROC 数组下标(即要唤醒的进程);-1 表示清除通知。
 * 【返回值】无。
 */
void
StrategyNotifyBgWriter(int bgwprocno)
{
	/*
	 * We acquire buffer_strategy_lock just to ensure that the store appears
	 * atomic to StrategyGetBuffer.  The bgwriter should call this rather
	 * infrequently, so there's no performance penalty from being safe.
	 */
	SpinLockAcquire(&StrategyControl->buffer_strategy_lock);
	StrategyControl->bgwprocno = bgwprocno;
	SpinLockRelease(&StrategyControl->buffer_strategy_lock);
}


/*
 * StrategyCtlShmemRequest -- request shared memory for the buffer
 *		cache replacement strategy.
 */
/* (中文)申请共享内存,存放 BufferStrategyControl 替换策略控制结构。
 * 见 StrategyCtlShmemCallbacks 的注册说明:request 阶段只声明需要多大
 * 空间、把分配好的指针写入全局变量 StrategyControl。 */
static void
StrategyCtlShmemRequest(void *arg)
{
	ShmemRequestStruct(.name = "Buffer Strategy Status",
					   .size = sizeof(BufferStrategyControl),
					   .ptr = (void **) &StrategyControl
		);
}

/*
 * StrategyCtlShmemInit -- initialize the buffer cache replacement strategy.
 */
/* (中文)初始化替换策略控制结构(共享内存分配完成后的 init 阶段调用):
 * 初始化自旋锁;时钟指针清零;统计计数清零;通知进程号置为 -1(无通知)。
 * 【设计思想】init 与 request 分离,使共享内存子系统能先统计总需求、
 * 再一次性分配,之后各子系统对自己的区域做初始化。 */
static void
StrategyCtlShmemInit(void *arg)
{
	SpinLockInit(&StrategyControl->buffer_strategy_lock);

	/* Initialize the clock-sweep pointer */
	pg_atomic_init_u32(&StrategyControl->nextVictimBuffer, 0);

	/* Clear statistics */
	StrategyControl->completePasses = 0;
	pg_atomic_init_u32(&StrategyControl->numBufferAllocs, 0);

	/* No pending notification */
	StrategyControl->bgwprocno = -1;
}


/* ----------------------------------------------------------------
 *				Backend-private buffer ring management
 * ----------------------------------------------------------------
 */


/*
 * GetAccessStrategy -- create a BufferAccessStrategy object
 *
 * The object is allocated in the current memory context.
 */
/*
 * GetAccessStrategy
 *      (中文)按策略类型创建缓冲环对象(自动选定合适的环大小)
 *
 * 【作用】根据调用场景选择环大小并创建 BufferAccessStrategy 对象,
 * 供一次性大量读/写页面的操作(顺序扫描、VACUUM、COPY 等)复用。
 *
 * 【环大小选择的设计思想】(详见 buffer/README 的 Buffer Ring 一节)
 * - BAS_BULKREAD(顺序扫描等只读):默认 256KB(约 32 个 8KB 页)。
 *   理由:① 足够小,能装进 CPU L2 缓存,从 OS 缓存搬运页面到共享缓冲池
 *   效率高;② 又要足够大,容纳扫描过程中同时被 pin 的所有页,否则自己的
 *   pin 会阻塞复用;③ 还要>= SYNC_SCAN_REPORT_INTERVAL,让"同步顺序扫描"
 *   协调器能追踪扫描进度。此外还要为 effective_io_concurrency 个并发
 *   AIO 预留空间(每个 IO 最大 io_combine_limit 块),最后被
 *   GetPinLimit()(即最多能同时 pin 的缓冲数)封顶;
 * - BAS_BULKWRITE(COPY IN、CREATE TABLE AS 等大批量写入):16MB。
 *   太小会导致频繁刷 WAL 而阻塞;后台 VACUUM 可以容忍自己刷 WAL 慢一点,
 *   但希望 COPY 这种前台操作不受影响;
 * - BAS_VACUUM:2MB。VACUUM 的环不丢脏页,而是必要时主动刷 WAL 以便
 *   复用环内缓冲区;
 * - BAS_NORMAL:返回 NULL 表示"用默认全局策略即可",调用方按无策略处理。
 *
 * 【参数】btype —— 环的策略类型(见 enum BufferAccessStrategyType)。
 * 【返回值】环对象指针;BAS_NORMAL 时返回 NULL。
 * 注意:对象分配在当前内存上下文(palloc),随上下文释放而释放。
 */
BufferAccessStrategy
GetAccessStrategy(BufferAccessStrategyType btype)
{
	int			ring_size_kb;

	/*
	 * Select ring size to use.  See buffer/README for rationales.
	 *
	 * Note: if you change the ring size for BAS_BULKREAD, see also
	 * SYNC_SCAN_REPORT_INTERVAL in access/heap/syncscan.c.
	 */
	switch (btype)
	{
		case BAS_NORMAL:
			/* if someone asks for NORMAL, just give 'em a "default" object */
			return NULL;

		case BAS_BULKREAD:
			{
				int			ring_max_kb;

				/*
				 * The ring always needs to be large enough to allow some
				 * separation in time between providing a buffer to the user
				 * of the strategy and that buffer being reused. Otherwise the
				 * user's pin will prevent reuse of the buffer, even without
				 * concurrent activity.
				 *
				 * We also need to ensure the ring always is large enough for
				 * SYNC_SCAN_REPORT_INTERVAL, as noted above.
				 *
				 * Thus we start out a minimal size and increase the size
				 * further if appropriate.
				 */
				ring_size_kb = 256;

				/*
				 * There's no point in a larger ring if we won't be allowed to
				 * pin sufficiently many buffers.  But we never limit to less
				 * than the minimal size above.
				 */
				ring_max_kb = GetPinLimit() * (BLCKSZ / 1024);
				ring_max_kb = Max(ring_size_kb, ring_max_kb);

				/*
				 * We would like the ring to additionally have space for the
				 * configured degree of IO concurrency. While being read in,
				 * buffers can obviously not yet be reused.
				 *
				 * Each IO can be up to io_combine_limit blocks large, and we
				 * want to start up to effective_io_concurrency IOs.
				 *
				 * Note that effective_io_concurrency may be 0, which disables
				 * AIO.
				 */
				ring_size_kb += (BLCKSZ / 1024) *
					io_combine_limit * effective_io_concurrency;

				if (ring_size_kb > ring_max_kb)
					ring_size_kb = ring_max_kb;
				break;
			}
		case BAS_BULKWRITE:
			ring_size_kb = 16 * 1024;
			break;
		case BAS_VACUUM:
			ring_size_kb = 2048;
			break;

		default:
			elog(ERROR, "unrecognized buffer access strategy: %d",
				 (int) btype);
			return NULL;		/* keep compiler quiet */
	}

	return GetAccessStrategyWithSize(btype, ring_size_kb);
}

/*
 * GetAccessStrategyWithSize -- create a BufferAccessStrategy object with a
 *		number of buffers equivalent to the passed in size.
 *
 * If the given ring size is 0, no BufferAccessStrategy will be created and
 * the function will return NULL.  ring_size_kb must not be negative.
 */
/*
 * GetAccessStrategyWithSize
 *      (中文)按给定大小(KB)创建缓冲环对象
 *
 * 【作用】把 ring_size_kb 折算成缓冲区个数,创建对应大小的缓冲环。
 * 这是 GetAccessStrategy 的底层实现,也允许其他调用者(如资源管理代码)
 * 按自定义大小建环。
 *
 * 【规则】
 * - ring_size_kb 为 0:表示"不限制",返回 NULL(无需环,用全局策略);
 * - 上限封顶为 NBuffers/8(即环最多占 1/8 缓冲池),防止环把整个缓冲池
 *   圈走,影响其他查询;
 * - 对象用一次 palloc0 分配"固定字段 + buffers[] 柔性数组",所有槽位
 *   初始为 0(即 InvalidBuffer,表示槽未填充)。
 *
 * 【参数】btype —— 策略类型;ring_size_kb —— 环的大小(千字节,必须>=0)。
 * 【返回值】环对象指针;size 为 0 或折算后为 0 时返回 NULL。
 */
BufferAccessStrategy
GetAccessStrategyWithSize(BufferAccessStrategyType btype, int ring_size_kb)
{
	int			ring_buffers;
	BufferAccessStrategy strategy;

	Assert(ring_size_kb >= 0);

	/* Figure out how many buffers ring_size_kb is */
	ring_buffers = ring_size_kb / (BLCKSZ / 1024);

	/* 0 means unlimited, so no BufferAccessStrategy required */
	if (ring_buffers == 0)
		return NULL;

	/* Cap to 1/8th of shared_buffers */
	ring_buffers = Min(NBuffers / 8, ring_buffers);

	/* NBuffers should never be less than 16, so this shouldn't happen */
	Assert(ring_buffers > 0);

	/* Allocate the object and initialize all elements to zeroes */
	strategy = (BufferAccessStrategy)
		palloc0(offsetof(BufferAccessStrategyData, buffers) +
				ring_buffers * sizeof(Buffer));

	/* Set fields that don't start out zero */
	strategy->btype = btype;
	strategy->nbuffers = ring_buffers;

	return strategy;
}

/*
 * GetAccessStrategyBufferCount -- an accessor for the number of buffers in
 *		the ring
 *
 * Returns 0 on NULL input to match behavior of GetAccessStrategyWithSize()
 * returning NULL with 0 size.
 */
/* (中文)读取缓冲环中的缓冲区槽位数;传入 NULL 时返回 0,
 * 与 GetAccessStrategyWithSize 在 size 为 0 时返回 NULL 的语义保持一致。 */
int
GetAccessStrategyBufferCount(BufferAccessStrategy strategy)
{
	if (strategy == NULL)
		return 0;

	return strategy->nbuffers;
}

/*
 * GetAccessStrategyPinLimit -- get cap of number of buffers that should be pinned
 *
 * When pinning extra buffers to look ahead, users of a ring-based strategy are
 * in danger of pinning too much of the ring at once while performing look-ahead.
 * For some strategies, that means "escaping" from the ring, and in others it
 * means forcing dirty data to disk very frequently with associated WAL
 * flushing.  Since external code has no insight into any of that, allow
 * individual strategy types to expose a clamp that should be applied when
 * deciding on a maximum number of buffers to pin at once.
 *
 * Callers should combine this number with other relevant limits and take the
 * minimum.
 */
/*
 * GetAccessStrategyPinLimit
 *      (中文)获取"同时最多可 pin 的缓冲区数"上限建议
 *
 * 【作用】使用缓冲环做预读(look-ahead)的调用方,可能一次性 pin 太多
 * 环内缓冲区:
 * - 对某些策略,这会"逃出"环(被迫使用环外缓冲区,环形同虚设);
 * - 对另一些策略,则会让脏页太频繁落盘、连带频繁刷 WAL。
 * 本函数按策略类型给出一个建议上限,调用方应把该值与自己的其他限制
 * 取最小值使用。
 *
 * 【规则】
 * - 无环(NULL):不限(返回 NBuffers);
 * - BAS_BULKREAD:允许 pin 整个环。因为脏页会被 StrategyRejectBuffer 丢出
 *   环,不存在刷 WAL 问题;
 * - 其他类型:最多 pin 环的一半——在"预读距离"与"推迟写回、减少 WAL
 *   流量"之间取平衡。
 *
 * 【参数】strategy —— 环对象(可空)。
 * 【返回值】建议的 pin 上限(缓冲区个数)。
 */
int
GetAccessStrategyPinLimit(BufferAccessStrategy strategy)
{
	if (strategy == NULL)
		return NBuffers;

	switch (strategy->btype)
	{
		case BAS_BULKREAD:

			/*
			 * Since BAS_BULKREAD uses StrategyRejectBuffer(), dirty buffers
			 * shouldn't be a problem and the caller is free to pin up to the
			 * entire ring at once.
			 */
			return strategy->nbuffers;

		default:

			/*
			 * Tell caller not to pin more than half the buffers in the ring.
			 * This is a trade-off between look ahead distance and deferring
			 * writeback and associated WAL traffic.
			 */
			return strategy->nbuffers / 2;
	}
}

/*
 * FreeAccessStrategy -- release a BufferAccessStrategy object
 *
 * A simple pfree would do at the moment, but we would prefer that callers
 * don't assume that much about the representation of BufferAccessStrategy.
 */
/* (中文)释放缓冲环对象。当前实现就是 pfree,但对外封装一层,让调用方
 * 不必依赖对象的具体表示(未来若改为其他分配方式,调用方无需改动)。
 * 对 NULL(默认策略)安全,不会崩溃。 */
void
FreeAccessStrategy(BufferAccessStrategy strategy)
{
	/* don't crash if called on a "default" strategy */
	if (strategy != NULL)
		pfree(strategy);
}

/*
 * GetBufferFromRing -- returns a buffer from the ring, or NULL if the
 *		ring is empty / not usable.
 *
 * The buffer is pinned and marked as owned, using TrackNewBufferPin(), before
 * returning.
 */
/*
 * GetBufferFromRing
 *      (中文)从缓冲环中取出一个可用缓冲区
 *
 * 【作用】环策略的核心取缓冲逻辑:轮转推进环内槽位指针(current),
 * 尝试复用当前槽位里的缓冲区。
 *
 * 【执行细节】
 * - 槽位还是 InvalidBuffer(从未填充):返回 NULL,通知调用者走全局
 *   时钟算法拿新缓冲区,之后再 AddBufferToRing 把这个槽填上;
 * - 槽位里有缓冲区,但要满足两个条件才能复用:
 *   a) 当前没人 pin 它(refcount == 0);
 *   b) usage_count <= 1(期望正好是 1——上次我们自己用完后留下的;
 *      若 > 1,说明有其他进程也碰过它,应让出);
 * - 满足条件就用 CAS 把 refcount 0->1 完成 pin(不锁缓冲区头);
 *   不满足则返回 NULL,调用者会用新缓冲区替换该槽。
 *
 * 【并发说明】环对象是进程私有的,无锁;只有对共享缓冲区头 state 的
 * CAS 是跨进程的。
 *
 * 【参数】
 *   strategy  —— 环对象;
 *   buf_state —— 输出参数,返回 pin 后缓冲区 state 的新值。
 * 【返回值】可复用的缓冲区描述符(已 pin、已登记资源所有者);
 * 环为空或当前槽位不可用时返回 NULL。
 */
static BufferDesc *
GetBufferFromRing(BufferAccessStrategy strategy, uint64 *buf_state)
{
	BufferDesc *buf;
	Buffer		bufnum;
	uint64		old_buf_state;
	uint64		local_buf_state;	/* to avoid repeated (de-)referencing */


	/* Advance to next ring slot */
	if (++strategy->current >= strategy->nbuffers)
		strategy->current = 0;

	/*
	 * If the slot hasn't been filled yet, tell the caller to allocate a new
	 * buffer with the normal allocation strategy.  He will then fill this
	 * slot by calling AddBufferToRing with the new buffer.
	 */
	bufnum = strategy->buffers[strategy->current];
	if (bufnum == InvalidBuffer)
		return NULL;

	buf = GetBufferDescriptor(bufnum - 1);

	/*
	 * Check whether the buffer can be used and pin it if so. Do this using a
	 * CAS loop, to avoid having to lock the buffer header.
	 */
	old_buf_state = pg_atomic_read_u64(&buf->state);
	for (;;)
	{
		local_buf_state = old_buf_state;

		/*
		 * If the buffer is pinned we cannot use it under any circumstances.
		 *
		 * If usage_count is 0 or 1 then the buffer is fair game (we expect 1,
		 * since our own previous usage of the ring element would have left it
		 * there, but it might've been decremented by clock-sweep since then).
		 * A higher usage_count indicates someone else has touched the buffer,
		 * so we shouldn't re-use it.
		 */
		if (BUF_STATE_GET_REFCOUNT(local_buf_state) != 0
			|| BUF_STATE_GET_USAGECOUNT(local_buf_state) > 1)
			break;

		/* See equivalent code in PinBuffer() */
		if (unlikely(local_buf_state & BM_LOCKED))
		{
			old_buf_state = WaitBufHdrUnlocked(buf);
			continue;
		}

		/* pin the buffer if the CAS succeeds */
		local_buf_state += BUF_REFCOUNT_ONE;

		if (pg_atomic_compare_exchange_u64(&buf->state, &old_buf_state,
										   local_buf_state))
		{
			*buf_state = local_buf_state;

			TrackNewBufferPin(BufferDescriptorGetBuffer(buf));
			return buf;
		}
	}

	/*
	 * Tell caller to allocate a new buffer with the normal allocation
	 * strategy.  He'll then replace this ring element via AddBufferToRing.
	 */
	return NULL;
}

/*
 * AddBufferToRing -- add a buffer to the buffer ring
 *
 * Caller must hold the buffer header spinlock on the buffer.  Since this
 * is called with the spinlock held, it had better be quite cheap.
 */
/* (中文)把新分配的缓冲区登记进环的当前槽位,供以后复用。
 * 注意:调用时调用者正持有该缓冲区头的自旋锁,因此本函数必须极轻量
 * (只写一个数组元素),不能做任何可能阻塞或获取其他锁的操作。 */
static void
AddBufferToRing(BufferAccessStrategy strategy, BufferDesc *buf)
{
	strategy->buffers[strategy->current] = BufferDescriptorGetBuffer(buf);
}

/*
 * Utility function returning the IOContext of a given BufferAccessStrategy's
 * strategy ring.
 */
/* (中文)返回给定缓冲环策略对应的 IO 上下文(IOCONTEXT_NORMAL/BULKREAD/
 * BULKWRITE/VACUUM),用于把后续 I/O 计入 pgstat 中对应的统计类别
 * (例如批量读写分别记账,便于观察"一次大查询到底花了多少 I/O")。 */
IOContext
IOContextForStrategy(BufferAccessStrategy strategy)
{
	if (!strategy)
		return IOCONTEXT_NORMAL;

	switch (strategy->btype)
	{
		case BAS_NORMAL:

			/*
			 * Currently, GetAccessStrategy() returns NULL for
			 * BufferAccessStrategyType BAS_NORMAL, so this case is
			 * unreachable.
			 */
			pg_unreachable();
			return IOCONTEXT_NORMAL;
		case BAS_BULKREAD:
			return IOCONTEXT_BULKREAD;
		case BAS_BULKWRITE:
			return IOCONTEXT_BULKWRITE;
		case BAS_VACUUM:
			return IOCONTEXT_VACUUM;
	}

	elog(ERROR, "unrecognized BufferAccessStrategyType: %d", strategy->btype);
	pg_unreachable();
}

/*
 * StrategyRejectBuffer -- consider rejecting a dirty buffer
 *
 * When a nondefault strategy is used, the buffer manager calls this function
 * when it turns out that the buffer selected by StrategyGetBuffer needs to
 * be written out and doing so would require flushing WAL too.  This gives us
 * a chance to choose a different victim.
 *
 * Returns true if buffer manager should ask for a new victim, and false
 * if this buffer should be written and re-used.
 */
/*
 * StrategyRejectBuffer
 *      (中文)考虑拒绝一个脏缓冲区(选择其他牺牲者)
 *
 * 【作用】缓冲管理器在复用牺牲者之前发现它是脏的,且写它需要连带刷 WAL
 * (比如页的 LSN 超过了当前 WAL flush 位置,不刷 WAL 就重写该页,崩溃后
 * 恢复时会损坏),此时调用本函数,给环策略一个"换人"的机会。
 *
 * 【规则】仅 BAS_BULKREAD(批量读)策略启用该拒绝机制:因为批量读本意是
 * 尽量少写盘,若被迫频繁刷 WAL 就违背初衷。若脏页正是环当前槽位的缓冲区,
 * 就把该槽位清空(置 InvalidBuffer),返回 true 让缓冲管理器另选牺牲者;
 * 否则(非 bulkread、或来自全局算法)返回 false,照常写盘复用。
 *
 * 【为何要清空槽位】如果不清空,环里全是脏页时每次都会选中脏页,形成
 * 无限循环;清空后调用者会用干净页重新填充该槽。
 *
 * 【参数】strategy —— 环对象;buf —— 被选中的候选缓冲区;from_ring —— 该
 * 缓冲区是否来自环(非环内缓冲区不参与拒绝逻辑)。
 * 【返回值】true 表示"请重新挑一个牺牲者";false 表示"这个就写盘复用吧"。
 */
bool
StrategyRejectBuffer(BufferAccessStrategy strategy, BufferDesc *buf, bool from_ring)
{
	/* We only do this in bulkread mode */
	if (strategy->btype != BAS_BULKREAD)
		return false;

	/* Don't muck with behavior of normal buffer-replacement strategy */
	if (!from_ring ||
		strategy->buffers[strategy->current] != BufferDescriptorGetBuffer(buf))
		return false;

	/*
	 * Remove the dirty buffer from the ring; necessary to prevent infinite
	 * loop if all ring members are dirty.
	 */
	strategy->buffers[strategy->current] = InvalidBuffer;

	return true;
}
