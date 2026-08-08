/*-------------------------------------------------------------------------
 *
 * localbuf.c
 *	  local buffer manager. Fast buffer manager for temporary tables,
 *	  which never need to be WAL-logged or checkpointed, etc.
 *
 * 【模块总览(中文)】
 * 本文件实现"本地缓冲区管理器"(Local Buffer Manager),专门服务于
 * 临时表/临时索引(以及并行查询中的临时工作文件)。
 *
 * 与共享缓冲池的根本区别:
 * - 本地缓冲区是本进程私有的(用 malloc 分配,不进共享内存),因此:
 *   a) 完全不需要加锁、不需要引用计数(pin)的并发保护——"pin"退化为
 *      一个简单的 LocalRefCount 数组,用于检测泄漏;
 *   b) 不需要 WAL 日志(临时表崩溃即消失,无需恢复)、不需要检查点、
 *      不需要后台写进程、不需要缓冲环策略;
 * - 缓冲区编号是负数(缓冲 id 从 -1 开始),Buffer 的正负号正好区分
 *   "共享缓冲区(非负)"与"本地缓冲区(负数)",见 BufferIsLocal 宏;
 * - 页内存采用"懒分配":首次使用时才从内存上下文按大块(16 块起步、
 *   翻倍增长)申请,减少对内存管理器的调用次数;
 * - 与共享缓冲池一样,也用一张哈希表(LocalBufHash,进程私有)完成
 *   "页标签 -> 本地缓冲区"的查找,替换算法同样是时钟扫描
 *   (GetLocalVictimBuffer),但实现简单得多。
 *
 * 状态变量说明:
 * - LocalBufferDescriptors  : 缓冲区描述符数组;
 * - LocalBufferBlockPointers: 各缓冲区对应的内存块指针数组(懒分配);
 * - LocalRefCount           : 各缓冲区的"引用计数"(仅本进程使用);
 * - nextFreeLocalBufId      : 时钟扫描指针;
 * - NLocalPinnedBuffers     : 被 pin 过的本地缓冲区个数(统计用)。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994-5, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/buffer/localbuf.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/parallel.h"
#include "executor/instrument.h"
#include "pgstat.h"
#include "storage/aio.h"
#include "storage/buf_internals.h"
#include "storage/bufmgr.h"
#include "storage/fd.h"
#include "utils/guc_hooks.h"
#include "utils/memdebug.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/resowner.h"


/*#define LBDEBUG*/

/* entry for buffer lookup hashtable */
/* 本地缓冲区查找哈希表条目:key 是页标签(BufferTag),id 是本地缓冲区
 * 在 LocalBufferDescriptors 数组中的下标(0 基;与共享表不同,这里直接用
 * 下标,不依赖"负缓冲区编号"的换算)。 */
typedef struct
{
	BufferTag	key;			/* Tag of a disk page */
	int			id;				/* Associated local buffer's index */
} LocalBufferLookupEnt;

/* Note: this macro only works on local buffers, not shared ones! */
/* 取本地缓冲区的内存块指针。本地缓冲区 id(经 BufferDescriptorGetBuffer
 * 加 1 后)是负数:buf_id = -i-2,所以 -((bufHdr)->buf_id + 2) 正好还原
 * 为数组下标 i。注意此宏只适用于本地缓冲区(共享缓冲区没有这个数组)。 */
#define LocalBufHdrGetBlock(bufHdr) \
	LocalBufferBlockPointers[-((bufHdr)->buf_id + 2)]

int			NLocBuffer = 0;		/* until buffers are initialized */
/* 本地缓冲区数量;InitLocalBuffers() 完成前为 0,之后等于 GUC 参数
 * temp_buffers 的值。 */

BufferDesc *LocalBufferDescriptors = NULL;
/* 本地缓冲区描述符数组(进程私有,内存来自普通 malloc)。 */
Block	   *LocalBufferBlockPointers = NULL;
/* 本地缓冲区的数据块指针数组:为 NULL 表示该块尚未分配(懒分配,
 * 见 GetLocalBufferStorage)。 */
int32	   *LocalRefCount = NULL;
/* 各本地缓冲区的引用计数(仅本进程,不需要原子操作;数值 >0 表示被 pin)。 */

static int	nextFreeLocalBufId = 0;
/* 本地时钟扫描指针:下次优先考察的缓冲区下标。 */

static HTAB *LocalBufHash = NULL;
/* "页标签 -> 本地缓冲区"查找哈希表(进程私有)。 */

/* number of local buffers pinned at least once */
/* 统计"当前有多少个本地缓冲区正处于 pin 状态"(LocalRefCount>0 的个数),
 * 用于 GetAdditionalLocalPinLimit 等预读限额计算。 */
static int	NLocalPinnedBuffers = 0;


static void InitLocalBuffers(void);
static Block GetLocalBufferStorage(void);
static Buffer GetLocalVictimBuffer(void);


/*
 * PrefetchLocalBuffer -
 *	  initiate asynchronous read of a block of a relation
 *
 * Do PrefetchBuffer's work for temporary relations.
 * No-op if prefetching isn't compiled in.
 */
/*
 * PrefetchLocalBuffer
 *      (中文)对临时表发起块的异步预读(异步 I/O 请求)
 *
 * 【作用】PrefetchBuffer() 的"临时表"版本:告诉 I/O 子系统"这个块以后
 * 会被用到,请提前读进 OS 缓存"。与共享缓冲版本的区别:临时表页不进
 * 共享缓冲池,所以这里只做 smgrprefetch(把读请求发给内核/io_uring),
 * 不做"调入共享缓冲区"的动作。
 *
 * 【执行流程】先查本地哈希表:
 * - 块已在本地缓冲区:返回 recent_buffer 指向它,无需预读;
 * - 不在:若编译期启用预读且未禁用直接 I/O,发起 smgrprefetch,
 *   返回 initiated_io = true 表示"已发起 I/O"。
 *
 * 【参数】
 *   smgr     —— 存储管理器关系对象;
 *   forkNum  —— 分支编号(主分支/VM/FSM);
 *   blockNum —— 要预读的块号。
 * 【返回值】PrefetchBufferResult{recent_buffer, initiated_io}:
 *   recent_buffer 有效表示该页已在缓冲(调用方可直接改用普通读,顺便
 *   消除预读状态);initiated_io 表示本调用真的发起了一次异步读。
 */
PrefetchBufferResult
PrefetchLocalBuffer(SMgrRelation smgr, ForkNumber forkNum,
					BlockNumber blockNum)
{
	PrefetchBufferResult result = {InvalidBuffer, false};
	BufferTag	newTag;			/* identity of requested block */
	LocalBufferLookupEnt *hresult;

	InitBufferTag(&newTag, &smgr->smgr_rlocator.locator, forkNum, blockNum);

	/* Initialize local buffers if first request in this session */
	if (LocalBufHash == NULL)
		InitLocalBuffers();

	/* See if the desired buffer already exists */
	hresult = (LocalBufferLookupEnt *)
		hash_search(LocalBufHash, &newTag, HASH_FIND, NULL);

	if (hresult)
	{
		/* Yes, so nothing to do */
		result.recent_buffer = -hresult->id - 1;
	}
	else
	{
#ifdef USE_PREFETCH
		/* Not in buffers, so initiate prefetch */
		if ((io_direct_flags & IO_DIRECT_DATA) == 0 &&
			smgrprefetch(smgr, forkNum, blockNum, 1))
		{
			result.initiated_io = true;
		}
#endif							/* USE_PREFETCH */
	}

	return result;
}


/*
 * LocalBufferAlloc -
 *	  Find or create a local buffer for the given page of the given relation.
 *
 * API is similar to bufmgr.c's BufferAlloc, except that we do not need to do
 * any locking since this is all local.  We support only default access
 * strategy (hence, usage_count is always advanced).
 */
/*
 * LocalBufferAlloc
 *      (中文)为给定关系的给定页"查找或创建"一个本地缓冲区
 *
 * 【作用】缓冲管理器请求临时表页时的核心分配函数(等价于共享版本的
 * BufferAlloc)。返回值已 pin(引用计数 +1)并登记到资源所有者。
 *
 * 【执行流程】
 * 1. 首次使用时惰性初始化本地缓冲池(InitLocalBuffers);
 * 2. 查本地哈希表:
 *    - 命中:直接 pin 该缓冲区,并通过 *foundPtr 返回页是否有效
 *      (BM_VALID;无效说明 I/O 未完成或页尚未读入);
 *    - 未命中:调用 GetLocalVictimBuffer() 挑一个牺牲缓冲区
 *      (时钟扫描),把它从旧标签切换到新标签,设置 usage_count = 1,
 *      登记进哈希表,*foundPtr = false 通知调用者"需要从磁盘读页"。
 *
 * 【与共享版本的关键差异】全程无锁!因为本地缓冲只有本进程能碰:
 * - 不需要 BufMappingLock 分区锁;
 * - 不需要"先 pin 再放锁"的并发协议;
 * - state 字段用非原子的 unlocked 写即可。
 *
 * 【参数】
 *   smgr     —— 存储管理器关系对象;
 *   forkNum  —— 分支编号;
 *   blockNum —— 块号;
 *   foundPtr —— 输出参数:true 表示页已在缓冲且有效。
 * 【返回值】已 pin 的本地缓冲区描述符。
 */
BufferDesc *
LocalBufferAlloc(SMgrRelation smgr, ForkNumber forkNum, BlockNumber blockNum,
				 bool *foundPtr)
{
	BufferTag	newTag;			/* identity of requested block */
	LocalBufferLookupEnt *hresult;
	BufferDesc *bufHdr;
	Buffer		victim_buffer;
	int			bufid;
	bool		found;

	InitBufferTag(&newTag, &smgr->smgr_rlocator.locator, forkNum, blockNum);

	/* Initialize local buffers if first request in this session */
	if (LocalBufHash == NULL)
		InitLocalBuffers();

	ResourceOwnerEnlarge(CurrentResourceOwner);

	/* See if the desired buffer already exists */
	hresult = (LocalBufferLookupEnt *)
		hash_search(LocalBufHash, &newTag, HASH_FIND, NULL);

	if (hresult)
	{
		bufid = hresult->id;
		bufHdr = GetLocalBufferDescriptor(bufid);
		Assert(BufferTagsEqual(&bufHdr->tag, &newTag));

		*foundPtr = PinLocalBuffer(bufHdr, true);
	}
	else
	{
		uint64		buf_state;

		victim_buffer = GetLocalVictimBuffer();
		bufid = -victim_buffer - 1;
		bufHdr = GetLocalBufferDescriptor(bufid);

		hresult = (LocalBufferLookupEnt *)
			hash_search(LocalBufHash, &newTag, HASH_ENTER, &found);
		if (found)				/* shouldn't happen */
			elog(ERROR, "local buffer hash table corrupted");
		hresult->id = bufid;

		/*
		 * it's all ours now.
		 */
		bufHdr->tag = newTag;

		buf_state = pg_atomic_read_u64(&bufHdr->state);
		buf_state &= ~(BUF_FLAG_MASK | BUF_USAGECOUNT_MASK);
		buf_state |= BM_TAG_VALID | BUF_USAGECOUNT_ONE;
		pg_atomic_unlocked_write_u64(&bufHdr->state, buf_state);

		*foundPtr = false;
	}

	return bufHdr;
}

/*
 * Like FlushBuffer(), just for local buffers.
 */
/*
 * FlushLocalBuffer
 *      (中文)把本地缓冲区写回磁盘(FlushBuffer 的临时表版本)
 *
 * 【作用】临时表缓冲区的写盘操作:计算页校验和,经 smgrwrite 写回磁盘,
 * 然后清除 BM_DIRTY。调用场景:牺牲者替换前必须先把脏页写盘。
 *
 * 【背景】临时表也走普通 smgr(文件系统/表空间),所以写盘路径相同,
 * 但无需 WAL(崩溃后临时表整个消失,无需恢复)。
 *
 * 【执行流程】StartLocalBufferIO 确认可以开始写 → 填页校验和 →
 * smgrwrite 落盘 → 统计临时表 I/O(IOOBJECT_TEMP_RELATION) →
 * TerminateLocalBufferIO 清除脏位 → 累加 pgBufferUsage 统计。
 *
 * 【参数】
 *   bufHdr —— 要写的本地缓冲区;
 *   reln   —— 对应的存储管理器关系;为 NULL 时按 tag 里的 rlocator 现场打开。
 * 【返回值】无。
 */
void
FlushLocalBuffer(BufferDesc *bufHdr, SMgrRelation reln)
{
	instr_time	io_start;
	Page		localpage = (char *) LocalBufHdrGetBlock(bufHdr);

	Assert(LocalRefCount[-BufferDescriptorGetBuffer(bufHdr) - 1] > 0);

	/*
	 * Try to start an I/O operation.  There currently are no reasons for
	 * StartLocalBufferIO to return anything other than
	 * BUFFER_IO_READY_FOR_IO, so we raise an error in that case.
	 */
	if (StartLocalBufferIO(bufHdr, false, true, NULL) != BUFFER_IO_READY_FOR_IO)
		elog(ERROR, "failed to start write IO on local buffer");

	/* Find smgr relation for buffer */
	if (reln == NULL)
		reln = smgropen(BufTagGetRelFileLocator(&bufHdr->tag),
						MyProcNumber);

	PageSetChecksum(localpage, bufHdr->tag.blockNum);

	io_start = pgstat_prepare_io_time(track_io_timing);

	/* And write... */
	smgrwrite(reln,
			  BufTagGetForkNum(&bufHdr->tag),
			  bufHdr->tag.blockNum,
			  localpage,
			  false);

	/* Temporary table I/O does not use Buffer Access Strategies */
	pgstat_count_io_op_time(IOOBJECT_TEMP_RELATION, IOCONTEXT_NORMAL,
							IOOP_WRITE, io_start, 1, BLCKSZ);

	/* Mark not-dirty */
	TerminateLocalBufferIO(bufHdr, true, 0, false);

	pgBufferUsage.local_blks_written++;
}

static Buffer
GetLocalVictimBuffer(void)
/* (中文)挑选并准备一个牺牲本地缓冲区(时钟扫描算法的本地简化版)
 *
 * 【作用】为新的页腾出缓冲区:按时钟扫描找到"空闲"的本地缓冲区,
 * 必要时把其中的脏页写盘,并把旧标签从哈希表清除,返回其 Buffer 编号
 * (负数)。
 *
 * 【执行流程】
 * 1. 时钟扫描:从 nextFreeLocalBufId 开始循环考察:
 *    - 已 pin(LocalRefCount>0):跳过;若整整扫了一圈都没找到,报
 *      "no empty local buffer available"(临时缓冲耗尽);
 *    - 未 pin 但 usage_count>0:减 1 后继续(近似 LRU 的"缓刑"机制);
 *    - 未 pin 且 usage_count==0:选中。
 * 2. 懒分配:若该缓冲区还没分配数据块内存,现在分配
 *    (GetLocalBufferStorage 按 16 块起步、翻倍增长的大块策略);
 * 3. 若里面是脏页,先 FlushLocalBuffer 写盘(临时表没有后台写进程,
 *    只能由本进程自己写);
 * 4. 若旧标签有效,InvalidateLocalBuffer 从哈希表删除并清状态,
 *    并统计一次 IOOP_EVICT。
 *
 * 【与共享版本的区别】共享版有缓冲环、bgwriter 唤醒、CAS 等并发机制;
 * 本地版全部是单进程操作,直接读/写数组和 state 即可。
 *
 * 【参数】无。
 * 【返回值】牺牲缓冲区的 Buffer 编号(负值,即 1 基的 -bufid-1)。
 */
{
	int			victim_bufid;
	int			trycounter;
	BufferDesc *bufHdr;

	ResourceOwnerEnlarge(CurrentResourceOwner);

	/*
	 * Need to get a new buffer.  We use a clock-sweep algorithm (essentially
	 * the same as what freelist.c does now...)
	 */
	trycounter = NLocBuffer;
	for (;;)
	{
		victim_bufid = nextFreeLocalBufId;

		if (++nextFreeLocalBufId >= NLocBuffer)
			nextFreeLocalBufId = 0;

		bufHdr = GetLocalBufferDescriptor(victim_bufid);

		if (LocalRefCount[victim_bufid] == 0)
		{
			uint64		buf_state = pg_atomic_read_u64(&bufHdr->state);

			if (BUF_STATE_GET_USAGECOUNT(buf_state) > 0)
			{
				buf_state -= BUF_USAGECOUNT_ONE;
				pg_atomic_unlocked_write_u64(&bufHdr->state, buf_state);
				trycounter = NLocBuffer;
			}
			else if (BUF_STATE_GET_REFCOUNT(buf_state) > 0)
			{
				/*
				 * This can be reached if the backend initiated AIO for this
				 * buffer and then errored out.
				 */
			}
			else
			{
				/* Found a usable buffer */
				PinLocalBuffer(bufHdr, false);
				break;
			}
		}
		else if (--trycounter == 0)
			ereport(ERROR,
					(errcode(ERRCODE_INSUFFICIENT_RESOURCES),
					 errmsg("no empty local buffer available")));
	}

	/*
	 * lazy memory allocation: allocate space on first use of a buffer.
	 */
	if (LocalBufHdrGetBlock(bufHdr) == NULL)
	{
		/* Set pointer for use by BufferGetBlock() macro */
		LocalBufHdrGetBlock(bufHdr) = GetLocalBufferStorage();
	}

	/*
	 * this buffer is not referenced but it might still be dirty. if that's
	 * the case, write it out before reusing it!
	 */
	if (pg_atomic_read_u64(&bufHdr->state) & BM_DIRTY)
		FlushLocalBuffer(bufHdr, NULL);

	/*
	 * Remove the victim buffer from the hashtable and mark as invalid.
	 */
	if (pg_atomic_read_u64(&bufHdr->state) & BM_TAG_VALID)
	{
		InvalidateLocalBuffer(bufHdr, false);

		pgstat_count_io_op(IOOBJECT_TEMP_RELATION, IOCONTEXT_NORMAL, IOOP_EVICT, 1, 0);
	}

	return BufferDescriptorGetBuffer(bufHdr);
}

/* see GetPinLimit() */
/* (中文)本地缓冲版的"pin 限额"(对应共享版的 GetPinLimit,见 bufmgr.c):
 * 返回本后端一次最多可 pin 的本地缓冲区数。每个后端有自己的临时缓冲池,
 * 但仍需预留余量给"同一查询中多个并发扫描"等同时持 pin 的场景,
 * 因此只取其 1/4。 */
uint32
GetLocalPinLimit(void)
{
	/*
	 * Every backend has its own temporary buffers, but we leave headroom for
	 * concurrent pin-holders -- like multiple scans in the same query.
	 */
	return num_temp_buffers / 4;
}

/* see GetAdditionalPinLimit() */
/* (中文)本地缓冲版的"额外可 pin 额度"(对应 GetAdditionalPinLimit):
 * 返回"还能再 pin 多少本地缓冲区":限额减去当前已 pin 数;已用满则返回 0。
 * 供预读循环判断是否还能继续往前 pin。 */
uint32
GetAdditionalLocalPinLimit(void)
{
	uint32		total = GetLocalPinLimit();

	Assert(NLocalPinnedBuffers <= num_temp_buffers);

	if (NLocalPinnedBuffers >= total)
		return 0;
	return total - NLocalPinnedBuffers;
}

/* see LimitAdditionalPins() */
/* (中文)把"计划额外 pin 的缓冲数"裁剪到可行范围:
 * 临时缓冲只被本进程使用,不需要考虑其他后端,但总数不能超过
 * num_temp_buffers(池可能还没初始化,直接读 GUC 值)。
 * additional_pins <= 1 时无需调整(也避免死循环)。 */
void
LimitAdditionalLocalPins(uint32 *additional_pins)
{
	uint32		max_pins;

	if (*additional_pins <= 1)
		return;

	/*
	 * In contrast to LimitAdditionalPins() other backends don't play a role
	 * here. We can allow up to NLocBuffer pins in total, but it might not be
	 * initialized yet so read num_temp_buffers.
	 */
	max_pins = (num_temp_buffers - NLocalPinnedBuffers);

	if (*additional_pins >= max_pins)
		*additional_pins = max_pins;
}

/*
 * Implementation of ExtendBufferedRelBy() and ExtendBufferedRelTo() for
 * temporary buffers.
 */
/*
 * ExtendBufferedRelLocal
 *      (中文)临时表的"批量扩展"实现(ExtendBufferedRelBy/To 的本地版本)
 *
 * 【作用】为临时表追加 extend_by 个新块:在本地缓冲池中准备好相应数量的
 * 缓冲区(内容清零),把文件真正扩展,并把新块登记到这些缓冲区、标记
 * BM_VALID,最后让调用者直接拿到这些已就绪的缓冲区。
 *
 * 这是 PG 16+ 引入的"预分配多个页 + 一次零扩展"优化:共享版本需要处理
 * 并发(别的进程可能同时扩展),而临时表是本进程独享,因此实现更简单。
 *
 * 【执行流程】
 * 1. 惰性初始化本地缓冲池;裁剪 extend_by 到可 pin 限额;
 * 2. 循环调用 GetLocalVictimBuffer 为每个新块准备缓冲区并清零内容
 *    (新块数据未定义,直接填 0);
 * 3. smgrnblocks 获取当前文件块数 first_block,检查不超出 MaxBlockNumber
 *    (注意:对临时表,文件大小只可能被本进程改变,因此不会出现"发现已
 *    有人扩展过"的情况,断言即可);
 * 4. 为每个新块构造标签:登记进哈希表。若发现标签已存在(理论上只在
 *    "上一轮扩展已进行到一半"时可能),则改用已有缓冲区、Unpin 自己的
 *    牺牲者;否则把牺牲者切换为新标签,并 StartLocalBufferIO 标记
 *    "I/O 进行中"(为下面的 smgrzeroextend 准备);
 * 5. smgrzeroextend 一次性把文件扩展 extend_by 块(实际写盘动作);
 * 6. 所有缓冲区置 BM_VALID(表示内容已就绪),输出实际扩展数。
 *
 * 【参数】
 *   bmr         —— 缓冲管理器关系(BufferManagerRelation,内含 smgr 句柄);
 *   fork        —— 分支编号;
 *   flags       —— 扩展选项标志(见 ExtendBufferedRelFlags);
 *   extend_by   —— 计划扩展的块数(会被裁剪);
 *   extend_upto —— 扩展上限块号(InvalidBlockNumber 表示不限);
 *   buffers     —— 输出数组:返回各新块对应的 Buffer;
 *   extended_by —— 输出:实际扩展的块数。
 * 【返回值】文件扩展前的第一块块号(即新块的起始块号)。
 */
BlockNumber
ExtendBufferedRelLocal(BufferManagerRelation bmr,
					   ForkNumber fork,
					   uint32 flags,
					   uint32 extend_by,
					   BlockNumber extend_upto,
					   Buffer *buffers,
					   uint32 *extended_by)
{
	BlockNumber first_block;
	instr_time	io_start;

	/* Initialize local buffers if first request in this session */
	if (LocalBufHash == NULL)
		InitLocalBuffers();

	LimitAdditionalLocalPins(&extend_by);

	for (uint32 i = 0; i < extend_by; i++)
	{
		BufferDesc *buf_hdr;
		Block		buf_block;

		buffers[i] = GetLocalVictimBuffer();
		buf_hdr = GetLocalBufferDescriptor(-buffers[i] - 1);
		buf_block = LocalBufHdrGetBlock(buf_hdr);

		/* new buffers are zero-filled */
		MemSet(buf_block, 0, BLCKSZ);
	}

	first_block = smgrnblocks(BMR_GET_SMGR(bmr), fork);

	if (extend_upto != InvalidBlockNumber)
	{
		/*
		 * In contrast to shared relations, nothing could change the relation
		 * size concurrently. Thus we shouldn't end up finding that we don't
		 * need to do anything.
		 */
		Assert(first_block <= extend_upto);

		Assert((uint64) first_block + extend_by <= extend_upto);
	}

	/* Fail if relation is already at maximum possible length */
	if ((uint64) first_block + extend_by >= MaxBlockNumber)
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("cannot extend relation %s beyond %u blocks",
						relpath(BMR_GET_SMGR(bmr)->smgr_rlocator, fork).str,
						MaxBlockNumber)));

	for (uint32 i = 0; i < extend_by; i++)
	{
		int			victim_buf_id;
		BufferDesc *victim_buf_hdr;
		BufferTag	tag;
		LocalBufferLookupEnt *hresult;
		bool		found;

		victim_buf_id = -buffers[i] - 1;
		victim_buf_hdr = GetLocalBufferDescriptor(victim_buf_id);

		/* in case we need to pin an existing buffer below */
		ResourceOwnerEnlarge(CurrentResourceOwner);

		InitBufferTag(&tag, &BMR_GET_SMGR(bmr)->smgr_rlocator.locator, fork,
					  first_block + i);

		hresult = (LocalBufferLookupEnt *)
			hash_search(LocalBufHash, &tag, HASH_ENTER, &found);
		if (found)
		{
			BufferDesc *existing_hdr;
			uint64		buf_state;

			UnpinLocalBuffer(BufferDescriptorGetBuffer(victim_buf_hdr));

			existing_hdr = GetLocalBufferDescriptor(hresult->id);
			PinLocalBuffer(existing_hdr, false);
			buffers[i] = BufferDescriptorGetBuffer(existing_hdr);

			/*
			 * Clear the BM_VALID bit, do StartLocalBufferIO() and proceed.
			 */
			buf_state = pg_atomic_read_u64(&existing_hdr->state);
			Assert(buf_state & BM_TAG_VALID);
			Assert(!(buf_state & BM_DIRTY));
			buf_state &= ~BM_VALID;
			pg_atomic_unlocked_write_u64(&existing_hdr->state, buf_state);

			/* no need to loop for local buffers */
			StartLocalBufferIO(existing_hdr, true, true, NULL);
		}
		else
		{
			uint64		buf_state = pg_atomic_read_u64(&victim_buf_hdr->state);

			Assert(!(buf_state & (BM_VALID | BM_TAG_VALID | BM_DIRTY)));

			victim_buf_hdr->tag = tag;

			buf_state |= BM_TAG_VALID | BUF_USAGECOUNT_ONE;

			pg_atomic_unlocked_write_u64(&victim_buf_hdr->state, buf_state);

			hresult->id = victim_buf_id;

			StartLocalBufferIO(victim_buf_hdr, true, true, NULL);
		}
	}

	io_start = pgstat_prepare_io_time(track_io_timing);

	/* actually extend relation */
	smgrzeroextend(BMR_GET_SMGR(bmr), fork, first_block, extend_by, false);

	pgstat_count_io_op_time(IOOBJECT_TEMP_RELATION, IOCONTEXT_NORMAL, IOOP_EXTEND,
							io_start, 1, extend_by * BLCKSZ);

	for (uint32 i = 0; i < extend_by; i++)
	{
		Buffer		buf = buffers[i];
		BufferDesc *buf_hdr;
		uint64		buf_state;

		buf_hdr = GetLocalBufferDescriptor(-buf - 1);

		buf_state = pg_atomic_read_u64(&buf_hdr->state);
		buf_state |= BM_VALID;
		pg_atomic_unlocked_write_u64(&buf_hdr->state, buf_state);
	}

	*extended_by = extend_by;

	pgBufferUsage.local_blks_written += extend_by;

	return first_block;
}

/*
 * MarkLocalBufferDirty -
 *	  mark a local buffer dirty
 */
/*
 * MarkLocalBufferDirty
 *      (中文)把本地缓冲区标记为"脏"
 *
 * 【作用】在本地缓冲区的页内容被修改后调用,置上 BM_DIRTY 位,表示
 * "该页与磁盘不一致,替换时需写回"。没有 WAL 环节(临时表不写 WAL)。
 *
 * 【实现】先确认调用者持有 pin(LocalRefCount > 0);若之前不是脏的,
 * 把 pgBufferUsage.local_blks_dirtied 统计 +1(避免重复计数),然后置位。
 * 单进程场景,直接非原子写 state 即可。
 *
 * 【参数】buffer —— 要标记的本地缓冲区(Buffer,负数)。
 * 【返回值】无。
 */
void
MarkLocalBufferDirty(Buffer buffer)
{
	int			bufid;
	BufferDesc *bufHdr;
	uint64		buf_state;

	Assert(BufferIsLocal(buffer));

#ifdef LBDEBUG
	fprintf(stderr, "LB DIRTY %d\n", buffer);
#endif

	bufid = -buffer - 1;

	Assert(LocalRefCount[bufid] > 0);

	bufHdr = GetLocalBufferDescriptor(bufid);

	buf_state = pg_atomic_read_u64(&bufHdr->state);

	if (!(buf_state & BM_DIRTY))
		pgBufferUsage.local_blks_dirtied++;

	buf_state |= BM_DIRTY;

	pg_atomic_unlocked_write_u64(&bufHdr->state, buf_state);
}

/*
 * Like StartSharedBufferIO, but for local buffers
 */
/*
 * StartLocalBufferIO
 *      (中文)开始一次针对本地缓冲区的 I/O(StartSharedBufferIO 的本地版)
 *
 * 【作用】返回三种结果之一,告知调用者"这次 I/O 是否可以开始"——
 * - BUFFER_IO_READY_FOR_IO:可以开始(调用者负责执行读/写并随后调用
 *   TerminateLocalBufferIO 收尾);
 * - BUFFER_IO_ALREADY_DONE:目标状态已满足(读时页已 BM_VALID、写时页
 *   已不脏),无需 I/O;
 * - BUFFER_IO_IN_PROGRESS:该缓冲区已有异步 I/O 在进行中。若 io_wref
 *   非空(调用者自己发起的异步 I/O 链),把已有的等待引用交还给它去"并入"
 *   该 I/O;否则若 wait 为 true 就阻塞等待其完成,若 wait 为 false 直接
 *   返回 IN_PROGRESS 由调用者决定。
 *
 * 【背景】本地缓冲区原本绝无并发 I/O 冲突,但引入异步 I/O(AIO)后,同一
 * 关系可能被两个扫描同时读取,其中一个可能在后台处理该缓冲区的读 I/O;
 * 因此需要这个检查点(单进程内的"并发")。
 *
 * 【参数】
 *   bufHdr  —— 本地缓冲区;
 *   forInput —— true 表示"要读入页"(检查 BM_VALID),false 表示"要写页"
 *               (检查 !BM_DIRTY);
 *   wait    —— 若已有 I/O 进行中,是否阻塞等待;
 *   io_wref —— 调用者的异步 I/O 等待引用(可空)。
 * 【返回值】见上方三种 BUFFER_IO_* 结果。
 */
StartBufferIOResult
StartLocalBufferIO(BufferDesc *bufHdr, bool forInput, bool wait, PgAioWaitRef *io_wref)
{
	uint64		buf_state;

	/*
	 * With AIO the buffer could have IO in progress, e.g. when there are two
	 * scans of the same relation.  Either wait for the other IO (if wait =
	 * true and io_wref == NULL) or return BUFFER_IO_IN_PROGRESS;
	 */
	if (pgaio_wref_valid(&bufHdr->io_wref))
	{
		PgAioWaitRef buf_wref = bufHdr->io_wref;

		if (io_wref != NULL)
		{
			/* We've already asynchronously started this IO, so join it */
			*io_wref = buf_wref;
			return BUFFER_IO_IN_PROGRESS;
		}

		/*
		 * For temp buffers we should never need to wait in
		 * StartLocalBufferIO() when called with io_wref == NULL while there
		 * are staged IOs, as it's not allowed to call code that is not aware
		 * of AIO while in batch mode.
		 */
		Assert(!pgaio_have_staged());

		if (!wait)
			return BUFFER_IO_IN_PROGRESS;

		pgaio_wref_wait(&buf_wref);
	}

	/* Once we get here, there is definitely no I/O active on this buffer */

	/* Check if someone else already did the I/O */
	buf_state = pg_atomic_read_u64(&bufHdr->state);
	if (forInput ? (buf_state & BM_VALID) : !(buf_state & BM_DIRTY))
	{
		return BUFFER_IO_ALREADY_DONE;
	}

	/* BM_IO_IN_PROGRESS isn't currently used for local buffers */

	/* local buffers don't track IO using resowners */

	return BUFFER_IO_READY_FOR_IO;
}

/*
 * Like TerminateBufferIO, but for local buffers
 */
/*
 * TerminateLocalBufferIO
 *      (中文)结束一次本地缓冲区的 I/O(TerminateBufferIO 的本地版)
 *
 * 【作用】在 I/O 完成后收尾:清除 BM_IO_ERROR(若本次失败,调用方会重新
 * 置位以便下次重试)、按需清除 BM_DIRTY(写完成)或设置指定标志位、
 * 若是 AIO 释放其持有的 pin 并清除 io_wref。单进程场景,直接非原子写。
 *
 * 【参数】
 *   bufHdr         —— 本地缓冲区;
 *   clear_dirty    —— 是否清除脏位;
 *   set_flag_bits  —— 要置位的新标志;
 *   release_aio    —— 是否释放 AIO 子系统持有的引用(pin)。
 * 【返回值】无。
 */
void
TerminateLocalBufferIO(BufferDesc *bufHdr, bool clear_dirty, uint64 set_flag_bits,
					   bool release_aio)
{
	/* Only need to adjust flags */
	uint64		buf_state = pg_atomic_read_u64(&bufHdr->state);

	/* BM_IO_IN_PROGRESS isn't currently used for local buffers */

	/* Clear earlier errors, if this IO failed, it'll be marked again */
	buf_state &= ~BM_IO_ERROR;

	if (clear_dirty)
		buf_state &= ~BM_DIRTY;

	if (release_aio)
	{
		/* release pin held by IO subsystem, see also buffer_stage_common() */
		Assert(BUF_STATE_GET_REFCOUNT(buf_state) > 0);
		buf_state -= BUF_REFCOUNT_ONE;
		pgaio_wref_clear(&bufHdr->io_wref);
	}

	buf_state |= set_flag_bits;
	pg_atomic_unlocked_write_u64(&bufHdr->state, buf_state);

	/* local buffers don't track IO using resowners */

	/* local buffers don't use the IO CV, as no other process can see buffer */

	/* local buffers don't use BM_PIN_COUNT_WAITER, so no need to wake */
}

/*
 * InvalidateLocalBuffer -- mark a local buffer invalid.
 *
 * If check_unreferenced is true, error out if the buffer is still
 * pinned. Passing false is appropriate when calling InvalidateLocalBuffer()
 * as part of changing the identity of a buffer, instead of just dropping the
 * buffer.
 *
 * See also InvalidateBuffer().
 */
/*
 * InvalidateLocalBuffer
 *      (中文)使一个本地缓冲区失效(清标签、清状态、移出哈希表)
 *
 * 【作用】把缓冲区从"属于某页"变为"无主空闲":
 * - 从哈希表删除其标签映射;
 * - 清空 tag、清掉所有标志位与 usage_count,使其可被时钟扫描重新复用。
 *
 * 典型调用场景:临时表被 DROP(见 DropRelationLocalBuffers)或缓冲区换页
 * (见 GetLocalVictimBuffer)。
 *
 * 【参数】
 *   bufHdr            —— 本地缓冲区;
 *   check_unreferenced —— true 表示"若仍被 pin 则报错"(用于表删除等场景,
 *                        pin 残留说明程序 bug);false 用于"换页"场景
 *                        (此时缓冲区已由本进程重新 pin,只是换标签)。
 * 【返回值】无。
 *
 * InvalidateLocalBuffer -- mark a local buffer invalid.
 *
 * If check_unreferenced is true, error out if the buffer is still
 * pinned. Passing false is appropriate when calling InvalidateLocalBuffer()
 * as part of changing the identity of a buffer, instead of just dropping the
 * buffer.
 *
 * See also InvalidateBuffer().
 */
void
InvalidateLocalBuffer(BufferDesc *bufHdr, bool check_unreferenced)
{
	Buffer		buffer = BufferDescriptorGetBuffer(bufHdr);
	int			bufid = -buffer - 1;
	uint64		buf_state;
	LocalBufferLookupEnt *hresult;

	/*
	 * It's possible that we started IO on this buffer before e.g. aborting
	 * the transaction that created a table. We need to wait for that IO to
	 * complete before removing / reusing the buffer.
	 */
	if (pgaio_wref_valid(&bufHdr->io_wref))
	{
		PgAioWaitRef iow = bufHdr->io_wref;

		pgaio_wref_wait(&iow);
		Assert(!pgaio_wref_valid(&bufHdr->io_wref));
	}

	buf_state = pg_atomic_read_u64(&bufHdr->state);

	/*
	 * We need to test not just LocalRefCount[bufid] but also the BufferDesc
	 * itself, as the latter is used to represent a pin by the AIO subsystem.
	 * This can happen if AIO is initiated and then the query errors out.
	 */
	if (check_unreferenced &&
		(LocalRefCount[bufid] != 0 || BUF_STATE_GET_REFCOUNT(buf_state) != 0))
		elog(ERROR, "block %u of %s is still referenced (local %d)",
			 bufHdr->tag.blockNum,
			 relpathbackend(BufTagGetRelFileLocator(&bufHdr->tag),
							MyProcNumber,
							BufTagGetForkNum(&bufHdr->tag)).str,
			 LocalRefCount[bufid]);

	/* Remove entry from hashtable */
	hresult = (LocalBufferLookupEnt *)
		hash_search(LocalBufHash, &bufHdr->tag, HASH_REMOVE, NULL);
	if (!hresult)				/* shouldn't happen */
		elog(ERROR, "local buffer hash table corrupted");
	/* Mark buffer invalid */
	ClearBufferTag(&bufHdr->tag);
	buf_state &= ~BUF_FLAG_MASK;
	buf_state &= ~BUF_USAGECOUNT_MASK;
	pg_atomic_unlocked_write_u64(&bufHdr->state, buf_state);
}

/*
 * DropRelationLocalBuffers
 *		This function removes from the buffer pool all the pages of the
 *		specified relation that have block numbers >= firstDelBlock.
 *		(In particular, with firstDelBlock = 0, all pages are removed.)
 *		Dirty pages are simply dropped, without bothering to write them
 *		out first.  Therefore, this is NOT rollback-able, and so should be
 *		used only with extreme caution!
 *
 *		See DropRelationBuffers in bufmgr.c for more notes.
 */
/*
 * DropRelationLocalBuffers
 *      (中文)从本地缓冲池中移除指定关系在 firstDelBlock 之后的全部页
 *
 * 【作用】用于临时表被截断(TRUNCATE)或部分删除等场景:把该关系块号
 * >= firstDelBlock 的页从本地缓冲池全部清除。脏页直接丢弃、不写盘!
 * (这正是 TRUNCATE 的语义:被砍掉的块本来就作废了)因此本操作不可回滚,
 * 只能由确认不需要这些页的调用者使用。
 *
 * 【实现】遍历所有本地缓冲区,匹配"关系 + fork 在指定集合中 + 块号
 * 达到删除阈值"的,调用 InvalidateLocalBuffer(要求无 pin 残留)。
 *
 * 【参数】
 *   rlocator     —— 关系文件定位符;
 *   forkNum      —— 要处理的分支编号数组;
 *   nforks       —— 数组长度;
 *   firstDelBlock —— 与 fork 数组对应的"删除起始块号"数组(块号>=该值
 *                    的页被删除)。
 * 【返回值】无。
 *
 * DropRelationLocalBuffers
 *		This function removes from the buffer pool all the pages of the
 *		specified relation that have block numbers >= firstDelBlock.
 *		(In particular, with firstDelBlock = 0, all pages are removed.)
 *		Dirty pages are simply dropped, without bothering to write them
 *		out first.  Therefore, this is NOT rollback-able, and so should be
 *		used only with extreme caution!
 *
 *		See DropRelationBuffers in bufmgr.c for more notes.
 */
void
DropRelationLocalBuffers(RelFileLocator rlocator, ForkNumber *forkNum,
						 int nforks, BlockNumber *firstDelBlock)
{
	int			i;
	int			j;

	for (i = 0; i < NLocBuffer; i++)
	{
		BufferDesc *bufHdr = GetLocalBufferDescriptor(i);
		uint64		buf_state;

		buf_state = pg_atomic_read_u64(&bufHdr->state);

		if (!(buf_state & BM_TAG_VALID) ||
			!BufTagMatchesRelFileLocator(&bufHdr->tag, &rlocator))
			continue;

		for (j = 0; j < nforks; j++)
		{
			if (BufTagGetForkNum(&bufHdr->tag) == forkNum[j] &&
				bufHdr->tag.blockNum >= firstDelBlock[j])
			{
				InvalidateLocalBuffer(bufHdr, true);
				break;
			}
		}
	}
}

/*
 * DropRelationAllLocalBuffers
 *		This function removes from the buffer pool all pages of all forks
 *		of the specified relation.
 *
 *		See DropRelationsAllBuffers in bufmgr.c for more notes.
 */
/* (中文)把指定关系的所有分支、所有页从本地缓冲池全部清除
 * (DropRelationLocalBuffers 的"全删"版本,用于 DROP TABLE 等场景)。
 * 脏页同样直接丢弃不写盘。 */
void
DropRelationAllLocalBuffers(RelFileLocator rlocator)
{
	int			i;

	for (i = 0; i < NLocBuffer; i++)
	{
		BufferDesc *bufHdr = GetLocalBufferDescriptor(i);
		uint64		buf_state;

		buf_state = pg_atomic_read_u64(&bufHdr->state);

		if ((buf_state & BM_TAG_VALID) &&
			BufTagMatchesRelFileLocator(&bufHdr->tag, &rlocator))
		{
			InvalidateLocalBuffer(bufHdr, true);
		}
	}
}

/*
 * InitLocalBuffers -
 *	  init the local buffer cache. Since most queries (esp. multi-user ones)
 *	  don't involve local buffers, we delay allocating actual memory for the
 *	  buffers until we need them; just make the buffer headers here.
 */
/*
 * InitLocalBuffers
 *      (中文)初始化本地缓冲池(首次使用临时表时才执行,惰性初始化)
 *
 * 【作用】分配本地缓冲池的全部基础设施:描述符数组、块指针数组、引用
 * 计数数组、查找哈希表。真正的页内存仍不分配,等首次用到时再按块分配
 * (见 GetLocalBufferStorage)。
 *
 * 【设计思想】大多数会话根本不用临时表,因此延迟到"第一次真正访问临时
 * 表"时才初始化,避免每个会话白白分配 temp_buffers 的内存。
 *
 * 【关键细节】
 * - 禁止在并行工作者中访问临时表:并行工作者看不到领导进程的本地缓冲
 *   (也访问不到临时表),这里做兜底检查并给出清晰的错误;
 * - buf_id 从 -2 开始逐个递减:BufferDescriptorGetBuffer(buf) = buf_id+1,
 *   于是首个本地缓冲区编号是 -1,恰好与共享缓冲区(>=0)区分开。
 *   注意 -1 与 0 的特殊语义:Buffer 0 是 InvalidBuffer,所以本地缓冲
 *   从 -1 起是安全的;
 * - 有意不初始化描述符里的原子 state(共享版本会 SpinLockInit /
 *   atomic init):本地缓冲不用并发保护,若有人对本地缓冲区引入原子操作,
 *   在没有原子支持的平台会立刻报错暴露问题。
 *
 * 【参数】无。【返回值】无(设置各全局变量)。
 */
static void
InitLocalBuffers(void)
{
	int			nbufs = num_temp_buffers;
	HASHCTL		info;
	int			i;

	/*
	 * Parallel workers can't access data in temporary tables, because they
	 * have no visibility into the local buffers of their leader.  This is a
	 * convenient, low-cost place to provide a backstop check for that.  Note
	 * that we don't wish to prevent a parallel worker from accessing catalog
	 * metadata about a temp table, so checks at higher levels would be
	 * inappropriate.
	 */
	if (IsParallelWorker())
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
				 errmsg("cannot access temporary tables during a parallel operation")));

	/* Allocate and zero buffer headers and auxiliary arrays */
	LocalBufferDescriptors = (BufferDesc *) calloc(nbufs, sizeof(BufferDesc));
	LocalBufferBlockPointers = (Block *) calloc(nbufs, sizeof(Block));
	LocalRefCount = (int32 *) calloc(nbufs, sizeof(int32));
	if (!LocalBufferDescriptors || !LocalBufferBlockPointers || !LocalRefCount)
		ereport(FATAL,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of memory")));

	nextFreeLocalBufId = 0;

	/* initialize fields that need to start off nonzero */
	for (i = 0; i < nbufs; i++)
	{
		BufferDesc *buf = GetLocalBufferDescriptor(i);

		/*
		 * negative to indicate local buffer. This is tricky: shared buffers
		 * start with 0. We have to start with -2. (Note that the routine
		 * BufferDescriptorGetBuffer adds 1 to buf_id so our first buffer id
		 * is -1.)
		 */
		buf->buf_id = -i - 2;

		pgaio_wref_clear(&buf->io_wref);

		/*
		 * Intentionally do not initialize the buffer's atomic variable
		 * (besides zeroing the underlying memory above). That way we get
		 * errors on platforms without atomics, if somebody (re-)introduces
		 * atomic operations for local buffers.
		 */
	}

	/* Create the lookup hash table */
	info.keysize = sizeof(BufferTag);
	info.entrysize = sizeof(LocalBufferLookupEnt);

	LocalBufHash = hash_create("Local Buffer Lookup Table",
							   nbufs,
							   &info,
							   HASH_ELEM | HASH_BLOBS);

	if (!LocalBufHash)
		elog(ERROR, "could not initialize local buffer hash table");

	/* Initialization done, mark buffers allocated */
	NLocBuffer = nbufs;
}

/*
 * XXX: We could have a slightly more efficient version of PinLocalBuffer()
 * that does not support adjusting the usagecount - but so far it does not
 * seem worth the trouble.
 *
 * Note that ResourceOwnerEnlarge() must have been done already.
 */
/*
 * PinLocalBuffer
 *      (中文)pin 一个本地缓冲区(引用计数 +1,登记资源所有者)
 *
 * 【作用】与共享版的 PinBuffer 对应:表示"本进程正在使用该缓冲区"。
 * 在单进程的本地场景下,它主要起两个作用:
 * 1) 计数(LocalRefCount / NLocalPinnedBuffers),供时钟扫描判断
 *    "该缓冲区是否正在被使用"以及做泄漏检测;
 * 2) 登记到资源所有者(resource owner),保证事务出错回滚时 pin 被
 *    自动释放,不会泄漏。
 *
 * 【返回值】缓冲区是否已有效(BM_VALID)。调用者据此判断"页内容是否
 * 已就绪":无效时需要通过 I/O 读入后再继续。
 *
 * 细节:第一次 pin(计数从 0 变 1)时,同步把描述符 state 里的 refcount
 * 加 1(本地缓冲用 unlocked 写即可),并按需把 usage_count 加 1(上限
 * BM_MAX_USAGE_COUNT);Valgrind 下把页内存标记为"已定义"以便检测。
 */
bool
PinLocalBuffer(BufferDesc *buf_hdr, bool adjust_usagecount)
{
	uint64		buf_state;
	Buffer		buffer = BufferDescriptorGetBuffer(buf_hdr);
	int			bufid = -buffer - 1;

	buf_state = pg_atomic_read_u64(&buf_hdr->state);

	if (LocalRefCount[bufid] == 0)
	{
		NLocalPinnedBuffers++;
		buf_state += BUF_REFCOUNT_ONE;
		if (adjust_usagecount &&
			BUF_STATE_GET_USAGECOUNT(buf_state) < BM_MAX_USAGE_COUNT)
		{
			buf_state += BUF_USAGECOUNT_ONE;
		}
		pg_atomic_unlocked_write_u64(&buf_hdr->state, buf_state);

		/*
		 * See comment in PinBuffer().
		 *
		 * If the buffer isn't allocated yet, it'll be marked as defined in
		 * GetLocalBufferStorage().
		 */
		if (LocalBufHdrGetBlock(buf_hdr) != NULL)
			VALGRIND_MAKE_MEM_DEFINED(LocalBufHdrGetBlock(buf_hdr), BLCKSZ);
	}
	LocalRefCount[bufid]++;
	ResourceOwnerRememberBuffer(CurrentResourceOwner,
								BufferDescriptorGetBuffer(buf_hdr));

	return buf_state & BM_VALID;
}

void
UnpinLocalBuffer(Buffer buffer)
/* (中文)解除对本地缓冲区的 pin:递减引用计数(含内部计数器与描述符
 * state),并从资源所有者处注销登记。
 * 详见 UnpinLocalBufferNoOwner 的注释。 */
{
	UnpinLocalBufferNoOwner(buffer);
	ResourceOwnerForgetBuffer(CurrentResourceOwner, buffer);
}

void
UnpinLocalBufferNoOwner(Buffer buffer)
/* (中文)UnpinLocalBuffer 的内核:只处理引用计数,不碰资源所有者。
 * 把 LocalRefCount[bufid] 减 1;若减到 0(这是最后一次 pin 释放),
 * 同步把描述符 state 的 refcount 减 1、递减 NLocalPinnedBuffers,并在
 * Valgrind 下把页内存标记为"未定义"(防止读到陈旧数据而不自知)。
 * 分离出 NoOwner 版本是为了给某些"pin 不由资源所有者管理"的场景
 * (如 AIO 持有的引用)使用。 */
{
	int			buffid = -buffer - 1;

	Assert(BufferIsLocal(buffer));
	Assert(LocalRefCount[buffid] > 0);
	Assert(NLocalPinnedBuffers > 0);

	if (--LocalRefCount[buffid] == 0)
	{
		BufferDesc *buf_hdr = GetLocalBufferDescriptor(buffid);
		uint64		buf_state;

		NLocalPinnedBuffers--;

		buf_state = pg_atomic_read_u64(&buf_hdr->state);
		Assert(BUF_STATE_GET_REFCOUNT(buf_state) > 0);
		buf_state -= BUF_REFCOUNT_ONE;
		pg_atomic_unlocked_write_u64(&buf_hdr->state, buf_state);

		/* see comment in UnpinBufferNoOwner */
		VALGRIND_MAKE_MEM_NOACCESS(LocalBufHdrGetBlock(buf_hdr), BLCKSZ);
	}
}

/*
 * GUC check_hook for temp_buffers
 */
/*
 * check_temp_buffers
 *      (中文)GUC 参数 temp_buffers 的校验钩子
 *
 * 【作用】用户通过 SET temp_buffers / postgresql.conf 修改该参数时,
 * 先经此钩子检查:
 * - 若本地缓冲池已初始化(NLocBuffer > 0)且新值不同,则拒绝修改
 *   ——因为缓冲池的大小已在初始化时定死,临时表也被访问过,无法更改。
 *   但 PGC_S_TEST(仅测试取值、不真正应用)不受此限制。
 *
 * 【返回值】true 接受新值;false 拒绝(并给出具体原因)。
 */
bool
check_temp_buffers(int *newval, void **extra, GucSource source)
{
	/*
	 * Once local buffers have been initialized, it's too late to change this.
	 * However, if this is only a test call, allow it.
	 */
	if (source != PGC_S_TEST && NLocBuffer && NLocBuffer != *newval)
	{
		GUC_check_errdetail("\"temp_buffers\" cannot be changed after any temporary tables have been accessed in the session.");
		return false;
	}
	return true;
}

/*
 * GetLocalBufferStorage - allocate memory for a local buffer
 *
 * The idea of this function is to aggregate our requests for storage
 * so that the memory manager doesn't see a whole lot of relatively small
 * requests.  Since we'll never give back a local buffer once it's created
 * within a particular process, no point in burdening memmgr with separately
 * managed chunks.
 */
/*
 * GetLocalBufferStorage
 *      (中文)为本地缓冲区分配数据块内存(懒分配 + 批量申请)
 *
 * 【作用】返回一块 BLCKSZ(默认 8KB)的页内存,并把指针记入
 * LocalBufferBlockPointers 对应槽位(通过调用方写回宏)。
 *
 * 【设计思想】两个层面的优化:
 * 1. 懒分配:缓冲区头在 InitLocalBuffers 时一次建好,但数据块等到首次
 *    真正使用时才分配——很多临时缓冲区可能永远用不到;
 * 2. 批量申请:一次向内存上下文申请 16 块起步、每轮翻倍的大块,然后
 *    逐块切给调用者。这样内存管理器只见到极少数的大请求,而不是几百
 *    个 8KB 小请求;本地缓冲区一经分配永不归还,单独管理小块毫无意义。
 * 所有块放在独立的 LocalBufferContext 中,便于在 MemoryContextStats
 * 里一眼看出临时表内存占了多少;并且按 PG_IO_ALIGN_SIZE 对齐,满足
 * 直接 I/O(AIO/io_uring)的对齐要求。
 *
 * 【参数】无。【返回值】新分配的页内存块(Block)。
 */
static Block
GetLocalBufferStorage(void)
{
	static char *cur_block = NULL;
	static int	next_buf_in_block = 0;
	static int	num_bufs_in_block = 0;
	static int	total_bufs_allocated = 0;
	static MemoryContext LocalBufferContext = NULL;

	char	   *this_buf;

	Assert(total_bufs_allocated < NLocBuffer);

	if (next_buf_in_block >= num_bufs_in_block)
	{
		/* Need to make a new request to memmgr */
		int			num_bufs;

		/*
		 * We allocate local buffers in a context of their own, so that the
		 * space eaten for them is easily recognizable in MemoryContextStats
		 * output.  Create the context on first use.
		 */
		if (LocalBufferContext == NULL)
			LocalBufferContext =
				AllocSetContextCreate(TopMemoryContext,
									  "LocalBufferContext",
									  ALLOCSET_DEFAULT_SIZES);

		/* Start with a 16-buffer request; subsequent ones double each time */
		num_bufs = Max(num_bufs_in_block * 2, 16);
		/* But not more than what we need for all remaining local bufs */
		num_bufs = Min(num_bufs, NLocBuffer - total_bufs_allocated);
		/* And don't overflow MaxAllocSize, either */
		num_bufs = Min(num_bufs, MaxAllocSize / BLCKSZ);

		/* Buffers should be I/O aligned. */
		cur_block = MemoryContextAllocAligned(LocalBufferContext,
											  num_bufs * BLCKSZ,
											  PG_IO_ALIGN_SIZE,
											  0);

		next_buf_in_block = 0;
		num_bufs_in_block = num_bufs;
	}

	/* Allocate next buffer in current memory block */
	this_buf = cur_block + next_buf_in_block * BLCKSZ;
	next_buf_in_block++;
	total_bufs_allocated++;

	/*
	 * Caller's PinLocalBuffer() was too early for Valgrind updates, so do it
	 * here.  The block is actually undefined, but we want consistency with
	 * the regular case of not needing to allocate memory.  This is
	 * specifically needed when method_io_uring.c fills the block, because
	 * Valgrind doesn't recognize io_uring reads causing undefined memory to
	 * become defined.
	 */
	VALGRIND_MAKE_MEM_DEFINED(this_buf, BLCKSZ);

	return (Block) this_buf;
}

/*
 * CheckForLocalBufferLeaks - ensure this backend holds no local buffer pins
 *
 * This is just like CheckForBufferLeaks(), but for local buffers.
 */
/* (中文)检查本后端是否残留本地缓冲区的 pin(泄漏检测)。
 * 仅断言构建(USE_ASSERT_CHECKING)下生效:逐个检查 LocalRefCount,
 * 对非 0 的打印 WARNING(用 DebugPrintBufferRefcount 生成可读信息),
 * 最后断言总数必须为 0。残留 pin 说明某条路径忘了 Unpin,
 * 属于编程错误。 */
static void
CheckForLocalBufferLeaks(void)
{
#ifdef USE_ASSERT_CHECKING
	if (LocalRefCount)
	{
		int			RefCountErrors = 0;
		int			i;

		for (i = 0; i < NLocBuffer; i++)
		{
			if (LocalRefCount[i] != 0)
			{
				Buffer		b = -i - 1;
				char	   *s;

				s = DebugPrintBufferRefcount(b);
				elog(WARNING, "local buffer refcount leak: %s", s);
				pfree(s);

				RefCountErrors++;
			}
		}
		Assert(RefCountErrors == 0);
	}
#endif
}

/*
 * AtEOXact_LocalBuffers - clean up at end of transaction.
 *
 * This is just like AtEOXact_Buffers, but for local buffers.
 */
/* (中文)事务结束钩子(AtEOXact_Buffers 的本地版):本后端每个事务
 * 提交/回滚时被调用,做泄漏检查(本地缓冲的 pin 必须随事务全部释放)。 */
void
AtEOXact_LocalBuffers(bool isCommit)
{
	CheckForLocalBufferLeaks();
}

/*
 * AtProcExit_LocalBuffers - ensure we have dropped pins during backend exit.
 *
 * This is just like AtProcExit_Buffers, but for local buffers.
 */
/* (中文)后端进程退出钩子(AtProcExit_Buffers 的本地版):确保退出时没有
 * 残留 pin。若仍有残留且断言未启用,后续 DropRelationBuffers 清理临时表
 * 时会暴露问题(这里提前检查并报告)。 */
void
AtProcExit_LocalBuffers(void)
{
	/*
	 * We shouldn't be holding any remaining pins; if we are, and assertions
	 * aren't enabled, we'll fail later in DropRelationBuffers while trying to
	 * drop the temp rels.
	 */
	CheckForLocalBufferLeaks();
}
