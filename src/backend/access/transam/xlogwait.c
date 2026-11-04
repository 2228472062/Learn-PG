/*-------------------------------------------------------------------------
 *
 * xlogwait.c
 *	  Implements waiting for WAL operations to reach specific LSNs.
 *
 * Copyright (c) 2025-2026, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *	  src/backend/access/transam/xlogwait.c
 *
 * NOTES
 *		This file implements waiting for WAL operations to reach specific LSNs
 *		on both physical standby and primary servers. The core idea is simple:
 *		every process that wants to wait publishes the LSN it needs to the
 *		shared memory, and the appropriate process (startup on standby,
 *		walreceiver on standby, or WAL writer/backend on primary) wakes it
 *		once that LSN has been reached.
 *
 *		The shared memory used by this module comprises a procInfos
 *		per-backend array with the information of the awaited LSN for each
 *		of the backend processes.  The elements of that array are organized
 *		into pairing heaps (waitersHeap), one for each WaitLSNType, which
 *		allows for very fast finding of the least awaited LSN for each type.
 *
 *		In addition, the least-awaited LSN for each type is cached in the
 *		minWaitedLSN array.  The waiter process publishes information about
 *		itself to the shared memory and waits on the latch until it is woken
 *		up by the appropriate process, standby is promoted, or the postmaster
 *		dies.  Then, it cleans information about itself in the shared memory.
 *
 *		On standby servers:
 *		- After replaying a WAL record, the startup process performs a fast
 *		  path check minWaitedLSN[REPLAY] > replayLSN.  If this check is
 *		  negative, it checks waitersHeap[REPLAY] and wakes up the backends
 *		  whose awaited LSNs are reached.
 *		- After receiving WAL, the walreceiver process performs similar checks
 *		  against the flush and write LSNs, waking up waiters in the FLUSH
 *		  and WRITE heaps, respectively.
 *
 *		On primary servers: After flushing WAL, the WAL writer or backend
 *		process performs a similar check against the flush LSN and wakes up
 *		waiters whose target flush LSNs have been reached.
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 的“等待 WAL 到达指定 LSN”机制（WAL wait facility），
 * 供 WAIT FOR 命令、REPACK 等需要确认 WAL 已经 write/flush/replay 到某个位置的
 * 功能使用。它同时支持主库（primary）和物理备库（standby）两种场景：
 *
 *   1. WAIT_LSN_TYPE_PRIMARY_FLUSH：在主库等待 WAL 已 flush 到目标 LSN，由
 *      WAL writer 或执行 WAL 写入的后端在完成 flush 后唤醒；
 *   2. WAIT_LSN_TYPE_STANDBY_WRITE：在备库等待 WAL 已写入本地 WAL 文件，由
 *      walreceiver 在 write 后唤醒；
 *   3. WAIT_LSN_TYPE_STANDBY_FLUSH：在备库等待 WAL 已 flush 到本地磁盘，由
 *      walreceiver 在 flush 后唤醒；
 *   4. WAIT_LSN_TYPE_STANDBY_REPLAY：在备库等待 WAL 已被 startup process 重放，
 *      由 startup process 每重放一条 WAL 记录后唤醒。
 *
 * 核心数据结构（定义在 access/xlogwait.h）：
 *   - WaitLSNProcInfo：每个进程一份的等待信息，包含 waitLSN、lsnType、procno、
 *     inHeap 以及 pairing heap 节点 heapNode；
 *   - WaitLSNState：共享内存中的全局状态，包含
 *       minWaitedLSN[WAIT_LSN_TYPE_COUNT]：每种类型当前最小等待 LSN 的原子缓存，
 *         用于 waker 侧的无锁快速路径判断；
 *       waitersHeap[WAIT_LSN_TYPE_COUNT]：每种类型一个按 LSN 排序的 pairing heap，
 *         堆顶是最小等待 LSN；
 *       procInfos[]：按 ProcNumber 索引的等待信息数组。
 *   全局指针 waitLSNState 指向这块共享内存，由 WaitLSNShmemCallbacks 注册和初始化。
 *
 * 并发协议：
 *   - 等待者调用 WaitForLSN()：在 WaitLSNLock 独占锁下把自身信息加入对应 heap，
 *     然后循环读取当前 LSN 并 WaitLatch() 睡眠；LSN 到达、超时、promotion 或
 *     postmaster 死亡时退出，并在锁保护下把自己从 heap 中删除。
 *   - 唤醒者（startup process / walreceiver / WAL writer / backend）在推进
 *     write/flush/replay 位置后调用 WaitLSNWakeup()：先读 minWaitedLSN 做快速
 *     路径过滤，仅在确实可能有等待者时才获取 WaitLSNLock，摘除 LSN 已到达的
 *     堆顶元素，释放锁后再逐个 SetLatch()，避免在锁内做昂贵的唤醒操作。
 *   - heap 和 procInfos 由 WaitLSNLock 保护；minWaitedLSN 使用带内存屏障的原子
 *     读写，与 heap 更新配对，保证 waker 一旦读到新的 minWaitedLSN，就能看到
 *     对应等待者已经发布的 heap 内容；而 WaitForLSN() “先登记、后检查”的顺序
 *     保证即使 waker 在这个窗口内没有看到新等待者，等待者也会自行发现 LSN 已
 *     到达，或者等待下一次 WAL 推进时的唤醒。
 *   - WaitLSNCleanup() 在事务/子事务 abort 以及进程退出时兜底清理，防止
 *     ERROR/取消打断 WaitForLSN() 后留下过期等待项。
 *
 * 设计思想：
 *   - 每个等待者只发布自己关心的 LSN，由“状态推进方”负责唤醒，等待者之间互不
 *     阻塞，也不需要轮询；
 *   - 每种等待类型独立建堆，唤醒者只处理与自己相关的类型，每次摘堆的代价与
 *     等待者数量成对数关系；
 *   - 用 minWaitedLSN 原子缓存把“没有等待者”这一最常见情况压缩为一次原子读，
 *     使 WAL 写入/重放热路径几乎不受影响；
 *   - 先用堆顶 LSN 与当前 LSN 比较，只有真正到达时才摘堆并 SetLatch，避免惊群；
 *   - promotion/recovery 结束时用 InvalidXLogRecPtr 调用 WaitLSNWakeup()，
 *     一次性唤醒全部 standby 等待者，让它们重新检查状态并返回错误或成功。
 */

#include "postgres.h"

#include <float.h>

#include "access/xlog.h"
#include "access/xlogrecovery.h"
#include "access/xlogwait.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "replication/walreceiver.h"
#include "storage/latch.h"
#include "storage/proc.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"
#include "utils/fmgrprotos.h"
#include "utils/pg_lsn.h"
#include "utils/snapmgr.h"
#include "utils/wait_event.h"


/*
 * 中文注释：
 * waitlsn_cmp 的前置声明。WaitLSNShmemInit() 在初始化 pairing heap 时需要把该
 * 比较函数作为参数传入，而它的定义在本文件后面，因此必须先声明。具体比较语义
 * 见函数定义处。
 */
static int	waitlsn_cmp(const pairingheap_node *a, const pairingheap_node *b,
						void *arg);

/*
 * 中文注释：
 * 指向共享内存中 WaitLSNState 的全局指针，是全部等待队列和每个进程等待信息的
 * 唯一访问入口。该变量初始为 NULL，由 shmem 框架在共享内存分配/挂接后、
 * 调用 init_fn 之前回填；在共享内存初始化完成前访问它是不安全的。
 * 各后端通过同一个指针访问同一份共享状态。字段的并发保护规则见文件头说明：
 * waitersHeap 和 procInfos 由 WaitLSNLock 保护，minWaitedLSN 用原子操作访问。
 */
struct WaitLSNState *waitLSNState = NULL;

/*
 * 中文注释：
 * 本模块两个 shmem 回调的前置声明，供下面的 WaitLSNShmemCallbacks 引用。
 * 具体行为见各自定义处。
 */
static void WaitLSNShmemRequest(void *arg);
static void WaitLSNShmemInit(void *arg);

/*
 * 中文注释：
 * 本模块注册给 shmem 子系统的回调集合（通过 storage/subsystemlist.h 中的
 * PG_SHMEM_SUBSYSTEM(WaitLSNShmemCallbacks) 引入）。
 * request_fn 在 postmaster 启动、共享内存尚未分配时登记 WaitLSNState 的大小和
 * 地址指针；init_fn 在共享内存分配完成后初始化原子变量、heap 和 procInfos。
 * 本模块没有 attach_fn：EXEC_BACKEND 模式下后端只需让 shmem 框架回填
 * waitLSNState 指针，不需要额外的挂接动作。
 */
const ShmemCallbacks WaitLSNShmemCallbacks = {
	.request_fn = WaitLSNShmemRequest,
	.init_fn = WaitLSNShmemInit,
};

/*
 * Wait event for each WaitLSNType, used with WaitLatch() to report
 * the wait in pg_stat_activity.
 */
/*
 * 中文注释：
 * 每种 WaitLSNType 对应的 wait event，传给 WaitLatch() 后可在 pg_stat_activity
 * 的 wait_event_type/wait_event 中看到等待原因。
 *   - standby_replay：等待 WAL 重放；
 *   - standby_write：等待 WAL 写入本地文件；
 *   - standby_flush 与 primary_flush：都等待 WAL flush 到磁盘，因此复用同一个
 *     WAIT_EVENT_WAIT_FOR_WAL_FLUSH 事件，只是等待发生的角色不同。
 * 数组使用指定初始化器（designated initializer）按枚举值定位，枚举顺序变化时
 * 不会错位；StaticAssertDecl 进一步保证数组长度与枚举值数量一致，新增枚举值
 * 时必须同步补充事件，否则编译失败。
 */
static const uint32 WaitLSNWaitEvents[] = {
	[WAIT_LSN_TYPE_STANDBY_REPLAY] = WAIT_EVENT_WAIT_FOR_WAL_REPLAY,
	[WAIT_LSN_TYPE_STANDBY_WRITE] = WAIT_EVENT_WAIT_FOR_WAL_WRITE,
	[WAIT_LSN_TYPE_STANDBY_FLUSH] = WAIT_EVENT_WAIT_FOR_WAL_FLUSH,
	[WAIT_LSN_TYPE_PRIMARY_FLUSH] = WAIT_EVENT_WAIT_FOR_WAL_FLUSH,
};

/*
 * 中文注释：
 * 编译期断言：WaitLSNWaitEvents 的元素个数必须等于 WaitLSNType 的取值数量。
 * 这是一个纯编译期检查，不产生运行时代码；若在枚举末尾新增等待类型而忘记添加
 * 对应的 wait event，数组长度与枚举数量不匹配会直接导致编译失败。若在枚举中间
 * 插入新值，长度可能仍然匹配，此时必须人工确认新类型也补上了自己的事件映射。
 */
StaticAssertDecl(lengthof(WaitLSNWaitEvents) == WAIT_LSN_TYPE_COUNT,
				 "WaitLSNWaitEvents must match WaitLSNType enum");

/*
 * Get the current LSN for the specified wait type.  Provide memory
 * barrier semantics before getting the value.
 */
/*
 * 中文注释：
 * 返回指定等待类型当前已经达到的 LSN，是 WaitForLSN() 循环中的判断依据。
 *
 * 参数 lsnType：等待类型，必须是 WaitLSNType 中的合法值。
 * 返回值：对应类型的当前 LSN：
 *   - WAIT_LSN_TYPE_STANDBY_REPLAY：GetXLogReplayRecPtr()，即 startup process
 *     最近重放到的位置；
 *   - WAIT_LSN_TYPE_STANDBY_WRITE：walreceiver 已写入本地 WAL 文件的位置，并以
 *     replay 位置为下界，即 Max(recptr, replay)。已经重放过的 WAL 必然已经在
 *     本地磁盘上（来自 base backup、归档恢复或之前的流复制），因此不需要再等
 *     walreceiver 重新接收；
 *   - WAIT_LSN_TYPE_STANDBY_FLUSH：walreceiver 已 flush 到磁盘的位置，同样以
 *     replay 位置为下界；
 *   - WAIT_LSN_TYPE_PRIMARY_FLUSH：GetFlushRecPtr()，即主库已 flush 的 WAL 位置。
 *
 * 内存序：本函数在返回前提供 memory barrier 语义（GetWalRcvWriteRecPtr() 和
 * GetFlushRecPtr() 内部有显式 barrier，GetXLogReplayRecPtr() 和
 * GetWalRcvFlushRecPtr() 使用 spinlock）。这与唤醒者发布新 LSN 的写操作配对，
 * 保证调用者看到新 LSN 时也能看到该 LSN 之前发布的共享状态，是 WaitForLSN()
 * 可以安全返回 SUCCESS 的前提。
 *
 * 非法类型会 elog(ERROR)；pg_unreachable() 告诉编译器 switch 已覆盖所有枚举值，
 * 不会继续执行到函数末尾。
 */
XLogRecPtr
GetCurrentLSNForWaitType(WaitLSNType lsnType)
{
	Assert(lsnType >= 0 && lsnType < WAIT_LSN_TYPE_COUNT);

	/*
	 * All of the cases below provide memory barrier semantics:
	 * GetWalRcvWriteRecPtr() and GetFlushRecPtr() have explicit barriers,
	 * while GetXLogReplayRecPtr() and GetWalRcvFlushRecPtr() use spinlocks.
	 */
	switch (lsnType)
	{
		case WAIT_LSN_TYPE_STANDBY_REPLAY:
			return GetXLogReplayRecPtr(NULL);

		case WAIT_LSN_TYPE_STANDBY_WRITE:
			{
				XLogRecPtr	recptr = GetWalRcvWriteRecPtr();
				XLogRecPtr	replay = GetXLogReplayRecPtr(NULL);

				/*
				 * Use the replay position as a floor.  WAL up to the replay
				 * point is already on disk from a base backup, archive
				 * restore, or prior streaming, so there is no reason to wait
				 * for the walreceiver to re-receive it.
				 */
				return Max(recptr, replay);
			}

		case WAIT_LSN_TYPE_STANDBY_FLUSH:
			{
				XLogRecPtr	recptr = GetWalRcvFlushRecPtr(NULL, NULL);
				XLogRecPtr	replay = GetXLogReplayRecPtr(NULL);

				/* Same floor as standby_write; see comment above. */
				return Max(recptr, replay);
			}

		case WAIT_LSN_TYPE_PRIMARY_FLUSH:
			return GetFlushRecPtr(NULL);
	}

	elog(ERROR, "invalid LSN wait type: %d", lsnType);
	pg_unreachable();
}

/* Register the shared memory space needed for WaitLSNState. */
/*
 * 中文注释：
 * shmem request 回调：在 postmaster 启动、共享内存尚未实际分配时，向 shmem 框架
 * 登记 WaitLSNState 所需的大小，以及用于接收分配地址的全局指针。
 *
 * 大小计算：offsetof(WaitLSNState, procInfos) 是结构体固定部分（minWaitedLSN 原子
 * 数组和 waitersHeap 数组）的大小，再加上 (MaxBackends + NUM_AUXILIARY_PROCS)
 * 个 WaitLSNProcInfo。必须把 NUM_AUXILIARY_PROCS 也计入，因为辅助进程同样有
 * ProcNumber，WaitForLSN() 用 procInfos[MyProcNumber] 定位自己的槽位；数组按
 * 最大可能的 ProcNumber 上界预留，避免越界。
 *
 * 参数 arg：shmem 框架传入的 opaque 参数，本模块不使用。
 * 并发/副作用：只在 postmaster 启动的单进程上下文中执行；函数不初始化任何字段，
 * 只登记需求，地址由 shmem 框架在分配后回填到 waitLSNState。
 */
static void
WaitLSNShmemRequest(void *arg)
{
	Size		size;

	size = offsetof(WaitLSNState, procInfos);
	size = add_size(size, mul_size(MaxBackends + NUM_AUXILIARY_PROCS, sizeof(WaitLSNProcInfo)));
	ShmemRequestStruct(.name = "WaitLSNState",
					   .size = size,
					   .ptr = (void **) &waitLSNState,
		);
}

/* Initialize the WaitLSNState in the shared memory. */
/*
 * 中文注释：
 * shmem init 回调：共享内存分配完成后初始化 WaitLSNState。
 *
 * 初始化内容：
 *   - 每种等待类型的 minWaitedLSN 设为 PG_UINT64_MAX，表示“当前没有等待者”。
 *     这个哨兵值使 WaitLSNWakeup() 的快速路径在空堆时直接返回，避免每次 WAL
 *     推进都去拿 WaitLSNLock；
 *   - 每种等待类型的 pairing heap 用 waitlsn_cmp 初始化，成为按 LSN 升序的
 *     min-heap（最小 LSN 在堆顶）；
 *   - procInfos 数组整体清零，使所有进程初始处于 inHeap=false 状态。
 *
 * 调用场景：postmaster 启动阶段、共享内存刚分配后调用一次。此时还没有其他后端
 * 运行，因此不需要持有 WaitLSNLock，也不存在并发访问。
 *
 * 参数 arg：shmem 框架传入的 opaque 参数，本模块不使用。
 * 副作用：只写共享内存初始化状态；不产生 WAL、不设置 latch。
 */
static void
WaitLSNShmemInit(void *arg)
{
	/* Initialize heaps and tracking */
	for (int i = 0; i < WAIT_LSN_TYPE_COUNT; i++)
	{
		pg_atomic_init_u64(&waitLSNState->minWaitedLSN[i], PG_UINT64_MAX);
		pairingheap_initialize(&waitLSNState->waitersHeap[i], waitlsn_cmp, NULL);
	}

	/* Initialize process info array */
	memset(&waitLSNState->procInfos, 0,
		   (MaxBackends + NUM_AUXILIARY_PROCS) * sizeof(WaitLSNProcInfo));
}

/*
 * Comparison function for LSN waiters heaps. Waiting processes are ordered by
 * LSN, so that the waiter with smallest LSN is at the top.
 */
/*
 * 中文注释：
 * waitersHeap 的比较函数，用于把等待者按 waitLSN 组织成 min-heap：waitLSN 越小
 * 优先级越高，堆顶就是所有等待者中最小的 LSN。
 *
 * PostgreSQL 的 pairingheap 对 min-heap 的约定是“比较条件反转”：a 的 waitLSN
 * 小于 b 时返回正值，大于时返回负值，相等返回 0。因此下面用
 * pairingheap_first() 取到的总是最小 LSN 对应的 WaitLSNProcInfo。
 *
 * 参数 a/b：指向 WaitLSNProcInfo 内部 heapNode 成员的节点指针，通过
 * pairingheap_const_container() 反推出所属的 WaitLSNProcInfo。
 * 参数 arg：pairingheap 传入的 opaque 参数，本模块不使用。
 * 并发：所有 heap 操作都在 WaitLSNLock 内进行，比较函数本身不再加锁。
 * 注意：LSN 是 64 位无符号值；相同 LSN 的等待者之间不规定顺序，但这不影响
 * 唤醒语义，因为它们的条件会同时满足。
 */
static int
waitlsn_cmp(const pairingheap_node *a, const pairingheap_node *b, void *arg)
{
	const WaitLSNProcInfo *aproc = pairingheap_const_container(WaitLSNProcInfo, heapNode, a);
	const WaitLSNProcInfo *bproc = pairingheap_const_container(WaitLSNProcInfo, heapNode, b);

	if (aproc->waitLSN < bproc->waitLSN)
		return 1;
	else if (aproc->waitLSN > bproc->waitLSN)
		return -1;
	else
		return 0;
}

/*
 * Update minimum waited LSN for the specified LSN type
 */
/*
 * 中文注释：
 * 重新计算并发布指定类型的 minWaitedLSN 缓存值。
 *
 * 逻辑：若对应 heap 非空，取堆顶元素的 waitLSN；否则写入 PG_UINT64_MAX，
 * 表示“无人等待”。随后用 pg_atomic_write_membarrier_u64() 把结果发布到共享
 * 内存，供 WaitLSNWakeup() 无锁读取。
 *
 * 调用场景：addLSNWaiter()、deleteLSNWaiter() 和 wakeupWaiters() 修改 heap
 * 之后调用。调用者必须已经持有 WaitLSNLock 独占锁；本函数自己不再加锁。
 *
 * 并发/内存序：写侧的 membarrier 与 WaitLSNWakeup() 中的
 * pg_atomic_read_membarrier_u64() 配对。这保证 waker 若读到新的、更小的
 * minWaitedLSN，就一定能看到对应等待者写入 heap 的 WaitLSNProcInfo 内容；
 * 反过来，若 waker 读到 PG_UINT64_MAX 或大于 currentLSN 的值，就可以安全地
 * 跳过加锁。该值只是快速路径提示，不是正确性依据：真正的摘堆操作仍会在锁内
 * 重新检查堆顶 LSN。
 *
 * 参数 lsnType：等待类型，函数内断言其索引合法。
 */
static void
updateMinWaitedLSN(WaitLSNType lsnType)
{
	XLogRecPtr	minWaitedLSN = PG_UINT64_MAX;
	int			i = (int) lsnType;

	Assert(i >= 0 && i < WAIT_LSN_TYPE_COUNT);

	if (!pairingheap_is_empty(&waitLSNState->waitersHeap[i]))
	{
		pairingheap_node *node = pairingheap_first(&waitLSNState->waitersHeap[i]);
		WaitLSNProcInfo *procInfo = pairingheap_container(WaitLSNProcInfo, heapNode, node);

		minWaitedLSN = procInfo->waitLSN;
	}
	/* Pairs with pg_atomic_read_membarrier_u64() in WaitLSNWakeup(). */
	pg_atomic_write_membarrier_u64(&waitLSNState->minWaitedLSN[i], minWaitedLSN);
}

/*
 * Add current process to appropriate waiters heap based on LSN type
 */
/*
 * 中文注释：
 * 把当前进程登记为指定类型的 LSN 等待者，并插入对应的 waitersHeap。
 *
 * 参数：
 *   lsn：本进程要等待的目标 LSN；
 *   lsnType：等待类型，决定插入哪个 heap，也决定之后由谁负责唤醒。
 *
 * 关键步骤（全部在 WaitLSNLock 独占锁内完成）：
 *   1. 用 MyProcNumber 定位 procInfos[MyProcNumber]，写入 procno、waitLSN、
 *      lsnType；
 *   2. 断言该进程当前不在 heap 中：一个进程同一时刻只能等待一个 LSN 类型；
 *   3. pairingheap_add() 插入 heap，并置 inHeap=true；
 *   4. 调用 updateMinWaitedLSN() 刷新快速路径缓存。
 *
 * 并发注意事项：必须在 WaitForLSN() 第一次检查目标 LSN 之前调用。如果目标 LSN
 * 在登记之前已经到达，WaitForLSN() 循环开头的检查会立即发现并删除自己，不会
 * 永久睡眠；反之，若先检查再登记，就可能错过唤醒并一直睡到超时。
 *
 * 副作用：修改共享内存中的 procInfos 和 waitersHeap；不设置 latch。
 */
static void
addLSNWaiter(XLogRecPtr lsn, WaitLSNType lsnType)
{
	WaitLSNProcInfo *procInfo = &waitLSNState->procInfos[MyProcNumber];
	int			i = (int) lsnType;

	Assert(i >= 0 && i < WAIT_LSN_TYPE_COUNT);

	LWLockAcquire(WaitLSNLock, LW_EXCLUSIVE);

	procInfo->procno = MyProcNumber;
	procInfo->waitLSN = lsn;
	procInfo->lsnType = lsnType;

	Assert(!procInfo->inHeap);
	pairingheap_add(&waitLSNState->waitersHeap[i], &procInfo->heapNode);
	procInfo->inHeap = true;
	updateMinWaitedLSN(lsnType);

	LWLockRelease(WaitLSNLock);
}

/*
 * Remove current process from appropriate waiters heap based on LSN type
 */
/*
 * 中文注释：
 * 把当前进程从指定类型的 waitersHeap 中删除，是 addLSNWaiter() 的逆操作。
 *
 * 参数 lsnType：等待类型，必须与登记时的类型一致，函数内用 Assert 校验。
 * 并发：在 WaitLSNLock 独占锁内检查 inHeap，只有仍留在 heap 中时才调用
 * pairingheap_remove()，并在删除后刷新 minWaitedLSN。
 *
 * 幂等性/竞争：唤醒者 wakeupWaiters() 可能已经先一步把该进程从 heap 中摘除并
 * 把 inHeap 置为 false；此时本函数什么也不做，避免二次删除破坏 heap。正因如此，
 * WaitForLSN() 的正常退出路径和 WaitLSNCleanup() 的兜底清理可以安全地重复调用。
 *
 * 注意：删除后不重置 waitLSN/lsnType 字段；它们会在下一次 addLSNWaiter() 时被
 * 覆盖，残留值本身不影响正确性。
 */
static void
deleteLSNWaiter(WaitLSNType lsnType)
{
	WaitLSNProcInfo *procInfo = &waitLSNState->procInfos[MyProcNumber];
	int			i = (int) lsnType;

	Assert(i >= 0 && i < WAIT_LSN_TYPE_COUNT);

	LWLockAcquire(WaitLSNLock, LW_EXCLUSIVE);

	Assert(procInfo->lsnType == lsnType);

	if (procInfo->inHeap)
	{
		pairingheap_remove(&waitLSNState->waitersHeap[i], &procInfo->heapNode);
		procInfo->inHeap = false;
		updateMinWaitedLSN(lsnType);
	}

	LWLockRelease(WaitLSNLock);
}

/*
 * Size of a static array of procs to wakeup by WaitLSNWakeup() allocated
 * on the stack.  It should be enough to take single iteration for most cases.
 */
/*
 * 中文注释：
 * wakeupWaiters() 在栈上一次性收集的待唤醒进程号数量上限。取 16 是为了让
 * 绝大多数场景（通常只有少量等待者）一次循环就完成，避免动态内存分配。
 * 若等待者超过 16 个，则分批处理：每批摘除 16 个、释放锁、在锁外 SetLatch，
 * 然后重新加锁继续，直到堆中没有已到达的等待者。分批可以缩短单次持有
 * WaitLSNLock 的时间，减少对 WAL 写入/重放热路径的影响。
 */
#define	WAKEUP_PROC_STATIC_ARRAY_SIZE (16)

/*
 * Remove waiters whose LSN has been reached from the heap and set their
 * latches.  If InvalidXLogRecPtr is given, remove all waiters from the heap
 * and set latches for all waiters.
 *
 * This function first accumulates waiters to wake up into an array, then
 * wakes them up without holding a WaitLSNLock.  The array size is static and
 * equal to WAKEUP_PROC_STATIC_ARRAY_SIZE.  That should be more than enough
 * to wake up all the waiters at once in the vast majority of cases.  However,
 * if there are more waiters, this function will loop to process them in
 * multiple chunks.
 */
/*
 * 中文注释：
 * 唤醒指定类型中目标 LSN 已经到达的等待者；若 currentLSN 为
 * InvalidXLogRecPtr，则唤醒该类型的所有等待者。
 *
 * 工作流程（do-while 分批）：
 *   1. 获取 WaitLSNLock 独占锁，反复查看堆顶：只要堆非空且
 *      （currentLSN 无效 或 堆顶 waitLSN <= currentLSN），就记录其 procno、
 *      pairingheap_remove_first() 摘堆、置 inHeap=false，直到遇到尚未到达的
 *      LSN、堆为空，或已收集满 WAKEUP_PROC_STATIC_ARRAY_SIZE 个；
 *   2. 刷新 minWaitedLSN，释放锁；
 *   3. 在锁外对收集到的 ProcNumber 调用 SetLatch()。SetLatch() 相对昂贵，
 *      放在锁外可以显著缩短临界区；
 *   4. 如果本批恰好装满，说明可能还有更多等待者，重新循环。
 *
 * 参数：
 *   lsnType：等待类型，决定操作哪个 heap；
 *   currentLSN：当前已达到的 LSN，或 InvalidXLogRecPtr 表示“全部唤醒”。
 *
 * 并发/安全性：SetLatch() 时不持有 WaitLSNLock，也不保证目标进程仍然是原来的
 * 等待者。procLatch 在 PGPROC 生命周期内不会被释放，因此最坏情况是给错误的
 * 进程或无人使用的槽位设置 latch；错误进程只会多做一次无意义唤醒并重新检查
 * 条件，不会造成内存安全问题。真正的正确性由等待者循环中重新读取 LSN 保证：
 * 即使发生误发，等待者也会在下一轮检查时重新确认条件。此外，latch 具有 sticky
 * 语义：若 SetLatch() 发生在 WaitLatch() 之前，等待者也不会丢失这次唤醒。
 *
 * 注意：循环条件用 numWakeUpProcs == WAKEUP_PROC_STATIC_ARRAY_SIZE 判断。
 * 如果恰好摘满一批但堆已空，会多做一次空的加锁/刷新/解锁迭代，这是无害的。
 */
static void
wakeupWaiters(WaitLSNType lsnType, XLogRecPtr currentLSN)
{
	ProcNumber	wakeUpProcs[WAKEUP_PROC_STATIC_ARRAY_SIZE];
	int			numWakeUpProcs;
	int			i = (int) lsnType;

	Assert(i >= 0 && i < WAIT_LSN_TYPE_COUNT);

	do
	{
		int			j;

		numWakeUpProcs = 0;
		LWLockAcquire(WaitLSNLock, LW_EXCLUSIVE);

		/*
		 * Iterate the waiters heap until we find LSN not yet reached. Record
		 * process numbers to wake up, but send wakeups after releasing lock.
		 */
		while (!pairingheap_is_empty(&waitLSNState->waitersHeap[i]))
		{
			pairingheap_node *node = pairingheap_first(&waitLSNState->waitersHeap[i]);
			WaitLSNProcInfo *procInfo;

			/* Get procInfo using appropriate heap node */
			procInfo = pairingheap_container(WaitLSNProcInfo, heapNode, node);

			if (XLogRecPtrIsValid(currentLSN) && procInfo->waitLSN > currentLSN)
				break;

			Assert(numWakeUpProcs < WAKEUP_PROC_STATIC_ARRAY_SIZE);
			wakeUpProcs[numWakeUpProcs++] = procInfo->procno;
			(void) pairingheap_remove_first(&waitLSNState->waitersHeap[i]);

			/* Update appropriate flag */
			procInfo->inHeap = false;

			if (numWakeUpProcs == WAKEUP_PROC_STATIC_ARRAY_SIZE)
				break;
		}

		updateMinWaitedLSN(lsnType);
		LWLockRelease(WaitLSNLock);

		/*
		 * Set latches for processes whose waited LSNs have been reached.
		 * Since SetLatch() is a time-consuming operation, we do this outside
		 * of WaitLSNLock. This is safe because procLatch is never freed, so
		 * at worst we may set a latch for the wrong process or for no process
		 * at all, which is harmless.
		 */
		for (j = 0; j < numWakeUpProcs; j++)
			SetLatch(&GetPGProcByNumber(wakeUpProcs[j])->procLatch);

	} while (numWakeUpProcs == WAKEUP_PROC_STATIC_ARRAY_SIZE);
}

/*
 * Wake up processes waiting for LSN to reach currentLSN
 */
/*
 * 中文注释：
 * WAL 推进方提供给外部的唤醒入口：当某种 WAL 操作推进到 currentLSN 时调用，
 * 唤醒所有目标 LSN 已经到达的等待者。
 *
 * 调用场景：
 *   - startup process 每重放一条 WAL 记录后，对 STANDBY_REPLAY/WRITE/FLUSH
 *     调用（replay 位置同时意味着这些 WAL 已经被 write 和 flush）；
 *   - walreceiver 写完 WAL 后对 STANDBY_WRITE、flush 后对 STANDBY_FLUSH 调用；
 *   - 主库 WAL writer 或后端完成 flush 后对 PRIMARY_FLUSH 调用；
 *   - recovery 结束/promotion 时用 InvalidXLogRecPtr 调用 standby 类型，
 *     唤醒所有等待者，让它们返回 NOT_IN_RECOVERY 或 SUCCESS。
 *
 * 参数：
 *   lsnType：等待类型，函数内断言其合法；
 *   currentLSN：当前已达到的 LSN；InvalidXLogRecPtr 表示唤醒该类型全部等待者。
 *
 * 快速路径：若 currentLSN 有效，并且原子读到的 minWaitedLSN 大于 currentLSN，
 * 说明没有等待者关心这个位置，直接返回，不获取 WaitLSNLock。该检查与
 * updateMinWaitedLSN() 的 membarrier 写配对。它只是优化：即使读到略旧的值而
 * 误判为“可能有等待者”，wakeupWaiters() 也会在锁内重新检查堆顶，不会误唤醒
 * 尚未到达的等待者。
 *
 * 设计思想：本函数位于 WAL 写入/重放热路径，必须尽可能廉价；加锁和 SetLatch
 * 都推迟到确实存在等待者时才做。
 */
void
WaitLSNWakeup(WaitLSNType lsnType, XLogRecPtr currentLSN)
{
	int			i = (int) lsnType;

	Assert(i >= 0 && i < WAIT_LSN_TYPE_COUNT);

	/*
	 * Fast path check.  Skip if currentLSN is InvalidXLogRecPtr, which means
	 * "wake all waiters" (e.g., during promotion when recovery ends). Pairs
	 * with pg_atomic_write_membarrier_u64() in updateMinWaitedLSN().
	 */
	if (XLogRecPtrIsValid(currentLSN) &&
		pg_atomic_read_membarrier_u64(&waitLSNState->minWaitedLSN[i]) > currentLSN)
		return;

	wakeupWaiters(lsnType, currentLSN);
}

/*
 * Clean up any LSN wait state for the current process.
 */
/*
 * 中文注释：
 * 兜底清理当前进程可能残留的 LSN 等待状态。当 WaitForLSN() 因 ERROR、查询取消
 * 或进程退出而没有走到正常删除路径时，由事务/子事务 abort 清理和 ProcKill()
 * 调用本函数，避免共享内存 heap 中留下永远不会被唤醒的僵尸项。
 *
 * 调用场景：AbortTransaction()、AbortSubTransaction() 以及 ProcKill()。
 * 返回值：无。
 *
 * 并发细节：先无锁读取 procInfos[MyProcNumber].inHeap 做快速路径判断。inHeap
 * 只会由本进程置为 true，唤醒者或其他清理路径只会置为 false，因此无锁读最多
 * 得到“假阳性”（读到过期的 true），随后 deleteLSNWaiter() 会在 WaitLSNLock 内
 * 重新检查并安全地不做任何事。反过来，若读到 false，则说明唤醒者已经摘除该项
 * （或本进程自己的删除已经完成），可以放心跳过；true 只可能由本进程在锁内设置，
 * 正常路径下不会出现“实际仍在 heap 中却读不到 true”的漏删。
 *
 * 注意：waitLSNState 可能尚未初始化（例如共享内存初始化前的极早期错误路径），
 * 因此先判断指针非空。
 */
void
WaitLSNCleanup(void)
{
	if (waitLSNState)
	{
		/*
		 * We do a fast-path check of the inHeap flag without the lock.  This
		 * flag is set to true only by the process itself.  So, it's only
		 * possible to get a false positive.  But that will be eliminated by a
		 * recheck inside deleteLSNWaiter().
		 */
		if (waitLSNState->procInfos[MyProcNumber].inHeap)
			deleteLSNWaiter(waitLSNState->procInfos[MyProcNumber].lsnType);
	}
}

/*
 * Check if the given LSN type requires recovery to be in progress.
 * Standby wait types (replay, write, flush) require recovery;
 * primary wait types (flush) do not.
 */
/*
 * 中文注释：
 * 判断给定等待类型是否依赖 recovery 正在进行。standby 的 replay/write/flush
 * 三种类型都只能在备库恢复期间等待；primary_flush 在主库使用，不要求 recovery。
 *
 * 用途：WaitForLSN() 每轮循环据此决定是否检查 RecoveryInProgress()。如果 recovery
 * 在等待期间结束（promotion 或恢复完成），standby 等待者必须尽快醒来并返回
 * WAIT_LSN_RESULT_NOT_IN_RECOVERY，而不是继续等一个可能永远不会再推进的 LSN。
 *
 * 参数 t：等待类型。返回 true 表示需要 recovery，false 表示不需要。
 * 声明为 static inline，避免在 WaitForLSN() 的热循环中引入函数调用开销。
 */
static inline bool
WaitLSNTypeRequiresRecovery(WaitLSNType t)
{
	return t == WAIT_LSN_TYPE_STANDBY_REPLAY ||
		t == WAIT_LSN_TYPE_STANDBY_WRITE ||
		t == WAIT_LSN_TYPE_STANDBY_FLUSH;
}

/*
 * Wait using MyLatch till the given LSN is reached, the replica gets
 * promoted, or the postmaster dies.
 *
 * Returns WAIT_LSN_RESULT_SUCCESS if target LSN was reached.
 * Returns WAIT_LSN_RESULT_NOT_IN_RECOVERY if run not in recovery,
 * or replica got promoted before the target LSN reached.
 */
/*
 * 中文注释：
 * 等待指定类型的 WAL 操作推进到 targetLSN，是上层 SQL 命令 WAIT FOR 以及
 * REPACK 等功能的公共入口。
 *
 * 参数：
 *   lsnType：等待类型，决定等待目标（replay/write/flush）和唤醒来源；
 *   targetLSN：目标 LSN；
 *   timeout：超时时间，单位毫秒；<= 0 表示无限等待，不启用 WL_TIMEOUT。
 *
 * 返回值（WaitLSNResult）：
 *   - WAIT_LSN_RESULT_SUCCESS：目标 LSN 已到达；若在 promotion 过程中 recovery
 *     结束但目标已经达到，也返回 SUCCESS；
 *   - WAIT_LSN_RESULT_TIMEOUT：超时且目标尚未到达；
 *   - WAIT_LSN_RESULT_NOT_IN_RECOVERY：等待期间 recovery 结束，并且不是
 *     “promotion 后目标已达到”的情况，典型于备库被提升或恢复提前结束。
 *
 * 执行流程：
 *   1. 断言共享内存已初始化、MyProcNumber 在 procInfos 数组范围内；
 *   2. 若 timeout > 0，计算绝对截止时间 endtime，并把 WL_TIMEOUT 加入唤醒事件；
 *   3. addLSNWaiter() 先登记自己，再进入循环。先登记后检查可以避免“目标 LSN
 *      在检查之后、登记之前到达”导致永久睡眠；
 *   4. 每轮读取当前 LSN：
 *        - standby 类型且 RecoveryInProgress() 为 false：删除自己；若 promotion
 *          已触发且 targetLSN <= currentLSN，返回 SUCCESS，否则返回
 *          NOT_IN_RECOVERY；
 *        - 否则若 targetLSN <= currentLSN，跳出循环；
 *   5. 若 timeout > 0，计算距 endtime 的剩余毫秒数；若已到期则跳出循环，
 *      循环外根据 targetLSN > currentLSN 返回 TIMEOUT；
 *   6. CHECK_FOR_INTERRUPTS() 允许查询取消等中断；
 *   7. WaitLatch(MyLatch, latch_set/postmaster_death[/timeout], delay_ms,
 *      wait event) 睡眠，等待原因会显示在 pg_stat_activity 中；若检测到
 *      postmaster 死亡则 FATAL 退出；否则 ResetLatch() 后继续循环。
 *
 * 并发与唤醒协议：等待者可能已被唤醒者提前从 heap 中摘除（inHeap=false），
 * 因此正常退出时 deleteLSNWaiter() 必须容忍“已经被删除”；反之，若等待者先被
 * latch 唤醒并自行删除，唤醒者随后的 SetLatch() 也只会造成一次多余唤醒。两种
 * 顺序都是安全的。
 *
 * 中断/副作用：CHECK_FOR_INTERRUPTS() 或 FATAL 可能使函数非正常返回，此时共享
 * 内存中的登记项由 AbortTransaction()/AbortSubTransaction()/ProcKill() 调用
 * WaitLSNCleanup() 兜底清除。函数本身不修改 WAL 状态，只读写等待队列和当前进程
 * 的 latch。
 *
 * 注意：超时判断使用本轮循环开头读取的 currentLSN。若目标 LSN 恰好在超时边界
 * 到达，可能返回 TIMEOUT 而不是 SUCCESS，这是超时语义允许的竞争结果；调用方
 * （如 WAIT FOR）会据此报告超时。
 */
WaitLSNResult
WaitForLSN(WaitLSNType lsnType, XLogRecPtr targetLSN, int64 timeout)
{
	XLogRecPtr	currentLSN;
	TimestampTz endtime = 0;
	int			wake_events = WL_LATCH_SET | WL_POSTMASTER_DEATH;

	/* Shouldn't be called when shmem isn't initialized */
	Assert(waitLSNState);

	/* Should have a valid proc number */
	Assert(MyProcNumber >= 0 && MyProcNumber < MaxBackends + NUM_AUXILIARY_PROCS);

	if (timeout > 0)
	{
		endtime = TimestampTzPlusMilliseconds(GetCurrentTimestamp(), timeout);
		wake_events |= WL_TIMEOUT;
	}

	/*
	 * Add our process to the waiters heap.  It might happen that target LSN
	 * gets reached before we do.  The check at the beginning of the loop
	 * below prevents the race condition.
	 */
	addLSNWaiter(targetLSN, lsnType);

	for (;;)
	{
		int			rc;
		long		delay_ms = -1;

		/* Get current LSN for the wait type */
		currentLSN = GetCurrentLSNForWaitType(lsnType);

		/* Check that recovery is still in-progress */
		if (WaitLSNTypeRequiresRecovery(lsnType) && !RecoveryInProgress())
		{
			/*
			 * Recovery was ended, but check if target LSN was already
			 * reached.
			 */
			deleteLSNWaiter(lsnType);

			if (PromoteIsTriggered() && targetLSN <= currentLSN)
				return WAIT_LSN_RESULT_SUCCESS;
			return WAIT_LSN_RESULT_NOT_IN_RECOVERY;
		}
		else
		{
			/* Check if the waited LSN has been reached */
			if (targetLSN <= currentLSN)
				break;
		}

		if (timeout > 0)
		{
			delay_ms = TimestampDifferenceMilliseconds(GetCurrentTimestamp(), endtime);
			if (delay_ms <= 0)
				break;
		}

		CHECK_FOR_INTERRUPTS();

		rc = WaitLatch(MyLatch, wake_events, delay_ms,
					   WaitLSNWaitEvents[lsnType]);

		/*
		 * Emergency bailout if postmaster has died.  This is to avoid the
		 * necessity for manual cleanup of all postmaster children.
		 */
		if (rc & WL_POSTMASTER_DEATH)
			ereport(FATAL,
					errcode(ERRCODE_ADMIN_SHUTDOWN),
					errmsg("terminating connection due to unexpected postmaster exit"),
					errcontext("while waiting for LSN"));

		ResetLatch(MyLatch);
	}

	/*
	 * Delete our process from the shared memory heap.  We might already be
	 * deleted by the startup process.  The 'inHeap' flags prevents us from
	 * the double deletion.
	 */
	deleteLSNWaiter(lsnType);

	/*
	 * If we didn't reach the target LSN, we must be exited by timeout.
	 */
	if (targetLSN > currentLSN)
		return WAIT_LSN_RESULT_TIMEOUT;

	return WAIT_LSN_RESULT_SUCCESS;
}
