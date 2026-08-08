/*-------------------------------------------------------------------------
 *
 * proc.c
 *	  routines to manage per-process shared memory data structure
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/lmgr/proc.c
 *
 * 【模块总览(中文)】
 * 本文件负责管理 PostgreSQL 的"进程表"——共享内存中每个后端/辅助进程/
 * prepared 事务对应的 PGPROC 结构(以及配套的 PROC_HDR 表头)。PGPROC 是
 * 整个锁系统与并发控制的中枢:它记录进程的虚拟事务号(VXID)、正在等待的
 * 重锁(waitLock/waitLockMode/waitStatus)、LWLock 等待状态(lwWaiting/
 * lwWaitMode)、每进程的 latch(procLatch,用于被其他进程唤醒)与信号量
 * (sem,用于 LWLock 睡眠)、fast-path 锁槽(fpLockBits/fpRelId)、锁组
 * 关系(lockGroupLeader)、同步复制与日志回收等状态,并被 ProcArray
 * (procarray.c)、procsignal、wait_event 统计等模块广泛引用。
 *
 * 【核心数据结构】
 * - PROC_HDR(ProcGlobal):进程表头。包含全部 PGPROC 的指针 allProcs、
 *   按角色划分的空闲链表(freeProcs/autovacFreeProcs/bgworkerFreeProcs/
 *   walsenderFreeProcs)、与 PGPROC 字段紧凑镜像的数组 xids/
 *   subxidStates/statusFlags,以及各辅助进程的 ProcNumber 广告位
 *   (avLauncherProc/walwriterProc/checkpointerProc);
 * - PGPROC:共享内存数组中的单进程条目。辅助进程使用固定预留的
 *   AuxiliaryProcs 区段,prepared 事务使用 PreparedXactProcs 区段,
 *   普通后端/自动清理/后台工作者/walsender 分别从各自的空闲链表摘取。
 *
 * 【设计思想】
 * 1. 预先分配:PGPROC 数组与每进程信号量在 postmaster 启动时按
 *    max_connections 等 GUC 上限一次性创建(ProcGlobalShmemInit),既满足
 *    "信号量须在 postmaster 中创建"的实现约束,也让"配置超出内核限制"
 *    尽早暴露,而不是负载高企时才开始失败;
 * 2. 按角色隔离的空闲链表:不同角色的进程从不同链表取 PGPROC,使
 *    "连接数超限"与"walsender 超限"等错误互不干扰;
 * 3. 等锁睡眠:重锁获取失败后,lock.c 调用本文件的 JoinWaitQueue/
 *    ProcSleep 把进程挂入锁的等待队列并睡眠(latch 唤醒),配合
 *    deadlock_timeout 定时器触发 CheckDeadLock 死锁检测;
 * 4. 退出清理:进程退出时 ProcKill 归还 PGPROC、清理 latch 所有权与
 *    锁组关系,持有的 LWLock 由 LWLockReleaseAll 兜底释放;
 * 5. 中断安全:等锁期间通过 WaitLatch + CHECK_FOR_INTERRUPTS 及时响应
 *    取消/死锁超时;LockErrorCleanup 保证出错时把进程从等待队列摘除。
 *
 * 与 lwlock.c 的关系:LWLock 的睡眠/唤醒使用 PGPROC 的 sem 信号量与
 * lwWaiting 状态;与 lock.c/deadlock.c 的协作见 ProcSleep/CheckDeadLock
 * 的注释。
 *
 *-------------------------------------------------------------------------
 */
/*
 * Interface (a):
 *		JoinWaitQueue(), ProcSleep(), ProcWakeup()
 *
 * Waiting for a lock causes the backend to be put to sleep.  Whoever releases
 * the lock wakes the process up again (and gives it an error code so it knows
 * whether it was awoken on an error condition).
 *
 * Interface (b):
 *
 * ProcReleaseLocks -- frees the locks associated with current transaction
 *
 * ProcKill -- destroys the shared memory state (and locks)
 * associated with the process.
 */
#include "postgres.h"

#include <signal.h>
#include <unistd.h>
#include <sys/time.h>

#include "access/clog.h"
#include "access/transam.h"
#include "access/twophase.h"
#include "access/xlogutils.h"
#include "access/xlogwait.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "postmaster/autovacuum.h"
#include "replication/slotsync.h"
#include "replication/syncrep.h"
#include "storage/condition_variable.h"
#include "storage/ipc.h"
#include "storage/lmgr.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "storage/procsignal.h"
#include "storage/spin.h"
#include "storage/standby.h"
#include "storage/subsystems.h"
#include "utils/injection_point.h"
#include "utils/timeout.h"
#include "utils/timestamp.h"
#include "utils/wait_event.h"

/* GUC variables */
/* (中文)本文件相关的 GUC 配置项(用户可在 postgresql.conf 中设置):
 * - DeadlockTimeout:等锁超过该毫秒数后触发死锁检测(见 ProcSleep/
 *   CheckDeadLock);
 * - StatementTimeout / LockTimeout / IdleInTransactionSessionTimeout /
 *   TransactionTimeout / IdleSessionTimeout:各类超时,LockTimeout 用于
 *   等锁超时(与 DeadlockTimeout 在同一定时器框架中启用);
 * - log_lock_waits:为 true 时,等待超过 DeadlockTimeout 的锁等待会写入
 *   服务器日志(见 ProcSleep 中的日志逻辑)。 */
int			DeadlockTimeout = 1000;
int			StatementTimeout = 0;
int			LockTimeout = 0;
int			IdleInTransactionSessionTimeout = 0;
int			TransactionTimeout = 0;
int			IdleSessionTimeout = 0;
bool		log_lock_waits = true;

/* (中文)本进程自己的 PGPROC 指针:InitProcess/InitAuxiliaryProcess 成功
 * 后非 NULL;为 NULL 时表示尚无 PGPROC(如共享内存初始化早期),此时
 * 不能睡眠等待 LWLock。进程退出清理(ProcKill/AuxiliaryProcKill)会把它
 * 置回 NULL。 */
/* Pointer to this process's PGPROC struct, if any */
PGPROC	   *MyProc = NULL;

/* (中文)指向共享内存结构的指针:
 * - ProcGlobal(PROC_HDR):进程表头,postmaster 启动时建立,各进程继承;
 * - AllProcsShmemPtr / FastPathLockArrayShmemPtr:分别指向"PGPROC 大块
 *   内存(PGPROC 数组 + xids 等镜像数组)"与"fast-path 锁数组"共享内存
 *   的基址,仅用于 ProcGlobalShmemInit 中的切片初始化;
 * - AuxiliaryProcs:固定预留给辅助进程(bgwriter、checkpointer 等)的
 *   PGPROC 区段(共 NUM_AUXILIARY_PROCS 个);
 * - PreparedXactProcs:预留给 prepared(两阶段)事务"虚拟进程"的 PGPROC
 *   区段。 */
/* Pointers to shared-memory structures */
PROC_HDR   *ProcGlobal = NULL;
static void *AllProcsShmemPtr;
static void *FastPathLockArrayShmemPtr;
NON_EXEC_STATIC PGPROC *AuxiliaryProcs = NULL;
PGPROC	   *PreparedXactProcs = NULL;

static void ProcGlobalShmemRequest(void *arg);
static void ProcGlobalShmemInit(void *arg);

/* (中文)向共享内存子系统注册的 request/init 回调对:request 阶段
 * (ProcGlobalShmemRequest)声明进程表所需字节数并让信号量实现登记其
 * 共享需求;init 阶段(ProcGlobalShmemInit)完成表头初始化、PGPROC
 * 区段切片与全部信号量创建。 */
const ShmemCallbacks ProcGlobalShmemCallbacks = {
	.request_fn = ProcGlobalShmemRequest,
	.init_fn = ProcGlobalShmemInit,
};

/* (中文)静态辅助量(见各使用处):
 * - TotalProcs:PGPROC 总数(MaxBackends + 辅助进程数 + prepared 事务数);
 * - ProcGlobalAllProcsShmemSize:PGPROC 及其镜像数组所需总字节数;
 * - FastPathLockArrayShmemSize:fast-path 锁数组所需总字节数。 */
static uint32 TotalProcs;
static size_t ProcGlobalAllProcsShmemSize;
static size_t FastPathLockArrayShmemSize;

/* (中文)死锁检测超时(deadlock_timeout)触发标志:由信号处理函数
 * CheckDeadLockAlert 置位,ProcSleep 的等待循环里轮询该标志后调用
 * CheckDeadLock() 做真正的检测(检测不能在信号处理器里做)。
 * sig_atomic_t 保证信号处理器中的写入在主执行流中原子可见。 */
/* Is a deadlock check pending? */
static volatile sig_atomic_t got_deadlock_timeout;

/* (中文)静态函数前置声明(实现见后文):
 * - RemoveProcFromArray:进程退出时把本进程从共享 ProcArray 中移除;
 * - ProcKill / AuxiliaryProcKill:普通/辅助进程的退出清理回调;
 * - CheckDeadLock:实际的死锁检测(锁表全分区加排他锁后调用
 *   DeadLockCheck)。 */
static void RemoveProcFromArray(int code, Datum arg);
static void ProcKill(int code, Datum arg);
static void AuxiliaryProcKill(int code, Datum arg);
static DeadLockState CheckDeadLock(void);


/*
 * Calculate shared-memory space needed by Fast-Path locks.
 */
/* (中文)计算 fast-path 锁数组所需的共享内存字节数。
 *
 * 【作用】仅被 ProcGlobalShmemRequest 调用(postmaster 阶段):每个
 * PGPROC 需要"锁模式位图数组"(FastPathLockGroupsPerBackend 个 uint64,
 * 记录各 fast-path 槽位请求的锁模式)与"关系 OID 数组"
 * (FastPathLockSlotsPerBackend() 个 Oid,记录各槽位锁定的关系),两者
 * 均按 MAXALIGN 对齐,再乘以进程总数 TotalProcs。
 *
 * 【设计思想】fast-path 锁数组是变长的,无法直接内嵌进 PGPROC,故单独
 * 划一块共享内存、按进程顺序连续切分(fast-path 机制见 lock.c);每个
 * 后端的两段数组交错布置(见 ProcGlobalShmemInit),尽量利用局部性。
 *
 * 【参数】无
 * 【返回值】所需字节数(恒大于 0)。 */
static Size
CalculateFastPathLockShmemSize(void)
{
	Size		size = 0;
	Size		fpLockBitsSize,
				fpRelIdSize;

	/*
	 * Memory needed for PGPROC fast-path lock arrays. Make sure the sizes are
	 * nicely aligned in each backend.
	 */
	fpLockBitsSize = MAXALIGN(FastPathLockGroupsPerBackend * sizeof(uint64));
	fpRelIdSize = MAXALIGN(FastPathLockSlotsPerBackend() * sizeof(Oid));

	size = add_size(size, mul_size(TotalProcs, (fpLockBitsSize + fpRelIdSize)));

	Assert(TotalProcs > 0);
	Assert(size > 0);

	return size;
}

/*
 * Report number of semaphores needed by ProcGlobalShmemInit.
 */
/* (中文)报告进程表子系统需要的信号量总数。
 *
 * 【作用】被 ProcGlobalShmemRequest(转发给 PGSemaphoreShmemRequest)与
 * ProcGlobalShmemInit(PGSemaphoreInit)调用,保证分配的信号量与 PGPROC
 * 一一对应。
 *
 * 【设计思想】信号量数量 = 普通后端(含自动清理、后台工作者、walsender,
 * 统一计入 MaxBackends) + 辅助进程数;prepared 事务的"虚拟 PGPROC"不
 * 与真实进程关联,不需要信号量(见 ProcGlobalShmemInit 中的分支)。
 *
 * 【参数】无
 * 【返回值】信号量总数。 */
int
ProcGlobalSemas(void)
{
	/*
	 * We need a sema per backend (including autovacuum), plus one for each
	 * auxiliary process.
	 */
	return MaxBackends + NUM_AUXILIARY_PROCS;
}

/*
 * ProcGlobalShmemRequest
 *	  Register shared memory needs.
 *
 * This is called during postmaster or standalone backend startup, and also
 * during backend startup in EXEC_BACKEND mode.
 */
/* (中文)共享内存 request 阶段回调:登记进程表子系统所需的共享内存。
 *
 * 【作用】postmaster(或独立后端、EXEC_BACKEND 下的后端)启动早期由共享
 * 内存子系统调用,声明三块内存:
 * 1. "PGPROC 大块":TotalProcs 个 PGPROC + 每进程一个的 xids/
 *    subxidStates/statusFlags 镜像数组(总大小记录进
 *    ProcGlobalAllProcsShmemSize);
 * 2. "Fast-Path Lock Array":postmaster 阶段按 CalculateFastPathLockShmemSize
 *    计算精确大小;子进程阶段以 SHMEM_ATTACH_UNKNOWN_SIZE 表示附加既有
 *    内存(避免重复计算,EXEC_BACKEND 下按同样布局重新附加);
 * 3. "Proc Header"(PROC_HDR)。
 * 最后委托信号量实现(PGSemaphoreShmemRequest)登记其共享需求。
 *
 * 【设计思想】"先请求后初始化"两阶段约定:request 阶段只统计并声明
 * 字节数,init 阶段(ProcGlobalShmemInit)才填充内容。EXEC_BACKEND 下
 * ProcGlobal 需要被后端在调用 ShmemAttachRequested() 之前就访问到,
 * 故其 .ptr 注册方式与普通结构相同、但传播路径特殊(见英文注释)。
 *
 * 【参数】arg —— 回调参数(未使用)。
 * 【返回值】无 */
static void
ProcGlobalShmemRequest(void *arg)
{
	Size		size;

	/*
	 * Reserve all the PGPROC structures we'll need.  There are six separate
	 * consumers: (1) normal backends, (2) autovacuum workers and special
	 * workers, (3) background workers, (4) walsenders, (5) auxiliary
	 * processes, and (6) prepared transactions.  (For largely-historical
	 * reasons, we combine autovacuum and special workers into one category
	 * with a single freelist.)  Each PGPROC structure is dedicated to exactly
	 * one of these purposes, and they do not move between groups.
	 */
	TotalProcs =
		add_size(MaxBackends, add_size(NUM_AUXILIARY_PROCS, max_prepared_xacts));

	size = 0;
	size = add_size(size, mul_size(TotalProcs, sizeof(PGPROC)));
	size = add_size(size, mul_size(TotalProcs, sizeof(*ProcGlobal->xids)));
	size = add_size(size, mul_size(TotalProcs, sizeof(*ProcGlobal->subxidStates)));
	size = add_size(size, mul_size(TotalProcs, sizeof(*ProcGlobal->statusFlags)));
	ProcGlobalAllProcsShmemSize = size;
	ShmemRequestStruct(.name = "PGPROC structures",
					   .size = ProcGlobalAllProcsShmemSize,
					   .ptr = &AllProcsShmemPtr,
		);

	if (!IsUnderPostmaster)
		size = FastPathLockArrayShmemSize = CalculateFastPathLockShmemSize();
	else
		size = SHMEM_ATTACH_UNKNOWN_SIZE;
	ShmemRequestStruct(.name = "Fast-Path Lock Array",
					   .size = size,
					   .ptr = &FastPathLockArrayShmemPtr,
		);

	/*
	 * ProcGlobal is registered here in .ptr as usual, but it needs to be
	 * propagated specially in EXEC_BACKEND mode, because ProcGlobal needs to
	 * be accessed early at backend startup, before ShmemAttachRequested() has
	 * been called.
	 */
	ShmemRequestStruct(.name = "Proc Header",
					   .size = sizeof(PROC_HDR),
					   .ptr = (void **) &ProcGlobal,
		);

	/* Let the semaphore implementation register its shared memory needs */
	PGSemaphoreShmemRequest(ProcGlobalSemas());
}


/*
 * ProcGlobalShmemInit -
 *	  Initialize the global process table during postmaster or standalone
 *	  backend startup.
 *
 *	  We also create all the per-process semaphores we will need to support
 *	  the requested number of backends.  We used to allocate semaphores
 *	  only when backends were actually started up, but that is bad because
 *	  it lets Postgres fail under load --- a lot of Unix systems are
 *	  (mis)configured with small limits on the number of semaphores, and
 *	  running out when trying to start another backend is a common failure.
 *	  So, now we grab enough semaphores to support the desired max number
 *	  of backends immediately at initialization --- if the sysadmin has set
 *	  MaxConnections, max_worker_processes, max_wal_senders, or
 *	  autovacuum_worker_slots higher than his kernel will support, he'll
 *	  find out sooner rather than later.
 *
 *	  Another reason for creating semaphores here is that the semaphore
 *	  implementation typically requires us to create semaphores in the
 *	  postmaster, not in backends.
 */
/* (中文)共享内存 init 阶段回调:初始化全局进程表并创建全部信号量。
 *
 * 【作用】共享内存分配完成后执行:
 * 1. 初始化 PROC_HDR:spinlock、四条空闲链表、各辅助进程广告位
 *    (avLauncherProc 等,先置 INVALID_PROC_NUMBER)、spins_per_delay;
 * 2. 把"PGPROC 大块"清零并切片:allProcs 数组(PGPROC 本体,共
 *    TotalProcs 个)+ 三个密集镜像数组 xids/subxidStates/statusFlags;
 * 3. 切分 fast-path 锁数组:按进程逐个分配 fpLockBits/fpRelId,两段
 *    交错布置以利用缓存局部性;前 FIRST_PREPARED_XACT_PROC_NUMBER 个
 *    PGPROC 创建各自信号量、共享 latch 与 fpInfoLock(prepared 事务
 *    的虚拟 PGPROC 不需要——它们不与真实进程关联);
 * 4. 按角色把 PGPROC 挂进对应空闲链表:普通后端(< MaxConnections)
 *    -> freeProcs;自动清理/特殊 worker -> autovacFreeProcs;后台
 *    worker -> bgworkerFreeProcs;walsender -> walsenderFreeProcs。
 *    辅助进程不用空闲链表(数量少且固定,由 InitAuxiliaryProcess 线性
 *    查找),prepared 事务 PGPROC 由 TwoPhaseShmemInit 管理;
 * 5. 初始化各 PGPROC 的 myProcLocks、lockGroupMembers 与原子字段,
 *    最后记录 AuxiliaryProcs/PreparedXactProcs 区段起始指针。
 *
 * 【设计思想】按角色分链表(见英文注释):不同类型的进程各有配额语义,
 * 单独链表让"连接满"与"walsender 满"等错误信息互不干扰;信号量在
 * postmaster 启动时一次性创建,宁可配置失败早暴露,也不在负载高峰
 * 时才因内核限额失败(见函数上方英文注释)。
 *
 * 【参数】arg —— 回调参数(未使用)。
 * 【返回值】无 */
static void
ProcGlobalShmemInit(void *arg)
{
	char	   *ptr;
	size_t		requestSize;
	PGPROC	   *procs;
	int			i,
				j;

	/* Used for setup of per-backend fast-path slots. */
	char	   *fpPtr,
			   *fpEndPtr PG_USED_FOR_ASSERTS_ONLY;
	Size		fpLockBitsSize,
				fpRelIdSize;

	Assert(ProcGlobal);
	ProcGlobal->spins_per_delay = DEFAULT_SPINS_PER_DELAY;
	SpinLockInit(&ProcGlobal->freeProcsLock);
	dlist_init(&ProcGlobal->freeProcs);
	dlist_init(&ProcGlobal->autovacFreeProcs);
	dlist_init(&ProcGlobal->bgworkerFreeProcs);
	dlist_init(&ProcGlobal->walsenderFreeProcs);
	ProcGlobal->startupBufferPinWaitBufId = -1;
	pg_atomic_init_u32(&ProcGlobal->avLauncherProc, INVALID_PROC_NUMBER);
	pg_atomic_init_u32(&ProcGlobal->walwriterProc, INVALID_PROC_NUMBER);
	pg_atomic_init_u32(&ProcGlobal->checkpointerProc, INVALID_PROC_NUMBER);
	pg_atomic_init_u32(&ProcGlobal->procArrayGroupFirst, INVALID_PROC_NUMBER);
	pg_atomic_init_u32(&ProcGlobal->clogGroupFirst, INVALID_PROC_NUMBER);

	ptr = AllProcsShmemPtr;
	requestSize = ProcGlobalAllProcsShmemSize;
	MemSet(ptr, 0, requestSize);

	/* Carve out the allProcs array from the shared memory area */
	procs = (PGPROC *) ptr;
	ptr = ptr + TotalProcs * sizeof(PGPROC);

	ProcGlobal->allProcs = procs;
	/* XXX allProcCount isn't really all of them; it excludes prepared xacts */
	ProcGlobal->allProcCount = MaxBackends + NUM_AUXILIARY_PROCS;

	/*
	 * Carve out arrays mirroring PGPROC fields in a dense manner. See
	 * PROC_HDR.
	 *
	 * XXX: It might make sense to increase padding for these arrays, given
	 * how hotly they are accessed.
	 */
	ProcGlobal->xids = (TransactionId *) ptr;
	ptr = ptr + (TotalProcs * sizeof(*ProcGlobal->xids));

	ProcGlobal->subxidStates = (XidCacheStatus *) ptr;
	ptr = ptr + (TotalProcs * sizeof(*ProcGlobal->subxidStates));

	ProcGlobal->statusFlags = (uint8 *) ptr;
	ptr = ptr + (TotalProcs * sizeof(*ProcGlobal->statusFlags));

	/* make sure we didn't overflow */
	Assert((ptr > (char *) procs) && (ptr <= (char *) procs + requestSize));

	/*
	 * Initialize arrays for fast-path locks. Those are variable-length, so
	 * can't be included in PGPROC directly. We allocate a separate piece of
	 * shared memory and then divide that between backends.
	 */
	fpLockBitsSize = MAXALIGN(FastPathLockGroupsPerBackend * sizeof(uint64));
	fpRelIdSize = MAXALIGN(FastPathLockSlotsPerBackend() * sizeof(Oid));

	fpPtr = FastPathLockArrayShmemPtr;
	requestSize = FastPathLockArrayShmemSize;
	memset(fpPtr, 0, requestSize);

	/* For asserts checking we did not overflow. */
	fpEndPtr = fpPtr + requestSize;

	/* Initialize semaphores */
	PGSemaphoreInit(ProcGlobalSemas());

	for (i = 0; i < TotalProcs; i++)
	{
		PGPROC	   *proc = &procs[i];

		/* Common initialization for all PGPROCs, regardless of type. */

		/*
		 * Set the fast-path lock arrays, and move the pointer. We interleave
		 * the two arrays, to (hopefully) get some locality for each backend.
		 */
		proc->fpLockBits = (uint64 *) fpPtr;
		fpPtr += fpLockBitsSize;

		proc->fpRelId = (Oid *) fpPtr;
		fpPtr += fpRelIdSize;

		Assert(fpPtr <= fpEndPtr);

		/*
		 * Set up per-PGPROC semaphore, latch, and fpInfoLock.  Prepared xact
		 * dummy PGPROCs don't need these though - they're never associated
		 * with a real process
		 */
		if (i < FIRST_PREPARED_XACT_PROC_NUMBER)
		{
			proc->sem = PGSemaphoreCreate();
			InitSharedLatch(&(proc->procLatch));
			LWLockInitialize(&(proc->fpInfoLock), LWTRANCHE_LOCK_FASTPATH);
		}

		/*
		 * Newly created PGPROCs for normal backends, autovacuum workers,
		 * special workers, bgworkers, and walsenders must be queued up on the
		 * appropriate free list.  Because there can only ever be a small,
		 * fixed number of auxiliary processes, no free list is used in that
		 * case; InitAuxiliaryProcess() instead uses a linear search.  PGPROCs
		 * for prepared transactions are added to a free list by
		 * TwoPhaseShmemInit().
		 */
		if (i < MaxConnections)
		{
			/* PGPROC for normal backend, add to freeProcs list */
			dlist_push_tail(&ProcGlobal->freeProcs, &proc->freeProcsLink);
			proc->procgloballist = &ProcGlobal->freeProcs;
		}
		else if (i < MaxConnections + autovacuum_worker_slots + NUM_SPECIAL_WORKER_PROCS)
		{
			/* PGPROC for AV or special worker, add to autovacFreeProcs list */
			dlist_push_tail(&ProcGlobal->autovacFreeProcs, &proc->freeProcsLink);
			proc->procgloballist = &ProcGlobal->autovacFreeProcs;
		}
		else if (i < MaxConnections + autovacuum_worker_slots + NUM_SPECIAL_WORKER_PROCS + max_worker_processes)
		{
			/* PGPROC for bgworker, add to bgworkerFreeProcs list */
			dlist_push_tail(&ProcGlobal->bgworkerFreeProcs, &proc->freeProcsLink);
			proc->procgloballist = &ProcGlobal->bgworkerFreeProcs;
		}
		else if (i < MaxBackends)
		{
			/* PGPROC for walsender, add to walsenderFreeProcs list */
			dlist_push_tail(&ProcGlobal->walsenderFreeProcs, &proc->freeProcsLink);
			proc->procgloballist = &ProcGlobal->walsenderFreeProcs;
		}

		/* Initialize myProcLocks[] shared memory queues. */
		for (j = 0; j < NUM_LOCK_PARTITIONS; j++)
			dlist_init(&(proc->myProcLocks[j]));

		/* Initialize lockGroupMembers list. */
		dlist_init(&proc->lockGroupMembers);

		/*
		 * Initialize the atomic variables, otherwise, it won't be safe to
		 * access them for backends that aren't currently in use.
		 */
		pg_atomic_init_u32(&(proc->procArrayGroupNext), INVALID_PROC_NUMBER);
		pg_atomic_init_u32(&(proc->clogGroupNext), INVALID_PROC_NUMBER);
		pg_atomic_init_u64(&(proc->waitStart), 0);
	}

	/* Should have consumed exactly the expected amount of fast-path memory. */
	Assert(fpPtr == fpEndPtr);

	/*
	 * Save pointers to the blocks of PGPROC structures reserved for auxiliary
	 * processes and prepared transactions.
	 */
	AuxiliaryProcs = &procs[MaxBackends];
	PreparedXactProcs = &procs[FIRST_PREPARED_XACT_PROC_NUMBER];
}

/*
 * InitProcess -- initialize a per-process PGPROC entry for this backend
 */
/* (中文)为当前后端进程初始化一个 PGPROC 条目(后端启动的关键一步)。
 *
 * 【作用】普通后端、自动清理 worker、后台工作者、walsender 进程在启动
 * 早期调用(由 postmaster 启动协议中的 BackendStartup/autovac 等路径
 * 触发):从对应角色空闲链表摘取一个空闲 PGPROC 作为 MyProc,初始化其
 * 全部字段,接管共享 latch、登记 wait_event 存储,注册退出清理回调
 * ProcKill,并初始化 LWLock 与死锁检测的本地状态。
 *
 * 【设计思想】
 * - 角色选择必须与 ProcGlobalShmemInit 建链表的划分完全一致(见函数内
 *   注释),否则会挂错链表、破坏角色配额;
 * - 摘取在 freeProcsLock 自旋锁内完成,顺带把共享的 spins_per_delay
 *   估计值拷进本地(自旋策略的全局自适应,见 s_lock.c);链表为空表示
 *   配额用尽,给出"too many clients"等标准错误;
 * - 大段字段初始化与 ProcGlobalShmemInit 的分工:后者负责"进程无关、
 *   一次到位"的公共部分(信号量、锁队列头、原子变量),本函数负责
 *   "每次占用都要重置"的进程相关部分;PGPROC 会被复用,故所有字段都
 *   必须恢复初值,断言确保前一个进程没留下锁;
 * - latch 所有权:本进程的 latch 原指向进程本地,OwnLatch + SwitchToSharedLatch
 *   后指向共享的 MyProc->procLatch,使其他进程能通过 SetLatch 唤醒我们;
 * - 信号量可能来自已崩溃进程,重新 PGSemaphoreReset 保证计数干净。
 *
 * 【参数】无
 * 【返回值】无(PGPROC 配额耗尽时 ereport(FATAL);重复调用会
 *         elog(ERROR))。 */
void
InitProcess(void)
{
	dlist_head *procgloballist;

	/*
	 * ProcGlobal should be set up already (if we are a backend, we inherit
	 * this by fork() or EXEC_BACKEND mechanism from the postmaster).
	 */
	if (ProcGlobal == NULL)
		elog(PANIC, "proc header uninitialized");

	if (MyProc != NULL)
		elog(ERROR, "you already exist");

	/*
	 * Before we start accessing the shared memory in a serious way, mark
	 * ourselves as an active postmaster child; this is so that the postmaster
	 * can detect it if we exit without cleaning up.
	 */
	if (IsUnderPostmaster)
		RegisterPostmasterChildActive();

	/*
	 * Decide which list should supply our PGPROC.  This logic must match the
	 * way the freelists were constructed in ProcGlobalShmemInit().
	 */
	if (AmAutoVacuumWorkerProcess() || AmSpecialWorkerProcess())
		procgloballist = &ProcGlobal->autovacFreeProcs;
	else if (AmBackgroundWorkerProcess())
		procgloballist = &ProcGlobal->bgworkerFreeProcs;
	else if (AmWalSenderProcess())
		procgloballist = &ProcGlobal->walsenderFreeProcs;
	else
		procgloballist = &ProcGlobal->freeProcs;

	/*
	 * Try to get a proc struct from the appropriate free list.  If this
	 * fails, we must be out of PGPROC structures (not to mention semaphores).
	 *
	 * While we are holding the spinlock, also copy the current shared
	 * estimate of spins_per_delay to local storage.
	 */
	SpinLockAcquire(&ProcGlobal->freeProcsLock);

	set_spins_per_delay(ProcGlobal->spins_per_delay);

	if (!dlist_is_empty(procgloballist))
	{
		MyProc = dlist_container(PGPROC, freeProcsLink, dlist_pop_head_node(procgloballist));
		SpinLockRelease(&ProcGlobal->freeProcsLock);
	}
	else
	{
		/*
		 * If we reach here, all the PGPROCs are in use.  This is one of the
		 * possible places to detect "too many backends", so give the standard
		 * error message.  XXX do we need to give a different failure message
		 * in the autovacuum case?
		 */
		SpinLockRelease(&ProcGlobal->freeProcsLock);
		if (AmWalSenderProcess())
			ereport(FATAL,
					(errcode(ERRCODE_TOO_MANY_CONNECTIONS),
					 errmsg("number of requested standby connections exceeds \"max_wal_senders\" (currently %d)",
							max_wal_senders)));
		ereport(FATAL,
				(errcode(ERRCODE_TOO_MANY_CONNECTIONS),
				 errmsg("sorry, too many clients already")));
	}
	MyProcNumber = GetNumberFromPGProc(MyProc);

	/*
	 * Cross-check that the PGPROC is of the type we expect; if this were not
	 * the case, it would get returned to the wrong list.
	 */
	Assert(MyProc->procgloballist == procgloballist);

	/*
	 * Initialize all fields of MyProc, except for those previously
	 * initialized by ProcGlobalShmemInit.
	 */
	dlist_node_init(&MyProc->freeProcsLink);
	MyProc->waitStatus = PROC_WAIT_STATUS_OK;
	MyProc->fpVXIDLock = false;
	MyProc->fpLocalTransactionId = InvalidLocalTransactionId;
	MyProc->xid = InvalidTransactionId;
	MyProc->xmin = InvalidTransactionId;
	MyProc->pid = MyProcPid;
	MyProc->vxid.procNumber = MyProcNumber;
	MyProc->vxid.lxid = InvalidLocalTransactionId;
	/* databaseId and roleId will be filled in later */
	MyProc->databaseId = InvalidOid;
	MyProc->roleId = InvalidOid;
	MyProc->tempNamespaceId = InvalidOid;
	MyProc->backendType = MyBackendType;
	MyProc->delayChkptFlags = 0;
	MyProc->statusFlags = 0;
	/* NB -- autovac launcher intentionally does not set IS_AUTOVACUUM */
	if (AmAutoVacuumWorkerProcess())
		MyProc->statusFlags |= PROC_IS_AUTOVACUUM;
	MyProc->lwWaiting = LW_WS_NOT_WAITING;
	MyProc->lwWaitMode = 0;
	MyProc->waitLock = NULL;
	dlist_node_init(&MyProc->waitLink);
	MyProc->waitProcLock = NULL;
	pg_atomic_write_u64(&MyProc->waitStart, 0);
#ifdef USE_ASSERT_CHECKING
	{
		int			i;

		/* Last process should have released all locks. */
		for (i = 0; i < NUM_LOCK_PARTITIONS; i++)
			Assert(dlist_is_empty(&(MyProc->myProcLocks[i])));
	}
#endif
	pg_atomic_write_u32(&MyProc->pendingRecoveryConflicts, 0);

	/* Initialize fields for sync rep */
	MyProc->waitLSN = InvalidXLogRecPtr;
	MyProc->syncRepState = SYNC_REP_NOT_WAITING;
	dlist_node_init(&MyProc->syncRepLinks);

	/* Initialize fields for group XID clearing. */
	MyProc->procArrayGroupMember = false;
	MyProc->procArrayGroupMemberXid = InvalidTransactionId;
	Assert(pg_atomic_read_u32(&MyProc->procArrayGroupNext) == INVALID_PROC_NUMBER);

	/* Check that group locking fields are in a proper initial state. */
	Assert(MyProc->lockGroupLeader == NULL);
	Assert(dlist_is_empty(&MyProc->lockGroupMembers));

	/* Initialize wait event information. */
	MyProc->wait_event_info = 0;

	/* Initialize fields for group transaction status update. */
	MyProc->clogGroupMember = false;
	MyProc->clogGroupMemberXid = InvalidTransactionId;
	MyProc->clogGroupMemberXidStatus = TRANSACTION_STATUS_IN_PROGRESS;
	MyProc->clogGroupMemberPage = -1;
	MyProc->clogGroupMemberLsn = InvalidXLogRecPtr;
	Assert(pg_atomic_read_u32(&MyProc->clogGroupNext) == INVALID_PROC_NUMBER);

	/*
	 * Acquire ownership of the PGPROC's latch, so that we can use WaitLatch
	 * on it.  That allows us to repoint the process latch, which so far
	 * points to process local one, to the shared one.
	 */
	OwnLatch(&MyProc->procLatch);
	SwitchToSharedLatch();

	/* now that we have a proc, report wait events to shared memory */
	pgstat_set_wait_event_storage(&MyProc->wait_event_info);

	/*
	 * We might be reusing a semaphore that belonged to a failed process. So
	 * be careful and reinitialize its value here.  (This is not strictly
	 * necessary anymore, but seems like a good idea for cleanliness.)
	 */
	PGSemaphoreReset(MyProc->sem);

	/* autovacuum launcher is specially advertised in ProcGlobal */
	if (MyBackendType == B_AUTOVAC_LAUNCHER)
		pg_atomic_write_u32(&ProcGlobal->avLauncherProc, MyProcNumber);

	/*
	 * Arrange to clean up at backend exit.
	 */
	on_shmem_exit(ProcKill, 0);

	/*
	 * Now that we have a PGPROC, we could try to acquire locks, so initialize
	 * local state needed for LWLocks, and the deadlock checker.
	 */
	InitLWLockAccess();
	InitDeadLockChecking();

#ifdef EXEC_BACKEND

	/*
	 * Initialize backend-local pointers to all the shared data structures.
	 * (We couldn't do this until now because it needs LWLocks.)
	 */
	if (IsUnderPostmaster)
		AttachSharedMemoryStructs();
#endif
}

/*
 * InitProcessPhase2 -- make MyProc visible in the shared ProcArray.
 *
 * This is separate from InitProcess because we can't acquire LWLocks until
 * we've created a PGPROC, but in the EXEC_BACKEND case ProcArrayAdd won't
 * work until after we've done AttachSharedMemoryStructs.
 */
/* (中文)初始化第二阶段:把本进程加入共享 ProcArray。
 *
 * 【作用】在 InitProcess 之后、事务真正开始之前调用:调用 ProcArrayAdd
 * 使本进程对 ProcArray(procarray.c,用于快照/活跃事务判定)可见,并注册
 * 退出回调 RemoveProcFromArray。
 *
 * 【设计思想】与 InitProcess 分开的原因:ProcArrayAdd 需要持有 LWLock,
 * 而拿到 PGPROC 是使用 LWLock 的前提;EXEC_BACKEND 模式下 ProcArrayAdd
 * 还要等 AttachSharedMemoryStructs 之后才能工作,故把"建 PGPROC"与
 * "进 ProcArray"拆成两步,让启动流程在两者之间插入必要的附加步骤。
 *
 * 【参数】无
 * 【返回值】无(前置条件:MyProc 已就绪)。 */
void
InitProcessPhase2(void)
{
	Assert(MyProc != NULL);

	/*
	 * Add our PGPROC to the PGPROC array in shared memory.
	 */
	ProcArrayAdd(MyProc);

	/*
	 * Arrange to clean that up at backend exit.
	 */
	on_shmem_exit(RemoveProcFromArray, 0);
}

/*
 * InitAuxiliaryProcess -- create a PGPROC entry for an auxiliary process
 *
 * This is called by bgwriter and similar processes so that they will have a
 * MyProc value that's real enough to let them wait for LWLocks.  The PGPROC
 * and sema that are assigned are one of the extra ones created during
 * ProcGlobalShmemInit.
 *
 * Auxiliary processes are presently not expected to wait for real (lockmgr)
 * locks, so we need not set up the deadlock checker.  They are never added
 * to the ProcArray or the sinval messaging mechanism, either.  They also
 * don't get a VXID assigned, since this is only useful when we actually
 * hold lockmgr locks.
 *
 * Startup process however uses locks but never waits for them in the
 * normal backend sense. Startup process also takes part in sinval messaging
 * as a sendOnly process, so never reads messages from sinval queue. So
 * Startup process does have a VXID and does show up in pg_locks.
 */
/* (中文)为辅助进程(bgwriter、checkpointer、walwriter、启动进程等)创建
 * PGPROC 条目。
 *
 * 【作用】辅助进程不经过 InitProcess,而是调用本函数:在 freeProcsLock
 * 保护下从固定区段 AuxiliaryProcs 里线性找一个空闲(pid == 0)槽位,
 * 标记占用后作为 MyProc,初始化所需字段,接管共享 latch、登记
 * wait_event 存储,注册退出回调 AuxiliaryProcKill,并初始化 LWLock
 * 本地状态。walwriter/checkpointer 还会把自己的 ProcNumber 广告到
 * ProcGlobal(见注释:部分辅助进程在 ProcGlobal 中"打广告")。
 *
 * 【设计思想】辅助进程是固定数量、固定角色的小集合,故不用空闲链表而
 * 用线性查找;它们不参与重锁等待、不进 ProcArray、不做 sinval 消息
 * 接收,因此相应机制(死锁检测器、VXID、ProcArrayAdd)一概跳过。例外:
 * 启动进程(startup)会持有重锁且以 sendOnly 身份参与 sinval,所以它有
 * VXID、会出现在 pg_locks 中(见英文注释)。这些进程只等 LWLock,故仅
 * 初始化 LWLock 所需状态。
 *
 * 【参数】无
 * 【返回值】无(槽位耗尽时 elog(FATAL);重复调用会 elog(ERROR))。 */
void
InitAuxiliaryProcess(void)
{
	PGPROC	   *auxproc;
	int			proctype;

	/*
	 * ProcGlobal should be set up already (if we are a backend, we inherit
	 * this by fork() or EXEC_BACKEND mechanism from the postmaster).
	 */
	if (ProcGlobal == NULL || AuxiliaryProcs == NULL)
		elog(PANIC, "proc header uninitialized");

	if (MyProc != NULL)
		elog(ERROR, "you already exist");

	if (IsUnderPostmaster)
		RegisterPostmasterChildActive();

	/*
	 * We use the freeProcsLock to protect assignment and releasing of
	 * AuxiliaryProcs entries.
	 *
	 * While we are holding the spinlock, also copy the current shared
	 * estimate of spins_per_delay to local storage.
	 */
	SpinLockAcquire(&ProcGlobal->freeProcsLock);

	set_spins_per_delay(ProcGlobal->spins_per_delay);

	/*
	 * Find a free auxproc ... *big* trouble if there isn't one ...
	 */
	for (proctype = 0; proctype < NUM_AUXILIARY_PROCS; proctype++)
	{
		auxproc = &AuxiliaryProcs[proctype];
		if (auxproc->pid == 0)
			break;
	}
	if (proctype >= NUM_AUXILIARY_PROCS)
	{
		SpinLockRelease(&ProcGlobal->freeProcsLock);
		elog(FATAL, "all AuxiliaryProcs are in use");
	}

	/* Mark auxiliary proc as in use by me */
	auxproc->pid = MyProcPid;

	SpinLockRelease(&ProcGlobal->freeProcsLock);

	MyProc = auxproc;
	MyProcNumber = GetNumberFromPGProc(MyProc);

	/*
	 * Initialize all fields of MyProc, except for those previously
	 * initialized by ProcGlobalShmemInit.
	 */
	dlist_node_init(&MyProc->freeProcsLink);
	MyProc->waitStatus = PROC_WAIT_STATUS_OK;
	MyProc->fpVXIDLock = false;
	MyProc->fpLocalTransactionId = InvalidLocalTransactionId;
	MyProc->xid = InvalidTransactionId;
	MyProc->xmin = InvalidTransactionId;
	MyProc->vxid.procNumber = INVALID_PROC_NUMBER;
	MyProc->vxid.lxid = InvalidLocalTransactionId;
	MyProc->databaseId = InvalidOid;
	MyProc->roleId = InvalidOid;
	MyProc->tempNamespaceId = InvalidOid;
	MyProc->backendType = MyBackendType;
	MyProc->delayChkptFlags = 0;
	MyProc->statusFlags = 0;
	MyProc->lwWaiting = LW_WS_NOT_WAITING;
	MyProc->lwWaitMode = 0;
	MyProc->waitLock = NULL;
	dlist_node_init(&MyProc->waitLink);
	MyProc->waitProcLock = NULL;
	pg_atomic_write_u64(&MyProc->waitStart, 0);
#ifdef USE_ASSERT_CHECKING
	{
		int			i;

		/* Last process should have released all locks. */
		for (i = 0; i < NUM_LOCK_PARTITIONS; i++)
			Assert(dlist_is_empty(&(MyProc->myProcLocks[i])));
	}
#endif
	pg_atomic_write_u32(&MyProc->pendingRecoveryConflicts, 0);

	/*
	 * Acquire ownership of the PGPROC's latch, so that we can use WaitLatch
	 * on it.  That allows us to repoint the process latch, which so far
	 * points to process local one, to the shared one.
	 */
	OwnLatch(&MyProc->procLatch);
	SwitchToSharedLatch();

	/* now that we have a proc, report wait events to shared memory */
	pgstat_set_wait_event_storage(&MyProc->wait_event_info);

	/* Check that group locking fields are in a proper initial state. */
	Assert(MyProc->lockGroupLeader == NULL);
	Assert(dlist_is_empty(&MyProc->lockGroupMembers));

	/*
	 * We might be reusing a semaphore that belonged to a failed process. So
	 * be careful and reinitialize its value here.  (This is not strictly
	 * necessary anymore, but seems like a good idea for cleanliness.)
	 */
	PGSemaphoreReset(MyProc->sem);

	/* Some aux processes are also advertised in ProcGlobal */
	if (MyBackendType == B_WAL_WRITER)
		pg_atomic_write_u32(&ProcGlobal->walwriterProc, MyProcNumber);
	if (MyBackendType == B_CHECKPOINTER)
		pg_atomic_write_u32(&ProcGlobal->checkpointerProc, MyProcNumber);

	/*
	 * Arrange to clean up at process exit.
	 */
	on_shmem_exit(AuxiliaryProcKill, Int32GetDatum(proctype));

	/*
	 * Now that we have a PGPROC, we could try to acquire lightweight locks.
	 * Initialize local state needed for them.  (Heavyweight locks cannot be
	 * acquired in aux processes.)
	 */
	InitLWLockAccess();

#ifdef EXEC_BACKEND

	/*
	 * Initialize backend-local pointers to all the shared data structures.
	 * (We couldn't do this until now because it needs LWLocks.)
	 */
	if (IsUnderPostmaster)
		AttachSharedMemoryStructs();
#endif
}

/*
 * Used from bufmgr to share the value of the buffer that Startup waits on,
 * or to reset the value to "not waiting" (-1). This allows processing
 * of recovery conflicts for buffer pins. Set is made before backends look
 * at this value, so locking not required, especially since the set is
 * an atomic integer set operation.
 */
/* (中文)设置/清除"启动进程等待的 buffer pin 缓冲号"。
 *
 * 【作用】热备恢复期间,启动进程(Startup)等待某个缓冲区被解除 pin 时
 * 把该缓冲区编号(或 -1 表示不等待)写入 ProcGlobal,供各后端读取
 * (见 GetStartupBufferPinWaitBufId),从而实现 buffer pin 恢复冲突的
 * 检测与协调。
 *
 * 【设计思想】写入先于后端的读取发生(先设置后使用),且是单字原子
 * 赋值,故不需要锁;用 volatile 指针防止编译器重排读序。
 *
 * 【参数】bufid —— 启动进程等待的缓冲区编号;传 -1 表示复位为
 *         "不等待"。
 * 【返回值】无 */
void
SetStartupBufferPinWaitBufId(int bufid)
{
	/* use volatile pointer to prevent code rearrangement */
	volatile PROC_HDR *procglobal = ProcGlobal;

	procglobal->startupBufferPinWaitBufId = bufid;
}

/*
 * Used by backends when they receive a request to check for buffer pin waits.
 */
/* (中文)读取"启动进程当前等待的 buffer pin 缓冲号"。
 *
 * 【作用】后端收到 procsignal 的恢复冲突请求时调用:若返回值为合法缓冲
 * 号且本进程正 pin 着该缓冲区,就主动解除 pin,配合 Startup 推进恢复。
 *
 * 【设计思想】与 SetStartupBufferPinWaitBufId 对应,读侧同样用 volatile
 * 指针;因写入先于读取(见 setter 注释),无需加锁。
 *
 * 【参数】无
 * 【返回值】启动进程等待的缓冲号;-1 表示没有等待。 */
int
GetStartupBufferPinWaitBufId(void)
{
	/* use volatile pointer to prevent code rearrangement */
	volatile PROC_HDR *procglobal = ProcGlobal;

	return procglobal->startupBufferPinWaitBufId;
}

/*
 * Check whether there are at least N free PGPROC objects.  If false is
 * returned, *nfree will be set to the number of free PGPROC objects.
 * Otherwise, *nfree will be set to n.
 *
 * Note: this is designed on the assumption that N will generally be small.
 */
/* (中文)检查普通后端空闲链表上是否还有至少 N 个空闲 PGPROC。
 *
 * 【作用】供需要"预先判断能否再接纳 N 个连接"的调用方(如 postmaster
 * 判断连接池/两阶段事务注册是否可行)使用:在 freeProcsLock 保护下清点
 * freeProcs 链表前 N 项(不到 N 项则数完为止)。
 *
 * 【设计思想】只查"普通后端"链表,不含 autovac/bgworker/walsender;
 * N 通常很小,线性数节点成本可忽略。返回 false 时把实际空闲数带出,
 * 方便调用方报出准确数字。
 *
 * 【参数】n —— 需要检查的空闲数;nfree —— 输出参数:空闲数 >= n 时
 *         写入 n,否则写入实际空闲数。
 * 【返回值】空闲数 >= n 返回 true,否则 false。 */
bool
HaveNFreeProcs(int n, int *nfree)
{
	dlist_iter	iter;

	Assert(n > 0);
	Assert(nfree);

	SpinLockAcquire(&ProcGlobal->freeProcsLock);

	*nfree = 0;
	dlist_foreach(iter, &ProcGlobal->freeProcs)
	{
		(*nfree)++;
		if (*nfree == n)
			break;
	}

	SpinLockRelease(&ProcGlobal->freeProcsLock);

	return (*nfree == n);
}

/*
 * Cancel any pending wait for lock, when aborting a transaction, and revert
 * any strong lock count acquisition for a lock being acquired.
 *
 * (Normally, this would only happen if we accept a cancel/die
 * interrupt while waiting; but an ereport(ERROR) before or during the lock
 * wait is within the realm of possibility, too.)
 */
/* (中文)事务中止时取消正在进行的锁等待,并回退强锁计数。
 *
 * 【作用】在事务中止/错误清理路径上调用(ProcReleaseLocks 与
 * ProcEndTransaction 等处):先 AbortStrongLockAcquire 撤销
 * "strong lock 计数已 +1"的获取登记;若本进程确实在等锁(GetAwaitedLock
 * 非空),关闭死锁与锁超时定时器,持对应分区锁把本进程从锁等待队列摘除
 * (若已被摘除且等待被授予,则把锁登记进本地锁表 GrantAwaitedLock),
 * 最后复位等待锁记录。
 *
 * 【设计思想】等锁期间随时可能被取消/出错,必须保证"进程要么在等待
 * 队列里、要么不在",共享锁表才一致;摘除操作以分区锁串行化,避免与
 * 释放者/死锁检测者竞争。定时器关闭时保留 LOCK_TIMEOUT 的 indicator
 * 标志:当 SIGINT 恰好来自锁超时而非用户取消时,错误要上报为"锁超时"
 * 而不是"查询取消"(见函数内注释)。本函数全程 HOLD_INTERRUPTS,保证
 * 清理过程不被再次中断。
 *
 * 【参数】无
 * 【返回值】无 */
void
LockErrorCleanup(void)
{
	LOCALLOCK  *lockAwaited;
	LWLock	   *partitionLock;
	DisableTimeoutParams timeouts[2];

	HOLD_INTERRUPTS();

	AbortStrongLockAcquire();

	/* Nothing to do if we weren't waiting for a lock */
	lockAwaited = GetAwaitedLock();
	if (lockAwaited == NULL)
	{
		RESUME_INTERRUPTS();
		return;
	}

	/*
	 * Turn off the deadlock and lock timeout timers, if they are still
	 * running (see ProcSleep).  Note we must preserve the LOCK_TIMEOUT
	 * indicator flag, since this function is executed before
	 * ProcessInterrupts when responding to SIGINT; else we'd lose the
	 * knowledge that the SIGINT came from a lock timeout and not an external
	 * source.
	 */
	timeouts[0].id = DEADLOCK_TIMEOUT;
	timeouts[0].keep_indicator = false;
	timeouts[1].id = LOCK_TIMEOUT;
	timeouts[1].keep_indicator = true;
	disable_timeouts(timeouts, 2);

	/* Unlink myself from the wait queue, if on it (might not be anymore!) */
	partitionLock = LockHashPartitionLock(lockAwaited->hashcode);
	LWLockAcquire(partitionLock, LW_EXCLUSIVE);

	if (!dlist_node_is_detached(&MyProc->waitLink))
	{
		/* We could not have been granted the lock yet */
		RemoveFromWaitQueue(MyProc, lockAwaited->hashcode);
	}
	else
	{
		/*
		 * Somebody kicked us off the lock queue already.  Perhaps they
		 * granted us the lock, or perhaps they detected a deadlock. If they
		 * did grant us the lock, we'd better remember it in our local lock
		 * table.
		 */
		if (MyProc->waitStatus == PROC_WAIT_STATUS_OK)
			GrantAwaitedLock();
	}

	ResetAwaitedLock();

	LWLockRelease(partitionLock);

	RESUME_INTERRUPTS();
}


/*
 * ProcReleaseLocks() -- release locks associated with current transaction
 *			at main transaction commit or abort
 *
 * At main transaction commit, we release standard locks except session locks.
 * At main transaction abort, we release all locks including session locks.
 *
 * Advisory locks are released only if they are transaction-level;
 * session-level holds remain, whether this is a commit or not.
 *
 * At subtransaction commit, we don't release any locks (so this func is not
 * needed at all); we will defer the releasing to the parent transaction.
 * At subtransaction abort, we release all locks held by the subtransaction;
 * this is implemented by retail releasing of the locks under control of
 * the ResourceOwner mechanism.
 */
/* (中文)在事务提交/中止时释放与当前事务相关的锁。
 *
 * 【作用】由事务提交/回滚路径(commit/abort)调用:
 * - 若本进程没有 PGPROC(如独立后端早期),直接返回;
 * - 若正停留在等锁队列上(通常是错误后的残留),先 LockErrorCleanup;
 * - 主事务提交:释放标准锁(除 session 级);主事务中止:释放包括
 *   session 级在内的全部标准锁;
 * - 用户锁(advisory):只释放事务级的,session 级持有的无论提交与否
 *   都保留。
 *
 * 【设计思想】子事务提交不释放任何锁(延迟到父事务处理,因此本函数
 * 根本不被调用);子事务中止时锁由 ResourceOwner 机制逐把零售释放。
 *
 * 【参数】isCommit —— true 表示提交(保留 session 级标准锁),false
 *         表示中止(全部标准锁都释放)。
 * 【返回值】无 */
void
ProcReleaseLocks(bool isCommit)
{
	if (!MyProc)
		return;
	/* If waiting, get off wait queue (should only be needed after error) */
	LockErrorCleanup();
	/* Release standard locks, including session-level if aborting */
	LockReleaseAll(DEFAULT_LOCKMETHOD, !isCommit);
	/* Release transaction-level advisory locks */
	LockReleaseAll(USER_LOCKMETHOD, false);
}


/*
 * RemoveProcFromArray() -- Remove this process from the shared ProcArray.
 */
/* (中文)进程退出回调:把本进程从共享 ProcArray 中移除。
 *
 * 【作用】由 InitProcessPhase2 注册的 on_shmem_exit 回调,进程退出时
 * 调用 ProcArrayRemove 使本进程在快照/活跃事务判定中不可见。
 *
 * 【参数】code —— 退出码;arg —— 附加参数(均未使用)。
 * 【返回值】无 */
static void
RemoveProcFromArray(int code, Datum arg)
{
	Assert(MyProc != NULL);
	ProcArrayRemove(MyProc, InvalidTransactionId);
}

/*
 * ProcKill() -- Destroy the per-proc data structure for
 *		this process. Release any of its held LW locks.
 */
/* (中文)普通后端的退出清理回调:销毁本进程的 PGPROC 条目并归还空闲链表。
 *
 * 【作用】由 InitProcess 注册的 on_shmem_exit 回调,进程(正常或异常)
 * 退出时执行,按序完成:同步复制链清理 -> 释放遗留 LWLock -> 清理
 * LSN 等待与条件变量睡眠 -> 把 latch 切回进程本地并放弃共享 latch
 * 所有权 -> 退出锁组(必要时连带归还 leader 的 PGPROC)-> 重置字段 ->
 * 把 PGPROC 挂回所属空闲链表,并更新全局 spins_per_delay 估计。
 *
 * 【设计思想】若干并发安全细节:
 * - DisownLatch 必须先于 PGPROC 回链:新 fork 的后端可能立刻弹出这个
 *   槽并 OwnLatch,若 latch 仍属旧进程会 PANIC;
 * - 锁组退出逻辑在 leader 的分区锁(leader_lwlock)保护下决定
 *   push_self/push_leader:组长在还有跟随者时提前退出,其 PGPROC 由
 *   最后一个跟随者归还,避免"组长 PGPROC 已回链却被跟随者引用";
 * - 实际回链在单次 freeProcsLock 临界区中完成(避免与 InitProcess 的
 *   摘取竞争),并顺带把本进程观察到的自旋延迟反馈进共享估计;
 * - LWLockReleaseAll 兜底:正常路径不该有遗留 LWLock,但保险起见
 *   在放弃 PGPROC 前再清一次(放弃后我们就无法再睡眠了);
 * - pgstat_reset_wait_event_storage 故意推迟到锁组处理之后,使我们在
 *   槽位上被他人观察期间 wait_event_info 仍有效。
 *
 * 【参数】code —— 退出码;arg —— 附加参数(均未使用)。
 * 【返回值】无 */
static void
ProcKill(int code, Datum arg)
{
	PGPROC	   *proc;
	PGPROC	   *leader;
	dlist_head *procgloballist;
	bool		push_leader;
	bool		push_self;

	Assert(MyProc != NULL);

	/* not safe if forked by system(), etc. */
	if (MyProc->pid != (int) getpid())
		elog(PANIC, "ProcKill() called in child process");

	/* Make sure we're out of the sync rep lists */
	SyncRepCleanupAtProcExit();

#ifdef USE_ASSERT_CHECKING
	{
		int			i;

		/* Last process should have released all locks. */
		for (i = 0; i < NUM_LOCK_PARTITIONS; i++)
			Assert(dlist_is_empty(&(MyProc->myProcLocks[i])));
	}
#endif

	/*
	 * Release any LW locks I am holding.  There really shouldn't be any, but
	 * it's cheap to check again before we cut the knees off the LWLock
	 * facility by releasing our PGPROC ...
	 */
	LWLockReleaseAll();

	/*
	 * Cleanup waiting for LSN if any.
	 */
	WaitLSNCleanup();

	/* Cancel any pending condition variable sleep, too */
	ConditionVariableCancelSleep();

	/*
	 * Reset MyLatch to the process local one and disown the shared latch, so
	 * that signal handlers et al can continue using the latch after the
	 * shared latch isn't ours anymore.
	 *
	 * DisownLatch() must happen before our PGPROC can appear on a freelist: a
	 * newly-forked backend that pops our slot and calls OwnLatch() would
	 * PANIC on a still-owned latch.
	 *
	 * pgstat_reset_wait_event_storage() is intentionally deferred until after
	 * the lock-group block so that wait_event_info remains visible in our
	 * PGPROC slot while we may be observed there.  It is safe to defer
	 * because our slot is not yet on any freelist at this point, and useful
	 * for testing purposes.
	 */
	SwitchBackToLocalLatch();
	DisownLatch(&MyProc->procLatch);

	if (MyBackendType == B_AUTOVAC_LAUNCHER)
	{
		Assert(pg_atomic_read_u32(&ProcGlobal->avLauncherProc) == MyProcNumber);
		pg_atomic_write_u32(&ProcGlobal->avLauncherProc, INVALID_PROC_NUMBER);
	}

	proc = MyProc;
	procgloballist = proc->procgloballist;

	/*
	 * Detach from any lock group of which we are a member, deciding under
	 * leader_lwlock whether we (via push_self) and/or the leader (via
	 * push_leader) need to be pushed onto a freelist.  The actual pushes
	 * happen after evaluating if any of these are required, under a single
	 * ProcGlobal->freeProcsLock.
	 *
	 * The decision whether any of the freelists needs to be updated is taken
	 * under a single leader_lwlock.
	 */
	push_leader = false;
	push_self = true;
	leader = NULL;

	if (proc->lockGroupLeader != NULL)
	{
		LWLock	   *leader_lwlock;

		leader = proc->lockGroupLeader;
		leader_lwlock = LockHashPartitionLockByProc(leader);

		LWLockAcquire(leader_lwlock, LW_EXCLUSIVE);
		Assert(!dlist_is_empty(&leader->lockGroupMembers));
		dlist_delete(&proc->lockGroupLink);
		if (dlist_is_empty(&leader->lockGroupMembers))
		{
			leader->lockGroupLeader = NULL;
			if (leader != proc)
			{
				/*
				 * We are the last follower and the leader exited earlier; its
				 * PGPROC is still allocated and must be pushed here.
				 */
				push_leader = true;
				proc->lockGroupLeader = NULL;
			}
		}
		else if (leader != proc)
		{
			/* Non-last follower; leader still present in the group. */
			proc->lockGroupLeader = NULL;
		}
		else
		{
			/*
			 * We are the leader and followers remain.  Skip our own push; the
			 * last follower to exit will push us back to the freelist.
			 */
			push_self = false;
		}
		LWLockRelease(leader_lwlock);
	}

	/* See comment above, close to DisownLatch() */
	pgstat_reset_wait_event_storage();

	MyProc = NULL;
	MyProcNumber = INVALID_PROC_NUMBER;

	/* Mark the proc no longer in use */
	proc->pid = 0;
	proc->vxid.procNumber = INVALID_PROC_NUMBER;
	proc->vxid.lxid = InvalidTransactionId;

	SpinLockAcquire(&ProcGlobal->freeProcsLock);
	if (push_leader)
	{
		/* Return leader PGPROC (and semaphore) to appropriate freelist */
		dlist_push_head(leader->procgloballist, &leader->freeProcsLink);
	}
	if (push_self)
	{
		Assert(proc->lockGroupLeader == NULL);
		/* Since lockGroupLeader is NULL, lockGroupMembers should be empty. */
		Assert(dlist_is_empty(&proc->lockGroupMembers));

		/* Return PGPROC structure (and semaphore) to appropriate freelist */
		dlist_push_tail(procgloballist, &proc->freeProcsLink);
	}

	/* Update shared estimate of spins_per_delay */
	ProcGlobal->spins_per_delay = update_spins_per_delay(ProcGlobal->spins_per_delay);

	SpinLockRelease(&ProcGlobal->freeProcsLock);
}

/*
 * AuxiliaryProcKill() -- Cut-down version of ProcKill for auxiliary
 *		processes (bgwriter, etc).  The PGPROC and sema are not released, only
 *		marked as not-in-use.
 */
/* (中文)辅助进程的退出清理回调(ProcKill 的精简版)。
 *
 * 【作用】由 InitAuxiliaryProcess 注册的 on_shmem_exit 回调,辅助进程
 * 退出时执行:释放遗留 LWLock、取消条件变量睡眠、把 latch 切回本地、
 * 清除 ProcGlobal 中本进程的广告位(walwriter/checkpointer)、放弃
 * latch 所有权、把槽位标记为空闲(pid = 0,供后继辅助进程复用),并
 * 更新 spins_per_delay。
 *
 * 【设计思想】辅助进程的 PGPROC 来自固定区段 AuxiliaryProcs,不挂任何
 * 空闲链表,退出只做"标记空闲"而非归还;标记动作在 freeProcsLock
 * 保护下完成,与 InitAuxiliaryProcess 的线性查找互斥。其余细节见
 * ProcKill 的注释(两者共享同样的 latch/信号量卫生约定)。
 *
 * 【参数】code —— 退出码;arg —— 注册时传入的辅助进程类型号
 *         (AuxiliaryProcs 下标)。
 * 【返回值】无 */
static void
AuxiliaryProcKill(int code, Datum arg)
{
	int			proctype = DatumGetInt32(arg);
	PGPROC	   *auxproc PG_USED_FOR_ASSERTS_ONLY;
	PGPROC	   *proc;

	Assert(proctype >= 0 && proctype < NUM_AUXILIARY_PROCS);

	/* not safe if forked by system(), etc. */
	if (MyProc->pid != (int) getpid())
		elog(PANIC, "AuxiliaryProcKill() called in child process");

	auxproc = &AuxiliaryProcs[proctype];

	Assert(MyProc == auxproc);

	/* Release any LW locks I am holding (see notes above) */
	LWLockReleaseAll();

	/* Cancel any pending condition variable sleep, too */
	ConditionVariableCancelSleep();

	/* look at the equivalent ProcKill() code for comments */
	SwitchBackToLocalLatch();
	pgstat_reset_wait_event_storage();

	/*
	 * If this was one of the aux processes advertised in ProcGlobal, clear it
	 */
	if (MyBackendType == B_WAL_WRITER)
	{
		Assert(pg_atomic_read_u32(&ProcGlobal->walwriterProc) == MyProcNumber);
		pg_atomic_write_u32(&ProcGlobal->walwriterProc, INVALID_PROC_NUMBER);
	}
	if (MyBackendType == B_CHECKPOINTER)
	{
		Assert(pg_atomic_read_u32(&ProcGlobal->checkpointerProc) == MyProcNumber);
		pg_atomic_write_u32(&ProcGlobal->checkpointerProc, INVALID_PROC_NUMBER);
	}

	proc = MyProc;
	MyProc = NULL;
	MyProcNumber = INVALID_PROC_NUMBER;
	DisownLatch(&proc->procLatch);

	SpinLockAcquire(&ProcGlobal->freeProcsLock);

	/* Mark auxiliary proc no longer in use */
	proc->pid = 0;
	proc->vxid.procNumber = INVALID_PROC_NUMBER;
	proc->vxid.lxid = InvalidTransactionId;

	/* Update shared estimate of spins_per_delay */
	ProcGlobal->spins_per_delay = update_spins_per_delay(ProcGlobal->spins_per_delay);

	SpinLockRelease(&ProcGlobal->freeProcsLock);
}

/*
 * AuxiliaryPidGetProc -- get PGPROC for an auxiliary process
 * given its PID
 *
 * Returns NULL if not found.
 */
/* (中文)按 PID 查找辅助进程的 PGPROC。
 *
 * 【作用】供 postmaster 等在需要定位某辅助进程(如按 PID 判断角色)时
 * 使用:线性扫描固定区段 AuxiliaryProcs,比对 pid 字段。
 *
 * 【设计思想】辅助进程数量少且固定(NUM_AUXILIARY_PROCS),线性扫描
 * 足够;pid == 0 的槽位是空闲槽(任何真实进程 pid 都不可能为 0),
 * 直接排除。查找不加锁:pid 字段的读在辅助进程退出清理里会被写回 0,
 * 最坏情况是查到"刚退出的进程"或"查不到",调用方自行容忍。
 *
 * 【参数】pid —— 要查找的进程 PID。
 * 【返回值】匹配的 PGPROC 指针;未找到返回 NULL。 */
PGPROC *
AuxiliaryPidGetProc(int pid)
{
	PGPROC	   *result = NULL;
	int			index;

	if (pid == 0)				/* never match dummy PGPROCs */
		return NULL;

	for (index = 0; index < NUM_AUXILIARY_PROCS; index++)
	{
		PGPROC	   *proc = &AuxiliaryProcs[index];

		if (proc->pid == pid)
		{
			result = proc;
			break;
		}
	}
	return result;
}


/*
 * JoinWaitQueue -- join the wait queue on the specified lock
 *
 * It's not actually guaranteed that we need to wait when this function is
 * called, because it could be that when we try to find a position at which
 * to insert ourself into the wait queue, we discover that we must be inserted
 * ahead of everyone who wants a lock that conflict with ours. In that case,
 * we get the lock immediately. Because of this, it's sensible for this function
 * to have a dontWait argument, despite the name.
 *
 * On entry, the caller has already set up LOCK and PROCLOCK entries to
 * reflect that we have "requested" the lock.  The caller is responsible for
 * cleaning that up, if we end up not joining the queue after all.
 *
 * The lock table's partition lock must be held at entry, and is still held
 * at exit.  The caller must release it before calling ProcSleep().
 *
 * Result is one of the following:
 *
 *  PROC_WAIT_STATUS_OK       - lock was immediately granted
 *  PROC_WAIT_STATUS_WAITING  - joined the wait queue; call ProcSleep()
 *  PROC_WAIT_STATUS_ERROR    - immediate deadlock was detected, or would
 *                              need to wait and dontWait == true
 *
 * NOTES: The process queue is now a priority queue for locking.
 */
/* (中文)把本进程加入指定重锁的等待队列(可能"一进去就被直接授予")。
 *
 * 【作用】LockAcquireExtended 在判定需要等待后、调用 ProcSleep 之前
 * 调用(由 lock.c 的 WaitOnLock 进入):在持分区锁(LW_EXCLUSIVE)的前提下,
 * 遍历锁的等待队列确定插入位置,必要时立即授予(不真正睡眠)。
 *
 * 【设计思想】
 * - 队列是优先级队列:若本进程已持有的锁与某个前方等待者的请求冲突,
 *   应插到该等待者之前(否则死锁检测迟早也会把我们挪到它前面,不如
 *   现在就地解决)。扫描中若发现"他必须等我、我也必须等他",即两人
 *   互等,构成即时死锁(early_deadlock),直接返回 ERROR 状态;
 * - 特殊情形:若本进程要插到某等待者之前,且与更前方的请求及所有已
 *   持有锁都不冲突,则干脆跳过等待、立即 GrantLock(相当于在队列"前
 *   半段"做一次立即授予判定);
 * - 锁组成员合并计数:组内成员持有的锁并入 myHeldLocks(组间协同
 *   获取,见 lock.c 的组锁机制),但互等的判定仍各自独立;
 * - 插入位置确定后:把 MyProc 链入 waitProcs、更新 waitMask,并在
 *   MyProc 上登记 waitLock/waitProcLock/waitLockMode,置
 *   PROC_WAIT_STATUS_WAITING。
 * 调用约定:进入与返回时调用者都持有分区锁;dontWait 为 true(条件
 * 加锁)且必须等待时,返回 ERROR 但不入队。
 *
 * 【参数】locallock —— 本进程对该锁的本地记账(含 LOCK/PROCLOCK/
 *         hashcode);lockMethodTable —— 锁方法表(冲突矩阵);
 *         dontWait —— true 表示不许等待。
 * 【返回值】PROC_WAIT_STATUS_OK(立即授予)/ WAITING(已入队,应调
 *         ProcSleep)/ ERROR(即时死锁或 dontWait)。 */
ProcWaitStatus
JoinWaitQueue(LOCALLOCK *locallock, LockMethod lockMethodTable, bool dontWait)
{
	LOCKMODE	lockmode = locallock->tag.mode;
	LOCK	   *lock = locallock->lock;
	PROCLOCK   *proclock = locallock->proclock;
	uint32		hashcode = locallock->hashcode;
	LWLock	   *partitionLock PG_USED_FOR_ASSERTS_ONLY = LockHashPartitionLock(hashcode);
	dclist_head *waitQueue = &lock->waitProcs;
	PGPROC	   *insert_before = NULL;
	LOCKMASK	myProcHeldLocks;
	LOCKMASK	myHeldLocks;
	bool		early_deadlock = false;
	PGPROC	   *leader = MyProc->lockGroupLeader;

	Assert(LWLockHeldByMeInMode(partitionLock, LW_EXCLUSIVE));

	/*
	 * Set bitmask of locks this process already holds on this object.
	 */
	myHeldLocks = MyProc->heldLocks = proclock->holdMask;

	/*
	 * Determine which locks we're already holding.
	 *
	 * If group locking is in use, locks held by members of my locking group
	 * need to be included in myHeldLocks.  This is not required for relation
	 * extension lock which conflict among group members. However, including
	 * them in myHeldLocks will give group members the priority to get those
	 * locks as compared to other backends which are also trying to acquire
	 * those locks.  OTOH, we can avoid giving priority to group members for
	 * that kind of locks, but there doesn't appear to be a clear advantage of
	 * the same.
	 */
	myProcHeldLocks = proclock->holdMask;
	myHeldLocks = myProcHeldLocks;
	if (leader != NULL)
	{
		dlist_iter	iter;

		dlist_foreach(iter, &lock->procLocks)
		{
			PROCLOCK   *otherproclock;

			otherproclock = dlist_container(PROCLOCK, lockLink, iter.cur);

			if (otherproclock->groupLeader == leader)
				myHeldLocks |= otherproclock->holdMask;
		}
	}

	/*
	 * Determine where to add myself in the wait queue.
	 *
	 * Normally I should go at the end of the queue.  However, if I already
	 * hold locks that conflict with the request of any previous waiter, put
	 * myself in the queue just in front of the first such waiter. This is not
	 * a necessary step, since deadlock detection would move me to before that
	 * waiter anyway; but it's relatively cheap to detect such a conflict
	 * immediately, and avoid delaying till deadlock timeout.
	 *
	 * Special case: if I find I should go in front of some waiter, check to
	 * see if I conflict with already-held locks or the requests before that
	 * waiter.  If not, then just grant myself the requested lock immediately.
	 * This is the same as the test for immediate grant in LockAcquire, except
	 * we are only considering the part of the wait queue before my insertion
	 * point.
	 */
	if (myHeldLocks != 0 && !dclist_is_empty(waitQueue))
	{
		LOCKMASK	aheadRequests = 0;
		dlist_iter	iter;

		dclist_foreach(iter, waitQueue)
		{
			PGPROC	   *proc = dlist_container(PGPROC, waitLink, iter.cur);

			/*
			 * If we're part of the same locking group as this waiter, its
			 * locks neither conflict with ours nor contribute to
			 * aheadRequests.
			 */
			if (leader != NULL && leader == proc->lockGroupLeader)
				continue;

			/* Must he wait for me? */
			if (lockMethodTable->conflictTab[proc->waitLockMode] & myHeldLocks)
			{
				/* Must I wait for him ? */
				if (lockMethodTable->conflictTab[lockmode] & proc->heldLocks)
				{
					/*
					 * Yes, so we have a deadlock.  Easiest way to clean up
					 * correctly is to call RemoveFromWaitQueue(), but we
					 * can't do that until we are *on* the wait queue. So, set
					 * a flag to check below, and break out of loop.  Also,
					 * record deadlock info for later message.
					 */
					RememberSimpleDeadLock(MyProc, lockmode, lock, proc);
					early_deadlock = true;
					break;
				}
				/* I must go before this waiter.  Check special case. */
				if ((lockMethodTable->conflictTab[lockmode] & aheadRequests) == 0 &&
					!LockCheckConflicts(lockMethodTable, lockmode, lock,
										proclock))
				{
					/* Skip the wait and just grant myself the lock. */
					GrantLock(lock, proclock, lockmode);
					return PROC_WAIT_STATUS_OK;
				}

				/* Put myself into wait queue before conflicting process */
				insert_before = proc;
				break;
			}
			/* Nope, so advance to next waiter */
			aheadRequests |= LOCKBIT_ON(proc->waitLockMode);
		}
	}

	/*
	 * If we detected deadlock, give up without waiting.  This must agree with
	 * CheckDeadLock's recovery code.
	 */
	if (early_deadlock)
		return PROC_WAIT_STATUS_ERROR;

	/*
	 * At this point we know that we'd really need to sleep. If we've been
	 * commanded not to do that, bail out.
	 */
	if (dontWait)
		return PROC_WAIT_STATUS_ERROR;

	/*
	 * Insert self into queue, at the position determined above.
	 */
	if (insert_before)
		dclist_insert_before(waitQueue, &insert_before->waitLink, &MyProc->waitLink);
	else
		dclist_push_tail(waitQueue, &MyProc->waitLink);

	lock->waitMask |= LOCKBIT_ON(lockmode);

	/* Set up wait information in PGPROC object, too */
	MyProc->heldLocks = myProcHeldLocks;
	MyProc->waitLock = lock;
	MyProc->waitProcLock = proclock;
	MyProc->waitLockMode = lockmode;

	MyProc->waitStatus = PROC_WAIT_STATUS_WAITING;

	return PROC_WAIT_STATUS_WAITING;
}

/*
 * ProcSleep -- put process to sleep waiting on lock
 *
 * This must be called when JoinWaitQueue() returns PROC_WAIT_STATUS_WAITING.
 * Returns after the lock has been granted, or if a deadlock is detected.  Can
 * also bail out with ereport(ERROR), if some other error condition, or a
 * timeout or cancellation is triggered.
 *
 * Result is one of the following:
 *
 *  PROC_WAIT_STATUS_OK      - lock was granted
 *  PROC_WAIT_STATUS_ERROR   - a deadlock was detected
 */
/* (中文)让本进程在锁的等待队列上睡眠,直到拿到锁或检测到死锁。
 *
 * 【作用】JoinWaitQueue 返回 PROC_WAIT_STATUS_WAITING 后由 lock.c 调用:
 * 开启死锁/锁超时定时器,然后在循环里 WaitLatch(或热备下的恢复冲突
 * 处理)等待;被唤醒(可能是授予、伪唤醒、超时或取消)后检查死锁标志,
 * 必要时运行 CheckDeadLock;若被 autovacuum 阻塞且条件允许,向该
 * autovacuum worker 发 SIGINT 取消它;日志记录长等待;直到
 * waitStatus 离开 WAITING 才返回。结束后关闭定时器。
 *
 * 【设计思想】要点:
 * - 死锁检测延迟到等待超过 deadlock_timeout 才做(Cheap:大多数锁很快
 *   就拿到,无需为每次获取运行昂贵的检测);超时处理器只置标志
 *   (got_deadlock_timeout + 置 latch),真正的 DeadLockCheck 在循环里
 *   执行,信号处理器里只做信号安全的事;
 * - waitStart(pg_locks 的 waitstart 列)复用定时器框架取到的时间戳,
 *   不额外获取分区锁,允许短暂为 NULL(见函数内注释);
 * - 等待用 latch 而非信号量:SetLatch 是异步信号安全的,释放者无需
 *   持有分区锁即可唤醒;但"latch 被置"≠"锁已授予"(可能有其他唤醒
 *   来源),所以醒来后必须重查 waitStatus;
 * - 中断处理:CHECK_FOR_INTERRUPTS 及时响应取消;若在等待中被取消,
 *   依赖 LockErrorCleanup 摘除队列(共享表状态变更都已完成,睡眠循环
 *   本身没有必须清理的共享状态);
 * - 热备:等待者还要处理"与 Startup 进程的恢复冲突"——启动进程要
 *   拿锁而我们挡路时,可能被要求主动放弃(ResolveRecoveryConflictWithLock),
 *   并按要求记录/上报冲突日志;
 * - 统计与日志:deadlock 检查后累计 pgstat 锁等待时长;log_lock_waits
 *   打开时,长等待、软/硬死锁、获取成功等都会写日志,"still waiting"
 *   消息每轮最多打一次;
 * - 与 CheckDeadLock 的配合:硬死锁时 RemoveFromWaitQueue 会把
 *   waitStatus 置为 ERROR,循环据此退出并返回错误。
 *
 * 【参数】locallock —— 本进程对该锁的本地记账;调用前必须已通过
 *         SetStartTimeOfWaitOnLock 之类的机制把 awaitedLock 设好(前置
 *         断言 GetAwaitedLock() == locallock),并已释放分区锁。
 * 【返回值】PROC_WAIT_STATUS_OK = 已授予(唤醒者已更新共享表,调用者
 *         负责更新本地锁表);PROC_WAIT_STATUS_ERROR = 死锁(取消或超时
 *         时 ereport(ERROR))。 */
ProcWaitStatus
ProcSleep(LOCALLOCK *locallock)
{
	LOCKMODE	lockmode = locallock->tag.mode;
	LOCK	   *lock = locallock->lock;
	uint32		hashcode = locallock->hashcode;
	LWLock	   *partitionLock = LockHashPartitionLock(hashcode);
	TimestampTz standbyWaitStart = 0;
	bool		allow_autovacuum_cancel = true;
	bool		logged_recovery_conflict = false;
	bool		logged_lock_wait = false;
	ProcWaitStatus myWaitStatus;
	DeadLockState deadlock_state;

	/* The caller must've armed the on-error cleanup mechanism */
	Assert(GetAwaitedLock() == locallock);
	Assert(!LWLockHeldByMe(partitionLock));

	/*
	 * Now that we will successfully clean up after an ereport, it's safe to
	 * check to see if there's a buffer pin deadlock against the Startup
	 * process.  Of course, that's only necessary if we're doing Hot Standby
	 * and are not the Startup process ourselves.
	 */
	if (RecoveryInProgress() && !InRecovery)
		CheckRecoveryConflictDeadlock();

	/* Reset deadlock_state before enabling the timeout handler */
	deadlock_state = DS_NOT_YET_CHECKED;
	got_deadlock_timeout = false;

	/*
	 * Set timer so we can wake up after awhile and check for a deadlock. If a
	 * deadlock is detected, the handler sets MyProc->waitStatus =
	 * PROC_WAIT_STATUS_ERROR, allowing us to know that we must report failure
	 * rather than success.
	 *
	 * By delaying the check until we've waited for a bit, we can avoid
	 * running the rather expensive deadlock-check code in most cases.
	 *
	 * If LockTimeout is set, also enable the timeout for that.  We can save a
	 * few cycles by enabling both timeout sources in one call.
	 *
	 * If InHotStandby we set lock waits slightly later for clarity with other
	 * code.
	 */
	if (!InHotStandby)
	{
		if (LockTimeout > 0)
		{
			EnableTimeoutParams timeouts[2];

			timeouts[0].id = DEADLOCK_TIMEOUT;
			timeouts[0].type = TMPARAM_AFTER;
			timeouts[0].delay_ms = DeadlockTimeout;
			timeouts[1].id = LOCK_TIMEOUT;
			timeouts[1].type = TMPARAM_AFTER;
			timeouts[1].delay_ms = LockTimeout;
			enable_timeouts(timeouts, 2);
		}
		else
			enable_timeout_after(DEADLOCK_TIMEOUT, DeadlockTimeout);

		/*
		 * Use the current time obtained for the deadlock timeout timer as
		 * waitStart (i.e., the time when this process started waiting for the
		 * lock). Since getting the current time newly can cause overhead, we
		 * reuse the already-obtained time to avoid that overhead.
		 *
		 * Note that waitStart is updated without holding the lock table's
		 * partition lock, to avoid the overhead by additional lock
		 * acquisition. This can cause "waitstart" in pg_locks to become NULL
		 * for a very short period of time after the wait started even though
		 * "granted" is false. This is OK in practice because we can assume
		 * that users are likely to look at "waitstart" when waiting for the
		 * lock for a long time.
		 */
		pg_atomic_write_u64(&MyProc->waitStart,
							get_timeout_start_time(DEADLOCK_TIMEOUT));
	}
	else if (log_recovery_conflict_waits)
	{
		/*
		 * Set the wait start timestamp if logging is enabled and in hot
		 * standby.
		 */
		standbyWaitStart = GetCurrentTimestamp();
	}

	/*
	 * If somebody wakes us between LWLockRelease and WaitLatch, the latch
	 * will not wait. But a set latch does not necessarily mean that the lock
	 * is free now, as there are many other sources for latch sets than
	 * somebody releasing the lock.
	 *
	 * We process interrupts whenever the latch has been set, so cancel/die
	 * interrupts are processed quickly. This means we must not mind losing
	 * control to a cancel/die interrupt here.  We don't, because we have no
	 * shared-state-change work to do after being granted the lock (the
	 * grantor did it all).  We do have to worry about canceling the deadlock
	 * timeout and updating the locallock table, but if we lose control to an
	 * error, LockErrorCleanup will fix that up.
	 */
	do
	{
		if (InHotStandby)
		{
			bool		maybe_log_conflict =
				(standbyWaitStart != 0 && !logged_recovery_conflict);

			/* Set a timer and wait for that or for the lock to be granted */
			ResolveRecoveryConflictWithLock(locallock->tag.lock,
											maybe_log_conflict);

			/*
			 * Emit the log message if the startup process is waiting longer
			 * than deadlock_timeout for recovery conflict on lock.
			 */
			if (maybe_log_conflict)
			{
				TimestampTz now = GetCurrentTimestamp();

				if (TimestampDifferenceExceeds(standbyWaitStart, now,
											   DeadlockTimeout))
				{
					VirtualTransactionId *vxids;
					int			cnt;

					vxids = GetLockConflicts(&locallock->tag.lock,
											 AccessExclusiveLock, &cnt);

					/*
					 * Log the recovery conflict and the list of PIDs of
					 * backends holding the conflicting lock. Note that we do
					 * logging even if there are no such backends right now
					 * because the startup process here has already waited
					 * longer than deadlock_timeout.
					 */
					LogRecoveryConflict(RECOVERY_CONFLICT_LOCK,
										standbyWaitStart, now,
										cnt > 0 ? vxids : NULL, true);
					logged_recovery_conflict = true;
				}
			}
		}
		else
		{
			(void) WaitLatch(MyLatch, WL_LATCH_SET | WL_EXIT_ON_PM_DEATH, 0,
							 PG_WAIT_LOCK | locallock->tag.lock.locktag_type);
			ResetLatch(MyLatch);
			/* check for deadlocks first, as that's probably log-worthy */
			if (got_deadlock_timeout)
			{
				deadlock_state = CheckDeadLock();
				got_deadlock_timeout = false;
			}
			CHECK_FOR_INTERRUPTS();
		}

		/*
		 * waitStatus could change from PROC_WAIT_STATUS_WAITING to something
		 * else asynchronously.  Read it just once per loop to prevent
		 * surprising behavior (such as missing log messages).
		 */
		myWaitStatus = *((volatile ProcWaitStatus *) &MyProc->waitStatus);

		/*
		 * If we are not deadlocked, but are waiting on an autovacuum-induced
		 * task, send a signal to interrupt it.
		 */
		if (deadlock_state == DS_BLOCKED_BY_AUTOVACUUM && allow_autovacuum_cancel)
		{
			PGPROC	   *autovac = GetBlockingAutoVacuumPgproc();
			uint8		statusFlags;
			uint8		lockmethod_copy;
			LOCKTAG		locktag_copy;

			/*
			 * Grab info we need, then release lock immediately.  Note this
			 * coding means that there is a tiny chance that the process
			 * terminates its current transaction and starts a different one
			 * before we have a change to send the signal; the worst possible
			 * consequence is that a for-wraparound vacuum is canceled.  But
			 * that could happen in any case unless we were to do kill() with
			 * the lock held, which is much more undesirable.
			 */
			LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);
			statusFlags = ProcGlobal->statusFlags[autovac->pgxactoff];
			lockmethod_copy = lock->tag.locktag_lockmethodid;
			locktag_copy = lock->tag;
			LWLockRelease(ProcArrayLock);

			/*
			 * Only do it if the worker is not working to protect against Xid
			 * wraparound.
			 */
			if ((statusFlags & PROC_IS_AUTOVACUUM) &&
				!(statusFlags & PROC_VACUUM_FOR_WRAPAROUND))
			{
				int			pid = autovac->pid;

				/* report the case, if configured to do so */
				if (message_level_is_interesting(DEBUG1))
				{
					StringInfoData locktagbuf;
					StringInfoData logbuf;	/* errdetail for server log */

					initStringInfo(&locktagbuf);
					initStringInfo(&logbuf);
					DescribeLockTag(&locktagbuf, &locktag_copy);
					appendStringInfo(&logbuf,
									 "Process %d waits for %s on %s.",
									 MyProcPid,
									 GetLockmodeName(lockmethod_copy, lockmode),
									 locktagbuf.data);

					ereport(DEBUG1,
							(errmsg_internal("sending cancel to blocking autovacuum PID %d",
											 pid),
							 errdetail_log("%s", logbuf.data)));

					pfree(locktagbuf.data);
					pfree(logbuf.data);
				}

				/* send the autovacuum worker Back to Old Kent Road */
				if (kill(pid, SIGINT) < 0)
				{
					/*
					 * There's a race condition here: once we release the
					 * ProcArrayLock, it's possible for the autovac worker to
					 * close up shop and exit before we can do the kill().
					 * Therefore, we do not whinge about no-such-process.
					 * Other errors such as EPERM could conceivably happen if
					 * the kernel recycles the PID fast enough, but such cases
					 * seem improbable enough that it's probably best to issue
					 * a warning if we see some other errno.
					 */
					if (errno != ESRCH)
						ereport(WARNING,
								(errmsg("could not send signal to process %d: %m",
										pid)));
				}
			}

			/* prevent signal from being sent again more than once */
			allow_autovacuum_cancel = false;
		}

		/*
		 * If awoken after the deadlock check interrupt has run, increment the
		 * lock statistics counters and if log_lock_waits is on, then report
		 * about the wait.
		 */
		if (deadlock_state != DS_NOT_YET_CHECKED)
		{
			long		secs;
			int			usecs;
			long		msecs;

			INJECTION_POINT("deadlock-timeout-fired", NULL);
			TimestampDifference(get_timeout_start_time(DEADLOCK_TIMEOUT),
								GetCurrentTimestamp(),
								&secs, &usecs);
			/* Increment the lock statistics counters if done waiting. */
			if (myWaitStatus == PROC_WAIT_STATUS_OK)
				pgstat_count_lock_waits(locallock->tag.lock.locktag_type,
										(PgStat_Counter) secs * 1000000 + usecs);

			msecs = secs * 1000 + usecs / 1000;
			usecs = usecs % 1000;

			if (log_lock_waits)
			{
				StringInfoData buf,
							lock_waiters_sbuf,
							lock_holders_sbuf;
				const char *modename;
				int			lockHoldersNum = 0;

				initStringInfo(&buf);
				initStringInfo(&lock_waiters_sbuf);
				initStringInfo(&lock_holders_sbuf);

				DescribeLockTag(&buf, &locallock->tag.lock);
				modename = GetLockmodeName(locallock->tag.lock.locktag_lockmethodid,
										   lockmode);

				/* Gather a list of all lock holders and waiters */
				LWLockAcquire(partitionLock, LW_SHARED);
				GetLockHoldersAndWaiters(locallock, &lock_holders_sbuf,
										 &lock_waiters_sbuf, &lockHoldersNum);
				LWLockRelease(partitionLock);

				if (deadlock_state == DS_SOFT_DEADLOCK)
					ereport(LOG,
							(errmsg("process %d avoided deadlock for %s on %s by rearranging queue order after %ld.%03d ms",
									MyProcPid, modename, buf.data, msecs, usecs),
							 (errdetail_log_plural("Process holding the lock: %s. Wait queue: %s.",
												   "Processes holding the lock: %s. Wait queue: %s.",
												   lockHoldersNum, lock_holders_sbuf.data, lock_waiters_sbuf.data))));
				else if (deadlock_state == DS_HARD_DEADLOCK)
				{
					/*
					 * This message is a bit redundant with the error that
					 * will be reported subsequently, but in some cases the
					 * error report might not make it to the log (eg, if it's
					 * caught by an exception handler), and we want to ensure
					 * all long-wait events get logged.
					 */
					ereport(LOG,
							(errmsg("process %d detected deadlock while waiting for %s on %s after %ld.%03d ms",
									MyProcPid, modename, buf.data, msecs, usecs),
							 (errdetail_log_plural("Process holding the lock: %s. Wait queue: %s.",
												   "Processes holding the lock: %s. Wait queue: %s.",
												   lockHoldersNum, lock_holders_sbuf.data, lock_waiters_sbuf.data))));
				}

				if (myWaitStatus == PROC_WAIT_STATUS_WAITING)
				{
					/*
					 * Guard the "still waiting on lock" log message so it is
					 * reported at most once while waiting for the lock.
					 *
					 * Without this guard, the message can be emitted whenever
					 * the lock-wait sleep is interrupted (for example by
					 * SIGHUP for config reload or by
					 * client_connection_check_interval). For example, if
					 * client_connection_check_interval is set very low (e.g.,
					 * 100 ms), the message could be logged repeatedly,
					 * flooding the log and making it difficult to use.
					 */
					if (!logged_lock_wait)
					{
						ereport(LOG,
								(errmsg("process %d still waiting for %s on %s after %ld.%03d ms",
										MyProcPid, modename, buf.data, msecs, usecs),
								 (errdetail_log_plural("Process holding the lock: %s. Wait queue: %s.",
													   "Processes holding the lock: %s. Wait queue: %s.",
													   lockHoldersNum, lock_holders_sbuf.data, lock_waiters_sbuf.data))));
						logged_lock_wait = true;
					}
				}
				else if (myWaitStatus == PROC_WAIT_STATUS_OK)
					ereport(LOG,
							(errmsg("process %d acquired %s on %s after %ld.%03d ms",
									MyProcPid, modename, buf.data, msecs, usecs)));
				else
				{
					Assert(myWaitStatus == PROC_WAIT_STATUS_ERROR);

					/*
					 * Currently, the deadlock checker always kicks its own
					 * process, which means that we'll only see
					 * PROC_WAIT_STATUS_ERROR when deadlock_state ==
					 * DS_HARD_DEADLOCK, and there's no need to print
					 * redundant messages.  But for completeness and
					 * future-proofing, print a message if it looks like
					 * someone else kicked us off the lock.
					 */
					if (deadlock_state != DS_HARD_DEADLOCK)
						ereport(LOG,
								(errmsg("process %d failed to acquire %s on %s after %ld.%03d ms",
										MyProcPid, modename, buf.data, msecs, usecs),
								 (errdetail_log_plural("Process holding the lock: %s. Wait queue: %s.",
													   "Processes holding the lock: %s. Wait queue: %s.",
													   lockHoldersNum, lock_holders_sbuf.data, lock_waiters_sbuf.data))));
				}
				pfree(buf.data);
				pfree(lock_holders_sbuf.data);
				pfree(lock_waiters_sbuf.data);
			}

			/*
			 * At this point we might still need to wait for the lock. Reset
			 * state so we don't print the above messages again if
			 * log_lock_waits is on.
			 */
			deadlock_state = DS_NO_DEADLOCK;
		}
	} while (myWaitStatus == PROC_WAIT_STATUS_WAITING);

	/*
	 * Disable the timers, if they are still running.  As in LockErrorCleanup,
	 * we must preserve the LOCK_TIMEOUT indicator flag: if a lock timeout has
	 * already caused QueryCancelPending to become set, we want the cancel to
	 * be reported as a lock timeout, not a user cancel.
	 */
	if (!InHotStandby)
	{
		if (LockTimeout > 0)
		{
			DisableTimeoutParams timeouts[2];

			timeouts[0].id = DEADLOCK_TIMEOUT;
			timeouts[0].keep_indicator = false;
			timeouts[1].id = LOCK_TIMEOUT;
			timeouts[1].keep_indicator = true;
			disable_timeouts(timeouts, 2);
		}
		else
			disable_timeout(DEADLOCK_TIMEOUT, false);
	}

	/*
	 * Emit the log message if recovery conflict on lock was resolved but the
	 * startup process waited longer than deadlock_timeout for it.
	 */
	if (InHotStandby && logged_recovery_conflict)
		LogRecoveryConflict(RECOVERY_CONFLICT_LOCK,
							standbyWaitStart, GetCurrentTimestamp(),
							NULL, false);

	/*
	 * We don't have to do anything else, because the awaker did all the
	 * necessary updates of the lock table and MyProc. (The caller is
	 * responsible for updating the local lock table.)
	 */
	return myWaitStatus;
}


/*
 * ProcWakeup -- wake up a process by setting its latch.
 *
 *	 Also remove the process from the wait queue and set its waitLink invalid.
 *
 * The appropriate lock partition lock must be held by caller.
 *
 * XXX: presently, this code is only used for the "success" case, and only
 * works correctly for that case.  To clean up in failure case, would need
 * to twiddle the lock's request counts too --- see RemoveFromWaitQueue.
 * Hence, in practice the waitStatus parameter must be PROC_WAIT_STATUS_OK.
 */
/* (中文)唤醒等待队列上的一个进程(设置其 latch)。
 *
 * 【作用】由锁释放路径(ProcLockWakeup、RemoveFromWaitQueue)调用:把
 * 目标进程从锁的等待队列中摘除、清理其 wait 状态,再 SetLatch 唤醒。
 *
 * 【设计思想】调用者必须已持有相应分区锁(队列操作因此安全);当前实现
 * 只用于"成功授予"场景:摘除时不做请求计数回滚(失败场景的清理见
 * RemoveFromWaitQueue 的注释,故 waitStatus 参数实际恒为 OK)。
 * 唤醒用 SetLatch 而非信号量:latch 设置是异步信号安全的,且唤醒者
 * 不依赖目标进程执行任何动作。
 *
 * 【参数】proc —— 要唤醒的进程;waitStatus —— 传给目标进程的结果码
 *         (实践中为 PROC_WAIT_STATUS_OK)。
 * 【返回值】无 */
void
ProcWakeup(PGPROC *proc, ProcWaitStatus waitStatus)
{
	if (dlist_node_is_detached(&proc->waitLink))
		return;

	Assert(proc->waitStatus == PROC_WAIT_STATUS_WAITING);

	/* Remove process from wait queue */
	dclist_delete_from_thoroughly(&proc->waitLock->waitProcs, &proc->waitLink);

	/* Clean up process' state and pass it the ok/fail signal */
	proc->waitLock = NULL;
	proc->waitProcLock = NULL;
	proc->waitStatus = waitStatus;
	pg_atomic_write_u64(&proc->waitStart, 0);

	/* And awaken it */
	SetLatch(&proc->procLatch);
}

/*
 * ProcLockWakeup -- routine for waking up processes when a lock is
 *		released (or a prior waiter is aborted).  Scan all waiters
 *		for lock, waken any that are no longer blocked.
 *
 * The appropriate lock partition lock must be held by caller.
 */
/* (中文)扫描锁的等待队列,唤醒所有"不再被阻塞"的等待者。
 *
 * 【作用】锁被释放(或前方等待者退出)后由 lock.c 调用:按队列顺序遍历
 * 每个等待者,只要其请求模式与"更前方等待者的请求"及"已授予锁"都不
 * 冲突,就 GrantLock + ProcWakeup;否则保留在队列中,并把它请求的模式
 * 并入 aheadRequests,供后续等待者判定。
 *
 * 【设计思想】队列是"请求优先级"队列(见 JoinWaitQueue):越靠前越优先,
 * 因此只需单向扫描、累计前方请求掩码即可判定能否唤醒。唤醒一个进程
 * 会"消耗"可并发兼容的剩余容量,故共享模式的多个等待者可依次通过,
 * 排他模式只允许在队列最合适的位置被授予(冲突矩阵自动保证)。调用者
 * 必须持有分区锁;被唤醒进程的 waitStatus 由 ProcWakeup 置 OK。
 *
 * 【参数】lockMethodTable —— 锁方法表(冲突矩阵);lock —— 目标锁
 *         (其等待队列非空才会继续处理)。
 * 【返回值】无 */
void
ProcLockWakeup(LockMethod lockMethodTable, LOCK *lock)
{
	dclist_head *waitQueue = &lock->waitProcs;
	LOCKMASK	aheadRequests = 0;
	dlist_mutable_iter miter;

	if (dclist_is_empty(waitQueue))
		return;

	dclist_foreach_modify(miter, waitQueue)
	{
		PGPROC	   *proc = dlist_container(PGPROC, waitLink, miter.cur);
		LOCKMODE	lockmode = proc->waitLockMode;

		/*
		 * Waken if (a) doesn't conflict with requests of earlier waiters, and
		 * (b) doesn't conflict with already-held locks.
		 */
		if ((lockMethodTable->conflictTab[lockmode] & aheadRequests) == 0 &&
			!LockCheckConflicts(lockMethodTable, lockmode, lock,
								proc->waitProcLock))
		{
			/* OK to waken */
			GrantLock(lock, proc->waitProcLock, lockmode);
			/* removes proc from the lock's waiting process queue */
			ProcWakeup(proc, PROC_WAIT_STATUS_OK);
		}
		else
		{
			/*
			 * Lock conflicts: Don't wake, but remember requested mode for
			 * later checks.
			 */
			aheadRequests |= LOCKBIT_ON(lockmode);
		}
	}
}

/*
 * CheckDeadLock
 *
 * We only get to this routine, if DEADLOCK_TIMEOUT fired while waiting for a
 * lock to be released by some other process.  Check if there's a deadlock; if
 * not, just return.  If we have a real deadlock, remove ourselves from the
 * lock's wait queue.
 */
/* (中文)执行一次完整的死锁检测(deadlock_timeout 到期后触发)。
 *
 * 【作用】由 ProcSleep 的等待循环在 got_deadlock_timeout 置位后调用:
 * 依次以 LW_EXCLUSIVE 获取全部 NUM_LOCK_PARTITIONS 个分区锁,锁定整个
 * 共享锁表;若本进程已被摘出等待队列,直接判定无死锁;否则调用
 * deadlock.c 的 DeadLockCheck(MyProc) 分析等待图。硬死锁
 * (DS_HARD_DEADLOCK)时把本进程从等待队列摘除(RemoveFromWaitQueue 会
 * 把 waitStatus 置 PROC_WAIT_STATUS_ERROR,ProcSleep 据此报错);软死锁
 * (DS_SOFT_DEADLOCK)时检测器已调整队列顺序,本进程继续等待即可。
 *
 * 【设计思想】按分区号递增顺序加锁、逆序释放,防止多个进程各自乱序
 * 取分区锁造成 LWLock 级死锁;加锁过程处于临界区(LWLockAcquire 内部
 * HOLD_INTERRUPTS),整个检测不可被取消打断,并且本进程此刻绝不能
 * 持有任何分区锁,否则会自等死锁(见英文注释)。全部锁加齐后,检测器
 * 读到的是锁表的一致快照;若加锁期间已被授予(从队列摘除),说明死锁
 * 已消失,跳过昂贵的检测。释放按逆序进行,既避免与"递增顺序取多把锁"
 * 的其他进程相互阻塞,也避免 LWLockRelease 内部的 O(N^2) 开销。
 *
 * 【参数】无
 * 【返回值】DeadLockState:DS_NO_DEADLOCK(无死锁)/ DS_SOFT_DEADLOCK
 *         (软死锁,已调整)/ DS_HARD_DEADLOCK(硬死锁,本进程为牺牲者)。
 *         语义定义见 deadlock.c。 */
static DeadLockState
CheckDeadLock(void)
{
	int			i;
	DeadLockState result;

	/*
	 * Acquire exclusive lock on the entire shared lock data structures. Must
	 * grab LWLocks in partition-number order to avoid LWLock deadlock.
	 *
	 * Note that the deadlock check interrupt had better not be enabled
	 * anywhere that this process itself holds lock partition locks, else this
	 * will wait forever.  Also note that LWLockAcquire creates a critical
	 * section, so that this routine cannot be interrupted by cancel/die
	 * interrupts.
	 */
	for (i = 0; i < NUM_LOCK_PARTITIONS; i++)
		LWLockAcquire(LockHashPartitionLockByIndex(i), LW_EXCLUSIVE);

	/*
	 * Check to see if we've been awoken by anyone in the interim.
	 *
	 * If we have, we can return and resume our transaction -- happy day.
	 * Before we are awoken the process releasing the lock grants it to us so
	 * we know that we don't have to wait anymore.
	 *
	 * We check by looking to see if we've been unlinked from the wait queue.
	 * This is safe because we hold the lock partition lock.
	 */
	if (dlist_node_is_detached(&MyProc->waitLink))
	{
		result = DS_NO_DEADLOCK;
		goto check_done;
	}

#ifdef LOCK_DEBUG
	if (Debug_deadlocks)
		DumpAllLocks();
#endif

	/* Run the deadlock check */
	result = DeadLockCheck(MyProc);

	if (result == DS_HARD_DEADLOCK)
	{
		/*
		 * Oops.  We have a deadlock.
		 *
		 * Get this process out of wait state. (Note: we could do this more
		 * efficiently by relying on lockAwaited, but use this coding to
		 * preserve the flexibility to kill some other transaction than the
		 * one detecting the deadlock.)
		 *
		 * RemoveFromWaitQueue sets MyProc->waitStatus to
		 * PROC_WAIT_STATUS_ERROR, so ProcSleep will report an error after we
		 * return.
		 */
		Assert(MyProc->waitLock != NULL);
		RemoveFromWaitQueue(MyProc, LockTagHashCode(&(MyProc->waitLock->tag)));

		/*
		 * We're done here.  Transaction abort caused by the error that
		 * ProcSleep will raise will cause any other locks we hold to be
		 * released, thus allowing other processes to wake up; we don't need
		 * to do that here.  NOTE: an exception is that releasing locks we
		 * hold doesn't consider the possibility of waiters that were blocked
		 * behind us on the lock we just failed to get, and might now be
		 * wakable because we're not in front of them anymore.  However,
		 * RemoveFromWaitQueue took care of waking up any such processes.
		 */
	}

	/*
	 * And release locks.  We do this in reverse order for two reasons: (1)
	 * Anyone else who needs more than one of the locks will be trying to lock
	 * them in increasing order; we don't want to release the other process
	 * until it can get all the locks it needs. (2) This avoids O(N^2)
	 * behavior inside LWLockRelease.
	 */
check_done:
	for (i = NUM_LOCK_PARTITIONS; --i >= 0;)
		LWLockRelease(LockHashPartitionLockByIndex(i));

	return result;
}

/*
 * CheckDeadLockAlert - Handle the expiry of deadlock_timeout.
 *
 * NB: Runs inside a signal handler, be careful.
 */
/* (中文)deadlock_timeout 到期处理(在信号处理器内运行!)。
 *
 * 【作用】定时器框架在 DEADLOCK_TIMEOUT 到期时调用本函数:置位
 * got_deadlock_timeout 标志,并再次 SetLatch(MyLatch) 唤醒正在
 * WaitLatch 的 ProcSleep 循环。
 *
 * 【设计思想】信号处理器只能做异步信号安全的事:真正的死锁检测代价高、
 * 还可能加锁,必须推迟到主执行流(ProcSleep 循环)去做,这里只"置标志
 * + 置 latch"。重复 SetLatch 是安全的(设置一个已设置的 latch 只是
 * 一次廉价写),也覆盖了 handle_sig_alarm 先于标志置位设置 latch 的
 * 时序(见英文注释);保存/恢复 errno 是信号处理器的标准卫生要求。
 * 注意:经 procsignal_sigusr1_handler 路径进入时,该 handler 之后还会
 * 再置一次 latch,无碍。
 *
 * 【参数】无
 * 【返回值】无 */
void
CheckDeadLockAlert(void)
{
	int			save_errno = errno;

	got_deadlock_timeout = true;

	/*
	 * Have to set the latch again, even if handle_sig_alarm already did. Back
	 * then got_deadlock_timeout wasn't yet set... It's unlikely that this
	 * ever would be a problem, but setting a set latch again is cheap.
	 *
	 * Note that, when this function runs inside procsignal_sigusr1_handler(),
	 * the handler function sets the latch again after the latch is set here.
	 */
	SetLatch(MyLatch);
	errno = save_errno;
}

/*
 * GetLockHoldersAndWaiters - get lock holders and waiters for a lock
 *
 * Fill lock_holders_sbuf and lock_waiters_sbuf with the PIDs of processes holding
 * and waiting for the lock, and set lockHoldersNum to the number of lock holders.
 *
 * The lock table's partition lock must be held on entry and remains held on exit.
 */
/* (中文)收集一把锁的全部持有者与等待者的 PID,填充进日志字符串。
 *
 * 【作用】供 ProcSleep 的日志逻辑(log_lock_waits)使用:遍历锁的
 * procLocks 链表(PROCLOCK 同时记录"持有"与"等待"两类关系),把持有者
 * PID 拼进 lock_holders_sbuf、等待者 PID 拼进 lock_waiters_sbuf,并
 * 统计持有者个数。
 *
 * 【设计思想】判断是持有还是等待:某进程的 waitProcLock 指向当前
 * PROCLOCK 即"该 PROCLOCK 代表一次等待"(见 JoinWaitQueue 设置的
 * MyProc->waitProcLock),否则是持有。调用者须持有分区锁(进入与返回
 * 时都是),保证链表不被并发修改;输出格式为逗号分隔的 PID 列表。
 *
 * 【参数】locallock —— 本地锁记账(取其 LOCK);lock_holders_sbuf /
 *         lock_waiters_sbuf —— 输出:StringInfo 缓冲,接收持有者/等待者
 *         PID 列表;lockHoldersNum —— 输出:持有者数量。
 * 【返回值】无 */
void
GetLockHoldersAndWaiters(LOCALLOCK *locallock, StringInfo lock_holders_sbuf,
						 StringInfo lock_waiters_sbuf, int *lockHoldersNum)
{
	dlist_iter	proc_iter;
	PROCLOCK   *curproclock;
	LOCK	   *lock = locallock->lock;
	bool		first_holder = true,
				first_waiter = true;

#ifdef USE_ASSERT_CHECKING
	{
		uint32		hashcode = locallock->hashcode;
		LWLock	   *partitionLock = LockHashPartitionLock(hashcode);

		Assert(LWLockHeldByMe(partitionLock));
	}
#endif

	*lockHoldersNum = 0;

	/*
	 * Loop over the lock's procLocks to gather a list of all holders and
	 * waiters. Thus we will be able to provide more detailed information for
	 * lock debugging purposes.
	 *
	 * lock->procLocks contains all processes which hold or wait for this
	 * lock.
	 */
	dlist_foreach(proc_iter, &lock->procLocks)
	{
		curproclock =
			dlist_container(PROCLOCK, lockLink, proc_iter.cur);

		/*
		 * We are a waiter if myProc->waitProcLock == curproclock; we are a
		 * holder if it is NULL or something different.
		 */
		if (curproclock->tag.myProc->waitProcLock == curproclock)
		{
			if (first_waiter)
			{
				appendStringInfo(lock_waiters_sbuf, "%d",
								 curproclock->tag.myProc->pid);
				first_waiter = false;
			}
			else
				appendStringInfo(lock_waiters_sbuf, ", %d",
								 curproclock->tag.myProc->pid);
		}
		else
		{
			if (first_holder)
			{
				appendStringInfo(lock_holders_sbuf, "%d",
								 curproclock->tag.myProc->pid);
				first_holder = false;
			}
			else
				appendStringInfo(lock_holders_sbuf, ", %d",
								 curproclock->tag.myProc->pid);

			(*lockHoldersNum)++;
		}
	}
}

/*
 * ProcWaitForSignal - wait for a signal from another backend.
 *
 * As this uses the generic process latch the caller has to be robust against
 * unrelated wakeups: Always check that the desired state has occurred, and
 * wait again if not.
 */
/* (中文)等待来自其他进程的信号(基于进程 latch 的通用等待)。
 *
 * 【作用】把本进程挂起在 MyLatch 上,直到被 SetLatch 唤醒或 postmaster
 * 退出;醒来后复位 latch 并处理挂起的中断。供"等别的进程发信号"的
 * 场景使用(如 autovacuum 协调、procsignal 交互等)。
 *
 * 【设计思想】latch 是"会丢失事件的共享内存通知"的替代品,但"被置位"
 * 不保证目标事件已发生(可能有无关唤醒来源),故调用方必须循环检查
 * 自己的目标条件,不满足就再次等待(见英文注释);WL_EXIT_ON_PM_DEATH
 * 保证 postmaster 死亡时立即醒来以便退出。
 *
 * 【参数】wait_event_info —— 等待期间在 pg_stat_activity.wait_event
 *         中展示的事件标识。
 * 【返回值】无 */
void
ProcWaitForSignal(uint32 wait_event_info)
{
	(void) WaitLatch(MyLatch, WL_LATCH_SET | WL_EXIT_ON_PM_DEATH, 0,
					 wait_event_info);
	ResetLatch(MyLatch);
	CHECK_FOR_INTERRUPTS();
}

/*
 * ProcSendSignal - set the latch of a backend identified by ProcNumber
 */
/* (中文)按 ProcNumber 设置目标后端的 latch,唤醒它。
 *
 * 【作用】在已知对方 ProcNumber(ProcArray 下标)时向其发信号:校验范围
 * 后 SetLatch 目标 PGPROC 的共享 latch。
 *
 * 【设计思想】比"按 PID 查找再发信号"更直接,且 ProcNumber 是稳定的
 * 槽位标识(进程在槽位上时其 procLatch 恒定有效,不被回收)。调用方需
 * 自行保证目标进程仍在该槽位上(如持有 ProcArrayLock 或目标状态
 * 明确);SetLatch 是异步信号安全操作。
 *
 * 【参数】procNumber —— 目标进程的 ProcNumber(须 < allProcCount)。
 * 【返回值】无;越界时 elog(ERROR)。 */
void
ProcSendSignal(ProcNumber procNumber)
{
	if (procNumber < 0 || procNumber >= ProcGlobal->allProcCount)
		elog(ERROR, "procNumber out of range");

	SetLatch(&GetPGProcByNumber(procNumber)->procLatch);
}

/*
 * BecomeLockGroupLeader - designate process as lock group leader
 *
 * Once this function has returned, other processes can join the lock group
 * by calling BecomeLockGroupMember.
 */
/* (中文)把本进程指定为锁组组长(创建只含自己的锁组)。
 *
 * 【作用】并行查询(Parallel Query)的 leader 进程在让 worker 加入锁组
 * 前调用:在 leader 自己的分区锁保护下,把 lockGroupLeader 指向自己、
 * 把自己链入 lockGroupMembers。之后其他进程可调用
 * BecomeLockGroupMember 加入。
 *
 * 【设计思想】锁组的访问全部经由组长分区锁(LockHashPartitionLockByProc
 * 按 PGPROC 槽位计算)串行化;重复调用是幂等的(已是组长则直接返回)。
 * 锁组的意义:组内成员共享的锁不互相阻塞(见 JoinWaitQueue 与 lock.c
 * 的组锁逻辑),用于并行查询间协调。
 *
 * 【参数】无
 * 【返回值】无(前置条件:本进程不是任何组的跟随者)。 */
void
BecomeLockGroupLeader(void)
{
	LWLock	   *leader_lwlock;

	/* If we already did it, we don't need to do it again. */
	if (MyProc->lockGroupLeader == MyProc)
		return;

	/* We had better not be a follower. */
	Assert(MyProc->lockGroupLeader == NULL);

	/* Create single-member group, containing only ourselves. */
	leader_lwlock = LockHashPartitionLockByProc(MyProc);
	LWLockAcquire(leader_lwlock, LW_EXCLUSIVE);
	MyProc->lockGroupLeader = MyProc;
	dlist_push_head(&MyProc->lockGroupMembers, &MyProc->lockGroupLink);
	LWLockRelease(leader_lwlock);
}

/*
 * BecomeLockGroupMember - designate process as lock group member
 *
 * This is pretty straightforward except for the possibility that the leader
 * whose group we're trying to join might exit before we manage to do so;
 * and the PGPROC might get recycled for an unrelated process.  To avoid
 * that, we require the caller to pass the PID of the intended PGPROC as
 * an interlock.  Returns true if we successfully join the intended lock
 * group, and false if not.
 */
/* (中文)把本进程加入指定 leader 的锁组。
 *
 * 【作用】并行查询的 worker 进程在拿到 leader 的 PGPROC 指针后调用:
 * 在组长分区锁保护下,校验"leader 槽位仍是目标进程(pid 匹配)且确为
 * 组长"后,把本进程链入其 lockGroupMembers;校验失败返回 false(leader
 * 已退出、槽位被回收等)。
 *
 * 【设计思想】leader 可能在本进程加入前退出、其 PGPROC 槽位可能已被
 * 回收给别的进程,故要求调用方传 PID 作为交叉校验(英文注释称之为
 * interlock);分区锁按槽位计算,即使 leader 正在被回收也能取到正确的
 * 锁,配合 PID 校验消除"加入错误的组"的窗口。
 *
 * 【参数】leader —— 目标组长的 PGPROC 指针;pid —— 期望的组长 PID。
 * 【返回值】true = 成功加入;false = 组长状态不符(未加入)。 */
bool
BecomeLockGroupMember(PGPROC *leader, int pid)
{
	LWLock	   *leader_lwlock;
	bool		ok = false;

	/* Group leader can't become member of group */
	Assert(MyProc != leader);

	/* Can't already be a member of a group */
	Assert(MyProc->lockGroupLeader == NULL);

	/* PID must be valid. */
	Assert(pid != 0);

	/*
	 * Get lock protecting the group fields.  Note LockHashPartitionLockByProc
	 * calculates the proc number based on the PGPROC slot without looking at
	 * its contents, so we will acquire the correct lock even if the leader
	 * PGPROC is in process of being recycled.
	 */
	leader_lwlock = LockHashPartitionLockByProc(leader);
	LWLockAcquire(leader_lwlock, LW_EXCLUSIVE);

	/* Is this the leader we're looking for? */
	if (leader->pid == pid && leader->lockGroupLeader == leader)
	{
		/* OK, join the group */
		ok = true;
		MyProc->lockGroupLeader = leader;
		dlist_push_tail(&leader->lockGroupMembers, &MyProc->lockGroupLink);
	}
	LWLockRelease(leader_lwlock);

	return ok;
}
