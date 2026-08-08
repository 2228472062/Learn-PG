/*-------------------------------------------------------------------------
 *
 * lwlock.c
 *	  Lightweight lock manager
 *
 * Lightweight locks are intended primarily to provide mutual exclusion of
 * access to shared-memory data structures.  Therefore, they offer both
 * exclusive and shared lock modes (to support read/write and read-only
 * access to a shared object).  There are few other frammishes.  User-level
 * locking should be done with the full lock manager --- which depends on
 * LWLocks to protect its shared state.
 *
 * In addition to exclusive and shared modes, lightweight locks can be used to
 * wait until a variable changes value.  The variable is initially not set
 * when the lock is acquired with LWLockAcquire, i.e. it remains set to the
 * value it was set to when the lock was released last, and can be updated
 * without releasing the lock by calling LWLockUpdateVar.  LWLockWaitForVar
 * waits for the variable to be updated, or until the lock is free.  When
 * releasing the lock with LWLockReleaseClearVar() the value can be set to an
 * appropriate value for a free lock.  The meaning of the variable is up to
 * the caller, the lightweight lock code just assigns and compares it.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/lmgr/lwlock.c
 *
 * NOTES:
 *
 * This used to be a pretty straight forward reader-writer lock
 * implementation, in which the internal state was protected by a
 * spinlock. Unfortunately the overhead of taking the spinlock proved to be
 * too high for workloads/locks that were taken in shared mode very
 * frequently. Often we were spinning in the (obviously exclusive) spinlock,
 * while trying to acquire a shared lock that was actually free.
 *
 * Thus a new implementation was devised that provides wait-free shared lock
 * acquisition for locks that aren't exclusively locked.
 *
 * The basic idea is to have a single atomic variable 'lockcount' instead of
 * the formerly separate shared and exclusive counters and to use atomic
 * operations to acquire the lock. That's fairly easy to do for plain
 * rw-spinlocks, but a lot harder for something like LWLocks that want to wait
 * in the OS.
 *
 * For lock acquisition we use an atomic compare-and-exchange on the lockcount
 * variable. For exclusive lock we swap in a sentinel value
 * (LW_VAL_EXCLUSIVE), for shared locks we count the number of holders.
 *
 * To release the lock we use an atomic decrement to release the lock. If the
 * new value is zero (we get that atomically), we know we can/have to release
 * waiters.
 *
 * Obviously it is important that the sentinel value for exclusive locks
 * doesn't conflict with the maximum number of possible share lockers -
 * luckily MAX_BACKENDS makes that easily possible.
 *
 *
 * The attentive reader might have noticed that naively doing the above has a
 * glaring race condition: We try to lock using the atomic operations and
 * notice that we have to wait. Unfortunately by the time we have finished
 * queuing, the former locker very well might have already finished its
 * work. That's problematic because we're now stuck waiting inside the OS.

 * To mitigate those races we use a two phased attempt at locking:
 *	 Phase 1: Try to do it atomically, if we succeed, nice
 *	 Phase 2: Add ourselves to the waitqueue of the lock
 *	 Phase 3: Try to grab the lock again, if we succeed, remove ourselves from
 *			  the queue
 *	 Phase 4: Sleep till wake-up, goto Phase 1
 *
 * This protects us against the problem from above as nobody can release too
 *	  quick, before we're queued, since after Phase 2 we're already queued.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 的"轻量锁(LWLock)"机制。LWLock 是介于自旋锁
 * (spinlock)与重锁(heavyweight lock,见 lock.c)之间的一类锁:它比自旋锁
 * 拥有更丰富的语义(支持排他/共享两种模式、可以在操作系统中睡眠等待、
 * 被持有时屏蔽 cancel/die 中断),又比重锁轻量得多(没有锁表、冲突矩阵、
 * 资源所有者登记等完整体系),主要用于保护"对共享内存数据结构的短临界区
 * 访问",以及实现"等待某个共享变量变化"的同步原语。
 *
 * 【核心数据结构】
 * - LWLockPadded/LWLock:锁本体。关键字段是 32 位原子变量 state,它把
 *   "共享持有者计数、排他持有者标记、是否有等待者、唤醒是否进行中、等待
 *   列表是否上锁"全部压缩进一个原子字,使加锁/解锁可以用单条原子指令
 *   完成,无需先取自旋锁;另有一个等待队列 waiters(proclist,由 state 中
 *   的 LW_FLAG_LOCKED 位充当其互斥锁)与 tranche 编号;
 * - LWLockTranche(锁组):若干把锁共享一个 tranche ID 与名字,名字会作为
 *   pg_stat_activity.wait_event 的一部分展示给用户;
 * - held_lwlocks:本后端私有的"当前持有锁"数组,供错误恢复时批量释放
 *   (LWLockReleaseAll)与调试断言使用;
 * - LWLockTrancheShmemData:共享内存中扩展自定义 tranche 的登记表。
 *
 * 【设计思想】
 * 1. state 原子字 + CAS:排他锁用哨兵值 LW_VAL_EXCLUSIVE 交换,共享锁对
 *    计数器做原子加;锁空闲时共享获取完全无锁(wait-free),只有发生竞争
 *    才进入慢路径,解决了旧实现里"取共享锁也要抢自旋锁"的性能瓶颈;
 * 2. 两阶段获取协议(见 LWLockAcquire):先 CAS 试一次;失败则把本进程挂进
 *    等待队列(LWLockQueueSelf)再试一次;仍失败才真正用信号量睡眠。这样
 *    既消除了"排队前锁已被释放、结果在 OS 里空等"的经典竞态,又让解锁者
 *    只需检查状态字即可决定是否唤醒,无需为每次获取付出进程切换的代价;
 * 3. 唤醒策略:释放锁时只摘出队首一批可执行者(共享先于排他)唤醒,被唤醒
 *    者醒来后自行重试获取,配合 LW_FLAG_WAKE_IN_PROGRESS 防止重复唤醒;
 * 4. 变量等待:LWLockWaitForVar/LWLockUpdateVar 把"持锁 + 轮询共享变量"
 *    的经典模式打包成等待原语,用于 WAL 插入等待等场合;
 * 5. 中断安全:持锁期间 HOLD_INTERRUPTS 屏蔽取消信号,锁持有记录保存在
 *    held_lwlocks,出错时由 LWLockReleaseAll 统一恢复,防止临界区被中断
 *    打断而留下不一致的共享内存状态。
 *
 * 与相关模块的交互:自旋协议来自 s_lock.c(perform_spin_delay 等,用于
 * 等待队列互斥锁的竞争等待);进程睡眠/唤醒依赖 proc.c 分配的 PGPROC
 * 及其信号量(PGSemaphoreLock/Unlock);共享内存的注册与初始化走
 * ShmemCallbacks 机制(见 LWLockCallbacks)。
 *
 * -------------------------------------------------------------------------
 */
#include "postgres.h"

#include "miscadmin.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "port/pg_bitutils.h"
#include "storage/proc.h"
#include "storage/proclist.h"
#include "storage/procnumber.h"
#include "storage/spin.h"
#include "storage/subsystems.h"
#include "utils/memutils.h"
#include "utils/wait_event.h"

#ifdef LWLOCK_STATS
#include "utils/hsearch.h"
#endif


/* (中文)LWLock 状态字段 state(32 位原子字)的高 3 位是"标志位"区:
 * - LW_FLAG_HAS_WAITERS(bit 31):锁的等待队列非空,可能有进程排队等锁;
 * - LW_FLAG_WAKE_IN_PROGRESS(bit 30):释放者已把一批等待者摘出队列、
 *   唤醒正在进行中(防止这批等待者被再次唤醒);
 * - LW_FLAG_LOCKED(bit 29):等待队列的"互斥锁",保护 waiters 链表的
 *   并发访问(相当于旧实现里保护整个锁状态的自旋锁);
 * - LW_FLAG_BITS / LW_FLAG_MASK:标志区的位数与掩码,用于从 state 中
 *   分离出"持有者/计数"部分(低 29 位)与标志部分(高 3 位)。 */
#define LW_FLAG_HAS_WAITERS			((uint32) 1 << 31)
#define LW_FLAG_WAKE_IN_PROGRESS	((uint32) 1 << 30)
#define LW_FLAG_LOCKED				((uint32) 1 << 29)
#define LW_FLAG_BITS				3
#define LW_FLAG_MASK				(((1<<LW_FLAG_BITS)-1)<<(32-LW_FLAG_BITS))

/* (中文)state 原子字的低 29 位是"锁持有者"字段的编码:
 * - LW_VAL_EXCLUSIVE = MAX_BACKENDS + 1:排他锁的哨兵值,整个低 29 位等于
 *   该值表示"被排他持有"。取 MAX_BACKENDS+1 是因为它大于共享计数器所能
 *   达到的最大值 MAX_BACKENDS(共享持有者至多 MAX_BACKENDS 个),二者
 *   永不冲突(见下方 StaticAssertDecl);
 * - LW_VAL_SHARED = 1:成功获取一把共享锁时 state 的原子增量;
 * - LW_SHARED_MASK = MAX_BACKENDS:取出共享持有者计数所用的掩码
 *   (与后文 state & LW_SHARED_MASK 配合);
 * - LW_LOCK_MASK = MAX_BACKENDS | LW_VAL_EXCLUSIVE:取出低 29 位中的
 *   "计数 + 排他哨兵"全部位(不含标志位),用于判断锁是否被持有。 */
/* assumes MAX_BACKENDS is a (power of 2) - 1, checked below */
#define LW_VAL_EXCLUSIVE			(MAX_BACKENDS + 1)
#define LW_VAL_SHARED				1

/* already (power of 2)-1, i.e. suitable for a mask */
#define LW_SHARED_MASK				MAX_BACKENDS
#define LW_LOCK_MASK				(MAX_BACKENDS | LW_VAL_EXCLUSIVE)

/* (中文)编译期静态断言,保证上述编码假设成立:
 * - MAX_BACKENDS+1 是 2 的幂:排他哨兵值与共享计数在位级不重叠,可区分;
 * - MAX_BACKENDS 与标志位掩码不重叠:共享计数不可能"染上"高 3 位标志;
 * - LW_VAL_EXCLUSIVE 与标志位掩码不重叠:排他哨兵同样只占低 29 位。 */
StaticAssertDecl(((MAX_BACKENDS + 1) & MAX_BACKENDS) == 0,
				 "MAX_BACKENDS + 1 needs to be a power of 2");

StaticAssertDecl((MAX_BACKENDS & LW_FLAG_MASK) == 0,
				 "MAX_BACKENDS and LW_FLAG_MASK overlap");

StaticAssertDecl((LW_VAL_EXCLUSIVE & LW_FLAG_MASK) == 0,
				 "LW_VAL_EXCLUSIVE and LW_FLAG_MASK overlap");

/*
 * There are three sorts of LWLock "tranches":
 *
 * 1. The individually-named locks defined in lwlocklist.h each have their
 * own tranche.  We absorb the names of these tranches from there into
 * BuiltinTrancheNames here.
 *
 * 2. There are some predefined tranches for built-in groups of locks defined
 * in lwlocklist.h.  We absorb the names of these tranches, too.
 *
 * 3. Extensions can create new tranches, via either RequestNamedLWLockTranche
 * or LWLockNewTrancheId.  These are stored in shared memory and can be
 * accessed via LWLockTranches.
 *
 * All these names are user-visible as wait event names, so choose with care
 * ... and do not forget to update the documentation's list of wait events.
 */
/* (中文)内建 tranche 的名字表:由 lwlocklist.h 中的 PG_LWLOCK /
 * PG_LWLOCKTRANCHE 宏在编译期生成,数组下标即 tranche/lock 的 ID。这些
 * 名字会作为 pg_stat_activity.wait_event 的一部分展示给用户,故起名需
 * 谨慎,且不得忘记同步更新文档中的 wait event 列表。末尾的
 * StaticAssertDecl 校验表长度恰为 LWTRANCHE_FIRST_USER_DEFINED,防止
 * lwlocklist.h 增删条目时漏改本表。 */
static const char *const BuiltinTrancheNames[] = {
#define PG_LWLOCK(id, lockname) [id] = CppAsString(lockname),
#define PG_LWLOCKTRANCHE(id, lockname) [LWTRANCHE_##id] = CppAsString(lockname),
#include "storage/lwlocklist.h"
#undef PG_LWLOCK
#undef PG_LWLOCKTRANCHE
};

StaticAssertDecl(lengthof(BuiltinTrancheNames) ==
				 LWTRANCHE_FIRST_USER_DEFINED,
				 "missing entries in BuiltinTrancheNames[]");

/* (中文)共享内存中 LWLock 主数组的基址指针:内建"命名锁"、buffer 映射
 * 分区锁、锁表分区锁、谓词锁表分区锁与 RequestNamedLWLockTranche() 申请的
 * 扩展锁,都按固定偏移排布在这个数组里(偏移常量见 lwlock.h 的
 * BUFFER_MAPPING_LWLOCK_OFFSET 等),由 LWLockShmemRequest/LWLockShmemInit
 * 在启动阶段注册并初始化。 */
/* Main array of LWLocks in shared memory */
LWLockPadded *MainLWLockArray = NULL;

/*
 * We use this structure to keep track of locked LWLocks for release
 * during error recovery.  Normally, only a few will be held at once, but
 * occasionally the number can be much higher.
 */
/* (中文)LWLock 持有记录(见上):每次 LWLockAcquire / LWLockConditionalAcquire /
 * LWLockAcquireOrWait 成功时,把 (lock, mode) 追加进本后端的 held_lwlocks
 * 数组;LWLockRelease 时再删除。用途:
 * - LWLockReleaseAll() 在错误恢复(ereport ERROR)时据此把仍持有的锁全部
 *   释放,避免临界区被打断导致共享内存结构被并发破坏;
 * - LWLockHeldByMe 等调试断言据此判断"当前进程是否持有一把锁"。
 * MAX_SIMUL_LWLOCKS = 200:单进程最多同时持有的 LWLock 数量上限,超过
 * 即报错(正常场景通常只同时持有几个)。 */
#define MAX_SIMUL_LWLOCKS	200

/* struct representing the LWLocks we're holding */
typedef struct LWLockHandle
{
	LWLock	   *lock;
	LWLockMode	mode;
} LWLockHandle;

/* (中文)本后端当前持有的 LWLock 列表:num_held_lwlocks 为计数,
 * held_lwlocks 为定长数组(见 LWLockHandle 上方注释)。 */
static int	num_held_lwlocks = 0;
static LWLockHandle held_lwlocks[MAX_SIMUL_LWLOCKS];

/* (中文)扩展可注册的"用户自定义 tranche"数量上限 */
#define MAX_USER_DEFINED_TRANCHES 256

/*
 * Shared memory structure holding user-defined tranches.
 */
/* (中文)共享内存中"用户自定义 tranche"登记表(LWLockTrancheShmemData):
 * - user_defined[]:按 (tranche ID - LWTRANCHE_FIRST_USER_DEFINED) 作下标
 *   索引的条目数组。name 是该 tranche 的名字(作为 wait_event 展示);
 *   main_array_idx 记录这批锁在 MainLWLockArray 中的起始下标:经
 *   RequestNamedLWLockTranche() 申请的锁在启动阶段就分配在主数组里(该值
 *   为有效下标);经 LWLockNewTrancheId() 注册的 tranche 不占用主数组
 *   (该值为 -1,锁由调用方自行创建);
 * - num_user_defined:已登记的条目数;
 * - lock:保护上述字段的自旋锁。
 * 访问约定:LWLockTranches 指向共享内存;各进程另有本地缓存
 * LocalNumUserDefinedTranches,绝大多数"查名字"操作无需取自旋锁。 */
typedef struct LWLockTrancheShmemData
{
	/* This is indexed by tranche ID minus LWTRANCHE_FIRST_USER_DEFINED */
	struct
	{
		char		name[NAMEDATALEN];

		/*
		 * Index of the tranche's locks in MainLWLockArray if this tranche was
		 * allocated with RequestNamedLWLockTranche(), or -1 if the tranche
		 * was allocated with LWLockNewTrancheId()
		 */
		int			main_array_idx;
	}			user_defined[MAX_USER_DEFINED_TRANCHES];

	int			num_user_defined;	/* 'user_defined' entries in use */

	slock_t		lock;			/* protects the above */
} LWLockTrancheShmemData;

static LWLockTrancheShmemData *LWLockTranches;

/* (中文)本后端缓存的 LWLockTranches->num_user_defined 副本:登记表只会
 * 增加条目,故只要本地计数大于要查询的 ID 就无需取自旋锁(见
 * GetLWTrancheName 的注释)。 */
/* backend-local copy of LWLockTranches->num_user_defined */
static int	LocalNumUserDefinedTranches;

/*
 * NamedLWLockTrancheRequests is a list of tranches requested with
 * RequestNamedLWLockTranche().  It is only valid in the postmaster; after
 * startup the tranches are tracked in LWLockTranches in shared memory.
 */
/* (中文)postmaster 启动阶段的"命名 tranche 请求"条目(见上):每个
 * RequestNamedLWLockTranche() 调用登记一个 (tranche 名, 需要的锁数量)。
 * 该列表只存在于 postmaster 进程中(共享内存初始化完成后便不再使用),
 * 真正的共享登记由 LWLockShmemInit 复制进共享内存的 LWLockTranches。 */
typedef struct NamedLWLockTrancheRequest
{
	char		tranche_name[NAMEDATALEN];
	int			num_lwlocks;
} NamedLWLockTrancheRequest;

/* (中文)上述请求条目的链表,见 NamedLWLockTrancheRequest 的注释 */
static List *NamedLWLockTrancheRequests = NIL;

/* (中文)MainLWLockArray 中锁的总数(固定锁 + 命名 tranche 锁),只有
 * postmaster 阶段有效,由 LWLockShmemRequest 计算、LWLockShmemInit
 * 校验。 */
/* Size of MainLWLockArray.  Only valid in postmaster. */
static int	num_main_array_locks;

static void LWLockShmemRequest(void *arg);
static void LWLockShmemInit(void *arg);

/* (中文)向共享内存子系统注册的 request/init 回调对:request 阶段
 * (LWLockShmemRequest)声明"LWLock tranches 登记表"与"主锁数组"各自
 * 所需的字节数,init 阶段(LWLockShmemInit)完成置零与逐把锁的初始化。
 * 注册机制见 ShmemRequestStruct / ShmemCallbacks(共享内存子系统的
 * request/init 回调约定)。 */
const ShmemCallbacks LWLockCallbacks = {
	.request_fn = LWLockShmemRequest,
	.init_fn = LWLockShmemInit,
};


static inline void LWLockReportWaitStart(LWLock *lock);
static inline void LWLockReportWaitEnd(void);
static const char *GetLWTrancheName(uint16 trancheId);

#define T_NAME(lock) \
	GetLWTrancheName((lock)->tranche)
/* (中文)便捷宏:取得一把锁所属 tranche 的名字(用于调试输出与日志),
 * 实际工作由 GetLWTrancheName() 完成。 */

#ifdef LWLOCK_STATS
/* (中文)(仅 LWLOCK_STATS 编译时)LWLock 统计信息,用于研究锁的争用
 * 分布:
 * - lwlock_stats_key:(tranche, instance) 二元组,标识"统计对象是哪一把
 *   锁"(instance 即锁的地址);
 * - lwlock_stats:各计数器——sh_acquire_count/ex_acquire_count 分别统计
 *   共享/排他获取尝试次数;block_count 统计实际睡眠等待的次数;
 *   dequeue_self_count 统计"入队后发现自己其实不用等"而自行退队的次数;
 *   spin_delay_count 统计在等待队列互斥锁(LW_FLAG_LOCKED)上自旋的次数;
 * - lwlock_stats_htab:本后端私有的统计哈希表(统计按进程各自记录);
 * - lwlock_stats_dummy:共享内存初始化阶段(哈希表尚未创建)的兜底条目,
 *   此阶段的锁操作全部计入该伪条目。 */
typedef struct lwlock_stats_key
{
	int			tranche;
	void	   *instance;
}			lwlock_stats_key;

typedef struct lwlock_stats
{
	lwlock_stats_key key;
	int			sh_acquire_count;
	int			ex_acquire_count;
	int			block_count;
	int			dequeue_self_count;
	int			spin_delay_count;
}			lwlock_stats;

static HTAB *lwlock_stats_htab;
static lwlock_stats lwlock_stats_dummy;
#endif

#ifdef LOCK_DEBUG
/* (中文)(仅 LOCK_DEBUG 编译时)LWLock 追踪开关,对应 GUC 配置项
 * trace_lwlocks(见文件头 lock.c 中 LOCK_DEBUG 配置段落的说明)。 */
bool		Trace_lwlocks = false;

/* (中文)(仅 LOCK_DEBUG 编译时)带完整状态的 LWLock 调试打印:输出当前
 * 进程 PID、调用位置 where、锁名、排他/共享持有情况、是否有等待者、
 * 等待者计数与唤醒标志,用于分析加解锁路径。
 *
 * 【参数】where —— 调用点标识字符串(如 "LWLockAcquire");
 *         lock  —— 目标锁;mode —— 本次操作的锁模式。
 * 【返回值】无 */
inline static void
PRINT_LWDEBUG(const char *where, LWLock *lock, LWLockMode mode)
{
	/* hide statement & context here, otherwise the log is just too verbose */
	if (Trace_lwlocks)
	{
		uint32		state = pg_atomic_read_u32(&lock->state);

		ereport(LOG,
				(errhidestmt(true),
				 errhidecontext(true),
				 errmsg_internal("%d: %s(%s %p): excl %u shared %u haswaiters %u waiters %u waking %d",
								 MyProcPid,
								 where, T_NAME(lock), lock,
								 (state & LW_VAL_EXCLUSIVE) != 0,
								 state & LW_SHARED_MASK,
								 (state & LW_FLAG_HAS_WAITERS) != 0,
								 pg_atomic_read_u32(&lock->nwaiters),
								 (state & LW_FLAG_WAKE_IN_PROGRESS) != 0)));
	}
}

/* (中文)(仅 LOCK_DEBUG 编译时)带一条自定义消息的 LWLock 调试打印:
 * 输出调用位置、锁名与消息文本,是 PRINT_LWDEBUG 的简化版,用于在
 * 加解锁流程的各个关键节点打点(如 "waiting"、"awakened")。
 *
 * 【参数】where —— 调用点标识字符串;lock —— 目标锁;msg —— 消息文本。
 * 【返回值】无 */
inline static void
LOG_LWDEBUG(const char *where, LWLock *lock, const char *msg)
{
	/* hide statement & context here, otherwise the log is just too verbose */
	if (Trace_lwlocks)
	{
		ereport(LOG,
				(errhidestmt(true),
				 errhidecontext(true),
				 errmsg_internal("%s(%s %p): %s", where,
								 T_NAME(lock), lock, msg)));
	}
}

#else							/* not LOCK_DEBUG */
#define PRINT_LWDEBUG(a,b,c) ((void)0)
#define LOG_LWDEBUG(a,b,c) ((void)0)
#endif							/* LOCK_DEBUG */

#ifdef LWLOCK_STATS

static void init_lwlock_stats(void);
static void print_lwlock_stats(int code, Datum arg);
static lwlock_stats * get_lwlock_stats_entry(LWLock *lock);

/* (中文)(仅 LWLOCK_STATS 编译时)初始化本后端私有的 LWLock 统计哈希表,
 * 并注册进程退出回调,使进程退出时自动打印统计结果。
 *
 * 【作用】由 InitLWLockAccess() 调用(每个后端启动时执行一次)。若此前
 * 已创建过统计哈希表,先把整个内存上下文删除再重建(保证每次调用都从
 * 零开始统计);然后创建以 lwlock_stats_key 为键的哈希表,并注册
 * on_shmem_exit 回调 print_lwlock_stats。
 *
 * 【设计思想】统计会在临界区(critical section,见 LWLockAcquire 的
 * HOLD_INTERRUPTS)内被更新,更新时可能因查找失败而需要分配哈希条目;
 * 临界区内分配内存若耗尽会 PANIC,这原本是禁止的,但 LWLOCK_STATS 只是
 * 调试选项、正常生产环境不开启,故用 MemoryContextAllowInCriticalSection
 * 显式放行,冒一点内存耗尽的风险换取统计能力。
 *
 * 【参数】无
 * 【返回值】无 */
static void
init_lwlock_stats(void)
{
	HASHCTL		ctl;
	static MemoryContext lwlock_stats_cxt = NULL;
	static bool exit_registered = false;

	if (lwlock_stats_cxt != NULL)
		MemoryContextDelete(lwlock_stats_cxt);

	/*
	 * The LWLock stats will be updated within a critical section, which
	 * requires allocating new hash entries. Allocations within a critical
	 * section are normally not allowed because running out of memory would
	 * lead to a PANIC, but LWLOCK_STATS is debugging code that's not normally
	 * turned on in production, so that's an acceptable risk. The hash entries
	 * are small, so the risk of running out of memory is minimal in practice.
	 */
	lwlock_stats_cxt = AllocSetContextCreate(TopMemoryContext,
											 "LWLock stats",
											 ALLOCSET_DEFAULT_SIZES);
	MemoryContextAllowInCriticalSection(lwlock_stats_cxt, true);

	ctl.keysize = sizeof(lwlock_stats_key);
	ctl.entrysize = sizeof(lwlock_stats);
	ctl.hcxt = lwlock_stats_cxt;
	lwlock_stats_htab = hash_create("lwlock stats", 16384, &ctl,
									HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);
	if (!exit_registered)
	{
		on_shmem_exit(print_lwlock_stats, 0);
		exit_registered = true;
	}
}

/* (中文)(仅 LWLOCK_STATS 编译时)进程退出回调:把本进程统计到的所有
 * LWLock 数据逐条打印到 stderr。
 *
 * 【作用】经 on_shmem_exit 注册,进程(正常或异常)退出时执行:顺序扫描
 * 统计哈希表,为每把锁输出 PID、tranche 名、锁地址与各计数器。
 *
 * 【设计思想】打印期间先以排他模式获取 MainLWLockArray[0] 这把全局锁,
 * 避免多个后端同时退出时把各自的统计输出交错混在一起。
 *
 * 【参数】code —— 退出码(由 on_shmem_exit 框架传入,此处未使用);
 *         arg  —— 注册时的附加参数(此处未使用)。
 * 【返回值】无 */
static void
print_lwlock_stats(int code, Datum arg)
{
	HASH_SEQ_STATUS scan;
	lwlock_stats *lwstats;

	hash_seq_init(&scan, lwlock_stats_htab);

	/* Grab an LWLock to keep different backends from mixing reports */
	LWLockAcquire(&MainLWLockArray[0].lock, LW_EXCLUSIVE);

	while ((lwstats = (lwlock_stats *) hash_seq_search(&scan)) != NULL)
	{
		fprintf(stderr,
				"PID %d lwlock %s %p: shacq %u exacq %u blk %u spindelay %u dequeue self %u\n",
				MyProcPid, GetLWTrancheName(lwstats->key.tranche),
				lwstats->key.instance, lwstats->sh_acquire_count,
				lwstats->ex_acquire_count, lwstats->block_count,
				lwstats->spin_delay_count, lwstats->dequeue_self_count);
	}

	LWLockRelease(&MainLWLockArray[0].lock);
}

/* (中文)(仅 LWLOCK_STATS 编译时)取得指定锁的统计条目(不存在则创建),
 * 供各加解锁函数在热路径上累计计数器。
 *
 * 【作用】以锁的 (tranche, 地址) 为键在统计哈希表中查找;查到直接返回,
 * 查不到则以 HASH_ENTER 新建一个全零条目再返回。
 *
 * 【设计思想】共享内存初始化阶段统计哈希表尚未创建(此时持锁者多为
 * 启动代码),此阶段的操作全部归入唯一的伪条目 lwlock_stats_dummy,
 * 避免对空指针解引用,也省去初始化早期的无意义统计。
 *
 * 【参数】lock —— 要统计的目标锁。
 * 【返回值】指向该锁统计条目的指针(不会为 NULL)。 */
static lwlock_stats *
get_lwlock_stats_entry(LWLock *lock)
{
	lwlock_stats_key key;
	lwlock_stats *lwstats;
	bool		found;

	/*
	 * During shared memory initialization, the hash table doesn't exist yet.
	 * Stats of that phase aren't very interesting, so just collect operations
	 * on all locks in a single dummy entry.
	 */
	if (lwlock_stats_htab == NULL)
		return &lwlock_stats_dummy;

	/* Fetch or create the entry. */
	MemSet(&key, 0, sizeof(key));
	key.tranche = lock->tranche;
	key.instance = lock;
	lwstats = hash_search(lwlock_stats_htab, &key, HASH_ENTER, &found);
	if (!found)
	{
		lwstats->sh_acquire_count = 0;
		lwstats->ex_acquire_count = 0;
		lwstats->block_count = 0;
		lwstats->dequeue_self_count = 0;
		lwstats->spin_delay_count = 0;
	}
	return lwstats;
}
#endif							/* LWLOCK_STATS */


/*
 * Compute number of LWLocks required by user-defined tranches requested with
 * RequestNamedLWLockTranche().  These will be allocated in the main array.
 */
/* (中文)计算 RequestNamedLWLockTranche() 申请的全部"命名 tranche"锁的
 * 总数量:遍历 postmaster 阶段收集的请求链表,把每个请求的 num_lwlocks
 * 累加。该数量用于在 postmaster 阶段确定 MainLWLockArray 的总大小。
 *
 * 【作用】仅被 LWLockShmemRequest() 调用。
 *
 * 【参数】无
 * 【返回值】命名 tranche 锁的总数。 */
static int
NumLWLocksForNamedTranches(void)
{
	int			numLocks = 0;

	foreach_ptr(NamedLWLockTrancheRequest, request, NamedLWLockTrancheRequests)
	{
		numLocks += request->num_lwlocks;
	}

	return numLocks;
}

/*
 * Request shmem space for user-defined tranches and the main LWLock array.
 */
/* (中文)共享内存 request 阶段回调:向共享内存子系统声明 LWLock 子系统
 * 所需的空间。
 *
 * 【作用】postmaster(或独立后端)启动时由共享内存子系统统一调用,声明
 * 两块内存:
 * 1. "LWLock tranches"登记表(大小为 sizeof(LWLockTrancheShmemData)),
 *    结果写入全局指针 LWLockTranches;
 * 2. 主锁数组 MainLWLockArray:在 postmaster 阶段计算精确大小
 *    (NUM_FIXED_LWLOCKS + 命名 tranche 锁数);在子进程阶段用
 *    SHMEM_ATTACH_UNKNOWN_SIZE 表示"附加到 postmaster 已创建好的
 *    数组"(EXEC_BACKEND 模式由后端按同样布局重新附加)。
 *
 * 【设计思想】共享内存"先请求后初始化"两阶段:request 阶段只统计字节数
 * (此时可调用 palloc 等,postmaster 用它汇总所有子系统后一次性分配),
 * init 阶段(见 LWLockShmemInit)才真正使用这些内存。子进程不再重复
 * 计算大小,直接附加。
 *
 * 【参数】arg —— 回调参数(本文件未使用)。
 * 【返回值】无 */
static void
LWLockShmemRequest(void *arg)
{
	size_t		size;

	/* Space for user-defined tranches */
	ShmemRequestStruct(.name = "LWLock tranches",
					   .size = sizeof(LWLockTrancheShmemData),
					   .ptr = (void **) &LWLockTranches,
		);

	/* Space for the LWLock array */
	if (!IsUnderPostmaster)
	{
		num_main_array_locks = NUM_FIXED_LWLOCKS + NumLWLocksForNamedTranches();
		size = num_main_array_locks * sizeof(LWLockPadded);
	}
	else
		size = SHMEM_ATTACH_UNKNOWN_SIZE;

	ShmemRequestStruct(.name = "Main LWLock array",
					   .size = size,
					   .ptr = (void **) &MainLWLockArray,
		);
}

/*
 * Initialize shmem space for user-defined tranches and the main LWLock array.
 */
/* (中文)共享内存 init 阶段回调:初始化 LWLock 子系统的共享结构。
 *
 * 【作用】在共享内存分配完成后(postmaster 或独立后端)执行:
 * 1. 清零 LWLockTranches 的登记数并初始化其自旋锁;
 * 2. 按固定布局依次初始化 MainLWLockArray 中的每把锁:先是
 *    NUM_INDIVIDUAL_LWLOCKS 把内建命名锁(编号 id 即 tranche),
 *    然后是 buffer 映射分区锁、锁表分区锁、谓词锁表分区锁
 *    (各自 128/16/16 把,分别以 LWTRANCHE_BUFFER_MAPPING 等为 tranche),
 *    最后是 RequestNamedLWLockTranche() 申请的锁:把请求信息复制进共享
 *    登记表并初始化对应锁(其 tranche 为 LWTRANCHE_FIRST_USER_DEFINED
 *    + 登记表下标)。各段之间用 Assert 校验偏移常量与 LWLockShmemRequest
 *    的计算一致。
 *
 * 【设计思想】各段锁在数组中的位置由 lwlock.h 的
 * BUFFER_MAPPING_LWLOCK_OFFSET / LOCK_MANAGER_LWLOCK_OFFSET 等偏移常量
 * 硬编码约定,所有进程按同一布局访问,避免每把锁单独登记指针。
 *
 * 【参数】arg —— 回调参数(本文件未使用)。
 * 【返回值】无 */
static void
LWLockShmemInit(void *arg)
{
	int			pos;

	/* Initialize the dynamic-allocation counter for tranches */
	LWLockTranches->num_user_defined = 0;

	SpinLockInit(&LWLockTranches->lock);

	/*
	 * Allocate and initialize all LWLocks in the main array.  It includes all
	 * LWLocks for built-in tranches and those requested with
	 * RequestNamedLWLockTranche().
	 */
	pos = 0;

	/* Initialize all individual LWLocks in main array */
	for (int id = 0; id < NUM_INDIVIDUAL_LWLOCKS; id++)
		LWLockInitialize(&MainLWLockArray[pos++].lock, id);

	/* Initialize buffer mapping LWLocks in main array */
	Assert(pos == BUFFER_MAPPING_LWLOCK_OFFSET);
	for (int i = 0; i < NUM_BUFFER_PARTITIONS; i++)
		LWLockInitialize(&MainLWLockArray[pos++].lock, LWTRANCHE_BUFFER_MAPPING);

	/* Initialize lmgrs' LWLocks in main array */
	Assert(pos == LOCK_MANAGER_LWLOCK_OFFSET);
	for (int i = 0; i < NUM_LOCK_PARTITIONS; i++)
		LWLockInitialize(&MainLWLockArray[pos++].lock, LWTRANCHE_LOCK_MANAGER);

	/* Initialize predicate lmgrs' LWLocks in main array */
	Assert(pos == PREDICATELOCK_MANAGER_LWLOCK_OFFSET);
	for (int i = 0; i < NUM_PREDICATELOCK_PARTITIONS; i++)
		LWLockInitialize(&MainLWLockArray[pos++].lock, LWTRANCHE_PREDICATE_LOCK_MANAGER);

	/*
	 * Copy the info about any user-defined tranches into shared memory (so
	 * that other processes can see it), and initialize the requested LWLocks.
	 */
	Assert(pos == NUM_FIXED_LWLOCKS);
	foreach_ptr(NamedLWLockTrancheRequest, request, NamedLWLockTrancheRequests)
	{
		int			idx = (LWLockTranches->num_user_defined++);

		strlcpy(LWLockTranches->user_defined[idx].name,
				request->tranche_name,
				NAMEDATALEN);
		LWLockTranches->user_defined[idx].main_array_idx = pos;

		for (int i = 0; i < request->num_lwlocks; i++)
			LWLockInitialize(&MainLWLockArray[pos++].lock, LWTRANCHE_FIRST_USER_DEFINED + idx);
	}

	/* Cross-check that we agree on the total size with LWLockShmemRequest() */
	Assert(pos == num_main_array_locks);
}

/*
 * InitLWLockAccess - initialize backend-local state needed to hold LWLocks
 */
/* (中文)初始化"持有 LWLock 所需的进程本地状态"。
 *
 * 【作用】每个后端进程在拿到 PGPROC 后调用(见 proc.c 的
 * InitProcess/InitAuxiliaryProcess):目前只做一件事——在 LWLOCK_STATS
 * 编译选项下初始化本进程的 LWLock 统计哈希表。
 *
 * 【设计思想】LWLock 的全局共享状态(锁数组、tranche 登记表)在
 * LWLockShmemInit 中初始化;本函数只负责后端私有的部分,故可在
 * 任何"已获得 PGPROC"的时刻调用。
 *
 * 【参数】无
 * 【返回值】无 */
void
InitLWLockAccess(void)
{
#ifdef LWLOCK_STATS
	init_lwlock_stats();
#endif
}

/*
 * GetNamedLWLockTranche - returns the base address of LWLock from the
 *		specified tranche.
 *
 * Caller needs to retrieve the requested number of LWLocks starting from
 * the base lock address returned by this API.  This can be used for
 * tranches that are requested by using RequestNamedLWLockTranche() API.
 */
/* (中文)按名字取得"命名 tranche"锁数组的基地址。
 *
 * 【作用】供扩展(或核心代码)在启动完成后使用:以 tranche 名在共享登记表
 * 中查找,返回其在 MainLWLockArray 中的起始位置。调用方按
 * RequestNamedLWLockTranche() 请求的数量从该地址连续取用锁。
 *
 * 【设计思想】先把共享登记表的已登记数量刷进本地缓存
 * (LocalNumUserDefinedTranches,取自旋锁一次),再遍历共享登记表找名字;
 * 名字是常量配置,登记表只增不改,故读到一致数量后遍历是安全的。
 * 只接受 RequestNamedLWLockTranche() 登记的 tranche(其
 * main_array_idx 有效);LWLockNewTrancheId() 申请的锁不在主数组中,
 * 若用它查询会报错。
 *
 * 【参数】tranche_name —— 要查找的 tranche 名字(必须事先用
 *         RequestNamedLWLockTranche() 登记过)。
 * 【返回值】目标 tranche 第一把锁的地址(LWLockPadded 数组基址);
 *         名字不存在或不属于命名 tranche 时 ereport(ERROR)。 */
LWLockPadded *
GetNamedLWLockTranche(const char *tranche_name)
{
	SpinLockAcquire(&LWLockTranches->lock);
	LocalNumUserDefinedTranches = LWLockTranches->num_user_defined;
	SpinLockRelease(&LWLockTranches->lock);

	/*
	 * Obtain the position of base address of LWLock belonging to requested
	 * tranche_name in MainLWLockArray.  LWLocks for user-defined tranches
	 * requested with RequestNamedLWLockTranche() are placed in
	 * MainLWLockArray after fixed locks.
	 */
	for (int i = 0; i < LocalNumUserDefinedTranches; i++)
	{
		if (strcmp(LWLockTranches->user_defined[i].name,
				   tranche_name) == 0)
		{
			int			lock_pos = LWLockTranches->user_defined[i].main_array_idx;

			/*
			 * GetNamedLWLockTranche() should only be used for locks requested
			 * with RequestNamedLWLockTranche(), not those allocated with
			 * LWLockNewTrancheId().
			 */
			if (lock_pos == -1)
				elog(ERROR, "requested tranche was not registered with RequestNamedLWLockTranche()");
			return &MainLWLockArray[lock_pos];
		}
	}

	elog(ERROR, "requested tranche is not registered");

	/* just to keep compiler quiet */
	return NULL;
}

/*
 * Allocate a new tranche ID with the provided name.
 */
/* (中文)在共享登记表中注册一个新的用户自定义 tranche,返回其 tranche ID。
 *
 * 【作用】供扩展在运行时动态创建新 tranche:校验名字合法性与上限后,在
 * 自旋锁保护下分配一个登记表条目、写入名字,并把 main_array_idx 置为 -1
 * (表示这批锁不占用 MainLWLockArray,由调用方自行创建锁对象,但锁的
 * tranche 字段要填返回值)。
 *
 * 【设计思想】与 RequestNamedLWLockTranche() 的区别:后者必须在 postmaster
 * 的 shmem_request_hook 里调用、锁由 LWLockShmemInit 统一分配在主数组
 * 中;本函数可在任意时刻(如扩展加载时)调用,只分配"编号 + 名字",
 * 锁内存由调用方自理。二者共用同一登记表,故上限同为
 * MAX_USER_DEFINED_TRANCHES。
 *
 * 【参数】name —— tranche 名字(将作为 wait_event 展示;不能为 NULL,
 *         不能长于 NAMEDATALEN - 1)。
 * 【返回值】新 tranche 的 ID(不小于 LWTRANCHE_FIRST_USER_DEFINED);
 *         注册已满或名字非法时 ereport(ERROR)。 */
int
LWLockNewTrancheId(const char *name)
{
	int			idx;

	if (!name)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_NAME),
				 errmsg("tranche name cannot be NULL")));

	if (strlen(name) >= NAMEDATALEN)
		ereport(ERROR,
				(errcode(ERRCODE_NAME_TOO_LONG),
				 errmsg("tranche name too long"),
				 errdetail("LWLock tranche names must be no longer than %d bytes.",
						   NAMEDATALEN - 1)));

	/* The counter and the tranche names are protected by the spinlock */
	SpinLockAcquire(&LWLockTranches->lock);

	if (LWLockTranches->num_user_defined >= MAX_USER_DEFINED_TRANCHES)
	{
		SpinLockRelease(&LWLockTranches->lock);
		ereport(ERROR,
				(errmsg("maximum number of tranches already registered"),
				 errdetail("No more than %d tranches may be registered.",
						   MAX_USER_DEFINED_TRANCHES)));
	}

	/* Allocate an entry in the user_defined array */
	idx = (LWLockTranches->num_user_defined)++;

	/* update our local copy while we're at it */
	LocalNumUserDefinedTranches = LWLockTranches->num_user_defined;

	/* Initialize it */
	strlcpy(LWLockTranches->user_defined[idx].name, name, NAMEDATALEN);

	/* the locks are not in the main array */
	LWLockTranches->user_defined[idx].main_array_idx = -1;

	SpinLockRelease(&LWLockTranches->lock);

	return LWTRANCHE_FIRST_USER_DEFINED + idx;
}

/*
 * RequestNamedLWLockTranche
 *		Request that extra LWLocks be allocated during postmaster
 *		startup.
 *
 * This may only be called via the shmem_request_hook of a library that is
 * loaded into the postmaster via shared_preload_libraries.  Calls from
 * elsewhere will fail.
 *
 * The tranche name will be user-visible as a wait event name, so try to
 * use a name that fits the style for those.
 */
/* (中文)请求在 postmaster 启动阶段为扩展分配一批命名 LWLock。
 *
 * 【作用】扩展通过 shared_preload_libraries 机制把自己的
 * shmem_request_hook 挂进 postmaster 时,在其中调用本函数,登记
 * "tranche 名 + 需要的锁数量"。postmaster 据此扩大 MainLWLockArray
 * (见 NumLWLocksForNamedTranches/LWLockShmemInit),启动后扩展用
 * GetNamedLWLockTranche() 取用这批锁。
 *
 * 【设计思想】必须在共享内存 request 阶段(process_shmem_requests_in_progress
 * 为真,即 postmaster 执行 shmem_request_hook 期间)调用,否则无法影响
 * 主锁数组的尺寸,直接 FATAL。请求记录分配在 PostmasterContext(独立
 * 后端用 TopMemoryContext)中,避免被其他生命周期更短的上下文回收;
 * 只登记名字、数量,锁的初始化推迟到 LWLockShmemInit。
 *
 * 【参数】tranche_name —— tranche 名字(将作为 wait_event 展示,故命名
 *         风格应与内建事件一致;不能为 NULL/超长/与已有请求重名);
 *         num_lwlocks —— 需要的锁数量。
 * 【返回值】无;参数非法或阶段不对时 elog(FATAL/ERROR)。 */
void
RequestNamedLWLockTranche(const char *tranche_name, int num_lwlocks)
{
	NamedLWLockTrancheRequest *request;
	MemoryContext oldcontext;

	if (!process_shmem_requests_in_progress)
		elog(FATAL, "cannot request additional LWLocks outside shmem_request_hook");

	if (!tranche_name)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_NAME),
				 errmsg("tranche name cannot be NULL")));

	if (strlen(tranche_name) >= NAMEDATALEN)
		ereport(ERROR,
				(errcode(ERRCODE_NAME_TOO_LONG),
				 errmsg("tranche name too long"),
				 errdetail("LWLock tranche names must be no longer than %d bytes.",
						   NAMEDATALEN - 1)));

	if (list_length(NamedLWLockTrancheRequests) >= MAX_USER_DEFINED_TRANCHES)
		ereport(ERROR,
				(errmsg("maximum number of tranches already registered"),
				 errdetail("No more than %d tranches may be registered.",
						   MAX_USER_DEFINED_TRANCHES)));

	/* Check that the name isn't already in use */
	foreach_ptr(NamedLWLockTrancheRequest, existing, NamedLWLockTrancheRequests)
	{
		if (strcmp(existing->tranche_name, tranche_name) == 0)
			elog(ERROR, "requested tranche \"%s\" is already registered", tranche_name);
	}

	if (IsPostmasterEnvironment)
		oldcontext = MemoryContextSwitchTo(PostmasterContext);
	else
		oldcontext = MemoryContextSwitchTo(TopMemoryContext);

	request = palloc0(sizeof(NamedLWLockTrancheRequest));
	strlcpy(request->tranche_name, tranche_name, NAMEDATALEN);
	request->num_lwlocks = num_lwlocks;
	NamedLWLockTrancheRequests = lappend(NamedLWLockTrancheRequests, request);

	MemoryContextSwitchTo(oldcontext);
}

/*
 * LWLockInitialize - initialize a new lwlock; it's initially unlocked
 */
/* (中文)初始化一把新的 LWLock,使其处于"未锁定"状态。
 *
 * 【作用】在共享内存初始化(逐把初始化主数组中的锁)或扩展创建自有锁
 * 时调用:把 state 原子字清零(无持有者、无等待者、无标志)、登记 tranche
 * 编号、初始化等待队列 waiters。首次使用前必须且只需调用一次。
 *
 * 【设计思想】state 初值为 0 即"空闲";等待队列(proclist)的头部由
 * proclist_init 归零;tranche 编号会在锁生命周期内保持不变,用于
 * wait_event 归类与统计。LOCK_DEBUG 下额外的 nwaiters 计数器一并清零。
 *
 * 【参数】lock —— 目标锁;tranche_id —— 所属 tranche 的 ID(须已登记,
 *          否则 GetLWTrancheName 校验会报错)。
 * 【返回值】无 */
void
LWLockInitialize(LWLock *lock, int tranche_id)
{
	/* verify the tranche_id is valid */
	(void) GetLWTrancheName(tranche_id);

	pg_atomic_init_u32(&lock->state, 0);
#ifdef LOCK_DEBUG
	pg_atomic_init_u32(&lock->nwaiters, 0);
#endif
	lock->tranche = tranche_id;
	proclist_init(&lock->waiters);
}

/*
 * Report start of wait event for light-weight locks.
 *
 * This function will be used by all the light-weight lock calls which
 * needs to wait to acquire the lock.  This function distinguishes wait
 * event based on tranche and lock id.
 */
/* (中文)开始记录 LWLock 等待事件。
 *
 * 【作用】在所有可能睡眠等待 LWLock 的路径(LWLockAcquire、
 * LWLockAcquireOrWait、LWLockWaitForVar)真正入睡前调用:把
 * "PG_WAIT_LWLOCK | tranche ID" 报告给 pgstat,使 pg_stat_activity
 * 的 wait_event 能区分出当前正等在哪一把锁/哪一组锁上。
 *
 * 【参数】lock —— 正在等待的锁(取其 tranche 字段)。
 * 【返回值】无 */
static inline void
LWLockReportWaitStart(LWLock *lock)
{
	pgstat_report_wait_start(PG_WAIT_LWLOCK | lock->tranche);
}

/*
 * Report end of wait event for light-weight locks.
 */
/* (中文)结束 LWLock 等待事件的记录,与 LWLockReportWaitStart() 成对
 * 使用:等待者从睡眠中醒来(无论是否拿到锁)后调用,把 wait_event 恢复
 * 为空闲状态。
 *
 * 【参数】无
 * 【返回值】无 */
static inline void
LWLockReportWaitEnd(void)
{
	pgstat_report_wait_end();
}

/*
 * Return the name of an LWLock tranche.
 */
/* (中文)返回指定 tranche ID 的名字。
 *
 * 【作用】LWLock 各路径(T_NAME 宏、统计、wait_event 映射等)统一经由
 * 本函数把 tranche ID 转成人类可读的名字。
 *
 * 【设计思想】ID 小于 LWTRANCHE_FIRST_USER_DEFINED 的是内建 tranche 或
 * 内建命名锁,直接查编译期生成的 BuiltinTrancheNames 数组(无需加锁);
 * 否则是用户自定义 tranche,查共享登记表。登记表只增不改,故绝大多数
 * 查询可仅凭本地缓存 LocalNumUserDefinedTranches 判断目标是否已登记
 * (缓存足够新时免取自旋锁),只有缓存过旧时才在自旋锁保护下刷新——
 * 这正是 GetNamedLWLockTranche 也刷新同一计数器的原因(两处共享同一
 * 约定)。
 *
 * 【参数】trancheId —— 要查询的 tranche ID。
 * 【返回值】tranche 名字字符串;ID 非法(未登记)时 elog(ERROR)。 */
static const char *
GetLWTrancheName(uint16 trancheId)
{
	int			idx;

	/* Built-in tranche or individual LWLock? */
	if (trancheId < LWTRANCHE_FIRST_USER_DEFINED)
		return BuiltinTrancheNames[trancheId];

	/*
	 * It's an extension tranche, so look in LWLockTranches->user_defined.
	 */
	idx = trancheId - LWTRANCHE_FIRST_USER_DEFINED;

	/*
	 * We only ever add new entries to LWLockTranches->user_defined, so most
	 * lookups can avoid taking the spinlock as long as the backend-local
	 * counter (LocalNumUserDefinedTranches) is greater than the requested
	 * tranche ID.  Else, we need to first update the backend-local counter
	 * with the spinlock held before attempting the lookup again.  In
	 * practice, the latter case is probably rare.
	 */
	if (idx >= LocalNumUserDefinedTranches)
	{
		SpinLockAcquire(&LWLockTranches->lock);
		LocalNumUserDefinedTranches = LWLockTranches->num_user_defined;
		SpinLockRelease(&LWLockTranches->lock);

		if (idx >= LocalNumUserDefinedTranches)
			elog(ERROR, "tranche %d is not registered", trancheId);
	}

	return LWLockTranches->user_defined[idx].name;
}

/*
 * Return an identifier for an LWLock based on the wait class and event.
 */
/* (中文)返回一个 LWLock 的标识名,供 wait_event 显示层使用。
 *
 * 【作用】pgstat 的 wait_event 映射代码按 (wait class, event ID) 查名字;
 * LWLock 的 event ID 就是 tranche 编号,故这里直接委托
 * GetLWTrancheName()。
 *
 * 【设计思想】事件 ID 与 tranche ID 复用同一命名空间,省去一张额外的
 * 映射表;调用前断言 wait class 必须是 PG_WAIT_LWLOCK,防止误用。
 *
 * 【参数】classId —— wait class(必须为 PG_WAIT_LWLOCK);
 *         eventId —— 事件 ID(即 tranche 编号)。
 * 【返回值】tranche 名字字符串。 */
const char *
GetLWLockIdentifier(uint32 classId, uint16 eventId)
{
	Assert(classId == PG_WAIT_LWLOCK);
	/* The event IDs are just tranche numbers. */
	return GetLWTrancheName(eventId);
}

/*
 * Internal function that tries to atomically acquire the lwlock in the passed
 * in mode.
 *
 * This function will not block waiting for a lock to become free - that's the
 * caller's job.
 *
 * Returns true if the lock isn't free and we need to wait.
 */
/* (中文)尝试"非阻塞地"原子获取一把 LWLock(核心快速路径)。
 *
 * 【作用】对锁的 state 原子字做一次 CAS 循环:若锁当前空闲且与请求模式
 * 兼容,则原子地"记账"(排他:写入哨兵值 LW_VAL_EXCLUSIVE;共享:计数 +1)
 * 并返回 false(拿到锁);若锁被他人持有,则什么都不改、返回 true(需要
 * 等待)。本函数绝不睡眠,等不等的决定留给调用者。
 *
 * 【设计思想】
 * - 关键设计是"无论如何都执行 CAS"(即使锁不空闲也把原值写回):这使 CAS
 *   顺带充当内存屏障,保证后续共享内存读写在加锁点前后排序正确,虽然
 *   基准测试显示"只在空闲时交换"并未更优,但语义更简单;
 * - 排他模式要求低 29 位全部为零(既无共享持有者也无排他持有者);共享
 *   模式只要求无排他持有者(可与任意多个共享持有者共存);
 * - 读-算-比较-交换循环可处理与其它进程的并发竞争:CAS 失败说明有人
 *   抢先改过 state,用新值(old_state 被就地更新)重试;
 * - 无锁设计:整个过程只用原子指令,锁空闲时共享获取是 wait-free 的,
 *   彻底避免了旧实现"共享锁也要抢自旋锁"的瓶颈(见文件头 NOTES)。
 *
 * 【参数】lock —— 目标锁;mode —— 请求模式(LW_EXCLUSIVE 或 LW_SHARED)。
 * 【返回值】false = 已成功获取;true = 锁不空闲,需要等待。 */
static bool
LWLockAttemptLock(LWLock *lock, LWLockMode mode)
{
	uint32		old_state;

	Assert(mode == LW_EXCLUSIVE || mode == LW_SHARED);

	/*
	 * Read once outside the loop, later iterations will get the newer value
	 * via compare & exchange.
	 */
	old_state = pg_atomic_read_u32(&lock->state);

	/* loop until we've determined whether we could acquire the lock or not */
	while (true)
	{
		uint32		desired_state;
		bool		lock_free;

		desired_state = old_state;

		if (mode == LW_EXCLUSIVE)
		{
			lock_free = (old_state & LW_LOCK_MASK) == 0;
			if (lock_free)
				desired_state += LW_VAL_EXCLUSIVE;
		}
		else
		{
			lock_free = (old_state & LW_VAL_EXCLUSIVE) == 0;
			if (lock_free)
				desired_state += LW_VAL_SHARED;
		}

		/*
		 * Attempt to swap in the state we are expecting. If we didn't see
		 * lock to be free, that's just the old value. If we saw it as free,
		 * we'll attempt to mark it acquired. The reason that we always swap
		 * in the value is that this doubles as a memory barrier. We could try
		 * to be smarter and only swap in values if we saw the lock as free,
		 * but benchmark haven't shown it as beneficial so far.
		 *
		 * Retry if the value changed since we last looked at it.
		 */
		if (pg_atomic_compare_exchange_u32(&lock->state,
										   &old_state, desired_state))
		{
			if (lock_free)
			{
				/* Great! Got the lock. */
#ifdef LOCK_DEBUG
				if (mode == LW_EXCLUSIVE)
					lock->owner = MyProc;
#endif
				return false;
			}
			else
				return true;	/* somebody else has the lock */
		}
	}
	pg_unreachable();
}

/*
 * Lock the LWLock's wait list against concurrent activity.
 *
 * NB: even though the wait list is locked, non-conflicting lock operations
 * may still happen concurrently.
 *
 * Time spent holding mutex should be short!
 */
/* (中文)获取 LWLock 等待队列的互斥锁(设置 state 中的 LW_FLAG_LOCKED 位)。
 *
 * 【作用】所有需要修改 waiters 链表或 HAS_WAITERS/WAKE_IN_PROGRESS 标志
 * 的操作(LWLockQueueSelf/LWLockDequeueSelf/LWLockWakeup/LWLockUpdateVar)
 * 都必须先取得该互斥锁,以保证链表操作的原子性。
 *
 * 【设计思想】用原子 fetch_or 把 LW_FLAG_LOCKED 置位即视为加锁成功;
 * 若发现已被他人持有,则先用 s_lock.c 的自旋延迟(perform_spin_delay)
 * 原地等待标志清除,再重试。与锁本身的获取/释放(对低 29 位的 CAS/加减)
 * 互不相干——这正是"等待列表被锁住时,不冲突的加锁仍可并发进行"的
 * 原因(NB 注释所强调的)。互斥锁持有时长短,以自旋而非睡眠等待。
 *
 * 【参数】lock —— 目标锁。
 * 【返回值】无(返回时互斥锁已到手)。 */
static void
LWLockWaitListLock(LWLock *lock)
{
	uint32		old_state;
#ifdef LWLOCK_STATS
	lwlock_stats *lwstats;
	uint32		delays = 0;

	lwstats = get_lwlock_stats_entry(lock);
#endif

	while (true)
	{
		/*
		 * Always try once to acquire the lock directly, without setting up
		 * the spin-delay infrastructure. The work necessary for that shows up
		 * in profiles and is rarely necessary.
		 */
		old_state = pg_atomic_fetch_or_u32(&lock->state, LW_FLAG_LOCKED);
		if (likely(!(old_state & LW_FLAG_LOCKED)))
			break;				/* got lock */

		/* and then spin without atomic operations until lock is released */
		{
			SpinDelayStatus delayStatus;

			init_local_spin_delay(&delayStatus);

			while (old_state & LW_FLAG_LOCKED)
			{
				perform_spin_delay(&delayStatus);
				old_state = pg_atomic_read_u32(&lock->state);
			}
#ifdef LWLOCK_STATS
			delays += delayStatus.delays;
#endif
			finish_spin_delay(&delayStatus);
		}

		/*
		 * Retry. The lock might obviously already be re-acquired by the time
		 * we're attempting to get it again.
		 */
	}

#ifdef LWLOCK_STATS
	lwstats->spin_delay_count += delays;
#endif
}

/*
 * Unlock the LWLock's wait list.
 *
 * Note that it can be more efficient to manipulate flags and release the
 * locks in a single atomic operation.
 */
/* (中文)释放 LWLock 等待队列的互斥锁(清除 LW_FLAG_LOCKED 位),
 * 与 LWLockWaitListLock() 成对使用。
 *
 * 【作用】把 state 中的 LW_FLAG_LOCKED 位原子清除,表示等待队列操作
 * 完毕。配合 fetch_and 还可顺带修改其他标志(见 LWLockWakeup 中
 * 一次 CAS 同时更新多个标志位的写法,那正是英文注释"合并到一次原子
 * 操作更高效"所指)。
 *
 * 【参数】lock —— 目标锁。
 * 【返回值】无 */
static void
LWLockWaitListUnlock(LWLock *lock)
{
	uint32		old_state PG_USED_FOR_ASSERTS_ONLY;

	old_state = pg_atomic_fetch_and_u32(&lock->state, ~LW_FLAG_LOCKED);

	Assert(old_state & LW_FLAG_LOCKED);
}

/*
 * Wakeup all the lockers that currently have a chance to acquire the lock.
 */
/* (中文)唤醒当前"有机会拿到锁"的全部等待者。
 *
 * 【作用】由 LWLockRelease(锁被释放、且没有其他持有者挡路)调用:持等待
 * 队列互斥锁遍历 waiters,把队首一段可以立即执行的等待者摘出来,统一
 * 更新标志位,最后逐个用信号量唤醒。
 *
 * 【设计思想】唤醒策略:
 * - 先唤醒共享等待者,再唤醒排他等待者:一旦唤醒了一个排他等待者,
 *   它拿到锁后其他人还得等,故后续(包括它后面的共享者)都不再唤醒;
 *   唤醒一批共享者后,只允许一个排他者跟在后面;
 * - 摘出的等待者置 LW_WS_PENDING_WAKEUP(而非直接置 NOT_WAITING):
 *   先改状态、出链表,等真正发信号前再置 NOT_WAITING,并用
 *   pg_write_barrier 保证"链表摘除先于状态可见"——否则目标进程可能
 *   因其他原因醒来、为另一把锁重新入队,若入队发生在本进程摘除完成
 *   之前,链表会被写坏(见循环中的屏障注释);
 * - 置 LW_FLAG_WAKE_IN_PROGRESS:被唤醒者会自行重试获取,此后锁被再次
 *   释放时看到该标志就不重复唤醒这批人;LW_WAIT_UNTIL_FREE 模式的
 *   等待者(如 LWLockAcquireOrWait)不会自动重试,故唤醒它们时不计入
 *   该标志;
 * - 一次 CAS 同时完成:设置/清除 WAKE_IN_PROGRESS、清除 HAS_WAITERS
 *   (队列已空时)与释放互斥锁,减少原子操作次数;
 * - 唤醒对象是"还挂在等待队列里"的进程,因此被锁持有者自己先出队、
 *   再以临时链表 wakeup 收集,最后统一 PGSemaphoreUnlock。
 *
 * 【参数】lock —— 目标锁。
 * 【返回值】无 */
static void
LWLockWakeup(LWLock *lock)
{
	bool		new_wake_in_progress = false;
	bool		wokeup_somebody = false;
	proclist_head wakeup;
	proclist_mutable_iter iter;

	proclist_init(&wakeup);

	/* lock wait list while collecting backends to wake up */
	LWLockWaitListLock(lock);

	proclist_foreach_modify(iter, &lock->waiters, lwWaitLink)
	{
		PGPROC	   *waiter = GetPGProcByNumber(iter.cur);

		if (wokeup_somebody && waiter->lwWaitMode == LW_EXCLUSIVE)
			continue;

		proclist_delete(&lock->waiters, iter.cur, lwWaitLink);
		proclist_push_tail(&wakeup, iter.cur, lwWaitLink);

		if (waiter->lwWaitMode != LW_WAIT_UNTIL_FREE)
		{
			/*
			 * Prevent additional wakeups until retryer gets to run. Backends
			 * that are just waiting for the lock to become free don't retry
			 * automatically.
			 */
			new_wake_in_progress = true;

			/*
			 * Don't wakeup (further) exclusive locks.
			 */
			wokeup_somebody = true;
		}

		/*
		 * Signal that the process isn't on the wait list anymore. This allows
		 * LWLockDequeueSelf() to remove itself of the waitlist with a
		 * proclist_delete(), rather than having to check if it has been
		 * removed from the list.
		 */
		Assert(waiter->lwWaiting == LW_WS_WAITING);
		waiter->lwWaiting = LW_WS_PENDING_WAKEUP;

		/*
		 * Once we've woken up an exclusive lock, there's no point in waking
		 * up anybody else.
		 */
		if (waiter->lwWaitMode == LW_EXCLUSIVE)
			break;
	}

	Assert(proclist_is_empty(&wakeup) || pg_atomic_read_u32(&lock->state) & LW_FLAG_HAS_WAITERS);

	/* unset required flags, and release lock, in one fell swoop */
	{
		uint32		old_state;
		uint32		desired_state;

		old_state = pg_atomic_read_u32(&lock->state);
		while (true)
		{
			desired_state = old_state;

			/* compute desired flags */

			if (new_wake_in_progress)
				desired_state |= LW_FLAG_WAKE_IN_PROGRESS;
			else
				desired_state &= ~LW_FLAG_WAKE_IN_PROGRESS;

			if (proclist_is_empty(&lock->waiters))
				desired_state &= ~LW_FLAG_HAS_WAITERS;

			desired_state &= ~LW_FLAG_LOCKED;	/* release lock */

			if (pg_atomic_compare_exchange_u32(&lock->state, &old_state,
											   desired_state))
				break;
		}
	}

	/* Awaken any waiters I removed from the queue. */
	proclist_foreach_modify(iter, &wakeup, lwWaitLink)
	{
		PGPROC	   *waiter = GetPGProcByNumber(iter.cur);

		LOG_LWDEBUG("LWLockRelease", lock, "release waiter");
		proclist_delete(&wakeup, iter.cur, lwWaitLink);

		/*
		 * Guarantee that lwWaiting being unset only becomes visible once the
		 * unlink from the link has completed. Otherwise the target backend
		 * could be woken up for other reason and enqueue for a new lock - if
		 * that happens before the list unlink happens, the list would end up
		 * being corrupted.
		 *
		 * The barrier pairs with the LWLockWaitListLock() when enqueuing for
		 * another lock.
		 */
		pg_write_barrier();
		waiter->lwWaiting = LW_WS_NOT_WAITING;
		PGSemaphoreUnlock(waiter->sem);
	}
}

/*
 * Add ourselves to the end of the queue.
 *
 * NB: Mode can be LW_WAIT_UNTIL_FREE here!
 */
/* (中文)把本进程挂入目标锁的等待队列。
 *
 * 【作用】在两阶段获取协议的慢路径中使用:在等待队列互斥锁保护下,把
 * 本进程的 PGPROC(以 MyProcNumber 为链表键)链入锁的 waiters,并把
 * 本进程的 lwWaiting/lwWaitMode 置为等待状态;随后设置锁的
 * LW_FLAG_HAS_WAITERS 标志(在互斥锁内设置,保证与队列内容一致)。
 *
 * 【设计思想】
 * - LW_WAIT_UNTIL_FREE 模式(等待"锁变空",不争抢)的等待者总是插在
 *   队首——他们在唤醒顺序上优先,且 LWLockUpdateVar 只需扫队首一段
 *   即可找到他们;
 * - 模式参数允许 LW_WAIT_UNTIL_FREE,这是与 LWLockAcquire 的唯一差别;
 * - 前置条件:本进程 lwWaiting 必须为 NOT_WAITING(不允许在等另一把锁
 *   时再入队,否则会破坏单一等待状态),且必须有 PGPROC(否则无法睡眠)。
 *
 * 【参数】lock —— 目标锁;mode —— 等待模式(LW_EXCLUSIVE/LW_SHARED/
 *         LW_WAIT_UNTIL_FREE)。
 * 【返回值】无(返回时已在队列中;锁的 HAS_WAITERS 标志已置位)。 */
static void
LWLockQueueSelf(LWLock *lock, LWLockMode mode)
{
	/*
	 * If we don't have a PGPROC structure, there's no way to wait. This
	 * should never occur, since MyProc should only be null during shared
	 * memory initialization.
	 */
	if (MyProc == NULL)
		elog(PANIC, "cannot wait without a PGPROC structure");

	if (MyProc->lwWaiting != LW_WS_NOT_WAITING)
		elog(PANIC, "queueing for lock while waiting on another one");

	LWLockWaitListLock(lock);

	/* setting the flag is protected by the spinlock */
	pg_atomic_fetch_or_u32(&lock->state, LW_FLAG_HAS_WAITERS);

	MyProc->lwWaiting = LW_WS_WAITING;
	MyProc->lwWaitMode = mode;

	/* LW_WAIT_UNTIL_FREE waiters are always at the front of the queue */
	if (mode == LW_WAIT_UNTIL_FREE)
		proclist_push_head(&lock->waiters, MyProcNumber, lwWaitLink);
	else
		proclist_push_tail(&lock->waiters, MyProcNumber, lwWaitLink);

	/* Can release the mutex now */
	LWLockWaitListUnlock(lock);

#ifdef LOCK_DEBUG
	pg_atomic_fetch_add_u32(&lock->nwaiters, 1);
#endif
}

/*
 * Remove ourselves from the waitlist.
 *
 * This is used if we queued ourselves because we thought we needed to sleep
 * but, after further checking, we discovered that we don't actually need to
 * do so.
 */
/* (中文)把本进程从等待队列中摘除(撤销 LWLockQueueSelf 的效果)。
 *
 * 【作用】两阶段获取协议中"入队后再试一次拿到了锁"时调用:若本进程仍
 * 在队列中,将其摘除并恢复 lwWaiting;若已被别人摘除(说明刚被唤醒),
 * 则吸收掉这次多余的唤醒信号。
 *
 * 【设计思想】与 LWLockQueueSelf 一样在等待队列互斥锁内操作,判断"是否
 * 还在队列"用 lwWaiting == LW_WS_WAITING,与摘除动作同锁,故无竞态:
 * - 自己还在队列:直接摘除;若队列因此变空,顺带清除 HAS_WAITERS;
 * - 已被摘除(LW_WS_PENDING_WAKEUP,唤醒者已安排信号):清除
 *   WAKE_IN_PROGRESS 标志(唤醒者会设置它),然后等信号到来直到
 *   lwWaiting 变为 NOT_WAITING,避免 lwWaiting 在未来某个不合适的
 *   时刻被置回初值;多吸收的信号(extraWaits)再补发回去,保持信号量
 *   计数一致。这套"吸收多余唤醒"的逻辑与 LWLockAcquire 睡眠循环中
 *   的 extraWaits 同理。
 *
 * 【参数】lock —— 目标锁。
 * 【返回值】无 */
static void
LWLockDequeueSelf(LWLock *lock)
{
	bool		on_waitlist;

#ifdef LWLOCK_STATS
	lwlock_stats *lwstats;

	lwstats = get_lwlock_stats_entry(lock);

	lwstats->dequeue_self_count++;
#endif

	LWLockWaitListLock(lock);

	/*
	 * Remove ourselves from the waitlist, unless we've already been removed.
	 * The removal happens with the wait list lock held, so there's no race in
	 * this check.
	 */
	on_waitlist = MyProc->lwWaiting == LW_WS_WAITING;
	if (on_waitlist)
		proclist_delete(&lock->waiters, MyProcNumber, lwWaitLink);

	if (proclist_is_empty(&lock->waiters) &&
		(pg_atomic_read_u32(&lock->state) & LW_FLAG_HAS_WAITERS) != 0)
	{
		pg_atomic_fetch_and_u32(&lock->state, ~LW_FLAG_HAS_WAITERS);
	}

	/* XXX: combine with fetch_and above? */
	LWLockWaitListUnlock(lock);

	/* clear waiting state again, nice for debugging */
	if (on_waitlist)
		MyProc->lwWaiting = LW_WS_NOT_WAITING;
	else
	{
		int			extraWaits = 0;

		/*
		 * Somebody else dequeued us and has or will wake us up. Deal with the
		 * superfluous absorption of a wakeup.
		 */

		/*
		 * Clear LW_FLAG_WAKE_IN_PROGRESS if somebody woke us before we
		 * removed ourselves - they'll have set it.
		 */
		pg_atomic_fetch_and_u32(&lock->state, ~LW_FLAG_WAKE_IN_PROGRESS);

		/*
		 * Now wait for the scheduled wakeup, otherwise our ->lwWaiting would
		 * get reset at some inconvenient point later. Most of the time this
		 * will immediately return.
		 */
		for (;;)
		{
			PGSemaphoreLock(MyProc->sem);
			if (MyProc->lwWaiting == LW_WS_NOT_WAITING)
				break;
			extraWaits++;
		}

		/*
		 * Fix the process wait semaphore's count for any absorbed wakeups.
		 */
		while (extraWaits-- > 0)
			PGSemaphoreUnlock(MyProc->sem);
	}

#ifdef LOCK_DEBUG
	{
		/* not waiting anymore */
		uint32		nwaiters PG_USED_FOR_ASSERTS_ONLY = pg_atomic_fetch_sub_u32(&lock->nwaiters, 1);

		Assert(nwaiters < MAX_BACKENDS);
	}
#endif
}

/*
 * LWLockAcquire - acquire a lightweight lock in the specified mode
 *
 * If the lock is not available, sleep until it is.  Returns true if the lock
 * was available immediately, false if we had to sleep.
 *
 * Side effect: cancel/die interrupts are held off until lock release.
 */
/* (中文)以指定模式获取一把轻量锁(可能睡眠等待),本文件最核心的入口。
 *
 * 【作用】几乎全部共享内存临界区的统一加锁入口。锁当前空闲则立即返回
 * true;否则入队并睡眠,直到被释放者唤醒并成功获取,返回 false(曾等待)。
 * 获取成功后,锁会登记进 held_lwlocks,并在整个持有期间屏蔽 cancel/die
 * 中断(直到 LWLockRelease 才解除)。
 *
 * 【设计思想】两阶段获取协议(见文件头 NOTES):
 * 1. 快速路径:LWLockAttemptLock 直接 CAS 尝试,空闲即成功(无锁、wait-free);
 * 2. 慢路径:先 LWLockQueueSelf 把自己挂进等待队列,再试一次——若拿到锁
 *    就 LWLockDequeueSelf 撤销入队;仍失败才真正 PGSemaphoreLock 睡眠。
 *    第二次尝试保证了"我们入队后,任何释放者都能看见队列里的我们",
 *    消除"排队前锁已被释放、却要在 OS 里空等"的竞态;
 * 3. 睡眠循环:被唤醒后若 lwWaiting 仍非 NOT_WAITING(伪唤醒,如其他
 *    来源的 latch),继续等待,吸收的信号计数用 extraWaits 记下、拿到锁
 *    后补发;醒来后清除 WAKE_IN_PROGRESS(允许后续释放再次唤醒),
 *    回到第 1 步重试;
 * 4. 唤醒不直接授予锁:释放者只发信号,获锁者自行重试。代价是释放的
 *    瞬间可能再次撞上竞争,但换来"进程无需为每次加锁切换"——LWLock
 *    临界区短,同一进程常在一次 CPU 时间片内反复加解锁(见循环上方的
 *    29-Dec-01 邮件讨论)。
 * 安全约束:持锁期间 HOLD_INTERRUPTS,防止中断处理触碰同一共享结构;
 * 等待(睡眠)不在临界区,可安全取消,出错路径见 LWLockReleaseAll。
 *
 * 【参数】lock —— 目标锁;mode —— LW_EXCLUSIVE(排他)或 LW_SHARED(共享)。
 * 【返回值】true = 立即可得(未等待);false = 曾入队睡眠。睡眠期间若
 *         持锁超限(held_lwlocks 满)会 elog(ERROR);无 PGPROC 时 Assert
 *         失败(PANIC)。 */
bool
LWLockAcquire(LWLock *lock, LWLockMode mode)
{
	PGPROC	   *proc = MyProc;
	bool		result = true;
	int			extraWaits = 0;
#ifdef LWLOCK_STATS
	lwlock_stats *lwstats;

	lwstats = get_lwlock_stats_entry(lock);
#endif

	Assert(mode == LW_SHARED || mode == LW_EXCLUSIVE);

	PRINT_LWDEBUG("LWLockAcquire", lock, mode);

#ifdef LWLOCK_STATS
	/* Count lock acquisition attempts */
	if (mode == LW_EXCLUSIVE)
		lwstats->ex_acquire_count++;
	else
		lwstats->sh_acquire_count++;
#endif							/* LWLOCK_STATS */

	/*
	 * We can't wait if we haven't got a PGPROC.  This should only occur
	 * during bootstrap or shared memory initialization.  Put an Assert here
	 * to catch unsafe coding practices.
	 */
	Assert(!(proc == NULL && IsUnderPostmaster));

	/* Ensure we will have room to remember the lock */
	if (num_held_lwlocks >= MAX_SIMUL_LWLOCKS)
		elog(ERROR, "too many LWLocks taken");

	/*
	 * Lock out cancel/die interrupts until we exit the code section protected
	 * by the LWLock.  This ensures that interrupts will not interfere with
	 * manipulations of data structures in shared memory.
	 */
	HOLD_INTERRUPTS();

	/*
	 * Loop here to try to acquire lock after each time we are signaled by
	 * LWLockRelease.
	 *
	 * NOTE: it might seem better to have LWLockRelease actually grant us the
	 * lock, rather than retrying and possibly having to go back to sleep. But
	 * in practice that is no good because it means a process swap for every
	 * lock acquisition when two or more processes are contending for the same
	 * lock.  Since LWLocks are normally used to protect not-very-long
	 * sections of computation, a process needs to be able to acquire and
	 * release the same lock many times during a single CPU time slice, even
	 * in the presence of contention.  The efficiency of being able to do that
	 * outweighs the inefficiency of sometimes wasting a process dispatch
	 * cycle because the lock is not free when a released waiter finally gets
	 * to run.  See pgsql-hackers archives for 29-Dec-01.
	 */
	for (;;)
	{
		bool		mustwait;

		/*
		 * Try to grab the lock the first time, we're not in the waitqueue
		 * yet/anymore.
		 */
		mustwait = LWLockAttemptLock(lock, mode);

		if (!mustwait)
		{
			LOG_LWDEBUG("LWLockAcquire", lock, "immediately acquired lock");
			break;				/* got the lock */
		}

		/*
		 * Ok, at this point we couldn't grab the lock on the first try. We
		 * cannot simply queue ourselves to the end of the list and wait to be
		 * woken up because by now the lock could long have been released.
		 * Instead add us to the queue and try to grab the lock again. If we
		 * succeed we need to revert the queuing and be happy, otherwise we
		 * recheck the lock. If we still couldn't grab it, we know that the
		 * other locker will see our queue entries when releasing since they
		 * existed before we checked for the lock.
		 */

		/* add to the queue */
		LWLockQueueSelf(lock, mode);

		/* we're now guaranteed to be woken up if necessary */
		mustwait = LWLockAttemptLock(lock, mode);

		/* ok, grabbed the lock the second time round, need to undo queueing */
		if (!mustwait)
		{
			LOG_LWDEBUG("LWLockAcquire", lock, "acquired, undoing queue");

			LWLockDequeueSelf(lock);
			break;
		}

		/*
		 * Wait until awakened.
		 *
		 * It is possible that we get awakened for a reason other than being
		 * signaled by LWLockRelease.  If so, loop back and wait again.  Once
		 * we've gotten the LWLock, re-increment the sema by the number of
		 * additional signals received.
		 */
		LOG_LWDEBUG("LWLockAcquire", lock, "waiting");

#ifdef LWLOCK_STATS
		lwstats->block_count++;
#endif

		LWLockReportWaitStart(lock);
		if (TRACE_POSTGRESQL_LWLOCK_WAIT_START_ENABLED())
			TRACE_POSTGRESQL_LWLOCK_WAIT_START(T_NAME(lock), mode);

		for (;;)
		{
			PGSemaphoreLock(proc->sem);
			if (proc->lwWaiting == LW_WS_NOT_WAITING)
				break;
			extraWaits++;
		}

		/* Retrying, allow LWLockRelease to release waiters again. */
		pg_atomic_fetch_and_u32(&lock->state, ~LW_FLAG_WAKE_IN_PROGRESS);

#ifdef LOCK_DEBUG
		{
			/* not waiting anymore */
			uint32		nwaiters PG_USED_FOR_ASSERTS_ONLY = pg_atomic_fetch_sub_u32(&lock->nwaiters, 1);

			Assert(nwaiters < MAX_BACKENDS);
		}
#endif

		if (TRACE_POSTGRESQL_LWLOCK_WAIT_DONE_ENABLED())
			TRACE_POSTGRESQL_LWLOCK_WAIT_DONE(T_NAME(lock), mode);
		LWLockReportWaitEnd();

		LOG_LWDEBUG("LWLockAcquire", lock, "awakened");

		/* Now loop back and try to acquire lock again. */
		result = false;
	}

	if (TRACE_POSTGRESQL_LWLOCK_ACQUIRE_ENABLED())
		TRACE_POSTGRESQL_LWLOCK_ACQUIRE(T_NAME(lock), mode);

	/* Add lock to list of locks held by this backend */
	held_lwlocks[num_held_lwlocks].lock = lock;
	held_lwlocks[num_held_lwlocks++].mode = mode;

	/*
	 * Fix the process wait semaphore's count for any absorbed wakeups.
	 */
	while (extraWaits-- > 0)
		PGSemaphoreUnlock(proc->sem);

	return result;
}

/*
 * LWLockConditionalAcquire - acquire a lightweight lock in the specified mode
 *
 * If the lock is not available, return false with no side-effects.
 *
 * If successful, cancel/die interrupts are held off until lock release.
 */
/* (中文)条件获取:拿不到锁就直接失败,绝不等待(快速路径专用)。
 *
 * 【作用】调用方要求"仅当锁立即可得时才获取"(如持锁顺序检查、试探性
 * 加锁):内部只执行一次 LWLockAttemptLock,不经过入队/睡眠。成功时与
 * LWLockAcquire 一样登记 held_lwlocks 并屏蔽中断;失败则无任何副作用
 * (中断屏蔽立即解除,不登记、不改锁状态)。
 *
 * 【设计思想】与 LWLockAcquire 共享全部共享代码路径,只跳过慢路径。
 * 失败返回值语义干净:锁"此刻"不可得,调用方自行决定重试或换路。
 *
 * 【参数】lock —— 目标锁;mode —— LW_EXCLUSIVE 或 LW_SHARED。
 * 【返回值】true = 获取成功(已屏蔽中断,须对应 LWLockRelease);
 *         false = 锁不可得,无任何副作用。 */
bool
LWLockConditionalAcquire(LWLock *lock, LWLockMode mode)
{
	bool		mustwait;

	Assert(mode == LW_SHARED || mode == LW_EXCLUSIVE);

	PRINT_LWDEBUG("LWLockConditionalAcquire", lock, mode);

	/* Ensure we will have room to remember the lock */
	if (num_held_lwlocks >= MAX_SIMUL_LWLOCKS)
		elog(ERROR, "too many LWLocks taken");

	/*
	 * Lock out cancel/die interrupts until we exit the code section protected
	 * by the LWLock.  This ensures that interrupts will not interfere with
	 * manipulations of data structures in shared memory.
	 */
	HOLD_INTERRUPTS();

	/* Check for the lock */
	mustwait = LWLockAttemptLock(lock, mode);

	if (mustwait)
	{
		/* Failed to get lock, so release interrupt holdoff */
		RESUME_INTERRUPTS();

		LOG_LWDEBUG("LWLockConditionalAcquire", lock, "failed");
		if (TRACE_POSTGRESQL_LWLOCK_CONDACQUIRE_FAIL_ENABLED())
			TRACE_POSTGRESQL_LWLOCK_CONDACQUIRE_FAIL(T_NAME(lock), mode);
	}
	else
	{
		/* Add lock to list of locks held by this backend */
		held_lwlocks[num_held_lwlocks].lock = lock;
		held_lwlocks[num_held_lwlocks++].mode = mode;
		if (TRACE_POSTGRESQL_LWLOCK_CONDACQUIRE_ENABLED())
			TRACE_POSTGRESQL_LWLOCK_CONDACQUIRE(T_NAME(lock), mode);
	}
	return !mustwait;
}

/*
 * LWLockAcquireOrWait - Acquire lock, or wait until it's free
 *
 * The semantics of this function are a bit funky.  If the lock is currently
 * free, it is acquired in the given mode, and the function returns true.  If
 * the lock isn't immediately free, the function waits until it is released
 * and returns false, but does not acquire the lock.
 *
 * This is currently used for WALWriteLock: when a backend flushes the WAL,
 * holding WALWriteLock, it can flush the commit records of many other
 * backends as a side-effect.  Those other backends need to wait until the
 * flush finishes, but don't need to acquire the lock anymore.  They can just
 * wake up, observe that their records have already been flushed, and return.
 */
/* (中文)获取锁,或等锁释放后带着"没拿到锁"的结果返回。
 *
 * 【作用】语义特殊:锁空闲则按指定模式取得(返回 true);锁被持有则入队
 * 等待其"变空",被释放者唤醒后返回 false,且并不获取锁。专为
 * WALWriteLock 设计:某个后端持锁刷 WAL 时会顺带刷掉其他后端的提交
 * 记录,那些后端只需等到刷盘结束(醒来检查自己的 LSN 已落盘),根本
 * 不需要再拿锁。
 *
 * 【设计思想】与 LWLockAcquire 相同的两阶段协议,唯一区别是以
 * LW_WAIT_UNTIL_FREE 模式入队:该模式等待者排在对首、由释放者统一
 * 唤醒,且"被唤醒"不等于"被授予锁"(唤醒者不设 WAKE_IN_PROGRESS,
 * 等待者醒来直接收尾返回)。注意"入队后又拿到锁"的撤销分支也要按
 * 成功处理——否则会漏唤醒被我们堵住的人(见函数内注释)。
 *
 * 【参数】lock —— 目标锁;mode —— LW_EXCLUSIVE 或 LW_SHARED。
 * 【返回值】true = 已获取锁(持锁期间屏蔽中断,须 LWLockRelease);
 *         false = 等到锁释放但未获取(无任何持有状态)。 */
bool
LWLockAcquireOrWait(LWLock *lock, LWLockMode mode)
{
	PGPROC	   *proc = MyProc;
	bool		mustwait;
	int			extraWaits = 0;
#ifdef LWLOCK_STATS
	lwlock_stats *lwstats;

	lwstats = get_lwlock_stats_entry(lock);
#endif

	Assert(mode == LW_SHARED || mode == LW_EXCLUSIVE);

	PRINT_LWDEBUG("LWLockAcquireOrWait", lock, mode);

	/* Ensure we will have room to remember the lock */
	if (num_held_lwlocks >= MAX_SIMUL_LWLOCKS)
		elog(ERROR, "too many LWLocks taken");

	/*
	 * Lock out cancel/die interrupts until we exit the code section protected
	 * by the LWLock.  This ensures that interrupts will not interfere with
	 * manipulations of data structures in shared memory.
	 */
	HOLD_INTERRUPTS();

	/*
	 * NB: We're using nearly the same twice-in-a-row lock acquisition
	 * protocol as LWLockAcquire(). Check its comments for details.
	 */
	mustwait = LWLockAttemptLock(lock, mode);

	if (mustwait)
	{
		LWLockQueueSelf(lock, LW_WAIT_UNTIL_FREE);

		mustwait = LWLockAttemptLock(lock, mode);

		if (mustwait)
		{
			/*
			 * Wait until awakened.  Like in LWLockAcquire, be prepared for
			 * bogus wakeups.
			 */
			LOG_LWDEBUG("LWLockAcquireOrWait", lock, "waiting");

#ifdef LWLOCK_STATS
			lwstats->block_count++;
#endif

			LWLockReportWaitStart(lock);
			if (TRACE_POSTGRESQL_LWLOCK_WAIT_START_ENABLED())
				TRACE_POSTGRESQL_LWLOCK_WAIT_START(T_NAME(lock), mode);

			for (;;)
			{
				PGSemaphoreLock(proc->sem);
				if (proc->lwWaiting == LW_WS_NOT_WAITING)
					break;
				extraWaits++;
			}

#ifdef LOCK_DEBUG
			{
				/* not waiting anymore */
				uint32		nwaiters PG_USED_FOR_ASSERTS_ONLY = pg_atomic_fetch_sub_u32(&lock->nwaiters, 1);

				Assert(nwaiters < MAX_BACKENDS);
			}
#endif
			if (TRACE_POSTGRESQL_LWLOCK_WAIT_DONE_ENABLED())
				TRACE_POSTGRESQL_LWLOCK_WAIT_DONE(T_NAME(lock), mode);
			LWLockReportWaitEnd();

			LOG_LWDEBUG("LWLockAcquireOrWait", lock, "awakened");
		}
		else
		{
			LOG_LWDEBUG("LWLockAcquireOrWait", lock, "acquired, undoing queue");

			/*
			 * Got lock in the second attempt, undo queueing. We need to treat
			 * this as having successfully acquired the lock, otherwise we'd
			 * not necessarily wake up people we've prevented from acquiring
			 * the lock.
			 */
			LWLockDequeueSelf(lock);
		}
	}

	/*
	 * Fix the process wait semaphore's count for any absorbed wakeups.
	 */
	while (extraWaits-- > 0)
		PGSemaphoreUnlock(proc->sem);

	if (mustwait)
	{
		/* Failed to get lock, so release interrupt holdoff */
		RESUME_INTERRUPTS();
		LOG_LWDEBUG("LWLockAcquireOrWait", lock, "failed");
		if (TRACE_POSTGRESQL_LWLOCK_ACQUIRE_OR_WAIT_FAIL_ENABLED())
			TRACE_POSTGRESQL_LWLOCK_ACQUIRE_OR_WAIT_FAIL(T_NAME(lock), mode);
	}
	else
	{
		LOG_LWDEBUG("LWLockAcquireOrWait", lock, "succeeded");
		/* Add lock to list of locks held by this backend */
		held_lwlocks[num_held_lwlocks].lock = lock;
		held_lwlocks[num_held_lwlocks++].mode = mode;
		if (TRACE_POSTGRESQL_LWLOCK_ACQUIRE_OR_WAIT_ENABLED())
			TRACE_POSTGRESQL_LWLOCK_ACQUIRE_OR_WAIT(T_NAME(lock), mode);
	}

	return !mustwait;
}

/*
 * Does the lwlock in its current state need to wait for the variable value to
 * change?
 *
 * If we don't need to wait, and it's because the value of the variable has
 * changed, store the current value in newval.
 *
 * *result is set to true if the lock was free, and false otherwise.
 */
/* (中文)判断:按当前锁状态,等待者是否需要等"变量变化"。
 *
 * 【作用】LWLockWaitForVar 的判定子例程(无睡眠):锁未被排他持有 -> 立即
 * 返回"不需等待"(result = true,锁空闲);锁被持有 -> 读共享变量 valptr:
 * 值已不是 oldval -> 不需等待,把新值写进 *newval(result = false);
 * 值仍是 oldval -> 需要等待(result = false)。
 *
 * 【设计思想】只检查排他持有者,忽略共享持有者(共享持锁者可同时存在,
 * 等待者只要看"锁是否空闲/变量是否更新");对 uint64 变量用原子读,避免
 * 在非原子对齐平台上读到撕裂值。注意:本函数不提供内存屏障(唯一调用者
 * WaitXLogInsertionsToFinish 借助其前置的自旋锁隐式屏障保证排序),
 * 一般场景调用者需自行安排屏障(LWLockWaitForVar 注释有说明)。
 *
 * 【参数】lock —— 目标锁;valptr —— 被监视的共享变量(原子 uint64);
 *         oldval —— 等待者期望的旧值;newval —— 输出参数(变量已变化时
 *         写入当前值);result —— 输出参数(锁是否空闲)。
 * 【返回值】true = 必须等待;false = 无需等待。 */
static bool
LWLockConflictsWithVar(LWLock *lock, pg_atomic_uint64 *valptr, uint64 oldval,
					   uint64 *newval, bool *result)
{
	bool		mustwait;
	uint64		value;

	/*
	 * Test first to see if it the slot is free right now.
	 *
	 * XXX: the unique caller of this routine, WaitXLogInsertionsToFinish()
	 * via LWLockWaitForVar(), uses an implied barrier with a spinlock before
	 * this, so we don't need a memory barrier here as far as the current
	 * usage is concerned.  But that might not be safe in general.
	 */
	mustwait = (pg_atomic_read_u32(&lock->state) & LW_VAL_EXCLUSIVE) != 0;

	if (!mustwait)
	{
		*result = true;
		return false;
	}

	*result = false;

	/*
	 * Reading this value atomically is safe even on platforms where uint64
	 * cannot be read without observing a torn value.
	 */
	value = pg_atomic_read_u64(valptr);

	if (value != oldval)
	{
		mustwait = false;
		*newval = value;
	}
	else
	{
		mustwait = true;
	}

	return mustwait;
}

/*
 * LWLockWaitForVar - Wait until lock is free, or a variable is updated.
 *
 * If the lock is held and *valptr equals oldval, waits until the lock is
 * either freed, or the lock holder updates *valptr by calling
 * LWLockUpdateVar.  If the lock is free on exit (immediately or after
 * waiting), returns true.  If the lock is still held, but *valptr no longer
 * matches oldval, returns false and sets *newval to the current value in
 * *valptr.
 *
 * Note: this function ignores shared lock holders; if the lock is held
 * in shared mode, returns 'true'.
 *
 * Be aware that LWLockConflictsWithVar() does not include a memory barrier,
 * hence the caller of this function may want to rely on an explicit barrier or
 * an implied barrier via spinlock or LWLock to avoid memory ordering issues.
 */
/* (中文)等待"锁空闲或共享变量被更新"(变量等待原语)。
 *
 * 【作用】在"持锁者会修改某共享变量"的协议中,等待者用本函数替代
 * LWLockAcquire:如果锁未被排他持有,立即返回 true(相当于拿到锁,可以
 * 安全访问变量);如果锁被持有但变量已从 oldval 变成别的值,返回 false
 * 并把新值写入 *newval;如果锁被持有且变量没变,则阻塞,直到锁释放或
 * 持有者用 LWLockUpdateVar 更新变量。典型用法是 WAL 的
 * WaitXLogInsertionsToFinish:等排他持有者把插入位置推进。
 *
 * 【设计思想】复用两阶段获取协议(先查、入队 LW_WAIT_UNTIL_FREE、再查、
 * 睡眠、醒来重查),差别在于每次检查都是 LWLockConflictsWithVar(锁状态
 * 和变量值一并看)。入队后主动清除 WAKE_IN_PROGRESS 标志,确保释放者
 * 会唤醒我们。睡眠期间中断被屏蔽(HOLD_INTERRUPTS):等待队列里没有
 * 中断清理机制,若中途被打断,进程将留在队列里。
 *
 * 【参数】lock —— 目标锁(须以排他模式被他人持有才有等待意义);
 *         valptr —— 被监视的共享变量;oldval —— 期望的旧值;
 *         newval —— 输出参数:变量已变化时写入其当前值。
 * 【返回值】true = 锁已空闲(变量对 *newval 无意义);false = 锁仍被持有、
 *         但变量已更新,*newval 为新值。 */
bool
LWLockWaitForVar(LWLock *lock, pg_atomic_uint64 *valptr, uint64 oldval,
				 uint64 *newval)
{
	PGPROC	   *proc = MyProc;
	int			extraWaits = 0;
	bool		result = false;
#ifdef LWLOCK_STATS
	lwlock_stats *lwstats;

	lwstats = get_lwlock_stats_entry(lock);
#endif

	PRINT_LWDEBUG("LWLockWaitForVar", lock, LW_WAIT_UNTIL_FREE);

	/*
	 * Lock out cancel/die interrupts while we sleep on the lock.  There is no
	 * cleanup mechanism to remove us from the wait queue if we got
	 * interrupted.
	 */
	HOLD_INTERRUPTS();

	/*
	 * Loop here to check the lock's status after each time we are signaled.
	 */
	for (;;)
	{
		bool		mustwait;

		mustwait = LWLockConflictsWithVar(lock, valptr, oldval, newval,
										  &result);

		if (!mustwait)
			break;				/* the lock was free or value didn't match */

		/*
		 * Add myself to wait queue. Note that this is racy, somebody else
		 * could wakeup before we're finished queuing. NB: We're using nearly
		 * the same twice-in-a-row lock acquisition protocol as
		 * LWLockAcquire(). Check its comments for details. The only
		 * difference is that we also have to check the variable's values when
		 * checking the state of the lock.
		 */
		LWLockQueueSelf(lock, LW_WAIT_UNTIL_FREE);

		/*
		 * Clear LW_FLAG_WAKE_IN_PROGRESS flag, to make sure we get woken up
		 * as soon as the lock is released.
		 */
		pg_atomic_fetch_and_u32(&lock->state, ~LW_FLAG_WAKE_IN_PROGRESS);

		/*
		 * We're now guaranteed to be woken up if necessary. Recheck the lock
		 * and variables state.
		 */
		mustwait = LWLockConflictsWithVar(lock, valptr, oldval, newval,
										  &result);

		/* Ok, no conflict after we queued ourselves. Undo queueing. */
		if (!mustwait)
		{
			LOG_LWDEBUG("LWLockWaitForVar", lock, "free, undoing queue");

			LWLockDequeueSelf(lock);
			break;
		}

		/*
		 * Wait until awakened.
		 *
		 * It is possible that we get awakened for a reason other than being
		 * signaled by LWLockRelease.  If so, loop back and wait again.  Once
		 * we've gotten the LWLock, re-increment the sema by the number of
		 * additional signals received.
		 */
		LOG_LWDEBUG("LWLockWaitForVar", lock, "waiting");

#ifdef LWLOCK_STATS
		lwstats->block_count++;
#endif

		LWLockReportWaitStart(lock);
		if (TRACE_POSTGRESQL_LWLOCK_WAIT_START_ENABLED())
			TRACE_POSTGRESQL_LWLOCK_WAIT_START(T_NAME(lock), LW_EXCLUSIVE);

		for (;;)
		{
			PGSemaphoreLock(proc->sem);
			if (proc->lwWaiting == LW_WS_NOT_WAITING)
				break;
			extraWaits++;
		}

#ifdef LOCK_DEBUG
		{
			/* not waiting anymore */
			uint32		nwaiters PG_USED_FOR_ASSERTS_ONLY = pg_atomic_fetch_sub_u32(&lock->nwaiters, 1);

			Assert(nwaiters < MAX_BACKENDS);
		}
#endif

		if (TRACE_POSTGRESQL_LWLOCK_WAIT_DONE_ENABLED())
			TRACE_POSTGRESQL_LWLOCK_WAIT_DONE(T_NAME(lock), LW_EXCLUSIVE);
		LWLockReportWaitEnd();

		LOG_LWDEBUG("LWLockWaitForVar", lock, "awakened");

		/* Now loop back and check the status of the lock again. */
	}

	/*
	 * Fix the process wait semaphore's count for any absorbed wakeups.
	 */
	while (extraWaits-- > 0)
		PGSemaphoreUnlock(proc->sem);

	/*
	 * Now okay to allow cancel/die interrupts.
	 */
	RESUME_INTERRUPTS();

	return result;
}


/*
 * LWLockUpdateVar - Update a variable and wake up waiters atomically
 *
 * Sets *valptr to 'val', and wakes up all processes waiting for us with
 * LWLockWaitForVar().  It first sets the value atomically and then wakes up
 * waiting processes so that any process calling LWLockWaitForVar() on the same
 * lock is guaranteed to see the new value, and act accordingly.
 *
 * The caller must be holding the lock in exclusive mode.
 */
/* (中文)更新共享变量并原子地唤醒等待者(LWLockWaitForVar 的配对方)。
 *
 * 【作用】把 *valptr 原子地设为 val,然后唤醒所有以 LW_WAIT_UNTIL_FREE
 * 模式等在这把锁上的进程,让它们醒来观察到新值。调用者必须持有锁的
 * 排他模式。
 *
 * 【设计思想】先 pg_atomic_exchange_u64 更新变量(该原子操作是全屏障,
 * 保证"变量新值"在"唤醒"之前对所有等待者可见),再持等待队列互斥锁把
 * 队首一段 LW_WAIT_UNTIL_FREE 等待者整体摘出(这类等待者恒在队首,
 * 见到其他模式即可停止扫描),最后逐个发信号。信号前的
 * pg_write_barrier 与 LWLockWakeup 中同理,防止"链表摘除完成"晚于
 * "lwWaiting 状态置 NOT_WAITING"被等待者观察到。
 *
 * 【参数】lock —— 目标锁;valptr —— 被更新并唤醒等待者的共享变量;
 *         val —— 要写入的新值。
 * 【返回值】无 */
void
LWLockUpdateVar(LWLock *lock, pg_atomic_uint64 *valptr, uint64 val)
{
	proclist_head wakeup;
	proclist_mutable_iter iter;

	PRINT_LWDEBUG("LWLockUpdateVar", lock, LW_EXCLUSIVE);

	/*
	 * Note that pg_atomic_exchange_u64 is a full barrier, so we're guaranteed
	 * that the variable is updated before waking up waiters.
	 */
	pg_atomic_exchange_u64(valptr, val);

	proclist_init(&wakeup);

	LWLockWaitListLock(lock);

	Assert(pg_atomic_read_u32(&lock->state) & LW_VAL_EXCLUSIVE);

	/*
	 * See if there are any LW_WAIT_UNTIL_FREE waiters that need to be woken
	 * up. They are always in the front of the queue.
	 */
	proclist_foreach_modify(iter, &lock->waiters, lwWaitLink)
	{
		PGPROC	   *waiter = GetPGProcByNumber(iter.cur);

		if (waiter->lwWaitMode != LW_WAIT_UNTIL_FREE)
			break;

		proclist_delete(&lock->waiters, iter.cur, lwWaitLink);
		proclist_push_tail(&wakeup, iter.cur, lwWaitLink);

		/* see LWLockWakeup() */
		Assert(waiter->lwWaiting == LW_WS_WAITING);
		waiter->lwWaiting = LW_WS_PENDING_WAKEUP;
	}

	/* We are done updating shared state of the lock itself. */
	LWLockWaitListUnlock(lock);

	/*
	 * Awaken any waiters I removed from the queue.
	 */
	proclist_foreach_modify(iter, &wakeup, lwWaitLink)
	{
		PGPROC	   *waiter = GetPGProcByNumber(iter.cur);

		proclist_delete(&wakeup, iter.cur, lwWaitLink);
		/* check comment in LWLockWakeup() about this barrier */
		pg_write_barrier();
		waiter->lwWaiting = LW_WS_NOT_WAITING;
		PGSemaphoreUnlock(waiter->sem);
	}
}


/*
 * LWLockRelease - release a previously acquired lock
 *
 * NB: This will leave lock->owner pointing to the current backend (if
 * LOCK_DEBUG is set). This is somewhat intentional, as it makes it easier to
 * debug cases of missing wakeups during lock release.
 */
/* (中文)释放一把先前获取的轻量锁,并视情况唤醒等待者。
 *
 * 【作用】与 LWLockAcquire/LWLockConditionalAcquire/LWLockAcquireOrWait
 * 成功返回配对使用:先从 held_lwlocks 中移除该锁的记录,原子地减少
 * state 中的持有记账(排他 -LW_VAL_EXCLUSIVE / 共享 -LW_VAL_SHARED),
 * 然后判断是否需要唤醒等待者,最后解除中断屏蔽(RESUME_INTERRUPTS,
 * 与获取时的 HOLD_INTERRUPTS 对应)。
 *
 * 【设计思想】
 * - 释放记账用原子 sub,锁在减法完成瞬间即可被他人获取,唤醒等后续
 *   工作不影响并发正确性;
 * - 唤醒条件三缺一不可:有等待者(HAS_WAITERS)、唤醒不在进行中
 *   (!WAKE_IN_PROGRESS,避免重复唤醒同一批人)、锁已彻底空闲
 *   (低 29 位为零,排他/共享都清光)。条件满足才调用 LWLockWakeup,
 *   因为唤醒要取等待队列互斥锁,能省则省;
 * - held_lwlocks 从尾部往前搜(通常最后拿的先放),移除时把后面的记录
 *   整体前移,保持数组紧凑;
 * - LOCK_DEBUG 下故意不清理 lock->owner,便于排查"释放后缺唤醒"类
 *   问题(见英文 NB 注释)。
 *
 * 【参数】lock —— 要释放的锁。
 * 【返回值】无;锁并未被本进程持有(不在 held_lwlocks 中)时
 *         elog(ERROR)。 */
void
LWLockRelease(LWLock *lock)
{
	LWLockMode	mode;
	uint32		oldstate;
	bool		check_waiters;
	int			i;

	/*
	 * Remove lock from list of locks held.  Usually, but not always, it will
	 * be the latest-acquired lock; so search array backwards.
	 */
	for (i = num_held_lwlocks; --i >= 0;)
		if (lock == held_lwlocks[i].lock)
			break;

	if (i < 0)
		elog(ERROR, "lock %s is not held", T_NAME(lock));

	mode = held_lwlocks[i].mode;

	num_held_lwlocks--;
	for (; i < num_held_lwlocks; i++)
		held_lwlocks[i] = held_lwlocks[i + 1];

	PRINT_LWDEBUG("LWLockRelease", lock, mode);

	/*
	 * Release my hold on lock, after that it can immediately be acquired by
	 * others, even if we still have to wakeup other waiters.
	 */
	if (mode == LW_EXCLUSIVE)
		oldstate = pg_atomic_sub_fetch_u32(&lock->state, LW_VAL_EXCLUSIVE);
	else
		oldstate = pg_atomic_sub_fetch_u32(&lock->state, LW_VAL_SHARED);

	/* nobody else can have that kind of lock */
	Assert(!(oldstate & LW_VAL_EXCLUSIVE));

	if (TRACE_POSTGRESQL_LWLOCK_RELEASE_ENABLED())
		TRACE_POSTGRESQL_LWLOCK_RELEASE(T_NAME(lock));

	/*
	 * Check if we're still waiting for backends to get scheduled, if so,
	 * don't wake them up again.
	 */
	if ((oldstate & LW_FLAG_HAS_WAITERS) &&
		!(oldstate & LW_FLAG_WAKE_IN_PROGRESS) &&
		(oldstate & LW_LOCK_MASK) == 0)
		check_waiters = true;
	else
		check_waiters = false;

	/*
	 * As waking up waiters requires the spinlock to be acquired, only do so
	 * if necessary.
	 */
	if (check_waiters)
	{
		/* XXX: remove before commit? */
		LOG_LWDEBUG("LWLockRelease", lock, "releasing waiters");
		LWLockWakeup(lock);
	}

	/*
	 * Now okay to allow cancel/die interrupts.
	 */
	RESUME_INTERRUPTS();
}

/*
 * LWLockReleaseClearVar - release a previously acquired lock, reset variable
 */
/* (中文)释放锁并把共享变量复位为指定值(LWLockUpdateVar 的"释放侧"对应)。
 *
 * 【作用】持有者结束对变量的修改时调用:先把 *valptr 原子地设为 val
 * (通常是"锁空闲"状态对应的值),再释放锁。LWLockWaitForVar 的等待者
 * 会因此醒来。
 *
 * 【设计思想】pg_atomic_exchange_u64 是全屏障,保证"变量复位"先于
 * "锁被释放"对所有观察者可见——否则等待者可能在锁已释放但变量还是
 * 旧值时醒来,读到过期数据。
 *
 * 【参数】lock —— 要释放的锁;valptr —— 要复位的共享变量;
 *         val —— 复位值。
 * 【返回值】无(其余语义同 LWLockRelease)。 */
void
LWLockReleaseClearVar(LWLock *lock, pg_atomic_uint64 *valptr, uint64 val)
{
	/*
	 * Note that pg_atomic_exchange_u64 is a full barrier, so we're guaranteed
	 * that the variable is updated before releasing the lock.
	 */
	pg_atomic_exchange_u64(valptr, val);

	LWLockRelease(lock);
}


/*
 * LWLockReleaseAll - release all currently-held locks
 *
 * Used to clean up after ereport(ERROR). An important difference between this
 * function and retail LWLockRelease calls is that InterruptHoldoffCount is
 * unchanged by this operation.  This is necessary since InterruptHoldoffCount
 * has been set to an appropriate level earlier in error recovery. We could
 * decrement it below zero if we allow it to drop for each released lock!
 *
 * Note that this function must be safe to call even before the LWLock
 * subsystem has been initialized (e.g., during early startup failures).
 * In that case, num_held_lwlocks will be 0 and we do nothing.
 */
/* (中文)释放本进程当前持有的全部 LWLock(错误恢复用的"大扫除")。
 *
 * 【作用】在 ereport(ERROR) 的错误恢复路径上被调用(经 elog/ereport 的
 * 清理框架,或 ProcKill 退出清理):只要 held_lwlocks 非空就反复释放最后
 * 一把,直到全部释放完毕。必须能容忍"LWLock 子系统尚未初始化"的早期
 * 启动失败场景(此时计数为 0,什么都不做)。
 *
 * 【设计思想】与逐把 LWLockRelease 的关键差异:本函数不碰
 * InterruptHoldoffCount 的平衡——错误恢复框架在此之前已把中断屏蔽
 * 计数设置到合适水平,这里若为每把锁做一次 RESUME_INTERRUPTS,会把
 * 计数降到负值(见英文注释)。因此循环内用 HOLD_INTERRUPTS 预先补一次
 * 计数,让内层 LWLockRelease 的 RESUME_INTERRUPTS 恰好抵消,净效果为
 * 零。释放顺序为"后拿的先放"(栈式),由循环从数组尾部取锁保证。
 *
 * 【参数】无
 * 【返回值】无(结束时本进程不持有任何 LWLock)。 */
void
LWLockReleaseAll(void)
{
	while (num_held_lwlocks > 0)
	{
		HOLD_INTERRUPTS();		/* match the upcoming RESUME_INTERRUPTS */

		LWLockRelease(held_lwlocks[num_held_lwlocks - 1].lock);
	}

	Assert(num_held_lwlocks == 0);
}


/*
 * LWLockHeldByMe - test whether my process holds a lock in any mode
 *
 * This is meant as debug support only.
 */
/* (中文)测试本进程是否以任意模式持有指定的锁。
 *
 * 【作用】供 Assert 等调试代码使用:在 held_lwlocks 中线性查找目标锁。
 *
 * 【参数】lock —— 目标锁。
 * 【返回值】持有任意模式则返回 true,否则 false。 */
bool
LWLockHeldByMe(LWLock *lock)
{
	int			i;

	for (i = 0; i < num_held_lwlocks; i++)
	{
		if (held_lwlocks[i].lock == lock)
			return true;
	}
	return false;
}

/*
 * LWLockAnyHeldByMe - test whether my process holds any of an array of locks
 *
 * This is meant as debug support only.
 */
/* (中文)测试本进程是否持有"某个连续数组"中的任意一把锁。
 *
 * 【作用】调试断言用:给定锁数组的基地址、锁个数与每把锁的步长(通常
 * 是 LWLockPadded 的大小或锁结构体大小),判断 held_lwlocks 中是否有
 * 一把锁的地址正好落在该数组的某个元素上(地址与基址的差整除步长,
 * 防止数组元素之间内嵌的其他锁被误判)。
 *
 * 【参数】lock —— 数组首元素的锁地址(视作字节指针做地址运算);
 *         nlocks —— 数组中锁的个数;stride —— 每个元素占用的字节数。
 * 【返回值】持有其中任意一把锁返回 true,否则 false。 */
bool
LWLockAnyHeldByMe(LWLock *lock, int nlocks, size_t stride)
{
	char	   *held_lock_addr;
	char	   *begin;
	char	   *end;
	int			i;

	begin = (char *) lock;
	end = begin + nlocks * stride;
	for (i = 0; i < num_held_lwlocks; i++)
	{
		held_lock_addr = (char *) held_lwlocks[i].lock;
		if (held_lock_addr >= begin &&
			held_lock_addr < end &&
			(held_lock_addr - begin) % stride == 0)
			return true;
	}
	return false;
}

/*
 * LWLockHeldByMeInMode - test whether my process holds a lock in given mode
 *
 * This is meant as debug support only.
 */
/* (中文)测试本进程是否以指定模式持有某把锁。
 *
 * 【作用】调试断言用:在 held_lwlocks 中查找"锁地址相同且模式相同"的
 * 记录。
 *
 * 【参数】lock —— 目标锁;mode —— 要检查的模式(LW_EXCLUSIVE/
 *         LW_SHARED)。
 * 【返回值】以该模式持有则 true,否则 false。 */
bool
LWLockHeldByMeInMode(LWLock *lock, LWLockMode mode)
{
	int			i;

	for (i = 0; i < num_held_lwlocks; i++)
	{
		if (held_lwlocks[i].lock == lock && held_lwlocks[i].mode == mode)
			return true;
	}
	return false;
}
