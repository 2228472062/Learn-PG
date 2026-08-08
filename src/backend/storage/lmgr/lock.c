/*-------------------------------------------------------------------------
 *
 * lock.c
 *	  POSTGRES primary lock mechanism
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/lmgr/lock.c
 *
 * NOTES
 *	  A lock table is a shared memory hash table.  When
 *	  a process tries to acquire a lock of a type that conflicts
 *	  with existing locks, it is put to sleep using the routines
 *	  in storage/lmgr/proc.c.
 *
 *	  For the most part, this code should be invoked via lmgr.c
 *	  or another lock-management module, not directly.
 *
 *	Interface:
 *
 *	LockManagerShmemInit(), GetLocksMethodTable(), GetLockTagsMethodTable(),
 *	LockAcquire(), LockRelease(), LockReleaseAll(),
 *	LockCheckConflicts(), GrantLock()
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 的"重锁(heavyweight lock)机制",是整个锁
 * 子系统的心脏。它维护一张位于共享内存的锁表(用分区哈希表组织,
 * 每把锁有一个等待队列),并实现加锁、解锁、冲突判定、唤醒等待者、
 * 死锁检测触发、事务结束时的批量释放、两阶段提交(prepared 事务)的
 * 锁持久化/恢复,以及 fast-path 快速路径加速。
 *
 * 【核心数据结构】
 * - LOCKTAG:锁的"标签"(类型 + 若干字段,如库 ID/关系 OID/页号),
 *   哈希键,决定"这把锁锁的是谁";
 * - LOCK:共享内存里的锁对象,含冲突掩码(nRequested/nGranted、
 *   grantedMask/waitMask)与等待队列 waitProcs;
 * - PROCLOCK:记录"某个进程在某个锁上持有什么"的链接点,按
 *   (持有者、锁)成对出现,并挂在持有者的锁列表上;
 * - LOCALLOCK:后端本地(进程私有)的锁记账,记录本进程各资源所有者
 *   对每把锁的持有次数(nLocks),是共享锁表中 LOCK/PROCLOCK 的本地
 *   镜像与缓冲层。
 *
 * 【关键机制】
 * 1. LockAcquire:先查本地 LOCALLOCK(持有中/已登记),必要时进共享表
 *    建 LOCK/PROCLOCK,冲突则入等待队列,调用 ProcSleep 睡眠,醒来后
 *    检查是否死锁(DeadLockCheck)或被取消;
 * 2. fast-path:小锁模式的表级锁若 fast-path 槽位有空,不进锁表,
 *    只在本后端 PGPROC 的位图里打标记,把共享锁表的争用降到最低;
 *    空间不够时由 LockReleaseAll 把 fast-path 锁搬进正式锁表
 *    (fastpath 升级);
 * 3. 锁的释放由资源所有者(resowner)统一管理:LockRelease 按
 *    所有者逐层释放,事务结束时 LockReleaseAll 一次性清理,包括把
 *    prepared 事务的锁信息写进 2PC 状态文件(PostPrepare_Locks)与
 *    recovery 时的恢复;
 * 4. 死锁:等待超过 deadlock_timeout 后触发 DeadLockCheck,本文件
 *    负责把锁表上锁并调用检测,检测结果的恢复动作在 deadlock.c。
 *
 * 调用约定:本文件的接口一般不应直接调用,而应通过 lmgr.c 提供的
 * 高级封装,或经 lockfuncs.c 的 advisory 锁接口调用。
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>
#include <unistd.h>

#include "access/transam.h"
#include "access/twophase.h"
#include "access/twophase_rmgr.h"
#include "access/xlog.h"
#include "access/xlogutils.h"
#include "miscadmin.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "storage/lmgr.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "storage/shmem.h"
#include "storage/spin.h"
#include "storage/standby.h"
#include "storage/subsystems.h"
#include "utils/memutils.h"
#include "utils/ps_status.h"
#include "utils/resowner.h"


/* GUC variables */
int			max_locks_per_xact; /* used to set the lock table size */
bool		log_lock_failures = false;
/* (中文)GUC 配置:
 * - max_locks_per_xact:单个事务预计持有的重锁数量上限,用于估算共享
 *   锁表大小(见 NLOCKENTS);
 * - log_lock_failures:为 true 时,条件加锁失败(拿不到锁)也写日志
 *   (用于诊断死锁/锁竞争,见 LockAcquireExtended 与 ProcSleep 的
 *   log_lock_waits 逻辑)。 */

#define NLOCKENTS() \
	mul_size(max_locks_per_xact, add_size(MaxBackends, max_prepared_xacts))
/* (中文)估算共享锁表应容纳的"锁条目"总数:
 * 每个并发后端最多 max_locks_per_xact 把锁,prepared 事务的锁也计入
 * (每个 prepared 事务可视为一个额外的"虚拟后端")。 */


/*
 * Data structures defining the semantics of the standard lock methods.
 *
 * The conflict table defines the semantics of the various lock modes.
 */
/*
 * LockConflicts
 *      (中文)标准锁方法的"锁模式冲突矩阵"
 *
 * 【作用】对 8 种重锁模式各定义一个掩码:该掩码列出"与当前模式互相
 * 冲突的其他模式"。加锁时若锁的 grantedMask(已授予的模式集合)与该
 * 掩码有交集,说明存在冲突持有者,当前请求必须等待。
 *
 * 【矩阵要点】(行 = 请求模式,掩码内 = 冲突模式)
 * - AccessShareLock 只与 AccessExclusiveLock 冲突(SELECT 不阻塞任何
 *   读,只与最重的锁冲突);
 * - RowExclusiveLock 与 ShareLock 及更强模式冲突(普通 INSERT/UPDATE
 *   的锁,见索引 B-tree 上的使用);
 * - ShareUpdateExclusiveLock 与自身冲突:该模式用于 VACUUM 等"多个
 *   相同操作应互斥"的场景(防止多个 VACUUM 同时跑);
 * - 对称性:矩阵是对称的(第 i 行第 j 列 = 第 j 行第 i 列)。
 */
static const LOCKMASK LockConflicts[] = {
	0,

	/* AccessShareLock */
	LOCKBIT_ON(AccessExclusiveLock),

	/* RowShareLock */
	LOCKBIT_ON(ExclusiveLock) | LOCKBIT_ON(AccessExclusiveLock),

	/* RowExclusiveLock */
	LOCKBIT_ON(ShareLock) | LOCKBIT_ON(ShareRowExclusiveLock) |
	LOCKBIT_ON(ExclusiveLock) | LOCKBIT_ON(AccessExclusiveLock),

	/* ShareUpdateExclusiveLock */
	LOCKBIT_ON(ShareUpdateExclusiveLock) |
	LOCKBIT_ON(ShareLock) | LOCKBIT_ON(ShareRowExclusiveLock) |
	LOCKBIT_ON(ExclusiveLock) | LOCKBIT_ON(AccessExclusiveLock),

	/* ShareLock */
	LOCKBIT_ON(RowExclusiveLock) | LOCKBIT_ON(ShareUpdateExclusiveLock) |
	LOCKBIT_ON(ShareRowExclusiveLock) |
	LOCKBIT_ON(ExclusiveLock) | LOCKBIT_ON(AccessExclusiveLock),

	/* ShareRowExclusiveLock */
	LOCKBIT_ON(RowExclusiveLock) | LOCKBIT_ON(ShareUpdateExclusiveLock) |
	LOCKBIT_ON(ShareLock) | LOCKBIT_ON(ShareRowExclusiveLock) |
	LOCKBIT_ON(ExclusiveLock) | LOCKBIT_ON(AccessExclusiveLock),

	/* ExclusiveLock */
	LOCKBIT_ON(RowShareLock) |
	LOCKBIT_ON(RowExclusiveLock) | LOCKBIT_ON(ShareUpdateExclusiveLock) |
	LOCKBIT_ON(ShareLock) | LOCKBIT_ON(ShareRowExclusiveLock) |
	LOCKBIT_ON(ExclusiveLock) | LOCKBIT_ON(AccessExclusiveLock),

	/* AccessExclusiveLock */
	LOCKBIT_ON(AccessShareLock) | LOCKBIT_ON(RowShareLock) |
	LOCKBIT_ON(RowExclusiveLock) | LOCKBIT_ON(ShareUpdateExclusiveLock) |
	LOCKBIT_ON(ShareLock) | LOCKBIT_ON(ShareRowExclusiveLock) |
	LOCKBIT_ON(ExclusiveLock) | LOCKBIT_ON(AccessExclusiveLock)

};

/* Names of lock modes, for debug printouts */
/* (中文)锁模式的名称表(下标 = 锁模式编号,0 号是 INVALID),用于
 * 调试输出、错误消息与日志。 */
static const char *const lock_mode_names[] =
{
	"INVALID",
	"AccessShareLock",
	"RowShareLock",
	"RowExclusiveLock",
	"ShareUpdateExclusiveLock",
	"ShareLock",
	"ShareRowExclusiveLock",
	"ExclusiveLock",
	"AccessExclusiveLock"
};

#ifndef LOCK_DEBUG
static bool Dummy_trace = false;
/* (中文)未编译 LOCK_DEBUG 时的占位"追踪开关":使两种锁方法的
 * traceFlag 始终指向一个无害的 false 变量,编译期无需条件判断。 */
#endif

/* (中文)默认锁方法(default_lockmethod):8 个锁模式、标准冲突矩阵,
 * 用于绝大多数对象(关系、页、元组、事务、对象、advisory 锁)。
 * user_lockmethod 与之共享同一矩阵,只是 traceFlag 不同(调试时追踪
 * 用户 advisory 锁)。两者都通过 LockMethods[] 索引表访问。 */
static const LockMethodData default_lockmethod = {
	MaxLockMode,
	LockConflicts,
	lock_mode_names,
#ifdef LOCK_DEBUG
	&Trace_locks
#else
	&Dummy_trace
#endif
};

static const LockMethodData user_lockmethod = {
	MaxLockMode,
	LockConflicts,
	lock_mode_names,
#ifdef LOCK_DEBUG
	&Trace_userlocks
#else
	&Dummy_trace
#endif
};

/*
 * map from lock method id to the lock table data structures
 */
/* (中文)锁方法 ID → 锁方法数据结构 的索引表:lockmethodid 1 =
 * default_lockmethod(标准重锁),2 = user_lockmethod(用户 advisory 锁),
 * 0 号位留空。GetLocksMethodTable 用它完成映射。 */
static const LockMethod LockMethods[] = {
	NULL,
	&default_lockmethod,
	&user_lockmethod
};


/* Record that's written to 2PC state file when a lock is persisted */
typedef struct TwoPhaseLockRecord
{
	LOCKTAG		locktag;
	LOCKMODE	lockmode;
} TwoPhaseLockRecord;
/* (中文)两阶段提交时写进 2PC 状态文件的"锁记录":Prepared 事务持
 * 有的每把锁记成一条 (locktag, lockmode)。恢复(prepare 后重启)时
 * 由 lock_redo 读回并重建共享锁表条目。 */


/*
 * Count of the number of fast path lock slots we believe to be used.  This
 * might be higher than the real number if another backend has transferred
 * our locks to the primary lock table, but it can never be lower than the
 * real value, since only we can acquire locks on our own behalf.
 *
 * XXX Allocate a static array of the maximum size. We could use a pointer
 * and then allocate just the right size to save a couple kB, but then we
 * would have to initialize that, while for the static array that happens
 * automatically. Doesn't seem worth the extra complexity.
 */
static int	FastPathLocalUseCounts[FP_LOCK_GROUPS_PER_BACKEND_MAX];
/* (中文)本后端 fast-path 锁位图的"每个组已用槽数"计数:组 g 用
 * 第 g 位到第 (g + FP_LOCK_SLOTS_PER_GROUP) 位的偏移区。该计数可能
 * 高于实际值(别的后端可能把我们的锁搬进了主锁表),但不会低于
 * 实际值——只有我们自己能为自己的 fast-path 槽位计数,别的进程
 * 只能搬走(清零),不能凭空增加。用于选择"空槽位"时避免超界。 */

/*
 * Flag to indicate if the relation extension lock is held by this backend.
 * This flag is used to ensure that while holding the relation extension lock
 * we don't try to acquire a heavyweight lock on any other object.  This
 * restriction implies that the relation extension lock won't ever participate
 * in the deadlock cycle because we can never wait for any other heavyweight
 * lock after acquiring this lock.
 *
 * Such a restriction is okay for relation extension locks as unlike other
 * heavyweight locks these are not held till the transaction end.  These are
 * taken for a short duration to extend a particular relation and then
 * released.
 */
static bool IsRelationExtensionLockHeld PG_USED_FOR_ASSERTS_ONLY = false;
/* (中文)断言专用标志:本后端当前是否持有关系统扩展锁。其存在是为
 * 了强制执行"持扩展锁期间不得再等任何重锁"的不变量——该不变量使
 * 扩展锁永不参与死锁环(见英文注释,扩展锁短持即放)。 */

/*
 * Number of fast-path locks per backend - size of the arrays in PGPROC.
 * This is set only once during start, before initializing shared memory,
 * and remains constant after that.
 *
 * We set the limit based on max_locks_per_transaction GUC, because that's
 * the best information about expected number of locks per backend we have.
 * See InitializeFastPathLocks() for details.
 */
int			FastPathLockGroupsPerBackend = 0;
/* (中文)每个后端 fast-path 锁的"组数"(PGPROC 中数组的大小)。
 * 启动时、初始化共享内存之前只设置一次,之后恒定。其取值由
 * max_locks_per_xact GUC 推导(见 InitializeFastPathLocks),且按
 * 2 的幂向上取整,保证 FAST_PATH_REL_GROUP 的位运算哈希有效。 */

/*
 * Macros to calculate the fast-path group and index for a relation.
 *
 * The formula is a simple hash function, designed to spread the OIDs a bit,
 * so that even contiguous values end up in different groups. In most cases
 * there will be gaps anyway, but the multiplication should help a bit.
 *
 * The selected constant (49157) is a prime not too close to 2^k, and it's
 * small enough to not cause overflows (in 64-bit).
 *
 * We can assume that FastPathLockGroupsPerBackend is a power-of-two per
 * InitializeFastPathLocks().
 */
#define FAST_PATH_REL_GROUP(rel) \
	(((uint64) (rel) * 49157) & (FastPathLockGroupsPerBackend - 1))
/* (中文)fast-path 分组哈希:由关系 OID 算出它应落入的组号。公式是
 * 简单的乘法散列:49157 是不太接近 2 的幂的素数,把连续 OID 也
 * 均匀摊开(避免相邻表挤在同一组);由于组数是 2 的幂,用
 * (组数-1) 做位与即可取模。 */

/*
 * Given the group/slot indexes, calculate the slot index in the whole array
 * of fast-path lock slots.
 */
/* (中文)由(组号, 组内下标)算出整个 fast-path 槽位数组的线性下标。
 * 数组按组连续排布,每组长 FP_LOCK_SLOTS_PER_GROUP 个槽。 */
#define FAST_PATH_SLOT(group, index) \
	(AssertMacro((uint32) (group) < FastPathLockGroupsPerBackend), \
	 AssertMacro((uint32) (index) < FP_LOCK_SLOTS_PER_GROUP), \
	 ((group) * FP_LOCK_SLOTS_PER_GROUP + (index)))

/*
 * Given a slot index (into the whole per-backend array), calculated using
 * the FAST_PATH_SLOT macro, split it into group and index (in the group).
 */
/* (中文)FAST_PATH_SLOT 的逆运算:由线性下标反推(组号, 组内下标)。
 * FAST_PATH_GROUP 得组号(整除),FAST_PATH_INDEX 得组内下标(取模)。 */
#define FAST_PATH_GROUP(index)	\
	(AssertMacro((uint32) (index) < FastPathLockSlotsPerBackend()), \
	 ((index) / FP_LOCK_SLOTS_PER_GROUP))
#define FAST_PATH_INDEX(index)	\
	(AssertMacro((uint32) (index) < FastPathLockSlotsPerBackend()), \
	 ((index) % FP_LOCK_SLOTS_PER_GROUP))

/* Macros for manipulating proc->fpLockBits */
#define FAST_PATH_BITS_PER_SLOT			3
#define FAST_PATH_LOCKNUMBER_OFFSET		1
#define FAST_PATH_MASK					((1 << FAST_PATH_BITS_PER_SLOT) - 1)
#define FAST_PATH_BITS(proc, n)			(proc)->fpLockBits[FAST_PATH_GROUP(n)]
#define FAST_PATH_GET_BITS(proc, n) \
	((FAST_PATH_BITS(proc, n) >> (FAST_PATH_BITS_PER_SLOT * FAST_PATH_INDEX(n))) & FAST_PATH_MASK)
#define FAST_PATH_BIT_POSITION(n, l) \
	(AssertMacro((l) >= FAST_PATH_LOCKNUMBER_OFFSET), \
	 AssertMacro((l) < FAST_PATH_BITS_PER_SLOT+FAST_PATH_LOCKNUMBER_OFFSET), \
	 AssertMacro((n) < FastPathLockSlotsPerBackend()), \
	 ((l) - FAST_PATH_LOCKNUMBER_OFFSET + FAST_PATH_BITS_PER_SLOT * (FAST_PATH_INDEX(n))))
#define FAST_PATH_SET_LOCKMODE(proc, n, l) \
	 FAST_PATH_BITS(proc, n) |= UINT64CONST(1) << FAST_PATH_BIT_POSITION(n, l)
#define FAST_PATH_CLEAR_LOCKMODE(proc, n, l) \
	 FAST_PATH_BITS(proc, n) &= ~(UINT64CONST(1) << FAST_PATH_BIT_POSITION(n, l))
#define FAST_PATH_CHECK_LOCKMODE(proc, n, l) \
	 (FAST_PATH_BITS(proc, n) & (UINT64CONST(1) << FAST_PATH_BIT_POSITION(n, l)))
/* (中文)proc->fpLockBits 位图的操纵宏:每个 fast-path 槽位占 3 位,
 * 存放"锁模式号 - 1"(值 0 表示空槽,故模式号从 FAST_PATH_LOCKNUMBER_OFFSET
 * = 1 起记,即 AccessShareLock=1 → 存 0... 实际模式值 1..3 对应
 * 位值 0..2,3 位恰好放得下)。FAST_PATH_BITS 取整组 64 位字,
 * 组内每 3 位一个槽;FAST_PATH_BIT_POSITION 计算槽内某模式对应的
 * 位偏移;SET/CLEAR/CHECK 分别置位、清位、查位。 */

/*
 * The fast-path lock mechanism is concerned only with relation locks on
 * unshared relations by backends bound to a database.  The fast-path
 * mechanism exists mostly to accelerate acquisition and release of locks
 * that rarely conflict.  Because ShareUpdateExclusiveLock is
 * self-conflicting, it can't use the fast-path mechanism; but it also does
 * not conflict with any of the locks that do, so we can ignore it completely.
 */
#define EligibleForRelationFastPath(locktag, mode) \
	((locktag)->locktag_lockmethodid == DEFAULT_LOCKMETHOD && \
	(locktag)->locktag_type == LOCKTAG_RELATION && \
	(locktag)->locktag_field1 == MyDatabaseId && \
	MyDatabaseId != InvalidOid && \
	(mode) < ShareUpdateExclusiveLock)
#define ConflictsWithRelationFastPath(locktag, mode) \
	((locktag)->locktag_lockmethodid == DEFAULT_LOCKMETHOD && \
	(locktag)->locktag_type == LOCKTAG_RELATION && \
	(locktag)->locktag_field1 != InvalidOid && \
	(mode) > ShareUpdateExclusiveLock)
/* (中文)fast-path 的两个判定谓词(见英文注释,fast-path 只关心"绑定
 * 在某数据库的后端"对"非共享关系的表级锁",且只处理很少冲突的
 * 模式):
 * - EligibleForRelationFastPath:请求 (locktag, mode) 能否走 fast-path?
 *   要求:默认锁方法 + 关系锁 + 本数据库对象(且确实绑定了数据库,
 *   即 MyDatabaseId 非 InvalidOid,说明非共享目录场景)+ 模式比
 *   ShareUpdateExclusiveLock 更弱(AccessShare/RowShare/RowExclusive)。
 * - ConflictsWithRelationFastPath:该锁会不会与别人的 fast-path 锁
 *   冲突?要求是关系锁(不限本数据库,共享对象也可能被 fast-path
 *   持有者锁定)+ 模式更强。加"强锁"时必须检查该谓词,以防遗漏
 *   fast-path 里的竞争者。
 * ShareUpdateExclusiveLock 因与自身冲突而不可走 fast-path,但它又
 * 与所有 fast-path 模式都不冲突,故可完全忽略。 */

static bool FastPathGrantRelationLock(Oid relid, LOCKMODE lockmode);
static bool FastPathUnGrantRelationLock(Oid relid, LOCKMODE lockmode);
static bool FastPathTransferRelationLocks(LockMethod lockMethodTable,
										  const LOCKTAG *locktag, uint32 hashcode);
static PROCLOCK *FastPathGetRelationLockEntry(LOCALLOCK *locallock);

/*
 * To make the fast-path lock mechanism work, we must have some way of
 * preventing the use of the fast-path when a conflicting lock might be present.
 * We partition* the locktag space into FAST_PATH_STRONG_LOCK_HASH_PARTITIONS,
 * and maintain an integer count of the number of "strong" lockers
 * in each partition.  When any "strong" lockers are present (which is
 * hopefully not very often), the fast-path mechanism can't be used, and we
 * must fall back to the slower method of pushing matching locks directly
 * into the main lock tables.
 *
 * The deadlock detector does not know anything about the fast path mechanism,
 * so any locks that might be involved in a deadlock must be transferred from
 * the fast-path queues to the main lock table.
 */

#define FAST_PATH_STRONG_LOCK_HASH_BITS			10
#define FAST_PATH_STRONG_LOCK_HASH_PARTITIONS \
	(1 << FAST_PATH_STRONG_LOCK_HASH_BITS)
#define FastPathStrongLockHashPartition(hashcode) \
	((hashcode) % FAST_PATH_STRONG_LOCK_HASH_PARTITIONS)

typedef struct
{
	slock_t		mutex;
	uint32		count[FAST_PATH_STRONG_LOCK_HASH_PARTITIONS];
} FastPathStrongRelationLockData;
/* (中文)共享内存中的"强锁计数"结构(见英文注释):把 locktag 哈希
 * 空间切成 1024 个分区(FAST_PATH_STRONG_LOCK_HASH_PARTITIONS),
 * 每区维护一个"当前持强锁的后端数"。任何分区计数 > 0 时,落入该
 * 分区的 fast-path 锁都必须搬进主锁表,以免被死锁检测器遗漏。
 * 计数随强锁的获取/释放增减,并用互斥锁保护。 */

static FastPathStrongRelationLockData *FastPathStrongRelationLocks;

static void LockManagerShmemRequest(void *arg);
static void LockManagerShmemInit(void *arg);

const ShmemCallbacks LockManagerShmemCallbacks = {
	.request_fn = LockManagerShmemRequest,
	.init_fn = LockManagerShmemInit,
};


/*
 * Pointers to hash tables containing lock state
 *
 * The LockMethodLockHash and LockMethodProcLockHash hash tables are in
 * shared memory; LockMethodLocalHash is local to each backend.
 */
/*
 * 锁状态的三张哈希表(见英文注释):
 * - LockMethodLockHash(共享):LOCKTAG → LOCK,即"这把锁存在吗、谁在等";
 * - LockMethodProcLockHash(共享):(proc, lock) → PROCLOCK,即"谁持有
 *   哪个锁的什么模式";
 * - LockMethodLocalHash(本后端私有):LOCKTAG → LOCALLOCK,记录本进程
 *   的持有计数与资源所有者归属,是前两者的本地缓存。
 */
static HTAB *LockMethodLockHash;
static HTAB *LockMethodProcLockHash;
static HTAB *LockMethodLocalHash;


/* private state for error cleanup */
static LOCALLOCK *StrongLockInProgress;
static LOCALLOCK *awaitedLock;
static ResourceOwner awaitedOwner;
/* (中文)错误清理用的私有状态:
 * - StrongLockInProgress:正在获取的"强锁"(其强锁计数已 +1,但可能
 *   在等待中出错,需在错误恢复路径里把计数退回);
 * - awaitedLock / awaitedOwner:当前正等的那把锁及其资源所有者,
 *   供 waitonlock_error_callback 在报错时打印等待上下文(如
 *   "process still waiting for ...")。 */


#ifdef LOCK_DEBUG

/*------
 * The following configuration options are available for lock debugging:
 *
 *	   TRACE_LOCKS		-- give a bunch of output what's going on in this file
 *	   TRACE_USERLOCKS	-- same but for user locks
 *	   TRACE_LOCK_OIDMIN-- do not trace locks for tables below this oid
 *						   (use to avoid output on system tables)
 *	   TRACE_LOCK_TABLE -- trace locks on this table (oid) unconditionally
 *	   DEBUG_DEADLOCKS	-- currently dumps locks at untimely occasions ;)
 *
 * Furthermore, but in storage/lmgr/lwlock.c:
 *	   TRACE_LWLOCKS	-- trace lightweight locks (pretty useless)
 *
 * Define LOCK_DEBUG at compile time to get all these enabled.
 * --------
 */

int			Trace_lock_oidmin = FirstNormalObjectId;
bool		Trace_locks = false;
bool		Trace_userlocks = false;
int			Trace_lock_table = 0;
bool		Debug_deadlocks = false;
/* (中文)锁调试 GUC(需编译 LOCK_DEBUG,见文件头英文注释):
 * - Trace_lock_oidmin:只追踪 OID 不小于该值的关系(避免系统表的噪音);
 * - Trace_locks / Trace_userlocks:分别开关标准锁与用户锁的追踪;
 * - Trace_lock_table:无条件追踪指定 OID 表上的锁;
 * - Debug_deadlocks:死锁相关调试输出。 */


/* (中文)(仅 LOCK_DEBUG)判定某锁是否值得输出追踪:该锁方法开了
 * 追踪开关且对象 OID 不低于下限,或是无条件追踪的目标表。 */
inline static bool
LOCK_DEBUG_ENABLED(const LOCKTAG *tag)
{
	return
		(*(LockMethods[tag->locktag_lockmethodid]->trace_flag) &&
		 ((Oid) tag->locktag_field2 >= (Oid) Trace_lock_oidmin))
		|| (Trace_lock_table &&
			(tag->locktag_field2 == Trace_lock_table));
}


/* (中文)(仅 LOCK_DEBUG)打印一把锁的完整状态:锁标签各字段、
 * grantMask、各模式的 requested/granted 计数、等待队列长度以及
 * 相关模式名,前缀 where 指明调用点。 */
inline static void
LOCK_PRINT(const char *where, const LOCK *lock, LOCKMODE type)
{	if (LOCK_DEBUG_ENABLED(&lock->tag))
		elog(LOG,
			 "%s: lock(%p) id(%u,%u,%u,%u,%u,%u) grantMask(%x) "
			 "req(%d,%d,%d,%d,%d,%d,%d)=%d "
			 "grant(%d,%d,%d,%d,%d,%d,%d)=%d wait(%d) type(%s)",
			 where, lock,
			 lock->tag.locktag_field1, lock->tag.locktag_field2,
			 lock->tag.locktag_field3, lock->tag.locktag_field4,
			 lock->tag.locktag_type, lock->tag.locktag_lockmethodid,
			 lock->grantMask,
			 lock->requested[1], lock->requested[2], lock->requested[3],
			 lock->requested[4], lock->requested[5], lock->requested[6],
			 lock->requested[7], lock->nRequested,
			 lock->granted[1], lock->granted[2], lock->granted[3],
			 lock->granted[4], lock->granted[5], lock->granted[6],
			 lock->granted[7], lock->nGranted,
			 dclist_count(&lock->waitProcs),
			 LockMethods[LOCK_LOCKMETHOD(*lock)]->lockModeNames[type]);
}


/* (中文)(仅 LOCK_DEBUG)打印一个 PROCLOCK:关联的锁、锁方法、持有者
 * 进程与持有模式掩码。 */
inline static void
PROCLOCK_PRINT(const char *where, const PROCLOCK *proclockP)
{
	if (LOCK_DEBUG_ENABLED(&proclockP->tag.myLock->tag))
		elog(LOG,
			 "%s: proclock(%p) lock(%p) method(%u) proc(%p) hold(%x)",
			 where, proclockP, proclockP->tag.myLock,
			 PROCLOCK_LOCKMETHOD(*(proclockP)),
			 proclockP->tag.myProc, (int) proclockP->holdMask);
}
#else							/* not LOCK_DEBUG */

#define LOCK_PRINT(where, lock, type)  ((void) 0)
#define PROCLOCK_PRINT(where, proclockP)  ((void) 0)
#endif							/* not LOCK_DEBUG */
static uint32 proclock_hash(const void *key, Size keysize);
static void RemoveLocalLock(LOCALLOCK *locallock);
static PROCLOCK *SetupLockInTable(LockMethod lockMethodTable, PGPROC *proc,
								  const LOCKTAG *locktag, uint32 hashcode, LOCKMODE lockmode);
static void GrantLockLocal(LOCALLOCK *locallock, ResourceOwner owner);
static void BeginStrongLockAcquire(LOCALLOCK *locallock, uint32 fasthashcode);
static void FinishStrongLockAcquire(void);
static ProcWaitStatus WaitOnLock(LOCALLOCK *locallock, ResourceOwner owner);
static void waitonlock_error_callback(void *arg);
static void ReleaseLockIfHeld(LOCALLOCK *locallock, bool sessionLock);
static void LockReassignOwner(LOCALLOCK *locallock, ResourceOwner parent);
static bool UnGrantLock(LOCK *lock, LOCKMODE lockmode,
						PROCLOCK *proclock, LockMethod lockMethodTable);
static void CleanUpLock(LOCK *lock, PROCLOCK *proclock,
						LockMethod lockMethodTable, uint32 hashcode,
						bool wakeupNeeded);
static void LockRefindAndRelease(LockMethod lockMethodTable, PGPROC *proc,
								 LOCKTAG *locktag, LOCKMODE lockmode,
								 bool decrement_strong_lock_count);
static void GetSingleProcBlockerStatusData(PGPROC *blocked_proc,
										   BlockedProcsData *data);
/* (中文)本文件内部辅助函数的原型清单(功能在各自定义处详述):
 * - proclock_hash:PROCLOCK 哈希键的散列函数;
 * - RemoveLocalLock:从本地锁表删除一个 LOCALLOCK;
 * - SetupLockInTable:在共享锁表中创建/更新 LOCK 与 PROCLOCK;
 * - GrantLockLocal:登记本后端本地"已获得"状态;
 * - Begin/FinishStrongLockAcquire:强锁获取前后的强锁计数进出栈;
 * - WaitOnLock + waitonlock_error_callback:入等待队列睡眠与错误上下文;
 * - ReleaseLockIfHeld / LockReassignOwner:释放/转移本地锁归属;
 * - UnGrantLock / CleanUpLock:共享锁表侧的撤权与收尾(唤醒等待者);
 * - LockRefindAndRelease:按 LOCKTAG 重新定位并释放锁(错误恢复用);
 * - GetSingleProcBlockerStatusData:收集阻塞链数据(供 pg_blocking_pids
 *   及锁等待报告使用)。 */


/*
 * Register the lock manager's shmem data structures.
 *
 * In addition to this, each backend must also call InitLockManagerAccess() to
 * create the locallock hash table.
 */
/*
 * LockManagerShmemRequest
 *      (中文)注册锁管理器的共享内存数据结构(shmem 预分配回调)
 *
 * 【作用】在共享内存预分配阶段(StartupProcess 之外的所有进程的
 * shmem 初始化流程里)向共享内存管理器"申报"锁表需要的大小:
 * 三张哈希表(LOCK、PROCLOCK、本地表则非共享),以及强锁计数区。
 * 若估算的锁表大小超过共享内存里其他数据结构占据的量,会给出
 * 建议提高 max_locks_per_xact 的 FATAL 错误。
 *
 * 【设计思想】max_table_size = NLOCKENTS()(见该宏:每后端上限 ×
 * (MaxBackends + max_prepared_xacts)),再乘以估算的每条记录大小
 * (并留出分区开销的余量)。锁表条目可能被临时"借用"作为 PROCLOCK
 * (同一内存池),因此单个池的容量要覆盖两者。
 *
 * 【参数】arg —— 回调上下文(未用)。
 * 【返回值】无。
 */
static void
LockManagerShmemRequest(void *arg)
{
	int64		max_table_size;

	/*
	 * Compute sizes for lock hashtables.
	 */
	max_table_size = NLOCKENTS();

	/*
	 * Hash table for LOCK structs.  This stores per-locked-object
	 * information.
	 */
	ShmemRequestHash(.name = "LOCK hash",
					 .nelems = max_table_size,
					 .ptr = &LockMethodLockHash,
					 .hash_info.keysize = sizeof(LOCKTAG),
					 .hash_info.entrysize = sizeof(LOCK),
					 .hash_info.num_partitions = NUM_LOCK_PARTITIONS,
					 .hash_flags = HASH_ELEM | HASH_BLOBS | HASH_PARTITION,
		);

	/* Assume an average of 2 holders per lock */
	max_table_size *= 2;

	ShmemRequestHash(.name = "PROCLOCK hash",
					 .nelems = max_table_size,
					 .ptr = &LockMethodProcLockHash,
					 .hash_info.keysize = sizeof(PROCLOCKTAG),
					 .hash_info.entrysize = sizeof(PROCLOCK),
					 .hash_info.hash = proclock_hash,
					 .hash_info.num_partitions = NUM_LOCK_PARTITIONS,
					 .hash_flags = HASH_ELEM | HASH_FUNCTION | HASH_PARTITION,
		);

	ShmemRequestStruct(.name = "Fast Path Strong Relation Lock Data",
					   .size = sizeof(FastPathStrongRelationLockData),
					   .ptr = (void **) (void *) &FastPathStrongRelationLocks,
		);
}

/* (中文)锁管理器共享内存的初始化回调(每个进程启动时执行):初始化
 * 强锁计数区的互斥锁。哈希表本体由 dynahash 在共享内存创建时完成。 */
static void
LockManagerShmemInit(void *arg)
{
	SpinLockInit(&FastPathStrongRelationLocks->mutex);
}

/*
 * Initialize the lock manager's backend-private data structures.
 */
/*
 * InitLockManagerAccess
 *      (中文)初始化锁管理器的后端私有数据结构(本地锁表)
 *
 * 【作用】创建本后端私有的 LOCALLOCK 哈希表(LockMethodLocalHash):
 * 键为 (LOCKTAG, mode),值为 LOCALLOCK(持有计数 + 资源所有者列表)。
 * 每个后端启动时都必须调用一次;共享表则由 LockManagerShmemRequest/
 * ShmemInit 负责。初始容量取 16,随需要自动扩展。
 *
 * 【参数】无。【返回值】无。
 */
void
InitLockManagerAccess(void)
{
	/*
	 * Allocate non-shared hash table for LOCALLOCK structs.  This stores lock
	 * counts and resource owner information.
	 */
	HASHCTL		info;

	info.keysize = sizeof(LOCALLOCKTAG);
	info.entrysize = sizeof(LOCALLOCK);

	LockMethodLocalHash = hash_create("LOCALLOCK hash",
									  16,
									  &info,
									  HASH_ELEM | HASH_BLOBS);
}


/*
 * Fetch the lock method table associated with a given lock
 */
/* (中文)由 LOCK 对象取回其锁方法表(默认锁方法或用户锁方法)。 */
LockMethod
GetLocksMethodTable(const LOCK *lock)
{
	LOCKMETHODID lockmethodid = LOCK_LOCKMETHOD(*lock);

	Assert(0 < lockmethodid && lockmethodid < lengthof(LockMethods));
	return LockMethods[lockmethodid];
}

/*
 * Fetch the lock method table associated with a given locktag
 */
/* (中文)由 LOCKTAG 取回其锁方法表。 */
LockMethod
GetLockTagsMethodTable(const LOCKTAG *locktag)
{
	LOCKMETHODID lockmethodid = (LOCKMETHODID) locktag->locktag_lockmethodid;

	Assert(0 < lockmethodid && lockmethodid < lengthof(LockMethods));
	return LockMethods[lockmethodid];
}


/*
 * Compute the hash code associated with a LOCKTAG.
 *
 * To avoid unnecessary recomputations of the hash code, we try to do this
 * just once per function, and then pass it around as needed.  Aside from
 * passing the hashcode to hash_search_with_hash_value(), we can extract
 * the lock partition number from the hashcode.
 */
/* (中文)计算 LOCKTAG 的哈希码。每个函数只算一次,再到处传递,避免
 * 重复计算;分区号可直接从哈希码低位提取(见 proc.c 的锁分区表)。 */
uint32
LockTagHashCode(const LOCKTAG *locktag)
{
	return get_hash_value(LockMethodLockHash, locktag);
}

/*
 * Compute the hash code associated with a PROCLOCKTAG.
 *
 * Because we want to use just one set of partition locks for both the
 * LOCK and PROCLOCK hash tables, we have to make sure that PROCLOCKs
 * fall into the same partition number as their associated LOCKs.
 * dynahash.c expects the partition number to be the low-order bits of
 * the hash code, and therefore a PROCLOCKTAG's hash code must have the
 * same low-order bits as the associated LOCKTAG's hash code.  We achieve
 * this with this specialized hash function.
 */
/* (中文)PROCLOCKTAG 的专用散列函数:先算其 LOCK 的哈希码,再把
 * PGPROC 地址异或进去(左移 LOG2_NUM_LOCK_PARTITIONS 位,保证低位的
 * 分区号不变)。这样 PROCLOCK 与其 LOCK 必然落入同一分区,共享同一
 * 组分区锁(见英文注释)。 */
static uint32
proclock_hash(const void *key, Size keysize)
{
	const PROCLOCKTAG *proclocktag = (const PROCLOCKTAG *) key;
	uint32		lockhash;
	Datum		procptr;

	Assert(keysize == sizeof(PROCLOCKTAG));

	/* Look into the associated LOCK object, and compute its hash code */
	lockhash = LockTagHashCode(&proclocktag->myLock->tag);

	/*
	 * To make the hash code also depend on the PGPROC, we xor the proc
	 * struct's address into the hash code, left-shifted so that the
	 * partition-number bits don't change.  Since this is only a hash, we
	 * don't care if we lose high-order bits of the address; use an
	 * intermediate variable to suppress cast-pointer-to-int warnings.
	 */
	procptr = PointerGetDatum(proclocktag->myProc);
	lockhash ^= DatumGetUInt32(procptr) << LOG2_NUM_LOCK_PARTITIONS;

	return lockhash;
}

/*
 * Compute the hash code associated with a PROCLOCKTAG, given the hashcode
 * for its underlying LOCK.
 *
 * We use this just to avoid redundant calls of LockTagHashCode().
 */
/* (中文)已知 LOCK 哈希码时计算 PROCLOCKTAG 哈希码的快捷版本:与
 * proclock_hash 结果必须完全一致(只省去重算 LockTagHashCode)。 */
static inline uint32
ProcLockHashCode(const PROCLOCKTAG *proclocktag, uint32 hashcode)
{
	uint32		lockhash = hashcode;
	Datum		procptr;

	/*
	 * This must match proclock_hash()!
	 */
	procptr = PointerGetDatum(proclocktag->myProc);
	lockhash ^= DatumGetUInt32(procptr) << LOG2_NUM_LOCK_PARTITIONS;

	return lockhash;
}

/*
 * Given two lock modes, return whether they would conflict.
 */
/* (中文)判断两种锁模式是否冲突:查默认锁方法的冲突矩阵
 * (conflictTab[mode1] 掩码里是否含 mode2 的位)。 */
bool
DoLockModesConflict(LOCKMODE mode1, LOCKMODE mode2)
{
	LockMethod	lockMethodTable = LockMethods[DEFAULT_LOCKMETHOD];

	if (lockMethodTable->conflictTab[mode1] & LOCKBIT_ON(mode2))
		return true;

	return false;
}


/*
 * LockHeldByMe -- test whether lock 'locktag' is held by the current
 *		transaction
 *
 * Returns true if current transaction holds a lock on 'tag' of mode
 * 'lockmode'.  If 'orstronger' is true, a stronger lockmode is also OK.
 * ("Stronger" is defined as "numerically higher", which is a bit
 * semantically dubious but is OK for the purposes we use this for.)
 */
/* (中文)测试当前事务是否持有 'locktag' 上 'lockmode' 的锁(只查本地
 * LOCALLOCK 表,nLocks > 0 即持有,不碰共享锁表、不等待)。orstronger
 * 为 true 时,更强的模式也算(遍历从 lockmode+1 到 MaxLockMode 递归
 * 复查)。注意:只是"数值上更强",语义上近似,但对本函数的使用
 * 场景足够准确。 */
bool
LockHeldByMe(const LOCKTAG *locktag,
			 LOCKMODE lockmode, bool orstronger)
{	LOCALLOCKTAG localtag;
	LOCALLOCK  *locallock;

	/*
	 * See if there is a LOCALLOCK entry for this lock and lockmode
	 */
	MemSet(&localtag, 0, sizeof(localtag)); /* must clear padding */
	localtag.lock = *locktag;
	localtag.mode = lockmode;

	locallock = (LOCALLOCK *) hash_search(LockMethodLocalHash,
										  &localtag,
										  HASH_FIND, NULL);

	if (locallock && locallock->nLocks > 0)
		return true;

	if (orstronger)
	{
		LOCKMODE	slockmode;

		for (slockmode = lockmode + 1;
			 slockmode <= MaxLockMode;
			 slockmode++)
		{
			if (LockHeldByMe(locktag, slockmode, false))
				return true;
		}
	}

	return false;
}

#ifdef USE_ASSERT_CHECKING
/*
 * GetLockMethodLocalHash -- return the hash of local locks, for modules that
 *		evaluate assertions based on all locks held.
 */
/* (中文)(仅断言构建)返回本地锁表哈希的句柄,供需要枚举"本后端
 * 当前持有哪些锁"的断言代码使用。 */
HTAB *
GetLockMethodLocalHash(void)
{
	return LockMethodLocalHash;
}
#endif

/*
 * LockHasWaiters -- look up 'locktag' and check if releasing this
 *		lock would wake up other processes waiting for it.
 */
/*
 * LockHasWaiters
 *      (中文)检查"释放该锁是否会唤醒其他等待者"
 *
 * 【作用】在共享锁表中找到这把锁,看它的等待掩码(waitMask)里有没有
 * 与 lockmode 冲突的模式:有,说明有别的事务正等着我们释放该锁。
 *
 * 【设计思想】先查本地表确认我们确实持有该锁(未持有则 WARNING 并
 * 返回 false,不抛错,让调用者自己决定措辞);再拿分区锁(共享模式)
 * 查共享表。持有期间 LOCK/PROCLOCK 不会被移除,故可直接用本地表里
 * 缓存的两个指针,无需重查。
 *
 * 【注意】如文件头所述,这是"尽力而为"的检查:等待队列状态可瞬时
 * 变化,返回 true 只是提示。调用方应避免依赖它的精确性。
 *
 * 【参数】locktag —— 锁标签;lockmode —— 关心的锁模式;
 * sessionLock —— 本函数不使用(签名兼容,见英文注释)。
 * 【返回值】true = 存在等待该锁的进程;false = 没有(或未持有该锁)。
 */
bool
LockHasWaiters(const LOCKTAG *locktag, LOCKMODE lockmode, bool sessionLock)
{
	LOCKMETHODID lockmethodid = locktag->locktag_lockmethodid;
	LockMethod	lockMethodTable;
	LOCALLOCKTAG localtag;
	LOCALLOCK  *locallock;
	LOCK	   *lock;
	PROCLOCK   *proclock;
	LWLock	   *partitionLock;
	bool		hasWaiters = false;

	/*
	 * sessionLock 参数本函数未使用(保留是为了与其它接口签名一致);
	 * 语义上"是否有等待者"只与共享锁表的等待队列有关。
	 */
	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);
	lockMethodTable = LockMethods[lockmethodid];
	if (lockmode <= 0 || lockmode > lockMethodTable->numLockModes)
		elog(ERROR, "unrecognized lock mode: %d", lockmode);

#ifdef LOCK_DEBUG
	if (LOCK_DEBUG_ENABLED(locktag))
		elog(LOG, "LockHasWaiters: lock [%u,%u] %s",
			 locktag->locktag_field1, locktag->locktag_field2,
			 lockMethodTable->lockModeNames[lockmode]);
#endif

	/*
	 * Find the LOCALLOCK entry for this lock and lockmode
	 */
	MemSet(&localtag, 0, sizeof(localtag)); /* must clear padding */
	localtag.lock = *locktag;
	localtag.mode = lockmode;

	locallock = (LOCALLOCK *) hash_search(LockMethodLocalHash,
										  &localtag,
										  HASH_FIND, NULL);

	/*
	 * let the caller print its own error message, too. Do not ereport(ERROR).
	 */
	if (!locallock || locallock->nLocks <= 0)
	{
		elog(WARNING, "you don't own a lock of type %s",
			 lockMethodTable->lockModeNames[lockmode]);
		return false;
	}

	/*
	 * Check the shared lock table.
	 */
	partitionLock = LockHashPartitionLock(locallock->hashcode);

	LWLockAcquire(partitionLock, LW_SHARED);

	/*
	 * We don't need to re-find the lock or proclock, since we kept their
	 * addresses in the locallock table, and they couldn't have been removed
	 * while we were holding a lock on them.
	 */
	lock = locallock->lock;
	LOCK_PRINT("LockHasWaiters: found", lock, lockmode);
	proclock = locallock->proclock;
	PROCLOCK_PRINT("LockHasWaiters: found", proclock);

	/*
	 * Double-check that we are actually holding a lock of the type we want to
	 * release.
	 */
	if (!(proclock->holdMask & LOCKBIT_ON(lockmode)))
	{
		PROCLOCK_PRINT("LockHasWaiters: WRONGTYPE", proclock);
		LWLockRelease(partitionLock);
		elog(WARNING, "you don't own a lock of type %s",
			 lockMethodTable->lockModeNames[lockmode]);
		RemoveLocalLock(locallock);
		return false;
	}

	/*
	 * Do the checking.
	 */
	if ((lockMethodTable->conflictTab[lockmode] & lock->waitMask) != 0)
		hasWaiters = true;

	LWLockRelease(partitionLock);

	return hasWaiters;
}

/*
 * LockAcquire -- Check for lock conflicts, sleep if conflict found,
 *		set lock if/when no conflicts.
 *
 * Inputs:
 *	locktag: unique identifier for the lockable object
 *	lockmode: lock mode to acquire
 *	sessionLock: if true, acquire lock for session not current transaction
 *	dontWait: if true, don't wait to acquire lock
 *
 * Returns one of:
 *		LOCKACQUIRE_NOT_AVAIL		lock not available, and dontWait=true
 *		LOCKACQUIRE_OK				lock successfully acquired
 *		LOCKACQUIRE_ALREADY_HELD	incremented count for lock already held
 *		LOCKACQUIRE_ALREADY_CLEAR	incremented count for lock already clear
 *
 * In the normal case where dontWait=false and the caller doesn't need to
 * distinguish a freshly acquired lock from one already taken earlier in
 * this same transaction, there is no need to examine the return value.
 *
 * Side Effects: The lock is acquired and recorded in lock tables.
 *
 * NOTE: if we wait for the lock, there is no way to abort the wait
 * short of aborting the transaction.
 */
/*
 * LockAcquire
 *      (中文)获取一把重锁(标准入口)
 *
 * 【作用】检查锁冲突:冲突则睡眠等待,无冲突则立即获得。这是
 * LockAcquireExtended 的默认参数封装(检查内存错误报告、无回调、
 * 不记失败日志)。
 *
 * 【返回值】见英文注释的四种 LOCKACQUIRE_* 结果;dontWait=false 且
 * 不关心"新获得"与"已持有"之别的调用者可以忽略返回值。
 * 【注意】一旦进入等待,除中止事务外无法取消等待。
 */
LockAcquireResult
LockAcquire(const LOCKTAG *locktag,
			LOCKMODE lockmode,
			bool sessionLock,
			bool dontWait)
{
	return LockAcquireExtended(locktag, lockmode, sessionLock, dontWait,
							   true, NULL, false);
}

/*
 * LockAcquireExtended - allows us to specify additional options
 *
 * reportMemoryError specifies whether a lock request that fills the lock
 * table should generate an ERROR or not.  Passing "false" allows the caller
 * to attempt to recover from lock-table-full situations, perhaps by forcibly
 * canceling other lock holders and then retrying.  Note, however, that the
 * return code for that is LOCKACQUIRE_NOT_AVAIL, so that it's unsafe to use
 * in combination with dontWait = true, as the cause of failure couldn't be
 * distinguished.
 *
 * If locallockp isn't NULL, *locallockp receives a pointer to the LOCALLOCK
 * table entry if a lock is successfully acquired, or NULL if not.
 *
 * logLockFailure indicates whether to log details when a lock acquisition
 * fails with dontWait = true.
 */
/*
 * LockAcquireExtended
 *      (中文)获取重锁的核心实现(LockAcquire 的增强版)
 *
 * 【作用】完整走一遍"获取重锁"流程:查本地表 →(可走 fast-path 则
 * 尝试)→ 必要时进共享锁表建/查 LOCK、PROCLOCK → 冲突则入队等待 →
 * 醒来后处理唤醒/取消/死锁结果 → 更新本地计数与 WAL 日志。这是本
 * 文件最重要、也最长的路径。
 *
 * 【主要步骤】(详细逻辑见函数体内的英文注释)
 * 1. 参数合法性检查 + recovery 期间的限制:恢复中不允许对
 *    LOCKTAG_OBJECT/RELATION 加比 RowExclusiveLock 更强的锁(standby
 *    上只读事务可获取的锁模式必须受限);
 * 2. 确定资源所有者:会话级锁 owner = NULL(挂到会话上),否则挂到
 *    CurrentResourceOwner;查找/创建 LOCALLOCK 条目(含 lockOwners
 *    数组按需翻倍);
 * 3. 若本地已计数(nLocks > 0):本地计数 +1 直接返回
 *    LOCKACQUIRE_ALREADY_HELD / _ALREADY_CLEAR(后者表示上次加锁时
 *    已经吸收过失效消息,调用者不必再吸收);
 * 4. 关系扩展锁不变量断言(持扩展锁期间不再拿别的重锁);
 * 5. 需要 WAL 保护时(AccessExclusiveLock 的关系锁、standby 信息激活)
 *    先做 WAL 日志准备(log_lock),锁定成功后写日志——这样 standby
 *    恢复时能重放该锁(避免 fast-path 锁在 standby 上不可见导致的
 *    冲突误判);
 * 6. fast-path 尝试(EligibleForRelationFastPath):组内槽未满且该哈希
 *    分区无"强锁"时,直接在 fpLockBits 里置位,返回 OK,完全不碰
 *    共享锁表;
 * 7. 强锁路径(ConflictsWithRelationFastPath):BeginStrongLockAcquire
 *    登记强锁计数,并把其他后端的 fast-path 锁迁移进共享表
 *    (FastPathTransferRelationLocks)——否则死锁检测器看不到它们;
 *    迁移失败按 reportMemoryError 决定报 ERROR 或返回 NOT_AVAIL;
 * 8. 主路径:拿分区排他锁,SetupLockInTable 建/查 LOCK/PROCLOCK,
 *    依次检查"与等待者的冲突"与"与已持有者的冲突"
 *    (LockCheckConflicts);无冲突则 GrantLock;有冲突则 JoinWaitQueue
 *    (即使 dontWait 也调用,因为入队过程可能发现可以立即获得);
 * 9. 等待结果处理:ERROR(死锁/取消/不允许等待)时清理计数并(若本
 *    事务原已持有)保留原锁;PROC_WAIT_STATUS_NOT_SET 按死锁处理并
 *    报告;OK 则统计、WAL 写日志、返回。
 *
 * 【参数】locktag —— 锁标签;lockmode —— 模式;sessionLock —— 会话级?
 * dontWait —— 不等待(拿不到立即失败);reportMemoryError —— 锁表满时
 * 是否报 ERROR(false 则返回 NOT_AVAIL 供调用者重试);locallockp ——
 * 成功时输出 LOCALLOCK 指针;logLockFailure —— dontWait 失败时记日志。
 * 【返回值】LOCKACQUIRE_OK / ALREADY_HELD / ALREADY_CLEAR /
 * NOT_AVAIL(见英文注释)。
 */
LockAcquireResult
LockAcquireExtended(const LOCKTAG *locktag,
					LOCKMODE lockmode,
					bool sessionLock,
					bool dontWait,
					bool reportMemoryError,
					LOCALLOCK **locallockp,
					bool logLockFailure)
{
	LOCKMETHODID lockmethodid = locktag->locktag_lockmethodid;
	LockMethod	lockMethodTable;
	LOCALLOCKTAG localtag;
	LOCALLOCK  *locallock;
	LOCK	   *lock;
	PROCLOCK   *proclock;
	bool		found;
	ResourceOwner owner;
	uint32		hashcode;
	LWLock	   *partitionLock;
	bool		found_conflict;
	ProcWaitStatus waitResult;
	bool		log_lock = false;

	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);
	lockMethodTable = LockMethods[lockmethodid];
	if (lockmode <= 0 || lockmode > lockMethodTable->numLockModes)
		elog(ERROR, "unrecognized lock mode: %d", lockmode);

	if (RecoveryInProgress() && !InRecovery &&
		(locktag->locktag_type == LOCKTAG_OBJECT ||
		 locktag->locktag_type == LOCKTAG_RELATION) &&
		lockmode > RowExclusiveLock)
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("cannot acquire lock mode %s on database objects while recovery is in progress",
						lockMethodTable->lockModeNames[lockmode]),
				 errhint("Only RowExclusiveLock or less can be acquired on database objects during recovery.")));

#ifdef LOCK_DEBUG
	if (LOCK_DEBUG_ENABLED(locktag))
		elog(LOG, "LockAcquire: lock [%u,%u] %s",
			 locktag->locktag_field1, locktag->locktag_field2,
			 lockMethodTable->lockModeNames[lockmode]);
#endif

	/* Identify owner for lock */
	if (sessionLock)
		owner = NULL;
	else
		owner = CurrentResourceOwner;

	/*
	 * Find or create a LOCALLOCK entry for this lock and lockmode
	 */
	MemSet(&localtag, 0, sizeof(localtag)); /* must clear padding */
	localtag.lock = *locktag;
	localtag.mode = lockmode;

	locallock = (LOCALLOCK *) hash_search(LockMethodLocalHash,
										  &localtag,
										  HASH_ENTER, &found);

	/*
	 * if it's a new locallock object, initialize it
	 */
	if (!found)
	{
		locallock->lock = NULL;
		locallock->proclock = NULL;
		locallock->hashcode = LockTagHashCode(&(localtag.lock));
		locallock->nLocks = 0;
		locallock->holdsStrongLockCount = false;
		locallock->lockCleared = false;
		locallock->numLockOwners = 0;
		locallock->maxLockOwners = 8;
		locallock->lockOwners = NULL;	/* in case next line fails */
		locallock->lockOwners = (LOCALLOCKOWNER *)
			MemoryContextAlloc(TopMemoryContext,
							   locallock->maxLockOwners * sizeof(LOCALLOCKOWNER));
	}
	else
	{
		/* Make sure there will be room to remember the lock */
		if (locallock->numLockOwners >= locallock->maxLockOwners)
		{
			int			newsize = locallock->maxLockOwners * 2;

			locallock->lockOwners = (LOCALLOCKOWNER *)
				repalloc(locallock->lockOwners,
						 newsize * sizeof(LOCALLOCKOWNER));
			locallock->maxLockOwners = newsize;
		}
	}
	hashcode = locallock->hashcode;

	if (locallockp)
		*locallockp = locallock;

	/*
	 * If we already hold the lock, we can just increase the count locally.
	 *
	 * If lockCleared is already set, caller need not worry about absorbing
	 * sinval messages related to the lock's object.
	 */
	if (locallock->nLocks > 0)
	{
		GrantLockLocal(locallock, owner);
		if (locallock->lockCleared)
			return LOCKACQUIRE_ALREADY_CLEAR;
		else
			return LOCKACQUIRE_ALREADY_HELD;
	}

	/*
	 * We don't acquire any other heavyweight lock while holding the relation
	 * extension lock.  We do allow to acquire the same relation extension
	 * lock more than once but that case won't reach here.
	 */
	Assert(!IsRelationExtensionLockHeld);

	/*
	 * Prepare to emit a WAL record if acquisition of this lock needs to be
	 * replayed in a standby server.
	 *
	 * Here we prepare to log; after lock is acquired we'll issue log record.
	 * This arrangement simplifies error recovery in case the preparation step
	 * fails.
	 *
	 * Only AccessExclusiveLocks can conflict with lock types that read-only
	 * transactions can acquire in a standby server. Make sure this definition
	 * matches the one in GetRunningTransactionLocks().
	 */
	if (lockmode >= AccessExclusiveLock &&
		locktag->locktag_type == LOCKTAG_RELATION &&
		!RecoveryInProgress() &&
		XLogStandbyInfoActive())
	{
		LogAccessExclusiveLockPrepare();
		log_lock = true;
	}

	/*
	 * Attempt to take lock via fast path, if eligible.  But if we remember
	 * having filled up the fast path array, we don't attempt to make any
	 * further use of it until we release some locks.  It's possible that some
	 * other backend has transferred some of those locks to the shared hash
	 * table, leaving space free, but it's not worth acquiring the LWLock just
	 * to check.  It's also possible that we're acquiring a second or third
	 * lock type on a relation we have already locked using the fast-path, but
	 * for now we don't worry about that case either.
	 */
	if (EligibleForRelationFastPath(locktag, lockmode))
	{
		if (FastPathLocalUseCounts[FAST_PATH_REL_GROUP(locktag->locktag_field2)] <
			FP_LOCK_SLOTS_PER_GROUP)
		{
			uint32		fasthashcode = FastPathStrongLockHashPartition(hashcode);
			bool		acquired;

			/*
			 * LWLockAcquire acts as a memory sequencing point, so it's safe
			 * to assume that any strong locker whose increment to
			 * FastPathStrongRelationLocks->counts becomes visible after we
			 * test it has yet to begin to transfer fast-path locks.
			 */
			LWLockAcquire(&MyProc->fpInfoLock, LW_EXCLUSIVE);
			if (FastPathStrongRelationLocks->count[fasthashcode] != 0)
				acquired = false;
			else
				acquired = FastPathGrantRelationLock(locktag->locktag_field2,
													 lockmode);
			LWLockRelease(&MyProc->fpInfoLock);
			if (acquired)
			{
				/*
				 * The locallock might contain stale pointers to some old
				 * shared objects; we MUST reset these to null before
				 * considering the lock to be acquired via fast-path.
				 */
				locallock->lock = NULL;
				locallock->proclock = NULL;
				GrantLockLocal(locallock, owner);
				return LOCKACQUIRE_OK;
			}
		}
		else
		{
			/*
			 * Increment the lock statistics counter if lock could not be
			 * acquired via the fast-path.
			 */
			pgstat_count_lock_fastpath_exceeded(locallock->tag.lock.locktag_type);
		}
	}

	/*
	 * If this lock could potentially have been taken via the fast-path by
	 * some other backend, we must (temporarily) disable further use of the
	 * fast-path for this lock tag, and migrate any locks already taken via
	 * this method to the main lock table.
	 */
	if (ConflictsWithRelationFastPath(locktag, lockmode))
	{
		uint32		fasthashcode = FastPathStrongLockHashPartition(hashcode);

		BeginStrongLockAcquire(locallock, fasthashcode);
		if (!FastPathTransferRelationLocks(lockMethodTable, locktag,
										   hashcode))
		{
			AbortStrongLockAcquire();
			if (locallock->nLocks == 0)
				RemoveLocalLock(locallock);
			if (locallockp)
				*locallockp = NULL;
			if (reportMemoryError)
				ereport(ERROR,
						(errcode(ERRCODE_OUT_OF_MEMORY),
						 errmsg("out of shared memory"),
						 errhint("You might need to increase \"%s\".", "max_locks_per_transaction")));
			else
				return LOCKACQUIRE_NOT_AVAIL;
		}
	}

	/*
	 * We didn't find the lock in our LOCALLOCK table, and we didn't manage to
	 * take it via the fast-path, either, so we've got to mess with the shared
	 * lock table.
	 */
	partitionLock = LockHashPartitionLock(hashcode);

	LWLockAcquire(partitionLock, LW_EXCLUSIVE);

	/*
	 * Find or create lock and proclock entries with this tag
	 *
	 * Note: if the locallock object already existed, it might have a pointer
	 * to the lock already ... but we should not assume that that pointer is
	 * valid, since a lock object with zero hold and request counts can go
	 * away anytime.  So we have to use SetupLockInTable() to recompute the
	 * lock and proclock pointers, even if they're already set.
	 */
	proclock = SetupLockInTable(lockMethodTable, MyProc, locktag,
								hashcode, lockmode);
	if (!proclock)
	{
		AbortStrongLockAcquire();
		LWLockRelease(partitionLock);
		if (locallock->nLocks == 0)
			RemoveLocalLock(locallock);
		if (locallockp)
			*locallockp = NULL;
		if (reportMemoryError)
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of shared memory"),
					 errhint("You might need to increase \"%s\".", "max_locks_per_transaction")));
		else
			return LOCKACQUIRE_NOT_AVAIL;
	}
	locallock->proclock = proclock;
	lock = proclock->tag.myLock;
	locallock->lock = lock;

	/*
	 * If lock requested conflicts with locks requested by waiters, must join
	 * wait queue.  Otherwise, check for conflict with already-held locks.
	 * (That's last because most complex check.)
	 */
	if (lockMethodTable->conflictTab[lockmode] & lock->waitMask)
		found_conflict = true;
	else
		found_conflict = LockCheckConflicts(lockMethodTable, lockmode,
											lock, proclock);

	if (!found_conflict)
	{
		/* No conflict with held or previously requested locks */
		GrantLock(lock, proclock, lockmode);
		waitResult = PROC_WAIT_STATUS_OK;
	}
	else
	{
		/*
		 * Join the lock's wait queue.  We call this even in the dontWait
		 * case, because JoinWaitQueue() may discover that we can acquire the
		 * lock immediately after all.
		 */
		waitResult = JoinWaitQueue(locallock, lockMethodTable, dontWait);
	}

	if (waitResult == PROC_WAIT_STATUS_ERROR)
	{
		/*
		 * We're not getting the lock because a deadlock was detected already
		 * while trying to join the wait queue, or because we would have to
		 * wait but the caller requested no blocking.
		 *
		 * Undo the changes to shared entries before releasing the partition
		 * lock.
		 */
		AbortStrongLockAcquire();

		if (proclock->holdMask == 0)
		{
			uint32		proclock_hashcode;

			proclock_hashcode = ProcLockHashCode(&proclock->tag,
												 hashcode);
			dlist_delete(&proclock->lockLink);
			dlist_delete(&proclock->procLink);
			if (!hash_search_with_hash_value(LockMethodProcLockHash,
											 &(proclock->tag),
											 proclock_hashcode,
											 HASH_REMOVE,
											 NULL))
				elog(PANIC, "proclock table corrupted");
		}
		else
			PROCLOCK_PRINT("LockAcquire: did not join wait queue", proclock);
		lock->nRequested--;
		lock->requested[lockmode]--;
		LOCK_PRINT("LockAcquire: did not join wait queue",
				   lock, lockmode);
		Assert((lock->nRequested > 0) &&
			   (lock->requested[lockmode] >= 0));
		Assert(lock->nGranted <= lock->nRequested);
		LWLockRelease(partitionLock);
		if (locallock->nLocks == 0)
			RemoveLocalLock(locallock);

		if (dontWait)
		{
			/*
			 * Log lock holders and waiters as a detail log message if
			 * logLockFailure = true and lock acquisition fails with dontWait
			 * = true
			 */
			if (logLockFailure)
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

				ereport(LOG,
						(errmsg("process %d could not obtain %s on %s",
								MyProcPid, modename, buf.data),
						 errdetail_log_plural(
											  "Process holding the lock: %s, Wait queue: %s.",
											  "Processes holding the lock: %s, Wait queue: %s.",
											  lockHoldersNum,
											  lock_holders_sbuf.data,
											  lock_waiters_sbuf.data)));

				pfree(buf.data);
				pfree(lock_holders_sbuf.data);
				pfree(lock_waiters_sbuf.data);
			}
			if (locallockp)
				*locallockp = NULL;
			return LOCKACQUIRE_NOT_AVAIL;
		}
		else
		{
			DeadLockReport();
			/* DeadLockReport() will not return */
		}
	}

	/*
	 * We are now in the lock queue, or the lock was already granted.  If
	 * queued, go to sleep.
	 */
	if (waitResult == PROC_WAIT_STATUS_WAITING)
	{
		Assert(!dontWait);
		PROCLOCK_PRINT("LockAcquire: sleeping on lock", proclock);
		LOCK_PRINT("LockAcquire: sleeping on lock", lock, lockmode);
		LWLockRelease(partitionLock);

		waitResult = WaitOnLock(locallock, owner);

		/*
		 * NOTE: do not do any material change of state between here and
		 * return.  All required changes in locktable state must have been
		 * done when the lock was granted to us --- see notes in WaitOnLock.
		 */

		if (waitResult == PROC_WAIT_STATUS_ERROR)
		{
			/*
			 * We failed as a result of a deadlock, see CheckDeadLock(). Quit
			 * now.
			 */
			Assert(!dontWait);
			DeadLockReport();
			/* DeadLockReport() will not return */
		}
	}
	else
		LWLockRelease(partitionLock);
	Assert(waitResult == PROC_WAIT_STATUS_OK);

	/* The lock was granted to us.  Update the local lock entry accordingly */
	Assert((proclock->holdMask & LOCKBIT_ON(lockmode)) != 0);
	GrantLockLocal(locallock, owner);

	/*
	 * Lock state is fully up-to-date now; if we error out after this, no
	 * special error cleanup is required.
	 */
	FinishStrongLockAcquire();

	/*
	 * Emit a WAL record if acquisition of this lock needs to be replayed in a
	 * standby server.
	 */
	if (log_lock)
	{
		/*
		 * Decode the locktag back to the original values, to avoid sending
		 * lots of empty bytes with every message.  See lock.h to check how a
		 * locktag is defined for LOCKTAG_RELATION
		 */
		LogAccessExclusiveLock(locktag->locktag_field1,
							   locktag->locktag_field2);
	}

	return LOCKACQUIRE_OK;
}

/*
 * Find or create LOCK and PROCLOCK objects as needed for a new lock
 * request.
 *
 * Returns the PROCLOCK object, or NULL if we failed to create the objects
 * for lack of shared memory.
 *
 * The appropriate partition lock must be held at entry, and will be
 * held at exit.
 */
/*
 * SetupLockInTable
 *      (中文)为加锁请求在共享表中查找/创建 LOCK 与 PROCLOCK
 *
 * 【作用】按 locktag 查共享锁表:没有就创建新的 LOCK 并初始化(掩码
 * 清零、链首初始化);然后把 (proc, lock) 的 PROCLOCK 也查/建出来,
 * 并让 proc 的锁数组(locallock)绑定这两个共享对象。
 *
 * 【设计思想】键都是"值"语义(LOCKTAG / PROCLOCKTAG),用哈希键直接
 * 查找;PROCLOCK 的哈希码由 proclock_hash 保证与 LOCK 同分区。新建
 * LOCK 时还把"持有进程数"统计计数初始化。调用者必须已持有分区锁,
 * 返回时仍持有。
 *
 * 【参数】
 *   lockMethodTable —— 锁方法表;
 *   proc            —— 锁的请求者(通常 MyProc);
 *   locktag/hashcode—— 锁标签及其哈希码;
 *   lockmode        —— 请求的锁模式(用于初始化 requested 计数)。
 * 【返回值】PROCLOCK 指针;共享内存不足返回 NULL(此时可能已创建
 * 了 LOCK,但由调用方决定如何处理,见其错误路径)。
 */
static PROCLOCK *
SetupLockInTable(LockMethod lockMethodTable, PGPROC *proc,
				 const LOCKTAG *locktag, uint32 hashcode, LOCKMODE lockmode)
{
	LOCK	   *lock;
	PROCLOCK   *proclock;
	PROCLOCKTAG proclocktag;
	uint32		proclock_hashcode;
	bool		found;

	/*
	 * Find or create a lock with this tag.
	 */
	lock = (LOCK *) hash_search_with_hash_value(LockMethodLockHash,
												locktag,
												hashcode,
												HASH_ENTER_NULL,
												&found);
	if (!lock)
		return NULL;

	/*
	 * if it's a new lock object, initialize it
	 */
	if (!found)
	{
		lock->grantMask = 0;
		lock->waitMask = 0;
		dlist_init(&lock->procLocks);
		dclist_init(&lock->waitProcs);
		lock->nRequested = 0;
		lock->nGranted = 0;
		MemSet(lock->requested, 0, sizeof(int) * MAX_LOCKMODES);
		MemSet(lock->granted, 0, sizeof(int) * MAX_LOCKMODES);
		LOCK_PRINT("LockAcquire: new", lock, lockmode);
	}
	else
	{
		LOCK_PRINT("LockAcquire: found", lock, lockmode);
		Assert((lock->nRequested >= 0) && (lock->requested[lockmode] >= 0));
		Assert((lock->nGranted >= 0) && (lock->granted[lockmode] >= 0));
		Assert(lock->nGranted <= lock->nRequested);
	}

	/*
	 * Create the hash key for the proclock table.
	 */
	proclocktag.myLock = lock;
	proclocktag.myProc = proc;

	proclock_hashcode = ProcLockHashCode(&proclocktag, hashcode);

	/*
	 * Find or create a proclock entry with this tag
	 */
	proclock = (PROCLOCK *) hash_search_with_hash_value(LockMethodProcLockHash,
														&proclocktag,
														proclock_hashcode,
														HASH_ENTER_NULL,
														&found);
	if (!proclock)
	{
		/* Oops, not enough shmem for the proclock */
		if (lock->nRequested == 0)
		{
			/*
			 * There are no other requestors of this lock, so garbage-collect
			 * the lock object.  We *must* do this to avoid a permanent leak
			 * of shared memory, because there won't be anything to cause
			 * anyone to release the lock object later.
			 */
			Assert(dlist_is_empty(&(lock->procLocks)));
			if (!hash_search_with_hash_value(LockMethodLockHash,
											 &(lock->tag),
											 hashcode,
											 HASH_REMOVE,
											 NULL))
				elog(PANIC, "lock table corrupted");
		}
		return NULL;
	}

	/*
	 * If new, initialize the new entry
	 */
	if (!found)
	{
		uint32		partition = LockHashPartition(hashcode);

		/*
		 * It might seem unsafe to access proclock->groupLeader without a
		 * lock, but it's not really.  Either we are initializing a proclock
		 * on our own behalf, in which case our group leader isn't changing
		 * because the group leader for a process can only ever be changed by
		 * the process itself; or else we are transferring a fast-path lock to
		 * the main lock table, in which case that process can't change its
		 * lock group leader without first releasing all of its locks (and in
		 * particular the one we are currently transferring).
		 */
		proclock->groupLeader = proc->lockGroupLeader != NULL ?
			proc->lockGroupLeader : proc;
		proclock->holdMask = 0;
		proclock->releaseMask = 0;
		/* Add proclock to appropriate lists */
		dlist_push_tail(&lock->procLocks, &proclock->lockLink);
		dlist_push_tail(&proc->myProcLocks[partition], &proclock->procLink);
		PROCLOCK_PRINT("LockAcquire: new", proclock);
	}
	else
	{
		PROCLOCK_PRINT("LockAcquire: found", proclock);
		Assert((proclock->holdMask & ~lock->grantMask) == 0);

#ifdef CHECK_DEADLOCK_RISK

		/*
		 * Issue warning if we already hold a lower-level lock on this object
		 * and do not hold a lock of the requested level or higher. This
		 * indicates a deadlock-prone coding practice (eg, we'd have a
		 * deadlock if another backend were following the same code path at
		 * about the same time).
		 *
		 * This is not enabled by default, because it may generate log entries
		 * about user-level coding practices that are in fact safe in context.
		 * It can be enabled to help find system-level problems.
		 *
		 * XXX Doing numeric comparison on the lockmodes is a hack; it'd be
		 * better to use a table.  For now, though, this works.
		 */
		{
			int			i;

			for (i = lockMethodTable->numLockModes; i > 0; i--)
			{
				if (proclock->holdMask & LOCKBIT_ON(i))
				{
					if (i >= (int) lockmode)
						break;	/* safe: we have a lock >= req level */
					elog(LOG, "deadlock risk: raising lock level"
						 " from %s to %s on object %u/%u/%u",
						 lockMethodTable->lockModeNames[i],
						 lockMethodTable->lockModeNames[lockmode],
						 lock->tag.locktag_field1, lock->tag.locktag_field2,
						 lock->tag.locktag_field3);
					break;
				}
			}
		}
#endif							/* CHECK_DEADLOCK_RISK */
	}

	/*
	 * lock->nRequested and lock->requested[] count the total number of
	 * requests, whether granted or waiting, so increment those immediately.
	 * The other counts don't increment till we get the lock.
	 */
	lock->nRequested++;
	lock->requested[lockmode]++;
	Assert((lock->nRequested > 0) && (lock->requested[lockmode] > 0));

	/*
	 * We shouldn't already hold the desired lock; else locallock table is
	 * broken.
	 */
	if (proclock->holdMask & LOCKBIT_ON(lockmode))
		elog(ERROR, "lock %s on object %u/%u/%u is already held",
			 lockMethodTable->lockModeNames[lockmode],
			 lock->tag.locktag_field1, lock->tag.locktag_field2,
			 lock->tag.locktag_field3);

	return proclock;
}

/*
 * Check and set/reset the flag that we hold the relation extension lock.
 *
 * It is callers responsibility that this function is called after
 * acquiring/releasing the relation extension lock.
 *
 * Pass acquired as true if lock is acquired, false otherwise.
 */
/* (中文)(仅断言构建)在"获取/释放关系扩展锁"之后由调用者调用,更新
 * IsRelationExtensionLockHeld 标志;对非扩展锁无操作。 */
static inline void
CheckAndSetLockHeld(LOCALLOCK *locallock, bool acquired)
{
#ifdef USE_ASSERT_CHECKING
	if (LOCALLOCK_LOCKTAG(*locallock) == LOCKTAG_RELATION_EXTEND)
		IsRelationExtensionLockHeld = acquired;
#endif
}

/*
 * Subroutine to free a locallock entry
 */
/*
 * RemoveLocalLock
 *      (中文)从本地锁表删除一个 LOCALLOCK 条目
 *
 * 【作用】彻底释放 LOCALLOCK:先把所有仍登记的所有者(LOCALLOCKOWNER)
 * 从对应资源所有者的锁集合里摘除(ResourceOwnerForgetLock),再释放
 * lockOwners 数组;若本条目还"扛着"强锁计数(holdsStrongLockCount),
 * 把对应分区的强锁计数减回并复位标志;最后从本地哈希表移除,并
 * 顺带复位关系扩展锁标志。
 *
 * 【参数】locallock —— 要删除的条目。
 * 【返回值】无。
 */
static void
RemoveLocalLock(LOCALLOCK *locallock)
{
	int			i;

	for (i = locallock->numLockOwners - 1; i >= 0; i--)
	{
		if (locallock->lockOwners[i].owner != NULL)
			ResourceOwnerForgetLock(locallock->lockOwners[i].owner, locallock);
	}
	locallock->numLockOwners = 0;
	if (locallock->lockOwners != NULL)
		pfree(locallock->lockOwners);
	locallock->lockOwners = NULL;

	if (locallock->holdsStrongLockCount)
	{
		uint32		fasthashcode;

		fasthashcode = FastPathStrongLockHashPartition(locallock->hashcode);

		SpinLockAcquire(&FastPathStrongRelationLocks->mutex);
		Assert(FastPathStrongRelationLocks->count[fasthashcode] > 0);
		FastPathStrongRelationLocks->count[fasthashcode]--;
		locallock->holdsStrongLockCount = false;
		SpinLockRelease(&FastPathStrongRelationLocks->mutex);
	}

	if (!hash_search(LockMethodLocalHash,
					 &(locallock->tag),
					 HASH_REMOVE, NULL))
		elog(WARNING, "locallock table corrupted");

	/*
	 * Indicate that the lock is released for certain types of locks
	 */
	CheckAndSetLockHeld(locallock, false);
}

/*
 * LockCheckConflicts -- test whether requested lock conflicts
 *		with those already granted
 *
 * Returns true if conflict, false if no conflict.
 *
 * NOTES:
 *		Here's what makes this complicated: one process's locks don't
 * conflict with one another, no matter what purpose they are held for
 * (eg, session and transaction locks do not conflict).  Nor do the locks
 * of one process in a lock group conflict with those of another process in
 * the same group.  So, we must subtract off these locks when determining
 * whether the requested new lock conflicts with those already held.
 */
/* (中文)测试请求的锁是否与"已授予的锁"冲突(返回 true 即冲突)。
 *
 * 复杂之处在于:同一进程(或同一锁组的成员)持有的锁互相不冲突
 * ——无论它们的用途(会话锁/事务锁)如何。因此要从冲突者里"减去"
 * 自己和自己锁组的持有:
 * 1. 快速路径:requested 的冲突掩码与 lock->grantMask 无交集 → 无冲突;
 * 2. 对每个冲突模式,统计"冲突的已授予数量",减去自己的持有
 *    (conflictsRemaining[]);
 * 3. 若自己不是锁组成员(无组锁),剩的冲突就是真冲突;
 * 4. 关系扩展锁例外:即使同组成员也冲突(扩展必须严格串行);
 * 5. 否则遍历该锁的 procLocks,把"同组其他成员持有的冲突模式"也
 *    减掉;减完无剩余 → 无冲突。
 * 调用前提:调用者已持有分区锁。 */
bool
LockCheckConflicts(LockMethod lockMethodTable,
				   LOCKMODE lockmode,
				   LOCK *lock,
				   PROCLOCK *proclock)
{
	int			numLockModes = lockMethodTable->numLockModes;	LOCKMASK	myLocks;
	int			conflictMask = lockMethodTable->conflictTab[lockmode];
	int			conflictsRemaining[MAX_LOCKMODES];
	int			totalConflictsRemaining = 0;
	dlist_iter	proclock_iter;
	int			i;

	/*
	 * first check for global conflicts: If no locks conflict with my request,
	 * then I get the lock.
	 *
	 * Checking for conflict: lock->grantMask represents the types of
	 * currently held locks.  conflictTable[lockmode] has a bit set for each
	 * type of lock that conflicts with request.   Bitwise compare tells if
	 * there is a conflict.
	 */
	if (!(conflictMask & lock->grantMask))
	{
		PROCLOCK_PRINT("LockCheckConflicts: no conflict", proclock);
		return false;
	}

	/*
	 * Rats.  Something conflicts.  But it could still be my own lock, or a
	 * lock held by another member of my locking group.  First, figure out how
	 * many conflicts remain after subtracting out any locks I hold myself.
	 */
	myLocks = proclock->holdMask;
	for (i = 1; i <= numLockModes; i++)
	{
		if ((conflictMask & LOCKBIT_ON(i)) == 0)
		{
			conflictsRemaining[i] = 0;
			continue;
		}
		conflictsRemaining[i] = lock->granted[i];
		if (myLocks & LOCKBIT_ON(i))
			--conflictsRemaining[i];
		totalConflictsRemaining += conflictsRemaining[i];
	}

	/* If no conflicts remain, we get the lock. */
	if (totalConflictsRemaining == 0)
	{
		PROCLOCK_PRINT("LockCheckConflicts: resolved (simple)", proclock);
		return false;
	}

	/* If no group locking, it's definitely a conflict. */
	if (proclock->groupLeader == MyProc && MyProc->lockGroupLeader == NULL)
	{
		Assert(proclock->tag.myProc == MyProc);
		PROCLOCK_PRINT("LockCheckConflicts: conflicting (simple)",
					   proclock);
		return true;
	}

	/*
	 * The relation extension lock conflict even between the group members.
	 */
	if (LOCK_LOCKTAG(*lock) == LOCKTAG_RELATION_EXTEND)
	{
		PROCLOCK_PRINT("LockCheckConflicts: conflicting (group)",
					   proclock);
		return true;
	}

	/*
	 * Locks held in conflicting modes by members of our own lock group are
	 * not real conflicts; we can subtract those out and see if we still have
	 * a conflict.  This is O(N) in the number of processes holding or
	 * awaiting locks on this object.  We could improve that by making the
	 * shared memory state more complex (and larger) but it doesn't seem worth
	 * it.
	 */
	dlist_foreach(proclock_iter, &lock->procLocks)
	{
		PROCLOCK   *otherproclock =
			dlist_container(PROCLOCK, lockLink, proclock_iter.cur);

		if (proclock != otherproclock &&
			proclock->groupLeader == otherproclock->groupLeader &&
			(otherproclock->holdMask & conflictMask) != 0)
		{
			int			intersectMask = otherproclock->holdMask & conflictMask;

			for (i = 1; i <= numLockModes; i++)
			{
				if ((intersectMask & LOCKBIT_ON(i)) != 0)
				{
					if (conflictsRemaining[i] <= 0)
						elog(PANIC, "proclocks held do not match lock");
					conflictsRemaining[i]--;
					totalConflictsRemaining--;
				}
			}

			if (totalConflictsRemaining == 0)
			{
				PROCLOCK_PRINT("LockCheckConflicts: resolved (group)",
							   proclock);
				return false;
			}
		}
	}

	/* Nope, it's a real conflict. */
	PROCLOCK_PRINT("LockCheckConflicts: conflicting (group)", proclock);
	return true;
}

/*
 * GrantLock -- update the lock and proclock data structures to show
 *		the lock request has been granted.
 *
 * NOTE: if proc was blocked, it also needs to be removed from the wait list
 * and have its waitLock/waitProcLock fields cleared.  That's not done here.
 *
 * NOTE: the lock grant also has to be recorded in the associated LOCALLOCK
 * table entry; but since we may be awaking some other process, we can't do
 * that here; it's done by GrantLockLocal, instead.
 */
/* (中文)在共享锁表里"授予"一把锁:更新 LOCK 的已授予计数/掩码与
 * PROCLOCK 的 holdMask。若该模式的授予数追平请求数,则等待掩码里
 * 去掉该模式(该模式的等待者都已被授予)。注意:被阻塞进程还要从
 * 等待队列摘除并清 waitLock(由调用者/唤醒方做);本地 LOCALLOCK 的
 * 计数由 GrantLockLocal 负责,不能在这里做(本函数可能在被唤醒的
 * 其他进程上下文中执行)。 */
void
GrantLock(LOCK *lock, PROCLOCK *proclock, LOCKMODE lockmode)
{
	lock->nGranted++;
	lock->granted[lockmode]++;
	lock->grantMask |= LOCKBIT_ON(lockmode);
	if (lock->granted[lockmode] == lock->requested[lockmode])
		lock->waitMask &= LOCKBIT_OFF(lockmode);
	proclock->holdMask |= LOCKBIT_ON(lockmode);
	LOCK_PRINT("GrantLock", lock, lockmode);
	Assert((lock->nGranted > 0) && (lock->granted[lockmode] > 0));
	Assert(lock->nGranted <= lock->nRequested);
}

/*
 * UnGrantLock -- opposite of GrantLock.
 *
 * Updates the lock and proclock data structures to show that the lock
 * is no longer held nor requested by the current holder.
 *
 * Returns true if there were any waiters waiting on the lock that
 * should now be woken up with ProcLockWakeup.
 */
/* (中文)GrantLock 的逆操作:撤销"当前持有者"对该锁的持有与请求。
 * 递减 LOCK 的 requested/granted 计数,该模式清零时从 grantMask
 * 去掉;PROCLOCK 的 holdMask 同步清除该位。
 *
 * 【返回值】true = 需要唤醒等待者(释放的模式与某个等待模式冲突,
 * 且 MVCC 时代不能只看"该模式还有无授予"——剩下的授予可能属于某个
 * 等待者自己,他不与自己冲突,故可能已被唤醒)。是否真正调用
 * ProcLockWakeup 由 CleanUpLock 决定。 */
static bool
UnGrantLock(LOCK *lock, LOCKMODE lockmode,
			PROCLOCK *proclock, LockMethod lockMethodTable)
{
	bool		wakeupNeeded = false;
	Assert((lock->nRequested > 0) && (lock->requested[lockmode] > 0));
	Assert((lock->nGranted > 0) && (lock->granted[lockmode] > 0));
	Assert(lock->nGranted <= lock->nRequested);

	/*
	 * fix the general lock stats
	 */
	lock->nRequested--;
	lock->requested[lockmode]--;
	lock->nGranted--;
	lock->granted[lockmode]--;

	if (lock->granted[lockmode] == 0)
	{
		/* change the conflict mask.  No more of this lock type. */
		lock->grantMask &= LOCKBIT_OFF(lockmode);
	}

	LOCK_PRINT("UnGrantLock: updated", lock, lockmode);

	/*
	 * We need only run ProcLockWakeup if the released lock conflicts with at
	 * least one of the lock types requested by waiter(s).  Otherwise whatever
	 * conflict made them wait must still exist.  NOTE: before MVCC, we could
	 * skip wakeup if lock->granted[lockmode] was still positive. But that's
	 * not true anymore, because the remaining granted locks might belong to
	 * some waiter, who could now be awakened because he doesn't conflict with
	 * his own locks.
	 */
	if (lockMethodTable->conflictTab[lockmode] & lock->waitMask)
		wakeupNeeded = true;

	/*
	 * Now fix the per-proclock state.
	 */
	proclock->holdMask &= LOCKBIT_OFF(lockmode);
	PROCLOCK_PRINT("UnGrantLock: updated", proclock);

	return wakeupNeeded;
}

/*
 * CleanUpLock -- clean up after releasing a lock.  We garbage-collect the
 * proclock and lock objects if possible, and call ProcLockWakeup if there
 * are remaining requests and the caller says it's OK.  (Normally, this
 * should be called after UnGrantLock, and wakeupNeeded is the result from
 * UnGrantLock.)
 *
 * The appropriate partition lock must be held at entry, and will be
 * held at exit.
 */
/* (中文)解锁后的收尾清理(通常在 UnGrantLock 之后调用,wakeupNeeded
 * 即其返回值):
 * - 若 PROCLOCK 不再持有任何模式(holdMask == 0):从锁的 procLocks
 *   链、进程的 myProcLocks 链摘除并从 PROCLOCK 哈希表删除;
 * - 若 LOCK 不再有任何请求(nRequested == 0):整把锁已无人问津,
 *   从 LOCK 哈希表删除(垃圾回收);
 * - 否则若需要唤醒:ProcLockWakeup 唤醒可被授予的等待者。
 * 调用者必须持有分区锁进出。 */
static void
CleanUpLock(LOCK *lock, PROCLOCK *proclock,
			LockMethod lockMethodTable, uint32 hashcode,
			bool wakeupNeeded)
{	/*
	 * If this was my last hold on this lock, delete my entry in the proclock
	 * table.
	 */
	if (proclock->holdMask == 0)
	{
		uint32		proclock_hashcode;

		PROCLOCK_PRINT("CleanUpLock: deleting", proclock);
		dlist_delete(&proclock->lockLink);
		dlist_delete(&proclock->procLink);
		proclock_hashcode = ProcLockHashCode(&proclock->tag, hashcode);
		if (!hash_search_with_hash_value(LockMethodProcLockHash,
										 &(proclock->tag),
										 proclock_hashcode,
										 HASH_REMOVE,
										 NULL))
			elog(PANIC, "proclock table corrupted");
	}

	if (lock->nRequested == 0)
	{
		/*
		 * The caller just released the last lock, so garbage-collect the lock
		 * object.
		 */
		LOCK_PRINT("CleanUpLock: deleting", lock, 0);
		Assert(dlist_is_empty(&lock->procLocks));
		if (!hash_search_with_hash_value(LockMethodLockHash,
										 &(lock->tag),
										 hashcode,
										 HASH_REMOVE,
										 NULL))
			elog(PANIC, "lock table corrupted");
	}
	else if (wakeupNeeded)
	{
		/* There are waiters on this lock, so wake them up. */
		ProcLockWakeup(lockMethodTable, lock);
	}
}

/*
 * GrantLockLocal -- update the locallock data structures to show
 *		the lock request has been granted.
 *
 * We expect that LockAcquire made sure there is room to add a new
 * ResourceOwner entry.
 */
/* (中文)在本地 LOCALLOCK 上登记"已获得":总计数 nLocks 加 1,并在
 * lockOwners 里给指定资源所有者(owner,可 NULL)的计数加 1;若是新
 * 所有者,登记到资源所有者(owner != NULL 时用 ResourceOwnerRememberLock
 * 反向登记,便于事务结束时统一释放),并更新关系扩展锁标志。 */
static void
GrantLockLocal(LOCALLOCK *locallock, ResourceOwner owner)
{
	LOCALLOCKOWNER *lockOwners = locallock->lockOwners;
	int			i;

	Assert(locallock->numLockOwners < locallock->maxLockOwners);
	/* Count the total */
	locallock->nLocks++;
	/* Count the per-owner lock */
	for (i = 0; i < locallock->numLockOwners; i++)
	{
		if (lockOwners[i].owner == owner)
		{
			lockOwners[i].nLocks++;
			return;
		}
	}
	lockOwners[i].owner = owner;
	lockOwners[i].nLocks = 1;
	locallock->numLockOwners++;
	if (owner != NULL)
		ResourceOwnerRememberLock(owner, locallock);

	/* Indicate that the lock is acquired for certain types of locks. */
	CheckAndSetLockHeld(locallock, true);
}

/*
 * BeginStrongLockAcquire - inhibit use of fastpath for a given LOCALLOCK,
 * and arrange for error cleanup if it fails
 */
/* (中文)"强锁获取"开始:把对应分区的强锁计数 +1(用自旋锁保护计数
 * 累加),并把 locallock 记入 StrongLockInProgress,以便后续步骤失败
 * 时由 AbortStrongLockAcquire 把计数退回。强锁计数非零会让 fast-path
 * 锁请求回退到共享锁表,避免死锁检测遗漏(见 FastPathStrongRelationLocks)。 */
static void
BeginStrongLockAcquire(LOCALLOCK *locallock, uint32 fasthashcode)
{
	Assert(StrongLockInProgress == NULL);
	Assert(locallock->holdsStrongLockCount == false);

	/*
	 * Adding to a memory location is not atomic, so we take a spinlock to
	 * ensure we don't collide with someone else trying to bump the count at
	 * the same time.
	 *
	 * XXX: It might be worth considering using an atomic fetch-and-add
	 * instruction here, on architectures where that is supported.
	 */

	SpinLockAcquire(&FastPathStrongRelationLocks->mutex);
	FastPathStrongRelationLocks->count[fasthashcode]++;
	locallock->holdsStrongLockCount = true;
	StrongLockInProgress = locallock;
	SpinLockRelease(&FastPathStrongRelationLocks->mutex);
}

/*
 * FinishStrongLockAcquire - cancel pending cleanup for a strong lock
 * acquisition once it's no longer needed
 */
/* (中文)强锁获取成功后的收尾:清除 StrongLockInProgress 挂起的清理
 * 需求(计数已实际生效,无需再退)。 */
static void
FinishStrongLockAcquire(void)
{
	StrongLockInProgress = NULL;
}

/*
 * AbortStrongLockAcquire - undo strong lock state changes performed by
 * BeginStrongLockAcquire.
 */
/* (中文)撤销 BeginStrongLockAcquire 的改动(强锁获取中途失败时调用):
 * 把分区强锁计数减回,复位标志与 StrongLockInProgress。 */
void
AbortStrongLockAcquire(void)
{
	uint32		fasthashcode;
	LOCALLOCK  *locallock = StrongLockInProgress;

	if (locallock == NULL)
		return;

	fasthashcode = FastPathStrongLockHashPartition(locallock->hashcode);
	Assert(locallock->holdsStrongLockCount == true);
	SpinLockAcquire(&FastPathStrongRelationLocks->mutex);
	Assert(FastPathStrongRelationLocks->count[fasthashcode] > 0);
	FastPathStrongRelationLocks->count[fasthashcode]--;
	locallock->holdsStrongLockCount = false;
	StrongLockInProgress = NULL;
	SpinLockRelease(&FastPathStrongRelationLocks->mutex);
}

/*
 * GrantAwaitedLock -- call GrantLockLocal for the lock we are doing
 *		WaitOnLock on.
 *
 * proc.c needs this for the case where we are booted off the lock by
 * timeout, but discover that someone granted us the lock anyway.
 *
 * We could just export GrantLockLocal, but that would require including
 * resowner.h in lock.h, which creates circularity.
 */
/* (中文)给"正在 WaitOnLock 的那把锁"补上本地授予登记。proc.c 在
 * 这种情况需要它:我们因超时被赶出等待(取消等待),却发现在此期间
 * 锁其实已被授予。不直接导出 GrantLockLocal,是为了避免 lock.h
 * 依赖 resowner.h(防止头文件循环)。 */
void
GrantAwaitedLock(void)
{
	GrantLockLocal(awaitedLock, awaitedOwner);
}

/*
 * GetAwaitedLock -- Return the lock we're currently doing WaitOnLock on.
 */
/* (中文)返回当前正在等待的那把锁(LOCALLOCK),供 proc.c 在唤醒/
 * 超时路径上使用。 */
LOCALLOCK *
GetAwaitedLock(void)
{
	return awaitedLock;
}

/*
 * ResetAwaitedLock -- Forget that we are waiting on a lock.
 */
/* (中文)清除"正在等待的锁"记录(等待结束后调用)。 */
void
ResetAwaitedLock(void)
{
	awaitedLock = NULL;
}

/*
 * MarkLockClear -- mark an acquired lock as "clear"
 *
 * This means that we know we have absorbed all sinval messages that other
 * sessions generated before we acquired this lock, and so we can confidently
 * assume we know about any catalog changes protected by this lock.
 */
/* (中文)把已获得的锁标记为"已清"(lockCleared = true):表示我们已知
 * 道加锁之前其他会话生成的全部 sinval 失效消息,能确信自己了解该锁
 * 保护的所有目录变更。此后同一事务再取同一把锁,LockAcquireExtended
 * 会返回 ALREADY_CLEAR,调用者可跳过重复的失效消息吸收。 */
void
MarkLockClear(LOCALLOCK *locallock)
{
	Assert(locallock->nLocks > 0);
	locallock->lockCleared = true;
}

/*
 * WaitOnLock -- wait to acquire a lock
 *
 * This is a wrapper around ProcSleep, with extra tracing and bookkeeping.
 */
/*
 * WaitOnLock
 *      (中文)等待获得一把锁(ProcSleep 的带簿记包装)
 *
 * 【作用】把本后端挂到锁的等待队列上睡眠,直到被授予/超时/取消/死锁
 * 而被唤醒。包装层负责:DTrace 探针、错误上下文回调(报错时打印
 * "waiting for X on Y")、进程标题加 "waiting" 后缀、记录
 * awaitedLock/awaitedOwner(供 LockErrorCleanup 在 cancel/die 时清理)。
 *
 * 【重要约定】ProcSleep 返回后(无论成败)绝不能再改共享锁表状态:
 * 锁授予方或 CheckDeadLock 已经完整设置好一切(可能发生"别人已授予
 * 我们、但取消信号先到"的竞态)。错误路径用 PG_TRY 只清理非关键
 * 状态(ps 显示),必要清理全在 LockErrorCleanup。
 *
 * 【参数】locallock —— 等待的本地锁条目;owner —— 其资源所有者。
 * 【返回值】ProcSleep 的结果(PROC_WAIT_STATUS_OK/ERROR/WAITING)。
 */
static ProcWaitStatus
WaitOnLock(LOCALLOCK *locallock, ResourceOwner owner)
{
	ProcWaitStatus result;
	ErrorContextCallback waiterrcontext;

	TRACE_POSTGRESQL_LOCK_WAIT_START(locallock->tag.lock.locktag_field1,
									 locallock->tag.lock.locktag_field2,
									 locallock->tag.lock.locktag_field3,
									 locallock->tag.lock.locktag_field4,
									 locallock->tag.lock.locktag_type,
									 locallock->tag.mode);

	/* Setup error traceback support for ereport() */
	waiterrcontext.callback = waitonlock_error_callback;
	waiterrcontext.arg = locallock;
	waiterrcontext.previous = error_context_stack;
	error_context_stack = &waiterrcontext;

	/* adjust the process title to indicate that it's waiting */
	set_ps_display_suffix("waiting");

	/*
	 * Record the fact that we are waiting for a lock, so that
	 * LockErrorCleanup will clean up if cancel/die happens.
	 */
	awaitedLock = locallock;
	awaitedOwner = owner;

	/*
	 * NOTE: Think not to put any shared-state cleanup after the call to
	 * ProcSleep, in either the normal or failure path.  The lock state must
	 * be fully set by the lock grantor, or by CheckDeadLock if we give up
	 * waiting for the lock.  This is necessary because of the possibility
	 * that a cancel/die interrupt will interrupt ProcSleep after someone else
	 * grants us the lock, but before we've noticed it. Hence, after granting,
	 * the locktable state must fully reflect the fact that we own the lock;
	 * we can't do additional work on return.
	 *
	 * We can and do use a PG_TRY block to try to clean up after failure, but
	 * this still has a major limitation: elog(FATAL) can occur while waiting
	 * (eg, a "die" interrupt), and then control won't come back here. So all
	 * cleanup of essential state should happen in LockErrorCleanup, not here.
	 * We can use PG_TRY to clear the "waiting" status flags, since doing that
	 * is unimportant if the process exits.
	 */
	PG_TRY();
	{
		result = ProcSleep(locallock);
	}
	PG_CATCH();
	{
		/* In this path, awaitedLock remains set until LockErrorCleanup */

		/* reset ps display to remove the suffix */
		set_ps_display_remove_suffix();

		/* and propagate the error */
		PG_RE_THROW();
	}
	PG_END_TRY();

	/*
	 * We no longer want LockErrorCleanup to do anything.
	 */
	awaitedLock = NULL;

	/* reset ps display to remove the suffix */
	set_ps_display_remove_suffix();

	error_context_stack = waiterrcontext.previous;

	TRACE_POSTGRESQL_LOCK_WAIT_DONE(locallock->tag.lock.locktag_field1,
									locallock->tag.lock.locktag_field2,
									locallock->tag.lock.locktag_field3,
									locallock->tag.lock.locktag_field4,
									locallock->tag.lock.locktag_type,
									locallock->tag.mode);

	return result;
}

/*
 * error context callback for failures in WaitOnLock
 *
 * We report which lock was being waited on, in the same style used in
 * deadlock reports.  This helps with lock timeout errors in particular.
 */
/* (中文)WaitOnLock 期间出错时的错误上下文回调:报告"正在等待哪个
 * 锁、什么模式"(与死锁报告的措辞风格一致,尤其利于锁超时错误的
 * 定位)。 */
static void
waitonlock_error_callback(void *arg)
{
	LOCALLOCK  *locallock = (LOCALLOCK *) arg;
	const LOCKTAG *tag = &locallock->tag.lock;
	LOCKMODE	mode = locallock->tag.mode;
	StringInfoData locktagbuf;

	initStringInfo(&locktagbuf);
	DescribeLockTag(&locktagbuf, tag);

	errcontext("waiting for %s on %s",
			   GetLockmodeName(tag->locktag_lockmethodid, mode),
			   locktagbuf.data);
}

/*
 * Remove a proc from the wait-queue it is on (caller must know it is on one).
 * This is only used when the proc has failed to get the lock, so we set its
 * waitStatus to PROC_WAIT_STATUS_ERROR.
 *
 * Appropriate partition lock must be held by caller.  Also, caller is
 * responsible for signaling the proc if needed.
 *
 * NB: this does not clean up any locallock object that may exist for the lock.
 */
void
RemoveFromWaitQueue(PGPROC *proc, uint32 hashcode)
{
	LOCK	   *waitLock = proc->waitLock;
	PROCLOCK   *proclock = proc->waitProcLock;
	LOCKMODE	lockmode = proc->waitLockMode;
	LOCKMETHODID lockmethodid = LOCK_LOCKMETHOD(*waitLock);

	/* Make sure proc is waiting */
	Assert(proc->waitStatus == PROC_WAIT_STATUS_WAITING);
	Assert(!dlist_node_is_detached(&proc->waitLink));
	Assert(waitLock);
	Assert(!dclist_is_empty(&waitLock->waitProcs));
	Assert(0 < lockmethodid && lockmethodid < lengthof(LockMethods));

	/*
	 * 此函数只在"进程没能拿到锁"(死锁牺牲者/被取消等待)时使用:
	 * 把它从等待队列摘除,把请求计数退回,清 waitStatus 为 ERROR
	 * (向进程传递失败信号),必要时立即删除 PROCLOCK(防止持有者随后
	 * 释放锁时计数归零却残留 proclock),最后 CleanUpLock 检查能否
	 * 唤醒其他等待者。调用者须持有分区锁,并负责给该进程发信号。
	 * 注意:不清理本地 LOCALLOCK(那由 LockErrorCleanup 负责)。
	 */
	/* Remove proc from lock's wait queue */
	dclist_delete_from_thoroughly(&waitLock->waitProcs, &proc->waitLink);

	/* Undo increments of request counts by waiting process */
	Assert(waitLock->nRequested > 0);
	Assert(waitLock->nRequested > proc->waitLock->nGranted);
	waitLock->nRequested--;
	Assert(waitLock->requested[lockmode] > 0);
	waitLock->requested[lockmode]--;
	/* don't forget to clear waitMask bit if appropriate */
	if (waitLock->granted[lockmode] == waitLock->requested[lockmode])
		waitLock->waitMask &= LOCKBIT_OFF(lockmode);

	/* Clean up the proc's own state, and pass it the ok/fail signal */
	proc->waitLock = NULL;
	proc->waitProcLock = NULL;
	proc->waitStatus = PROC_WAIT_STATUS_ERROR;

	/*
	 * Delete the proclock immediately if it represents no already-held locks.
	 * (This must happen now because if the owner of the lock decides to
	 * release it, and the requested/granted counts then go to zero,
	 * LockRelease expects there to be no remaining proclocks.) Then see if
	 * any other waiters for the lock can be woken up now.
	 */
	CleanUpLock(waitLock, proclock,
				LockMethods[lockmethodid], hashcode,
				true);
}

/*
 * LockRelease -- look up 'locktag' and release one 'lockmode' lock on it.
 *		Release a session lock if 'sessionLock' is true, else release a
 *		regular transaction lock.
 *
 * Side Effects: find any waiting processes that are now wakable,
 *		grant them their requested locks and awaken them.
 *		(We have to grant the lock here to avoid a race between
 *		the waking process and any new process to
 *		come along and request the lock.)
 */
/* (中文)释放 'locktag' 上的一把 'lockmode' 锁(sessionLock 决定释放
 * 会话锁还是事务锁)。
 *
 * 【流程】查本地 LOCALLOCK(sessionLock 时只找"无所有者"的那条;未
 * 持有则 WARNING 返回 false)→ 更新本地所有者计数与 nLocks → 若
 * nLocks 归零,进共享表:拿分区排他锁,UnGrantLock 撤权
 * (wakeupNeeded),CleanUpLock 做清理并唤醒等待者。若还有剩余本地
 * 持有,则只需改本地计数,不动共享表。
 *
 * 【设计思想】在共享表里"先授予再唤醒"(GrantLock 在唤醒者上下文)
 * 是为了避免竞态:被唤醒进程与新来的请求者同时争锁时,共享表状态
 * 已由唤醒方一次改好。
 *
 * 【参数】locktag —— 锁标签;lockmode —— 模式;
 * sessionLock —— true 释放会话级锁(false 释放事务级锁)。
 * 【返回值】true = 成功释放;false = 未持有该锁(已发 WARNING)。
 */
bool
LockRelease(const LOCKTAG *locktag, LOCKMODE lockmode, bool sessionLock)
{
	LOCKMETHODID lockmethodid = locktag->locktag_lockmethodid;
	LockMethod	lockMethodTable;
	LOCALLOCKTAG localtag;
	LOCALLOCK  *locallock;
	LOCK	   *lock;
	PROCLOCK   *proclock;
	LWLock	   *partitionLock;
	bool		wakeupNeeded;
	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);
	lockMethodTable = LockMethods[lockmethodid];
	if (lockmode <= 0 || lockmode > lockMethodTable->numLockModes)
		elog(ERROR, "unrecognized lock mode: %d", lockmode);

#ifdef LOCK_DEBUG
	if (LOCK_DEBUG_ENABLED(locktag))
		elog(LOG, "LockRelease: lock [%u,%u] %s",
			 locktag->locktag_field1, locktag->locktag_field2,
			 lockMethodTable->lockModeNames[lockmode]);
#endif

	/*
	 * Find the LOCALLOCK entry for this lock and lockmode
	 */
	MemSet(&localtag, 0, sizeof(localtag)); /* must clear padding */
	localtag.lock = *locktag;
	localtag.mode = lockmode;

	locallock = (LOCALLOCK *) hash_search(LockMethodLocalHash,
										  &localtag,
										  HASH_FIND, NULL);

	/*
	 * let the caller print its own error message, too. Do not ereport(ERROR).
	 */
	if (!locallock || locallock->nLocks <= 0)
	{
		elog(WARNING, "you don't own a lock of type %s",
			 lockMethodTable->lockModeNames[lockmode]);
		return false;
	}

	/*
	 * Decrease the count for the resource owner.
	 */
	{
		LOCALLOCKOWNER *lockOwners = locallock->lockOwners;
		ResourceOwner owner;
		int			i;

		/* Identify owner for lock */
		if (sessionLock)
			owner = NULL;
		else
			owner = CurrentResourceOwner;

		for (i = locallock->numLockOwners - 1; i >= 0; i--)
		{
			if (lockOwners[i].owner == owner)
			{
				Assert(lockOwners[i].nLocks > 0);
				if (--lockOwners[i].nLocks == 0)
				{
					if (owner != NULL)
						ResourceOwnerForgetLock(owner, locallock);
					/* compact out unused slot */
					locallock->numLockOwners--;
					if (i < locallock->numLockOwners)
						lockOwners[i] = lockOwners[locallock->numLockOwners];
				}
				break;
			}
		}
		if (i < 0)
		{
			/* don't release a lock belonging to another owner */
			elog(WARNING, "you don't own a lock of type %s",
				 lockMethodTable->lockModeNames[lockmode]);
			return false;
		}
	}

	/*
	 * Decrease the total local count.  If we're still holding the lock, we're
	 * done.
	 */
	locallock->nLocks--;

	if (locallock->nLocks > 0)
		return true;

	/*
	 * At this point we can no longer suppose we are clear of invalidation
	 * messages related to this lock.  Although we'll delete the LOCALLOCK
	 * object before any intentional return from this routine, it seems worth
	 * the trouble to explicitly reset lockCleared right now, just in case
	 * some error prevents us from deleting the LOCALLOCK.
	 */
	locallock->lockCleared = false;

	/* Attempt fast release of any lock eligible for the fast path. */
	if (EligibleForRelationFastPath(locktag, lockmode) &&
		FastPathLocalUseCounts[FAST_PATH_REL_GROUP(locktag->locktag_field2)] > 0)
	{
		bool		released;

		/*
		 * We might not find the lock here, even if we originally entered it
		 * here.  Another backend may have moved it to the main table.
		 */
		LWLockAcquire(&MyProc->fpInfoLock, LW_EXCLUSIVE);
		released = FastPathUnGrantRelationLock(locktag->locktag_field2,
											   lockmode);
		LWLockRelease(&MyProc->fpInfoLock);
		if (released)
		{
			RemoveLocalLock(locallock);
			return true;
		}
	}

	/*
	 * Otherwise we've got to mess with the shared lock table.
	 */
	partitionLock = LockHashPartitionLock(locallock->hashcode);

	LWLockAcquire(partitionLock, LW_EXCLUSIVE);

	/*
	 * Normally, we don't need to re-find the lock or proclock, since we kept
	 * their addresses in the locallock table, and they couldn't have been
	 * removed while we were holding a lock on them.  But it's possible that
	 * the lock was taken fast-path and has since been moved to the main hash
	 * table by another backend, in which case we will need to look up the
	 * objects here.  We assume the lock field is NULL if so.
	 */
	lock = locallock->lock;
	if (!lock)
	{
		PROCLOCKTAG proclocktag;

		Assert(EligibleForRelationFastPath(locktag, lockmode));
		lock = (LOCK *) hash_search_with_hash_value(LockMethodLockHash,
													locktag,
													locallock->hashcode,
													HASH_FIND,
													NULL);
		if (!lock)
			elog(ERROR, "failed to re-find shared lock object");
		locallock->lock = lock;

		proclocktag.myLock = lock;
		proclocktag.myProc = MyProc;
		locallock->proclock = (PROCLOCK *) hash_search(LockMethodProcLockHash,
													   &proclocktag,
													   HASH_FIND,
													   NULL);
		if (!locallock->proclock)
			elog(ERROR, "failed to re-find shared proclock object");
	}
	LOCK_PRINT("LockRelease: found", lock, lockmode);
	proclock = locallock->proclock;
	PROCLOCK_PRINT("LockRelease: found", proclock);

	/*
	 * Double-check that we are actually holding a lock of the type we want to
	 * release.
	 */
	if (!(proclock->holdMask & LOCKBIT_ON(lockmode)))
	{
		PROCLOCK_PRINT("LockRelease: WRONGTYPE", proclock);
		LWLockRelease(partitionLock);
		elog(WARNING, "you don't own a lock of type %s",
			 lockMethodTable->lockModeNames[lockmode]);
		RemoveLocalLock(locallock);
		return false;
	}

	/*
	 * Do the releasing.  CleanUpLock will waken any now-wakable waiters.
	 */
	wakeupNeeded = UnGrantLock(lock, lockmode, proclock, lockMethodTable);

	CleanUpLock(lock, proclock,
				lockMethodTable, locallock->hashcode,
				wakeupNeeded);

	LWLockRelease(partitionLock);

	RemoveLocalLock(locallock);
	return true;
}

/*
 * LockReleaseAll -- Release all locks of the specified lock method that
 *		are held by the current process.
 *
 * Well, not necessarily *all* locks.  The available behaviors are:
 *		allLocks == true: release all locks including session locks.
 *		allLocks == false: release all non-session locks.
 */
/*
 * LockReleaseAll
 *      (中文)释放当前进程持有的指定锁方法的全部锁
 *
 * 【作用】事务结束(或后端退出)时的总清理:释放本进程在
 * lockmethodid 锁方法下的所有锁。allLocks = true 时连会话级锁也释放,
 * false 时保留会话锁、只清事务锁。
 *
 * 【设计思想】
 * - 先清 fast-path 的本事务 VXID 锁(VirtualXactLockTableCleanup):自己
 *    VXID 上的锁只有顶层事务结束时才会释放,只能走到这里;
 * - 分两趟:先扫本地 LOCALLOCK 表(顺带清理 fast-path 位图),再扫
 *   进程的 myProcLocks 链处理共享 PROCLOCK——必须分开做,因为多个
 *   LOCALLOCK 可能指向同一个 PROCLOCK,直接删共享对象会留下悬垂
 *   指针;fast-path 锁在本地表扫描时一并清掉;
 * - 非 allLocks 时,把"无所有者(会话锁)"的条目降级保留:把 owner==NULL
 *   的条目挪到 0 位、撤销其余所有者的登记,使 LOCALLOCK 只剩会话锁;
 * - 共享侧:对仍由本地引用的 PROCLOCK 逐一 LockRefindAndRelease
 *   (按需递减强锁计数);随后把本地表里所有剩余条目删除(强制清空
 *   本地表,因为此后本地表状态不再可信)。
 *
 * 【参数】lockmethodid —— 要清理的锁方法;allLocks —— 是否含会话锁。
 * 【返回值】无。
 */
void
LockReleaseAll(LOCKMETHODID lockmethodid, bool allLocks)
{
	HASH_SEQ_STATUS status;
	LockMethod	lockMethodTable;
	int			i,
				numLockModes;
	LOCALLOCK  *locallock;
	LOCK	   *lock;
	int			partition;
	bool		have_fast_path_lwlock = false;

	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);
	lockMethodTable = LockMethods[lockmethodid];

#ifdef LOCK_DEBUG
	if (*(lockMethodTable->trace_flag))
		elog(LOG, "LockReleaseAll: lockmethod=%d", lockmethodid);
#endif

	/*
	 * Get rid of our fast-path VXID lock, if appropriate.  Note that this is
	 * the only way that the lock we hold on our own VXID can ever get
	 * released: it is always and only released when a toplevel transaction
	 * ends.
	 */
	if (lockmethodid == DEFAULT_LOCKMETHOD)
		VirtualXactLockTableCleanup();

	numLockModes = lockMethodTable->numLockModes;

	/*
	 * First we run through the locallock table and get rid of unwanted
	 * entries, then we scan the process's proclocks and get rid of those. We
	 * do this separately because we may have multiple locallock entries
	 * pointing to the same proclock, and we daren't end up with any dangling
	 * pointers.  Fast-path locks are cleaned up during the locallock table
	 * scan, though.
	 */
	hash_seq_init(&status, LockMethodLocalHash);

	while ((locallock = (LOCALLOCK *) hash_seq_search(&status)) != NULL)
	{
		/*
		 * If the LOCALLOCK entry is unused, something must've gone wrong
		 * while trying to acquire this lock.  Just forget the local entry.
		 */
		if (locallock->nLocks == 0)
		{
			RemoveLocalLock(locallock);
			continue;
		}

		/* Ignore items that are not of the lockmethod to be removed */
		if (LOCALLOCK_LOCKMETHOD(*locallock) != lockmethodid)
			continue;

		/*
		 * If we are asked to release all locks, we can just zap the entry.
		 * Otherwise, must scan to see if there are session locks. We assume
		 * there is at most one lockOwners entry for session locks.
		 */
		if (!allLocks)
		{
			LOCALLOCKOWNER *lockOwners = locallock->lockOwners;

			/* If session lock is above array position 0, move it down to 0 */
			for (i = 0; i < locallock->numLockOwners; i++)
			{
				if (lockOwners[i].owner == NULL)
					lockOwners[0] = lockOwners[i];
				else
					ResourceOwnerForgetLock(lockOwners[i].owner, locallock);
			}

			if (locallock->numLockOwners > 0 &&
				lockOwners[0].owner == NULL &&
				lockOwners[0].nLocks > 0)
			{
				/* Fix the locallock to show just the session locks */
				locallock->nLocks = lockOwners[0].nLocks;
				locallock->numLockOwners = 1;
				/* We aren't deleting this locallock, so done */
				continue;
			}
			else
				locallock->numLockOwners = 0;
		}

#ifdef USE_ASSERT_CHECKING

		/*
		 * Tuple locks are currently held only for short durations within a
		 * transaction. Check that we didn't forget to release one.
		 */
		if (LOCALLOCK_LOCKTAG(*locallock) == LOCKTAG_TUPLE && !allLocks)
			elog(WARNING, "tuple lock held at commit");
#endif

		/*
		 * If the lock or proclock pointers are NULL, this lock was taken via
		 * the relation fast-path (and is not known to have been transferred).
		 */
		if (locallock->proclock == NULL || locallock->lock == NULL)
		{
			LOCKMODE	lockmode = locallock->tag.mode;
			Oid			relid;

			/* Verify that a fast-path lock is what we've got. */
			if (!EligibleForRelationFastPath(&locallock->tag.lock, lockmode))
				elog(PANIC, "locallock table corrupted");

			/*
			 * If we don't currently hold the LWLock that protects our
			 * fast-path data structures, we must acquire it before attempting
			 * to release the lock via the fast-path.  We will continue to
			 * hold the LWLock until we're done scanning the locallock table,
			 * unless we hit a transferred fast-path lock.  (XXX is this
			 * really such a good idea?  There could be a lot of entries ...)
			 */
			if (!have_fast_path_lwlock)
			{
				LWLockAcquire(&MyProc->fpInfoLock, LW_EXCLUSIVE);
				have_fast_path_lwlock = true;
			}

			/* Attempt fast-path release. */
			relid = locallock->tag.lock.locktag_field2;
			if (FastPathUnGrantRelationLock(relid, lockmode))
			{
				RemoveLocalLock(locallock);
				continue;
			}

			/*
			 * Our lock, originally taken via the fast path, has been
			 * transferred to the main lock table.  That's going to require
			 * some extra work, so release our fast-path lock before starting.
			 */
			LWLockRelease(&MyProc->fpInfoLock);
			have_fast_path_lwlock = false;

			/*
			 * Now dump the lock.  We haven't got a pointer to the LOCK or
			 * PROCLOCK in this case, so we have to handle this a bit
			 * differently than a normal lock release.  Unfortunately, this
			 * requires an extra LWLock acquire-and-release cycle on the
			 * partitionLock, but hopefully it shouldn't happen often.
			 */
			LockRefindAndRelease(lockMethodTable, MyProc,
								 &locallock->tag.lock, lockmode, false);
			RemoveLocalLock(locallock);
			continue;
		}

		/* Mark the proclock to show we need to release this lockmode */
		if (locallock->nLocks > 0)
			locallock->proclock->releaseMask |= LOCKBIT_ON(locallock->tag.mode);

		/* And remove the locallock hashtable entry */
		RemoveLocalLock(locallock);
	}

	/* Done with the fast-path data structures */
	if (have_fast_path_lwlock)
		LWLockRelease(&MyProc->fpInfoLock);

	/*
	 * Now, scan each lock partition separately.
	 */
	for (partition = 0; partition < NUM_LOCK_PARTITIONS; partition++)
	{
		LWLock	   *partitionLock;
		dlist_head *procLocks = &MyProc->myProcLocks[partition];
		dlist_mutable_iter proclock_iter;

		partitionLock = LockHashPartitionLockByIndex(partition);

		/*
		 * If the proclock list for this partition is empty, we can skip
		 * acquiring the partition lock.  This optimization is trickier than
		 * it looks, because another backend could be in process of adding
		 * something to our proclock list due to promoting one of our
		 * fast-path locks.  However, any such lock must be one that we
		 * decided not to delete above, so it's okay to skip it again now;
		 * we'd just decide not to delete it again.  We must, however, be
		 * careful to re-fetch the list header once we've acquired the
		 * partition lock, to be sure we have a valid, up-to-date pointer.
		 * (There is probably no significant risk if pointer fetch/store is
		 * atomic, but we don't wish to assume that.)
		 *
		 * XXX This argument assumes that the locallock table correctly
		 * represents all of our fast-path locks.  While allLocks mode
		 * guarantees to clean up all of our normal locks regardless of the
		 * locallock situation, we lose that guarantee for fast-path locks.
		 * This is not ideal.
		 */
		if (dlist_is_empty(procLocks))
			continue;			/* needn't examine this partition */

		LWLockAcquire(partitionLock, LW_EXCLUSIVE);

		dlist_foreach_modify(proclock_iter, procLocks)
		{
			PROCLOCK   *proclock = dlist_container(PROCLOCK, procLink, proclock_iter.cur);
			bool		wakeupNeeded = false;

			Assert(proclock->tag.myProc == MyProc);

			lock = proclock->tag.myLock;

			/* Ignore items that are not of the lockmethod to be removed */
			if (LOCK_LOCKMETHOD(*lock) != lockmethodid)
				continue;

			/*
			 * In allLocks mode, force release of all locks even if locallock
			 * table had problems
			 */
			if (allLocks)
				proclock->releaseMask = proclock->holdMask;
			else
				Assert((proclock->releaseMask & ~proclock->holdMask) == 0);

			/*
			 * Ignore items that have nothing to be released, unless they have
			 * holdMask == 0 and are therefore recyclable
			 */
			if (proclock->releaseMask == 0 && proclock->holdMask != 0)
				continue;

			PROCLOCK_PRINT("LockReleaseAll", proclock);
			LOCK_PRINT("LockReleaseAll", lock, 0);
			Assert(lock->nRequested >= 0);
			Assert(lock->nGranted >= 0);
			Assert(lock->nGranted <= lock->nRequested);
			Assert((proclock->holdMask & ~lock->grantMask) == 0);

			/*
			 * Release the previously-marked lock modes
			 */
			for (i = 1; i <= numLockModes; i++)
			{
				if (proclock->releaseMask & LOCKBIT_ON(i))
					wakeupNeeded |= UnGrantLock(lock, i, proclock,
												lockMethodTable);
			}
			Assert((lock->nRequested >= 0) && (lock->nGranted >= 0));
			Assert(lock->nGranted <= lock->nRequested);
			LOCK_PRINT("LockReleaseAll: updated", lock, 0);

			proclock->releaseMask = 0;

			/* CleanUpLock will wake up waiters if needed. */
			CleanUpLock(lock, proclock,
						lockMethodTable,
						LockTagHashCode(&lock->tag),
						wakeupNeeded);
		}						/* loop over PROCLOCKs within this partition */

		LWLockRelease(partitionLock);
	}							/* loop over partitions */

#ifdef LOCK_DEBUG
	if (*(lockMethodTable->trace_flag))
		elog(LOG, "LockReleaseAll done");
#endif
}

/*
 * LockReleaseSession -- Release all session locks of the specified lock method
 *		that are held by the current process.
 */
/* (中文)释放当前进程持有的指定锁方法的全部"会话级"锁(逐个 LOCALLOCK
 * 调 ReleaseLockIfHeld(locallock, true))。 */
void
LockReleaseSession(LOCKMETHODID lockmethodid)
{
	HASH_SEQ_STATUS status;
	LOCALLOCK  *locallock;

	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);

	hash_seq_init(&status, LockMethodLocalHash);

	while ((locallock = (LOCALLOCK *) hash_seq_search(&status)) != NULL)
	{
		/* Ignore items that are not of the specified lock method */
		if (LOCALLOCK_LOCKMETHOD(*locallock) != lockmethodid)
			continue;

		ReleaseLockIfHeld(locallock, true);
	}
}

/*
 * LockReleaseCurrentOwner
 *		Release all locks belonging to CurrentResourceOwner
 *
 * If the caller knows what those locks are, it can pass them as an array.
 * That speeds up the call significantly, when a lot of locks are held.
 * Otherwise, pass NULL for locallocks, and we'll traverse through our hash
 * table to find them.
 */
/*
 * LockReleaseCurrentOwner
 *      (中文)释放属于 CurrentResourceOwner 的全部锁
 *
 * 【作用】资源所有者结束时(subtransaction abort 等)回调:撤销当前
 * 资源所有者名下所有锁。调用者可传已知的锁数组加速;传 NULL 则
 * 遍历本地锁表。每个候选锁交给 ReleaseLockIfHeld(locallock, false)。
 *
 * 【参数】locallocks —— 已知的锁列表(NULL = 遍历哈希表);
 * nlocks —— 列表长度。
 * 【返回值】无。
 */
void
LockReleaseCurrentOwner(LOCALLOCK **locallocks, int nlocks)
{
	if (locallocks == NULL)
	{
		HASH_SEQ_STATUS status;
		LOCALLOCK  *locallock;

		hash_seq_init(&status, LockMethodLocalHash);

		while ((locallock = (LOCALLOCK *) hash_seq_search(&status)) != NULL)
			ReleaseLockIfHeld(locallock, false);
	}
	else
	{
		int			i;

		for (i = nlocks - 1; i >= 0; i--)
			ReleaseLockIfHeld(locallocks[i], false);
	}
}

/*
 * ReleaseLockIfHeld
 *		Release any session-level locks on this lockable object if sessionLock
 *		is true; else, release any locks held by CurrentResourceOwner.
 *
 * It is tempting to pass this a ResourceOwner pointer (or NULL for session
 * locks), but without refactoring LockRelease() we cannot support releasing
 * locks belonging to resource owners other than CurrentResourceOwner.
 * If we were to refactor, it'd be a good idea to fix it so we don't have to
 * do a hashtable lookup of the locallock, too.  However, currently this
 * function isn't used heavily enough to justify refactoring for its
 * convenience.
 */
/* (中文)释放该 LOCALLOCK 上属于目标所有者(sessionLock → 会话锁
 * owner=NULL;否则 CurrentResourceOwner)的锁:
 * - 若目标所有者只是部分持有(nLocks 少于总数):只扣减计数、撤销
 *   该所有者的登记,共享锁表不动;
 * - 若全部持有:把计数收成 1 后调用一次 LockRelease 真正释放(避免
 *   多次递减的重复开销)。
 * 注意:无法支持"任意指定资源所有者",只能按当前所有者释放(见
 * 英文注释的取舍说明)。 */
static void
ReleaseLockIfHeld(LOCALLOCK *locallock, bool sessionLock)
{
	ResourceOwner owner;
	LOCALLOCKOWNER *lockOwners;
	int			i;
	/* Identify owner for lock (must match LockRelease!) */
	if (sessionLock)
		owner = NULL;
	else
		owner = CurrentResourceOwner;

	/* Scan to see if there are any locks belonging to the target owner */
	lockOwners = locallock->lockOwners;
	for (i = locallock->numLockOwners - 1; i >= 0; i--)
	{
		if (lockOwners[i].owner == owner)
		{
			Assert(lockOwners[i].nLocks > 0);
			if (lockOwners[i].nLocks < locallock->nLocks)
			{
				/*
				 * We will still hold this lock after forgetting this
				 * ResourceOwner.
				 */
				locallock->nLocks -= lockOwners[i].nLocks;
				/* compact out unused slot */
				locallock->numLockOwners--;
				if (owner != NULL)
					ResourceOwnerForgetLock(owner, locallock);
				if (i < locallock->numLockOwners)
					lockOwners[i] = lockOwners[locallock->numLockOwners];
			}
			else
			{
				Assert(lockOwners[i].nLocks == locallock->nLocks);
				/* We want to call LockRelease just once */
				lockOwners[i].nLocks = 1;
				locallock->nLocks = 1;
				if (!LockRelease(&locallock->tag.lock,
								 locallock->tag.mode,
								 sessionLock))
					elog(WARNING, "ReleaseLockIfHeld: failed??");
			}
			break;
		}
	}
}

/*
 * LockReassignCurrentOwner
 *		Reassign all locks belonging to CurrentResourceOwner to belong
 *		to its parent resource owner.
 *
 * If the caller knows what those locks are, it can pass them as an array.
 * That speeds up the call significantly, when a lot of locks are held
 * (e.g pg_dump with a large schema).  Otherwise, pass NULL for locallocks,
 * and we'll traverse through our hash table to find them.
 */
/*
 * LockReassignCurrentOwner
 *      (中文)把 CurrentResourceOwner 名下所有锁改归其父资源所有者
 *
 * 【作用】子事务成功提交时,它的锁要"上缴"给父事务(父资源所有者),
 * 而不是释放。逐个把当前所有者的锁交给 LockReassignOwner 迁移。
 *
 * 【参数】locallocks —— 已知锁列表(NULL = 遍历本地表);nlocks —— 长度。
 * 【返回值】无。
 */
void
LockReassignCurrentOwner(LOCALLOCK **locallocks, int nlocks)
{
	ResourceOwner parent = ResourceOwnerGetParent(CurrentResourceOwner);

	Assert(parent != NULL);

	if (locallocks == NULL)
	{
		HASH_SEQ_STATUS status;
		LOCALLOCK  *locallock;

		hash_seq_init(&status, LockMethodLocalHash);

		while ((locallock = (LOCALLOCK *) hash_seq_search(&status)) != NULL)
			LockReassignOwner(locallock, parent);
	}
	else
	{
		int			i;

		for (i = nlocks - 1; i >= 0; i--)
			LockReassignOwner(locallocks[i], parent);
	}
}

/*
 * Subroutine of LockReassignCurrentOwner. Reassigns a given lock belonging to
 * CurrentResourceOwner to its parent.
 */
/* (中文)LockReassignCurrentOwner 的子例程:把指定 LOCALLOCK 上属于
 * CurrentResourceOwner 的份额转给 parent。父所有者尚无条目 → 直接
 * 改 owner 字段并反向登记;已有条目 → 计数合并并压缩数组;最后从
 * 当前所有者的登记里摘除。 */
static void
LockReassignOwner(LOCALLOCK *locallock, ResourceOwner parent)
{
	LOCALLOCKOWNER *lockOwners;
	int			i;
	int			ic = -1;
	int			ip = -1;

	/*
	 * Scan to see if there are any locks belonging to current owner or its
	 * parent
	 */
	lockOwners = locallock->lockOwners;
	for (i = locallock->numLockOwners - 1; i >= 0; i--)
	{
		if (lockOwners[i].owner == CurrentResourceOwner)
			ic = i;
		else if (lockOwners[i].owner == parent)
			ip = i;
	}

	if (ic < 0)
		return;					/* no current locks */

	if (ip < 0)
	{
		/* Parent has no slot, so just give it the child's slot */
		lockOwners[ic].owner = parent;
		ResourceOwnerRememberLock(parent, locallock);
	}
	else
	{
		/* Merge child's count with parent's */
		lockOwners[ip].nLocks += lockOwners[ic].nLocks;
		/* compact out unused slot */
		locallock->numLockOwners--;
		if (ic < locallock->numLockOwners)
			lockOwners[ic] = lockOwners[locallock->numLockOwners];
	}
	ResourceOwnerForgetLock(CurrentResourceOwner, locallock);
}

/*
 * FastPathGrantRelationLock
 *		Grant lock using per-backend fast-path array, if there is space.
 */
/* (中文)用本后端 fast-path 数组授予锁(前提是数组有空间,且没有强锁
 * 竞争者——调用者已检查):在关系所属组内先找"该 relid 已有条目"
 * 则直接置新模式的位;否则找空槽登记。返回是否成功。调用者须持
 * MyProc->fpInfoLock。 */
static bool
FastPathGrantRelationLock(Oid relid, LOCKMODE lockmode)
{
	uint32		i;
	uint32		unused_slot = FastPathLockSlotsPerBackend();

	/* fast-path group the lock belongs to */
	uint32		group = FAST_PATH_REL_GROUP(relid);

	/* Scan for existing entry for this relid, remembering empty slot. */
	for (i = 0; i < FP_LOCK_SLOTS_PER_GROUP; i++)
	{
		/* index into the whole per-backend array */
		uint32		f = FAST_PATH_SLOT(group, i);

		if (FAST_PATH_GET_BITS(MyProc, f) == 0)
			unused_slot = f;
		else if (MyProc->fpRelId[f] == relid)
		{
			Assert(!FAST_PATH_CHECK_LOCKMODE(MyProc, f, lockmode));
			FAST_PATH_SET_LOCKMODE(MyProc, f, lockmode);
			return true;
		}
	}

	/* If no existing entry, use any empty slot. */
	if (unused_slot < FastPathLockSlotsPerBackend())
	{
		MyProc->fpRelId[unused_slot] = relid;
		FAST_PATH_SET_LOCKMODE(MyProc, unused_slot, lockmode);
		++FastPathLocalUseCounts[group];
		return true;
	}

	/* No existing entry, and no empty slot. */
	return false;
}

/*
 * FastPathUnGrantRelationLock
 *		Release fast-path lock, if present.  Update backend-private local
 *		use count, while we're at it.
 */
/* (中文)释放 fast-path 锁(若存在):清除对应槽位上的模式位,顺带把
 * 本组的使用计数 FastPathLocalUseCounts 重新统计一遍(先清零再按
 * 剩余非空槽累加——调用者持 fpInfoLock,故这里可以直接写)。
 * 返回是否真的清除了某个槽。 */
static bool
FastPathUnGrantRelationLock(Oid relid, LOCKMODE lockmode)
{
	uint32		i;
	bool		result = false;

	/* fast-path group the lock belongs to */
	uint32		group = FAST_PATH_REL_GROUP(relid);

	FastPathLocalUseCounts[group] = 0;
	for (i = 0; i < FP_LOCK_SLOTS_PER_GROUP; i++)
	{
		/* index into the whole per-backend array */
		uint32		f = FAST_PATH_SLOT(group, i);

		if (MyProc->fpRelId[f] == relid
			&& FAST_PATH_CHECK_LOCKMODE(MyProc, f, lockmode))
		{
			Assert(!result);
			FAST_PATH_CLEAR_LOCKMODE(MyProc, f, lockmode);
			result = true;
			/* we continue iterating so as to update FastPathLocalUseCount */
		}
		if (FAST_PATH_GET_BITS(MyProc, f) != 0)
			++FastPathLocalUseCounts[group];
	}
	return result;
}

/*
 * FastPathTransferRelationLocks
 *		Transfer locks matching the given lock tag from per-backend fast-path
 *		arrays to the shared hash table.
 *
 * Returns true if successful, false if ran out of shared memory.
 */
/* (中文)把"所有后端 fast-path 数组里与给定锁标签匹配的锁"搬进共享
 * 锁表。加"强锁"时调用,确保死锁检测器能看到这些原本不可见的锁。
 *
 * 【流程】遍历 ProcGlobal->allProcs 里每个 PGPROC(注意 prepared
 * 事务不在其中,但它们的 fast-path 锁已被搬入共享表,所以不漏):
 * 持其 fpInfoLock,跳过数据库不匹配或组内无锁的进程;把匹配 relid
 * 的槽位逐一在共享表里 SetupLockInTable + GrantLock,再清掉 fast-path
 * 位。内存不足时返回 false(调用方按强锁失败处理)。
 *
 * 【参数】lockMethodTable —— 锁方法表;locktag —— 目标锁标签;
 * hashcode —— 其哈希码。
 * 【返回值】true = 成功;false = 共享内存不足。 */
static bool
FastPathTransferRelationLocks(LockMethod lockMethodTable, const LOCKTAG *locktag,
							  uint32 hashcode)
{
	LWLock	   *partitionLock = LockHashPartitionLock(hashcode);
	Oid			relid = locktag->locktag_field2;
	uint32		i;

	/* fast-path group the lock belongs to */
	uint32		group = FAST_PATH_REL_GROUP(relid);

	/*
	 * Every PGPROC that can potentially hold a fast-path lock is present in
	 * ProcGlobal->allProcs.  Prepared transactions are not, but any
	 * outstanding fast-path locks held by prepared transactions are
	 * transferred to the main lock table.
	 */
	for (i = 0; i < ProcGlobal->allProcCount; i++)
	{
		PGPROC	   *proc = GetPGProcByNumber(i);
		uint32		j;

		LWLockAcquire(&proc->fpInfoLock, LW_EXCLUSIVE);

		/*
		 * If the target backend isn't referencing the same database as the
		 * lock, then we needn't examine the individual relation IDs at all;
		 * none of them can be relevant.
		 *
		 * proc->databaseId is set at backend startup time and never changes
		 * thereafter, so it might be safe to perform this test before
		 * acquiring &proc->fpInfoLock.  In particular, it's certainly safe to
		 * assume that if the target backend holds any fast-path locks, it
		 * must have performed a memory-fencing operation (in particular, an
		 * LWLock acquisition) since setting proc->databaseId.  However, it's
		 * less clear that our backend is certain to have performed a memory
		 * fencing operation since the other backend set proc->databaseId.  So
		 * for now, we test it after acquiring the LWLock just to be safe.
		 *
		 * Also skip groups without any registered fast-path locks.
		 */
		if (proc->databaseId != locktag->locktag_field1 ||
			proc->fpLockBits[group] == 0)
		{
			LWLockRelease(&proc->fpInfoLock);
			continue;
		}

		for (j = 0; j < FP_LOCK_SLOTS_PER_GROUP; j++)
		{
			uint32		lockmode;

			/* index into the whole per-backend array */
			uint32		f = FAST_PATH_SLOT(group, j);

			/* Look for an allocated slot matching the given relid. */
			if (relid != proc->fpRelId[f] || FAST_PATH_GET_BITS(proc, f) == 0)
				continue;

			/* Find or create lock object. */
			LWLockAcquire(partitionLock, LW_EXCLUSIVE);
			for (lockmode = FAST_PATH_LOCKNUMBER_OFFSET;
				 lockmode < FAST_PATH_LOCKNUMBER_OFFSET + FAST_PATH_BITS_PER_SLOT;
				 ++lockmode)
			{
				PROCLOCK   *proclock;

				if (!FAST_PATH_CHECK_LOCKMODE(proc, f, lockmode))
					continue;
				proclock = SetupLockInTable(lockMethodTable, proc, locktag,
											hashcode, lockmode);
				if (!proclock)
				{
					LWLockRelease(partitionLock);
					LWLockRelease(&proc->fpInfoLock);
					return false;
				}
				GrantLock(proclock->tag.myLock, proclock, lockmode);
				FAST_PATH_CLEAR_LOCKMODE(proc, f, lockmode);
			}
			LWLockRelease(partitionLock);

			/* No need to examine remaining slots. */
			break;
		}
		LWLockRelease(&proc->fpInfoLock);
	}
	return true;
}

/*
 * FastPathGetRelationLockEntry
 *		Return the PROCLOCK for a lock originally taken via the fast-path,
 *		transferring it to the primary lock table if necessary.
 *
 * Note: caller takes care of updating the locallock object.
 */
/* (中文)为"原先通过 fast-path 取得的锁"取回 PROCLOCK:若它还在
 * fast-path 里,则把它搬进共享锁表(建 PROCLOCK + GrantLock);若已被
 * 别的后端搬过,则直接查共享表返回。供 GetLockConflicts 等需要
 * "把 fast-path 锁视作共享锁"的场景使用。调用者负责更新 locallock。 */
static PROCLOCK *
FastPathGetRelationLockEntry(LOCALLOCK *locallock)
{
	LockMethod	lockMethodTable = LockMethods[DEFAULT_LOCKMETHOD];
	LOCKTAG    *locktag = &locallock->tag.lock;
	PROCLOCK   *proclock = NULL;
	LWLock	   *partitionLock = LockHashPartitionLock(locallock->hashcode);
	Oid			relid = locktag->locktag_field2;
	uint32		i,
				group;

	/* fast-path group the lock belongs to */
	group = FAST_PATH_REL_GROUP(relid);

	LWLockAcquire(&MyProc->fpInfoLock, LW_EXCLUSIVE);

	for (i = 0; i < FP_LOCK_SLOTS_PER_GROUP; i++)
	{
		uint32		lockmode;

		/* index into the whole per-backend array */
		uint32		f = FAST_PATH_SLOT(group, i);

		/* Look for an allocated slot matching the given relid. */
		if (relid != MyProc->fpRelId[f] || FAST_PATH_GET_BITS(MyProc, f) == 0)
			continue;

		/* If we don't have a lock of the given mode, forget it! */
		lockmode = locallock->tag.mode;
		if (!FAST_PATH_CHECK_LOCKMODE(MyProc, f, lockmode))
			break;

		/* Find or create lock object. */
		LWLockAcquire(partitionLock, LW_EXCLUSIVE);

		proclock = SetupLockInTable(lockMethodTable, MyProc, locktag,
									locallock->hashcode, lockmode);
		if (!proclock)
		{
			LWLockRelease(partitionLock);
			LWLockRelease(&MyProc->fpInfoLock);
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of shared memory"),
					 errhint("You might need to increase \"%s\".", "max_locks_per_transaction")));
		}
		GrantLock(proclock->tag.myLock, proclock, lockmode);
		FAST_PATH_CLEAR_LOCKMODE(MyProc, f, lockmode);

		LWLockRelease(partitionLock);

		/* No need to examine remaining slots. */
		break;
	}

	LWLockRelease(&MyProc->fpInfoLock);

	/* Lock may have already been transferred by some other backend. */
	if (proclock == NULL)
	{
		LOCK	   *lock;
		PROCLOCKTAG proclocktag;
		uint32		proclock_hashcode;

		LWLockAcquire(partitionLock, LW_SHARED);

		lock = (LOCK *) hash_search_with_hash_value(LockMethodLockHash,
													locktag,
													locallock->hashcode,
													HASH_FIND,
													NULL);
		if (!lock)
			elog(ERROR, "failed to re-find shared lock object");

		proclocktag.myLock = lock;
		proclocktag.myProc = MyProc;

		proclock_hashcode = ProcLockHashCode(&proclocktag, locallock->hashcode);
		proclock = (PROCLOCK *)
			hash_search_with_hash_value(LockMethodProcLockHash,
										&proclocktag,
										proclock_hashcode,
										HASH_FIND,
										NULL);
		if (!proclock)
			elog(ERROR, "failed to re-find shared proclock object");
		LWLockRelease(partitionLock);
	}

	return proclock;
}

/*
 * GetLockConflicts
 *		Get an array of VirtualTransactionIds of xacts currently holding locks
 *		that would conflict with the specified lock/lockmode.
 *		xacts merely awaiting such a lock are NOT reported.
 *
 * The result array is palloc'd and is terminated with an invalid VXID.
 * *countp, if not null, is updated to the number of items set.
 *
 * Of course, the result could be out of date by the time it's returned, so
 * use of this function has to be thought about carefully.  Similarly, a
 * PGPROC with no "lxid" will be considered non-conflicting regardless of any
 * lock it holds.  Existing callers don't care about a locker after that
 * locker's pg_xact updates complete.  CommitTransaction() clears "lxid" after
 * pg_xact updates and before releasing locks.
 *
 * Note we never include the current xact's vxid in the result array,
 * since an xact never blocks itself.
 */
/* (中文)返回"当前持有与该锁冲突的锁"的全部事务的 VXID 数组(只等
 * 待、未持有的不计;结果以 InvalidVXID 结尾,countp 非空时给出个数)。
 *
 * 【设计思想】供 WaitForLockers(DROP 对象前等所有冲突者)使用:
 * - 若请求模式可能冲突于 fast-path 锁(ConflictsWithRelationFastPath),
 *   先遍历所有 PGPROC 检查其 fast-path 数组(按组查位图;注意
 *   结果随时可能过时——新锁可能在返回后被别的进程取走);
 * - 再查共享锁表:对每个 PROCLOCK,若其 holdMask 与冲突掩码有交集,
 *   且该进程不是本事务,把它的 VXID 记下(已提交/回滚的进程
 *   lxid 无效则跳过,见英文注释的时机说明);
 * - 同一进程对同把锁的多条 PROCLOCK 只记一次(VXID 唯一性去重,
 *   靠"同 vxid 连续收集"的遍历顺序);
 * - 热备(Hot Standby)下用 TopMemoryContext 一次性分配静态缓冲,
 *   避免恢复进程里反复 palloc。
 *
 * 【参数】locktag —— 锁标签;lockmode —— 关心的模式;
 * countp —— 可选输出:冲突者个数。
 * 【返回值】palloc 的 VXID 数组,InvalidVXID 结尾。
 */
VirtualTransactionId *
GetLockConflicts(const LOCKTAG *locktag, LOCKMODE lockmode, int *countp)
{
	static VirtualTransactionId *vxids;
	LOCKMETHODID lockmethodid = locktag->locktag_lockmethodid;
	LockMethod	lockMethodTable;
	LOCK	   *lock;
	LOCKMASK	conflictMask;
	dlist_iter	proclock_iter;
	PROCLOCK   *proclock;
	uint32		hashcode;
	LWLock	   *partitionLock;
	int			count = 0;
	int			fast_count = 0;

	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);
	lockMethodTable = LockMethods[lockmethodid];
	if (lockmode <= 0 || lockmode > lockMethodTable->numLockModes)
		elog(ERROR, "unrecognized lock mode: %d", lockmode);

	/*
	 * Allocate memory to store results, and fill with InvalidVXID.  We only
	 * need enough space for MaxBackends + max_prepared_xacts + a terminator.
	 * InHotStandby allocate once in TopMemoryContext.
	 */
	if (InHotStandby)
	{
		if (vxids == NULL)
			vxids = (VirtualTransactionId *)
				MemoryContextAlloc(TopMemoryContext,
								   sizeof(VirtualTransactionId) *
								   (MaxBackends + max_prepared_xacts + 1));
	}
	else
		vxids = palloc0_array(VirtualTransactionId, (MaxBackends + max_prepared_xacts + 1));

	/* Compute hash code and partition lock, and look up conflicting modes. */
	hashcode = LockTagHashCode(locktag);
	partitionLock = LockHashPartitionLock(hashcode);
	conflictMask = lockMethodTable->conflictTab[lockmode];

	/*
	 * Fast path locks might not have been entered in the primary lock table.
	 * If the lock we're dealing with could conflict with such a lock, we must
	 * examine each backend's fast-path array for conflicts.
	 */
	if (ConflictsWithRelationFastPath(locktag, lockmode))
	{
		Oid			relid = locktag->locktag_field2;
		VirtualTransactionId vxid;

		/* fast-path group the lock belongs to */
		uint32		group = FAST_PATH_REL_GROUP(relid);

		/*
		 * Iterate over relevant PGPROCs.  Anything held by a prepared
		 * transaction will have been transferred to the primary lock table,
		 * so we need not worry about those.  This is all a bit fuzzy, because
		 * new locks could be taken after we've visited a particular
		 * partition, but the callers had better be prepared to deal with that
		 * anyway, since the locks could equally well be taken between the
		 * time we return the value and the time the caller does something
		 * with it.
		 */
		for (uint32 i = 0; i < ProcGlobal->allProcCount; i++)
		{
			PGPROC	   *proc = GetPGProcByNumber(i);
			uint32		j;

			/* A backend never blocks itself */
			if (proc == MyProc)
				continue;

			LWLockAcquire(&proc->fpInfoLock, LW_SHARED);

			/*
			 * If the target backend isn't referencing the same database as
			 * the lock, then we needn't examine the individual relation IDs
			 * at all; none of them can be relevant.
			 *
			 * See FastPathTransferRelationLocks() for discussion of why we do
			 * this test after acquiring the lock.
			 *
			 * Also skip groups without any registered fast-path locks.
			 */
			if (proc->databaseId != locktag->locktag_field1 ||
				proc->fpLockBits[group] == 0)
			{
				LWLockRelease(&proc->fpInfoLock);
				continue;
			}

			for (j = 0; j < FP_LOCK_SLOTS_PER_GROUP; j++)
			{
				uint32		lockmask;

				/* index into the whole per-backend array */
				uint32		f = FAST_PATH_SLOT(group, j);

				/* Look for an allocated slot matching the given relid. */
				if (relid != proc->fpRelId[f])
					continue;
				lockmask = FAST_PATH_GET_BITS(proc, f);
				if (!lockmask)
					continue;
				lockmask <<= FAST_PATH_LOCKNUMBER_OFFSET;

				/*
				 * There can only be one entry per relation, so if we found it
				 * and it doesn't conflict, we can skip the rest of the slots.
				 */
				if ((lockmask & conflictMask) == 0)
					break;

				/* Conflict! */
				GET_VXID_FROM_PGPROC(vxid, *proc);

				if (VirtualTransactionIdIsValid(vxid))
					vxids[count++] = vxid;
				/* else, xact already committed or aborted */

				/* No need to examine remaining slots. */
				break;
			}

			LWLockRelease(&proc->fpInfoLock);
		}
	}

	/* Remember how many fast-path conflicts we found. */
	fast_count = count;

	/*
	 * Look up the lock object matching the tag.
	 */
	LWLockAcquire(partitionLock, LW_SHARED);

	lock = (LOCK *) hash_search_with_hash_value(LockMethodLockHash,
												locktag,
												hashcode,
												HASH_FIND,
												NULL);
	if (!lock)
	{
		/*
		 * If the lock object doesn't exist, there is nothing holding a lock
		 * on this lockable object.
		 */
		LWLockRelease(partitionLock);
		vxids[count].procNumber = INVALID_PROC_NUMBER;
		vxids[count].localTransactionId = InvalidLocalTransactionId;
		if (countp)
			*countp = count;
		return vxids;
	}

	/*
	 * Examine each existing holder (or awaiter) of the lock.
	 */
	dlist_foreach(proclock_iter, &lock->procLocks)
	{
		proclock = dlist_container(PROCLOCK, lockLink, proclock_iter.cur);

		if (conflictMask & proclock->holdMask)
		{
			PGPROC	   *proc = proclock->tag.myProc;

			/* A backend never blocks itself */
			if (proc != MyProc)
			{
				VirtualTransactionId vxid;

				GET_VXID_FROM_PGPROC(vxid, *proc);

				if (VirtualTransactionIdIsValid(vxid))
				{
					int			i;

					/* Avoid duplicate entries. */
					for (i = 0; i < fast_count; ++i)
						if (VirtualTransactionIdEquals(vxids[i], vxid))
							break;
					if (i >= fast_count)
						vxids[count++] = vxid;
				}
				/* else, xact already committed or aborted */
			}
		}
	}

	LWLockRelease(partitionLock);

	if (count > MaxBackends + max_prepared_xacts)	/* should never happen */
		elog(PANIC, "too many conflicting locks found");

	vxids[count].procNumber = INVALID_PROC_NUMBER;
	vxids[count].localTransactionId = InvalidLocalTransactionId;
	if (countp)
		*countp = count;
	return vxids;
}

/*
 * Find a lock in the shared lock table and release it.  It is the caller's
 * responsibility to verify that this is a sane thing to do.  (For example, it
 * would be bad to release a lock here if there might still be a LOCALLOCK
 * object with pointers to it.)
 *
 * We currently use this in two situations: first, to release locks held by
 * prepared transactions on commit (see lock_twophase_postcommit); and second,
 * to release locks taken via the fast-path, transferred to the main hash
 * table, and then released (see LockReleaseAll).
 */
/* (中文)在共享锁表里"重新定位"并释放一把锁。两种使用场景(见英文
 * 注释):① 2PC 提交时释放 prepared 事务的锁(lock_twophase_postcommit);
 * ② LockReleaseAll 里释放"曾走 fast-path、后被搬入共享表"的锁。
 *
 * 【流程】按哈希重查 LOCK/PROCLOCK(必须在),校验持有后 UnGrantLock
 * + CleanUpLock,释放分区锁;若 decrement_strong_lock_count 且这把锁
 * 属于"可能与 fast-path 冲突"的类型(仅 2PC 需要),把强锁计数减回。
 *
 * 【注意】调用者必须保证"这么做是安全的"(例如没有 LOCALLLOCK 还
 * 指着这把锁)。 */
static void
LockRefindAndRelease(LockMethod lockMethodTable, PGPROC *proc,
					 LOCKTAG *locktag, LOCKMODE lockmode,
					 bool decrement_strong_lock_count)
{
	LOCK	   *lock;
	PROCLOCK   *proclock;
	PROCLOCKTAG proclocktag;
	uint32		hashcode;
	uint32		proclock_hashcode;
	LWLock	   *partitionLock;
	bool		wakeupNeeded;

	hashcode = LockTagHashCode(locktag);
	partitionLock = LockHashPartitionLock(hashcode);

	LWLockAcquire(partitionLock, LW_EXCLUSIVE);

	/*
	 * Re-find the lock object (it had better be there).
	 */
	lock = (LOCK *) hash_search_with_hash_value(LockMethodLockHash,
												locktag,
												hashcode,
												HASH_FIND,
												NULL);
	if (!lock)
		elog(PANIC, "failed to re-find shared lock object");

	/*
	 * Re-find the proclock object (ditto).
	 */
	proclocktag.myLock = lock;
	proclocktag.myProc = proc;

	proclock_hashcode = ProcLockHashCode(&proclocktag, hashcode);

	proclock = (PROCLOCK *) hash_search_with_hash_value(LockMethodProcLockHash,
														&proclocktag,
														proclock_hashcode,
														HASH_FIND,
														NULL);
	if (!proclock)
		elog(PANIC, "failed to re-find shared proclock object");

	/*
	 * Double-check that we are actually holding a lock of the type we want to
	 * release.
	 */
	if (!(proclock->holdMask & LOCKBIT_ON(lockmode)))
	{
		PROCLOCK_PRINT("lock_twophase_postcommit: WRONGTYPE", proclock);
		LWLockRelease(partitionLock);
		elog(WARNING, "you don't own a lock of type %s",
			 lockMethodTable->lockModeNames[lockmode]);
		return;
	}

	/*
	 * Do the releasing.  CleanUpLock will waken any now-wakable waiters.
	 */
	wakeupNeeded = UnGrantLock(lock, lockmode, proclock, lockMethodTable);

	CleanUpLock(lock, proclock,
				lockMethodTable, hashcode,
				wakeupNeeded);

	LWLockRelease(partitionLock);

	/*
	 * Decrement strong lock count.  This logic is needed only for 2PC.
	 */
	if (decrement_strong_lock_count
		&& ConflictsWithRelationFastPath(locktag, lockmode))
	{
		uint32		fasthashcode = FastPathStrongLockHashPartition(hashcode);

		SpinLockAcquire(&FastPathStrongRelationLocks->mutex);
		Assert(FastPathStrongRelationLocks->count[fasthashcode] > 0);
		FastPathStrongRelationLocks->count[fasthashcode]--;
		SpinLockRelease(&FastPathStrongRelationLocks->mutex);
	}
}

/*
 * CheckForSessionAndXactLocks
 *		Check to see if transaction holds both session-level and xact-level
 *		locks on the same object; if so, throw an error.
 *
 * If we have both session- and transaction-level locks on the same object,
 * PREPARE TRANSACTION must fail.  This should never happen with regular
 * locks, since we only take those at session level in some special operations
 * like VACUUM.  It's possible to hit this with advisory locks, though.
 *
 * It would be nice if we could keep the session hold and give away the
 * transactional hold to the prepared xact.  However, that would require two
 * PROCLOCK objects, and we cannot be sure that another PROCLOCK will be
 * available when it comes time for PostPrepare_Locks to do the deed.
 * So for now, we error out while we can still do so safely.
 *
 * Since the LOCALLOCK table stores a separate entry for each lockmode,
 * we can't implement this check by examining LOCALLOCK entries in isolation.
 * We must build a transient hashtable that is indexed by locktag only.
 */
/* (中文)检查本事务是否对同一对象同时持有"会话级"与"事务级"锁;
 * 若两者皆有,PREPARE TRANSACTION 必须报错(见英文注释:理想方案是
 * 把事务级部分让给 prepared 事务、保住会话部分,但那需要两个
 * PROCLOCK,无法保证 PREPARE 时刻还有空闲的 PROCLOCK 可用,所以
 * 保守地直接报错)。
 *
 * 【设计思想】LOCALLOCK 按 (LOCKTAG, mode) 拆条存储,无法在单条里
 * 判断"同一对象两种级别都有",因此临时建一张"只按 LOCKTAG 为键"的
 * 本地哈希表,合并同对象的会话/事务标志;一旦发现违规立即抛错。
 * VXID 锁被忽略(不随 prepared 事务存在)。 */
static void
CheckForSessionAndXactLocks(void)
{
	typedef struct
	{
		LOCKTAG		lock;		/* identifies the lockable object */
		bool		sessLock;	/* is any lockmode held at session level? */
		bool		xactLock;	/* is any lockmode held at xact level? */
	} PerLockTagEntry;

	HASHCTL		hash_ctl;
	HTAB	   *lockhtab;
	HASH_SEQ_STATUS status;
	LOCALLOCK  *locallock;

	/* Create a local hash table keyed by LOCKTAG only */
	hash_ctl.keysize = sizeof(LOCKTAG);
	hash_ctl.entrysize = sizeof(PerLockTagEntry);
	hash_ctl.hcxt = CurrentMemoryContext;

	lockhtab = hash_create("CheckForSessionAndXactLocks table",
						   256, /* arbitrary initial size */
						   &hash_ctl,
						   HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);

	/* Scan local lock table to find entries for each LOCKTAG */
	hash_seq_init(&status, LockMethodLocalHash);

	while ((locallock = (LOCALLOCK *) hash_seq_search(&status)) != NULL)
	{
		LOCALLOCKOWNER *lockOwners = locallock->lockOwners;
		PerLockTagEntry *hentry;
		bool		found;
		int			i;

		/*
		 * Ignore VXID locks.  We don't want those to be held by prepared
		 * transactions, since they aren't meaningful after a restart.
		 */
		if (locallock->tag.lock.locktag_type == LOCKTAG_VIRTUALTRANSACTION)
			continue;

		/* Ignore it if we don't actually hold the lock */
		if (locallock->nLocks <= 0)
			continue;

		/* Otherwise, find or make an entry in lockhtab */
		hentry = (PerLockTagEntry *) hash_search(lockhtab,
												 &locallock->tag.lock,
												 HASH_ENTER, &found);
		if (!found)				/* initialize, if newly created */
			hentry->sessLock = hentry->xactLock = false;

		/* Scan to see if we hold lock at session or xact level or both */
		for (i = locallock->numLockOwners - 1; i >= 0; i--)
		{
			if (lockOwners[i].owner == NULL)
				hentry->sessLock = true;
			else
				hentry->xactLock = true;
		}

		/*
		 * We can throw error immediately when we see both types of locks; no
		 * need to wait around to see if there are more violations.
		 */
		if (hentry->sessLock && hentry->xactLock)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("cannot PREPARE while holding both session-level and transaction-level locks on the same object")));
	}

	/* Success, so clean up */
	hash_destroy(lockhtab);
}

/*
 * AtPrepare_Locks
 *		Do the preparatory work for a PREPARE: make 2PC state file records
 *		for all locks currently held.
 *
 * Session-level locks are ignored, as are VXID locks.
 *
 * For the most part, we don't need to touch shared memory for this ---
 * all the necessary state information is in the locallock table.
 * Fast-path locks are an exception, however: we move any such locks to
 * the main table before allowing PREPARE TRANSACTION to succeed.
 */
/* (中文)PREPARE 的准备工作:为当前持有的所有锁写 2PC 状态文件记录。
 *
 * 【流程】先 CheckForSessionAndXactLocks 排除违规;再遍历 LOCALLOCK:
 * 跳过 VXID 锁与只持会话级的锁(它们不随 prepared 事务走);对每个
 * 事务级锁:若它还停在 fast-path(proclock == NULL),通过
 * FastPathGetRelationLockEntry 搬进共享表(2PC 期间必须让所有锁可见);
 * 把 holdsStrongLockCount 置 false,使强锁计数被"转让"给 prepared
 * 事务继续承担;最后把 (locktag, lockmode) 写进 2PC 状态文件
 * (register_2pc_record),恢复时靠它重建共享锁。
 *
 * 【参数】无。【返回值】无。
 */
void
AtPrepare_Locks(void)
{
	HASH_SEQ_STATUS status;
	LOCALLOCK  *locallock;

	/* First, verify there aren't locks of both xact and session level */
	CheckForSessionAndXactLocks();

	/* Now do the per-locallock cleanup work */
	hash_seq_init(&status, LockMethodLocalHash);

	while ((locallock = (LOCALLOCK *) hash_seq_search(&status)) != NULL)
	{
		TwoPhaseLockRecord record;
		LOCALLOCKOWNER *lockOwners = locallock->lockOwners;
		bool		haveSessionLock;
		bool		haveXactLock;
		int			i;

		/*
		 * Ignore VXID locks.  We don't want those to be held by prepared
		 * transactions, since they aren't meaningful after a restart.
		 */
		if (locallock->tag.lock.locktag_type == LOCKTAG_VIRTUALTRANSACTION)
			continue;

		/* Ignore it if we don't actually hold the lock */
		if (locallock->nLocks <= 0)
			continue;

		/* Scan to see whether we hold it at session or transaction level */
		haveSessionLock = haveXactLock = false;
		for (i = locallock->numLockOwners - 1; i >= 0; i--)
		{
			if (lockOwners[i].owner == NULL)
				haveSessionLock = true;
			else
				haveXactLock = true;
		}

		/* Ignore it if we have only session lock */
		if (!haveXactLock)
			continue;

		/* This can't happen, because we already checked it */
		if (haveSessionLock)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("cannot PREPARE while holding both session-level and transaction-level locks on the same object")));

		/*
		 * If the local lock was taken via the fast-path, we need to move it
		 * to the primary lock table, or just get a pointer to the existing
		 * primary lock table entry if by chance it's already been
		 * transferred.
		 */
		if (locallock->proclock == NULL)
		{
			locallock->proclock = FastPathGetRelationLockEntry(locallock);
			locallock->lock = locallock->proclock->tag.myLock;
		}

		/*
		 * Arrange to not release any strong lock count held by this lock
		 * entry.  We must retain the count until the prepared transaction is
		 * committed or rolled back.
		 */
		locallock->holdsStrongLockCount = false;

		/*
		 * Create a 2PC record.
		 */
		memcpy(&(record.locktag), &(locallock->tag.lock), sizeof(LOCKTAG));
		record.lockmode = locallock->tag.mode;

		RegisterTwoPhaseRecord(TWOPHASE_RM_LOCK_ID, 0,
							   &record, sizeof(TwoPhaseLockRecord));
	}
}

/*
 * PostPrepare_Locks
 *		Clean up after successful PREPARE
 *
 * Here, we want to transfer ownership of our locks to a dummy PGPROC
 * that's now associated with the prepared transaction, and we want to
 * clean out the corresponding entries in the LOCALLOCK table.
 *
 * Note: by removing the LOCALLOCK entries, we are leaving dangling
 * pointers in the transaction's resource owner.  This is OK at the
 * moment since resowner.c doesn't try to free locks retail at a toplevel
 * transaction commit or abort.  We could alternatively zero out nLocks
 * and leave the LOCALLOCK entries to be garbage-collected by LockReleaseAll,
 * but that probably costs more cycles.
 */
/* (中文)PREPARE 成功后的收尾:把我们的锁"过户"给 prepared 事务的
 * 虚拟 PGPROC,并清空对应的 LOCALLOCK 条目。
 *
 * 【流程】两趟(理由与 LockReleaseAll 相同:避免多 LOCALLOCK 指向同
 * 一 PROCLOCK 造成悬垂):
 * 1. 遍历本地表:对每个事务级锁,在 PROCLOCK 的 releaseMask 上标记
 *    "待过户的模式",然后 RemoveLocalLock(注意:此时 resowner 里会
 *    留下悬垂指针——顶层事务提交/回滚时 resowner 不逐把释放锁,
 *    所以安全);
 * 2. 按分区遍历 MyProc 的 proclocks:对 releaseMask 非零者,把
 *    PROCLOCK 从我们的 procLink 链摘下,用 hash_update_hash_key 把
 *    (myProc → newproc) 换键重挂(直接改 tag.myProc 会把哈希链弄乱;
 *    换键不换分区,故已持有的分区锁足够),更新 groupLeader,挂到
 *    newproc 的链上。
 * 全程处于临界区(START/END_CRIT_SECTION),任何错误都是大麻烦
 * (PANIC 级别)。 */
void
PostPrepare_Locks(FullTransactionId fxid)
{
	PGPROC	   *newproc = TwoPhaseGetDummyProc(fxid, false);
	HASH_SEQ_STATUS status;
	LOCALLOCK  *locallock;
	LOCK	   *lock;
	PROCLOCK   *proclock;
	PROCLOCKTAG proclocktag;
	int			partition;

	/* Can't prepare a lock group follower. */
	Assert(MyProc->lockGroupLeader == NULL ||
		   MyProc->lockGroupLeader == MyProc);

	/* This is a critical section: any error means big trouble */
	START_CRIT_SECTION();

	/*
	 * First we run through the locallock table and get rid of unwanted
	 * entries, then we scan the process's proclocks and transfer them to the
	 * target proc.
	 *
	 * We do this separately because we may have multiple locallock entries
	 * pointing to the same proclock, and we daren't end up with any dangling
	 * pointers.
	 */
	hash_seq_init(&status, LockMethodLocalHash);

	while ((locallock = (LOCALLOCK *) hash_seq_search(&status)) != NULL)
	{
		LOCALLOCKOWNER *lockOwners = locallock->lockOwners;
		bool		haveSessionLock;
		bool		haveXactLock;
		int			i;

		if (locallock->proclock == NULL || locallock->lock == NULL)
		{
			/*
			 * We must've run out of shared memory while trying to set up this
			 * lock.  Just forget the local entry.
			 */
			Assert(locallock->nLocks == 0);
			RemoveLocalLock(locallock);
			continue;
		}

		/* Ignore VXID locks */
		if (locallock->tag.lock.locktag_type == LOCKTAG_VIRTUALTRANSACTION)
			continue;

		/* Scan to see whether we hold it at session or transaction level */
		haveSessionLock = haveXactLock = false;
		for (i = locallock->numLockOwners - 1; i >= 0; i--)
		{
			if (lockOwners[i].owner == NULL)
				haveSessionLock = true;
			else
				haveXactLock = true;
		}

		/* Ignore it if we have only session lock */
		if (!haveXactLock)
			continue;

		/* This can't happen, because we already checked it */
		if (haveSessionLock)
			ereport(PANIC,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("cannot PREPARE while holding both session-level and transaction-level locks on the same object")));

		/* Mark the proclock to show we need to release this lockmode */
		if (locallock->nLocks > 0)
			locallock->proclock->releaseMask |= LOCKBIT_ON(locallock->tag.mode);

		/* And remove the locallock hashtable entry */
		RemoveLocalLock(locallock);
	}

	/*
	 * Now, scan each lock partition separately.
	 */
	for (partition = 0; partition < NUM_LOCK_PARTITIONS; partition++)
	{
		LWLock	   *partitionLock;
		dlist_head *procLocks = &(MyProc->myProcLocks[partition]);
		dlist_mutable_iter proclock_iter;

		partitionLock = LockHashPartitionLockByIndex(partition);

		/*
		 * If the proclock list for this partition is empty, we can skip
		 * acquiring the partition lock.  This optimization is safer than the
		 * situation in LockReleaseAll, because we got rid of any fast-path
		 * locks during AtPrepare_Locks, so there cannot be any case where
		 * another backend is adding something to our lists now.  For safety,
		 * though, we code this the same way as in LockReleaseAll.
		 */
		if (dlist_is_empty(procLocks))
			continue;			/* needn't examine this partition */

		LWLockAcquire(partitionLock, LW_EXCLUSIVE);

		dlist_foreach_modify(proclock_iter, procLocks)
		{
			proclock = dlist_container(PROCLOCK, procLink, proclock_iter.cur);

			Assert(proclock->tag.myProc == MyProc);

			lock = proclock->tag.myLock;

			/* Ignore VXID locks */
			if (lock->tag.locktag_type == LOCKTAG_VIRTUALTRANSACTION)
				continue;

			PROCLOCK_PRINT("PostPrepare_Locks", proclock);
			LOCK_PRINT("PostPrepare_Locks", lock, 0);
			Assert(lock->nRequested >= 0);
			Assert(lock->nGranted >= 0);
			Assert(lock->nGranted <= lock->nRequested);
			Assert((proclock->holdMask & ~lock->grantMask) == 0);

			/* Ignore it if nothing to release (must be a session lock) */
			if (proclock->releaseMask == 0)
				continue;

			/* Else we should be releasing all locks */
			if (proclock->releaseMask != proclock->holdMask)
				elog(PANIC, "we seem to have dropped a bit somewhere");

			/*
			 * We cannot simply modify proclock->tag.myProc to reassign
			 * ownership of the lock, because that's part of the hash key and
			 * the proclock would then be in the wrong hash chain.  Instead
			 * use hash_update_hash_key.  (We used to create a new hash entry,
			 * but that risks out-of-memory failure if other processes are
			 * busy making proclocks too.)	We must unlink the proclock from
			 * our procLink chain and put it into the new proc's chain, too.
			 *
			 * Note: the updated proclock hash key will still belong to the
			 * same hash partition, cf proclock_hash().  So the partition lock
			 * we already hold is sufficient for this.
			 */
			dlist_delete(&proclock->procLink);

			/*
			 * Create the new hash key for the proclock.
			 */
			proclocktag.myLock = lock;
			proclocktag.myProc = newproc;

			/*
			 * Update groupLeader pointer to point to the new proc.  (We'd
			 * better not be a member of somebody else's lock group!)
			 */
			Assert(proclock->groupLeader == proclock->tag.myProc);
			proclock->groupLeader = newproc;

			/*
			 * Update the proclock.  We should not find any existing entry for
			 * the same hash key, since there can be only one entry for any
			 * given lock with my own proc.
			 */
			if (!hash_update_hash_key(LockMethodProcLockHash,
									  proclock,
									  &proclocktag))
				elog(PANIC, "duplicate entry found while reassigning a prepared transaction's locks");

			/* Re-link into the new proc's proclock list */
			dlist_push_tail(&newproc->myProcLocks[partition], &proclock->procLink);

			PROCLOCK_PRINT("PostPrepare_Locks: updated", proclock);
		}						/* loop over PROCLOCKs within this partition */

		LWLockRelease(partitionLock);
	}							/* loop over partitions */

	END_CRIT_SECTION();
}


/*
 * GetLockStatusData - Return a summary of the lock manager's internal
 * status, for use in a user-level reporting function.
 *
 * The return data consists of an array of LockInstanceData objects,
 * which are a lightly abstracted version of the PROCLOCK data structures,
 * i.e. there is one entry for each unique lock and interested PGPROC.
 * It is the caller's responsibility to match up related items (such as
 * references to the same lockable object or PGPROC) if wanted.
 *
 * The design goal is to hold the LWLocks for as short a time as possible;
 * thus, this function simply makes a copy of the necessary data and releases
 * the locks, allowing the caller to contemplate and format the data for as
 * long as it pleases.
 */
/* (中文)汇总锁管理器的内部状态,供用户级报告函数(pg_locks 视图、
 * pg_stat_activity 的锁等待字段)使用。
 *
 * 【设计思想】返回 LockInstanceData 数组(每"进程 × 锁"一条,即
 * PROCLOCK 的轻量抽象);设计目标是最短时间持 LWLock:函数只把
 * 必要数据拷贝进 palloc 的内存就释放锁,调用方爱怎么格式化都行。
 *
 * 【内容】先逐进程遍历 fast-path 数组(每次只持一个 fpInfoLock,
 * 快照可能略不一致——但能进 fast-path 的锁本就不参与冲突,无妨;
 * 顺带把 fast-path VXID 锁也记一条);再对主锁表:持所有分区锁(共享
 * 模式,尽量保证一致性)后,遍历 LOCK 表与 PROCLOCK 表,把每把锁的
 * 持有者/等待者、锁模式、等待开始时间(等待者的 waitStart)等全部
 * 拷贝;最后按快照里"等待者"记录补上持有的等待边
 * (GetBlockedProcs 相关,用于构造阻塞链)。
 *
 * 【参数】无。
 * 【返回值】LockData 结构(内含 palloc 的 LockInstanceData 数组)。
 */
LockData *
GetLockStatusData(void)
{
	LockData   *data;
	PROCLOCK   *proclock;
	HASH_SEQ_STATUS seqstat;
	int			els;
	int			el;

	data = palloc_object(LockData);

	/* Guess how much space we'll need. */
	els = MaxBackends;
	el = 0;
	data->locks = palloc_array(LockInstanceData, els);

	/*
	 * First, we iterate through the per-backend fast-path arrays, locking
	 * them one at a time.  This might produce an inconsistent picture of the
	 * system state, but taking all of those LWLocks at the same time seems
	 * impractical (in particular, note MAX_SIMUL_LWLOCKS).  It shouldn't
	 * matter too much, because none of these locks can be involved in lock
	 * conflicts anyway - anything that might must be present in the main lock
	 * table.  (For the same reason, we don't sweat about making leaderPid
	 * completely valid.  We cannot safely dereference another backend's
	 * lockGroupLeader field without holding all lock partition locks, and
	 * it's not worth that.)
	 */
	for (uint32 i = 0; i < ProcGlobal->allProcCount; ++i)
	{
		PGPROC	   *proc = GetPGProcByNumber(i);

		/* Skip backends with pid=0, as they don't hold fast-path locks */
		if (proc->pid == 0)
			continue;

		LWLockAcquire(&proc->fpInfoLock, LW_SHARED);

		for (uint32 g = 0; g < FastPathLockGroupsPerBackend; g++)
		{
			/* Skip groups without registered fast-path locks */
			if (proc->fpLockBits[g] == 0)
				continue;

			for (int j = 0; j < FP_LOCK_SLOTS_PER_GROUP; j++)
			{
				LockInstanceData *instance;
				uint32		f = FAST_PATH_SLOT(g, j);
				uint32		lockbits = FAST_PATH_GET_BITS(proc, f);

				/* Skip unallocated slots */
				if (!lockbits)
					continue;

				if (el >= els)
				{
					els += MaxBackends;
					data->locks = (LockInstanceData *)
						repalloc(data->locks, sizeof(LockInstanceData) * els);
				}

				instance = &data->locks[el];
				SET_LOCKTAG_RELATION(instance->locktag, proc->databaseId,
									 proc->fpRelId[f]);
				instance->holdMask = lockbits << FAST_PATH_LOCKNUMBER_OFFSET;
				instance->waitLockMode = NoLock;
				instance->vxid.procNumber = proc->vxid.procNumber;
				instance->vxid.localTransactionId = proc->vxid.lxid;
				instance->pid = proc->pid;
				instance->leaderPid = proc->pid;
				instance->fastpath = true;

				/*
				 * Successfully taking fast path lock means there were no
				 * conflicting locks.
				 */
				instance->waitStart = 0;

				el++;
			}
		}

		if (proc->fpVXIDLock)
		{
			VirtualTransactionId vxid;
			LockInstanceData *instance;

			if (el >= els)
			{
				els += MaxBackends;
				data->locks = (LockInstanceData *)
					repalloc(data->locks, sizeof(LockInstanceData) * els);
			}

			vxid.procNumber = proc->vxid.procNumber;
			vxid.localTransactionId = proc->fpLocalTransactionId;

			instance = &data->locks[el];
			SET_LOCKTAG_VIRTUALTRANSACTION(instance->locktag, vxid);
			instance->holdMask = LOCKBIT_ON(ExclusiveLock);
			instance->waitLockMode = NoLock;
			instance->vxid.procNumber = proc->vxid.procNumber;
			instance->vxid.localTransactionId = proc->vxid.lxid;
			instance->pid = proc->pid;
			instance->leaderPid = proc->pid;
			instance->fastpath = true;
			instance->waitStart = 0;

			el++;
		}

		LWLockRelease(&proc->fpInfoLock);
	}

	/*
	 * Next, acquire lock on the entire shared lock data structure.  We do
	 * this so that, at least for locks in the primary lock table, the state
	 * will be self-consistent.
	 *
	 * Since this is a read-only operation, we take shared instead of
	 * exclusive lock.  There's not a whole lot of point to this, because all
	 * the normal operations require exclusive lock, but it doesn't hurt
	 * anything either. It will at least allow two backends to do
	 * GetLockStatusData in parallel.
	 *
	 * Must grab LWLocks in partition-number order to avoid LWLock deadlock.
	 */
	for (int i = 0; i < NUM_LOCK_PARTITIONS; i++)
		LWLockAcquire(LockHashPartitionLockByIndex(i), LW_SHARED);

	/* Now we can safely count the number of proclocks */
	data->nelements = el + hash_get_num_entries(LockMethodProcLockHash);
	if (data->nelements > els)
	{
		els = data->nelements;
		data->locks = (LockInstanceData *)
			repalloc(data->locks, sizeof(LockInstanceData) * els);
	}

	/* Now scan the tables to copy the data */
	hash_seq_init(&seqstat, LockMethodProcLockHash);

	while ((proclock = (PROCLOCK *) hash_seq_search(&seqstat)))
	{
		PGPROC	   *proc = proclock->tag.myProc;
		LOCK	   *lock = proclock->tag.myLock;
		LockInstanceData *instance = &data->locks[el];

		memcpy(&instance->locktag, &lock->tag, sizeof(LOCKTAG));
		instance->holdMask = proclock->holdMask;
		if (proc->waitLock == proclock->tag.myLock)
			instance->waitLockMode = proc->waitLockMode;
		else
			instance->waitLockMode = NoLock;
		instance->vxid.procNumber = proc->vxid.procNumber;
		instance->vxid.localTransactionId = proc->vxid.lxid;
		instance->pid = proc->pid;
		instance->leaderPid = proclock->groupLeader->pid;
		instance->fastpath = false;
		instance->waitStart = (TimestampTz) pg_atomic_read_u64(&proc->waitStart);

		el++;
	}

	/*
	 * And release locks.  We do this in reverse order for two reasons: (1)
	 * Anyone else who needs more than one of the locks will be trying to lock
	 * them in increasing order; we don't want to release the other process
	 * until it can get all the locks it needs. (2) This avoids O(N^2)
	 * behavior inside LWLockRelease.
	 */
	for (int i = NUM_LOCK_PARTITIONS; --i >= 0;)
		LWLockRelease(LockHashPartitionLockByIndex(i));

	Assert(el == data->nelements);

	return data;
}

/*
 * GetBlockerStatusData - Return a summary of the lock manager's state
 * concerning locks that are blocking the specified PID or any member of
 * the PID's lock group, for use in a user-level reporting function.
 *
 * For each PID within the lock group that is awaiting some heavyweight lock,
 * the return data includes an array of LockInstanceData objects, which are
 * the same data structure used by GetLockStatusData; but unlike that function,
 * this one reports only the PROCLOCKs associated with the lock that that PID
 * is blocked on.  (Hence, all the locktags should be the same for any one
 * blocked PID.)  In addition, we return an array of the PIDs of those backends
 * that are ahead of the blocked PID in the lock's wait queue.  These can be
 * compared with the PIDs in the LockInstanceData objects to determine which
 * waiters are ahead of or behind the blocked PID in the queue.
 *
 * If blocked_pid isn't a valid backend PID or nothing in its lock group is
 * waiting on any heavyweight lock, return empty arrays.
 *
 * The design goal is to hold the LWLocks for as short a time as possible;
 * thus, this function simply makes a copy of the necessary data and releases
 * the locks, allowing the caller to contemplate and format the data for as
 * long as it pleases.
 */
/* (中文)返回"阻塞指定 PID(或它所在锁组任一成员)的锁"的状态摘要,
 * 供 pg_blocking_pids 等用户级报告函数使用。
 *
 * 【返回内容】对被阻塞的每个 PID:
 * - procs[]:一条 BlockedProcData(该 PID、其锁/等待者条目在数组中的
 *   区间下标);
 * - locks[]:阻塞它的那把锁上的全部 PROCLOCK(LockInstanceData 形式,
 *   与 GetLockStatusData 相同);
 * - waiter_pids[]:等待队列中排在被阻塞 PID 之前的各进程 PID(可与
 *   locks[] 里的 PID 对比,看出谁在它前面/后面)。
 *
 * 【一致性】须持 ProcArrayLock 才能保证 blocked_pid 的 ProcArray 条目
 * 不会消失;再持全部分区锁(虽然只用得上一个分区,但事先不知道是
 * 哪个),保证瞬时自洽的快照。持锁期间尽量不 repalloc(预分配
 * MaxBackends 容量)。
 *
 * 【参数】blocked_pid —— 要考察的后端 PID(无效或无所属等待则返回
 * 空数组)。
 * 【返回值】BlockedProcsData(含三个 palloc 数组)。
 */
BlockedProcsData *
GetBlockerStatusData(int blocked_pid)
{
	BlockedProcsData *data;
	PGPROC	   *proc;
	int			i;

	data = palloc_object(BlockedProcsData);

	/*
	 * Guess how much space we'll need, and preallocate.  Most of the time
	 * this will avoid needing to do repalloc while holding the LWLocks.  (We
	 * assume, but check with an Assert, that MaxBackends is enough entries
	 * for the procs[] array; the other two could need enlargement, though.)
	 */
	data->nprocs = data->nlocks = data->npids = 0;
	data->maxprocs = data->maxlocks = data->maxpids = MaxBackends;
	data->procs = palloc_array(BlockedProcData, data->maxprocs);
	data->locks = palloc_array(LockInstanceData, data->maxlocks);
	data->waiter_pids = palloc_array(int, data->maxpids);

	/*
	 * In order to search the ProcArray for blocked_pid and assume that that
	 * entry won't immediately disappear under us, we must hold ProcArrayLock.
	 * In addition, to examine the lock grouping fields of any other backend,
	 * we must hold all the hash partition locks.  (Only one of those locks is
	 * actually relevant for any one lock group, but we can't know which one
	 * ahead of time.)	It's fairly annoying to hold all those locks
	 * throughout this, but it's no worse than GetLockStatusData(), and it
	 * does have the advantage that we're guaranteed to return a
	 * self-consistent instantaneous state.
	 */
	LWLockAcquire(ProcArrayLock, LW_SHARED);

	proc = BackendPidGetProcWithLock(blocked_pid);

	/* Nothing to do if it's gone */
	if (proc != NULL)
	{
		/*
		 * Acquire lock on the entire shared lock data structure.  See notes
		 * in GetLockStatusData().
		 */
		for (i = 0; i < NUM_LOCK_PARTITIONS; i++)
			LWLockAcquire(LockHashPartitionLockByIndex(i), LW_SHARED);

		if (proc->lockGroupLeader == NULL)
		{
			/* Easy case, proc is not a lock group member */
			GetSingleProcBlockerStatusData(proc, data);
		}
		else
		{
			/* Examine all procs in proc's lock group */
			dlist_iter	iter;

			dlist_foreach(iter, &proc->lockGroupLeader->lockGroupMembers)
			{
				PGPROC	   *memberProc;

				memberProc = dlist_container(PGPROC, lockGroupLink, iter.cur);
				GetSingleProcBlockerStatusData(memberProc, data);
			}
		}

		/*
		 * And release locks.  See notes in GetLockStatusData().
		 */
		for (i = NUM_LOCK_PARTITIONS; --i >= 0;)
			LWLockRelease(LockHashPartitionLockByIndex(i));

		Assert(data->nprocs <= data->maxprocs);
	}

	LWLockRelease(ProcArrayLock);

	return data;
}

/* Accumulate data about one possibly-blocked proc for GetBlockerStatusData */
/* (中文)GetBlockerStatusData 的子例程:收集"一个可能被阻塞的进程"的
 * 数据——若它没在等锁(waitLock == NULL)直接返回;否则登记一条
 * BlockedProcData,把它等的那把锁的所有 PROCLOCK 拷贝进 locks[],
 * 并把等待队列里排它之前的进程 PID 拷进 waiter_pids[](到它为止)。
 * 该进程的 fast-path 数组可忽略(能与冲突锁相关的锁必在主锁表)。 */
static void
GetSingleProcBlockerStatusData(PGPROC *blocked_proc, BlockedProcsData *data)
{
	LOCK	   *theLock = blocked_proc->waitLock;
	BlockedProcData *bproc;
	dlist_iter	proclock_iter;
	dlist_iter	proc_iter;
	dclist_head *waitQueue;
	int			queue_size;

	/* Nothing to do if this proc is not blocked */
	if (theLock == NULL)
		return;

	/* Set up a procs[] element */
	bproc = &data->procs[data->nprocs++];
	bproc->pid = blocked_proc->pid;
	bproc->first_lock = data->nlocks;
	bproc->first_waiter = data->npids;

	/*
	 * We may ignore the proc's fast-path arrays, since nothing in those could
	 * be related to a contended lock.
	 */

	/* Collect all PROCLOCKs associated with theLock */
	dlist_foreach(proclock_iter, &theLock->procLocks)
	{
		PROCLOCK   *proclock =
			dlist_container(PROCLOCK, lockLink, proclock_iter.cur);
		PGPROC	   *proc = proclock->tag.myProc;
		LOCK	   *lock = proclock->tag.myLock;
		LockInstanceData *instance;

		if (data->nlocks >= data->maxlocks)
		{
			data->maxlocks += MaxBackends;
			data->locks = (LockInstanceData *)
				repalloc(data->locks, sizeof(LockInstanceData) * data->maxlocks);
		}

		instance = &data->locks[data->nlocks];
		memcpy(&instance->locktag, &lock->tag, sizeof(LOCKTAG));
		instance->holdMask = proclock->holdMask;
		if (proc->waitLock == lock)
			instance->waitLockMode = proc->waitLockMode;
		else
			instance->waitLockMode = NoLock;
		instance->vxid.procNumber = proc->vxid.procNumber;
		instance->vxid.localTransactionId = proc->vxid.lxid;
		instance->pid = proc->pid;
		instance->leaderPid = proclock->groupLeader->pid;
		instance->fastpath = false;
		data->nlocks++;
	}

	/* Enlarge waiter_pids[] if it's too small to hold all wait queue PIDs */
	waitQueue = &(theLock->waitProcs);
	queue_size = dclist_count(waitQueue);

	if (queue_size > data->maxpids - data->npids)
	{
		data->maxpids = Max(data->maxpids + MaxBackends,
							data->npids + queue_size);
		data->waiter_pids = (int *) repalloc(data->waiter_pids,
											 sizeof(int) * data->maxpids);
	}

	/* Collect PIDs from the lock's wait queue, stopping at blocked_proc */
	dclist_foreach(proc_iter, waitQueue)
	{
		PGPROC	   *queued_proc = dlist_container(PGPROC, waitLink, proc_iter.cur);

		if (queued_proc == blocked_proc)
			break;
		data->waiter_pids[data->npids++] = queued_proc->pid;
	}

	bproc->num_locks = data->nlocks - bproc->first_lock;
	bproc->num_waiters = data->npids - bproc->first_waiter;
}

/*
 * Returns a list of currently held AccessExclusiveLocks, for use by
 * LogStandbySnapshot().  The result is a palloc'd array,
 * with the number of elements returned into *nlocks.
 *
 * XXX This currently takes a lock on all partitions of the lock table,
 * but it's possible to do better.  By reference counting locks and storing
 * the value in the ProcArray entry for each backend we could tell if any
 * locks need recording without having to acquire the partition locks and
 * scan the lock table.  Whether that's worth the additional overhead
 * is pretty dubious though.
 */
/* (中文)返回当前持有 AccessExclusiveLock 的关系锁清单(供
 * LogStandbySnapshot 写入 standby 快照,恢复时据此重建冲突锁)。
 *
 * 【流程】持全部分区锁(共享)后扫描 PROCLOCK 表:凡 holdMask 含
 * AccessExclusiveLock 且锁类型是关系锁的,记下 (xid, dbOid, relOid);
 * 跳过 xid 无效者(已提交但尚未清 xid 的,以及提交 WAL 已发但锁未
 * 放的事务都不该记录,见英文注释)。
 *
 * 【注意】"AccessExclusiveLock 只有一个持有者"的前提使这里不会出现
 * 重复条目——不要把这个写法推广到其他锁类型。此定义必须与
 * LockAcquireExtended 中 WAL 日志的判断保持一致。
 *
 * 【参数】nlocks —— 输出参数:返回条数。
 * 【返回值】palloc 的 xl_standby_lock 数组。
 */
xl_standby_lock *
GetRunningTransactionLocks(int *nlocks)
{
	xl_standby_lock *accessExclusiveLocks;
	PROCLOCK   *proclock;
	HASH_SEQ_STATUS seqstat;
	int			i;
	int			index;
	int			els;

	/*
	 * Acquire lock on the entire shared lock data structure.
	 *
	 * Must grab LWLocks in partition-number order to avoid LWLock deadlock.
	 */
	for (i = 0; i < NUM_LOCK_PARTITIONS; i++)
		LWLockAcquire(LockHashPartitionLockByIndex(i), LW_SHARED);

	/* Now we can safely count the number of proclocks */
	els = hash_get_num_entries(LockMethodProcLockHash);

	/*
	 * Allocating enough space for all locks in the lock table is overkill,
	 * but it's more convenient and faster than having to enlarge the array.
	 */
	accessExclusiveLocks = palloc(els * sizeof(xl_standby_lock));

	/* Now scan the tables to copy the data */
	hash_seq_init(&seqstat, LockMethodProcLockHash);

	/*
	 * If lock is a currently granted AccessExclusiveLock then it will have
	 * just one proclock holder, so locks are never accessed twice in this
	 * particular case. Don't copy this code for use elsewhere because in the
	 * general case this will give you duplicate locks when looking at
	 * non-exclusive lock types.
	 */
	index = 0;
	while ((proclock = (PROCLOCK *) hash_seq_search(&seqstat)))
	{
		/* make sure this definition matches the one used in LockAcquire */
		if ((proclock->holdMask & LOCKBIT_ON(AccessExclusiveLock)) &&
			proclock->tag.myLock->tag.locktag_type == LOCKTAG_RELATION)
		{
			PGPROC	   *proc = proclock->tag.myProc;
			LOCK	   *lock = proclock->tag.myLock;
			TransactionId xid = proc->xid;

			/*
			 * Don't record locks for transactions if we know they have
			 * already issued their WAL record for commit but not yet released
			 * lock. It is still possible that we see locks held by already
			 * complete transactions, if they haven't yet zeroed their xids.
			 */
			if (!TransactionIdIsValid(xid))
				continue;

			accessExclusiveLocks[index].xid = xid;
			accessExclusiveLocks[index].dbOid = lock->tag.locktag_field1;
			accessExclusiveLocks[index].relOid = lock->tag.locktag_field2;

			index++;
		}
	}

	Assert(index <= els);

	/*
	 * And release locks.  We do this in reverse order for two reasons: (1)
	 * Anyone else who needs more than one of the locks will be trying to lock
	 * them in increasing order; we don't want to release the other process
	 * until it can get all the locks it needs. (2) This avoids O(N^2)
	 * behavior inside LWLockRelease.
	 */
	for (i = NUM_LOCK_PARTITIONS; --i >= 0;)
		LWLockRelease(LockHashPartitionLockByIndex(i));

	*nlocks = index;
	return accessExclusiveLocks;
}

/* Provide the textual name of any lock mode */
/* (中文)返回任意锁模式的文本名称(查锁方法表的 lockModeNames)。
 * 供错误消息、日志与报告函数使用。 */
const char *
GetLockmodeName(LOCKMETHODID lockmethodid, LOCKMODE mode)
{
	Assert(lockmethodid > 0 && lockmethodid < lengthof(LockMethods));
	Assert(mode > 0 && mode <= LockMethods[lockmethodid]->numLockModes);
	return LockMethods[lockmethodid]->lockModeNames[mode];
}

#ifdef LOCK_DEBUG
/*
 * Dump all locks in the given proc's myProcLocks lists.
 *
 * Caller is responsible for having acquired appropriate LWLocks.
 */
/* (中文)(仅 LOCK_DEBUG)把指定进程持有的所有锁打印出来(含正在等待
 * 的锁)。调用者负责先拿好相应的 LWLock。 */
void
DumpLocks(PGPROC *proc)
{
	int			i;

	if (proc == NULL)
		return;

	if (proc->waitLock)
		LOCK_PRINT("DumpLocks: waiting on", proc->waitLock, 0);

	for (i = 0; i < NUM_LOCK_PARTITIONS; i++)
	{
		dlist_head *procLocks = &proc->myProcLocks[i];
		dlist_iter	iter;

		dlist_foreach(iter, procLocks)
		{
			PROCLOCK   *proclock = dlist_container(PROCLOCK, procLink, iter.cur);
			LOCK	   *lock = proclock->tag.myLock;

			Assert(proclock->tag.myProc == proc);
			PROCLOCK_PRINT("DumpLocks", proclock);
			LOCK_PRINT("DumpLocks", lock, 0);
		}
	}
}

/*
 * Dump all lmgr locks.
 *
 * Caller is responsible for having acquired appropriate LWLocks.
 */
/* (中文)(仅 LOCK_DEBUG)扫描整个 PROCLOCK 表,把全集群的锁状态全部
 * 打印出来(含 MyProc 正在等待的锁)。调用者负责拿好 LWLock。 */
void
DumpAllLocks(void)
{
	PGPROC	   *proc;
	PROCLOCK   *proclock;
	LOCK	   *lock;
	HASH_SEQ_STATUS status;

	proc = MyProc;

	if (proc && proc->waitLock)
		LOCK_PRINT("DumpAllLocks: waiting on", proc->waitLock, 0);

	hash_seq_init(&status, LockMethodProcLockHash);

	while ((proclock = (PROCLOCK *) hash_seq_search(&status)) != NULL)
	{
		PROCLOCK_PRINT("DumpAllLocks", proclock);

		lock = proclock->tag.myLock;
		if (lock)
			LOCK_PRINT("DumpAllLocks", lock, 0);
		else
			elog(LOG, "DumpAllLocks: proclock->tag.myLock = NULL");
	}
}
#endif							/* LOCK_DEBUG */

/*
 * LOCK 2PC resource manager's routines
 */

/*
 * Re-acquire a lock belonging to a transaction that was prepared.
 *
 * Because this function is run at db startup, re-acquiring the locks should
 * never conflict with running transactions because there are none.  We
 * assume that the lock state represented by the stored 2PC files is legal.
 *
 * When switching from Hot Standby mode to normal operation, the locks will
 * be already held by the startup process. The locks are acquired for the new
 * procs without checking for conflicts, so we don't get a conflict between the
 * startup process and the dummy procs, even though we will momentarily have
 * a situation where two procs are holding the same AccessExclusiveLock,
 * which isn't normally possible because the conflict. If we're in standby
 * mode, but a recovery snapshot hasn't been established yet, it's possible
 * that some but not all of the locks are already held by the startup process.
 *
 * This approach is simple, but also a bit dangerous, because if there isn't
 * enough shared memory to acquire the locks, an error will be thrown, which
 * is promoted to FATAL and recovery will abort, bringing down postmaster.
 * A safer approach would be to transfer the locks like we do in
 * AtPrepare_Locks, but then again, in hot standby mode it's possible for
 * read-only backends to use up all the shared lock memory anyway, so that
 * replaying the WAL record that needs to acquire a lock will throw an error
 * and PANIC anyway.
 */
/* (中文)从 2PC 状态文件重新获取 prepared 事务的锁(数据库启动时由
 * 2PC 资源管理器回调)。
 *
 * 【设计思想】启动时没有并发事务,重获锁绝不会与运行中事务冲突,
 * 因此假定 2PC 文件里的锁状态是合法的,直接建/查 LOCK、PROCLOCK
 * 并 GrantLock,不做冲突检查。Hot Standby 切回普通模式时,startup
 * 进程可能已持有这些锁:这里"跳过冲突检查"保证 dummy proc 与
 * startup 进程不会互掐(虽然短暂地出现两个进程同持
 * AccessExclusiveLock 的非常规局面)。锁重获后要"把强锁计数 +1",
 * 防止 fast-path 请求绕过主锁表。
 *
 * 【风险】共享内存不足会抛 ERROR → 提升为 FATAL → 恢复中止、关闭
 * postmaster(见英文注释的取舍说明)。
 *
 * 【参数】fxid —— prepared 事务的 FullTransactionId;info —— 记录
 * 类型;recdata —— 状态文件中的记录数据(TwoPhaseLockRecord);
 * len —— 其长度(必须恰为 sizeof(TwoPhaseLockRecord))。
 * 【返回值】无。
 */
void
lock_twophase_recover(FullTransactionId fxid, uint16 info,
					  void *recdata, uint32 len)
{
	TwoPhaseLockRecord *rec = (TwoPhaseLockRecord *) recdata;
	PGPROC	   *proc = TwoPhaseGetDummyProc(fxid, false);
	LOCKTAG    *locktag;
	LOCKMODE	lockmode;
	LOCKMETHODID lockmethodid;
	LOCK	   *lock;
	PROCLOCK   *proclock;
	PROCLOCKTAG proclocktag;
	bool		found;
	uint32		hashcode;
	uint32		proclock_hashcode;
	int			partition;
	LWLock	   *partitionLock;
	LockMethod	lockMethodTable;

	Assert(len == sizeof(TwoPhaseLockRecord));
	locktag = &rec->locktag;
	lockmode = rec->lockmode;
	lockmethodid = locktag->locktag_lockmethodid;

	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);
	lockMethodTable = LockMethods[lockmethodid];

	hashcode = LockTagHashCode(locktag);
	partition = LockHashPartition(hashcode);
	partitionLock = LockHashPartitionLock(hashcode);

	LWLockAcquire(partitionLock, LW_EXCLUSIVE);

	/*
	 * Find or create a lock with this tag.
	 */
	lock = (LOCK *) hash_search_with_hash_value(LockMethodLockHash,
												locktag,
												hashcode,
												HASH_ENTER_NULL,
												&found);
	if (!lock)
	{
		LWLockRelease(partitionLock);
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of shared memory"),
				 errhint("You might need to increase \"%s\".", "max_locks_per_transaction")));
	}

	/*
	 * if it's a new lock object, initialize it
	 */
	if (!found)
	{
		lock->grantMask = 0;
		lock->waitMask = 0;
		dlist_init(&lock->procLocks);
		dclist_init(&lock->waitProcs);
		lock->nRequested = 0;
		lock->nGranted = 0;
		MemSet(lock->requested, 0, sizeof(int) * MAX_LOCKMODES);
		MemSet(lock->granted, 0, sizeof(int) * MAX_LOCKMODES);
		LOCK_PRINT("lock_twophase_recover: new", lock, lockmode);
	}
	else
	{
		LOCK_PRINT("lock_twophase_recover: found", lock, lockmode);
		Assert((lock->nRequested >= 0) && (lock->requested[lockmode] >= 0));
		Assert((lock->nGranted >= 0) && (lock->granted[lockmode] >= 0));
		Assert(lock->nGranted <= lock->nRequested);
	}

	/*
	 * Create the hash key for the proclock table.
	 */
	proclocktag.myLock = lock;
	proclocktag.myProc = proc;

	proclock_hashcode = ProcLockHashCode(&proclocktag, hashcode);

	/*
	 * Find or create a proclock entry with this tag
	 */
	proclock = (PROCLOCK *) hash_search_with_hash_value(LockMethodProcLockHash,
														&proclocktag,
														proclock_hashcode,
														HASH_ENTER_NULL,
														&found);
	if (!proclock)
	{
		/* Oops, not enough shmem for the proclock */
		if (lock->nRequested == 0)
		{
			/*
			 * There are no other requestors of this lock, so garbage-collect
			 * the lock object.  We *must* do this to avoid a permanent leak
			 * of shared memory, because there won't be anything to cause
			 * anyone to release the lock object later.
			 */
			Assert(dlist_is_empty(&lock->procLocks));
			if (!hash_search_with_hash_value(LockMethodLockHash,
											 &(lock->tag),
											 hashcode,
											 HASH_REMOVE,
											 NULL))
				elog(PANIC, "lock table corrupted");
		}
		LWLockRelease(partitionLock);
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of shared memory"),
				 errhint("You might need to increase \"%s\".", "max_locks_per_transaction")));
	}

	/*
	 * If new, initialize the new entry
	 */
	if (!found)
	{
		Assert(proc->lockGroupLeader == NULL);
		proclock->groupLeader = proc;
		proclock->holdMask = 0;
		proclock->releaseMask = 0;
		/* Add proclock to appropriate lists */
		dlist_push_tail(&lock->procLocks, &proclock->lockLink);
		dlist_push_tail(&proc->myProcLocks[partition],
						&proclock->procLink);
		PROCLOCK_PRINT("lock_twophase_recover: new", proclock);
	}
	else
	{
		PROCLOCK_PRINT("lock_twophase_recover: found", proclock);
		Assert((proclock->holdMask & ~lock->grantMask) == 0);
	}

	/*
	 * lock->nRequested and lock->requested[] count the total number of
	 * requests, whether granted or waiting, so increment those immediately.
	 */
	lock->nRequested++;
	lock->requested[lockmode]++;
	Assert((lock->nRequested > 0) && (lock->requested[lockmode] > 0));

	/*
	 * We shouldn't already hold the desired lock.
	 */
	if (proclock->holdMask & LOCKBIT_ON(lockmode))
		elog(ERROR, "lock %s on object %u/%u/%u is already held",
			 lockMethodTable->lockModeNames[lockmode],
			 lock->tag.locktag_field1, lock->tag.locktag_field2,
			 lock->tag.locktag_field3);

	/*
	 * We ignore any possible conflicts and just grant ourselves the lock. Not
	 * only because we don't bother, but also to avoid deadlocks when
	 * switching from standby to normal mode. See function comment.
	 */
	GrantLock(lock, proclock, lockmode);

	/*
	 * Bump strong lock count, to make sure any fast-path lock requests won't
	 * be granted without consulting the primary lock table.
	 */
	if (ConflictsWithRelationFastPath(&lock->tag, lockmode))
	{
		uint32		fasthashcode = FastPathStrongLockHashPartition(hashcode);

		SpinLockAcquire(&FastPathStrongRelationLocks->mutex);
		FastPathStrongRelationLocks->count[fasthashcode]++;
		SpinLockRelease(&FastPathStrongRelationLocks->mutex);
	}

	LWLockRelease(partitionLock);
}

/*
 * Re-acquire a lock belonging to a transaction that was prepared, when
 * starting up into hot standby mode.
 */
/* (中文)以 Hot Standby 模式启动时重获 prepared 事务的锁:不必在锁表
 * 里登记,只要让"冲突检测"知道这些 AccessExclusiveLock 存在即可——
 * 直接调用 StandbyAcquireAccessExclusiveLock,把 (xid, dbOid, relOid)
 * 登记到 standby 的冲突跟踪结构里(只关心"关系上的 AccessExclusiveLock"
 * 这类会影响只读事务冲突判定的锁)。
 *
 * 【参数】fxid —— prepared 事务的 FullTransactionId;info —— 记录
 * 类型;recdata —— TwoPhaseLockRecord;len —— 记录长度。
 * 【返回值】无。
 */
void
lock_twophase_standby_recover(FullTransactionId fxid, uint16 info,
							  void *recdata, uint32 len)
{
	TwoPhaseLockRecord *rec = (TwoPhaseLockRecord *) recdata;
	LOCKTAG    *locktag;
	LOCKMODE	lockmode;
	LOCKMETHODID lockmethodid;

	Assert(len == sizeof(TwoPhaseLockRecord));
	locktag = &rec->locktag;
	lockmode = rec->lockmode;
	lockmethodid = locktag->locktag_lockmethodid;

	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);

	if (lockmode == AccessExclusiveLock &&
		locktag->locktag_type == LOCKTAG_RELATION)
	{
		StandbyAcquireAccessExclusiveLock(XidFromFullTransactionId(fxid),
										  locktag->locktag_field1 /* dboid */ ,
										  locktag->locktag_field2 /* reloid */ );
	}
}


/*
 * 2PC processing routine for COMMIT PREPARED case.
 *
 * Find and release the lock indicated by the 2PC record.
 */
/* (中文)COMMIT PREPARED 时的 2PC 处理:找到 2PC 记录指定的锁并释放
 * (取 dummy proc 后调 LockRefindAndRelease,decrement_strong_lock_count
 * = true 表示还要把对应的强锁计数退回,恢复 fast-path 可用性)。 */
void
lock_twophase_postcommit(FullTransactionId fxid, uint16 info,
						 void *recdata, uint32 len)
{
	TwoPhaseLockRecord *rec = (TwoPhaseLockRecord *) recdata;
	PGPROC	   *proc = TwoPhaseGetDummyProc(fxid, true);
	LOCKTAG    *locktag;
	LOCKMETHODID lockmethodid;
	LockMethod	lockMethodTable;

	Assert(len == sizeof(TwoPhaseLockRecord));
	locktag = &rec->locktag;
	lockmethodid = locktag->locktag_lockmethodid;

	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);
	lockMethodTable = LockMethods[lockmethodid];

	LockRefindAndRelease(lockMethodTable, proc, locktag, rec->lockmode, true);
}

/*
 * 2PC processing routine for ROLLBACK PREPARED case.
 *
 * This is actually just the same as the COMMIT case.
 */
/* (中文)ROLLBACK PREPARED 时的 2PC 处理:与 COMMIT 情形完全一致
 * (释放锁的动作相同),直接转发。 */
void
lock_twophase_postabort(FullTransactionId fxid, uint16 info,
						void *recdata, uint32 len)
{
	lock_twophase_postcommit(fxid, info, recdata, len);
}

/*
 *		VirtualXactLockTableInsert
 *
 *		Take vxid lock via the fast-path.  There can't be any pre-existing
 *		lockers, as we haven't advertised this vxid via the ProcArray yet.
 *
 *		Since MyProc->fpLocalTransactionId will normally contain the same data
 *		as MyProc->vxid.lxid, you might wonder if we really need both.  The
 *		difference is that MyProc->vxid.lxid is set and cleared unlocked, and
 *		examined by procarray.c, while fpLocalTransactionId is protected by
 *		fpInfoLock and is used only by the locking subsystem.  Doing it this
 *		way makes it easier to verify that there are no funny race conditions.
 *
 *		We don't bother recording this lock in the local lock table, since it's
 *		only ever released at the end of a transaction.  Instead,
 *		LockReleaseAll() calls VirtualXactLockTableCleanup().
 */
/* (中文)通过 fast-path 登记"本事务 VXID 的锁"(ExclusiveLock,由
 * fpVXIDLock + fpLocalTransactionId 表示)。在向 ProcArray 公布 vxid
 * 之前调用,因此不可能存在先到的加锁者。
 *
 * 【设计思想】为什么要两个字段存同一个 lxid:MyProc->vxid.lxid 由
 * procarray.c 无锁读写(快速查看),而 fpLocalTransactionId 受
 * fpInfoLock 保护、仅供锁子系统使用,便于排除各种竞态。
 * 本锁不登记进本地锁表(它只在事务结束时释放),LockReleaseAll
 * 会调用 VirtualXactLockTableCleanup 收尾。 */
void
VirtualXactLockTableInsert(VirtualTransactionId vxid)
{
	Assert(VirtualTransactionIdIsValid(vxid));

	LWLockAcquire(&MyProc->fpInfoLock, LW_EXCLUSIVE);

	Assert(MyProc->vxid.procNumber == vxid.procNumber);
	Assert(MyProc->fpLocalTransactionId == InvalidLocalTransactionId);
	Assert(MyProc->fpVXIDLock == false);

	MyProc->fpVXIDLock = true;
	MyProc->fpLocalTransactionId = vxid.localTransactionId;

	LWLockRelease(&MyProc->fpInfoLock);
}

/*
 *		VirtualXactLockTableCleanup
 *
 *		Check whether a VXID lock has been materialized; if so, release it,
 *		unblocking waiters.
 */
/* (中文)清理本事务的 VXID 锁(顶层事务结束时由 LockReleaseAll 调用):
 * 若锁仍在 fast-path(fpVXIDLock = true),清零标志即可;若已被别人
 * "物化"进共享锁表(fpVXIDLock 被清但 fpLocalTransactionId 仍有效),
 * 则用 LockRefindAndRelease 释放共享锁,唤醒等待者。全程受
 * fpInfoLock 保护。 */
void
VirtualXactLockTableCleanup(void)
{
	bool		fastpath;
	LocalTransactionId lxid;

	Assert(MyProc->vxid.procNumber != INVALID_PROC_NUMBER);

	/*
	 * Clean up shared memory state.
	 */
	LWLockAcquire(&MyProc->fpInfoLock, LW_EXCLUSIVE);

	fastpath = MyProc->fpVXIDLock;
	lxid = MyProc->fpLocalTransactionId;
	MyProc->fpVXIDLock = false;
	MyProc->fpLocalTransactionId = InvalidLocalTransactionId;

	LWLockRelease(&MyProc->fpInfoLock);

	/*
	 * If fpVXIDLock has been cleared without touching fpLocalTransactionId,
	 * that means someone transferred the lock to the main lock table.
	 */
	if (!fastpath && LocalTransactionIdIsValid(lxid))
	{
		VirtualTransactionId vxid;
		LOCKTAG		locktag;

		vxid.procNumber = MyProcNumber;
		vxid.localTransactionId = lxid;
		SET_LOCKTAG_VIRTUALTRANSACTION(locktag, vxid);

		LockRefindAndRelease(LockMethods[DEFAULT_LOCKMETHOD], MyProc,
							 &locktag, ExclusiveLock, false);
	}
}

/*
 *		XactLockForVirtualXact
 *
 * If TransactionIdIsValid(xid), this is essentially XactLockTableWait(xid,
 * NULL, NULL, XLTW_None) or ConditionalXactLockTableWait(xid).  Unlike those
 * functions, it assumes "xid" is never a subtransaction and that "xid" is
 * prepared, committed, or aborted.
 *
 * If !TransactionIdIsValid(xid), this locks every prepared XID having been
 * known as "vxid" before its PREPARE TRANSACTION.
 */
/* (中文)等待"某个 VXID 曾对应的事务"结束(见 VirtualXactLock 的
 * 调用路径):
 * - xid 有效:等价于 XactLockTableWait / ConditionalXactLockTableWait,
 *   但假设 xid 不是子事务、且已处于 prepared/committed/aborted 状态;
 * - xid 无效:通过 TwoPhaseGetXidByVirtualXID 枚举所有"PREPARE 前曾是
 *   该 vxid"的 prepared XID,逐个等待(可能多个,循环处理)。
 * max_prepared_xacts == 0 时直接成功(没有 2PC 可等)。
 *
 * 【参数】vxid —— 原 VXID;xid —— 已知的对应 XID(可无效);
 * wait —— true 阻塞等待,false 只检查。
 * 【返回值】true = 事务已结束(或无需等);false = 仍在运行(仅
 * wait = false 时可能)。
 */
static bool
XactLockForVirtualXact(VirtualTransactionId vxid,
					   TransactionId xid, bool wait)
{
	bool		more = false;

	/* There is no point to wait for 2PCs if you have no 2PCs. */
	if (max_prepared_xacts == 0)
		return true;

	do
	{
		LockAcquireResult lar;
		LOCKTAG		tag;

		/* Clear state from previous iterations. */
		if (more)
		{
			xid = InvalidTransactionId;
			more = false;
		}

		/* If we have no xid, try to find one. */
		if (!TransactionIdIsValid(xid))
			xid = TwoPhaseGetXidByVirtualXID(vxid, &more);
		if (!TransactionIdIsValid(xid))
		{
			Assert(!more);
			return true;
		}

		/* Check or wait for XID completion. */
		SET_LOCKTAG_TRANSACTION(tag, xid);
		lar = LockAcquire(&tag, ShareLock, false, !wait);
		if (lar == LOCKACQUIRE_NOT_AVAIL)
			return false;
		LockRelease(&tag, ShareLock, false);
	} while (more);

	return true;
}

/*
 *		VirtualXactLock
 *
 * If wait = true, wait as long as the given VXID or any XID acquired by the
 * same transaction is still running.  Then, return true.
 *
 * If wait = false, just check whether that VXID or one of those XIDs is still
 * running, and return true or false.
 */
/* (中文)等待/检查指定 VXID 对应的"虚拟事务"结束:
 * - wait = true:一直等到该 VXID(或它后来取得的 XID)不再运行,返回
 *   true;
 * - wait = false:只检查是否仍在运行,立即返回 true/false。
 *
 * 【算法】若 vxid 是"恢复的 prepared 事务",直接按其 XID 等待
 * (XactLockForVirtualXact);否则:
 * 1. 查该 PGPROC 是否还存在、其 fpLocalTransactionId 是否仍是这个
 *    lxid(必须持 proc->fpInfoLock 检查,目标进程只在持锁时改 lxid);
 * 2. 已不存在/已不同 → 说明 VXID 已结束,跳到 XactLockForVirtualXact
 *    处理"它可能转成的 prepared XID";
 * 3. wait = false → 直接返回 false(还在运行);
 * 4. 否则,若目标进程的 VXID 锁还在 fast-path(fpVXIDLock),先在共享
 *    锁表里物化(SetupLockInTable + GrantLock,基于目标 proc 而不是
 *    我们——因为我们是在"替"目标进程制造阻塞点),记录其 XID,
 *    然后对 VXID 锁加 ShareLock 等待它释放,最后再查它可能转成的
 *    prepared XID。
 *
 * 【参数】vxid —— 目标虚拟事务;wait —— 是否阻塞等待。
 * 【返回值】true = 已结束;false = 仍在运行(仅 wait = false)。
 */
bool
VirtualXactLock(VirtualTransactionId vxid, bool wait)
{
	LOCKTAG		tag;
	PGPROC	   *proc;
	TransactionId xid = InvalidTransactionId;

	Assert(VirtualTransactionIdIsValid(vxid));

	if (VirtualTransactionIdIsRecoveredPreparedXact(vxid))
		/* no vxid lock; localTransactionId is a normal, locked XID */
		return XactLockForVirtualXact(vxid, vxid.localTransactionId, wait);

	SET_LOCKTAG_VIRTUALTRANSACTION(tag, vxid);

	/*
	 * If a lock table entry must be made, this is the PGPROC on whose behalf
	 * it must be done.  Note that the transaction might end or the PGPROC
	 * might be reassigned to a new backend before we get around to examining
	 * it, but it doesn't matter.  If we find upon examination that the
	 * relevant lxid is no longer running here, that's enough to prove that
	 * it's no longer running anywhere.
	 */
	proc = ProcNumberGetProc(vxid.procNumber);
	if (proc == NULL)
		return XactLockForVirtualXact(vxid, InvalidTransactionId, wait);

	/*
	 * We must acquire this lock before checking the procNumber and lxid
	 * against the ones we're waiting for.  The target backend will only set
	 * or clear lxid while holding this lock.
	 */
	LWLockAcquire(&proc->fpInfoLock, LW_EXCLUSIVE);

	if (proc->vxid.procNumber != vxid.procNumber
		|| proc->fpLocalTransactionId != vxid.localTransactionId)
	{
		/* VXID ended */
		LWLockRelease(&proc->fpInfoLock);
		return XactLockForVirtualXact(vxid, InvalidTransactionId, wait);
	}

	/*
	 * If we aren't asked to wait, there's no need to set up a lock table
	 * entry.  The transaction is still in progress, so just return false.
	 */
	if (!wait)
	{
		LWLockRelease(&proc->fpInfoLock);
		return false;
	}

	/*
	 * OK, we're going to need to sleep on the VXID.  But first, we must set
	 * up the primary lock table entry, if needed (ie, convert the proc's
	 * fast-path lock on its VXID to a regular lock).
	 */
	if (proc->fpVXIDLock)
	{
		PROCLOCK   *proclock;
		uint32		hashcode;
		LWLock	   *partitionLock;

		hashcode = LockTagHashCode(&tag);

		partitionLock = LockHashPartitionLock(hashcode);
		LWLockAcquire(partitionLock, LW_EXCLUSIVE);

		proclock = SetupLockInTable(LockMethods[DEFAULT_LOCKMETHOD], proc,
									&tag, hashcode, ExclusiveLock);
		if (!proclock)
		{
			LWLockRelease(partitionLock);
			LWLockRelease(&proc->fpInfoLock);
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of shared memory"),
					 errhint("You might need to increase \"%s\".", "max_locks_per_transaction")));
		}
		GrantLock(proclock->tag.myLock, proclock, ExclusiveLock);

		LWLockRelease(partitionLock);

		proc->fpVXIDLock = false;
	}

	/*
	 * If the proc has an XID now, we'll avoid a TwoPhaseGetXidByVirtualXID()
	 * search.  The proc might have assigned this XID but not yet locked it,
	 * in which case the proc will lock this XID before releasing the VXID.
	 * The fpInfoLock critical section excludes VirtualXactLockTableCleanup(),
	 * so we won't save an XID of a different VXID.  It doesn't matter whether
	 * we save this before or after setting up the primary lock table entry.
	 */
	xid = proc->xid;

	/* Done with proc->fpLockBits */
	LWLockRelease(&proc->fpInfoLock);

	/* Time to wait. */
	(void) LockAcquire(&tag, ShareLock, false, false);

	LockRelease(&tag, ShareLock, false);
	return XactLockForVirtualXact(vxid, xid, wait);
}

/*
 * LockWaiterCount
 *
 * Find the number of lock requester on this locktag
 */
/* (中文)统计该锁标签上"请求者"的总数(nRequested,含已授予与等待
 * 中的)。供 RelationExtensionLockWaiterCount 等"探测锁竞争程度"的
 * 调用使用。 */
int
LockWaiterCount(const LOCKTAG *locktag)
{
	LOCKMETHODID lockmethodid = locktag->locktag_lockmethodid;
	LOCK	   *lock;
	bool		found;
	uint32		hashcode;
	LWLock	   *partitionLock;
	int			waiters = 0;

	if (lockmethodid <= 0 || lockmethodid >= lengthof(LockMethods))
		elog(ERROR, "unrecognized lock method: %d", lockmethodid);

	hashcode = LockTagHashCode(locktag);
	partitionLock = LockHashPartitionLock(hashcode);
	LWLockAcquire(partitionLock, LW_EXCLUSIVE);

	lock = (LOCK *) hash_search_with_hash_value(LockMethodLockHash,
												locktag,
												hashcode,
												HASH_FIND,
												&found);
	if (found)
	{
		Assert(lock != NULL);
		waiters = lock->nRequested;
	}
	LWLockRelease(partitionLock);

	return waiters;
}
