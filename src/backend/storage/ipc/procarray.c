/*-------------------------------------------------------------------------
 *
 * procarray.c
 *	  POSTGRES process array code.
 *
 *
 * This module maintains arrays of PGPROC substructures, as well as associated
 * arrays in ProcGlobal, for all active backends.  Although there are several
 * uses for this, the principal one is as a means of determining the set of
 * currently running transactions.
 *
 * Because of various subtle race conditions it is critical that a backend
 * hold the correct locks while setting or clearing its xid (in
 * ProcGlobal->xids[]/MyProc->xid).  See notes in
 * src/backend/access/transam/README.
 *
 * The process arrays now also include structures representing prepared
 * transactions.  The xid and subxids fields of these are valid, as are the
 * myProcLocks lists.  They can be distinguished from regular backend PGPROCs
 * at need by checking for pid == 0.
 *
 * During hot standby, we also keep a list of XIDs representing transactions
 * that are known to be running on the primary (or more precisely, were running
 * as of the current point in the WAL stream).  This list is kept in the
 * KnownAssignedXids array, and is updated by watching the sequence of
 * arriving XIDs.  This is necessary because if we leave those XIDs out of
 * snapshots taken for standby queries, then they will appear to be already
 * complete, leading to MVCC failures.  Note that in hot standby, the PGPROC
 * array represents standby processes, which by definition are not running
 * transactions that have XIDs.
 *
 * It is perhaps possible for a backend on the primary to terminate without
 * writing an abort record for its transaction.  While that shouldn't really
 * happen, it would tie up KnownAssignedXids indefinitely, so we protect
 * ourselves by pruning the array when a valid list of running XIDs arrives.
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 事务可见性判定的核心模块。它维护一个位于共享内存
 * 的"进程数组"(ProcArrayStruct),登记所有活跃后端与两阶段提交
 * (prepared)事务的 PGPROC,并据此回答 MVCC 体系最根本的问题:"给定的
 * xid 是否仍然活跃?"。快照(snapshot)构造、VACUUM 清理边界、热备
 * 冲突处理、hot_standby_feedback、checkpoint 延时判定等大量子系统都
 * 依赖本模块。
 *
 * 【核心数据结构】
 * - ProcArrayStruct(procArray):共享控制结构。核心是 pgprocnos[] 数组,
 *   存放"当前活跃"PGPROC 在 allProcs[] 中的下标,并按 PGPROC 地址升序
 *   排列(见 ProcArrayAdd 的注释,为的是遍历时的 cache 局部性);
 *   ProcGlobal->xids[] / subxidStates[] / statusFlags[] 是与之一一对应的
 *   并行数组,分别保存各后端的 xid、子事务缓存状态与状态标志。取快照时
 *   只需顺序遍历这三个紧凑数组,而无需触碰整个 PGPROC,大幅降低缓存
 *   缺失。PGPROC 的 pgxactoff 字段是它在这些并行数组中的下标。
 * - ProcArrayLock:保护上述共享结构的 LWLock。读方(取快照、判断 xid
 *   是否活跃、计算水位)持 SHARED;写方(提交/中止时清除 xid、
 *   ProcArrayAdd/Remove)持 EXCLUSIVE。设置与清除 xid 的锁协议细节见
 *   src/backend/access/transam/README。
 * - KnownAssignedXids:热备(hot standby)模式下在备机维护的"主库上
 *   正在运行事务"的 xid 集合。备机的 PGPROC 不持有 xid,必须靠重放
 *   WAL 记录推断主库的运行状态,否则这些事务在备机快照中会看起来已经
 *   完成,导致 MVCC 错误(见文件头英文注释与 KnownAssignedXids 子模块)。
 * - xmin/xmax 与水位(horizon):GetSnapshotData() 收集 xmin(仍在运行的
 *   最小 xid)、xmax(最新已完成 xid + 1)与 xip 数组(xmin 与 xmax 之间
 *   正在运行的 xid 列表);ComputeXidHorizons() 计算各类清理边界
 *   (shared/catalog/data/temp 表各有各的"最老不可删除 xid")。
 *
 * 【设计思想】
 * - 锁协议:清除 xid 必须持 EXCLUSIVE 锁,使"正在运行集合"的变化对
 *   取快照者原子可见;快照构造持 SHARED 锁即可,因为 xid 只能"从无到有"
 *   (赋新值),取快照者不会漏掉任何已提交的事务;
 * - 性能考量:提交/取快照是全系统最热门的路径,本模块做了大量优化——
 *   xactCompletionCount 计数允许快照整体复用(GetSnapshotDataReuse);
 *   组提交(group XID clearing)用一次加锁替一批进程清除 xid;
 *   latch 与锁的获取顺序、原子读(见 UINT32_ACCESS_ONCE)等细节都为了
 *   把 ProcArrayLock 的持有时间与争用压到最低;
 * - 协作关系:与 access/transam/xact.c(事务开始/结束)、clog 与
 *   pg_subtrans(提交状态、父子事务链)、snapmgr.c(快照缓存)、
 *   replication(槽位 xmin)、standby.c(恢复冲突)紧密配合。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/procarray.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>

#include "access/subtrans.h"
#include "access/transam.h"
#include "access/twophase.h"
#include "access/xact.h"
#include "access/xlogutils.h"
#include "catalog/catalog.h"
#include "catalog/pg_authid.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "postmaster/bgworker.h"
#include "port/pg_lfind.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "storage/procsignal.h"
#include "storage/subsystems.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/injection_point.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/snapmgr.h"
#include "utils/wait_event.h"

#define UINT32_ACCESS_ONCE(var)		 ((uint32)(*((volatile uint32 *)&(var))))
/* (中文)对 32 位变量做"单次读取"的辅助宏:强制编译器把 var 当作
 * volatile 一次性读入,防止并发修改(如其他后端正在设置/清除 xid)时
 * 出现撕裂读,也避免编译器多次重读造成前后不一致。procarray 读取别的
 * 进程的 xid 时一律走这个宏,与 GetNewTransactionId() 的写入侧配合。 */

/* Our shared memory area */
/* (中文)进程数组的共享控制结构(ProcArrayStruct),位于共享内存,
 * 由 ProcArrayLock 保护。它登记"当前所有活跃后端 + prepared 事务",
 * 是 MVCC 可见性判定的数据基础。
 *
 * 字段含义:
 * - numProcs  : 当前有效的条目数(逻辑数组长度);
 * - maxProcs  : pgprocnos[] 的分配容量(固定为 PROCARRAY_MAXPROCS =
 *               MaxBackends + max_prepared_xacts,永不增长);
 * - KnownAssignedXids 一族字段 : 热备模式专用的 xid 表(见本文件
 *   KnownAssignedXids 子模块的注释):maxKnownAssignedXids 是容量,
 *   numKnownAssignedXids 是当前有效条目数,tail/head 是该数组
 *   [tail, head) 区间的两个指针(head 指向最新元素之后一位)。数组
 *   允许中间有"空洞"(被标记为无效但未物理清除的槽位),以换取删除
 *   O(1) 的代价,定期压缩(见 KnownAssignedXidsCompress);
 * - lastOverflowedXid : 从 KnownAssignedXids 中"被丢弃"的最晚子事务
 *   xid,无则 InvalidTransactionId。语义与 PGPROC 子事务缓存溢出
 *   (overflowed)完全对应:只要目标 xid 不晚于它,就不能断言快照中
 *   的子事务信息是完整的。修改须持 EXCLUSIVE 锁,读取持 SHARED 锁;
 * - replication_slot_xmin / replication_slot_catalog_xmin : 所有复制槽
 *   要求的最老 xmin(数据表 / 系统目录分别)。计算清理水位时必须计入,
 *   防止 VACUUM 删除复制客户端仍需要的数据;
 * - pgprocnos[] : 柔性数组,保存 allProcs[] 中当前活跃 PGPROC 的下标,
 *   按下标升序排列(见 ProcArrayAdd 的排序注释)。 */
typedef struct ProcArrayStruct
{
	int			numProcs;		/* number of valid procs entries */
	int			maxProcs;		/* allocated size of procs array */

	/*
	 * Known assigned XIDs handling
	 */
	int			maxKnownAssignedXids;	/* allocated size of array */
	int			numKnownAssignedXids;	/* current # of valid entries */
	int			tailKnownAssignedXids;	/* index of oldest valid element */
	int			headKnownAssignedXids;	/* index of newest element, + 1 */

	/*
	 * Highest subxid that has been removed from KnownAssignedXids array to
	 * prevent overflow; or InvalidTransactionId if none.  We track this for
	 * similar reasons to tracking overflowing cached subxids in PGPROC
	 * entries.  Must hold exclusive ProcArrayLock to change this, and shared
	 * lock to read it.
	 */
	TransactionId lastOverflowedXid;

	/* oldest xmin of any replication slot */
	TransactionId replication_slot_xmin;
	/* oldest catalog xmin of any replication slot */
	TransactionId replication_slot_catalog_xmin;

	/* indexes into allProcs[], has PROCARRAY_MAXPROCS entries */
	int			pgprocnos[FLEXIBLE_ARRAY_MEMBER];
} ProcArrayStruct;

static void ProcArrayShmemRequest(void *arg);
static void ProcArrayShmemInit(void *arg);
static void ProcArrayShmemAttach(void *arg);

/* (中文)指向共享内存中 ProcArrayStruct 的指针:启动阶段由
 * ProcArrayShmemInit 初始化(借助 ShmemRequestStruct 分配的地址),
 * 本文件其余函数都通过它访问进程数组。 */
static ProcArrayStruct *procArray;

/* (中文)向共享内存子系统注册的 request/init/attach 回调集:
 * - request : 启动阶段声明"Proc Array"结构与热备所需的 KnownAssignedXids
 *   数组各需要多少共享内存;
 * - init    : postmaster 内负责把共享内存清零并设初值;
 * - attach  : postmaster 派生的其他进程(如 bgworker)启动时重新取得
 *   共享指针。 */
const struct ShmemCallbacks ProcArrayShmemCallbacks = {
	.request_fn = ProcArrayShmemRequest,
	.init_fn = ProcArrayShmemInit,
	.attach_fn = ProcArrayShmemAttach,
};

/*
 * State for the GlobalVisTest* family of functions. Those functions can
 * e.g. be used to decide if a deleted row can be removed without violating
 * MVCC semantics: If the deleted row's xmax is not considered to be running
 * by anyone, the row can be removed.
 *
 * To avoid slowing down GetSnapshotData(), we don't calculate a precise
 * cutoff XID while building a snapshot (looking at the frequently changing
 * xmins scales badly). Instead we compute two boundaries while building the
 * snapshot:
 *
 * 1) definitely_needed, indicating that rows deleted by XIDs >=
 *    definitely_needed are definitely still visible.
 *
 * 2) maybe_needed, indicating that rows deleted by XIDs < maybe_needed can
 *    definitely be removed
 *
 * When testing an XID that falls in between the two (i.e. XID >= maybe_needed
 * && XID < definitely_needed), the boundaries can be recomputed (using
 * ComputeXidHorizons()) to get a more accurate answer. This is cheaper than
 * maintaining an accurate value all the time.
 *
 * As it is not cheap to compute accurate boundaries, we limit the number of
 * times that happens in short succession. See GlobalVisTestShouldUpdate().
 *
 *
 * There are three backend lifetime instances of this struct, optimized for
 * different types of relations. As e.g. a normal user defined table in one
 * database is inaccessible to backends connected to another database, a test
 * specific to a relation can be more aggressive than a test for a shared
 * relation.  Currently we track four different states:
 *
 * 1) GlobalVisSharedRels, which only considers an XID's
 *    effects visible-to-everyone if neither snapshots in any database, nor a
 *    replication slot's xmin, nor a replication slot's catalog_xmin might
 *    still consider XID as running.
 *
 * 2) GlobalVisCatalogRels, which only considers an XID's
 *    effects visible-to-everyone if neither snapshots in the current
 *    database, nor a replication slot's xmin, nor a replication slot's
 *    catalog_xmin might still consider XID as running.
 *
 *    I.e. the difference to GlobalVisSharedRels is that
 *    snapshot in other databases are ignored.
 *
 * 3) GlobalVisDataRels, which only considers an XID's
 *    effects visible-to-everyone if neither snapshots in the current
 *    database, nor a replication slot's xmin consider XID as running.
 *
 *    I.e. the difference to GlobalVisCatalogRels is that
 *    replication slot's catalog_xmin is not taken into account.
 *
 * 4) GlobalVisTempRels, which only considers the current session, as temp
 *    tables are not visible to other sessions.
 *
 * GlobalVisTestFor(relation) returns the appropriate state
 * for the relation.
 *
 * The boundaries are FullTransactionIds instead of TransactionIds to avoid
 * wraparound dangers. There e.g. would otherwise exist no procarray state to
 * prevent maybe_needed to become old enough after the GetSnapshotData()
 * call.
 *
 * The typedef is in the header.
 */
/* (中文)GlobalVisTest* 系列函数使用的"全局可见性状态":用两个粗糙的
 * 边界回答"某 xid 是否可能仍被某个快照认为在运行",避免每次都精确
 * 计算水位(见上方英文注释)。
 *
 * - definitely_needed : XID >= 该值的行"一定仍可见"(边界本身含义为
 *   "xid 大于等于此值则可能仍被某些后端视为运行"),即上界;
 * - maybe_needed      : XID < 该值的行"一定可以删除/被所有人看到已提交",
 *   即下界。
 *
 * 落在 [maybe_needed, definitely_needed) 之间的 xid 无法确定,需要用
 * ComputeXidHorizons() 重新精确计算边界后再判断(见
 * GlobalVisTestIsRemovableFullXid)。
 *
 * 之所以用 FullTransactionId(64 位)而非 32 位 TransactionId,是为了
 * 避免回绕(如果用一个 32 位值作"比它老就安全"的基准,事务 id 回绕后
 * 这个判断就失效了,详见英文注释)。
 *
 * 进程内共维护四份这样的状态(见下方四个静态变量),分别用于共享表 /
 * 系统目录 / 普通数据表 / 临时表:前三种的可删除边界可以越来越激进
 * (共享表受所有库影响,普通表只受本库影响),临时表只与当前会话有关。 */
struct GlobalVisState
{
	/* XIDs >= are considered running by some backend */
	FullTransactionId definitely_needed;

	/* XIDs < are not considered to be running by any backend */
	FullTransactionId maybe_needed;
};

/*
 * Result of ComputeXidHorizons().
 */
/* (中文)ComputeXidHorizons() 的计算结果:一组"水位"(horizon)值,
 * 每种水位都回答"删除/清理到哪个 xid 为止是安全的"。字段含义:
 *
 * - latest_completed : 持锁时 TransamVariables->latestCompletedXid 的值
 *   (最新已提交/中止的事务 id),后续水位计算都以它为时间基准;
 * - slot_xmin / slot_catalog_xmin : 复制槽要求的数据 / catalog 水位
 *   (与 procArray 中的对应字段一致);
 * - oldest_considered_running : 可能仍被任意后端(含 VACUUM、逻辑解码)
 *   认为在运行的最老 xid。注意与普通清理水位不同,连 VACUUM 进程都
 *   必须计入——VACUUM 判断可见性时也要查 pg_subtrans,因此这是
 *   pg_subtrans 能安全截断的最低界限(见英文注释);
 * - shared_oldest_nonremovable : 共享表(所有库可见)中已删除元组必须
 *   保留到的最老 xid,含复制槽影响;
 * - shared_oldest_nonremovable_raw : 同上,但不含 catalog_xmin 的影响,
 *   用于 hot_standby_feedback:主库收到普通反馈只对数据表收紧,
 *   catalog 反馈只对目录收紧,从而让数据表清理得更积极;
 * - catalog_oldest_nonremovable : 非共享系统目录表中必须保留到的最老 xid;
 * - data_oldest_nonremovable    : 普通用户表中必须保留到的最老 xid;
 * - temp_oldest_nonremovable    : 本会话临时表中必须保留到的最老 xid。 */
typedef struct ComputeXidHorizonsResult
{
	/*
	 * The value of TransamVariables->latestCompletedXid when
	 * ComputeXidHorizons() held ProcArrayLock.
	 */
	FullTransactionId latest_completed;

	/*
	 * The same for procArray->replication_slot_xmin and
	 * procArray->replication_slot_catalog_xmin.
	 */
	TransactionId slot_xmin;
	TransactionId slot_catalog_xmin;

	/*
	 * Oldest xid that any backend might still consider running. This needs to
	 * include processes running VACUUM, in contrast to the normal visibility
	 * cutoffs, as vacuum needs to be able to perform pg_subtrans lookups when
	 * determining visibility, but doesn't care about rows above its xmin to
	 * be removed.
	 *
	 * This likely should only be needed to determine whether pg_subtrans can
	 * be truncated. It currently includes the effects of replication slots,
	 * for historical reasons. But that could likely be changed.
	 */
	TransactionId oldest_considered_running;

	/*
	 * Oldest xid for which deleted tuples need to be retained in shared
	 * tables.
	 *
	 * This includes the effects of replication slots. If that's not desired,
	 * look at shared_oldest_nonremovable_raw;
	 */
	TransactionId shared_oldest_nonremovable;

	/*
	 * Oldest xid that may be necessary to retain in shared tables. This is
	 * the same as shared_oldest_nonremovable, except that is not affected by
	 * replication slot's catalog_xmin.
	 *
	 * This is mainly useful to be able to send the catalog_xmin to upstream
	 * streaming replication servers via hot_standby_feedback, so they can
	 * apply the limit only when accessing catalog tables.
	 */
	TransactionId shared_oldest_nonremovable_raw;

	/*
	 * Oldest xid for which deleted tuples need to be retained in non-shared
	 * catalog tables.
	 */
	TransactionId catalog_oldest_nonremovable;

	/*
	 * Oldest xid for which deleted tuples need to be retained in normal user
	 * defined tables.
	 */
	TransactionId data_oldest_nonremovable;

	/*
	 * Oldest xid for which deleted tuples need to be retained in this
	 * session's temporary tables.
	 */
	TransactionId temp_oldest_nonremovable;
} ComputeXidHorizonsResult;

/*
 * Return value for GlobalVisHorizonKindForRel().
 */
/* (中文)GlobalVisHorizonKindForRel() 的返回值:指明某张关系(或
 * 全局场景,rel == NULL)应使用哪种水位,决定删除元组时的保守程度:
 * - VISHORIZON_SHARED : 最保守,所有库的会话都计入(共享表、recovery);
 * - VISHORIZON_CATALOG : 只计本库会话 + 槽位的 catalog xmin
 *   (系统目录、逻辑解码可访问的关系);
 * - VISHORIZON_DATA : 只计本库会话 + 槽位普通 xmin(普通用户表);
 * - VISHORIZON_TEMP : 只计本会话(临时表)。 */
typedef enum GlobalVisHorizonKind
{
	VISHORIZON_SHARED,
	VISHORIZON_CATALOG,
	VISHORIZON_DATA,
	VISHORIZON_TEMP,
} GlobalVisHorizonKind;

/*
 * Reason codes for KnownAssignedXidsCompress().
 */
/* (中文)KnownAssignedXidsCompress() 的"压缩原因"枚举:除了空间不够
 * (KAX_NO_SPACE)必须压缩外,其余情况是否压缩由启发式决定:
 * - KAX_NO_SPACE           : 数组尾部空间不足,必须立即压缩腾位;
 * - KAX_PRUNE              : 刚做过"按 xid 批量删除旧条目"的收尾压缩;
 * - KAX_TRANSACTION_END    : 事务提交/中止刚删了一批 xid 之后的
 *                            机会式压缩(每 128 次才考虑一次);
 * - KAX_STARTUP_PROCESS_IDLE : 启动进程即将进入空闲(等新 WAL),顺手
 *                            压缩(至少间隔 1 秒,避免与读者争锁)。 */
typedef enum KAXCompressReason
{
	KAX_NO_SPACE,				/* need to free up space at array end */
	KAX_PRUNE,					/* we just pruned old entries */
	KAX_TRANSACTION_END,		/* we just committed/removed some XIDs */
	KAX_STARTUP_PROCESS_IDLE,	/* startup process is about to sleep */
} KAXCompressReason;

/* (中文)指向 ProcGlobal->allProcs 的指针:共享内存中"全部 PGPROC"的
 * 数组(包含普通后端、辅助进程与 prepared 事务的占位条目,共
 * MaxBackends + NUM_AUXILIARY_PROCS + max_prepared_xacts 个)。
 * ProcArrayStruct->pgprocnos[] 里保存的正是这个数组的下标(procno);
 * 通过 GetPGProcByNumber(procno) 或 &allProcs[procno] 访问。 */
static PGPROC *allProcs;

/*
 * Cache to reduce overhead of repeated calls to TransactionIdIsInProgress()
 */
/* (中文)TransactionIdIsInProgress() 的"已确认不在运行"缓存:同一个 xid
 * 短时间内被反复询问(例如同一页面上多次可见性判断)时,直接命中缓存
 * 返回 false,避免反复加锁扫描共享内存。注意只缓存"不在运行"的结论:
 * "正在运行"的 xid 不能缓存——它随时可能结束,缓存的旧结论会变成
 * 错误的正确答案。 */
static TransactionId cachedXidIsNotInProgress = InvalidTransactionId;

/*
 * Bookkeeping for tracking emulated transactions in recovery
 */
/* (中文)热备(recovery)模式下"模拟主库运行事务"的簿记(详见文件头
 * 英文注释与本文件 KnownAssignedXids 子模块注释):
 * - KnownAssignedXids : 主库上已知已分配(因而视为仍在运行)的 xid 表,
 *   按 TransactionIdPrecedes 逻辑序排序,支持二分查找;
 * - KnownAssignedXidsValid : 与上面数组平行的"有效性"布尔数组:删除
 *   条目时只把这里置 false、不清 xid 本身,制造"空洞"以换取 O(1) 删除;
 * - latestObservedXid : 最近一个被观察到(从 WAL 记录中得知)的 xid。
 *   由于 xid 按序分配、不留空隙,凡是比它新、比某个观察到的 xid 旧的
 *   xid 都能"推断已分配",一并写入 KnownAssignedXids。初始化时它被设为
 *   SUBTRANS 已初始化到的位置(见 ProcArrayInitRecovery);
 * - standbySnapshotPendingXmin : 处于 STANDBY_SNAPSHOT_PENDING 状态时,
 *   "可能仍在运行、但我们尚未收入 KnownAssignedXids"的最大 xid
 *   (见 ProcArrayApplyRecoveryInfo)。 */

static TransactionId *KnownAssignedXids;

static bool *KnownAssignedXidsValid;

static TransactionId latestObservedXid = InvalidTransactionId;

/*
 * If we're in STANDBY_SNAPSHOT_PENDING state, standbySnapshotPendingXmin is
 * the highest xid that might still be running that we don't have in
 * KnownAssignedXids.
 */
/* (中文)处于 STANDBY_SNAPSHOT_PENDING(快照尚不完整)状态时,
 * standbySnapshotPendingXmin 是"可能仍在运行、但我们没有收进
 * KnownAssignedXids"的最大 xid;离开 PENDING 状态后恢复为
 * InvalidTransactionId。含义见上面模块级注释。 */
static TransactionId standbySnapshotPendingXmin;

/*
 * State for visibility checks on different types of relations. See struct
 * GlobalVisState for details. As shared, catalog, normal and temporary
 * relations can have different horizons, one such state exists for each.
 */
/* (中文)四份全局可见性状态(结构含义见 GlobalVisState 的中文注释):
 * 共享表(所有库共用,最保守)、系统目录、普通数据表、临时表各一份。
 * 由于跨库会话看不到对方的普通表/目录,后三者可以比共享表更激进地
 * 判定"行可删除",代价是临时表以外的三份边界需要根据关系类型选对。 */
static GlobalVisState GlobalVisSharedRels;
static GlobalVisState GlobalVisCatalogRels;
static GlobalVisState GlobalVisDataRels;
static GlobalVisState GlobalVisTempRels;

/*
 * This backend's RecentXmin at the last time the accurate xmin horizon was
 * recomputed, or InvalidTransactionId if it has not. Used to limit how many
 * times accurate horizons are recomputed. See GlobalVisTestShouldUpdate().
 */
/* (中文)最近一次用 ComputeXidHorizons() 精确重算水位时的 RecentXmin,
 * 未重算过则为 InvalidTransactionId。GlobalVisTestShouldUpdate() 靠它
 * 限制精确重算的频率:只有 RecentXmin 变化(最老快照事务已结束)时
 * 重算才有意义。 */
static TransactionId ComputeXidHorizonsResultLastXmin;

#ifdef XIDCACHE_DEBUG

/* counters for XidCache measurement */
/* (中文)(仅 XIDCACHE_DEBUG 编译时)TransactionIdIsInProgress() 各条
 * 判断路径的命中计数,用于研究 xid 状态缓存的命中率与优化方向:
 * - xc_by_recent_xmin    : 因 xid < RecentXmin 直接判定"不在运行";
 * - xc_by_known_xact     : 命中 cachedXidIsNotInProgress 缓存;
 * - xc_by_my_xact        : 是本进程自己的事务(含子事务);
 * - xc_by_latest_xid     : xid > latestCompletedXid,必然仍在运行;
 * - xc_by_main_xid       : 在 ProcGlobal->xids[] 主事务中找到;
 * - xc_by_child_xid      : 在某个后端的子事务缓存数组中找到;
 * - xc_by_known_assigned : 在 KnownAssignedXids 中找到(热备);
 * - xc_no_overflow       : 所有缓存都没溢出,无需查 pg_subtrans;
 * - xc_slow_answer       : 走了最慢的 pg_subtrans 树查找路径。 */
static long xc_by_recent_xmin = 0;
static long xc_by_known_xact = 0;
static long xc_by_my_xact = 0;
static long xc_by_latest_xid = 0;
static long xc_by_main_xid = 0;
static long xc_by_child_xid = 0;
static long xc_by_known_assigned = 0;
static long xc_no_overflow = 0;
static long xc_slow_answer = 0;

#define xc_by_recent_xmin_inc()		(xc_by_recent_xmin++)
#define xc_by_known_xact_inc()		(xc_by_known_xact++)
#define xc_by_my_xact_inc()			(xc_by_my_xact++)
#define xc_by_latest_xid_inc()		(xc_by_latest_xid++)
#define xc_by_main_xid_inc()		(xc_by_main_xid++)
#define xc_by_child_xid_inc()		(xc_by_child_xid++)
#define xc_by_known_assigned_inc()	(xc_by_known_assigned++)
#define xc_no_overflow_inc()		(xc_no_overflow++)
#define xc_slow_answer_inc()		(xc_slow_answer++)
/* (中文)(仅 XIDCACHE_DEBUG)上面各计数器的自增宏:编译时统计用。 */

static void DisplayXidCache(void);
#else							/* !XIDCACHE_DEBUG */

#define xc_by_recent_xmin_inc()		((void) 0)
#define xc_by_known_xact_inc()		((void) 0)
#define xc_by_my_xact_inc()			((void) 0)
#define xc_by_latest_xid_inc()		((void) 0)
#define xc_by_main_xid_inc()		((void) 0)
#define xc_by_child_xid_inc()		((void) 0)
#define xc_by_known_assigned_inc()	((void) 0)
#define xc_no_overflow_inc()		((void) 0)
#define xc_slow_answer_inc()		((void) 0)
#endif							/* XIDCACHE_DEBUG */
/* (中文)(未编译 XIDCACHE_DEBUG)上述自增宏全部退化为空操作,使
 * TransactionIdIsInProgress() 在正式构建里不带任何统计开销。 */

/* Primitives for KnownAssignedXids array handling for standby */
/* (中文)KnownAssignedXids 数组处理原语的内部函数原型(热备专用)。
 * 锁要求:除 KnownAssignedXidsAdd 外,各函数都要求调用方已持
 * ProcArrayLock(读取函数至少 SHARED,修改函数必须 EXCLUSIVE);
 * KnownAssignedXidsAdd 通常无需持锁,靠内存屏障与读方互锁。 */
static void KnownAssignedXidsCompress(KAXCompressReason reason, bool haveLock);
static void KnownAssignedXidsAdd(TransactionId from_xid, TransactionId to_xid,
								 bool exclusive_lock);
static bool KnownAssignedXidsSearch(TransactionId xid, bool remove);
static bool KnownAssignedXidExists(TransactionId xid);
static void KnownAssignedXidsRemove(TransactionId xid);
static void KnownAssignedXidsRemoveTree(TransactionId xid, int nsubxids,
										TransactionId *subxids);
static void KnownAssignedXidsRemovePreceding(TransactionId removeXid);
static int	KnownAssignedXidsGet(TransactionId *xarray, TransactionId xmax);
static int	KnownAssignedXidsGetAndSetXmin(TransactionId *xarray,
										   TransactionId *xmin,
										   TransactionId xmax);
static TransactionId KnownAssignedXidsGetOldestXmin(void);
static void KnownAssignedXidsDisplay(int trace_level);
static void KnownAssignedXidsReset(void);
static inline void ProcArrayEndTransactionInternal(PGPROC *proc, TransactionId latestXid);
static void ProcArrayGroupClearXid(PGPROC *proc, TransactionId latestXid);
static void MaintainLatestCompletedXid(TransactionId latestXid);
static void MaintainLatestCompletedXidRecovery(TransactionId latestXid);

static inline FullTransactionId FullXidRelativeTo(FullTransactionId rel,
												  TransactionId xid);
static void GlobalVisUpdateApply(ComputeXidHorizonsResult *horizons);
/* (中文)其余静态函数原型(自文档化,详见各自函数定义处的注释):
 * ProcArrayEndTransactionInternal —— 事务结束时实际清除 xid 的公共内联
 *   实现(要求已持 ProcArrayLock EXCLUSIVE);
 * ProcArrayGroupClearXid —— 组提交式的批量清除 xid;
 * MaintainLatestCompletedXid(Recovery) —— 推进全局 latestCompletedXid
 *   (正常/恢复两个版本);
 * FullXidRelativeTo —— 32 位 xid 参照某个 64 位基准换算成 FullTransactionId;
 * GlobalVisUpdateApply —— 把 ComputeXidHorizons 的结果灌入四份
 *   GlobalVisState。 */

/*
 * Register the shared PGPROC array during postmaster startup.
 */
/* (中文)共享内存 request 阶段回调:向共享内存子系统申报本模块需要的
 * 全部共享内存。
 *
 * 【作用】postmaster 启动时被调用一次,声明两块内存:
 * 1. 热备数据(仅 EnableHotStandby 时):KnownAssignedXids 与其有效性
 *    标志两个数组,容量为 TOTAL_MAX_CACHED_SUBXIDS;
 * 2. "Proc Array" 主结构(ProcArrayStruct),容量按 PROCARRAY_MAXPROCS
 *    个 int(procno)计算。
 * 分配出的共享内存地址直接写入本文件的两个静态指针(KnownAssignedXids
 * 与 procArray),供后续 init/attach 阶段与所有后端使用。
 *
 * 【设计思想】KnownAssignedXids 的容量取 TOTAL_MAX_CACHED_SUBXIDS =
 * (PGPROC_MAX_CACHED_SUBXIDS + 1) * PROCARRAY_MAXPROCS,与快照的
 * subxip 数组、TransactionIdIsInProgress 的工作数组保持一致:某些场景
 * 需要把整份数组互相拷贝,三处必须大小相同(见英文注释)。由于申报
 * 阶段还不知道本次运行是否会真的进入热备,只要参数 EnableHotStandby
 * 开启就无条件申报,宁可多占一点共享内存。
 *
 * 【参数】arg —— 共享内存子系统透传,本函数不使用。
 * 【返回值】无。 */
static void
ProcArrayShmemRequest(void *arg)
{
#define PROCARRAY_MAXPROCS	(MaxBackends + max_prepared_xacts)
/* (中文)进程数组的容量上限:所有后端 + prepared 事务的占位条目。
 * pgprocnos[]、ProcGlobal->xids[] 等并行数组都按它分配。 */

	/*
	 * During Hot Standby processing we have a data structure called
	 * KnownAssignedXids, created in shared memory. Local data structures are
	 * also created in various backends during GetSnapshotData(),
	 * TransactionIdIsInProgress() and GetRunningTransactionData(). All of the
	 * main structures created in those functions must be identically sized,
	 * since we may at times copy the whole of the data structures around. We
	 * refer to this size as TOTAL_MAX_CACHED_SUBXIDS.
	 *
	 * Ideally we'd only create this structure if we were actually doing hot
	 * standby in the current run, but we don't know that yet at the time
	 * shared memory is being set up.
	 */
#define TOTAL_MAX_CACHED_SUBXIDS \
	((PGPROC_MAX_CACHED_SUBXIDS + 1) * PROCARRAY_MAXPROCS)
/* (中文)热备相关的三处大型数组(共享的 KnownAssignedXids / 快照的
 * subxip / TransactionIdIsInProgress 的工作数组)统一使用的容量:每个
 * 后端最多 PGPROC_MAX_CACHED_SUBXIDS + 1 个 xid 可能同时"在运行"。
 * 三处必须同尺寸,因为某些路径会把整份数组整体拷贝(见英文注释)。 */

	if (EnableHotStandby)
	{
		ShmemRequestStruct(.name = "KnownAssignedXids",
						   .size = mul_size(sizeof(TransactionId), TOTAL_MAX_CACHED_SUBXIDS),
						   .ptr = (void **) &KnownAssignedXids,
			);

		ShmemRequestStruct(.name = "KnownAssignedXidsValid",
						   .size = mul_size(sizeof(bool), TOTAL_MAX_CACHED_SUBXIDS),
						   .ptr = (void **) &KnownAssignedXidsValid,
			);
	}

	/* Register the ProcArray shared structure */
	ShmemRequestStruct(.name = "Proc Array",
					   .size = add_size(offsetof(ProcArrayStruct, pgprocnos),
										mul_size(sizeof(int), PROCARRAY_MAXPROCS)),
					   .ptr = (void **) &procArray,
		);
}

/*
 * Initialize the shared PGPROC array during postmaster startup.
 */
/* (中文)共享内存 init 阶段回调:在 postmaster 中对进程数组做初始化。
 *
 * 【作用】把 ProcArrayStruct 的全部字段置为初值(空数组:numProcs = 0,
 * 无 KnownAssignedXids、无复制槽水位);把 xactCompletionCount 置 1;
 * 记住 allProcs 的基址。之后 ProcArrayAdd() 才会开始填充数组。
 *
 * 【设计思想】xactCompletionCount(事务完成计数)初始为 1 而不是 0,
 * 与快照中 snapXactCompletionCount 的 0 初值区分:0 表示"该快照从未
 * 参与复用判定",见 GetSnapshotDataReuse()。
 *
 * 【参数】arg —— 共享内存子系统透传,本函数不使用。
 * 【返回值】无。 */
static void
ProcArrayShmemInit(void *arg)
{
	procArray->numProcs = 0;
	procArray->maxProcs = PROCARRAY_MAXPROCS;
	procArray->maxKnownAssignedXids = TOTAL_MAX_CACHED_SUBXIDS;
	procArray->numKnownAssignedXids = 0;
	procArray->tailKnownAssignedXids = 0;
	procArray->headKnownAssignedXids = 0;
	procArray->lastOverflowedXid = InvalidTransactionId;
	procArray->replication_slot_xmin = InvalidTransactionId;
	procArray->replication_slot_catalog_xmin = InvalidTransactionId;
	TransamVariables->xactCompletionCount = 1;

	allProcs = ProcGlobal->allProcs;
}

static void
ProcArrayShmemAttach(void *arg)
{
	allProcs = ProcGlobal->allProcs;
}
/* (中文)共享内存 attach 阶段回调:postmaster 派生的其他进程(如
 * 后台工作者 bgworker)启动时,把 allProcs 重新绑定到共享的 PGPROC
 * 数组(进程私有的地址映射可能不同)。init 阶段已完成的其余初始化
 * 都是共享内存里的,无需重做。 */

/*
 * Add the specified PGPROC to the shared array.
 */
/* (中文)把一个 PGPROC 登记进共享进程数组(后端或 prepared 事务启动时)。
 *
 * 【作用】把 proc 的 procno 插入 pgprocnos[],并把它的 xid / 子事务
 * 状态 / statusFlags 同步写入 ProcGlobal 的三个并行数组,保证后续所有
 * 快照与可见性判定能看见它。数组按 procno 升序排列,插入处之后的
 * 元素全部后移,同时把它们的 pgxactoff 相应加 1。
 *
 * 【设计思想】
 * - 为什么按 procno 排序:让遍历进程数组时的内存访问尽量局部化
 *   (相邻条目往往在同一条缓存行里)。添加/删除远比遍历少,排序成本
 *   摊下来微不足道(见英文注释);
 * - 为什么同时持 ProcArrayLock 与 XidGenLock:进程数组(快照读方)
 *   与 xid 分配(GetNewTransactionId 的写方)必须互斥,防止取快照的
 *   人看到"有 xid 却不在数组里"的中间状态。释放时按相反顺序
 *   (先 XidGenLock 后 ProcArrayLock),减少"持 ProcArrayLock 等
 *   XidGenLock"的等待频率;
 * - pgxactoff 是 PGPROC 在并行数组里的下标,数组插入后所有后续
 *   条目的 pgxactoff 都要 +1,同步维护(allProcs[procno].pgxactoff)。
 *
 * 【参数】proc —— 要登记的后端 PGPROC。
 * 【返回值】无。数组已满(理论不可能)时报 FATAL "too many clients"。 */
void
ProcArrayAdd(PGPROC *proc)
{
	int			pgprocno = GetNumberFromPGProc(proc);
	ProcArrayStruct *arrayP = procArray;
	int			index;
	int			movecount;

	/* See ProcGlobal comment explaining why both locks are held */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);
	LWLockAcquire(XidGenLock, LW_EXCLUSIVE);

	if (arrayP->numProcs >= arrayP->maxProcs)
	{
		/*
		 * Oops, no room.  (This really shouldn't happen, since there is a
		 * fixed supply of PGPROC structs too, and so we should have failed
		 * earlier.)
		 */
		ereport(FATAL,
				(errcode(ERRCODE_TOO_MANY_CONNECTIONS),
				 errmsg("sorry, too many clients already")));
	}

	/*
	 * Keep the procs array sorted by (PGPROC *) so that we can utilize
	 * locality of references much better. This is useful while traversing the
	 * ProcArray because there is an increased likelihood of finding the next
	 * PGPROC structure in the cache.
	 *
	 * Since the occurrence of adding/removing a proc is much lower than the
	 * access to the ProcArray itself, the overhead should be marginal
	 */
	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			this_procno = arrayP->pgprocnos[index];

		Assert(this_procno >= 0 && this_procno < (arrayP->maxProcs + NUM_AUXILIARY_PROCS));
		Assert(allProcs[this_procno].pgxactoff == index);

		/* If we have found our right position in the array, break */
		if (this_procno > pgprocno)
			break;
	}

	movecount = arrayP->numProcs - index;
	memmove(&arrayP->pgprocnos[index + 1],
			&arrayP->pgprocnos[index],
			movecount * sizeof(*arrayP->pgprocnos));
	memmove(&ProcGlobal->xids[index + 1],
			&ProcGlobal->xids[index],
			movecount * sizeof(*ProcGlobal->xids));
	memmove(&ProcGlobal->subxidStates[index + 1],
			&ProcGlobal->subxidStates[index],
			movecount * sizeof(*ProcGlobal->subxidStates));
	memmove(&ProcGlobal->statusFlags[index + 1],
			&ProcGlobal->statusFlags[index],
			movecount * sizeof(*ProcGlobal->statusFlags));

	arrayP->pgprocnos[index] = GetNumberFromPGProc(proc);
	proc->pgxactoff = index;
	ProcGlobal->xids[index] = proc->xid;
	ProcGlobal->subxidStates[index] = proc->subxidStatus;
	ProcGlobal->statusFlags[index] = proc->statusFlags;

	arrayP->numProcs++;

	/* adjust pgxactoff for all following PGPROCs */
	index++;
	for (; index < arrayP->numProcs; index++)
	{
		int			procno = arrayP->pgprocnos[index];

		Assert(procno >= 0 && procno < (arrayP->maxProcs + NUM_AUXILIARY_PROCS));
		Assert(allProcs[procno].pgxactoff == index - 1);

		allProcs[procno].pgxactoff = index;
	}

	/*
	 * Release in reversed acquisition order, to reduce frequency of having to
	 * wait for XidGenLock while holding ProcArrayLock.
	 */
	LWLockRelease(XidGenLock);
	LWLockRelease(ProcArrayLock);
}

/*
 * Remove the specified PGPROC from the shared array.
 *
 * When latestXid is a valid XID, we are removing a live 2PC gxact from the
 * array, and thus causing it to appear as "not running" anymore.  In this
 * case we must advance latestCompletedXid.  (This is essentially the same
 * as ProcArrayEndTransaction followed by removal of the PGPROC, but we take
 * the ProcArrayLock only once, and don't damage the content of the PGPROC;
 * twophase.c depends on the latter.)
 */
/* (中文)把指定的 PGPROC 从共享进程数组中移除(后端退出或 prepared
 * 事务结束)。
 *
 * 【作用】按 pgxactoff 从四个并行数组中删除该条目,后续条目前移并
 * 修正 pgxactoff。若传入了合法的 latestXid(移除"活着的"prepared
 * 事务时),说明此刻必须宣告该事务不再运行,于是像
 * ProcArrayEndTransaction 那样推进 latestCompletedXid 与
 * xactCompletionCount,但不清 PGPROC 内容——twophase.c 还依赖
 * PGPROC 里的 xid 等字段做后续清理。
 *
 * 【设计思想】
 * - 同时持 ProcArrayLock(EXCLUSIVE)与 XidGenLock(EXCLUSIVE),理由
 *   与 ProcArrayAdd 相同:移除条目会让"正在运行的 xid 集合"缩小,
 *   必须对取快照者原子可见;
 * - 数组保持 procno 升序,删除即前移,与 ProcArrayAdd 对称;
 * - XIDCACHE_DEBUG 构建时,普通后端(pid != 0)退出前打印 XID 缓存
 *   统计,prepared 事务结束不算"后端退出",不打印。
 *
 * 【参数】
 *   proc      —— 要移除的 PGPROC;
 *   latestXid —— 若是"活着的"2PC 事务被移除,传它的最新 xid(用于
 *                推进 latestCompletedXid);否则 InvalidTransactionId。
 * 【返回值】无。 */
void
ProcArrayRemove(PGPROC *proc, TransactionId latestXid)
{
	ProcArrayStruct *arrayP = procArray;
	int			myoff;
	int			movecount;

#ifdef XIDCACHE_DEBUG
	/* dump stats at backend shutdown, but not prepared-xact end */
	if (proc->pid != 0)
		DisplayXidCache();
#endif

	/* See ProcGlobal comment explaining why both locks are held */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);
	LWLockAcquire(XidGenLock, LW_EXCLUSIVE);

	myoff = proc->pgxactoff;

	Assert(myoff >= 0 && myoff < arrayP->numProcs);
	Assert(ProcGlobal->allProcs[arrayP->pgprocnos[myoff]].pgxactoff == myoff);

	if (TransactionIdIsValid(latestXid))
	{
		Assert(TransactionIdIsValid(ProcGlobal->xids[myoff]));

		/* Advance global latestCompletedXid while holding the lock */
		MaintainLatestCompletedXid(latestXid);

		/* Same with xactCompletionCount  */
		TransamVariables->xactCompletionCount++;

		ProcGlobal->xids[myoff] = InvalidTransactionId;
		ProcGlobal->subxidStates[myoff].overflowed = false;
		ProcGlobal->subxidStates[myoff].count = 0;
	}
	else
	{
		/* Shouldn't be trying to remove a live transaction here */
		Assert(!TransactionIdIsValid(ProcGlobal->xids[myoff]));
	}

	Assert(!TransactionIdIsValid(ProcGlobal->xids[myoff]));
	Assert(ProcGlobal->subxidStates[myoff].count == 0);
	Assert(ProcGlobal->subxidStates[myoff].overflowed == false);

	ProcGlobal->statusFlags[myoff] = 0;

	/* Keep the PGPROC array sorted. See notes above */
	movecount = arrayP->numProcs - myoff - 1;
	memmove(&arrayP->pgprocnos[myoff],
			&arrayP->pgprocnos[myoff + 1],
			movecount * sizeof(*arrayP->pgprocnos));
	memmove(&ProcGlobal->xids[myoff],
			&ProcGlobal->xids[myoff + 1],
			movecount * sizeof(*ProcGlobal->xids));
	memmove(&ProcGlobal->subxidStates[myoff],
			&ProcGlobal->subxidStates[myoff + 1],
			movecount * sizeof(*ProcGlobal->subxidStates));
	memmove(&ProcGlobal->statusFlags[myoff],
			&ProcGlobal->statusFlags[myoff + 1],
			movecount * sizeof(*ProcGlobal->statusFlags));

	arrayP->pgprocnos[arrayP->numProcs - 1] = -1;	/* for debugging */
	arrayP->numProcs--;

	/*
	 * Adjust pgxactoff of following procs for removed PGPROC (note that
	 * numProcs already has been decremented).
	 */
	for (int index = myoff; index < arrayP->numProcs; index++)
	{
		int			procno = arrayP->pgprocnos[index];

		Assert(procno >= 0 && procno < (arrayP->maxProcs + NUM_AUXILIARY_PROCS));
		Assert(allProcs[procno].pgxactoff - 1 == index);

		allProcs[procno].pgxactoff = index;
	}

	/*
	 * Release in reversed acquisition order, to reduce frequency of having to
	 * wait for XidGenLock while holding ProcArrayLock.
	 */
	LWLockRelease(XidGenLock);
	LWLockRelease(ProcArrayLock);
}


/*
 * ProcArrayEndTransaction -- mark a transaction as no longer running
 *
 * This is used interchangeably for commit and abort cases.  The transaction
 * commit/abort must already be reported to WAL and pg_xact.
 *
 * proc is currently always MyProc, but we pass it explicitly for flexibility.
 * latestXid is the latest Xid among the transaction's main XID and
 * subtransactions, or InvalidTransactionId if it has no XID.  (We must ask
 * the caller to pass latestXid, instead of computing it from the PGPROC's
 * contents, because the subxid information in the PGPROC might be
 * incomplete.)
 */
/* (中文)事务结束时调用:把事务从"正在运行"集合中移除(提交与中止
 * 共用此函数)。
 *
 * 【作用】清除本进程在 ProcArray 中宣告的 xid、xmin、子事务缓存等,
 * 并推进全局 latestCompletedXid 与 xactCompletionCount,使所有后来
 * 构造的快照都能看到该事务已完成。事务的 commit/abort 必须先写进
 * WAL 与 pg_xact,本函数只是"宣告结束"。
 *
 * 【设计思想】
 * - 为什么必须持锁清 xid:取快照的人(持 SHARED 锁)必须看到"正在
 *   运行集合"的完整变迁。若不加锁清除,可能出现快照把已提交事务
 *   当作还在运行(或反之)的窗口,详见 access/transam/README;
 * - 无 xid 的事务(只读事务)不需要加锁:它不在任何人的快照里,
 *   清了 xmin 只会让全局 xmin 的估计略不精确,无碍正确性;
 * - 性能:提交路径热点竞争 ProcArrayLock,因此先试"条件加锁"
 *   (LWLockConditionalAcquire):立刻拿到就自己清(走
 *   ProcArrayEndTransactionInternal);拿不到就加入"组清除"队列
 *   由带头人统一处理(ProcArrayGroupClearXid),避免把锁传来传去;
 * - statusFlags 的 VACUUM 状态位与 xid/xmin 必须同时清除,否则清理
 *   进程会误判该后端的 xmin 是否要计入水位;无锁路径下只在这个位
 *   置必要时才单独取锁,避免弄脏共享缓存行。
 *
 * 【参数】
 *   proc      —— 本事务的 PGPROC(当前调用总是 MyProc,显式传参是为
 *                灵活性与组清除共用);
 *   latestXid —— 本事务主 xid 与所有子事务中最大的一个;没有 xid
 *                则为 InvalidTransactionId。必须由调用方传入而不是
 *                从 PGPROC 里读:PGPROC 的子事务缓存可能不完整。
 * 【返回值】无。 */
void
ProcArrayEndTransaction(PGPROC *proc, TransactionId latestXid)
{
	if (TransactionIdIsValid(latestXid))
	{
		/*
		 * We must lock ProcArrayLock while clearing our advertised XID, so
		 * that we do not exit the set of "running" transactions while someone
		 * else is taking a snapshot.  See discussion in
		 * src/backend/access/transam/README.
		 */
		Assert(TransactionIdIsValid(proc->xid));

		/*
		 * If we can immediately acquire ProcArrayLock, we clear our own XID
		 * and release the lock.  If not, use group XID clearing to improve
		 * efficiency.
		 */
		if (LWLockConditionalAcquire(ProcArrayLock, LW_EXCLUSIVE))
		{
			ProcArrayEndTransactionInternal(proc, latestXid);
			LWLockRelease(ProcArrayLock);
		}
		else
			ProcArrayGroupClearXid(proc, latestXid);
	}
	else
	{
		/*
		 * If we have no XID, we don't need to lock, since we won't affect
		 * anyone else's calculation of a snapshot.  We might change their
		 * estimate of global xmin, but that's OK.
		 */
		Assert(!TransactionIdIsValid(proc->xid));
		Assert(proc->subxidStatus.count == 0);
		Assert(!proc->subxidStatus.overflowed);

		proc->vxid.lxid = InvalidLocalTransactionId;
		proc->xmin = InvalidTransactionId;

		/* be sure this is cleared in abort */
		proc->delayChkptFlags = 0;

		/* must be cleared with xid/xmin: */
		/* avoid unnecessarily dirtying shared cachelines */
		if (proc->statusFlags & PROC_VACUUM_STATE_MASK)
		{
			Assert(!LWLockHeldByMe(ProcArrayLock));
			LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);
			Assert(proc->statusFlags == ProcGlobal->statusFlags[proc->pgxactoff]);
			proc->statusFlags &= ~PROC_VACUUM_STATE_MASK;
			ProcGlobal->statusFlags[proc->pgxactoff] = proc->statusFlags;
			LWLockRelease(ProcArrayLock);
		}
	}
}

/*
 * Mark a write transaction as no longer running.
 *
 * We don't do any locking here; caller must handle that.
 */
/* (中文)事务结束时的实际清除动作(ProcArrayEndTransaction 与组清除
 * 带头人共用的内联实现)。
 *
 * 【作用】在已持锁的前提下,把 proc 的 xid / xmin / vxid / 子事务缓存
 * 全部清零,清除 VACUUM 状态位,并推进 latestCompletedXid 与
 * xactCompletionCount。
 *
 * 【设计思想】
 * - 调用者必须已持 ProcArrayLock EXCLUSIVE(函数内有 Assert):清除
 *   别人的 xid 改变的是整个"正在运行集合",只能排他;
 * - 清 statusFlags 的 PROC_VACUUM_STATE_MASK 位与 xid/xmin 同步进行,
 *   且只在确实置位时才写,避免不必要的共享缓存行弄脏;
 * - 子事务缓存一并清零(它的内容随事务结束全部失效);
 * - MaintainLatestCompletedXid 与 xactCompletionCount 的递增都必须在
 *   持锁期间完成,使"事务完成"这一事件对读取者原子可见。
 *
 * 【参数】
 *   proc      —— 要清除的 PGPROC(可以是别人的,组清除时由带头人代劳);
 *   latestXid —— 该事务的最新 xid,用于推进 latestCompletedXid。
 * 【返回值】无。 */
static inline void
ProcArrayEndTransactionInternal(PGPROC *proc, TransactionId latestXid)
{
	int			pgxactoff = proc->pgxactoff;

	/*
	 * Note: we need exclusive lock here because we're going to change other
	 * processes' PGPROC entries.
	 */
	Assert(LWLockHeldByMeInMode(ProcArrayLock, LW_EXCLUSIVE));
	Assert(TransactionIdIsValid(ProcGlobal->xids[pgxactoff]));
	Assert(ProcGlobal->xids[pgxactoff] == proc->xid);

	ProcGlobal->xids[pgxactoff] = InvalidTransactionId;
	proc->xid = InvalidTransactionId;
	proc->vxid.lxid = InvalidLocalTransactionId;
	proc->xmin = InvalidTransactionId;

	/* be sure this is cleared in abort */
	proc->delayChkptFlags = 0;

	/* must be cleared with xid/xmin: */
	/* avoid unnecessarily dirtying shared cachelines */
	if (proc->statusFlags & PROC_VACUUM_STATE_MASK)
	{
		proc->statusFlags &= ~PROC_VACUUM_STATE_MASK;
		ProcGlobal->statusFlags[proc->pgxactoff] = proc->statusFlags;
	}

	/* Clear the subtransaction-XID cache too while holding the lock */
	Assert(ProcGlobal->subxidStates[pgxactoff].count == proc->subxidStatus.count &&
		   ProcGlobal->subxidStates[pgxactoff].overflowed == proc->subxidStatus.overflowed);
	if (proc->subxidStatus.count > 0 || proc->subxidStatus.overflowed)
	{
		ProcGlobal->subxidStates[pgxactoff].count = 0;
		ProcGlobal->subxidStates[pgxactoff].overflowed = false;
		proc->subxidStatus.count = 0;
		proc->subxidStatus.overflowed = false;
	}

	/* Also advance global latestCompletedXid while holding the lock */
	MaintainLatestCompletedXid(latestXid);

	/* Same with xactCompletionCount  */
	TransamVariables->xactCompletionCount++;
}

/*
 * ProcArrayGroupClearXid -- group XID clearing
 *
 * When we cannot immediately acquire ProcArrayLock in exclusive mode at
 * commit time, add ourselves to a list of processes that need their XIDs
 * cleared.  The first process to add itself to the list will acquire
 * ProcArrayLock in exclusive mode and perform ProcArrayEndTransactionInternal
 * on behalf of all group members.  This avoids a great deal of contention
 * around ProcArrayLock when many processes are trying to commit at once,
 * since the lock need not be repeatedly handed off from one committing
 * process to the next.
 */
/* (中文)组 XID 清除(组提交优化):拿不到 ProcArrayLock 时的备用提交路径。
 *
 * 【作用】提交时若条件加锁失败,把自己挂进 ProcGlobal->procArrayGroupFirst
 * 指向的无锁单向链表,然后:
 * - 若链上已有其他进程(nextidx != INVALID_PROC_NUMBER),说明已有
 *   "带头人"在干活:在自己的信号量上睡眠,等带头人把自己的 xid 清掉
 *   后再唤醒;
 * - 若是第一个入链的进程(带头人):一次取得 EXCLUSIVE 锁,遍历整条链,
 *   替所有成员调用 ProcArrayEndTransactionInternal 清除 xid,然后释放
 *   锁,最后逐个唤醒成员。
 *
 * 【设计思想】
 * - 为什么值得这么做:高并发提交时,每个进程都试图独占 ProcArrayLock,
 *   锁会在提交进程间反复交接,持有时间被"排队-获得-释放"的开销放大。
 *   组清除把 N 次加锁合并成 1 次,大幅降低争用(见英文注释);
 * - 链表用原子 CAS 维护(procArrayGroupNext / procArrayGroupFirst),
 *   入链完全无锁;取出链头用 pg_atomic_exchange 一次交换为空,避免
 *   逐个 pop 造成的 ABA 问题(见英文注释);
 * - 唤醒放在释放锁之后:唤醒他人要发信号(系统调用),比锁内的普通
 *   内存写慢得多,不应占用锁持有时间;
 * - 睡眠期间可能有额外的信号到达(extraWaits 计数),醒来后要按计数
 *   补发信号量,保持信号量计数平衡;
 * - 内存序:带头人写 xid 清除结果后,用 pg_write_barrier 再置成员
 *   的 procArrayGroupMember = false,保证成员醒来看到的清除结果
 *   一定是完整的。
 *
 * 【参数】
 *   proc      —— 本进程 PGPROC;
 *   latestXid —— 本事务最新 xid(记入 procArrayGroupMemberXid,由带头人
 *                传给 ProcArrayEndTransactionInternal)。
 * 【返回值】无。 */
static void
ProcArrayGroupClearXid(PGPROC *proc, TransactionId latestXid)
{
	int			pgprocno = GetNumberFromPGProc(proc);
	PROC_HDR   *procglobal = ProcGlobal;
	uint32		nextidx;
	uint32		wakeidx;

	/* We should definitely have an XID to clear. */
	Assert(TransactionIdIsValid(proc->xid));

	/* Add ourselves to the list of processes needing a group XID clear. */
	proc->procArrayGroupMember = true;
	proc->procArrayGroupMemberXid = latestXid;
	nextidx = pg_atomic_read_u32(&procglobal->procArrayGroupFirst);
	while (true)
	{
		pg_atomic_write_u32(&proc->procArrayGroupNext, nextidx);

		if (pg_atomic_compare_exchange_u32(&procglobal->procArrayGroupFirst,
										   &nextidx,
										   (uint32) pgprocno))
			break;
	}

	/*
	 * If the list was not empty, the leader will clear our XID.  It is
	 * impossible to have followers without a leader because the first process
	 * that has added itself to the list will always have nextidx as
	 * INVALID_PROC_NUMBER.
	 */
	if (nextidx != INVALID_PROC_NUMBER)
	{
		int			extraWaits = 0;

		/* Sleep until the leader clears our XID. */
		pgstat_report_wait_start(WAIT_EVENT_PROCARRAY_GROUP_UPDATE);
		for (;;)
		{
			/* acts as a read barrier */
			PGSemaphoreLock(proc->sem);
			if (!proc->procArrayGroupMember)
				break;
			extraWaits++;
		}
		pgstat_report_wait_end();

		Assert(pg_atomic_read_u32(&proc->procArrayGroupNext) == INVALID_PROC_NUMBER);

		/* Fix semaphore count for any absorbed wakeups */
		while (extraWaits-- > 0)
			PGSemaphoreUnlock(proc->sem);
		return;
	}

	/* We are the leader.  Acquire the lock on behalf of everyone. */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	/*
	 * Now that we've got the lock, clear the list of processes waiting for
	 * group XID clearing, saving a pointer to the head of the list.  Trying
	 * to pop elements one at a time could lead to an ABA problem.
	 */
	nextidx = pg_atomic_exchange_u32(&procglobal->procArrayGroupFirst,
									 INVALID_PROC_NUMBER);

	/* Remember head of list so we can perform wakeups after dropping lock. */
	wakeidx = nextidx;

	/* Walk the list and clear all XIDs. */
	while (nextidx != INVALID_PROC_NUMBER)
	{
		PGPROC	   *nextproc = &allProcs[nextidx];

		ProcArrayEndTransactionInternal(nextproc, nextproc->procArrayGroupMemberXid);

		/* Move to next proc in list. */
		nextidx = pg_atomic_read_u32(&nextproc->procArrayGroupNext);
	}

	/* We're done with the lock now. */
	LWLockRelease(ProcArrayLock);

	/*
	 * Now that we've released the lock, go back and wake everybody up.  We
	 * don't do this under the lock so as to keep lock hold times to a
	 * minimum.  The system calls we need to perform to wake other processes
	 * up are probably much slower than the simple memory writes we did while
	 * holding the lock.
	 */
	while (wakeidx != INVALID_PROC_NUMBER)
	{
		PGPROC	   *nextproc = &allProcs[wakeidx];

		wakeidx = pg_atomic_read_u32(&nextproc->procArrayGroupNext);
		pg_atomic_write_u32(&nextproc->procArrayGroupNext, INVALID_PROC_NUMBER);

		/* ensure all previous writes are visible before follower continues. */
		pg_write_barrier();

		nextproc->procArrayGroupMember = false;

		if (nextproc != MyProc)
			PGSemaphoreUnlock(nextproc->sem);
	}
}

/*
 * ProcArrayClearTransaction -- clear the transaction fields
 *
 * This is used after successfully preparing a 2-phase transaction.  We are
 * not actually reporting the transaction's XID as no longer running --- it
 * will still appear as running because the 2PC's gxact is in the ProcArray
 * too.  We just have to clear out our own PGPROC.
 */
/* (中文)2PC 事务 PREPARE 成功后的清理:清空本后端自己的 PGPROC 事务
 * 字段,但"事务仍在运行"的宣告由已插入的 gxact(prepared 事务占位
 * PGPROC)继续承担。
 *
 * 【作用】PREPARE 时把 ProcGlobal->xids[pgxactoff] 与本进程的
 * xid/xmin/vxid/子事务缓存清掉,并递增 xactCompletionCount。此时
 * 进程数组中已插入同 xid 的 gxact,所以从快照角度看事务仍然"在运行",
 * 本函数不会改变任何人的可见性视图。
 *
 * 【设计思想】
 * - 为什么递增 xactCompletionCount:GetSnapshotData() 构造快照时会把
 *   自己的 xid 排除在 xip 之外;若不递增计数,PREPARE 前后构造的快照
 *   内容相同,可能被 GetSnapshotDataReuse() 判定"可以复用",而复用的
 *   旧快照没把 prepared 事务算作运行,导致可见性错误(见英文注释);
 * - 锁级别:理论上有"清除动作本身"用 SHARED 锁就够,但 xactCompletionCount
 *   的递增要求 EXCLUSIVE,故整体取 EXCLUSIVE(把 2PC 提交后紧跟着的
 *   ProcArrayRemove 合并考虑也许是未来的优化方向)。
 *
 * 【参数】proc —— 本后端 PGPROC。
 * 【返回值】无。 */
void
ProcArrayClearTransaction(PGPROC *proc)
{
	int			pgxactoff;

	/*
	 * Currently we need to lock ProcArrayLock exclusively here, as we
	 * increment xactCompletionCount below. We also need it at least in shared
	 * mode for pgproc->pgxactoff to stay the same below.
	 *
	 * We could however, as this action does not actually change anyone's view
	 * of the set of running XIDs (our entry is duplicate with the gxact that
	 * has already been inserted into the ProcArray), lower the lock level to
	 * shared if we were to make xactCompletionCount an atomic variable. But
	 * that doesn't seem worth it currently, as a 2PC commit is heavyweight
	 * enough for this not to be the bottleneck.  If it ever becomes a
	 * bottleneck it may also be worth considering to combine this with the
	 * subsequent ProcArrayRemove()
	 */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	pgxactoff = proc->pgxactoff;

	ProcGlobal->xids[pgxactoff] = InvalidTransactionId;
	proc->xid = InvalidTransactionId;

	proc->vxid.lxid = InvalidLocalTransactionId;
	proc->xmin = InvalidTransactionId;

	Assert(!(proc->statusFlags & PROC_VACUUM_STATE_MASK));
	Assert(!proc->delayChkptFlags);

	/*
	 * Need to increment completion count even though transaction hasn't
	 * really committed yet. The reason for that is that GetSnapshotData()
	 * omits the xid of the current transaction, thus without the increment we
	 * otherwise could end up reusing the snapshot later. Which would be bad,
	 * because it might not count the prepared transaction as running.
	 */
	TransamVariables->xactCompletionCount++;

	/* Clear the subtransaction-XID cache too */
	Assert(ProcGlobal->subxidStates[pgxactoff].count == proc->subxidStatus.count &&
		   ProcGlobal->subxidStates[pgxactoff].overflowed == proc->subxidStatus.overflowed);
	if (proc->subxidStatus.count > 0 || proc->subxidStatus.overflowed)
	{
		ProcGlobal->subxidStates[pgxactoff].count = 0;
		ProcGlobal->subxidStates[pgxactoff].overflowed = false;
		proc->subxidStatus.count = 0;
		proc->subxidStatus.overflowed = false;
	}

	LWLockRelease(ProcArrayLock);
}

/*
 * Update TransamVariables->latestCompletedXid to point to latestXid if
 * currently older.
 */
/* (中文)推进全局"最新已完成事务"水位 latestCompletedXid(正常运行时
 * 版本)。
 *
 * 【作用】若 latestXid 比当前 latestCompletedXid 新,则把
 * latestCompletedXid 更新为 latestXid。所有快照的 xmax 都取自它
 * (xmax = latestCompletedXid + 1),因此它必须"单调不后退"且在任何
 * 事务完成后立即推进。
 *
 * 【设计思想】
 * - 为什么必须持锁调用:latestCompletedXid 与"正在运行集合"必须
 *   一致推进,否则取快照者可能看到 xid 已经"完成"却还留在运行集合
 *   中(或反过来)。函数内有 Assert(LWLockHeldByMe(ProcArrayLock));
 * - 64 位换算:用 FullXidRelativeTo(以当前 latestCompletedXid 为基准)
 *   把 32 位 latestXid 还原成 FullTransactionId,避免事务 id 回绕导致
 *   错误(这里的最新值必然在 32 位空间内处于当前基准附近)。
 *
 * 【参数】latestXid —— 刚完成事务的最新 xid。
 * 【返回值】无。 */
static void
MaintainLatestCompletedXid(TransactionId latestXid)
{
	FullTransactionId cur_latest = TransamVariables->latestCompletedXid;

	Assert(FullTransactionIdIsValid(cur_latest));
	Assert(!RecoveryInProgress());
	Assert(LWLockHeldByMe(ProcArrayLock));

	if (TransactionIdPrecedes(XidFromFullTransactionId(cur_latest), latestXid))
	{
		TransamVariables->latestCompletedXid =
			FullXidRelativeTo(cur_latest, latestXid);
	}

	Assert(IsBootstrapProcessingMode() ||
		   FullTransactionIdIsNormal(TransamVariables->latestCompletedXid));
}

/*
 * Same as MaintainLatestCompletedXid, except for use during WAL replay.
 */
/* (中文)推进 latestCompletedXid 的恢复(recovery)版本:在备机重放
 * WAL 期间由 startup 进程调用。
 *
 * 【作用】与 MaintainLatestCompletedXid 语义相同(单调推进到 latestXid),
 * 但基准不同:正常运行时基准是"当前的 latestCompletedXid"(恒有效),
 * 恢复期间该值可能尚未初始化,改用 TransamVariables->nextXid 作基准。
 *
 * 【设计思想】
 * - 恢复期间只有 startup 进程写 nextXid,且它自己就是本函数的调用者,
 *   无需加锁读 nextXid(函数内只有 ProcArrayLock 的 Assert,因为调用方
 *   承诺持锁——恢复期间推进该值同样要与 KnownAssignedXids 的删除
 *   原子一致);
 * - FullTransactionId 还原依然用 FullXidRelativeTo,基准换成 nextXid
 *   后得到的仍是正确的 64 位表示。
 *
 * 【参数】latestXid —— 从 WAL 记录中得知的最新完成事务 xid。
 * 【返回值】无。 */
static void
MaintainLatestCompletedXidRecovery(TransactionId latestXid)
{
	FullTransactionId cur_latest = TransamVariables->latestCompletedXid;
	FullTransactionId rel;

	Assert(AmStartupProcess() || !IsUnderPostmaster);
	Assert(LWLockHeldByMe(ProcArrayLock));

	/*
	 * Need a FullTransactionId to compare latestXid with. Can't rely on
	 * latestCompletedXid to be initialized in recovery. But in recovery it's
	 * safe to access nextXid without a lock for the startup process.
	 */
	rel = TransamVariables->nextXid;
	Assert(FullTransactionIdIsValid(TransamVariables->nextXid));

	if (!FullTransactionIdIsValid(cur_latest) ||
		TransactionIdPrecedes(XidFromFullTransactionId(cur_latest), latestXid))
	{
		TransamVariables->latestCompletedXid =
			FullXidRelativeTo(rel, latestXid);
	}

	Assert(FullTransactionIdIsNormal(TransamVariables->latestCompletedXid));
}

/*
 * ProcArrayInitRecovery -- initialize recovery xid mgmt environment
 *
 * Remember up to where the startup process initialized the CLOG and subtrans
 * so we can ensure it's initialized gaplessly up to the point where necessary
 * while in recovery.
 */
/* (中文)初始化恢复期的 xid 管理环境。
 *
 * 【作用】记录 startup 进程把 CLOG 与 pg_subtrans 初始化到了哪个 xid
 * (initializedUptoXID),作为 latestObservedXid 的起点。此后
 * RecordKnownAssignedTransactionIds() 与 ProcArrayApplyRecoveryInfo()
 * 会从这一点开始"无缝隙"地补齐 pg_subtrans 的扩展,保证任何时刻
 * 需要查询的父子事务链都可用。
 *
 * 【设计思想】latestObservedXid 的含义是"已知已分配的最大 xid"。
 * 把它先退一格(TransactionIdRetreat)再交给后续逻辑:后续代码总是
 * "先推进一步、再检查",这样能干净地处理"下一个待观察 xid"的边界。
 *
 * 【参数】initializedUptoXID —— pg_subtrans 已初始化到的最远 xid。
 * 【返回值】无。 */
void
ProcArrayInitRecovery(TransactionId initializedUptoXID)
{
	Assert(standbyState == STANDBY_INITIALIZED);
	Assert(TransactionIdIsNormal(initializedUptoXID));

	/*
	 * we set latestObservedXid to the xid SUBTRANS has been initialized up
	 * to, so we can extend it from that point onwards in
	 * RecordKnownAssignedTransactionIds, and when we get consistent in
	 * ProcArrayApplyRecoveryInfo().
	 */
	latestObservedXid = initializedUptoXID;
	TransactionIdRetreat(latestObservedXid);
}

/*
 * ProcArrayApplyRecoveryInfo -- apply recovery info about xids
 *
 * Takes us through 3 states: Initialized, Pending and Ready.
 * Normal case is to go all the way to Ready straight away, though there
 * are atypical cases where we need to take it in steps.
 *
 * Use the data about running transactions on the primary to create the initial
 * state of KnownAssignedXids. We also use these records to regularly prune
 * KnownAssignedXids because we know it is possible that some transactions
 * with FATAL errors fail to write abort records, which could cause eventual
 * overflow.
 *
 * See comments for LogStandbySnapshot().
 */
/* (中文)应用主库传来的"运行事务快照"(XLOG_RUNNING_XACTS),初始化
 * 备机的 KnownAssignedXids,并推进 standbyState 状态机。
 *
 * 【作用】备机一致性恢复开始时调用,可能多次(每次收到新的
 * RUNNING_XACTS 记录)。处理步骤:
 * 1. 用快照的 oldestRunningXid 修剪过期的 KnownAssignedXids 与锁
 *    (防溢出:主库可能因崩溃没写 abort 记录,遗留的 xid 需要清掉);
 * 2. 推进 nextXid(StandbyReleaseOldLocks 需要它来识别 2PC 事务);
 * 3. 把快照里"尚未完成"的 xid 排序后全部装入 KnownAssignedXids
 *    (去重,跳过已在 clog 中完成的事务);
 * 4. 把 pg_subtrans 无缝隙扩展到 nextXid - 1;
 * 5. 根据快照是否溢出设置 standbyState:
 *    - 完整快照 -> STANDBY_SNAPSHOT_READY(快照立即可用);
 *    - 快照缺失子事务(SUBXIDS_MISSING) -> STANDBY_SNAPSHOT_PENDING:
 *      记下 standbySnapshotPendingXmin = 已知最晚 xid,等后续
 *      RUNNING_XACTS 的 oldestRunningXid 超过它,说明丢失的信息已被
 *      完全取代,才转为 READY(见英文注释里的判定逻辑)。
 *
 * 【设计思想】
 * - KnownAssignedXids 必须有序:内部用二分查找,所以先 qsort;
 * - 为什么不此时建 pg_subtrans 父子链:未溢出时全部子事务都在快照里,
 *   不需要;溢出时信息本来就不全,建了也白建。链的建立留给后续
 *   XLOG_XACT_ASSIGNMENT 记录(ProcArrayApplyXidAssignment);
 * - latestCompletedXid 可能已比快照里记录的新(快照生成与落盘之间有
 *   提交发生),所以用"取较大者"语义的 MaintainLatestCompletedXidRecovery。
 *
 * 【参数】running —— 主库日志的快照数据(见 RunningTransactionsData)。
 * 【返回值】无。 */
void
ProcArrayApplyRecoveryInfo(RunningTransactions running)
{
	TransactionId *xids;
	TransactionId advanceNextXid;
	int			nxids;
	int			i;

	Assert(standbyState >= STANDBY_INITIALIZED);
	Assert(TransactionIdIsValid(running->nextXid));
	Assert(TransactionIdIsValid(running->oldestRunningXid));
	Assert(TransactionIdIsNormal(running->latestCompletedXid));

	/*
	 * Remove stale transactions, if any.
	 */
	ExpireOldKnownAssignedTransactionIds(running->oldestRunningXid);

	/*
	 * Adjust TransamVariables->nextXid before StandbyReleaseOldLocks(),
	 * because we will need it up to date for accessing two-phase transactions
	 * in StandbyReleaseOldLocks().
	 */
	advanceNextXid = running->nextXid;
	TransactionIdRetreat(advanceNextXid);
	AdvanceNextFullTransactionIdPastXid(advanceNextXid);
	Assert(FullTransactionIdIsValid(TransamVariables->nextXid));

	/*
	 * Remove stale locks, if any.
	 */
	StandbyReleaseOldLocks(running->oldestRunningXid);

	/*
	 * If our snapshot is already valid, nothing else to do...
	 */
	if (standbyState == STANDBY_SNAPSHOT_READY)
		return;

	/*
	 * If our initial RunningTransactionsData had an overflowed snapshot then
	 * we knew we were missing some subxids from our snapshot. If we continue
	 * to see overflowed snapshots then we might never be able to start up, so
	 * we make another test to see if our snapshot is now valid. We know that
	 * the missing subxids are equal to or earlier than nextXid. After we
	 * initialise we continue to apply changes during recovery, so once the
	 * oldestRunningXid is later than the nextXid from the initial snapshot we
	 * know that we no longer have missing information and can mark the
	 * snapshot as valid.
	 */
	if (standbyState == STANDBY_SNAPSHOT_PENDING)
	{
		/*
		 * If the snapshot isn't overflowed or if its empty we can reset our
		 * pending state and use this snapshot instead.
		 */
		if (running->subxid_status != SUBXIDS_MISSING || running->xcnt == 0)
		{
			/*
			 * If we have already collected known assigned xids, we need to
			 * throw them away before we apply the recovery snapshot.
			 */
			KnownAssignedXidsReset();
			standbyState = STANDBY_INITIALIZED;
		}
		else
		{
			if (TransactionIdPrecedes(standbySnapshotPendingXmin,
									  running->oldestRunningXid))
			{
				standbyState = STANDBY_SNAPSHOT_READY;
				elog(DEBUG1,
					 "recovery snapshots are now enabled");
			}
			else
				elog(DEBUG1,
					 "recovery snapshot waiting for non-overflowed snapshot or "
					 "until oldest active xid on standby is at least %u (now %u)",
					 standbySnapshotPendingXmin,
					 running->oldestRunningXid);
			return;
		}
	}

	Assert(standbyState == STANDBY_INITIALIZED);

	/*
	 * NB: this can be reached at least twice, so make sure new code can deal
	 * with that.
	 */

	/*
	 * Nobody else is running yet, but take locks anyhow
	 */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	/*
	 * KnownAssignedXids is sorted so we cannot just add the xids, we have to
	 * sort them first.
	 *
	 * Some of the new xids are top-level xids and some are subtransactions.
	 * We don't call SubTransSetParent because it doesn't matter yet. If we
	 * aren't overflowed then all xids will fit in snapshot and so we don't
	 * need subtrans. If we later overflow, an xid assignment record will add
	 * xids to subtrans. If RunningTransactionsData is overflowed then we
	 * don't have enough information to correctly update subtrans anyway.
	 */

	/*
	 * Allocate a temporary array to avoid modifying the array passed as
	 * argument.
	 */
	xids = palloc_array(TransactionId, running->xcnt + running->subxcnt);

	/*
	 * Add to the temp array any xids which have not already completed.
	 */
	nxids = 0;
	for (i = 0; i < running->xcnt + running->subxcnt; i++)
	{
		TransactionId xid = running->xids[i];

		/*
		 * The running-xacts snapshot can contain xids that were still visible
		 * in the procarray when the snapshot was taken, but were already
		 * WAL-logged as completed. They're not running anymore, so ignore
		 * them.
		 */
		if (TransactionIdDidCommit(xid) || TransactionIdDidAbort(xid))
			continue;

		xids[nxids++] = xid;
	}

	if (nxids > 0)
	{
		if (procArray->numKnownAssignedXids != 0)
		{
			LWLockRelease(ProcArrayLock);
			elog(ERROR, "KnownAssignedXids is not empty");
		}

		/*
		 * Sort the array so that we can add them safely into
		 * KnownAssignedXids.
		 *
		 * We have to sort them logically, because in KnownAssignedXidsAdd we
		 * call TransactionIdFollowsOrEquals and so on. But we know these XIDs
		 * come from RUNNING_XACTS, which means there are only normal XIDs
		 * from the same epoch, so this is safe.
		 */
		qsort(xids, nxids, sizeof(TransactionId), xidLogicalComparator);

		/*
		 * Add the sorted snapshot into KnownAssignedXids.  The running-xacts
		 * snapshot may include duplicated xids because of prepared
		 * transactions, so ignore them.
		 */
		for (i = 0; i < nxids; i++)
		{
			if (i > 0 && TransactionIdEquals(xids[i - 1], xids[i]))
			{
				elog(DEBUG1,
					 "found duplicated transaction %u for KnownAssignedXids insertion",
					 xids[i]);
				continue;
			}
			KnownAssignedXidsAdd(xids[i], xids[i], true);
		}

		KnownAssignedXidsDisplay(DEBUG3);
	}

	pfree(xids);

	/*
	 * latestObservedXid is at least set to the point where SUBTRANS was
	 * started up to (cf. ProcArrayInitRecovery()) or to the biggest xid
	 * RecordKnownAssignedTransactionIds() was called for.  Initialize
	 * subtrans from thereon, up to nextXid - 1.
	 *
	 * We need to duplicate parts of RecordKnownAssignedTransactionId() here,
	 * because we've just added xids to the known assigned xids machinery that
	 * haven't gone through RecordKnownAssignedTransactionId().
	 */
	Assert(TransactionIdIsNormal(latestObservedXid));
	TransactionIdAdvance(latestObservedXid);
	while (TransactionIdPrecedes(latestObservedXid, running->nextXid))
	{
		ExtendSUBTRANS(latestObservedXid);
		TransactionIdAdvance(latestObservedXid);
	}
	TransactionIdRetreat(latestObservedXid);	/* = running->nextXid - 1 */

	/* ----------
	 * Now we've got the running xids we need to set the global values that
	 * are used to track snapshots as they evolve further.
	 *
	 * - latestCompletedXid which will be the xmax for snapshots
	 * - lastOverflowedXid which shows whether snapshots overflow
	 * - nextXid
	 *
	 * If the snapshot overflowed, then we still initialise with what we know,
	 * but the recovery snapshot isn't fully valid yet because we know there
	 * are some subxids missing. We don't know the specific subxids that are
	 * missing, so conservatively assume the last one is latestObservedXid.
	 * ----------
	 */
	if (running->subxid_status == SUBXIDS_MISSING)
	{
		standbyState = STANDBY_SNAPSHOT_PENDING;

		standbySnapshotPendingXmin = latestObservedXid;
		procArray->lastOverflowedXid = latestObservedXid;
	}
	else
	{
		standbyState = STANDBY_SNAPSHOT_READY;

		standbySnapshotPendingXmin = InvalidTransactionId;

		/*
		 * If the 'xids' array didn't include all subtransactions, we have to
		 * mark any snapshots taken as overflowed.
		 */
		if (running->subxid_status == SUBXIDS_IN_SUBTRANS)
			procArray->lastOverflowedXid = latestObservedXid;
		else
		{
			Assert(running->subxid_status == SUBXIDS_IN_ARRAY);
			procArray->lastOverflowedXid = InvalidTransactionId;
		}
	}

	/*
	 * If a transaction wrote a commit record in the gap between taking and
	 * logging the snapshot then latestCompletedXid may already be higher than
	 * the value from the snapshot, so check before we use the incoming value.
	 * It also might not yet be set at all.
	 */
	MaintainLatestCompletedXidRecovery(running->latestCompletedXid);

	/*
	 * NB: No need to increment TransamVariables->xactCompletionCount here,
	 * nobody can see it yet.
	 */

	LWLockRelease(ProcArrayLock);

	KnownAssignedXidsDisplay(DEBUG3);
	if (standbyState == STANDBY_SNAPSHOT_READY)
		elog(DEBUG1, "recovery snapshots are now enabled");
	else
		elog(DEBUG1,
			 "recovery snapshot waiting for non-overflowed snapshot or "
			 "until oldest active xid on standby is at least %u (now %u)",
			 standbySnapshotPendingXmin,
			 running->oldestRunningXid);
}

/*
 * ProcArrayApplyXidAssignment
 *		Process an XLOG_XACT_ASSIGNMENT WAL record
 */
/* (中文)处理 XLOG_XACT_ASSIGNMENT WAL 记录(备机侧:主库某事务分配了
 * 一批子事务 xid)。
 *
 * 【作用】
 * 1. 把这些子事务在 pg_subtrans 中登记为 topxid 的孩子
 *    (SubTransSetParent,供 TransactionIdIsInProgress 的树查找使用);
 * 2. 把已收入 KnownAssignedXids 的对应子事务 xid 删除——与主库侧
 *    子事务进入 PGPROC 缓存后"从主事务宣告中剥离"的行为对应;
 * 3. 推进 lastOverflowedXid 到这批子事务的最大值:这些子事务从此
 *    不在 KnownAssignedXids 里,快照对"不晚于该值的子事务"信息不完
 *    整,见 ProcArrayStruct 字段注释。
 *
 * 【设计思想】
 * - 用 topxid 而不是直接父 xid 登记:恢复期子事务的提交状态在 clog
 *   中要等顶层提交才标记,而中止的已标记;直接把子事务连到顶层,可
 *   以跳过中间状态直接查顶层,是"仍正确"的简化(见英文注释);
 * - RecordKnownAssignedTransactionIds(max_xid) 会顺带把中间未观察
 *   到的 xid 也"推断已分配"收入数组,保证无缝隙;
 * - 与正常事务提交同样的加锁(EXCLUSIVE)删除 KnownAssignedXids 条目。
 *
 * 【参数】
 *   topxid  —— 顶层事务 xid;
 *   nsubxids、subxids —— 子事务的数量与数组。
 * 【返回值】无。 */
void
ProcArrayApplyXidAssignment(TransactionId topxid,
							int nsubxids, TransactionId *subxids)
{
	TransactionId max_xid;
	int			i;

	Assert(standbyState >= STANDBY_INITIALIZED);

	max_xid = TransactionIdLatest(topxid, nsubxids, subxids);

	/*
	 * Mark all the subtransactions as observed.
	 *
	 * NOTE: This will fail if the subxid contains too many previously
	 * unobserved xids to fit into known-assigned-xids. That shouldn't happen
	 * as the code stands, because xid-assignment records should never contain
	 * more than PGPROC_MAX_CACHED_SUBXIDS entries.
	 */
	RecordKnownAssignedTransactionIds(max_xid);

	/*
	 * Notice that we update pg_subtrans with the top-level xid, rather than
	 * the parent xid. This is a difference between normal processing and
	 * recovery, yet is still correct in all cases. The reason is that
	 * subtransaction commit is not marked in clog until commit processing, so
	 * all aborted subtransactions have already been clearly marked in clog.
	 * As a result we are able to refer directly to the top-level
	 * transaction's state rather than skipping through all the intermediate
	 * states in the subtransaction tree. This should be the first time we
	 * have attempted to SubTransSetParent().
	 */
	for (i = 0; i < nsubxids; i++)
		SubTransSetParent(subxids[i], topxid);

	/* KnownAssignedXids isn't maintained yet, so we're done for now */
	if (standbyState == STANDBY_INITIALIZED)
		return;

	/*
	 * Uses same locking as transaction commit
	 */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	/*
	 * Remove subxids from known-assigned-xacts.
	 */
	KnownAssignedXidsRemoveTree(InvalidTransactionId, nsubxids, subxids);

	/*
	 * Advance lastOverflowedXid to be at least the last of these subxids.
	 */
	if (TransactionIdPrecedes(procArray->lastOverflowedXid, max_xid))
		procArray->lastOverflowedXid = max_xid;

	LWLockRelease(ProcArrayLock);
}

/*
 * TransactionIdIsInProgress -- is given transaction running in some backend
 *
 * Aside from some shortcuts such as checking RecentXmin and our own Xid,
 * there are four possibilities for finding a running transaction:
 *
 * 1. The given Xid is a main transaction Id.  We will find this out cheaply
 * by looking at ProcGlobal->xids.
 *
 * 2. The given Xid is one of the cached subxact Xids in the PGPROC array.
 * We can find this out cheaply too.
 *
 * 3. In Hot Standby mode, we must search the KnownAssignedXids list to see
 * if the Xid is running on the primary.
 *
 * 4. Search the SubTrans tree to find the Xid's topmost parent, and then see
 * if that is running according to ProcGlobal->xids[] or KnownAssignedXids.
 * This is the slowest way, but sadly it has to be done always if the others
 * failed, unless we see that the cached subxact sets are complete (none have
 * overflowed).
 *
 * ProcArrayLock has to be held while we do 1, 2, 3.  If we save the top Xids
 * while doing 1 and 3, we can release the ProcArrayLock while we do 4.
 * This buys back some concurrency (and we can't retrieve the main Xids from
 * ProcGlobal->xids[] again anyway; see GetNewTransactionId).
 */
/* (中文)核心可见性查询:判断给定 xid 是否仍被某个后端当作"正在运行"
 * (含自己)的事务。
 *
 * 【作用】这是 MVCC 可见性判定的关键一步(例如 HeapTupleSatisfiesMVCC
 * 判断 xmax 是否仍活跃)。除了若干廉价捷径,寻找"正在运行"的事务有
 * 四条途径,按成本从低到高:
 * 1. 主事务 xid 直接匹配 ProcGlobal->xids[](排他共享数组,一次遍历);
 * 2. 匹配某后端子事务缓存数组里的子 xid;
 * 3. 热备时查 KnownAssignedXids(主库上运行的事务);
 * 4. 最后手段:查 pg_subtrans 把 xid 上升到其最顶层父事务,再看该
 *    顶层是否在上面 1/3 的集合里——这要求子事务缓存曾经溢出
 *    (overflowed),否则第 1/2 步已经能给出确定答案。
 *
 * 执行捷径(均无需进入共享内存):
 * - xid < RecentXmin:必然已完成(顺带排除了 Invalid/Frozen 等特殊值);
 * - 命中 cachedXidIsNotInProgress:上次已确认不在运行;
 * - 是自己的事务(TransactionIdIsCurrentTransactionId,含子事务链):
 *   必在运行;
 * - 持锁后比较 latestCompletedXid:xid 比它新,必然还在运行。
 *
 * 【设计思想】
 * - 锁协议:步骤 1/2/3 持 ProcArrayLock SHARED(防止并发提交/删除把
 *   数组改动);期间把"需要进 pg_subtrans 复查的顶层 xid"先收集到
 *   私有数组 xids[],再释放锁做步骤 4——父链查询不需要数组稳定,
 *   而且提交者已把 xid 清出数组,复查时也必须用收集的快照值;
 * - 溢出标志的不可逆性保证了收集无遗漏:overflowed 一旦置位不会被
 *   清除(持锁期间),所以"需要复查"的集合只会变大不会变小;
 * - 已知全部相关缓存未溢出(nxids == 0)时直接断定"不在运行",
 *   这就是绝大多数情况下热路径的终点;
 * - 步骤 4 前先查 TransactionIdDidAbort:已中止的子事务即使父事务
 *   还在运行,也必须回答"不在运行";
 * - 工作数组 xids[] 用 malloc 一次性分配、永久复用(按热备需求取
 *   TOTAL_MAX_CACHED_SUBXIDS 大小),避免每次查询的分配开销;
 * - 频繁的小值读取使用 UINT32_ACCESS_ONCE 防撕裂读(与
 *   GetNewTransactionId 的写入侧配对)。
 *
 * 【参数】xid —— 待查询的事务 id。
 * 【返回值】true = 仍在运行(可能由步骤 1/2/3 直接判定,或由步骤 4
 *         经父事务链判定);false = 肯定不在运行(并把 xid 记入
 *         cachedXidIsNotInProgress 缓存)。 */
bool
TransactionIdIsInProgress(TransactionId xid)
{
	static TransactionId *xids = NULL;
	static TransactionId *other_xids;
	XidCacheStatus *other_subxidstates;
	int			nxids = 0;
	ProcArrayStruct *arrayP = procArray;
	TransactionId topxid;
	TransactionId latestCompletedXid;
	int			mypgxactoff;
	int			numProcs;
	int			j;

	/*
	 * Don't bother checking a transaction older than RecentXmin; it could not
	 * possibly still be running.  (Note: in particular, this guarantees that
	 * we reject InvalidTransactionId, FrozenTransactionId, etc as not
	 * running.)
	 */
	if (TransactionIdPrecedes(xid, RecentXmin))
	{
		xc_by_recent_xmin_inc();
		return false;
	}

	/*
	 * We may have just checked the status of this transaction, so if it is
	 * already known to be completed, we can fall out without any access to
	 * shared memory.
	 */
	if (TransactionIdEquals(cachedXidIsNotInProgress, xid))
	{
		xc_by_known_xact_inc();
		return false;
	}

	/*
	 * Also, we can handle our own transaction (and subtransactions) without
	 * any access to shared memory.
	 */
	if (TransactionIdIsCurrentTransactionId(xid))
	{
		xc_by_my_xact_inc();
		return true;
	}

	/*
	 * If first time through, get workspace to remember main XIDs in. We
	 * malloc it permanently to avoid repeated palloc/pfree overhead.
	 */
	if (xids == NULL)
	{
		/*
		 * In hot standby mode, reserve enough space to hold all xids in the
		 * known-assigned list. If we later finish recovery, we no longer need
		 * the bigger array, but we don't bother to shrink it.
		 */
		int			maxxids = RecoveryInProgress() ? TOTAL_MAX_CACHED_SUBXIDS : arrayP->maxProcs;

		xids = (TransactionId *) malloc(maxxids * sizeof(TransactionId));
		if (xids == NULL)
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of memory")));
	}

	other_xids = ProcGlobal->xids;
	other_subxidstates = ProcGlobal->subxidStates;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	/*
	 * Now that we have the lock, we can check latestCompletedXid; if the
	 * target Xid is after that, it's surely still running.
	 */
	latestCompletedXid =
		XidFromFullTransactionId(TransamVariables->latestCompletedXid);
	if (TransactionIdPrecedes(latestCompletedXid, xid))
	{
		LWLockRelease(ProcArrayLock);
		xc_by_latest_xid_inc();
		return true;
	}

	/* No shortcuts, gotta grovel through the array */
	mypgxactoff = MyProc->pgxactoff;
	numProcs = arrayP->numProcs;
	for (int pgxactoff = 0; pgxactoff < numProcs; pgxactoff++)
	{
		int			pgprocno;
		PGPROC	   *proc;
		TransactionId pxid;
		int			pxids;

		/* Ignore ourselves --- dealt with it above */
		if (pgxactoff == mypgxactoff)
			continue;

		/* Fetch xid just once - see GetNewTransactionId */
		pxid = UINT32_ACCESS_ONCE(other_xids[pgxactoff]);

		if (!TransactionIdIsValid(pxid))
			continue;

		/*
		 * Step 1: check the main Xid
		 */
		if (TransactionIdEquals(pxid, xid))
		{
			LWLockRelease(ProcArrayLock);
			xc_by_main_xid_inc();
			return true;
		}

		/*
		 * We can ignore main Xids that are younger than the target Xid, since
		 * the target could not possibly be their child.
		 */
		if (TransactionIdPrecedes(xid, pxid))
			continue;

		/*
		 * Step 2: check the cached child-Xids arrays
		 */
		pxids = other_subxidstates[pgxactoff].count;
		pg_read_barrier();		/* pairs with barrier in GetNewTransactionId() */
		pgprocno = arrayP->pgprocnos[pgxactoff];
		proc = &allProcs[pgprocno];
		for (j = pxids - 1; j >= 0; j--)
		{
			/* Fetch xid just once - see GetNewTransactionId */
			TransactionId cxid = UINT32_ACCESS_ONCE(proc->subxids.xids[j]);

			if (TransactionIdEquals(cxid, xid))
			{
				LWLockRelease(ProcArrayLock);
				xc_by_child_xid_inc();
				return true;
			}
		}

		/*
		 * Save the main Xid for step 4.  We only need to remember main Xids
		 * that have uncached children.  (Note: there is no race condition
		 * here because the overflowed flag cannot be cleared, only set, while
		 * we hold ProcArrayLock.  So we can't miss an Xid that we need to
		 * worry about.)
		 */
		if (other_subxidstates[pgxactoff].overflowed)
			xids[nxids++] = pxid;
	}

	/*
	 * Step 3: in hot standby mode, check the known-assigned-xids list.  XIDs
	 * in the list must be treated as running.
	 */
	if (RecoveryInProgress())
	{
		/* none of the PGPROC entries should have XIDs in hot standby mode */
		Assert(nxids == 0);

		if (KnownAssignedXidExists(xid))
		{
			LWLockRelease(ProcArrayLock);
			xc_by_known_assigned_inc();
			return true;
		}

		/*
		 * If the KnownAssignedXids overflowed, we have to check pg_subtrans
		 * too.  Fetch all xids from KnownAssignedXids that are lower than
		 * xid, since if xid is a subtransaction its parent will always have a
		 * lower value.  Note we will collect both main and subXIDs here, but
		 * there's no help for it.
		 */
		if (TransactionIdPrecedesOrEquals(xid, procArray->lastOverflowedXid))
			nxids = KnownAssignedXidsGet(xids, xid);
	}

	LWLockRelease(ProcArrayLock);

	/*
	 * If none of the relevant caches overflowed, we know the Xid is not
	 * running without even looking at pg_subtrans.
	 */
	if (nxids == 0)
	{
		xc_no_overflow_inc();
		cachedXidIsNotInProgress = xid;
		return false;
	}

	/*
	 * Step 4: have to check pg_subtrans.
	 *
	 * At this point, we know it's either a subtransaction of one of the Xids
	 * in xids[], or it's not running.  If it's an already-failed
	 * subtransaction, we want to say "not running" even though its parent may
	 * still be running.  So first, check pg_xact to see if it's been aborted.
	 */
	xc_slow_answer_inc();

	if (TransactionIdDidAbort(xid))
	{
		cachedXidIsNotInProgress = xid;
		return false;
	}

	/*
	 * It isn't aborted, so check whether the transaction tree it belongs to
	 * is still running (or, more precisely, whether it was running when we
	 * held ProcArrayLock).
	 */
	topxid = SubTransGetTopmostTransaction(xid);
	Assert(TransactionIdIsValid(topxid));
	if (!TransactionIdEquals(topxid, xid) &&
		pg_lfind32(topxid, xids, nxids))
		return true;

	cachedXidIsNotInProgress = xid;
	return false;
}


/*
 * Determine XID horizons.
 *
 * This is used by wrapper functions like GetOldestNonRemovableTransactionId()
 * (for VACUUM), GetReplicationHorizons() (for hot_standby_feedback), etc as
 * well as "internally" by GlobalVisUpdate() (see comment above struct
 * GlobalVisState).
 *
 * See the definition of ComputeXidHorizonsResult for the various computed
 * horizons.
 *
 * For VACUUM separate horizons (used to decide which deleted tuples must
 * be preserved), for shared and non-shared tables are computed.  For shared
 * relations backends in all databases must be considered, but for non-shared
 * relations that's not required, since only backends in my own database could
 * ever see the tuples in them. Also, we can ignore concurrently running lazy
 * VACUUMs because (a) they must be working on other tables, and (b) they
 * don't need to do snapshot-based lookups.
 *
 * This also computes a horizon used to truncate pg_subtrans. For that
 * backends in all databases have to be considered, and concurrently running
 * lazy VACUUMs cannot be ignored, as they still may perform pg_subtrans
 * accesses.
 *
 * Note: we include all currently running xids in the set of considered xids.
 * This ensures that if a just-started xact has not yet set its snapshot,
 * when it does set the snapshot it cannot set xmin less than what we compute.
 * See notes in src/backend/access/transam/README.
 *
 * Note: despite the above, it's possible for the calculated values to move
 * backwards on repeated calls. The calculated values are conservative, so
 * that anything older is definitely not considered as running by anyone
 * anymore, but the exact values calculated depend on a number of things. For
 * example, if there are no transactions running in the current database, the
 * horizon for normal tables will be latestCompletedXid. If a transaction
 * begins after that, its xmin will include in-progress transactions in other
 * databases that started earlier, so another call will return a lower value.
 * Nonetheless it is safe to vacuum a table in the current database with the
 * first result.  There are also replication-related effects: a walsender
 * process can set its xmin based on transactions that are no longer running
 * on the primary but are still being replayed on the standby, thus possibly
 * making the values go backwards.  In this case there is a possibility that
 * we lose data that the standby would like to have, but unless the standby
 * uses a replication slot to make its xmin persistent there is little we can
 * do about that --- data is only protected if the walsender runs continuously
 * while queries are executed on the standby.  (The Hot Standby code deals
 * with such cases by failing standby queries that needed to access
 * already-removed data, so there's no integrity bug.)
 *
 * Note: the approximate horizons (see definition of GlobalVisState) are
 * updated by the computations done here. That's currently required for
 * correctness and a small optimization. Without doing so it's possible that
 * heap vacuum's call to heap_page_prune_and_freeze() uses a more conservative
 * horizon than later when deciding which tuples can be removed - which the
 * code doesn't expect (breaking HOT).
 */
/* (中文)计算各种"水位"(horizon):一个 xid 达到多少才能安全清理。
 *
 * 【作用】在持 ProcArrayLock SHARED 期间,扫描进程数组收集所有活跃
 * 后端的 xid 与 xmin,并综合复制槽水位,计算并填充
 * ComputeXidHorizonsResult 中的一组下界(结果字段含义见该结构的中文
 * 注释)。封装函数 GetOldestNonRemovableTransactionId() /
 * GetOldestTransactionIdConsideredRunning() / GetReplicationHorizons()
 * 以及 GlobalVisUpdate() 都依赖它。
 *
 * 【设计思想】
 * - 计算原则:一切"最老不可删除 xid"的初值都取 latestCompletedXid + 1
 *   ——这是"将来可能出现在进程数组中的最小 xid"的下界,防止对未来
 *   加入的事务过度乐观(见英文注释);再对所有候选 xid/xmin 取 MIN;
 * - 为什么同时看 xmin 和 xid:事务可能"有 xmin 还没 xid"(只读事务
 *   也保快照),也可能"有 xid 还没设 xmin"(见英文注释);
 * - 按关系类别区分保守度:共享表要把所有库的后端都计入;普通数据表
 *   只计本库后端(其他库的会话看不到本库的表),但 MyDatabaseId 尚未
 *   设置(启动中)、带 PROC_AFFECTS_ALL_HORIZONS(如 walsender 反馈)
 *   或处于恢复期时必须全部计入,否则可能把仍需要的数据剪掉;
 * - 恢复期用 KnownAssignedXids 的最老 xid 补充(备机的 PGPROC 没有
 *   xid);VACUUM 进程/逻辑解码进程不进"非共享"水位,但永远计入
 *   oldest_considered_running(他们还要查 pg_subtrans);
 * - 锁只持有到共享数据读完为止,其余纯计算在锁外进行,缩短持锁时间;
 * - 结果可能比上次更激进(更小):返回值都是"保守有效"的,例如当前
 *   库没有事务时数据表水位是 latestCompletedXid,新事务随后开始会把
 *   它压低。重复调用允许回退,但任何一次结果对当时的使用都是安全
 *   的(详情与复制相关的回退场景见英文注释);
 * - 顺带更新 GlobalVisUpdateApply 维护的四份近似边界,这是正确性
 *   要求(heap vacuum 的 prune 调用需要一致的水位,见英文注释)。
 *
 * 【参数】h —— 输出:计算出的各组水位。
 * 【返回值】无(结果写入 h)。 */
static void
ComputeXidHorizons(ComputeXidHorizonsResult *h)
{
	ProcArrayStruct *arrayP = procArray;
	TransactionId kaxmin;
	bool		in_recovery = RecoveryInProgress();
	TransactionId *other_xids = ProcGlobal->xids;

	/* inferred after ProcArrayLock is released */
	h->catalog_oldest_nonremovable = InvalidTransactionId;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	h->latest_completed = TransamVariables->latestCompletedXid;

	/*
	 * We initialize the MIN() calculation with latestCompletedXid + 1. This
	 * is a lower bound for the XIDs that might appear in the ProcArray later,
	 * and so protects us against overestimating the result due to future
	 * additions.
	 */
	{
		TransactionId initial;

		initial = XidFromFullTransactionId(h->latest_completed);
		Assert(TransactionIdIsValid(initial));
		TransactionIdAdvance(initial);

		h->oldest_considered_running = initial;
		h->shared_oldest_nonremovable = initial;
		h->data_oldest_nonremovable = initial;

		/*
		 * Only modifications made by this backend affect the horizon for
		 * temporary relations. Instead of a check in each iteration of the
		 * loop over all PGPROCs it is cheaper to just initialize to the
		 * current top-level xid any.
		 *
		 * Without an assigned xid we could use a horizon as aggressive as
		 * GetNewTransactionId(), but we can get away with the much cheaper
		 * latestCompletedXid + 1: If this backend has no xid there, by
		 * definition, can't be any newer changes in the temp table than
		 * latestCompletedXid.
		 */
		if (TransactionIdIsValid(MyProc->xid))
			h->temp_oldest_nonremovable = MyProc->xid;
		else
			h->temp_oldest_nonremovable = initial;
	}

	/*
	 * Fetch slot horizons while ProcArrayLock is held - the
	 * LWLockAcquire/LWLockRelease are a barrier, ensuring this happens inside
	 * the lock.
	 */
	h->slot_xmin = procArray->replication_slot_xmin;
	h->slot_catalog_xmin = procArray->replication_slot_catalog_xmin;

	for (int index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];
		int8		statusFlags = ProcGlobal->statusFlags[index];
		TransactionId xid;
		TransactionId xmin;

		/* Fetch xid just once - see GetNewTransactionId */
		xid = UINT32_ACCESS_ONCE(other_xids[index]);
		xmin = UINT32_ACCESS_ONCE(proc->xmin);

		/*
		 * Consider both the transaction's Xmin, and its Xid.
		 *
		 * We must check both because a transaction might have an Xmin but not
		 * (yet) an Xid; conversely, if it has an Xid, that could determine
		 * some not-yet-set Xmin.
		 */
		xmin = TransactionIdOlder(xmin, xid);

		/* if neither is set, this proc doesn't influence the horizon */
		if (!TransactionIdIsValid(xmin))
			continue;

		/*
		 * Don't ignore any procs when determining which transactions might be
		 * considered running.  While slots should ensure logical decoding
		 * backends are protected even without this check, it can't hurt to
		 * include them here as well..
		 */
		h->oldest_considered_running =
			TransactionIdOlder(h->oldest_considered_running, xmin);

		/*
		 * Skip over backends either vacuuming (which is ok with rows being
		 * removed, as long as pg_subtrans is not truncated) or doing logical
		 * decoding (which manages xmin separately, check below).
		 */
		if (statusFlags & (PROC_IN_VACUUM | PROC_IN_LOGICAL_DECODING))
			continue;

		/* shared tables need to take backends in all databases into account */
		h->shared_oldest_nonremovable =
			TransactionIdOlder(h->shared_oldest_nonremovable, xmin);

		/*
		 * Normally sessions in other databases are ignored for anything but
		 * the shared horizon.
		 *
		 * However, include them when MyDatabaseId is not (yet) set.  A
		 * backend in the process of starting up must not compute a "too
		 * aggressive" horizon, otherwise we could end up using it to prune
		 * still-needed data away.  If the current backend never connects to a
		 * database this is harmless, because data_oldest_nonremovable will
		 * never be utilized.
		 *
		 * Also, sessions marked with PROC_AFFECTS_ALL_HORIZONS should always
		 * be included.  (This flag is used for hot standby feedback, which
		 * can't be tied to a specific database.)
		 *
		 * Also, while in recovery we cannot compute an accurate per-database
		 * horizon, as all xids are managed via the KnownAssignedXids
		 * machinery.
		 */
		if (proc->databaseId == MyDatabaseId ||
			MyDatabaseId == InvalidOid ||
			(statusFlags & PROC_AFFECTS_ALL_HORIZONS) ||
			in_recovery)
		{
			h->data_oldest_nonremovable =
				TransactionIdOlder(h->data_oldest_nonremovable, xmin);
		}
	}

	/*
	 * If in recovery fetch oldest xid in KnownAssignedXids, will be applied
	 * after lock is released.
	 */
	if (in_recovery)
		kaxmin = KnownAssignedXidsGetOldestXmin();

	/*
	 * No other information from shared state is needed, release the lock
	 * immediately. The rest of the computations can be done without a lock.
	 */
	LWLockRelease(ProcArrayLock);

	if (in_recovery)
	{
		h->oldest_considered_running =
			TransactionIdOlder(h->oldest_considered_running, kaxmin);
		h->shared_oldest_nonremovable =
			TransactionIdOlder(h->shared_oldest_nonremovable, kaxmin);
		h->data_oldest_nonremovable =
			TransactionIdOlder(h->data_oldest_nonremovable, kaxmin);
		/* temp relations cannot be accessed in recovery */
	}

	Assert(TransactionIdPrecedesOrEquals(h->oldest_considered_running,
										 h->shared_oldest_nonremovable));
	Assert(TransactionIdPrecedesOrEquals(h->shared_oldest_nonremovable,
										 h->data_oldest_nonremovable));

	/*
	 * Check whether there are replication slots requiring an older xmin.
	 */
	h->shared_oldest_nonremovable =
		TransactionIdOlder(h->shared_oldest_nonremovable, h->slot_xmin);
	h->data_oldest_nonremovable =
		TransactionIdOlder(h->data_oldest_nonremovable, h->slot_xmin);

	/*
	 * The only difference between catalog / data horizons is that the slot's
	 * catalog xmin is applied to the catalog one (so catalogs can be accessed
	 * for logical decoding). Initialize with data horizon, and then back up
	 * further if necessary. Have to back up the shared horizon as well, since
	 * that also can contain catalogs.
	 */
	h->shared_oldest_nonremovable_raw = h->shared_oldest_nonremovable;
	h->shared_oldest_nonremovable =
		TransactionIdOlder(h->shared_oldest_nonremovable,
						   h->slot_catalog_xmin);
	h->catalog_oldest_nonremovable = h->data_oldest_nonremovable;
	h->catalog_oldest_nonremovable =
		TransactionIdOlder(h->catalog_oldest_nonremovable,
						   h->slot_catalog_xmin);

	/*
	 * It's possible that slots backed up the horizons further than
	 * oldest_considered_running. Fix.
	 */
	h->oldest_considered_running =
		TransactionIdOlder(h->oldest_considered_running,
						   h->shared_oldest_nonremovable);
	h->oldest_considered_running =
		TransactionIdOlder(h->oldest_considered_running,
						   h->catalog_oldest_nonremovable);
	h->oldest_considered_running =
		TransactionIdOlder(h->oldest_considered_running,
						   h->data_oldest_nonremovable);

	/*
	 * shared horizons have to be at least as old as the oldest visible in
	 * current db
	 */
	Assert(TransactionIdPrecedesOrEquals(h->shared_oldest_nonremovable,
										 h->data_oldest_nonremovable));
	Assert(TransactionIdPrecedesOrEquals(h->shared_oldest_nonremovable,
										 h->catalog_oldest_nonremovable));

	/*
	 * Horizons need to ensure that pg_subtrans access is still possible for
	 * the relevant backends.
	 */
	Assert(TransactionIdPrecedesOrEquals(h->oldest_considered_running,
										 h->shared_oldest_nonremovable));
	Assert(TransactionIdPrecedesOrEquals(h->oldest_considered_running,
										 h->catalog_oldest_nonremovable));
	Assert(TransactionIdPrecedesOrEquals(h->oldest_considered_running,
										 h->data_oldest_nonremovable));
	Assert(TransactionIdPrecedesOrEquals(h->oldest_considered_running,
										 h->temp_oldest_nonremovable));
	Assert(!TransactionIdIsValid(h->slot_xmin) ||
		   TransactionIdPrecedesOrEquals(h->oldest_considered_running,
										 h->slot_xmin));
	Assert(!TransactionIdIsValid(h->slot_catalog_xmin) ||
		   TransactionIdPrecedesOrEquals(h->oldest_considered_running,
										 h->slot_catalog_xmin));

	/* update approximate horizons with the computed horizons */
	GlobalVisUpdateApply(h);
}

/*
 * Determine what kind of visibility horizon needs to be used for a
 * relation. If rel is NULL, the most conservative horizon is used.
 */
/* (中文)决定某张关系应该使用哪种水位(保守度)。
 *
 * 【作用】把关系分类映射到 GlobalVisHorizonKind 四档:
 * - rel == NULL(未指定关系)或共享表或处于恢复期:取最保守的
 *   VISHORIZON_SHARED;
 * - 系统目录、逻辑解码需要访问的关系:VISHORIZON_CATALOG;
 * - 普通非本地表:VISHORIZON_DATA;
 * - 临时表(仅本会话可见):VISHORIZON_TEMP。
 *
 * 【设计思想】其他 relkind(索引、序列等)不直接存 xid,也不带逻辑
 * 解码标记,所以函数只接受堆/物化视图/TOAST(有 Assert 检查)。
 * 分类依据见 GlobalVisHorizonKind 枚举的中文注释。
 *
 * 【参数】rel —— 关系描述符;NULL 表示"所有关系的通用答案"。
 * 【返回值】对应的水位类别枚举。 */
static inline GlobalVisHorizonKind
GlobalVisHorizonKindForRel(Relation rel)
{
	/*
	 * Other relkinds currently don't contain xids, nor always the necessary
	 * logical decoding markers.
	 */
	Assert(!rel ||
		   rel->rd_rel->relkind == RELKIND_RELATION ||
		   rel->rd_rel->relkind == RELKIND_MATVIEW ||
		   rel->rd_rel->relkind == RELKIND_TOASTVALUE);

	if (rel == NULL || rel->rd_rel->relisshared || RecoveryInProgress())
		return VISHORIZON_SHARED;
	else if (IsCatalogRelation(rel) ||
			 RelationIsAccessibleInLogicalDecoding(rel))
		return VISHORIZON_CATALOG;
	else if (!RELATION_IS_LOCAL(rel))
		return VISHORIZON_DATA;
	else
		return VISHORIZON_TEMP;
}

/*
 * Return the oldest XID for which deleted tuples must be preserved in the
 * passed table.
 *
 * If rel is not NULL the horizon may be considerably more recent than
 * otherwise (i.e. fewer tuples will be removable). In the NULL case a horizon
 * that is correct (but not optimal) for all relations will be returned.
 *
 * This is used by VACUUM to decide which deleted tuples must be preserved in
 * the passed in table.
 */
/* (中文)VACUUM 用:返回"指定表中已删除元组必须保留到的最老 xid"。
 *
 * 【作用】调用 ComputeXidHorizons() 后,按关系的类别
 * (GlobalVisHorizonKindForRel)挑选对应的水位返回:共享表/目录/普通
 * 表/临时表各有各的边界。
 *
 * 【设计思想】传具体关系能拿到比全局答案更"激进"(更新)的边界——
 * 例如普通用户表不需要为其他库的会话保守;rel == NULL 时返回对一切
 * 关系都安全(但不够优)的值。VACUUM 用返回值的含义是:凡是 xmax
 * 早于它的已删除元组都可以移除。
 *
 * 【参数】rel —— 目标关系;NULL 表示"对所有关系都安全"的通用水位。
 * 【返回值】该表可删除元组的 xid 下界(早于此 xid 的删除可见/可清理)。 */
TransactionId
GetOldestNonRemovableTransactionId(Relation rel)
{
	ComputeXidHorizonsResult horizons;

	ComputeXidHorizons(&horizons);

	switch (GlobalVisHorizonKindForRel(rel))
	{
		case VISHORIZON_SHARED:
			return horizons.shared_oldest_nonremovable;
		case VISHORIZON_CATALOG:
			return horizons.catalog_oldest_nonremovable;
		case VISHORIZON_DATA:
			return horizons.data_oldest_nonremovable;
		case VISHORIZON_TEMP:
			return horizons.temp_oldest_nonremovable;
	}

	/* just to prevent compiler warnings */
	return InvalidTransactionId;
}

/*
 * Return the oldest transaction id any currently running backend might still
 * consider running. This should not be used for visibility / pruning
 * determinations (see GetOldestNonRemovableTransactionId()), but for
 * decisions like up to where pg_subtrans can be truncated.
 */
/* (中文)返回"可能仍被任何后端认为在运行的最老 xid"。
 *
 * 【作用】调用 ComputeXidHorizons() 返回 oldest_considered_running。
 * 该值的用途不是可见性/清理判定(那是
 * GetOldestNonRemovableTransactionId 的事),而是类似"pg_subtrans 可以
 * 截断到哪个 xid"这种决策——它把 VACUUM、逻辑解码等所有仍可能做
 * pg_subtrans 查询的进程都考虑进去了。
 *
 * 【设计思想】与普通清理水位不同,该值不能忽略 VACUUM 进程(它们判断
 * 可见性时也要查 pg_subtrans,见 ComputeXidHorizons 的中文注释)。
 *
 * 【参数】无。
 * 【返回值】最老的可能被视为运行的事务 xid。 */
TransactionId
GetOldestTransactionIdConsideredRunning(void)
{
	ComputeXidHorizonsResult horizons;

	ComputeXidHorizons(&horizons);

	return horizons.oldest_considered_running;
}

/*
 * Return the visibility horizons for a hot standby feedback message.
 */
/* (中文)计算要发给主库的 hot_standby_feedback 消息里的水位。
 *
 * 【作用】walsender 周期性地调用本函数,把备机上"仍可能需要的 xid"
 * 反馈给主库,主库据此收紧 VACUUM 的清理边界。
 *
 * 【设计思想】刻意不用 shared_oldest_nonremovable(它已计入复制槽的
 * catalog_xmin),而是返回 shared_oldest_nonremovable_raw(不受
 * catalog_xmin 影响)与槽位的 slot_catalog_xmin 分开:这样主库可以对
 * 数据表采用更激进的清理,只对系统目录(逻辑解码还要用)采取保守
 * 边界(见英文注释)。
 *
 * 【参数】
 *   xmin         —— 输出:数据表水位;
 *   catalog_xmin —— 输出:系统目录水位。
 * 【返回值】无。 */
void
GetReplicationHorizons(TransactionId *xmin, TransactionId *catalog_xmin)
{
	ComputeXidHorizonsResult horizons;

	ComputeXidHorizons(&horizons);

	/*
	 * Don't want to use shared_oldest_nonremovable here, as that contains the
	 * effect of replication slot's catalog_xmin. We want to send a separate
	 * feedback for the catalog horizon, so the primary can remove data table
	 * contents more aggressively.
	 */
	*xmin = horizons.shared_oldest_nonremovable_raw;
	*catalog_xmin = horizons.slot_catalog_xmin;
}

/*
 * GetMaxSnapshotXidCount -- get max size for snapshot XID array
 *
 * We have to export this for use by snapmgr.c.
 */
/* (中文)返回快照 xip 数组(主事务 xid 列表)的最大容量。
 *
 * 【作用】导出给 snapmgr.c:取快照前按此容量一次性 malloc xip 数组。
 * 容量固定为 procArray->maxProcs = PROCARRAY_MAXPROCS,即"所有后端
 * 都可能同时各持一个主 xid"的极端情况。
 *
 * 【设计思想】快照复用机制(GetSnapshotDataReuse)依赖 xip 数组在多次
 * 调用间保持不变(调用方传静态 SnapshotData),因此容量一次定死、不
 * 随 numProcs 变化(见 GetSnapshotData 的英文注释)。
 *
 * 【参数】无。
 * 【返回值】xip 数组容量。 */
int
GetMaxSnapshotXidCount(void)
{
	return procArray->maxProcs;
}

/*
 * GetMaxSnapshotSubxidCount -- get max size for snapshot sub-XID array
 *
 * We have to export this for use by snapmgr.c.
 */
/* (中文)返回快照 subxip 数组(子事务 xid 列表)的最大容量。
 *
 * 【作用】导出给 snapmgr.c:取快照前按此容量 malloc subxip 数组。
 * 容量为 TOTAL_MAX_CACHED_SUBXIDS,即所有后端子事务缓存总和的上限
 * (热备时 KnownAssignedXids 的容量与之相同,因为热备快照会把全部
 * xid 塞进 subxip,见 GetSnapshotData 的英文注释)。
 *
 * 【参数】无。
 * 【返回值】subxip 数组容量。 */
int
GetMaxSnapshotSubxidCount(void)
{
	return TOTAL_MAX_CACHED_SUBXIDS;
}

/*
 * Helper function for GetSnapshotData() that checks if the bulk of the
 * visibility information in the snapshot is still valid. If so, it updates
 * the fields that need to change and returns true. Otherwise it returns
 * false.
 *
 * This very likely can be evolved to not need ProcArrayLock held (at very
 * least in the case we already hold a snapshot), but that's for another day.
 */
/* (中文)GetSnapshotData 的快照复用判定:检查旧快照的可见性信息是否
 * 仍然有效,有效则就地刷新后返回 true。
 *
 * 【作用】取快照时发现"自上次构造以来没有任何带 xid 的事务完成"
 * (xactCompletionCount 未变),则"正在运行集合"必然与上次相同,快照
 * 的 xmin/xmax/xip/subxip 都可以直接沿用,只需刷新 curcid 与引用计数
 * 等易变字段。
 *
 * 【设计思想】
 * - 正确性依据(见英文注释):快照内容只取决于"带 xid 的事务集合";
 *   每个带 xid 的事务结束时都会在持 EXCLUSIVE 锁的情况下递增
 *   xactCompletionCount。因此计数相同 => 内容相同;
 * - 复用时仍要把 xmin 重新登记进 MyProc->xmin:并发取快照的进程之间
 *   必须满足"xmin 单调不后退"的约定(两个进程的 xmin 互相覆盖会破坏
 *   VACUUM 的清理判定),且旧快照中可见的行不可能已被删除;
 * - snapXactCompletionCount == 0 表示快照从未参与复用(首用),直接
 *   返回 false 走完整重建。
 *
 * 【参数】snapshot —— 目标快照(须是静态分配、xip/subxip 已分配)。
 * 【返回值】true = 复用成功(快照字段已被更新);false = 必须重建。 */
static bool
GetSnapshotDataReuse(Snapshot snapshot)
{
	uint64		curXactCompletionCount;

	Assert(LWLockHeldByMe(ProcArrayLock));

	if (unlikely(snapshot->snapXactCompletionCount == 0))
		return false;

	curXactCompletionCount = TransamVariables->xactCompletionCount;
	if (curXactCompletionCount != snapshot->snapXactCompletionCount)
		return false;

	/*
	 * If the current xactCompletionCount is still the same as it was at the
	 * time the snapshot was built, we can be sure that rebuilding the
	 * contents of the snapshot the hard way would result in the same snapshot
	 * contents:
	 *
	 * As explained in transam/README, the set of xids considered running by
	 * GetSnapshotData() cannot change while ProcArrayLock is held. Snapshot
	 * contents only depend on transactions with xids and xactCompletionCount
	 * is incremented whenever a transaction with an xid finishes (while
	 * holding ProcArrayLock exclusively). Thus the xactCompletionCount check
	 * ensures we would detect if the snapshot would have changed.
	 *
	 * As the snapshot contents are the same as it was before, it is safe to
	 * re-enter the snapshot's xmin into the PGPROC array. None of the rows
	 * visible under the snapshot could already have been removed (that'd
	 * require the set of running transactions to change) and it fulfills the
	 * requirement that concurrent GetSnapshotData() calls yield the same
	 * xmin.
	 */
	if (!TransactionIdIsValid(MyProc->xmin))
		MyProc->xmin = TransactionXmin = snapshot->xmin;

	RecentXmin = snapshot->xmin;
	Assert(TransactionIdPrecedesOrEquals(TransactionXmin, RecentXmin));

	snapshot->curcid = GetCurrentCommandId(false);
	snapshot->active_count = 0;
	snapshot->regd_count = 0;
	snapshot->copied = false;

	return true;
}

/*
 * GetSnapshotData -- returns information about running transactions.
 *
 * The returned snapshot includes xmin (lowest still-running xact ID),
 * xmax (highest completed xact ID + 1), and a list of running xact IDs
 * in the range xmin <= xid < xmax.  It is used as follows:
 *		All xact IDs < xmin are considered finished.
 *		All xact IDs >= xmax are considered still running.
 *		For an xact ID xmin <= xid < xmax, consult list to see whether
 *		it is considered running or not.
 * This ensures that the set of transactions seen as "running" by the
 * current xact will not change after it takes the snapshot.
 *
 * All running top-level XIDs are included in the snapshot, except for lazy
 * VACUUM processes.  We also try to include running subtransaction XIDs,
 * but since PGPROC has only a limited cache area for subxact XIDs, full
 * information may not be available.  If we find any overflowed subxid arrays,
 * we have to mark the snapshot's subxid data as overflowed, and extra work
 * *may* need to be done to determine what's running (see XidInMVCCSnapshot()).
 *
 * We also update the following backend-global variables:
 *		TransactionXmin: the oldest xmin of any snapshot in use in the
 *			current transaction (this is the same as MyProc->xmin).
 *		RecentXmin: the xmin computed for the most recent snapshot.  XIDs
 *			older than this are known not running any more.
 *
 * And try to advance the bounds of GlobalVis{Shared,Catalog,Data,Temp}Rels
 * for the benefit of the GlobalVisTest* family of functions.
 *
 * Note: this function should probably not be called with an argument that's
 * not statically allocated (see xip allocation below).
 */
/* (中文)构造事务快照:收集"正在运行的事务"集合,这是 MVCC 可见性
 * 判定的核心数据。
 *
 * 【作用】在持 ProcArrayLock SHARED 锁期间,遍历进程数组(正常运行时
 * 用 ProcGlobal->xids[] 与子事务缓存;热备时用 KnownAssignedXids),
 * 产出快照:
 * - xmin : 仍在运行的最小 xid(所有小于它的 xid 视为已结束);
 * - xmax : 最新已完成 xid + 1(所有 >= 它的 xid 视为仍在运行);
 * - xip[]: [xmin, xmax) 之间"正在运行"的 xid 列表(xcnt 个)——落在
 *   此区间内的 xid 必须查这张表才能判定;
 * - subxip[]: 各活跃后端子事务缓存里收集的子 xid(subxcnt 个);
 * - suboverflowed: 是否有后端子事务缓存溢出(溢出时子 xid 信息不全,
 *   判定方必须走 pg_subtrans 复查,见 XidInMVCCSnapshot);
 * 同时更新后端全局量 TransactionXmin / RecentXmin 与四份
 * GlobalVisState 的 definitely_needed 上界。
 *
 * 【设计思想】
 * - 快照的不变性承诺:取快照者持锁期间,"正在运行集合"只能变大不能
 *   变小(事务只能从无 xid 变成有 xid,有 xid 的必须持 EXCLUSIVE 锁
 *   才能清除),因此构造出的快照保证了"我看到的运行集合在事务期间
 *   不会向后变化"——这正是 MVCC 可重复读的基础;
 * - 自己的 xid 不进 xip(自己当然算运行,但不需要写进快照;xmin 的
 *   计算单独提前处理它);
 * - 跳过逻辑解码与 LAZY VACUUM 进程(它们的 xmin 单独管理,见英文
 *   注释);xid >= xmax 的也跳过(反正被视为运行);
 * - 热备时把全部 xid 塞进 subxip:恢复期不区分主/子 xid(设计取舍,
 *   见英文注释),xip 留空;
 * - 子事务拷贝只读一次 nsubxids(对方可以并发"增加"子事务但不能
 *   删除,而新加的子事务必然 >= xmax,对快照无关紧要,见英文注释);
 * - xip/subxip 用 malloc 一次分配永久复用(调用方须传静态 Snapshot),
 *   取锁前分配以免持锁做内存分配;
 * - 快照封顶:数组容量固定为 maxProcs / TOTAL_MAX_CACHED_SUBXIDS
 *   (见 GetMaxSnapshotXidCount 等),不会出现"收集途中数组不够"的
 *   情况。
 *
 * 【参数】snapshot —— 输出:填充好的快照(须为静态分配,首次调用时
 *                    xip/subxip 为 NULL,由本函数分配)。
 * 【返回值】同一快照指针(字段已填充)。 */
Snapshot
GetSnapshotData(Snapshot snapshot)
{
	ProcArrayStruct *arrayP = procArray;
	TransactionId *other_xids = ProcGlobal->xids;
	TransactionId xmin;
	TransactionId xmax;
	int			count = 0;
	int			subcount = 0;
	bool		suboverflowed = false;
	FullTransactionId latest_completed;
	TransactionId oldestxid;
	int			mypgxactoff;
	TransactionId myxid;
	uint64		curXactCompletionCount;

	TransactionId replication_slot_xmin = InvalidTransactionId;
	TransactionId replication_slot_catalog_xmin = InvalidTransactionId;

	Assert(snapshot != NULL);

	/*
	 * Allocating space for maxProcs xids is usually overkill; numProcs would
	 * be sufficient.  But it seems better to do the malloc while not holding
	 * the lock, so we can't look at numProcs.  Likewise, we allocate much
	 * more subxip storage than is probably needed.
	 *
	 * This does open a possibility for avoiding repeated malloc/free: since
	 * maxProcs does not change at runtime, we can simply reuse the previous
	 * xip arrays if any.  (This relies on the fact that all callers pass
	 * static SnapshotData structs.)
	 */
	if (snapshot->xip == NULL)
	{
		/*
		 * First call for this snapshot. Snapshot is same size whether or not
		 * we are in recovery, see later comments.
		 */
		snapshot->xip = (TransactionId *)
			malloc(GetMaxSnapshotXidCount() * sizeof(TransactionId));
		if (snapshot->xip == NULL)
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of memory")));
		Assert(snapshot->subxip == NULL);
		snapshot->subxip = (TransactionId *)
			malloc(GetMaxSnapshotSubxidCount() * sizeof(TransactionId));
		if (snapshot->subxip == NULL)
		{
			/*
			 * Clean up the Snapshot state before throwing the error, so that
			 * a retry does not see a partially-initialized snapshot.
			 */
			free(snapshot->xip);
			snapshot->xip = NULL;
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of memory")));
		}
	}

	/*
	 * It is sufficient to get shared lock on ProcArrayLock, even if we are
	 * going to set MyProc->xmin.
	 */
	LWLockAcquire(ProcArrayLock, LW_SHARED);

	if (GetSnapshotDataReuse(snapshot))
	{
		LWLockRelease(ProcArrayLock);
		return snapshot;
	}

	latest_completed = TransamVariables->latestCompletedXid;
	mypgxactoff = MyProc->pgxactoff;
	myxid = other_xids[mypgxactoff];
	Assert(myxid == MyProc->xid);

	oldestxid = TransamVariables->oldestXid;
	curXactCompletionCount = TransamVariables->xactCompletionCount;

	/* xmax is always latestCompletedXid + 1 */
	xmax = XidFromFullTransactionId(latest_completed);
	TransactionIdAdvance(xmax);
	Assert(TransactionIdIsNormal(xmax));

	/* initialize xmin calculation with xmax */
	xmin = xmax;

	/* take own xid into account, saves a check inside the loop */
	if (TransactionIdIsNormal(myxid) && NormalTransactionIdPrecedes(myxid, xmin))
		xmin = myxid;

	snapshot->takenDuringRecovery = RecoveryInProgress();

	if (!snapshot->takenDuringRecovery)
	{
		int			numProcs = arrayP->numProcs;
		TransactionId *xip = snapshot->xip;
		int		   *pgprocnos = arrayP->pgprocnos;
		XidCacheStatus *subxidStates = ProcGlobal->subxidStates;
		uint8	   *allStatusFlags = ProcGlobal->statusFlags;

		/*
		 * First collect set of pgxactoff/xids that need to be included in the
		 * snapshot.
		 */
		for (int pgxactoff = 0; pgxactoff < numProcs; pgxactoff++)
		{
			/* Fetch xid just once - see GetNewTransactionId */
			TransactionId xid = UINT32_ACCESS_ONCE(other_xids[pgxactoff]);
			uint8		statusFlags;

			Assert(allProcs[arrayP->pgprocnos[pgxactoff]].pgxactoff == pgxactoff);

			/*
			 * If the transaction has no XID assigned, we can skip it; it
			 * won't have sub-XIDs either.
			 */
			if (likely(xid == InvalidTransactionId))
				continue;

			/*
			 * We don't include our own XIDs (if any) in the snapshot. It
			 * needs to be included in the xmin computation, but we did so
			 * outside the loop.
			 */
			if (pgxactoff == mypgxactoff)
				continue;

			/*
			 * The only way we are able to get here with a non-normal xid is
			 * during bootstrap - with this backend using
			 * BootstrapTransactionId. But the above test should filter that
			 * out.
			 */
			Assert(TransactionIdIsNormal(xid));

			/*
			 * If the XID is >= xmax, we can skip it; such transactions will
			 * be treated as running anyway (and any sub-XIDs will also be >=
			 * xmax).
			 */
			if (!NormalTransactionIdPrecedes(xid, xmax))
				continue;

			/*
			 * Skip over backends doing logical decoding which manages xmin
			 * separately (check below) and ones running LAZY VACUUM.
			 */
			statusFlags = allStatusFlags[pgxactoff];
			if (statusFlags & (PROC_IN_LOGICAL_DECODING | PROC_IN_VACUUM))
				continue;

			if (NormalTransactionIdPrecedes(xid, xmin))
				xmin = xid;

			/* Add XID to snapshot. */
			xip[count++] = xid;

			/*
			 * Save subtransaction XIDs if possible (if we've already
			 * overflowed, there's no point).  Note that the subxact XIDs must
			 * be later than their parent, so no need to check them against
			 * xmin.  We could filter against xmax, but it seems better not to
			 * do that much work while holding the ProcArrayLock.
			 *
			 * The other backend can add more subxids concurrently, but cannot
			 * remove any.  Hence it's important to fetch nxids just once.
			 * Should be safe to use memcpy, though.  (We needn't worry about
			 * missing any xids added concurrently, because they must postdate
			 * xmax.)
			 *
			 * Again, our own XIDs are not included in the snapshot.
			 */
			if (!suboverflowed)
			{

				if (subxidStates[pgxactoff].overflowed)
					suboverflowed = true;
				else
				{
					int			nsubxids = subxidStates[pgxactoff].count;

					if (nsubxids > 0)
					{
						int			pgprocno = pgprocnos[pgxactoff];
						PGPROC	   *proc = &allProcs[pgprocno];

						pg_read_barrier();	/* pairs with GetNewTransactionId */

						memcpy(snapshot->subxip + subcount,
							   proc->subxids.xids,
							   nsubxids * sizeof(TransactionId));
						subcount += nsubxids;
					}
				}
			}
		}
	}
	else
	{
		/*
		 * We're in hot standby, so get XIDs from KnownAssignedXids.
		 *
		 * We store all xids directly into subxip[]. Here's why:
		 *
		 * In recovery we don't know which xids are top-level and which are
		 * subxacts, a design choice that greatly simplifies xid processing.
		 *
		 * It seems like we would want to try to put xids into xip[] only, but
		 * that is fairly small. We would either need to make that bigger or
		 * to increase the rate at which we WAL-log xid assignment; neither is
		 * an appealing choice.
		 *
		 * We could try to store xids into xip[] first and then into subxip[]
		 * if there are too many xids. That only works if the snapshot doesn't
		 * overflow because we do not search subxip[] in that case. A simpler
		 * way is to just store all xids in the subxip array because this is
		 * by far the bigger array. We just leave the xip array empty.
		 *
		 * Either way we need to change the way XidInMVCCSnapshot() works
		 * depending upon when the snapshot was taken, or change normal
		 * snapshot processing so it matches.
		 *
		 * Note: It is possible for recovery to end before we finish taking
		 * the snapshot, and for newly assigned transaction ids to be added to
		 * the ProcArray.  xmax cannot change while we hold ProcArrayLock, so
		 * those newly added transaction ids would be filtered away, so we
		 * need not be concerned about them.
		 */
		subcount = KnownAssignedXidsGetAndSetXmin(snapshot->subxip, &xmin,
												  xmax);

		if (TransactionIdPrecedesOrEquals(xmin, procArray->lastOverflowedXid))
			suboverflowed = true;
	}


	/*
	 * Fetch into local variable while ProcArrayLock is held - the
	 * LWLockRelease below is a barrier, ensuring this happens inside the
	 * lock.
	 */
	replication_slot_xmin = procArray->replication_slot_xmin;
	replication_slot_catalog_xmin = procArray->replication_slot_catalog_xmin;

	if (!TransactionIdIsValid(MyProc->xmin))
		MyProc->xmin = TransactionXmin = xmin;

	LWLockRelease(ProcArrayLock);

	/* maintain state for GlobalVis* */
	{
		TransactionId def_vis_xid;
		TransactionId def_vis_xid_data;
		FullTransactionId def_vis_fxid;
		FullTransactionId def_vis_fxid_data;
		FullTransactionId oldestfxid;

		/*
		 * Converting oldestXid is only safe when xid horizon cannot advance,
		 * i.e. holding locks. While we don't hold the lock anymore, all the
		 * necessary data has been gathered with lock held.
		 */
		oldestfxid = FullXidRelativeTo(latest_completed, oldestxid);

		/* Check whether there's a replication slot requiring an older xmin. */
		def_vis_xid_data =
			TransactionIdOlder(xmin, replication_slot_xmin);

		/*
		 * Rows in non-shared, non-catalog tables possibly could be vacuumed
		 * if older than this xid.
		 */
		def_vis_xid = def_vis_xid_data;

		/*
		 * Check whether there's a replication slot requiring an older catalog
		 * xmin.
		 */
		def_vis_xid =
			TransactionIdOlder(replication_slot_catalog_xmin, def_vis_xid);

		def_vis_fxid = FullXidRelativeTo(latest_completed, def_vis_xid);
		def_vis_fxid_data = FullXidRelativeTo(latest_completed, def_vis_xid_data);

		/*
		 * Check if we can increase upper bound. As a previous
		 * GlobalVisUpdate() might have computed more aggressive values, don't
		 * overwrite them if so.
		 */
		GlobalVisSharedRels.definitely_needed =
			FullTransactionIdNewer(def_vis_fxid,
								   GlobalVisSharedRels.definitely_needed);
		GlobalVisCatalogRels.definitely_needed =
			FullTransactionIdNewer(def_vis_fxid,
								   GlobalVisCatalogRels.definitely_needed);
		GlobalVisDataRels.definitely_needed =
			FullTransactionIdNewer(def_vis_fxid_data,
								   GlobalVisDataRels.definitely_needed);
		/* See temp_oldest_nonremovable computation in ComputeXidHorizons() */
		if (TransactionIdIsNormal(myxid))
			GlobalVisTempRels.definitely_needed =
				FullXidRelativeTo(latest_completed, myxid);
		else
		{
			GlobalVisTempRels.definitely_needed = latest_completed;
			FullTransactionIdAdvance(&GlobalVisTempRels.definitely_needed);
		}

		/*
		 * Check if we know that we can initialize or increase the lower
		 * bound. Currently the only cheap way to do so is to use
		 * TransamVariables->oldestXid as input.
		 *
		 * We should definitely be able to do better. We could e.g. put a
		 * global lower bound value into TransamVariables.
		 */
		GlobalVisSharedRels.maybe_needed =
			FullTransactionIdNewer(GlobalVisSharedRels.maybe_needed,
								   oldestfxid);
		GlobalVisCatalogRels.maybe_needed =
			FullTransactionIdNewer(GlobalVisCatalogRels.maybe_needed,
								   oldestfxid);
		GlobalVisDataRels.maybe_needed =
			FullTransactionIdNewer(GlobalVisDataRels.maybe_needed,
								   oldestfxid);
		/* accurate value known */
		GlobalVisTempRels.maybe_needed = GlobalVisTempRels.definitely_needed;
	}

	RecentXmin = xmin;
	Assert(TransactionIdPrecedesOrEquals(TransactionXmin, RecentXmin));

	snapshot->xmin = xmin;
	snapshot->xmax = xmax;
	snapshot->xcnt = count;
	snapshot->subxcnt = subcount;
	snapshot->suboverflowed = suboverflowed;
	snapshot->snapXactCompletionCount = curXactCompletionCount;

	snapshot->curcid = GetCurrentCommandId(false);

	/*
	 * This is a new snapshot, so set both refcounts are zero, and mark it as
	 * not copied in persistent memory.
	 */
	snapshot->active_count = 0;
	snapshot->regd_count = 0;
	snapshot->copied = false;

	return snapshot;
}

/*
 * ProcArrayInstallImportedXmin -- install imported xmin into MyProc->xmin
 *
 * This is called when installing a snapshot imported from another
 * transaction.  To ensure that OldestXmin doesn't go backwards, we must
 * check that the source transaction is still running, and we'd better do
 * that atomically with installing the new xmin.
 *
 * Returns true if successful, false if source xact is no longer running.
 */
/* (中文)把"从其他事务导入的 xmin"安装进 MyProc->xmin。
 *
 * 【作用】快照导入(snapshot import,如 REFRESH MATERIALIZED VIEW 的
 * CONCURRENTLY 或内部跨会话借用快照)时调用:先核对"源事务"仍活着
 * 且其 xmin 能覆盖我们,再把 xmin 写入 MyProc->xmin 与 TransactionXmin。
 * 失败(源事务已不在运行)时返回 false,由调用方决定如何处理。
 *
 * 【设计思想】
 * - 为什么要原子地做:全局最老 xmin(影响 VACUUM 清理边界)只允许
 *   后退、不允许前进。若源事务已结束,它的 xmin 对 VACUUM 已无约束,
 *   我们拿着它当自己的 xmin 会把全局下界"抬高"(变激进),可能删掉
 *   源事务仍在看的数据。因此必须在持 SHARED 锁期间验证源事务还在
 *   procarray 里(结束方要持 EXCLUSIVE 锁才能移除,互斥成立);
 * - 用 vxid(虚拟事务 id = procNumber + 本地事务号)而非 xid 标识源
 *   事务:源事务可能还没有分配 xid(只读事务);
 * - 源事务必须与本进程同库(异库会话的 xmin 不覆盖本库表),且其
 *   xmin 不晚于要导入的 xmin(否则说明它在保护更旧的数据,我们导入
 *   的是它的快照,取其最老的边界);
 * - VACUUM 进程(带 PROC_IN_VACUUM)被跳过:其 xmin 语义特殊。
 *
 * 【参数】
 *   xmin       —— 要安装的 xmin(须为正常 xid);
 *   sourcevxid —— 源事务的虚拟事务 id。
 * 【返回值】true = 安装成功;false = 源事务已不在运行或条件不满足。 */
bool
ProcArrayInstallImportedXmin(TransactionId xmin,
							 VirtualTransactionId *sourcevxid)
{
	bool		result = false;
	ProcArrayStruct *arrayP = procArray;
	int			index;

	Assert(TransactionIdIsNormal(xmin));
	if (!sourcevxid)
		return false;

	/* Get lock so source xact can't end while we're doing this */
	LWLockAcquire(ProcArrayLock, LW_SHARED);

	/*
	 * Find the PGPROC entry of the source transaction. (This could use
	 * GetPGProcByNumber(), unless it's a prepared xact.  But this isn't
	 * performance critical.)
	 */
	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];
		int			statusFlags = ProcGlobal->statusFlags[index];
		TransactionId xid;

		/* Ignore procs running LAZY VACUUM */
		if (statusFlags & PROC_IN_VACUUM)
			continue;

		/* We are only interested in the specific virtual transaction. */
		if (proc->vxid.procNumber != sourcevxid->procNumber)
			continue;
		if (proc->vxid.lxid != sourcevxid->localTransactionId)
			continue;

		/*
		 * We check the transaction's database ID for paranoia's sake: if it's
		 * in another DB then its xmin does not cover us.  Caller should have
		 * detected this already, so we just treat any funny cases as
		 * "transaction not found".
		 */
		if (proc->databaseId != MyDatabaseId)
			continue;

		/*
		 * Likewise, let's just make real sure its xmin does cover us.
		 */
		xid = UINT32_ACCESS_ONCE(proc->xmin);
		if (!TransactionIdIsNormal(xid) ||
			!TransactionIdPrecedesOrEquals(xid, xmin))
			continue;

		/*
		 * We're good.  Install the new xmin.  As in GetSnapshotData, set
		 * TransactionXmin too.  (Note that because snapmgr.c called
		 * GetSnapshotData first, we'll be overwriting a valid xmin here, so
		 * we don't check that.)
		 */
		MyProc->xmin = TransactionXmin = xmin;

		result = true;
		break;
	}

	LWLockRelease(ProcArrayLock);

	return result;
}

/*
 * ProcArrayInstallRestoredXmin -- install restored xmin into MyProc->xmin
 *
 * This is like ProcArrayInstallImportedXmin, but we have a pointer to the
 * PGPROC of the transaction from which we imported the snapshot, rather than
 * an XID.
 *
 * Note that this function also copies statusFlags from the source `proc` in
 * order to avoid the case where MyProc's xmin needs to be skipped for
 * computing xid horizon.
 *
 * Returns true if successful, false if source xact is no longer running.
 */
/* (中文)把"恢复的 xmin"安装进 MyProc->xmin(ProcArrayInstallImportedXmin
 * 的变体:直接持有源事务的 PGPROC 指针)。
 *
 * 【作用】与 ProcArrayInstallImportedXmin 相同(安装 xmin,防止全局
 * xmin 后退),但源事务是直接以 PGPROC 指针给出的;此外还会把源
 * PGPROC 的 statusFlags 中影响 xmin 解释的位(PROC_XMIN_FLAGS)复制
 * 过来——这些标志(如"xmin 是否为 VACUUM 相关")决定水位计算时该
 * 后端要不要被跳过,不复制会导致 MyProc 的 xmin 被错误对待。
 *
 * 【设计思想】
 * - 取 EXCLUSIVE 锁而不是 SHARED:要写 MyProc->statusFlags 与
 *   ProcGlobal->statusFlags[pgxactoff],两者是并行数组的关系;
 * - 同样的前提校验:同库、xmin 有效且不晚于要安装的值(防止全局与
 *   库级 xmin 后退)。
 *
 * 【参数】
 *   xmin —— 要安装的 xmin(须为正常 xid);
 *   proc —— 源事务的 PGPROC(不能为 NULL)。
 * 【返回值】true = 安装成功;false = 源事务已不在运行或条件不满足。 */
bool
ProcArrayInstallRestoredXmin(TransactionId xmin, PGPROC *proc)
{
	bool		result = false;
	TransactionId xid;

	Assert(TransactionIdIsNormal(xmin));
	Assert(proc != NULL);

	/*
	 * Get an exclusive lock so that we can copy statusFlags from source proc.
	 */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	/*
	 * Be certain that the referenced PGPROC has an advertised xmin which is
	 * no later than the one we're installing, so that the system-wide xmin
	 * can't go backwards.  Also, make sure it's running in the same database,
	 * so that the per-database xmin cannot go backwards.
	 */
	xid = UINT32_ACCESS_ONCE(proc->xmin);
	if (proc->databaseId == MyDatabaseId &&
		TransactionIdIsNormal(xid) &&
		TransactionIdPrecedesOrEquals(xid, xmin))
	{
		/*
		 * Install xmin and propagate the statusFlags that affect how the
		 * value is interpreted by vacuum.
		 */
		MyProc->xmin = TransactionXmin = xmin;
		MyProc->statusFlags = (MyProc->statusFlags & ~PROC_XMIN_FLAGS) |
			(proc->statusFlags & PROC_XMIN_FLAGS);
		ProcGlobal->statusFlags[MyProc->pgxactoff] = MyProc->statusFlags;

		result = true;
	}

	LWLockRelease(ProcArrayLock);

	return result;
}

/*
 * GetRunningTransactionData -- returns information about running transactions.
 *
 * Similar to GetSnapshotData but returns more information. We include
 * all PGPROCs with an assigned TransactionId, even VACUUM processes and
 * prepared transactions.
 *
 * We acquire XidGenLock and ProcArrayLock, but the caller is responsible for
 * releasing them. Acquiring XidGenLock ensures that no new XIDs enter the proc
 * array until the caller has WAL-logged this snapshot, and releases the
 * lock. Acquiring ProcArrayLock ensures that no transactions commit until the
 * lock is released.
 *
 * The returned data structure is statically allocated; caller should not
 * modify it, and must not assume it is valid past the next call.
 *
 * This is never executed during recovery so there is no need to look at
 * KnownAssignedXids.
 *
 * Dummy PGPROCs from prepared transaction are included, meaning that this
 * may return entries with duplicated TransactionId values coming from
 * transaction finishing to prepare.  Nothing is done about duplicated
 * entries here to not hold on ProcArrayLock more than necessary.
 *
 * We don't worry about updating other counters, we want to keep this as
 * simple as possible and leave GetSnapshotData() as the primary code for
 * that bookkeeping.
 *
 * Note that if any transaction has overflowed its cached subtransactions
 * then there is no real need include any subtransactions.
 */
/* (中文)返回"运行事务数据"(RUNNING_XACTS 快照素材):比
 * GetSnapshotData 信息更全、专供 WAL 日志记录用。
 *
 * 【作用】checkpoint / 周期性日志运行时调用,生成主库发送给备机的
 * RunningTransactionsData:
 * - 包含所有持有 xid 的 PGPROC,包括 VACUUM 进程与 prepared 事务
 *   (备机需要完整信息来初始化 KnownAssignedXids);
 * - 记录 oldestRunningXid(清理备机过期数据用)、oldestDatabaseRunningXid
 *   (本库的最老运行 xid,用于获取各库 xmin 反馈)、latestCompletedXid、
 *   nextXid 与 xcnt/subxcnt/subxid_status;
 * - 子事务缓存有溢出时不再收集子事务(subxid_status = SUBXIDS_IN_SUBTRANS,
 *   备机据此把快照标记为"子事务不完整")。
 *
 * 【设计思想】
 * - 持 XidGenLock SHARED + ProcArrayLock SHARED,但不释放、交还调用
 *   方:调用方要先把这份快照写进 WAL,再释放锁。XidGenLock 保证写
 *   WAL 期间没有新 xid 进入数组(否则备机可能漏掉),ProcArrayLock
 *   保证没有事务提交;
 * - 故意不把复制槽水位算进 oldestRunningXid:槽位的 xmin 只增不减,
 *   若算进去会和 running xacts 互相牵制形成死锁般的循环(见英文注释);
 * - 结果存放在静态的 RunningTransactionsData 里,反复复用同一块
 *   xids 缓冲,调用方不得跨调用保留结果;
 * - 恢复期不执行本函数,无需考虑 KnownAssignedXids;由于 prepared
 *   事务的 gxact 与真实后端可能持同一 xid,结果中可能含重复 xid,
 *   不去重(不为去重多持锁,备机侧 ProcArrayApplyRecoveryInfo 会去重)。
 *
 * 【参数】无。
 * 【返回值】填充好的 RunningTransactions(静态存储,调用方负责在返回
 *         后先记 WAL 再释放两个锁)。 */
RunningTransactions
GetRunningTransactionData(void)
{
	/* result workspace */
	static RunningTransactionsData CurrentRunningXactsData;

	ProcArrayStruct *arrayP = procArray;
	TransactionId *other_xids = ProcGlobal->xids;
	RunningTransactions CurrentRunningXacts = &CurrentRunningXactsData;
	TransactionId latestCompletedXid;
	TransactionId oldestRunningXid;
	TransactionId oldestDatabaseRunningXid;
	TransactionId *xids;
	int			index;
	int			count;
	int			subcount;
	bool		suboverflowed;

	Assert(!RecoveryInProgress());

	/*
	 * Allocating space for maxProcs xids is usually overkill; numProcs would
	 * be sufficient.  But it seems better to do the malloc while not holding
	 * the lock, so we can't look at numProcs.  Likewise, we allocate much
	 * more subxip storage than is probably needed.
	 *
	 * Should only be allocated in bgwriter, since only ever executed during
	 * checkpoints.
	 */
	if (CurrentRunningXacts->xids == NULL)
	{
		/*
		 * First call
		 */
		CurrentRunningXacts->xids = (TransactionId *)
			malloc(TOTAL_MAX_CACHED_SUBXIDS * sizeof(TransactionId));
		if (CurrentRunningXacts->xids == NULL)
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of memory")));
	}

	xids = CurrentRunningXacts->xids;

	count = subcount = 0;
	suboverflowed = false;

	/*
	 * Ensure that no xids enter or leave the procarray while we obtain
	 * snapshot.
	 */
	LWLockAcquire(ProcArrayLock, LW_SHARED);
	LWLockAcquire(XidGenLock, LW_SHARED);

	latestCompletedXid =
		XidFromFullTransactionId(TransamVariables->latestCompletedXid);
	oldestDatabaseRunningXid = oldestRunningXid =
		XidFromFullTransactionId(TransamVariables->nextXid);

	/*
	 * Spin over procArray collecting all xids
	 */
	for (index = 0; index < arrayP->numProcs; index++)
	{
		TransactionId xid;

		/* Fetch xid just once - see GetNewTransactionId */
		xid = UINT32_ACCESS_ONCE(other_xids[index]);

		/*
		 * We don't need to store transactions that don't have a TransactionId
		 * yet because they will not show as running on a standby server.
		 */
		if (!TransactionIdIsValid(xid))
			continue;

		/*
		 * Be careful not to exclude any xids before calculating the values of
		 * oldestRunningXid and suboverflowed, since these are used to clean
		 * up transaction information held on standbys.
		 */
		if (TransactionIdPrecedes(xid, oldestRunningXid))
			oldestRunningXid = xid;

		/*
		 * Also, update the oldest running xid within the current database. As
		 * fetching pgprocno and PGPROC could cause cache misses, we do cheap
		 * TransactionId comparison first.
		 */
		if (TransactionIdPrecedes(xid, oldestDatabaseRunningXid))
		{
			int			pgprocno = arrayP->pgprocnos[index];
			PGPROC	   *proc = &allProcs[pgprocno];

			if (proc->databaseId == MyDatabaseId)
				oldestDatabaseRunningXid = xid;
		}

		if (ProcGlobal->subxidStates[index].overflowed)
			suboverflowed = true;

		/*
		 * If we wished to exclude xids this would be the right place for it.
		 * Procs with the PROC_IN_VACUUM flag set don't usually assign xids,
		 * but they do during truncation at the end when they get the lock and
		 * truncate, so it is not much of a problem to include them if they
		 * are seen and it is cleaner to include them.
		 */

		xids[count++] = xid;
	}

	/*
	 * Spin over procArray collecting all subxids, but only if there hasn't
	 * been a suboverflow.
	 */
	if (!suboverflowed)
	{
		XidCacheStatus *other_subxidstates = ProcGlobal->subxidStates;

		for (index = 0; index < arrayP->numProcs; index++)
		{
			int			pgprocno = arrayP->pgprocnos[index];
			PGPROC	   *proc = &allProcs[pgprocno];
			int			nsubxids;

			/*
			 * Save subtransaction XIDs. Other backends can't add or remove
			 * entries while we're holding XidGenLock.
			 */
			nsubxids = other_subxidstates[index].count;
			if (nsubxids > 0)
			{
				/* barrier not really required, as XidGenLock is held, but ... */
				pg_read_barrier();	/* pairs with GetNewTransactionId */

				memcpy(&xids[count], proc->subxids.xids,
					   nsubxids * sizeof(TransactionId));
				count += nsubxids;
				subcount += nsubxids;

				/*
				 * Top-level XID of a transaction is always less than any of
				 * its subxids, so we don't need to check if any of the
				 * subxids are smaller than oldestRunningXid
				 */
			}
		}
	}

	/*
	 * It's important *not* to include the limits set by slots here because
	 * snapbuild.c uses oldestRunningXid to manage its xmin horizon. If those
	 * were to be included here the initial value could never increase because
	 * of a circular dependency where slots only increase their limits when
	 * running xacts increases oldestRunningXid and running xacts only
	 * increases if slots do.
	 */

	CurrentRunningXacts->xcnt = count - subcount;
	CurrentRunningXacts->subxcnt = subcount;
	CurrentRunningXacts->subxid_status = suboverflowed ? SUBXIDS_IN_SUBTRANS : SUBXIDS_IN_ARRAY;
	CurrentRunningXacts->nextXid = XidFromFullTransactionId(TransamVariables->nextXid);
	CurrentRunningXacts->oldestRunningXid = oldestRunningXid;
	CurrentRunningXacts->oldestDatabaseRunningXid = oldestDatabaseRunningXid;
	CurrentRunningXacts->latestCompletedXid = latestCompletedXid;

	Assert(TransactionIdIsValid(CurrentRunningXacts->nextXid));
	Assert(TransactionIdIsValid(CurrentRunningXacts->oldestRunningXid));
	Assert(TransactionIdIsNormal(CurrentRunningXacts->latestCompletedXid));

	/* We don't release the locks here, the caller is responsible for that */

	return CurrentRunningXacts;
}

/*
 * GetOldestActiveTransactionId()
 *
 * Similar to GetSnapshotData but returns just oldestActiveXid. We include
 * all PGPROCs with an assigned TransactionId, even VACUUM processes.
 *
 * If allDbs is true, we look at all databases, though there is no need to
 * include WALSender since this has no effect on hot standby conflicts. If
 * allDbs is false, skip processes attached to other databases.
 *
 * This is never executed during recovery so there is no need to look at
 * KnownAssignedXids.
 *
 * We don't worry about updating other counters, we want to keep this as
 * simple as possible and leave GetSnapshotData() as the primary code for
 * that bookkeeping.
 *
 * inCommitOnly indicates getting the oldestActiveXid among the transactions
 * in the commit critical section.
 */
/* (中文)返回当前仍活跃的最老事务 xid(简化版 GetSnapshotData)。
 *
 * 【作用】遍历进程数组收集所有合法 xid 的最小值(初始化为 nextXid,
 * 即"仍可能活跃"的天然上界)。与 GetSnapshotData 不同,它不区分
 * 主/子事务、不跳过 VACUUM 进程,也不更新任何全局计数器。
 *
 * 【设计思想】
 * - 先读 nextXid 再遍历:必须保证"小于 nextXid 的 xid 要么已在数组
 *   里、要么已完成",否则会漏算(加 XidGenLock 短锁);
 * - inCommitOnly = true 时只看处于提交临界区(DELAY_CHKPT_IN_COMMIT)
 *   的事务:这是 checkpoint 判断"是否可以立刻推进 checkpoint 位置"
 *   的专用查询——只关心正准备提交的事务;
 * - allDbs = false 时跳过其他库的后端(热备冲突判定只需本库);
 *   walsender 无需计入(它不影响冲突判定)。
 * - 恢复期不执行(备机的运行事务由 KnownAssignedXids 表达)。
 *
 * 【参数】
 *   inCommitOnly —— true 时只统计处于提交临界区的事务;
 *   allDbs       —— true 时统计所有库,false 时只统计本库。
 * 【返回值】最老活跃事务的 xid。 */
TransactionId
GetOldestActiveTransactionId(bool inCommitOnly, bool allDbs)
{
	ProcArrayStruct *arrayP = procArray;
	TransactionId *other_xids = ProcGlobal->xids;
	TransactionId oldestRunningXid;
	int			index;

	Assert(!RecoveryInProgress());

	/*
	 * Read nextXid, as the upper bound of what's still active.
	 *
	 * Reading a TransactionId is atomic, but we must grab the lock to make
	 * sure that all XIDs < nextXid are already present in the proc array (or
	 * have already completed), when we spin over it.
	 */
	LWLockAcquire(XidGenLock, LW_SHARED);
	oldestRunningXid = XidFromFullTransactionId(TransamVariables->nextXid);
	LWLockRelease(XidGenLock);

	/*
	 * Spin over procArray collecting all xids and subxids.
	 */
	LWLockAcquire(ProcArrayLock, LW_SHARED);
	for (index = 0; index < arrayP->numProcs; index++)
	{
		TransactionId xid;
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];

		/* Fetch xid just once - see GetNewTransactionId */
		xid = UINT32_ACCESS_ONCE(other_xids[index]);

		if (!TransactionIdIsNormal(xid))
			continue;

		if (inCommitOnly &&
			(proc->delayChkptFlags & DELAY_CHKPT_IN_COMMIT) == 0)
			continue;

		if (!allDbs && proc->databaseId != MyDatabaseId)
			continue;

		if (TransactionIdPrecedes(xid, oldestRunningXid))
			oldestRunningXid = xid;

		/*
		 * Top-level XID of a transaction is always less than any of its
		 * subxids, so we don't need to check if any of the subxids are
		 * smaller than oldestRunningXid
		 */
	}
	LWLockRelease(ProcArrayLock);

	return oldestRunningXid;
}

/*
 * GetOldestSafeDecodingTransactionId -- lowest xid not affected by vacuum
 *
 * Returns the oldest xid that we can guarantee not to have been affected by
 * vacuum, i.e. no rows >= that xid have been vacuumed away unless the
 * transaction aborted. Note that the value can (and most of the time will) be
 * much more conservative than what really has been affected by vacuum, but we
 * currently don't have better data available.
 *
 * This is useful to initialize the cutoff xid after which a new changeset
 * extraction replication slot can start decoding changes.
 *
 * Must be called with ProcArrayLock held either shared or exclusively,
 * although most callers will want to use exclusive mode since it is expected
 * that the caller will immediately use the xid to peg the xmin horizon.
 */
/* (中文)返回"可保证未被 VACUUM 影响"的最老 xid(新建逻辑复制槽时的
 * 起始解码水位)。
 *
 * 【作用】新建 changeset extraction 复制槽时,用返回值初始化解码的
 * cutoff xid:任何 >= 该值的行都保证还没被 VACUUM 清掉(除非所属事务
 * 已中止),从它之后开始解码不会漏数据。注意该值通常比真实情况保守
 * 得多(见英文注释)。
 *
 * 【设计思想】
 * - 初始化为 nextXid(必然安全的保守值),再取复制槽已有的 xmin
 *   与其比较取更小(已有槽保护的数据也一并保护);catalogOnly 时
 *   再考虑槽位的 catalog_xmin;
 * - 非恢复期再遍历进程数组取所有正常 xid 的最小值:由于调用方已持
 *   ProcArrayLock 且本函数再拿 XidGenLock,条目不会凭空消失或增加
 *   (ProcGlobal->xids[i] 的设置持 XidGenLock、清除持 ProcArrayLock,
 *   见英文注释);
 * - 恢复期不能再用 KnownAssignedXids 求最老值:该机制可能漏值,给出
 *   的"最老"不可靠(见英文注释),只能停留在上面算出的保守值,等
 *   恢复结束后再精确化。
 *
 * 【参数】catalogOnly —— true 时把槽位 catalog_xmin 也算入保护。
 * 【返回值】最老的、保证未被 VACUUM 影响过的 xid。 */
TransactionId
GetOldestSafeDecodingTransactionId(bool catalogOnly)
{
	ProcArrayStruct *arrayP = procArray;
	TransactionId oldestSafeXid;
	int			index;
	bool		recovery_in_progress = RecoveryInProgress();

	Assert(LWLockHeldByMe(ProcArrayLock));

	/*
	 * Acquire XidGenLock, so no transactions can acquire an xid while we're
	 * running. If no transaction with xid were running concurrently a new xid
	 * could influence the RecentXmin et al.
	 *
	 * We initialize the computation to nextXid since that's guaranteed to be
	 * a safe, albeit pessimal, value.
	 */
	LWLockAcquire(XidGenLock, LW_SHARED);
	oldestSafeXid = XidFromFullTransactionId(TransamVariables->nextXid);

	/*
	 * If there's already a slot pegging the xmin horizon, we can start with
	 * that value, it's guaranteed to be safe since it's computed by this
	 * routine initially and has been enforced since.  We can always use the
	 * slot's general xmin horizon, but the catalog horizon is only usable
	 * when only catalog data is going to be looked at.
	 */
	if (TransactionIdIsValid(procArray->replication_slot_xmin) &&
		TransactionIdPrecedes(procArray->replication_slot_xmin,
							  oldestSafeXid))
		oldestSafeXid = procArray->replication_slot_xmin;

	if (catalogOnly &&
		TransactionIdIsValid(procArray->replication_slot_catalog_xmin) &&
		TransactionIdPrecedes(procArray->replication_slot_catalog_xmin,
							  oldestSafeXid))
		oldestSafeXid = procArray->replication_slot_catalog_xmin;

	/*
	 * If we're not in recovery, we walk over the procarray and collect the
	 * lowest xid. Since we're called with ProcArrayLock held and have
	 * acquired XidGenLock, no entries can vanish concurrently, since
	 * ProcGlobal->xids[i] is only set with XidGenLock held and only cleared
	 * with ProcArrayLock held.
	 *
	 * In recovery we can't lower the safe value besides what we've computed
	 * above, so we'll have to wait a bit longer there. We unfortunately can
	 * *not* use KnownAssignedXidsGetOldestXmin() since the KnownAssignedXids
	 * machinery can miss values and return an older value than is safe.
	 */
	if (!recovery_in_progress)
	{
		TransactionId *other_xids = ProcGlobal->xids;

		/*
		 * Spin over procArray collecting min(ProcGlobal->xids[i])
		 */
		for (index = 0; index < arrayP->numProcs; index++)
		{
			TransactionId xid;

			/* Fetch xid just once - see GetNewTransactionId */
			xid = UINT32_ACCESS_ONCE(other_xids[index]);

			if (!TransactionIdIsNormal(xid))
				continue;

			if (TransactionIdPrecedes(xid, oldestSafeXid))
				oldestSafeXid = xid;
		}
	}

	LWLockRelease(XidGenLock);

	return oldestSafeXid;
}

/*
 * GetVirtualXIDsDelayingChkpt -- Get the VXIDs of transactions that are
 * delaying checkpoint because they have critical actions in progress.
 *
 * Constructs an array of VXIDs of transactions that are currently in commit
 * critical sections, as shown by having specified delayChkptFlags bits set
 * in their PGPROC.
 *
 * Returns a palloc'd array that should be freed by the caller.
 * *nvxids is the number of valid entries.
 *
 * Note that because backends set or clear delayChkptFlags without holding any
 * lock, the result is somewhat indeterminate, but we don't really care.  Even
 * in a multiprocessor with delayed writes to shared memory, it should be
 * certain that setting of delayChkptFlags will propagate to shared memory
 * when the backend takes a lock, so we cannot fail to see a virtual xact as
 * delayChkptFlags if it's already inserted its commit record.  Whether it
 * takes a little while for clearing of delayChkptFlags to propagate is
 * unimportant for correctness.
 */
/* (中文)收集"正在拖延 checkpoint 的事务"的虚拟事务 id(VXID)列表。
 *
 * 【作用】checkpoint 推进前调用:找出所有 PGPROC 中 delayChkptFlags
 * 带有指定 type 位的后端(即正处在提交临界区、尚未完成关键 WAL 写入
 * 的事务),返回它们的 VXID 数组。checkpoint 得到空列表才敢推进。
 *
 * 【设计思想】
 * - 用 VXID 而非 xid:提交临界区可能跨越"分配 xid"这个时点,用虚拟
 *   事务 id 才稳定可比较;
 * - delayChkptFlags 的置位/清除不加锁,结果"有点模糊",但语义足够:
 *   只要提交记录已插入,WAL 里就有它,是否立刻看到标志位只影响
 *   checkpoint 多等一轮,不影响正确性(见英文注释);
 * - 结果数组按 maxProcs 大小 palloc(必然够装),由调用方负责释放。
 *
 * 【参数】
 *   nvxids —— 输出:有效条目数;
 *   type   —— 要匹配的 delayChkptFlags 位掩码(非零)。
 * 【返回值】VXID 数组(palloc 分配,调用方释放)。 */
VirtualTransactionId *
GetVirtualXIDsDelayingChkpt(int *nvxids, int type)
{
	VirtualTransactionId *vxids;
	ProcArrayStruct *arrayP = procArray;
	int			count = 0;
	int			index;

	Assert(type != 0);

	/* allocate what's certainly enough result space */
	vxids = palloc_array(VirtualTransactionId, arrayP->maxProcs);

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];

		if ((proc->delayChkptFlags & type) != 0)
		{
			VirtualTransactionId vxid;

			GET_VXID_FROM_PGPROC(vxid, *proc);
			if (VirtualTransactionIdIsValid(vxid))
				vxids[count++] = vxid;
		}
	}

	LWLockRelease(ProcArrayLock);

	*nvxids = count;
	return vxids;
}

/*
 * HaveVirtualXIDsDelayingChkpt -- Are any of the specified VXIDs delaying?
 *
 * This is used with the results of GetVirtualXIDsDelayingChkpt to see if any
 * of the specified VXIDs are still in critical sections of code.
 *
 * Note: this is O(N^2) in the number of vxacts that are/were delaying, but
 * those numbers should be small enough for it not to be a problem.
 */
/* (中文)检查指定的 VXID 们是否仍有事务在拖延 checkpoint。
 *
 * 【作用】与 GetVirtualXIDsDelayingChkpt 配套使用:把上次收集到的
 * VXID 列表与本轮扫描到的"仍处于临界区"的 VXID 求交集,返回是否有
 * 任一命中。checkpoint 用它循环等待"上一批拖延者全部退出临界区"。
 *
 * 【设计思想】O(N^2) 的双重循环(对每个当前拖延者线性查传入列表),
 * 但拖延者数量级很小,不值得为此引入哈希表(见英文注释)。
 *
 * 【参数】
 *   vxids  —— 要检查的 VXID 列表;
 *   nvxids —— 列表长度;
 *   type   —— delayChkptFlags 位掩码(非零)。
 * 【返回值】true = 列表中有 VXID 仍处于临界区。 */
bool
HaveVirtualXIDsDelayingChkpt(VirtualTransactionId *vxids, int nvxids, int type)
{
	bool		result = false;
	ProcArrayStruct *arrayP = procArray;
	int			index;

	Assert(type != 0);

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];
		VirtualTransactionId vxid;

		GET_VXID_FROM_PGPROC(vxid, *proc);

		if ((proc->delayChkptFlags & type) != 0 &&
			VirtualTransactionIdIsValid(vxid))
		{
			int			i;

			for (i = 0; i < nvxids; i++)
			{
				if (VirtualTransactionIdEquals(vxid, vxids[i]))
				{
					result = true;
					break;
				}
			}
			if (result)
				break;
		}
	}

	LWLockRelease(ProcArrayLock);

	return result;
}

/*
 * ProcNumberGetProc -- get a backend's PGPROC given its proc number
 *
 * The result may be out of date arbitrarily quickly, so the caller
 * must be careful about how this information is used.  NULL is
 * returned if the backend is not active.
 */
/* (中文)按进程号(procNumber)取得某后端的 PGPROC。
 *
 * 【作用】把"全局 PGPROC 数组下标"翻译成 PGPROC 指针,并过滤掉
 * 不活跃的条目:进程号越界或对应 PGPROC 的 pid == 0(prepared 事务
 * 占位或空闲槽)时返回 NULL。
 *
 * 【设计思想】返回的指针可能立刻过期(对方随时退出、槽位被复用),
 * 调用方必须自己保证"问题在一段时间内仍有意义";pid == 0 既是
 * "dummy PGPROC"的标志也是"空闲槽"的标志,不能当活跃后端返回。
 * 不加锁(返回后锁也没有意义)。
 *
 * 【参数】procNumber —— 目标进程号(0 基)。
 * 【返回值】对应 PGPROC 指针;无效或非活跃返回 NULL。 */
PGPROC *
ProcNumberGetProc(ProcNumber procNumber)
{
	PGPROC	   *result;

	if (procNumber < 0 || procNumber >= ProcGlobal->allProcCount)
		return NULL;
	result = GetPGProcByNumber(procNumber);

	if (result->pid == 0)
		return NULL;

	return result;
}

/*
 * ProcNumberGetTransactionIds -- get a backend's transaction status
 *
 * Get the xid, xmin, nsubxid and overflow status of the backend.  The
 * result may be out of date arbitrarily quickly, so the caller must be
 * careful about how this information is used.
 */
/* (中文)按进程号取某后端的事务状态(xid、xmin、子事务数与溢出标志)。
 *
 * 【作用】把指定 PGPROC 的事务字段整体读出(通过输出参数返回)。
 * 进程号越界或后端不活跃时,输出参数保持初值(xid/xmin 为
 * InvalidTransactionId、子事务数 0、未溢出)。
 *
 * 【设计思想】读 PGPROC 时短暂持有 ProcArrayLock SHARED,把"后端
 * 进/出数组"的窗口排除掉,保证读到的字段来自同一时刻(避免读到
 * 正在被 ProcArrayRemove 搬移的条目);PGPROC 里的事务字段本身由
 * 各进程自己写,这里只要求"条目还在数组里"。
 *
 * 【参数】
 *   procNumber —— 目标进程号;
 *   xid/xmin/nsubxid/overflowed —— 四个输出参数,含义同 PGPROC 字段。
 * 【返回值】无。 */
void
ProcNumberGetTransactionIds(ProcNumber procNumber, TransactionId *xid,
							TransactionId *xmin, int *nsubxid, bool *overflowed)
{
	PGPROC	   *proc;

	*xid = InvalidTransactionId;
	*xmin = InvalidTransactionId;
	*nsubxid = 0;
	*overflowed = false;

	if (procNumber < 0 || procNumber >= ProcGlobal->allProcCount)
		return;
	proc = GetPGProcByNumber(procNumber);

	/* Need to lock out additions/removals of backends */
	LWLockAcquire(ProcArrayLock, LW_SHARED);

	if (proc->pid != 0)
	{
		*xid = proc->xid;
		*xmin = proc->xmin;
		*nsubxid = proc->subxidStatus.count;
		*overflowed = proc->subxidStatus.overflowed;
	}

	LWLockRelease(ProcArrayLock);
}

/*
 * BackendPidGetProc -- get a backend's PGPROC given its PID
 *
 * Returns NULL if not found.  Note that it is up to the caller to be
 * sure that the question remains meaningful for long enough for the
 * answer to be used ...
 */
/* (中文)按操作系统 PID 查找后端 PGPROC(带锁版本)。
 *
 * 【作用】在进程数组中线性查找 pid 匹配的 PGPROC,返回指针;找不到
 * (或 pid == 0,用于排除 dummy PGPROC)返回 NULL。内部对
 * BackendPidGetProcWithLock 做了一次 SHARED 加锁/解锁包装。
 *
 * 【设计思想】返回的指针在锁释放后就可能失效(后端随时退出),调用方
 * 必须自行保证答案在使用期间仍有意义(见英文注释)。
 *
 * 【参数】pid —— 目标进程的操作系统 PID。
 * 【返回值】匹配的 PGPROC 指针,或 NULL。 */
PGPROC *
BackendPidGetProc(int pid)
{
	PGPROC	   *result;

	if (pid == 0)				/* never match dummy PGPROCs */
		return NULL;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	result = BackendPidGetProcWithLock(pid);

	LWLockRelease(ProcArrayLock);

	return result;
}

/*
 * BackendPidGetProcWithLock -- get a backend's PGPROC given its PID
 *
 * Same as above, except caller must be holding ProcArrayLock.  The found
 * entry, if any, can be assumed to be valid as long as the lock remains held.
 */
/* (中文)按 PID 查找后端 PGPROC(调用方已持锁版本)。
 *
 * 【作用】BackendPidGetProc 的内部实现:假定调用方已持有 ProcArrayLock
 * (任意模式),直接线性扫描 pgprocnos[] 找 pid 匹配的后端。
 *
 * 【设计思想】pid == 0 的 PGPROC 是 prepared 事务占位(dummy),永不该
 * 匹配,直接短路返回 NULL;找到的条目只要锁还持有就保证未被移除,
 * 这正是把扫描放在锁内的意义。
 *
 * 【参数】pid —— 目标进程的操作系统 PID。
 * 【返回值】匹配的 PGPROC 指针,或 NULL。 */
PGPROC *
BackendPidGetProcWithLock(int pid)
{
	PGPROC	   *result = NULL;
	ProcArrayStruct *arrayP = procArray;
	int			index;

	if (pid == 0)				/* never match dummy PGPROCs */
		return NULL;

	for (index = 0; index < arrayP->numProcs; index++)
	{
		PGPROC	   *proc = &allProcs[arrayP->pgprocnos[index]];

		if (proc->pid == pid)
		{
			result = proc;
			break;
		}
	}

	return result;
}

/*
 * BackendXidGetPid -- get a backend's pid given its XID
 *
 * Returns 0 if not found or it's a prepared transaction.  Note that
 * it is up to the caller to be sure that the question remains
 * meaningful for long enough for the answer to be used ...
 *
 * Only main transaction Ids are considered.  This function is mainly
 * useful for determining what backend owns a lock.
 *
 * Beware that not every xact has an XID assigned.  However, as long as you
 * only call this using an XID found on disk, you're safe.
 */
/* (中文)按 xid 查找持有它的后端 PID。
 *
 * 【作用】在 ProcGlobal->xids[] 中找给定主事务 xid,返回对应后端的
 * 操作系统 PID;没找到或 xid 非法返回 0。prepared 事务的 pid 为 0,
 * 天然与"未找到"同值(调用方按语义自行区分,见英文注释)。
 *
 * 【设计思想】只匹配"主事务 xid"(数组里就是主 xid,子事务在各自
 * 缓存里),常用于"这把锁被哪个后端持有"的排查;并非所有事务都有
 * xid,但磁盘上找到的 xid 一定被分配过,此时调用是安全的(见英文
 * 注释)。
 *
 * 【参数】xid —— 要查找的主事务 xid。
 * 【返回值】持有该 xid 的后端 PID;0 = 未找到或非法输入。 */
int
BackendXidGetPid(TransactionId xid)
{
	int			result = 0;
	ProcArrayStruct *arrayP = procArray;
	TransactionId *other_xids = ProcGlobal->xids;
	int			index;

	if (xid == InvalidTransactionId)	/* never match invalid xid */
		return 0;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		if (other_xids[index] == xid)
		{
			int			pgprocno = arrayP->pgprocnos[index];
			PGPROC	   *proc = &allProcs[pgprocno];

			result = proc->pid;
			break;
		}
	}

	LWLockRelease(ProcArrayLock);

	return result;
}

/*
 * IsBackendPid -- is a given pid a running backend
 *
 * This is not called by the backend, but is called by external modules.
 */
/* (中文)判断给定的 PID 是否是一个正在运行的后端。
 *
 * 【作用】外部模块(如复制管理)查询 pid 是否对应某个活跃后端。
 * 实现就是 BackendPidGetProc() != NULL 的一次薄封装。
 *
 * 【参数】pid —— 要查询的进程 PID。
 * 【返回值】true = 该 PID 正被某个活跃后端使用。 */
bool
IsBackendPid(int pid)
{
	return (BackendPidGetProc(pid) != NULL);
}


/*
 * GetCurrentVirtualXIDs -- returns an array of currently active VXIDs.
 *
 * The array is palloc'd. The number of valid entries is returned into *nvxids.
 *
 * The arguments allow filtering the set of VXIDs returned.  Our own process
 * is always skipped.  In addition:
 *	If limitXmin is not InvalidTransactionId, skip processes with
 *		xmin > limitXmin.
 *	If excludeXmin0 is true, skip processes with xmin = 0.
 *	If allDbs is false, skip processes attached to other databases.
 *	If excludeVacuum isn't zero, skip processes for which
 *		(statusFlags & excludeVacuum) is not zero.
 *
 * Note: the purpose of the limitXmin and excludeXmin0 parameters is to
 * allow skipping backends whose oldest live snapshot is no older than
 * some snapshot we have.  Since we examine the procarray with only shared
 * lock, there are race conditions: a backend could set its xmin just after
 * we look.  Indeed, on multiprocessors with weak memory ordering, the
 * other backend could have set its xmin *before* we look.  We know however
 * that such a backend must have held shared ProcArrayLock overlapping our
 * own hold of ProcArrayLock, else we would see its xmin update.  Therefore,
 * any snapshot the other backend is taking concurrently with our scan cannot
 * consider any transactions as still running that we think are committed
 * (since backends must hold ProcArrayLock exclusive to commit).
 */
/* (中文)收集当前活跃事务的虚拟事务 id(VXID)数组,支持多种过滤条件。
 *
 * 【作用】按需过滤后返回所有活跃后端的 VXID(自己除外):
 * - limitXmin:跳过 xmin 晚于该值(更"新")的后端——xmin 不早于给定
 *   快照的会话,其"最老活快照"不会比给定快照更老;
 * - excludeXmin0:跳过还没设置 xmin 的后端;
 * - allDbs:false 时只统计本库后端;
 * - excludeVacuum:跳过 statusFlags 与之有交集的后端(通常用于排除
 *   VACUUM 与逻辑解码)。
 *
 * 【设计思想】
 * - 为什么只用 SHARED 锁就安全(见英文注释):并发取快照的后端在
 *   我们扫描期间也可能更新 xmin,但对方必然与我们重叠持有 SHARED
 *   锁;而提交必须持 EXCLUSIVE 锁,所以"我们扫描时对方正要提交"
 *   的情况被排除——我们认为已提交的事务,对方不可能正拿着快照;
 * - 结果数组按 maxProcs 大小 palloc,由调用方释放。
 *
 * 【参数】见上面过滤条件说明(limitXmin 可为 InvalidTransactionId 表示
 *        不限制;excludeVacuum 可为 0 表示不排除)。
 * 【返回值】VXID 数组(palloc 分配),*nvxids 输出条目数。 */
VirtualTransactionId *
GetCurrentVirtualXIDs(TransactionId limitXmin, bool excludeXmin0,
					  bool allDbs, int excludeVacuum,
					  int *nvxids)
{
	VirtualTransactionId *vxids;
	ProcArrayStruct *arrayP = procArray;
	int			count = 0;
	int			index;

	/* allocate what's certainly enough result space */
	vxids = palloc_array(VirtualTransactionId, arrayP->maxProcs);

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];
		uint8		statusFlags = ProcGlobal->statusFlags[index];

		if (proc == MyProc)
			continue;

		if (excludeVacuum & statusFlags)
			continue;

		if (allDbs || proc->databaseId == MyDatabaseId)
		{
			/* Fetch xmin just once - might change on us */
			TransactionId pxmin = UINT32_ACCESS_ONCE(proc->xmin);

			if (excludeXmin0 && !TransactionIdIsValid(pxmin))
				continue;

			/*
			 * InvalidTransactionId precedes all other XIDs, so a proc that
			 * hasn't set xmin yet will not be rejected by this test.
			 */
			if (!TransactionIdIsValid(limitXmin) ||
				TransactionIdPrecedesOrEquals(pxmin, limitXmin))
			{
				VirtualTransactionId vxid;

				GET_VXID_FROM_PGPROC(vxid, *proc);
				if (VirtualTransactionIdIsValid(vxid))
					vxids[count++] = vxid;
			}
		}
	}

	LWLockRelease(ProcArrayLock);

	*nvxids = count;
	return vxids;
}

/*
 * GetConflictingVirtualXIDs -- returns an array of currently active VXIDs.
 *
 * Usage is limited to conflict resolution during recovery on standby servers.
 * limitXmin is supplied as either a cutoff with snapshotConflictHorizon
 * semantics, or InvalidTransactionId in cases where caller cannot accurately
 * determine a safe snapshotConflictHorizon value.
 *
 * If limitXmin is InvalidTransactionId then we want to kill everybody,
 * so we're not worried if they have a snapshot or not, nor does it really
 * matter what type of lock we hold.  Caller must avoid calling here with
 * snapshotConflictHorizon style cutoffs that were set to InvalidTransactionId
 * during original execution, since that actually indicates that there is
 * definitely no need for a recovery conflict (the snapshotConflictHorizon
 * convention for InvalidTransactionId values is the opposite of our own!).
 *
 * All callers that are checking xmins always now supply a valid and useful
 * value for limitXmin. The limitXmin is always lower than the lowest
 * numbered KnownAssignedXid that is not already a FATAL error. This is
 * because we only care about cleanup records that are cleaning up tuple
 * versions from committed transactions. In that case they will only occur
 * at the point where the record is less than the lowest running xid. That
 * allows us to say that if any backend takes a snapshot concurrently with
 * us then the conflict assessment made here would never include the snapshot
 * that is being derived. So we take LW_SHARED on the ProcArray and allow
 * concurrent snapshots when limitXmin is valid. We might think about adding
 *	 Assert(limitXmin < lowest(KnownAssignedXids))
 * but that would not be true in the case of FATAL errors lagging in array,
 * but we already know those are bogus anyway, so we skip that test.
 *
 * If dbOid is valid we skip backends attached to other databases.
 *
 * Be careful to *not* pfree the result from this function. We reuse
 * this array sufficiently often that we use malloc for the result.
 */
/* (中文)收集"与恢复冲突"的虚拟事务 id 数组(备机专用)。
 *
 * 【作用】热备中 startup 进程判定某清理动作与哪些备机查询冲突时调用:
 * 返回所有"其快照可能还涉及给定 limitXmin 之前的数据"的后端 VXID,
 * 数组末尾以哨兵(procNumber = INVALID_PROC_NUMBER)结尾。
 *
 * 【设计思想】
 * - 判定条件:limitXmin 无效 = 杀掉所有人(不管有没有快照);有效时
 *   只杀"xmin 已设置且不晚于 limitXmin"的后端。已提交事务的清理
 *   记录只会出现在"比最老运行 xid 还早"的位置(见英文注释),因此
 *   持 SHARED 锁、与并发取快照者共存是安全的:任何与我们并发的
 *   快照都不会用我们正在判定的这批数据;
 * - 跳过 prepared 事务(pid == 0):它们没有查询,不冲突;
 * - dbOid 有效时只统计该库的后端;
 * - 结果数组用 malloc 永久复用(频繁调用,避免反复分配),所以调用方
 *   绝不能 pfree 它(见英文注释)。
 *
 * 【参数】
 *   limitXmin —— 冲突判定水位(见上面设计思想);
 *   dbOid     —— 只统计该数据库的后端;InvalidOid 表示全部。
 * 【返回值】以哨兵结尾的 VXID 数组(静态存储,勿释放)。 */
VirtualTransactionId *
GetConflictingVirtualXIDs(TransactionId limitXmin, Oid dbOid)
{
	static VirtualTransactionId *vxids;
	ProcArrayStruct *arrayP = procArray;
	int			count = 0;
	int			index;

	/*
	 * If first time through, get workspace to remember main XIDs in. We
	 * malloc it permanently to avoid repeated palloc/pfree overhead. Allow
	 * result space, remembering room for a terminator.
	 */
	if (vxids == NULL)
	{
		vxids = (VirtualTransactionId *)
			malloc(sizeof(VirtualTransactionId) * (arrayP->maxProcs + 1));
		if (vxids == NULL)
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of memory")));
	}

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];

		/* Exclude prepared transactions */
		if (proc->pid == 0)
			continue;

		if (!OidIsValid(dbOid) ||
			proc->databaseId == dbOid)
		{
			/* Fetch xmin just once - can't change on us, but good coding */
			TransactionId pxmin = UINT32_ACCESS_ONCE(proc->xmin);

			/*
			 * We ignore an invalid pxmin because this means that backend has
			 * no snapshot currently. We hold a Share lock to avoid contention
			 * with users taking snapshots.  That is not a problem because the
			 * current xmin is always at least one higher than the latest
			 * removed xid, so any new snapshot would never conflict with the
			 * test here.
			 */
			if (!TransactionIdIsValid(limitXmin) ||
				(TransactionIdIsValid(pxmin) && !TransactionIdFollows(pxmin, limitXmin)))
			{
				VirtualTransactionId vxid;

				GET_VXID_FROM_PGPROC(vxid, *proc);
				if (VirtualTransactionIdIsValid(vxid))
					vxids[count++] = vxid;
			}
		}
	}

	LWLockRelease(ProcArrayLock);

	/* add the terminator */
	vxids[count].procNumber = INVALID_PROC_NUMBER;
	vxids[count].localTransactionId = InvalidLocalTransactionId;

	return vxids;
}

/*
 * SignalRecoveryConflict -- signal that a process is blocking recovery
 *
 * The 'pid' is redundant with 'proc', but it acts as a cross-check to
 * detect process had exited and the PGPROC entry was reused for a different
 * process.
 *
 * Returns true if the process was signaled, or false if not found.
 */
/* (中文)给"阻塞恢复的进程"发送冲突信号(按 PGPROC 定位)。
 *
 * 【作用】热备冲突处理:确认 proc 仍对应 pid(防止 PGPROC 已被复用给
 * 别的进程时误发信号),在它的 pendingRecoveryConflicts 位图中置上
 * reason 对应位,再发 PROCSIG_RECOVERY_CONFLICT 信号唤醒它处理冲突。
 *
 * 【设计思想】
 * - pid 冗余参数充当交叉校验:进程退出后 PGPROC 槽位可能被新进程
 *   复用,若 proc->pid != pid 说明对象已换人,不发信号(正好是想要
 *   的结果:阻塞者已消失);
 * - 持 SHARED 锁保证 PGPROC 在检查与置位期间不被移除;
 * - pendingRecoveryConflicts 用原子 fetch_or 置位,与目标进程自己的
 *   读/清操作并发安全。
 *
 * 【参数】
 *   proc   —— 目标 PGPROC;
 *   pid    —— 预期进程 PID(交叉校验);
 *   reason —— 冲突原因(决定置哪一位,也决定备机如何处理)。
 * 【返回值】true = 信号已发出;false = 进程已不存在(未发)。 */
bool
SignalRecoveryConflict(PGPROC *proc, pid_t pid, RecoveryConflictReason reason)
{
	bool		found = false;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	/*
	 * Kill the pid if it's still here. If not, that's what we wanted so
	 * ignore any errors.
	 */
	if (proc->pid == pid)
	{
		(void) pg_atomic_fetch_or_u32(&proc->pendingRecoveryConflicts, (1 << reason));

		/* wake up the process */
		(void) SendProcSignal(pid, PROCSIG_RECOVERY_CONFLICT, GetNumberFromPGProc(proc));
		found = true;
	}

	LWLockRelease(ProcArrayLock);

	return found;
}

/*
 * SignalRecoveryConflictWithVirtualXID -- signal that a VXID is blocking recovery
 *
 * Like SignalRecoveryConflict, but the target is identified by VXID
 */
/* (中文)给"阻塞恢复的进程"发送冲突信号(按虚拟事务 id 定位)。
 *
 * 【作用】SignalRecoveryConflict 的 VXID 变体:遍历进程数组找 vxid
 * 匹配的后端,置位并发送 PROCSIG_RECOVERY_CONFLICT。
 *
 * 【设计思想】vxid(procNumber + lxid)能唯一标定一个后端内的一次
 * 事务;prepared 事务的 pid 为 0,不发送。返回是否有活的后端被信号
 * 命中(pid != 0),供调用方判断冲突是否已解除。
 *
 * 【参数】
 *   vxid   —— 目标事务的虚拟事务 id;
 *   reason —— 冲突原因。
 * 【返回值】true = 有活跃后端被发送信号;false = 目标不存在/是
 *          prepared 事务。 */
bool
SignalRecoveryConflictWithVirtualXID(VirtualTransactionId vxid, RecoveryConflictReason reason)
{
	ProcArrayStruct *arrayP = procArray;
	int			index;
	pid_t		pid = 0;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];
		VirtualTransactionId procvxid;

		GET_VXID_FROM_PGPROC(procvxid, *proc);

		if (procvxid.procNumber == vxid.procNumber &&
			procvxid.localTransactionId == vxid.localTransactionId)
		{
			pid = proc->pid;
			if (pid != 0)
			{
				(void) pg_atomic_fetch_or_u32(&proc->pendingRecoveryConflicts, (1 << reason));

				/*
				 * Kill the pid if it's still here. If not, that's what we
				 * wanted so ignore any errors.
				 */
				(void) SendProcSignal(pid, PROCSIG_RECOVERY_CONFLICT, vxid.procNumber);
			}
			break;
		}
	}

	LWLockRelease(ProcArrayLock);

	return pid != 0;
}

/*
 * SignalRecoveryConflictWithDatabase -- signal backends using specified database
 *
 * Like SignalRecoveryConflict, but signals all backends using the database.
 */
/* (中文)给"使用指定数据库的所有后端"发送恢复冲突信号。
 *
 * 【作用】DROP DATABASE / 需要把某库所有会话赶走时调用:遍历进程数组,
 * 对所有 databaseId 匹配(或 databaseid 为 InvalidOid 即全体)的活跃
 * 后端置位 pendingRecoveryConflicts 并发送 PROCSIG_RECOVERY_CONFLICT。
 *
 * 【设计思想】持 EXCLUSIVE 锁执行:这是一次"群体驱逐",期间不允许
 * 新后端登记进数组;prepared 事务(pid == 0)不发送信号(它们没有
 * 进程可收)。
 *
 * 【参数】
 *   databaseid —— 目标数据库 OID;InvalidOid 表示所有数据库;
 *   reason     —— 冲突原因。
 * 【返回值】无。 */
void
SignalRecoveryConflictWithDatabase(Oid databaseid, RecoveryConflictReason reason)
{
	ProcArrayStruct *arrayP = procArray;
	int			index;

	/* tell all backends to die */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];

		if (databaseid == InvalidOid || proc->databaseId == databaseid)
		{
			VirtualTransactionId procvxid;
			pid_t		pid;

			GET_VXID_FROM_PGPROC(procvxid, *proc);

			pid = proc->pid;
			if (pid != 0)
			{
				(void) pg_atomic_fetch_or_u32(&proc->pendingRecoveryConflicts, (1 << reason));

				/*
				 * Kill the pid if it's still here. If not, that's what we
				 * wanted so ignore any errors.
				 */
				(void) SendProcSignal(pid, PROCSIG_RECOVERY_CONFLICT, procvxid.procNumber);
			}
		}
	}

	LWLockRelease(ProcArrayLock);
}

/*
 * MinimumActiveBackends --- count backends (other than myself) that are
 *		in active transactions.  Return true if the count exceeds the
 *		minimum threshold passed.  This is used as a heuristic to decide if
 *		a pre-XLOG-flush delay is worthwhile during commit.
 *
 * Do not count backends that are blocked waiting for locks, since they are
 * not going to get to run until someone else commits.
 */
/* (中文)统计"活跃事务数"是否超过阈值(启发式)。
 *
 * 【作用】提交路径判断"是否值得为等待刷新 WAL 而延迟一下"的启发式:
 * 统计除自己以外、持有 xid、没有阻塞在锁上、且不是 prepared 事务的
 * 后端数量,超过 min 即返回 true。
 *
 * 【设计思想】
 * - 不加锁直接扫(速度优先):只判断字段的零/非零,且结果仅用于启发
 *   式决策,容忍垃圾值。为防并发带来的脏读,遇到 pgprocno == -1
 *   (被删除的条目)要跳过——有人刚减了 numProcs,数组尾部可能残留
 *   -1(见英文注释);proc 指针指向的 PGPROC 即使已被回收,内容虽
 *   无意义但指针仍合法,不影响本函数的安全;
 * - 排除等锁的后端:它们要等别人提交后才能运行,对"是否值得延迟
 *   WAL flush 以增加事务并发度"没有贡献(见英文注释)。
 *
 * 【参数】min —— 阈值;0 表示"无需计数",直接返回 true。
 * 【返回值】true = 活跃事务数 >= min。 */
bool
MinimumActiveBackends(int min)
{
	ProcArrayStruct *arrayP = procArray;
	int			count = 0;
	int			index;

	/* Quick short-circuit if no minimum is specified */
	if (min == 0)
		return true;

	/*
	 * Note: for speed, we don't acquire ProcArrayLock.  This is a little bit
	 * bogus, but since we are only testing fields for zero or nonzero, it
	 * should be OK.  The result is only used for heuristic purposes anyway...
	 */
	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];

		/*
		 * Since we're not holding a lock, need to be prepared to deal with
		 * garbage, as someone could have incremented numProcs but not yet
		 * filled the structure.
		 *
		 * If someone just decremented numProcs, 'proc' could also point to a
		 * PGPROC entry that's no longer in the array. It still points to a
		 * PGPROC struct, though, because freed PGPROC entries just go to the
		 * free list and are recycled. Its contents are nonsense in that case,
		 * but that's acceptable for this function.
		 */
		if (pgprocno == -1)
			continue;			/* do not count deleted entries */
		if (proc == MyProc)
			continue;			/* do not count myself */
		if (proc->xid == InvalidTransactionId)
			continue;			/* do not count if no XID assigned */
		if (proc->pid == 0)
			continue;			/* do not count prepared xacts */
		if (proc->waitLock != NULL)
			continue;			/* do not count if blocked on a lock */
		count++;
		if (count >= min)
			break;
	}

	return count >= min;
}

/*
 * CountDBBackends --- count backends that are using specified database
 */
/* (中文)统计正在使用指定数据库的后端数。
 *
 * 【作用】遍历进程数组,统计 databaseId 匹配的活跃后端(prepared 事务
 * 占位不计)。databaseid 为 InvalidOid 时统计全部。
 *
 * 【设计思想】用于数据库管理(DROP DATABASE 前的检查等);计数在
 * SHARED 锁内完成,保证与后端进出数组互斥。
 *
 * 【参数】databaseid —— 目标数据库 OID;InvalidOid 表示全部。
 * 【返回值】匹配的后端数量。 */
int
CountDBBackends(Oid databaseid)
{
	ProcArrayStruct *arrayP = procArray;
	int			count = 0;
	int			index;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];

		if (proc->pid == 0)
			continue;			/* do not count prepared xacts */
		if (!OidIsValid(databaseid) ||
			proc->databaseId == databaseid)
			count++;
	}

	LWLockRelease(ProcArrayLock);

	return count;
}

/*
 * CountDBConnections --- counts database backends (only regular backends)
 */
/* (中文)统计到指定数据库的"连接数"(只统计普通后端进程)。
 *
 * 【作用】与 CountDBBackends 类似,但额外要求 backendType == B_BACKEND:
 * 后台工作者(bgworker)、辅助进程等不计入"连接"。
 *
 * 【设计思想】用于统计连接数相关的管理视图/限制逻辑,把"连接"限定
 * 为真正的用户会话。
 *
 * 【参数】databaseid —— 目标数据库 OID;InvalidOid 表示全部。
 * 【返回值】匹配的普通后端数量。 */
int
CountDBConnections(Oid databaseid)
{
	ProcArrayStruct *arrayP = procArray;
	int			count = 0;
	int			index;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];

		if (proc->pid == 0)
			continue;			/* do not count prepared xacts */
		if (proc->backendType != B_BACKEND)
			continue;			/* count only regular backend processes */
		if (!OidIsValid(databaseid) ||
			proc->databaseId == databaseid)
			count++;
	}

	LWLockRelease(ProcArrayLock);

	return count;
}

/*
 * CountUserBackends --- count backends that are used by specified user
 * (only regular backends, not any type of background worker)
 */
/* (中文)统计属于指定用户的"会话数"(只统计普通后端进程)。
 *
 * 【作用】按 roleId 统计活跃的普通后端数量;prepared 事务占位与后台
 * 工作者(backendType != B_BACKEND)不计入。
 *
 * 【设计思想】服务于连接/角色相关的管理限制(如角色连接数上限)。
 *
 * 【参数】roleid —— 目标角色 OID。
 * 【返回值】匹配的普通后端数量。 */
int
CountUserBackends(Oid roleid)
{
	ProcArrayStruct *arrayP = procArray;
	int			count = 0;
	int			index;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (index = 0; index < arrayP->numProcs; index++)
	{
		int			pgprocno = arrayP->pgprocnos[index];
		PGPROC	   *proc = &allProcs[pgprocno];

		if (proc->pid == 0)
			continue;			/* do not count prepared xacts */
		if (proc->backendType != B_BACKEND)
			continue;			/* count only regular backend processes */
		if (proc->roleId == roleid)
			count++;
	}

	LWLockRelease(ProcArrayLock);

	return count;
}

/*
 * CountOtherDBBackends -- check for other backends running in the given DB
 *
 * If there are other backends in the DB, we will wait a maximum of 5 seconds
 * for them to exit (or 0.3s for testing purposes).  Autovacuum backends are
 * encouraged to exit early by sending them SIGTERM, but normal user backends
 * are just waited for.  If background workers connected to this database are
 * marked as interruptible, they are terminated.
 *
 * The current backend is always ignored; it is caller's responsibility to
 * check whether the current backend uses the given DB, if it's important.
 *
 * Returns true if there are (still) other backends in the DB, false if not.
 * Also, *nbackends and *nprepared are set to the number of other backends
 * and prepared transactions in the DB, respectively.
 *
 * This function is used to interlock DROP DATABASE and related commands
 * against there being any active backends in the target DB --- dropping the
 * DB while active backends remain would be a Bad Thing.  Note that we cannot
 * detect here the possibility of a newly-started backend that is trying to
 * connect to the doomed database, so additional interlocking is needed during
 * backend startup.  The caller should normally hold an exclusive lock on the
 * target DB before calling this, which is one reason we mustn't wait
 * indefinitely.
 */
/* (中文)检查指定数据库是否还有"其他"后端在使用(最多等 5 秒)。
 *
 * 【作用】DROP DATABASE 的互斥检查:循环扫描(最多 50 次、每次间隔
 * 100ms)目标库的后端;发现有 autovacuum 就发 SIGTERM 请它提前退出,
 * 有可中断的 bgworker 就终止它们,然后等待再查。全部清空返回 false;
 * 超时仍有人返回 true。
 *
 * 【设计思想】
 * - 计数与发信号分离:kill() 可能在内核里阻塞,不能在持锁时调用,
 *   所以先扫出 autovacuum 的 pid 列表、释放锁再逐个 SIGTERM(见英文
 *   注释);TerminateBackgroundWorkersForDatabase 同样在锁外调用;
 * - 为什么必须限时:调用方通常已持有目标库的排他锁(阻止新后端进入
 *   也是它的事),无限等待会与其他持锁者死锁,详见英文注释;
 * - 通过 *nbackends / *nprepared 输出两类阻塞者的数量,供调用方生成
 *   错误信息;prepared 事务(pid == 0)无法被赶走,只能等待或报错。
 *
 * 【参数】
 *   databaseId —— 目标数据库 OID;
 *   nbackends  —— 输出:其他普通后端数;
 *   nprepared  —— 输出:其他 prepared 事务数。
 * 【返回值】true = 超时仍有冲突;false = 已无其他后端。 */
bool
CountOtherDBBackends(Oid databaseId, int *nbackends, int *nprepared)
{
	ProcArrayStruct *arrayP = procArray;

#define MAXAUTOVACPIDS	10		/* max autovacs to SIGTERM per iteration */
	int			autovac_pids[MAXAUTOVACPIDS];

	/*
	 * Retry up to 50 times with 100ms between attempts (max 5s total). Can be
	 * reduced to 3 attempts (max 0.3s total) to speed up tests.
	 */
	int			ntries = 50;

#ifdef USE_INJECTION_POINTS
	if (IS_INJECTION_POINT_ATTACHED("procarray-reduce-count"))
		ntries = 3;
#endif

	for (int tries = 0; tries < ntries; tries++)
	{
		int			nautovacs = 0;
		bool		found = false;
		int			index;

		CHECK_FOR_INTERRUPTS();

		*nbackends = *nprepared = 0;

		LWLockAcquire(ProcArrayLock, LW_SHARED);

		for (index = 0; index < arrayP->numProcs; index++)
		{
			int			pgprocno = arrayP->pgprocnos[index];
			PGPROC	   *proc = &allProcs[pgprocno];
			uint8		statusFlags = ProcGlobal->statusFlags[index];

			if (proc->databaseId != databaseId)
				continue;
			if (proc == MyProc)
				continue;

			found = true;

			if (proc->pid == 0)
				(*nprepared)++;
			else
			{
				(*nbackends)++;
				if ((statusFlags & PROC_IS_AUTOVACUUM) &&
					nautovacs < MAXAUTOVACPIDS)
					autovac_pids[nautovacs++] = proc->pid;
			}
		}

		LWLockRelease(ProcArrayLock);

		if (!found)
			return false;		/* no conflicting backends, so done */

		/*
		 * Send SIGTERM to any conflicting autovacuums before sleeping. We
		 * postpone this step until after the loop because we don't want to
		 * hold ProcArrayLock while issuing kill(). We have no idea what might
		 * block kill() inside the kernel...
		 */
		for (index = 0; index < nautovacs; index++)
			(void) kill(autovac_pids[index], SIGTERM);	/* ignore any error */

		/*
		 * Terminate all background workers for this database, if they have
		 * requested it (BGWORKER_INTERRUPTIBLE).
		 */
		TerminateBackgroundWorkersForDatabase(databaseId);

		/* sleep, then try again */
		pg_usleep(100 * 1000L); /* 100ms */
	}

	return true;				/* timed out, still conflicts */
}

/*
 * Terminate existing connections to the specified database. This routine
 * is used by the DROP DATABASE command when user has asked to forcefully
 * drop the database.
 *
 * The current backend is always ignored; it is caller's responsibility to
 * check whether the current backend uses the given DB, if it's important.
 *
 * If the target database has a prepared transaction or permissions checks
 * fail for a connection, this fails without terminating anything.
 */
/* (中文)强制终止指定数据库的所有连接(DROP DATABASE ... FORCE)。
 *
 * 【作用】先扫描收集目标库其他后端的 pid 与 prepared 事务数;有
 * prepared 事务则直接报错(不能强杀,只能中止整条命令);然后做权限
 * 检查(放宽了 pg_terminate_backend 的两条限制:允许杀 autovacuum、
 * 允许杀 bgworker,见英文注释),最后对每个 pid 发 SIGTERM。
 *
 * 【设计思想】
 * - 收集与执行分离:锁内只收集 pid 列表,锁外做权限判断与 kill,
 *   避免长持锁(且 kill 可能在核内阻塞);
 * - 先权限后动作:任一连接权限不足就整体失败、什么都不杀(见英文
 *   注释);
 * - 发信号前用 BackendPidGetProc 复核会话是否还在(两次遍历之间
 *   会话可能退出,属可接受的竞态,见英文注释);
 * - 有 setsid 时对整进程组发信号(-pid),确保该会话的子进程也退出。
 *
 * 【参数】databaseId —— 目标数据库 OID。
 * 【返回值】无(有 prepared 事务或权限不足时 ereport(ERROR))。 */
void
TerminateOtherDBBackends(Oid databaseId)
{
	ProcArrayStruct *arrayP = procArray;
	List	   *pids = NIL;
	int			nprepared = 0;
	int			i;

	LWLockAcquire(ProcArrayLock, LW_SHARED);

	for (i = 0; i < procArray->numProcs; i++)
	{
		int			pgprocno = arrayP->pgprocnos[i];
		PGPROC	   *proc = &allProcs[pgprocno];

		if (proc->databaseId != databaseId)
			continue;
		if (proc == MyProc)
			continue;

		if (proc->pid != 0)
			pids = lappend_int(pids, proc->pid);
		else
			nprepared++;
	}

	LWLockRelease(ProcArrayLock);

	if (nprepared > 0)
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_IN_USE),
				 errmsg("database \"%s\" is being used by prepared transactions",
						get_database_name(databaseId)),
				 errdetail_plural("There is %d prepared transaction using the database.",
								  "There are %d prepared transactions using the database.",
								  nprepared,
								  nprepared)));

	if (pids)
	{
		ListCell   *lc;

		/*
		 * Permissions checks relax the pg_terminate_backend checks in two
		 * ways, both by omitting the !OidIsValid(proc->roleId) check:
		 *
		 * - Accept terminating autovacuum workers, since DROP DATABASE
		 * without FORCE terminates them.
		 *
		 * - Accept terminating bgworkers.  For bgworker authors, it's
		 * convenient to be able to recommend FORCE if a worker is blocking
		 * DROP DATABASE unexpectedly.
		 *
		 * Unlike pg_terminate_backend, we don't raise some warnings - like
		 * "PID %d is not a PostgreSQL server process", because for us already
		 * finished session is not a problem.
		 */
		foreach(lc, pids)
		{
			int			pid = lfirst_int(lc);
			PGPROC	   *proc = BackendPidGetProc(pid);

			if (proc != NULL)
			{
				if (superuser_arg(proc->roleId) && !superuser())
					ereport(ERROR,
							(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
							 errmsg("permission denied to terminate process"),
							 errdetail("Only roles with the %s attribute may terminate processes of roles with the %s attribute.",
									   "SUPERUSER", "SUPERUSER")));

				if (!has_privs_of_role(GetUserId(), proc->roleId) &&
					!has_privs_of_role(GetUserId(), ROLE_PG_SIGNAL_BACKEND))
					ereport(ERROR,
							(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
							 errmsg("permission denied to terminate process"),
							 errdetail("Only roles with privileges of the role whose process is being terminated or with privileges of the \"%s\" role may terminate this process.",
									   "pg_signal_backend")));
			}
		}

		/*
		 * There's a race condition here: once we release the ProcArrayLock,
		 * it's possible for the session to exit before we issue kill.  That
		 * race condition possibility seems too unlikely to worry about.  See
		 * pg_signal_backend.
		 */
		foreach(lc, pids)
		{
			int			pid = lfirst_int(lc);
			PGPROC	   *proc = BackendPidGetProc(pid);

			if (proc != NULL)
			{
				/*
				 * If we have setsid(), signal the backend's whole process
				 * group
				 */
#ifdef HAVE_SETSID
				(void) kill(-pid, SIGTERM);
#else
				(void) kill(pid, SIGTERM);
#endif
			}
		}
	}
}

/*
 * ProcArraySetReplicationSlotXmin
 *
 * Install limits to future computations of the xmin horizon to prevent vacuum
 * and HOT pruning from removing affected rows still needed by clients with
 * replication slots.
 */
/* (中文)安装/更新复制槽要求的 xmin 下限。
 *
 * 【作用】复制槽管理器在槽位 xmin 变化时调用:把槽位要求的最老 xmin
 * (数据与 catalog 两个水位)写入 procArray->replication_slot_xmin /
 * replication_slot_catalog_xmin。此后 ComputeXidHorizons() 与
 * GetSnapshotData() 都会把这两个值计入清理边界,防止 VACUUM 与 HOT
 * 剪枝删掉复制客户端还需要的数据。
 *
 * 【设计思想】必须持 EXCLUSIVE 锁写入(除非调用方已持锁并传
 * already_locked):两个字段要成对更新,读者(ComputeXidHorizons 等)
 * 持 SHARED 锁读取,写读必须互斥;调用方如已持锁则省一次加解锁。
 *
 * 【参数】
 *   xmin          —— 槽位要求的普通 xmin;
 *   catalog_xmin  —— 槽位要求的 catalog xmin;
 *   already_locked —— true 表示调用方已持 ProcArrayLock(EXCLUSIVE)。
 * 【返回值】无。 */
void
ProcArraySetReplicationSlotXmin(TransactionId xmin, TransactionId catalog_xmin,
								bool already_locked)
{
	Assert(!already_locked || LWLockHeldByMe(ProcArrayLock));

	if (!already_locked)
		LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	procArray->replication_slot_xmin = xmin;
	procArray->replication_slot_catalog_xmin = catalog_xmin;

	if (!already_locked)
		LWLockRelease(ProcArrayLock);

	elog(DEBUG1, "xmin required by slots: data %u, catalog %u",
		 xmin, catalog_xmin);
}

/*
 * ProcArrayGetReplicationSlotXmin
 *
 * Return the current slot xmin limits. That's useful to be able to remove
 * data that's older than those limits.
 */
/* (中文)读取当前的复制槽 xmin 下限。
 *
 * 【作用】把 procArray 里的两个槽位水位读出(SHARED 锁内读取,与
 * ProcArraySetReplicationSlotXmin 的写入互斥);输出参数可为 NULL
 * (只取其中一项)。
 *
 * 【参数】
 *   xmin         —— 输出:普通 xmin(可空);
 *   catalog_xmin —— 输出:catalog xmin(可空)。
 * 【返回值】无。 */
void
ProcArrayGetReplicationSlotXmin(TransactionId *xmin,
								TransactionId *catalog_xmin)
{
	LWLockAcquire(ProcArrayLock, LW_SHARED);

	if (xmin != NULL)
		*xmin = procArray->replication_slot_xmin;

	if (catalog_xmin != NULL)
		*catalog_xmin = procArray->replication_slot_catalog_xmin;

	LWLockRelease(ProcArrayLock);
}

/*
 * XidCacheRemoveRunningXids
 *
 * Remove a bunch of TransactionIds from the list of known-running
 * subtransactions for my backend.  Both the specified xid and those in
 * the xids[] array (of length nxids) are removed from the subxids cache.
 * latestXid must be the latest XID among the group.
 */
/* (中文)从本进程的子事务缓存中移除一批 xid(子事务中止时调用)。
 *
 * 【作用】子事务回滚时,把它(主 xid 参数 xid 或 xids[] 数组)从
 * MyProc->subxids.xids[] 缓存中删掉(交换删除法:与数组末尾元素互换
 * 再减计数),并同步 ProcGlobal->subxidStates;最后推进
 * latestCompletedXid 与 xactCompletionCount。
 *
 * 【设计思想】
 * - 为什么必须 EXCLUSIVE 锁:虽然只有本进程写自己的缓存,但"运行中
 *   事务集合"的缩小必须对取快照者原子可见(同 ProcArrayEndTransaction
 *   的理由,见英文注释与 access/transam/README);
 * - 倒序删除避免 O(N^2):缓存按 xid 升序,而传入的 xids[] 也是升序,
 *   两重倒序扫描让"要删的"总在尾部附近(见英文注释);
 * - 交换删除(把最后一个元素搬到被删位置)使删除为 O(1),但缓存
 *   不再有序——这不影响正确性,因为本进程读自己的缓存不依赖顺序;
 * - pg_write_barrier 保证"计数递减"发生在"数组内容就绪"之后,与
 *   取快照者的 pg_read_barrier 配对;
 * - 找不到目标 xid 不报错只告警:缓存可能已溢出(丢失),或同一
 *   子事务因 AbortSubTransaction 出错被调用了两次(见英文注释)。
 *
 * 【参数】
 *   xid       —— 要删除的主 xid;
 *   nxids、xids —— 额外要删除的子 xid 数组;
 *   latestXid —— 本组中最大的 xid(推进 latestCompletedXid 用)。
 * 【返回值】无。 */
void
XidCacheRemoveRunningXids(TransactionId xid,
						  int nxids, const TransactionId *xids,
						  TransactionId latestXid)
{
	int			i,
				j;
	XidCacheStatus *mysubxidstat;

	Assert(TransactionIdIsValid(xid));

	/*
	 * We must hold ProcArrayLock exclusively in order to remove transactions
	 * from the PGPROC array.  (See src/backend/access/transam/README.)  It's
	 * possible this could be relaxed since we know this routine is only used
	 * to abort subtransactions, but pending closer analysis we'd best be
	 * conservative.
	 *
	 * Note that we do not have to be careful about memory ordering of our own
	 * reads wrt. GetNewTransactionId() here - only this process can modify
	 * relevant fields of MyProc/ProcGlobal->xids[].  But we do have to be
	 * careful about our own writes being well ordered.
	 */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	mysubxidstat = &ProcGlobal->subxidStates[MyProc->pgxactoff];

	/*
	 * Under normal circumstances xid and xids[] will be in increasing order,
	 * as will be the entries in subxids.  Scan backwards to avoid O(N^2)
	 * behavior when removing a lot of xids.
	 */
	for (i = nxids - 1; i >= 0; i--)
	{
		TransactionId anxid = xids[i];

		for (j = MyProc->subxidStatus.count - 1; j >= 0; j--)
		{
			if (TransactionIdEquals(MyProc->subxids.xids[j], anxid))
			{
				MyProc->subxids.xids[j] = MyProc->subxids.xids[MyProc->subxidStatus.count - 1];
				pg_write_barrier();
				mysubxidstat->count--;
				MyProc->subxidStatus.count--;
				break;
			}
		}

		/*
		 * Ordinarily we should have found it, unless the cache has
		 * overflowed. However it's also possible for this routine to be
		 * invoked multiple times for the same subtransaction, in case of an
		 * error during AbortSubTransaction.  So instead of Assert, emit a
		 * debug warning.
		 */
		if (j < 0 && !MyProc->subxidStatus.overflowed)
			elog(WARNING, "did not find subXID %u in MyProc", anxid);
	}

	for (j = MyProc->subxidStatus.count - 1; j >= 0; j--)
	{
		if (TransactionIdEquals(MyProc->subxids.xids[j], xid))
		{
			MyProc->subxids.xids[j] = MyProc->subxids.xids[MyProc->subxidStatus.count - 1];
			pg_write_barrier();
			mysubxidstat->count--;
			MyProc->subxidStatus.count--;
			break;
		}
	}
	/* Ordinarily we should have found it, unless the cache has overflowed */
	if (j < 0 && !MyProc->subxidStatus.overflowed)
		elog(WARNING, "did not find subXID %u in MyProc", xid);

	/* Also advance global latestCompletedXid while holding the lock */
	MaintainLatestCompletedXid(latestXid);

	/* ... and xactCompletionCount */
	TransamVariables->xactCompletionCount++;

	LWLockRelease(ProcArrayLock);
}

#ifdef XIDCACHE_DEBUG

/*
 * Print stats about effectiveness of XID cache
 */
/* (中文)(仅 XIDCACHE_DEBUG)打印 TransactionIdIsInProgress() 各条
 * 路径的命中统计(见文件头处九个计数器的中文注释)。后端退出时由
 * ProcArrayRemove 调用,输出到 stderr,用于评估 xid 缓存的有效性。 */
static void
DisplayXidCache(void)
{
	fprintf(stderr,
			"XidCache: xmin: %ld, known: %ld, myxact: %ld, latest: %ld, mainxid: %ld, childxid: %ld, knownassigned: %ld, nooflo: %ld, slow: %ld\n",
			xc_by_recent_xmin,
			xc_by_known_xact,
			xc_by_my_xact,
			xc_by_latest_xid,
			xc_by_main_xid,
			xc_by_child_xid,
			xc_by_known_assigned,
			xc_no_overflow,
			xc_slow_answer);
}
#endif							/* XIDCACHE_DEBUG */

/*
 * If rel != NULL, return test state appropriate for relation, otherwise
 * return state usable for all relations.  The latter may consider XIDs as
 * not-yet-visible-to-everyone that a state for a specific relation would
 * already consider visible-to-everyone.
 *
 * This needs to be called while a snapshot is active or registered, otherwise
 * there are wraparound and other dangers.
 *
 * See comment for GlobalVisState for details.
 */
/* (中文)取得与某张关系匹配的全局可见性状态(GlobalVisTest* 系列入口)。
 *
 * 【作用】按 GlobalVisHorizonKindForRel 的关系分类,返回四份
 * GlobalVisState 中对应的一份(共享表/目录/数据表/临时表),供后续
 * 可删除性判定使用。rel == NULL 返回最保守的共享表状态。
 *
 * 【设计思想】
 * - 必须在"快照已激活或已登记"期间调用:边界值的有效性依赖当前
 *   快照上下文,否则有回绕等危险(见英文注释);
 * - 进程退出时四份状态由 GetSnapshotData / ComputeXidHorizons 持续
 *   维护,这里只是取用指针。
 *
 * 【参数】rel —— 目标关系;NULL 表示最保守状态。
 * 【返回值】对应状态的指针。 */
GlobalVisState *
GlobalVisTestFor(Relation rel)
{
	GlobalVisState *state = NULL;

	/* XXX: we should assert that a snapshot is pushed or registered */
	Assert(RecentXmin);

	switch (GlobalVisHorizonKindForRel(rel))
	{
		case VISHORIZON_SHARED:
			state = &GlobalVisSharedRels;
			break;
		case VISHORIZON_CATALOG:
			state = &GlobalVisCatalogRels;
			break;
		case VISHORIZON_DATA:
			state = &GlobalVisDataRels;
			break;
		case VISHORIZON_TEMP:
			state = &GlobalVisTempRels;
			break;
	}

	Assert(FullTransactionIdIsValid(state->definitely_needed) &&
		   FullTransactionIdIsValid(state->maybe_needed));

	return state;
}

/*
 * Return true if it's worth updating the accurate maybe_needed boundary.
 *
 * As it is somewhat expensive to determine xmin horizons, we don't want to
 * repeatedly do so when there is a low likelihood of it being beneficial.
 *
 * The current heuristic is that we update only if RecentXmin has changed
 * since the last update. If the oldest currently running transaction has not
 * finished, it is unlikely that recomputing the horizon would be useful.
 */
/* (中文)判断"是否值得用 ComputeXidHorizons() 精确重算水位"。
 *
 * 【作用】返回 true 时,调用方(GlobalVisTestIsRemovableFullXid)会
 * 做一次精确重算;false 则沿用现有边界。启发式三条:
 * 1. 从未重算过(ComputeXidHorizonsResultLastXmin 无效):值得算一次;
 * 2. maybe_needed 已经追上 definitely_needed:两个边界重合,没有
 *   悬而未决的区间,重算无益;
 * 3. 最近一次构造快照的 xmin 与上次重算时相同:最老的事务还没结束,
 *   重算多半不会改变答案。
 *
 * 【设计思想】精确重算要加锁扫全数组,代价不小;而只有"最老活跃
 * 事务消失"才可能让边界前进,用 RecentXmin 当代理指标非常廉价。
 *
 * 【参数】state —— 目标 GlobalVisState(读它的两个边界比较)。
 * 【返回值】true = 值得重算。 */
static bool
GlobalVisTestShouldUpdate(GlobalVisState *state)
{
	/* hasn't been updated yet */
	if (!TransactionIdIsValid(ComputeXidHorizonsResultLastXmin))
		return true;

	/*
	 * If the maybe_needed/definitely_needed boundaries are the same, it's
	 * unlikely to be beneficial to refresh boundaries.
	 */
	if (FullTransactionIdFollowsOrEquals(state->maybe_needed,
										 state->definitely_needed))
		return false;

	/* does the last snapshot built have a different xmin? */
	return RecentXmin != ComputeXidHorizonsResultLastXmin;
}

/* (中文)把 ComputeXidHorizons() 的精确结果应用到四份 GlobalVisState
 * 的边界上。
 *
 * 【作用】ComputeXidHorizons 收尾时调用(它持有全部精确水位):
 * 把 shared/catalog/data/temp 各自的老边界(shared_oldest_nonremovable
 * 等)换算成 FullTransactionId 写入对应状态的 maybe_needed;再把
 * definitely_needed 向前推进到至少不低于 maybe_needed(长时间运行的
 * 事务中,之前需要保守对待的 xid 可能已全部结束),最后记录本次重算
 * 时的 RecentXmin(供 GlobalVisTestShouldUpdate 使用)。
 *
 * 【设计思想】
 * - maybe_needed 与 definitely_needed 的语义见 GlobalVisState 注释:
 *   精确值更新下界,上界只允许前进不允许后退(FullTransactionIdNewer);
 * - 换算基准用精确计算时的 latest_completed,保证 64 位表示一致。
 *
 * 【参数】horizons —— ComputeXidHorizons 的精确结果。
 * 【返回值】无(副作用:更新四份全局状态)。 */
static void
GlobalVisUpdateApply(ComputeXidHorizonsResult *horizons)
{
	GlobalVisSharedRels.maybe_needed =
		FullXidRelativeTo(horizons->latest_completed,
						  horizons->shared_oldest_nonremovable);
	GlobalVisCatalogRels.maybe_needed =
		FullXidRelativeTo(horizons->latest_completed,
						  horizons->catalog_oldest_nonremovable);
	GlobalVisDataRels.maybe_needed =
		FullXidRelativeTo(horizons->latest_completed,
						  horizons->data_oldest_nonremovable);
	GlobalVisTempRels.maybe_needed =
		FullXidRelativeTo(horizons->latest_completed,
						  horizons->temp_oldest_nonremovable);

	/*
	 * In longer running transactions it's possible that transactions we
	 * previously needed to treat as running aren't around anymore. So update
	 * definitely_needed to not be earlier than maybe_needed.
	 */
	GlobalVisSharedRels.definitely_needed =
		FullTransactionIdNewer(GlobalVisSharedRels.maybe_needed,
							   GlobalVisSharedRels.definitely_needed);
	GlobalVisCatalogRels.definitely_needed =
		FullTransactionIdNewer(GlobalVisCatalogRels.maybe_needed,
							   GlobalVisCatalogRels.definitely_needed);
	GlobalVisDataRels.definitely_needed =
		FullTransactionIdNewer(GlobalVisDataRels.maybe_needed,
							   GlobalVisDataRels.definitely_needed);
	GlobalVisTempRels.definitely_needed = GlobalVisTempRels.maybe_needed;

	ComputeXidHorizonsResultLastXmin = RecentXmin;
}

/*
 * Update boundaries in GlobalVis{Shared,Catalog, Data}Rels
 * using ComputeXidHorizons().
 */
/* (中文)用一次精确水位计算更新四份 GlobalVisState 的边界。
 *
 * 【作用】GlobalVisTestIsRemovableFullXid 判定"落在不确定区间"时
 * 调用:执行 ComputeXidHorizons(),其副作用(经 GlobalVisUpdateApply)
 * 即更新边界,使本次判定能以新边界重查。
 *
 * 【参数】无。
 * 【返回值】无。 */
static void
GlobalVisUpdate(void)
{
	ComputeXidHorizonsResult horizons;

	/* updates the horizons as a side-effect */
	ComputeXidHorizons(&horizons);
}

/*
 * Return true if no snapshot still considers fxid to be running.
 *
 * The state passed needs to have been initialized for the relation fxid is
 * from (NULL is also OK), otherwise the result may not be correct.
 *
 * If allow_update is false, the GlobalVisState boundaries will not be updated
 * even if it would otherwise be beneficial. This is useful for callers that
 * do not want GlobalVisState to advance at all, for example because they need
 * a conservative answer based on the current boundaries.
 *
 * See comment for GlobalVisState for details.
 */
/* (中文)GlobalVisTest 核心判定:fxid 是否已不被任何快照视为运行
 * (即其效果对所有人可见,可安全清理)。
 *
 * 【作用】三级判定:
 * 1. fxid < maybe_needed:必已对所有人可见,返回 true;
 * 2. fxid >= definitely_needed:极可能仍被视为运行,返回 false;
 * 3. 落在两边界之间(不确定):若允许更新(allow_update)且启发式
 *    认为值得(GlobalVisTestShouldUpdate),就精确重算边界
 *    (GlobalVisUpdate)后按新边界重判——重算后 fxid 必然 <
 *    definitely_needed(断言),答案由 maybe_needed 决定;否则
 *    保守返回 false。
 *
 * 【设计思想】这就是"用廉价近似 + 按需精确化"的两级策略:绝大多数
 * 判定落在边界外,零开销;只有少数不确定样本才付出加锁扫数组的代价,
 * 且用 GlobalVisTestShouldUpdate 限制重算频率(见英文注释)。
 *
 * 【参数】
 *   state        —— 与 fxid 来源关系匹配的状态(错配会给出错误答案);
 *   fxid         —— 要判定的完整事务 id;
 *   allow_update —— false 时不更新边界(需要基于当前边界的保守答案
 *                   的调用方使用)。
 * 【返回值】true = 没有任何快照把 fxid 视为运行。 */
bool
GlobalVisTestIsRemovableFullXid(GlobalVisState *state,
								FullTransactionId fxid,
								bool allow_update)
{
	/*
	 * If fxid is older than maybe_needed bound, it definitely is visible to
	 * everyone.
	 */
	if (FullTransactionIdPrecedes(fxid, state->maybe_needed))
		return true;

	/*
	 * If fxid is >= definitely_needed bound, it is very likely to still be
	 * considered running.
	 */
	if (FullTransactionIdFollowsOrEquals(fxid, state->definitely_needed))
		return false;

	/*
	 * fxid is between maybe_needed and definitely_needed, i.e. there might or
	 * might not exist a snapshot considering fxid running. If it makes sense,
	 * update boundaries and recheck.
	 */
	if (allow_update && GlobalVisTestShouldUpdate(state))
	{
		GlobalVisUpdate();

		Assert(FullTransactionIdPrecedes(fxid, state->definitely_needed));

		return FullTransactionIdPrecedes(fxid, state->maybe_needed);
	}
	else
		return false;
}

/*
 * Wrapper around GlobalVisTestIsRemovableFullXid() for 32bit xids.
 *
 * It is crucial that this only gets called for xids from a source that
 * protects against xid wraparounds (e.g. from a table and thus protected by
 * relfrozenxid).
 */
/* (中文)GlobalVisTestIsRemovableFullXid 的 32 位 xid 包装。
 *
 * 【作用】把 32 位 xid 参照 state->definitely_needed(基于快照构造时
 * 的 [oldestXid, nextXid) 区间)换算成 FullTransactionId 后调用
 * 64 位版本。
 *
 * 【设计思想】换算(FULLXID 的"相对 xid 增量加回基准")只在 xid 与
 * 基准的差落在 ±2^31 内才可靠——函数的前提条件正是"xid 来自受回绕
 * 保护的地方",例如表里由 relfrozenxid 保证的 xid(见英文注释);
 * 不取锁而直接用边界当基准,是"快照上下文有效"这一约定换来的。
 *
 * 【参数】
 *   state        —— 状态(兼作换算基准);
 *   xid          —— 要判定的 32 位事务 id;
 *   allow_update —— 透传给 64 位版本。
 * 【返回值】true = 没有任何快照把 xid 视为运行。 */
bool
GlobalVisTestIsRemovableXid(GlobalVisState *state, TransactionId xid,
							bool allow_update)
{
	FullTransactionId fxid;

	/*
	 * Convert 32 bit argument to FullTransactionId. We can do so safely
	 * because we know the xid has to, at the very least, be between
	 * [oldestXid, nextXid), i.e. within 2 billion of xid. To avoid taking a
	 * lock to determine either, we can just compare with
	 * state->definitely_needed, which was based on those value at the time
	 * the current snapshot was built.
	 */
	fxid = FullXidRelativeTo(state->definitely_needed, xid);

	return GlobalVisTestIsRemovableFullXid(state, fxid, allow_update);
}

/*
 * Wrapper around GlobalVisTestIsRemovableXid() for use when examining live
 * tuples. Returns true if the given XID may be considered running by at least
 * one snapshot.
 *
 * This function alone is insufficient to determine tuple visibility; callers
 * must also consider the XID's commit status. Its purpose is purely semantic:
 * when applied to live tuples, GlobalVisTestIsRemovableXid() is checking
 * whether the inserting transaction is still considered running, not whether
 * the tuple is removable. Live tuples are, by definition, not removable, but
 * the snapshot criteria for "transaction still running" are identical to
 * those used for removal XIDs.
 *
 * If allow_update is true, the GlobalVisState boundaries may be updated. If
 * it is false, they definitely will not be updated.
 *
 * See the comment above GlobalVisTestIsRemovable[Full]Xid() for details on
 * the required preconditions for calling this function.
 */
/* (中文)GlobalVisTest 的"是否仍被视为运行"变体(判活元组的插入者)。
 *
 * 【作用】GlobalVisTestIsRemovableXid 的取反:true = 至少有一个快照
 * 可能把该 xid 视为运行。适用于检查"活元组的插入事务是否还在跑"
 * ——活元组本身不可删,但"事务是否运行"的判定标准与删除场景完全
 * 相同(见英文注释)。
 *
 * 【设计思想】只回答"运行与否"这一语义问题,不判断元组可见性:调用
 * 方仍需自行结合 xid 的提交状态做完整可见性判定(见英文注释)。
 *
 * 【参数】
 *   state        —— 与来源关系匹配的状态;
 *   xid          —— 要判定的 xid;
 *   allow_update —— true 时允许更新边界,false 时绝不更新。
 * 【返回值】true = 可能仍被视为运行。 */
bool
GlobalVisTestXidConsideredRunning(GlobalVisState *state, TransactionId xid,
								  bool allow_update)
{
	return !GlobalVisTestIsRemovableXid(state, xid, allow_update);
}

/*
 * Convenience wrapper around GlobalVisTestFor() and
 * GlobalVisTestIsRemovableFullXid(), see their comments.
 */
/* (中文)便捷包装:按关系取状态后判定 64 位 xid 是否可删。
 *
 * 【作用】GlobalVisTestFor(rel) + GlobalVisTestIsRemovableFullXid
 * (允许更新边界)一步到位,供"关系已知"的调用方使用。
 *
 * 【参数】
 *   rel  —— 目标关系;
 *   fxid —— 要判定的完整事务 id。
 * 【返回值】true = 可安全删除(无快照视为运行)。 */
bool
GlobalVisCheckRemovableFullXid(Relation rel, FullTransactionId fxid)
{
	GlobalVisState *state;

	state = GlobalVisTestFor(rel);

	return GlobalVisTestIsRemovableFullXid(state, fxid, true);
}

/*
 * Convenience wrapper around GlobalVisTestFor() and
 * GlobalVisTestIsRemovableXid(), see their comments.
 */
/* (中文)便捷包装:按关系取状态后判定 32 位 xid 是否可删。
 *
 * 【作用】GlobalVisTestFor(rel) + GlobalVisTestIsRemovableXid(允许
 * 更新边界)一步到位;前提条件与 64 位版本相同(xid 须来自防回绕
 * 的来源)。
 *
 * 【参数】
 *   rel —— 目标关系;
 *   xid —— 要判定的事务 id。
 * 【返回值】true = 可安全删除(无快照视为运行)。 */
bool
GlobalVisCheckRemovableXid(Relation rel, TransactionId xid)
{
	GlobalVisState *state;

	state = GlobalVisTestFor(rel);

	return GlobalVisTestIsRemovableXid(state, xid, true);
}

/*
 * Convert a 32 bit transaction id into 64 bit transaction id, by assuming it
 * is within MaxTransactionId / 2 of XidFromFullTransactionId(rel).
 *
 * Be very careful about when to use this function. It can only safely be used
 * when there is a guarantee that xid is within MaxTransactionId / 2 xids of
 * rel. That e.g. can be guaranteed if the caller assures a snapshot is
 * held by the backend and xid is from a table (where vacuum/freezing ensures
 * the xid has to be within that range), or if xid is from the procarray and
 * prevents xid wraparound that way.
 */
/* (中文)把 32 位事务 id 按"相对差"换算成 64 位 FullTransactionId。
 *
 * 【作用】给定 64 位基准 rel,假设 xid 与 XidFromFullTransactionId(rel)
 * 的差在 ±2^31 之内(即在 32 位事务空间的"半圈"内),用
 * (rel 的 64 位值 + (int32)(xid - rel_xid)) 恢复 xid 的完整 64 位
 * 表示。这是把 32 位 xid 安全提升到 64 位、避免回绕歧义的标准手法
 * (数学上:64 位值单调递增,相对差把符号位一并带回来)。
 *
 * 【设计思想】使用条件极其严格:仅当调用方能保证 xid 与 rel 相距
 * 不超过 MaxTransactionId/2 时可用——例如持有快照时表里的 xid(受
 * VACUUM 冻结保证)、或来自进程数组的 xid(数组本身限制回绕)。
 * 函数内有 AssertTransactionIdInAllowableRange 兜底检查。
 *
 * 【参数】
 *   rel —— 64 位基准(当前时刻的某个已知 FullTransactionId);
 *   xid —— 32 位事务 id(须有效)。
 * 【返回值】换算后的 64 位 FullTransactionId。 */
static inline FullTransactionId
FullXidRelativeTo(FullTransactionId rel, TransactionId xid)
{
	TransactionId rel_xid = XidFromFullTransactionId(rel);

	Assert(TransactionIdIsValid(xid));
	Assert(TransactionIdIsValid(rel_xid));

	/* not guaranteed to find issues, but likely to catch mistakes */
	AssertTransactionIdInAllowableRange(xid);

	return FullTransactionIdFromU64(U64FromFullTransactionId(rel)
									+ (int32) (xid - rel_xid));
}


/* ----------------------------------------------
 *		KnownAssignedTransactionIds sub-module
 * ----------------------------------------------
 */

/*
 * In Hot Standby mode, we maintain a list of transactions that are (or were)
 * running on the primary at the current point in WAL.  These XIDs must be
 * treated as running by standby transactions, even though they are not in
 * the standby server's PGPROC array.
 *
 * We record all XIDs that we know have been assigned.  That includes all the
 * XIDs seen in WAL records, plus all unobserved XIDs that we can deduce have
 * been assigned.  We can deduce the existence of unobserved XIDs because we
 * know XIDs are assigned in sequence, with no gaps.  The KnownAssignedXids
 * list expands as new XIDs are observed or inferred, and contracts when
 * transaction completion records arrive.
 *
 * During hot standby we do not fret too much about the distinction between
 * top-level XIDs and subtransaction XIDs. We store both together in the
 * KnownAssignedXids list.  In backends, this is copied into snapshots in
 * GetSnapshotData(), taking advantage of the fact that XidInMVCCSnapshot()
 * doesn't care about the distinction either.  Subtransaction XIDs are
 * effectively treated as top-level XIDs and in the typical case pg_subtrans
 * links are *not* maintained (which does not affect visibility).
 *
 * We have room in KnownAssignedXids and in snapshots to hold maxProcs *
 * (1 + PGPROC_MAX_CACHED_SUBXIDS) XIDs, so every primary transaction must
 * report its subtransaction XIDs in a WAL XLOG_XACT_ASSIGNMENT record at
 * least every PGPROC_MAX_CACHED_SUBXIDS.  When we receive one of these
 * records, we mark the subXIDs as children of the top XID in pg_subtrans,
 * and then remove them from KnownAssignedXids.  This prevents overflow of
 * KnownAssignedXids and snapshots, at the cost that status checks for these
 * subXIDs will take a slower path through TransactionIdIsInProgress().
 * This means that KnownAssignedXids is not necessarily complete for subXIDs,
 * though it should be complete for top-level XIDs; this is the same situation
 * that holds with respect to the PGPROC entries in normal running.
 *
 * When we throw away subXIDs from KnownAssignedXids, we need to keep track of
 * that, similarly to tracking overflow of a PGPROC's subxids array.  We do
 * that by remembering the lastOverflowedXid, ie the last thrown-away subXID.
 * As long as that is within the range of interesting XIDs, we have to assume
 * that subXIDs are missing from snapshots.  (Note that subXID overflow occurs
 * on primary when 65th subXID arrives, whereas on standby it occurs when 64th
 * subXID arrives - that is not an error.)
 *
 * Should a backend on primary somehow disappear before it can write an abort
 * record, then we just leave those XIDs in KnownAssignedXids. They actually
 * aborted but we think they were running; the distinction is irrelevant
 * because either way any changes done by the transaction are not visible to
 * backends in the standby.  We prune KnownAssignedXids when
 * XLOG_RUNNING_XACTS arrives, to forestall possible overflow of the
 * array due to such dead XIDs.
 */
/* (中文)【KnownAssignedXids 子模块(中文)】
 * 热备模式下,备机用本子模块模拟"主库上正在运行的事务集合"。
 *
 * 思路(详见上方英文注释):xid 按序分配、不留空隙,因此只要观察到
 * 某个 xid,就能推断"它之前的连续区间内所有未观察到的 xid"也已被
 * 分配;把这些"已知已分配"的 xid 都当作"可能仍在运行",就能保证
 * 备机快照不会把主库还在跑的事务误判为已完成。数组随观察到的
 * WAL 记录生长(RecordKnownAssignedTransactionIds),随事务完成记录
 * 收缩(ExpireTreeKnownAssignedTransactionIds 等),还定期用主库的
 * RUNNING_XACTS 快照修剪(ProcArrayApplyRecoveryInfo),防止主库进程
 * 崩溃未写 abort 记录导致的永久残留与溢出。
 *
 * 数据结构与算法(详见 KnownAssignedXidsCompress 前的英文注释):
 * - KnownAssignedXids[] 保持 TransactionIdPrecedes 逻辑序(二分查找
 *   的前提;只要数组跨度不超过半个 xid 空间,该比较就是全序);
 * - 删除用"标记无效"实现(平行数组 KnownAssignedXidsValid[]),制造
 *   空洞换取 O(1) 删除;head/tail 指针标定有效区间 [tail, head),
 *   空洞定期压缩(KnownAssignedXidsCompress),避免回绕;
 * - 添加通常无需加锁(只有 startup 进程写),靠写屏障让读者先看到
 *   数组内容再看到 head 前进;删除/压缩须持 EXCLUSIVE 锁,读取须持
 *   SHARED 锁。
 * 性能特征:添加 O(1)、删除 O(logS)、压缩 O(S)、快照拷贝 O(S),
 * 而 S(数组占用)被"压缩启发式 S >= 2N 即压缩"约束在 2N 内。
 */

/*
 * RecordKnownAssignedTransactionIds
 *		Record the given XID in KnownAssignedXids, as well as any preceding
 *		unobserved XIDs.
 *
 * RecordKnownAssignedTransactionIds() should be run for *every* WAL record
 * associated with a transaction. Must be called for each record after we
 * have executed StartupCLOG() et al, since we must ExtendCLOG() etc..
 *
 * Called during recovery in analogy with and in place of GetNewTransactionId()
 */
/* (中文)登记"已知已分配"的 xid(热备中,凡是事务相关的 WAL 记录
 * 到达都要调用,见英文注释)。
 *
 * 【作用】把 xid 及其之前"推断已分配"的连续区间全部收入
 * KnownAssignedXids,并推进 latestObservedXid:
 * - 若 xid <= latestObservedXid:早已知晓,无事可做;
 * - 否则:先把 pg_subtrans 无缝隙扩展到 xid(与正常流程
 *   GetNewTransactionId 的做法对应;clog 不用扩,其扩展已 WAL 日志
 *   化),再把 (latestObservedXid, xid] 整段加入数组,更新
 *   latestObservedXid,并推进 nextXid 至少到最新观察值。
 *
 * 【设计思想】
 * - "推断已分配"是正确性关键:主库可能跳过中间 xid 的记录(例如
 *   崩溃后提交记录不完整),不补全会让这些 xid 在快照里"凭空消失",
 *   违反无空隙分配的前提(见英文注释);
 * - 数组尚未建立(STANDBY_INITIALIZED 及以前)时只推进
 *   latestObservedXid 并扩 subtrans,等 ProcArrayApplyRecoveryInfo
 *   建立数组后再补登记(它内部会做同样的扩展);
 * - 加锁要求:KnownAssignedXidsAdd 无锁执行(只有 startup 进程写),
 *   靠内存屏障保证读者可见性。
 *
 * 【参数】xid —— 刚观察到的事务 xid(须有效)。
 * 【返回值】无。 */
void
RecordKnownAssignedTransactionIds(TransactionId xid)
{
	Assert(standbyState >= STANDBY_INITIALIZED);
	Assert(TransactionIdIsValid(xid));
	Assert(TransactionIdIsValid(latestObservedXid));

	elog(DEBUG4, "record known xact %u latestObservedXid %u",
		 xid, latestObservedXid);

	/*
	 * When a newly observed xid arrives, it is frequently the case that it is
	 * *not* the next xid in sequence. When this occurs, we must treat the
	 * intervening xids as running also.
	 */
	if (TransactionIdFollows(xid, latestObservedXid))
	{
		TransactionId next_expected_xid;

		/*
		 * Extend subtrans like we do in GetNewTransactionId() during normal
		 * operation using individual extend steps. Note that we do not need
		 * to extend clog since its extensions are WAL logged.
		 *
		 * This part has to be done regardless of standbyState since we
		 * immediately start assigning subtransactions to their toplevel
		 * transactions.
		 */
		next_expected_xid = latestObservedXid;
		while (TransactionIdPrecedes(next_expected_xid, xid))
		{
			TransactionIdAdvance(next_expected_xid);
			ExtendSUBTRANS(next_expected_xid);
		}
		Assert(next_expected_xid == xid);

		/*
		 * If the KnownAssignedXids machinery isn't up yet, there's nothing
		 * more to do since we don't track assigned xids yet.
		 */
		if (standbyState <= STANDBY_INITIALIZED)
		{
			latestObservedXid = xid;
			return;
		}

		/*
		 * Add (latestObservedXid, xid] onto the KnownAssignedXids array.
		 */
		next_expected_xid = latestObservedXid;
		TransactionIdAdvance(next_expected_xid);
		KnownAssignedXidsAdd(next_expected_xid, xid, false);

		/*
		 * Now we can advance latestObservedXid
		 */
		latestObservedXid = xid;

		/* TransamVariables->nextXid must be beyond any observed xid */
		AdvanceNextFullTransactionIdPastXid(latestObservedXid);
	}
}

/*
 * ExpireTreeKnownAssignedTransactionIds
 *		Remove the given XIDs from KnownAssignedXids.
 *
 * Called during recovery in analogy with and in place of ProcArrayEndTransaction()
 */
/* (中文)热备中事务结束时,把该事务整棵树(主 xid + 子 xid)从
 * KnownAssignedXids 中移除(ProcArrayEndTransaction 的恢复期对应)。
 *
 * 【作用】持 EXCLUSIVE 锁删除主 xid 与所有子 xid,再像正常提交那样
 * 推进 latestCompletedXid(恢复版本)与 xactCompletionCount。
 *
 * 【设计思想】与正常提交完全相同的"原子性":删除"正在运行集合"条目
 * 与推进"最新完成事务"必须对取快照者同时可见,否则备机快照会看到
 * 相互矛盾的状态。xactCompletionCount 的递增同样是为了快照复用判定
 * (见 ProcArrayEndTransaction 注释)。
 *
 * 【参数】
 *   xid     —— 顶层事务 xid(可为 InvalidTransactionId,表示只有子事务);
 *   nsubxids、subxids —— 子事务数量与数组;
 *   max_xid —— 本组中最大 xid(推进 latestCompletedXid 用)。
 * 【返回值】无。 */
void
ExpireTreeKnownAssignedTransactionIds(TransactionId xid, int nsubxids,
									  TransactionId *subxids, TransactionId max_xid)
{
	Assert(standbyState >= STANDBY_INITIALIZED);

	/*
	 * Uses same locking as transaction commit
	 */
	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	KnownAssignedXidsRemoveTree(xid, nsubxids, subxids);

	/* As in ProcArrayEndTransaction, advance latestCompletedXid */
	MaintainLatestCompletedXidRecovery(max_xid);

	/* ... and xactCompletionCount */
	TransamVariables->xactCompletionCount++;

	LWLockRelease(ProcArrayLock);
}

/*
 * ExpireAllKnownAssignedTransactionIds
 *		Remove all entries in KnownAssignedXids and reset lastOverflowedXid.
 */
/* (中文)清空整个 KnownAssignedXids 并把相关水位复位。
 *
 * 【作用】恢复结束(进入正常运行时)调用:删除全部条目、把
 * latestCompletedXid 复位为 nextXid - 1(此后所有快照的 xmax 不再
 * 包含恢复期事务)、推进 xactCompletionCount(清空中所有事务都相当于
 * "结束")、复位 lastOverflowedXid。
 *
 * 【设计思想】从恢复切换到正常运行时,备机的进程数组开始承担职责,
 * KnownAssignedXids 使命完成;lastOverflowedXid 虽已无用处,仍复位
 * 以与 ExpireOldKnownAssignedTransactionIds 的行为保持一致(见英文
 * 注释)。
 *
 * 【参数】无。
 * 【返回值】无。 */
void
ExpireAllKnownAssignedTransactionIds(void)
{
	FullTransactionId latestXid;

	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);
	KnownAssignedXidsRemovePreceding(InvalidTransactionId);

	/* Reset latestCompletedXid to nextXid - 1 */
	Assert(FullTransactionIdIsValid(TransamVariables->nextXid));
	latestXid = TransamVariables->nextXid;
	FullTransactionIdRetreat(&latestXid);
	TransamVariables->latestCompletedXid = latestXid;

	/*
	 * Any transactions that were in-progress were effectively aborted, so
	 * advance xactCompletionCount.
	 */
	TransamVariables->xactCompletionCount++;

	/*
	 * Reset lastOverflowedXid.  Currently, lastOverflowedXid has no use after
	 * the call of this function.  But do this for unification with what
	 * ExpireOldKnownAssignedTransactionIds() do.
	 */
	procArray->lastOverflowedXid = InvalidTransactionId;
	LWLockRelease(ProcArrayLock);
}

/*
 * ExpireOldKnownAssignedTransactionIds
 *		Remove KnownAssignedXids entries preceding the given XID and
 *		potentially reset lastOverflowedXid.
 */
/* (中文)修剪 KnownAssignedXids:删除所有早于给定 xid 的条目。
 *
 * 【作用】收到主库 RUNNING_XACTS 快照时调用(见
 * ProcArrayApplyRecoveryInfo):以 oldestRunningXid 为界,把比它还老
 * 的条目全部标为无效(能保留的"还可能在运行"的 xid 只可能是比它新
 * 的),并顺带推进 latestCompletedXid 与 xactCompletionCount。若
 * lastOverflowedXid 也早于该 xid,说明所有"曾丢失子事务"的 xid 都
 * 已被跨越,可以安全复位 lastOverflowedXid(否则快照会被多余地标记
 * 为子事务溢出,见英文注释)。
 *
 * 【设计思想】这就是防 KnownAssignedXids 无限膨胀的"消毒"手段:
 * 主库进程崩溃可能留下没有 abort 记录的僵尸事务,只有主库的快照能
 * 证明它们早已消失。
 *
 * 【参数】xid —— 修剪水位:所有 < xid 的条目被删除。
 * 【返回值】无。 */
void
ExpireOldKnownAssignedTransactionIds(TransactionId xid)
{
	TransactionId latestXid;

	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	/* As in ProcArrayEndTransaction, advance latestCompletedXid */
	latestXid = xid;
	TransactionIdRetreat(latestXid);
	MaintainLatestCompletedXidRecovery(latestXid);

	/* ... and xactCompletionCount */
	TransamVariables->xactCompletionCount++;

	/*
	 * Reset lastOverflowedXid if we know all transactions that have been
	 * possibly running are being gone.  Not doing so could cause an incorrect
	 * lastOverflowedXid value, which makes extra snapshots be marked as
	 * suboverflowed.
	 */
	if (TransactionIdPrecedes(procArray->lastOverflowedXid, xid))
		procArray->lastOverflowedXid = InvalidTransactionId;
	KnownAssignedXidsRemovePreceding(xid);
	LWLockRelease(ProcArrayLock);
}

/*
 * KnownAssignedTransactionIdsIdleMaintenance
 *		Opportunistically do maintenance work when the startup process
 *		is about to go idle.
 */
/* (中文)startup 进程即将空闲时,机会式地做 KnownAssignedXids 维护。
 *
 * 【作用】热备中 WAL 消费暂时耗尽(即将休眠等待新记录)时调用:触发
 * 一次"空闲压缩"(KAX_STARTUP_PROCESS_IDLE)。空闲期间反正没有新 xid
 * 到来,压缩不会干扰正常添加;通过限制压缩频率(至少间隔 1 秒)避免
 * 与快照读者频繁争用 ProcArrayLock(见 KnownAssignedXidsCompress 的
 * 英文注释)。
 *
 * 【参数】无。
 * 【返回值】无。 */
void
KnownAssignedTransactionIdsIdleMaintenance(void)
{
	KnownAssignedXidsCompress(KAX_STARTUP_PROCESS_IDLE, false);
}


/*
 * Private module functions to manipulate KnownAssignedXids
 *
 * There are 5 main uses of the KnownAssignedXids data structure:
 *
 *	* backends taking snapshots - all valid XIDs need to be copied out
 *	* backends seeking to determine presence of a specific XID
 *	* startup process adding new known-assigned XIDs
 *	* startup process removing specific XIDs as transactions end
 *	* startup process pruning array when special WAL records arrive
 *
 * This data structure is known to be a hot spot during Hot Standby, so we
 * go to some lengths to make these operations as efficient and as concurrent
 * as possible.
 *
 * The XIDs are stored in an array in sorted order --- TransactionIdPrecedes
 * order, to be exact --- to allow binary search for specific XIDs.  Note:
 * in general TransactionIdPrecedes would not provide a total order, but
 * we know that the entries present at any instant should not extend across
 * a large enough fraction of XID space to wrap around (the primary would
 * shut down for fear of XID wrap long before that happens).  So it's OK to
 * use TransactionIdPrecedes as a binary-search comparator.
 *
 * It's cheap to maintain the sortedness during insertions, since new known
 * XIDs are always reported in XID order; we just append them at the right.
 *
 * To keep individual deletions cheap, we need to allow gaps in the array.
 * This is implemented by marking array elements as valid or invalid using
 * the parallel boolean array KnownAssignedXidsValid[].  A deletion is done
 * by setting KnownAssignedXidsValid[i] to false, *without* clearing the
 * XID entry itself.  This preserves the property that the XID entries are
 * sorted, so we can do binary searches easily.  Periodically we compress
 * out the unused entries; that's much cheaper than having to compress the
 * array immediately on every deletion.
 *
 * The actually valid items in KnownAssignedXids[] and KnownAssignedXidsValid[]
 * are those with indexes tail <= i < head; items outside this subscript range
 * have unspecified contents.  When head reaches the end of the array, we
 * force compression of unused entries rather than wrapping around, since
 * allowing wraparound would greatly complicate the search logic.  We maintain
 * an explicit tail pointer so that pruning of old XIDs can be done without
 * immediately moving the array contents.  In most cases only a small fraction
 * of the array contains valid entries at any instant.
 *
 * Although only the startup process can ever change the KnownAssignedXids
 * data structure, we still need interlocking so that standby backends will
 * not observe invalid intermediate states.  The convention is that backends
 * must hold shared ProcArrayLock to examine the array.  To remove XIDs from
 * the array, the startup process must hold ProcArrayLock exclusively, for
 * the usual transactional reasons (compare commit/abort of a transaction
 * during normal running).  Compressing unused entries out of the array
 * likewise requires exclusive lock.  To add XIDs to the array, we just insert
 * them into slots to the right of the head pointer and then advance the head
 * pointer.  This doesn't require any lock at all, but on machines with weak
 * memory ordering, we need to be careful that other processors see the array
 * element changes before they see the head pointer change.  We handle this by
 * using memory barriers when reading or writing the head/tail pointers (unless
 * the caller holds ProcArrayLock exclusively).
 *
 * Algorithmic analysis:
 *
 * If we have a maximum of M slots, with N XIDs currently spread across
 * S elements then we have N <= S <= M always.
 *
 *	* Adding a new XID is O(1) and needs no lock (unless compression must
 *		happen)
 *	* Compressing the array is O(S) and requires exclusive lock
 *	* Removing an XID is O(logS) and requires exclusive lock
 *	* Taking a snapshot is O(S) and requires shared lock
 *	* Checking for an XID is O(logS) and requires shared lock
 *
 * In comparison, using a hash table for KnownAssignedXids would mean that
 * taking snapshots would be O(M). If we can maintain S << M then the
 * sorted array technique will deliver significantly faster snapshots.
 * If we try to keep S too small then we will spend too much time compressing,
 * so there is an optimal point for any workload mix. We use a heuristic to
 * decide when to compress the array, though trimming also helps reduce
 * frequency of compressing. The heuristic requires us to track the number of
 * currently valid XIDs in the array (N).  Except in special cases, we'll
 * compress when S >= 2N.  Bounding S at 2N in turn bounds the time for
 * taking a snapshot to be O(N), which it would have to be anyway.
 */


/*
 * Compress KnownAssignedXids by shifting valid data down to the start of the
 * array, removing any gaps.
 *
 * A compression step is forced if "reason" is KAX_NO_SPACE, otherwise
 * we do it only if a heuristic indicates it's a good time to do it.
 *
 * Compression requires holding ProcArrayLock in exclusive mode.
 * Caller must pass haveLock = true if it already holds the lock.
 */
/* (中文)压缩 KnownAssignedXids:把 [tail, head) 中仍有效的条目紧挨着
 * 搬到数组头部,消除因"标记无效式删除"积累的空洞。
 *
 * 【作用】按 reason 决定是否真的压缩:
 * - KAX_NO_SPACE:必须压缩(数组尾部放不下新 xid);
 * - KAX_TRANSACTION_END:每 128 次事务结束才考虑一次,且仅当数组
 *   占用 S >= 2N(有效条目数 N,空洞占了一半以上)时压缩;
 * - KAX_PRUNE:批量修剪后顺手压缩;
 * - KAX_STARTUP_PROCESS_IDLE:空闲时压缩,但距上次压缩不足 1 秒则
 *   跳过(避免频繁争锁)。
 * 压缩后 head/tail 归零、numKnownAssignedXids 不变。
 *
 * 【设计思想】
 * - 延迟压缩的取舍:立即压缩是 O(S),会把删除的成本从 O(logS) 摊成
 *   O(S);而"只在快照与添加真的受影响时再压缩"让 S 稳定在 2N 以内,
 *   快照拷贝的上界因此是 O(N)(算法分析见上方英文注释);
 * - 为什么必须 EXCLUSIVE 锁:压缩要整体搬移数组,读者必须在锁外
 *   观察不到中间状态;
 * - 只有 startup 进程写 head/tail,所以压缩前读它们无需加锁。
 *
 * 【参数】
 *   reason   —— 压缩触发原因(KAXCompressReason 枚举);
 *   haveLock —— true 表示调用方已持 ProcArrayLock EXCLUSIVE。
 * 【返回值】无。 */
static void
KnownAssignedXidsCompress(KAXCompressReason reason, bool haveLock)
{
	ProcArrayStruct *pArray = procArray;
	int			head,
				tail,
				nelements;
	int			compress_index;
	int			i;

	/* Counters for compression heuristics */
	static unsigned int transactionEndsCounter;
	static TimestampTz lastCompressTs;

	/* Tuning constants */
#define KAX_COMPRESS_FREQUENCY 128	/* in transactions */
#define KAX_COMPRESS_IDLE_INTERVAL 1000 /* in ms */

	/*
	 * Since only the startup process modifies the head/tail pointers, we
	 * don't need a lock to read them here.
	 */
	head = pArray->headKnownAssignedXids;
	tail = pArray->tailKnownAssignedXids;
	nelements = head - tail;

	/*
	 * If we can choose whether to compress, use a heuristic to avoid
	 * compressing too often or not often enough.  "Compress" here simply
	 * means moving the values to the beginning of the array, so it is not as
	 * complex or costly as typical data compression algorithms.
	 */
	if (nelements == pArray->numKnownAssignedXids)
	{
		/*
		 * When there are no gaps between head and tail, don't bother to
		 * compress, except in the KAX_NO_SPACE case where we must compress to
		 * create some space after the head.
		 */
		if (reason != KAX_NO_SPACE)
			return;
	}
	else if (reason == KAX_TRANSACTION_END)
	{
		/*
		 * Consider compressing only once every so many commits.  Frequency
		 * determined by benchmarks.
		 */
		if ((transactionEndsCounter++) % KAX_COMPRESS_FREQUENCY != 0)
			return;

		/*
		 * Furthermore, compress only if the used part of the array is less
		 * than 50% full (see comments above).
		 */
		if (nelements < 2 * pArray->numKnownAssignedXids)
			return;
	}
	else if (reason == KAX_STARTUP_PROCESS_IDLE)
	{
		/*
		 * We're about to go idle for lack of new WAL, so we might as well
		 * compress.  But not too often, to avoid ProcArray lock contention
		 * with readers.
		 */
		if (lastCompressTs != 0)
		{
			TimestampTz compress_after;

			compress_after = TimestampTzPlusMilliseconds(lastCompressTs,
														 KAX_COMPRESS_IDLE_INTERVAL);
			if (GetCurrentTimestamp() < compress_after)
				return;
		}
	}

	/* Need to compress, so get the lock if we don't have it. */
	if (!haveLock)
		LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	/*
	 * We compress the array by reading the valid values from tail to head,
	 * re-aligning data to 0th element.
	 */
	compress_index = 0;
	for (i = tail; i < head; i++)
	{
		if (KnownAssignedXidsValid[i])
		{
			KnownAssignedXids[compress_index] = KnownAssignedXids[i];
			KnownAssignedXidsValid[compress_index] = true;
			compress_index++;
		}
	}
	Assert(compress_index == pArray->numKnownAssignedXids);

	pArray->tailKnownAssignedXids = 0;
	pArray->headKnownAssignedXids = compress_index;

	if (!haveLock)
		LWLockRelease(ProcArrayLock);

	/* Update timestamp for maintenance.  No need to hold lock for this. */
	lastCompressTs = GetCurrentTimestamp();
}

/*
 * Add xids into KnownAssignedXids at the head of the array.
 *
 * xids from from_xid to to_xid, inclusive, are added to the array.
 *
 * If exclusive_lock is true then caller already holds ProcArrayLock in
 * exclusive mode, so we need no extra locking here.  Else caller holds no
 * lock, so we need to be sure we maintain sufficient interlocks against
 * concurrent readers.  (Only the startup process ever calls this, so no need
 * to worry about concurrent writers.)
 */
/* (中文)把 [from_xid, to_xid] 闭区间内的一串连续 xid 追加到
 * KnownAssignedXids 数组头部(添加原语)。
 *
 * 【作用】先算区间长度 nxids,若放不下就先压缩(KAX_NO_SPACE);然后
 * 从 head 处顺序写入 xid 与有效标志,推进 numKnownAssignedXids 与
 * head 指针。要求插入严格递增(from_xid 必须大于等于数组中最后一个
 * 元素,即便那个元素已标记无效,违者报错并打印数组供调试)。
 *
 * 【设计思想】
 * - 无锁添加 + 内存屏障:只有 startup 进程写数组,不存在写写竞争;
 *   读者(持 SHARED 锁或干脆无锁读取)依赖"先看到数组内容、再看到
 *   head 前进"的顺序,因此 !exclusive_lock 时用 pg_write_barrier
 *   保证该顺序(见英文注释);
 * - exclusive_lock 参数:调用方已持 EXCLUSIVE 锁时(例如
 *   ProcArrayApplyRecoveryInfo 批量装载),屏障可省且压缩时不再重复
 *   加锁。
 *
 * 【参数】
 *   from_xid —— 区间起点(含);
 *   to_xid   —— 区间终点(含),须 >= from_xid;
 *   exclusive_lock —— true 表示调用方已持 EXCLUSIVE 锁。
 * 【返回值】无。数组容量不足且压缩后仍放不下时报错。 */
static void
KnownAssignedXidsAdd(TransactionId from_xid, TransactionId to_xid,
					 bool exclusive_lock)
{
	ProcArrayStruct *pArray = procArray;
	TransactionId next_xid;
	int			head,
				tail;
	int			nxids;
	int			i;

	Assert(TransactionIdPrecedesOrEquals(from_xid, to_xid));

	/*
	 * Calculate how many array slots we'll need.  Normally this is cheap; in
	 * the unusual case where the XIDs cross the wrap point, we do it the hard
	 * way.
	 */
	if (to_xid >= from_xid)
		nxids = to_xid - from_xid + 1;
	else
	{
		nxids = 1;
		next_xid = from_xid;
		while (TransactionIdPrecedes(next_xid, to_xid))
		{
			nxids++;
			TransactionIdAdvance(next_xid);
		}
	}

	/*
	 * Since only the startup process modifies the head/tail pointers, we
	 * don't need a lock to read them here.
	 */
	head = pArray->headKnownAssignedXids;
	tail = pArray->tailKnownAssignedXids;

	Assert(head >= 0 && head <= pArray->maxKnownAssignedXids);
	Assert(tail >= 0 && tail < pArray->maxKnownAssignedXids);

	/*
	 * Verify that insertions occur in TransactionId sequence.  Note that even
	 * if the last existing element is marked invalid, it must still have a
	 * correctly sequenced XID value.
	 */
	if (head > tail &&
		TransactionIdFollowsOrEquals(KnownAssignedXids[head - 1], from_xid))
	{
		KnownAssignedXidsDisplay(LOG);
		elog(ERROR, "out-of-order XID insertion in KnownAssignedXids");
	}

	/*
	 * If our xids won't fit in the remaining space, compress out free space
	 */
	if (head + nxids > pArray->maxKnownAssignedXids)
	{
		KnownAssignedXidsCompress(KAX_NO_SPACE, exclusive_lock);

		head = pArray->headKnownAssignedXids;
		/* note: we no longer care about the tail pointer */

		/*
		 * If it still won't fit then we're out of memory
		 */
		if (head + nxids > pArray->maxKnownAssignedXids)
			elog(ERROR, "too many KnownAssignedXids");
	}

	/* Now we can insert the xids into the space starting at head */
	next_xid = from_xid;
	for (i = 0; i < nxids; i++)
	{
		KnownAssignedXids[head] = next_xid;
		KnownAssignedXidsValid[head] = true;
		TransactionIdAdvance(next_xid);
		head++;
	}

	/* Adjust count of number of valid entries */
	pArray->numKnownAssignedXids += nxids;

	/*
	 * Now update the head pointer.  We use a write barrier to ensure that
	 * other processors see the above array updates before they see the head
	 * pointer change.  The barrier isn't required if we're holding
	 * ProcArrayLock exclusively.
	 */
	if (!exclusive_lock)
		pg_write_barrier();

	pArray->headKnownAssignedXids = head;
}

/*
 * KnownAssignedXidsSearch
 *
 * Searches KnownAssignedXids for a specific xid and optionally removes it.
 * Returns true if it was found, false if not.
 *
 * Caller must hold ProcArrayLock in shared or exclusive mode.
 * Exclusive lock must be held for remove = true.
 */
/* (中文)在 KnownAssignedXids 中查找(并可选地删除)指定 xid。
 *
 * 【作用】标准二分查找:在 [tail, head) 内用 TransactionIdPrecedes
 * 折半定位 xid;找到且有效(remove 时)则标记为无效、递减计数,若删
 * 的是 tail 元素则顺带把 tail 前移到下一个有效元素(数组空则双指针
 * 归零)。返回是否"找到且有效"。
 *
 * 【设计思想】
 * - 二分查找可以无视有效标志:无效条目只是"标记过",xid 值本身仍
 *   按序摆放,数组整体保持有序(见英文注释);
 * - 删除用"标无效"而非物理删除,保持 O(logS) 而不是 O(S);
 * - 读者(remove == false)要先 pg_read_barrier 再读,与
 *   KnownAssignedXidsAdd 的写屏障配对;删除方(remove == true)只
 *   有 startup 进程,无需该屏障;
 * - tail 的前移是启发式加速:tail 处聚集的无效条目不必留到下次压缩。
 *
 * 【参数】
 *   xid    —— 要查找的 xid;
 *   remove —— true 时执行删除(调用方必须持 EXCLUSIVE 锁)。
 * 【返回值】true = 找到且条目有效(若 remove,已删除)。 */
static bool
KnownAssignedXidsSearch(TransactionId xid, bool remove)
{
	ProcArrayStruct *pArray = procArray;
	int			first,
				last;
	int			head;
	int			tail;
	int			result_index = -1;

	tail = pArray->tailKnownAssignedXids;
	head = pArray->headKnownAssignedXids;

	/*
	 * Only the startup process removes entries, so we don't need the read
	 * barrier in that case.
	 */
	if (!remove)
		pg_read_barrier();		/* pairs with KnownAssignedXidsAdd */

	/*
	 * Standard binary search.  Note we can ignore the KnownAssignedXidsValid
	 * array here, since even invalid entries will contain sorted XIDs.
	 */
	first = tail;
	last = head - 1;
	while (first <= last)
	{
		int			mid_index;
		TransactionId mid_xid;

		mid_index = (first + last) / 2;
		mid_xid = KnownAssignedXids[mid_index];

		if (xid == mid_xid)
		{
			result_index = mid_index;
			break;
		}
		else if (TransactionIdPrecedes(xid, mid_xid))
			last = mid_index - 1;
		else
			first = mid_index + 1;
	}

	if (result_index < 0)
		return false;			/* not in array */

	if (!KnownAssignedXidsValid[result_index])
		return false;			/* in array, but invalid */

	if (remove)
	{
		KnownAssignedXidsValid[result_index] = false;

		pArray->numKnownAssignedXids--;
		Assert(pArray->numKnownAssignedXids >= 0);

		/*
		 * If we're removing the tail element then advance tail pointer over
		 * any invalid elements.  This will speed future searches.
		 */
		if (result_index == tail)
		{
			tail++;
			while (tail < head && !KnownAssignedXidsValid[tail])
				tail++;
			if (tail >= head)
			{
				/* Array is empty, so we can reset both pointers */
				pArray->headKnownAssignedXids = 0;
				pArray->tailKnownAssignedXids = 0;
			}
			else
			{
				pArray->tailKnownAssignedXids = tail;
			}
		}
	}

	return true;
}

/*
 * Is the specified XID present in KnownAssignedXids[]?
 *
 * Caller must hold ProcArrayLock in shared or exclusive mode.
 */
/* (中文)查询指定 xid 是否在 KnownAssignedXids 中(仅查询,不删除)。
 *
 * 【作用】TransactionIdIsInProgress 的热备路径入口:命中即说明主库
 * 上该事务仍可能运行。实现即 KnownAssignedXidsSearch(xid, false)。
 *
 * 【参数】xid —— 要查询的 xid(须有效)。
 * 【返回值】true = 存在且有效。 */
static bool
KnownAssignedXidExists(TransactionId xid)
{
	Assert(TransactionIdIsValid(xid));

	return KnownAssignedXidsSearch(xid, false);
}

/*
 * Remove the specified XID from KnownAssignedXids[].
 *
 * Caller must hold ProcArrayLock in exclusive mode.
 */
/* (中文)从 KnownAssignedXids 中删除单个 xid。
 *
 * 【作用】KnownAssignedXidsSearch(xid, true) 的薄封装(忽略返回值)。
 *
 * 【设计思想】找不到不算错误:处理 XLOG_XACT_ASSIGNMENT 时会故意先
 * 删掉子 xid(防数组溢出),顶层事务提交/中止时它们会再被删一次,因此
 * 第二次删除必然落空(见英文注释);区分"真错误"需要额外记账,不值
 * 得。
 *
 * 【参数】xid —— 要删除的 xid(须有效)。
 * 【返回值】无。 */
static void
KnownAssignedXidsRemove(TransactionId xid)
{
	Assert(TransactionIdIsValid(xid));

	elog(DEBUG4, "remove KnownAssignedXid %u", xid);

	/*
	 * Note: we cannot consider it an error to remove an XID that's not
	 * present.  We intentionally remove subxact IDs while processing
	 * XLOG_XACT_ASSIGNMENT, to avoid array overflow.  Then those XIDs will be
	 * removed again when the top-level xact commits or aborts.
	 *
	 * It might be possible to track such XIDs to distinguish this case from
	 * actual errors, but it would be complicated and probably not worth it.
	 * So, just ignore the search result.
	 */
	(void) KnownAssignedXidsSearch(xid, true);
}

/*
 * KnownAssignedXidsRemoveTree
 *		Remove xid (if it's not InvalidTransactionId) and all the subxids.
 *
 * Caller must hold ProcArrayLock in exclusive mode.
 */
/* (中文)从 KnownAssignedXids 中删除一整棵事务树(主 xid + 全部子 xid)。
 *
 * 【作用】先删主 xid(若有效)再逐个删子 xid,最后机会式地压缩一次
 * (KAX_TRANSACTION_END:带频率与空洞比例的启发式)。
 *
 * 【设计思想】事务结束时"整树消失"是一次原子事件,压缩与删除在同
 * 一 EXCLUSIVE 锁区间内完成,读者不会看到半删除状态。
 *
 * 【参数】
 *   xid     —— 顶层事务 xid(可为 InvalidTransactionId);
 *   nsubxids、subxids —— 子事务数量与数组。
 * 【返回值】无。 */
static void
KnownAssignedXidsRemoveTree(TransactionId xid, int nsubxids,
							TransactionId *subxids)
{
	int			i;

	if (TransactionIdIsValid(xid))
		KnownAssignedXidsRemove(xid);

	for (i = 0; i < nsubxids; i++)
		KnownAssignedXidsRemove(subxids[i]);

	/* Opportunistically compress the array */
	KnownAssignedXidsCompress(KAX_TRANSACTION_END, true);
}

/*
 * Prune KnownAssignedXids up to, but *not* including xid. If xid is invalid
 * then clear the whole table.
 *
 * Caller must hold ProcArrayLock in exclusive mode.
 */
/* (中文)修剪 KnownAssignedXids:删除所有 < removeXid 的条目
 * (removeXid 无效时清空整张表)。
 *
 * 【作用】从 tail 顺序扫描,凡是 xid < removeXid 的条目标记无效
 * (prepared 事务除外,见设计思想);更新计数与 tail 指针(顺带把
 * 连续无效的头部一起吃掉;表空则双指针归零);最后机会式压缩
 * (KAX_PRUNE)。
 *
 * 【设计思想】
 * - 数组有序,扫描到第一个 >= removeXid 的条目即可停止;
 * - 跳过 prepared 事务(StandbyTransactionIdIsPrepared):它们是
 *   两阶段提交的事务,尚未结束,不能当过期条目修剪;
 * - 与 KnownAssignedXidsSearch 的"单点删除"互补:这里是一次性
 *   批量删除,用于主库 RUNNING_XACTS 快照到达时的整体梳理。
 *
 * 【参数】removeXid —— 修剪水位(不含);InvalidTransactionId = 清空。
 * 【返回值】无。 */
static void
KnownAssignedXidsRemovePreceding(TransactionId removeXid)
{
	ProcArrayStruct *pArray = procArray;
	int			count = 0;
	int			head,
				tail,
				i;

	if (!TransactionIdIsValid(removeXid))
	{
		elog(DEBUG4, "removing all KnownAssignedXids");
		pArray->numKnownAssignedXids = 0;
		pArray->headKnownAssignedXids = pArray->tailKnownAssignedXids = 0;
		return;
	}

	elog(DEBUG4, "prune KnownAssignedXids to %u", removeXid);

	/*
	 * Mark entries invalid starting at the tail.  Since array is sorted, we
	 * can stop as soon as we reach an entry >= removeXid.
	 */
	tail = pArray->tailKnownAssignedXids;
	head = pArray->headKnownAssignedXids;

	for (i = tail; i < head; i++)
	{
		if (KnownAssignedXidsValid[i])
		{
			TransactionId knownXid = KnownAssignedXids[i];

			if (TransactionIdFollowsOrEquals(knownXid, removeXid))
				break;

			if (!StandbyTransactionIdIsPrepared(knownXid))
			{
				KnownAssignedXidsValid[i] = false;
				count++;
			}
		}
	}

	pArray->numKnownAssignedXids -= count;
	Assert(pArray->numKnownAssignedXids >= 0);

	/*
	 * Advance the tail pointer if we've marked the tail item invalid.
	 */
	for (i = tail; i < head; i++)
	{
		if (KnownAssignedXidsValid[i])
			break;
	}
	if (i >= head)
	{
		/* Array is empty, so we can reset both pointers */
		pArray->headKnownAssignedXids = 0;
		pArray->tailKnownAssignedXids = 0;
	}
	else
	{
		pArray->tailKnownAssignedXids = i;
	}

	/* Opportunistically compress the array */
	KnownAssignedXidsCompress(KAX_PRUNE, true);
}

/*
 * KnownAssignedXidsGet - Get an array of xids by scanning KnownAssignedXids.
 * We filter out anything >= xmax.
 *
 * Returns the number of XIDs stored into xarray[].  Caller is responsible
 * that array is large enough.
 *
 * Caller must hold ProcArrayLock in (at least) shared mode.
 */
/* (中文)把 KnownAssignedXids 中小于 xmax 的全部 xid 拷出到调用方数组。
 *
 * 【作用】TransactionIdIsInProgress 的步骤 3(热备、数组溢出时)使用:
 * 收集所有 < xid 的 KnownAssignedXids 条目——若目标 xid 是子事务,
 * 它的父事务必然更小,正好从这批候选中继续查。xmin 输出参数用
 * 一个临时变量承接(不关心),实际逻辑全部委托给
 * KnownAssignedXidsGetAndSetXmin。
 *
 * 【参数】
 *   xarray —— 输出:拷贝的 xid 数组(容量须足够);
 *   xmax   —— 过滤水位:>= xmax 的不拷贝。
 * 【返回值】拷出的 xid 数量。 */
static int
KnownAssignedXidsGet(TransactionId *xarray, TransactionId xmax)
{
	TransactionId xtmp = InvalidTransactionId;

	return KnownAssignedXidsGetAndSetXmin(xarray, &xtmp, xmax);
}

/*
 * KnownAssignedXidsGetAndSetXmin - as KnownAssignedXidsGet, plus
 * we reduce *xmin to the lowest xid value seen if not already lower.
 *
 * Caller must hold ProcArrayLock in (at least) shared mode.
 */
/* (中文)KnownAssignedXidsGet 的增强版:拷贝的同时把 xmin 下压到
 * 所见最小 xid。
 *
 * 【作用】GetSnapshotData 的热备路径调用:把所有有效条目(< xmax)
 * 拷入 subxip 数组,并让 xmin 不高于数组中第一个(即最小的)有效
 * xid——数组有序,只检查第一个拷贝的条目即可。
 *
 * 【设计思想】
 * - head 只读一次:持有 SHARED 锁期间,条目只会"从有效变无效"
 *   (startup 进程删除)或"在 head 处新增";新增的 xid >= xmax(主库
 *   快照的 xmax 之外),对结果无影响,读到旧的 head 就够了(见英文
 *   注释);
 * - 有效性判断跳过"空洞";过滤 >= xmax 的条目同样利用有序性提前
 *   break。
 *
 * 【参数】
 *   xarray —— 输出:xid 数组(容量须足够);
 *   xmin   —— 输入输出:初始 xmin,被下压到所见最小值;
 *   xmax   —— 过滤水位。
 * 【返回值】拷出的 xid 数量。 */
static int
KnownAssignedXidsGetAndSetXmin(TransactionId *xarray, TransactionId *xmin,
							   TransactionId xmax)
{
	int			count = 0;
	int			head,
				tail;
	int			i;

	/*
	 * Fetch head just once, since it may change while we loop. We can stop
	 * once we reach the initially seen head, since we are certain that an xid
	 * cannot enter and then leave the array while we hold ProcArrayLock.  We
	 * might miss newly-added xids, but they should be >= xmax so irrelevant
	 * anyway.
	 */
	tail = procArray->tailKnownAssignedXids;
	head = procArray->headKnownAssignedXids;

	pg_read_barrier();			/* pairs with KnownAssignedXidsAdd */

	for (i = tail; i < head; i++)
	{
		/* Skip any gaps in the array */
		if (KnownAssignedXidsValid[i])
		{
			TransactionId knownXid = KnownAssignedXids[i];

			/*
			 * Update xmin if required.  Only the first XID need be checked,
			 * since the array is sorted.
			 */
			if (count == 0 &&
				TransactionIdPrecedes(knownXid, *xmin))
				*xmin = knownXid;

			/*
			 * Filter out anything >= xmax, again relying on sorted property
			 * of array.
			 */
			if (TransactionIdIsValid(xmax) &&
				TransactionIdFollowsOrEquals(knownXid, xmax))
				break;

			/* Add knownXid into output array */
			xarray[count++] = knownXid;
		}
	}

	return count;
}

/*
 * Get oldest XID in the KnownAssignedXids array, or InvalidTransactionId
 * if nothing there.
 */
/* (中文)返回 KnownAssignedXids 中最老的 xid。
 *
 * 【作用】ComputeXidHorizons 在恢复期调用:备机的"运行事务下界"需要
 * 用 KnownAssignedXids 的最老条目补充(数组有序,第一个有效条目就是
 * 最老)。数组为空返回 InvalidTransactionId。
 *
 * 【设计思想】head/tail 的读取加读屏障与 KnownAssignedXidsAdd 配对;
 * 由持 SHARED 锁的调用方使用,保证扫描期间数组不被删除。
 *
 * 【参数】无。
 * 【返回值】最老的有效 xid,或 InvalidTransactionId。 */
static TransactionId
KnownAssignedXidsGetOldestXmin(void)
{
	int			head,
				tail;
	int			i;

	/*
	 * Fetch head just once, since it may change while we loop.
	 */
	tail = procArray->tailKnownAssignedXids;
	head = procArray->headKnownAssignedXids;

	pg_read_barrier();			/* pairs with KnownAssignedXidsAdd */

	for (i = tail; i < head; i++)
	{
		/* Skip any gaps in the array */
		if (KnownAssignedXidsValid[i])
			return KnownAssignedXids[i];
	}

	return InvalidTransactionId;
}

/*
 * Display KnownAssignedXids to provide debug trail
 *
 * Currently this is only called within startup process, so we need no
 * special locking.
 *
 * Note this is pretty expensive, and much of the expense will be incurred
 * even if the elog message will get discarded.  It's not currently called
 * in any performance-critical places, however, so no need to be tenser.
 */
/* (中文)把 KnownAssignedXids 的当前内容拼成一条日志输出(调试用)。
 *
 * 【作用】在指定 trace_level 打印有效条目数、数组控制字段与每个
 * 有效条目 [下标]=xid 的清单。
 *
 * 【设计思想】只在 startup 进程内调用,无需加锁;构造字符串本身
 * 有成本,但调用点都不在性能关键路径上(见英文注释)。
 *
 * 【参数】trace_level —— elog 级别(如 DEBUG3、LOG)。
 * 【返回值】无。 */
static void
KnownAssignedXidsDisplay(int trace_level)
{
	ProcArrayStruct *pArray = procArray;
	StringInfoData buf;
	int			head,
				tail,
				i;
	int			nxids = 0;

	tail = pArray->tailKnownAssignedXids;
	head = pArray->headKnownAssignedXids;

	initStringInfo(&buf);

	for (i = tail; i < head; i++)
	{
		if (KnownAssignedXidsValid[i])
		{
			nxids++;
			appendStringInfo(&buf, "[%d]=%u ", i, KnownAssignedXids[i]);
		}
	}

	elog(trace_level, "%d KnownAssignedXids (num=%d tail=%d head=%d) %s",
		 nxids,
		 pArray->numKnownAssignedXids,
		 pArray->tailKnownAssignedXids,
		 pArray->headKnownAssignedXids,
		 buf.data);

	pfree(buf.data);
}

/*
 * KnownAssignedXidsReset
 *		Resets KnownAssignedXids to be empty
 */
/* (中文)把 KnownAssignedXids 重置为空表。
 *
 * 【作用】ProcArrayApplyRecoveryInfo 在丢弃旧快照、换用新快照前调用:
 * 持 EXCLUSIVE 锁把计数与 head/tail 全部归零。
 *
 * 【设计思想】只复位指针与计数、不清数组内容:旧内容被 head/tail
 * 区间自然屏蔽,下一次添加会直接覆盖(数组有序性由新添加保证)。
 *
 * 【参数】无。
 * 【返回值】无。 */
static void
KnownAssignedXidsReset(void)
{
	ProcArrayStruct *pArray = procArray;

	LWLockAcquire(ProcArrayLock, LW_EXCLUSIVE);

	pArray->numKnownAssignedXids = 0;
	pArray->tailKnownAssignedXids = 0;
	pArray->headKnownAssignedXids = 0;

	LWLockRelease(ProcArrayLock);
}
