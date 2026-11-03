/*-------------------------------------------------------------------------
 *
 * xact.c
 *	  top level transaction system support routines
 *
 * See src/backend/access/transam/README for more information.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/access/transam/xact.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 顶层事务管理，主要包括：
 *   1. 事务/子事务状态机（TransState 与 TBlockState）；
 *   2. 事务的启动、提交、两阶段提交（PREPARE）、中止与清理；
 *   3. XID/命令 ID 分配、事务时间戳、并行模式等状态访问器；
 *   4. 保存点（SAVEPOINT）与内部子事务支持；
 *   5. 事务 WAL 记录（XLOG_XACT_COMMIT/ABORT）的写入与恢复重放；
 *   6. 事务回调，以及 BEGIN/COMMIT/ROLLBACK 等事务块命令的接口实现。
 * 更完整的背景说明见 src/backend/access/transam/README。
 */

#include "postgres.h"

#include <time.h>
#include <unistd.h>

#include "access/commit_ts.h"
#include "access/multixact.h"
#include "access/parallel.h"
#include "access/subtrans.h"
#include "access/transam.h"
#include "access/twophase.h"
#include "access/xact.h"
#include "access/xlog.h"
#include "access/xloginsert.h"
#include "access/xlogrecovery.h"
#include "access/xlogutils.h"
#include "access/xlogwait.h"
#include "catalog/index.h"
#include "catalog/namespace.h"
#include "catalog/pg_enum.h"
#include "catalog/storage.h"
#include "commands/async.h"
#include "commands/tablecmds.h"
#include "commands/trigger.h"
#include "common/pg_prng.h"
#include "executor/spi.h"
#include "libpq/be-fsstubs.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "replication/logical.h"
#include "replication/logicallauncher.h"
#include "replication/logicalworker.h"
#include "replication/origin.h"
#include "replication/snapbuild.h"
#include "replication/syncrep.h"
#include "storage/aio_subsys.h"
#include "storage/condition_variable.h"
#include "storage/fd.h"
#include "storage/lmgr.h"
#include "storage/md.h"
#include "storage/predicate.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "storage/sinvaladt.h"
#include "storage/smgr.h"
#include "utils/builtins.h"
#include "utils/combocid.h"
#include "utils/guc.h"
#include "utils/inval.h"
#include "utils/memutils.h"
#include "utils/relmapper.h"
#include "utils/snapmgr.h"
#include "utils/timeout.h"
#include "utils/timestamp.h"
#include "utils/typcache.h"
#include "utils/wait_event.h"

/*
 *	User-tweakable parameters
 *	（中文）用户可调参数：默认/当前事务隔离级别、只读属性、可延迟属性以及同步提交设置。
 */
int			DefaultXactIsoLevel = XACT_READ_COMMITTED;
int			XactIsoLevel = XACT_READ_COMMITTED;

bool		DefaultXactReadOnly = false;
bool		XactReadOnly;

bool		DefaultXactDeferrable = false;
bool		XactDeferrable;

int			synchronous_commit = SYNCHRONOUS_COMMIT_ON;

/*
 * CheckXidAlive is a xid value pointing to a possibly ongoing (sub)
 * transaction.  Currently, it is used in logical decoding.  It's possible
 * that such transactions can get aborted while the decoding is ongoing in
 * which case we skip decoding that particular transaction.  To ensure that we
 * check whether the CheckXidAlive is aborted after fetching the tuple from
 * system tables.  We also ensure that during logical decoding we never
 * directly access the tableam or heap APIs because we are checking for the
 * concurrent aborts only in systable_* APIs.
 *	（中文）CheckXidAlive 指向一个可能仍在进行的（子）事务 XID，目前用于逻辑解码。
 *	（中文）解码期间该事务可能被中止，此时会跳过该事务；因此从系统表取出元组后需要检查它是否已中止。
 *	（中文）逻辑解码期间只通过 systable_* API 检查并发中止，不直接使用 tableam/heap API。
 */
TransactionId CheckXidAlive = InvalidTransactionId;
bool		bsysscan = false;

/*
 * When running as a parallel worker, we place only a single
 * TransactionStateData on the parallel worker's state stack, and the XID
 * reflected there will be that of the *innermost* currently-active
 * subtransaction in the backend that initiated parallelism.  However,
 * GetTopTransactionId() and TransactionIdIsCurrentTransactionId()
 * need to return the same answers in the parallel worker as they would have
 * in the user backend, so we need some additional bookkeeping.
 *
 * XactTopFullTransactionId stores the XID of our toplevel transaction, which
 * will be the same as TopTransactionStateData.fullTransactionId in an
 * ordinary backend; but in a parallel backend, which does not have the entire
 * transaction state, it will instead be copied from the backend that started
 * the parallel operation.
 *
 * nParallelCurrentXids will be 0 and ParallelCurrentXids NULL in an ordinary
 * backend, but in a parallel backend, nParallelCurrentXids will contain the
 * number of XIDs that need to be considered current, and ParallelCurrentXids
 * will contain the XIDs themselves.  This includes all XIDs that were current
 * or sub-committed in the parent at the time the parallel operation began.
 * The XIDs are stored sorted in numerical order (not logical order) to make
 * lookups as fast as possible.
 *	（中文）并行 worker 只保存一个 TransactionStateData，因此需要额外记录顶层事务信息：
 *	（中文）XactTopFullTransactionId 保存顶层事务的完整 XID；普通后端与
 *	TopTransactionStateData.fullTransactionId 相同，
 *	（中文）并行 worker 中则从启动并行操作的父后端复制。
 *	（中文）nParallelCurrentXids/ParallelCurrentXids 保存并行操作开始时父事务中所有当前或已提交子事务
 *	的 XID，
 *	（中文）按 XID 数值升序排列以便快速查找；普通后端中数量为 0、指针为 NULL。
 */
static FullTransactionId XactTopFullTransactionId = {InvalidTransactionId};
static int	nParallelCurrentXids = 0;
static TransactionId *ParallelCurrentXids;

/*
 * Miscellaneous flag bits to record events which occur on the top level
 * transaction. These flags are only persisted in MyXactFlags and are intended
 * so we remember to do certain things later on in the transaction. This is
 * globally accessible, so can be set from anywhere in the code that requires
 * recording flags.
 *	（中文）记录顶层事务期间发生的事件标志，供事务后续阶段判断需要执行哪些操作；
 *	（中文）该变量全局可访问，任何需要记录标志的代码都可以设置它。
 */
int			MyXactFlags;

/*
 *	transaction states - transaction state from server perspective
 *	（中文）服务端视角的事务底层状态：空闲、启动、进行中、提交中、中止中、准备中。
 */
typedef enum TransState
{
	TRANS_DEFAULT,				/* idle（空闲，不在事务中） */
	TRANS_START,				/* transaction starting（事务正在启动） */
	TRANS_INPROGRESS,			/* inside a valid transaction（处于有效事务中） */
	TRANS_COMMIT,				/* commit in progress（正在提交） */
	TRANS_ABORT,				/* abort in progress（正在中止） */
	TRANS_PREPARE,				/* prepare in progress（正在准备两阶段提交） */
} TransState;

/*
 *	transaction block states - transaction state of client queries
 *
 * Note: the subtransaction states are used only for non-topmost
 * transactions; the others appear only in the topmost transaction.
 *	（中文）客户端查询视角的事务块状态。子事务状态只用于非最顶层事务，其余状态只出现在最顶层事务中。
 */
typedef enum TBlockState
{
	/* not-in-transaction-block states（不在事务块中的状态） */
	TBLOCK_DEFAULT,				/* idle（空闲，不在事务块中） */
	TBLOCK_STARTED,				/* running single-query transaction（正在执行单条语句事务） */

	/* transaction block states（事务块状态） */
	TBLOCK_BEGIN,				/* starting transaction block（正在开始事务块） */
	TBLOCK_INPROGRESS,			/* live transaction（活动事务） */
	TBLOCK_IMPLICIT_INPROGRESS, /* live transaction after implicit BEGIN（隐式 BEGIN 后的活动事务） */
	TBLOCK_PARALLEL_INPROGRESS, /* live transaction inside parallel worker（并行 worker 内的活动事务） */
	TBLOCK_END,					/* COMMIT received（收到 COMMIT） */
	TBLOCK_ABORT,				/* failed xact, awaiting ROLLBACK（事务失败，等待 ROLLBACK） */
	TBLOCK_ABORT_END,			/* failed xact, ROLLBACK received（事务失败，已收到 ROLLBACK） */
	TBLOCK_ABORT_PENDING,		/* live xact, ROLLBACK received（活动事务收到 ROLLBACK） */
	TBLOCK_PREPARE,				/* live xact, PREPARE received（活动事务收到 PREPARE） */

	/* subtransaction states（子事务状态） */
	TBLOCK_SUBBEGIN,			/* starting a subtransaction（正在开始子事务） */
	TBLOCK_SUBINPROGRESS,		/* live subtransaction（活动子事务） */
	TBLOCK_SUBRELEASE,			/* RELEASE received（收到 RELEASE） */
	TBLOCK_SUBCOMMIT,			/* COMMIT received while TBLOCK_SUBINPROGRESS（子事务进行中收到 COMMIT） */
	TBLOCK_SUBABORT,			/* failed subxact, awaiting ROLLBACK（子事务失败，等待 ROLLBACK） */
	TBLOCK_SUBABORT_END,		/* failed subxact, ROLLBACK received（子事务失败，已收到 ROLLBACK） */
	TBLOCK_SUBABORT_PENDING,	/* live subxact, ROLLBACK received（活动子事务收到 ROLLBACK） */
	TBLOCK_SUBRESTART,			/* live subxact, ROLLBACK TO received（活动子事务收到 ROLLBACK TO） */
	TBLOCK_SUBABORT_RESTART,	/* failed subxact, ROLLBACK TO received（失败子事务收到 ROLLBACK TO） */
} TBlockState;

/*
 *	transaction state structure
 *
 * Note: parallelModeLevel counts the number of unmatched EnterParallelMode
 * calls done at this transaction level.  parallelChildXact is true if any
 * upper transaction level has nonzero parallelModeLevel.
 *	（中文）事务状态结构：每个顶层事务和每个子事务都对应一个 TransactionStateData。
 *	（中文）parallelModeLevel 表示当前事务层级上未配对的 EnterParallelMode 调用次数；
 *	（中文）parallelChildXact 表示任一上层事务是否处于并行模式。
 */
typedef struct TransactionStateData
{
	FullTransactionId fullTransactionId;	/* my FullTransactionId（本事务的完整事务 ID，含 epoch） */
	SubTransactionId subTransactionId;	/* my subxact ID（本事务的子事务 ID） */
	char	   *name;			/* savepoint name, if any（保存点名称，如果有） */
	int			savepointLevel; /* savepoint level（保存点层级） */
	TransState	state;			/* low-level state（底层事务状态，TransState） */
	TBlockState blockState;		/* high-level state（高层事务块状态，TBlockState） */
	int			nestingLevel;	/* transaction nesting depth（事务嵌套深度） */
	int			gucNestLevel;	/* GUC context nesting depth（GUC 上下文嵌套深度） */
	MemoryContext curTransactionContext;	/* my xact-lifetime context（本事务生命周期的内存上下文） */
	ResourceOwner curTransactionOwner;	/* my query resources（本查询的资源所有者） */
	MemoryContext priorContext; /* CurrentMemoryContext before xact started（事务开始前的 CurrentMemoryContext） */
	TransactionId *childXids;	/* subcommitted child XIDs, in XID order（已提交子事务的 XID 数组，按 XID 排序） */
	int			nChildXids;		/* # of subcommitted child XIDs（已提交子事务 XID 的数量） */
	int			maxChildXids;	/* allocated size of childXids[]（childXids[] 的已分配大小） */
	Oid			prevUser;		/* previous CurrentUserId setting（之前的 CurrentUserId 设置） */
	int			prevSecContext; /* previous SecurityRestrictionContext（之前的 SecurityRestrictionContext） */
	bool		prevXactReadOnly;	/* entry-time xact r/o state（进入事务时的只读状态） */
	bool		startedInRecovery;	/* did we start in recovery?（是否在恢复期间启动） */
	bool		didLogXid;		/* has xid been included in WAL record?（XID 是否已写入 WAL 记录） */
	int			parallelModeLevel;	/* Enter/ExitParallelMode counter（EnterParallelMode/ExitParallelMode 的配对计数） */
	bool		parallelChildXact;	/* is any parent transaction parallel?（任一父事务是否处于并行模式） */
	bool		chain;			/* start a new block after this one（本事务结束后是否开始新事务块，AND CHAIN） */
	bool		topXidLogged;	/* for a subxact: is top-level XID logged?（对子事务而言，顶层 XID 是否已记录） */
	struct TransactionStateData *parent;	/* back link to parent（指向父事务状态的回链） */
} TransactionStateData;

typedef TransactionStateData *TransactionState;	/* 指向事务状态结构的指针类型 */

/*
 * Serialized representation used to transmit transaction state to parallel
 * workers through shared memory.
 *	（中文）用于通过共享内存把事务状态传递给并行 worker 的序列化结构。
 */
typedef struct SerializedTransactionState
{
	int			xactIsoLevel;	/* 事务隔离级别 */
	bool		xactDeferrable;	/* 事务是否可延迟 */
	FullTransactionId topFullTransactionId;	/* 顶层事务的完整事务 ID */
	FullTransactionId currentFullTransactionId;	/* 当前事务的完整事务 ID */
	CommandId	currentCommandId;	/* 当前命令 ID */
	int			nParallelCurrentXids;	/* 当前 XID 列表的长度 */
	TransactionId parallelCurrentXids[FLEXIBLE_ARRAY_MEMBER];	/* 当前有效的 XID 列表（柔性数组） */
} SerializedTransactionState;

/* The size of SerializedTransactionState, not including the final array（不含末尾柔性数组的结构大小）. */
#define SerializedTransactionStateHeaderSize \
	offsetof(SerializedTransactionState, parallelCurrentXids)

/*
 * CurrentTransactionState always points to the current transaction state
 * block.  It will point to TopTransactionStateData when not in a
 * transaction at all, or when in a top-level transaction.
 *	（中文）CurrentTransactionState 始终指向当前事务状态块；不在事务中或处于顶层事务时，它指向
 *	TopTransactionStateData。
 */
static TransactionStateData TopTransactionStateData = {
	.state = TRANS_DEFAULT,
	.blockState = TBLOCK_DEFAULT,
	.topXidLogged = false,
};

/*
 * unreportedXids holds XIDs of all subtransactions that have not yet been
 * reported in an XLOG_XACT_ASSIGNMENT record.
 *	（中文）unreportedXids 保存尚未在 XLOG_XACT_ASSIGNMENT 记录中报告的子事务 XID。
 */
static int	nUnreportedXids;
static TransactionId unreportedXids[PGPROC_MAX_CACHED_SUBXIDS];

static TransactionState CurrentTransactionState = &TopTransactionStateData;

/*
 * The subtransaction ID and command ID assignment counters are global
 * to a whole transaction, so we do not keep them in the state stack.
 *	（中文）子事务 ID 和命令 ID 分配计数器对整个事务全局有效，因此不放入事务状态栈。
 */
static SubTransactionId currentSubTransactionId;
static CommandId currentCommandId;
static bool currentCommandIdUsed;

/*
 * xactStartTimestamp is the value of transaction_timestamp().
 * stmtStartTimestamp is the value of statement_timestamp().
 * xactStopTimestamp is the time at which we log a commit / abort WAL record,
 * or if that was skipped, the time of the first subsequent
 * GetCurrentTransactionStopTimestamp() call.
 *
 * These do not change as we enter and exit subtransactions, so we don't
 * keep them inside the TransactionState stack.
 *	（中文）xactStartTimestamp 是 transaction_timestamp() 的值；stmtStartTimestamp 是
 *	statement_timestamp() 的值；
 *	（中文）xactStopTimestamp 是记录提交/中止 WAL 记录的时间，若跳过了 WAL 记录，则为随后首次调用
 *	（中文）GetCurrentTransactionStopTimestamp() 的时间。这些值在进出子事务时不变，因此不放在状态栈中。
 */
static TimestampTz xactStartTimestamp;
static TimestampTz stmtStartTimestamp;
static TimestampTz xactStopTimestamp;

/*
 * GID to be used for preparing the current transaction.  This is also
 * global to a whole transaction, so we don't keep it in the state stack.
 *	（中文）当前事务用于 PREPARE TRANSACTION 的 GID；对整个事务全局有效，不放入状态栈。
 */
static char *prepareGID;

/*
 * Some commands want to force synchronous commit.
 *	（中文）某些命令需要强制同步提交，此标志用于记录该需求。
 */
static bool forceSyncCommit = false;

/* Flag for logging statements in a transaction（是否对本事务中的语句进行采样记录）. */
bool		xact_is_sampled = false;

/*
 * Private context for transaction-abort work --- we reserve space for this
 * at startup to ensure that AbortTransaction and AbortSubTransaction can work
 * when we've run out of memory.
 *	（中文）事务中止专用私有上下文：启动时预留，保证即使内存耗尽，AbortTransaction 和
 *	（中文）AbortSubTransaction 仍能完成工作。
 */
static MemoryContext TransactionAbortContext = NULL;

/*
 * List of add-on start- and end-of-xact callbacks
 *	（中文）事务开始/结束回调链表。
 */
typedef struct XactCallbackItem
{
	struct XactCallbackItem *next;
	XactCallback callback;
	void	   *arg;
} XactCallbackItem;

static XactCallbackItem *Xact_callbacks = NULL;

/*
 * List of add-on start- and end-of-subxact callbacks
 *	（中文）子事务开始/结束回调链表。
 */
typedef struct SubXactCallbackItem
{
	struct SubXactCallbackItem *next;
	SubXactCallback callback;
	void	   *arg;
} SubXactCallbackItem;

static SubXactCallbackItem *SubXact_callbacks = NULL;


/* local function prototypes（本地静态函数原型声明） */
static void AssignTransactionId(TransactionState s);
static void AbortTransaction(void);
static void AtAbort_Memory(void);
static void AtCleanup_Memory(void);
static void AtAbort_ResourceOwner(void);
static void AtCCI_LocalCache(void);
static void AtCommit_Memory(void);
static void AtStart_Cache(void);
static void AtStart_Memory(void);
static void AtStart_ResourceOwner(void);
static void CallXactCallbacks(XactEvent event);
static void CallSubXactCallbacks(SubXactEvent event,
								 SubTransactionId mySubid,
								 SubTransactionId parentSubid);
static void CleanupTransaction(void);
static void CheckTransactionBlock(bool isTopLevel, bool throwError,
								  const char *stmtType);
static void CommitTransaction(void);
static TransactionId RecordTransactionAbort(bool isSubXact);
static void StartTransaction(void);

static bool CommitTransactionCommandInternal(void);
static bool AbortCurrentTransactionInternal(void);

static void StartSubTransaction(void);
static void CommitSubTransaction(void);
static void AbortSubTransaction(void);
static void CleanupSubTransaction(void);
static void PushTransaction(void);
static void PopTransaction(void);

static void AtSubAbort_Memory(void);
static void AtSubCleanup_Memory(void);
static void AtSubAbort_ResourceOwner(void);
static void AtSubCommit_Memory(void);
static void AtSubStart_Memory(void);
static void AtSubStart_ResourceOwner(void);

static void ShowTransactionState(const char *str);
static void ShowTransactionStateRec(const char *str, TransactionState s);
static const char *BlockStateAsString(TBlockState blockState);
static const char *TransStateAsString(TransState state);


/* ----------------------------------------------------------------
 *	transaction state accessors
 *	（中文）事务状态访问器：查询/分配事务 ID、子事务 ID、命令 ID、时间戳，并处理并行模式等状态。
 * ----------------------------------------------------------------
 */

/*
 *	IsTransactionState
 *
 *	This returns true if we are inside a valid transaction; that is,
 *	it is safe to initiate database access, take heavyweight locks, etc.
 */
/*
 * 中文注释：
 * 判断当前是否处于有效事务中（TRANS_INPROGRESS）。只有此时才可以安全地访问数据库、获取重量级锁等；
 * 启动、提交、中止等过渡状态均视为无效。
 */
bool
IsTransactionState(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * TRANS_DEFAULT and TRANS_ABORT are obviously unsafe states.  However, we
	 * also reject the startup/shutdown states TRANS_START, TRANS_COMMIT,
	 * TRANS_PREPARE since it might be too soon or too late within those
	 * transition states to do anything interesting.  Hence, the only "valid"
	 * state is TRANS_INPROGRESS.
	 */
	return (s->state == TRANS_INPROGRESS);
}

/*
 *	IsAbortedTransactionBlockState
 *
 *	This returns true if we are within an aborted transaction block.
 */
/*
 * 中文注释：
 * 判断当前是否处于已中止的事务块中（TBLOCK_ABORT 或 TBLOCK_SUBABORT）。
 */
bool
IsAbortedTransactionBlockState(void)
{
	TransactionState s = CurrentTransactionState;

	if (s->blockState == TBLOCK_ABORT ||
		s->blockState == TBLOCK_SUBABORT)
		return true;

	return false;
}


/*
 *	GetTopTransactionId
 *
 * This will return the XID of the main transaction, assigning one if
 * it's not yet set.  Be careful to call this only inside a valid xact.
 */
/*
 * 中文注释：
 * 返回顶层事务的 XID；若尚未分配则为其分配一个。只能在有效事务内调用。
 */
TransactionId
GetTopTransactionId(void)
{
	if (!FullTransactionIdIsValid(XactTopFullTransactionId))
		AssignTransactionId(&TopTransactionStateData);
	return XidFromFullTransactionId(XactTopFullTransactionId);
}

/*
 *	GetTopTransactionIdIfAny
 *
 * This will return the XID of the main transaction, if one is assigned.
 * It will return InvalidTransactionId if we are not currently inside a
 * transaction, or inside a transaction that hasn't yet been assigned an XID.
 */
/*
 * 中文注释：
 * 返回顶层事务已分配的 XID；不在事务中或尚未分配 XID 时返回 InvalidTransactionId。
 */
TransactionId
GetTopTransactionIdIfAny(void)
{
	return XidFromFullTransactionId(XactTopFullTransactionId);
}

/*
 *	GetCurrentTransactionId
 *
 * This will return the XID of the current transaction (main or sub
 * transaction), assigning one if it's not yet set.  Be careful to call this
 * only inside a valid xact.
 */
/*
 * 中文注释：
 * 返回当前事务（顶层事务或子事务）的 XID；若尚未分配则分配。
 */
TransactionId
GetCurrentTransactionId(void)
{
	TransactionState s = CurrentTransactionState;

	if (!FullTransactionIdIsValid(s->fullTransactionId))
		AssignTransactionId(s);
	return XidFromFullTransactionId(s->fullTransactionId);
}

/*
 *	GetCurrentTransactionIdIfAny
 *
 * This will return the XID of the current sub xact, if one is assigned.
 * It will return InvalidTransactionId if we are not currently inside a
 * transaction, or inside a transaction that hasn't been assigned an XID yet.
 */
/*
 * 中文注释：
 * 返回当前事务已分配的 XID；不在事务中或尚未分配时返回 InvalidTransactionId。
 */
TransactionId
GetCurrentTransactionIdIfAny(void)
{
	return XidFromFullTransactionId(CurrentTransactionState->fullTransactionId);
}

/*
 *	GetTopFullTransactionId
 *
 * This will return the FullTransactionId of the main transaction, assigning
 * one if it's not yet set.  Be careful to call this only inside a valid xact.
 */
/*
 * 中文注释：
 * 返回顶层事务的 FullTransactionId（包含 epoch）；若尚未分配则分配。
 */
FullTransactionId
GetTopFullTransactionId(void)
{
	if (!FullTransactionIdIsValid(XactTopFullTransactionId))
		AssignTransactionId(&TopTransactionStateData);
	return XactTopFullTransactionId;
}

/*
 *	GetTopFullTransactionIdIfAny
 *
 * This will return the FullTransactionId of the main transaction, if one is
 * assigned.  It will return InvalidFullTransactionId if we are not currently
 * inside a transaction, or inside a transaction that hasn't yet been assigned
 * one.
 */
/*
 * 中文注释：
 * 返回顶层事务已分配的 FullTransactionId；否则返回 InvalidFullTransactionId。
 */
FullTransactionId
GetTopFullTransactionIdIfAny(void)
{
	return XactTopFullTransactionId;
}

/*
 *	GetCurrentFullTransactionId
 *
 * This will return the FullTransactionId of the current transaction (main or
 * sub transaction), assigning one if it's not yet set.  Be careful to call
 * this only inside a valid xact.
 */
/*
 * 中文注释：
 * 返回当前事务（顶层或子事务）的 FullTransactionId；若尚未分配则分配。
 */
FullTransactionId
GetCurrentFullTransactionId(void)
{
	TransactionState s = CurrentTransactionState;

	if (!FullTransactionIdIsValid(s->fullTransactionId))
		AssignTransactionId(s);
	return s->fullTransactionId;
}

/*
 *	GetCurrentFullTransactionIdIfAny
 *
 * This will return the FullTransactionId of the current sub xact, if one is
 * assigned.  It will return InvalidFullTransactionId if we are not currently
 * inside a transaction, or inside a transaction that hasn't been assigned one
 * yet.
 */
/*
 * 中文注释：
 * 返回当前事务已分配的 FullTransactionId；否则返回 InvalidFullTransactionId。
 */
FullTransactionId
GetCurrentFullTransactionIdIfAny(void)
{
	return CurrentTransactionState->fullTransactionId;
}

/*
 *	MarkCurrentTransactionIdLoggedIfAny
 *
 * Remember that the current xid - if it is assigned - now has been wal logged.
 */
/*
 * 中文注释：
 * 如果当前 XID 已分配，则标记它已经写入 WAL 记录，避免重复记录。
 */
void
MarkCurrentTransactionIdLoggedIfAny(void)
{
	if (FullTransactionIdIsValid(CurrentTransactionState->fullTransactionId))
		CurrentTransactionState->didLogXid = true;
}

/*
 * IsSubxactTopXidLogPending
 *
 * This is used to decide whether we need to WAL log the top-level XID for
 * operation in a subtransaction.  We require that for logical decoding, see
 * LogicalDecodingProcessRecord.
 *
 * This returns true if effective_wal_level is logical and we are inside
 * a valid subtransaction, for which the assignment was not yet written to
 * any WAL record.
 */
/*
 * 中文注释：
 * 判断当前子事务对应的顶层 XID 是否还需要写入 WAL。逻辑解码要求子事务操作也记录顶层 XID；当
 * wal_level=logical 且处于有效子事务、其 XID 尚未写入任何 WAL 记录时返回 true。
 */
bool
IsSubxactTopXidLogPending(void)
{
	/* check whether it is already logged */
	if (CurrentTransactionState->topXidLogged)
		return false;

	/* effective_wal_level has to be logical */
	if (!XLogLogicalInfoActive())
		return false;

	/* we need to be in a transaction state */
	if (!IsTransactionState())
		return false;

	/* it has to be a subtransaction */
	if (!IsSubTransaction())
		return false;

	/* the subtransaction has to have a XID assigned */
	if (!TransactionIdIsValid(GetCurrentTransactionIdIfAny()))
		return false;

	return true;
}

/*
 * MarkSubxactTopXidLogged
 *
 * Remember that the top transaction id for the current subtransaction is WAL
 * logged now.
 */
/*
 * 中文注释：
 * 标记当前子事务的顶层 XID 已经写入 WAL。
 */
void
MarkSubxactTopXidLogged(void)
{
	Assert(IsSubxactTopXidLogPending());

	CurrentTransactionState->topXidLogged = true;
}

/*
 *	GetStableLatestTransactionId
 *
 * Get the transaction's XID if it has one, else read the next-to-be-assigned
 * XID.  Once we have a value, return that same value for the remainder of the
 * current transaction.  This is meant to provide the reference point for the
 * age(xid) function, but might be useful for other maintenance tasks as well.
 */
/*
 * 中文注释：
 * 获取事务 XID；若未分配则读取下一个将要分配的 XID，并在本事务剩余时间内保持该值稳定。主要用于
 * age(xid) 等维护操作。
 */
TransactionId
GetStableLatestTransactionId(void)
{
	static LocalTransactionId lxid = InvalidLocalTransactionId;
	static TransactionId stablexid = InvalidTransactionId;

	if (lxid != MyProc->vxid.lxid)
	{
		lxid = MyProc->vxid.lxid;
		stablexid = GetTopTransactionIdIfAny();
		if (!TransactionIdIsValid(stablexid))
			stablexid = ReadNextTransactionId();
	}

	Assert(TransactionIdIsValid(stablexid));

	return stablexid;
}

/*
 * AssignTransactionId
 *
 * Assigns a new permanent FullTransactionId to the given TransactionState.
 * We do not assign XIDs to transactions until/unless this is called.
 * Also, any parent TransactionStates that don't yet have XIDs are assigned
 * one; this maintains the invariant that a child transaction has an XID
 * following its parent's.
 */
/*
 * 中文注释：
 * 为指定事务状态分配新的永久 FullTransactionId。PostgreSQL 采用惰性分配：直到需要时才给事务分配 XID；同时会为尚未分配 XID 的父事务也分配 XID，以保证子事务的 XID 总是晚于父事务。
 */
static void
AssignTransactionId(TransactionState s)
{
	bool		isSubXact = (s->parent != NULL);
	ResourceOwner currentOwner;
	bool		log_unknown_top = false;

	/* Assert that caller didn't screw up */
	Assert(!FullTransactionIdIsValid(s->fullTransactionId));
	Assert(s->state == TRANS_INPROGRESS);

	/*
	 * Workers synchronize transaction state at the beginning of each parallel
	 * operation, so we can't account for new XIDs at this point.
	 */
	if (IsInParallelMode() || IsParallelWorker())
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
				 errmsg("cannot assign transaction IDs during a parallel operation")));

	/*
	 * Ensure parent(s) have XIDs, so that a child always has an XID later
	 * than its parent.  Mustn't recurse here, or we might get a stack
	 * overflow if we're at the bottom of a huge stack of subtransactions none
	 * of which have XIDs yet.
	 */
	if (isSubXact && !FullTransactionIdIsValid(s->parent->fullTransactionId))
	{
		TransactionState p = s->parent;
		TransactionState *parents;
		size_t		parentOffset = 0;

		parents = palloc_array(TransactionState, s->nestingLevel);
		while (p != NULL && !FullTransactionIdIsValid(p->fullTransactionId))
		{
			parents[parentOffset++] = p;
			p = p->parent;
		}

		/*
		 * This is technically a recursive call, but the recursion will never
		 * be more than one layer deep.
		 */
		while (parentOffset != 0)
			AssignTransactionId(parents[--parentOffset]);

		pfree(parents);
	}

	/*
	 * When effective_wal_level is logical, guarantee that a subtransaction's
	 * xid can only be seen in the WAL stream if its toplevel xid has been
	 * logged before. If necessary we log an xact_assignment record with fewer
	 * than PGPROC_MAX_CACHED_SUBXIDS. Note that it is fine if didLogXid isn't
	 * set for a transaction even though it appears in a WAL record, we just
	 * might superfluously log something. That can happen when an xid is
	 * included somewhere inside a wal record, but not in XLogRecord->xl_xid,
	 * like in xl_standby_locks.
	 */
	if (isSubXact && XLogLogicalInfoActive() &&
		!TopTransactionStateData.didLogXid)
		log_unknown_top = true;

	/*
	 * Generate a new FullTransactionId and record its xid in PGPROC and
	 * pg_subtrans.
	 *
	 * NB: we must make the subtrans entry BEFORE the Xid appears anywhere in
	 * shared storage other than PGPROC; because if there's no room for it in
	 * PGPROC, the subtrans entry is needed to ensure that other backends see
	 * the Xid as "running".  See GetNewTransactionId.
	 */
	s->fullTransactionId = GetNewTransactionId(isSubXact);
	if (!isSubXact)
		XactTopFullTransactionId = s->fullTransactionId;

	if (isSubXact)
		SubTransSetParent(XidFromFullTransactionId(s->fullTransactionId),
						  XidFromFullTransactionId(s->parent->fullTransactionId));

	/*
	 * If it's a top-level transaction, the predicate locking system needs to
	 * be told about it too.
	 */
	if (!isSubXact)
		RegisterPredicateLockingXid(XidFromFullTransactionId(s->fullTransactionId));

	/*
	 * Acquire lock on the transaction XID.  (We assume this cannot block.) We
	 * have to ensure that the lock is assigned to the transaction's own
	 * ResourceOwner.
	 */
	currentOwner = CurrentResourceOwner;
	CurrentResourceOwner = s->curTransactionOwner;

	XactLockTableInsert(XidFromFullTransactionId(s->fullTransactionId));

	CurrentResourceOwner = currentOwner;

	/*
	 * Every PGPROC_MAX_CACHED_SUBXIDS assigned transaction ids within each
	 * top-level transaction we issue a WAL record for the assignment. We
	 * include the top-level xid and all the subxids that have not yet been
	 * reported using XLOG_XACT_ASSIGNMENT records.
	 *
	 * This is required to limit the amount of shared memory required in a hot
	 * standby server to keep track of in-progress XIDs. See notes for
	 * RecordKnownAssignedTransactionIds().
	 *
	 * We don't keep track of the immediate parent of each subxid, only the
	 * top-level transaction that each subxact belongs to. This is correct in
	 * recovery only because aborted subtransactions are separately WAL
	 * logged.
	 *
	 * This is correct even for the case where several levels above us didn't
	 * have an xid assigned as we recursed up to them beforehand.
	 */
	if (isSubXact && XLogStandbyInfoActive())
	{
		unreportedXids[nUnreportedXids] = XidFromFullTransactionId(s->fullTransactionId);
		nUnreportedXids++;

		/*
		 * ensure this test matches similar one in
		 * RecoverPreparedTransactions()
		 */
		if (nUnreportedXids >= PGPROC_MAX_CACHED_SUBXIDS ||
			log_unknown_top)
		{
			xl_xact_assignment xlrec;

			/*
			 * xtop is always set by now because we recurse up transaction
			 * stack to the highest unassigned xid and then come back down
			 */
			xlrec.xtop = GetTopTransactionId();
			Assert(TransactionIdIsValid(xlrec.xtop));
			xlrec.nsubxacts = nUnreportedXids;

			XLogBeginInsert();
			XLogRegisterData(&xlrec, MinSizeOfXactAssignment);
			XLogRegisterData(unreportedXids,
							 nUnreportedXids * sizeof(TransactionId));

			(void) XLogInsert(RM_XACT_ID, XLOG_XACT_ASSIGNMENT);

			nUnreportedXids = 0;
			/* mark top, not current xact as having been logged */
			TopTransactionStateData.didLogXid = true;
		}
	}
}

/*
 *	GetCurrentSubTransactionId
 */
/*
 * 中文注释：
 * 返回当前子事务 ID（来自全局子事务 ID 计数器）。
 */
SubTransactionId
GetCurrentSubTransactionId(void)
{
	TransactionState s = CurrentTransactionState;

	return s->subTransactionId;
}

/*
 *	SubTransactionIsActive
 *
 * Test if the specified subxact ID is still active.  Note caller is
 * responsible for checking whether this ID is relevant to the current xact.
 */
/*
 * 中文注释：
 * 判断给定子事务 ID 是否仍处于活动状态；调用者需自行确认该 ID 属于当前事务。
 */
bool
SubTransactionIsActive(SubTransactionId subxid)
{
	TransactionState s;

	for (s = CurrentTransactionState; s != NULL; s = s->parent)
	{
		if (s->state == TRANS_ABORT)
			continue;
		if (s->subTransactionId == subxid)
			return true;
	}
	return false;
}


/*
 *	GetCurrentCommandId
 *
 * "used" must be true if the caller intends to use the command ID to mark
 * inserted/updated/deleted tuples.  false means the ID is being fetched
 * for read-only purposes (ie, as a snapshot validity cutoff).  See
 * CommandCounterIncrement() for discussion.
 */
/*
 * 中文注释：
 * 返回当前命令 ID。used=true 表示调用者要用该 ID 标记插入/更新/删除的元组；false 表示仅用于只读目的
 * （如作为快照可见性截止点）。详见 CommandCounterIncrement() 的说明。
 */
CommandId
GetCurrentCommandId(bool used)
{
	/* this is global to a transaction, not subtransaction-local */
	if (used)
	{
		/*
		 * Forbid setting currentCommandIdUsed in a parallel worker, because
		 * we have no provision for communicating this back to the leader.  We
		 * could relax this restriction when currentCommandIdUsed was already
		 * true at the start of the parallel operation.
		 */
		if (IsParallelWorker())
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
					 errmsg("cannot modify data in a parallel worker")));

		currentCommandIdUsed = true;
	}
	return currentCommandId;
}

/*
 *	SetParallelStartTimestamps
 *
 * In a parallel worker, we should inherit the parent transaction's
 * timestamps rather than setting our own.  The parallel worker
 * infrastructure must call this to provide those values before
 * calling StartTransaction() or SetCurrentStatementStartTimestamp().
 */
/*
 * 中文注释：
 * 供并行 worker 使用：继承父事务的事务时间戳和语句时间戳，必须在 StartTransaction() 或
 * SetCurrentStatementStartTimestamp() 之前调用。
 */
void
SetParallelStartTimestamps(TimestampTz xact_ts, TimestampTz stmt_ts)
{
	Assert(IsParallelWorker());
	xactStartTimestamp = xact_ts;
	stmtStartTimestamp = stmt_ts;
}

/*
 *	GetCurrentTransactionStartTimestamp
 */
/*
 * 中文注释：
 * 返回 transaction_timestamp() 的值（事务开始时间）。
 */
TimestampTz
GetCurrentTransactionStartTimestamp(void)
{
	return xactStartTimestamp;
}

/*
 *	GetCurrentStatementStartTimestamp
 */
/*
 * 中文注释：
 * 返回 statement_timestamp() 的值（当前语句开始时间）。
 */
TimestampTz
GetCurrentStatementStartTimestamp(void)
{
	return stmtStartTimestamp;
}

/*
 *	GetCurrentTransactionStopTimestamp
 *
 * If the transaction stop time hasn't already been set, which can happen if
 * we decided we don't need to log an XLOG record, set xactStopTimestamp.
 */
/*
 * 中文注释：
 * 返回事务停止时间。如果尚未设置（例如无需写 WAL 记录），则在此处将 xactStopTimestamp 设为当前时间。
 */
TimestampTz
GetCurrentTransactionStopTimestamp(void)
{
	TransactionState s PG_USED_FOR_ASSERTS_ONLY = CurrentTransactionState;

	/* should only be called after commit / abort processing */
	Assert(s->state == TRANS_DEFAULT ||
		   s->state == TRANS_COMMIT ||
		   s->state == TRANS_ABORT ||
		   s->state == TRANS_PREPARE);

	if (xactStopTimestamp == 0)
		xactStopTimestamp = GetCurrentTimestamp();

	return xactStopTimestamp;
}

/*
 *	SetCurrentStatementStartTimestamp
 *
 * In a parallel worker, this should already have been provided by a call
 * to SetParallelStartTimestamps().
 */
/*
 * 中文注释：
 * 设置当前语句开始时间戳。并行 worker 中该值应由 SetParallelStartTimestamps() 提前提供。
 */
void
SetCurrentStatementStartTimestamp(void)
{
	if (!IsParallelWorker())
		stmtStartTimestamp = GetCurrentTimestamp();
	else
		Assert(stmtStartTimestamp != 0);
}

/*
 *	GetCurrentTransactionNestLevel
 *
 * Note: this will return zero when not inside any transaction, one when
 * inside a top-level transaction, etc.
 */
/*
 * 中文注释：
 * 返回当前事务嵌套层级：不在事务中为 0，顶层事务为 1，每进入一层子事务加 1。
 */
int
GetCurrentTransactionNestLevel(void)
{
	TransactionState s = CurrentTransactionState;

	return s->nestingLevel;
}


/*
 *	TransactionIdIsCurrentTransactionId
 */
/*
 * 中文注释：
 * 判断给定 XID 是否属于当前事务（包括当前事务已提交的子事务）。普通后端遍历状态栈中的 XID；并行
 * worker 则查询启动并行操作时复制的 ParallelCurrentXids 列表。
 */
bool
TransactionIdIsCurrentTransactionId(TransactionId xid)
{
	TransactionState s;

	/*
	 * We always say that BootstrapTransactionId is "not my transaction ID"
	 * even when it is (ie, during bootstrap).  Along with the fact that
	 * transam.c always treats BootstrapTransactionId as already committed,
	 * this causes the heapam_visibility.c routines to see all tuples as
	 * committed, which is what we need during bootstrap.  (Bootstrap mode
	 * only inserts tuples, it never updates or deletes them, so all tuples
	 * can be presumed good immediately.)
	 *
	 * Likewise, InvalidTransactionId and FrozenTransactionId are certainly
	 * not my transaction ID, so we can just return "false" immediately for
	 * any non-normal XID.
	 */
	if (!TransactionIdIsNormal(xid))
		return false;

	if (TransactionIdEquals(xid, GetTopTransactionIdIfAny()))
		return true;

	/*
	 * In parallel workers, the XIDs we must consider as current are stored in
	 * ParallelCurrentXids rather than the transaction-state stack.  Note that
	 * the XIDs in this array are sorted numerically rather than according to
	 * transactionIdPrecedes order.
	 */
	if (nParallelCurrentXids > 0)
	{
		int			low,
					high;

		low = 0;
		high = nParallelCurrentXids - 1;
		while (low <= high)
		{
			int			middle;
			TransactionId probe;

			middle = low + (high - low) / 2;
			probe = ParallelCurrentXids[middle];
			if (probe == xid)
				return true;
			else if (probe < xid)
				low = middle + 1;
			else
				high = middle - 1;
		}
		return false;
	}

	/*
	 * We will return true for the Xid of the current subtransaction, any of
	 * its subcommitted children, any of its parents, or any of their
	 * previously subcommitted children.  However, a transaction being aborted
	 * is no longer "current", even though it may still have an entry on the
	 * state stack.
	 */
	for (s = CurrentTransactionState; s != NULL; s = s->parent)
	{
		int			low,
					high;

		if (s->state == TRANS_ABORT)
			continue;
		if (!FullTransactionIdIsValid(s->fullTransactionId))
			continue;			/* it can't have any child XIDs either */
		if (TransactionIdEquals(xid, XidFromFullTransactionId(s->fullTransactionId)))
			return true;
		/* As the childXids array is ordered, we can use binary search */
		low = 0;
		high = s->nChildXids - 1;
		while (low <= high)
		{
			int			middle;
			TransactionId probe;

			middle = low + (high - low) / 2;
			probe = s->childXids[middle];
			if (TransactionIdEquals(probe, xid))
				return true;
			else if (TransactionIdPrecedes(probe, xid))
				low = middle + 1;
			else
				high = middle - 1;
		}
	}

	return false;
}

/*
 *	TransactionStartedDuringRecovery
 *
 * Returns true if the current transaction started while recovery was still
 * in progress. Recovery might have ended since so RecoveryInProgress() might
 * return false already.
 */
/*
 * 中文注释：
 * 判断当前事务是否在数据库恢复期间启动。恢复可能已经结束，因此 RecoveryInProgress() 现在可能返回
 * false。
 */
bool
TransactionStartedDuringRecovery(void)
{
	return CurrentTransactionState->startedInRecovery;
}

/*
 *	GetTopReadOnlyTransactionNestLevel
 *
 * Note: this will return zero when not inside any transaction or when neither
 * a top-level transaction nor subtransactions are read-only, one when the
 * top-level transaction is read-only, two when one level of subtransaction is
 * read-only, etc.
 *
 * Note: subtransactions of the topmost read-only transaction are also
 * read-only, because they inherit read-only mode from the transaction, and
 * thus can't change to read-write mode (see check_transaction_read_only).
 */
/*
 * 中文注释：
 * 返回只读事务的嵌套层级：0 表示不在只读事务中，1 表示顶层事务只读，2 表示一级子事务只读……顶层只读
 * 事务的所有子事务也必然是只读的。
 */
int
GetTopReadOnlyTransactionNestLevel(void)
{
	TransactionState s = CurrentTransactionState;

	if (!XactReadOnly)
		return 0;
	while (s->nestingLevel > 1)
	{
		if (!s->prevXactReadOnly)
			return s->nestingLevel;
		s = s->parent;
	}
	return s->nestingLevel;
}

/*
 *	EnterParallelMode
 */
/*
 * 中文注释：
 * 进入并行模式：递增当前事务层级的 parallelModeLevel 计数；并行模式下禁止执行会改变后端本地状态的操
 * 作。
 */
void
EnterParallelMode(void)
{
	TransactionState s = CurrentTransactionState;

	Assert(s->parallelModeLevel >= 0);

	++s->parallelModeLevel;
}

/*
 *	ExitParallelMode
 */
/*
 * 中文注释：
 * 退出并行模式：递减 parallelModeLevel 计数。
 */
void
ExitParallelMode(void)
{
	TransactionState s = CurrentTransactionState;

	Assert(s->parallelModeLevel > 0);
	Assert(s->parallelModeLevel > 1 || s->parallelChildXact ||
		   !ParallelContextActive());

	--s->parallelModeLevel;
}

/*
 *	IsInParallelMode
 *
 * Are we in a parallel operation, as either the leader or a worker?  Check
 * this to prohibit operations that change backend-local state expected to
 * match across all workers.  Mere caches usually don't require such a
 * restriction.  State modified in a strict push/pop fashion, such as the
 * active snapshot stack, is often fine.
 *
 * We say we are in parallel mode if we are in a subxact of a transaction
 * that's initiated a parallel operation; for most purposes that context
 * has all the same restrictions.
 */
/*
 * 中文注释：
 * 判断当前是否处于并行操作中（并行 leader 或 worker）。并行模式会限制许多操作；处于并行事务的子事务
 * 中时同样视为并行模式。
 */
bool
IsInParallelMode(void)
{
	TransactionState s = CurrentTransactionState;

	return s->parallelModeLevel != 0 || s->parallelChildXact;
}

/*
 *	CommandCounterIncrement
 */
/*
 * 中文注释：
 * 递增命令 ID，使当前事务中后续命令能够看到此前命令所做的修改。这是 PostgreSQL 语句内可见性机制的核
 * 心。
 */
void
CommandCounterIncrement(void)
{
	/*
	 * If the current value of the command counter hasn't been "used" to mark
	 * tuples, we need not increment it, since there's no need to distinguish
	 * a read-only command from others.  This helps postpone command counter
	 * overflow, and keeps no-op CommandCounterIncrement operations cheap.
	 */
	if (currentCommandIdUsed)
	{
		/*
		 * Workers synchronize transaction state at the beginning of each
		 * parallel operation, so we can't account for new commands after that
		 * point.
		 */
		if (IsInParallelMode() || IsParallelWorker())
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
					 errmsg("cannot start commands during a parallel operation")));

		currentCommandId += 1;
		if (currentCommandId == InvalidCommandId)
		{
			currentCommandId -= 1;
			ereport(ERROR,
					(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
					 errmsg("cannot have more than 2^32-2 commands in a transaction")));
		}
		currentCommandIdUsed = false;

		/* Propagate new command ID into static snapshots */
		SnapshotSetCommandId(currentCommandId);

		/*
		 * Make any catalog changes done by the just-completed command visible
		 * in the local syscache.  We obviously don't need to do this after a
		 * read-only command.  (But see hacks in inval.c to make real sure we
		 * don't think a command that queued inval messages was read-only.)
		 */
		AtCCI_LocalCache();
	}
}

/*
 * ForceSyncCommit
 *
 * Interface routine to allow commands to force a synchronous commit of the
 * current top-level transaction.  Currently, two-phase commit does not
 * persist and restore this variable.  So long as all callers use
 * PreventInTransactionBlock(), that omission has no consequences.
 */
/*
 * 中文注释：
 * 允许命令强制当前顶层事务同步提交（例如某些需要落盘后才返回的操作）。
 */
void
ForceSyncCommit(void)
{
	forceSyncCommit = true;
}


/* ----------------------------------------------------------------
 *						StartTransaction stuff
 *	（中文）StartTransaction 相关：事务启动时的内存上下文、资源所有者和本地缓存初始化。
 * ----------------------------------------------------------------
 */

/*
 *	AtStart_Cache
 */
/*
 * 中文注释：
 * 接收并处理启动事务前已经到达的失效消息，使本地缓存与共享目录状态保持一致。
 */
static void
AtStart_Cache(void)
{
	AcceptInvalidationMessages();
}

/*
 *	AtStart_Memory
 */
/*
 * 中文注释：
 * 记录事务开始前的内存上下文；必要时创建 TransactionAbortContext（供中止清理使用）
 * 和 TopTransactionContext，然后把 TopTransactionContext 设为当前内存上下文。
 */
static void
AtStart_Memory(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * Remember the memory context that was active prior to transaction start.
	 */
	s->priorContext = CurrentMemoryContext;

	/*
	 * If this is the first time through, create a private context for
	 * AbortTransaction to work in.  By reserving some space now, we can
	 * insulate AbortTransaction from out-of-memory scenarios.  Like
	 * ErrorContext, we set it up with slow growth rate and a nonzero minimum
	 * size, so that space will be reserved immediately.
	 */
	if (TransactionAbortContext == NULL)
		TransactionAbortContext =
			AllocSetContextCreate(TopMemoryContext,
								  "TransactionAbortContext",
								  32 * 1024,
								  32 * 1024,
								  32 * 1024);

	/*
	 * Likewise, if this is the first time through, create a top-level context
	 * for transaction-local data.  This context will be reset at transaction
	 * end, and then re-used in later transactions.
	 */
	if (TopTransactionContext == NULL)
		TopTransactionContext =
			AllocSetContextCreate(TopMemoryContext,
								  "TopTransactionContext",
								  ALLOCSET_DEFAULT_SIZES);

	/*
	 * In a top-level transaction, CurTransactionContext is the same as
	 * TopTransactionContext.
	 */
	CurTransactionContext = TopTransactionContext;
	s->curTransactionContext = CurTransactionContext;

	/* Make the CurTransactionContext active. */
	MemoryContextSwitchTo(CurTransactionContext);
}

/*
 *	AtStart_ResourceOwner
 */
/*
 * 中文注释：
 * 为顶层事务创建资源所有者，用于跟踪事务期间获取的资源。
 */
static void
AtStart_ResourceOwner(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * We shouldn't have a transaction resource owner already.
	 */
	Assert(TopTransactionResourceOwner == NULL);

	/*
	 * Create a toplevel resource owner for the transaction.
	 */
	s->curTransactionOwner = ResourceOwnerCreate(NULL, "TopTransaction");

	TopTransactionResourceOwner = s->curTransactionOwner;
	CurTransactionResourceOwner = s->curTransactionOwner;
	CurrentResourceOwner = s->curTransactionOwner;
}

/* ----------------------------------------------------------------
 *						StartSubTransaction stuff
 *	（中文）StartSubTransaction 相关：子事务启动时的内存上下文和资源所有者初始化。
 * ----------------------------------------------------------------
 */

/*
 * AtSubStart_Memory
 */
/*
 * 中文注释：
 * 子事务开始时创建子事务内存上下文；子事务提交时其内容会合并到父上下文。
 */
static void
AtSubStart_Memory(void)
{
	TransactionState s = CurrentTransactionState;

	Assert(CurTransactionContext != NULL);

	/*
	 * Remember the context that was active prior to subtransaction start.
	 */
	s->priorContext = CurrentMemoryContext;

	/*
	 * Create a CurTransactionContext, which will be used to hold data that
	 * survives subtransaction commit but disappears on subtransaction abort.
	 * We make it a child of the immediate parent's CurTransactionContext.
	 */
	CurTransactionContext = AllocSetContextCreate(CurTransactionContext,
												  "CurTransactionContext",
												  ALLOCSET_DEFAULT_SIZES);
	s->curTransactionContext = CurTransactionContext;

	/* Make the CurTransactionContext active. */
	MemoryContextSwitchTo(CurTransactionContext);
}

/*
 * AtSubStart_ResourceOwner
 */
/*
 * 中文注释：
 * 子事务开始时创建子事务资源所有者，并挂到父资源所有者下。
 */
static void
AtSubStart_ResourceOwner(void)
{
	TransactionState s = CurrentTransactionState;

	Assert(s->parent != NULL);

	/*
	 * Create a resource owner for the subtransaction.  We make it a child of
	 * the immediate parent's resource owner.
	 */
	s->curTransactionOwner =
		ResourceOwnerCreate(s->parent->curTransactionOwner,
							"SubTransaction");

	CurTransactionResourceOwner = s->curTransactionOwner;
	CurrentResourceOwner = s->curTransactionOwner;
}

/* ----------------------------------------------------------------
 *						CommitTransaction stuff
 *	（中文）CommitTransaction 相关：事务提交的 WAL 记录、内存清理和子事务 XID 合并。
 * ----------------------------------------------------------------
 */

/*
 *	RecordTransactionCommit
 *
 * Returns latest XID among xact and its children, or InvalidTransactionId
 * if the xact has no XID.  (We compute that here just because it's easier.)
 *
 * If you change this function, see RecordTransactionCommitPrepared also.
 */
/*
 * 中文注释：
 * 记录顶层事务的提交：向 WAL 写入 XLOG_XACT_COMMIT（或 XLOG_XACT_COMMIT_COMPACT）记录，处理同步提交、提交时间戳、复制等；返回事务及其子事务中的最大 XID。若修改此函数，请同时检查
 * RecordTransactionCommitPrepared 及两阶段提交相关代码。
 */
static TransactionId
RecordTransactionCommit(void)
{
	TransactionId xid = GetTopTransactionIdIfAny();
	bool		markXidCommitted = TransactionIdIsValid(xid);
	TransactionId latestXid = InvalidTransactionId;
	int			nrels;
	RelFileLocator *rels;
	int			nchildren;
	TransactionId *children;
	int			ndroppedstats = 0;
	xl_xact_stats_item *droppedstats = NULL;
	int			nmsgs = 0;
	SharedInvalidationMessage *invalMessages = NULL;
	bool		RelcacheInitFileInval = false;
	bool		wrote_xlog;

	/*
	 * 中文注释：只有已分配 XID 的事务才需要写提交 WAL；没有 XID 且没有副作用的事务可以跳过。
	 * 写提交记录前要收集待删除文件、已提交子事务 XID、失效消息、统计项等附加数据，
	 * 并处理同步提交、复制源推进和提交时间戳。
	 */

	/*
	 * Log pending invalidations for logical decoding of in-progress
	 * transactions.  Normally for DDLs, we log this at each command end,
	 * however, for certain cases where we directly update the system table
	 * without a transaction block, the invalidations are not logged till this
	 * time.
	 */
	if (XLogLogicalInfoActive())
		LogLogicalInvalidations();

	/* Get data needed for commit record */
	nrels = smgrGetPendingDeletes(true, &rels);
	nchildren = xactGetCommittedChildren(&children);
	ndroppedstats = pgstat_get_transactional_drops(true, &droppedstats);
	if (XLogStandbyInfoActive())
		nmsgs = xactGetCommittedInvalidationMessages(&invalMessages,
													 &RelcacheInitFileInval);
	wrote_xlog = (XactLastRecEnd != 0);

	/*
	 * If we haven't been assigned an XID yet, we neither can, nor do we want
	 * to write a COMMIT record.
	 */
	if (!markXidCommitted)
	{
		/*
		 * We expect that every RelationDropStorage is followed by a catalog
		 * update, and hence XID assignment, so we shouldn't get here with any
		 * pending deletes. Same is true for dropping stats.
		 *
		 * Use a real test not just an Assert to check this, since it's a bit
		 * fragile.
		 */
		if (nrels != 0 || ndroppedstats != 0)
			elog(ERROR, "cannot commit a transaction that deleted files but has no xid");

		/* Can't have child XIDs either; AssignTransactionId enforces this */
		Assert(nchildren == 0);

		/*
		 * Transactions without an assigned xid can contain invalidation
		 * messages.  While inplace updates do this, this is not known to be
		 * necessary; see comment at inplace CacheInvalidateHeapTuple().
		 * Extensions might still rely on this capability, and standbys may
		 * need to process those invals.  We can't emit a commit record
		 * without an xid, and we don't want to force assigning an xid,
		 * because that'd be problematic for e.g. vacuum.  Hence we emit a
		 * bespoke record for the invalidations. We don't want to use that in
		 * case a commit record is emitted, so they happen synchronously with
		 * commits (besides not wanting to emit more WAL records).
		 *
		 * XXX Every known use of this capability is a defect.  Since an XID
		 * isn't controlling visibility of the change that prompted invals,
		 * other sessions need the inval even if this transactions aborts.
		 *
		 * ON COMMIT DELETE ROWS does a nontransactional index_build(), which
		 * queues a relcache inval, including in transactions without an xid
		 * that had read the (empty) table.  Standbys don't need any ON COMMIT
		 * DELETE ROWS invals, but we've not done the work to withhold them.
		 */
		if (nmsgs != 0)
		{
			LogStandbyInvalidations(nmsgs, invalMessages,
									RelcacheInitFileInval);
			wrote_xlog = true;	/* not strictly necessary */
		}

		/*
		 * If we didn't create XLOG entries, we're done here; otherwise we
		 * should trigger flushing those entries the same as a commit record
		 * would.  This will primarily happen for HOT pruning and the like; we
		 * want these to be flushed to disk in due time.
		 */
		if (!wrote_xlog)
			goto cleanup;
	}
	else
	{
		bool		replorigin;

		/*
		 * Are we using the replication origins feature?  Or, in other words,
		 * are we replaying remote actions?
		 */
		replorigin = (replorigin_xact_state.origin != InvalidReplOriginId &&
					  replorigin_xact_state.origin != DoNotReplicateId);

		/*
		 * Mark ourselves as within our "commit critical section".  This
		 * forces any concurrent checkpoint to wait until we've updated
		 * pg_xact.  Without this, it is possible for the checkpoint to set
		 * REDO after the XLOG record but fail to flush the pg_xact update to
		 * disk, leading to loss of the transaction commit if the system
		 * crashes a little later.
		 *
		 * Note: we could, but don't bother to, set this flag in
		 * RecordTransactionAbort.  That's because loss of a transaction abort
		 * is noncritical; the presumption would be that it aborted, anyway.
		 *
		 * It's safe to change the delayChkptFlags flag of our own backend
		 * without holding the ProcArrayLock, since we're the only one
		 * modifying it.  This makes checkpoint's determination of which xacts
		 * are delaying the checkpoint a bit fuzzy, but it doesn't matter.
		 *
		 * Note, it is important to get the commit timestamp after marking the
		 * transaction in the commit critical section. See
		 * RecordTransactionCommitPrepared.
		 */
		Assert((MyProc->delayChkptFlags & DELAY_CHKPT_IN_COMMIT) == 0);
		START_CRIT_SECTION();
		MyProc->delayChkptFlags |= DELAY_CHKPT_IN_COMMIT;

		Assert(xactStopTimestamp == 0);

		/*
		 * Ensures the DELAY_CHKPT_IN_COMMIT flag write is globally visible
		 * before commit time is written.
		 */
		pg_write_barrier();

		/*
		 * Insert the commit XLOG record.
		 */
		XactLogCommitRecord(GetCurrentTransactionStopTimestamp(),
							nchildren, children, nrels, rels,
							ndroppedstats, droppedstats,
							nmsgs, invalMessages,
							RelcacheInitFileInval,
							MyXactFlags,
							InvalidTransactionId, NULL /* plain commit */ );

		if (replorigin)
			/* Move LSNs forward for this replication origin */
			replorigin_session_advance(replorigin_xact_state.origin_lsn,
									   XactLastRecEnd);

		/*
		 * Record commit timestamp.  The value comes from plain commit
		 * timestamp if there's no replication origin; otherwise, the
		 * timestamp was already set in replorigin_xact_state.origin_timestamp
		 * by replication.
		 *
		 * We don't need to WAL-log anything here, as the commit record
		 * written above already contains the data.
		 */

		if (!replorigin || replorigin_xact_state.origin_timestamp == 0)
			replorigin_xact_state.origin_timestamp = GetCurrentTransactionStopTimestamp();

		TransactionTreeSetCommitTsData(xid, nchildren, children,
									   replorigin_xact_state.origin_timestamp,
									   replorigin_xact_state.origin);
	}

	/*
	 * Check if we want to commit asynchronously.  We can allow the XLOG flush
	 * to happen asynchronously if synchronous_commit=off, or if the current
	 * transaction has not performed any WAL-logged operation or didn't assign
	 * an xid.  The transaction can end up not writing any WAL, even if it has
	 * an xid, if it only wrote to temporary and/or unlogged tables.  It can
	 * end up having written WAL without an xid if it did HOT pruning.  In
	 * case of a crash, the loss of such a transaction will be irrelevant;
	 * temp tables will be lost anyway, unlogged tables will be truncated and
	 * HOT pruning will be done again later. (Given the foregoing, you might
	 * think that it would be unnecessary to emit the XLOG record at all in
	 * this case, but we don't currently try to do that.  It would certainly
	 * cause problems at least in Hot Standby mode, where the
	 * KnownAssignedXids machinery requires tracking every XID assignment.  It
	 * might be OK to skip it only when wal_level < replica, but for now we
	 * don't.)
	 *
	 * However, if we're doing cleanup of any non-temp rels or committing any
	 * command that wanted to force sync commit, then we must flush XLOG
	 * immediately.  (We must not allow asynchronous commit if there are any
	 * non-temp tables to be deleted, because we might delete the files before
	 * the COMMIT record is flushed to disk.  We do allow asynchronous commit
	 * if all to-be-deleted tables are temporary though, since they are lost
	 * anyway if we crash.)
	 */
	if ((wrote_xlog && markXidCommitted &&
		 synchronous_commit > SYNCHRONOUS_COMMIT_OFF) ||
		forceSyncCommit || nrels > 0)
	{
		XLogFlush(XactLastRecEnd);

		/*
		 * Now we may update the CLOG, if we wrote a COMMIT record above
		 */
		if (markXidCommitted)
			TransactionIdCommitTree(xid, nchildren, children);
	}
	else
	{
		/*
		 * Asynchronous commit case:
		 *
		 * This enables possible committed transaction loss in the case of a
		 * postmaster crash because WAL buffers are left unwritten. Ideally we
		 * could issue the WAL write without the fsync, but some
		 * wal_sync_methods do not allow separate write/fsync.
		 *
		 * Report the latest async commit LSN, so that the WAL writer knows to
		 * flush this commit.
		 */
		XLogSetAsyncXactLSN(XactLastRecEnd);

		/*
		 * We must not immediately update the CLOG, since we didn't flush the
		 * XLOG. Instead, we store the LSN up to which the XLOG must be
		 * flushed before the CLOG may be updated.
		 */
		if (markXidCommitted)
			TransactionIdAsyncCommitTree(xid, nchildren, children, XactLastRecEnd);
	}

	/*
	 * If we entered a commit critical section, leave it now, and let
	 * checkpoints proceed.
	 */
	if (markXidCommitted)
	{
		MyProc->delayChkptFlags &= ~DELAY_CHKPT_IN_COMMIT;
		END_CRIT_SECTION();
	}

	/* Compute latestXid while we have the child XIDs handy */
	latestXid = TransactionIdLatest(xid, nchildren, children);

	/*
	 * Wait for synchronous replication, if required. Similar to the decision
	 * above about using committing asynchronously we only want to wait if
	 * this backend assigned an xid and wrote WAL.  No need to wait if an xid
	 * was assigned due to temporary/unlogged tables or due to HOT pruning.
	 *
	 * Note that at this stage we have marked clog, but still show as running
	 * in the procarray and continue to hold locks.
	 */
	if (wrote_xlog && markXidCommitted)
		SyncRepWaitForLSN(XactLastRecEnd, true);

	/* remember end of last commit record */
	XactLastCommitEnd = XactLastRecEnd;

	/* Reset XactLastRecEnd until the next transaction writes something */
	XactLastRecEnd = 0;
cleanup:
	/* Clean up local data */
	if (rels)
		pfree(rels);
	if (ndroppedstats)
		pfree(droppedstats);

	return latestXid;
}


/*
 *	AtCCI_LocalCache
 */
/*
 * 中文注释：
 * CommandCounterIncrement() 的本地缓存处理部分：先让待处理的 relation map 变更可见，
 * 再处理本地失效消息，使下一条命令看到最新的目录和缓存状态。
 */
static void
AtCCI_LocalCache(void)
{
	/*
	 * Make any pending relation map changes visible.  We must do this before
	 * processing local sinval messages, so that the map changes will get
	 * reflected into the relcache when relcache invals are processed.
	 */
	AtCCI_RelationMap();

	/*
	 * Make catalog changes visible to me for the next command.
	 */
	CommandEndInvalidationMessages();
}

/*
 *	AtCommit_Memory
 */
/*
 * 中文注释：
 * 顶层事务提交后的内存清理：切回事务开始前的内存上下文，并重置 TopTransactionContext
 * （保留上下文对象本身，但释放其中的全部事务级分配）。
 */
static void
AtCommit_Memory(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * Return to the memory context that was current before we started the
	 * transaction.  (In principle, this could not be any of the contexts we
	 * are about to delete.  If it somehow is, assertions in mcxt.c will
	 * complain.)
	 */
	MemoryContextSwitchTo(s->priorContext);

	/*
	 * Release all transaction-local memory.  TopTransactionContext survives
	 * but becomes empty; any sub-contexts go away.
	 */
	Assert(TopTransactionContext != NULL);
	MemoryContextReset(TopTransactionContext);

	/*
	 * Clear these pointers as a pro-forma matter.  (Notionally, while
	 * TopTransactionContext still exists, it's currently not associated with
	 * this TransactionState struct.)
	 */
	CurTransactionContext = NULL;
	s->curTransactionContext = NULL;
}

/* ----------------------------------------------------------------
 *						CommitSubTransaction stuff
 *	（中文）CommitSubTransaction 相关：子事务提交时把 XID 和内存上下文上交给父事务。
 * ----------------------------------------------------------------
 */

/*
 * AtSubCommit_Memory
 */
/*
 * 中文注释：
 * 子事务提交时切回父事务的内存上下文；若子事务上下文为空则直接删除，
 * 避免大量“空子事务”造成内存泄漏。
 */
static void
AtSubCommit_Memory(void)
{
	TransactionState s = CurrentTransactionState;

	Assert(s->parent != NULL);

	/* Return to parent transaction level's memory context. */
	CurTransactionContext = s->parent->curTransactionContext;
	MemoryContextSwitchTo(CurTransactionContext);

	/*
	 * Ordinarily we cannot throw away the child's CurTransactionContext,
	 * since the data it contains will be needed at upper commit.  However, if
	 * there isn't actually anything in it, we can throw it away.  This avoids
	 * a small memory leak in the common case of "trivial" subxacts.
	 */
	if (MemoryContextIsEmpty(s->curTransactionContext))
	{
		MemoryContextDelete(s->curTransactionContext);
		s->curTransactionContext = NULL;
	}
}

/*
 * AtSubCommit_childXids
 *
 * Pass my own XID and my child XIDs up to my parent as committed children.
 */
/*
 * 中文注释：
 * 子事务提交时，把自己的 XID 和所有子 XID 上交给父事务，记录为父事务的已提交子事务。
 */
static void
AtSubCommit_childXids(void)
{
	TransactionState s = CurrentTransactionState;
	int			new_nChildXids;

	Assert(s->parent != NULL);

	/*
	 * The parent childXids array will need to hold my XID and all my
	 * childXids, in addition to the XIDs already there.
	 */
	new_nChildXids = s->parent->nChildXids + s->nChildXids + 1;

	/* Allocate or enlarge the parent array if necessary */
	if (s->parent->maxChildXids < new_nChildXids)
	{
		int			new_maxChildXids;
		TransactionId *new_childXids;

		/*
		 * Make it 2x what's needed right now, to avoid having to enlarge it
		 * repeatedly. But we can't go above MaxAllocSize.  (The latter limit
		 * is what ensures that we don't need to worry about integer overflow
		 * here or in the calculation of new_nChildXids.)
		 */
		new_maxChildXids = Min(new_nChildXids * 2,
							   (int) (MaxAllocSize / sizeof(TransactionId)));

		if (new_maxChildXids < new_nChildXids)
			ereport(ERROR,
					(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
					 errmsg("maximum number of committed subtransactions (%d) exceeded",
							(int) (MaxAllocSize / sizeof(TransactionId)))));

		/*
		 * We keep the child-XID arrays in TopTransactionContext; this avoids
		 * setting up child-transaction contexts for what might be just a few
		 * bytes of grandchild XIDs.
		 */
		if (s->parent->childXids == NULL)
			new_childXids =
				MemoryContextAlloc(TopTransactionContext,
								   new_maxChildXids * sizeof(TransactionId));
		else
			new_childXids = repalloc(s->parent->childXids,
									 new_maxChildXids * sizeof(TransactionId));

		s->parent->childXids = new_childXids;
		s->parent->maxChildXids = new_maxChildXids;
	}

	/*
	 * Copy all my XIDs to parent's array.
	 *
	 * Note: We rely on the fact that the XID of a child always follows that
	 * of its parent.  By copying the XID of this subtransaction before the
	 * XIDs of its children, we ensure that the array stays ordered. Likewise,
	 * all XIDs already in the array belong to subtransactions started and
	 * subcommitted before us, so their XIDs must precede ours.
	 */
	s->parent->childXids[s->parent->nChildXids] = XidFromFullTransactionId(s->fullTransactionId);

	if (s->nChildXids > 0)
		memcpy(&s->parent->childXids[s->parent->nChildXids + 1],
			   s->childXids,
			   s->nChildXids * sizeof(TransactionId));

	s->parent->nChildXids = new_nChildXids;

	/* Release child's array to avoid leakage */
	if (s->childXids != NULL)
		pfree(s->childXids);
	/* We must reset these to avoid double-free if fail later in commit */
	s->childXids = NULL;
	s->nChildXids = 0;
	s->maxChildXids = 0;
}

/* ----------------------------------------------------------------
 *						AbortTransaction stuff
 *	（中文）AbortTransaction 相关：事务中止时的 WAL 记录、内存与资源所有者恢复。
 * ----------------------------------------------------------------
 */

/*
 *	RecordTransactionAbort
 *
 * Returns latest XID among xact and its children, or InvalidTransactionId
 * if the xact has no XID.  (We compute that here just because it's easier.)
 */
/*
 * 中文注释：
 * 记录事务/子事务的中止：若已分配有效 XID，则写 XLOG_XACT_ABORT 记录，并在 pg_xact 中
 * 把该事务（及其子事务）标记为中止。中止记录不需要立即刷盘，因为崩溃恢复默认就认为
 * 未提交的事务已中止。返回事务及其子事务中的最大 XID。
 */
static TransactionId
RecordTransactionAbort(bool isSubXact)
{
	TransactionId xid = GetCurrentTransactionIdIfAny();
	TransactionId latestXid;
	int			nrels;
	RelFileLocator *rels;
	int			ndroppedstats = 0;
	xl_xact_stats_item *droppedstats = NULL;
	int			nchildren;
	TransactionId *children;
	TimestampTz xact_time;
	bool		replorigin;

	/*
	 * 中文注释：没有有效 XID 的事务无需记录中止；有 XID 时写中止记录并在 pg_xact 中标记中止。
	 * 中止记录不要求立即刷盘，因为崩溃后未提交事务本来就会被视为中止。
	 */

	/*
	 * If we haven't been assigned an XID, nobody will care whether we aborted
	 * or not.  Hence, we're done in that case.  It does not matter if we have
	 * rels to delete (note that this routine is not responsible for actually
	 * deleting 'em).  We cannot have any child XIDs, either.
	 */
	if (!TransactionIdIsValid(xid))
	{
		/* Reset XactLastRecEnd until the next transaction writes something */
		if (!isSubXact)
			XactLastRecEnd = 0;
		return InvalidTransactionId;
	}

	/*
	 * We have a valid XID, so we should write an ABORT record for it.
	 *
	 * We do not flush XLOG to disk here, since the default assumption after a
	 * crash would be that we aborted, anyway.  For the same reason, we don't
	 * need to worry about interlocking against checkpoint start.
	 */

	/*
	 * Check that we haven't aborted halfway through RecordTransactionCommit.
	 */
	if (TransactionIdDidCommit(xid))
		elog(PANIC, "cannot abort transaction %u, it was already committed",
			 xid);

	/*
	 * Are we using the replication origins feature?  Or, in other words, are
	 * we replaying remote actions?
	 */
	replorigin = (replorigin_xact_state.origin != InvalidReplOriginId &&
				  replorigin_xact_state.origin != DoNotReplicateId);

	/* Fetch the data we need for the abort record */
	nrels = smgrGetPendingDeletes(false, &rels);
	nchildren = xactGetCommittedChildren(&children);
	ndroppedstats = pgstat_get_transactional_drops(false, &droppedstats);

	/* XXX do we really need a critical section here? */
	START_CRIT_SECTION();

	/* Write the ABORT record */
	if (isSubXact)
		xact_time = GetCurrentTimestamp();
	else
	{
		xact_time = GetCurrentTransactionStopTimestamp();
	}

	XactLogAbortRecord(xact_time,
					   nchildren, children,
					   nrels, rels,
					   ndroppedstats, droppedstats,
					   MyXactFlags, InvalidTransactionId,
					   NULL);

	if (replorigin)
		/* Move LSNs forward for this replication origin */
		replorigin_session_advance(replorigin_xact_state.origin_lsn,
								   XactLastRecEnd);

	/*
	 * Report the latest async abort LSN, so that the WAL writer knows to
	 * flush this abort. There's nothing to be gained by delaying this, since
	 * WALWriter may as well do this when it can. This is important with
	 * streaming replication because if we don't flush WAL regularly we will
	 * find that large aborts leave us with a long backlog for when commits
	 * occur after the abort, increasing our window of data loss should
	 * problems occur at that point.
	 */
	if (!isSubXact)
		XLogSetAsyncXactLSN(XactLastRecEnd);

	/*
	 * Mark the transaction aborted in clog.  This is not absolutely necessary
	 * but we may as well do it while we are here; also, in the subxact case
	 * it is helpful because XactLockTableWait makes use of it to avoid
	 * waiting for already-aborted subtransactions.  It is OK to do it without
	 * having flushed the ABORT record to disk, because in event of a crash
	 * we'd be assumed to have aborted anyway.
	 */
	TransactionIdAbortTree(xid, nchildren, children);

	END_CRIT_SECTION();

	/* Compute latestXid while we have the child XIDs handy */
	latestXid = TransactionIdLatest(xid, nchildren, children);

	/*
	 * If we're aborting a subtransaction, we can immediately remove failed
	 * XIDs from PGPROC's cache of running child XIDs.  We do that here for
	 * subxacts, because we already have the child XID array at hand.  For
	 * main xacts, the equivalent happens just after this function returns.
	 */
	if (isSubXact)
		XidCacheRemoveRunningXids(xid, nchildren, children, latestXid);

	/* Reset XactLastRecEnd until the next transaction writes something */
	if (!isSubXact)
		XactLastRecEnd = 0;

	/* And clean up local data */
	if (rels)
		pfree(rels);
	if (ndroppedstats)
		pfree(droppedstats);

	return latestXid;
}

/*
 *	AtAbort_Memory
 */
/*
 * 中文注释：
 * 事务中止后恢复内存上下文，确保后续清理工作使用正确的上下文。
 */
static void
AtAbort_Memory(void)
{
	/*
	 * Switch into TransactionAbortContext, which should have some free space
	 * even if nothing else does.  We'll work in this context until we've
	 * finished cleaning up.
	 *
	 * It is barely possible to get here when we've not been able to create
	 * TransactionAbortContext yet; if so use TopMemoryContext.
	 */
	if (TransactionAbortContext != NULL)
		MemoryContextSwitchTo(TransactionAbortContext);
	else
		MemoryContextSwitchTo(TopMemoryContext);
}

/*
 * AtSubAbort_Memory
 */
/*
 * 中文注释：
 * 子事务中止后切换到事务中止专用上下文（TransactionAbortContext），
 * 以保证即使内存紧张也能安全完成清理工作。
 */
static void
AtSubAbort_Memory(void)
{
	Assert(TransactionAbortContext != NULL);

	MemoryContextSwitchTo(TransactionAbortContext);
}


/*
 *	AtAbort_ResourceOwner
 */
/*
 * 中文注释：
 * 事务中止后恢复/清理资源所有者。
 */
static void
AtAbort_ResourceOwner(void)
{
	/*
	 * Make sure we have a valid ResourceOwner, if possible (else it will be
	 * NULL, which is OK)
	 */
	CurrentResourceOwner = TopTransactionResourceOwner;
}

/*
 * AtSubAbort_ResourceOwner
 */
/*
 * 中文注释：
 * 子事务中止时把 CurrentResourceOwner 指向该子事务的资源所有者，
 * 以便后续清理它持有的资源。
 */
static void
AtSubAbort_ResourceOwner(void)
{
	TransactionState s = CurrentTransactionState;

	/* Make sure we have a valid ResourceOwner */
	CurrentResourceOwner = s->curTransactionOwner;
}


/*
 * AtSubAbort_childXids
 */
/*
 * 中文注释：
 * 子事务中止时清理其已提交子事务的 XID 记录，因为这些子事务已随之中止。
 */
static void
AtSubAbort_childXids(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * We keep the child-XID arrays in TopTransactionContext (see
	 * AtSubCommit_childXids).  This means we'd better free the array
	 * explicitly at abort to avoid leakage.
	 */
	if (s->childXids != NULL)
		pfree(s->childXids);
	s->childXids = NULL;
	s->nChildXids = 0;
	s->maxChildXids = 0;

	/*
	 * We could prune the unreportedXids array here. But we don't bother. That
	 * would potentially reduce number of XLOG_XACT_ASSIGNMENT records but it
	 * would likely introduce more CPU time into the more common paths, so we
	 * choose not to do that.
	 */
}

/* ----------------------------------------------------------------
 *						CleanupTransaction stuff
 *	（中文）CleanupTransaction 相关：事务中止后的内存清理。
 * ----------------------------------------------------------------
 */

/*
 *	AtCleanup_Memory
 */
/*
 * 中文注释：
 * 事务完全结束后的内存清理：切回事务开始前的上下文，重置事务中止上下文，
 * 重置 TopTransactionContext 并清空相关指针。
 */
static void
AtCleanup_Memory(void)
{
	TransactionState s = CurrentTransactionState;

	/* Should be at top level */
	Assert(s->parent == NULL);

	/*
	 * Return to the memory context that was current before we started the
	 * transaction.  (In principle, this could not be any of the contexts we
	 * are about to delete.  If it somehow is, assertions in mcxt.c will
	 * complain.)
	 */
	MemoryContextSwitchTo(s->priorContext);

	/*
	 * Clear the special abort context for next time.
	 */
	if (TransactionAbortContext != NULL)
		MemoryContextReset(TransactionAbortContext);

	/*
	 * Release all transaction-local memory, the same as in AtCommit_Memory,
	 * except we must cope with the possibility that we didn't get as far as
	 * creating TopTransactionContext.
	 */
	if (TopTransactionContext != NULL)
		MemoryContextReset(TopTransactionContext);

	/*
	 * Clear these pointers as a pro-forma matter.  (Notionally, while
	 * TopTransactionContext still exists, it's currently not associated with
	 * this TransactionState struct.)
	 */
	CurTransactionContext = NULL;
	s->curTransactionContext = NULL;
}


/* ----------------------------------------------------------------
 *						CleanupSubTransaction stuff
 *	（中文）CleanupSubTransaction 相关：子事务清理阶段的内存清理。
 * ----------------------------------------------------------------
 */

/*
 * AtSubCleanup_Memory
 */
/*
 * 中文注释：
 * 子事务清理阶段的内存清理：切回子事务开始前的上下文，重置事务中止上下文，
 * 并删除子事务内存上下文及其所有子上下文。
 */
static void
AtSubCleanup_Memory(void)
{
	TransactionState s = CurrentTransactionState;

	Assert(s->parent != NULL);

	/*
	 * Return to the memory context that was current before we started the
	 * subtransaction.  (In principle, this could not be any of the contexts
	 * we are about to delete.  If it somehow is, assertions in mcxt.c will
	 * complain.)
	 */
	MemoryContextSwitchTo(s->priorContext);

	/* Update CurTransactionContext (might not be same as priorContext) */
	CurTransactionContext = s->parent->curTransactionContext;

	/*
	 * Clear the special abort context for next time.
	 */
	if (TransactionAbortContext != NULL)
		MemoryContextReset(TransactionAbortContext);

	/*
	 * Delete the subxact local memory contexts. Its CurTransactionContext can
	 * go too (note this also kills CurTransactionContexts from any children
	 * of the subxact).
	 */
	if (s->curTransactionContext)
		MemoryContextDelete(s->curTransactionContext);
	s->curTransactionContext = NULL;
}

/* ----------------------------------------------------------------
 *						interface routines
 *	（中文）接口例程：事务启动/提交/准备/中止/清理命令的入口，以及事务块和回调接口。
 * ----------------------------------------------------------------
 */

/*
 *	StartTransaction
 */
/*
 * 中文注释：
 * 启动一个顶层事务：复位事务状态与各字段，确定只读/隔离级别，创建内存上下文和资源所有者，分配虚拟事
 * 务 ID，设置时间戳并初始化各子系统，最终进入 TRANS_INPROGRESS 状态。
 */
static void
StartTransaction(void)
{
	TransactionState s;
	VirtualTransactionId vxid;

	/*
	 * 中文注释（执行流程）：
	 * 1. 将状态栈复位到顶层，并把底层状态置为 TRANS_START；
	 * 2. 初始化嵌套层级、子事务 ID、命令 ID、XID 记账等事务字段；
	 * 3. 设置隔离级别、只读/可延迟属性，并保存用户 ID 与安全上下文；
	 * 4. 创建事务内存上下文和资源所有者；
	 * 5. 分配虚拟事务 ID（vxid）并登记到 ProcArray；
	 * 6. 设置事务/语句时间戳，初始化 GUC、缓存、触发器、统计等子系统；
	 * 7. 把状态置为 TRANS_INPROGRESS，事务正式有效。
	 */

	/*
	 * Let's just make sure the state stack is empty
	 */
	s = &TopTransactionStateData;
	CurrentTransactionState = s;

	Assert(!FullTransactionIdIsValid(XactTopFullTransactionId));

	/* check the current transaction state */
	Assert(s->state == TRANS_DEFAULT);

	/*
	 * Set the current transaction state information appropriately during
	 * start processing.  Note that once the transaction status is switched
	 * this process cannot fail until the user ID and the security context
	 * flags are fetched below.
	 */
	s->state = TRANS_START;
	s->fullTransactionId = InvalidFullTransactionId;	/* until assigned */

	/* Determine if statements are logged in this transaction */
	xact_is_sampled = log_xact_sample_rate != 0 &&
		(log_xact_sample_rate == 1 ||
		 pg_prng_double(&pg_global_prng_state) <= log_xact_sample_rate);

	/*
	 * initialize current transaction state fields
	 *
	 * note: prevXactReadOnly is not used at the outermost level
	 */
	s->nestingLevel = 1;
	s->gucNestLevel = 1;
	s->childXids = NULL;
	s->nChildXids = 0;
	s->maxChildXids = 0;

	/*
	 * Once the current user ID and the security context flags are fetched,
	 * both will be properly reset even if transaction startup fails.
	 */
	GetUserIdAndSecContext(&s->prevUser, &s->prevSecContext);

	/* SecurityRestrictionContext should never be set outside a transaction */
	Assert(s->prevSecContext == 0);

	/*
	 * Make sure we've reset xact state variables
	 *
	 * If recovery is still in progress, mark this transaction as read-only.
	 * We have lower level defences in XLogInsert and elsewhere to stop us
	 * from modifying data during recovery, but this gives the normal
	 * indication to the user that the transaction is read-only.
	 */
	if (RecoveryInProgress())
	{
		s->startedInRecovery = true;
		XactReadOnly = true;
	}
	else
	{
		s->startedInRecovery = false;
		XactReadOnly = DefaultXactReadOnly;
	}
	XactDeferrable = DefaultXactDeferrable;
	XactIsoLevel = DefaultXactIsoLevel;
	forceSyncCommit = false;
	MyXactFlags = 0;

	/*
	 * reinitialize within-transaction counters
	 */
	s->subTransactionId = TopSubTransactionId;
	currentSubTransactionId = TopSubTransactionId;
	currentCommandId = FirstCommandId;
	currentCommandIdUsed = false;

	/*
	 * initialize reported xid accounting
	 */
	nUnreportedXids = 0;
	s->didLogXid = false;

	/*
	 * must initialize resource-management stuff first
	 */
	AtStart_Memory();
	AtStart_ResourceOwner();

	/*
	 * Assign a new LocalTransactionId, and combine it with the proc number to
	 * form a virtual transaction id.
	 */
	vxid.procNumber = MyProcNumber;
	vxid.localTransactionId = GetNextLocalTransactionId();

	/*
	 * Lock the virtual transaction id before we announce it in the proc array
	 */
	VirtualXactLockTableInsert(vxid);

	/*
	 * Advertise it in the proc array.  We assume assignment of
	 * localTransactionId is atomic, and the proc number should be set
	 * already.
	 */
	Assert(MyProc->vxid.procNumber == vxid.procNumber);
	MyProc->vxid.lxid = vxid.localTransactionId;

	TRACE_POSTGRESQL_TRANSACTION_START(vxid.localTransactionId);

	/*
	 * set transaction_timestamp() (a/k/a now()).  Normally, we want this to
	 * be the same as the first command's statement_timestamp(), so don't do a
	 * fresh GetCurrentTimestamp() call (which'd be expensive anyway).  But
	 * for transactions started inside procedures (i.e., nonatomic SPI
	 * contexts), we do need to advance the timestamp.  Also, in a parallel
	 * worker, the timestamp should already have been provided by a call to
	 * SetParallelStartTimestamps().
	 */
	if (!IsParallelWorker())
	{
		if (!SPI_inside_nonatomic_context())
			xactStartTimestamp = stmtStartTimestamp;
		else
			xactStartTimestamp = GetCurrentTimestamp();
	}
	else
		Assert(xactStartTimestamp != 0);
	pgstat_report_xact_timestamp(xactStartTimestamp);
	/* Mark xactStopTimestamp as unset. */
	xactStopTimestamp = 0;

	/*
	 * initialize other subsystems for new transaction
	 */
	AtStart_GUC();
	AtStart_Cache();
	AfterTriggerBeginXact();

	/*
	 * done with start processing, set current transaction state to "in
	 * progress"
	 */
	s->state = TRANS_INPROGRESS;

	/* Schedule transaction timeout */
	if (TransactionTimeout > 0)
		enable_timeout_after(TRANSACTION_TIMEOUT, TransactionTimeout);

	ShowTransactionState("StartTransaction");
}


/*
 *	CommitTransaction
 *
 * NB: if you change this routine, better look at PrepareTransaction too!
 */
/*
 * 中文注释：
 * 顶层事务提交主流程：先执行延迟触发器和关闭游标等预提交工作，再调用回调、清理并行操作、检查序列化
 * 冲突；随后写 WAL 提交记录、从 ProcArray 移除事务、按顺序释放资源并清理本地状态。若修改此函数，务
 * 必同步检查 PrepareTransaction。
 */
static void
CommitTransaction(void)
{
	TransactionState s = CurrentTransactionState;
	TransactionId latestXid;
	bool		is_parallel_worker;

	is_parallel_worker = (s->blockState == TBLOCK_PARALLEL_INPROGRESS);

	/*
	 * 中文注释（执行流程）：
	 * 1. 预提交阶段：触发延迟触发器并关闭所有打开的 Portal；
	 * 2. 调用事务回调，清理未完成的并行操作、延迟触发器和 ON COMMIT 动作；
	 * 3. 同步未写 WAL 的文件，关闭大对象，发送 NOTIFY，检查序列化冲突；
	 * 4. 把底层状态置为 TRANS_COMMIT，调用 RecordTransactionCommit() 写 WAL 并持久化提交；
	 * 5. 从 ProcArray 中移除本事务，使其他后端不再看到它；
	 * 6. 按“其他后端可见资源 -> 锁 -> 后端本地资源”的顺序释放资源并清理各子系统；
	 * 7. 删除资源所有者和事务内存上下文，复位字段，回到 TRANS_DEFAULT。
	 */

	/* Enforce parallel mode restrictions during parallel worker commit. */
	if (is_parallel_worker)
		EnterParallelMode();

	ShowTransactionState("CommitTransaction");

	/*
	 * check the current transaction state
	 */
	if (s->state != TRANS_INPROGRESS)
		elog(WARNING, "CommitTransaction while in %s state",
			 TransStateAsString(s->state));
	Assert(s->parent == NULL);

	/*
	 * Do pre-commit processing that involves calling user-defined code, such
	 * as triggers.  SECURITY_RESTRICTED_OPERATION contexts must not queue an
	 * action that would run here, because that would bypass the sandbox.
	 * Since closing cursors could queue trigger actions, triggers could open
	 * cursors, etc, we have to keep looping until there's nothing left to do.
	 */
	for (;;)
	{
		/*
		 * Fire all currently pending deferred triggers.
		 */
		AfterTriggerFireDeferred();

		/*
		 * Close open portals (converting holdable ones into static portals).
		 * If there weren't any, we are done ... otherwise loop back to check
		 * if they queued deferred triggers.  Lather, rinse, repeat.
		 */
		if (!PreCommit_Portals(false))
			break;
	}

	/*
	 * The remaining actions cannot call any user-defined code, so it's safe
	 * to start shutting down within-transaction services.  But note that most
	 * of this stuff could still throw an error, which would switch us into
	 * the transaction-abort path.
	 */

	CallXactCallbacks(is_parallel_worker ? XACT_EVENT_PARALLEL_PRE_COMMIT
					  : XACT_EVENT_PRE_COMMIT);

	/*
	 * If this xact has started any unfinished parallel operation, clean up
	 * its workers, warning about leaked resources.  (But we don't actually
	 * reset parallelModeLevel till entering TRANS_COMMIT, a bit below.  This
	 * keeps parallel mode restrictions active as long as possible in a
	 * parallel worker.)
	 */
	AtEOXact_Parallel(true);
	if (is_parallel_worker)
	{
		if (s->parallelModeLevel != 1)
			elog(WARNING, "parallelModeLevel is %d not 1 at end of parallel worker transaction",
				 s->parallelModeLevel);
	}
	else
	{
		if (s->parallelModeLevel != 0)
			elog(WARNING, "parallelModeLevel is %d not 0 at end of transaction",
				 s->parallelModeLevel);
	}

	/* Shut down the deferred-trigger manager */
	AfterTriggerEndXact(true);

	/*
	 * Let ON COMMIT management do its thing (must happen after closing
	 * cursors, to avoid dangling-reference problems)
	 */
	PreCommit_on_commit_actions();

	/*
	 * Synchronize files that are created and not WAL-logged during this
	 * transaction. This must happen before AtEOXact_RelationMap(), so that we
	 * don't see committed-but-broken files after a crash.
	 */
	smgrDoPendingSyncs(true, is_parallel_worker);

	/* close large objects before lower-level cleanup */
	AtEOXact_LargeObject(true);

	/*
	 * Insert notifications sent by NOTIFY commands into the queue.  This
	 * should be late in the pre-commit sequence to minimize time spent
	 * holding the notify-insertion lock.  However, this could result in
	 * creating a snapshot, so we must do it before serializable cleanup.
	 */
	PreCommit_Notify();

	/*
	 * Mark serializable transaction as complete for predicate locking
	 * purposes.  This should be done as late as we can put it and still allow
	 * errors to be raised for failure patterns found at commit.  This is not
	 * appropriate in a parallel worker however, because we aren't committing
	 * the leader's transaction and its serializable state will live on.
	 */
	if (!is_parallel_worker)
		PreCommit_CheckForSerializationFailure();

	/* Prevent cancel/die interrupt while cleaning up */
	HOLD_INTERRUPTS();

	/* Commit updates to the relation map --- do this as late as possible */
	AtEOXact_RelationMap(true, is_parallel_worker);

	/*
	 * set the current transaction state information appropriately during
	 * commit processing
	 */
	s->state = TRANS_COMMIT;
	s->parallelModeLevel = 0;
	s->parallelChildXact = false;	/* should be false already */

	/* Disable transaction timeout */
	if (TransactionTimeout > 0)
		disable_timeout(TRANSACTION_TIMEOUT, false);

	if (!is_parallel_worker)
	{
		/*
		 * We need to mark our XIDs as committed in pg_xact.  This is where we
		 * durably commit.
		 */
		latestXid = RecordTransactionCommit();
	}
	else
	{
		/*
		 * We must not mark our XID committed; the parallel leader is
		 * responsible for that.
		 */
		latestXid = InvalidTransactionId;

		/*
		 * Make sure the leader will know about any WAL we wrote before it
		 * commits.
		 */
		ParallelWorkerReportLastRecEnd(XactLastRecEnd);
	}

	TRACE_POSTGRESQL_TRANSACTION_COMMIT(MyProc->vxid.lxid);

	/*
	 * Let others know about no transaction in progress by me. Note that this
	 * must be done _before_ releasing locks we hold and _after_
	 * RecordTransactionCommit.
	 */
	ProcArrayEndTransaction(MyProc, latestXid);

	/*
	 * This is all post-commit cleanup.  Note that if an error is raised here,
	 * it's too late to abort the transaction.  This should be just
	 * noncritical resource releasing.
	 *
	 * The ordering of operations is not entirely random.  The idea is:
	 * release resources visible to other backends (eg, files, buffer pins);
	 * then release locks; then release backend-local resources. We want to
	 * release locks at the point where any backend waiting for us will see
	 * our transaction as being fully cleaned up.
	 *
	 * Resources that can be associated with individual queries are handled by
	 * the ResourceOwner mechanism.  The other calls here are for backend-wide
	 * state.
	 */

	CallXactCallbacks(is_parallel_worker ? XACT_EVENT_PARALLEL_COMMIT
					  : XACT_EVENT_COMMIT);

	CurrentResourceOwner = NULL;
	ResourceOwnerRelease(TopTransactionResourceOwner,
						 RESOURCE_RELEASE_BEFORE_LOCKS,
						 true, true);

	AtEOXact_Aio(true);

	/* Check we've released all buffer pins */
	AtEOXact_Buffers(true);

	/* Clean up the relation cache */
	AtEOXact_RelationCache(true);

	/* Clean up the type cache */
	AtEOXact_TypeCache();

	/*
	 * Make catalog changes visible to all backends.  This has to happen after
	 * relcache references are dropped (see comments for
	 * AtEOXact_RelationCache), but before locks are released (if anyone is
	 * waiting for lock on a relation we've modified, we want them to know
	 * about the catalog change before they start using the relation).
	 */
	AtEOXact_Inval(true);

	AtEOXact_MultiXact();

	ResourceOwnerRelease(TopTransactionResourceOwner,
						 RESOURCE_RELEASE_LOCKS,
						 true, true);
	ResourceOwnerRelease(TopTransactionResourceOwner,
						 RESOURCE_RELEASE_AFTER_LOCKS,
						 true, true);

	/*
	 * Likewise, dropping of files deleted during the transaction is best done
	 * after releasing relcache and buffer pins.  (This is not strictly
	 * necessary during commit, since such pins should have been released
	 * already, but this ordering is definitely critical during abort.)  Since
	 * this may take many seconds, also delay until after releasing locks.
	 * Other backends will observe the attendant catalog changes and not
	 * attempt to access affected files.
	 */
	smgrDoPendingDeletes(true);

	/*
	 * Send out notification signals to other backends (and do other
	 * post-commit NOTIFY cleanup).  This must not happen until after our
	 * transaction is fully done from the viewpoint of other backends.
	 */
	AtCommit_Notify();

	/*
	 * Everything after this should be purely internal-to-this-backend
	 * cleanup.
	 */
	AtEOXact_GUC(true, 1);
	AtEOXact_SPI(true);
	AtEOXact_Enum();
	AtEOXact_on_commit_actions(true);
	AtEOXact_Namespace(true, is_parallel_worker);
	AtEOXact_SMgr();
	AtEOXact_Files(true);
	AtEOXact_ComboCid();
	AtEOXact_HashTables(true);
	AtEOXact_RI(true);
	AtEOXact_PgStat(true, is_parallel_worker);
	AtEOXact_Snapshot(true, false);
	AtEOXact_ApplyLauncher(true);
	AtEOXact_LogicalRepWorkers(true);
	AtEOXact_LogicalCtl();
	pgstat_report_xact_timestamp(0);

	ResourceOwnerDelete(TopTransactionResourceOwner);
	s->curTransactionOwner = NULL;
	CurTransactionResourceOwner = NULL;
	TopTransactionResourceOwner = NULL;

	AtCommit_Memory();

	s->fullTransactionId = InvalidFullTransactionId;
	s->subTransactionId = InvalidSubTransactionId;
	s->nestingLevel = 0;
	s->gucNestLevel = 0;
	s->childXids = NULL;
	s->nChildXids = 0;
	s->maxChildXids = 0;

	XactTopFullTransactionId = InvalidFullTransactionId;
	nParallelCurrentXids = 0;

	/*
	 * done with commit processing, set current transaction state back to
	 * default
	 */
	s->state = TRANS_DEFAULT;

	RESUME_INTERRUPTS();
}


/*
 *	PrepareTransaction
 *
 * NB: if you change this routine, better look at CommitTransaction too!
 */
/*
 * 中文注释：
 * 两阶段提交的第一阶段：执行预提交工作，检查临时对象和导出快照等限制，写 prepare WAL 记录并创建全局
 * 事务，然后把锁和资源转移给 prepared 事务，最后清理后端本地状态。若修改此函数，务必同步检查
 * CommitTransaction。
 */
static void
PrepareTransaction(void)
{
	TransactionState s = CurrentTransactionState;
	FullTransactionId fxid = GetCurrentFullTransactionId();
	GlobalTransaction gxact;
	TimestampTz prepared_at;

	Assert(!IsInParallelMode());

	/*
	 * 中文注释（执行流程）：
	 * 1. 与提交类似地执行预提交工作（触发器、Portal、回调、ON COMMIT 动作）；
	 * 2. 禁止对访问过临时对象或导出过快照的事务执行 PREPARE；
	 * 3. 把状态置为 TRANS_PREPARE，调用 MarkAsPreparing() 预留 GID；
	 * 4. 各子系统通过 AtPrepare_* 收集 2PC 状态，EndPrepare() 真正写 prepare WAL 记录；
	 * 5. 把锁和资源转移给 prepared 事务的 PGPROC，并从 ProcArray 清除当前事务；
	 * 6. 清理后端本地状态并回到 TRANS_DEFAULT；后续由其他后端执行 COMMIT/ROLLBACK PREPARED。
	 */

	ShowTransactionState("PrepareTransaction");

	/*
	 * check the current transaction state
	 */
	if (s->state != TRANS_INPROGRESS)
		elog(WARNING, "PrepareTransaction while in %s state",
			 TransStateAsString(s->state));
	Assert(s->parent == NULL);

	/*
	 * Do pre-commit processing that involves calling user-defined code, such
	 * as triggers.  Since closing cursors could queue trigger actions,
	 * triggers could open cursors, etc, we have to keep looping until there's
	 * nothing left to do.
	 */
	for (;;)
	{
		/*
		 * Fire all currently pending deferred triggers.
		 */
		AfterTriggerFireDeferred();

		/*
		 * Close open portals (converting holdable ones into static portals).
		 * If there weren't any, we are done ... otherwise loop back to check
		 * if they queued deferred triggers.  Lather, rinse, repeat.
		 */
		if (!PreCommit_Portals(true))
			break;
	}

	CallXactCallbacks(XACT_EVENT_PRE_PREPARE);

	/*
	 * The remaining actions cannot call any user-defined code, so it's safe
	 * to start shutting down within-transaction services.  But note that most
	 * of this stuff could still throw an error, which would switch us into
	 * the transaction-abort path.
	 */

	/* Shut down the deferred-trigger manager */
	AfterTriggerEndXact(true);

	/*
	 * Let ON COMMIT management do its thing (must happen after closing
	 * cursors, to avoid dangling-reference problems)
	 */
	PreCommit_on_commit_actions();

	/*
	 * Synchronize files that are created and not WAL-logged during this
	 * transaction. This must happen before EndPrepare(), so that we don't see
	 * committed-but-broken files after a crash and COMMIT PREPARED.
	 */
	smgrDoPendingSyncs(true, false);

	/* close large objects before lower-level cleanup */
	AtEOXact_LargeObject(true);

	/* NOTIFY requires no work at this point */

	/*
	 * Mark serializable transaction as complete for predicate locking
	 * purposes.  This should be done as late as we can put it and still allow
	 * errors to be raised for failure patterns found at commit.
	 */
	PreCommit_CheckForSerializationFailure();

	/*
	 * Don't allow PREPARE TRANSACTION if we've accessed a temporary table in
	 * this transaction.  Having the prepared xact hold locks on another
	 * backend's temp table seems a bad idea --- for instance it would prevent
	 * the backend from exiting.  There are other problems too, such as how to
	 * clean up the source backend's local buffers and ON COMMIT state if the
	 * prepared xact includes a DROP of a temp table.
	 *
	 * Other objects types, like functions, operators or extensions, share the
	 * same restriction as they should not be created, locked or dropped as
	 * this can mess up with this session or even a follow-up session trying
	 * to use the same temporary namespace.
	 *
	 * We must check this after executing any ON COMMIT actions, because they
	 * might still access a temp relation.
	 *
	 * XXX In principle this could be relaxed to allow some useful special
	 * cases, such as a temp table created and dropped all within the
	 * transaction.  That seems to require much more bookkeeping though.
	 */
	if ((MyXactFlags & XACT_FLAGS_ACCESSEDTEMPNAMESPACE))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot PREPARE a transaction that has operated on temporary objects")));

	/*
	 * Likewise, don't allow PREPARE after pg_export_snapshot.  This could be
	 * supported if we added cleanup logic to twophase.c, but for now it
	 * doesn't seem worth the trouble.
	 */
	if (XactHasExportedSnapshots())
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot PREPARE a transaction that has exported snapshots")));

	/* Prevent cancel/die interrupt while cleaning up */
	HOLD_INTERRUPTS();

	/*
	 * set the current transaction state information appropriately during
	 * prepare processing
	 */
	s->state = TRANS_PREPARE;

	/* Disable transaction timeout */
	if (TransactionTimeout > 0)
		disable_timeout(TRANSACTION_TIMEOUT, false);

	prepared_at = GetCurrentTimestamp();

	/*
	 * Reserve the GID for this transaction. This could fail if the requested
	 * GID is invalid or already in use.
	 */
	gxact = MarkAsPreparing(fxid, prepareGID, prepared_at,
							GetUserId(), MyDatabaseId);
	prepareGID = NULL;

	/*
	 * Collect data for the 2PC state file.  Note that in general, no actual
	 * state change should happen in the called modules during this step,
	 * since it's still possible to fail before commit, and in that case we
	 * want transaction abort to be able to clean up.  (In particular, the
	 * AtPrepare routines may error out if they find cases they cannot
	 * handle.)  State cleanup should happen in the PostPrepare routines
	 * below.  However, some modules can go ahead and clear state here because
	 * they wouldn't do anything with it during abort anyway.
	 *
	 * Note: because the 2PC state file records will be replayed in the same
	 * order they are made, the order of these calls has to match the order in
	 * which we want things to happen during COMMIT PREPARED or ROLLBACK
	 * PREPARED; in particular, pay attention to whether things should happen
	 * before or after releasing the transaction's locks.
	 */
	StartPrepare(gxact);

	AtPrepare_Notify();
	AtPrepare_Locks();
	AtPrepare_PredicateLocks();
	AtPrepare_PgStat();
	AtPrepare_MultiXact();
	AtPrepare_RelationMap();

	/*
	 * Here is where we really truly prepare.
	 *
	 * We have to record transaction prepares even if we didn't make any
	 * updates, because the transaction manager might get confused if we lose
	 * a global transaction.
	 */
	EndPrepare(gxact);

	/*
	 * Now we clean up backend-internal state and release internal resources.
	 */

	/* Reset XactLastRecEnd until the next transaction writes something */
	XactLastRecEnd = 0;

	/*
	 * Transfer our locks to a dummy PGPROC.  This has to be done before
	 * ProcArrayClearTransaction().  Otherwise, a GetLockConflicts() would
	 * conclude "xact already committed or aborted" for our locks.
	 */
	PostPrepare_Locks(fxid);

	/*
	 * Let others know about no transaction in progress by me.  This has to be
	 * done *after* the prepared transaction has been marked valid, else
	 * someone may think it is unlocked and recyclable.
	 */
	ProcArrayClearTransaction(MyProc);

	/*
	 * In normal commit-processing, this is all non-critical post-transaction
	 * cleanup.  When the transaction is prepared, however, it's important
	 * that the locks and other per-backend resources are transferred to the
	 * prepared transaction's PGPROC entry.  Note that if an error is raised
	 * here, it's too late to abort the transaction. XXX: This probably should
	 * be in a critical section, to force a PANIC if any of this fails, but
	 * that cure could be worse than the disease.
	 */

	CallXactCallbacks(XACT_EVENT_PREPARE);

	ResourceOwnerRelease(TopTransactionResourceOwner,
						 RESOURCE_RELEASE_BEFORE_LOCKS,
						 true, true);

	AtEOXact_Aio(true);

	/* Check we've released all buffer pins */
	AtEOXact_Buffers(true);

	/* Clean up the relation cache */
	AtEOXact_RelationCache(true);

	/* Clean up the type cache */
	AtEOXact_TypeCache();

	/* notify doesn't need a postprepare call */

	PostPrepare_PgStat();

	PostPrepare_Inval();

	PostPrepare_smgr();

	PostPrepare_MultiXact(fxid);

	PostPrepare_PredicateLocks(fxid);

	ResourceOwnerRelease(TopTransactionResourceOwner,
						 RESOURCE_RELEASE_LOCKS,
						 true, true);
	ResourceOwnerRelease(TopTransactionResourceOwner,
						 RESOURCE_RELEASE_AFTER_LOCKS,
						 true, true);

	/*
	 * Allow another backend to finish the transaction.  After
	 * PostPrepare_Twophase(), the transaction is completely detached from our
	 * backend.  The rest is just non-critical cleanup of backend-local state.
	 */
	PostPrepare_Twophase();

	/* PREPARE acts the same as COMMIT as far as GUC is concerned */
	AtEOXact_GUC(true, 1);
	AtEOXact_SPI(true);
	AtEOXact_Enum();
	AtEOXact_on_commit_actions(true);
	AtEOXact_Namespace(true, false);
	AtEOXact_SMgr();
	AtEOXact_Files(true);
	AtEOXact_ComboCid();
	AtEOXact_HashTables(true);
	AtEOXact_RI(true);
	/* don't call AtEOXact_PgStat here; we fixed pgstat state above */
	AtEOXact_Snapshot(true, true);
	/* we treat PREPARE as ROLLBACK so far as waking workers goes */
	AtEOXact_ApplyLauncher(false);
	AtEOXact_LogicalRepWorkers(false);
	AtEOXact_LogicalCtl();
	pgstat_report_xact_timestamp(0);

	CurrentResourceOwner = NULL;
	ResourceOwnerDelete(TopTransactionResourceOwner);
	s->curTransactionOwner = NULL;
	CurTransactionResourceOwner = NULL;
	TopTransactionResourceOwner = NULL;

	AtCommit_Memory();

	s->fullTransactionId = InvalidFullTransactionId;
	s->subTransactionId = InvalidSubTransactionId;
	s->nestingLevel = 0;
	s->gucNestLevel = 0;
	s->childXids = NULL;
	s->nChildXids = 0;
	s->maxChildXids = 0;

	XactTopFullTransactionId = InvalidFullTransactionId;
	nParallelCurrentXids = 0;

	/*
	 * done with 1st phase commit processing, set current transaction state
	 * back to default
	 */
	s->state = TRANS_DEFAULT;

	RESUME_INTERRUPTS();
}


/*
 *	AbortTransaction
 */
/*
 * 中文注释：
 * 顶层事务中止主流程：尽快释放轻量锁，恢复用户 ID/安全上下文和内存上下文，停止并行操作，写中止 WAL
 * 记录，从 ProcArray 移除事务，然后按与提交相反的顺序释放资源和清理状态。状态保持 TRANS_ABORT，直到
 * CleanupTransaction。
 */
static void
AbortTransaction(void)
{
	TransactionState s = CurrentTransactionState;
	TransactionId latestXid;
	bool		is_parallel_worker;

	/*
	 * 中文注释（执行流程）：
	 * 1. 持有中断，禁用事务超时，并恢复可用的内存上下文和资源所有者；
	 * 2. 尽快释放轻量锁、缓冲区内容锁和等待状态，清理 WAL 插入与超时状态；
	 * 3. 把底层状态置为 TRANS_ABORT，恢复用户 ID 与安全上下文；
	 * 4. 停止并行操作，中止触发器、Portal、大对象、NOTIFY、两阶段状态等；
	 * 5. 调用 RecordTransactionAbort() 写中止 WAL 记录；
	 * 6. 从 ProcArray 移除事务，按与提交相反的顺序释放资源；
	 * 7. 状态保持 TRANS_ABORT，等待 CleanupTransaction() 做最终清理。
	 */

	/* Prevent cancel/die interrupt while cleaning up */
	HOLD_INTERRUPTS();

	/* Disable transaction timeout */
	if (TransactionTimeout > 0)
		disable_timeout(TRANSACTION_TIMEOUT, false);

	/* Make sure we have a valid memory context and resource owner */
	AtAbort_Memory();
	AtAbort_ResourceOwner();

	/*
	 * Release any LW locks we might be holding as quickly as possible.
	 * (Regular locks, however, must be held till we finish aborting.)
	 * Releasing LW locks is critical since we might try to grab them again
	 * while cleaning up!
	 */
	LWLockReleaseAll();

	/*
	 * Cleanup waiting for LSN if any.
	 */
	WaitLSNCleanup();

	/* Clear wait information and command progress indicator */
	pgstat_report_wait_end();
	pgstat_progress_end_command();

	pgaio_error_cleanup();

	/* Clean up buffer content locks, too */
	UnlockBuffers();

	/* Reset WAL record construction state */
	XLogResetInsertion();

	/* Cancel condition variable sleep */
	ConditionVariableCancelSleep();

	/*
	 * Also clean up any open wait for lock, since the lock manager will choke
	 * if we try to wait for another lock before doing this.
	 */
	LockErrorCleanup();

	/*
	 * If any timeout events are still active, make sure the timeout interrupt
	 * is scheduled.  This covers possible loss of a timeout interrupt due to
	 * longjmp'ing out of the SIGINT handler (see notes in handle_sig_alarm).
	 * We delay this till after LockErrorCleanup so that we don't uselessly
	 * reschedule lock or deadlock check timeouts.
	 */
	reschedule_timeouts();

	/*
	 * Re-enable signals, in case we got here by longjmp'ing out of a signal
	 * handler.  We do this fairly early in the sequence so that the timeout
	 * infrastructure will be functional if needed while aborting.
	 */
	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/*
	 * check the current transaction state
	 */
	is_parallel_worker = (s->blockState == TBLOCK_PARALLEL_INPROGRESS);
	if (s->state != TRANS_INPROGRESS && s->state != TRANS_PREPARE)
		elog(WARNING, "AbortTransaction while in %s state",
			 TransStateAsString(s->state));
	Assert(s->parent == NULL);

	/*
	 * set the current transaction state information appropriately during the
	 * abort processing
	 */
	s->state = TRANS_ABORT;

	/*
	 * Reset user ID which might have been changed transiently.  We need this
	 * to clean up in case control escaped out of a SECURITY DEFINER function
	 * or other local change of CurrentUserId; therefore, the prior value of
	 * SecurityRestrictionContext also needs to be restored.
	 *
	 * (Note: it is not necessary to restore session authorization or role
	 * settings here because those can only be changed via GUC, and GUC will
	 * take care of rolling them back if need be.)
	 */
	SetUserIdAndSecContext(s->prevUser, s->prevSecContext);

	/* Forget about any active REINDEX. */
	ResetReindexState(s->nestingLevel);

	/* Reset logical streaming state. */
	ResetLogicalStreamingState();

	/* Reset snapshot export state. */
	SnapBuildResetExportedSnapshotState();

	/*
	 * If this xact has started any unfinished parallel operation, clean up
	 * its workers and exit parallel mode.  Don't warn about leaked resources.
	 */
	AtEOXact_Parallel(false);
	s->parallelModeLevel = 0;
	s->parallelChildXact = false;	/* should be false already */

	/*
	 * do abort processing
	 */
	AfterTriggerEndXact(false); /* 'false' means it's abort */
	AtAbort_Portals();
	smgrDoPendingSyncs(false, is_parallel_worker);
	AtEOXact_LargeObject(false);
	AtAbort_Notify();
	AtEOXact_RelationMap(false, is_parallel_worker);
	AtAbort_Twophase();

	/*
	 * Advertise the fact that we aborted in pg_xact (assuming that we got as
	 * far as assigning an XID to advertise).  But if we're inside a parallel
	 * worker, skip this; the user backend must be the one to write the abort
	 * record.
	 */
	if (!is_parallel_worker)
		latestXid = RecordTransactionAbort(false);
	else
	{
		latestXid = InvalidTransactionId;

		/*
		 * Since the parallel leader won't get our value of XactLastRecEnd in
		 * this case, we nudge WAL-writer ourselves in this case.  See related
		 * comments in RecordTransactionAbort for why this matters.
		 */
		XLogSetAsyncXactLSN(XactLastRecEnd);
	}

	TRACE_POSTGRESQL_TRANSACTION_ABORT(MyProc->vxid.lxid);

	/*
	 * Let others know about no transaction in progress by me. Note that this
	 * must be done _before_ releasing locks we hold and _after_
	 * RecordTransactionAbort.
	 */
	ProcArrayEndTransaction(MyProc, latestXid);

	/*
	 * Post-abort cleanup.  See notes in CommitTransaction() concerning
	 * ordering.  We can skip all of it if the transaction failed before
	 * creating a resource owner.
	 */
	if (TopTransactionResourceOwner != NULL)
	{
		if (is_parallel_worker)
			CallXactCallbacks(XACT_EVENT_PARALLEL_ABORT);
		else
			CallXactCallbacks(XACT_EVENT_ABORT);

		ResourceOwnerRelease(TopTransactionResourceOwner,
							 RESOURCE_RELEASE_BEFORE_LOCKS,
							 false, true);
		AtEOXact_Aio(false);
		AtEOXact_Buffers(false);
		AtEOXact_RelationCache(false);
		AtEOXact_TypeCache();
		AtEOXact_Inval(false);
		AtEOXact_MultiXact();
		ResourceOwnerRelease(TopTransactionResourceOwner,
							 RESOURCE_RELEASE_LOCKS,
							 false, true);
		ResourceOwnerRelease(TopTransactionResourceOwner,
							 RESOURCE_RELEASE_AFTER_LOCKS,
							 false, true);
		smgrDoPendingDeletes(false);

		AtEOXact_GUC(false, 1);
		AtEOXact_SPI(false);
		AtEOXact_Enum();
		AtEOXact_on_commit_actions(false);
		AtEOXact_Namespace(false, is_parallel_worker);
		AtEOXact_SMgr();
		AtEOXact_Files(false);
		AtEOXact_ComboCid();
		AtEOXact_HashTables(false);
		AtEOXact_RI(false);
		AtEOXact_PgStat(false, is_parallel_worker);
		AtEOXact_ApplyLauncher(false);
		AtEOXact_LogicalRepWorkers(false);
		AtEOXact_LogicalCtl();
		pgstat_report_xact_timestamp(0);
	}

	/*
	 * State remains TRANS_ABORT until CleanupTransaction().
	 */
	RESUME_INTERRUPTS();
}

/*
 *	CleanupTransaction
 */
/*
 * 中文注释：
 * 事务中止后的清理阶段：释放 Portal 内存和快照，删除资源所有者和事务内存上下文，复位事务状态字段，
 * 最终回到 TRANS_DEFAULT 空闲状态。
 */
static void
CleanupTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * State should still be TRANS_ABORT from AbortTransaction().
	 */
	if (s->state != TRANS_ABORT)
		elog(FATAL, "CleanupTransaction: unexpected state %s",
			 TransStateAsString(s->state));

	/*
	 * do abort cleanup processing
	 */
	AtCleanup_Portals();		/* now safe to release portal memory */
	AtEOXact_Snapshot(false, true); /* and release the transaction's snapshots */

	CurrentResourceOwner = NULL;	/* and resource owner */
	if (TopTransactionResourceOwner)
		ResourceOwnerDelete(TopTransactionResourceOwner);
	s->curTransactionOwner = NULL;
	CurTransactionResourceOwner = NULL;
	TopTransactionResourceOwner = NULL;

	AtCleanup_Memory();			/* and transaction memory */

	s->fullTransactionId = InvalidFullTransactionId;
	s->subTransactionId = InvalidSubTransactionId;
	s->nestingLevel = 0;
	s->gucNestLevel = 0;
	s->childXids = NULL;
	s->nChildXids = 0;
	s->maxChildXids = 0;
	s->parallelModeLevel = 0;
	s->parallelChildXact = false;

	XactTopFullTransactionId = InvalidFullTransactionId;
	nParallelCurrentXids = 0;

	/*
	 * done with abort processing, set current transaction state back to
	 * default
	 */
	s->state = TRANS_DEFAULT;
}

/*
 *	StartTransactionCommand
 */
/*
 * 中文注释：
 * 每条 SQL 命令开始时调用。根据当前 blockState 决定是启动新事务，还是沿用已有事务/子事务；最后切换
 * 到事务级内存上下文。
 */
void
StartTransactionCommand(void)
{
	TransactionState s = CurrentTransactionState;

	switch (s->blockState)
	{
			/*
			 * if we aren't in a transaction block, we just do our usual start
			 * transaction.
			 */
		case TBLOCK_DEFAULT:
			StartTransaction();
			s->blockState = TBLOCK_STARTED;
			break;

			/*
			 * We are somewhere in a transaction block or subtransaction and
			 * about to start a new command.  For now we do nothing, but
			 * someday we may do command-local resource initialization. (Note
			 * that any needed CommandCounterIncrement was done by the
			 * previous CommitTransactionCommand.)
			 */
		case TBLOCK_INPROGRESS:
		case TBLOCK_IMPLICIT_INPROGRESS:
		case TBLOCK_SUBINPROGRESS:
			break;

			/*
			 * Here we are in a failed transaction block (one of the commands
			 * caused an abort) so we do nothing but remain in the abort
			 * state.  Eventually we will get a ROLLBACK command which will
			 * get us out of this state.  (It is up to other code to ensure
			 * that no commands other than ROLLBACK will be processed in these
			 * states.)
			 */
		case TBLOCK_ABORT:
		case TBLOCK_SUBABORT:
			break;

			/* These cases are invalid. */
		case TBLOCK_STARTED:
		case TBLOCK_BEGIN:
		case TBLOCK_PARALLEL_INPROGRESS:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
		case TBLOCK_PREPARE:
			elog(ERROR, "StartTransactionCommand: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}

	/*
	 * We must switch to CurTransactionContext before returning. This is
	 * already done if we called StartTransaction, otherwise not.
	 */
	Assert(CurTransactionContext != NULL);
	MemoryContextSwitchTo(CurTransactionContext);
}


/*
 * Simple system for saving and restoring transaction characteristics
 * (isolation level, read only, deferrable).  We need this for transaction
 * chaining, so that we can set the characteristics of the new transaction to
 * be the same as the previous one.  (We need something like this because the
 * GUC system resets the characteristics at transaction end, so for example
 * just skipping the reset in StartTransaction() won't work.)
 */
/*
 * 中文注释：
 * 保存当前事务特征（隔离级别、只读、可延迟），供 COMMIT/ROLLBACK AND CHAIN 在开启新事务时恢复。
 */
void
SaveTransactionCharacteristics(SavedTransactionCharacteristics *s)
{
	s->save_XactIsoLevel = XactIsoLevel;
	s->save_XactReadOnly = XactReadOnly;
	s->save_XactDeferrable = XactDeferrable;
}

/*
 * 中文注释：
 * 恢复先前保存的事务特征，用于事务链（AND CHAIN）。
 */
void
RestoreTransactionCharacteristics(const SavedTransactionCharacteristics *s)
{
	XactIsoLevel = s->save_XactIsoLevel;
	XactReadOnly = s->save_XactReadOnly;
	XactDeferrable = s->save_XactDeferrable;
}

/*
 *	CommitTransactionCommand -- a wrapper function handling the
 *		loop over subtransactions to avoid a potentially dangerous recursion
 *		in CommitTransactionCommandInternal().
 */
/*
 * 中文注释：
 * 包装函数：反复调用 CommitTransactionCommandInternal()，以循环代替递归，避免大量嵌套子事务导致栈溢
 * 出。
 */
void
CommitTransactionCommand(void)
{
	/*
	 * Repeatedly call CommitTransactionCommandInternal() until all the work
	 * is done.
	 */
	while (!CommitTransactionCommandInternal())
	{
	}
}

/*
 *	CommitTransactionCommandInternal - a function doing an iteration of work
 *		regarding handling the commit transaction command.  In the case of
 *		subtransactions more than one iterations could be required.  Returns
 *		true when no more iterations required, false otherwise.
 */
/*
 * 中文注释：
 * 执行一次 COMMIT 处理迭代。根据 blockState 完成顶层提交、子事务提交、保存点释放、清理中止事务等；
 * 若还需继续处理父事务则返回 false。
 */
static bool
CommitTransactionCommandInternal(void)
{
	TransactionState s = CurrentTransactionState;
	SavedTransactionCharacteristics savetc;

	/* Must save in case we need to restore below */
	SaveTransactionCharacteristics(&savetc);

	/*
	 * 中文注释（事务块状态机）：
	 * - TBLOCK_STARTED：单条语句事务，直接提交并回到空闲；
	 * - TBLOCK_BEGIN：BEGIN 完成，进入 TBLOCK_INPROGRESS；
	 * - TBLOCK_INPROGRESS/TBLOCK_SUBINPROGRESS：命令结束，递增命令 ID；
	 * - TBLOCK_END：执行顶层提交（支持 AND CHAIN）；
	 * - TBLOCK_ABORT/SUBABORT：保持失败状态，等待 ROLLBACK；
	 * - TBLOCK_ABORT_END/ABORT_PENDING：清理，或先中止再清理；
	 * - TBLOCK_PREPARE：执行两阶段提交的 prepare；
	 * - TBLOCK_SUBBEGIN/SUBRELEASE/SUBCOMMIT/SUBRESTART：启动、释放、提交或重启子事务。
	 * 返回 false 表示还需要继续处理父事务。
	 */

	switch (s->blockState)
	{
			/*
			 * These shouldn't happen.  TBLOCK_DEFAULT means the previous
			 * StartTransactionCommand didn't set the STARTED state
			 * appropriately, while TBLOCK_PARALLEL_INPROGRESS should be ended
			 * by EndParallelWorkerTransaction(), not this function.
			 */
		case TBLOCK_DEFAULT:
		case TBLOCK_PARALLEL_INPROGRESS:
			elog(FATAL, "CommitTransactionCommand: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;

			/*
			 * If we aren't in a transaction block, just do our usual
			 * transaction commit, and return to the idle state.
			 */
		case TBLOCK_STARTED:
			CommitTransaction();
			s->blockState = TBLOCK_DEFAULT;
			break;

			/*
			 * We are completing a "BEGIN TRANSACTION" command, so we change
			 * to the "transaction block in progress" state and return.  (We
			 * assume the BEGIN did nothing to the database, so we need no
			 * CommandCounterIncrement.)
			 */
		case TBLOCK_BEGIN:
			s->blockState = TBLOCK_INPROGRESS;
			break;

			/*
			 * This is the case when we have finished executing a command
			 * someplace within a transaction block.  We increment the command
			 * counter and return.
			 */
		case TBLOCK_INPROGRESS:
		case TBLOCK_IMPLICIT_INPROGRESS:
		case TBLOCK_SUBINPROGRESS:
			CommandCounterIncrement();
			break;

			/*
			 * We are completing a "COMMIT" command.  Do it and return to the
			 * idle state.
			 */
		case TBLOCK_END:
			CommitTransaction();
			s->blockState = TBLOCK_DEFAULT;
			if (s->chain)
			{
				StartTransaction();
				s->blockState = TBLOCK_INPROGRESS;
				s->chain = false;
				RestoreTransactionCharacteristics(&savetc);
			}
			break;

			/*
			 * Here we are in the middle of a transaction block but one of the
			 * commands caused an abort so we do nothing but remain in the
			 * abort state.  Eventually we will get a ROLLBACK command.
			 */
		case TBLOCK_ABORT:
		case TBLOCK_SUBABORT:
			break;

			/*
			 * Here we were in an aborted transaction block and we just got
			 * the ROLLBACK command from the user, so clean up the
			 * already-aborted transaction and return to the idle state.
			 */
		case TBLOCK_ABORT_END:
			CleanupTransaction();
			s->blockState = TBLOCK_DEFAULT;
			if (s->chain)
			{
				StartTransaction();
				s->blockState = TBLOCK_INPROGRESS;
				s->chain = false;
				RestoreTransactionCharacteristics(&savetc);
			}
			break;

			/*
			 * Here we were in a perfectly good transaction block but the user
			 * told us to ROLLBACK anyway.  We have to abort the transaction
			 * and then clean up.
			 */
		case TBLOCK_ABORT_PENDING:
			AbortTransaction();
			CleanupTransaction();
			s->blockState = TBLOCK_DEFAULT;
			if (s->chain)
			{
				StartTransaction();
				s->blockState = TBLOCK_INPROGRESS;
				s->chain = false;
				RestoreTransactionCharacteristics(&savetc);
			}
			break;

			/*
			 * We are completing a "PREPARE TRANSACTION" command.  Do it and
			 * return to the idle state.
			 */
		case TBLOCK_PREPARE:
			PrepareTransaction();
			s->blockState = TBLOCK_DEFAULT;
			break;

			/*
			 * The user issued a SAVEPOINT inside a transaction block. Start a
			 * subtransaction.  (DefineSavepoint already did PushTransaction,
			 * so as to have someplace to put the SUBBEGIN state.)
			 */
		case TBLOCK_SUBBEGIN:
			StartSubTransaction();
			s->blockState = TBLOCK_SUBINPROGRESS;
			break;

			/*
			 * The user issued a RELEASE command, so we end the current
			 * subtransaction and return to the parent transaction. The parent
			 * might be ended too, so repeat till we find an INPROGRESS
			 * transaction or subtransaction.
			 */
		case TBLOCK_SUBRELEASE:
			do
			{
				CommitSubTransaction();
				s = CurrentTransactionState;	/* changed by pop */
			} while (s->blockState == TBLOCK_SUBRELEASE);

			Assert(s->blockState == TBLOCK_INPROGRESS ||
				   s->blockState == TBLOCK_SUBINPROGRESS);
			break;

			/*
			 * The user issued a COMMIT, so we end the current subtransaction
			 * hierarchy and perform final commit. We do this by rolling up
			 * any subtransactions into their parent, which leads to O(N^2)
			 * operations with respect to resource owners - this isn't that
			 * bad until we approach a thousands of savepoints but is
			 * necessary for correctness should after triggers create new
			 * resource owners.
			 */
		case TBLOCK_SUBCOMMIT:
			do
			{
				CommitSubTransaction();
				s = CurrentTransactionState;	/* changed by pop */
			} while (s->blockState == TBLOCK_SUBCOMMIT);
			/* If we had a COMMIT command, finish off the main xact too */
			if (s->blockState == TBLOCK_END)
			{
				Assert(s->parent == NULL);
				CommitTransaction();
				s->blockState = TBLOCK_DEFAULT;
				if (s->chain)
				{
					StartTransaction();
					s->blockState = TBLOCK_INPROGRESS;
					s->chain = false;
					RestoreTransactionCharacteristics(&savetc);
				}
			}
			else if (s->blockState == TBLOCK_PREPARE)
			{
				Assert(s->parent == NULL);
				PrepareTransaction();
				s->blockState = TBLOCK_DEFAULT;
			}
			else
				elog(ERROR, "CommitTransactionCommand: unexpected state %s",
					 BlockStateAsString(s->blockState));
			break;

			/*
			 * The current already-failed subtransaction is ending due to a
			 * ROLLBACK or ROLLBACK TO command, so pop it and recursively
			 * examine the parent (which could be in any of several states).
			 * As we need to examine the parent, return false to request the
			 * caller to do the next iteration.
			 */
		case TBLOCK_SUBABORT_END:
			CleanupSubTransaction();
			return false;

			/*
			 * As above, but it's not dead yet, so abort first.
			 */
		case TBLOCK_SUBABORT_PENDING:
			AbortSubTransaction();
			CleanupSubTransaction();
			return false;

			/*
			 * The current subtransaction is the target of a ROLLBACK TO
			 * command.  Abort and pop it, then start a new subtransaction
			 * with the same name.
			 */
		case TBLOCK_SUBRESTART:
			{
				char	   *name;
				int			savepointLevel;

				/* save name and keep Cleanup from freeing it */
				name = s->name;
				s->name = NULL;
				savepointLevel = s->savepointLevel;

				AbortSubTransaction();
				CleanupSubTransaction();

				DefineSavepoint(NULL);
				s = CurrentTransactionState;	/* changed by push */
				s->name = name;
				s->savepointLevel = savepointLevel;

				/* This is the same as TBLOCK_SUBBEGIN case */
				Assert(s->blockState == TBLOCK_SUBBEGIN);
				StartSubTransaction();
				s->blockState = TBLOCK_SUBINPROGRESS;
			}
			break;

			/*
			 * Same as above, but the subtransaction had already failed, so we
			 * don't need AbortSubTransaction.
			 */
		case TBLOCK_SUBABORT_RESTART:
			{
				char	   *name;
				int			savepointLevel;

				/* save name and keep Cleanup from freeing it */
				name = s->name;
				s->name = NULL;
				savepointLevel = s->savepointLevel;

				CleanupSubTransaction();

				DefineSavepoint(NULL);
				s = CurrentTransactionState;	/* changed by push */
				s->name = name;
				s->savepointLevel = savepointLevel;

				/* This is the same as TBLOCK_SUBBEGIN case */
				Assert(s->blockState == TBLOCK_SUBBEGIN);
				StartSubTransaction();
				s->blockState = TBLOCK_SUBINPROGRESS;
			}
			break;
	}

	/* Done, no more iterations required */
	return true;
}

/*
 *	AbortCurrentTransaction -- a wrapper function handling the
 *		loop over subtransactions to avoid potentially dangerous recursion in
 *		AbortCurrentTransactionInternal().
 */
/*
 * 中文注释：
 * 包装函数：反复调用 AbortCurrentTransactionInternal()，以循环代替递归处理多层子事务中止。
 */
void
AbortCurrentTransaction(void)
{
	/*
	 * Repeatedly call AbortCurrentTransactionInternal() until all the work is
	 * done.
	 */
	while (!AbortCurrentTransactionInternal())
	{
	}
}

/*
 *	AbortCurrentTransactionInternal - a function doing an iteration of work
 *		regarding handling the current transaction abort.  In the case of
 *		subtransactions more than one iterations could be required.  Returns
 *		true when no more iterations required, false otherwise.
 */
/*
 * 中文注释：
 * 执行一次事务中止处理迭代。根据 blockState 中止顶层事务或子事务并做相应清理；若还需处理父事务则返
 * 回 false。
 */
static bool
AbortCurrentTransactionInternal(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * 中文注释（中止状态机）：
	 * - 空闲状态直接返回；事务启动失败（TRANS_START）时先修正状态再中止；
	 * - 单条语句、隐式事务或 BEGIN 阶段失败：中止并清理，回到空闲；
	 * - TBLOCK_INPROGRESS：中止后保持 TBLOCK_ABORT，等待用户 ROLLBACK；
	 * - TBLOCK_END/PREPARE：提交或准备阶段失败，中止并清理；
	 * - 子事务失败：只中止当前子事务并进入 TBLOCK_SUBABORT；
	 * - 子事务启动/释放/提交/重启失败：中止并弹出子事务，返回 false 继续处理父事务。
	 */

	switch (s->blockState)
	{
		case TBLOCK_DEFAULT:
			if (s->state == TRANS_DEFAULT)
			{
				/* we are idle, so nothing to do */
			}
			else
			{
				/*
				 * We can get here after an error during transaction start
				 * (state will be TRANS_START).  Need to clean up the
				 * incompletely started transaction.  First, adjust the
				 * low-level state to suppress warning message from
				 * AbortTransaction.
				 */
				if (s->state == TRANS_START)
					s->state = TRANS_INPROGRESS;
				AbortTransaction();
				CleanupTransaction();
			}
			break;

			/*
			 * If we aren't in a transaction block, we just do the basic abort
			 * & cleanup transaction.  For this purpose, we treat an implicit
			 * transaction block as if it were a simple statement.
			 */
		case TBLOCK_STARTED:
		case TBLOCK_IMPLICIT_INPROGRESS:
			AbortTransaction();
			CleanupTransaction();
			s->blockState = TBLOCK_DEFAULT;
			break;

			/*
			 * If we are in TBLOCK_BEGIN it means something screwed up right
			 * after reading "BEGIN TRANSACTION".  We assume that the user
			 * will interpret the error as meaning the BEGIN failed to get him
			 * into a transaction block, so we should abort and return to idle
			 * state.
			 */
		case TBLOCK_BEGIN:
			AbortTransaction();
			CleanupTransaction();
			s->blockState = TBLOCK_DEFAULT;
			break;

			/*
			 * We are somewhere in a transaction block and we've gotten a
			 * failure, so we abort the transaction and set up the persistent
			 * ABORT state.  We will stay in ABORT until we get a ROLLBACK.
			 */
		case TBLOCK_INPROGRESS:
		case TBLOCK_PARALLEL_INPROGRESS:
			AbortTransaction();
			s->blockState = TBLOCK_ABORT;
			/* CleanupTransaction happens when we exit TBLOCK_ABORT_END */
			break;

			/*
			 * Here, we failed while trying to COMMIT.  Clean up the
			 * transaction and return to idle state (we do not want to stay in
			 * the transaction).
			 */
		case TBLOCK_END:
			AbortTransaction();
			CleanupTransaction();
			s->blockState = TBLOCK_DEFAULT;
			break;

			/*
			 * Here, we are already in an aborted transaction state and are
			 * waiting for a ROLLBACK, but for some reason we failed again! So
			 * we just remain in the abort state.
			 */
		case TBLOCK_ABORT:
		case TBLOCK_SUBABORT:
			break;

			/*
			 * We are in a failed transaction and we got the ROLLBACK command.
			 * We have already aborted, we just need to cleanup and go to idle
			 * state.
			 */
		case TBLOCK_ABORT_END:
			CleanupTransaction();
			s->blockState = TBLOCK_DEFAULT;
			break;

			/*
			 * We are in a live transaction and we got a ROLLBACK command.
			 * Abort, cleanup, go to idle state.
			 */
		case TBLOCK_ABORT_PENDING:
			AbortTransaction();
			CleanupTransaction();
			s->blockState = TBLOCK_DEFAULT;
			break;

			/*
			 * Here, we failed while trying to PREPARE.  Clean up the
			 * transaction and return to idle state (we do not want to stay in
			 * the transaction).
			 */
		case TBLOCK_PREPARE:
			AbortTransaction();
			CleanupTransaction();
			s->blockState = TBLOCK_DEFAULT;
			break;

			/*
			 * We got an error inside a subtransaction.  Abort just the
			 * subtransaction, and go to the persistent SUBABORT state until
			 * we get ROLLBACK.
			 */
		case TBLOCK_SUBINPROGRESS:
			AbortSubTransaction();
			s->blockState = TBLOCK_SUBABORT;
			break;

			/*
			 * If we failed while trying to create a subtransaction, clean up
			 * the broken subtransaction and abort the parent.  The same
			 * applies if we get a failure while ending a subtransaction.  As
			 * we need to abort the parent, return false to request the caller
			 * to do the next iteration.
			 */
		case TBLOCK_SUBBEGIN:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
			AbortSubTransaction();
			CleanupSubTransaction();
			return false;

			/*
			 * Same as above, except the Abort() was already done.
			 */
		case TBLOCK_SUBABORT_END:
		case TBLOCK_SUBABORT_RESTART:
			CleanupSubTransaction();
			return false;
	}

	/* Done, no more iterations required */
	return true;
}

/*
 *	PreventInTransactionBlock
 *
 *	This routine is to be called by statements that must not run inside
 *	a transaction block, typically because they have non-rollback-able
 *	side effects or do internal commits.
 *
 *	If this routine completes successfully, then the calling statement is
 *	guaranteed that if it completes without error, its results will be
 *	committed immediately.
 *
 *	If we have already started a transaction block, issue an error; also issue
 *	an error if we appear to be running inside a user-defined function (which
 *	could issue more commands and possibly cause a failure after the statement
 *	completes).  Subtransactions are verboten too.
 *
 *	We must also set XACT_FLAGS_NEEDIMMEDIATECOMMIT in MyXactFlags, to ensure
 *	that postgres.c follows through by committing after the statement is done.
 *
 *	isTopLevel: passed down from ProcessUtility to determine whether we are
 *	inside a function.  (We will always fail if this is false, but it's
 *	convenient to centralize the check here instead of making callers do it.)
 *	stmtType: statement type name, for error messages.
 */
/*
 * 中文注释：
 * 供不能在事务块中执行的语句调用（这类语句通常有不可回滚的副作用或需要内部提交）。若已处于事务块、
 * 用户定义函数或子事务中则报错；成功返回即可保证语句完成后立即提交。
 */
void
PreventInTransactionBlock(bool isTopLevel, const char *stmtType)
{
	/*
	 * xact block already started?
	 */
	if (IsTransactionBlock())
		ereport(ERROR,
				(errcode(ERRCODE_ACTIVE_SQL_TRANSACTION),
		/* translator: %s represents an SQL statement name */
				 errmsg("%s cannot run inside a transaction block",
						stmtType)));

	/*
	 * subtransaction?
	 */
	if (IsSubTransaction())
		ereport(ERROR,
				(errcode(ERRCODE_ACTIVE_SQL_TRANSACTION),
		/* translator: %s represents an SQL statement name */
				 errmsg("%s cannot run inside a subtransaction",
						stmtType)));

	/*
	 * inside a function call?
	 */
	if (!isTopLevel)
		ereport(ERROR,
				(errcode(ERRCODE_ACTIVE_SQL_TRANSACTION),
		/* translator: %s represents an SQL statement name */
				 errmsg("%s cannot be executed from a function or procedure",
						stmtType)));

	/* If we got past IsTransactionBlock test, should be in default state */
	if (CurrentTransactionState->blockState != TBLOCK_DEFAULT &&
		CurrentTransactionState->blockState != TBLOCK_STARTED)
		elog(FATAL, "cannot prevent transaction chain");

	/* All okay.  Set the flag to make sure the right thing happens later. */
	MyXactFlags |= XACT_FLAGS_NEEDIMMEDIATECOMMIT;
}

/*
 *	WarnNoTransactionBlock
 *	RequireTransactionBlock
 *
 *	These two functions allow for warnings or errors if a command is executed
 *	outside of a transaction block.  This is useful for commands that have no
 *	effects that persist past transaction end (and so calling them outside a
 *	transaction block is presumably an error).  DECLARE CURSOR is an example.
 *	While top-level transaction control commands (BEGIN/COMMIT/ABORT) and SET
 *	that have no effect issue warnings, all other no-effect commands generate
 *	errors.
 *
 *	If we appear to be running inside a user-defined function, we do not
 *	issue anything, since the function could issue more commands that make
 *	use of the current statement's results.  Likewise subtransactions.
 *	Thus these are inverses for PreventInTransactionBlock.
 *
 *	isTopLevel: passed down from ProcessUtility to determine whether we are
 *	inside a function.
 *	stmtType: statement type name, for warning or error messages.
 */
/*
 * 中文注释：
 * 若当前不在事务块中则发出警告；用于在事务块外执行没有持久效果的语句（如 DECLARE CURSOR）。
 */
void
WarnNoTransactionBlock(bool isTopLevel, const char *stmtType)
{
	CheckTransactionBlock(isTopLevel, false, stmtType);
}

/*
 * 中文注释：
 * 若当前不在事务块中则报错；用于必须在事务块内执行的语句。
 */
void
RequireTransactionBlock(bool isTopLevel, const char *stmtType)
{
	CheckTransactionBlock(isTopLevel, true, stmtType);
}

/*
 * This is the implementation of the above two.
 */
/*
 * 中文注释：
 * WarnNoTransactionBlock 和 RequireTransactionBlock 的共同实现。
 */
static void
CheckTransactionBlock(bool isTopLevel, bool throwError, const char *stmtType)
{
	/*
	 * xact block already started?
	 */
	if (IsTransactionBlock())
		return;

	/*
	 * subtransaction?
	 */
	if (IsSubTransaction())
		return;

	/*
	 * inside a function call?
	 */
	if (!isTopLevel)
		return;

	ereport(throwError ? ERROR : WARNING,
			(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
	/* translator: %s represents an SQL statement name */
			 errmsg("%s can only be used in transaction blocks",
					stmtType)));
}

/*
 *	IsInTransactionBlock
 *
 *	This routine is for statements that need to behave differently inside
 *	a transaction block than when running as single commands.  ANALYZE is
 *	currently the only example.
 *
 *	If this routine returns "false", then the calling statement is allowed
 *	to perform internal transaction-commit-and-start cycles; there is not a
 *	risk of messing up any transaction already in progress.  (Note that this
 *	is not the identical guarantee provided by PreventInTransactionBlock,
 *	since we will not force a post-statement commit.)
 *
 *	isTopLevel: passed down from ProcessUtility to determine whether we are
 *	inside a function.
 */
/*
 * 中文注释：
 * 判断当前是否位于事务块中。需要区分“事务块内执行”和“单条命令执行”行为的语句（如 ANALYZE）使用它。
 */
bool
IsInTransactionBlock(bool isTopLevel)
{
	/*
	 * Return true on same conditions that would make
	 * PreventInTransactionBlock error out
	 */
	if (IsTransactionBlock())
		return true;

	if (IsSubTransaction())
		return true;

	if (!isTopLevel)
		return true;

	if (CurrentTransactionState->blockState != TBLOCK_DEFAULT &&
		CurrentTransactionState->blockState != TBLOCK_STARTED)
		return true;

	return false;
}


/*
 * Register or deregister callback functions for start- and end-of-xact
 * operations.
 *
 * These functions are intended for use by dynamically loaded modules.
 * For built-in modules we generally just hardwire the appropriate calls
 * (mainly because it's easier to control the order that way, where needed).
 *
 * At transaction end, the callback occurs post-commit or post-abort, so the
 * callback functions can only do noncritical cleanup.
 */
/*
 * 中文注释：
 * 注册事务开始/结束回调。主要供动态加载模块使用；回调在提交或中止之后执行，因此只能做非关键清理。
 */
void
RegisterXactCallback(XactCallback callback, void *arg)
{
	XactCallbackItem *item;

	item = (XactCallbackItem *)
		MemoryContextAlloc(TopMemoryContext, sizeof(XactCallbackItem));
	item->callback = callback;
	item->arg = arg;
	item->next = Xact_callbacks;
	Xact_callbacks = item;
}

/*
 * 中文注释：
 * 注销之前注册的事务回调。
 */
void
UnregisterXactCallback(XactCallback callback, void *arg)
{
	XactCallbackItem *item;
	XactCallbackItem *prev;

	prev = NULL;
	for (item = Xact_callbacks; item; prev = item, item = item->next)
	{
		if (item->callback == callback && item->arg == arg)
		{
			if (prev)
				prev->next = item->next;
			else
				Xact_callbacks = item->next;
			pfree(item);
			break;
		}
	}
}

/*
 * 中文注释：
 * 按注册顺序调用所有事务回调，通知当前事务事件（开始、预提交、提交、中止等）。
 */
static void
CallXactCallbacks(XactEvent event)
{
	XactCallbackItem *item;
	XactCallbackItem *next;

	for (item = Xact_callbacks; item; item = next)
	{
		/* allow callbacks to unregister themselves when called */
		next = item->next;
		item->callback(event, item->arg);
	}
}


/*
 * Register or deregister callback functions for start- and end-of-subxact
 * operations.
 *
 * Pretty much same as above, but for subtransaction events.
 *
 * At subtransaction end, the callback occurs post-subcommit or post-subabort,
 * so the callback functions can only do noncritical cleanup.  At
 * subtransaction start, the callback is called when the subtransaction has
 * finished initializing.
 */
/*
 * 中文注释：
 * 注册子事务开始/结束回调。
 */
void
RegisterSubXactCallback(SubXactCallback callback, void *arg)
{
	SubXactCallbackItem *item;

	item = (SubXactCallbackItem *)
		MemoryContextAlloc(TopMemoryContext, sizeof(SubXactCallbackItem));
	item->callback = callback;
	item->arg = arg;
	item->next = SubXact_callbacks;
	SubXact_callbacks = item;
}

/*
 * 中文注释：
 * 注销之前注册的子事务回调。
 */
void
UnregisterSubXactCallback(SubXactCallback callback, void *arg)
{
	SubXactCallbackItem *item;
	SubXactCallbackItem *prev;

	prev = NULL;
	for (item = SubXact_callbacks; item; prev = item, item = item->next)
	{
		if (item->callback == callback && item->arg == arg)
		{
			if (prev)
				prev->next = item->next;
			else
				SubXact_callbacks = item->next;
			pfree(item);
			break;
		}
	}
}

/*
 * 中文注释：
 * 调用所有子事务回调，通知子事务事件（开始、提交、中止等）。
 */
static void
CallSubXactCallbacks(SubXactEvent event,
					 SubTransactionId mySubid,
					 SubTransactionId parentSubid)
{
	SubXactCallbackItem *item;
	SubXactCallbackItem *next;

	for (item = SubXact_callbacks; item; item = next)
	{
		/* allow callbacks to unregister themselves when called */
		next = item->next;
		item->callback(event, mySubid, parentSubid, item->arg);
	}
}


/* ----------------------------------------------------------------
 *					   transaction block support
 *	（中文）事务块支持：BEGIN/COMMIT/ROLLBACK、保存点以及事务块状态查询等用户级操作。
 * ----------------------------------------------------------------
 */

/*
 *	BeginTransactionBlock
 *		This executes a BEGIN command.
 */
/*
 * 中文注释：
 * 执行 BEGIN 命令：把 blockState 从 TBLOCK_STARTED/TBLOCK_IMPLICIT_INPROGRESS 切到 TBLOCK_BEGIN，实
 * 际事务启动由后续 StartTransactionCommand/CommitTransactionCommand 完成。
 */
void
BeginTransactionBlock(void)
{
	TransactionState s = CurrentTransactionState;

	switch (s->blockState)
	{
			/*
			 * We are not inside a transaction block, so allow one to begin.
			 */
		case TBLOCK_STARTED:
			s->blockState = TBLOCK_BEGIN;
			break;

			/*
			 * BEGIN converts an implicit transaction block to a regular one.
			 * (Note that we allow this even if we've already done some
			 * commands, which is a bit odd but matches historical practice.)
			 */
		case TBLOCK_IMPLICIT_INPROGRESS:
			s->blockState = TBLOCK_BEGIN;
			break;

			/*
			 * Already a transaction block in progress.
			 */
		case TBLOCK_INPROGRESS:
		case TBLOCK_PARALLEL_INPROGRESS:
		case TBLOCK_SUBINPROGRESS:
		case TBLOCK_ABORT:
		case TBLOCK_SUBABORT:
			ereport(WARNING,
					(errcode(ERRCODE_ACTIVE_SQL_TRANSACTION),
					 errmsg("there is already a transaction in progress")));
			break;

			/* These cases are invalid. */
		case TBLOCK_DEFAULT:
		case TBLOCK_BEGIN:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
		case TBLOCK_PREPARE:
			elog(FATAL, "BeginTransactionBlock: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}
}

/*
 *	PrepareTransactionBlock
 *		This executes a PREPARE command.
 *
 * Since PREPARE may actually do a ROLLBACK, the result indicates what
 * happened: true for PREPARE, false for ROLLBACK.
 *
 * Note that we don't actually do anything here except change blockState.
 * The real work will be done in the upcoming PrepareTransaction().
 * We do it this way because it's not convenient to change memory context,
 * resource owner, etc while executing inside a Portal.
 */
/*
 * 中文注释：
 * 执行 PREPARE TRANSACTION 命令：先按 COMMIT 处理，再把顶层 blockState 改为 TBLOCK_PREPARE，并保存
 * GID。真正工作由随后的 PrepareTransaction() 完成；返回 true 表示 PREPARE，false 表示实际执行了回滚。
 */
bool
PrepareTransactionBlock(const char *gid)
{
	TransactionState s;
	bool		result;

	/* Set up to commit the current transaction */
	result = EndTransactionBlock(false);

	/* If successful, change outer tblock state to PREPARE */
	if (result)
	{
		s = CurrentTransactionState;

		while (s->parent != NULL)
			s = s->parent;

		if (s->blockState == TBLOCK_END)
		{
			/* Save GID where PrepareTransaction can find it again */
			prepareGID = MemoryContextStrdup(TopTransactionContext, gid);

			s->blockState = TBLOCK_PREPARE;
		}
		else
		{
			/*
			 * ignore case where we are not in a transaction;
			 * EndTransactionBlock already issued a warning.
			 */
			Assert(s->blockState == TBLOCK_STARTED ||
				   s->blockState == TBLOCK_IMPLICIT_INPROGRESS);
			/* Don't send back a PREPARE result tag... */
			result = false;
		}
	}

	return result;
}

/*
 *	EndTransactionBlock
 *		This executes a COMMIT command.
 *
 * Since COMMIT may actually do a ROLLBACK, the result indicates what
 * happened: true for COMMIT, false for ROLLBACK.
 *
 * Note that we don't actually do anything here except change blockState.
 * The real work will be done in the upcoming CommitTransactionCommand().
 * We do it this way because it's not convenient to change memory context,
 * resource owner, etc while executing inside a Portal.
 */
/*
 * 中文注释：
 * 执行 COMMIT 命令：只修改 blockState（顶层为 TBLOCK_END，子事务为 TBLOCK_SUBCOMMIT，失败事务为
 * TBLOCK_ABORT_END 等），真正提交由 CommitTransactionCommand 完成；返回 true 表示提交，false 表示回
 * 滚。
 */
bool
EndTransactionBlock(bool chain)
{
	TransactionState s = CurrentTransactionState;
	bool		result = false;

	switch (s->blockState)
	{
			/*
			 * We are in a transaction block, so tell CommitTransactionCommand
			 * to COMMIT.
			 */
		case TBLOCK_INPROGRESS:
			s->blockState = TBLOCK_END;
			result = true;
			break;

			/*
			 * We are in an implicit transaction block.  If AND CHAIN was
			 * specified, error.  Otherwise commit, but issue a warning
			 * because there was no explicit BEGIN before this.
			 */
		case TBLOCK_IMPLICIT_INPROGRESS:
			if (chain)
				ereport(ERROR,
						(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
				/* translator: %s represents an SQL statement name */
						 errmsg("%s can only be used in transaction blocks",
								"COMMIT AND CHAIN")));
			else
				ereport(WARNING,
						(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
						 errmsg("there is no transaction in progress")));
			s->blockState = TBLOCK_END;
			result = true;
			break;

			/*
			 * We are in a failed transaction block.  Tell
			 * CommitTransactionCommand it's time to exit the block.
			 */
		case TBLOCK_ABORT:
			s->blockState = TBLOCK_ABORT_END;
			break;

			/*
			 * We are in a live subtransaction block.  Set up to subcommit all
			 * open subtransactions and then commit the main transaction.
			 */
		case TBLOCK_SUBINPROGRESS:
			while (s->parent != NULL)
			{
				if (s->blockState == TBLOCK_SUBINPROGRESS)
					s->blockState = TBLOCK_SUBCOMMIT;
				else
					elog(FATAL, "EndTransactionBlock: unexpected state %s",
						 BlockStateAsString(s->blockState));
				s = s->parent;
			}
			if (s->blockState == TBLOCK_INPROGRESS)
				s->blockState = TBLOCK_END;
			else
				elog(FATAL, "EndTransactionBlock: unexpected state %s",
					 BlockStateAsString(s->blockState));
			result = true;
			break;

			/*
			 * Here we are inside an aborted subtransaction.  Treat the COMMIT
			 * as ROLLBACK: set up to abort everything and exit the main
			 * transaction.
			 */
		case TBLOCK_SUBABORT:
			while (s->parent != NULL)
			{
				if (s->blockState == TBLOCK_SUBINPROGRESS)
					s->blockState = TBLOCK_SUBABORT_PENDING;
				else if (s->blockState == TBLOCK_SUBABORT)
					s->blockState = TBLOCK_SUBABORT_END;
				else
					elog(FATAL, "EndTransactionBlock: unexpected state %s",
						 BlockStateAsString(s->blockState));
				s = s->parent;
			}
			if (s->blockState == TBLOCK_INPROGRESS)
				s->blockState = TBLOCK_ABORT_PENDING;
			else if (s->blockState == TBLOCK_ABORT)
				s->blockState = TBLOCK_ABORT_END;
			else
				elog(FATAL, "EndTransactionBlock: unexpected state %s",
					 BlockStateAsString(s->blockState));
			break;

			/*
			 * The user issued COMMIT when not inside a transaction.  For
			 * COMMIT without CHAIN, issue a WARNING, staying in
			 * TBLOCK_STARTED state.  The upcoming call to
			 * CommitTransactionCommand() will then close the transaction and
			 * put us back into the default state.  For COMMIT AND CHAIN,
			 * error.
			 */
		case TBLOCK_STARTED:
			if (chain)
				ereport(ERROR,
						(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
				/* translator: %s represents an SQL statement name */
						 errmsg("%s can only be used in transaction blocks",
								"COMMIT AND CHAIN")));
			else
				ereport(WARNING,
						(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
						 errmsg("there is no transaction in progress")));
			result = true;
			break;

			/*
			 * The user issued a COMMIT that somehow ran inside a parallel
			 * worker.  We can't cope with that.
			 */
		case TBLOCK_PARALLEL_INPROGRESS:
			ereport(FATAL,
					(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
					 errmsg("cannot commit during a parallel operation")));
			break;

			/* These cases are invalid. */
		case TBLOCK_DEFAULT:
		case TBLOCK_BEGIN:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
		case TBLOCK_PREPARE:
			elog(FATAL, "EndTransactionBlock: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}

	Assert(s->blockState == TBLOCK_STARTED ||
		   s->blockState == TBLOCK_END ||
		   s->blockState == TBLOCK_ABORT_END ||
		   s->blockState == TBLOCK_ABORT_PENDING);

	s->chain = chain;

	return result;
}

/*
 *	UserAbortTransactionBlock
 *		This executes a ROLLBACK command.
 *
 * As above, we don't actually do anything here except change blockState.
 */
/*
 * 中文注释：
 * 执行 ROLLBACK 命令：只把 blockState 标记为待中止/待清理状态，真正回滚由 CommitTransactionCommand
 * 完成。
 */
void
UserAbortTransactionBlock(bool chain)
{
	TransactionState s = CurrentTransactionState;

	switch (s->blockState)
	{
			/*
			 * We are inside a transaction block and we got a ROLLBACK command
			 * from the user, so tell CommitTransactionCommand to abort and
			 * exit the transaction block.
			 */
		case TBLOCK_INPROGRESS:
			s->blockState = TBLOCK_ABORT_PENDING;
			break;

			/*
			 * We are inside a failed transaction block and we got a ROLLBACK
			 * command from the user.  Abort processing is already done, so
			 * CommitTransactionCommand just has to cleanup and go back to
			 * idle state.
			 */
		case TBLOCK_ABORT:
			s->blockState = TBLOCK_ABORT_END;
			break;

			/*
			 * We are inside a subtransaction.  Mark everything up to top
			 * level as exitable.
			 */
		case TBLOCK_SUBINPROGRESS:
		case TBLOCK_SUBABORT:
			while (s->parent != NULL)
			{
				if (s->blockState == TBLOCK_SUBINPROGRESS)
					s->blockState = TBLOCK_SUBABORT_PENDING;
				else if (s->blockState == TBLOCK_SUBABORT)
					s->blockState = TBLOCK_SUBABORT_END;
				else
					elog(FATAL, "UserAbortTransactionBlock: unexpected state %s",
						 BlockStateAsString(s->blockState));
				s = s->parent;
			}
			if (s->blockState == TBLOCK_INPROGRESS)
				s->blockState = TBLOCK_ABORT_PENDING;
			else if (s->blockState == TBLOCK_ABORT)
				s->blockState = TBLOCK_ABORT_END;
			else
				elog(FATAL, "UserAbortTransactionBlock: unexpected state %s",
					 BlockStateAsString(s->blockState));
			break;

			/*
			 * The user issued ABORT when not inside a transaction.  For
			 * ROLLBACK without CHAIN, issue a WARNING and go to abort state.
			 * The upcoming call to CommitTransactionCommand() will then put
			 * us back into the default state.  For ROLLBACK AND CHAIN, error.
			 *
			 * We do the same thing with ABORT inside an implicit transaction,
			 * although in this case we might be rolling back actual database
			 * state changes.  (It's debatable whether we should issue a
			 * WARNING in this case, but we have done so historically.)
			 */
		case TBLOCK_STARTED:
		case TBLOCK_IMPLICIT_INPROGRESS:
			if (chain)
				ereport(ERROR,
						(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
				/* translator: %s represents an SQL statement name */
						 errmsg("%s can only be used in transaction blocks",
								"ROLLBACK AND CHAIN")));
			else
				ereport(WARNING,
						(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
						 errmsg("there is no transaction in progress")));
			s->blockState = TBLOCK_ABORT_PENDING;
			break;

			/*
			 * The user issued an ABORT that somehow ran inside a parallel
			 * worker.  We can't cope with that.
			 */
		case TBLOCK_PARALLEL_INPROGRESS:
			ereport(FATAL,
					(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
					 errmsg("cannot abort during a parallel operation")));
			break;

			/* These cases are invalid. */
		case TBLOCK_DEFAULT:
		case TBLOCK_BEGIN:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
		case TBLOCK_PREPARE:
			elog(FATAL, "UserAbortTransactionBlock: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}

	Assert(s->blockState == TBLOCK_ABORT_END ||
		   s->blockState == TBLOCK_ABORT_PENDING);

	s->chain = chain;
}

/*
 * BeginImplicitTransactionBlock
 *		Start an implicit transaction block if we're not already in one.
 *
 * Unlike BeginTransactionBlock, this is called directly from the main loop
 * in postgres.c, not within a Portal.  So we can just change blockState
 * without a lot of ceremony.  We do not expect caller to do
 * CommitTransactionCommand/StartTransactionCommand.
 */
/*
 * 中文注释：
 * 在尚未进入事务块时启动隐式事务块（TBLOCK_IMPLICIT_INPROGRESS）。由 postgres.c 主循环直接调用，不
 * 在 Portal 内。
 */
void
BeginImplicitTransactionBlock(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * If we are in STARTED state (that is, no transaction block is open),
	 * switch to IMPLICIT_INPROGRESS state, creating an implicit transaction
	 * block.
	 *
	 * For caller convenience, we consider all other transaction states as
	 * legal here; otherwise the caller would need its own state check, which
	 * seems rather pointless.
	 */
	if (s->blockState == TBLOCK_STARTED)
		s->blockState = TBLOCK_IMPLICIT_INPROGRESS;
}

/*
 * EndImplicitTransactionBlock
 *		End an implicit transaction block, if we're in one.
 *
 * Like EndTransactionBlock, we just make any needed blockState change here.
 * The real work will be done in the upcoming CommitTransactionCommand().
 */
/*
 * 中文注释：
 * 结束隐式事务块，把状态改回 TBLOCK_STARTED，使 CommitTransactionCommand 像处理单条语句一样提交它。
 */
void
EndImplicitTransactionBlock(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * If we are in IMPLICIT_INPROGRESS state, switch back to STARTED state,
	 * allowing CommitTransactionCommand to commit whatever happened during
	 * the implicit transaction block as though it were a single statement.
	 *
	 * For caller convenience, we consider all other transaction states as
	 * legal here; otherwise the caller would need its own state check, which
	 * seems rather pointless.
	 */
	if (s->blockState == TBLOCK_IMPLICIT_INPROGRESS)
		s->blockState = TBLOCK_STARTED;
}

/*
 * DefineSavepoint
 *		This executes a SAVEPOINT command.
 */
/*
 * 中文注释：
 * 执行 SAVEPOINT 命令：检查并行模式限制，为当前事务压入一个新的子事务状态并记录保存点名称；子事务的
 * 实际初始化在 StartSubTransaction 完成。
 */
void
DefineSavepoint(const char *name)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * Workers synchronize transaction state at the beginning of each parallel
	 * operation, so we can't account for new subtransactions after that
	 * point.  (Note that this check will certainly error out if s->blockState
	 * is TBLOCK_PARALLEL_INPROGRESS, so we can treat that as an invalid case
	 * below.)
	 */
	if (IsInParallelMode() || IsParallelWorker())
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
				 errmsg("cannot define savepoints during a parallel operation")));

	switch (s->blockState)
	{
		case TBLOCK_INPROGRESS:
		case TBLOCK_SUBINPROGRESS:
			/* Normal subtransaction start */
			PushTransaction();
			s = CurrentTransactionState;	/* changed by push */

			/*
			 * Savepoint names, like the TransactionState block itself, live
			 * in TopTransactionContext.
			 */
			if (name)
				s->name = MemoryContextStrdup(TopTransactionContext, name);
			break;

			/*
			 * We disallow savepoint commands in implicit transaction blocks.
			 * There would be no great difficulty in allowing them so far as
			 * this module is concerned, but a savepoint seems inconsistent
			 * with exec_simple_query's behavior of abandoning the whole query
			 * string upon error.  Also, the point of an implicit transaction
			 * block (as opposed to a regular one) is to automatically close
			 * after an error, so it's hard to see how a savepoint would fit
			 * into that.
			 *
			 * The error messages for this are phrased as if there were no
			 * active transaction block at all, which is historical but
			 * perhaps could be improved.
			 */
		case TBLOCK_IMPLICIT_INPROGRESS:
			ereport(ERROR,
					(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
			/* translator: %s represents an SQL statement name */
					 errmsg("%s can only be used in transaction blocks",
							"SAVEPOINT")));
			break;

			/* These cases are invalid. */
		case TBLOCK_DEFAULT:
		case TBLOCK_STARTED:
		case TBLOCK_BEGIN:
		case TBLOCK_PARALLEL_INPROGRESS:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT:
		case TBLOCK_SUBABORT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
		case TBLOCK_PREPARE:
			elog(FATAL, "DefineSavepoint: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}
}

/*
 * ReleaseSavepoint
 *		This executes a RELEASE command.
 *
 * As above, we don't actually do anything here except change blockState.
 */
/*
 * 中文注释：
 * 执行 RELEASE SAVEPOINT：查找目标保存点，把从当前子事务到目标之间的所有子事务标记为
 * TBLOCK_SUBRELEASE，待 CommitTransactionCommand 统一提交。
 */
void
ReleaseSavepoint(const char *name)
{
	TransactionState s = CurrentTransactionState;
	TransactionState target,
				xact;

	/*
	 * Workers synchronize transaction state at the beginning of each parallel
	 * operation, so we can't account for transaction state change after that
	 * point.  (Note that this check will certainly error out if s->blockState
	 * is TBLOCK_PARALLEL_INPROGRESS, so we can treat that as an invalid case
	 * below.)
	 */
	if (IsInParallelMode() || IsParallelWorker())
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
				 errmsg("cannot release savepoints during a parallel operation")));

	switch (s->blockState)
	{
			/*
			 * We can't release a savepoint if there is no savepoint defined.
			 */
		case TBLOCK_INPROGRESS:
			ereport(ERROR,
					(errcode(ERRCODE_S_E_INVALID_SPECIFICATION),
					 errmsg("savepoint \"%s\" does not exist", name)));
			break;

		case TBLOCK_IMPLICIT_INPROGRESS:
			/* See comment about implicit transactions in DefineSavepoint */
			ereport(ERROR,
					(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
			/* translator: %s represents an SQL statement name */
					 errmsg("%s can only be used in transaction blocks",
							"RELEASE SAVEPOINT")));
			break;

			/*
			 * We are in a non-aborted subtransaction.  This is the only valid
			 * case.
			 */
		case TBLOCK_SUBINPROGRESS:
			break;

			/* These cases are invalid. */
		case TBLOCK_DEFAULT:
		case TBLOCK_STARTED:
		case TBLOCK_BEGIN:
		case TBLOCK_PARALLEL_INPROGRESS:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT:
		case TBLOCK_SUBABORT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
		case TBLOCK_PREPARE:
			elog(FATAL, "ReleaseSavepoint: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}

	for (target = s; target; target = target->parent)
	{
		if (target->name && strcmp(target->name, name) == 0)
			break;
	}

	if (!target)
		ereport(ERROR,
				(errcode(ERRCODE_S_E_INVALID_SPECIFICATION),
				 errmsg("savepoint \"%s\" does not exist", name)));

	/* disallow crossing savepoint level boundaries */
	if (target->savepointLevel != s->savepointLevel)
		ereport(ERROR,
				(errcode(ERRCODE_S_E_INVALID_SPECIFICATION),
				 errmsg("savepoint \"%s\" does not exist within current savepoint level", name)));

	/*
	 * Mark "commit pending" all subtransactions up to the target
	 * subtransaction.  The actual commits will happen when control gets to
	 * CommitTransactionCommand.
	 */
	xact = CurrentTransactionState;
	for (;;)
	{
		Assert(xact->blockState == TBLOCK_SUBINPROGRESS);
		xact->blockState = TBLOCK_SUBRELEASE;
		if (xact == target)
			break;
		xact = xact->parent;
		Assert(xact);
	}
}

/*
 * RollbackToSavepoint
 *		This executes a ROLLBACK TO <savepoint> command.
 *
 * As above, we don't actually do anything here except change blockState.
 */
/*
 * 中文注释：
 * 执行 ROLLBACK TO SAVEPOINT：查找目标保存点，把其上的子事务标记为待中止，并把目标子事务标记为待重
 * 启；实际回滚与重建由 CommitTransactionCommand 完成。
 */
void
RollbackToSavepoint(const char *name)
{
	TransactionState s = CurrentTransactionState;
	TransactionState target,
				xact;

	/*
	 * Workers synchronize transaction state at the beginning of each parallel
	 * operation, so we can't account for transaction state change after that
	 * point.  (Note that this check will certainly error out if s->blockState
	 * is TBLOCK_PARALLEL_INPROGRESS, so we can treat that as an invalid case
	 * below.)
	 */
	if (IsInParallelMode() || IsParallelWorker())
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
				 errmsg("cannot rollback to savepoints during a parallel operation")));

	switch (s->blockState)
	{
			/*
			 * We can't rollback to a savepoint if there is no savepoint
			 * defined.
			 */
		case TBLOCK_INPROGRESS:
		case TBLOCK_ABORT:
			ereport(ERROR,
					(errcode(ERRCODE_S_E_INVALID_SPECIFICATION),
					 errmsg("savepoint \"%s\" does not exist", name)));
			break;

		case TBLOCK_IMPLICIT_INPROGRESS:
			/* See comment about implicit transactions in DefineSavepoint */
			ereport(ERROR,
					(errcode(ERRCODE_NO_ACTIVE_SQL_TRANSACTION),
			/* translator: %s represents an SQL statement name */
					 errmsg("%s can only be used in transaction blocks",
							"ROLLBACK TO SAVEPOINT")));
			break;

			/*
			 * There is at least one savepoint, so proceed.
			 */
		case TBLOCK_SUBINPROGRESS:
		case TBLOCK_SUBABORT:
			break;

			/* These cases are invalid. */
		case TBLOCK_DEFAULT:
		case TBLOCK_STARTED:
		case TBLOCK_BEGIN:
		case TBLOCK_PARALLEL_INPROGRESS:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
		case TBLOCK_PREPARE:
			elog(FATAL, "RollbackToSavepoint: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}

	for (target = s; target; target = target->parent)
	{
		if (target->name && strcmp(target->name, name) == 0)
			break;
	}

	if (!target)
		ereport(ERROR,
				(errcode(ERRCODE_S_E_INVALID_SPECIFICATION),
				 errmsg("savepoint \"%s\" does not exist", name)));

	/* disallow crossing savepoint level boundaries */
	if (target->savepointLevel != s->savepointLevel)
		ereport(ERROR,
				(errcode(ERRCODE_S_E_INVALID_SPECIFICATION),
				 errmsg("savepoint \"%s\" does not exist within current savepoint level", name)));

	/*
	 * Mark "abort pending" all subtransactions up to the target
	 * subtransaction.  The actual aborts will happen when control gets to
	 * CommitTransactionCommand.
	 */
	xact = CurrentTransactionState;
	for (;;)
	{
		if (xact == target)
			break;
		if (xact->blockState == TBLOCK_SUBINPROGRESS)
			xact->blockState = TBLOCK_SUBABORT_PENDING;
		else if (xact->blockState == TBLOCK_SUBABORT)
			xact->blockState = TBLOCK_SUBABORT_END;
		else
			elog(FATAL, "RollbackToSavepoint: unexpected state %s",
				 BlockStateAsString(xact->blockState));
		xact = xact->parent;
		Assert(xact);
	}

	/* And mark the target as "restart pending" */
	if (xact->blockState == TBLOCK_SUBINPROGRESS)
		xact->blockState = TBLOCK_SUBRESTART;
	else if (xact->blockState == TBLOCK_SUBABORT)
		xact->blockState = TBLOCK_SUBABORT_RESTART;
	else
		elog(FATAL, "RollbackToSavepoint: unexpected state %s",
			 BlockStateAsString(xact->blockState));
}

/*
 * BeginInternalSubTransaction
 *		This is the same as DefineSavepoint except it allows TBLOCK_STARTED,
 *		TBLOCK_IMPLICIT_INPROGRESS, TBLOCK_PARALLEL_INPROGRESS, TBLOCK_END,
 *		and TBLOCK_PREPARE states, and therefore it can safely be used in
 *		functions that might be called when not inside a BEGIN block or when
 *		running deferred triggers at COMMIT/PREPARE time.  Also, it
 *		automatically does CommitTransactionCommand/StartTransactionCommand
 *		instead of expecting the caller to do it.
 */
/*
 * 中文注释：
 * 内部使用的子事务启动函数。与 DefineSavepoint 类似，但允许在 TBLOCK_STARTED、隐式事务、并行 worker、COMMIT/PREPARE 等状态下调用，适合函数内以及 COMMIT 时触发的延迟触发器使用；它会自动执行
 * CommitTransactionCommand/StartTransactionCommand。
 */
void
BeginInternalSubTransaction(const char *name)
{
	TransactionState s = CurrentTransactionState;
	bool		save_ExitOnAnyError = ExitOnAnyError;

	/*
	 * Errors within this function are improbable, but if one does happen we
	 * force a FATAL exit.  Callers generally aren't prepared to handle losing
	 * control, and moreover our transaction state is probably corrupted if we
	 * fail partway through; so an ordinary ERROR longjmp isn't okay.
	 */
	ExitOnAnyError = true;

	/*
	 * We do not check for parallel mode here.  It's permissible to start and
	 * end "internal" subtransactions while in parallel mode, so long as no
	 * new XIDs or command IDs are assigned.  Enforcement of that occurs in
	 * AssignTransactionId() and CommandCounterIncrement().
	 */

	switch (s->blockState)
	{
		case TBLOCK_STARTED:
		case TBLOCK_INPROGRESS:
		case TBLOCK_IMPLICIT_INPROGRESS:
		case TBLOCK_PARALLEL_INPROGRESS:
		case TBLOCK_END:
		case TBLOCK_PREPARE:
		case TBLOCK_SUBINPROGRESS:
			/* Normal subtransaction start */
			PushTransaction();
			s = CurrentTransactionState;	/* changed by push */

			/*
			 * Savepoint names, like the TransactionState block itself, live
			 * in TopTransactionContext.
			 */
			if (name)
				s->name = MemoryContextStrdup(TopTransactionContext, name);
			break;

			/* These cases are invalid. */
		case TBLOCK_DEFAULT:
		case TBLOCK_BEGIN:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT:
		case TBLOCK_SUBABORT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
			elog(FATAL, "BeginInternalSubTransaction: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}

	CommitTransactionCommand();
	StartTransactionCommand();

	ExitOnAnyError = save_ExitOnAnyError;
}

/*
 * ReleaseCurrentSubTransaction
 *
 * RELEASE (ie, commit) the innermost subtransaction, regardless of its
 * savepoint name (if any).
 * NB: do NOT use CommitTransactionCommand/StartTransactionCommand with this.
 */
/*
 * 中文注释：
 * 提交（RELEASE）最内层子事务，不依赖保存点名称。调用者不要同时使用
 * CommitTransactionCommand/StartTransactionCommand。
 */
void
ReleaseCurrentSubTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * We do not check for parallel mode here.  It's permissible to start and
	 * end "internal" subtransactions while in parallel mode, so long as no
	 * new XIDs or command IDs are assigned.
	 */

	if (s->blockState != TBLOCK_SUBINPROGRESS)
		elog(ERROR, "ReleaseCurrentSubTransaction: unexpected state %s",
			 BlockStateAsString(s->blockState));
	Assert(s->state == TRANS_INPROGRESS);
	MemoryContextSwitchTo(CurTransactionContext);
	CommitSubTransaction();
	s = CurrentTransactionState;	/* changed by pop */
	Assert(s->state == TRANS_INPROGRESS);
}

/*
 * RollbackAndReleaseCurrentSubTransaction
 *
 * ROLLBACK and RELEASE (ie, abort) the innermost subtransaction, regardless
 * of its savepoint name (if any).
 * NB: do NOT use CommitTransactionCommand/StartTransactionCommand with this.
 */
/*
 * 中文注释：
 * 中止并释放最内层子事务，不依赖保存点名称。调用者不要同时使用
 * CommitTransactionCommand/StartTransactionCommand。
 */
void
RollbackAndReleaseCurrentSubTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	/*
	 * We do not check for parallel mode here.  It's permissible to start and
	 * end "internal" subtransactions while in parallel mode, so long as no
	 * new XIDs or command IDs are assigned.
	 */

	switch (s->blockState)
	{
			/* Must be in a subtransaction */
		case TBLOCK_SUBINPROGRESS:
		case TBLOCK_SUBABORT:
			break;

			/* These cases are invalid. */
		case TBLOCK_DEFAULT:
		case TBLOCK_STARTED:
		case TBLOCK_BEGIN:
		case TBLOCK_IMPLICIT_INPROGRESS:
		case TBLOCK_PARALLEL_INPROGRESS:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_INPROGRESS:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_ABORT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
		case TBLOCK_PREPARE:
			elog(FATAL, "RollbackAndReleaseCurrentSubTransaction: unexpected state %s",
				 BlockStateAsString(s->blockState));
			break;
	}

	/*
	 * Abort the current subtransaction, if needed.
	 */
	if (s->blockState == TBLOCK_SUBINPROGRESS)
		AbortSubTransaction();

	/* And clean it up, too */
	CleanupSubTransaction();

	s = CurrentTransactionState;	/* changed by pop */
	Assert(s->blockState == TBLOCK_SUBINPROGRESS ||
		   s->blockState == TBLOCK_INPROGRESS ||
		   s->blockState == TBLOCK_IMPLICIT_INPROGRESS ||
		   s->blockState == TBLOCK_PARALLEL_INPROGRESS ||
		   s->blockState == TBLOCK_STARTED);
}

/*
 *	AbortOutOfAnyTransaction
 *
 *	This routine is provided for error recovery purposes.  It aborts any
 *	active transaction or transaction block, leaving the system in a known
 *	idle state.
 */
/*
 * 中文注释：
 * 错误恢复例程：中止任何活动事务或事务块，把系统恢复到已知的空闲状态。即使事务状态已损坏也应尽量可
 * 用。
 */
void
AbortOutOfAnyTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	/* Ensure we're not running in a doomed memory context */
	AtAbort_Memory();

	/*
	 * Get out of any transaction or nested transaction
	 */
	do
	{
		switch (s->blockState)
		{
			case TBLOCK_DEFAULT:
				if (s->state == TRANS_DEFAULT)
				{
					/* Not in a transaction, do nothing */
				}
				else
				{
					/*
					 * We can get here after an error during transaction start
					 * (state will be TRANS_START).  Need to clean up the
					 * incompletely started transaction.  First, adjust the
					 * low-level state to suppress warning message from
					 * AbortTransaction.
					 */
					if (s->state == TRANS_START)
						s->state = TRANS_INPROGRESS;
					AbortTransaction();
					CleanupTransaction();
				}
				break;
			case TBLOCK_STARTED:
			case TBLOCK_BEGIN:
			case TBLOCK_INPROGRESS:
			case TBLOCK_IMPLICIT_INPROGRESS:
			case TBLOCK_PARALLEL_INPROGRESS:
			case TBLOCK_END:
			case TBLOCK_ABORT_PENDING:
			case TBLOCK_PREPARE:
				/* In a transaction, so clean up */
				AbortTransaction();
				CleanupTransaction();
				s->blockState = TBLOCK_DEFAULT;
				break;
			case TBLOCK_ABORT:
			case TBLOCK_ABORT_END:

				/*
				 * AbortTransaction is already done, still need Cleanup.
				 * However, if we failed partway through running ROLLBACK,
				 * there will be an active portal running that command, which
				 * we need to shut down before doing CleanupTransaction.
				 */
				AtAbort_Portals();
				CleanupTransaction();
				s->blockState = TBLOCK_DEFAULT;
				break;

				/*
				 * In a subtransaction, so clean it up and abort parent too
				 */
			case TBLOCK_SUBBEGIN:
			case TBLOCK_SUBINPROGRESS:
			case TBLOCK_SUBRELEASE:
			case TBLOCK_SUBCOMMIT:
			case TBLOCK_SUBABORT_PENDING:
			case TBLOCK_SUBRESTART:
				AbortSubTransaction();
				CleanupSubTransaction();
				s = CurrentTransactionState;	/* changed by pop */
				break;

			case TBLOCK_SUBABORT:
			case TBLOCK_SUBABORT_END:
			case TBLOCK_SUBABORT_RESTART:
				/* As above, but AbortSubTransaction already done */
				if (s->curTransactionOwner)
				{
					/* As in TBLOCK_ABORT, might have a live portal to zap */
					AtSubAbort_Portals(s->subTransactionId,
									   s->parent->subTransactionId,
									   s->curTransactionOwner,
									   s->parent->curTransactionOwner);
				}
				CleanupSubTransaction();
				s = CurrentTransactionState;	/* changed by pop */
				break;
		}
	} while (s->blockState != TBLOCK_DEFAULT);

	/* Should be out of all subxacts now */
	Assert(s->parent == NULL);

	/*
	 * Revert to TopMemoryContext, to ensure we exit in a well-defined state
	 * whether there were any transactions to close or not.  (Callers that
	 * don't intend to exit soon should switch to some other context to avoid
	 * long-term memory leaks.)
	 */
	MemoryContextSwitchTo(TopMemoryContext);
}

/*
 * IsTransactionBlock --- are we within a transaction block?
 */
/*
 * 中文注释：
 * 判断当前是否处于事务块中。
 */
bool
IsTransactionBlock(void)
{
	TransactionState s = CurrentTransactionState;

	if (s->blockState == TBLOCK_DEFAULT || s->blockState == TBLOCK_STARTED)
		return false;

	return true;
}

/*
 * IsTransactionOrTransactionBlock --- are we within either a transaction
 * or a transaction block?	(The backend is only really "idle" when this
 * returns false.)
 *
 * This should match up with IsTransactionBlock and IsTransactionState.
 */
/*
 * 中文注释：
 * 判断当前是否处于事务中或事务块中；返回 false 表示后端真正空闲。
 */
bool
IsTransactionOrTransactionBlock(void)
{
	TransactionState s = CurrentTransactionState;

	if (s->blockState == TBLOCK_DEFAULT)
		return false;

	return true;
}

/*
 * TransactionBlockStatusCode - return status code to send in ReadyForQuery
 */
/*
 * 中文注释：
 * 返回 ReadyForQuery 消息中的事务状态码：'T' 表示在事务块中，'E' 表示处于失败事务中，'I' 表示空闲。
 */
char
TransactionBlockStatusCode(void)
{
	TransactionState s = CurrentTransactionState;

	switch (s->blockState)
	{
		case TBLOCK_DEFAULT:
		case TBLOCK_STARTED:
			return 'I';			/* idle --- not in transaction */
		case TBLOCK_BEGIN:
		case TBLOCK_SUBBEGIN:
		case TBLOCK_INPROGRESS:
		case TBLOCK_IMPLICIT_INPROGRESS:
		case TBLOCK_PARALLEL_INPROGRESS:
		case TBLOCK_SUBINPROGRESS:
		case TBLOCK_END:
		case TBLOCK_SUBRELEASE:
		case TBLOCK_SUBCOMMIT:
		case TBLOCK_PREPARE:
			return 'T';			/* in transaction */
		case TBLOCK_ABORT:
		case TBLOCK_SUBABORT:
		case TBLOCK_ABORT_END:
		case TBLOCK_SUBABORT_END:
		case TBLOCK_ABORT_PENDING:
		case TBLOCK_SUBABORT_PENDING:
		case TBLOCK_SUBRESTART:
		case TBLOCK_SUBABORT_RESTART:
			return 'E';			/* in failed transaction */
	}

	/* should never get here */
	elog(FATAL, "invalid transaction block state: %s",
		 BlockStateAsString(s->blockState));
	return 0;					/* keep compiler quiet */
}

/*
 * IsSubTransaction
 */
/*
 * 中文注释：
 * 判断当前是否处于子事务中（嵌套层级大于 1）。
 */
bool
IsSubTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	if (s->nestingLevel >= 2)
		return true;

	return false;
}

/*
 * StartSubTransaction
 *
 * If you're wondering why this is separate from PushTransaction: it's because
 * we can't conveniently do this stuff right inside DefineSavepoint.  The
 * SAVEPOINT utility command will be executed inside a Portal, and if we
 * muck with CurrentMemoryContext or CurrentResourceOwner then exit from
 * the Portal will undo those settings.  So we make DefineSavepoint just
 * push a dummy transaction block, and when control returns to the main
 * idle loop, CommitTransactionCommand will be called, and we'll come here
 * to finish starting the subtransaction.
 */
/*
 * 中文注释：
 * 完成子事务的启动。之所以与 PushTransaction 分开，是因为 SAVEPOINT 命令在 Portal 内执行，不能在
 * Portal 中切换内存上下文和资源所有者；等控制返回主循环后再在这里完成初始化。
 */
static void
StartSubTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	if (s->state != TRANS_DEFAULT)
		elog(WARNING, "StartSubTransaction while in %s state",
			 TransStateAsString(s->state));

	s->state = TRANS_START;

	/*
	 * Initialize subsystems for new subtransaction
	 *
	 * must initialize resource-management stuff first
	 */
	AtSubStart_Memory();
	AtSubStart_ResourceOwner();
	AfterTriggerBeginSubXact();

	s->state = TRANS_INPROGRESS;

	/*
	 * Call start-of-subxact callbacks
	 */
	CallSubXactCallbacks(SUBXACT_EVENT_START_SUB, s->subTransactionId,
						 s->parent->subTransactionId);

	ShowTransactionState("StartSubTransaction");
}

/*
 * CommitSubTransaction
 *
 *	The caller has to make sure to always reassign CurrentTransactionState
 *	if it has a local pointer to it after calling this function.
 */
/*
 * 中文注释：
 * 提交当前子事务：调用子事务提交回调，合并子事务资源到父事务，把 XID 上交给父事务，然后弹出状态栈。
 * 调用后必须重新获取 CurrentTransactionState。
 */
static void
CommitSubTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	ShowTransactionState("CommitSubTransaction");

	if (s->state != TRANS_INPROGRESS)
		elog(WARNING, "CommitSubTransaction while in %s state",
			 TransStateAsString(s->state));

	/* Pre-commit processing goes here */

	CallSubXactCallbacks(SUBXACT_EVENT_PRE_COMMIT_SUB, s->subTransactionId,
						 s->parent->subTransactionId);

	/*
	 * If this subxact has started any unfinished parallel operation, clean up
	 * its workers and exit parallel mode.  Warn about leaked resources.
	 */
	AtEOSubXact_Parallel(true, s->subTransactionId);
	if (s->parallelModeLevel != 0)
	{
		elog(WARNING, "parallelModeLevel is %d not 0 at end of subtransaction",
			 s->parallelModeLevel);
		s->parallelModeLevel = 0;
	}

	/* Do the actual "commit", such as it is */
	s->state = TRANS_COMMIT;

	/* Must CCI to ensure commands of subtransaction are seen as done */
	CommandCounterIncrement();

	/*
	 * Prior to 8.4 we marked subcommit in clog at this point.  We now only
	 * perform that step, if required, as part of the atomic update of the
	 * whole transaction tree at top level commit or abort.
	 */

	/* Post-commit cleanup */
	if (FullTransactionIdIsValid(s->fullTransactionId))
		AtSubCommit_childXids();
	AfterTriggerEndSubXact(true);
	AtSubCommit_Portals(s->subTransactionId,
						s->parent->subTransactionId,
						s->parent->nestingLevel,
						s->parent->curTransactionOwner);
	AtEOSubXact_LargeObject(true, s->subTransactionId,
							s->parent->subTransactionId);
	AtSubCommit_Notify();

	CallSubXactCallbacks(SUBXACT_EVENT_COMMIT_SUB, s->subTransactionId,
						 s->parent->subTransactionId);

	ResourceOwnerRelease(s->curTransactionOwner,
						 RESOURCE_RELEASE_BEFORE_LOCKS,
						 true, false);
	AtEOSubXact_RelationCache(true, s->subTransactionId,
							  s->parent->subTransactionId);
	AtEOSubXact_TypeCache();
	AtEOSubXact_Inval(true);
	AtSubCommit_smgr();

	/*
	 * The only lock we actually release here is the subtransaction XID lock.
	 */
	CurrentResourceOwner = s->curTransactionOwner;
	if (FullTransactionIdIsValid(s->fullTransactionId))
		XactLockTableDelete(XidFromFullTransactionId(s->fullTransactionId));

	/*
	 * Other locks should get transferred to their parent resource owner.
	 */
	ResourceOwnerRelease(s->curTransactionOwner,
						 RESOURCE_RELEASE_LOCKS,
						 true, false);
	ResourceOwnerRelease(s->curTransactionOwner,
						 RESOURCE_RELEASE_AFTER_LOCKS,
						 true, false);

	AtEOXact_GUC(true, s->gucNestLevel);
	AtEOSubXact_SPI(true, s->subTransactionId);
	AtEOSubXact_on_commit_actions(true, s->subTransactionId,
								  s->parent->subTransactionId);
	AtEOSubXact_Namespace(true, s->subTransactionId,
						  s->parent->subTransactionId);
	AtEOSubXact_Files(true, s->subTransactionId,
					  s->parent->subTransactionId);
	AtEOSubXact_HashTables(true, s->nestingLevel);
	AtEOSubXact_PgStat(true, s->nestingLevel);
	AtSubCommit_Snapshot(s->nestingLevel);

	/*
	 * We need to restore the upper transaction's read-only state, in case the
	 * upper is read-write while the child is read-only; GUC will incorrectly
	 * think it should leave the child state in place.
	 */
	XactReadOnly = s->prevXactReadOnly;

	CurrentResourceOwner = s->parent->curTransactionOwner;
	CurTransactionResourceOwner = s->parent->curTransactionOwner;
	ResourceOwnerDelete(s->curTransactionOwner);
	s->curTransactionOwner = NULL;

	AtSubCommit_Memory();

	s->state = TRANS_DEFAULT;

	PopTransaction();
}

/*
 * AbortSubTransaction
 */
/*
 * 中文注释：
 * 中止当前子事务：释放子事务资源、回滚其修改、清理状态并记录必要的中止信息，最后弹出状态栈。
 */
static void
AbortSubTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	/* Prevent cancel/die interrupt while cleaning up */
	HOLD_INTERRUPTS();

	/* Make sure we have a valid memory context and resource owner */
	AtSubAbort_Memory();
	AtSubAbort_ResourceOwner();

	/*
	 * Release any LW locks we might be holding as quickly as possible.
	 * (Regular locks, however, must be held till we finish aborting.)
	 * Releasing LW locks is critical since we might try to grab them again
	 * while cleaning up!
	 *
	 * FIXME This may be incorrect --- Are there some locks we should keep?
	 * Buffer locks, for example?  I don't think so but I'm not sure.
	 */
	LWLockReleaseAll();

	/*
	 * Cleanup waiting for LSN if any.
	 */
	WaitLSNCleanup();

	pgstat_report_wait_end();
	pgstat_progress_end_command();

	pgaio_error_cleanup();

	UnlockBuffers();

	/* Reset WAL record construction state */
	XLogResetInsertion();

	/* Cancel condition variable sleep */
	ConditionVariableCancelSleep();

	/*
	 * Also clean up any open wait for lock, since the lock manager will choke
	 * if we try to wait for another lock before doing this.
	 */
	LockErrorCleanup();

	/*
	 * If any timeout events are still active, make sure the timeout interrupt
	 * is scheduled.  This covers possible loss of a timeout interrupt due to
	 * longjmp'ing out of the SIGINT handler (see notes in handle_sig_alarm).
	 * We delay this till after LockErrorCleanup so that we don't uselessly
	 * reschedule lock or deadlock check timeouts.
	 */
	reschedule_timeouts();

	/*
	 * Re-enable signals, in case we got here by longjmp'ing out of a signal
	 * handler.  We do this fairly early in the sequence so that the timeout
	 * infrastructure will be functional if needed while aborting.
	 */
	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/*
	 * check the current transaction state
	 */
	ShowTransactionState("AbortSubTransaction");

	if (s->state != TRANS_INPROGRESS)
		elog(WARNING, "AbortSubTransaction while in %s state",
			 TransStateAsString(s->state));

	s->state = TRANS_ABORT;

	/*
	 * Reset user ID which might have been changed transiently.  (See notes in
	 * AbortTransaction.)
	 */
	SetUserIdAndSecContext(s->prevUser, s->prevSecContext);

	/* Forget about any active REINDEX. */
	ResetReindexState(s->nestingLevel);

	/* Reset logical streaming state. */
	ResetLogicalStreamingState();

	/*
	 * No need for SnapBuildResetExportedSnapshotState() here, snapshot
	 * exports are not supported in subtransactions.
	 */

	/*
	 * If this subxact has started any unfinished parallel operation, clean up
	 * its workers and exit parallel mode.  Don't warn about leaked resources.
	 */
	AtEOSubXact_Parallel(false, s->subTransactionId);
	s->parallelModeLevel = 0;

	/*
	 * We can skip all this stuff if the subxact failed before creating a
	 * ResourceOwner...
	 */
	if (s->curTransactionOwner)
	{
		AfterTriggerEndSubXact(false);
		AtSubAbort_Portals(s->subTransactionId,
						   s->parent->subTransactionId,
						   s->curTransactionOwner,
						   s->parent->curTransactionOwner);
		AtEOSubXact_LargeObject(false, s->subTransactionId,
								s->parent->subTransactionId);
		AtSubAbort_Notify();

		/* Advertise the fact that we aborted in pg_xact. */
		(void) RecordTransactionAbort(true);

		/* Post-abort cleanup */
		if (FullTransactionIdIsValid(s->fullTransactionId))
			AtSubAbort_childXids();

		CallSubXactCallbacks(SUBXACT_EVENT_ABORT_SUB, s->subTransactionId,
							 s->parent->subTransactionId);

		ResourceOwnerRelease(s->curTransactionOwner,
							 RESOURCE_RELEASE_BEFORE_LOCKS,
							 false, false);

		AtEOXact_Aio(false);
		AtEOSubXact_RelationCache(false, s->subTransactionId,
								  s->parent->subTransactionId);
		AtEOSubXact_TypeCache();
		AtEOSubXact_Inval(false);
		ResourceOwnerRelease(s->curTransactionOwner,
							 RESOURCE_RELEASE_LOCKS,
							 false, false);
		ResourceOwnerRelease(s->curTransactionOwner,
							 RESOURCE_RELEASE_AFTER_LOCKS,
							 false, false);
		AtSubAbort_smgr();

		AtEOXact_GUC(false, s->gucNestLevel);
		AtEOSubXact_SPI(false, s->subTransactionId);
		AtEOSubXact_on_commit_actions(false, s->subTransactionId,
									  s->parent->subTransactionId);
		AtEOSubXact_Namespace(false, s->subTransactionId,
							  s->parent->subTransactionId);
		AtEOSubXact_Files(false, s->subTransactionId,
						  s->parent->subTransactionId);
		AtEOSubXact_HashTables(false, s->nestingLevel);
		AtEOSubXact_PgStat(false, s->nestingLevel);
		AtSubAbort_Snapshot(s->nestingLevel);
	}

	/*
	 * Restore the upper transaction's read-only state, too.  This should be
	 * redundant with GUC's cleanup but we may as well do it for consistency
	 * with the commit case.
	 */
	XactReadOnly = s->prevXactReadOnly;

	RESUME_INTERRUPTS();
}

/*
 * CleanupSubTransaction
 *
 *	The caller has to make sure to always reassign CurrentTransactionState
 *	if it has a local pointer to it after calling this function.
 */
/*
 * 中文注释：
 * 子事务中止后的清理：释放子事务内存上下文和资源所有者，然后弹出状态栈。调用后必须重新获取
 * CurrentTransactionState。
 */
static void
CleanupSubTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	ShowTransactionState("CleanupSubTransaction");

	if (s->state != TRANS_ABORT)
		elog(WARNING, "CleanupSubTransaction while in %s state",
			 TransStateAsString(s->state));

	AtSubCleanup_Portals(s->subTransactionId);

	CurrentResourceOwner = s->parent->curTransactionOwner;
	CurTransactionResourceOwner = s->parent->curTransactionOwner;
	if (s->curTransactionOwner)
		ResourceOwnerDelete(s->curTransactionOwner);
	s->curTransactionOwner = NULL;

	AtSubCleanup_Memory();

	s->state = TRANS_DEFAULT;

	PopTransaction();
}

/*
 * PushTransaction
 *		Create transaction state stack entry for a subtransaction
 *
 *	The caller has to make sure to always reassign CurrentTransactionState
 *	if it has a local pointer to it after calling this function.
 */
/*
 * 中文注释：
 * 为子事务创建新的 TransactionState 栈条目，并复制父事务的只读状态、用户 ID、安全上下文等信息。调用
 * 后必须重新获取 CurrentTransactionState。
 */
static void
PushTransaction(void)
{
	TransactionState p = CurrentTransactionState;
	TransactionState s;

	/*
	 * We keep subtransaction state nodes in TopTransactionContext.
	 */
	s = (TransactionState)
		MemoryContextAllocZero(TopTransactionContext,
							   sizeof(TransactionStateData));

	/*
	 * Assign a subtransaction ID, watching out for counter wraparound.
	 */
	currentSubTransactionId += 1;
	if (currentSubTransactionId == InvalidSubTransactionId)
	{
		currentSubTransactionId -= 1;
		pfree(s);
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("cannot have more than 2^32-1 subtransactions in a transaction")));
	}

	/*
	 * We can now stack a minimally valid subtransaction without fear of
	 * failure.
	 */
	s->fullTransactionId = InvalidFullTransactionId;	/* until assigned */
	s->subTransactionId = currentSubTransactionId;
	s->parent = p;
	s->nestingLevel = p->nestingLevel + 1;
	s->gucNestLevel = NewGUCNestLevel();
	s->savepointLevel = p->savepointLevel;
	s->state = TRANS_DEFAULT;
	s->blockState = TBLOCK_SUBBEGIN;
	GetUserIdAndSecContext(&s->prevUser, &s->prevSecContext);
	s->prevXactReadOnly = XactReadOnly;
	s->startedInRecovery = p->startedInRecovery;
	s->parallelModeLevel = 0;
	s->parallelChildXact = (p->parallelModeLevel != 0 || p->parallelChildXact);
	s->topXidLogged = false;

	CurrentTransactionState = s;

	/*
	 * AbortSubTransaction and CleanupSubTransaction have to be able to cope
	 * with the subtransaction from here on out; in particular they should not
	 * assume that it necessarily has a transaction context, resource owner,
	 * or XID.
	 */
}

/*
 * PopTransaction
 *		Pop back to parent transaction state
 *
 *	The caller has to make sure to always reassign CurrentTransactionState
 *	if it has a local pointer to it after calling this function.
 */
/*
 * 中文注释：
 * 弹出当前子事务状态，回到父事务状态，并恢复父事务的内存上下文和资源所有者。调用后必须重新获取
 * CurrentTransactionState。
 */
static void
PopTransaction(void)
{
	TransactionState s = CurrentTransactionState;

	if (s->state != TRANS_DEFAULT)
		elog(WARNING, "PopTransaction while in %s state",
			 TransStateAsString(s->state));

	if (s->parent == NULL)
		elog(FATAL, "PopTransaction with no parent");

	CurrentTransactionState = s->parent;

	/* Let's just make sure CurTransactionContext is good */
	CurTransactionContext = s->parent->curTransactionContext;
	MemoryContextSwitchTo(CurTransactionContext);

	/* Ditto for ResourceOwner links */
	CurTransactionResourceOwner = s->parent->curTransactionOwner;
	CurrentResourceOwner = s->parent->curTransactionOwner;

	/* Free the old child structure */
	if (s->name)
		pfree(s->name);
	pfree(s);
}

/*
 * EstimateTransactionStateSpace
 *		Estimate the amount of space that will be needed by
 *		SerializeTransactionState.  It would be OK to overestimate slightly,
 *		but it's simple for us to work out the precise value, so we do.
 */
/*
 * 中文注释：
 * 估算 SerializeTransactionState() 需要的共享内存空间大小。精确计算虽然稍多几行代码，但可以避免浪费
 * 空间。
 */
Size
EstimateTransactionStateSpace(void)
{
	TransactionState s;
	Size		nxids = 0;
	Size		size = SerializedTransactionStateHeaderSize;

	for (s = CurrentTransactionState; s != NULL; s = s->parent)
	{
		if (FullTransactionIdIsValid(s->fullTransactionId))
			nxids = add_size(nxids, 1);
		nxids = add_size(nxids, s->nChildXids);
	}

	return add_size(size, mul_size(sizeof(TransactionId), nxids));
}

/*
 * SerializeTransactionState
 *		Write out relevant details of our transaction state that will be
 *		needed by a parallel worker.
 *
 * We need to save and restore XactDeferrable, XactIsoLevel, and the XIDs
 * associated with this transaction.  These are serialized into a
 * caller-supplied buffer big enough to hold the number of bytes reported by
 * EstimateTransactionStateSpace().  We emit the XIDs in sorted order for the
 * convenience of the receiving process.
 */
/*
 * 中文注释：
 * 把并行 worker 需要的事务状态序列化到调用者提供的缓冲区：隔离级别、可延迟属性、顶层/当前
 * FullTransactionId、当前命令 ID 以及当前有效的 XID 列表（按数值排序）。
 */
void
SerializeTransactionState(Size maxsize, char *start_address)
{
	TransactionState s;
	Size		nxids = 0;
	Size		i = 0;
	TransactionId *workspace;
	SerializedTransactionState *result;

	result = (SerializedTransactionState *) start_address;

	result->xactIsoLevel = XactIsoLevel;
	result->xactDeferrable = XactDeferrable;
	result->topFullTransactionId = XactTopFullTransactionId;
	result->currentFullTransactionId =
		CurrentTransactionState->fullTransactionId;
	result->currentCommandId = currentCommandId;

	/*
	 * If we're running in a parallel worker and launching a parallel worker
	 * of our own, we can just pass along the information that was passed to
	 * us.
	 */
	if (nParallelCurrentXids > 0)
	{
		result->nParallelCurrentXids = nParallelCurrentXids;
		memcpy(&result->parallelCurrentXids[0], ParallelCurrentXids,
			   nParallelCurrentXids * sizeof(TransactionId));
		return;
	}

	/*
	 * OK, we need to generate a sorted list of XIDs that our workers should
	 * view as current.  First, figure out how many there are.
	 */
	for (s = CurrentTransactionState; s != NULL; s = s->parent)
	{
		if (FullTransactionIdIsValid(s->fullTransactionId))
			nxids = add_size(nxids, 1);
		nxids = add_size(nxids, s->nChildXids);
	}
	Assert(SerializedTransactionStateHeaderSize + nxids * sizeof(TransactionId)
		   <= maxsize);

	/* Copy them to our scratch space. */
	workspace = palloc(nxids * sizeof(TransactionId));
	for (s = CurrentTransactionState; s != NULL; s = s->parent)
	{
		if (FullTransactionIdIsValid(s->fullTransactionId))
			workspace[i++] = XidFromFullTransactionId(s->fullTransactionId);
		if (s->nChildXids > 0)
			memcpy(&workspace[i], s->childXids,
				   s->nChildXids * sizeof(TransactionId));
		i += s->nChildXids;
	}
	Assert(i == nxids);

	/* Sort them. */
	qsort(workspace, nxids, sizeof(TransactionId), xidComparator);

	/* Copy data into output area. */
	result->nParallelCurrentXids = nxids;
	memcpy(&result->parallelCurrentXids[0], workspace,
		   nxids * sizeof(TransactionId));
}

/*
 * StartParallelWorkerTransaction
 *		Start a parallel worker transaction, restoring the relevant
 *		transaction state serialized by SerializeTransactionState.
 */
/*
 * 中文注释：
 * 并行 worker 启动事务：从 SerializeTransactionState 产生的状态缓冲区恢复事务特征和 XID 信息。
 */
void
StartParallelWorkerTransaction(char *tstatespace)
{
	SerializedTransactionState *tstate;

	Assert(CurrentTransactionState->blockState == TBLOCK_DEFAULT);
	StartTransaction();

	tstate = (SerializedTransactionState *) tstatespace;
	XactIsoLevel = tstate->xactIsoLevel;
	XactDeferrable = tstate->xactDeferrable;
	XactTopFullTransactionId = tstate->topFullTransactionId;
	CurrentTransactionState->fullTransactionId =
		tstate->currentFullTransactionId;
	currentCommandId = tstate->currentCommandId;
	nParallelCurrentXids = tstate->nParallelCurrentXids;
	ParallelCurrentXids = &tstate->parallelCurrentXids[0];

	CurrentTransactionState->blockState = TBLOCK_PARALLEL_INPROGRESS;
}

/*
 * EndParallelWorkerTransaction
 *		End a parallel worker transaction.
 */
/*
 * 中文注释：
 * 结束并行 worker 的事务。
 */
void
EndParallelWorkerTransaction(void)
{
	Assert(CurrentTransactionState->blockState == TBLOCK_PARALLEL_INPROGRESS);
	CommitTransaction();
	CurrentTransactionState->blockState = TBLOCK_DEFAULT;
}

/*
 * ShowTransactionState
 *		Debug support
 */
/*
 * 中文注释：
 * 调试辅助函数：输出当前事务状态栈。
 */
static void
ShowTransactionState(const char *str)
{
	/* skip work if message will definitely not be printed */
	if (message_level_is_interesting(DEBUG5))
		ShowTransactionStateRec(str, CurrentTransactionState);
}

/*
 * ShowTransactionStateRec
 *		Recursive subroutine for ShowTransactionState
 */
/*
 * 中文注释：
 * ShowTransactionState 的递归子程序，逐层输出事务状态。
 */
static void
ShowTransactionStateRec(const char *str, TransactionState s)
{
	StringInfoData buf;

	if (s->parent)
	{
		/*
		 * Since this function recurses, it could be driven to stack overflow.
		 * This is just a debugging aid, so we can leave out some details
		 * instead of erroring out with check_stack_depth().
		 */
		if (stack_is_too_deep())
			ereport(DEBUG5,
					(errmsg_internal("%s(%d): parent omitted to avoid stack overflow",
									 str, s->nestingLevel)));
		else
			ShowTransactionStateRec(str, s->parent);
	}

	initStringInfo(&buf);
	if (s->nChildXids > 0)
	{
		int			i;

		appendStringInfo(&buf, ", children: %u", s->childXids[0]);
		for (i = 1; i < s->nChildXids; i++)
			appendStringInfo(&buf, " %u", s->childXids[i]);
	}
	ereport(DEBUG5,
			(errmsg_internal("%s(%d) name: %s; blockState: %s; state: %s, xid/subid/cid: %u/%u/%u%s%s",
							 str, s->nestingLevel,
							 s->name ? s->name : "unnamed",
							 BlockStateAsString(s->blockState),
							 TransStateAsString(s->state),
							 XidFromFullTransactionId(s->fullTransactionId),
							 s->subTransactionId,
							 currentCommandId,
							 currentCommandIdUsed ? " (used)" : "",
							 buf.data)));
	pfree(buf.data);
}

/*
 * BlockStateAsString
 *		Debug support
 */
/*
 * 中文注释：
 * 调试辅助函数：把 TBlockState 枚举转换为可读字符串。
 */
static const char *
BlockStateAsString(TBlockState blockState)
{
	switch (blockState)
	{
		case TBLOCK_DEFAULT:
			return "DEFAULT";
		case TBLOCK_STARTED:
			return "STARTED";
		case TBLOCK_BEGIN:
			return "BEGIN";
		case TBLOCK_INPROGRESS:
			return "INPROGRESS";
		case TBLOCK_IMPLICIT_INPROGRESS:
			return "IMPLICIT_INPROGRESS";
		case TBLOCK_PARALLEL_INPROGRESS:
			return "PARALLEL_INPROGRESS";
		case TBLOCK_END:
			return "END";
		case TBLOCK_ABORT:
			return "ABORT";
		case TBLOCK_ABORT_END:
			return "ABORT_END";
		case TBLOCK_ABORT_PENDING:
			return "ABORT_PENDING";
		case TBLOCK_PREPARE:
			return "PREPARE";
		case TBLOCK_SUBBEGIN:
			return "SUBBEGIN";
		case TBLOCK_SUBINPROGRESS:
			return "SUBINPROGRESS";
		case TBLOCK_SUBRELEASE:
			return "SUBRELEASE";
		case TBLOCK_SUBCOMMIT:
			return "SUBCOMMIT";
		case TBLOCK_SUBABORT:
			return "SUBABORT";
		case TBLOCK_SUBABORT_END:
			return "SUBABORT_END";
		case TBLOCK_SUBABORT_PENDING:
			return "SUBABORT_PENDING";
		case TBLOCK_SUBRESTART:
			return "SUBRESTART";
		case TBLOCK_SUBABORT_RESTART:
			return "SUBABORT_RESTART";
	}
	return "UNRECOGNIZED";
}

/*
 * TransStateAsString
 *		Debug support
 */
/*
 * 中文注释：
 * 调试辅助函数：把 TransState 枚举转换为可读字符串。
 */
static const char *
TransStateAsString(TransState state)
{
	switch (state)
	{
		case TRANS_DEFAULT:
			return "DEFAULT";
		case TRANS_START:
			return "START";
		case TRANS_INPROGRESS:
			return "INPROGRESS";
		case TRANS_COMMIT:
			return "COMMIT";
		case TRANS_ABORT:
			return "ABORT";
		case TRANS_PREPARE:
			return "PREPARE";
	}
	return "UNRECOGNIZED";
}

/*
 * xactGetCommittedChildren
 *
 * Gets the list of committed children of the current transaction.  The return
 * value is the number of child transactions.  *ptr is set to point to an
 * array of TransactionIds.  The array is allocated in TopTransactionContext;
 * the caller should *not* pfree() it (this is a change from pre-8.4 code!).
 * If there are no subxacts, *ptr is set to NULL.
 */
/*
 * 中文注释：
 * 获取当前事务已提交子事务的 XID 列表，返回子事务数量，*ptr 指向 TransactionId 数组。数组分配在
 * TopTransactionContext 中，调用者不要 pfree；没有子事务时 *ptr 为 NULL。
 */
int
xactGetCommittedChildren(TransactionId **ptr)
{
	TransactionState s = CurrentTransactionState;

	if (s->nChildXids == 0)
		*ptr = NULL;
	else
		*ptr = s->childXids;

	return s->nChildXids;
}

/*
 *	XLOG support routines
 */


/*
 * Log the commit record for a plain or twophase transaction commit.
 *
 * A 2pc commit will be emitted when twophase_xid is valid, a plain one
 * otherwise.
 */
/*
 * 中文注释：
 * 构造并写入提交 WAL 记录。twophase_xid 有效时写两阶段提交记录，否则写普通提交记录。
 */
XLogRecPtr
XactLogCommitRecord(TimestampTz commit_time,
					int nsubxacts, TransactionId *subxacts,
					int nrels, RelFileLocator *rels,
					int ndroppedstats, xl_xact_stats_item *droppedstats,
					int nmsgs, SharedInvalidationMessage *msgs,
					bool relcacheInval,
					int xactflags, TransactionId twophase_xid,
					const char *twophase_gid)
{
	xl_xact_commit xlrec;
	xl_xact_xinfo xl_xinfo;
	xl_xact_dbinfo xl_dbinfo;
	xl_xact_subxacts xl_subxacts;
	xl_xact_relfilelocators xl_relfilelocators;
	xl_xact_stats_items xl_dropped_stats;
	xl_xact_invals xl_invals;
	xl_xact_twophase xl_twophase;
	xl_xact_origin xl_origin;
	uint8		info;

	Assert(CritSectionCount > 0);

	xl_xinfo.xinfo = 0;

	/* decide between a plain and 2pc commit */
	if (!TransactionIdIsValid(twophase_xid))
		info = XLOG_XACT_COMMIT;
	else
		info = XLOG_XACT_COMMIT_PREPARED;

	/* First figure out and collect all the information needed */

	xlrec.xact_time = commit_time;

	if (relcacheInval)
		xl_xinfo.xinfo |= XACT_COMPLETION_UPDATE_RELCACHE_FILE;
	if (forceSyncCommit)
		xl_xinfo.xinfo |= XACT_COMPLETION_FORCE_SYNC_COMMIT;
	if ((xactflags & XACT_FLAGS_ACQUIREDACCESSEXCLUSIVELOCK))
		xl_xinfo.xinfo |= XACT_XINFO_HAS_AE_LOCKS;

	/*
	 * Check if the caller would like to ask standbys for immediate feedback
	 * once this commit is applied.
	 */
	if (synchronous_commit >= SYNCHRONOUS_COMMIT_REMOTE_APPLY)
		xl_xinfo.xinfo |= XACT_COMPLETION_APPLY_FEEDBACK;

	/*
	 * Relcache invalidations requires information about the current database
	 * and so does logical decoding.
	 */
	if (nmsgs > 0 || XLogLogicalInfoActive())
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_DBINFO;
		xl_dbinfo.dbId = MyDatabaseId;
		xl_dbinfo.tsId = MyDatabaseTableSpace;
	}

	if (nsubxacts > 0)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_SUBXACTS;
		xl_subxacts.nsubxacts = nsubxacts;
	}

	if (nrels > 0)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_RELFILELOCATORS;
		xl_relfilelocators.nrels = nrels;
		info |= XLR_SPECIAL_REL_UPDATE;
	}

	if (ndroppedstats > 0)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_DROPPED_STATS;
		xl_dropped_stats.nitems = ndroppedstats;
	}

	if (nmsgs > 0)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_INVALS;
		xl_invals.nmsgs = nmsgs;
	}

	if (TransactionIdIsValid(twophase_xid))
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_TWOPHASE;
		xl_twophase.xid = twophase_xid;
		Assert(twophase_gid != NULL);

		if (XLogLogicalInfoActive())
			xl_xinfo.xinfo |= XACT_XINFO_HAS_GID;
	}

	/* dump transaction origin information */
	if (replorigin_xact_state.origin != InvalidReplOriginId)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_ORIGIN;

		xl_origin.origin_lsn = replorigin_xact_state.origin_lsn;
		xl_origin.origin_timestamp = replorigin_xact_state.origin_timestamp;
	}

	if (xl_xinfo.xinfo != 0)
		info |= XLOG_XACT_HAS_INFO;

	/* Then include all the collected data into the commit record. */

	XLogBeginInsert();

	XLogRegisterData(&xlrec, sizeof(xl_xact_commit));

	if (xl_xinfo.xinfo != 0)
		XLogRegisterData(&xl_xinfo.xinfo, sizeof(xl_xinfo.xinfo));

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_DBINFO)
		XLogRegisterData(&xl_dbinfo, sizeof(xl_dbinfo));

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_SUBXACTS)
	{
		XLogRegisterData(&xl_subxacts,
						 MinSizeOfXactSubxacts);
		XLogRegisterData(subxacts,
						 nsubxacts * sizeof(TransactionId));
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_RELFILELOCATORS)
	{
		XLogRegisterData(&xl_relfilelocators,
						 MinSizeOfXactRelfileLocators);
		XLogRegisterData(rels,
						 nrels * sizeof(RelFileLocator));
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_DROPPED_STATS)
	{
		XLogRegisterData(&xl_dropped_stats,
						 MinSizeOfXactStatsItems);
		XLogRegisterData(droppedstats,
						 ndroppedstats * sizeof(xl_xact_stats_item));
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_INVALS)
	{
		XLogRegisterData(&xl_invals, MinSizeOfXactInvals);
		XLogRegisterData(msgs,
						 nmsgs * sizeof(SharedInvalidationMessage));
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_TWOPHASE)
	{
		XLogRegisterData(&xl_twophase, sizeof(xl_xact_twophase));
		if (xl_xinfo.xinfo & XACT_XINFO_HAS_GID)
			XLogRegisterData(twophase_gid, strlen(twophase_gid) + 1);
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_ORIGIN)
		XLogRegisterData(&xl_origin, sizeof(xl_xact_origin));

	/* we allow filtering by xacts */
	XLogSetRecordFlags(XLOG_INCLUDE_ORIGIN);

	return XLogInsert(RM_XACT_ID, info);
}

/*
 * Log the commit record for a plain or twophase transaction abort.
 *
 * A 2pc abort will be emitted when twophase_xid is valid, a plain one
 * otherwise.
 */
/*
 * 中文注释：
 * 构造并写入中止 WAL 记录。twophase_xid 有效时写两阶段中止记录，否则写普通中止记录。
 */
XLogRecPtr
XactLogAbortRecord(TimestampTz abort_time,
				   int nsubxacts, TransactionId *subxacts,
				   int nrels, RelFileLocator *rels,
				   int ndroppedstats, xl_xact_stats_item *droppedstats,
				   int xactflags, TransactionId twophase_xid,
				   const char *twophase_gid)
{
	xl_xact_abort xlrec;
	xl_xact_xinfo xl_xinfo;
	xl_xact_subxacts xl_subxacts;
	xl_xact_relfilelocators xl_relfilelocators;
	xl_xact_stats_items xl_dropped_stats;
	xl_xact_twophase xl_twophase;
	xl_xact_dbinfo xl_dbinfo;
	xl_xact_origin xl_origin;

	uint8		info;

	Assert(CritSectionCount > 0);

	xl_xinfo.xinfo = 0;

	/* decide between a plain and 2pc abort */
	if (!TransactionIdIsValid(twophase_xid))
		info = XLOG_XACT_ABORT;
	else
		info = XLOG_XACT_ABORT_PREPARED;


	/* First figure out and collect all the information needed */

	xlrec.xact_time = abort_time;

	if ((xactflags & XACT_FLAGS_ACQUIREDACCESSEXCLUSIVELOCK))
		xl_xinfo.xinfo |= XACT_XINFO_HAS_AE_LOCKS;

	if (nsubxacts > 0)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_SUBXACTS;
		xl_subxacts.nsubxacts = nsubxacts;
	}

	if (nrels > 0)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_RELFILELOCATORS;
		xl_relfilelocators.nrels = nrels;
		info |= XLR_SPECIAL_REL_UPDATE;
	}

	if (ndroppedstats > 0)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_DROPPED_STATS;
		xl_dropped_stats.nitems = ndroppedstats;
	}

	if (TransactionIdIsValid(twophase_xid))
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_TWOPHASE;
		xl_twophase.xid = twophase_xid;
		Assert(twophase_gid != NULL);

		if (XLogLogicalInfoActive())
			xl_xinfo.xinfo |= XACT_XINFO_HAS_GID;
	}

	if (TransactionIdIsValid(twophase_xid) && XLogLogicalInfoActive())
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_DBINFO;
		xl_dbinfo.dbId = MyDatabaseId;
		xl_dbinfo.tsId = MyDatabaseTableSpace;
	}

	/*
	 * Dump transaction origin information. We need this during recovery to
	 * update the replication origin progress.
	 */
	if (replorigin_xact_state.origin != InvalidReplOriginId)
	{
		xl_xinfo.xinfo |= XACT_XINFO_HAS_ORIGIN;

		xl_origin.origin_lsn = replorigin_xact_state.origin_lsn;
		xl_origin.origin_timestamp = replorigin_xact_state.origin_timestamp;
	}

	if (xl_xinfo.xinfo != 0)
		info |= XLOG_XACT_HAS_INFO;

	/* Then include all the collected data into the abort record. */

	XLogBeginInsert();

	XLogRegisterData(&xlrec, MinSizeOfXactAbort);

	if (xl_xinfo.xinfo != 0)
		XLogRegisterData(&xl_xinfo, sizeof(xl_xinfo));

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_DBINFO)
		XLogRegisterData(&xl_dbinfo, sizeof(xl_dbinfo));

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_SUBXACTS)
	{
		XLogRegisterData(&xl_subxacts,
						 MinSizeOfXactSubxacts);
		XLogRegisterData(subxacts,
						 nsubxacts * sizeof(TransactionId));
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_RELFILELOCATORS)
	{
		XLogRegisterData(&xl_relfilelocators,
						 MinSizeOfXactRelfileLocators);
		XLogRegisterData(rels,
						 nrels * sizeof(RelFileLocator));
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_DROPPED_STATS)
	{
		XLogRegisterData(&xl_dropped_stats,
						 MinSizeOfXactStatsItems);
		XLogRegisterData(droppedstats,
						 ndroppedstats * sizeof(xl_xact_stats_item));
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_TWOPHASE)
	{
		XLogRegisterData(&xl_twophase, sizeof(xl_xact_twophase));
		if (xl_xinfo.xinfo & XACT_XINFO_HAS_GID)
			XLogRegisterData(twophase_gid, strlen(twophase_gid) + 1);
	}

	if (xl_xinfo.xinfo & XACT_XINFO_HAS_ORIGIN)
		XLogRegisterData(&xl_origin, sizeof(xl_xact_origin));

	/* Include the replication origin */
	XLogSetRecordFlags(XLOG_INCLUDE_ORIGIN);

	return XLogInsert(RM_XACT_ID, info);
}

/*
 * Before 9.0 this was a fairly short function, but now it performs many
 * actions for which the order of execution is critical.
 */
/*
 * 中文注释：
 * 恢复阶段重放事务提交记录：更新 pg_xact 中的提交状态、提交时间戳、子事务状态，并处理 2PC 与文件删
 * 除等。执行顺序非常关键。
 */
static void
xact_redo_commit(xl_xact_parsed_commit *parsed,
				 TransactionId xid,
				 XLogRecPtr lsn,
				 ReplOriginId origin_id)
{
	TransactionId max_xid;
	TimestampTz commit_time;

	Assert(TransactionIdIsValid(xid));

	max_xid = TransactionIdLatest(xid, parsed->nsubxacts, parsed->subxacts);

	/* Make sure nextXid is beyond any XID mentioned in the record. */
	AdvanceNextFullTransactionIdPastXid(max_xid);

	Assert(((parsed->xinfo & XACT_XINFO_HAS_ORIGIN) == 0) ==
		   (origin_id == InvalidReplOriginId));

	if (parsed->xinfo & XACT_XINFO_HAS_ORIGIN)
		commit_time = parsed->origin_timestamp;
	else
		commit_time = parsed->xact_time;

	/* Set the transaction commit timestamp and metadata */
	TransactionTreeSetCommitTsData(xid, parsed->nsubxacts, parsed->subxacts,
								   commit_time, origin_id);

	if (standbyState == STANDBY_DISABLED)
	{
		/*
		 * Mark the transaction committed in pg_xact.
		 */
		TransactionIdCommitTree(xid, parsed->nsubxacts, parsed->subxacts);
	}
	else
	{
		/*
		 * If a transaction completion record arrives that has as-yet
		 * unobserved subtransactions then this will not have been fully
		 * handled by the call to RecordKnownAssignedTransactionIds() in the
		 * main recovery loop in PerformWalRecovery(). So we need to do
		 * bookkeeping again to cover that case. This is confusing and it is
		 * easy to think this call is irrelevant, which has happened three
		 * times in development already. Leave it in.
		 */
		RecordKnownAssignedTransactionIds(max_xid);

		/*
		 * Mark the transaction committed in pg_xact. We use async commit
		 * protocol during recovery to provide information on database
		 * consistency for when users try to set hint bits. It is important
		 * that we do not set hint bits until the minRecoveryPoint is past
		 * this commit record. This ensures that if we crash we don't see hint
		 * bits set on changes made by transactions that haven't yet
		 * recovered. It's unlikely but it's good to be safe.
		 */
		TransactionIdAsyncCommitTree(xid, parsed->nsubxacts, parsed->subxacts, lsn);

		/*
		 * We must mark clog before we update the ProcArray.
		 */
		ExpireTreeKnownAssignedTransactionIds(xid, parsed->nsubxacts, parsed->subxacts, max_xid);

		/*
		 * Send any cache invalidations attached to the commit. We must
		 * maintain the same order of invalidation then release locks as
		 * occurs in CommitTransaction().
		 */
		ProcessCommittedInvalidationMessages(parsed->msgs, parsed->nmsgs,
											 XactCompletionRelcacheInitFileInval(parsed->xinfo),
											 parsed->dbId, parsed->tsId);

		/*
		 * Release locks, if any. We do this for both two phase and normal one
		 * phase transactions. In effect we are ignoring the prepare phase and
		 * just going straight to lock release.
		 */
		if (parsed->xinfo & XACT_XINFO_HAS_AE_LOCKS)
			StandbyReleaseLockTree(xid, parsed->nsubxacts, parsed->subxacts);
	}

	if (parsed->xinfo & XACT_XINFO_HAS_ORIGIN)
	{
		/* recover apply progress */
		replorigin_advance(origin_id, parsed->origin_lsn, lsn,
						   false /* backward */ , false /* WAL */ );
	}

	/* Make sure files supposed to be dropped are dropped */
	if (parsed->nrels > 0)
	{
		/*
		 * First update minimum recovery point to cover this WAL record. Once
		 * a relation is deleted, there's no going back. The buffer manager
		 * enforces the WAL-first rule for normal updates to relation files,
		 * so that the minimum recovery point is always updated before the
		 * corresponding change in the data file is flushed to disk, but we
		 * have to do the same here since we're bypassing the buffer manager.
		 *
		 * Doing this before deleting the files means that if a deletion fails
		 * for some reason, you cannot start up the system even after restart,
		 * until you fix the underlying situation so that the deletion will
		 * succeed. Alternatively, we could update the minimum recovery point
		 * after deletion, but that would leave a small window where the
		 * WAL-first rule would be violated.
		 */
		XLogFlush(lsn);

		/* Make sure files supposed to be dropped are dropped */
		DropRelationFiles(parsed->xlocators, parsed->nrels, true);
	}

	if (parsed->nstats > 0)
	{
		/* see equivalent call for relations above */
		XLogFlush(lsn);

		pgstat_execute_transactional_drops(parsed->nstats, parsed->stats, true);
	}

	/*
	 * We issue an XLogFlush() for the same reason we emit ForceSyncCommit()
	 * in normal operation. For example, in CREATE DATABASE, we copy all files
	 * from the template database, and then commit the transaction. If we
	 * crash after all the files have been copied but before the commit, you
	 * have files in the data directory without an entry in pg_database. To
	 * minimize the window for that, we use ForceSyncCommit() to rush the
	 * commit record to disk as quick as possible. We have the same window
	 * during recovery, and forcing an XLogFlush() (which updates
	 * minRecoveryPoint during recovery) helps to reduce that problem window,
	 * for any user that requested ForceSyncCommit().
	 */
	if (XactCompletionForceSyncCommit(parsed->xinfo))
		XLogFlush(lsn);

	/*
	 * If asked by the primary (because someone is waiting for a synchronous
	 * commit = remote_apply), we will need to ask walreceiver to send a reply
	 * immediately.
	 */
	if (XactCompletionApplyFeedback(parsed->xinfo))
		XLogRequestWalReceiverReply();
}

/*
 * Be careful with the order of execution, as with xact_redo_commit().
 * The two functions are similar but differ in key places.
 *
 * Note also that an abort can be for a subtransaction and its children,
 * not just for a top level abort. That means we have to consider
 * topxid != xid, whereas in commit we would find topxid == xid always
 * because subtransaction commit is never WAL logged.
 */
/*
 * 中文注释：
 * 恢复阶段重放事务中止记录：更新 pg_xact 中的中止状态、子事务状态，并处理 2PC 与文件删除等。执行顺
 * 序与 xact_redo_commit 类似但有关键差异；中止可能针对子事务，因此 topxid 可能与 xid 不同。
 */
static void
xact_redo_abort(xl_xact_parsed_abort *parsed, TransactionId xid,
				XLogRecPtr lsn, ReplOriginId origin_id)
{
	TransactionId max_xid;

	Assert(TransactionIdIsValid(xid));

	/* Make sure nextXid is beyond any XID mentioned in the record. */
	max_xid = TransactionIdLatest(xid,
								  parsed->nsubxacts,
								  parsed->subxacts);
	AdvanceNextFullTransactionIdPastXid(max_xid);

	if (standbyState == STANDBY_DISABLED)
	{
		/* Mark the transaction aborted in pg_xact, no need for async stuff */
		TransactionIdAbortTree(xid, parsed->nsubxacts, parsed->subxacts);
	}
	else
	{
		/*
		 * If a transaction completion record arrives that has as-yet
		 * unobserved subtransactions then this will not have been fully
		 * handled by the call to RecordKnownAssignedTransactionIds() in the
		 * main recovery loop in PerformWalRecovery(). So we need to do
		 * bookkeeping again to cover that case. This is confusing and it is
		 * easy to think this call is irrelevant, which has happened three
		 * times in development already. Leave it in.
		 */
		RecordKnownAssignedTransactionIds(max_xid);

		/* Mark the transaction aborted in pg_xact, no need for async stuff */
		TransactionIdAbortTree(xid, parsed->nsubxacts, parsed->subxacts);

		/*
		 * We must update the ProcArray after we have marked clog.
		 */
		ExpireTreeKnownAssignedTransactionIds(xid, parsed->nsubxacts, parsed->subxacts, max_xid);

		/*
		 * There are no invalidation messages to send or undo.
		 */

		/*
		 * Release locks, if any. There are no invalidations to send.
		 */
		if (parsed->xinfo & XACT_XINFO_HAS_AE_LOCKS)
			StandbyReleaseLockTree(xid, parsed->nsubxacts, parsed->subxacts);
	}

	if (parsed->xinfo & XACT_XINFO_HAS_ORIGIN)
	{
		/* recover apply progress */
		replorigin_advance(origin_id, parsed->origin_lsn, lsn,
						   false /* backward */ , false /* WAL */ );
	}

	/* Make sure files supposed to be dropped are dropped */
	if (parsed->nrels > 0)
	{
		/*
		 * See comments about update of minimum recovery point on truncation,
		 * in xact_redo_commit().
		 */
		XLogFlush(lsn);

		DropRelationFiles(parsed->xlocators, parsed->nrels, true);
	}

	if (parsed->nstats > 0)
	{
		/* see equivalent call for relations above */
		XLogFlush(lsn);

		pgstat_execute_transactional_drops(parsed->nstats, parsed->stats, true);
	}
}

/*
 * 中文注释：
 * WAL 恢复入口：解析 XLOG_XACT_* 记录并分派给 xact_redo_commit、xact_redo_abort 或两阶段提交恢复逻
 * 辑。
 */
void
xact_redo(XLogReaderState *record)
{
	uint8		info = XLogRecGetInfo(record) & XLOG_XACT_OPMASK;

	/* Backup blocks are not used in xact records */
	Assert(!XLogRecHasAnyBlockRefs(record));

	if (info == XLOG_XACT_COMMIT)
	{
		xl_xact_commit *xlrec = (xl_xact_commit *) XLogRecGetData(record);
		xl_xact_parsed_commit parsed;

		ParseCommitRecord(XLogRecGetInfo(record), xlrec, &parsed);
		xact_redo_commit(&parsed, XLogRecGetXid(record),
						 record->EndRecPtr, XLogRecGetOrigin(record));
	}
	else if (info == XLOG_XACT_COMMIT_PREPARED)
	{
		xl_xact_commit *xlrec = (xl_xact_commit *) XLogRecGetData(record);
		xl_xact_parsed_commit parsed;

		ParseCommitRecord(XLogRecGetInfo(record), xlrec, &parsed);
		xact_redo_commit(&parsed, parsed.twophase_xid,
						 record->EndRecPtr, XLogRecGetOrigin(record));

		/* Delete TwoPhaseState gxact entry and/or 2PC file. */
		LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
		PrepareRedoRemove(parsed.twophase_xid, false);
		LWLockRelease(TwoPhaseStateLock);
	}
	else if (info == XLOG_XACT_ABORT)
	{
		xl_xact_abort *xlrec = (xl_xact_abort *) XLogRecGetData(record);
		xl_xact_parsed_abort parsed;

		ParseAbortRecord(XLogRecGetInfo(record), xlrec, &parsed);
		xact_redo_abort(&parsed, XLogRecGetXid(record),
						record->EndRecPtr, XLogRecGetOrigin(record));
	}
	else if (info == XLOG_XACT_ABORT_PREPARED)
	{
		xl_xact_abort *xlrec = (xl_xact_abort *) XLogRecGetData(record);
		xl_xact_parsed_abort parsed;

		ParseAbortRecord(XLogRecGetInfo(record), xlrec, &parsed);
		xact_redo_abort(&parsed, parsed.twophase_xid,
						record->EndRecPtr, XLogRecGetOrigin(record));

		/* Delete TwoPhaseState gxact entry and/or 2PC file. */
		LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
		PrepareRedoRemove(parsed.twophase_xid, false);
		LWLockRelease(TwoPhaseStateLock);
	}
	else if (info == XLOG_XACT_PREPARE)
	{
		/*
		 * Store xid and start/end pointers of the WAL record in TwoPhaseState
		 * gxact entry.
		 */
		LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
		PrepareRedoAdd(InvalidFullTransactionId,
					   XLogRecGetData(record),
					   record->ReadRecPtr,
					   record->EndRecPtr,
					   XLogRecGetOrigin(record));
		LWLockRelease(TwoPhaseStateLock);
	}
	else if (info == XLOG_XACT_ASSIGNMENT)
	{
		xl_xact_assignment *xlrec = (xl_xact_assignment *) XLogRecGetData(record);

		if (standbyState >= STANDBY_INITIALIZED)
			ProcArrayApplyXidAssignment(xlrec->xtop,
										xlrec->nsubxacts, xlrec->xsub);
	}
	else if (info == XLOG_XACT_INVALIDATIONS)
	{
		/*
		 * XXX we do ignore this for now, what matters are invalidations
		 * written into the commit record.
		 */
	}
	else
		elog(PANIC, "xact_redo: unknown op code %u", info);
}
