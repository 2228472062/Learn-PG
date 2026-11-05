/*-------------------------------------------------------------------------
 *
 * twophase.c
 *		Two-phase commit support functions.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *		src/backend/access/transam/twophase.c
 *
 * NOTES
 *		Each global transaction is associated with a global transaction
 *		identifier (GID). The client assigns a GID to a postgres
 *		transaction with the PREPARE TRANSACTION command.
 *
 *		We keep all active global transactions in a shared memory array.
 *		When the PREPARE TRANSACTION command is issued, the GID is
 *		reserved for the transaction in the array. This is done before
 *		a WAL entry is made, because the reservation checks for duplicate
 *		GIDs and aborts the transaction if there already is a global
 *		transaction in prepared state with the same GID.
 *
 *		A global transaction (gxact) also has dummy PGPROC; this is what keeps
 *		the XID considered running by TransactionIdIsInProgress.  It is also
 *		convenient as a PGPROC to hook the gxact's locks to.
 *
 *		Information to recover prepared transactions in case of crash is
 *		now stored in WAL for the common case. In some cases there will be
 *		an extended period between preparing a GXACT and commit/abort, in
 *		which case we need to separately record prepared transaction data
 *		in permanent storage. This includes locking information, pending
 *		notifications etc. All that state information is written to the
 *		per-transaction state file in the pg_twophase directory.
 *		All prepared transactions will be written prior to shutdown.
 *
 *		Life track of state data is following:
 *
 *		* On PREPARE TRANSACTION backend writes state data only to the WAL and
 *		  stores pointer to the start of the WAL record in
 *		  gxact->prepare_start_lsn.
 *		* If COMMIT occurs before checkpoint then backend reads data from WAL
 *		  using prepare_start_lsn.
 *		* On checkpoint state data copied to files in pg_twophase directory and
 *		  fsynced
 *		* If COMMIT happens after checkpoint then backend reads state data from
 *		  files
 *
 *		During replay and replication, TwoPhaseState also holds information
 *		about active prepared transactions that haven't been moved to disk yet.
 *
 *		Replay of twophase records happens by the following rules:
 *
 *		* At the beginning of recovery, pg_twophase is scanned once, filling
 *		  TwoPhaseState with entries marked with gxact->inredo and
 *		  gxact->ondisk.  Two-phase file data older than the XID horizon of
 *		  the redo position are discarded.
 *		* On PREPARE redo, the transaction is added to TwoPhaseState->prepXacts.
 *		  gxact->inredo is set to true for such entries.
 *		* On Checkpoint we iterate through TwoPhaseState->prepXacts entries
 *		  that have gxact->inredo set and are behind the redo_horizon. We
 *		  save them to disk and then switch gxact->ondisk to true.
 *		* On COMMIT/ABORT we delete the entry from TwoPhaseState->prepXacts.
 *		  If gxact->ondisk is true, the corresponding entry from the disk
 *		  is additionally deleted.
 *		* RecoverPreparedTransactions(), StandbyRecoverPreparedTransactions()
 *		  and PrescanPreparedTransactions() have been modified to go through
 *		  gxact->inredo entries that have not made it to disk.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <fcntl.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#include "access/commit_ts.h"
#include "access/htup_details.h"
#include "access/subtrans.h"
#include "access/transam.h"
#include "access/twophase.h"
#include "access/twophase_rmgr.h"
#include "access/xact.h"
#include "access/xlog.h"
#include "access/xloginsert.h"
#include "access/xlogreader.h"
#include "access/xlogrecovery.h"
#include "access/xlogutils.h"
#include "catalog/pg_type.h"
#include "catalog/storage.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "replication/origin.h"
#include "replication/syncrep.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "storage/md.h"
#include "storage/predicate.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "storage/subsystems.h"
#include "utils/builtins.h"
#include "utils/injection_point.h"
#include "utils/memutils.h"
#include "utils/timestamp.h"
#include "utils/wait_event.h"

/*
 * Directory where Two-phase commit files reside within PGDATA
 */
#define TWOPHASE_DIR "pg_twophase"

/* GUC variable, can't be changed after startup */
int			max_prepared_xacts = 0;

/*
 * This struct describes one global transaction that is in prepared state
 * or attempting to become prepared.
 *
 * The lifecycle of a global transaction is:
 *
 * 1. After checking that the requested GID is not in use, set up an entry in
 * the TwoPhaseState->prepXacts array with the correct GID and valid = false,
 * and mark it as locked by my backend.
 *
 * 2. After successfully completing prepare, set valid = true and enter the
 * referenced PGPROC into the global ProcArray.
 *
 * 3. To begin COMMIT PREPARED or ROLLBACK PREPARED, check that the entry is
 * valid and not locked, then mark the entry as locked by storing my current
 * proc number into locking_backend.  This prevents concurrent attempts to
 * commit or rollback the same prepared xact.
 *
 * 4. On completion of COMMIT PREPARED or ROLLBACK PREPARED, remove the entry
 * from the ProcArray and the TwoPhaseState->prepXacts array and return it to
 * the freelist.
 *
 * Note that if the preparing transaction fails between steps 1 and 2, the
 * entry must be removed so that the GID and the GlobalTransaction struct
 * can be reused.  See AtAbort_Twophase().
 *
 * typedef struct GlobalTransactionData *GlobalTransaction appears in
 * twophase.h
 */

typedef struct GlobalTransactionData
{
	GlobalTransaction next;		/* list link for free list */
	int			pgprocno;		/* ID of associated dummy PGPROC */
	TimestampTz prepared_at;	/* time of preparation */

	/*
	 * Note that we need to keep track of two LSNs for each GXACT. We keep
	 * track of the start LSN because this is the address we must use to read
	 * state data back from WAL when committing a prepared GXACT. We keep
	 * track of the end LSN because that is the LSN we need to wait for prior
	 * to commit.
	 */
	XLogRecPtr	prepare_start_lsn;	/* XLOG offset of prepare record start */
	XLogRecPtr	prepare_end_lsn;	/* XLOG offset of prepare record end */
	FullTransactionId fxid;		/* The GXACT full xid */

	Oid			owner;			/* ID of user that executed the xact */
	ProcNumber	locking_backend;	/* backend currently working on the xact */
	bool		valid;			/* true if PGPROC entry is in proc array */
	bool		ondisk;			/* true if prepare state file is on disk */
	bool		inredo;			/* true if entry was added via xlog_redo */
	char		gid[GIDSIZE];	/* The GID assigned to the prepared xact */
} GlobalTransactionData;

/*
 * Two Phase Commit shared state.  Access to this struct is protected
 * by TwoPhaseStateLock.
 */
typedef struct TwoPhaseStateData
{
	/* Head of linked list of free GlobalTransactionData structs */
	GlobalTransaction freeGXacts;

	/* Number of valid prepXacts entries. */
	int			numPrepXacts;

	/* There are max_prepared_xacts items in this array */
	GlobalTransaction prepXacts[FLEXIBLE_ARRAY_MEMBER];
} TwoPhaseStateData;

static TwoPhaseStateData *TwoPhaseState;

static void TwoPhaseShmemRequest(void *arg);
static void TwoPhaseShmemInit(void *arg);

const ShmemCallbacks TwoPhaseShmemCallbacks = {
	.request_fn = TwoPhaseShmemRequest,
	.init_fn = TwoPhaseShmemInit,
};

/*
 * Global transaction entry currently locked by us, if any.  Note that any
 * access to the entry pointed to by this variable must be protected by
 * TwoPhaseStateLock, though obviously the pointer itself doesn't need to be
 * (since it's just local memory).
 */
static GlobalTransaction MyLockedGxact = NULL;

static bool twophaseExitRegistered = false;

static void PrepareRedoRemoveFull(FullTransactionId fxid, bool giveWarning);
static void RecordTransactionCommitPrepared(TransactionId xid,
											int nchildren,
											TransactionId *children,
											int nrels,
											RelFileLocator *rels,
											int nstats,
											xl_xact_stats_item *stats,
											int ninvalmsgs,
											SharedInvalidationMessage *invalmsgs,
											bool initfileinval,
											const char *gid);
static void RecordTransactionAbortPrepared(TransactionId xid,
										   int nchildren,
										   TransactionId *children,
										   int nrels,
										   RelFileLocator *rels,
										   int nstats,
										   xl_xact_stats_item *stats,
										   const char *gid);
static void ProcessRecords(char *bufptr, FullTransactionId fxid,
						   const TwoPhaseCallback callbacks[]);
static void RemoveGXact(GlobalTransaction gxact);

static void XlogReadTwoPhaseData(XLogRecPtr lsn, char **buf, size_t *len);
static char *ProcessTwoPhaseBuffer(FullTransactionId fxid,
								   XLogRecPtr prepare_start_lsn,
								   bool fromdisk, bool setParent, bool setNextXid);
static void MarkAsPreparingGuts(GlobalTransaction gxact, FullTransactionId fxid,
								const char *gid, TimestampTz prepared_at, Oid owner,
								Oid databaseid);
static void RemoveTwoPhaseFile(FullTransactionId fxid, bool giveWarning);
static void RecreateTwoPhaseFile(FullTransactionId fxid, const void *content, size_t len);

/*
 * Register shared memory for two-phase state.
 */
/*
 * 中文注释：
 * 向共享内存框架登记两阶段提交状态所需的共享内存大小。
 *
 * 布局是“固定头 + 指针数组 + GlobalTransactionData 数组”：TwoPhaseStateData
 * 的 prepXacts 柔性数组保存指向活动 gxact 的指针，后面 MAXALIGN 对齐再放
 * max_prepared_xacts 个 GlobalTransactionData 实体。这样活动数组与空闲链表可以
 * 复用同一批实体，不需要额外分配。实际的指针和链表初始化在 TwoPhaseShmemInit。
 */
static void
TwoPhaseShmemRequest(void *arg)
{
	Size		size;

	/* Need the fixed struct, the array of pointers, and the GTD structs */
	size = offsetof(TwoPhaseStateData, prepXacts);
	size = add_size(size, mul_size(max_prepared_xacts,
								   sizeof(GlobalTransaction)));
	size = MAXALIGN(size);
	size = add_size(size, mul_size(max_prepared_xacts,
								   sizeof(GlobalTransactionData)));
	ShmemRequestStruct(.name = "Prepared Transaction Table",
					   .size = size,
					   .ptr = (void **) &TwoPhaseState,
		);
}

/*
 * Initialize shared memory for two-phase state.
 */
/*
 * 中文注释：
 * 初始化两阶段提交的共享内存状态。
 *
 * 把 freeGXacts 置空并把所有 GlobalTransactionData 串成空闲链表；每个实体通过
 * GetNumberFromPGProc 关联到 postmaster 预分配的 PreparedXactProcs[i]。该 PGPROC
 * 就是预备事务的“虚拟进程”，使 TransactionIdIsInProgress 仍认为其 XID 在运行，
 * 同时也作为挂载该事务锁的锚点。numPrepXacts 置零表示当前没有活动的预备事务。
 */
static void
TwoPhaseShmemInit(void *arg)
{
	GlobalTransaction gxacts;
	int			i;

	TwoPhaseState->freeGXacts = NULL;
	TwoPhaseState->numPrepXacts = 0;

	/*
	 * Initialize the linked list of free GlobalTransactionData structs
	 */
	gxacts = (GlobalTransaction)
		((char *) TwoPhaseState +
		 MAXALIGN(offsetof(TwoPhaseStateData, prepXacts) +
				  sizeof(GlobalTransaction) * max_prepared_xacts));
	for (i = 0; i < max_prepared_xacts; i++)
	{
		/* insert into linked list */
		gxacts[i].next = TwoPhaseState->freeGXacts;
		TwoPhaseState->freeGXacts = &gxacts[i];

		/* associate it with a PGPROC assigned by ProcGlobalShmemInit */
		gxacts[i].pgprocno = GetNumberFromPGProc(&PreparedXactProcs[i]);
	}
}

/*
 * Exit hook to unlock the global transaction entry we're working on.
 */
/*
 * 中文注释：
 * 后端退出时的 before_shmem_exit 回调。
 *
 * 仅转发到 AtAbort_Twophase，保证进程异常退出时不会把 TwoPhaseState 中某个
 * gxact 永远标记为“被本后端锁定”。注册时机是第一次调用 MarkAsPreparing 或
 * LockGXact 时，避免为不涉及 2PC 的普通会话增加退出钩子。
 */
static void
AtProcExit_Twophase(int code, Datum arg)
{
	/* same logic as abort */
	AtAbort_Twophase();
}

/*
 * Abort hook to unlock the global transaction entry we're working on.
 */
/*
 * 中文注释：
 * 事务中止钩子：释放或回收本后端锁定的 GlobalTransaction。
 *
 * MyLockedGxact 记录了当前后端正在 prepare/finish 的条目。是否需要保留取决于
 * gxact->valid：
 *   - 无效：说明还没写完 WAL/状态文件，或第二阶段已经写完但尚未完成清理，此时
 *     事务不应再被视为 prepared，直接从共享内存移除并归还空闲链表；
 *   - 有效：说明 PREPARE 已经持久化，条目必须留给后续 COMMIT/ROLLBACK PREPARED，
 *     这里只清除 locking_backend 标记。
 * 两种情况都在 TwoPhaseStateLock 排他锁下完成，最后清空 MyLockedGxact。
 */
void
AtAbort_Twophase(void)
{
	if (MyLockedGxact == NULL)
		return;

	/*
	 * What to do with the locked global transaction entry?  If we were in the
	 * process of preparing the transaction, but haven't written the WAL
	 * record and state file yet, the transaction must not be considered as
	 * prepared.  Likewise, if we are in the process of finishing an
	 * already-prepared transaction, and fail after having already written the
	 * 2nd phase commit or rollback record to the WAL, the transaction should
	 * not be considered as prepared anymore.  In those cases, just remove the
	 * entry from shared memory.
	 *
	 * Otherwise, the entry must be left in place so that the transaction can
	 * be finished later, so just unlock it.
	 *
	 * If we abort during prepare, after having written the WAL record, we
	 * might not have transferred all locks and other state to the prepared
	 * transaction yet.  Likewise, if we abort during commit or rollback,
	 * after having written the WAL record, we might not have released all the
	 * resources held by the transaction yet.  In those cases, the in-memory
	 * state can be wrong, but it's too late to back out.
	 */
	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
	if (!MyLockedGxact->valid)
		RemoveGXact(MyLockedGxact);
	else
		MyLockedGxact->locking_backend = INVALID_PROC_NUMBER;
	LWLockRelease(TwoPhaseStateLock);

	MyLockedGxact = NULL;
}

/*
 * This is called after we have finished transferring state to the prepared
 * PGPROC entry.
 */
/*
 * 中文注释：
 * PREPARE TRANSACTION 完成状态转移后的收尾。
 *
 * 调用时事务的锁、子事务等信息已经转移到预备事务的虚拟 PGPROC，本后端不再需要
 * 独占该 gxact。函数在排他锁下把 locking_backend 置为 INVALID_PROC_NUMBER，
 * 允许其他后端执行 COMMIT/ROLLBACK PREPARED，然后清空 MyLockedGxact。
 */
void
PostPrepare_Twophase(void)
{
	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
	MyLockedGxact->locking_backend = INVALID_PROC_NUMBER;
	LWLockRelease(TwoPhaseStateLock);

	MyLockedGxact = NULL;
}


/*
 * MarkAsPreparing
 *		Reserve the GID for the given transaction.
 */
/*
 * 中文注释：
 * 为指定事务预留 GID，是 PREPARE TRANSACTION 的第一个共享内存步骤。
 *
 * 依次检查：GID 长度不超过 GIDSIZE、max_prepared_xacts 非零、GID 未被其他
 * 有效/无效条目占用（GID 在整个集簇内唯一）、空闲链表非空。然后从 freeGXacts
 * 摘下一个实体，调用 MarkAsPreparingGuts 初始化，标记 ondisk=false，并加入
 * prepXacts 活动数组。整个过程持有 TwoPhaseStateLock 排他锁，保证“检查重复 +
 * 占用槽位”是原子的。此时 gxact->valid 仍为 false，直到 WAL 和状态文件写完。
 */
GlobalTransaction
MarkAsPreparing(FullTransactionId fxid, const char *gid,
				TimestampTz prepared_at, Oid owner, Oid databaseid)
{
	GlobalTransaction gxact;
	int			i;

	if (strlen(gid) >= GIDSIZE)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("transaction identifier \"%s\" is too long",
						gid)));

	/* fail immediately if feature is disabled */
	if (max_prepared_xacts == 0)
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("prepared transactions are disabled"),
				 errhint("Set \"max_prepared_transactions\" to a nonzero value.")));

	/* on first call, register the exit hook */
	if (!twophaseExitRegistered)
	{
		before_shmem_exit(AtProcExit_Twophase, 0);
		twophaseExitRegistered = true;
	}

	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);

	/* Check for conflicting GID */
	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		gxact = TwoPhaseState->prepXacts[i];
		if (strcmp(gxact->gid, gid) == 0)
		{
			ereport(ERROR,
					(errcode(ERRCODE_DUPLICATE_OBJECT),
					 errmsg("transaction identifier \"%s\" is already in use",
							gid)));
		}
	}

	/* Get a free gxact from the freelist */
	if (TwoPhaseState->freeGXacts == NULL)
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("maximum number of prepared transactions reached"),
				 errhint("Increase \"max_prepared_transactions\" (currently %d).",
						 max_prepared_xacts)));
	gxact = TwoPhaseState->freeGXacts;
	TwoPhaseState->freeGXacts = gxact->next;

	MarkAsPreparingGuts(gxact, fxid, gid, prepared_at, owner, databaseid);

	gxact->ondisk = false;

	/* And insert it into the active array */
	Assert(TwoPhaseState->numPrepXacts < max_prepared_xacts);
	TwoPhaseState->prepXacts[TwoPhaseState->numPrepXacts++] = gxact;

	LWLockRelease(TwoPhaseStateLock);

	return gxact;
}

/*
 * MarkAsPreparingGuts
 *
 * This uses a gxact struct and puts it into the active array.
 * NOTE: this is also used when reloading a gxact after a crash; so avoid
 * assuming that we can use very much backend context.
 *
 * Note: This function should be called with appropriate locks held.
 */
/*
 * 中文注释：
 * 初始化一个 GlobalTransaction 及其虚拟 PGPROC 的核心字段。
 *
 * 该函数既用于正常 PREPARE，也用于崩溃恢复时重建 gxact，因此不能依赖太多后端
 * 上下文（例如恢复时 MyProc 可能不是普通后端）。主要工作：
 *   - 清零虚拟 PGPROC，设置 xid、databaseId、roleId、等待状态和锁分区链表头；
 *   - 复制当前后端的本地 VXID（若有效），使 TwoPhaseGetXidByVirtualXID 能找到
 *     这个预备事务；恢复场景没有本地 VXID，则用 xid 充当 vxid.lxid 且 procNumber
 *     为 INVALID_PROC_NUMBER，供 GetLockConflicts 等待；
 *   - 填充 prepared_at/fxid/owner/gid，valid=false，inredo=false；
 *   - 记录 MyLockedGxact，确保后续出错时 AtAbort_Twophase 能释放它。
 * 调用者必须持有 TwoPhaseStateLock 排他锁；子事务数据稍后由
 * GXactLoadSubxactData 填入。
 */
static void
MarkAsPreparingGuts(GlobalTransaction gxact, FullTransactionId fxid,
					const char *gid, TimestampTz prepared_at, Oid owner,
					Oid databaseid)
{
	PGPROC	   *proc;
	int			i;
	TransactionId xid = XidFromFullTransactionId(fxid);

	Assert(LWLockHeldByMeInMode(TwoPhaseStateLock, LW_EXCLUSIVE));

	Assert(gxact != NULL);
	proc = GetPGProcByNumber(gxact->pgprocno);

	/* Initialize the PGPROC entry */
	MemSet(proc, 0, sizeof(PGPROC));
	proc->waitStatus = PROC_WAIT_STATUS_OK;
	if (LocalTransactionIdIsValid(MyProc->vxid.lxid))
	{
		/* clone VXID, for TwoPhaseGetXidByVirtualXID() to find */
		proc->vxid.lxid = MyProc->vxid.lxid;
		proc->vxid.procNumber = MyProcNumber;
	}
	else
	{
		Assert(AmStartupProcess() || !IsPostmasterEnvironment);
		/* GetLockConflicts() uses this to specify a wait on the XID */
		proc->vxid.lxid = xid;
		proc->vxid.procNumber = INVALID_PROC_NUMBER;
	}
	proc->xid = xid;
	Assert(proc->xmin == InvalidTransactionId);
	proc->delayChkptFlags = 0;
	proc->statusFlags = 0;
	proc->pid = 0;
	proc->databaseId = databaseid;
	proc->roleId = owner;
	proc->tempNamespaceId = InvalidOid;
	proc->backendType = B_INVALID;
	proc->lwWaiting = LW_WS_NOT_WAITING;
	proc->lwWaitMode = 0;
	proc->waitLock = NULL;
	dlist_node_init(&proc->waitLink);
	proc->waitProcLock = NULL;
	pg_atomic_init_u64(&proc->waitStart, 0);
	for (i = 0; i < NUM_LOCK_PARTITIONS; i++)
		dlist_init(&proc->myProcLocks[i]);
	/* subxid data must be filled later by GXactLoadSubxactData */
	proc->subxidStatus.overflowed = false;
	proc->subxidStatus.count = 0;

	gxact->prepared_at = prepared_at;
	gxact->fxid = fxid;
	gxact->owner = owner;
	gxact->locking_backend = MyProcNumber;
	gxact->valid = false;
	gxact->inredo = false;
	strlcpy(gxact->gid, gid, GIDSIZE);

	/*
	 * Remember that we have this GlobalTransaction entry locked for us. If we
	 * abort after this, we must release it.
	 */
	MyLockedGxact = gxact;
}

/*
 * GXactLoadSubxactData
 *
 * If the transaction being persisted had any subtransactions, this must
 * be called before MarkAsPrepared() to load information into the dummy
 * PGPROC.
 */
/*
 * 中文注释：
 * 把顶层事务的子事务 XID 列表复制到虚拟 PGPROC 的 subxids 缓存中。
 *
 * ProcArray 用这段缓存快速判断子事务是否属于某个顶层事务；超过
 * PGPROC_MAX_CACHED_SUBXIDS 时不能全部保存，于是把 overflowed 置 true，之后
 * 检查子事务会退化为查询 pg_subtrans。调用时 gxact 尚未 valid，其他进程看不到，
 * 因此不需要额外加锁。
 */
static void
GXactLoadSubxactData(GlobalTransaction gxact, int nsubxacts,
					 TransactionId *children)
{
	PGPROC	   *proc = GetPGProcByNumber(gxact->pgprocno);

	/* We need no extra lock since the GXACT isn't valid yet */
	if (nsubxacts > PGPROC_MAX_CACHED_SUBXIDS)
	{
		proc->subxidStatus.overflowed = true;
		nsubxacts = PGPROC_MAX_CACHED_SUBXIDS;
	}
	if (nsubxacts > 0)
	{
		memcpy(proc->subxids.xids, children,
			   nsubxacts * sizeof(TransactionId));
		proc->subxidStatus.count = nsubxacts;
	}
}

/*
 * MarkAsPrepared
 *		Mark the GXACT as fully valid, and enter it into the global ProcArray.
 *
 * lock_held indicates whether caller already holds TwoPhaseStateLock.
 */
/*
 * 中文注释：
 * 把 gxact 标记为“完全有效”，并加入全局 ProcArray。
 *
 * valid=true 表示 WAL 中的 PREPARE 记录和状态文件都已持久化，其他后端可以对其
 * 执行 COMMIT/ROLLBACK PREPARED。随后 ProcArrayAdd 把虚拟 PGPROC 加入
 * ProcArray，使 TransactionIdIsInProgress 继续认为该 XID 在运行，直到第二阶段
 * 完成。顺序很关键：必须先让虚拟条目可见，再清除原后端的 XID，否则会出现
 * “XID 既不在运行、也尚未 prepared”的窗口。lock_held 允许调用者复用已持有的
 * TwoPhaseStateLock。
 */
static void
MarkAsPrepared(GlobalTransaction gxact, bool lock_held)
{
	/* Lock here may be overkill, but I'm not convinced of that ... */
	if (!lock_held)
		LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
	Assert(!gxact->valid);
	gxact->valid = true;
	if (!lock_held)
		LWLockRelease(TwoPhaseStateLock);

	/*
	 * Put it into the global ProcArray so TransactionIdIsInProgress considers
	 * the XID as still running.
	 */
	ProcArrayAdd(GetPGProcByNumber(gxact->pgprocno));
}

/*
 * LockGXact
 *		Locate the prepared transaction and mark it busy for COMMIT or PREPARE.
 */
/*
 * 中文注释：
 * 按 GID 查找预备事务并将其锁定给当前后端，供 COMMIT/ROLLBACK PREPARED 使用。
 *
 * 在 TwoPhaseStateLock 排他锁下线性扫描 prepXacts，跳过尚未 valid 的条目，找到
 * GID 匹配者后检查：
 *   - locking_backend 必须为空，否则说明另一个后端正在处理，报“is busy”；
 *   - 调用者必须是该事务的 owner 或超级用户；
 *   - 必须在事务准备时所在的数据库内执行，否则 NOTIFY 等机制无法正确工作。
 * 检查通过后设置 locking_backend=MyProcNumber、MyLockedGxact=gxact 并返回。
 * 找不到 GID 时报“does not exist”。锁只保护共享内存状态，实际事务锁仍由虚拟
 * PGPROC 持有。
 */
static GlobalTransaction
LockGXact(const char *gid, Oid user)
{
	int			i;

	/* on first call, register the exit hook */
	if (!twophaseExitRegistered)
	{
		before_shmem_exit(AtProcExit_Twophase, 0);
		twophaseExitRegistered = true;
	}

	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);

	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];
		PGPROC	   *proc = GetPGProcByNumber(gxact->pgprocno);

		/* Ignore not-yet-valid GIDs */
		if (!gxact->valid)
			continue;
		if (strcmp(gxact->gid, gid) != 0)
			continue;

		/* Found it, but has someone else got it locked? */
		if (gxact->locking_backend != INVALID_PROC_NUMBER)
			ereport(ERROR,
					(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
					 errmsg("prepared transaction with identifier \"%s\" is busy",
							gid)));

		if (user != gxact->owner && !superuser_arg(user))
			ereport(ERROR,
					(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
					 errmsg("permission denied to finish prepared transaction"),
					 errhint("Must be superuser or the user that prepared the transaction.")));

		/*
		 * Note: it probably would be possible to allow committing from
		 * another database; but at the moment NOTIFY is known not to work and
		 * there may be some other issues as well.  Hence disallow until
		 * someone gets motivated to make it work.
		 */
		if (MyDatabaseId != proc->databaseId)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("prepared transaction belongs to another database"),
					 errhint("Connect to the database where the transaction was prepared to finish it.")));

		/* OK for me to lock it */
		gxact->locking_backend = MyProcNumber;
		MyLockedGxact = gxact;

		LWLockRelease(TwoPhaseStateLock);

		return gxact;
	}

	LWLockRelease(TwoPhaseStateLock);

	ereport(ERROR,
			(errcode(ERRCODE_UNDEFINED_OBJECT),
			 errmsg("prepared transaction with identifier \"%s\" does not exist",
					gid)));

	/* NOTREACHED */
	return NULL;
}

/*
 * RemoveGXact
 *		Remove the prepared transaction from the shared memory array.
 *
 * NB: caller should have already removed it from ProcArray
 */
/*
 * 中文注释：
 * 从活动数组 prepXacts 中移除 gxact，并把它归还 freeGXacts 空闲链表。
 *
 * 采用“用最后一个元素填补被删位置”的方式，避免移动数组造成指针失效；因此活动
 * 数组不保持任何顺序。调用者必须持有 TwoPhaseStateLock 排他锁，并且应当已经从
 * ProcArray 移除对应的虚拟 PGPROC（见函数头注释）。若传入的指针不在数组中，
 * 说明共享内存状态已损坏，直接 ERROR。
 */
static void
RemoveGXact(GlobalTransaction gxact)
{
	int			i;

	Assert(LWLockHeldByMeInMode(TwoPhaseStateLock, LW_EXCLUSIVE));

	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		if (gxact == TwoPhaseState->prepXacts[i])
		{
			/* remove from the active array */
			TwoPhaseState->numPrepXacts--;
			TwoPhaseState->prepXacts[i] = TwoPhaseState->prepXacts[TwoPhaseState->numPrepXacts];

			/* and put it back in the freelist */
			gxact->next = TwoPhaseState->freeGXacts;
			TwoPhaseState->freeGXacts = gxact;

			return;
		}
	}

	elog(ERROR, "failed to find %p in GlobalTransaction array", gxact);
}

/*
 * Returns an array of all prepared transactions for the user-level
 * function pg_prepared_xact.
 *
 * The returned array and all its elements are copies of internal data
 * structures, to minimize the time we need to hold the TwoPhaseStateLock.
 *
 * WARNING -- we return even those transactions that are not fully prepared
 * yet.  The caller should filter them out if he doesn't want them.
 *
 * The returned array is palloc'd.
 */
/*
 * 中文注释：
 * 复制当前所有预备事务的 GlobalTransactionData 快照，供 pg_prepared_xact 使用。
 *
 * 在共享锁下读取 numPrepXacts 并分配数组，逐项 memcpy 后立即释放锁，尽量缩短
 * 持锁时间、避免 I/O 或返回元组时阻塞 PREPARE/COMMIT PREPARED。注意快照包含
 * 尚未 valid 的条目；调用者（SQL 函数）需要自行过滤。返回数组由 palloc 分配，
 * 调用者负责释放。
 */
static int
GetPreparedTransactionList(GlobalTransaction *gxacts)
{
	GlobalTransaction array;
	int			num;
	int			i;

	LWLockAcquire(TwoPhaseStateLock, LW_SHARED);

	if (TwoPhaseState->numPrepXacts == 0)
	{
		LWLockRelease(TwoPhaseStateLock);

		*gxacts = NULL;
		return 0;
	}

	num = TwoPhaseState->numPrepXacts;
	array = palloc_array(GlobalTransactionData, num);
	*gxacts = array;
	for (i = 0; i < num; i++)
		memcpy(array + i, TwoPhaseState->prepXacts[i],
			   sizeof(GlobalTransactionData));

	LWLockRelease(TwoPhaseStateLock);

	return num;
}


/* Working status for pg_prepared_xact */
typedef struct
{
	GlobalTransaction array;
	int			ngxacts;
	int			currIdx;
} Working_State;

/*
 * pg_prepared_xact
 *		Produce a view with one row per prepared transaction.
 *
 * This function is here so we don't have to export the
 * GlobalTransactionData struct definition.
 */
/*
 * 中文注释：
 * pg_prepared_xact 视图的集合返回函数（SRF），每个预备事务输出一行。
 *
 * 首次调用时在多调用内存上下文中构建 5 列 tupledesc（transaction、gid、
 * prepared、ownerid、dbid），并一次性取得 GetPreparedTransactionList 的快照；
 * 之后每次 SRF_RETURN_NEXT 从快照取一个 valid 条目。跳过 invalid 条目是因为
 * 快照可能包含正在 prepare、尚未写完 WAL 的事务。列定义必须与
 * system_views.sql 中的视图保持一致。
 */
Datum
pg_prepared_xact(PG_FUNCTION_ARGS)
{
	FuncCallContext *funcctx;
	Working_State *status;

	if (SRF_IS_FIRSTCALL())
	{
		TupleDesc	tupdesc;
		MemoryContext oldcontext;

		/* create a function context for cross-call persistence */
		funcctx = SRF_FIRSTCALL_INIT();

		/*
		 * Switch to memory context appropriate for multiple function calls
		 */
		oldcontext = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx);

		/* build tupdesc for result tuples */
		/* this had better match pg_prepared_xacts view in system_views.sql */
		tupdesc = CreateTemplateTupleDesc(5);
		TupleDescInitEntry(tupdesc, (AttrNumber) 1, "transaction",
						   XIDOID, -1, 0);
		TupleDescInitEntry(tupdesc, (AttrNumber) 2, "gid",
						   TEXTOID, -1, 0);
		TupleDescInitEntry(tupdesc, (AttrNumber) 3, "prepared",
						   TIMESTAMPTZOID, -1, 0);
		TupleDescInitEntry(tupdesc, (AttrNumber) 4, "ownerid",
						   OIDOID, -1, 0);
		TupleDescInitEntry(tupdesc, (AttrNumber) 5, "dbid",
						   OIDOID, -1, 0);

		TupleDescFinalize(tupdesc);
		funcctx->tuple_desc = BlessTupleDesc(tupdesc);

		/*
		 * Collect all the 2PC status information that we will format and send
		 * out as a result set.
		 */
		status = palloc_object(Working_State);
		funcctx->user_fctx = status;

		status->ngxacts = GetPreparedTransactionList(&status->array);
		status->currIdx = 0;

		MemoryContextSwitchTo(oldcontext);
	}

	funcctx = SRF_PERCALL_SETUP();
	status = (Working_State *) funcctx->user_fctx;

	while (status->array != NULL && status->currIdx < status->ngxacts)
	{
		GlobalTransaction gxact = &status->array[status->currIdx++];
		PGPROC	   *proc = GetPGProcByNumber(gxact->pgprocno);
		Datum		values[5] = {0};
		bool		nulls[5] = {0};
		HeapTuple	tuple;
		Datum		result;

		if (!gxact->valid)
			continue;

		/*
		 * Form tuple with appropriate data.
		 */

		values[0] = TransactionIdGetDatum(proc->xid);
		values[1] = CStringGetTextDatum(gxact->gid);
		values[2] = TimestampTzGetDatum(gxact->prepared_at);
		values[3] = ObjectIdGetDatum(gxact->owner);
		values[4] = ObjectIdGetDatum(proc->databaseId);

		tuple = heap_form_tuple(funcctx->tuple_desc, values, nulls);
		result = HeapTupleGetDatum(tuple);
		SRF_RETURN_NEXT(funcctx, result);
	}

	SRF_RETURN_DONE(funcctx);
}

/*
 * TwoPhaseGetGXact
 *		Get the GlobalTransaction struct for a prepared transaction
 *		specified by XID
 *
 * If lock_held is set to true, TwoPhaseStateLock will not be taken, so the
 * caller had better hold it.
 */
/*
 * 中文注释：
 * 按 FullTransactionId 查找对应的 GlobalTransaction。
 *
 * 恢复、COMMIT PREPARED、ROLLBACK PREPARED 会针对同一 XID 反复调用，因此用
 * 函数内静态缓存（cached_fxid/cached_gxact）避免重复扫描和加锁。未命中时在
 * 共享锁下线性扫描 prepXacts，比较 fxid；lock_held 为 true 表示调用者已持有
 * TwoPhaseStateLock，此时不再加锁。找不到属于严重状态不一致，直接 ERROR。
 * 缓存不失效，但只在同一 XID 连续处理期间有效，不会返回错误条目。
 */
static GlobalTransaction
TwoPhaseGetGXact(FullTransactionId fxid, bool lock_held)
{
	GlobalTransaction result = NULL;
	int			i;

	static FullTransactionId cached_fxid = {InvalidTransactionId};
	static GlobalTransaction cached_gxact = NULL;

	Assert(!lock_held || LWLockHeldByMe(TwoPhaseStateLock));

	/*
	 * During a recovery, COMMIT PREPARED, or ABORT PREPARED, we'll be called
	 * repeatedly for the same XID.  We can save work with a simple cache.
	 */
	if (FullTransactionIdEquals(fxid, cached_fxid))
		return cached_gxact;

	if (!lock_held)
		LWLockAcquire(TwoPhaseStateLock, LW_SHARED);

	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];

		if (FullTransactionIdEquals(gxact->fxid, fxid))
		{
			result = gxact;
			break;
		}
	}

	if (!lock_held)
		LWLockRelease(TwoPhaseStateLock);

	if (result == NULL)			/* should not happen */
		elog(ERROR, "failed to find GlobalTransaction for xid %u",
			 XidFromFullTransactionId(fxid));

	cached_fxid = fxid;
	cached_gxact = result;

	return result;
}

/*
 * TwoPhaseGetXidByVirtualXID
 *		Lookup VXID among xacts prepared since last startup.
 *
 * (This won't find recovered xacts.)  If more than one matches, return any
 * and set "have_more" to true.  To witness multiple matches, a single
 * proc number must consume 2^32 LXIDs, with no intervening database restart.
 */
/*
 * 中文注释：
 * 按虚拟事务 ID（VXID）查找自本次启动以来 prepare 的事务 XID。
 *
 * 用于 pg_locks 等需要把 VXID 映射回 XID 的场景。恢复出来的预备事务没有原始
 * 本地 VXID（procNumber 为 INVALID_PROC_NUMBER），因此本函数找不到它们，函数头
 * 注释也明确说明了这一点。若多个条目匹配（同一 proc number 在未重启的情况下
 * 用尽 2^32 个 LXID 才可能发生），返回任意一个并把 *have_more 置 true。
 */
TransactionId
TwoPhaseGetXidByVirtualXID(VirtualTransactionId vxid,
						   bool *have_more)
{
	int			i;
	TransactionId result = InvalidTransactionId;

	Assert(VirtualTransactionIdIsValid(vxid));
	LWLockAcquire(TwoPhaseStateLock, LW_SHARED);

	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];
		PGPROC	   *proc;
		VirtualTransactionId proc_vxid;

		if (!gxact->valid)
			continue;
		proc = GetPGProcByNumber(gxact->pgprocno);
		GET_VXID_FROM_PGPROC(proc_vxid, *proc);
		if (VirtualTransactionIdEquals(vxid, proc_vxid))
		{
			/*
			 * Startup process sets proc->vxid.procNumber to
			 * INVALID_PROC_NUMBER.
			 */
			Assert(!gxact->inredo);

			if (result != InvalidTransactionId)
			{
				*have_more = true;
				break;
			}
			result = XidFromFullTransactionId(gxact->fxid);
		}
	}

	LWLockRelease(TwoPhaseStateLock);

	return result;
}

/*
 * TwoPhaseGetDummyProcNumber
 *		Get the dummy proc number for prepared transaction
 *
 * Dummy proc numbers are similar to proc numbers of real backends.  They
 * start at FIRST_PREPARED_XACT_PROC_NUMBER, and are unique across all
 * currently active real backends and prepared transactions.  If lock_held is
 * set to true, TwoPhaseStateLock will not be taken, so the caller had better
 * hold it.
 */
/*
 * 中文注释：
 * 返回预备事务对应的虚拟 ProcNumber。
 *
 * 虚拟 ProcNumber 从 FIRST_PREPARED_XACT_PROC_NUMBER 开始，与真实后端编号不
 * 重叠，因此在锁管理器、ProcArray 等以 ProcNumber 为索引的结构中可以安全使用。
 * 内部复用 TwoPhaseGetGXact；lock_held 语义与之一致。
 */
ProcNumber
TwoPhaseGetDummyProcNumber(FullTransactionId fxid, bool lock_held)
{
	GlobalTransaction gxact = TwoPhaseGetGXact(fxid, lock_held);

	return gxact->pgprocno;
}

/*
 * TwoPhaseGetDummyProc
 *		Get the PGPROC that represents a prepared transaction
 *
 * If lock_held is set to true, TwoPhaseStateLock will not be taken, so the
 * caller had better hold it.
 */
/*
 * 中文注释：
 * 返回预备事务对应的虚拟 PGPROC 指针。
 *
 * 该 PGPROC 保存事务的 xid、databaseId、锁等待状态和锁链表，是预备事务在
 * 共享内存中的“进程替身”。内部先 TwoPhaseGetGXact 再 GetPGProcByNumber。
 */
PGPROC *
TwoPhaseGetDummyProc(FullTransactionId fxid, bool lock_held)
{
	GlobalTransaction gxact = TwoPhaseGetGXact(fxid, lock_held);

	return GetPGProcByNumber(gxact->pgprocno);
}

/************************************************************************/
/* State file support													*/
/************************************************************************/

/*
 * Compute the FullTransactionId for the given TransactionId.
 *
 * This is safe if the xid has not yet reached COMMIT PREPARED or ROLLBACK
 * PREPARED.  After those commands, concurrent vac_truncate_clog() may make
 * the xid cease to qualify as allowable.  XXX Not all callers limit their
 * calls accordingly.
 */
/*
 * 中文注释：
 * 把 32 位 TransactionId 转换为 64 位 FullTransactionId。
 *
 * 以当前 ReadNextFullTransactionId() 为参照，选择使 XID 落在允许范围内的 epoch。
 * 该转换只在 XID 尚未执行 COMMIT/ROLLBACK PREPARED 时安全；之后并发的
 * vac_truncate_clog 可能推进最老 XID，使该 XID 不再“allowable”，转换结果可能
 * 错误。函数头注释也提示并非所有调用者都满足这一限制。
 */
static inline FullTransactionId
AdjustToFullTransactionId(TransactionId xid)
{
	Assert(TransactionIdIsValid(xid));
	return FullTransactionIdFromAllowableAt(ReadNextFullTransactionId(), xid);
}

/*
 * 中文注释：
 * 构造两阶段状态文件路径：pg_twophase/<epoch 8 位 hex><xid 8 位 hex>。
 *
 * 使用完整 64 位事务 ID 命名，避免 XID 回绕后新旧文件互相覆盖。返回 snprintf
 * 的结果，调用者可据此判断是否发生截断（正常 MAXPGPATH 足够）。TWOPHASE_DIR
 * 是相对于数据目录的固定子目录。
 */
static inline int
TwoPhaseFilePath(char *path, FullTransactionId fxid)
{
	return snprintf(path, MAXPGPATH, TWOPHASE_DIR "/%08X%08X",
					EpochFromFullTransactionId(fxid),
					XidFromFullTransactionId(fxid));
}

/*
 * 2PC state file format:
 *
 *	1. TwoPhaseFileHeader
 *	2. TransactionId[] (subtransactions)
 *	3. RelFileLocator[] (files to be deleted at commit)
 *	4. RelFileLocator[] (files to be deleted at abort)
 *	5. SharedInvalidationMessage[] (inval messages to be sent at commit)
 *	6. TwoPhaseRecordOnDisk
 *	7. ...
 *	8. TwoPhaseRecordOnDisk (end sentinel, rmid == TWOPHASE_RM_END_ID)
 *	9. checksum (CRC-32C)
 *
 * Each segment except the final checksum is MAXALIGN'd.
 */

/*
 * Header for a 2PC state file
 */
#define TWOPHASE_MAGIC	0x57F94534	/* format identifier */

typedef xl_xact_prepare TwoPhaseFileHeader;

/*
 * Header for each record in a state file
 *
 * NOTE: len counts only the rmgr data, not the TwoPhaseRecordOnDisk header.
 * The rmgr data will be stored starting on a MAXALIGN boundary.
 */
typedef struct TwoPhaseRecordOnDisk
{
	uint32		len;			/* length of rmgr data */
	TwoPhaseRmgrId rmid;		/* resource manager for this record */
	uint16		info;			/* flag bits for use by rmgr */
} TwoPhaseRecordOnDisk;

/*
 * During prepare, the state file is assembled in memory before writing it
 * to WAL and the actual state file.  We use a chain of StateFileChunk blocks
 * for that.
 */
typedef struct StateFileChunk
{
	char	   *data;
	uint32		len;
	struct StateFileChunk *next;
} StateFileChunk;

static struct xllist
{
	StateFileChunk *head;		/* first data block in the chain */
	StateFileChunk *tail;		/* last block in chain */
	uint32		num_chunks;
	uint32		bytes_free;		/* free bytes left in tail block */
	uint32		total_len;		/* total data bytes in chain */
}			records;


/*
 * Append a block of data to records data structure.
 *
 * NB: each block is padded to a MAXALIGN multiple.  This must be
 * accounted for when the file is later read!
 *
 * The data is copied, so the caller is free to modify it afterwards.
 */
/*
 * 中文注释：
 * 把一段数据追加到内存中的 2PC 状态文件链。
 *
 * 状态文件在写出前由 StateFileChunk 链表拼接而成。每段都按 MAXALIGN 补齐，因此
 * 读取端必须用同样的 MAXALIGN 步进；records.total_len 也累计补齐后的长度。若
 * 当前尾块剩余空间不足，就新分配一个块（至少 512 字节），避免为每个小片段都
 * 分配独立内存。函数会复制数据，调用者随后可以修改或释放原缓冲区。
 */
static void
save_state_data(const void *data, uint32 len)
{
	uint32		padlen = MAXALIGN(len);

	if (padlen > records.bytes_free)
	{
		records.tail->next = palloc0_object(StateFileChunk);
		records.tail = records.tail->next;
		records.tail->len = 0;
		records.tail->next = NULL;
		records.num_chunks++;

		records.bytes_free = Max(padlen, 512);
		records.tail->data = palloc(records.bytes_free);
	}

	memcpy(records.tail->data + records.tail->len, data, len);
	records.tail->len += padlen;
	records.bytes_free -= padlen;
	records.total_len += padlen;
}

/*
 * Start preparing a state file.
 *
 * Initializes data structure and inserts the 2PC file header record.
 */
/*
 * 中文注释：
 * 开始构造 2PC 状态文件：初始化链表并写入文件头及各类附属数组。
 *
 * 收集的信息包括：提交的子事务 XID、提交/中止时需要删除的 relfilenode、提交/
 * 中止时需要执行的统计删除项、以及需要在提交时广播的共享失效消息。文件头中的
 * total_len 暂时留空，由 EndPrepare 回填；origin_lsn/origin_timestamp 也留待
 * EndPrepare 根据复制源状态填写。hdr.gidlen 包含结尾的 '\0'。
 *
 * 子事务列表还会顺便通过 GXactLoadSubxactData 装入虚拟 PGPROC，因为后续
 * ProcArray 检查需要它。所有数据都按 MAXALIGN 追加，读取时必须按相同布局解析。
 */
void
StartPrepare(GlobalTransaction gxact)
{
	PGPROC	   *proc = GetPGProcByNumber(gxact->pgprocno);
	TransactionId xid = XidFromFullTransactionId(gxact->fxid);
	TwoPhaseFileHeader hdr;
	TransactionId *children;
	RelFileLocator *commitrels;
	RelFileLocator *abortrels;
	xl_xact_stats_item *abortstats = NULL;
	xl_xact_stats_item *commitstats = NULL;
	SharedInvalidationMessage *invalmsgs;

	/* Initialize linked list */
	records.head = palloc0_object(StateFileChunk);
	records.head->len = 0;
	records.head->next = NULL;

	records.bytes_free = Max(sizeof(TwoPhaseFileHeader), 512);
	records.head->data = palloc(records.bytes_free);

	records.tail = records.head;
	records.num_chunks = 1;

	records.total_len = 0;

	/* Create header */
	hdr.magic = TWOPHASE_MAGIC;
	hdr.total_len = 0;			/* EndPrepare will fill this in */
	hdr.xid = xid;
	hdr.database = proc->databaseId;
	hdr.prepared_at = gxact->prepared_at;
	hdr.owner = gxact->owner;
	hdr.nsubxacts = xactGetCommittedChildren(&children);
	hdr.ncommitrels = smgrGetPendingDeletes(true, &commitrels);
	hdr.nabortrels = smgrGetPendingDeletes(false, &abortrels);
	hdr.ncommitstats =
		pgstat_get_transactional_drops(true, &commitstats);
	hdr.nabortstats =
		pgstat_get_transactional_drops(false, &abortstats);
	hdr.ninvalmsgs = xactGetCommittedInvalidationMessages(&invalmsgs,
														  &hdr.initfileinval);
	hdr.gidlen = strlen(gxact->gid) + 1;	/* Include '\0' */
	/* EndPrepare will fill the origin data, if necessary */
	hdr.origin_lsn = InvalidXLogRecPtr;
	hdr.origin_timestamp = 0;

	save_state_data(&hdr, sizeof(TwoPhaseFileHeader));
	save_state_data(gxact->gid, hdr.gidlen);

	/*
	 * Add the additional info about subxacts, deletable files and cache
	 * invalidation messages.
	 */
	if (hdr.nsubxacts > 0)
	{
		save_state_data(children, hdr.nsubxacts * sizeof(TransactionId));
		/* While we have the child-xact data, stuff it in the gxact too */
		GXactLoadSubxactData(gxact, hdr.nsubxacts, children);
	}
	if (hdr.ncommitrels > 0)
	{
		save_state_data(commitrels, hdr.ncommitrels * sizeof(RelFileLocator));
		pfree(commitrels);
	}
	if (hdr.nabortrels > 0)
	{
		save_state_data(abortrels, hdr.nabortrels * sizeof(RelFileLocator));
		pfree(abortrels);
	}
	if (hdr.ncommitstats > 0)
	{
		save_state_data(commitstats,
						hdr.ncommitstats * sizeof(xl_xact_stats_item));
		pfree(commitstats);
	}
	if (hdr.nabortstats > 0)
	{
		save_state_data(abortstats,
						hdr.nabortstats * sizeof(xl_xact_stats_item));
		pfree(abortstats);
	}
	if (hdr.ninvalmsgs > 0)
	{
		save_state_data(invalmsgs,
						hdr.ninvalmsgs * sizeof(SharedInvalidationMessage));
		pfree(invalmsgs);
	}
}

/*
 * Finish preparing state data and writing it to WAL.
 */
/*
 * 中文注释：
 * 完成 2PC 状态文件的构造，写 XLOG_XACT_PREPARE 并确保其持久化。
 *
 * 步骤：
 *   1. 追加 TWOPHASE_RM_END_ID 哨兵记录，回填 hdr->total_len（含结尾 CRC）；
 *   2. 若当前事务属于某个复制源，写入 origin_lsn/origin_timestamp；
 *   3. 检查总长不超过 MaxAllocSize，避免以后 ReadTwoPhaseFile 无法一次性读入；
 *   4. 进入临界区并设置 DELAY_CHKPT_START，防止“WAL 已插入但状态文件尚未 fsync
 *      的检查点”完成，从而在崩溃后丢失预备事务；
 *   5. 把链表中所有块注册为 main data，插入 PREPARE 记录，记录 prepare_start_lsn
 *      和 prepare_end_lsn，推进复制源进度并 XLogFlush；
 *   6. 调用 MarkAsPrepared 让虚拟 PGPROC 进入 ProcArray，再清除 delay 标志；
 *   7. 最后等待同步复制（若配置），并清空全局 records 链。
 * 这里不单独计算状态文件 CRC：WAL 记录自身的 CRC 已覆盖全部内容；只有后来把
 * 数据搬到独立文件时才需要额外 CRC（见 RecreateTwoPhaseFile）。
 */
void
EndPrepare(GlobalTransaction gxact)
{
	TwoPhaseFileHeader *hdr;
	StateFileChunk *record;
	bool		replorigin;

	/* Add the end sentinel to the list of 2PC records */
	RegisterTwoPhaseRecord(TWOPHASE_RM_END_ID, 0,
						   NULL, 0);

	/* Go back and fill in total_len in the file header record */
	hdr = (TwoPhaseFileHeader *) records.head->data;
	Assert(hdr->magic == TWOPHASE_MAGIC);
	hdr->total_len = records.total_len + sizeof(pg_crc32c);

	replorigin = (replorigin_xact_state.origin != InvalidReplOriginId &&
				  replorigin_xact_state.origin != DoNotReplicateId);

	if (replorigin)
	{
		hdr->origin_lsn = replorigin_xact_state.origin_lsn;
		hdr->origin_timestamp = replorigin_xact_state.origin_timestamp;
	}

	/*
	 * If the data size exceeds MaxAllocSize, we won't be able to read it in
	 * ReadTwoPhaseFile. Check for that now, rather than fail in the case
	 * where we write data to file and then re-read at commit time.
	 */
	if (hdr->total_len > MaxAllocSize)
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("two-phase state file maximum length exceeded")));

	/*
	 * Now writing 2PC state data to WAL. We let the WAL's CRC protection
	 * cover us, so no need to calculate a separate CRC.
	 *
	 * We have to set DELAY_CHKPT_START here, too; otherwise a checkpoint
	 * starting immediately after the WAL record is inserted could complete
	 * without fsync'ing our state file.  (This is essentially the same kind
	 * of race condition as the COMMIT-to-clog-write case that
	 * RecordTransactionCommit uses DELAY_CHKPT_IN_COMMIT for; see notes
	 * there.) Note that DELAY_CHKPT_IN_COMMIT is used to find transactions in
	 * the critical commit section. We need to know about such transactions
	 * for conflict detection in logical replication. See
	 * GetOldestActiveTransactionId(true, false) and its use.
	 *
	 * We save the PREPARE record's location in the gxact for later use by
	 * CheckPointTwoPhase.
	 */
	XLogEnsureRecordSpace(0, records.num_chunks);

	START_CRIT_SECTION();

	Assert((MyProc->delayChkptFlags & DELAY_CHKPT_START) == 0);
	MyProc->delayChkptFlags |= DELAY_CHKPT_START;

	XLogBeginInsert();
	for (record = records.head; record != NULL; record = record->next)
		XLogRegisterData(record->data, record->len);

	XLogSetRecordFlags(XLOG_INCLUDE_ORIGIN);

	gxact->prepare_end_lsn = XLogInsert(RM_XACT_ID, XLOG_XACT_PREPARE);

	if (replorigin)
	{
		/* Move LSNs forward for this replication origin */
		replorigin_session_advance(replorigin_xact_state.origin_lsn,
								   gxact->prepare_end_lsn);
	}

	XLogFlush(gxact->prepare_end_lsn);

	/* If we crash now, we have prepared: WAL replay will fix things */

	/* Store record's start location to read that later on Commit */
	gxact->prepare_start_lsn = ProcLastRecPtr;

	/*
	 * Mark the prepared transaction as valid.  As soon as xact.c marks MyProc
	 * as not running our XID (which it will do immediately after this
	 * function returns), others can commit/rollback the xact.
	 *
	 * NB: a side effect of this is to make a dummy ProcArray entry for the
	 * prepared XID.  This must happen before we clear the XID from MyProc /
	 * ProcGlobal->xids[], else there is a window where the XID is not running
	 * according to TransactionIdIsInProgress, and onlookers would be entitled
	 * to assume the xact crashed.  Instead we have a window where the same
	 * XID appears twice in ProcArray, which is OK.
	 */
	MarkAsPrepared(gxact, false);

	/*
	 * Now we can mark ourselves as out of the commit critical section: a
	 * checkpoint starting after this will certainly see the gxact as a
	 * candidate for fsyncing.
	 */
	MyProc->delayChkptFlags &= ~DELAY_CHKPT_START;

	/*
	 * Remember that we have this GlobalTransaction entry locked for us.  If
	 * we crash after this point, it's too late to abort, but we must unlock
	 * it so that the prepared transaction can be committed or rolled back.
	 */
	MyLockedGxact = gxact;

	END_CRIT_SECTION();

	/*
	 * Wait for synchronous replication, if required.
	 *
	 * Note that at this stage we have marked the prepare, but still show as
	 * running in the procarray (twice!) and continue to hold locks.
	 */
	SyncRepWaitForLSN(gxact->prepare_end_lsn, false);

	records.tail = records.head = NULL;
	records.num_chunks = 0;
}

/*
 * Register a 2PC record to be written to state file.
 */
/*
 * 中文注释：
 * 向当前 2PC 状态文件追加一条资源管理器记录。
 *
 * 先写 TwoPhaseRecordOnDisk 头（rmid、info、len），再按 len 追加 rmgr 私有数据；
 * 两者都经过 MAXALIGN 补齐。EndPrepare 会追加一个 rmid=TWOPHASE_RM_END_ID 的
 * 哨兵，读取端（ProcessRecords）据此判断结束。rmid 的取值范围由
 * TwoPhaseRmgrId 枚举限制，回调表按 rmid 索引。
 */
void
RegisterTwoPhaseRecord(TwoPhaseRmgrId rmid, uint16 info,
					   const void *data, uint32 len)
{
	TwoPhaseRecordOnDisk record;

	record.rmid = rmid;
	record.info = info;
	record.len = len;
	save_state_data(&record, sizeof(TwoPhaseRecordOnDisk));
	if (len > 0)
		save_state_data(data, len);
}


/*
 * Read and validate the state file for xid.
 *
 * If it looks OK (has a valid magic number and CRC), return the palloc'd
 * contents of the file, issuing an error when finding corrupted data.  If
 * missing_ok is true, which indicates that missing files can be safely
 * ignored, then return NULL.  This state can be reached when doing recovery
 * after discarding two-phase files from frozen epochs.
 */
/*
 * 中文注释：
 * 读取并校验一个 2PC 状态文件，返回 palloc 出来的完整内容。
 *
 * 校验项：文件长度下界（至少能容纳头、哨兵和 CRC）、上界（不超过 MaxAllocSize）、
 * CRC 偏移必须 MAXALIGN 对齐、magic 正确、头部 total_len 与文件实际大小一致、
 * 末尾 CRC-32C 与重算结果一致。任何不一致都按数据损坏报 ERROR，而不是尝试继续，
 * 因为损坏的预备事务无法安全恢复。missing_ok 为 true 且文件不存在时返回 NULL，
 * 用于“被冻结 epoch 清理过的文件在恢复时可以被安全忽略”的场景。读取使用
 * OpenTransientFile，不占用 VFD；等待事件标记为 TWOPHASE_FILE_READ。
 */
static char *
ReadTwoPhaseFile(FullTransactionId fxid, bool missing_ok)
{
	char		path[MAXPGPATH];
	size_t		buflen;
	char	   *buf;
	TwoPhaseFileHeader *hdr;
	int			fd;
	struct stat stat;
	uint32		crc_offset;
	pg_crc32c	calc_crc,
				file_crc;
	ssize_t		r;

	TwoPhaseFilePath(path, fxid);

	fd = OpenTransientFile(path, O_RDONLY | PG_BINARY);
	if (fd < 0)
	{
		if (missing_ok && errno == ENOENT)
			return NULL;

		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not open file \"%s\": %m", path)));
	}

	/*
	 * Check file length.  We can determine a lower bound pretty easily. We
	 * set an upper bound to avoid palloc() failure on a corrupt file, though
	 * we can't guarantee that we won't get an out of memory error anyway,
	 * even on a valid file.
	 */
	if (fstat(fd, &stat))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not stat file \"%s\": %m", path)));

	if (stat.st_size < (MAXALIGN(sizeof(TwoPhaseFileHeader)) +
						MAXALIGN(sizeof(TwoPhaseRecordOnDisk)) +
						sizeof(pg_crc32c)) ||
		stat.st_size > MaxAllocSize)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg_plural("incorrect size of file \"%s\": %lld byte",
							   "incorrect size of file \"%s\": %lld bytes",
							   (long long int) stat.st_size, path,
							   (long long int) stat.st_size)));

	crc_offset = stat.st_size - sizeof(pg_crc32c);
	if (crc_offset != MAXALIGN(crc_offset))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("incorrect alignment of CRC offset for file \"%s\"",
						path)));

	/*
	 * OK, slurp in the file.
	 */
	buflen = stat.st_size;
	buf = (char *) palloc(buflen);

	pgstat_report_wait_start(WAIT_EVENT_TWOPHASE_FILE_READ);
	r = read(fd, buf, buflen);
	if (r != buflen)
	{
		if (r < 0)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not read file \"%s\": %m", path)));
		else
			ereport(ERROR,
					(errmsg("could not read file \"%s\": read %zd of %zu",
							path, r, buflen)));
	}

	pgstat_report_wait_end();

	if (CloseTransientFile(fd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close file \"%s\": %m", path)));

	hdr = (TwoPhaseFileHeader *) buf;
	if (hdr->magic != TWOPHASE_MAGIC)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("invalid magic number stored in file \"%s\"",
						path)));

	if (hdr->total_len != stat.st_size)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("invalid size stored in file \"%s\"",
						path)));

	INIT_CRC32C(calc_crc);
	COMP_CRC32C(calc_crc, buf, crc_offset);
	FIN_CRC32C(calc_crc);

	file_crc = *((pg_crc32c *) (buf + crc_offset));

	if (!EQ_CRC32C(calc_crc, file_crc))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("calculated CRC checksum does not match value stored in file \"%s\"",
						path)));

	return buf;
}


/*
 * Reads 2PC data from xlog. During checkpoint this data will be moved to
 * twophase files and ReadTwoPhaseFile should be used instead.
 *
 * Note clearly that this function can access WAL during normal operation,
 * similarly to the way WALSender or Logical Decoding would do.
 */
/*
 * 中文注释：
 * 从 WAL 中读取一条 XLOG_XACT_PREPARE 记录的 main data，即尚未落盘的 2PC 状态。
 *
 * 预备事务的数据通常先只存在于 WAL 中，只有跨检查点长期存在时才由
 * CheckPointTwoPhase 搬到 pg_twophase 文件。本函数临时分配一个 XLogReader，
 * 从 prepare_start_lsn 开始读一条记录，校验 rmid 为 RM_XACT_ID 且子类型为
 * XLOG_XACT_PREPARE，然后把 main data 复制到 palloc 缓冲区返回。
 *
 * 注意它可以在正常运行期间访问 WAL（类似 walsender/逻辑解码），不要求处于恢复
 * 模式；因此不能假设 WAL 文件一定还在，读不到就报错。调用者负责释放缓冲区，
 * XLogReader 在返回前已释放。
 */
static void
XlogReadTwoPhaseData(XLogRecPtr lsn, char **buf, size_t *len)
{
	XLogRecord *record;
	XLogReaderState *xlogreader;
	char	   *errormsg;

	xlogreader = XLogReaderAllocate(wal_segment_size, NULL,
									XL_ROUTINE(.page_read = &read_local_xlog_page,
											   .segment_open = &wal_segment_open,
											   .segment_close = &wal_segment_close),
									NULL);
	if (!xlogreader)
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of memory"),
				 errdetail("Failed while allocating a WAL reading processor.")));

	XLogBeginRead(xlogreader, lsn);
	record = XLogReadRecord(xlogreader, &errormsg);

	if (record == NULL)
	{
		if (errormsg)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not read two-phase state from WAL at %X/%08X: %s",
							LSN_FORMAT_ARGS(lsn), errormsg)));
		else
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not read two-phase state from WAL at %X/%08X",
							LSN_FORMAT_ARGS(lsn))));
	}

	if (XLogRecGetRmid(xlogreader) != RM_XACT_ID ||
		(XLogRecGetInfo(xlogreader) & XLOG_XACT_OPMASK) != XLOG_XACT_PREPARE)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("expected two-phase state data is not present in WAL at %X/%08X",
						LSN_FORMAT_ARGS(lsn))));

	if (len != NULL)
		*len = XLogRecGetDataLen(xlogreader);

	*buf = palloc_array(char, XLogRecGetDataLen(xlogreader));
	memcpy(*buf, XLogRecGetData(xlogreader), sizeof(char) * XLogRecGetDataLen(xlogreader));

	XLogReaderFree(xlogreader);
}


/*
 * Confirms an xid is prepared, during recovery
 */
/*
 * 中文注释：
 * 在恢复/热备期间判断某个 32 位 XID 是否有对应的 2PC 状态文件。
 *
 * max_prepared_xacts <= 0 时直接返回 false。否则把 XID 转成 FullTransactionId，
 * 以 missing_ok=true 读取文件；文件不存在返回 false。文件存在时还要检查头部
 * 记录的 XID 与请求一致，避免仅凭文件名（可能来自不同 epoch 或损坏）误判。
 * 注意本函数要求该 XID 尚未完成 COMMIT/ROLLBACK PREPARED，否则
 * AdjustToFullTransactionId 可能选错 epoch。
 */
bool
StandbyTransactionIdIsPrepared(TransactionId xid)
{
	char	   *buf;
	TwoPhaseFileHeader *hdr;
	bool		result;
	FullTransactionId fxid;

	Assert(TransactionIdIsValid(xid));

	if (max_prepared_xacts <= 0)
		return false;			/* nothing to do */

	/* Read and validate file */
	fxid = AdjustToFullTransactionId(xid);
	buf = ReadTwoPhaseFile(fxid, true);
	if (buf == NULL)
		return false;

	/* Check header also */
	hdr = (TwoPhaseFileHeader *) buf;
	result = TransactionIdEquals(hdr->xid, xid);
	pfree(buf);

	return result;
}

/*
 * FinishPreparedTransaction: execute COMMIT PREPARED or ROLLBACK PREPARED
 */
/*
 * 中文注释：
 * 执行 COMMIT PREPARED 或 ROLLBACK PREPARED 的完整流程。
 *
 * 1. LockGXact 按 GID 找到并独占 gxact，同时完成权限/数据库检查。
 * 2. 根据 gxact->ondisk 选择从 pg_twophase 文件还是从 WAL 读取状态数据，然后按
 *    固定布局拆出子事务、待删除 relfilenode、统计项和失效消息。
 * 3. 计算 latestXid（含所有子事务），HOLD_INTERRUPTS 防止清理期间被取消。
 * 4. 写第二阶段 WAL 并把 pg_xact 标记为提交/中止：
 *      RecordTransactionCommitPrepared / RecordTransactionAbortPrepared
 * 5. ProcArrayRemove 移除虚拟 PGPROC，使 XID 不再被视为运行；随后把 gxact
 *    valid 置 false，防止回调失败时别人重复处理。
 * 6. 删除应在提交/中止时删除的文件、执行统计删除、提交时广播共享失效消息
 *    （涉及 relcache init 文件时按 AtEOXact_Inval 的顺序前后处理）。
 * 7. 在 TwoPhaseStateLock 下调用各 rmgr 的 postcommit/postabort 回调，释放锁等
 *    资源；然后 RemoveGXact 清空共享内存条目。
 * 8. 更新统计、删除磁盘状态文件、清空 MyLockedGxact、恢复中断并释放缓冲区。
 * 顺序的核心原则是：先让 WAL 和 pg_xact 持久化，再让 XID 从 ProcArray 消失，
 * 最后才释放锁和删除文件；任何一步崩溃都能通过 WAL 重放得到一致状态。
 */
void
FinishPreparedTransaction(const char *gid, bool isCommit)
{
	GlobalTransaction gxact;
	PGPROC	   *proc;
	FullTransactionId fxid;
	TransactionId xid;
	bool		ondisk;
	char	   *buf;
	char	   *bufptr;
	TwoPhaseFileHeader *hdr;
	TransactionId latestXid;
	TransactionId *children;
	RelFileLocator *commitrels;
	RelFileLocator *abortrels;
	RelFileLocator *delrels;
	int			ndelrels;
	xl_xact_stats_item *commitstats;
	xl_xact_stats_item *abortstats;
	SharedInvalidationMessage *invalmsgs;

	/*
	 * Validate the GID, and lock the GXACT to ensure that two backends do not
	 * try to commit the same GID at once.
	 */
	gxact = LockGXact(gid, GetUserId());
	proc = GetPGProcByNumber(gxact->pgprocno);
	fxid = gxact->fxid;
	xid = XidFromFullTransactionId(fxid);

	/*
	 * Read and validate 2PC state data. State data will typically be stored
	 * in WAL files if the LSN is after the last checkpoint record, or moved
	 * to disk if for some reason they have lived for a long time.
	 */
	if (gxact->ondisk)
		buf = ReadTwoPhaseFile(fxid, false);
	else
		XlogReadTwoPhaseData(gxact->prepare_start_lsn, &buf, NULL);


	/*
	 * Disassemble the header area
	 */
	hdr = (TwoPhaseFileHeader *) buf;
	Assert(TransactionIdEquals(hdr->xid, xid));
	bufptr = buf + MAXALIGN(sizeof(TwoPhaseFileHeader));
	bufptr += MAXALIGN(hdr->gidlen);
	children = (TransactionId *) bufptr;
	bufptr += MAXALIGN(hdr->nsubxacts * sizeof(TransactionId));
	commitrels = (RelFileLocator *) bufptr;
	bufptr += MAXALIGN(hdr->ncommitrels * sizeof(RelFileLocator));
	abortrels = (RelFileLocator *) bufptr;
	bufptr += MAXALIGN(hdr->nabortrels * sizeof(RelFileLocator));
	commitstats = (xl_xact_stats_item *) bufptr;
	bufptr += MAXALIGN(hdr->ncommitstats * sizeof(xl_xact_stats_item));
	abortstats = (xl_xact_stats_item *) bufptr;
	bufptr += MAXALIGN(hdr->nabortstats * sizeof(xl_xact_stats_item));
	invalmsgs = (SharedInvalidationMessage *) bufptr;
	bufptr += MAXALIGN(hdr->ninvalmsgs * sizeof(SharedInvalidationMessage));

	/* compute latestXid among all children */
	latestXid = TransactionIdLatest(xid, hdr->nsubxacts, children);

	/* Prevent cancel/die interrupt while cleaning up */
	HOLD_INTERRUPTS();

	/*
	 * The order of operations here is critical: make the XLOG entry for
	 * commit or abort, then mark the transaction committed or aborted in
	 * pg_xact, then remove its PGPROC from the global ProcArray (which means
	 * TransactionIdIsInProgress will stop saying the prepared xact is in
	 * progress), then run the post-commit or post-abort callbacks. The
	 * callbacks will release the locks the transaction held.
	 */
	if (isCommit)
		RecordTransactionCommitPrepared(xid,
										hdr->nsubxacts, children,
										hdr->ncommitrels, commitrels,
										hdr->ncommitstats,
										commitstats,
										hdr->ninvalmsgs, invalmsgs,
										hdr->initfileinval, gid);
	else
		RecordTransactionAbortPrepared(xid,
									   hdr->nsubxacts, children,
									   hdr->nabortrels, abortrels,
									   hdr->nabortstats,
									   abortstats,
									   gid);

	ProcArrayRemove(proc, latestXid);

	/*
	 * In case we fail while running the callbacks, mark the gxact invalid so
	 * no one else will try to commit/rollback, and so it will be recycled if
	 * we fail after this point.  It is still locked by our backend so it
	 * won't go away yet.
	 *
	 * (We assume it's safe to do this without taking TwoPhaseStateLock.)
	 */
	gxact->valid = false;

	/*
	 * We have to remove any files that were supposed to be dropped. For
	 * consistency with the regular xact.c code paths, must do this before
	 * releasing locks, so do it before running the callbacks.
	 *
	 * NB: this code knows that we couldn't be dropping any temp rels ...
	 */
	if (isCommit)
	{
		delrels = commitrels;
		ndelrels = hdr->ncommitrels;
	}
	else
	{
		delrels = abortrels;
		ndelrels = hdr->nabortrels;
	}

	/* Make sure files supposed to be dropped are dropped */
	DropRelationFiles(delrels, ndelrels, false);

	if (isCommit)
		pgstat_execute_transactional_drops(hdr->ncommitstats, commitstats, false);
	else
		pgstat_execute_transactional_drops(hdr->nabortstats, abortstats, false);

	/*
	 * Handle cache invalidation messages.
	 *
	 * Relcache init file invalidation requires processing both before and
	 * after we send the SI messages, only when committing.  See
	 * AtEOXact_Inval().
	 */
	if (isCommit)
	{
		if (hdr->initfileinval)
			RelationCacheInitFilePreInvalidate();
		SendSharedInvalidMessages(invalmsgs, hdr->ninvalmsgs);
		if (hdr->initfileinval)
			RelationCacheInitFilePostInvalidate();
	}

	/*
	 * Acquire the two-phase lock.  We want to work on the two-phase callbacks
	 * while holding it to avoid potential conflicts with other transactions
	 * attempting to use the same GID, so the lock is released once the shared
	 * memory state is cleared.
	 */
	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);

	/* And now do the callbacks */
	if (isCommit)
		ProcessRecords(bufptr, fxid, twophase_postcommit_callbacks);
	else
		ProcessRecords(bufptr, fxid, twophase_postabort_callbacks);

	PredicateLockTwoPhaseFinish(fxid, isCommit);

	/*
	 * Read this value while holding the two-phase lock, as the on-disk 2PC
	 * file is physically removed after the lock is released.
	 */
	ondisk = gxact->ondisk;

	/* Clear shared memory state */
	RemoveGXact(gxact);

	/*
	 * Release the lock as all callbacks are called and shared memory cleanup
	 * is done.
	 */
	LWLockRelease(TwoPhaseStateLock);

	/* Count the prepared xact as committed or aborted */
	AtEOXact_PgStat(isCommit, false);

	/*
	 * And now we can clean up any files we may have left.
	 */
	if (ondisk)
		RemoveTwoPhaseFile(fxid, true);

	MyLockedGxact = NULL;

	RESUME_INTERRUPTS();

	pfree(buf);
}

/*
 * Scan 2PC state data in memory and call the indicated callbacks for each 2PC record.
 */
/*
 * 中文注释：
 * 遍历 2PC 状态文件中的 rmgr 记录，对每条调用对应的回调。
 *
 * 记录以 TWOPHASE_RM_END_ID 哨兵结束；回调表按 rmid 索引，允许某些 rmid 的回调
 * 为 NULL（表示该 rmgr 不需要在 commit/abort/recover 时做额外工作）。bufptr 按
 * MAXALIGN 步进：先跨过 TwoPhaseRecordOnDisk 头，再跨过 record->len 对齐后的
 * 数据。函数只读缓冲区，不负责释放。
 */
static void
ProcessRecords(char *bufptr, FullTransactionId fxid,
			   const TwoPhaseCallback callbacks[])
{
	for (;;)
	{
		TwoPhaseRecordOnDisk *record = (TwoPhaseRecordOnDisk *) bufptr;

		Assert(record->rmid <= TWOPHASE_RM_MAX_ID);
		if (record->rmid == TWOPHASE_RM_END_ID)
			break;

		bufptr += MAXALIGN(sizeof(TwoPhaseRecordOnDisk));

		if (callbacks[record->rmid] != NULL)
			callbacks[record->rmid] (fxid, record->info, bufptr, record->len);

		bufptr += MAXALIGN(record->len);
	}
}

/*
 * Remove the 2PC file.
 *
 * If giveWarning is false, do not complain about file-not-present;
 * this is an expected case during WAL replay.
 *
 * This routine is used at early stages at recovery where future and
 * past orphaned files are checked, hence the FullTransactionId to build
 * a complete file name fit for the removal.
 */
/*
 * 中文注释：
 * 删除指定 FullTransactionId 的 2PC 状态文件。
 *
 * giveWarning 为 false 时，文件不存在（ENOENT）被视为正常，不发出警告；WAL 重放
 * 中多次处理同一事务时这是常见情况。其他 unlink 错误一律 WARNING，因为删除失败
 * 不会立刻破坏一致性，但会留下垃圾文件，需要 DBA 注意。恢复早期检查“未来/过去
 * 的孤儿文件”时也会调用本函数，因此使用完整 64 位 ID 构造文件名。
 */
static void
RemoveTwoPhaseFile(FullTransactionId fxid, bool giveWarning)
{
	char		path[MAXPGPATH];

	TwoPhaseFilePath(path, fxid);
	if (unlink(path))
		if (errno != ENOENT || giveWarning)
			ereport(WARNING,
					(errcode_for_file_access(),
					 errmsg("could not remove file \"%s\": %m", path)));
}

/*
 * Recreates a state file. This is used in WAL replay and during
 * checkpoint creation.
 *
 * Note: content and len don't include CRC.
 */
/*
 * 中文注释：
 * 根据内存中的内容重建一个 2PC 状态文件，并重新计算 CRC。
 *
 * 用于 WAL 重放（把 PREPARE 数据落到 pg_twophase）和 CheckPointTwoPhase（把
 * 长期存活的预备事务从 WAL 搬到磁盘）。content/len 不包含 CRC，函数先算
 * CRC-32C，再以 O_CREAT|O_TRUNC 写入内容和 CRC。写入后必须 pg_fsync：恢复结束
 * 时的检查点看不到尚未进入共享内存的 GXACT，不会替我们同步这个文件。任何打开、
 * 写入、fsync、关闭失败都按文件访问错误报 ERROR。
 */
static void
RecreateTwoPhaseFile(FullTransactionId fxid, const void *content, size_t len)
{
	char		path[MAXPGPATH];
	pg_crc32c	statefile_crc;
	int			fd;

	/* Recompute CRC */
	INIT_CRC32C(statefile_crc);
	COMP_CRC32C(statefile_crc, content, len);
	FIN_CRC32C(statefile_crc);

	TwoPhaseFilePath(path, fxid);

	fd = OpenTransientFile(path,
						   O_CREAT | O_TRUNC | O_WRONLY | PG_BINARY);
	if (fd < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not recreate file \"%s\": %m", path)));

	/* Write content and CRC */
	errno = 0;
	pgstat_report_wait_start(WAIT_EVENT_TWOPHASE_FILE_WRITE);
	if (write(fd, content, len) != len)
	{
		/* if write didn't set errno, assume problem is no disk space */
		if (errno == 0)
			errno = ENOSPC;
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write file \"%s\": %m", path)));
	}
	if (write(fd, &statefile_crc, sizeof(pg_crc32c)) != sizeof(pg_crc32c))
	{
		/* if write didn't set errno, assume problem is no disk space */
		if (errno == 0)
			errno = ENOSPC;
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write file \"%s\": %m", path)));
	}
	pgstat_report_wait_end();

	/*
	 * We must fsync the file because the end-of-replay checkpoint will not do
	 * so, there being no GXACT in shared memory yet to tell it to.
	 */
	pgstat_report_wait_start(WAIT_EVENT_TWOPHASE_FILE_SYNC);
	if (pg_fsync(fd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not fsync file \"%s\": %m", path)));
	pgstat_report_wait_end();

	if (CloseTransientFile(fd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close file \"%s\": %m", path)));
}

/*
 * CheckPointTwoPhase -- handle 2PC component of checkpointing.
 *
 * We must fsync the state file of any GXACT that is valid or has been
 * generated during redo and has a PREPARE LSN <= the checkpoint's redo
 * horizon.  (If the gxact isn't valid yet, has not been generated in
 * redo, or has a later LSN, this checkpoint is not responsible for
 * fsyncing it.)
 *
 * This is deliberately run as late as possible in the checkpoint sequence,
 * because GXACTs ordinarily have short lifespans, and so it is quite
 * possible that GXACTs that were valid at checkpoint start will no longer
 * exist if we wait a little bit. With typical checkpoint settings this
 * will be about 3 minutes for an online checkpoint, so as a result we
 * expect that there will be no GXACTs that need to be copied to disk.
 *
 * If a GXACT remains valid across multiple checkpoints, it will already
 * be on disk so we don't bother to repeat that write.
 */
/*
 * 中文注释：
 * 检查点中负责 2PC 的部分：把需要在本次检查点之前持久化的预备事务写到磁盘。
 *
 * 判据是 (valid || inredo) && !ondisk && prepare_end_lsn <= redo_horizon。满足
 * 条件的 gxact 其 PREPARE WAL 可能在本检查点之后被回收，因此必须把状态数据
 * 物化成 pg_twophase 文件。这里故意把该步骤放在检查点接近尾声时执行：预备事务
 * 通常很短命，等到这时很多 gxact 可能已经提交/回滚，从而避免不必要的 I/O。
 *
 * 为了简化，所有 I/O 都在 TwoPhaseStateLock 共享锁下完成；这能防止新事务在此
 * 期间 prepare，也不会与提交者并发修改同一 gxact。已有 ondisk 的条目不会重复写。
 * 最后无条件 fsync pg_twophase 目录，使新建和删除都持久化。delayChkptFlags
 * 保证不会出现“prepare_end_lsn 早于上一检查点但 valid 尚未设置”的条目。
 */
void
CheckPointTwoPhase(XLogRecPtr redo_horizon)
{
	int			i;
	int			serialized_xacts = 0;

	if (max_prepared_xacts <= 0)
		return;					/* nothing to do */

	TRACE_POSTGRESQL_TWOPHASE_CHECKPOINT_START();

	/*
	 * We are expecting there to be zero GXACTs that need to be copied to
	 * disk, so we perform all I/O while holding TwoPhaseStateLock for
	 * simplicity. This prevents any new xacts from preparing while this
	 * occurs, which shouldn't be a problem since the presence of long-lived
	 * prepared xacts indicates the transaction manager isn't active.
	 *
	 * It's also possible to move I/O out of the lock, but on every error we
	 * should check whether somebody committed our transaction in different
	 * backend. Let's leave this optimization for future, if somebody will
	 * spot that this place cause bottleneck.
	 *
	 * Note that it isn't possible for there to be a GXACT with a
	 * prepare_end_lsn set prior to the last checkpoint yet is marked invalid,
	 * because of the efforts with delayChkptFlags.
	 */
	LWLockAcquire(TwoPhaseStateLock, LW_SHARED);
	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		/*
		 * Note that we are using gxact not PGPROC so this works in recovery
		 * also
		 */
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];

		if ((gxact->valid || gxact->inredo) &&
			!gxact->ondisk &&
			gxact->prepare_end_lsn <= redo_horizon)
		{
			char	   *buf;
			size_t		len;

			XlogReadTwoPhaseData(gxact->prepare_start_lsn, &buf, &len);
			RecreateTwoPhaseFile(gxact->fxid, buf, len);
			gxact->ondisk = true;
			gxact->prepare_start_lsn = InvalidXLogRecPtr;
			gxact->prepare_end_lsn = InvalidXLogRecPtr;
			pfree(buf);
			serialized_xacts++;
		}
	}
	LWLockRelease(TwoPhaseStateLock);

	/*
	 * Flush unconditionally the parent directory to make any information
	 * durable on disk.  Two-phase files could have been removed and those
	 * removals need to be made persistent as well as any files newly created
	 * previously since the last checkpoint.
	 */
	fsync_fname(TWOPHASE_DIR, true);

	TRACE_POSTGRESQL_TWOPHASE_CHECKPOINT_DONE();

	if (log_checkpoints && serialized_xacts > 0)
		ereport(LOG,
				(errmsg_plural("%u two-phase state file was written "
							   "for a long-running prepared transaction",
							   "%u two-phase state files were written "
							   "for long-running prepared transactions",
							   serialized_xacts,
							   serialized_xacts)));
}

/*
 * restoreTwoPhaseData
 *
 * Scan pg_twophase and fill TwoPhaseState depending on the on-disk data.
 * This is called once at the beginning of recovery, saving any extra
 * lookups in the future.  Two-phase files that are newer than the
 * minimum XID horizon are discarded on the way.
 */
/*
 * 中文注释：
 * 恢复开始时扫描 pg_twophase 目录，把磁盘上的预备事务装入共享内存。
 *
 * 只处理文件名为 16 个十六进制字符的普通状态文件（完整 64 位事务 ID）。对每个
 * 文件调用 ProcessTwoPhaseBuffer，它会丢弃已经提交/中止或 XID 过于未来的陈旧
 * 文件；有效文件通过 PrepareRedoAdd 加入 TwoPhaseState，此时 start_lsn 为
 * InvalidXLogRecPtr，表示数据在磁盘上。这样后续 WAL 重放遇到相同 PREPARE 记录时
 * 可以快速识别并避免重复添加。整个扫描持有 TwoPhaseStateLock 排他锁。
 */
void
restoreTwoPhaseData(void)
{
	DIR		   *cldir;
	struct dirent *clde;

	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
	cldir = AllocateDir(TWOPHASE_DIR);
	while ((clde = ReadDir(cldir, TWOPHASE_DIR)) != NULL)
	{
		if (strlen(clde->d_name) == 16 &&
			strspn(clde->d_name, "0123456789ABCDEF") == 16)
		{
			FullTransactionId fxid;
			char	   *buf;

			fxid = FullTransactionIdFromU64(strtou64(clde->d_name, NULL, 16));

			buf = ProcessTwoPhaseBuffer(fxid, InvalidXLogRecPtr,
										true, false, false);
			if (buf == NULL)
				continue;

			PrepareRedoAdd(fxid, buf, InvalidXLogRecPtr,
						   InvalidXLogRecPtr, InvalidReplOriginId);
		}
	}
	LWLockRelease(TwoPhaseStateLock);
	FreeDir(cldir);
}

/*
 * PrescanPreparedTransactions
 *
 * Scan the shared memory entries of TwoPhaseState and determine the range
 * of valid XIDs present.  This is run during database startup, after we
 * have completed reading WAL.  TransamVariables->nextXid has been set to
 * one more than the highest XID for which evidence exists in WAL.
 *
 * We throw away any prepared xacts with main XID beyond nextXid --- if any
 * are present, it suggests that the DBA has done a PITR recovery to an
 * earlier point in time without cleaning out pg_twophase.  We dare not
 * try to recover such prepared xacts since they likely depend on database
 * state that doesn't exist now.
 *
 * However, we will advance nextXid beyond any subxact XIDs belonging to
 * valid prepared xacts.  We need to do this since subxact commit doesn't
 * write a WAL entry, and so there might be no evidence in WAL of those
 * subxact XIDs.
 *
 * On corrupted two-phase files, fail immediately.  Keeping around broken
 * entries and let replay continue causes harm on the system, and a new
 * backup should be rolled in.
 *
 * Our other responsibility is to determine and return the oldest valid XID
 * among the prepared xacts (if none, return TransamVariables->nextXid).
 * This is needed to synchronize pg_subtrans startup properly.
 *
 * If xids_p and nxids_p are not NULL, pointer to a palloc'd array of all
 * top-level xids is stored in *xids_p. The number of entries in the array
 * is returned in *nxids_p.
 */
/*
 * 中文注释：
 * 在恢复读完 WAL 之后、数据库开始接受连接之前，预扫描所有预备事务。
 *
 * 主要职责：
 *   1. 用 ProcessTwoPhaseBuffer 校验每个 gxact 的状态数据；主 XID 不早于
 *      nextXid 的条目被视为 PITR 到过去时间点后残留的“未来事务”，直接丢弃；
 *   2. 把有效预备事务的子事务 XID 纳入 nextXid 推进：子事务提交不写 WAL，因此
 *      WAL 中可能没有它们的证据，不推进会导致后续分配重复 XID；
 *   3. 返回所有有效预备事务中最小的顶层 XID，供 pg_subtrans 启动时确定下界；
 *      若没有预备事务则返回原 nextXid；
 *   4. 可选地把所有顶层 XID 复制到 palloc 数组，供调用者进一步使用。
 * 损坏的状态文件会立即报错，而不是带着坏条目继续恢复。调用期间持有
 * TwoPhaseStateLock 排他锁。
 */
TransactionId
PrescanPreparedTransactions(TransactionId **xids_p, int *nxids_p)
{
	FullTransactionId nextXid = TransamVariables->nextXid;
	TransactionId origNextXid = XidFromFullTransactionId(nextXid);
	TransactionId result = origNextXid;
	TransactionId *xids = NULL;
	int			nxids = 0;
	int			allocsize = 0;
	int			i;

	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		TransactionId xid;
		char	   *buf;
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];

		Assert(gxact->inredo);

		buf = ProcessTwoPhaseBuffer(gxact->fxid,
									gxact->prepare_start_lsn,
									gxact->ondisk, false, true);

		if (buf == NULL)
			continue;

		/*
		 * OK, we think this file is valid.  Incorporate xid into the
		 * running-minimum result.
		 */
		xid = XidFromFullTransactionId(gxact->fxid);
		if (TransactionIdPrecedes(xid, result))
			result = xid;

		if (xids_p)
		{
			if (nxids == allocsize)
			{
				if (nxids == 0)
				{
					allocsize = 10;
					xids = palloc(allocsize * sizeof(TransactionId));
				}
				else
				{
					allocsize = allocsize * 2;
					xids = repalloc(xids, allocsize * sizeof(TransactionId));
				}
			}
			xids[nxids++] = xid;
		}

		pfree(buf);
	}
	LWLockRelease(TwoPhaseStateLock);

	if (xids_p)
	{
		*xids_p = xids;
		*nxids_p = nxids;
	}

	return result;
}

/*
 * StandbyRecoverPreparedTransactions
 *
 * Scan the shared memory entries of TwoPhaseState and setup all the required
 * information to allow standby queries to treat prepared transactions as still
 * active.
 *
 * This is never called at the end of recovery - we use
 * RecoverPreparedTransactions() at that point.
 *
 * This updates pg_subtrans, so that any subtransactions will be correctly
 * seen as in-progress in snapshots taken during recovery.
 */
/*
 * 中文注释：
 * 热备模式下重建预备事务的子事务映射，使备库快照能正确把它们视为运行中。
 *
 * 与 RecoverPreparedTransactions 不同，本函数在恢复尚未结束时调用，只做
 * setParent：把每个子事务的父 XID 写入 pg_subtrans。这样备库查询在构造快照时，
 * 遇到这些子事务会追溯到顶层预备事务，从而判断其仍在运行。函数不重新获取锁，
 * 也不清除 inredo 标志；这些留给恢复结束时的 RecoverPreparedTransactions。
 */
void
StandbyRecoverPreparedTransactions(void)
{
	int			i;

	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		char	   *buf;
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];

		Assert(gxact->inredo);

		buf = ProcessTwoPhaseBuffer(gxact->fxid,
									gxact->prepare_start_lsn,
									gxact->ondisk, true, false);
		if (buf != NULL)
			pfree(buf);
	}
	LWLockRelease(TwoPhaseStateLock);
}

/*
 * RecoverPreparedTransactions
 *
 * Scan the shared memory entries of TwoPhaseState and reload the state for
 * each prepared transaction (reacquire locks, etc).
 *
 * This is run at the end of recovery, but before we allow backends to write
 * WAL.
 *
 * At the end of recovery the way we take snapshots will change. We now need
 * to mark all running transactions with their full SubTransSetParent() info
 * to allow normal snapshots to work correctly if snapshots overflow.
 * We do this here because by definition prepared transactions are the only
 * type of write transaction still running, so this is necessary and
 * complete.
 */
/*
 * 中文注释：
 * 恢复结束时重新装载所有预备事务的完整状态（尤其是锁）。
 *
 * 对每个由 redo 添加的 gxact：
 *   1. 读取并校验状态数据，丢弃陈旧/未来条目；
 *   2. 从头中取出 GID、子事务列表，重建虚拟 PGPROC 的 subxids，并调用
 *      MarkAsPreparingGuts/MarkAsPrepared 让它重新进入 ProcArray；
 *   3. 释放 TwoPhaseStateLock 后调用 twophase_recover_callbacks，让各 rmgr
 *      （特别是锁管理器）重新获取事务持有的锁；
 *   4. 热备时释放备库进程为冲突检测临时持有的锁；
 *   5. PostPrepare_Twophase 清除 MyLockedGxact。
 * 这里把子事务直接挂到顶层 XID，而不恢复原始层次结构：快照只需要知道“属于哪个
 * 顶层事务”，精确的父子链在重启后已无意义。函数在允许后端写 WAL 之前运行。
 */
void
RecoverPreparedTransactions(void)
{
	int			i;

	LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		char	   *buf;
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];
		FullTransactionId fxid = gxact->fxid;
		char	   *bufptr;
		TwoPhaseFileHeader *hdr;
		TransactionId *subxids;
		const char *gid;

		/*
		 * Reconstruct subtrans state for the transaction --- needed because
		 * pg_subtrans is not preserved over a restart.  Note that we are
		 * linking all the subtransactions directly to the top-level XID;
		 * there may originally have been a more complex hierarchy, but
		 * there's no need to restore that exactly. It's possible that
		 * SubTransSetParent has been set before, if the prepared transaction
		 * generated xid assignment records.
		 */
		buf = ProcessTwoPhaseBuffer(gxact->fxid,
									gxact->prepare_start_lsn,
									gxact->ondisk, true, false);
		if (buf == NULL)
			continue;

		ereport(LOG,
				(errmsg("recovering prepared transaction %u of epoch %u from shared memory",
						XidFromFullTransactionId(gxact->fxid),
						EpochFromFullTransactionId(gxact->fxid))));

		hdr = (TwoPhaseFileHeader *) buf;
		Assert(TransactionIdEquals(hdr->xid,
								   XidFromFullTransactionId(gxact->fxid)));
		bufptr = buf + MAXALIGN(sizeof(TwoPhaseFileHeader));
		gid = (const char *) bufptr;
		bufptr += MAXALIGN(hdr->gidlen);
		subxids = (TransactionId *) bufptr;
		bufptr += MAXALIGN(hdr->nsubxacts * sizeof(TransactionId));
		bufptr += MAXALIGN(hdr->ncommitrels * sizeof(RelFileLocator));
		bufptr += MAXALIGN(hdr->nabortrels * sizeof(RelFileLocator));
		bufptr += MAXALIGN(hdr->ncommitstats * sizeof(xl_xact_stats_item));
		bufptr += MAXALIGN(hdr->nabortstats * sizeof(xl_xact_stats_item));
		bufptr += MAXALIGN(hdr->ninvalmsgs * sizeof(SharedInvalidationMessage));

		/*
		 * Recreate its GXACT and dummy PGPROC. But, check whether it was
		 * added in redo and already has a shmem entry for it.
		 */
		MarkAsPreparingGuts(gxact, gxact->fxid, gid,
							hdr->prepared_at,
							hdr->owner, hdr->database);

		/* recovered, so reset the flag for entries generated by redo */
		gxact->inredo = false;

		GXactLoadSubxactData(gxact, hdr->nsubxacts, subxids);
		MarkAsPrepared(gxact, true);

		LWLockRelease(TwoPhaseStateLock);

		/*
		 * Recover other state (notably locks) using resource managers.
		 */
		ProcessRecords(bufptr, fxid, twophase_recover_callbacks);

		/*
		 * Release locks held by the standby process after we process each
		 * prepared transaction. As a result, we don't need too many
		 * additional locks at any one time.
		 */
		if (InHotStandby)
			StandbyReleaseLockTree(hdr->xid, hdr->nsubxacts, subxids);

		/*
		 * We're done with recovering this transaction. Clear MyLockedGxact,
		 * like we do in PrepareTransaction() during normal operation.
		 */
		PostPrepare_Twophase();

		pfree(buf);

		LWLockAcquire(TwoPhaseStateLock, LW_EXCLUSIVE);
	}

	LWLockRelease(TwoPhaseStateLock);
}

/*
 * ProcessTwoPhaseBuffer
 *
 * Given a FullTransactionId, read it either from disk or read it directly
 * via shmem xlog record pointer using the provided "prepare_start_lsn".
 *
 * If setParent is true, set up subtransaction parent linkages.
 *
 * If setNextXid is true, set TransamVariables->nextXid to the newest
 * value scanned.
 */
/*
 * 中文注释：
 * 读取并校验一个预备事务的状态数据，是恢复路径的公共核心。
 *
 * 数据来源二选一：fromdisk 为 true 时读 pg_twophase 文件，否则按
 * prepare_start_lsn 从 WAL 读取。读取前先做两项淘汰：
 *   - XID 已经 commit/abort：说明是陈旧数据，删除文件或共享内存条目后返回 NULL；
 *   - fxid >= nextXid：说明是 PITR 到过去时间点后残留的“未来事务”，同样删除。
 * 读取后校验头部 xid 与请求一致，然后遍历子事务列表：
 *   - setNextXid 时用 AdvanceNextFullTransactionIdPastXid 推进全局 nextXid；
 *   - setParent 时用 SubTransSetParent 建立 pg_subtrans 映射。
 * 调用者必须持有 TwoPhaseStateLock 排他锁，并负责 pfree 返回的缓冲区。
 */
static char *
ProcessTwoPhaseBuffer(FullTransactionId fxid,
					  XLogRecPtr prepare_start_lsn,
					  bool fromdisk,
					  bool setParent, bool setNextXid)
{
	FullTransactionId nextXid = TransamVariables->nextXid;
	TransactionId *subxids;
	char	   *buf;
	TwoPhaseFileHeader *hdr;
	int			i;

	Assert(LWLockHeldByMeInMode(TwoPhaseStateLock, LW_EXCLUSIVE));

	if (!fromdisk)
		Assert(XLogRecPtrIsValid(prepare_start_lsn));

	/* Already processed? */
	if (TransactionIdDidCommit(XidFromFullTransactionId(fxid)) ||
		TransactionIdDidAbort(XidFromFullTransactionId(fxid)))
	{
		if (fromdisk)
		{
			ereport(WARNING,
					(errmsg("removing stale two-phase state file for transaction %u of epoch %u",
							XidFromFullTransactionId(fxid),
							EpochFromFullTransactionId(fxid))));
			RemoveTwoPhaseFile(fxid, true);
		}
		else
		{
			ereport(WARNING,
					(errmsg("removing stale two-phase state from memory for transaction %u of epoch %u",
							XidFromFullTransactionId(fxid),
							EpochFromFullTransactionId(fxid))));
			PrepareRedoRemoveFull(fxid, true);
		}
		return NULL;
	}

	/* Reject XID if too new */
	if (FullTransactionIdFollowsOrEquals(fxid, nextXid))
	{
		if (fromdisk)
		{
			ereport(WARNING,
					(errmsg("removing future two-phase state file for transaction %u of epoch %u",
							XidFromFullTransactionId(fxid),
							EpochFromFullTransactionId(fxid))));
			RemoveTwoPhaseFile(fxid, true);
		}
		else
		{
			ereport(WARNING,
					(errmsg("removing future two-phase state from memory for transaction %u of epoch %u",
							XidFromFullTransactionId(fxid),
							EpochFromFullTransactionId(fxid))));
			PrepareRedoRemoveFull(fxid, true);
		}
		return NULL;
	}

	if (fromdisk)
	{
		/* Read and validate file */
		buf = ReadTwoPhaseFile(fxid, false);
	}
	else
	{
		/* Read xlog data */
		XlogReadTwoPhaseData(prepare_start_lsn, &buf, NULL);
	}

	/* Deconstruct header */
	hdr = (TwoPhaseFileHeader *) buf;
	if (!TransactionIdEquals(hdr->xid, XidFromFullTransactionId(fxid)))
	{
		if (fromdisk)
			ereport(ERROR,
					(errcode(ERRCODE_DATA_CORRUPTED),
					 errmsg("corrupted two-phase state file for transaction %u of epoch %u",
							XidFromFullTransactionId(fxid),
							EpochFromFullTransactionId(fxid))));
		else
			ereport(ERROR,
					(errcode(ERRCODE_DATA_CORRUPTED),
					 errmsg("corrupted two-phase state in memory for transaction %u of epoch %u",
							XidFromFullTransactionId(fxid),
							EpochFromFullTransactionId(fxid))));
	}

	/*
	 * Examine subtransaction XIDs ... they should all follow main XID, and
	 * they may force us to advance nextXid.
	 */
	subxids = (TransactionId *) (buf +
								 MAXALIGN(sizeof(TwoPhaseFileHeader)) +
								 MAXALIGN(hdr->gidlen));
	for (i = 0; i < hdr->nsubxacts; i++)
	{
		TransactionId subxid = subxids[i];

		Assert(TransactionIdFollows(subxid, XidFromFullTransactionId(fxid)));

		/* update nextXid if needed */
		if (setNextXid)
			AdvanceNextFullTransactionIdPastXid(subxid);

		if (setParent)
			SubTransSetParent(subxid, XidFromFullTransactionId(fxid));
	}

	return buf;
}


/*
 *	RecordTransactionCommitPrepared
 *
 * This is basically the same as RecordTransactionCommit (q.v. if you change
 * this function): in particular, we must set DELAY_CHKPT_IN_COMMIT to avoid a
 * race condition.
 *
 * We know the transaction made at least one XLOG entry (its PREPARE),
 * so it is never possible to optimize out the commit record.
 */
/*
 * 中文注释：
 * 为 COMMIT PREPARED 写提交 WAL、刷盘并在 pg_xact 中标记提交。
 *
 * 与普通 RecordTransactionCommit 结构相同，关键点是 DELAY_CHKPT_IN_COMMIT：
 * 在写提交时间戳之前设置该标志，确保检查点不会在 clog 更新完成前推进，也确保
 * 逻辑复制冲突检测能看到所有已取得提交时间戳的事务。随后调用
 * XactLogCommitRecord 写 XLOG_XACT_COMMIT_PREPARED（强制带上
 * XACT_FLAGS_ACQUIREDACCESSEXCLUSIVELOCK，因为 2PC 无法准确知道是否持有
 * AccessExclusiveLock），推进复制源、记录 commit timestamp，XLogFlush 后调用
 * TransactionIdCommitTree 更新 pg_xact。最后等待同步复制，并清除 delay 标志。
 * 2PC 不支持异步提交，因此这里总是同步刷 WAL。
 */
static void
RecordTransactionCommitPrepared(TransactionId xid,
								int nchildren,
								TransactionId *children,
								int nrels,
								RelFileLocator *rels,
								int nstats,
								xl_xact_stats_item *stats,
								int ninvalmsgs,
								SharedInvalidationMessage *invalmsgs,
								bool initfileinval,
								const char *gid)
{
	XLogRecPtr	recptr;
	TimestampTz committs;
	bool		replorigin;

	/*
	 * Are we using the replication origins feature?  Or, in other words, are
	 * we replaying remote actions?
	 */
	replorigin = (replorigin_xact_state.origin != InvalidReplOriginId &&
				  replorigin_xact_state.origin != DoNotReplicateId);

	/* Load the injection point before entering the critical section */
	INJECTION_POINT_LOAD("commit-after-delay-checkpoint");

	START_CRIT_SECTION();

	/* See notes in RecordTransactionCommit */
	Assert((MyProc->delayChkptFlags & DELAY_CHKPT_IN_COMMIT) == 0);
	MyProc->delayChkptFlags |= DELAY_CHKPT_IN_COMMIT;

	INJECTION_POINT_CACHED("commit-after-delay-checkpoint", NULL);

	/*
	 * Ensures the DELAY_CHKPT_IN_COMMIT flag write is globally visible before
	 * commit time is written.
	 */
	pg_write_barrier();

	/*
	 * Note it is important to set committs value after marking ourselves as
	 * in the commit critical section (DELAY_CHKPT_IN_COMMIT). This is because
	 * we want to ensure all transactions that have acquired commit timestamp
	 * are finished before we allow the logical replication client to advance
	 * its xid which is used to hold back dead rows for conflict detection.
	 * See comments atop worker.c.
	 */
	committs = GetCurrentTimestamp();

	/*
	 * Emit the XLOG commit record. Note that we mark 2PC commits as
	 * potentially having AccessExclusiveLocks since we don't know whether or
	 * not they do.
	 */
	recptr = XactLogCommitRecord(committs,
								 nchildren, children, nrels, rels,
								 nstats, stats,
								 ninvalmsgs, invalmsgs,
								 initfileinval,
								 MyXactFlags | XACT_FLAGS_ACQUIREDACCESSEXCLUSIVELOCK,
								 xid, gid);


	if (replorigin)
		/* Move LSNs forward for this replication origin */
		replorigin_session_advance(replorigin_xact_state.origin_lsn,
								   XactLastRecEnd);

	/*
	 * Record commit timestamp.  The value comes from plain commit timestamp
	 * if replorigin is not enabled, or replorigin already set a value for us
	 * in replorigin_xact_state.origin_timestamp otherwise.
	 *
	 * We don't need to WAL-log anything here, as the commit record written
	 * above already contains the data.
	 */
	if (!replorigin || replorigin_xact_state.origin_timestamp == 0)
		replorigin_xact_state.origin_timestamp = committs;

	TransactionTreeSetCommitTsData(xid, nchildren, children,
								   replorigin_xact_state.origin_timestamp,
								   replorigin_xact_state.origin);

	/*
	 * We don't currently try to sleep before flush here ... nor is there any
	 * support for async commit of a prepared xact (the very idea is probably
	 * a contradiction)
	 */

	/* Flush XLOG to disk */
	XLogFlush(recptr);

	/* Mark the transaction committed in pg_xact */
	TransactionIdCommitTree(xid, nchildren, children);

	/* Checkpoint can proceed now */
	MyProc->delayChkptFlags &= ~DELAY_CHKPT_IN_COMMIT;

	END_CRIT_SECTION();

	/*
	 * Wait for synchronous replication, if required.
	 *
	 * Note that at this stage we have marked clog, but still show as running
	 * in the procarray and continue to hold locks.
	 */
	SyncRepWaitForLSN(recptr, true);
}

/*
 *	RecordTransactionAbortPrepared
 *
 * This is basically the same as RecordTransactionAbort.
 *
 * We know the transaction made at least one XLOG entry (its PREPARE),
 * so it is never possible to optimize out the abort record.
 */
/*
 * 中文注释：
 * 为 ROLLBACK PREPARED 写中止 WAL、刷盘并在 pg_xact 中标记中止。
 *
 * 进入临界区前先检查该 XID 是否已经提交；若是则 PANIC，说明第二阶段状态机被
 * 破坏，继续下去会造成提交/中止不一致。随后写 XLOG_XACT_ABORT_PREPARED，
 * 推进复制源，XLogFlush（因为马上要删除状态文件），再调用
 * TransactionIdAbortTree 更新 pg_xact。虽然 pg_xact 标记中止不是绝对必要，但
 * 顺手完成可以避免后续查询反复推断。最后等待同步复制。
 */
static void
RecordTransactionAbortPrepared(TransactionId xid,
							   int nchildren,
							   TransactionId *children,
							   int nrels,
							   RelFileLocator *rels,
							   int nstats,
							   xl_xact_stats_item *stats,
							   const char *gid)
{
	XLogRecPtr	recptr;
	bool		replorigin;

	/*
	 * Are we using the replication origins feature?  Or, in other words, are
	 * we replaying remote actions?
	 */
	replorigin = (replorigin_xact_state.origin != InvalidReplOriginId &&
				  replorigin_xact_state.origin != DoNotReplicateId);

	/*
	 * Catch the scenario where we aborted partway through
	 * RecordTransactionCommitPrepared ...
	 */
	if (TransactionIdDidCommit(xid))
		elog(PANIC, "cannot abort transaction %u, it was already committed",
			 xid);

	START_CRIT_SECTION();

	/*
	 * Emit the XLOG commit record. Note that we mark 2PC aborts as
	 * potentially having AccessExclusiveLocks since we don't know whether or
	 * not they do.
	 */
	recptr = XactLogAbortRecord(GetCurrentTimestamp(),
								nchildren, children,
								nrels, rels,
								nstats, stats,
								MyXactFlags | XACT_FLAGS_ACQUIREDACCESSEXCLUSIVELOCK,
								xid, gid);

	if (replorigin)
		/* Move LSNs forward for this replication origin */
		replorigin_session_advance(replorigin_xact_state.origin_lsn,
								   XactLastRecEnd);

	/* Always flush, since we're about to remove the 2PC state file */
	XLogFlush(recptr);

	/*
	 * Mark the transaction aborted in clog.  This is not absolutely necessary
	 * but we may as well do it while we are here.
	 */
	TransactionIdAbortTree(xid, nchildren, children);

	END_CRIT_SECTION();

	/*
	 * Wait for synchronous replication, if required.
	 *
	 * Note that at this stage we have marked clog, but still show as running
	 * in the procarray and continue to hold locks.
	 */
	SyncRepWaitForLSN(recptr, false);
}

/*
 * PrepareRedoAdd
 *
 * Store pointers to the start/end of the WAL record along with the xid in
 * a gxact entry in shared memory TwoPhaseState structure.  If caller
 * specifies InvalidXLogRecPtr as WAL location to fetch the two-phase
 * data, the entry is marked as located on disk.
 */
/*
 * 中文注释：
 * WAL 重放 XLOG_XACT_PREPARE 时，在共享内存中登记一个 gxact。
 *
 * 若传入的 fxid 无效（旧格式 WAL 只有 32 位 XID），用
 * FullTransactionIdFromAllowableAt 结合 nextXid 还原 64 位 ID。然后从空闲链表取
 * 实体，填写 prepared_at、prepare_start_lsn/end_lsn、fxid、owner、gid，设置
 * inredo=true、valid=false；数据在磁盘上时 ondisk=true。
 *
 * 特殊处理“检查点崩溃后磁盘文件与 WAL 记录重复”的情况：若 start_lsn 有效且
 * pg_twophase 中已存在同名文件，说明 restoreTwoPhaseData 已经恢复过该事务，此时
 * 跳过本条记录（达到一致性后报 ERROR，否则只 WARNING），避免共享内存出现重复
 * 条目。若记录来自复制源，还会推进 origin 的应用进度。
 */
void
PrepareRedoAdd(FullTransactionId fxid, char *buf,
			   XLogRecPtr start_lsn, XLogRecPtr end_lsn,
			   ReplOriginId origin_id)
{
	TwoPhaseFileHeader *hdr = (TwoPhaseFileHeader *) buf;
	char	   *bufptr;
	const char *gid;
	GlobalTransaction gxact;

	Assert(LWLockHeldByMeInMode(TwoPhaseStateLock, LW_EXCLUSIVE));
	Assert(RecoveryInProgress());

	if (!FullTransactionIdIsValid(fxid))
	{
		Assert(InRecovery);
		fxid = FullTransactionIdFromAllowableAt(TransamVariables->nextXid,
												hdr->xid);
	}

	bufptr = buf + MAXALIGN(sizeof(TwoPhaseFileHeader));
	gid = (const char *) bufptr;

	/*
	 * Reserve the GID for the given transaction in the redo code path.
	 *
	 * This creates a gxact struct and puts it into the active array.
	 *
	 * In redo, this struct is mainly used to track PREPARE/COMMIT entries in
	 * shared memory. Hence, we only fill up the bare minimum contents here.
	 * The gxact also gets marked with gxact->inredo set to true to indicate
	 * that it got added in the redo phase
	 */

	/*
	 * In the event of a crash while a checkpoint was running, it may be
	 * possible that some two-phase data found its way to disk while its
	 * corresponding record needs to be replayed in the follow-up recovery. As
	 * the 2PC data was on disk, it has already been restored at the beginning
	 * of recovery with restoreTwoPhaseData(), so skip this record to avoid
	 * duplicates in TwoPhaseState.  If a consistent state has been reached,
	 * the record is added to TwoPhaseState and it should have no
	 * corresponding file in pg_twophase.
	 */
	if (XLogRecPtrIsValid(start_lsn))
	{
		char		path[MAXPGPATH];

		Assert(InRecovery);
		TwoPhaseFilePath(path, fxid);

		if (access(path, F_OK) == 0)
		{
			ereport(reachedConsistency ? ERROR : WARNING,
					(errmsg("could not recover two-phase state file for transaction %u",
							hdr->xid),
					 errdetail("Two-phase state file has been found in WAL record %X/%08X, but this transaction has already been restored from disk.",
							   LSN_FORMAT_ARGS(start_lsn))));
			return;
		}

		if (errno != ENOENT)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not access file \"%s\": %m", path)));
	}

	/* Get a free gxact from the freelist */
	if (TwoPhaseState->freeGXacts == NULL)
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("maximum number of prepared transactions reached"),
				 errhint("Increase \"max_prepared_transactions\" (currently %d).",
						 max_prepared_xacts)));
	gxact = TwoPhaseState->freeGXacts;
	TwoPhaseState->freeGXacts = gxact->next;

	gxact->prepared_at = hdr->prepared_at;
	gxact->prepare_start_lsn = start_lsn;
	gxact->prepare_end_lsn = end_lsn;
	gxact->fxid = fxid;
	gxact->owner = hdr->owner;
	gxact->locking_backend = INVALID_PROC_NUMBER;
	gxact->valid = false;
	gxact->ondisk = !XLogRecPtrIsValid(start_lsn);
	gxact->inredo = true;		/* yes, added in redo */
	strlcpy(gxact->gid, gid, GIDSIZE);

	/* And insert it into the active array */
	Assert(TwoPhaseState->numPrepXacts < max_prepared_xacts);
	TwoPhaseState->prepXacts[TwoPhaseState->numPrepXacts++] = gxact;

	if (origin_id != InvalidReplOriginId)
	{
		/* recover apply progress */
		replorigin_advance(origin_id, hdr->origin_lsn, end_lsn,
						   false /* backward */ , false /* WAL */ );
	}

	elog(DEBUG2, "added 2PC data in shared memory for transaction %u of epoch %u",
		 XidFromFullTransactionId(gxact->fxid),
		 EpochFromFullTransactionId(gxact->fxid));
}

/*
 * PrepareRedoRemoveFull
 *
 * Remove the corresponding gxact entry from TwoPhaseState. Also remove
 * the 2PC file if a prepared transaction was saved via an earlier checkpoint.
 *
 * Caller must hold TwoPhaseStateLock in exclusive mode, because TwoPhaseState
 * is updated.
 */
/*
 * 中文注释：
 * 在 WAL 重放 COMMIT/ROLLBACK PREPARED 时，从共享内存移除对应 gxact。
 *
 * 先按 FullTransactionId 在 prepXacts 中查找；找不到直接返回，这是重放的正常
 * 情况（例如该 PREPARE 记录早于恢复起点）。找到后要求 gxact->inredo 为真，
 * 若条目在磁盘上则删除 pg_twophase 文件，然后调用 RemoveGXact 归还空闲链表。
 * 调用者必须持有 TwoPhaseStateLock 排他锁，且只能处于恢复模式。
 */
static void
PrepareRedoRemoveFull(FullTransactionId fxid, bool giveWarning)
{
	GlobalTransaction gxact = NULL;
	int			i;
	bool		found = false;

	Assert(LWLockHeldByMeInMode(TwoPhaseStateLock, LW_EXCLUSIVE));
	Assert(RecoveryInProgress());

	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		gxact = TwoPhaseState->prepXacts[i];

		if (FullTransactionIdEquals(gxact->fxid, fxid))
		{
			Assert(gxact->inredo);
			found = true;
			break;
		}
	}

	/*
	 * Just leave if there is nothing, this is expected during WAL replay.
	 */
	if (!found)
		return;

	/*
	 * And now we can clean up any files we may have left.
	 */
	elog(DEBUG2, "removing 2PC data for transaction %u of epoch %u ",
		 XidFromFullTransactionId(fxid),
		 EpochFromFullTransactionId(fxid));

	if (gxact->ondisk)
		RemoveTwoPhaseFile(fxid, giveWarning);

	RemoveGXact(gxact);
}

/*
 * Wrapper of PrepareRedoRemoveFull(), for TransactionIds.
 */
/*
 * 中文注释：
 * PrepareRedoRemoveFull 的 32 位 XID 包装。
 *
 * 用 FullTransactionIdFromAllowableAt 依据当前 nextXid 还原 epoch，然后执行完整
 * 移除逻辑。用于重放只携带 TransactionId 的旧式 COMMIT/ROLLBACK PREPARED
 * 记录。
 */
void
PrepareRedoRemove(TransactionId xid, bool giveWarning)
{
	FullTransactionId fxid =
		FullTransactionIdFromAllowableAt(TransamVariables->nextXid, xid);

	PrepareRedoRemoveFull(fxid, giveWarning);
}

/*
 * LookupGXact
 *		Check if the prepared transaction with the given GID, lsn and timestamp
 *		exists.
 *
 * Note that we always compare with the LSN where prepare ends because that is
 * what is stored as origin_lsn in the 2PC file.
 *
 * This function is primarily used to check if the prepared transaction
 * received from the upstream (remote node) already exists. Checking only GID
 * is not sufficient because a different prepared xact with the same GID can
 * exist on the same node. So, we are ensuring to match origin_lsn and
 * origin_timestamp of prepared xact to avoid the possibility of a match of
 * prepared xact from two different nodes.
 */
/*
 * 中文注释：
 * 判断具有给定 GID、prepare_end_lsn 和 origin 时间戳的预备事务是否已经存在。
 *
 * 仅比较 GID 不够：不同上游节点可能碰巧使用相同 GID，因此还要比对状态文件头中
 * 的 origin_lsn 和 origin_timestamp。这里刻意比较 prepare_end_lsn，因为该值就是
 * 写入 2PC 文件 origin_lsn 的内容。
 *
 * 在 TwoPhaseStateLock 共享锁下扫描 valid 条目；命中 GID 后读取状态文件（磁盘或
 * WAL）取出头部比较。函数头注释说明：当前把所有 I/O 放在锁内以简化并发处理，
 * 前提是发布端与订阅端 GID 冲突极少；若将来冲突频繁，可以在确保无人并发完成
 * 该事务的前提下把 I/O 移出锁外。
 */
bool
LookupGXact(const char *gid, XLogRecPtr prepare_end_lsn,
			TimestampTz origin_prepare_timestamp)
{
	int			i;
	bool		found = false;

	LWLockAcquire(TwoPhaseStateLock, LW_SHARED);
	for (i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];

		/* Ignore not-yet-valid GIDs. */
		if (gxact->valid && strcmp(gxact->gid, gid) == 0)
		{
			char	   *buf;
			TwoPhaseFileHeader *hdr;

			/*
			 * We are not expecting collisions of GXACTs (same gid) between
			 * publisher and subscribers, so we perform all I/O while holding
			 * TwoPhaseStateLock for simplicity.
			 *
			 * To move the I/O out of the lock, we need to ensure that no
			 * other backend commits the prepared xact in the meantime. We can
			 * do this optimization if we encounter many collisions in GID
			 * between publisher and subscriber.
			 */
			if (gxact->ondisk)
				buf = ReadTwoPhaseFile(gxact->fxid, false);
			else
			{
				Assert(gxact->prepare_start_lsn);
				XlogReadTwoPhaseData(gxact->prepare_start_lsn, &buf, NULL);
			}

			hdr = (TwoPhaseFileHeader *) buf;

			if (hdr->origin_lsn == prepare_end_lsn &&
				hdr->origin_timestamp == origin_prepare_timestamp)
			{
				found = true;
				pfree(buf);
				break;
			}

			pfree(buf);
		}
	}
	LWLockRelease(TwoPhaseStateLock);
	return found;
}

/*
 * TwoPhaseTransactionGid
 *		Form the prepared transaction GID for two_phase transactions.
 *
 * Return the GID in the supplied buffer.
 */
/*
 * 中文注释：
 * 为逻辑复制订阅端的二阶段事务生成固定格式的 GID：pg_gid_<subid>_<xid>。
 *
 * subid 是订阅 OID，xid 是事务 ID。该格式使 LookupGXactBySubid 能从 GID 反解出
 * 订阅并判断是否已有对应的预备事务，从而在订阅端重启后避免重复准备。xid 无效
 * 属于协议错误，直接 ERROR；结果写入调用者提供的缓冲区，szgid 用于防止溢出。
 */
void
TwoPhaseTransactionGid(Oid subid, TransactionId xid, char *gid_res, int szgid)
{
	Assert(OidIsValid(subid));

	if (!TransactionIdIsValid(xid))
		ereport(ERROR,
				(errcode(ERRCODE_PROTOCOL_VIOLATION),
				 errmsg_internal("invalid two-phase transaction ID")));

	snprintf(gid_res, szgid, "pg_gid_%u_%u", subid, xid);
}

/*
 * IsTwoPhaseTransactionGidForSubid
 *		Check whether the given GID (as formed by TwoPhaseTransactionGid) is
 *		for the specified 'subid'.
 */
/*
 * 中文注释：
 * 判断一个 GID 是否由 TwoPhaseTransactionGid 为指定 subid 生成。
 *
 * 先用 sscanf 严格解析 "pg_gid_%u_%u"；格式不符或 subid 不匹配立即返回 false。
 * 然后把解析出的 subid/xid 重新格式化，并与原 GID 做完整字符串比较。这样做可以
 * 排除前导零、多余字符、数值溢出等 sscanf 宽松解析造成的误匹配，保证只有完全
 * 符合规范格式的 GID 才被认作订阅事务。
 */
static bool
IsTwoPhaseTransactionGidForSubid(Oid subid, char *gid)
{
	int			ret;
	Oid			subid_from_gid;
	TransactionId xid_from_gid;
	char		gid_tmp[GIDSIZE];

	/* Extract the subid and xid from the given GID */
	ret = sscanf(gid, "pg_gid_%u_%u", &subid_from_gid, &xid_from_gid);

	/*
	 * Check that the given GID has expected format, and at least the subid
	 * matches.
	 */
	if (ret != 2 || subid != subid_from_gid)
		return false;

	/*
	 * Reconstruct a temporary GID based on the subid and xid extracted from
	 * the given GID and check whether the temporary GID and the given GID
	 * match.
	 */
	TwoPhaseTransactionGid(subid, xid_from_gid, gid_tmp, sizeof(gid_tmp));

	return strcmp(gid, gid_tmp) == 0;
}

/*
 * LookupGXactBySubid
 *		Check if the prepared transaction done by apply worker exists.
 */
/*
 * 中文注释：
 * 判断某个订阅（subid）是否已经有处于 prepared 状态的事务。
 *
 * 在共享锁下遍历 valid 的 gxact，用 IsTwoPhaseTransactionGidForSubid 检查 GID
 * 格式。逻辑复制应用进程在准备事务前调用它，若已存在则说明之前已经执行过
 * PREPARE，应改为继续完成 COMMIT/ROLLBACK PREPARED，避免重复创建。
 */
bool
LookupGXactBySubid(Oid subid)
{
	bool		found = false;

	LWLockAcquire(TwoPhaseStateLock, LW_SHARED);
	for (int i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];

		/* Ignore not-yet-valid GIDs. */
		if (gxact->valid &&
			IsTwoPhaseTransactionGidForSubid(subid, gxact->gid))
		{
			found = true;
			break;
		}
	}
	LWLockRelease(TwoPhaseStateLock);

	return found;
}

/*
 * TwoPhaseGetOldestXidInCommit
 *		Return the oldest transaction ID from prepared transactions that are
 *		currently in the commit critical section.
 *
 * This function only considers transactions in the currently connected
 * database. If no matching transactions are found, it returns
 * InvalidTransactionId.
 */
/*
 * 中文注释：
 * 返回当前数据库中正处于提交临界区（DELAY_CHKPT_IN_COMMIT）的预备事务里最老的 XID。
 *
 * 只考虑 valid 且被某个后端锁定的 gxact；通过 locking_backend 找到该后端，再检查
 * 它是否与当前数据库相同并处于提交临界区。持锁访问该 PGPROC 是安全的：后端只有
 * 在移除或解锁 gxact 之后才可能退出，而这两者都需要 TwoPhaseStateLock 排他锁。
 * 结果用于逻辑复制冲突检测中防止死元组被过早回收；没有匹配事务时返回
 * InvalidTransactionId。
 */
TransactionId
TwoPhaseGetOldestXidInCommit(void)
{
	TransactionId oldestRunningXid = InvalidTransactionId;

	LWLockAcquire(TwoPhaseStateLock, LW_SHARED);

	for (int i = 0; i < TwoPhaseState->numPrepXacts; i++)
	{
		GlobalTransaction gxact = TwoPhaseState->prepXacts[i];
		PGPROC	   *commitproc;
		TransactionId xid;

		if (!gxact->valid)
			continue;

		if (gxact->locking_backend == INVALID_PROC_NUMBER)
			continue;

		/*
		 * Get the backend that is handling the transaction. It's safe to
		 * access this backend while holding TwoPhaseStateLock, as the backend
		 * can only be destroyed after either removing or unlocking the
		 * current global transaction, both of which require an exclusive
		 * TwoPhaseStateLock.
		 */
		commitproc = GetPGProcByNumber(gxact->locking_backend);

		if (MyDatabaseId != commitproc->databaseId)
			continue;

		if ((commitproc->delayChkptFlags & DELAY_CHKPT_IN_COMMIT) == 0)
			continue;

		xid = XidFromFullTransactionId(gxact->fxid);

		if (!TransactionIdIsValid(oldestRunningXid) ||
			TransactionIdPrecedes(xid, oldestRunningXid))
			oldestRunningXid = xid;
	}

	LWLockRelease(TwoPhaseStateLock);

	return oldestRunningXid;
}
