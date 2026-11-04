/*-------------------------------------------------------------------------
 *
 * varsup.c
 *	  postgres OID & XID variables support routines
 *
 * Copyright (c) 2000-2026, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *	  src/backend/access/transam/varsup.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 集群级的 OID 与 XID 分配器，以及 XID 回卷（wraparound）
 * 保护逻辑，主要包含：
 *   1. GetNewTransactionId：从共享内存的 nextXid 分配新的 FullTransactionId，并把
 *      32 位 XID 发布到 ProcArray（PGPROC / ProcGlobal->xids / 子事务缓存）；
 *   2. ReadNextFullTransactionId / AdvanceNextFullTransactionIdPastXid：读取 nextXid，
 *      或在恢复、两阶段提交启动等场景下把 nextXid 推进到某个 XID 之后；
 *   3. SetTransactionIdLimit / ForceTransactionIdLimitUpdate：根据全集群最老的
 *      datfrozenxid 计算强制 autovacuum、告警、拒绝分配等阈值，并在接近回卷时发出
 *      信号或报错；
 *   4. AdvanceOldestClogXid：推进可以安全查询 pg_xact（CLOG）的最老 XID 下界；
 *   5. GetNewObjectId / SetNextObjectId / StopGeneratingPinnedObjectIds：集群级 OID
 *      计数器及 OID 的 WAL 预分配。
 *
 * 核心数据结构是共享内存中的 TransamVariablesData（由全局指针 TransamVariables
 * 指向）。其中 nextOid/oidCount 由 OidGenLock 保护；nextXid 以及 oldestXid、
 * xidVacLimit、xidWarnLimit、xidStopLimit、xidWrapLimit、oldestXidDB 由 XidGenLock
 * 保护；oldestClogXid 由 XactTruncationLock 保护。该结构在 postmaster 启动时通过
 * VarsupShmemCallbacks 注册，并由 ShmemRequestStruct() 分配。
 *
 * 与其他模块的关系：xact.c 通过 AssignTransactionId() 调用 GetNewTransactionId()；
 * CLOG、commit timestamp、subtrans 模块依赖本文件保证“先扩展状态空间、再推进
 * nextXid”的顺序；procarray.c 依赖本文件把新 XID 及时发布到 ProcArray；vacuum.c 与
 * xlog.c 则调用 SetTransactionIdLimit() 刷新回卷保护阈值。
 *
 * 关键设计思想：
 *   - XID 分配是集群级、集中式且必须与持久化状态保持顺序的：nextXid 的推进必须晚于
 *     pg_xact/pg_commit_ts/pg_subtrans 的扩展，否则崩溃恢复后可能查到不存在的状态；
 *   - 使用 32 位 TransactionId 加 epoch 组成 FullTransactionId，消除回卷带来的歧义；
 *   - 事务只在真正需要时才分配 XID（惰性分配），以减少 XID 消耗；
 *   - 接近回卷时逐级升级保护（触发 autovacuum、WARNING、拒绝新事务），给 DBA 留出
 *     足够的处理时间；
 *   - OID 采用 WAL 批量预分配（VAR_OID_PREFETCH），避免每分配一个 OID 都写 WAL。
 */

#include "postgres.h"

#include "access/clog.h"
#include "access/commit_ts.h"
#include "access/subtrans.h"
#include "access/transam.h"
#include "access/xact.h"
#include "access/xlogutils.h"
#include "miscadmin.h"
#include "postmaster/autovacuum.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/subsystems.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"


/* Number of OIDs to prefetch (preallocate) per XLOG write */
/*
 * 中文注释：
 * 每次写 WAL 时预分配（预记录）的 OID 数量。GetNewObjectId() 在 oidCount 用尽时，
 * 会把 nextOid + VAR_OID_PREFETCH 作为“下一个可用 OID 上界”写入 WAL
 * （XLogPutNextOid），并把 oidCount 设为该值。这样无需为每个 OID 都写一条 WAL
 * 记录；崩溃恢复时 nextOid 至少会被恢复到该预留上界，避免重新发放已经使用过的
 * OID 区间（即使 WAL 未及落盘，调用方仍会做 OID 冲突检查兜底）。
 */
#define VAR_OID_PREFETCH		8192

/*
 * 中文注释：
 * VarsupShmemRequest 的前置声明，供下面的 VarsupShmemCallbacks 引用。具体说明见
 * 函数定义处。
 */
static void VarsupShmemRequest(void *arg);

/* pointer to variables struct in shared memory */
/*
 * 中文注释：
 * 指向共享内存中的 TransamVariablesData，是集群级 XID/OID 分配状态的唯一实例。
 * 该结构由 VarsupShmemRequest() 在 postmaster 启动阶段通过 ShmemRequestStruct()
 * 申请，并由 shmem 框架在分配或挂接后写入本指针；各后端通过它访问同一份状态。
 * 字段的并发访问规则：
 *   - nextOid / oidCount 由 OidGenLock 保护；
 *   - nextXid、oldestXid、xidVacLimit、xidWarnLimit、xidStopLimit、xidWrapLimit、
 *     oldestXidDB 由 XidGenLock 保护；
 *   - oldestClogXid 由 XactTruncationLock 保护；
 *   - 其余字段（如 latestCompletedXid、xactCompletionCount）由各自所属模块的锁保护。
 * 读取时通常需要持有相应的 LWLock，以获得一组彼此一致的阈值；不要无锁地把多个字段
 * 拼在一起做判断。
 */
TransamVariablesData *TransamVariables = NULL;

/*
 * 中文注释：
 * 本模块注册给 shmem 子系统的回调集合（通过 storage/subsystemlist.h 中的
 * PG_SHMEM_SUBSYSTEM(VarsupShmemCallbacks) 引入）。
 * request_fn 在 postmaster 启动、共享内存尚未实际分配时被调用，用来登记
 * TransamVariablesData 的大小和用于接收地址的全局指针。这里没有 init_fn 或
 * attach_fn：结构体字段的初值由启动/检查点恢复流程写入，而指针由 shmem 框架在
 * 分配或挂接时自动设置。
 */
const ShmemCallbacks VarsupShmemCallbacks = {
	.request_fn = VarsupShmemRequest,
};

/*
 * Request shared memory for TransamVariables.
 */
/*
 * 中文注释：
 * shmem request 回调：向共享内存框架申请一块大小为 sizeof(TransamVariablesData)、
 * 名称为 "TransamVariables" 的区域，并把分配后的地址写入全局指针
 * TransamVariables。
 *
 * 调用场景：postmaster 启动阶段，由 shmem 框架在共享内存实际分配之前调用；这是
 * 现代 PostgreSQL 用回调方式替代在 ipci.c 中集中申请共享内存的机制。
 *
 * 参数 arg：shmem 框架传入的 opaque 参数，本模块不使用。
 * 并发/副作用：只在 postmaster 启动的单进程上下文中执行，不存在并发问题；函数本身
 * 不初始化任何字段，仅登记需求并让框架回填指针。
 */
static void
VarsupShmemRequest(void *arg)
{
	ShmemRequestStruct(.name = "TransamVariables",
					   .size = sizeof(TransamVariablesData),
					   .ptr = (void **) &TransamVariables,
		);
}

/*
 * Allocate the next FullTransactionId for a new transaction or
 * subtransaction.
 *
 * The new XID is also stored into MyProc->xid/ProcGlobal->xids[] before
 * returning.
 *
 * Note: when this is called, we are actually already inside a valid
 * transaction, since XIDs are now not allocated until the transaction
 * does something.  So it is safe to do a database lookup if we want to
 * issue a warning about XID wrap.
 */
/*
 * 中文注释：
 * 从集群级计数器分配下一个 FullTransactionId，并立即把其中的 32 位 XID 发布到
 * 当前后端的 PGPROC（ProcGlobal->xids 或子事务缓存）中。
 *
 * 调用场景：xact.c 的 AssignTransactionId() 在事务第一次真正需要 XID 时调用本函数，
 * 实现 XID 的惰性分配。isSubXact 为 true 表示正在为子事务分配 XID，此时 XID 写入
 * PGPROC->subxids 缓存（或置溢出标志）；为 false 表示顶层事务，写入 PGPROC->xid
 * 与 ProcGlobal->xids[]。
 *
 * 返回值：本次分配到的 FullTransactionId（包含 epoch），此时 nextXid 已经递增。
 * 特殊路径：bootstrap 模式直接返回 BootstrapTransactionId（epoch 为 0），不推进
 * nextXid；并行模式和恢复（Hot Standby）期间禁止分配，分别会 ERROR。
 *
 * 关键流程与并发注意事项：
 *   1. 使用 XidGenLock 独占锁保护 nextXid 的读取、CLOG/commit_ts/subtrans 的扩展
 *      以及 nextXid 的推进。必须先成功扩展这些状态空间，再推进 nextXid；否则崩溃后
 *      可能分配出没有对应 pg_xact 页的 XID。
 *   2. 接近回卷阈值时，函数会临时释放 XidGenLock，再发送 autovacuum 信号或发出
 *      WARNING/ERROR。这样做主要是避免在 get_database_name() 访问系统表时持锁造成
 *      死锁。释放锁前先把需要的阈值和 oldestXidDB 复制到局部变量；重新加锁后会
 *      重新读取 nextXid，因为期间可能有其他后端完成分配。
 *   3. 发布 XID 必须在释放 XidGenLock 之前完成，并配合 pg_write_barrier()。这保证
 *      任何小于 latestCompletedXid 的活跃 XID 都存在于 ProcArray 中，是 OldestXmin
 *      和快照正确性的基础；读方也应每个 PGPROC 只读取一次 XID，不能假设重复读取
 *      会得到相同值。
 *   4. 子事务缓存满（PGPROC_MAX_CACHED_SUBXIDS）时设置 overflowed 标志，强制读方
 *      转而查询 pg_subtrans 获取子事务到顶层事务的映射。
 *
 * 副作用：修改共享内存中的 nextXid、ProcGlobal->xids / subxidStates；可能扩展
 * CLOG、commit timestamp、SUBTRANS；可能发送 postmaster 信号或产生 WARNING/ERROR。
 */
FullTransactionId
GetNewTransactionId(bool isSubXact)
{
	FullTransactionId full_xid;
	TransactionId xid;

	/*
	 * Workers synchronize transaction state at the beginning of each parallel
	 * operation, so we can't account for new XIDs after that point.
	 */
	if (IsInParallelMode())
		elog(ERROR, "cannot assign TransactionIds during a parallel operation");

	/*
	 * During bootstrap initialization, we return the special bootstrap
	 * transaction id.
	 */
	if (IsBootstrapProcessingMode())
	{
		Assert(!isSubXact);
		MyProc->xid = BootstrapTransactionId;
		ProcGlobal->xids[MyProc->pgxactoff] = BootstrapTransactionId;
		return FullTransactionIdFromEpochAndXid(0, BootstrapTransactionId);
	}

	/* safety check, we should never get this far in a HS standby */
	if (RecoveryInProgress())
		elog(ERROR, "cannot assign TransactionIds during recovery");

	LWLockAcquire(XidGenLock, LW_EXCLUSIVE);

	full_xid = TransamVariables->nextXid;
	xid = XidFromFullTransactionId(full_xid);

	/*----------
	 * Check to see if it's safe to assign another XID.  This protects against
	 * catastrophic data loss due to XID wraparound.  The basic rules are:
	 *
	 * If we're past xidVacLimit, start trying to force autovacuum cycles.
	 * If we're past xidWarnLimit, start issuing warnings.
	 * If we're past xidStopLimit, refuse to execute transactions, unless
	 * we are running in single-user mode (which gives an escape hatch
	 * to the DBA who somehow got past the earlier defenses).
	 *
	 * Note that this coding also appears in GetNewMultiXactId.
	 *----------
	 */
	if (TransactionIdFollowsOrEquals(xid, TransamVariables->xidVacLimit))
	{
		/*
		 * For safety's sake, we release XidGenLock while sending signals,
		 * warnings, etc.  This is not so much because we care about
		 * preserving concurrency in this situation, as to avoid any
		 * possibility of deadlock while doing get_database_name(). First,
		 * copy all the shared values we'll need in this path.
		 */
		TransactionId xidWarnLimit = TransamVariables->xidWarnLimit;
		TransactionId xidStopLimit = TransamVariables->xidStopLimit;
		TransactionId xidWrapLimit = TransamVariables->xidWrapLimit;
		Oid			oldest_datoid = TransamVariables->oldestXidDB;

		LWLockRelease(XidGenLock);

		/*
		 * To avoid swamping the postmaster with signals, we issue the autovac
		 * request only once per 64K transaction starts.  This still gives
		 * plenty of chances before we get into real trouble.
		 */
		if (IsUnderPostmaster && (xid % 65536) == 0)
			SendPostmasterSignal(PMSIGNAL_START_AUTOVAC_LAUNCHER);

		if (IsUnderPostmaster &&
			TransactionIdFollowsOrEquals(xid, xidStopLimit))
		{
			char	   *oldest_datname = get_database_name(oldest_datoid);

			/* complain even if that DB has disappeared */
			if (oldest_datname)
				ereport(ERROR,
						(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
						 errmsg("database is not accepting commands that assign new transaction IDs to avoid wraparound data loss in database \"%s\"",
								oldest_datname),
						 errhint("Execute a database-wide VACUUM in that database.\n"
								 "You might also need to commit or roll back old prepared transactions, or drop stale replication slots.")));
			else
				ereport(ERROR,
						(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
						 errmsg("database is not accepting commands that assign new transaction IDs to avoid wraparound data loss in database with OID %u",
								oldest_datoid),
						 errhint("Execute a database-wide VACUUM in that database.\n"
								 "You might also need to commit or roll back old prepared transactions, or drop stale replication slots.")));
		}
		else if (TransactionIdFollowsOrEquals(xid, xidWarnLimit))
		{
			char	   *oldest_datname = get_database_name(oldest_datoid);

			/* complain even if that DB has disappeared */
			if (oldest_datname)
				ereport(WARNING,
						(errmsg("database \"%s\" must be vacuumed within %u transactions",
								oldest_datname,
								xidWrapLimit - xid),
						 errdetail("Approximately %.2f%% of transaction ID space remains before wraparound.",
								   (double) (xidWrapLimit - xid) / (MaxTransactionId / 2) * 100),
						 errhint("To avoid transaction ID assignment failures, execute a database-wide VACUUM in that database.\n"
								 "You might also need to commit or roll back old prepared transactions, or drop stale replication slots.")));
			else
				ereport(WARNING,
						(errmsg("database with OID %u must be vacuumed within %u transactions",
								oldest_datoid,
								xidWrapLimit - xid),
						 errdetail("Approximately %.2f%% of transaction ID space remains before wraparound.",
								   (double) (xidWrapLimit - xid) / (MaxTransactionId / 2) * 100),
						 errhint("To avoid transaction ID assignment failures, execute a database-wide VACUUM in that database.\n"
								 "You might also need to commit or roll back old prepared transactions, or drop stale replication slots.")));
		}

		/* Re-acquire lock and start over */
		LWLockAcquire(XidGenLock, LW_EXCLUSIVE);
		full_xid = TransamVariables->nextXid;
		xid = XidFromFullTransactionId(full_xid);
	}

	/*
	 * If we are allocating the first XID of a new page of the commit log,
	 * zero out that commit-log page before returning. We must do this while
	 * holding XidGenLock, else another xact could acquire and commit a later
	 * XID before we zero the page.  Fortunately, a page of the commit log
	 * holds 32K or more transactions, so we don't have to do this very often.
	 *
	 * Extend pg_subtrans and pg_commit_ts too.
	 */
	ExtendCLOG(xid);
	ExtendCommitTs(xid);
	ExtendSUBTRANS(xid);

	/*
	 * Now advance the nextXid counter.  This must not happen until after we
	 * have successfully completed ExtendCLOG() --- if that routine fails, we
	 * want the next incoming transaction to try it again.  We cannot assign
	 * more XIDs until there is CLOG space for them.
	 */
	FullTransactionIdAdvance(&TransamVariables->nextXid);

	/*
	 * We must store the new XID into the shared ProcArray before releasing
	 * XidGenLock.  This ensures that every active XID older than
	 * latestCompletedXid is present in the ProcArray, which is essential for
	 * correct OldestXmin tracking; see src/backend/access/transam/README.
	 *
	 * Note that readers of ProcGlobal->xids/PGPROC->xid should be careful to
	 * fetch the value for each proc only once, rather than assume they can
	 * read a value multiple times and get the same answer each time.  Note we
	 * are assuming that TransactionId and int fetch/store are atomic.
	 *
	 * The same comments apply to the subxact xid count and overflow fields.
	 *
	 * Use of a write barrier prevents dangerous code rearrangement in this
	 * function; other backends could otherwise e.g. be examining my subxids
	 * info concurrently, and we don't want them to see an invalid
	 * intermediate state, such as an incremented nxids before the array entry
	 * is filled.
	 *
	 * Other processes that read nxids should do so before reading xids
	 * elements with a pg_read_barrier() in between, so that they can be sure
	 * not to read an uninitialized array element; see
	 * src/backend/storage/lmgr/README.barrier.
	 *
	 * If there's no room to fit a subtransaction XID into PGPROC, set the
	 * cache-overflowed flag instead.  This forces readers to look in
	 * pg_subtrans to map subtransaction XIDs up to top-level XIDs. There is a
	 * race-condition window, in that the new XID will not appear as running
	 * until its parent link has been placed into pg_subtrans. However, that
	 * will happen before anyone could possibly have a reason to inquire about
	 * the status of the XID, so it seems OK.  (Snapshots taken during this
	 * window *will* include the parent XID, so they will deliver the correct
	 * answer later on when someone does have a reason to inquire.)
	 */
	if (!isSubXact)
	{
		Assert(ProcGlobal->subxidStates[MyProc->pgxactoff].count == 0);
		Assert(!ProcGlobal->subxidStates[MyProc->pgxactoff].overflowed);
		Assert(MyProc->subxidStatus.count == 0);
		Assert(!MyProc->subxidStatus.overflowed);

		/* LWLockRelease acts as barrier */
		MyProc->xid = xid;
		ProcGlobal->xids[MyProc->pgxactoff] = xid;
	}
	else
	{
		XidCacheStatus *substat = &ProcGlobal->subxidStates[MyProc->pgxactoff];
		int			nxids = MyProc->subxidStatus.count;

		Assert(substat->count == MyProc->subxidStatus.count);
		Assert(substat->overflowed == MyProc->subxidStatus.overflowed);

		if (nxids < PGPROC_MAX_CACHED_SUBXIDS)
		{
			MyProc->subxids.xids[nxids] = xid;
			pg_write_barrier();
			MyProc->subxidStatus.count = substat->count = nxids + 1;
		}
		else
			MyProc->subxidStatus.overflowed = substat->overflowed = true;
	}

	LWLockRelease(XidGenLock);

	return full_xid;
}

/*
 * Read nextXid but don't allocate it.
 */
/*
 * 中文注释：
 * 在 XidGenLock 共享锁的保护下读取当前 nextXid，即下一个将被分配的
 * FullTransactionId；本函数不分配 XID，也不修改任何共享状态。
 *
 * 调用场景：需要只读地获知“当前最新事务 ID 边界”的代码，例如 walsender、
 * nbtree 页面回收安全性判断、xid8 相关函数以及测试模块等。
 *
 * 返回值：读取瞬间的 nextXid 副本。释放锁后其他后端可能立刻推进 nextXid，因此该值
 * 只是瞬时快照，不能当作稳定的分配结果，也不能据此认为某个 XID 一定尚未被分配。
 */
FullTransactionId
ReadNextFullTransactionId(void)
{
	FullTransactionId fullXid;

	LWLockAcquire(XidGenLock, LW_SHARED);
	fullXid = TransamVariables->nextXid;
	LWLockRelease(XidGenLock);

	return fullXid;
}

/*
 * Advance nextXid to the value after a given xid.  The epoch is inferred.
 * This must only be called during recovery or from two-phase start-up code.
 */
/*
 * 中文注释：
 * 把 nextXid 推进到给定 32 位 xid 之后；如果当前 nextXid 已经足够大，则直接返回。
 *
 * 为什么需要推断 epoch：WAL 记录和两阶段提交状态中只保存 32 位 XID，而 nextXid 是
 * 带 epoch 的 FullTransactionId。本函数保留当前 nextXid 的 epoch，并在推进后的低
 * 32 位小于原低 32 位（即发生 32 位回卷）时把 epoch 加一，从而构造出正确的完整
 * XID。WAL 流中活跃 XID 的跨度不会超过一个 epoch，因此这种推断是安全的。
 *
 * 调用场景：WAL 恢复重放（xlogrecovery.c、事务提交/中止记录、2PC 重放）、热备恢复
 * 中 ProcArray 观察到更大的已分配 XID（ProcArrayApplyRecoveryInfo）等。目的是保证
 * 恢复后的 nextXid 永远大于 WAL 中出现过的任何 XID，避免再次分配已经使用过的 XID。
 *
 * 参数：xid 为需要越过的 32 位 XID。
 * 并发：初次读取 nextXid 时故意不加锁，因为调用者只能是 startup process 或单进程
 * 模式（函数内用 Assert 约束），此时没有其他进程会修改它；写回时仍要持有
 * XidGenLock 独占锁，因为热备后端可能并发读取 nextXid。无返回值。
 */
void
AdvanceNextFullTransactionIdPastXid(TransactionId xid)
{
	FullTransactionId newNextFullXid;
	TransactionId next_xid;
	uint32		epoch;

	/*
	 * It is safe to read nextXid without a lock, because this is only called
	 * from the startup process or single-process mode, meaning that no other
	 * process can modify it.
	 */
	Assert(AmStartupProcess() || !IsUnderPostmaster);

	/* Fast return if this isn't an xid high enough to move the needle. */
	next_xid = XidFromFullTransactionId(TransamVariables->nextXid);
	if (!TransactionIdFollowsOrEquals(xid, next_xid))
		return;

	/*
	 * Compute the FullTransactionId that comes after the given xid.  To do
	 * this, we preserve the existing epoch, but detect when we've wrapped
	 * into a new epoch.  This is necessary because WAL records and 2PC state
	 * currently contain 32 bit xids.  The wrap logic is safe in those cases
	 * because the span of active xids cannot exceed one epoch at any given
	 * point in the WAL stream.
	 */
	TransactionIdAdvance(xid);
	epoch = EpochFromFullTransactionId(TransamVariables->nextXid);
	if (unlikely(xid < next_xid))
		++epoch;
	newNextFullXid = FullTransactionIdFromEpochAndXid(epoch, xid);

	/*
	 * We still need to take a lock to modify the value when there are
	 * concurrent readers.
	 */
	LWLockAcquire(XidGenLock, LW_EXCLUSIVE);
	TransamVariables->nextXid = newNextFullXid;
	LWLockRelease(XidGenLock);
}

/*
 * Advance the cluster-wide value for the oldest valid clog entry.
 *
 * We must acquire XactTruncationLock to advance the oldestClogXid. It's not
 * necessary to hold the lock during the actual clog truncation, only when we
 * advance the limit, as code looking up arbitrary xids is required to hold
 * XactTruncationLock from when it tests oldestClogXid through to when it
 * completes the clog lookup.
 */
/*
 * 中文注释：
 * 推进集群级的 oldestClogXid，即仍然可以安全地在 pg_xact（CLOG）中查询状态的最老
 * XID 下界。只有新值比当前值更“新”时才写入，保证该下界单调向前推进，绝不倒退。
 *
 * 调用场景：CLOG 截断（clog.c 的 TruncateCLOG 及其 WAL 重放）以及检查点/恢复流程
 * （xlog.c）在确认更老的 CLOG 页可以被截断后调用；参数是需要保留的最老 XID，通常
 * 对应 pg_database 中最小的 datfrozenxid 或检查点记录中的 oldestXid。
 *
 * 并发：必须持有 XactTruncationLock 独占锁。查询任意 XID 状态的代码需要从检查
 * oldestClogXid 开始，一直持共享锁到完成 CLOG 查找，因此不能无锁更新该字段。
 * 注意该锁只保护“可安全查询下界”的推进，不需要覆盖实际的截断文件操作。
 */
void
AdvanceOldestClogXid(TransactionId oldest_datfrozenxid)
{
	LWLockAcquire(XactTruncationLock, LW_EXCLUSIVE);
	if (TransactionIdPrecedes(TransamVariables->oldestClogXid,
							  oldest_datfrozenxid))
	{
		TransamVariables->oldestClogXid = oldest_datfrozenxid;
	}
	LWLockRelease(XactTruncationLock);
}

/*
 * Determine the last safe XID to allocate using the currently oldest
 * datfrozenxid (ie, the oldest XID that might exist in any database
 * of our cluster), and the OID of the (or a) database with that value.
 */
/*
 * 中文注释：
 * 根据当前全集群最老的 datfrozenxid 重新计算 XID 回卷保护阈值，并把它们写入共享
 * 内存的 TransamVariables 中。
 *
 * 参数：
 *   oldest_datfrozenxid —— 集群中所有数据库 pg_database.datfrozenxid 的最小值，
 *                          也就是理论上仍可能存在的最老 XID；
 *   oldest_datoid       —— 拥有该最老值的数据库 OID，仅用于生成告警/日志信息。
 *
 * 计算出的四个 32 位阈值：
 *   xidWrapLimit —— oldest_datfrozenxid + (MaxTransactionId >> 1)，即绕行半圈后的
 *                   理论数据丢失点；
 *   xidStopLimit —— xidWrapLimit - 3,000,000，普通后端越过它后拒绝再分配 XID，为
 *                   DBA 留出在单用户模式下修复的空间；
 *   xidWarnLimit —— xidWrapLimit - 100,000,000，越过它后开始发出 WARNING；
 *   xidVacLimit —— oldest_datfrozenxid + autovacuum_freeze_max_age，越过它后立即
 *                   请求 autovacuum 强制清理。
 * 代码还对计算结果低于 FirstNormalTransactionId 的情况做了修正，以补偿特殊 XID
 * 占用事务空间造成的偏移。
 *
 * 调用场景：VACUUM 更新 datfrozenxid 之后、检查点以及 StartupXLOG 恢复启动时。
 * 副作用：在 XidGenLock 独占锁保护下更新 oldestXid、上述四个 limit 和 oldestXidDB；
 * 输出 DEBUG1 日志；若当前 nextXid 已超过 xidVacLimit，且在 postmaster 下且不处于
 * 恢复中，则发送 PMSIGNAL_START_AUTOVAC_LAUNCHER；若已超过 xidWarnLimit，则立即
 * 发出 WARNING（只有处于事务状态时才尝试查询数据库名，避免在启动阶段访问系统表）。
 *
 * 设计思想：按“距离数据丢失还剩多少 XID”分级采取措施——先自动清理、再告警、最后
 * 拒绝服务，层层兜底。autovacuum_freeze_max_age 被定义为 PGC_POSTMASTER 参数，正是
 * 为了避免运行期修改该值导致共享阈值更新出现竞态。
 */
void
SetTransactionIdLimit(TransactionId oldest_datfrozenxid, Oid oldest_datoid)
{
	TransactionId xidVacLimit;
	TransactionId xidWarnLimit;
	TransactionId xidStopLimit;
	TransactionId xidWrapLimit;
	TransactionId curXid;

	Assert(TransactionIdIsNormal(oldest_datfrozenxid));

	/*
	 * The place where we actually get into deep trouble is halfway around
	 * from the oldest potentially-existing XID.  (This calculation is
	 * probably off by one or two counts, because the special XIDs reduce the
	 * size of the loop a little bit.  But we throw in plenty of slop below,
	 * so it doesn't matter.)
	 */
	xidWrapLimit = oldest_datfrozenxid + (MaxTransactionId >> 1);
	if (xidWrapLimit < FirstNormalTransactionId)
		xidWrapLimit += FirstNormalTransactionId;

	/*
	 * We'll refuse to continue assigning XIDs in interactive mode once we get
	 * within 3M transactions of data loss.  This leaves lots of room for the
	 * DBA to fool around fixing things in a standalone backend, while not
	 * being significant compared to total XID space. (VACUUM requires an XID
	 * if it truncates at wal_level!=minimal.  "VACUUM (ANALYZE)", which a DBA
	 * might do by reflex, assigns an XID.  Hence, we had better be sure
	 * there's lots of XIDs left...)  Also, at default BLCKSZ, this leaves two
	 * completely-idle segments.  In the event of edge-case bugs involving
	 * page or segment arithmetic, idle segments render the bugs unreachable
	 * outside of single-user mode.
	 */
	xidStopLimit = xidWrapLimit - 3000000;
	if (xidStopLimit < FirstNormalTransactionId)
		xidStopLimit -= FirstNormalTransactionId;

	/*
	 * We'll start complaining loudly when we get within 100M transactions of
	 * data loss.  This is kind of arbitrary, but if you let your gas gauge
	 * get down to 5% of full, would you be looking for the next gas station?
	 * We need to be fairly liberal about this number because there are lots
	 * of scenarios where most transactions are done by automatic clients that
	 * won't pay attention to warnings.  (No, we're not gonna make this
	 * configurable.  If you know enough to configure it, you know enough to
	 * not get in this kind of trouble in the first place.)
	 */
	xidWarnLimit = xidWrapLimit - 100000000;
	if (xidWarnLimit < FirstNormalTransactionId)
		xidWarnLimit -= FirstNormalTransactionId;

	/*
	 * We'll start trying to force autovacuums when oldest_datfrozenxid gets
	 * to be more than autovacuum_freeze_max_age transactions old.
	 *
	 * Note: guc.c ensures that autovacuum_freeze_max_age is in a sane range,
	 * so that xidVacLimit will be well before xidWarnLimit.
	 *
	 * Note: autovacuum_freeze_max_age is a PGC_POSTMASTER parameter so that
	 * we don't have to worry about dealing with on-the-fly changes in its
	 * value.  It doesn't look practical to update shared state from a GUC
	 * assign hook (too many processes would try to execute the hook,
	 * resulting in race conditions as well as crashes of those not connected
	 * to shared memory).  Perhaps this can be improved someday.  See also
	 * SetMultiXactIdLimit.
	 */
	xidVacLimit = oldest_datfrozenxid + autovacuum_freeze_max_age;
	if (xidVacLimit < FirstNormalTransactionId)
		xidVacLimit += FirstNormalTransactionId;

	/* Grab lock for just long enough to set the new limit values */
	LWLockAcquire(XidGenLock, LW_EXCLUSIVE);
	TransamVariables->oldestXid = oldest_datfrozenxid;
	TransamVariables->xidVacLimit = xidVacLimit;
	TransamVariables->xidWarnLimit = xidWarnLimit;
	TransamVariables->xidStopLimit = xidStopLimit;
	TransamVariables->xidWrapLimit = xidWrapLimit;
	TransamVariables->oldestXidDB = oldest_datoid;
	curXid = XidFromFullTransactionId(TransamVariables->nextXid);
	LWLockRelease(XidGenLock);

	/* Log the info */
	ereport(DEBUG1,
			(errmsg_internal("transaction ID wrap limit is %u, limited by database with OID %u",
							 xidWrapLimit, oldest_datoid)));

	/*
	 * If past the autovacuum force point, immediately signal an autovac
	 * request.  The reason for this is that autovac only processes one
	 * database per invocation.  Once it's finished cleaning up the oldest
	 * database, it'll call here, and we'll signal the postmaster to start
	 * another iteration immediately if there are still any old databases.
	 */
	if (TransactionIdFollowsOrEquals(curXid, xidVacLimit) &&
		IsUnderPostmaster && !InRecovery)
		SendPostmasterSignal(PMSIGNAL_START_AUTOVAC_LAUNCHER);

	/* Give an immediate warning if past the wrap warn point */
	if (TransactionIdFollowsOrEquals(curXid, xidWarnLimit) && !InRecovery)
	{
		char	   *oldest_datname;

		/*
		 * We can be called when not inside a transaction, for example during
		 * StartupXLOG().  In such a case we cannot do database access, so we
		 * must just report the oldest DB's OID.
		 *
		 * Note: it's also possible that get_database_name fails and returns
		 * NULL, for example because the database just got dropped.  We'll
		 * still warn, even though the warning might now be unnecessary.
		 */
		if (IsTransactionState())
			oldest_datname = get_database_name(oldest_datoid);
		else
			oldest_datname = NULL;

		if (oldest_datname)
			ereport(WARNING,
					(errmsg("database \"%s\" must be vacuumed within %u transactions",
							oldest_datname,
							xidWrapLimit - curXid),
					 errdetail("Approximately %.2f%% of transaction ID space remains before wraparound.",
							   (double) (xidWrapLimit - curXid) / (MaxTransactionId / 2) * 100),
					 errhint("To avoid transaction ID assignment failures, execute a database-wide VACUUM in that database.\n"
							 "You might also need to commit or roll back old prepared transactions, or drop stale replication slots.")));
		else
			ereport(WARNING,
					(errmsg("database with OID %u must be vacuumed within %u transactions",
							oldest_datoid,
							xidWrapLimit - curXid),
					 errdetail("Approximately %.2f%% of transaction ID space remains before wraparound.",
							   (double) (xidWrapLimit - curXid) / (MaxTransactionId / 2) * 100),
					 errhint("To avoid transaction ID assignment failures, execute a database-wide VACUUM in that database.\n"
							 "You might also need to commit or roll back old prepared transactions, or drop stale replication slots.")));
	}
}


/*
 * ForceTransactionIdLimitUpdate -- does the XID wrap-limit data need updating?
 *
 * We primarily check whether oldestXidDB is valid.  The cases we have in
 * mind are that that database was dropped, or the field was reset to zero
 * by pg_resetwal.  In either case we should force recalculation of the
 * wrap limit.  Also do it if oldestXid is old enough to be forcing
 * autovacuums or other actions; this ensures we update our state as soon
 * as possible once extra overhead is being incurred.
 */
/*
 * 中文注释：
 * 判断共享内存中的 XID 回卷限制信息是否已经失效、需要重新计算。返回 true 时，
 * 调用方应调用 SetTransactionIdLimit() 刷新阈值。
 *
 * 需要更新的情形：
 *   1. oldestXid 不是普通 XID（异常兜底，正常情况下不应发生）；
 *   2. xidVacLimit 无效（历史遗留或异常状态）；
 *   3. nextXid 已达到或超过 xidVacLimit，说明已经进入强制 autovacuum 区间，不能让
 *      过期阈值继续拖延；
 *   4. oldestXidDB 在 pg_database 中已不存在——数据库被删除，或该字段被
 *      pg_resetwal 清零；此时必须重新确定最老数据库并重算回卷限制。
 *
 * 调用场景：VACUUM 在决定是否需要更新 datfrozenxid 相关信息时调用。
 * 并发：只用 XidGenLock 共享锁复制出一组值，随后释放锁再做 syscache 查询，避免
 * 持锁访问系统表。复制出的值可能很快过时，但本函数只用于决定“是否需要重算”，
 * 多余的 true 只会导致一次无谓刷新，不影响正确性。
 */
bool
ForceTransactionIdLimitUpdate(void)
{
	TransactionId nextXid;
	TransactionId xidVacLimit;
	TransactionId oldestXid;
	Oid			oldestXidDB;

	/* Locking is probably not really necessary, but let's be careful */
	LWLockAcquire(XidGenLock, LW_SHARED);
	nextXid = XidFromFullTransactionId(TransamVariables->nextXid);
	xidVacLimit = TransamVariables->xidVacLimit;
	oldestXid = TransamVariables->oldestXid;
	oldestXidDB = TransamVariables->oldestXidDB;
	LWLockRelease(XidGenLock);

	if (!TransactionIdIsNormal(oldestXid))
		return true;			/* shouldn't happen, but just in case */
	if (!TransactionIdIsValid(xidVacLimit))
		return true;			/* this shouldn't happen anymore either */
	if (TransactionIdFollowsOrEquals(nextXid, xidVacLimit))
		return true;			/* past xidVacLimit, don't delay updating */
	if (!SearchSysCacheExists1(DATABASEOID, ObjectIdGetDatum(oldestXidDB)))
		return true;			/* could happen, per comments above */
	return false;
}


/*
 * GetNewObjectId -- allocate a new OID
 *
 * OIDs are generated by a cluster-wide counter.  Since they are only 32 bits
 * wide, counter wraparound will occur eventually, and therefore it is unwise
 * to assume they are unique unless precautions are taken to make them so.
 * Hence, this routine should generally not be used directly.  The only direct
 * callers should be GetNewOidWithIndex() and GetNewRelFileNumber() in
 * catalog/catalog.c.
 */
/*
 * 中文注释：
 * 从集群级共享的 32 位 OID 计数器中分配一个新的 OID。
 *
 * 调用场景：正常情况下只应由 catalog/catalog.c 中的 GetNewOidWithIndex() 和
 * GetNewRelFileNumber() 直接调用；这两个封装会在 OID 回卷后检查是否与已有对象或
 * 文件名冲突。其他代码若直接调用本函数，必须自行承担 OID 重复的风险。
 * 恢复期间（Hot Standby）禁止分配 OID，否则会 ERROR。
 *
 * 关键逻辑：
 *   1. 使用 OidGenLock 独占锁保护 nextOid 和 oidCount；
 *   2. 回卷保护：在正常 postmaster 环境下，若 nextOid 小于 FirstNormalObjectId，
 *      直接抬升到 FirstNormalObjectId（低于该值的 OID 区间保留给 initdb 生成的
 *      对象，正常运行不应分配）；在 bootstrap/standalone/initdb 环境下，只有低于
 *      FirstGenbkiObjectId 时才抬升，从而允许自动分配
 *      [FirstGenbkiObjectId, FirstNormalObjectId) 区间；
 *   3. WAL 预分配：oidCount 为 0 时，调用 XLogPutNextOid(nextOid +
 *      VAR_OID_PREFETCH)，把“预留上界”写入 WAL，并把 oidCount 重置为
 *      VAR_OID_PREFETCH。这样崩溃恢复后 nextOid 至少恢复到该上界，不会把这一批
 *      已预留的 OID 再发一遍；代价是可能浪费部分未实际使用的 OID。
 *
 * 返回值：本次分配到的 OID。副作用：nextOid 自增、oidCount 自减；必要时插入一条
 * XLOG_NEXTOID 记录。
 */
Oid
GetNewObjectId(void)
{
	Oid			result;

	/* safety check, we should never get this far in a HS standby */
	if (RecoveryInProgress())
		elog(ERROR, "cannot assign OIDs during recovery");

	LWLockAcquire(OidGenLock, LW_EXCLUSIVE);

	/*
	 * Check for wraparound of the OID counter.  We *must* not return 0
	 * (InvalidOid), and in normal operation we mustn't return anything below
	 * FirstNormalObjectId since that range is reserved for initdb (see
	 * IsCatalogRelationOid()).  Note we are relying on unsigned comparison.
	 *
	 * During initdb, we start the OID generator at FirstGenbkiObjectId, so we
	 * only wrap if before that point when in bootstrap or standalone mode.
	 * The first time through this routine after normal postmaster start, the
	 * counter will be forced up to FirstNormalObjectId.  This mechanism
	 * leaves the OIDs between FirstGenbkiObjectId and FirstNormalObjectId
	 * available for automatic assignment during initdb, while ensuring they
	 * will never conflict with user-assigned OIDs.
	 */
	if (TransamVariables->nextOid < ((Oid) FirstNormalObjectId))
	{
		if (IsPostmasterEnvironment)
		{
			/* wraparound, or first post-initdb assignment, in normal mode */
			TransamVariables->nextOid = FirstNormalObjectId;
			TransamVariables->oidCount = 0;
		}
		else
		{
			/* we may be bootstrapping, so don't enforce the full range */
			if (TransamVariables->nextOid < ((Oid) FirstGenbkiObjectId))
			{
				/* wraparound in standalone mode (unlikely but possible) */
				TransamVariables->nextOid = FirstNormalObjectId;
				TransamVariables->oidCount = 0;
			}
		}
	}

	/* If we run out of logged for use oids then we must log more */
	if (TransamVariables->oidCount == 0)
	{
		XLogPutNextOid(TransamVariables->nextOid + VAR_OID_PREFETCH);
		TransamVariables->oidCount = VAR_OID_PREFETCH;
	}

	result = TransamVariables->nextOid;

	(TransamVariables->nextOid)++;
	(TransamVariables->oidCount)--;

	LWLockRelease(OidGenLock);

	return result;
}

/*
 * SetNextObjectId
 *
 * This may only be called during initdb; it advances the OID counter
 * to the specified value.
 */
/*
 * 中文注释：
 * 把 OID 计数器直接推进到指定值，只能在 initdb 期间调用。
 *
 * 调用场景：由 StopGeneratingPinnedObjectIds() 间接调用，用于把 initdb 后续创建的
 * 对象切换到未 pinned 的 OID 区间。
 * 安全检查：若已在 postmaster 环境（正常服务进程）中调用则 ERROR；在 OidGenLock
 * 独占锁下，如果当前 nextOid 已经大于目标值则 ERROR（计数器不允许倒退），否则设置
 * nextOid 并把 oidCount 清零，迫使下一次 GetNewObjectId() 重新写 WAL 预留记录。
 * 并发：initdb 是单进程环境，这里的加锁主要是形式上的保护，但仍保持与其他 OID
 * 访问路径一致的锁顺序。
 */
static void
SetNextObjectId(Oid nextOid)
{
	/* Safety check, this is only allowable during initdb */
	if (IsPostmasterEnvironment)
		elog(ERROR, "cannot advance OID counter anymore");

	/* Taking the lock is, therefore, just pro forma; but do it anyway */
	LWLockAcquire(OidGenLock, LW_EXCLUSIVE);

	if (TransamVariables->nextOid > nextOid)
		elog(ERROR, "too late to advance OID counter to %u, it is now %u",
			 nextOid, TransamVariables->nextOid);

	TransamVariables->nextOid = nextOid;
	TransamVariables->oidCount = 0;

	LWLockRelease(OidGenLock);
}

/*
 * StopGeneratingPinnedObjectIds
 *
 * This is called once during initdb to force the OID counter up to
 * FirstUnpinnedObjectId.  This supports letting initdb's post-bootstrap
 * processing create some pinned objects early on.  Once it's done doing
 * so, it calls this (via pg_stop_making_pinned_objects()) so that the
 * remaining objects it makes will be considered un-pinned.
 */
/*
 * 中文注释：
 * 在 initdb 期间调用一次，把 OID 计数器强制推进到 FirstUnpinnedObjectId。
 *
 * 背景：initdb 的 post-bootstrap 处理会先创建少量需要“pinned”（固定保留、不会被
 * 自动清理）的对象，这些对象使用 FirstGenbkiObjectId 到 FirstUnpinnedObjectId
 * 之间的 OID。创建完毕后通过 SQL 函数 pg_stop_making_pinned_objects() 调用本函数，
 * 此后创建的对象就落在普通（un-pinned）OID 区间。实现直接委托给
 * SetNextObjectId()。
 */
void
StopGeneratingPinnedObjectIds(void)
{
	SetNextObjectId(FirstUnpinnedObjectId);
}


#ifdef USE_ASSERT_CHECKING

/*
 * Assert that xid is between [oldestXid, nextXid], which is the range we
 * expect XIDs coming from tables etc to be in.
 *
 * As TransamVariables->oldestXid could change just after this call without
 * further precautions, and as a wrapped-around xid could again fall within
 * the valid range, this assertion can only detect if something is definitely
 * wrong, but not establish correctness.
 *
 * This intentionally does not expose a return value, to avoid code being
 * introduced that depends on the return value.
 */
/*
 * 中文注释：
 * 仅在 USE_ASSERT_CHECKING 构建中提供的断言辅助函数：检查 xid 落在
 * [oldestXid, nextXid] 这个“可能合法”的范围内，用于发现明显的事务 ID 错误。
 * 参数 xid 为待检查的 32 位 XID；BootstrapTransactionId、FrozenTransactionId 等
 * 特殊 XID 直接放行。
 *
 * 并发注意事项：本函数不能获取 XidGenLock，因为调用者可能已经持有该锁，或持有
 * 不允许再嵌套获取 XidGenLock 的其他锁。这里依赖 32 位读写原子性以及
 * pg_memory_barrier()：无锁读取 oldestXid/nextXid 可能得到略微过时或彼此不完全
 * 一致的值。断言的比较使用“或”而非严格的闭区间“与”，因此比字面意义上的区间
 * 检查更宽松；这可以容忍某一侧边界在读取之后已经推进，但也意味着它只能检测
 * “确定越界”的错误，不能证明正确性，也不能反过来推导 xid 一定在区间内。
 *
 * 另外，允许 xid == nextXid：从 ProcArray 读到的 XID 可能来自其他后端，而本后端
 * 尚未看到更新后的 nextXid。函数刻意不返回任何值，避免调用方依赖检查结果。
 */
void
AssertTransactionIdInAllowableRange(TransactionId xid)
{
	TransactionId oldest_xid;
	TransactionId next_xid;

	Assert(TransactionIdIsValid(xid));

	/* we may see bootstrap / frozen */
	if (!TransactionIdIsNormal(xid))
		return;

	/*
	 * We can't acquire XidGenLock, as this may be called with XidGenLock
	 * already held (or with other locks that don't allow XidGenLock to be
	 * nested). That's ok for our purposes though, since we already rely on
	 * 32bit reads to be atomic. While nextXid is 64 bit, we only look at the
	 * lower 32bit, so a skewed read doesn't hurt.
	 *
	 * There's no increased danger of falling outside [oldest, next] by
	 * accessing them without a lock. xid needs to have been created with
	 * GetNewTransactionId() in the originating session, and the locks there
	 * pair with the memory barrier below.  We do however accept xid to be <=
	 * to next_xid, instead of just <, as xid could be from the procarray,
	 * before we see the updated nextXid value.
	 */
	pg_memory_barrier();
	oldest_xid = TransamVariables->oldestXid;
	next_xid = XidFromFullTransactionId(TransamVariables->nextXid);

	Assert(TransactionIdFollowsOrEquals(xid, oldest_xid) ||
		   TransactionIdPrecedesOrEquals(xid, next_xid));
}
#endif
