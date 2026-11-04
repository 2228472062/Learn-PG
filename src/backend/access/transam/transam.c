/*-------------------------------------------------------------------------
 *
 * transam.c
 *	  postgres transaction (commit) log interface routines
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/access/transam/transam.c
 *
 * NOTES
 *	  This file contains the high level access-method interface to the
 *	  transaction system.
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件是 PostgreSQL 事务状态查询与提交日志（CLOG，物理实现为 pg_xact）的
 * 高层访问接口，向上层屏蔽底层 CLOG 与子事务日志（pg_subtrans）的存储细节。
 * 主要内容包括：
 *   1. TransactionLogFetch 统一读取指定 XID 的当前状态（committed/aborted/
 *      in-progress/sub-committed），并用单条目缓存减少对共享内存的重复访问；
 *   2. TransactionIdDidCommit / TransactionIdDidAbort 供可见性判断等路径查询
 *      事务是否提交或中止；
 *   3. TransactionIdCommitTree / TransactionIdAsyncCommitTree /
 *      TransactionIdAbortTree 把顶层事务及其子事务树的状态写入 CLOG；
 *   4. TransactionIdLatest 求主事务与子事务中的最大 XID；
 *   5. TransactionIdGetCommitLSN 返回足以保证提交记录已落盘的 LSN。
 *
 * 核心数据结构是 cachedFetchXid / cachedFetchXidStatus / cachedCommitLSN 组成的
 * 单条目缓存，以及 clog.h 中定义的 XidStatus 状态码
 * （TRANSACTION_STATUS_IN_PROGRESS/COMMITTED/ABORTED/SUB_COMMITTED）。
 *
 * 与其他模块的关系：
 *   - xact.c 在提交、中止路径以及 twophase.c 在两阶段提交路径调用本文件的
 *     Tree 系列函数记录最终状态；
 *   - clog.c 提供 TransactionIdGetStatus / TransactionIdSetTreeStatus 等底层
 *     CLOG 读写例程，本文件是它们的主要上层调用者；
 *   - subtrans.c 提供 SubTransGetParent，用于递归解析 sub-committed 子事务的
 *     父事务，从而得到整个事务树的最终结果；
 *   - procarray.c 的 TransactionIdIsInProgress 判断事务是否仍在运行，与本文件的
 *     “已结束事务状态查询”互补，二者结合才能完整判断元组可见性；
 *   - heapam_visibility.c 依据本文件的结果与 commit LSN 判断元组可见性并设置
 *     hint bits；commit timestamp 模块（commit_ts.c）记录的提交时间戳同样以
 *     事务提交状态和提交 WAL 记录为基础。
 *
 * 关键设计思想：
 *   - 已结束事务的状态一旦写入 CLOG 就不会再改变，因此可以安全缓存；in-progress
 *     和 sub-committed 是暂态，绝不能缓存，否则会返回过期结果；
 *   - 子事务状态延迟解析：子事务在 CLOG 中可能只有 sub-committed 标记，需要沿
 *     pg_subtrans 递归找到顶层事务才能得出最终结论；
 *   - 提交树的写入尽量原子：若子事务跨 CLOG 页，先把非首页子事务标为
 *     sub-committed，再提交主事务所在页，最后补全其余页，保证并发观察者不会看到
 *     “子事务已提交但父事务未提交”的中间状态；
 *   - 查询接口本身无副作用（缓存除外），调用者无需为读取 CLOG 额外加锁。
 */

#include "postgres.h"

#include "access/clog.h"
#include "access/subtrans.h"
#include "access/transam.h"
#include "utils/snapmgr.h"

/*
 * Single-item cache for results of TransactionLogFetch.  It's worth having
 * such a cache because we frequently find ourselves repeatedly checking the
 * same XID, for example when scanning a table just after a bulk insert,
 * update, or delete.
 */
/*
 * 中文注释：
 * 这三个变量构成 TransactionLogFetch 的单条目缓存：
 *   cachedFetchXid       —— 最近一次查询的 XID，InvalidTransactionId 表示缓存为空；
 *   cachedFetchXidStatus —— 该 XID 的 CLOG 状态；
 *   cachedCommitLSN      —— 与该状态一同读出的提交记录 LSN，供
 *                           TransactionIdGetCommitLSN 直接复用。
 * 只有 committed/aborted 这类不会再变化的状态才会写入缓存；in-progress 与
 * sub-committed 属于暂态，不能缓存，否则后续查询可能得到过期结果。
 * 这些变量是进程内私有（static）的，不需要加锁，也不跨进程共享。
 */
static TransactionId cachedFetchXid = InvalidTransactionId;
static XidStatus cachedFetchXidStatus;
static XLogRecPtr cachedCommitLSN;

/* Local functions */
static XidStatus TransactionLogFetch(TransactionId transactionId);


/* ----------------------------------------------------------------
 *		Postgres log access method interface
 *
 *		TransactionLogFetch
 * ----------------------------------------------------------------
 */

/*
 * TransactionLogFetch --- fetch commit status of specified transaction id
 */
/*
 * 中文注释：
 * 读取指定 XID 在 CLOG 中的状态，并维护单条目缓存。
 *
 * 调用场景：TransactionIdDidCommit / TransactionIdDidAbort 以及
 * TransactionIdGetCommitLSN 的内部实现都经过这里，是查询事务状态的统一入口。
 *
 * 参数：transactionId 为待查询的 XID，可以是普通事务 ID，也可以是
 * BootstrapTransactionId、FrozenTransactionId 等特殊 XID。
 *
 * 返回值：XidStatus，取值见 clog.h：
 *   TRANSACTION_STATUS_COMMITTED / ABORTED / IN_PROGRESS / SUB_COMMITTED。
 *
 * 副作用：命中缓存时不访问共享内存；未命中且状态已终结时更新三个缓存变量
 * （cachedFetchXid/cachedFetchXidStatus/cachedCommitLSN）。
 *
 * 并发注意：CLOG 中已终结状态不会改变，因此缓存安全；IN_PROGRESS 和
 * SUB_COMMITTED 可能随后变化，故不缓存。特殊 XID 中 Bootstrap/Frozen 直接视为
 * 已提交，其他非普通 XID（如 InvalidTransactionId）视为已中止。
 */
static XidStatus
TransactionLogFetch(TransactionId transactionId)
{
	XidStatus	xidstatus;
	XLogRecPtr	xidlsn;

	/*
	 * Before going to the commit log manager, check our single item cache to
	 * see if we didn't just check the transaction status a moment ago.
	 */
	if (TransactionIdEquals(transactionId, cachedFetchXid))
		return cachedFetchXidStatus;

	/*
	 * Also, check to see if the transaction ID is a permanent one.
	 */
	if (!TransactionIdIsNormal(transactionId))
	{
		if (TransactionIdEquals(transactionId, BootstrapTransactionId))
			return TRANSACTION_STATUS_COMMITTED;
		if (TransactionIdEquals(transactionId, FrozenTransactionId))
			return TRANSACTION_STATUS_COMMITTED;
		return TRANSACTION_STATUS_ABORTED;
	}

	/*
	 * Get the transaction status.
	 */
	xidstatus = TransactionIdGetStatus(transactionId, &xidlsn);

	/*
	 * Cache it, but DO NOT cache status for unfinished or sub-committed
	 * transactions!  We only cache status that is guaranteed not to change.
	 */
	if (xidstatus != TRANSACTION_STATUS_IN_PROGRESS &&
		xidstatus != TRANSACTION_STATUS_SUB_COMMITTED)
	{
		cachedFetchXid = transactionId;
		cachedFetchXidStatus = xidstatus;
		cachedCommitLSN = xidlsn;
	}

	return xidstatus;
}

/* ----------------------------------------------------------------
 *						Interface functions
 *
 *		TransactionIdDidCommit
 *		TransactionIdDidAbort
 *		========
 *		   these functions test the transaction status of
 *		   a specified transaction id.
 *
 *		TransactionIdCommitTree
 *		TransactionIdAsyncCommitTree
 *		TransactionIdAbortTree
 *		========
 *		   these functions set the transaction status of the specified
 *		   transaction tree.
 *
 * See also TransactionIdIsInProgress, which once was in this module
 * but now lives in procarray.c, as well as comments at the top of
 * heapam_visibility.c that explain how everything fits together.
 * ----------------------------------------------------------------
 */

/*
 * TransactionIdDidCommit
 *		True iff transaction associated with the identifier did commit.
 *
 * Note:
 *		Assumes transaction identifier is valid and exists in clog.
 */
/*
 * 中文注释：
 * 判断给定 XID 对应的事务是否已经提交。
 *
 * 调用场景：堆元组可见性判断（heapam_visibility.c）、hint bits 设置、逻辑解码
 * 以及异步通知等需要确认“事务确实提交”的路径。
 *
 * 参数：transactionId 必须是有效 XID；普通 XID 通常已存在于 CLOG 中，特殊 XID
 * 则由 TransactionLogFetch 直接判定。函数本身不做有效性检查。
 * 返回值：已提交返回 true；已中止、仍在进行或无法判定时返回 false。
 *
 * 处理逻辑与副作用：
 *   - 状态直接为 committed 时返回 true；
 *   - 状态为 sub-committed 时说明该 XID 是子事务，需要经 SubTransGetParent 递归
 *     检查父事务。若 XID 早于 TransactionXmin，pg_subtrans 中可能已无记录（父事务
 *     在崩溃后未及清理），此时保守地返回 false；若查不到父 XID，则发出 WARNING
 *     并返回 false；
 *   - 其他状态（in-progress/aborted）返回 false。本函数只读取 CLOG/subtrans，
 *     自身不产生持久化副作用。
 *
 * 并发注意：读取 CLOG 由底层 SLRU 加共享锁保护；已终结状态不会再改变，因此结果
 * 稳定。设计思想是只有“提交”才是可见性判断的肯定答案，其余情况一律按未提交
 * 处理，避免把不确定状态误判为可见。
 */
bool							/* true if given transaction committed */
TransactionIdDidCommit(TransactionId transactionId)
{
	XidStatus	xidstatus;

	xidstatus = TransactionLogFetch(transactionId);

	/*
	 * If it's marked committed, it's committed.
	 */
	if (xidstatus == TRANSACTION_STATUS_COMMITTED)
		return true;

	/*
	 * If it's marked subcommitted, we have to check the parent recursively.
	 * However, if it's older than TransactionXmin, we can't look at
	 * pg_subtrans; instead assume that the parent crashed without cleaning up
	 * its children.
	 *
	 * Originally we Assert'ed that the result of SubTransGetParent was not
	 * zero. However with the introduction of prepared transactions, there can
	 * be a window just after database startup where we do not have complete
	 * knowledge in pg_subtrans of the transactions after TransactionXmin.
	 * StartupSUBTRANS() has ensured that any missing information will be
	 * zeroed.  Since this case should not happen under normal conditions, it
	 * seems reasonable to emit a WARNING for it.
	 */
	if (xidstatus == TRANSACTION_STATUS_SUB_COMMITTED)
	{
		TransactionId parentXid;

		if (TransactionIdPrecedes(transactionId, TransactionXmin))
			return false;
		parentXid = SubTransGetParent(transactionId);
		if (!TransactionIdIsValid(parentXid))
		{
			elog(WARNING, "no pg_subtrans entry for subcommitted XID %u",
				 transactionId);
			return false;
		}
		return TransactionIdDidCommit(parentXid);
	}

	/*
	 * It's not committed.
	 */
	return false;
}

/*
 * TransactionIdDidAbort
 *		True iff transaction associated with the identifier did abort.
 *
 * Note:
 *		Assumes transaction identifier is valid and exists in clog.
 *
 *		Returns true only for explicitly aborted transactions, as transactions
 *		implicitly aborted due to a crash will commonly still appear to be
 *		in-progress in the clog.  Most of the time TransactionIdDidCommit(),
 *		with a preceding TransactionIdIsInProgress() check, should be used
 *		instead of TransactionIdDidAbort().
 */
/*
 * 中文注释：
 * 判断给定 XID 对应的事务是否被显式中止。
 *
 * 调用场景：堆元组可见性判断与更新链遍历（heapam.c）、判断 XID 是否仍在进行的
 * 辅助检查（procarray.c）、两阶段提交与恢复（twophase.c/standby.c）等需要区分
 * “已中止”与“仍在进行”的路径。一般的元组可见性判断更常用
 * TransactionIdDidCommit，并在此之前配合 TransactionIdIsInProgress 使用。
 *
 * 参数/返回值：transactionId 为有效 XID，普通 XID 通常已存在于 CLOG；显式中止
 * 返回 true，否则返回 false。返回 false 只表示“没有显式中止”，不能理解为“事务
 * 已提交”——崩溃导致隐式中止的事务在 CLOG 中通常仍显示为 in-progress。
 *
 * 处理逻辑：与 TransactionIdDidCommit 对称，状态为 sub-committed 时递归检查父
 * 事务；若 XID 早于 TransactionXmin，则假定父事务已崩溃且未清理，返回 true；
 * 若查不到父 XID，则发出 WARNING 并返回 true（原因见 TransactionIdDidCommit
 * 中的说明）。本函数只读取 CLOG/subtrans，不产生持久化副作用。
 */
bool							/* true if given transaction aborted */
TransactionIdDidAbort(TransactionId transactionId)
{
	XidStatus	xidstatus;

	xidstatus = TransactionLogFetch(transactionId);

	/*
	 * If it's marked aborted, it's aborted.
	 */
	if (xidstatus == TRANSACTION_STATUS_ABORTED)
		return true;

	/*
	 * If it's marked subcommitted, we have to check the parent recursively.
	 * However, if it's older than TransactionXmin, we can't look at
	 * pg_subtrans; instead assume that the parent crashed without cleaning up
	 * its children.
	 */
	if (xidstatus == TRANSACTION_STATUS_SUB_COMMITTED)
	{
		TransactionId parentXid;

		if (TransactionIdPrecedes(transactionId, TransactionXmin))
			return true;
		parentXid = SubTransGetParent(transactionId);
		if (!TransactionIdIsValid(parentXid))
		{
			/* see notes in TransactionIdDidCommit */
			elog(WARNING, "no pg_subtrans entry for subcommitted XID %u",
				 transactionId);
			return true;
		}
		return TransactionIdDidAbort(parentXid);
	}

	/*
	 * It's not aborted.
	 */
	return false;
}

/*
 * TransactionIdCommitTree
 *		Marks the given transaction and children as committed
 *
 * "xid" is a toplevel transaction commit, and the xids array contains its
 * committed subtransactions.
 *
 * This commit operation is not guaranteed to be atomic, but if not, subxids
 * are correctly marked subcommit first.
 */
/*
 * 中文注释：
 * 把顶层事务 xid 及其子事务数组 xids 一并标记为已提交。
 *
 * 参数：
 *   xid   —— 顶层事务 ID；
 *   nxids —— 子事务个数；
 *   xids  —— 子事务 XID 数组（可以为 0 个）。
 * 返回值：无。
 *
 * 副作用：调用 clog.c 的 TransactionIdSetTreeStatus 写入 CLOG。若子事务跨 CLOG
 * 页，先把非首页子事务标为 sub-committed，再提交主事务所在页，最后补全其余页；
 * 因此整个过程对外不是严格原子的，但并发观察者能够通过 sub-committed 标记递归
 * 找到正确的顶层提交结果。
 *
 * lsn 传入 InvalidXLogRecPtr：同步提交由调用者保证提交记录已经刷盘，无需在此
 * 记录 LSN。
 */
void
TransactionIdCommitTree(TransactionId xid, int nxids, TransactionId *xids)
{
	TransactionIdSetTreeStatus(xid, nxids, xids,
							   TRANSACTION_STATUS_COMMITTED,
							   InvalidXLogRecPtr);
}

/*
 * TransactionIdAsyncCommitTree
 *		Same as above, but for async commits.  The commit record LSN is needed.
 */
/*
 * 中文注释：
 * 与 TransactionIdCommitTree 相同，但用于异步提交（例如
 * synchronous_commit = off 的场景）。
 *
 * 多出的参数 lsn 是提交 WAL 记录的 LSN，会被记录到 CLOG 的 group LSN 中，供
 * TransactionIdGetCommitLSN 返回；这样后续设置 hint bits 前可以判断提交记录是否
 * 已经落盘。其余参数含义、副作用以及提交树的非原子性说明同
 * TransactionIdCommitTree。
 */
void
TransactionIdAsyncCommitTree(TransactionId xid, int nxids, TransactionId *xids,
							 XLogRecPtr lsn)
{
	TransactionIdSetTreeStatus(xid, nxids, xids,
							   TRANSACTION_STATUS_COMMITTED, lsn);
}

/*
 * TransactionIdAbortTree
 *		Marks the given transaction and children as aborted.
 *
 * "xid" is a toplevel transaction commit, and the xids array contains its
 * committed subtransactions.
 *
 * We don't need to worry about the non-atomic behavior, since any onlookers
 * will consider all the xacts as not-yet-committed anyway.
 */
/*
 * 中文注释：
 * 把顶层事务 xid 及其子事务数组 xids 一并标记为已中止。
 *
 * 参数含义同 TransactionIdCommitTree；lsn 固定为 InvalidXLogRecPtr，因为中止
 * 不需要等待提交记录落盘。
 *
 * 设计思想：中止时无需像提交那样使用 sub-committed 中间状态。并发观察者本来
 * 就会把未提交事务视为不可见，即使看到部分子事务已中止、部分仍在进行，也不会
 * 得出错误结论，因此可以容忍非原子写入。
 */
void
TransactionIdAbortTree(TransactionId xid, int nxids, TransactionId *xids)
{
	TransactionIdSetTreeStatus(xid, nxids, xids,
							   TRANSACTION_STATUS_ABORTED, InvalidXLogRecPtr);
}


/*
 * TransactionIdLatest --- get latest XID among a main xact and its children
 */
/*
 * 中文注释：
 * 返回主事务 XID 与其子事务 XID 中的最大值（按 XID 全序比较）。
 *
 * 调用场景：两阶段提交（twophase.c）等需要为事务树生成一个“最新 XID”，作为
 * 清理或比较依据的路径。
 *
 * 参数：mainxid 为主事务 XID；nxids/xids 为子事务个数与数组。
 * 返回值：所有给定 XID 中的最大者；没有子事务时返回 mainxid。
 *
 * 实现上从数组尾部向前扫描以减少无谓赋值。虽然实践中 xids 通常有序，但这里不
 * 依赖该假设，因此对乱序输入同样正确。纯函数，无副作用。
 */
TransactionId
TransactionIdLatest(TransactionId mainxid,
					int nxids, const TransactionId *xids)
{
	TransactionId result;

	/*
	 * In practice it is highly likely that the xids[] array is sorted, and so
	 * we could save some cycles by just taking the last child XID, but this
	 * probably isn't so performance-critical that it's worth depending on
	 * that assumption.  But just to show we're not totally stupid, scan the
	 * array back-to-front to avoid useless assignments.
	 */
	result = mainxid;
	while (--nxids >= 0)
	{
		if (TransactionIdPrecedes(result, xids[nxids]))
			result = xids[nxids];
	}
	return result;
}


/*
 * TransactionIdGetCommitLSN
 *
 * This function returns an LSN that is late enough to be able
 * to guarantee that if we flush up to the LSN returned then we
 * will have flushed the transaction's commit record to disk.
 *
 * The result is not necessarily the exact LSN of the transaction's
 * commit record!  For example, for long-past transactions (those whose
 * clog pages already migrated to disk), we'll return InvalidXLogRecPtr.
 * Also, because we group transactions on the same clog page to conserve
 * storage, we might return the LSN of a later transaction that falls into
 * the same group.
 */
/*
 * 中文注释：
 * 返回一个“足够新”的 LSN：只要把 WAL 刷到该位置，就能保证该 XID 的提交记录
 * 已经落盘。
 *
 * 调用场景：heapam_visibility.c 在设置 hint bits 前调用，确认提交记录已持久化，
 * 避免崩溃后 hint bits 指向一个实际丢失的提交。
 *
 * 参数：xid 为已确认提交的事务 ID。
 * 返回值：提交记录或其所在 CLOG group 中较晚事务的 LSN；对于很久以前、CLOG 页
 * 已迁移到磁盘的事务返回 InvalidXLogRecPtr（表示无需再等待刷盘）。
 *
 * 实现细节：优先复用 TransactionLogFetch 的单条目缓存；特殊 XID 直接返回
 * InvalidXLogRecPtr；否则通过 TransactionIdGetStatus 读取状态及 group LSN。
 * 返回值不保证是提交记录的精确 LSN，只保证“刷到它即可”。函数只读，无副作用。
 */
XLogRecPtr
TransactionIdGetCommitLSN(TransactionId xid)
{
	XLogRecPtr	result;

	/*
	 * Currently, all uses of this function are for xids that were just
	 * reported to be committed by TransactionLogFetch, so we expect that
	 * checking TransactionLogFetch's cache will usually succeed and avoid an
	 * extra trip to shared memory.
	 */
	if (TransactionIdEquals(xid, cachedFetchXid))
		return cachedCommitLSN;

	/* Special XIDs are always known committed */
	if (!TransactionIdIsNormal(xid))
		return InvalidXLogRecPtr;

	/*
	 * Get the transaction status.
	 */
	(void) TransactionIdGetStatus(xid, &result);

	return result;
}
