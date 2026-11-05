/*-------------------------------------------------------------------------
 *
 * multixact.c
 *		PostgreSQL multi-transaction-log manager
 *
 * The pg_multixact manager is a pg_xact-like manager that stores an array of
 * MultiXactMember for each MultiXactId.  It is a fundamental part of the
 * shared-row-lock implementation.  Each MultiXactMember is comprised of a
 * TransactionId and a set of flag bits.  The name is a bit historical:
 * originally, a MultiXactId consisted of more than one TransactionId (except
 * in rare corner cases), hence "multi".  Nowadays, however, it's perfectly
 * legitimate to have MultiXactIds that only include a single Xid.
 *
 * The meaning of the flag bits is opaque to this module, but they are mostly
 * used in heapam.c to identify lock modes that each of the member transactions
 * is holding on any given tuple.  This module just contains support to store
 * and retrieve the arrays.
 *
 * We use two SLRU areas, one for storing the offsets at which the data
 * starts for each MultiXactId in the other one.  This trick allows us to
 * store variable length arrays of TransactionIds.  (We could alternatively
 * use one area containing counts and TransactionIds, with valid MultiXactId
 * values pointing at slots containing counts; but that way seems less robust
 * since it would get completely confused if someone inquired about a bogus
 * MultiXactId that pointed to an intermediate slot containing an XID.)
 *
 * XLOG interactions: this module generates a record whenever a new OFFSETs or
 * MEMBERs page is initialized to zeroes, as well as an
 * XLOG_MULTIXACT_CREATE_ID record whenever a new MultiXactId is defined.
 * This module ignores the WAL rule "write xlog before data," because it
 * suffices that actions recording a MultiXactId in a heap xmax do follow that
 * rule.  The only way for the MXID to be referenced from any data page is for
 * heap_lock_tuple() or heap_update() to have put it there, and each generates
 * an XLOG record that must follow ours.  The normal LSN interlock between the
 * data page and that XLOG record will ensure that our XLOG record reaches
 * disk first.  If the SLRU members/offsets data reaches disk sooner than the
 * XLOG records, we do not care; after recovery, no xmax will refer to it.  On
 * the flip side, to ensure that all referenced entries _do_ reach disk, this
 * module's XLOG records completely rebuild the data entered since the last
 * checkpoint.  We flush and sync all dirty OFFSETs and MEMBERs pages to disk
 * before each checkpoint is considered complete.
 *
 * Like clog.c, and unlike subtrans.c, we have to preserve state across
 * crashes and ensure that MXID and offset numbering increases monotonically
 * across a crash.  We do this in the same way as it's done for transaction
 * IDs: the WAL record is guaranteed to contain evidence of every MXID we
 * could need to worry about, and we just make sure that at the end of
 * replay, the next-MXID and next-offset counters are at least as large as
 * anything we saw during replay.
 *
 * We are able to remove segments no longer necessary by carefully tracking
 * each table's used values: during vacuum, any multixact older than a certain
 * value is removed; the cutoff value is stored in pg_class.  The minimum value
 * across all tables in each database is stored in pg_database, and the global
 * minimum across all databases is part of pg_control and is kept in shared
 * memory.  Whenever that minimum is advanced, the SLRUs are truncated.
 *
 * When new multixactid values are to be created, care is taken that the
 * counter does not fall within the wraparound horizon considering the global
 * minimum value.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/multixact.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/multixact.h"
#include "access/multixact_internal.h"
#include "access/slru.h"
#include "access/twophase.h"
#include "access/twophase_rmgr.h"
#include "access/xlog.h"
#include "access/xloginsert.h"
#include "access/xlogutils.h"
#include "miscadmin.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "postmaster/autovacuum.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "storage/subsystems.h"
#include "utils/guc_hooks.h"
#include "utils/injection_point.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"


/*
 * Thresholds used to keep members disk usage in check when multixids have a
 * lot of members.  When MULTIXACT_MEMBER_LOW_THRESHOLD is reached, vacuum
 * starts freezing multixids more aggressively, even if the normal multixid
 * age limits haven't been reached yet.
 */
#define MULTIXACT_MEMBER_LOW_THRESHOLD		UINT64CONST(2000000000)
#define MULTIXACT_MEMBER_HIGH_THRESHOLD		UINT64CONST(4000000000)

/*
 * 中文注释：
 * 返回 MultiXactId 逻辑上的下一个值。MultiXactId 是无符号 32 位计数器，
 * 到达 MaxMultiXactId 后回绕到 FirstMultiXactId；比较大小必须使用
 * MultiXactIdPrecedes 系列函数，不能直接用整数比较。该函数只做算术，不加锁。
 */
static inline MultiXactId
NextMultiXactId(MultiXactId multi)
{
	return multi == MaxMultiXactId ? FirstMultiXactId : multi + 1;
}

/*
 * 中文注释：
 * 返回 MultiXactId 逻辑上的前一个值。FirstMultiXactId 的前驱回绕为
 * MaxMultiXactId，与 NextMultiXactId 对称。用于截断时回退一页等边界计算。
 */
static inline MultiXactId
PreviousMultiXactId(MultiXactId multi)
{
	return multi == FirstMultiXactId ? MaxMultiXactId : multi - 1;
}

/*
 * Links to shared-memory data structures for MultiXact control
 */
static bool MultiXactOffsetPagePrecedes(int64 page1, int64 page2);
static int	MultiXactOffsetIoErrorDetail(const void *opaque_data);
static bool MultiXactMemberPagePrecedes(int64 page1, int64 page2);
static int	MultiXactMemberIoErrorDetail(const void *opaque_data);

static SlruDesc MultiXactOffsetSlruDesc;
static SlruDesc MultiXactMemberSlruDesc;

#define MultiXactOffsetCtl	(&MultiXactOffsetSlruDesc)
#define MultiXactMemberCtl	(&MultiXactMemberSlruDesc)

/*
 * MultiXact state shared across all backends.  All this state is protected
 * by MultiXactGenLock.  (We also use SLRU bank's lock of MultiXactOffset and
 * MultiXactMember to guard accesses to the two sets of SLRU buffers.  For
 * concurrency's sake, we avoid holding more than one of these locks at a
 * time.)
 */
typedef struct MultiXactStateData
{
	/* next-to-be-assigned MultiXactId */
	MultiXactId nextMXact;

	/* next-to-be-assigned offset */
	MultiXactOffset nextOffset;

	/* Have we completed multixact startup? */
	bool		finishedStartup;

	/*
	 * Oldest multixact that is still potentially referenced by a relation.
	 * Anything older than this should not be consulted.  These values are
	 * updated by vacuum.
	 */
	MultiXactId oldestMultiXactId;
	Oid			oldestMultiXactDB;

	/*
	 * Oldest multixact offset that is potentially referenced by a multixact
	 * referenced by a relation.
	 */
	MultiXactOffset oldestOffset;

	/* support for anti-wraparound measures */
	MultiXactId multiVacLimit;
	MultiXactId multiWarnLimit;
	MultiXactId multiStopLimit;
	MultiXactId multiWrapLimit;

	/*
	 * Per-backend data starts here.  We have two arrays stored in the area
	 * immediately following the MultiXactStateData struct:
	 *
	 * OldestMemberMXactId[k] is the oldest MultiXactId each backend's current
	 * transaction(s) could possibly be a member of, or InvalidMultiXactId
	 * when the backend has no live transaction that could possibly be a
	 * member of a MultiXact.  Each backend sets its entry to the current
	 * nextMXact counter just before first acquiring a shared lock in a given
	 * transaction, and clears it at transaction end. (This works because only
	 * during or after acquiring a shared lock could an XID possibly become a
	 * member of a MultiXact, and that MultiXact would have to be created
	 * during or after the lock acquisition.)
	 *
	 * In the OldestMemberMXactId array, there's a slot for all normal
	 * backends (0..MaxBackends-1) followed by a slot for max_prepared_xacts
	 * prepared transactions.
	 *
	 * OldestVisibleMXactId[k] is the oldest MultiXactId each backend's
	 * current transaction(s) think is potentially live, or InvalidMultiXactId
	 * when not in a transaction or not in a transaction that's paid any
	 * attention to MultiXacts yet.  This is computed when first needed in a
	 * given transaction, and cleared at transaction end.  We can compute it
	 * as the minimum of the valid OldestMemberMXactId[] entries at the time
	 * we compute it (using nextMXact if none are valid).  Each backend is
	 * required not to attempt to access any SLRU data for MultiXactIds older
	 * than its own OldestVisibleMXactId[] setting; this is necessary because
	 * the relevant SLRU data can be concurrently truncated away.
	 *
	 * In the OldestVisibleMXactId array, there's a slot for all normal
	 * backends (0..MaxBackends-1) only. No slots for prepared transactions.
	 *
	 * The oldest valid value among all of the OldestMemberMXactId[] and
	 * OldestVisibleMXactId[] entries is considered by vacuum as the earliest
	 * possible value still having any live member transaction -- OldestMxact.
	 * Any value older than that is typically removed from tuple headers, or
	 * "frozen" via being replaced with a new xmax.  VACUUM can sometimes even
	 * remove an individual MultiXact xmax whose value is >= its OldestMxact
	 * cutoff, though typically only when no individual member XID is still
	 * running.  See FreezeMultiXactId for full details.
	 *
	 * Whenever VACUUM advances relminmxid, then either its OldestMxact cutoff
	 * or the oldest extant Multi remaining in the table is used as the new
	 * pg_class.relminmxid value (whichever is earlier).  The minimum of all
	 * relminmxid values in each database is stored in pg_database.datminmxid.
	 * In turn, the minimum of all of those values is stored in pg_control.
	 * This is used as the truncation point for pg_multixact when unneeded
	 * segments get removed by vac_truncate_clog() during vacuuming.
	 */
	MultiXactId perBackendXactIds[FLEXIBLE_ARRAY_MEMBER];
} MultiXactStateData;

/*
 * Sizes of OldestMemberMXactId and OldestVisibleMXactId arrays.
 */
#define NumMemberSlots		(MaxBackends + max_prepared_xacts)
#define NumVisibleSlots		MaxBackends

/* Pointers to the state data in shared memory */
static MultiXactStateData *MultiXactState;
static MultiXactId *OldestMemberMXactId;
static MultiXactId *OldestVisibleMXactId;

static void MultiXactShmemRequest(void *arg);
static void MultiXactShmemInit(void *arg);
static void MultiXactShmemAttach(void *arg);

const ShmemCallbacks MultiXactShmemCallbacks = {
	.request_fn = MultiXactShmemRequest,
	.init_fn = MultiXactShmemInit,
	.attach_fn = MultiXactShmemAttach,
};

/*
 * 中文注释：
 * 返回当前普通后端在共享 OldestMemberMXactId 数组中的槽位指针。
 *
 * 前 MaxBackends 个槽位按 MyProcNumber 分配给普通后端；预备事务的槽位排在其后。
 * 该值表示“当前事务可能成为其成员的最老 MultiXactId”，在事务第一次可能获取
 * 共享行锁之前设置，事务结束时清除；它防止相关 MultiXact 在事务仍可能引用时被
 * vacuum 截断。
 */
static inline MultiXactId *
MyOldestMemberMXactIdSlot(void)
{
	/*
	 * The first MaxBackends entries in the OldestMemberMXactId array are
	 * reserved for regular backends.  MyProcNumber should index into one of
	 * them.
	 */
	Assert(MyProcNumber >= 0 && MyProcNumber < MaxBackends);
	return &OldestMemberMXactId[MyProcNumber];
}

/*
 * 中文注释：
 * 返回某个预备事务在 OldestMemberMXactId 数组中的槽位指针。
 *
 * 预备事务没有普通 PGPROC，而是使用 FIRST_PREPARED_XACT_PROC_NUMBER 之后的虚拟
 * ProcNumber。槽位位于普通后端的 MaxBackends 个槽位之后，索引由 dummy ProcNumber
 * 减去 FIRST_PREPARED_XACT_PROC_NUMBER 得到。这样预备事务也能阻止其可能引用的
 * MultiXact 被截断。
 */
static inline MultiXactId *
PreparedXactOldestMemberMXactIdSlot(ProcNumber procno)
{
	int			prepared_xact_idx;

	Assert(procno >= FIRST_PREPARED_XACT_PROC_NUMBER);
	prepared_xact_idx = procno - FIRST_PREPARED_XACT_PROC_NUMBER;

	/*
	 * The first MaxBackends entries in the OldestMemberMXactId array are
	 * reserved for regular backends.  Prepared xacts come after them.
	 */
	Assert(MaxBackends + prepared_xact_idx < NumMemberSlots);
	return &OldestMemberMXactId[MaxBackends + prepared_xact_idx];
}

/*
 * 中文注释：
 * 返回当前后端在 OldestVisibleMXactId 数组中的槽位指针。
 *
 * 该值表示“当前事务认为可能仍然存活的最老 MultiXactId”，在第一次检查
 * MultiXact 时计算，事务结束时清除。它保证本后端不会去访问已经被截断的 SLRU
 * 数据。与 OldestMember 不同，预备事务没有 visible 槽位，因为预备后不再检查
 * MultiXact。
 */
static inline MultiXactId *
MyOldestVisibleMXactIdSlot(void)
{
	Assert(MyProcNumber >= 0 && MyProcNumber < NumVisibleSlots);
	return &OldestVisibleMXactId[MyProcNumber];
}

/*
 * Definitions for the backend-local MultiXactId cache.
 *
 * We use this cache to store known MultiXacts, so we don't need to go to
 * SLRU areas every time.
 *
 * The cache lasts for the duration of a single transaction, the rationale
 * for this being that most entries will contain our own TransactionId and
 * so they will be uninteresting by the time our next transaction starts.
 * (XXX not clear that this is correct --- other members of the MultiXact
 * could hang around longer than we did.  However, it's not clear what a
 * better policy for flushing old cache entries would be.)	FIXME actually
 * this is plain wrong now that multixact's may contain update Xids.
 *
 * We allocate the cache entries in a memory context that is deleted at
 * transaction end, so we don't need to do retail freeing of entries.
 */
typedef struct mXactCacheEnt
{
	MultiXactId multi;
	int			nmembers;
	dlist_node	node;
	MultiXactMember members[FLEXIBLE_ARRAY_MEMBER];
} mXactCacheEnt;

#define MAX_CACHE_ENTRIES	256
static dclist_head MXactCache = DCLIST_STATIC_INIT(MXactCache);
static MemoryContext MXactContext = NULL;

#ifdef MULTIXACT_DEBUG
#define debug_elog2(a,b) elog(a,b)
#define debug_elog3(a,b,c) elog(a,b,c)
#define debug_elog4(a,b,c,d) elog(a,b,c,d)
#define debug_elog5(a,b,c,d,e) elog(a,b,c,d,e)
#define debug_elog6(a,b,c,d,e,f) elog(a,b,c,d,e,f)
#else
#define debug_elog2(a,b)
#define debug_elog3(a,b,c)
#define debug_elog4(a,b,c,d)
#define debug_elog5(a,b,c,d,e)
#define debug_elog6(a,b,c,d,e,f)
#endif

/* internal MultiXactId management */
static void MultiXactIdSetOldestVisible(void);
static void RecordNewMultiXact(MultiXactId multi, MultiXactOffset offset,
							   int nmembers, MultiXactMember *members);
static MultiXactId GetNewMultiXactId(int nmembers, MultiXactOffset *offset);

/* MultiXact cache management */
static int	mxactMemberComparator(const void *arg1, const void *arg2);
static MultiXactId mXactCacheGetBySet(int nmembers, MultiXactMember *members);
static int	mXactCacheGetById(MultiXactId multi, MultiXactMember **members);
static void mXactCachePut(MultiXactId multi, int nmembers,
						  MultiXactMember *members);

/* management of SLRU infrastructure */

/* opaque_data type for MultiXactMemberIoErrorDetail */
typedef struct MultiXactMemberSlruReadContext
{
	MultiXactId multi;
	MultiXactOffset offset;
} MultiXactMemberSlruReadContext;

static void ExtendMultiXactOffset(MultiXactId multi);
static void ExtendMultiXactMember(MultiXactOffset offset, int nmembers);
static void SetOldestOffset(void);
static bool find_multixact_start(MultiXactId multi, MultiXactOffset *result);
static void WriteMTruncateXlogRec(Oid oldestMultiDB,
								  MultiXactId oldestMulti,
								  MultiXactOffset oldestOffset);


/*
 * MultiXactIdCreate
 *		Construct a MultiXactId representing two TransactionIds.
 *
 * The two XIDs must be different, or be requesting different statuses.
 *
 * NB - we don't worry about our local MultiXactId cache here, because that
 * is handled by the lower-level routines.
 */
/*
 * 中文注释：
 * 用两个 TransactionId 及其锁状态创建一个新的 MultiXactId。
 *
 * 两个 XID 必须不同，或者虽然相同但请求的状态不同；相同 XID 且相同状态没有意义。
 * 调用前必须已经调用 MultiXactIdSetOldestMember()，把当前事务可能成为成员的最老
 * MultiXact 记录到共享槽位。函数把两个成员放入临时数组，交给
 * MultiXactIdCreateFromMembers 完成去重、分配 ID、写 WAL 和写 SLRU。这里不检查
 * 两个 XID 是否仍在运行，因为典型调用者刚刚检查过，重复检查代价高。
 */
MultiXactId
MultiXactIdCreate(TransactionId xid1, MultiXactStatus status1,
				  TransactionId xid2, MultiXactStatus status2)
{
	MultiXactId newMulti;
	MultiXactMember members[2];

	Assert(TransactionIdIsValid(xid1));
	Assert(TransactionIdIsValid(xid2));

	Assert(!TransactionIdEquals(xid1, xid2) || (status1 != status2));

	/* MultiXactIdSetOldestMember() must have been called already. */
	Assert(MultiXactIdIsValid(*MyOldestMemberMXactIdSlot()));

	/*
	 * Note: unlike MultiXactIdExpand, we don't bother to check that both XIDs
	 * are still running.  In typical usage, xid2 will be our own XID and the
	 * caller just did a check on xid1, so it'd be wasted effort.
	 */

	members[0].xid = xid1;
	members[0].status = status1;
	members[1].xid = xid2;
	members[1].status = status2;

	newMulti = MultiXactIdCreateFromMembers(2, members);

	debug_elog3(DEBUG2, "Create: %s",
				mxid_to_string(newMulti, 2, members));

	return newMulti;
}

/*
 * MultiXactIdExpand
 *		Add a TransactionId to a pre-existing MultiXactId.
 *
 * If the TransactionId is already a member of the passed MultiXactId with the
 * same status, just return it as-is.
 *
 * Note that we do NOT actually modify the membership of a pre-existing
 * MultiXactId; instead we create a new one.  This is necessary to avoid
 * a race condition against code trying to wait for one MultiXactId to finish;
 * see notes in heapam.c.
 *
 * NB - we don't worry about our local MultiXactId cache here, because that
 * is handled by the lower-level routines.
 *
 * Note: It is critical that MultiXactIds that come from an old cluster (i.e.
 * one upgraded by pg_upgrade from a cluster older than this feature) are not
 * passed in.
 */
/*
 * 中文注释：
 * 把一个 TransactionId 及状态加入已有的 MultiXactId，并返回新的 MultiXactId。
 *
 * 关键设计：绝不原地修改已有 MultiXact 的成员集合，而是读取旧成员、过滤掉已经
 * 死亡且不再有意义的成员，再加入新成员，最后创建一个全新的 MultiXactId。这是为了
 * 避免与正在等待旧 MultiXact 结束的代码发生竞态。若旧 MultiXact 已经没有任何成员
 * （调用者检查后成员全部结束），则退化为创建一个单成员 MultiXact。若新 XID 已经以
 * 相同状态存在，直接复用旧 ID。缓存由更底层的 CreateFromMembers 处理。
 */
MultiXactId
MultiXactIdExpand(MultiXactId multi, TransactionId xid, MultiXactStatus status)
{
	MultiXactId newMulti;
	MultiXactMember *members;
	MultiXactMember *newMembers;
	int			nmembers;
	int			i;
	int			j;

	Assert(MultiXactIdIsValid(multi));
	Assert(TransactionIdIsValid(xid));

	/* MultiXactIdSetOldestMember() must have been called already. */
	Assert(MultiXactIdIsValid(*MyOldestMemberMXactIdSlot()));

	debug_elog5(DEBUG2, "Expand: received multi %u, xid %u status %s",
				multi, xid, mxstatus_to_string(status));

	/*
	 * Note: we don't allow for old multis here.  The reason is that the only
	 * caller of this function does a check that the multixact is no longer
	 * running.
	 */
	nmembers = GetMultiXactIdMembers(multi, &members, false, false);

	if (nmembers < 0)
	{
		MultiXactMember member;

		/*
		 * The MultiXactId is obsolete.  This can only happen if all the
		 * MultiXactId members stop running between the caller checking and
		 * passing it to us.  It would be better to return that fact to the
		 * caller, but it would complicate the API and it's unlikely to happen
		 * too often, so just deal with it by creating a singleton MultiXact.
		 */
		member.xid = xid;
		member.status = status;
		newMulti = MultiXactIdCreateFromMembers(1, &member);

		debug_elog4(DEBUG2, "Expand: %u has no members, create singleton %u",
					multi, newMulti);
		return newMulti;
	}

	/*
	 * If the TransactionId is already a member of the MultiXactId with the
	 * same status, just return the existing MultiXactId.
	 */
	for (i = 0; i < nmembers; i++)
	{
		if (TransactionIdEquals(members[i].xid, xid) &&
			(members[i].status == status))
		{
			debug_elog4(DEBUG2, "Expand: %u is already a member of %u",
						xid, multi);
			pfree(members);
			return multi;
		}
	}

	/*
	 * Determine which of the members of the MultiXactId are still of
	 * interest. This is any running transaction, and also any transaction
	 * that grabbed something stronger than just a lock and was committed. (An
	 * update that aborted is of no interest here; and having more than one
	 * update Xid in a multixact would cause errors elsewhere.)
	 *
	 * Removing dead members is not just an optimization: freezing of tuples
	 * whose Xmax are multis depends on this behavior.
	 *
	 * Note we have the same race condition here as above: j could be 0 at the
	 * end of the loop.
	 */
	newMembers = palloc_array(MultiXactMember, nmembers + 1);

	for (i = 0, j = 0; i < nmembers; i++)
	{
		if (TransactionIdIsInProgress(members[i].xid) ||
			(ISUPDATE_from_mxstatus(members[i].status) &&
			 TransactionIdDidCommit(members[i].xid)))
		{
			newMembers[j].xid = members[i].xid;
			newMembers[j++].status = members[i].status;
		}
	}

	newMembers[j].xid = xid;
	newMembers[j++].status = status;
	newMulti = MultiXactIdCreateFromMembers(j, newMembers);

	pfree(members);
	pfree(newMembers);

	debug_elog3(DEBUG2, "Expand: returning new multi %u", newMulti);

	return newMulti;
}

/*
 * MultiXactIdIsRunning
 *		Returns whether a MultiXactId is "running".
 *
 * We return true if at least one member of the given MultiXactId is still
 * running.  Note that a "false" result is certain not to change,
 * because it is not legal to add members to an existing MultiXactId.
 *
 * Caller is expected to have verified that the multixact does not come from
 * a pg_upgraded share-locked tuple.
 */
/*
 * 中文注释：
 * 判断一个 MultiXactId 是否仍然“运行中”，即至少有一个成员事务尚未结束。
 *
 * 先查本地缓存/SLRU 取出成员；若没有成员（或来自 pg_upgrade 的旧格式）直接返回
 * false。随后先检查成员中是否有当前事务（含子事务）的 XID，这是廉价的快速路径；
 * 再逐个调用 TransactionIdIsInProgress 查询 ProcArray。isLockOnly 表示调用者确定
 * 该 MultiXact 只用于加锁、不包含更新事务，此时可以跳过“太老”的成员检查并快速
 * 返回 false。返回 false 是稳定的：MultiXact 不允许追加成员，所以不会 later 变 true。
 */
bool
MultiXactIdIsRunning(MultiXactId multi, bool isLockOnly)
{
	MultiXactMember *members;
	int			nmembers;
	int			i;

	debug_elog3(DEBUG2, "IsRunning %u?", multi);

	/*
	 * "false" here means we assume our callers have checked that the given
	 * multi cannot possibly come from a pg_upgraded database.
	 */
	nmembers = GetMultiXactIdMembers(multi, &members, false, isLockOnly);

	if (nmembers <= 0)
	{
		debug_elog2(DEBUG2, "IsRunning: no members");
		return false;
	}

	/*
	 * Checking for myself is cheap compared to looking in shared memory;
	 * return true if any live subtransaction of the current top-level
	 * transaction is a member.
	 *
	 * This is not needed for correctness, it's just a fast path.
	 */
	for (i = 0; i < nmembers; i++)
	{
		if (TransactionIdIsCurrentTransactionId(members[i].xid))
		{
			debug_elog3(DEBUG2, "IsRunning: I (%d) am running!", i);
			pfree(members);
			return true;
		}
	}

	/*
	 * This could be made faster by having another entry point in procarray.c,
	 * walking the PGPROC array only once for all the members.  But in most
	 * cases nmembers should be small enough that it doesn't much matter.
	 */
	for (i = 0; i < nmembers; i++)
	{
		if (TransactionIdIsInProgress(members[i].xid))
		{
			debug_elog4(DEBUG2, "IsRunning: member %d (%u) is running",
						i, members[i].xid);
			pfree(members);
			return true;
		}
	}

	pfree(members);

	debug_elog3(DEBUG2, "IsRunning: %u is not running", multi);

	return false;
}

/*
 * MultiXactIdSetOldestMember
 *		Save the oldest MultiXactId this transaction could be a member of.
 *
 * We set the OldestMemberMXactId for a given transaction the first time it's
 * going to do some operation that might require a MultiXactId (tuple lock,
 * update or delete).  We need to do this even if we end up using a
 * TransactionId instead of a MultiXactId, because there is a chance that
 * another transaction would add our XID to a MultiXactId.
 *
 * The value to set is the next-to-be-assigned MultiXactId, so this is meant to
 * be called just before doing any such possibly-MultiXactId-able operation.
 */
/*
 * 中文注释：
 * 在当前事务第一次可能成为 MultiXact 成员之前，记录一个安全下界。
 *
 * 把当前共享的 nextMXact 写入本后端的 OldestMemberMXactId 槽位。即使最终只使用
 * 普通 XID 而不创建 MultiXact，也必须这样做：其他事务可能把我们的 XID 加入某个
 * MultiXact，而那个 MultiXact 的 ID 一定 >= 当前 nextMXact。使用共享锁即可，因为
 * 只需阻止别人推进 nextMXact；槽位只有本进程写、其他进程读。若已经设置过则直接
 * 返回，避免重复加锁。
 */
void
MultiXactIdSetOldestMember(void)
{
	if (!MultiXactIdIsValid(*MyOldestMemberMXactIdSlot()))
	{
		MultiXactId nextMXact;

		/*
		 * You might think we don't need to acquire a lock here, since
		 * fetching and storing of TransactionIds is probably atomic, but in
		 * fact we do: suppose we pick up nextMXact and then lose the CPU for
		 * a long time.  Someone else could advance nextMXact, and then
		 * another someone else could compute an OldestVisibleMXactId that
		 * would be after the value we are going to store when we get control
		 * back.  Which would be wrong.
		 *
		 * Note that a shared lock is sufficient, because it's enough to stop
		 * someone from advancing nextMXact; and nobody else could be trying
		 * to write to our OldestMember entry, only reading (and we assume
		 * storing it is atomic.)
		 */
		LWLockAcquire(MultiXactGenLock, LW_SHARED);

		nextMXact = MultiXactState->nextMXact;

		*MyOldestMemberMXactIdSlot() = nextMXact;

		LWLockRelease(MultiXactGenLock);

		debug_elog4(DEBUG2, "MultiXact: setting OldestMember[%d] = %u",
					MyProcNumber, nextMXact);
	}
}

/*
 * MultiXactIdSetOldestVisible
 *		Save the oldest MultiXactId this transaction considers possibly live.
 *
 * We set the OldestVisibleMXactId for a given transaction the first time
 * it's going to inspect any MultiXactId.  Once we have set this, we are
 * guaranteed that SLRU data for MultiXactIds >= our own OldestVisibleMXactId
 * won't be truncated away.
 *
 * The value to set is the oldest of nextMXact and all the valid per-backend
 * OldestMemberMXactId[] entries.  Because of the locking we do, we can be
 * certain that no subsequent call to MultiXactIdSetOldestMember can set
 * an OldestMemberMXactId[] entry older than what we compute here.  Therefore
 * there is no live transaction, now or later, that can be a member of any
 * MultiXactId older than the OldestVisibleMXactId we compute here.
 */
/*
 * 中文注释：
 * 在当前事务第一次检查 MultiXact 时，计算并保存“可能存活的最老 MultiXactId”。
 *
 * 取 nextMXact 与所有后端 OldestMemberMXactId 槽位中的最小值，写入本后端的
 * OldestVisibleMXactId。由于持有 MultiXactGenLock 排他锁，计算之后不可能再有事务
 * 把更老的 MultiXact 设为成员下界，因此任何比该值更老的 MultiXact 都不可能仍有
 * 活跃成员。该下界用于阻止 truncate 删除本事务仍可能读取的 SLRU 数据，也用于
 * GetMultiXactIdMembers 的范围检查。
 */
static void
MultiXactIdSetOldestVisible(void)
{
	if (!MultiXactIdIsValid(*MyOldestVisibleMXactIdSlot()))
	{
		MultiXactId oldestMXact;
		int			i;

		LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);

		oldestMXact = MultiXactState->nextMXact;
		for (i = 0; i < NumMemberSlots; i++)
		{
			MultiXactId thisoldest = OldestMemberMXactId[i];

			if (MultiXactIdIsValid(thisoldest) &&
				MultiXactIdPrecedes(thisoldest, oldestMXact))
				oldestMXact = thisoldest;
		}

		*MyOldestVisibleMXactIdSlot() = oldestMXact;

		LWLockRelease(MultiXactGenLock);

		debug_elog4(DEBUG2, "MultiXact: setting OldestVisible[%d] = %u",
					MyProcNumber, oldestMXact);
	}
}

/*
 * ReadNextMultiXactId
 *		Return the next MultiXactId to be assigned, but don't allocate it
 */
/*
 * 中文注释：
 * 只读取下一个将要分配的 MultiXactId，不实际分配。
 *
 * 在 MultiXactGenLock 共享锁下读取共享状态，保证读到一致值。用于需要知道当前
 * 计数器但不应推进它的场景，例如统计、检查点估算或调试。
 */
MultiXactId
ReadNextMultiXactId(void)
{
	MultiXactId mxid;

	/* XXX we could presumably do this without a lock. */
	LWLockAcquire(MultiXactGenLock, LW_SHARED);
	mxid = MultiXactState->nextMXact;
	LWLockRelease(MultiXactGenLock);

	return mxid;
}

/*
 * ReadMultiXactIdRange
 *		Get the range of IDs that may still be referenced by a relation.
 */
/*
 * 中文注释：
 * 一次读取 MultiXactId 的可用范围：最老仍可能被引用的 ID 和下一个待分配 ID。
 *
 * 两个值在同一把共享锁下读取，避免调用者看到彼此不一致的边界。调用者可用它们
 * 判断某个 MultiXactId 是否在合法范围内，或估算仍存活的 MultiXact 数量。
 */
void
ReadMultiXactIdRange(MultiXactId *oldest, MultiXactId *next)
{
	LWLockAcquire(MultiXactGenLock, LW_SHARED);
	*oldest = MultiXactState->oldestMultiXactId;
	*next = MultiXactState->nextMXact;
	LWLockRelease(MultiXactGenLock);
}


/*
 * MultiXactIdCreateFromMembers
 *		Make a new MultiXactId from the specified set of members
 *
 * Make XLOG, SLRU and cache entries for a new MultiXactId, recording the
 * given TransactionIds as members.  Returns the newly created MultiXactId.
 *
 * NB: the passed members[] array will be sorted in-place.
 */
/*
 * 中文注释：
 * 从给定的成员集合创建一个新的 MultiXactId，是本模块创建路径的核心。
 *
 * 步骤：
 *   1. 先查本地事务级缓存，若相同成员集合已经存在则直接复用，降低 ID 消耗；
 *   2. 校验集合中最多只有一个“更新”成员（MultiXactStatusUpdate/NoKeyUpdate），
 *      因为一个元组不能被多个更新事务同时修改；
 *   3. 调用 GetNewMultiXactId 分配 ID 和 members 区间，并扩展 offsets/members
 *      SLRU（可能写零页 WAL）；
 *   4. 写 XLOG_MULTIXACT_CREATE_ID，记录 mid、起始 offset 和全部成员；
 *   5. 调用 RecordNewMultiXact 把成员写入 SLRU，最后结束临界区并放入本地缓存。
 * 注意成员数组会被就地排序；该函数也用于 vacuum 冻结 MultiXact，因此不要求当前
 * 事务已调用 MultiXactIdSetOldestMember。
 */
MultiXactId
MultiXactIdCreateFromMembers(int nmembers, MultiXactMember *members)
{
	MultiXactId multi;
	MultiXactOffset offset;
	xl_multixact_create xlrec;

	debug_elog3(DEBUG2, "Create: %s",
				mxid_to_string(InvalidMultiXactId, nmembers, members));

	/*
	 * See if the same set of members already exists in our cache; if so, just
	 * re-use that MultiXactId.  (Note: it might seem that looking in our
	 * cache is insufficient, and we ought to search disk to see if a
	 * duplicate definition already exists.  But since we only ever create
	 * MultiXacts containing our own XID, in most cases any such MultiXacts
	 * were in fact created by us, and so will be in our cache.  There are
	 * corner cases where someone else added us to a MultiXact without our
	 * knowledge, but it's not worth checking for.)
	 */
	multi = mXactCacheGetBySet(nmembers, members);
	if (MultiXactIdIsValid(multi))
	{
		debug_elog2(DEBUG2, "Create: in cache!");
		return multi;
	}

	/* Verify that there is a single update Xid among the given members. */
	{
		int			i;
		bool		has_update = false;

		for (i = 0; i < nmembers; i++)
		{
			if (ISUPDATE_from_mxstatus(members[i].status))
			{
				if (has_update)
					elog(ERROR, "new multixact has more than one updating member: %s",
						 mxid_to_string(InvalidMultiXactId, nmembers, members));
				has_update = true;
			}
		}
	}

	/* Load the injection point before entering the critical section */
	INJECTION_POINT_LOAD("multixact-create-from-members");

	/*
	 * Assign the MXID and offsets range to use, and make sure there is space
	 * in the OFFSETs and MEMBERs files.  NB: this routine does
	 * START_CRIT_SECTION().
	 *
	 * Note: unlike MultiXactIdCreate and MultiXactIdExpand, we do not check
	 * that we've called MultiXactIdSetOldestMember here.  This is because
	 * this routine is used in some places to create new MultiXactIds of which
	 * the current backend is not a member, notably during freezing of multis
	 * in vacuum.  During vacuum, in particular, it would be unacceptable to
	 * keep OldestMulti set, in case it runs for long.
	 */
	multi = GetNewMultiXactId(nmembers, &offset);

	INJECTION_POINT_CACHED("multixact-create-from-members", NULL);

	/* Make an XLOG entry describing the new MXID. */
	xlrec.mid = multi;
	xlrec.moff = offset;
	xlrec.nmembers = nmembers;

	/*
	 * XXX Note: there's a lot of padding space in MultiXactMember.  We could
	 * find a more compact representation of this Xlog record -- perhaps all
	 * the status flags in one XLogRecData, then all the xids in another one?
	 * Not clear that it's worth the trouble though.
	 */
	XLogBeginInsert();
	XLogRegisterData(&xlrec, SizeOfMultiXactCreate);
	XLogRegisterData(members, nmembers * sizeof(MultiXactMember));

	(void) XLogInsert(RM_MULTIXACT_ID, XLOG_MULTIXACT_CREATE_ID);

	/* Now enter the information into the OFFSETs and MEMBERs logs */
	RecordNewMultiXact(multi, offset, nmembers, members);

	/* Done with critical section */
	END_CRIT_SECTION();

	/* Store the new MultiXactId in the local cache, too */
	mXactCachePut(multi, nmembers, members);

	debug_elog2(DEBUG2, "Create: all done");

	return multi;
}

/*
 * RecordNewMultiXact
 *		Write info about a new multixact into the offsets and members files
 *
 * This is broken out of MultiXactIdCreateFromMembers so that xlog replay can
 * use it.
 */
/*
 * 中文注释：
 * 把一个新 MultiXact 的成员信息写入 offsets 和 members 两个 SLRU。
 *
 * offsets SLRU 为每个 MultiXactId 保存其成员数组的起始偏移；本函数既要写入当前
 * MultiXact 的起始 offset，也要把“下一个 MultiXact”的起始 offset 设为当前成员
 * 区间末尾（并跳过 0，因为 0 表示无效）。当两个 ID 落在不同 offset 页时，需要
 * 切换到下一页并换 bank 锁。随后逐个成员写入 members SLRU：成员 XID 与 2-bit
 * 状态标志分开存储，可能跨页、跨 bank；代码在页变化时释放旧 bank 锁、获取新锁。
 * 函数由创建路径和 WAL 重放共用，因此必须幂等：若目标位置已经是期望值则不动，
 * 否则要求原值为 0 再写入并标脏。
 */
static void
RecordNewMultiXact(MultiXactId multi, MultiXactOffset offset,
				   int nmembers, MultiXactMember *members)
{
	int64		pageno;
	int64		prev_pageno;
	int			entryno;
	int			slotno;
	MultiXactOffset *offptr;
	MultiXactId next;
	int64		next_pageno;
	int			next_entryno;
	MultiXactOffset *next_offptr;
	MultiXactOffset next_offset;
	LWLock	   *lock;
	LWLock	   *prevlock = NULL;

	/* position of this multixid in the offsets SLRU area  */
	pageno = MultiXactIdToOffsetPage(multi);
	entryno = MultiXactIdToOffsetEntry(multi);

	/* position of the next multixid */
	next = NextMultiXactId(multi);
	next_pageno = MultiXactIdToOffsetPage(next);
	next_entryno = MultiXactIdToOffsetEntry(next);

	/*
	 * Set the starting offset of this multixid's members.
	 *
	 * In the common case, it was already set by the previous
	 * RecordNewMultiXact call, as this was the next multixid of the previous
	 * multixid.  But if multiple backends are generating multixids
	 * concurrently, we might race ahead and get called before the previous
	 * multixid.
	 */
	lock = SimpleLruGetBankLock(MultiXactOffsetCtl, pageno);
	LWLockAcquire(lock, LW_EXCLUSIVE);

	slotno = SimpleLruReadPage(MultiXactOffsetCtl, pageno, true, &multi);
	offptr = (MultiXactOffset *) MultiXactOffsetCtl->shared->page_buffer[slotno];
	offptr += entryno;

	if (*offptr != offset)
	{
		/* should already be set to the correct value, or not at all */
		Assert(*offptr == 0);
		*offptr = offset;
		MultiXactOffsetCtl->shared->page_dirty[slotno] = true;
	}

	/*
	 * Set the next multixid's offset to the end of this multixid's members.
	 */
	if (next_pageno == pageno)
	{
		next_offptr = offptr + 1;
	}
	else
	{
		/* must be the first entry on the page */
		Assert(next_entryno == 0 || next == FirstMultiXactId);

		/* Swap the lock for a lock on the next page */
		LWLockRelease(lock);
		lock = SimpleLruGetBankLock(MultiXactOffsetCtl, next_pageno);
		LWLockAcquire(lock, LW_EXCLUSIVE);

		slotno = SimpleLruReadPage(MultiXactOffsetCtl, next_pageno, true, &next);
		next_offptr = (MultiXactOffset *) MultiXactOffsetCtl->shared->page_buffer[slotno];
		next_offptr += next_entryno;
	}

	/* Like in GetNewMultiXactId(), skip over offset 0 */
	next_offset = offset + nmembers;
	if (next_offset == 0)
		next_offset = 1;
	if (*next_offptr != next_offset)
	{
		/* should already be set to the correct value, or not at all */
		Assert(*next_offptr == 0);
		*next_offptr = next_offset;
		MultiXactOffsetCtl->shared->page_dirty[slotno] = true;
	}

	/* Release MultiXactOffset SLRU lock. */
	LWLockRelease(lock);

	prev_pageno = -1;

	for (int i = 0; i < nmembers; i++, offset++)
	{
		TransactionId *memberptr;
		uint32	   *flagsptr;
		uint32		flagsval;
		int			bshift;
		int			flagsoff;
		int			memberoff;

		Assert(members[i].status <= MultiXactStatusUpdate);

		pageno = MXOffsetToMemberPage(offset);
		memberoff = MXOffsetToMemberOffset(offset);
		flagsoff = MXOffsetToFlagsOffset(offset);
		bshift = MXOffsetToFlagsBitShift(offset);

		if (pageno != prev_pageno)
		{
			MultiXactMemberSlruReadContext slru_read_context = {multi, offset};

			/*
			 * MultiXactMember SLRU page is changed so check if this new page
			 * fall into the different SLRU bank then release the old bank's
			 * lock and acquire lock on the new bank.
			 */
			lock = SimpleLruGetBankLock(MultiXactMemberCtl, pageno);
			if (lock != prevlock)
			{
				if (prevlock != NULL)
					LWLockRelease(prevlock);

				LWLockAcquire(lock, LW_EXCLUSIVE);
				prevlock = lock;
			}
			slotno = SimpleLruReadPage(MultiXactMemberCtl, pageno, true,
									   &slru_read_context);
			prev_pageno = pageno;
		}

		memberptr = (TransactionId *)
			(MultiXactMemberCtl->shared->page_buffer[slotno] + memberoff);

		*memberptr = members[i].xid;

		flagsptr = (uint32 *)
			(MultiXactMemberCtl->shared->page_buffer[slotno] + flagsoff);

		flagsval = *flagsptr;
		flagsval &= ~(((1 << MXACT_MEMBER_BITS_PER_XACT) - 1) << bshift);
		flagsval |= (members[i].status << bshift);
		*flagsptr = flagsval;

		MultiXactMemberCtl->shared->page_dirty[slotno] = true;
	}

	if (prevlock != NULL)
		LWLockRelease(prevlock);
}

/*
 * GetNewMultiXactId
 *		Get the next MultiXactId.
 *
 * Also, reserve the needed amount of space in the "members" area.  The
 * starting offset of the reserved space is returned in *offset.
 *
 * This may generate XLOG records for expansion of the offsets and/or members
 * files.  Unfortunately, we have to do that while holding MultiXactGenLock
 * to avoid race conditions --- the XLOG record for zeroing a page must appear
 * before any backend can possibly try to store data in that page!
 *
 * We start a critical section before advancing the shared counters.  The
 * caller must end the critical section after writing SLRU data.
 */
/*
 * 中文注释：
 * 分配下一个 MultiXactId，并在 members 空间预留 nmembers 个槽位。
 *
 * 在 MultiXactGenLock 排他锁下读取 nextMXact，并检查回卷保护阈值：
 *   - 超过 multiVacLimit 或成员空间阈值：触发 autovacuum；
 *   - 超过 multiWarnLimit：发出 WARNING；
 *   - 超过 multiStopLimit：拒绝分配并 ERROR，避免 MultiXact 回卷导致数据丢失。
 * 为避免在持有锁时做 get_database_name 等可能阻塞的操作，必要时先释放锁、发信号/
 * 告警，再重新加锁读取最新值。
 *
 * 随后调用 ExtendMultiXactOffset/ExtendMultiXactMember 确保 SLRU 有空间（可能写
 * XLOG_MULTIXACT_ZERO_*_PAGE 记录），预留 offset，然后进入临界区推进 nextMXact 和
 * nextOffset。临界区要持续到调用者把成员数据真正写入 SLRU，否则崩溃可能留下
 * “ID 已推进但成员未写”的半成品。
 */
static MultiXactId
GetNewMultiXactId(int nmembers, MultiXactOffset *offset)
{
	MultiXactId result;
	MultiXactOffset nextOffset;

	debug_elog3(DEBUG2, "GetNew: for %d xids", nmembers);

	/* safety check, we should never get this far in a HS standby */
	if (RecoveryInProgress())
		elog(ERROR, "cannot assign MultiXactIds during recovery");

	LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);

	/* Assign the MXID */
	result = MultiXactState->nextMXact;

	/*----------
	 * Check to see if it's safe to assign another MultiXactId.  This protects
	 * against catastrophic data loss due to multixact wraparound.  The basic
	 * rules are:
	 *
	 * If we're past multiVacLimit or the safe threshold for member storage
	 * space, or we don't know what the safe threshold for member storage is,
	 * start trying to force autovacuum cycles.
	 * If we're past multiWarnLimit, start issuing warnings.
	 * If we're past multiStopLimit, refuse to create new MultiXactIds.
	 *
	 * Note these are pretty much the same protections in GetNewTransactionId.
	 *----------
	 */
	if (!MultiXactIdPrecedes(result, MultiXactState->multiVacLimit))
	{
		/*
		 * For safety's sake, we release MultiXactGenLock while sending
		 * signals, warnings, etc.  This is not so much because we care about
		 * preserving concurrency in this situation, as to avoid any
		 * possibility of deadlock while doing get_database_name(). First,
		 * copy all the shared values we'll need in this path.
		 */
		MultiXactId multiWarnLimit = MultiXactState->multiWarnLimit;
		MultiXactId multiStopLimit = MultiXactState->multiStopLimit;
		MultiXactId multiWrapLimit = MultiXactState->multiWrapLimit;
		Oid			oldest_datoid = MultiXactState->oldestMultiXactDB;

		LWLockRelease(MultiXactGenLock);

		if (IsUnderPostmaster &&
			!MultiXactIdPrecedes(result, multiStopLimit))
		{
			char	   *oldest_datname = get_database_name(oldest_datoid);

			/*
			 * Immediately kick autovacuum into action as we're already in
			 * ERROR territory.
			 */
			SendPostmasterSignal(PMSIGNAL_START_AUTOVAC_LAUNCHER);

			/* complain even if that DB has disappeared */
			if (oldest_datname)
				ereport(ERROR,
						(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
						 errmsg("database is not accepting commands that assign new MultiXactIds to avoid wraparound data loss in database \"%s\"",
								oldest_datname),
						 errhint("Execute a database-wide VACUUM in that database.\n"
								 "You might also need to commit or roll back old prepared transactions.")));
			else
				ereport(ERROR,
						(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
						 errmsg("database is not accepting commands that assign new MultiXactIds to avoid wraparound data loss in database with OID %u",
								oldest_datoid),
						 errhint("Execute a database-wide VACUUM in that database.\n"
								 "You might also need to commit or roll back old prepared transactions.")));
		}

		/*
		 * To avoid swamping the postmaster with signals, we issue the autovac
		 * request only once per 64K multis generated.  This still gives
		 * plenty of chances before we get into real trouble.
		 */
		if (IsUnderPostmaster && ((result % 65536) == 0 || result == FirstMultiXactId))
			SendPostmasterSignal(PMSIGNAL_START_AUTOVAC_LAUNCHER);

		if (!MultiXactIdPrecedes(result, multiWarnLimit))
		{
			char	   *oldest_datname = get_database_name(oldest_datoid);

			/* complain even if that DB has disappeared */
			if (oldest_datname)
				ereport(WARNING,
						(errmsg_plural("database \"%s\" must be vacuumed before %u more MultiXactId is used",
									   "database \"%s\" must be vacuumed before %u more MultiXactIds are used",
									   multiWrapLimit - result,
									   oldest_datname,
									   multiWrapLimit - result),
						 errdetail("Approximately %.2f%% of MultiXactId space remains before wraparound.",
								   (double) (multiWrapLimit - result) / (MaxMultiXactId / 2) * 100),
						 errhint("Execute a database-wide VACUUM in that database.\n"
								 "You might also need to commit or roll back old prepared transactions.")));
			else
				ereport(WARNING,
						(errmsg_plural("database with OID %u must be vacuumed before %u more MultiXactId is used",
									   "database with OID %u must be vacuumed before %u more MultiXactIds are used",
									   multiWrapLimit - result,
									   oldest_datoid,
									   multiWrapLimit - result),
						 errdetail("Approximately %.2f%% of MultiXactId space remains before wraparound.",
								   (double) (multiWrapLimit - result) / (MaxMultiXactId / 2) * 100),
						 errhint("Execute a database-wide VACUUM in that database.\n"
								 "You might also need to commit or roll back old prepared transactions.")));
		}

		/* Re-acquire lock and start over */
		LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);
		result = MultiXactState->nextMXact;
	}

	/*
	 * Make sure there is room for the next MXID in the file.  Assigning this
	 * MXID sets the next MXID's offset already.
	 */
	ExtendMultiXactOffset(NextMultiXactId(result));

	/*
	 * Reserve the members space, similarly to above.
	 */
	nextOffset = MultiXactState->nextOffset;

	/*
	 * Offsets are 64-bit integers and will never wrap around.  Firstly, it
	 * would take an unrealistic amount of time and resources to consume 2^64
	 * offsets.  Secondly, multixid creation is WAL-logged, so you would run
	 * out of LSNs before reaching offset wraparound.  Nevertheless, check for
	 * wraparound as a sanity check.
	 */
	if (nextOffset + nmembers < nextOffset)
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("MultiXact members would wrap around")));
	*offset = nextOffset;

	ExtendMultiXactMember(nextOffset, nmembers);

	/*
	 * Critical section from here until caller has written the data into the
	 * just-reserved SLRU space; we don't want to error out with a partly
	 * written MultiXact structure.  (In particular, failing to write our
	 * start offset after advancing nextMXact would effectively corrupt the
	 * previous MultiXact.)
	 */
	START_CRIT_SECTION();

	/*
	 * Advance counters.  As in GetNewTransactionId(), this must not happen
	 * until after file extension has succeeded!
	 */
	MultiXactState->nextMXact = NextMultiXactId(result);
	MultiXactState->nextOffset += nmembers;

	LWLockRelease(MultiXactGenLock);

	debug_elog4(DEBUG2, "GetNew: returning %u offset %" PRIu64,
				result, *offset);
	return result;
}

/*
 * GetMultiXactIdMembers
 *		Return the set of MultiXactMembers that make up a MultiXactId
 *
 * Return value is the number of members found, or -1 if there are none,
 * and *members is set to a newly palloc'ed array of members.  It's the
 * caller's responsibility to free it when done with it.
 *
 * from_pgupgrade must be passed as true if and only if only the multixact
 * corresponds to a value from a tuple that was locked in a 9.2-or-older
 * installation and later pg_upgrade'd (that is, the infomask is
 * HEAP_LOCKED_UPGRADED).  In this case, we know for certain that no members
 * can still be running, so we return -1 just like for an empty multixact
 * without any further checking.  It would be wrong to try to resolve such a
 * multixact: either the multixact is within the current valid multixact
 * range, in which case the returned result would be bogus, or outside that
 * range, in which case an error would be raised.
 *
 * In all other cases, the passed multixact must be within the known valid
 * range, that is, greater than or equal to oldestMultiXactId, and less than
 * nextMXact.  Otherwise, an error is raised.
 *
 * isLockOnly must be set to true if caller is certain that the given multi
 * is used only to lock tuples; can be false without loss of correctness,
 * but passing a true means we can return quickly without checking for
 * old updates.
 */
/*
 * 中文注释：
 * 取出一个 MultiXactId 的全部成员（XID + 状态标志）。
 *
 * 返回成员数量；若 MultiXact 无效、来自 pg_upgrade 旧格式或已无成员，返回 -1 并
 * 把 *members 置 NULL。成功时分配新数组，调用者负责 pfree。
 *
 * 流程：先查本地缓存；必要时设置 OldestVisible 下界；在 MultiXactGenLock 下读取
 * oldestMultiXactId/nextMXact 做范围检查（过老说明已被截断，过新说明发生回卷，
 * 都是严重错误）；然后从 offsets SLRU 读取本 MultiXact 的起始 offset，以及下一个
 * MultiXact 的起始 offset，两者之差就是成员数量；最后按偏移读取 members SLRU 中的
 * XID 和状态位，并把结果放入缓存。isLockOnly 允许对“只用于加锁”的过老 MultiXact
 * 快速返回 -1，因为这种 MultiXact 不可能还有更新成员需要解析。
 */
int
GetMultiXactIdMembers(MultiXactId multi, MultiXactMember **members,
					  bool from_pgupgrade, bool isLockOnly)
{
	int64		pageno;
	int64		prev_pageno;
	int			entryno;
	int			slotno;
	MultiXactOffset *offptr;
	MultiXactOffset offset;
	MultiXactOffset nextMXOffset;
	int			length;
	MultiXactId oldestMXact;
	MultiXactId nextMXact;
	MultiXactMember *ptr;
	LWLock	   *lock;

	debug_elog3(DEBUG2, "GetMembers: asked for %u", multi);

	if (!MultiXactIdIsValid(multi) || from_pgupgrade)
	{
		*members = NULL;
		return -1;
	}

	/* See if the MultiXactId is in the local cache */
	length = mXactCacheGetById(multi, members);
	if (length >= 0)
	{
		debug_elog3(DEBUG2, "GetMembers: found %s in the cache",
					mxid_to_string(multi, length, *members));
		return length;
	}

	/* Set our OldestVisibleMXactId[] entry if we didn't already */
	MultiXactIdSetOldestVisible();

	/*
	 * If we know the multi is used only for locking and not for updates, then
	 * we can skip checking if the value is older than our oldest visible
	 * multi.  It cannot possibly still be running.
	 */
	if (isLockOnly &&
		MultiXactIdPrecedes(multi, *MyOldestVisibleMXactIdSlot()))
	{
		debug_elog2(DEBUG2, "GetMembers: a locker-only multi is too old");
		*members = NULL;
		return -1;
	}

	/*
	 * We check known limits on MultiXact before resorting to the SLRU area.
	 *
	 * An ID older than MultiXactState->oldestMultiXactId cannot possibly be
	 * useful; it has already been removed, or will be removed shortly, by
	 * truncation.  If one is passed, an error is raised.
	 *
	 * Also, an ID >= nextMXact shouldn't ever be seen here; if it is seen, it
	 * implies undetected ID wraparound has occurred.  This raises a hard
	 * error.
	 *
	 * Shared lock is enough here since we aren't modifying any global state.
	 * Acquire it just long enough to grab the current counter values.
	 */
	LWLockAcquire(MultiXactGenLock, LW_SHARED);

	oldestMXact = MultiXactState->oldestMultiXactId;
	nextMXact = MultiXactState->nextMXact;

	LWLockRelease(MultiXactGenLock);

	if (MultiXactIdPrecedes(multi, oldestMXact))
		ereport(ERROR,
				(errcode(ERRCODE_INTERNAL_ERROR),
				 errmsg("MultiXactId %u does no longer exist -- apparent wraparound",
						multi)));

	if (!MultiXactIdPrecedes(multi, nextMXact))
		ereport(ERROR,
				(errcode(ERRCODE_INTERNAL_ERROR),
				 errmsg("MultiXactId %u has not been created yet -- apparent wraparound",
						multi)));

	/*
	 * Find out the offset at which we need to start reading MultiXactMembers
	 * and the number of members in the multixact.  We determine the latter as
	 * the difference between this multixact's starting offset and the next
	 * one's.
	 */
	pageno = MultiXactIdToOffsetPage(multi);
	entryno = MultiXactIdToOffsetEntry(multi);

	/* Acquire the bank lock for the page we need. */
	lock = SimpleLruGetBankLock(MultiXactOffsetCtl, pageno);
	LWLockAcquire(lock, LW_EXCLUSIVE);

	/* read this multi's offset */
	slotno = SimpleLruReadPage(MultiXactOffsetCtl, pageno, true, &multi);
	offptr = (MultiXactOffset *) MultiXactOffsetCtl->shared->page_buffer[slotno];
	offptr += entryno;
	offset = *offptr;

	if (offset == 0)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("MultiXact %u has invalid offset", multi)));

	/* read next multi's offset */
	{
		MultiXactId tmpMXact;

		/* handle wraparound if needed */
		tmpMXact = NextMultiXactId(multi);

		prev_pageno = pageno;

		pageno = MultiXactIdToOffsetPage(tmpMXact);
		entryno = MultiXactIdToOffsetEntry(tmpMXact);

		if (pageno != prev_pageno)
		{
			LWLock	   *newlock;

			/*
			 * Since we're going to access a different SLRU page, if this page
			 * falls under a different bank, release the old bank's lock and
			 * acquire the lock of the new bank.
			 */
			newlock = SimpleLruGetBankLock(MultiXactOffsetCtl, pageno);
			if (newlock != lock)
			{
				LWLockRelease(lock);
				LWLockAcquire(newlock, LW_EXCLUSIVE);
				lock = newlock;
			}
			slotno = SimpleLruReadPage(MultiXactOffsetCtl, pageno, true, &tmpMXact);
		}

		offptr = (MultiXactOffset *) MultiXactOffsetCtl->shared->page_buffer[slotno];
		offptr += entryno;
		nextMXOffset = *offptr;
	}

	LWLockRelease(lock);
	lock = NULL;

	/* Sanity check the next offset */
	if (nextMXOffset == 0)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("MultiXact %u has invalid next offset", multi)));
	if (nextMXOffset == offset)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("MultiXact %u with offset (%" PRIu64 ") has zero members",
						multi, offset)));
	if (nextMXOffset < offset)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("MultiXact %u has offset (%" PRIu64 ") greater than its next offset (%" PRIu64 ")",
						multi, offset, nextMXOffset)));
	if (nextMXOffset - offset > INT32_MAX)
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("MultiXact %u has too many members (%" PRIu64 ")",
						multi, nextMXOffset - offset)));
	length = nextMXOffset - offset;

	/* read the members */
	ptr = (MultiXactMember *) palloc(length * sizeof(MultiXactMember));
	prev_pageno = -1;
	for (int i = 0; i < length; i++, offset++)
	{
		TransactionId *xactptr;
		uint32	   *flagsptr;
		int			flagsoff;
		int			bshift;
		int			memberoff;

		pageno = MXOffsetToMemberPage(offset);
		memberoff = MXOffsetToMemberOffset(offset);

		if (pageno != prev_pageno)
		{
			MultiXactMemberSlruReadContext slru_read_context = {multi, offset};
			LWLock	   *newlock;

			/*
			 * Since we're going to access a different SLRU page, if this page
			 * falls under a different bank, release the old bank's lock and
			 * acquire the lock of the new bank.
			 */
			newlock = SimpleLruGetBankLock(MultiXactMemberCtl, pageno);
			if (newlock != lock)
			{
				if (lock)
					LWLockRelease(lock);
				LWLockAcquire(newlock, LW_EXCLUSIVE);
				lock = newlock;
			}
			slotno = SimpleLruReadPage(MultiXactMemberCtl, pageno, true,
									   &slru_read_context);
			prev_pageno = pageno;
		}

		xactptr = (TransactionId *)
			(MultiXactMemberCtl->shared->page_buffer[slotno] + memberoff);
		Assert(TransactionIdIsValid(*xactptr));

		flagsoff = MXOffsetToFlagsOffset(offset);
		bshift = MXOffsetToFlagsBitShift(offset);
		flagsptr = (uint32 *) (MultiXactMemberCtl->shared->page_buffer[slotno] + flagsoff);

		ptr[i].xid = *xactptr;
		ptr[i].status = (*flagsptr >> bshift) & MXACT_MEMBER_XACT_BITMASK;
	}

	LWLockRelease(lock);

	/*
	 * Copy the result into the local cache.
	 */
	mXactCachePut(multi, length, ptr);

	debug_elog3(DEBUG2, "GetMembers: no cache for %s",
				mxid_to_string(multi, length, ptr));
	*members = ptr;
	return length;
}

/*
 * mxactMemberComparator
 *		qsort comparison function for MultiXactMember
 *
 * We can't use wraparound comparison for XIDs because that does not respect
 * the triangle inequality!  Any old sort order will do.
 */
/*
 * 中文注释：
 * qsort 使用的 MultiXactMember 比较函数：先按 XID 数值升序，再按状态数值升序。
 *
 * 这里刻意不使用 TransactionIdPrecedes 的回绕比较，因为回绕比较不满足三角形
 * 不等式，不能作为全序排序的判据；缓存去重只需要一个稳定、确定的排序即可。状态
 * 的高位在写入时已清零，因此可以直接比较整个结构。
 */
static int
mxactMemberComparator(const void *arg1, const void *arg2)
{
	MultiXactMember member1 = *(const MultiXactMember *) arg1;
	MultiXactMember member2 = *(const MultiXactMember *) arg2;

	if (member1.xid > member2.xid)
		return 1;
	if (member1.xid < member2.xid)
		return -1;
	if (member1.status > member2.status)
		return 1;
	if (member1.status < member2.status)
		return -1;
	return 0;
}

/*
 * mXactCacheGetBySet
 *		returns a MultiXactId from the cache based on the set of
 *		TransactionIds that compose it, or InvalidMultiXactId if
 *		none matches.
 *
 * This is helpful, for example, if two transactions want to lock a huge
 * table.  By using the cache, the second will use the same MultiXactId
 * for the majority of tuples, thus keeping MultiXactId usage low (saving
 * both I/O and wraparound issues).
 *
 * NB: the passed members array will be sorted in-place.
 */
/*
 * 中文注释：
 * 按“成员集合”在事务级缓存中查找已有的 MultiXactId，找不到返回
 * InvalidMultiXactId。
 *
 * 先把传入成员数组排序，使比较不受顺序影响；然后线性扫描缓存，先比较成员数量，
 * 再用 memcmp 比较整个数组。命中时把该缓存项移到链表头部（近似 LRU），返回其 ID。
 * 该缓存能显著减少同一组事务反复锁同一批元组时产生的重复 MultiXact，从而降低
 * SLRU I/O 和回卷压力。
 */
static MultiXactId
mXactCacheGetBySet(int nmembers, MultiXactMember *members)
{
	dlist_iter	iter;

	debug_elog3(DEBUG2, "CacheGet: looking for %s",
				mxid_to_string(InvalidMultiXactId, nmembers, members));

	/* sort the array so comparison is easy */
	qsort(members, nmembers, sizeof(MultiXactMember), mxactMemberComparator);

	dclist_foreach(iter, &MXactCache)
	{
		mXactCacheEnt *entry = dclist_container(mXactCacheEnt, node,
												iter.cur);

		if (entry->nmembers != nmembers)
			continue;

		/*
		 * We assume the cache entries are sorted, and that the unused bits in
		 * "status" are zeroed.
		 */
		if (memcmp(members, entry->members, nmembers * sizeof(MultiXactMember)) == 0)
		{
			debug_elog3(DEBUG2, "CacheGet: found %u", entry->multi);
			dclist_move_head(&MXactCache, iter.cur);
			return entry->multi;
		}
	}

	debug_elog2(DEBUG2, "CacheGet: not found :-(");
	return InvalidMultiXactId;
}

/*
 * mXactCacheGetById
 *		returns the composing MultiXactMember set from the cache for a
 *		given MultiXactId, if present.
 *
 * If successful, *xids is set to the address of a palloc'd copy of the
 * MultiXactMember set.  Return value is number of members, or -1 on failure.
 */
/*
 * 中文注释：
 * 按 MultiXactId 在事务级缓存中查找成员集合。
 *
 * 命中时分配一份成员数组副本交给调用者（调用者负责释放），把缓存项移到链表头，
 * 返回成员数量；未命中返回 -1。缓存只保存当前事务期间创建的/读取过的 MultiXact，
 * 事务结束随内存上下文一起销毁。
 */
static int
mXactCacheGetById(MultiXactId multi, MultiXactMember **members)
{
	dlist_iter	iter;

	debug_elog3(DEBUG2, "CacheGet: looking for %u", multi);

	dclist_foreach(iter, &MXactCache)
	{
		mXactCacheEnt *entry = dclist_container(mXactCacheEnt, node,
												iter.cur);

		if (entry->multi == multi)
		{
			MultiXactMember *ptr;
			Size		size;

			size = sizeof(MultiXactMember) * entry->nmembers;
			ptr = (MultiXactMember *) palloc(size);

			memcpy(ptr, entry->members, size);

			debug_elog3(DEBUG2, "CacheGet: found %s",
						mxid_to_string(multi,
									   entry->nmembers,
									   entry->members));

			/*
			 * Note we modify the list while not using a modifiable iterator.
			 * This is acceptable only because we exit the iteration
			 * immediately afterwards.
			 */
			dclist_move_head(&MXactCache, iter.cur);

			*members = ptr;
			return entry->nmembers;
		}
	}

	debug_elog2(DEBUG2, "CacheGet: not found");
	return -1;
}

/*
 * mXactCachePut
 *		Add a new MultiXactId and its composing set into the local cache.
 */
/*
 * 中文注释：
 * 把一个 MultiXactId 及其成员集合加入事务级缓存。
 *
 * 缓存项分配在 MXactContext（TopTransactionContext 的子上下文）中，事务结束自动
 * 释放。成员数组会先排序，以满足 mXactCacheGetBySet 的 memcmp 前提。新项插入链表
 * 头部；当缓存超过 MAX_CACHE_ENTRIES（256）时，从尾部淘汰最久未使用的项并 pfree。
 * 该上限防止一个长事务缓存无限增长。
 */
static void
mXactCachePut(MultiXactId multi, int nmembers, MultiXactMember *members)
{
	mXactCacheEnt *entry;

	debug_elog3(DEBUG2, "CachePut: storing %s",
				mxid_to_string(multi, nmembers, members));

	if (MXactContext == NULL)
	{
		/* The cache only lives as long as the current transaction */
		debug_elog2(DEBUG2, "CachePut: initializing memory context");
		MXactContext = AllocSetContextCreate(TopTransactionContext,
											 "MultiXact cache context",
											 ALLOCSET_SMALL_SIZES);
	}

	entry = (mXactCacheEnt *)
		MemoryContextAlloc(MXactContext,
						   offsetof(mXactCacheEnt, members) +
						   nmembers * sizeof(MultiXactMember));

	entry->multi = multi;
	entry->nmembers = nmembers;
	memcpy(entry->members, members, nmembers * sizeof(MultiXactMember));

	/* mXactCacheGetBySet assumes the entries are sorted, so sort them */
	qsort(entry->members, nmembers, sizeof(MultiXactMember), mxactMemberComparator);

	dclist_push_head(&MXactCache, &entry->node);
	if (dclist_count(&MXactCache) > MAX_CACHE_ENTRIES)
	{
		dlist_node *node;

		node = dclist_tail_node(&MXactCache);
		dclist_delete_from(&MXactCache, node);

		entry = dclist_container(mXactCacheEnt, node, node);
		debug_elog3(DEBUG2, "CachePut: pruning cached multi %u",
					entry->multi);

		pfree(entry);
	}
}

/*
 * 中文注释：
 * 把 MultiXactStatus 枚举转换成简短的调试字符串（如 keysh、sh、upd）。
 *
 * 仅用于 DEBUG 日志和错误信息，不参与持久化格式；未知状态直接 ERROR，帮助尽早
 * 发现枚举与实现不一致。
 */
char *
mxstatus_to_string(MultiXactStatus status)
{
	switch (status)
	{
		case MultiXactStatusForKeyShare:
			return "keysh";
		case MultiXactStatusForShare:
			return "sh";
		case MultiXactStatusForNoKeyUpdate:
			return "fornokeyupd";
		case MultiXactStatusForUpdate:
			return "forupd";
		case MultiXactStatusNoKeyUpdate:
			return "nokeyupd";
		case MultiXactStatusUpdate:
			return "upd";
		default:
			elog(ERROR, "unrecognized multixact status %d", status);
			return "";
	}
}

/*
 * 中文注释：
 * 把 MultiXactId 及其成员格式化成可读字符串，供 DEBUG 日志使用。
 *
 * 使用 TopMemoryContext 中的静态缓冲区保存结果：每次调用先释放上一次的字符串，
 * 再构建新字符串。因此返回值不能被长期保存，也不能在多次调用之间同时使用；它只
 * 适合立即传给 elog/ereport。格式为 "mid n[xid (status), ...]"。
 */
char *
mxid_to_string(MultiXactId multi, int nmembers, MultiXactMember *members)
{
	static char *str = NULL;
	StringInfoData buf;
	int			i;

	if (str != NULL)
		pfree(str);

	initStringInfo(&buf);

	appendStringInfo(&buf, "%u %d[%u (%s)", multi, nmembers, members[0].xid,
					 mxstatus_to_string(members[0].status));

	for (i = 1; i < nmembers; i++)
		appendStringInfo(&buf, ", %u (%s)", members[i].xid,
						 mxstatus_to_string(members[i].status));

	appendStringInfoChar(&buf, ']');
	str = MemoryContextStrdup(TopMemoryContext, buf.data);
	pfree(buf.data);
	return str;
}

/*
 * AtEOXact_MultiXact
 *		Handle transaction end for MultiXact
 *
 * This is called at top transaction commit or abort (we don't care which).
 */
/*
 * 中文注释：
 * 顶层事务提交或中止时的 MultiXact 清理。
 *
 * 清除本后端的 OldestMemberMXactId 和 OldestVisibleMXactId 槽位，使 vacuum 不再
 * 受本事务约束；这两个值只在事务内有效，且写入是原子的，因此无需加
 * MultiXactGenLock。随后丢弃事务级缓存：MXactContext 是 TopTransactionContext 的
 * 子上下文，会随事务上下文销毁，这里只需把指针置 NULL 并重新初始化链表。
 */
void
AtEOXact_MultiXact(void)
{
	/*
	 * Reset our OldestMemberMXactId and OldestVisibleMXactId values, both of
	 * which should only be valid while within a transaction.
	 *
	 * We assume that storing a MultiXactId is atomic and so we need not take
	 * MultiXactGenLock to do this.
	 */
	*MyOldestMemberMXactIdSlot() = InvalidMultiXactId;
	*MyOldestVisibleMXactIdSlot() = InvalidMultiXactId;

	/*
	 * Discard the local MultiXactId cache.  Since MXactContext was created as
	 * a child of TopTransactionContext, we needn't delete it explicitly.
	 */
	MXactContext = NULL;
	dclist_init(&MXactCache);
}

/*
 * AtPrepare_MultiXact
 *		Save multixact state at 2PC transaction prepare
 *
 * In this phase, we only store our OldestMemberMXactId value in the two-phase
 * state file.
 */
/*
 * 中文注释：
 * PREPARE TRANSACTION 阶段保存 MultiXact 相关状态。
 *
 * 若当前事务有有效的 OldestMemberMXactId，就通过 RegisterTwoPhaseRecord 把它写入
 * 两阶段状态文件（资源管理器 ID 为 TWOPHASE_RM_MULTIXACT_ID）。恢复/COMMIT
 * PREPARED 时需要这个下界，防止预备事务仍可能引用的 MultiXact 被截断。
 */
void
AtPrepare_MultiXact(void)
{
	MultiXactId myOldestMember = *MyOldestMemberMXactIdSlot();

	if (MultiXactIdIsValid(myOldestMember))
		RegisterTwoPhaseRecord(TWOPHASE_RM_MULTIXACT_ID, 0,
							   &myOldestMember, sizeof(MultiXactId));
}

/*
 * PostPrepare_MultiXact
 *		Clean up after successful PREPARE TRANSACTION
 */
/*
 * 中文注释：
 * PREPARE TRANSACTION 成功后的 MultiXact 清理与状态转移。
 *
 * 把当前后端的 OldestMemberMXactId 转移到该预备事务专用的槽位（由
 * TwoPhaseGetDummyProcNumber 得到虚拟 ProcNumber），然后清空普通后端槽位。虽然
 * 单个 MultiXactId 的存储是原子的，这里仍用排他锁保证其他进程不会只看到“普通槽位
 * 已清空、预备槽位尚未设置”的中间状态。OldestVisible 不需要转移，因为预备事务
 * 不会再检查 MultiXact；最后像事务结束一样丢弃本地缓存。
 */
void
PostPrepare_MultiXact(FullTransactionId fxid)
{
	MultiXactId myOldestMember;

	/*
	 * Transfer our OldestMemberMXactId value to the slot reserved for the
	 * prepared transaction.
	 */
	myOldestMember = *MyOldestMemberMXactIdSlot();
	if (MultiXactIdIsValid(myOldestMember))
	{
		ProcNumber	dummyProcNumber = TwoPhaseGetDummyProcNumber(fxid, false);

		/*
		 * Even though storing MultiXactId is atomic, acquire lock to make
		 * sure others see both changes, not just the reset of the slot of the
		 * current backend. Using a volatile pointer might suffice, but this
		 * isn't a hot spot.
		 */
		LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);

		*PreparedXactOldestMemberMXactIdSlot(dummyProcNumber) = myOldestMember;
		*MyOldestMemberMXactIdSlot() = InvalidMultiXactId;

		LWLockRelease(MultiXactGenLock);
	}

	/*
	 * We don't need to transfer OldestVisibleMXactId value, because the
	 * transaction is not going to be looking at any more multixacts once it's
	 * prepared.
	 *
	 * We assume that storing a MultiXactId is atomic and so we need not take
	 * MultiXactGenLock to do this.
	 */
	*MyOldestVisibleMXactIdSlot() = InvalidMultiXactId;

	/*
	 * Discard the local MultiXactId cache like in AtEOXact_MultiXact.
	 */
	MXactContext = NULL;
	dclist_init(&MXactCache);
}

/*
 * multixact_twophase_recover
 *		Recover the state of a prepared transaction at startup
 */
/*
 * 中文注释：
 * 崩溃恢复时重建一个预备事务的 MultiXact 状态。
 *
 * 两阶段状态文件中的记录只包含 OldestMemberMXactId。函数根据 FullTransactionId
 * 找到预备事务的虚拟 ProcNumber，把该值写入对应的 OldestMember 槽位，从而在恢复
 * 期间继续保护相关 MultiXact 不被截断。记录长度必须正好是一个 MultiXactId。
 */
void
multixact_twophase_recover(FullTransactionId fxid, uint16 info,
						   void *recdata, uint32 len)
{
	ProcNumber	dummyProcNumber = TwoPhaseGetDummyProcNumber(fxid, false);
	MultiXactId oldestMember;

	/*
	 * Get the oldest member XID from the state file record, and set it in the
	 * OldestMemberMXactId slot reserved for this prepared transaction.
	 */
	Assert(len == sizeof(MultiXactId));
	oldestMember = *((MultiXactId *) recdata);

	*PreparedXactOldestMemberMXactIdSlot(dummyProcNumber) = oldestMember;
}

/*
 * multixact_twophase_postcommit
 *		Similar to AtEOXact_MultiXact but for COMMIT PREPARED
 */
/*
 * 中文注释：
 * COMMIT PREPARED 完成后清除该预备事务的 OldestMember 槽位。
 *
 * 事务已经提交，不再可能成为新的 MultiXact 成员，因此释放这个保护下界。使用
 * TwoPhaseGetDummyProcNumber(fxid, true) 取得仍存在的虚拟 ProcNumber；记录内容
 * 只用于长度校验，实际不需要读取。
 */
void
multixact_twophase_postcommit(FullTransactionId fxid, uint16 info,
							  void *recdata, uint32 len)
{
	ProcNumber	dummyProcNumber = TwoPhaseGetDummyProcNumber(fxid, true);

	Assert(len == sizeof(MultiXactId));

	*PreparedXactOldestMemberMXactIdSlot(dummyProcNumber) = InvalidMultiXactId;
}

/*
 * multixact_twophase_postabort
 *		This is actually just the same as the COMMIT case.
 */
/*
 * 中文注释：
 * ROLLBACK PREPARED 后的清理，与 COMMIT PREPARED 完全相同：清除预备事务的
 * OldestMember 槽位。直接复用 multixact_twophase_postcommit 以避免两份逻辑漂移。
 */
void
multixact_twophase_postabort(FullTransactionId fxid, uint16 info,
							 void *recdata, uint32 len)
{
	multixact_twophase_postcommit(fxid, info, recdata, len);
}


/*
 * Register shared memory needs for MultiXact.
 */
/*
 * 中文注释：
 * 向共享内存框架登记 MultiXact 所需的共享状态和两个 SLRU。
 *
 * 共享状态是一块连续内存：MultiXactStateData 固定部分，后面紧跟
 * OldestMemberMXactId[NumMemberSlots] 和 OldestVisibleMXactId[NumVisibleSlots]
 * 两个柔性数组。两个 SLRU 分别是：
 *   - pg_multixact/offsets：每个 MultiXactId 的成员起始偏移，32 位段号命名；
 *   - pg_multixact/members：成员 XID 与状态位，64 位段号命名。
 * 这里还登记各自的 buffer 数量、同步处理器、页优先级回调和 I/O 错误详情回调。
 */
static void
MultiXactShmemRequest(void *arg)
{
	Size		size;

	/*
	 * Calculate the size of the MultiXactState struct, and the two
	 * per-backend MultiXactId arrays.  They are carved out of the same
	 * allocation.
	 */
	size = offsetof(MultiXactStateData, perBackendXactIds);
	size = add_size(size,
					mul_size(sizeof(MultiXactId), NumMemberSlots));
	size = add_size(size,
					mul_size(sizeof(MultiXactId), NumVisibleSlots));
	ShmemRequestStruct(.name = "Shared MultiXact State",
					   .size = size,
					   .ptr = (void **) &MultiXactState,
		);

	SimpleLruRequest(.desc = &MultiXactOffsetSlruDesc,
					 .name = "multixact_offset",
					 .Dir = "pg_multixact/offsets",
					 .long_segment_names = false,

					 .nslots = multixact_offset_buffers,

					 .sync_handler = SYNC_HANDLER_MULTIXACT_OFFSET,
					 .PagePrecedes = MultiXactOffsetPagePrecedes,
					 .errdetail_for_io_error = MultiXactOffsetIoErrorDetail,

					 .buffer_tranche_id = LWTRANCHE_MULTIXACTOFFSET_BUFFER,
					 .bank_tranche_id = LWTRANCHE_MULTIXACTOFFSET_SLRU,
		);

	SimpleLruRequest(.desc = &MultiXactMemberSlruDesc,
					 .name = "multixact_member",
					 .Dir = "pg_multixact/members",
					 .long_segment_names = true,

					 .nslots = multixact_member_buffers,

					 .sync_handler = SYNC_HANDLER_MULTIXACT_MEMBER,
					 .PagePrecedes = MultiXactMemberPagePrecedes,
					 .errdetail_for_io_error = MultiXactMemberIoErrorDetail,

					 .buffer_tranche_id = LWTRANCHE_MULTIXACTMEMBER_BUFFER,
					 .bank_tranche_id = LWTRANCHE_MULTIXACTMEMBER_SLRU,
		);
}

/*
 * 中文注释：
 * 初始化 MultiXact 的共享内存布局。
 *
 * 对 offsets SLRU 运行 PagePrecedes 单元测试，验证其 32 位回绕比较正确；members
 * SLRU 不使用 SimpleLruTruncate 的通用页优先级测试，因此跳过。随后把
 * OldestMemberMXactId 指向共享结构尾部，OldestVisibleMXactId 指向其后再偏移
 * NumMemberSlots 个元素的位置。该函数在 postmaster 初始化共享内存时调用一次。
 */
static void
MultiXactShmemInit(void *arg)
{
	SlruPagePrecedesUnitTests(MultiXactOffsetCtl, MULTIXACT_OFFSETS_PER_PAGE);

	/*
	 * members SLRU doesn't call SimpleLruTruncate() or meet criteria for unit
	 * tests
	 */

	/* Set up array pointers */
	OldestMemberMXactId = MultiXactState->perBackendXactIds;
	OldestVisibleMXactId = OldestMemberMXactId + NumMemberSlots;
}

/*
 * 中文注释：
 * 在 EXEC_BACKEND 等“重新挂接共享内存”的场景中恢复两个全局数组指针。
 *
 * MultiXactState 由 shmem 框架回填后，其后的柔性数组地址需要重新计算；
 * 逻辑与 MultiXactShmemInit 中的指针设置相同，但不重复做单元测试或初始化。
 */
static void
MultiXactShmemAttach(void *arg)
{
	/* Set up array pointers */
	OldestMemberMXactId = MultiXactState->perBackendXactIds;
	OldestVisibleMXactId = OldestMemberMXactId + NumMemberSlots;
}

/*
 * GUC check_hook for multixact_offset_buffers
 */
/*
 * 中文注释：
 * multixact_offset_buffers GUC 的 check_hook。
 *
 * 直接委托给通用的 check_slru_buffers，校验取值在允许范围内并与页面大小/共享内存
 * 限制兼容。具体 SLRU 不需要重复实现通用检查逻辑。
 */
bool
check_multixact_offset_buffers(int *newval, void **extra, GucSource source)
{
	return check_slru_buffers("multixact_offset_buffers", newval);
}

/*
 * GUC check_hook for multixact_member_buffers
 */
/*
 * 中文注释：
 * multixact_member_buffers GUC 的 check_hook，委托给 check_slru_buffers 做通用
 * SLRU buffer 数量校验。
 */
bool
check_multixact_member_buffers(int *newval, void **extra, GucSource source)
{
	return check_slru_buffers("multixact_member_buffers", newval);
}

/*
 * This func must be called ONCE on system install.  It creates the initial
 * MultiXact segments.  (The MultiXacts directories are assumed to have been
 * created by initdb, and MultiXactShmemInit must have been called already.)
 */
/*
 * 中文注释：
 * initdb 安装集簇时创建 MultiXact 的初始段文件。
 *
 * 对 offsets 和 members 两个 SLRU 的第 0 页执行“清零并写盘”，确保后续启动时
 * 文件存在且内容确定。目录本身由 initdb 预先创建；共享内存已由
 * MultiXactShmemInit 初始化。
 */
void
BootStrapMultiXact(void)
{
	/* Zero the initial pages and flush them to disk */
	SimpleLruZeroAndWritePage(MultiXactOffsetCtl, 0);
	SimpleLruZeroAndWritePage(MultiXactMemberCtl, 0);
}

/*
 * This must be called ONCE during postmaster or standalone-backend startup.
 *
 * StartupXLOG has already established nextMXact/nextOffset by calling
 * MultiXactSetNextMXact and/or MultiXactAdvanceNextMXact, and the oldestMulti
 * info from pg_control and/or MultiXactAdvanceOldest, but we haven't yet
 * replayed WAL.
 */
/*
 * 中文注释：
 * postmaster 或单用户模式启动时初始化 MultiXact SLRU 的“最新页”提示。
 *
 * StartupXLOG 已经通过检查点记录或 WAL 重放设置了 nextMXact/nextOffset，本函数
 * 据此计算 offsets 和 members 各自的最新页号并写入 SLRU 共享状态。latest_page_number
 * 用于淘汰时保护正在增长的页，避免把最新页当作 LRU 受害者。
 */
void
StartupMultiXact(void)
{
	MultiXactId multi = MultiXactState->nextMXact;
	MultiXactOffset offset = MultiXactState->nextOffset;
	int64		pageno;

	/*
	 * Initialize offset's idea of the latest page number.
	 */
	pageno = MultiXactIdToOffsetPage(multi);
	pg_atomic_write_u64(&MultiXactOffsetCtl->shared->latest_page_number,
						pageno);

	/*
	 * Initialize member's idea of the latest page number.
	 */
	pageno = MXOffsetToMemberPage(offset);
	pg_atomic_write_u64(&MultiXactMemberCtl->shared->latest_page_number,
						pageno);
}

/*
 * This must be called ONCE at the end of startup/recovery.
 */
/*
 * 中文注释：
 * 启动/恢复结束时对 MultiXact 做一次“修剪”，为正常运行建立一致边界。
 *
 * 主要工作：
 *   1. 读取 nextMXact/nextOffset/oldest 信息；
 *   2. 重设两个 SLRU 的 latest_page_number；
 *   3. 在 offsets 页中写入 nextMXact 的起始 offset，并把该位置之后的旧数据清零，
 *      防止 pg_resetwal 等场景留下过期的非零 offset；
 *   4. 对 members 当前页从当前 offset 到页尾清零，避免旧成员数据被误读；
 *   5. 置 finishedStartup = true，表示数据目录已一致；
 *   6. 调用 SetMultiXactIdLimit 重新计算回卷保护阈值和 oldestOffset。
 * 之所以要清零，是因为 MultiXact 不像 CLOG 那样严格遵循“先写 WAL 再写数据”，
 * 某些旧数据可能没有对应的 WAL 证据。
 */
void
TrimMultiXact(void)
{
	MultiXactId nextMXact;
	MultiXactOffset offset;
	MultiXactId oldestMXact;
	Oid			oldestMXactDB;
	int64		pageno;
	int			entryno;
	int			flagsoff;

	LWLockAcquire(MultiXactGenLock, LW_SHARED);
	nextMXact = MultiXactState->nextMXact;
	offset = MultiXactState->nextOffset;
	oldestMXact = MultiXactState->oldestMultiXactId;
	oldestMXactDB = MultiXactState->oldestMultiXactDB;
	LWLockRelease(MultiXactGenLock);

	/* Clean up offsets state */

	/*
	 * (Re-)Initialize our idea of the latest page number for offsets.
	 */
	pageno = MultiXactIdToOffsetPage(nextMXact);
	pg_atomic_write_u64(&MultiXactOffsetCtl->shared->latest_page_number,
						pageno);

	/*
	 * Set the offset of nextMXact on the offsets page.  This is normally done
	 * in RecordNewMultiXact() of the previous multixact, but let's be sure
	 * the next page exists, if the nextMXact was reset with pg_resetwal for
	 * example.
	 *
	 * Zero out the remainder of the page.  See notes in TrimCLOG() for
	 * background.  Unlike CLOG, some WAL record covers every pg_multixact
	 * SLRU mutation.  Since, also unlike CLOG, we ignore the WAL rule "write
	 * xlog before data," nextMXact successors may carry obsolete, nonzero
	 * offset values.
	 */
	entryno = MultiXactIdToOffsetEntry(nextMXact);
	{
		int			slotno;
		MultiXactOffset *offptr;
		LWLock	   *lock = SimpleLruGetBankLock(MultiXactOffsetCtl, pageno);

		LWLockAcquire(lock, LW_EXCLUSIVE);
		if (entryno == 0 || nextMXact == FirstMultiXactId)
			slotno = SimpleLruZeroPage(MultiXactOffsetCtl, pageno);
		else
			slotno = SimpleLruReadPage(MultiXactOffsetCtl, pageno, true, &nextMXact);
		offptr = (MultiXactOffset *) MultiXactOffsetCtl->shared->page_buffer[slotno];
		offptr += entryno;

		*offptr = offset;
		if (entryno != 0 && (entryno + 1) * sizeof(MultiXactOffset) != BLCKSZ)
			MemSet(offptr + 1, 0, BLCKSZ - (entryno + 1) * sizeof(MultiXactOffset));

		MultiXactOffsetCtl->shared->page_dirty[slotno] = true;
		LWLockRelease(lock);
	}

	/*
	 * And the same for members.
	 *
	 * (Re-)Initialize our idea of the latest page number for members.
	 */
	pageno = MXOffsetToMemberPage(offset);
	pg_atomic_write_u64(&MultiXactMemberCtl->shared->latest_page_number,
						pageno);

	/*
	 * Zero out the remainder of the current members page.  See notes in
	 * TrimCLOG() for motivation.
	 */
	flagsoff = MXOffsetToFlagsOffset(offset);
	if (flagsoff != 0)
	{
		MultiXactMemberSlruReadContext slru_read_context = {InvalidMultiXactId, offset};
		int			slotno;
		TransactionId *xidptr;
		int			memberoff;
		LWLock	   *lock = SimpleLruGetBankLock(MultiXactMemberCtl, pageno);

		LWLockAcquire(lock, LW_EXCLUSIVE);
		memberoff = MXOffsetToMemberOffset(offset);
		slotno = SimpleLruReadPage(MultiXactMemberCtl, pageno, true, &slru_read_context);
		xidptr = (TransactionId *)
			(MultiXactMemberCtl->shared->page_buffer[slotno] + memberoff);

		MemSet(xidptr, 0, BLCKSZ - memberoff);

		/*
		 * Note: we don't need to zero out the flag bits in the remaining
		 * members of the current group, because they are always reset before
		 * writing.
		 */

		MultiXactMemberCtl->shared->page_dirty[slotno] = true;
		LWLockRelease(lock);
	}

	/* signal that we're officially up */
	LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);
	MultiXactState->finishedStartup = true;
	LWLockRelease(MultiXactGenLock);

	/* Now compute how far away the next multixid wraparound is. */
	SetMultiXactIdLimit(oldestMXact, oldestMXactDB);
}

/*
 * Get the MultiXact data to save in a checkpoint record
 */
/*
 * 中文注释：
 * 读取写入检查点记录所需的 MultiXact 状态快照。
 *
 * 在共享锁下复制 nextMXact、nextOffset、oldestMultiXactId 和 oldestMultiXactDB，
 * 保证四个值来自同一一致状态。检查点恢复时用这些值重建计数器下界；is_shutdown
 * 参数目前仅用于区分调用场景，不改变取值。
 */
void
MultiXactGetCheckptMulti(bool is_shutdown,
						 MultiXactId *nextMulti,
						 MultiXactOffset *nextMultiOffset,
						 MultiXactId *oldestMulti,
						 Oid *oldestMultiDB)
{
	LWLockAcquire(MultiXactGenLock, LW_SHARED);
	*nextMulti = MultiXactState->nextMXact;
	*nextMultiOffset = MultiXactState->nextOffset;
	*oldestMulti = MultiXactState->oldestMultiXactId;
	*oldestMultiDB = MultiXactState->oldestMultiXactDB;
	LWLockRelease(MultiXactGenLock);

	debug_elog6(DEBUG2,
				"MultiXact: checkpoint is nextMulti %u, nextOffset %" PRIu64 ", oldestMulti %u in DB %u",
				*nextMulti, *nextMultiOffset, *oldestMulti, *oldestMultiDB);
}

/*
 * Perform a checkpoint --- either during shutdown, or on-the-fly
 */
/*
 * 中文注释：
 * 检查点或关闭时把两个 MultiXact SLRU 的所有脏页写回磁盘。
 *
 * 调用 SimpleLruWriteAll 分别处理 offsets 和 members；写回可能把 fsync 请求排入
 * checkpointer 的同步队列，由 ProcessSyncRequests 统一完成。允许页面在写回期间
 * 被重新弄脏（allow_redirtied=true），因为检查点不要求 MultiXact 页在那一刻完全
 * 干净，只要相关 WAL 已持久化即可。
 */
void
CheckPointMultiXact(void)
{
	TRACE_POSTGRESQL_MULTIXACT_CHECKPOINT_START(true);

	/*
	 * Write dirty MultiXact pages to disk.  This may result in sync requests
	 * queued for later handling by ProcessSyncRequests(), as part of the
	 * checkpoint.
	 */
	SimpleLruWriteAll(MultiXactOffsetCtl, true);
	SimpleLruWriteAll(MultiXactMemberCtl, true);

	TRACE_POSTGRESQL_MULTIXACT_CHECKPOINT_DONE(true);
}

/*
 * Set the next-to-be-assigned MultiXactId and offset
 *
 * This is used when we can determine the correct next ID/offset exactly
 * from a checkpoint record.  Although this is only called during bootstrap
 * and XLog replay, we take the lock in case any hot-standby backends are
 * examining the values.
 */
/*
 * 中文注释：
 * 根据检查点记录或 bootstrap 信息，精确设置 nextMXact 和 nextOffset。
 *
 * 与 MultiXactAdvanceNextMXact 的“只增不减”不同，本函数允许直接赋值，用于恢复
 * 到一个已知的精确起点。虽然主要在启动/重放中调用，仍获取排他锁，以防热备后端
 * 同时读取这些计数器。
 */
void
MultiXactSetNextMXact(MultiXactId nextMulti,
					  MultiXactOffset nextMultiOffset)
{
	Assert(MultiXactIdIsValid(nextMulti));
	debug_elog4(DEBUG2, "MultiXact: setting next multi to %u offset %" PRIu64,
				nextMulti, nextMultiOffset);

	LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);
	MultiXactState->nextMXact = nextMulti;
	MultiXactState->nextOffset = nextMultiOffset;
	LWLockRelease(MultiXactGenLock);
}

/*
 * Determine the last safe MultiXactId to allocate given the currently oldest
 * datminmxid (ie, the oldest MultiXactId that might exist in any database
 * of our cluster), and the OID of the (or a) database with that value.
 *
 * This also updates MultiXactState->oldestOffset, by looking up the offset of
 * MultiXactState->oldestMultiXactId.
 */
/*
 * 中文注释：
 * 根据全集群最老的 datminmxid 重新计算 MultiXact 回卷保护阈值。
 *
 * 以 oldest_datminmxid 为基准，把“回卷点”设为 ID 空间的一半处，然后计算：
 *   - multiVacLimit：超过后触发 autovacuum（oldest + autovacuum_multixact_freeze_max_age）；
 *   - multiWarnLimit：回卷点前 1 亿个 ID，开始 WARNING；
 *   - multiStopLimit：回卷点前 300 万个 ID，拒绝分配新 MultiXact；
 *   - multiWrapLimit：理论回卷点。
 * 更新共享状态后，如果已经完成启动（finishedStartup），还会计算 oldestOffset，
 * 并在超过 vac/warn 阈值时触发 autovacuum 或发出告警。告警需要数据库名，但本函数
 * 可能在非事务上下文中调用，因此只有在 IsTransactionState() 时才查系统表。
 */
void
SetMultiXactIdLimit(MultiXactId oldest_datminmxid, Oid oldest_datoid)
{
	MultiXactId multiVacLimit;
	MultiXactId multiWarnLimit;
	MultiXactId multiStopLimit;
	MultiXactId multiWrapLimit;
	MultiXactId curMulti;

	Assert(MultiXactIdIsValid(oldest_datminmxid));

	/*
	 * We pretend that a wrap will happen halfway through the multixact ID
	 * space, but that's not really true, because multixacts wrap differently
	 * from transaction IDs.
	 */
	multiWrapLimit = oldest_datminmxid + (MaxMultiXactId >> 1);
	if (multiWrapLimit < FirstMultiXactId)
		multiWrapLimit += FirstMultiXactId;

	/*
	 * We'll refuse to continue assigning MultiXactIds once we get within 3M
	 * multi of data loss.  See SetTransactionIdLimit.
	 */
	multiStopLimit = multiWrapLimit - 3000000;
	if (multiStopLimit < FirstMultiXactId)
		multiStopLimit -= FirstMultiXactId;

	/*
	 * We'll start complaining loudly when we get within 100M multis of data
	 * loss.  This is kind of arbitrary, but if you let your gas gauge get
	 * down to 5% of full, would you be looking for the next gas station?  We
	 * need to be fairly liberal about this number because there are lots of
	 * scenarios where most transactions are done by automatic clients that
	 * won't pay attention to warnings.  (No, we're not gonna make this
	 * configurable.  If you know enough to configure it, you know enough to
	 * not get in this kind of trouble in the first place.)
	 */
	multiWarnLimit = multiWrapLimit - 100000000;
	if (multiWarnLimit < FirstMultiXactId)
		multiWarnLimit -= FirstMultiXactId;

	/*
	 * We'll start trying to force autovacuums when oldest_datminmxid gets to
	 * be more than autovacuum_multixact_freeze_max_age mxids old.
	 *
	 * Note: autovacuum_multixact_freeze_max_age is a PGC_POSTMASTER parameter
	 * so that we don't have to worry about dealing with on-the-fly changes in
	 * its value.  See SetTransactionIdLimit.
	 */
	multiVacLimit = oldest_datminmxid + autovacuum_multixact_freeze_max_age;
	if (multiVacLimit < FirstMultiXactId)
		multiVacLimit += FirstMultiXactId;

	/* Grab lock for just long enough to set the new limit values */
	LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);
	MultiXactState->oldestMultiXactId = oldest_datminmxid;
	MultiXactState->oldestMultiXactDB = oldest_datoid;
	MultiXactState->multiVacLimit = multiVacLimit;
	MultiXactState->multiWarnLimit = multiWarnLimit;
	MultiXactState->multiStopLimit = multiStopLimit;
	MultiXactState->multiWrapLimit = multiWrapLimit;
	curMulti = MultiXactState->nextMXact;
	LWLockRelease(MultiXactGenLock);

	/* Log the info */
	ereport(DEBUG1,
			(errmsg_internal("MultiXactId wrap limit is %u, limited by database with OID %u",
							 multiWrapLimit, oldest_datoid)));

	/*
	 * Computing the actual limits is only possible once the data directory is
	 * in a consistent state. There's no need to compute the limits while
	 * still replaying WAL - no decisions about new multis are made even
	 * though multixact creations might be replayed. So we'll only do further
	 * checks after TrimMultiXact() has been called.
	 */
	if (!MultiXactState->finishedStartup)
		return;

	Assert(!InRecovery);

	/*
	 * Offsets are 64-bits wide and never wrap around, so we don't need to
	 * consider them for emergency autovacuum purposes.  But now that we're in
	 * a consistent state, determine MultiXactState->oldestOffset.  It will be
	 * used to adjust the freezing cutoff, to keep the offsets disk usage in
	 * check.
	 */
	SetOldestOffset();

	/*
	 * If past the autovacuum force point, immediately signal an autovac
	 * request.  The reason for this is that autovac only processes one
	 * database per invocation.  Once it's finished cleaning up the oldest
	 * database, it'll call here, and we'll signal the postmaster to start
	 * another iteration immediately if there are still any old databases.
	 */
	if (MultiXactIdPrecedes(multiVacLimit, curMulti) && IsUnderPostmaster)
		SendPostmasterSignal(PMSIGNAL_START_AUTOVAC_LAUNCHER);

	/* Give an immediate warning if past the wrap warn point */
	if (MultiXactIdPrecedes(multiWarnLimit, curMulti))
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
					(errmsg_plural("database \"%s\" must be vacuumed before %u more MultiXactId is used",
								   "database \"%s\" must be vacuumed before %u more MultiXactIds are used",
								   multiWrapLimit - curMulti,
								   oldest_datname,
								   multiWrapLimit - curMulti),
					 errdetail("Approximately %.2f%% of MultiXactId space remains before wraparound.",
							   (double) (multiWrapLimit - curMulti) / (MaxMultiXactId / 2) * 100),
					 errhint("To avoid MultiXactId assignment failures, execute a database-wide VACUUM in that database.\n"
							 "You might also need to commit or roll back old prepared transactions.")));
		else
			ereport(WARNING,
					(errmsg_plural("database with OID %u must be vacuumed before %u more MultiXactId is used",
								   "database with OID %u must be vacuumed before %u more MultiXactIds are used",
								   multiWrapLimit - curMulti,
								   oldest_datoid,
								   multiWrapLimit - curMulti),
					 errdetail("Approximately %.2f%% of MultiXactId space remains before wraparound.",
							   (double) (multiWrapLimit - curMulti) / (MaxMultiXactId / 2) * 100),
					 errhint("To avoid MultiXactId assignment failures, execute a database-wide VACUUM in that database.\n"
							 "You might also need to commit or roll back old prepared transactions.")));
	}
}

/*
 * Ensure the next-to-be-assigned MultiXactId is at least minMulti,
 * and similarly nextOffset is at least minMultiOffset.
 *
 * This is used when we can determine minimum safe values from an XLog
 * record (either an on-line checkpoint or an mxact creation log entry).
 * Although this is only called during XLog replay, we take the lock in case
 * any hot-standby backends are examining the values.
 */
/*
 * 中文注释：
 * 在 WAL 重放中把 nextMXact/nextOffset 单调推进到至少给定值。
 *
 * 重放可能乱序或重复看到创建记录，因此不能直接赋值，只能取较大值；比较
 * MultiXactId 时必须用 MultiXactIdPrecedes 处理回绕。持有排他锁是因为热备后端
 * 可能同时读取这些计数器。
 */
void
MultiXactAdvanceNextMXact(MultiXactId minMulti,
						  MultiXactOffset minMultiOffset)
{
	Assert(MultiXactIdIsValid(minMulti));

	LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);
	if (MultiXactIdPrecedes(MultiXactState->nextMXact, minMulti))
	{
		debug_elog3(DEBUG2, "MultiXact: setting next multi to %u", minMulti);
		MultiXactState->nextMXact = minMulti;
	}
	if (MultiXactState->nextOffset < minMultiOffset)
	{
		debug_elog3(DEBUG2, "MultiXact: setting next offset to %" PRIu64,
					minMultiOffset);
		MultiXactState->nextOffset = minMultiOffset;
	}
	LWLockRelease(MultiXactGenLock);
}

/*
 * Update our oldestMultiXactId value, but only if it's more recent than what
 * we had.
 *
 * This may only be called during WAL replay.
 */
/*
 * 中文注释：
 * WAL 重放期间推进 oldestMultiXactId。
 *
 * 只有当重放记录中的 oldestMulti 比当前值更新时才调用 SetMultiXactIdLimit，
 * 从而更新回卷阈值和 oldestOffset。该函数只允许在恢复期间调用（Assert(InRecovery)）。
 */
void
MultiXactAdvanceOldest(MultiXactId oldestMulti, Oid oldestMultiDB)
{
	Assert(InRecovery);

	if (MultiXactIdPrecedes(MultiXactState->oldestMultiXactId, oldestMulti))
		SetMultiXactIdLimit(oldestMulti, oldestMultiDB);
}

/*
 * Make sure that MultiXactOffset has room for a newly-allocated MultiXactId.
 *
 * NB: this is called while holding MultiXactGenLock.  We want it to be very
 * fast most of the time; even when it's not so fast, no actual I/O need
 * happen unless we're forced to write out a dirty log or xlog page to make
 * room in shared memory.
 */
/*
 * 中文注释：
 * 确保 offsets SLRU 有空间容纳新分配的 MultiXactId。
 *
 * 只有当新 ID 是某个 offsets 页的第一个条目（或回绕后的 FirstMultiXactId）时才
 * 需要动作：在对应 bank 锁下清零该页，并写一条
 * XLOG_MULTIXACT_ZERO_OFF_PAGE WAL 记录，告诉恢复端“这页被重新初始化”。
 * 调用者持有 MultiXactGenLock，因此多个后端不会并发扩展同一个计数器；但 SLRU
 * 页本身仍需自己的 bank 锁。大多数调用会在第一条判断处快速返回。
 */
static void
ExtendMultiXactOffset(MultiXactId multi)
{
	int64		pageno;
	LWLock	   *lock;

	/*
	 * No work except at first MultiXactId of a page.  But beware: just after
	 * wraparound, the first MultiXactId of page zero is FirstMultiXactId.
	 */
	if (MultiXactIdToOffsetEntry(multi) != 0 &&
		multi != FirstMultiXactId)
		return;

	pageno = MultiXactIdToOffsetPage(multi);
	lock = SimpleLruGetBankLock(MultiXactOffsetCtl, pageno);

	LWLockAcquire(lock, LW_EXCLUSIVE);

	/* Zero the page and make a WAL entry about it */
	SimpleLruZeroPage(MultiXactOffsetCtl, pageno);
	XLogSimpleInsertInt64(RM_MULTIXACT_ID, XLOG_MULTIXACT_ZERO_OFF_PAGE,
						  pageno);

	LWLockRelease(lock);
}

/*
 * Make sure that MultiXactMember has room for the members of a newly-
 * allocated MultiXactId.
 *
 * Like the above routine, this is called while holding MultiXactGenLock;
 * same comments apply.
 */
/*
 * 中文注释：
 * 确保 members SLRU 有足够空间容纳新 MultiXact 的 nmembers 个成员。
 *
 * 成员可能跨多个页，因此循环处理：每当 offset 位于某页的第一个条目（flags 偏移和
 * 位偏移都为 0）时，在对应 bank 锁下清零该页并写
 * XLOG_MULTIXACT_ZERO_MEM_PAGE WAL 记录；然后计算当前页剩余槽位，推进 offset 并
 * 减少 nmembers。调用者持有 MultiXactGenLock；与 offsets 扩展一样，正常路径只在
 * 跨页时产生工作。
 */
static void
ExtendMultiXactMember(MultiXactOffset offset, int nmembers)
{
	/*
	 * It's possible that the members span more than one page of the members
	 * file, so we loop to ensure we consider each page.  The coding is not
	 * optimal if the members span several pages, but that seems unusual
	 * enough to not worry much about.
	 */
	while (nmembers > 0)
	{
		int			flagsoff;
		int			flagsbit;
		uint32		difference;

		/*
		 * Only zero when at first entry of a page.
		 */
		flagsoff = MXOffsetToFlagsOffset(offset);
		flagsbit = MXOffsetToFlagsBitShift(offset);
		if (flagsoff == 0 && flagsbit == 0)
		{
			int64		pageno;
			LWLock	   *lock;

			pageno = MXOffsetToMemberPage(offset);
			lock = SimpleLruGetBankLock(MultiXactMemberCtl, pageno);

			LWLockAcquire(lock, LW_EXCLUSIVE);

			/* Zero the page and make a WAL entry about it */
			SimpleLruZeroPage(MultiXactMemberCtl, pageno);
			XLogSimpleInsertInt64(RM_MULTIXACT_ID,
								  XLOG_MULTIXACT_ZERO_MEM_PAGE, pageno);

			LWLockRelease(lock);
		}

		/* Compute the number of items till end of current page. */
		difference = MULTIXACT_MEMBERS_PER_PAGE - offset % MULTIXACT_MEMBERS_PER_PAGE;

		/*
		 * Advance to next page.  OK if nmembers goes negative.
		 */
		nmembers -= difference;
		offset += difference;
	}
}

/*
 * GetOldestMultiXactId
 *
 * Return the oldest MultiXactId that's still possibly still seen as live by
 * any running transaction.  Older ones might still exist on disk, but they no
 * longer have any running member transaction.
 *
 * It's not safe to truncate MultiXact SLRU segments on the value returned by
 * this function; however, it can be set as the new relminmxid for any table
 * that VACUUM knows has no remaining MXIDs < the same value.  It is only safe
 * to truncate SLRUs when no table can possibly still have a referencing MXID.
 */
/*
 * 中文注释：
 * 返回所有活跃事务仍可能看到的最老 MultiXactId。
 *
 * 取 nextMXact 与所有 OldestMemberMXactId、OldestVisibleMXactId 槽位中的最小值。
 * 该值适合作为表的 relminmxid 下界（VACUUM 可据此判断元组中的 MultiXact 是否已
 * 死亡），但不能直接作为 SLRU 截断点：截断还要求没有任何表可能引用更老的
 * MultiXact，通常由 pg_class.relminmxid -> pg_database.datminmxid -> pg_control
 * 的全局最小值决定。
 */
MultiXactId
GetOldestMultiXactId(void)
{
	MultiXactId oldestMXact;

	/*
	 * This is the oldest valid value among all the OldestMemberMXactId[] and
	 * OldestVisibleMXactId[] entries, or nextMXact if none are valid.
	 */
	LWLockAcquire(MultiXactGenLock, LW_SHARED);
	oldestMXact = MultiXactState->nextMXact;
	for (int i = 0; i < NumMemberSlots; i++)
	{
		MultiXactId thisoldest;

		thisoldest = OldestMemberMXactId[i];
		if (MultiXactIdIsValid(thisoldest) &&
			MultiXactIdPrecedes(thisoldest, oldestMXact))
			oldestMXact = thisoldest;
	}
	for (int i = 0; i < NumVisibleSlots; i++)
	{
		MultiXactId thisoldest;

		thisoldest = OldestVisibleMXactId[i];
		if (MultiXactIdIsValid(thisoldest) &&
			MultiXactIdPrecedes(thisoldest, oldestMXact))
			oldestMXact = thisoldest;
	}

	LWLockRelease(MultiXactGenLock);

	return oldestMXact;
}

/*
 * Calculate the oldest member offset and install it in MultiXactState, where
 * it can be used to adjust multixid freezing cutoffs.
 */
/*
 * 中文注释：
 * 计算并安装“最老仍可能被引用的成员偏移”（oldestOffset）。
 *
 * oldestOffset 用于限制 members SLRU 的磁盘占用：即使 MultiXactId 数量还不多，
 * 若每个 MultiXact 成员很多，也可能积累大量成员数据。
 *
 * 计算时需要防止并发截断，因此先拿 MultiXactTruncationLock 共享锁；然后读取
 * oldestMultiXactId/nextMXact/nextOffset。若 oldest == next，说明当前没有任何
 * MultiXact，下一个创建将使用 nextOffset；否则调用 find_multixact_start 查其起始
 * 偏移。若查不到（历史 bug 或数据不一致），保持旧值并禁用成员截断，避免误删。
 * 最后在排他锁下更新 MultiXactState->oldestOffset。
 */
static void
SetOldestOffset(void)
{
	MultiXactId oldestMultiXactId;
	MultiXactId nextMXact;
	MultiXactOffset oldestOffset = 0;	/* placate compiler */
	MultiXactOffset nextOffset;
	bool		oldestOffsetKnown = false;

	/*
	 * NB: Have to prevent concurrent truncation, we might otherwise try to
	 * lookup an oldestMulti that's concurrently getting truncated away.
	 */
	LWLockAcquire(MultiXactTruncationLock, LW_SHARED);

	/* Read relevant fields from shared memory. */
	LWLockAcquire(MultiXactGenLock, LW_SHARED);
	oldestMultiXactId = MultiXactState->oldestMultiXactId;
	nextMXact = MultiXactState->nextMXact;
	nextOffset = MultiXactState->nextOffset;
	Assert(MultiXactState->finishedStartup);
	LWLockRelease(MultiXactGenLock);

	/*
	 * Determine the offset of the oldest multixact.  Normally, we can read
	 * the offset from the multixact itself, but there's an important special
	 * case: if there are no multixacts in existence at all, oldestMXact
	 * obviously can't point to one.  It will instead point to the multixact
	 * ID that will be assigned the next time one is needed.
	 */
	if (oldestMultiXactId == nextMXact)
	{
		/*
		 * When the next multixact gets created, it will be stored at the next
		 * offset.
		 */
		oldestOffset = nextOffset;
		oldestOffsetKnown = true;
	}
	else
	{
		/*
		 * Look up the offset at which the oldest existing multixact's members
		 * are stored.  If we cannot find it, be careful not to fail, and
		 * leave oldestOffset unchanged.  oldestOffset is initialized to zero
		 * at system startup, which prevents truncating members until a proper
		 * value is calculated.
		 *
		 * (We had bugs in early releases of PostgreSQL 9.3.X and 9.4.X where
		 * the supposedly-earliest multixact might not really exist.  Those
		 * should be long gone by now, so this should not fail, but let's
		 * still be defensive.)
		 */
		oldestOffsetKnown =
			find_multixact_start(oldestMultiXactId, &oldestOffset);

		if (oldestOffsetKnown)
			ereport(DEBUG1,
					(errmsg_internal("oldest MultiXactId member is at offset %" PRIu64,
									 oldestOffset)));
		else
			ereport(LOG,
					(errmsg("MultiXact member truncation is disabled because oldest checkpointed MultiXact %u does not exist on disk",
							oldestMultiXactId)));
	}

	LWLockRelease(MultiXactTruncationLock);

	/* Install the computed value */
	if (oldestOffsetKnown)
	{
		LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);
		MultiXactState->oldestOffset = oldestOffset;
		LWLockRelease(MultiXactGenLock);
	}
}

/*
 * Find the starting offset of the given MultiXactId.
 *
 * Returns false if the file containing the multi does not exist on disk.
 * Otherwise, returns true and sets *result to the starting member offset.
 *
 * This function does not prevent concurrent truncation, so if that's
 * required, the caller has to protect against that.
 */
/*
 * 中文注释：
 * 查找指定 MultiXactId 的成员起始偏移。
 *
 * 先把两个 SLRU 的脏页写回，确保 SimpleLruDoesPhysicalPageExist 能看到真实文件
 * 状态；若 offsets 页不存在则返回 false。然后用只读方式读取对应 offset 页并取出
 * 条目。函数本身不防止并发截断，调用者若需要保护必须自己持有
 * MultiXactTruncationLock。
 */
static bool
find_multixact_start(MultiXactId multi, MultiXactOffset *result)
{
	MultiXactOffset offset;
	int64		pageno;
	int			entryno;
	int			slotno;
	MultiXactOffset *offptr;

	Assert(MultiXactState->finishedStartup);

	pageno = MultiXactIdToOffsetPage(multi);
	entryno = MultiXactIdToOffsetEntry(multi);

	/*
	 * Write out dirty data, so PhysicalPageExists can work correctly.
	 */
	SimpleLruWriteAll(MultiXactOffsetCtl, true);
	SimpleLruWriteAll(MultiXactMemberCtl, true);

	if (!SimpleLruDoesPhysicalPageExist(MultiXactOffsetCtl, pageno))
		return false;

	/* lock is acquired by SimpleLruReadPage_ReadOnly */
	slotno = SimpleLruReadPage_ReadOnly(MultiXactOffsetCtl, pageno, &multi);
	offptr = (MultiXactOffset *) MultiXactOffsetCtl->shared->page_buffer[slotno];
	offptr += entryno;
	offset = *offptr;
	LWLockRelease(SimpleLruGetBankLock(MultiXactOffsetCtl, pageno));

	*result = offset;
	return true;
}

/*
 * GetMultiXactInfo
 *
 * Returns information about the current MultiXact state, as of:
 * multixacts: Number of MultiXacts (nextMultiXactId - oldestMultiXactId)
 * nextOffset: Next-to-be-assigned offset
 * oldestMultiXactId: Oldest MultiXact ID still in use
 * oldestOffset: Oldest offset still in use
 */
/*
 * 中文注释：
 * 一次性读取 MultiXact 的统计信息：存活 MultiXact 数量、下一个 offset、最老
 * MultiXactId 和最老 offset。
 *
 * 在 MultiXactGenLock 共享锁下复制字段，保证一致性；multixacts 由 nextMXact 减去
 * oldestMultiXactId 得到，按 32 位无符号差值计算。该接口供 SQL 统计函数和
 * MultiXactMemberFreezeThreshold 使用。
 */
void
GetMultiXactInfo(uint32 *multixacts, MultiXactOffset *nextOffset,
				 MultiXactId *oldestMultiXactId, MultiXactOffset *oldestOffset)
{
	MultiXactId nextMultiXactId;

	LWLockAcquire(MultiXactGenLock, LW_SHARED);
	*nextOffset = MultiXactState->nextOffset;
	*oldestMultiXactId = MultiXactState->oldestMultiXactId;
	nextMultiXactId = MultiXactState->nextMXact;
	*oldestOffset = MultiXactState->oldestOffset;
	LWLockRelease(MultiXactGenLock);

	*multixacts = nextMultiXactId - *oldestMultiXactId;
}

/*
 * Multixact members can be removed once the multixacts that refer to them
 * are older than every datminmxid.  autovacuum_multixact_freeze_max_age and
 * vacuum_multixact_freeze_table_age work together to make sure we never have
 * too many multixacts; we hope that, at least under normal circumstances,
 * this will also be sufficient to keep us from using too many offsets.
 * However, if the average multixact has many members, we might accumulate a
 * large amount of members, consuming disk space, while still using few enough
 * multixids that the multixid limits fail to trigger relminmxid advancement
 * by VACUUM.
 *
 * To prevent that, if the members space usage exceeds a threshold
 * (MULTIXACT_MEMBER_LOW_THRESHOLD), we effectively reduce
 * autovacuum_multixact_freeze_max_age to a value just less than the number of
 * multixacts in use.  We hope that this will quickly trigger autovacuuming on
 * the table or tables with the oldest relminmxid, thus allowing datminmxid
 * values to advance and removing some members.
 *
 * As the amount of the member space in use grows, we become more aggressive
 * in clamping this value.  That not only causes autovacuum to ramp up, but
 * also makes any manual vacuums the user issues more aggressive.  This
 * happens because vacuum_get_cutoffs() will clamp the freeze table and the
 * minimum freeze age cutoffs based on the effective
 * autovacuum_multixact_freeze_max_age this function returns.  At the extreme,
 * when the members usage reaches MULTIXACT_MEMBER_HIGH_THRESHOLD, we clamp
 * freeze_max_age to zero, and every vacuum of any table will freeze every
 * multixact.
 */
/*
 * 中文注释：
 * 根据 members 空间使用量动态调整“多激进地冻结 MultiXact”。
 *
 * 正常情况下返回 autovacuum_multixact_freeze_max_age。当已用成员空间超过
 * MULTIXACT_MEMBER_LOW_THRESHOLD 后，按线性比例降低有效 freeze age：空间越接近
 * HIGH_THRESHOLD，返回值越接近 0；超过 HIGH 后直接返回 0，使每次 VACUUM 都尽量
 * 冻结所有 MultiXact。这样即使 MultiXact 数量不多，只要单个 MultiXact 成员很多，
 * 也能通过更积极的 vacuum 推进 relminmxid、释放成员空间，避免磁盘无限增长。
 * 返回值不会大于配置的 autovacuum_multixact_freeze_max_age。
 */
int
MultiXactMemberFreezeThreshold(void)
{
	uint32		multixacts;
	uint32		victim_multixacts;
	double		fraction;
	int			result;
	MultiXactId oldestMultiXactId;
	MultiXactOffset oldestOffset;
	MultiXactOffset nextOffset;
	uint64		members;

	/* Read the current offsets and multixact usage. */
	GetMultiXactInfo(&multixacts, &nextOffset, &oldestMultiXactId, &oldestOffset);
	members = nextOffset - oldestOffset;

	/* If member space utilization is low, no special action is required. */
	if (members <= MULTIXACT_MEMBER_LOW_THRESHOLD)
		return autovacuum_multixact_freeze_max_age;

	/*
	 * Compute a target for relminmxid advancement.  The number of multixacts
	 * we try to eliminate from the system is based on how far we are past
	 * MULTIXACT_MEMBER_LOW_THRESHOLD.
	 *
	 * The way this formula works is that when members is exactly at the low
	 * threshold, fraction = 0.0, and we set freeze_max_age equal to
	 * mxid_age(oldestMultiXactId).  As members grows further, towards the
	 * high threshold, fraction grows linearly from 0.0 to 1.0, and the result
	 * shrinks from mxid_age(oldestMultiXactId) to 0.  Beyond the high
	 * threshold, fraction > 1.0 and the result is clamped to 0.
	 */
	fraction = (double) (members - MULTIXACT_MEMBER_LOW_THRESHOLD) /
		(MULTIXACT_MEMBER_HIGH_THRESHOLD - MULTIXACT_MEMBER_LOW_THRESHOLD);

	/* fraction could be > 1.0, but lowest possible freeze age is zero */
	if (fraction >= 1.0)
		return 0;

	victim_multixacts = multixacts * fraction;
	result = multixacts - victim_multixacts;

	/*
	 * Clamp to autovacuum_multixact_freeze_max_age, so that we never make
	 * autovacuum less aggressive than it would otherwise be.
	 */
	return Min(result, autovacuum_multixact_freeze_max_age);
}


/*
 * Delete members segments older than newOldestOffset
 */
/*
 * 中文注释：
 * 删除 members SLRU 中 newOldestOffset 之前的段。
 *
 * 把成员偏移换算成 members 页号，再交给通用的 SimpleLruTruncate。调用者必须已经
 * 持有 MultiXactTruncationLock，并确保没有事务仍需要这些成员。
 */
static void
PerformMembersTruncation(MultiXactOffset newOldestOffset)
{
	SimpleLruTruncate(MultiXactMemberCtl,
					  MXOffsetToMemberPage(newOldestOffset));
}

/*
 * Delete offsets segments older than newOldestMulti
 */
/*
 * 中文注释：
 * 删除 offsets SLRU 中 newOldestMulti 之前的段。
 *
 * 这里先取 PreviousMultiXactId 再换算页号：若 oldestMulti 恰好是某页第一项且等于
 * nextMulti，直接用它做 cutoff 可能触发 SimpleLruTruncate 的“回绕”安全检查，
 * 导致截断被拒绝；回退一个 ID 可以避免这个边界问题。
 */
static void
PerformOffsetsTruncation(MultiXactId newOldestMulti)
{
	/*
	 * We step back one multixact to avoid passing a cutoff page that hasn't
	 * been created yet in the rare case that oldestMulti would be the first
	 * item on a page and oldestMulti == nextMulti.  In that case, if we
	 * didn't subtract one, we'd trigger SimpleLruTruncate's wraparound
	 * detection.
	 */
	SimpleLruTruncate(MultiXactOffsetCtl,
					  MultiXactIdToOffsetPage(PreviousMultiXactId(newOldestMulti)));
}

/*
 * Remove all MultiXactOffset and MultiXactMember segments before the oldest
 * ones still of interest.
 *
 * This is only called on a primary as part of vacuum (via
 * vac_truncate_clog()). During recovery truncation is done by replaying
 * truncation WAL records logged here.
 *
 * newOldestMulti is the oldest currently required multixact, newOldestMultiDB
 * is one of the databases preventing newOldestMulti from increasing.
 */
/*
 * 中文注释：
 * 按 VACUUM 计算出的新下界截断 MultiXact 的 offsets 和 members SLRU。
 *
 * 只在主库调用；备库通过重放这里写的 XLOG_MULTIXACT_TRUNCATE_ID 记录完成截断。
 *
 * 流程：
 *   1. 获取 MultiXactTruncationLock 排他锁，保证同一时刻只有一个截断；
 *   2. 读取 next/oldest 状态，如果新下界没有前进则直接返回；
 *   3. 计算 newOldestOffset：若没有 MultiXact 则用 nextOffset，否则查
 *      newOldestMulti 的起始偏移；查不到或偏移为 0 时记录 LOG 并跳过，等待下次；
 *   4. 进入临界区，设置 DELAY_CHKPT_START 阻止检查点并发，写并 flush
 *      XLOG_MULTIXACT_TRUNCATE_ID（必须在删除文件前持久化）；
 *   5. 更新共享 oldestMulti/oldestOffset（必须在截断前，防止并发查询访问已删数据）；
 *   6. 先截断 members，再截断 offsets；最后清除 delay 标志、结束临界区、释放锁。
 * 先写 WAL、再更新内存、最后删除文件，保证崩溃后重放能恢复一致的截断状态。
 */
void
TruncateMultiXact(MultiXactId newOldestMulti, Oid newOldestMultiDB)
{
	MultiXactId oldestMulti;
	MultiXactId nextMulti;
	MultiXactOffset newOldestOffset;
	MultiXactOffset nextOffset;

	Assert(!RecoveryInProgress());
	Assert(MultiXactState->finishedStartup);
	Assert(MultiXactIdIsValid(newOldestMulti));

	/*
	 * We can only allow one truncation to happen at once. Otherwise parts of
	 * members might vanish while we're doing lookups or similar. There's no
	 * need to have an interlock with creating new multis or such, since those
	 * are constrained by the limits (which only grow, never shrink).
	 */
	LWLockAcquire(MultiXactTruncationLock, LW_EXCLUSIVE);

	LWLockAcquire(MultiXactGenLock, LW_SHARED);
	nextMulti = MultiXactState->nextMXact;
	nextOffset = MultiXactState->nextOffset;
	oldestMulti = MultiXactState->oldestMultiXactId;
	LWLockRelease(MultiXactGenLock);

	/*
	 * Make sure to only attempt truncation if there's values to truncate
	 * away. In normal processing values shouldn't go backwards, but there's
	 * some corner cases (due to bugs) where that's possible.
	 */
	if (MultiXactIdPrecedesOrEquals(newOldestMulti, oldestMulti))
	{
		LWLockRelease(MultiXactTruncationLock);
		return;
	}

	/*
	 * Compute up to where to truncate MultiXactMember. Lookup the
	 * corresponding member offset for newOldestMulti for that.
	 */
	if (newOldestMulti == nextMulti)
	{
		/* there are NO MultiXacts */
		newOldestOffset = nextOffset;
	}
	else if (!find_multixact_start(newOldestMulti, &newOldestOffset))
	{
		ereport(LOG,
				(errmsg("cannot truncate up to MultiXact %u because it does not exist on disk, skipping truncation",
						newOldestMulti)));
		LWLockRelease(MultiXactTruncationLock);
		return;
	}

	/*
	 * On crash, MultiXactIdCreateFromMembers() can leave behind multixids
	 * that were not yet written out and hence have zero offset on disk. If
	 * such a multixid becomes oldestMulti, we won't be able to look up its
	 * offset. That should be rare, so we don't try to do anything smart about
	 * it. Just skip the truncation, and hope that by the next truncation
	 * attempt, oldestMulti has advanced to a valid multixid.
	 */
	if (newOldestOffset == 0)
	{
		ereport(LOG,
				(errmsg("cannot truncate up to MultiXact %u because it has invalid offset, skipping truncation",
						newOldestMulti)));
		LWLockRelease(MultiXactTruncationLock);
		return;
	}

	elog(DEBUG1, "performing multixact truncation: "
		 "oldestMulti %u (offsets segment %" PRIx64 "), "
		 "oldestOffset %" PRIu64 " (members segment %" PRIx64 ")",
		 newOldestMulti,
		 MultiXactIdToOffsetSegment(newOldestMulti),
		 newOldestOffset,
		 MXOffsetToMemberSegment(newOldestOffset));

	/*
	 * Do truncation, and the WAL logging of the truncation, in a critical
	 * section. That way offsets/members cannot get out of sync anymore, i.e.
	 * once consistent the newOldestMulti will always exist in members, even
	 * if we crashed in the wrong moment.
	 */
	START_CRIT_SECTION();

	/*
	 * Prevent checkpoints from being scheduled concurrently. This is critical
	 * because otherwise a truncation record might not be replayed after a
	 * crash/basebackup, even though the state of the data directory would
	 * require it.
	 */
	Assert((MyProc->delayChkptFlags & DELAY_CHKPT_START) == 0);
	MyProc->delayChkptFlags |= DELAY_CHKPT_START;

	/* WAL log truncation */
	WriteMTruncateXlogRec(newOldestMultiDB, newOldestMulti, newOldestOffset);

	/*
	 * Update in-memory limits before performing the truncation, while inside
	 * the critical section: Have to do it before truncation, to prevent
	 * concurrent lookups of those values. Has to be inside the critical
	 * section as otherwise a future call to this function would error out,
	 * while looking up the oldest member in offsets, if our caller crashes
	 * before updating the limits.
	 */
	LWLockAcquire(MultiXactGenLock, LW_EXCLUSIVE);
	MultiXactState->oldestMultiXactId = newOldestMulti;
	MultiXactState->oldestMultiXactDB = newOldestMultiDB;
	MultiXactState->oldestOffset = newOldestOffset;
	LWLockRelease(MultiXactGenLock);

	/* First truncate members */
	PerformMembersTruncation(newOldestOffset);

	/* Then offsets */
	PerformOffsetsTruncation(newOldestMulti);

	MyProc->delayChkptFlags &= ~DELAY_CHKPT_START;

	END_CRIT_SECTION();
	LWLockRelease(MultiXactTruncationLock);
}

/*
 * Decide whether a MultiXactOffset page number is "older" for truncation
 * purposes.  Analogous to CLOGPagePrecedes().
 *
 * Offsetting the values is optional, because MultiXactIdPrecedes() has
 * translational symmetry.
 */
/*
 * 中文注释：
 * offsets SLRU 的页优先级回调：判断 page1 是否在 page2 之前（考虑 32 位回绕）。
 *
 * 页号乘以每页条目数换算成 MultiXactId 区间，加上 FirstMultiXactId+1 的偏移后，
 * 用 MultiXactIdPrecedes 比较区间起点；同时要求 page1 的起点也先于 page2 区间的
 * 最后一个 ID，以避免两个页在回绕点附近部分重叠时误判。SimpleLruTruncate 用它
 * 决定哪些段可以删除。
 */
static bool
MultiXactOffsetPagePrecedes(int64 page1, int64 page2)
{
	MultiXactId multi1;
	MultiXactId multi2;

	multi1 = ((MultiXactId) page1) * MULTIXACT_OFFSETS_PER_PAGE;
	multi1 += FirstMultiXactId + 1;
	multi2 = ((MultiXactId) page2) * MULTIXACT_OFFSETS_PER_PAGE;
	multi2 += FirstMultiXactId + 1;

	return (MultiXactIdPrecedes(multi1, multi2) &&
			MultiXactIdPrecedes(multi1,
								multi2 + MULTIXACT_OFFSETS_PER_PAGE - 1));
}

/*
 * Decide whether a MultiXactMember page number is "older" for truncation
 * purposes.  There is no "invalid offset number" and members never wrap
 * around, so use the numbers verbatim.
 */
/*
 * 中文注释：
 * members SLRU 的页优先级回调。成员偏移是 64 位且从不回绕，因此直接按页号数值
 * 比较即可，不需要 MultiXactId 的回绕逻辑。
 */
static bool
MultiXactMemberPagePrecedes(int64 page1, int64 page2)
{
	return page1 < page2;
}

/*
 * 中文注释：
 * offsets SLRU 的 I/O 错误详情回调。
 *
 * opaque_data 指向出错时正在访问的 MultiXactId；返回 errdetail，告诉用户无法访问
 * 哪个 MultiXact 的偏移。该回调由 SlruReportIOError 在构造错误消息时调用。
 */
static int
MultiXactOffsetIoErrorDetail(const void *opaque_data)
{
	MultiXactId multixid = *(const MultiXactId *) opaque_data;

	return errdetail("Could not access offset of multixact %u.", multixid);
}

/*
 * 中文注释：
 * members SLRU 的 I/O 错误详情回调。
 *
 * opaque_data 是 MultiXactMemberSlruReadContext，包含 MultiXactId 和成员偏移。
 * 若 MultiXactId 有效，报告“无法访问某 MultiXact 在某偏移的成员”；否则只报告
 * 偏移（例如启动修剪阶段还没有具体 MultiXact）。
 */
static int
MultiXactMemberIoErrorDetail(const void *opaque_data)
{
	const MultiXactMemberSlruReadContext *context = opaque_data;

	if (MultiXactIdIsValid(context->multi))
		return errdetail("Could not access member of multixact %u at offset %" PRIu64 ".",
						 context->multi, context->offset);
	else
		return errdetail("Could not access multixact member at offset %" PRIu64 ".",
						 context->offset);
}

/*
 * Decide which of two MultiXactIds is earlier.
 *
 * XXX do we need to do something special for InvalidMultiXactId?
 * (Doesn't look like it.)
 */
/*
 * 中文注释：
 * 判断两个 MultiXactId 的逻辑先后，正确处理 32 位回绕。
 *
 * 把差值转成有符号 32 位整数：若差值为负，说明 multi1 在 multi2 之前。该比较
 * 假定两个 ID 相距小于 2^31；MultiXact 回卷保护保证活跃值不会跨越这个范围。
 */
bool
MultiXactIdPrecedes(MultiXactId multi1, MultiXactId multi2)
{
	int32		diff = (int32) (multi1 - multi2);

	return (diff < 0);
}

/*
 * MultiXactIdPrecedesOrEquals -- is multi1 logically <= multi2?
 *
 * XXX do we need to do something special for InvalidMultiXactId?
 * (Doesn't look like it.)
 */
/*
 * 中文注释：
 * 判断 multi1 是否逻辑上小于等于 multi2，使用与 MultiXactIdPrecedes 相同的
 * 32 位有符号差值方法处理回绕。用于“只前进不后退”的边界检查。
 */
bool
MultiXactIdPrecedesOrEquals(MultiXactId multi1, MultiXactId multi2)
{
	int32		diff = (int32) (multi1 - multi2);

	return (diff <= 0);
}


/*
 * Write a TRUNCATE xlog record
 *
 * We must flush the xlog record to disk before returning --- see notes in
 * TruncateCLOG().
 */
/*
 * 中文注释：
 * 写一条 XLOG_MULTIXACT_TRUNCATE_ID 记录并立即 flush 到磁盘。
 *
 * 记录包含 oldestMultiDB、oldestMulti 和 oldestOffset，恢复端据此重放截断。
 * 必须在删除任何 SLRU 段之前调用并完成 XLogFlush，否则崩溃后可能出现“文件已删、
 * 但没有 WAL 证据”的不一致；这也是 MultiXact 模块少数严格遵循 WAL-before-data
 * 的地方。调用者应处于临界区并已阻止检查点并发。
 */
static void
WriteMTruncateXlogRec(Oid oldestMultiDB,
					  MultiXactId oldestMulti,
					  MultiXactOffset oldestOffset)
{
	XLogRecPtr	recptr;
	xl_multixact_truncate xlrec;

	xlrec.oldestMultiDB = oldestMultiDB;
	xlrec.oldestMulti = oldestMulti;
	xlrec.oldestOffset = oldestOffset;

	XLogBeginInsert();
	XLogRegisterData(&xlrec, SizeOfMultiXactTruncate);
	recptr = XLogInsert(RM_MULTIXACT_ID, XLOG_MULTIXACT_TRUNCATE_ID);
	XLogFlush(recptr);
}

/*
 * MULTIXACT resource manager's routines
 */
/*
 * 中文注释：
 * MultiXact 资源管理器的 redo 回调，按 WAL 记录子类型恢复 SLRU 状态。
 *
 * 支持四种记录：
 *   - XLOG_MULTIXACT_ZERO_OFF_PAGE：清零指定 offsets 页；
 *   - XLOG_MULTIXACT_ZERO_MEM_PAGE：清零指定 members 页；
 *   - XLOG_MULTIXACT_CREATE_ID：把记录中的成员写回两个 SLRU，并推进
 *     nextMXact/nextOffset，确保 nextXid 超过记录中出现的所有 XID；
 *   - XLOG_MULTIXACT_TRUNCATE_ID：更新回卷下界并删除对应旧段。
 * MultiXact 记录不使用 backup block，因此先断言没有 block reference。未知子类型
 * 视为 WAL 损坏，直接 PANIC。
 */
void
multixact_redo(XLogReaderState *record)
{
	uint8		info = XLogRecGetInfo(record) & ~XLR_INFO_MASK;

	/* Backup blocks are not used in multixact records */
	Assert(!XLogRecHasAnyBlockRefs(record));

	if (info == XLOG_MULTIXACT_ZERO_OFF_PAGE)
	{
		int64		pageno;

		memcpy(&pageno, XLogRecGetData(record), sizeof(pageno));
		SimpleLruZeroAndWritePage(MultiXactOffsetCtl, pageno);
	}
	else if (info == XLOG_MULTIXACT_ZERO_MEM_PAGE)
	{
		int64		pageno;

		memcpy(&pageno, XLogRecGetData(record), sizeof(pageno));
		SimpleLruZeroAndWritePage(MultiXactMemberCtl, pageno);
	}
	else if (info == XLOG_MULTIXACT_CREATE_ID)
	{
		xl_multixact_create *xlrec =
			(xl_multixact_create *) XLogRecGetData(record);
		TransactionId max_xid;
		int			i;

		/* Store the data back into the SLRU files */
		RecordNewMultiXact(xlrec->mid, xlrec->moff, xlrec->nmembers,
						   xlrec->members);

		/* Make sure nextMXact/nextOffset are beyond what this record has */
		MultiXactAdvanceNextMXact(NextMultiXactId(xlrec->mid),
								  xlrec->moff + xlrec->nmembers);

		/*
		 * Make sure nextXid is beyond any XID mentioned in the record. This
		 * should be unnecessary, since any XID found here ought to have other
		 * evidence in the XLOG, but let's be safe.
		 */
		max_xid = XLogRecGetXid(record);
		for (i = 0; i < xlrec->nmembers; i++)
		{
			if (TransactionIdPrecedes(max_xid, xlrec->members[i].xid))
				max_xid = xlrec->members[i].xid;
		}

		AdvanceNextFullTransactionIdPastXid(max_xid);
	}
	else if (info == XLOG_MULTIXACT_TRUNCATE_ID)
	{
		xl_multixact_truncate xlrec;

		memcpy(&xlrec, XLogRecGetData(record),
			   SizeOfMultiXactTruncate);

		elog(DEBUG1, "replaying multixact truncation: "
			 "oldestMulti %u (offsets segment %" PRIx64 "), "
			 "oldestOffset %" PRIu64 " (members segment %" PRIx64 ")",
			 xlrec.oldestMulti,
			 MultiXactIdToOffsetSegment(xlrec.oldestMulti),
			 xlrec.oldestOffset,
			 MXOffsetToMemberSegment(xlrec.oldestOffset));

		/* should not be required, but more than cheap enough */
		LWLockAcquire(MultiXactTruncationLock, LW_EXCLUSIVE);

		/*
		 * Advance the horizon values, so they're current at the end of
		 * recovery.
		 */
		SetMultiXactIdLimit(xlrec.oldestMulti, xlrec.oldestMultiDB);

		PerformMembersTruncation(xlrec.oldestOffset);
		PerformOffsetsTruncation(xlrec.oldestMulti);

		LWLockRelease(MultiXactTruncationLock);
	}
	else
		elog(PANIC, "multixact_redo: unknown op code %u", info);
}

/*
 * Entrypoint for sync.c to sync offsets files.
 */
/*
 * 中文注释：
 * offsets SLRU 提供给 sync.c 的同步入口。
 *
 * sync 机制只持有 FileTag 和输出路径缓冲区，不知道具体 SLRU 的目录/命名规则，
 * 因此各 SLRU 提供薄包装，把正确的 SlruDesc 传给通用的 SlruSyncFileTag 完成
 * 路径构造和 fsync。
 */
int
multixactoffsetssyncfiletag(const FileTag *ftag, char *path)
{
	return SlruSyncFileTag(MultiXactOffsetCtl, ftag, path);
}

/*
 * Entrypoint for sync.c to sync members files.
 */
/*
 * 中文注释：
 * members SLRU 提供给 sync.c 的同步入口，转发给 SlruSyncFileTag，并使用
 * MultiXactMemberCtl 构造 pg_multixact/members 下的文件路径。
 */
int
multixactmemberssyncfiletag(const FileTag *ftag, char *path)
{
	return SlruSyncFileTag(MultiXactMemberCtl, ftag, path);
}
