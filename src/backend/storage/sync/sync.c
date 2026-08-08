/*-------------------------------------------------------------------------
 *
 * sync.c
 *	  File synchronization management code.
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 文件同步(sync)的基础设施:它让"文件被写脏"
 * 与"文件真正落盘"解耦,把 fsync 集中到检查点(checkpoint)统一
 * 执行,避免每个后端每次写盘都做昂贵的同步。
 *
 * 两大机制:
 * 1) 待 fsync 请求表(pendingOps,哈希表):任何后端写完数据文件后
 *    (md.c、clog、commit_ts、multixact 等),并不直接 fsync,而是
 *    登记一个 SYNC_REQUEST"这个文件需要 fsync"。哈希表以 FileTag
 *    为键,同一文件的重复请求自然合并去重,一个检查点内每个文件
 *    只 fsync 一次。
 * 2) 延迟删除请求表(pendingUnlinks,链表):DROP 掉的关系的首段
 *    文件不能立即删除(防止 relfilenumber 在崩溃恢复前被复用,
 *    详见 md.c 的 mdunlink 注释),mdunlink 把它截断为 0 后登记
 *    SYNC_UNLINK_REQUEST,由 checkpointer 在下一个检查点完成后
 *    真正 unlink。
 *
 * 两种角色:
 * - 登记端(普通后端):本地没有请求表(pendingOps == NULL),通过
 *   RegisterSyncRequest -> ForwardSyncRequest(checkpointer.c)把请求
 *   放入共享内存队列,由 checkpointer 周期性吸收;
 * - 执行端(standalone 后端、checkpointer):在 InitSync 里建立本地
 *   请求表,吸收队列(checkpointer 侧 AbsorbSyncRequests 在
 *   checkpointer.c 中,会把队列里的请求转成 RememberSyncRequest
 *   的调用)后在 ProcessSyncRequests/SyncPostCheckpoint 中统一执行。
 *
 * 轮次计数与取消:
 * - sync_cycle_ctr:区分"本轮检查点该处理的 fsync 请求"与"处理开始
 *   后才到达的新请求"(后者留到下一轮),防止检查点永不完结;
 * - checkpoint_cycle_ctr:给 unlink 请求打轮次标记,保证在检查点
 *   REDO 点确定之前到达的删除请求不被过早执行;
 * - SYNC_FORGET_REQUEST/SYNC_FILTER_REQUEST:把已登记请求标记为
 *   canceled,让删除文件与待 fsync 记录保持正确、不再对已消失的
 *   文件做同步。
 *
 * 分发机制:请求按 FileTag.handler 字段经 syncsw[] 函数表分派到
 * 具体的存储模块(md、clog、commit_ts、multixact),每个模块只需
 * 提供自己的 sync/unlink/match 回调,新增文件类型无需改动本文件
 * 的队列逻辑。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/sync/sync.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <unistd.h>
#include <fcntl.h>
#include <sys/file.h>

#include "access/clog.h"
#include "access/commit_ts.h"
#include "access/multixact.h"
#include "access/xlog.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "portability/instr_time.h"
#include "postmaster/bgwriter.h"
#include "storage/fd.h"
#include "storage/latch.h"
#include "storage/md.h"
#include "utils/hsearch.h"
#include "utils/memutils.h"
#include "utils/wait_event.h"

/*
 * In some contexts (currently, standalone backends and the checkpointer)
 * we keep track of pending fsync operations: we need to remember all relation
 * segments that have been written since the last checkpoint, so that we can
 * fsync them down to disk before completing the next checkpoint.  This hash
 * table remembers the pending operations.  We use a hash table mostly as
 * a convenient way of merging duplicate requests.
 *
 * We use a similar mechanism to remember no-longer-needed files that can
 * be deleted after the next checkpoint, but we use a linked list instead of
 * a hash table, because we don't expect there to be any duplicate requests.
 *
 * These mechanisms are only used for non-temp relations; we never fsync
 * temp rels, nor do we need to postpone their deletion (see comments in
 * mdunlink).
 *
 * (Regular backends do not track pending operations locally, but forward
 * them to the checkpointer.)
 */
typedef uint16 CycleCtr;		/* can be any convenient integer size */

/* 周期计数器类型(CycleCtr,取足够容纳轮次的最小宽度即可,这里用
 * uint16):给"fsync/unlink 请求"打上"属于第几轮检查点"的标记,
 * 用于区分新旧请求。回绕是允许的,最坏后果只是多等一轮,不会出错 */

/* "待 fsync"请求的哈希表条目(哈希键为 tag,即 FileTag,见 sync.h):
 * - tag       : 标识"由哪个 handler 处理、哪个文件";
 * - cycle_ctr : 条目里"最老的请求"所属轮次(sync_cycle_ctr 登记时
 *               的值)。同一文件的重复请求会合并进同一条目,此时
 *               必须保留最早登记时的轮次,保证该轮不会被跳过;
 * - canceled  : 是否已被取消(SYNC_FORGET/FILTER 请求标记)。为
 *                true 时执行阶段跳过,但条目仍会被移除。 */
typedef struct
{
	FileTag		tag;			/* identifies handler and file */
	CycleCtr	cycle_ctr;		/* sync_cycle_ctr of oldest request */
	bool		canceled;		/* canceled is true if we canceled "recently" */
} PendingFsyncEntry;

/* "检查点后删除"请求的链表条目(用链表而非哈希表:预期不会出现
 * 重复请求):
 * - tag       : 标识要删除的文件;
 * - cycle_ctr : 登记时的 checkpoint_cycle_ctr,用来判断该请求是否
 *               迟于当前检查点开始(迟到的留到下一轮才删);
 * - canceled  : 请求是否已被取消。 */
typedef struct
{
	FileTag		tag;			/* identifies handler and file */
	CycleCtr	cycle_ctr;		/* checkpoint_cycle_ctr when request was made */
	bool		canceled;		/* true if request has been canceled */
} PendingUnlinkEntry;

/* 待 fsync 请求的哈希表;待删除请求的链表;二者共用的内存上下文
 * (挂在 TopMemoryContext 下,并被明确允许在 critical section 中
 * 分配,见 InitSync 的说明)。只有"本地执行者"(standalone 后端、
 * checkpointer)会创建它们;普通后端保持 NULL/NIL,仅转发请求。 */
static HTAB *pendingOps = NULL;
static List *pendingUnlinks = NIL;
static MemoryContext pendingOpsCxt; /* context for the above  */

/* sync_cycle_ctr:本轮 fsync 的轮次号。ProcessSyncRequests 开始时
 * 加 1,此后新登记的请求带上新轮次,与"本轮应处理"的旧请求区分。
 * checkpoint_cycle_ctr:本轮 unlink 的轮次号。SyncPreCheckpoint 时
 * 加 1,用于判断删除请求的先后(见 SyncPreCheckpoint/SyncPostCheckpoint) */
static CycleCtr sync_cycle_ctr = 0;
static CycleCtr checkpoint_cycle_ctr = 0;

/* Intervals for calling AbsorbSyncRequests */
/* 处理若干条请求后吸收一次共享队列的间隔:fsync 每处理
 * FSYNCS_PER_ABSORB 条、unlink 每处理 UNLINKS_PER_ABSORB 条,
 * 就调用一次 AbsorbSyncRequests(),防止长时间不吸收导致
 * checkpointer 的共享请求队列溢出 */
#define FSYNCS_PER_ABSORB		10
#define UNLINKS_PER_ABSORB		10

/*
 * Function pointers for handling sync and unlink requests.
 */
/* 某类文件(handler)的同步操作函数表:
 * - sync_syncfiletag   : 对文件执行 fsync(返回 0 成功,<0 失败,
 *                        失败原因在 errno,path 输出文件路径);
 * - sync_unlinkfiletag : 删除文件(语义同上);
 * - sync_filetagmatches: 判断一个候选 tag 是否与给定 tag 匹配
 *                        (用于按范围取消请求,如取消整个关系的
 *                        所有段的 fsync)。
 * 新增文件类型时在此注册一组回调即可,队列逻辑无需改动。 */
typedef struct SyncOps
{
	int			(*sync_syncfiletag) (const FileTag *ftag, char *path);
	int			(*sync_unlinkfiletag) (const FileTag *ftag, char *path);
	bool		(*sync_filetagmatches) (const FileTag *ftag,
										const FileTag *candidate);
} SyncOps;

/*
 * These indexes must correspond to the values of the SyncRequestHandler enum.
 */
/* 所有 handler 的操作函数表。数组下标必须与 sync.h 中
 * SyncRequestHandler 枚举值严格对应:
 * - md(magnetic disk)提供完整的三类回调,负责关系数据文件;
 * - clog(pg_xact)、commit_ts(pg_commit_ts)、multixact 的
 *   offsets/members 只需 fsync 回调——它们位于固定目录,删除走
 *   目录级清理,不通过本队列;
 * - 未提供的字段保持 NULL,调用方保证不会用到。 */
static const SyncOps syncsw[] = {
	/* magnetic disk */
	[SYNC_HANDLER_MD] = {
		.sync_syncfiletag = mdsyncfiletag,
		.sync_unlinkfiletag = mdunlinkfiletag,
		.sync_filetagmatches = mdfiletagmatches
	},
	/* pg_xact */
	[SYNC_HANDLER_CLOG] = {
		.sync_syncfiletag = clogsyncfiletag
	},
	/* pg_commit_ts */
	[SYNC_HANDLER_COMMIT_TS] = {
		.sync_syncfiletag = committssyncfiletag
	},
	/* pg_multixact/offsets */
	[SYNC_HANDLER_MULTIXACT_OFFSET] = {
		.sync_syncfiletag = multixactoffsetssyncfiletag
	},
	/* pg_multixact/members */
	[SYNC_HANDLER_MULTIXACT_MEMBER] = {
		.sync_syncfiletag = multixactmemberssyncfiletag
	}
};

/*
 * Initialize data structures for the file sync tracking.
 */
/*
 * InitSync (中文)初始化文件同步跟踪所需的数据结构
 *
 * 【作用】后端进程启动时调用。仅当本进程是"本地执行者"——standalone
 * 后端(不在 postmaster 管理下)或 checkpointer 辅助进程——才创建
 * pendingOps 哈希表、pendingUnlinks 链表及它们的内存上下文;普通
 * 后端保持 pendingOps == NULL,意味着"我不执行同步,只把请求转发
 * 给 checkpointer"(见 RegisterSyncRequest)。
 *
 * 【设计思想】
 * - 用哈希表(pendingOps)收集待 fsync 请求:同一文件被反复登记时
 *   自动合并为一条,天然完成去重;
 * - 内存上下文显式调用 MemoryContextAllowInCriticalSection:
 *   checkpointer 在吸收请求(AbsorbSyncRequests,可能发生在临界区
 *   内)时也要向表中插入条目。代价是理论上临界区内可能内存耗尽
 *   而 PANIC,但该表很小,实际几乎不可能发生。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
InitSync(void)
{
	/*
	 * Create pending-operations hashtable if we need it.  Currently, we need
	 * it if we are standalone (not under a postmaster) or if we are a
	 * checkpointer auxiliary process.
	 */
	if (!IsUnderPostmaster || AmCheckpointerProcess())
	{
		HASHCTL		hash_ctl;

		/*
		 * XXX: The checkpointer needs to add entries to the pending ops table
		 * when absorbing fsync requests.  That is done within a critical
		 * section, which isn't usually allowed, but we make an exception. It
		 * means that there's a theoretical possibility that you run out of
		 * memory while absorbing fsync requests, which leads to a PANIC.
		 * Fortunately the hash table is small so that's unlikely to happen in
		 * practice.
		 */
		pendingOpsCxt = AllocSetContextCreate(TopMemoryContext,
											  "Pending ops context",
											  ALLOCSET_DEFAULT_SIZES);
		MemoryContextAllowInCriticalSection(pendingOpsCxt, true);

		hash_ctl.keysize = sizeof(FileTag);
		hash_ctl.entrysize = sizeof(PendingFsyncEntry);
		hash_ctl.hcxt = pendingOpsCxt;
		pendingOps = hash_create("Pending Ops Table",
								 100L,
								 &hash_ctl,
								 HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);
		pendingUnlinks = NIL;
	}
}

/*
 * SyncPreCheckpoint() -- Do pre-checkpoint work
 *
 * To distinguish unlink requests that arrived before this checkpoint
 * started from those that arrived during the checkpoint, we use a cycle
 * counter similar to the one we use for fsync requests. That cycle
 * counter is incremented here.
 *
 * This must be called *before* the checkpoint REDO point is determined.
 * That ensures that we won't delete files too soon.  Since this calls
 * AbsorbSyncRequests(), which performs memory allocations, it cannot be
 * called within a critical section.
 *
 * Note that we can't do anything here that depends on the assumption
 * that the checkpoint will be completed.
 */
void
SyncPreCheckpoint(void)
{
	/*
	 * Operations such as DROP TABLESPACE assume that the next checkpoint will
	 * process all recently forwarded unlink requests, but if they aren't
	 * absorbed prior to advancing the cycle counter, they won't be processed
	 * until a future checkpoint.  The following absorb ensures that any
	 * unlink requests forwarded before the checkpoint began will be processed
	 * in the current checkpoint.
	 */
	AbsorbSyncRequests();

	/*
	 * Any unlink requests arriving after this point will be assigned the next
	 * cycle counter, and won't be unlinked until next checkpoint.
	 */
	checkpoint_cycle_ctr++;
}

/*
 * SyncPostCheckpoint() -- Do post-checkpoint work
 *
 * Remove any lingering files that can now be safely removed.
 */
void
SyncPostCheckpoint(void)
{
	int			absorb_counter;
	ListCell   *lc;

	absorb_counter = UNLINKS_PER_ABSORB;
	foreach(lc, pendingUnlinks)
	{
		PendingUnlinkEntry *entry = (PendingUnlinkEntry *) lfirst(lc);
		char		path[MAXPGPATH];

		/* Skip over any canceled entries */
		if (entry->canceled)
			continue;

		/*
		 * New entries are appended to the end, so if the entry is new we've
		 * reached the end of old entries.
		 *
		 * Note: if just the right number of consecutive checkpoints fail, we
		 * could be fooled here by cycle_ctr wraparound.  However, the only
		 * consequence is that we'd delay unlinking for one more checkpoint,
		 * which is perfectly tolerable.
		 */
		if (entry->cycle_ctr == checkpoint_cycle_ctr)
			break;

		/* Unlink the file */
		if (syncsw[entry->tag.handler].sync_unlinkfiletag(&entry->tag,
														  path) < 0)
		{
			/*
			 * There's a race condition, when the database is dropped at the
			 * same time that we process the pending unlink requests. If the
			 * DROP DATABASE deletes the file before we do, we will get ENOENT
			 * here. rmtree() also has to ignore ENOENT errors, to deal with
			 * the possibility that we delete the file first.
			 */
			if (errno != ENOENT)
				ereport(WARNING,
						(errcode_for_file_access(),
						 errmsg("could not remove file \"%s\": %m", path)));
		}

		/* Mark the list entry as canceled, just in case */
		entry->canceled = true;

		/*
		 * As in ProcessSyncRequests, we don't want to stop absorbing fsync
		 * requests for a long time when there are many deletions to be done.
		 * We can safely call AbsorbSyncRequests() at this point in the loop.
		 */
		if (--absorb_counter <= 0)
		{
			AbsorbSyncRequests();
			absorb_counter = UNLINKS_PER_ABSORB;
		}
	}

	/*
	 * If we reached the end of the list, we can just remove the whole list
	 * (remembering to pfree all the PendingUnlinkEntry objects).  Otherwise,
	 * we must keep the entries at or after "lc".
	 */
	if (lc == NULL)
	{
		list_free_deep(pendingUnlinks);
		pendingUnlinks = NIL;
	}
	else
	{
		int			ntodelete = list_cell_number(pendingUnlinks, lc);

		for (int i = 0; i < ntodelete; i++)
			pfree(list_nth(pendingUnlinks, i));

		pendingUnlinks = list_delete_first_n(pendingUnlinks, ntodelete);
	}
}

/*
 *	ProcessSyncRequests() -- Process queued fsync requests.
 */
void
ProcessSyncRequests(void)
{
	static bool sync_in_progress = false;

	HASH_SEQ_STATUS hstat;
	PendingFsyncEntry *entry;
	int			absorb_counter;

	/* Statistics on sync times */
	int			processed = 0;
	instr_time	sync_start,
				sync_end,
				sync_diff;
	uint64		elapsed;
	uint64		longest = 0;
	uint64		total_elapsed = 0;

	/*
	 * This is only called during checkpoints, and checkpoints should only
	 * occur in processes that have created a pendingOps.
	 */
	if (!pendingOps)
		elog(ERROR, "cannot sync without a pendingOps table");

	/*
	 * If we are in the checkpointer, the sync had better include all fsync
	 * requests that were queued by backends up to this point.  The tightest
	 * race condition that could occur is that a buffer that must be written
	 * and fsync'd for the checkpoint could have been dumped by a backend just
	 * before it was visited by BufferSync().  We know the backend will have
	 * queued an fsync request before clearing the buffer's dirtybit, so we
	 * are safe as long as we do an Absorb after completing BufferSync().
	 */
	AbsorbSyncRequests();

	/*
	 * To avoid excess fsync'ing (in the worst case, maybe a never-terminating
	 * checkpoint), we want to ignore fsync requests that are entered into the
	 * hashtable after this point --- they should be processed next time,
	 * instead.  We use sync_cycle_ctr to tell old entries apart from new
	 * ones: new ones will have cycle_ctr equal to the incremented value of
	 * sync_cycle_ctr.
	 *
	 * In normal circumstances, all entries present in the table at this point
	 * will have cycle_ctr exactly equal to the current (about to be old)
	 * value of sync_cycle_ctr.  However, if we fail partway through the
	 * fsync'ing loop, then older values of cycle_ctr might remain when we
	 * come back here to try again.  Repeated checkpoint failures would
	 * eventually wrap the counter around to the point where an old entry
	 * might appear new, causing us to skip it, possibly allowing a checkpoint
	 * to succeed that should not have.  To forestall wraparound, any time the
	 * previous ProcessSyncRequests() failed to complete, run through the
	 * table and forcibly set cycle_ctr = sync_cycle_ctr.
	 *
	 * Think not to merge this loop with the main loop, as the problem is
	 * exactly that that loop may fail before having visited all the entries.
	 * From a performance point of view it doesn't matter anyway, as this path
	 * will never be taken in a system that's functioning normally.
	 */
	if (sync_in_progress)
	{
		/* prior try failed, so update any stale cycle_ctr values */
		hash_seq_init(&hstat, pendingOps);
		while ((entry = (PendingFsyncEntry *) hash_seq_search(&hstat)) != NULL)
		{
			entry->cycle_ctr = sync_cycle_ctr;
		}
	}

	/* Advance counter so that new hashtable entries are distinguishable */
	sync_cycle_ctr++;

	/* Set flag to detect failure if we don't reach the end of the loop */
	sync_in_progress = true;

	/* Now scan the hashtable for fsync requests to process */
	absorb_counter = FSYNCS_PER_ABSORB;
	hash_seq_init(&hstat, pendingOps);
	while ((entry = (PendingFsyncEntry *) hash_seq_search(&hstat)) != NULL)
	{
		int			failures;

		/*
		 * If the entry is new then don't process it this time; it is new.
		 * Note "continue" bypasses the hash-remove call at the bottom of the
		 * loop.
		 */
		if (entry->cycle_ctr == sync_cycle_ctr)
			continue;

		/* Else assert we haven't missed it */
		Assert((CycleCtr) (entry->cycle_ctr + 1) == sync_cycle_ctr);

		/*
		 * If fsync is off then we don't have to bother opening the file at
		 * all.  (We delay checking until this point so that changing fsync on
		 * the fly behaves sensibly.)
		 */
		if (enableFsync)
		{
			/*
			 * If in checkpointer, we want to absorb pending requests every so
			 * often to prevent overflow of the fsync request queue.  It is
			 * unspecified whether newly-added entries will be visited by
			 * hash_seq_search, but we don't care since we don't need to
			 * process them anyway.
			 */
			if (--absorb_counter <= 0)
			{
				AbsorbSyncRequests();
				absorb_counter = FSYNCS_PER_ABSORB;
			}

			/*
			 * The fsync table could contain requests to fsync segments that
			 * have been deleted (unlinked) by the time we get to them. Rather
			 * than just hoping an ENOENT (or EACCES on Windows) error can be
			 * ignored, what we do on error is absorb pending requests and
			 * then retry. Since mdunlink() queues a "cancel" message before
			 * actually unlinking, the fsync request is guaranteed to be
			 * marked canceled after the absorb if it really was this case.
			 * DROP DATABASE likewise has to tell us to forget fsync requests
			 * before it starts deletions.
			 */
			for (failures = 0; !entry->canceled; failures++)
			{
				char		path[MAXPGPATH];

				INSTR_TIME_SET_CURRENT(sync_start);
				if (syncsw[entry->tag.handler].sync_syncfiletag(&entry->tag,
																path) == 0)
				{
					/* Success; update statistics about sync timing */
					INSTR_TIME_SET_CURRENT(sync_end);
					sync_diff = sync_end;
					INSTR_TIME_SUBTRACT(sync_diff, sync_start);
					elapsed = INSTR_TIME_GET_MICROSEC(sync_diff);
					if (elapsed > longest)
						longest = elapsed;
					total_elapsed += elapsed;
					processed++;

					if (log_checkpoints)
						elog(DEBUG1, "checkpoint sync: number=%d file=%s time=%.3f ms",
							 processed,
							 path,
							 (double) elapsed / 1000);

					break;		/* out of retry loop */
				}

				/*
				 * It is possible that the relation has been dropped or
				 * truncated since the fsync request was entered. Therefore,
				 * allow ENOENT, but only if we didn't fail already on this
				 * file.
				 */
				if (!FILE_POSSIBLY_DELETED(errno) || failures > 0)
					ereport(data_sync_elevel(ERROR),
							(errcode_for_file_access(),
							 errmsg("could not fsync file \"%s\": %m",
									path)));
				else
					ereport(DEBUG1,
							(errcode_for_file_access(),
							 errmsg_internal("could not fsync file \"%s\" but retrying: %m",
											 path)));

				/*
				 * Absorb incoming requests and check to see if a cancel
				 * arrived for this relation fork.
				 */
				AbsorbSyncRequests();
				absorb_counter = FSYNCS_PER_ABSORB; /* might as well... */
			}					/* end retry loop */
		}

		/* We are done with this entry, remove it */
		if (hash_search(pendingOps, &entry->tag, HASH_REMOVE, NULL) == NULL)
			elog(ERROR, "pendingOps corrupted");
	}							/* end loop over hashtable entries */

	/* Return sync performance metrics for report at checkpoint end */
	CheckpointStats.ckpt_sync_rels = processed;
	CheckpointStats.ckpt_longest_sync = longest;
	CheckpointStats.ckpt_agg_sync_time = total_elapsed;

	/* Flag successful completion of ProcessSyncRequests */
	sync_in_progress = false;
}

/*
 * RememberSyncRequest() -- callback from checkpointer side of sync request
 *
 * We stuff fsync requests into the local hash table for execution
 * during the checkpointer's next checkpoint.  UNLINK requests go into a
 * separate linked list, however, because they get processed separately.
 *
 * See sync.h for more information on the types of sync requests supported.
 */
void
RememberSyncRequest(const FileTag *ftag, SyncRequestType type)
{
	Assert(pendingOps);

	if (type == SYNC_FORGET_REQUEST)
	{
		PendingFsyncEntry *entry;

		/* Cancel previously entered request */
		entry = (PendingFsyncEntry *) hash_search(pendingOps,
												  ftag,
												  HASH_FIND,
												  NULL);
		if (entry != NULL)
			entry->canceled = true;
	}
	else if (type == SYNC_FILTER_REQUEST)
	{
		HASH_SEQ_STATUS hstat;
		PendingFsyncEntry *pfe;
		ListCell   *cell;

		/* Cancel matching fsync requests */
		hash_seq_init(&hstat, pendingOps);
		while ((pfe = (PendingFsyncEntry *) hash_seq_search(&hstat)) != NULL)
		{
			if (pfe->tag.handler == ftag->handler &&
				syncsw[ftag->handler].sync_filetagmatches(ftag, &pfe->tag))
				pfe->canceled = true;
		}

		/* Cancel matching unlink requests */
		foreach(cell, pendingUnlinks)
		{
			PendingUnlinkEntry *pue = (PendingUnlinkEntry *) lfirst(cell);

			if (pue->tag.handler == ftag->handler &&
				syncsw[ftag->handler].sync_filetagmatches(ftag, &pue->tag))
				pue->canceled = true;
		}
	}
	else if (type == SYNC_UNLINK_REQUEST)
	{
		/* Unlink request: put it in the linked list */
		MemoryContext oldcxt = MemoryContextSwitchTo(pendingOpsCxt);
		PendingUnlinkEntry *entry;

		entry = palloc_object(PendingUnlinkEntry);
		entry->tag = *ftag;
		entry->cycle_ctr = checkpoint_cycle_ctr;
		entry->canceled = false;

		pendingUnlinks = lappend(pendingUnlinks, entry);

		MemoryContextSwitchTo(oldcxt);
	}
	else
	{
		/* Normal case: enter a request to fsync this segment */
		MemoryContext oldcxt = MemoryContextSwitchTo(pendingOpsCxt);
		PendingFsyncEntry *entry;
		bool		found;

		Assert(type == SYNC_REQUEST);

		entry = (PendingFsyncEntry *) hash_search(pendingOps,
												  ftag,
												  HASH_ENTER,
												  &found);
		/* if new entry, or was previously canceled, initialize it */
		if (!found || entry->canceled)
		{
			entry->cycle_ctr = sync_cycle_ctr;
			entry->canceled = false;
		}

		/*
		 * NB: it's intentional that we don't change cycle_ctr if the entry
		 * already exists.  The cycle_ctr must represent the oldest fsync
		 * request that could be in the entry.
		 */

		MemoryContextSwitchTo(oldcxt);
	}
}

/*
 * Register the sync request locally, or forward it to the checkpointer.
 *
 * If retryOnError is true, we'll keep trying if there is no space in the
 * queue.  Return true if we succeeded, or false if there wasn't space.
 */
bool
RegisterSyncRequest(const FileTag *ftag, SyncRequestType type,
					bool retryOnError)
{
	bool		ret;

	if (pendingOps != NULL)
	{
		/* standalone backend or startup process: fsync state is local */
		RememberSyncRequest(ftag, type);
		return true;
	}

	for (;;)
	{
		/*
		 * Notify the checkpointer about it.  If we fail to queue a message in
		 * retryOnError mode, we have to sleep and try again ... ugly, but
		 * hopefully won't happen often.
		 *
		 * XXX should we CHECK_FOR_INTERRUPTS in this loop?  Escaping with an
		 * error in the case of SYNC_UNLINK_REQUEST would leave the
		 * no-longer-used file still present on disk, which would be bad, so
		 * I'm inclined to assume that the checkpointer will always empty the
		 * queue soon.
		 */
		ret = ForwardSyncRequest(ftag, type);

		/*
		 * If we are successful in queueing the request, or we failed and were
		 * instructed not to retry on error, break.
		 */
		if (ret || (!ret && !retryOnError))
			break;

		WaitLatch(NULL, WL_EXIT_ON_PM_DEATH | WL_TIMEOUT, 10,
				  WAIT_EVENT_REGISTER_SYNC_REQUEST);
	}

	return ret;
}
