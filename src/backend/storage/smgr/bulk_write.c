/*-------------------------------------------------------------------------
 *
 * bulk_write.c
 *	  Efficiently and reliably populate a new relation
 *
 * The assumption is that no other backends access the relation while we are
 * loading it, so we can take some shortcuts.  Pages already present in the
 * indicated fork when the bulk write operation is started are not modified
 * unless explicitly written to.  Do not mix operations through the regular
 * buffer manager and the bulk loading interface!
 *
 * We bypass the buffer manager to avoid the locking overhead, and call
 * smgrextend() directly.  A downside is that the pages will need to be
 * re-read into shared buffers on first use after the build finishes.  That's
 * usually a good tradeoff for large relations, and for small relations, the
 * overhead isn't very significant compared to creating the relation in the
 * first place.
 *
 * The pages are WAL-logged if needed.  To save on WAL header overhead, we
 * WAL-log several pages in one record.
 *
 * One tricky point is that because we bypass the buffer manager, we need to
 * register the relation for fsyncing at the next checkpoint ourselves, and
 * make sure that the relation is correctly fsync'd by us or the checkpointer
 * even if a checkpoint happens concurrently.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 的"批量写入"(bulk write)机制,为 COPY、批量
 * INSERT 等"一次性往新关系里灌大量数据"的场景提供高效且可靠的写路径。
 * 它由 PG 17 引入,核心思想是:既然整个加载期间不会有其他后端进程访问
 * 该关系,就可以绕开共享缓冲池(buffer pool)及其加锁/查找机制,直接调用
 * smgrextend()/smgrwrite() 把页面写到磁盘,省去缓冲池的锁开销与 pin
 * 管理。
 *
 * 设计要点:
 * 1) 页缓冲 + 批量 WAL:要写的页先攒在一个定长队列
 *    (pending_writes,上限 MAX_PENDING_WRITES,与单条 WAL 记录能容纳的
 *    最大块数 XLR_MAX_BLOCK_ID 对齐)里,凑满一批后按块号排序,再用
 *    log_newpages() 把多页合并进同一条 WAL 记录,大幅削减 WAL 头开销;
 * 2) 与检查点的竞态处理:因为绕过了缓冲管理器,没有谁替我们把脏页登记
 *    到检查点;本文件通过记录开始时的 RedoRecPtr、并在结束时用
 *    DELAY_CHKPT_START 延迟检查点启动来保证"要么检查点覆盖了我们的
 *    页,要么我们在结束时自己 fsync",详见 smgr_bulk_finish() 的注释;
 * 3) 调用约定:整个批量操作期间禁止混用普通缓冲管理器路径访问同一
 *    关系;同一块在一次批量操作内只能写一次;写出的页在首次被正常
 *    访问时会重新从磁盘读入共享缓冲池,这是有意为之的取舍。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/smgr/bulk_write.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/xloginsert.h"
#include "access/xlogrecord.h"
#include "storage/bufpage.h"
#include "storage/bulk_write.h"
#include "storage/proc.h"
#include "storage/smgr.h"
#include "utils/rel.h"

/* 待写页面队列的长度上限:与一条 WAL 记录(block 型记录)能引用的最大
 * 块数 XLR_MAX_BLOCK_ID 保持一致。因为批量 WAL 记录一次要装入这么多页,
 * 队列容量必须能容纳"一次 WAL 记录所需的全部页"。 */
#define MAX_PENDING_WRITES XLR_MAX_BLOCK_ID

/* 全零页缓冲(按 I/O 对齐要求分配,长度与 BLCKSZ 相同):
 * 当批量写入出现"跳跃式扩展"(先写后面的块、再回头补前面的块)时,
 * 用它在两块之间垫出全零页,避免文件碎片。全零页不算校验和(全零页的
 * 校验和是固定值,无需显式计算),也不做 WAL 记录。 */
static const PGIOAlignedBlock zero_buffer = {0};	/* worth BLCKSZ */

/* 一条"待写页"记录,保存在 BulkWriteState::pending_writes 队列中:
 * - buf      : 待写的页内容(BulkWriteBuffer,由 smgr_bulk_get_buf()
 *               分配,本记录持有其所有权,写完后由 smgr_bulk_flush()
 *               负责释放);
 * - blkno    : 页所在块号(关系内偏移,从 0 开始);
 * - page_std : 该页是否是"标准页布局"(标准页头,含 pd_lower/pd_upper
 *               等字段)。写 WAL 记录时需要知道这一点:只要有一页非
 *               标准,整批就按非标准方式记录(见 smgr_bulk_flush())。 */
typedef struct PendingWrite
{
	BulkWriteBuffer buf;
	BlockNumber blkno;
	bool		page_std;
} PendingWrite;

/*
 * Bulk writer state for one relation fork.
 */
/* 一个关系 fork 的批量写入状态对象(对调用方不透明,完整定义只在本文件
 * 内可见):
 * - smgr       : 目标关系的 SMgrRelation(通过 smgr API 直接读写磁盘,
 *                绕开共享缓冲池);
 * - forknum    : 正在加载的目标 fork(通常是 MAIN_FORKNUM 或
 *                INIT_FORKNUM);
 * - use_wal    : 是否需要为这些页写 WAL(临时关系或不写 WAL 的关系为
 *                false);
 * - npending / pending_writes[] : 待写页队列。攒满 MAX_PENDING_WRITES
 *                条就调用 smgr_bulk_flush() 批量落盘,控制单条 WAL
 *                记录的大小;
 * - relsize    : 当前已知的关系大小(块数),用来判断某块是否超出 EOF
 *                (超出则必须 smgrextend 而不是 smgrwrite);
 * - start_RedoRecPtr : 批量操作开始时刻的全局 RedoRecPtr 快照。结束时
 *                若与当前值不同,说明期间发生了检查点而检查点没来得及
 *                覆盖我们的写,必须自己 fsync(见 smgr_bulk_finish());
 * - memcxt     : 创建本状态时所在的内存上下文;之后所有待写页缓冲都从
 *                这里分配,保证与调用方的上下文生命周期一致。 */
struct BulkWriteState
{
	/* Information about the target relation we're writing */
	SMgrRelation smgr;
	ForkNumber	forknum;
	bool		use_wal;

	/* We keep several writes queued, and WAL-log them in batches */
	int			npending;
	PendingWrite pending_writes[MAX_PENDING_WRITES];

	/* Current size of the relation */
	BlockNumber relsize;

	/* The RedoRecPtr at the time that the bulk operation started */
	XLogRecPtr	start_RedoRecPtr;

	MemoryContext memcxt;
};

/* 把队列中所有待写页刷出(排序 -> WAL -> 写盘)的内部函数,见函数定义处
 * 的详细说明。 */
static void smgr_bulk_flush(BulkWriteState *bulkstate);

/*
 * smgr_bulk_start_rel (中文)开始对一个关系 fork 的批量写入(基于 relcache)
 *
 * 【作用】COPY、批量 INSERT 等上层模块在开始加载数据前调用,创建并
 * 返回 BulkWriteState 状态对象。本版本直接使用 relcache 条目的
 * SMgrRelation,并自动判断是否需要写 WAL:只要该关系需要 WAL
 * (RelationNeedsWAL)或目标是 init fork(INIT_FORKNUM 永远需要 WAL,
 * 因为它是 unlogged 表在崩溃后重建数据的依据),就开启 WAL。
 *
 * 【设计思想】把"是否需要 WAL"的判定集中在这里,调用方无需关心关系
 * 的持久性细节;没有 relcache 条目的场景(如恢复过程)使用
 * smgr_bulk_start_smgr() 手工指定。
 *
 * 【参数】
 *   rel     —— 目标关系的 relcache 条目(必须已存在);
 *   forknum —— 要加载的 fork(MAIN_FORKNUM 或 INIT_FORKNUM)。
 * 【返回值】新分配的 BulkWriteState(调用方必须在结束时调用
 *           smgr_bulk_finish() 收尾)。
 *
 * Start a bulk write operation on a relation fork.
 */
BulkWriteState *
smgr_bulk_start_rel(Relation rel, ForkNumber forknum)
{
	return smgr_bulk_start_smgr(RelationGetSmgr(rel),
								forknum,
								RelationNeedsWAL(rel) || forknum == INIT_FORKNUM);
}

/*
 * smgr_bulk_start_smgr (中文)开始批量写入(SMgrRelation 版本,不依赖 relcache)
 *
 * 【作用】与 smgr_bulk_start_rel() 等价,但直接接收 SMgrRelation 和
 * use_wal 标志,供没有 relcache 条目可用的场景使用。初始化要点:
 * - 记录当前关系大小(relsize = smgrnblocks()),用于后续区分"扩展"
 *   与"覆写"已有块;
 * - 记录当前 RedoRecPtr 快照,供 smgr_bulk_finish() 检测并发检查点;
 * - 记住当前内存上下文,之后所有页缓冲都从它分配。
 *
 * 【设计思想】启动时查询一次关系大小,之后 smgr_bulk_flush() 里只做
 * 整数比较即可判断是否超出 EOF,不需要每次写都向内核问询文件大小。
 *
 * 【参数】
 *   smgr   —— 目标关系的 SMgrRelation;
 *   forknum—— 目标 fork;
 *   use_wal—— 是否需要写 WAL(由调用方根据关系持久性决定)。
 * 【返回值】新分配的 BulkWriteState。
 *
 * Start a bulk write operation on a relation fork.
 *
 * This is like smgr_bulk_start_rel, but can be used without a relcache entry.
 */
BulkWriteState *
smgr_bulk_start_smgr(SMgrRelation smgr, ForkNumber forknum, bool use_wal)
{
	BulkWriteState *state;

	state = palloc_object(BulkWriteState);
	state->smgr = smgr;
	state->forknum = forknum;
	state->use_wal = use_wal;

	state->npending = 0;
	state->relsize = smgrnblocks(smgr, forknum);

	state->start_RedoRecPtr = GetRedoRecPtr();

	/*
	 * Remember the memory context.  We will use it to allocate all the
	 * buffers later.
	 */
	state->memcxt = CurrentMemoryContext;

	return state;
}

/*
 * smgr_bulk_finish (中文)结束批量写入:刷出剩余页并保证数据安全落盘
 *
 * 【作用】批量加载结束时调用,做两件事:
 * 1) 把队列里剩余的待写页全部刷出(smgr_bulk_flush():WAL + 写盘);
 * 2) 按关系的持久性级别,确保数据在崩溃/正常停机后仍然可靠:
 *    - 临时关系:从不 fsync,直接返回;
 *    - 非 WAL 关系(use_wal=false,即 unlogged 表或 wal_level=minimal
 *      下的永久关系):调用 smgrregistersync() 登记到检查点。unlogged
 *      表只需在正常关机的检查点被刷出即可;minimal 模式下永久关系实际
 *      会在提交时由 smgrDoPendingSyncs() 处理(小关系甚至可能改为"整表
 *      记 WAL"而免去 fsync),这里保守地登记一次也无妨;
 *    - 正常 WAL 关系:写入时传了 skipFsync=true,因此要把整个关系登记
 *      给下一个检查点。但这有一个漏洞:如果检查点在我们写页期间启动,
 *      它没见到这些写请求,崩溃重放只会从该检查点开始,我们更早的 WAL
 *      记录就丢了。为此:
 *      a) 置 DELAY_CHKPT_START 标志,阻止新检查点在"读 RedoRecPtr"与
 *         "登记 fsync"两步之间启动;
 *      b) 比较 start_RedoRecPtr 与当前 GetRedoRecPtr():若不一致,说明
 *         检查点确实发生过,立即自己 smgrimmedsync() 把关系刷盘;否则
 *         正常 smgrregistersync() 即可。
 *      最后清除 DELAY_CHKPT_START。
 *
 * 【设计思想】"WAL 日志 + 检查点"与"直接 fsync"两套可靠性机制在此精确
 * 衔接:要么检查点覆盖了我们的全部写(登记成功,无需自刷),要么检查点
 * 已经过去而我们错过了它(检测到 RedoRecPtr 前进,自己刷)。这个判断
 * 依赖的前提是"没有其他后端在并发修改该页",这正是批量加载的独占假设。
 *
 * 【参数】bulkstate —— 要结束的批量写入状态。
 * 【返回值】无。
 *
 * Finish bulk write operation.
 *
 * This WAL-logs and flushes any remaining pending writes to disk, and fsyncs
 * the relation if needed.
 */
void
smgr_bulk_finish(BulkWriteState *bulkstate)
{
	/* WAL-log and flush any remaining pages */
	smgr_bulk_flush(bulkstate);

	/*
	 * Fsync the relation, or register it for the next checkpoint, if
	 * necessary.
	 */
	if (SmgrIsTemp(bulkstate->smgr))
	{
		/* Temporary relations don't need to be fsync'd, ever */
	}
	else if (!bulkstate->use_wal)
	{
		/*----------
		 * This is either an unlogged relation, or a permanent relation but we
		 * skipped WAL-logging because wal_level=minimal:
		 *
		 * A) Unlogged relation
		 *
		 *    Unlogged relations will go away on crash, but they need to be
		 *    fsync'd on a clean shutdown. It's sufficient to call
		 *    smgrregistersync(), that ensures that the checkpointer will
		 *    flush it at the shutdown checkpoint. (It will flush it on the
		 *    next online checkpoint too, which is not strictly necessary.)
		 *
		 *    Note that the init-fork of an unlogged relation is not
		 *    considered unlogged for our purposes. It's treated like a
		 *    regular permanent relation. The callers will pass use_wal=true
		 *    for the init fork.
		 *
		 * B) Permanent relation, WAL-logging skipped because wal_level=minimal
		 *
		 *    This is a new relation, and we didn't WAL-log the pages as we
		 *    wrote, but they need to be fsync'd before commit.
		 *
		 *    We don't need to do that here, however. The fsync() is done at
		 *    commit, by smgrDoPendingSyncs() (*).
		 *
		 *    (*) smgrDoPendingSyncs() might decide to WAL-log the whole
		 *    relation at commit instead of fsyncing it, if the relation was
		 *    very small, but it's smgrDoPendingSyncs() responsibility in any
		 *    case.
		 *
		 * We cannot distinguish the two here, so conservatively assume it's
		 * an unlogged relation. A permanent relation with wal_level=minimal
		 * would require no actions, see above.
		 */
		smgrregistersync(bulkstate->smgr, bulkstate->forknum);
	}
	else
	{
		/*
		 * Permanent relation, WAL-logged normally.
		 *
		 * We already WAL-logged all the pages, so they will be replayed from
		 * WAL on crash. However, when we wrote out the pages, we passed
		 * skipFsync=true to avoid the overhead of registering all the writes
		 * with the checkpointer.  Register the whole relation now.
		 *
		 * There is one hole in that idea: If a checkpoint occurred while we
		 * were writing the pages, it already missed fsyncing the pages we had
		 * written before the checkpoint started.  A crash later on would
		 * replay the WAL starting from the checkpoint, therefore it wouldn't
		 * replay our earlier WAL records.  So if a checkpoint started after
		 * the bulk write, fsync the files now.
		 */

		/*
		 * Prevent a checkpoint from starting between the GetRedoRecPtr() and
		 * smgrregistersync() calls.
		 */
		Assert((MyProc->delayChkptFlags & DELAY_CHKPT_START) == 0);
		MyProc->delayChkptFlags |= DELAY_CHKPT_START;

		if (bulkstate->start_RedoRecPtr != GetRedoRecPtr())
		{
			/*
			 * A checkpoint occurred and it didn't know about our writes, so
			 * fsync() the relation ourselves.
			 */
			MyProc->delayChkptFlags &= ~DELAY_CHKPT_START;
			smgrimmedsync(bulkstate->smgr, bulkstate->forknum);
			elog(DEBUG1, "flushed relation because a checkpoint occurred concurrently");
		}
		else
		{
			smgrregistersync(bulkstate->smgr, bulkstate->forknum);
			MyProc->delayChkptFlags &= ~DELAY_CHKPT_START;
		}
	}
}

/*
 * buffer_cmp (中文)按块号升序比较两条待写页记录(qsort 比较函数)
 *
 * 【作用】smgr_bulk_flush() 在对待写队列排序时使用。排序的目的:
 * 1) 使 smgrextend() 按块号顺序扩展,减少磁盘寻道、避免文件碎片;
 * 2) 使 WAL 记录中的块号单调递增,便于重放。
 *
 * 【设计思想】同一个块在一次批量操作中只允许写一次(见 smgr_bulk_write()
 * 的注释),因此理论上不会出现 blkno 相等的情况;这里用 Assert 把这种
 * 编程错误挡在调试构建里,生产构建中该分支不可能触发。
 *
 * 【参数】a、b —— 指向两条 PendingWrite 记录的指针。
 * 【返回值】a 的块号大于 b 返回 1,否则返回 -1。
 */
static int
buffer_cmp(const void *a, const void *b)
{
	const PendingWrite *bufa = (const PendingWrite *) a;
	const PendingWrite *bufb = (const PendingWrite *) b;

	/* We should not see duplicated writes for the same block */
	Assert(bufa->blkno != bufb->blkno);
	if (bufa->blkno > bufb->blkno)
		return 1;
	else
		return -1;
}

/*
 * smgr_bulk_flush (中文)把待写队列中的所有页一次性刷出(WAL + 写盘)
 *
 * 【作用】把 pending_writes[] 队列清空:若启用 WAL,先用 log_newpages()
 * 把整批页(最多 MAX_PENDING_WRITES 页)合并成一条 WAL 记录;随后逐页
 * 写盘:
 * - 块号 >= relsize(超出当前 EOF):smgrextend() 扩展文件。若出现
 *   "跳跃"(目标块号比 relsize 大出不止一块),先用 zero_buffer 垫出
 *   中间的全零页(不写 WAL、不算校验和,只为避免文件碎片);
 * - 块号 < relsize(覆写已有的块):smgrwrite()。
 * 所有写都带 skipFsync=true(可靠性由 smgr_bulk_finish() 统一负责)。
 * 每页写完即 pfree 释放,最后把 npending 清零。
 *
 * 【设计思想】把多页打包进一条 WAL 记录是本文件的核心优化:每条 WAL
 * 记录都有固定头开销,批量合并后平均每页的开销降到接近零。排序在写盘
 * 之前完成,使扩展尽量连续。注意队列满时(smgr_bulk_write())也会主动
 * 调用本函数,因此"批"的边界完全由队列容量决定,与调用频率无关。
 *
 * 【参数】bulkstate —— 批量写入状态。
 * 【返回值】无。
 *
 * Finish all the pending writes.
 */
static void
smgr_bulk_flush(BulkWriteState *bulkstate)
{
	int			npending = bulkstate->npending;
	PendingWrite *pending_writes = bulkstate->pending_writes;

	if (npending == 0)
		return;

	if (npending > 1)
		qsort(pending_writes, npending, sizeof(PendingWrite), buffer_cmp);

	if (bulkstate->use_wal)
	{
		BlockNumber blknos[MAX_PENDING_WRITES];
		Page		pages[MAX_PENDING_WRITES];
		bool		page_std = true;

		for (int i = 0; i < npending; i++)
		{
			blknos[i] = pending_writes[i].blkno;
			pages[i] = pending_writes[i].buf->data;

			/*
			 * If any of the pages use !page_std, we log them all as such.
			 * That's a bit wasteful, but in practice, a mix of standard and
			 * non-standard page layout is rare.  None of the built-in AMs do
			 * that.
			 */
			if (!pending_writes[i].page_std)
				page_std = false;
		}
		log_newpages(&bulkstate->smgr->smgr_rlocator.locator, bulkstate->forknum,
					 npending, blknos, pages, page_std);
	}

	for (int i = 0; i < npending; i++)
	{
		BlockNumber blkno = pending_writes[i].blkno;
		Page		page = pending_writes[i].buf->data;

		PageSetChecksum(page, blkno);

		if (blkno >= bulkstate->relsize)
		{
			/*
			 * If we have to write pages nonsequentially, fill in the space
			 * with zeroes until we come back and overwrite.  This is not
			 * logically necessary on standard Unix filesystems (unwritten
			 * space will read as zeroes anyway), but it should help to avoid
			 * fragmentation.  The dummy pages aren't WAL-logged though.
			 */
			while (blkno > bulkstate->relsize)
			{
				/* don't set checksum for all-zero page */
				smgrextend(bulkstate->smgr, bulkstate->forknum,
						   bulkstate->relsize,
						   &zero_buffer,
						   true);
				bulkstate->relsize++;
			}

			smgrextend(bulkstate->smgr, bulkstate->forknum, blkno, page, true);
			bulkstate->relsize++;
		}
		else
			smgrwrite(bulkstate->smgr, bulkstate->forknum, blkno, page, true);
		pfree(page);
	}

	bulkstate->npending = 0;
}

/*
 * smgr_bulk_write (中文)把一页加入待写队列
 *
 * 【作用】批量加载过程中,每构造好一页(如 COPY 攒满的一页元组),调用
 * 本函数排队;队列攒满 MAX_PENDING_WRITES 页时立即触发一次
 * smgr_bulk_flush()。
 *
 * 【所有权约定】本函数取得 buf 的所有权:它不再属于调用方,后续由
 * smgr_bulk_flush() 负责释放;调用方不得再次使用或释放该缓冲。
 * 【约束】同一块在一次批量操作内只能写一次(队列没有重复检测,违反
 * 约定会破坏 WAL 重放的不变性;调试构建由 buffer_cmp 的 Assert 兜底)。
 *
 * 【参数】
 *   bulkstate —— 批量写入状态;
 *   blocknum  —— 目标块号;
 *   buf       —— 待写的页(smgr_bulk_get_buf() 分配的缓冲,所有权转移);
 *   page_std  —— 该页是否为标准页布局(影响 WAL 记录的记录方式)。
 * 【返回值】无。
 *
 * Queue write of 'buf'.
 *
 * NB: this takes ownership of 'buf'!
 *
 * You are only allowed to write a given block once as part of one bulk write
 * operation.
 */
void
smgr_bulk_write(BulkWriteState *bulkstate, BlockNumber blocknum, BulkWriteBuffer buf, bool page_std)
{
	PendingWrite *w;

	w = &bulkstate->pending_writes[bulkstate->npending++];
	w->buf = buf;
	w->blkno = blocknum;
	w->page_std = page_std;

	if (bulkstate->npending == MAX_PENDING_WRITES)
		smgr_bulk_flush(bulkstate);
}

/*
 * smgr_bulk_get_buf (中文)分配一个可写入的页缓冲
 *
 * 【作用】批量加载时用来构造页内容的临时缓冲:按 I/O 对齐要求分配
 * BLCKSZ 字节(直接 I/O 等路径要求对齐),在当前实现里就是一次简单的
 * 对齐 palloc,未来可能改成环形缓冲或大块分段分配,因此调用方不要
 * 依赖其内部实现。
 *
 * 【所有权】没有独立的释放函数:把缓冲传给 smgr_bulk_write() 后所有权
 * 转移,由 smgr_bulk_flush() 在写完该页后释放。
 *
 * 【参数】bulkstate —— 批量写入状态(决定分配的内存上下文)。
 * 【返回值】新分配的页缓冲(BulkWriteBuffer)。
 *
 * Allocate a new buffer which can later be written with smgr_bulk_write().
 *
 * There is no function to free the buffer.  When you pass it to
 * smgr_bulk_write(), it takes ownership and frees it when it's no longer
 * needed.
 *
 * This is currently implemented as a simple palloc, but could be implemented
 * using a ring buffer or larger chunks in the future, so don't rely on it.
 */
BulkWriteBuffer
smgr_bulk_get_buf(BulkWriteState *bulkstate)
{
	return MemoryContextAllocAligned(bulkstate->memcxt, BLCKSZ, PG_IO_ALIGN_SIZE, 0);
}
