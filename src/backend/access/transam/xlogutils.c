/*-------------------------------------------------------------------------
 *
 * xlogutils.c
 *
 * PostgreSQL write-ahead log manager utility routines
 *
 * This file contains support routines that are used by XLOG replay functions.
 * None of this code is used during normal system operation.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/xlogutils.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件提供 WAL redo（重做）阶段使用的底层工具函数。虽然文件名带有 xlog，
 * 但它并不负责 WAL 的写入、刷盘或归档，而是为各个资源管理器（RMGR）的 redo
 * 回调以及 WAL reader 提供“读取 buffer、校验页面、处理异常页面、读取 WAL 文件”
 * 的基础设施。
 *
 * 主要职责：
 *   1. 读取 redo 需要的 buffer：XLogReadBufferForRedo() /
 *      XLogReadBufferForRedoExtended() 根据 WAL record 中的 block reference
 *      （backup block）定位 page，必要时用 FPI（full-page image）覆盖页面，
 *      并根据 page header 中的 LSN 判断该记录是否已经重放；
 *   2. 恢复中的锁与失效处理：redo 期间需要独占锁（Hot Standby 下还可能使用
 *      cleanup lock），即使页面无需重做也要返回已加锁的 buffer，供
 *      MarkBufferDirty() 等接口使用；对 invalid page 的引用则记录到本地 hash
 *      表，等待后续 DROP/TRUNCATE 解释；
 *   3. backup block 处理：识别 BKPBLOCK_WILL_INIT、BKPIMAGE_APPLY 等标志，
 *      保证 redo 例程与 WAL record 描述一致，并在恢复 FPI 时设置 page LSN；
 *   4. 页头 LSN 校验：用 record->EndRecPtr 与 PageGetLSN() 比较，决定
 *      BLK_DONE 还是 BLK_NEEDS_REDO，从而支持幂等（idempotent）重放；
 *   5. 无效页处理：报告页面“不存在”或“存在但未初始化”，并在恢复到达一致点
 *      时做最终检查；
 *   6. WAL 文件读取辅助：提供 XLogReaderRoutine 的 segment_open/segment_close/
 *      page_read 回调（wal_segment_open、wal_segment_close、
 *      read_local_xlog_page 等），以及 timeline 选择逻辑
 *      XLogReadDetermineTimeline()；
 *   7. 构造“假” relcache 项（CreateFakeRelcacheEntry），让 redo 代码可以复用
 *      依赖 Relation 的底层存储接口。
 *
 * 与其他 xlog 模块的关系：
 *   - xlog.c / xlogrecovery.c 负责 WAL 的物理写入、恢复主循环、checkpoint 和
 *     timeline 管理；本文件向它们提供页面级 redo 工具，并从它们读取
 *     InRecovery、reachedConsistency 等全局状态；
 *   - xlogreader.c 定义 XLogReaderState 与 XLogReaderRoutine；本文件实现其中
 *     面向本地 pg_wal 目录的 routine 回调，也被 logical decoding、两阶段提交
 *     检查、repack_worker 等复用；
 *   - 各 RMGR（heap、btree、hash、xact、sequence 等）的 redo 回调调用本文件的
 *     XLogReadBufferForRedo()/XLogInitBufferForRedo() 获取待修改页面；
 *   - smgr.c 提供实际的段文件与 buffer 管理；本文件通过 smgropen()、
 *     ReadBufferWithoutRelcache()、ExtendBufferedRelTo() 等接口访问存储层。
 *
 * 设计思想：
 *   - redo 必须幂等：通过 page LSN 判断记录是否已应用，并优先信任经过 CRC
 *     校验的 WAL 中的 FPI，而不是可能因掉电而损坏的数据库页面；
 *   - 恢复期间假定“只有 startup 进程在写页面”，因此可以省去某些锁和
 *     relcache 查找；但 Hot Standby 下仍有只读后端并发访问，buffer 锁不可省略；
 *   - 对“引用了已删除/已截断对象”的 WAL 记录采取延迟判定：先记录，等恢复结束
 *     或到达一致点时再确认是否真的缺少 DROP/TRUNCATE，避免误报；
 *   - 尽量让 redo 代码与正常路径共享底层接口，减少两套实现之间的语义差异。
 */
#include "postgres.h"

#include <unistd.h>

#include "access/timeline.h"
#include "access/xlogrecovery.h"
#include "access/xlog_internal.h"
#include "access/xlogutils.h"
#include "miscadmin.h"
#include "storage/fd.h"
#include "storage/smgr.h"
#include "utils/hsearch.h"
#include "utils/rel.h"


/* GUC variable */
/*
 * 中文注释：
 * GUC 参数 ignore_invalid_pages（对应 postgresql.conf 中的同名选项）。默认 false：
 * 当 WAL 引用了不存在或未初始化的页面，且恢复已经到达一致点（reachedConsistency）
 * 时，直接 PANIC，防止带着不一致的数据继续运行。设为 true 时降级为 WARNING，
 * 仅用于紧急抢救数据；这会让恢复在页面缺失的情况下继续，因此可能造成数据丢失
 * 或更隐蔽的后续错误，生产环境不应随意开启。该变量只在 startup 进程的 redo
 * 路径中被读取。
 */
bool		ignore_invalid_pages = false;

/*
 * Are we doing recovery from XLOG?
 *
 * This is only ever true in the startup process; it should be read as meaning
 * "this process is replaying WAL records", rather than "the system is in
 * recovery mode".  It should be examined primarily by functions that need
 * to act differently when called from a WAL redo function (e.g., to skip WAL
 * logging).  To check whether the system is in recovery regardless of which
 * process you're running in, use RecoveryInProgress() but only after shared
 * memory startup and lock initialization.
 *
 * This is updated from xlog.c and xlogrecovery.c, but lives here because
 * it's mostly read by WAL redo functions.
 */
/*
 * 中文注释：
 * 是否正在从 WAL 重放记录。该标志只在 startup 进程中为 true，语义是“本进程
 * 正在 replay WAL records”，而不是“系统处于 recovery 模式”。因此它主要供
 * redo 函数判断是否需要跳过 WAL 日志、是否可以使用恢复期专用捷径（例如不取
 * relation extension lock）；其他进程若想判断系统是否在恢复，应调用
 * RecoveryInProgress()，且必须在共享内存和锁初始化完成之后。
 *
 * 该变量由 xlog.c / xlogrecovery.c 在恢复开始和结束时更新，但定义放在本文件，
 * 因为主要读者是 WAL redo 函数。它不是原子变量：仅在 startup 进程内单线程
 * 读写，其他进程不应依赖它。
 */
bool		InRecovery = false;

/* Are we in Hot Standby mode? Only valid in startup process, see xlogutils.h */
/*
 * 中文注释：
 * Hot Standby 状态机，仅对 startup 进程有意义，取值见 xlogutils.h 中的
 * HotStandbyState（STANDBY_DISABLED / STANDBY_INITIALIZED /
 * STANDBY_SNAPSHOT_PENDING / STANDBY_SNAPSHOT_READY）。宏 InHotStandby 通过
 * standbyState >= STANDBY_SNAPSHOT_PENDING 判断是否已进入 Hot Standby 模式
 * （快照就绪后才真正向只读查询提供服务）。
 * 状态迁移由 xlogrecovery.c 控制；redo 路径据此决定是否必须严格遵守并发安全
 * （例如 buffer 锁、cleanup lock）以及是否允许某些恢复期捷径。
 */
HotStandbyState standbyState = STANDBY_DISABLED;

/*
 * During XLOG replay, we may see XLOG records for incremental updates of
 * pages that no longer exist, because their relation was later dropped or
 * truncated.  (Note: this is only possible when full_page_writes = OFF,
 * since when it's ON, the first reference we see to a page should always
 * be a full-page rewrite not an incremental update.)  Rather than simply
 * ignoring such records, we make a note of the referenced page, and then
 * complain if we don't actually see a drop or truncate covering the page
 * later in replay.
 */
/*
 * 中文注释：
 * invalid-page hash table 的 key：用物理位置（RelFileLocator + fork + block
 * number）唯一标识一个被 WAL record 引用的页面。hash 表以 HASH_BLOBS 方式按
 * 字节比较 key，因此结构体中不能有未初始化的 padding（见 log_invalid_page()
 * 的注释）；这三个字段恰好紧凑排列，没有填充字节。
 */
typedef struct xl_invalid_page_key
{
	RelFileLocator locator;		/* the relation */
	ForkNumber	forkno;			/* the fork number */
	BlockNumber blkno;			/* the page */
} xl_invalid_page_key;

/*
 * 中文注释：
 * invalid-page hash table 的 value。key 必须位于结构体第一个字段，以满足
 * dynahash 对定长 entry 的布局要求。present 记录该页面的实际状态：
 *   - false：页面在文件中根本不存在（blkno >= smgrnblocks）；
 *   - true ：页面存在但内容全零（PageIsNew() 为真，即未初始化）。
 * 该标志只用于生成更精确的错误信息；重复引用同一页面时保留首次观察到的值。
 */
typedef struct xl_invalid_page
{
	xl_invalid_page_key key;	/* hash key ... must be first */
	bool		present;		/* page existed but contained zeroes */
} xl_invalid_page;

/*
 * 中文注释：
 * 记录恢复过程中遇到的 invalid page 引用的本地 hash table，仅在 startup 进程
 * 内使用，因此不需要加锁，也不会出现在共享内存中。表在第一次遇到 invalid
 * page 时才惰性创建（见 log_invalid_page()），初始容量 100，key 为
 * xl_invalid_page_key，value 为 xl_invalid_page。
 *
 * 生命周期：恢复过程中累积；遇到 DROP/TRUNCATE 时由 forget_invalid_pages() /
 * forget_invalid_pages_db() 删除对应条目；到达一致点时由
 * XLogCheckInvalidPages() 检查并销毁。若在到达一致点之后仍有引用，
 * log_invalid_page() 会立即报错，避免把问题拖到恢复结束。
 */
static HTAB *invalid_page_tab = NULL;

/*
 * 中文注释：
 * read_local_xlog_page_guts() 的前置声明。公开的 read_local_xlog_page() 与
 * read_local_xlog_page_no_wait() 只是对它的薄封装，区别仅在于是否等待尚未
 * 产生的 WAL。
 */
static int	read_local_xlog_page_guts(XLogReaderState *state, XLogRecPtr targetPagePtr,
									  int reqLen, XLogRecPtr targetRecPtr,
									  char *cur_page, bool wait_for_wal);

/* Report a reference to an invalid page */
/*
 * 中文注释：
 * 以指定错误级别报告一次 invalid page 引用，错误文本区分两种情形：
 *   present == true ：页面存在但未初始化（全零），报 "is uninitialized"；
 *   present == false：页面在关系中不存在，报 "does not exist"。
 *
 * 参数：
 *   elevel  —— elog 级别（DEBUG1/WARNING/PANIC 等），由调用者决定严重程度；
 *   locator —— 关系的物理定位符；
 *   forkno  —— fork 编号（MAIN_FORKNUM/INIT_FORKNUM/FSM/VISIBILITYMAP）；
 *   blkno   —— 块号；
 *   present —— 页面是否存在但全零。
 *
 * 副作用：通过 relpathperm() 构造用于显示的相对路径；elog 可能不返回（PANIC
 * 或达到 log_min_messages 时写日志）。本函数不修改任何恢复状态，可在报错路径
 * 中安全调用。relpathperm() 返回的是栈上结构体，不涉及 palloc。
 */
static void
report_invalid_page(int elevel, RelFileLocator locator, ForkNumber forkno,
					BlockNumber blkno, bool present)
{
	RelPathStr	path = relpathperm(locator, forkno);

	if (present)
		elog(elevel, "page %u of relation %s is uninitialized",
			 blkno, path.str);
	else
		elog(elevel, "page %u of relation %s does not exist",
			 blkno, path.str);
}

/* Log a reference to an invalid page */
/*
 * 中文注释：
 * 记录（或报告）一次对 invalid page 的引用。调用者通常是
 * XLogReadBufferExtended()：当 redo 需要读取的页面不存在或全零时调用。
 *
 * 关键行为：
 *   1. 若 reachedConsistency 已经为 true，说明数据库已处于一致状态，此时再
 *      出现 invalid page 引用就是严重错误：先以 WARNING 输出页面信息，然后
 *      根据 ignore_invalid_pages 决定 PANIC 还是 WARNING。这样比把条目留在
 *      hash 表里等到恢复结束再报错更及时，尤其是 standby 可能长期运行的情况。
 *   2. 若 DEBUG1 级别的日志是感兴趣的，输出一条 DEBUG1 记录，便于借助 elog
 *      的上下文（当前正在重放的 WAL record）追踪问题来源。
 *   3. 惰性创建 invalid_page_tab，并把 (locator, forkno, blkno) 插入表中。
 *      重复引用时保留第一次记录下来的 present 值，因为首次观察更能反映页面
 *      当时的状态。
 *
 * 参数：locator/forkno/blkno 标识页面；present 表示页面是“存在但全零”(true)
 * 还是“不存在”(false)。
 *
 * 并发/恢复注意：本函数只在 startup 进程的 redo 路径中调用，invalid_page_tab
 * 是进程私有数据，无需加锁。hash_create 未指定 HASH_CONTEXT，因此表和表项
 * 使用当前内存上下文创建；表项在恢复结束或 DROP/TRUNCATE 时清除。
 */
static void
log_invalid_page(RelFileLocator locator, ForkNumber forkno, BlockNumber blkno,
				 bool present)
{
	xl_invalid_page_key key;
	xl_invalid_page *hentry;
	bool		found;

	/*
	 * Once recovery has reached a consistent state, the invalid-page table
	 * should be empty and remain so. If a reference to an invalid page is
	 * found after consistency is reached, PANIC immediately. This might seem
	 * aggressive, but it's better than letting the invalid reference linger
	 * in the hash table until the end of recovery and PANIC there, which
	 * might come only much later if this is a standby server.
	 */
	if (reachedConsistency)
	{
		report_invalid_page(WARNING, locator, forkno, blkno, present);
		elog(ignore_invalid_pages ? WARNING : PANIC,
			 "WAL contains references to invalid pages");
	}

	/*
	 * Log references to invalid pages at DEBUG1 level.  This allows some
	 * tracing of the cause (note the elog context mechanism will tell us
	 * something about the XLOG record that generated the reference).
	 */
	if (message_level_is_interesting(DEBUG1))
		report_invalid_page(DEBUG1, locator, forkno, blkno, present);

	if (invalid_page_tab == NULL)
	{
		/* create hash table when first needed */
		HASHCTL		ctl;

		ctl.keysize = sizeof(xl_invalid_page_key);
		ctl.entrysize = sizeof(xl_invalid_page);

		invalid_page_tab = hash_create("XLOG invalid-page table",
									   100,
									   &ctl,
									   HASH_ELEM | HASH_BLOBS);
	}

	/* we currently assume xl_invalid_page_key contains no padding */
	key.locator = locator;
	key.forkno = forkno;
	key.blkno = blkno;
	hentry = (xl_invalid_page *)
		hash_search(invalid_page_tab, &key, HASH_ENTER, &found);

	if (!found)
	{
		/* hash_search already filled in the key */
		hentry->present = present;
	}
	else
	{
		/* repeat reference ... leave "present" as it was */
	}
}

/* Forget any invalid pages >= minblkno, because they've been dropped */
/*
 * 中文注释：
 * 当重放 DROP/TRUNCATE 类记录时，删除 invalid_page_tab 中所有属于指定关系、
 * 指定 fork、且块号 >= minblkno 的条目，表示这些页面“已经被合法地丢弃”，
 * 后续不应再被判定为悬空引用。
 *
 * 参数：locator/forkno 定位关系与 fork；minblkno 是截断后的新块数，因此
 * blkno >= minblkno 的页面都已不存在。DROP 场景由 XLogDropRelation() 传入 0。
 *
 * 实现：用 hash_seq_search() 顺序扫描并在扫描过程中 HASH_REMOVE。dynahash 允许
 * 在 seq scan 中删除当前条目。若 hash 表尚未创建则直接返回。
 *
 * 并发：仅在 startup 进程内调用，无并发问题；DEBUG2 日志用于追踪清理过程。
 */
static void
forget_invalid_pages(RelFileLocator locator, ForkNumber forkno,
					 BlockNumber minblkno)
{
	HASH_SEQ_STATUS status;
	xl_invalid_page *hentry;

	if (invalid_page_tab == NULL)
		return;					/* nothing to do */

	hash_seq_init(&status, invalid_page_tab);

	while ((hentry = (xl_invalid_page *) hash_seq_search(&status)) != NULL)
	{
		if (RelFileLocatorEquals(hentry->key.locator, locator) &&
			hentry->key.forkno == forkno &&
			hentry->key.blkno >= minblkno)
		{
			elog(DEBUG2, "page %u of relation %s has been dropped",
				 hentry->key.blkno,
				 relpathperm(hentry->key.locator, forkno).str);

			if (hash_search(invalid_page_tab,
							&hentry->key,
							HASH_REMOVE, NULL) == NULL)
				elog(ERROR, "hash table corrupted");
		}
	}
}

/* Forget any invalid pages in a whole database */
/*
 * 中文注释：
 * DROP DATABASE 的 redo 辅助函数：删除 invalid_page_tab 中所有 dbOid 等于
 * dbid 的条目。与 forget_invalid_pages() 不同，这里按数据库而非具体关系过滤，
 * 因为整个数据库下的所有页面都会随目录删除而失效。
 *
 * 参数 dbid：被删除数据库的 OID。实现同样是 hash 顺序扫描 + HASH_REMOVE；
 * 表不存在时直接返回。只在 startup 进程内执行，无并发问题。
 */
static void
forget_invalid_pages_db(Oid dbid)
{
	HASH_SEQ_STATUS status;
	xl_invalid_page *hentry;

	if (invalid_page_tab == NULL)
		return;					/* nothing to do */

	hash_seq_init(&status, invalid_page_tab);

	while ((hentry = (xl_invalid_page *) hash_seq_search(&status)) != NULL)
	{
		if (hentry->key.locator.dbOid == dbid)
		{
			elog(DEBUG2, "page %u of relation %s has been dropped",
				 hentry->key.blkno,
				 relpathperm(hentry->key.locator, hentry->key.forkno).str);

			if (hash_search(invalid_page_tab,
							&hentry->key,
							HASH_REMOVE, NULL) == NULL)
				elog(ERROR, "hash table corrupted");
		}
	}
}

/* Are there any unresolved references to invalid pages? */
/*
 * 中文注释：
 * 判断 invalid_page_tab 中是否还有未解决的 invalid page 引用。
 *
 * 调用场景：xlog.c 的 RecoveryRestartPoint() 在决定是否记录 restartpoint
 * 之前调用。如果存在未解决的引用，就不能在此处建立 restartpoint：从该
 * restartpoint 重新恢复时将看不到这些引用，也就失去了“这些页面应当被后续
 * DROP/TRUNCATE 覆盖”的交叉校验。
 *
 * 返回值：表存在且条目数 > 0 时返回 true，否则 false（包括表尚未创建的情况）。
 * 无副作用；只在 startup 进程内调用，不需要加锁。
 */
bool
XLogHaveInvalidPages(void)
{
	if (invalid_page_tab != NULL &&
		hash_get_num_entries(invalid_page_tab) > 0)
		return true;
	return false;
}

/* Complain about any remaining invalid-page entries */
/*
 * 中文注释：
 * 在恢复即将到达一致点时做最终检查（xlogrecovery.c 在把 reachedConsistency
 * 置为 true 之前调用）：如果 invalid_page_tab 中仍有条目，说明 WAL 引用了
 * 不存在的页面，但后面没有相应的 DROP/TRUNCATE 记录来解释，数据可能存在
 * 不一致。
 *
 * 处理策略：先对每个剩余条目发出 WARNING，把所有可用信息都打印出来，最后再
 * 根据 ignore_invalid_pages 决定 PANIC 还是 WARNING。这样即使进程随后终止，
 * 日志里也能看到完整的页面列表。
 *
 * 副作用：销毁 hash 表并把 invalid_page_tab 置为 NULL。此后若再出现 invalid
 * page 引用，log_invalid_page() 会因 reachedConsistency 为 true 而立即报错。
 *
 * 调用场景：xlogrecovery.c 在确认到达一致点、且没有 backupEndRequired 时调用。
 * 只在 startup 进程内执行。
 */
void
XLogCheckInvalidPages(void)
{
	HASH_SEQ_STATUS status;
	xl_invalid_page *hentry;
	bool		foundone = false;

	if (invalid_page_tab == NULL)
		return;					/* nothing to do */

	hash_seq_init(&status, invalid_page_tab);

	/*
	 * Our strategy is to emit WARNING messages for all remaining entries and
	 * only PANIC after we've dumped all the available info.
	 */
	while ((hentry = (xl_invalid_page *) hash_seq_search(&status)) != NULL)
	{
		report_invalid_page(WARNING, hentry->key.locator, hentry->key.forkno,
							hentry->key.blkno, hentry->present);
		foundone = true;
	}

	if (foundone)
		elog(ignore_invalid_pages ? WARNING : PANIC,
			 "WAL contains references to invalid pages");

	hash_destroy(invalid_page_tab);
	invalid_page_tab = NULL;
}


/*
 * XLogReadBufferForRedo
 *		Read a page during XLOG replay
 *
 * Reads a block referenced by a WAL record into shared buffer cache, and
 * determines what needs to be done to redo the changes to it.  If the WAL
 * record includes a full-page image of the page, it is restored.
 *
 * 'record.EndRecPtr' is compared to the page's LSN to determine if the record
 * has already been replayed.  'block_id' is the ID number the block was
 * registered with, when the WAL record was created.
 *
 * Returns one of the following:
 *
 *	BLK_NEEDS_REDO	- changes from the WAL record need to be applied
 *	BLK_DONE		- block doesn't need replaying
 *	BLK_RESTORED	- block was restored from a full-page image included in
 *					  the record
 *	BLK_NOTFOUND	- block was not found (because it was truncated away by
 *					  an operation later in the WAL stream)
 *
 * On return, the buffer is locked in exclusive-mode, and returned in *buf.
 * Note that the buffer is locked and returned even if it doesn't need
 * replaying.  (Getting the buffer lock is not really necessary during
 * single-process crash recovery, but some subroutines such as MarkBufferDirty
 * will complain if we don't have the lock.  In hot standby mode it's
 * definitely necessary.)
 *
 * Note: when a backup block is available in XLOG with the BKPIMAGE_APPLY flag
 * set, we restore it, even if the page in the database appears newer.  This
 * is to protect ourselves against database pages that were partially or
 * incorrectly written during a crash.  We assume that the XLOG data must be
 * good because it has passed a CRC check, while the database page might not
 * be.  This will force us to replay all subsequent modifications of the page
 * that appear in XLOG, rather than possibly ignoring them as already
 * applied, but that's not a huge drawback.
 */
/*
 * 中文注释：
 * redo 例程读取页面并判断是否需要重做的主要入口，等价于以 RBM_NORMAL 模式、
 * 不获取 cleanup lock 调用 XLogReadBufferForRedoExtended()。
 *
 * 参数：
 *   record   —— 当前正在重放的 WAL record（XLogReaderState）；
 *   block_id —— 该页面在 WAL record 中注册时的 block ID（从 0 开始）；
 *   buf      —— 输出参数，返回 pinned 且已加独占锁的 buffer；若返回
 *               BLK_NOTFOUND，则为 InvalidBuffer。
 *
 * 返回值（XLogRedoAction）：
 *   BLK_NEEDS_REDO —— WAL record 的修改尚未应用，需要调用者继续修改页面；
 *   BLK_DONE       —— 页面 LSN 已 >= record->EndRecPtr，无需重做；
 *   BLK_RESTORED   —— 已用 record 中的 FPI 恢复页面，无需再应用增量修改；
 *   BLK_NOTFOUND   —— 页面不存在（已被后续 DROP/TRUNCATE 删除），调用者应跳过。
 *
 * 恢复/并发注意：无论是否需要重做，只要 buffer 有效就处于独占锁定状态，调用者
 * 必须 UnlockReleaseBuffer()。crash recovery 中单进程运行时锁并非绝对必要，但
 * MarkBufferDirty() 等接口要求持锁；Hot Standby 下则有只读后端并发访问，锁是
 * 正确性所必需的。
 */
XLogRedoAction
XLogReadBufferForRedo(XLogReaderState *record, uint8 block_id,
					  Buffer *buf)
{
	return XLogReadBufferForRedoExtended(record, block_id, RBM_NORMAL,
										 false, buf);
}

/*
 * Pin and lock a buffer referenced by a WAL record, for the purpose of
 * re-initializing it.
 */
/*
 * 中文注释：
 * 为“重新初始化页面”的 redo 例程获取 buffer：以 RBM_ZERO_AND_LOCK 模式读取，
 * 页面不存在时把关系扩展到目标块号并返回全零页面，返回值总是 pinned 且已加
 * 独占锁的 buffer。
 *
 * 参数：record/block_id 指定 WAL record 中的 block reference。
 * 返回值：有效的 Buffer；零模式下 XLogReadBufferForRedoExtended() 保证返回
 * BLK_NEEDS_REDO，所以这里忽略其返回值。
 *
 * 使用约束：对应的 WAL record 必须带 BKPBLOCK_WILL_INIT 标志，否则
 * XLogReadBufferForRedoExtended() 会 PANIC。调用者负责填充页面内容、设置
 * page LSN、MarkBufferDirty()，最后 UnlockReleaseBuffer()。
 *
 * 典型调用者：seq_redo()、btree/gist/spgist/gin 的初始化页 redo 等需要重建
 * 整页的例程。Hot Standby
 * 下可能有读者并发扫描该页面，因此重写页面时应先在本地构造内容再整体拷贝，
 * 避免读者看到半成品（参见 sequence_xlog.c 的注释）。
 */
Buffer
XLogInitBufferForRedo(XLogReaderState *record, uint8 block_id)
{
	Buffer		buf;

	XLogReadBufferForRedoExtended(record, block_id, RBM_ZERO_AND_LOCK, false,
								  &buf);
	return buf;
}

/*
 * If a redo routine modified an init fork, flush the buffer immediately.
 *
 * At the end of crash recovery the init forks of unlogged relations are
 * copied to the main fork directly from disk, without going through shared
 * buffers. Therefore, redo routines that update init forks without
 * restoring a full-page image must call this after setting the page LSN and
 * marking the buffer dirty.
 */
/*
 * 中文注释：
 * 如果当前 block reference 指向 init fork，立即把 buffer 刷到磁盘。
 *
 * 背景：crash recovery 结束时，unlogged relation 的 init fork 会被直接按磁盘
 * 内容复制成 main fork，而不经过 shared buffers。因此 redo 例程对 init fork
 * 的修改必须在恢复结束前落盘，否则复制到 main fork 的可能是旧内容。
 *
 * 参数：
 *   record   —— 当前 WAL record；
 *   block_id —— 页面在 record 中的 block ID；
 *   buffer   —— 已经被 redo 例程修改、设置过 page LSN 并 MarkBufferDirty()
 *               的 buffer。
 *
 * 行为：通过 XLogRecGetBlockTag() 取出 forknum；仅当 forknum == INIT_FORKNUM
 * 时调用 FlushOneBuffer() 立即把它写出（FlushBuffer() 会先 XLogFlush 该 buffer
 * 的 LSN 之前的 WAL），其他 fork 什么也不做。
 *
 * 调用场景：redo 例程在“没有恢复 FPI、而是直接修改 init fork 页面”时必须调用
 * 本函数；如果走的是 FPI 恢复路径，XLogReadBufferForRedoExtended() 内部已经
 * 处理。注意调用时 buffer 必须仍然 pinned（通常还持锁），且调用者之后仍需
 * UnlockReleaseBuffer()。
 */
void
XLogFlushBufferForRedoIfInit(XLogReaderState *record, uint8 block_id,
							 Buffer buffer)
{
	ForkNumber	forknum;

	Assert(BufferIsValid(buffer));

	XLogRecGetBlockTag(record, block_id, NULL, &forknum, NULL);
	if (forknum == INIT_FORKNUM)
		FlushOneBuffer(buffer);
}

/*
 * XLogReadBufferForRedoExtended
 *		Like XLogReadBufferForRedo, but with extra options.
 *
 * In RBM_ZERO_* modes, if the page doesn't exist, the relation is extended
 * with all-zeroes pages up to the referenced block number.  In
 * RBM_ZERO_AND_LOCK and RBM_ZERO_AND_CLEANUP_LOCK modes, the return value
 * is always BLK_NEEDS_REDO.
 *
 * (The RBM_ZERO_AND_CLEANUP_LOCK mode is redundant with the get_cleanup_lock
 * parameter. Do not use an inconsistent combination!)
 *
 * If 'get_cleanup_lock' is true, a "cleanup lock" is acquired on the buffer
 * using LockBufferForCleanup(), instead of a regular exclusive lock.
 */
/*
 * 中文注释：
 * XLogReadBufferForRedo() 的通用实现，支持指定 ReadBufferMode 和是否获取
 * cleanup lock。
 *
 * 参数：
 *   record           —— 当前 WAL record；
 *   block_id         —— block reference ID；
 *   mode             —— RBM_NORMAL / RBM_ZERO_AND_LOCK /
 *                       RBM_ZERO_AND_CLEANUP_LOCK / RBM_NORMAL_NO_LOG；
 *   get_cleanup_lock —— true 时用 LockBufferForCleanup() 获取 cleanup lock，
 *                       而不是普通独占锁；
 *   buf              —— 输出 buffer。
 *
 * 处理流程：
 *   1. 用 XLogRecGetBlockTagExtended() 解析 locator/fork/blkno，并取得
 *      prefetch_buffer 提示；找不到 block 说明调用者传了错误的 block_id，PANIC。
 *   2. 校验 WILL_INIT 与 zero 模式必须成对出现：带 BKPBLOCK_WILL_INIT 的块
 *      必须由 redo 例程重新初始化（zero 模式），反之 zero 模式也必须对应
 *      WILL_INIT，否则 PANIC。这可以防止 WAL record 与 redo 代码不一致导致
 *      页面被错误清空。
 *   3. 若 BKPIMAGE_APPLY 为真（backup block 含应恢复的 FPI）：以
 *      RBM_ZERO_AND_LOCK（或 cleanup 版本）读取页面，用 RestoreBlockImage()
 *      覆盖页面内容；恢复失败则 ERROR。若页面不是全零（PageIsNew 为假），把
 *      page LSN 设为 record->EndRecPtr；然后 MarkBufferDirty()。对 init fork
 *      还要立即 FlushOneBuffer()，保证恢复结束时按磁盘复制 init fork 的
 *      正确性。返回 BLK_RESTORED。
 *   4. 否则按调用者给定的 mode 读取页面：buffer 有效时加锁（zero 模式在读取
 *      时已经加锁，不再重复加），比较 record->EndRecPtr 与 PageGetLSN()：
 *      lsn <= page LSN 说明记录已应用，返回 BLK_DONE；否则返回
 *      BLK_NEEDS_REDO。buffer 无效（页面不存在）则返回 BLK_NOTFOUND。
 *
 * 重要语义：
 *   - 只要返回的 buffer 有效，它就是 pinned 且独占锁定的，调用者必须释放；
 *   - 即使 FPI 对应的页面在磁盘上看起来更新，也仍然恢复 FPI。原因是 WAL 已经
 *     通过 CRC 校验，而数据库页面可能在崩溃时被部分写入（torn page）；宁可
 *     多重放后续修改，也不能信任可能损坏的页面；
 *   - 在 RBM_ZERO_AND_LOCK / RBM_ZERO_AND_CLEANUP_LOCK 模式下，新扩展的页面
 *     总是返回 BLK_NEEDS_REDO；
 *   - cleanup lock 用于需要等待所有 pin 释放的 redo（如 heap cleanup），普通
 *     独占锁不等待 pin，两者不能混用。
 *
 * 并发：crash recovery 中只有 startup 进程，Hot Standby 下需与只读后端并发，
 * 因此锁语义必须严格遵守；page LSN 的比较在持有 buffer 锁后进行。
 */
XLogRedoAction
XLogReadBufferForRedoExtended(XLogReaderState *record,
							  uint8 block_id,
							  ReadBufferMode mode, bool get_cleanup_lock,
							  Buffer *buf)
{
	XLogRecPtr	lsn = record->EndRecPtr;
	RelFileLocator rlocator;
	ForkNumber	forknum;
	BlockNumber blkno;
	Buffer		prefetch_buffer;
	Page		page;
	bool		zeromode;
	bool		willinit;

	if (!XLogRecGetBlockTagExtended(record, block_id, &rlocator, &forknum, &blkno,
									&prefetch_buffer))
	{
		/* Caller specified a bogus block_id */
		elog(PANIC, "failed to locate backup block with ID %d in WAL record",
			 block_id);
	}

	/*
	 * Make sure that if the block is marked with WILL_INIT, the caller is
	 * going to initialize it. And vice versa.
	 */
	zeromode = (mode == RBM_ZERO_AND_LOCK || mode == RBM_ZERO_AND_CLEANUP_LOCK);
	willinit = (XLogRecGetBlock(record, block_id)->flags & BKPBLOCK_WILL_INIT) != 0;
	if (willinit && !zeromode)
		elog(PANIC, "block with WILL_INIT flag in WAL record must be zeroed by redo routine");
	if (!willinit && zeromode)
		elog(PANIC, "block to be initialized in redo routine must be marked with WILL_INIT flag in the WAL record");

	/* If it has a full-page image and it should be restored, do it. */
	if (XLogRecBlockImageApply(record, block_id))
	{
		Assert(XLogRecHasBlockImage(record, block_id));
		*buf = XLogReadBufferExtended(rlocator, forknum, blkno,
									  get_cleanup_lock ? RBM_ZERO_AND_CLEANUP_LOCK : RBM_ZERO_AND_LOCK,
									  prefetch_buffer);
		page = BufferGetPage(*buf);
		if (!RestoreBlockImage(record, block_id, page))
			ereport(ERROR,
					(errcode(ERRCODE_INTERNAL_ERROR),
					 errmsg_internal("%s", record->errormsg_buf)));

		/*
		 * The page may be uninitialized. If so, we can't set the LSN because
		 * that would corrupt the page.
		 */
		if (!PageIsNew(page))
		{
			PageSetLSN(page, lsn);
		}

		MarkBufferDirty(*buf);

		/*
		 * At the end of crash recovery the init forks of unlogged relations
		 * are copied, without going through shared buffers. So we need to
		 * force the on-disk state of init forks to always be in sync with the
		 * state in shared buffers. Use XLogFlushBufferForRedoIfInit() for
		 * redo routines that dirty init-fork buffers without restoring a
		 * full-page image.
		 */
		if (forknum == INIT_FORKNUM)
			FlushOneBuffer(*buf);

		return BLK_RESTORED;
	}
	else
	{
		*buf = XLogReadBufferExtended(rlocator, forknum, blkno, mode, prefetch_buffer);
		if (BufferIsValid(*buf))
		{
			if (mode != RBM_ZERO_AND_LOCK && mode != RBM_ZERO_AND_CLEANUP_LOCK)
			{
				if (get_cleanup_lock)
					LockBufferForCleanup(*buf);
				else
					LockBuffer(*buf, BUFFER_LOCK_EXCLUSIVE);
			}
			if (lsn <= PageGetLSN(BufferGetPage(*buf)))
				return BLK_DONE;
			else
				return BLK_NEEDS_REDO;
		}
		else
			return BLK_NOTFOUND;
	}
}

/*
 * XLogReadBufferExtended
 *		Read a page during XLOG replay
 *
 * This is functionally comparable to ReadBufferExtended. There's some
 * differences in the behavior wrt. the "mode" argument:
 *
 * In RBM_NORMAL mode, if the page doesn't exist, or contains all-zeroes, we
 * return InvalidBuffer. In this case the caller should silently skip the
 * update on this page. (In this situation, we expect that the page was later
 * dropped or truncated. If we don't see evidence of that later in the WAL
 * sequence, we'll complain at the end of WAL replay.)
 *
 * In RBM_ZERO_* modes, if the page doesn't exist, the relation is extended
 * with all-zeroes pages up to the given block number.
 *
 * In RBM_NORMAL_NO_LOG mode, we return InvalidBuffer if the page doesn't
 * exist, and we don't check for all-zeroes.  Thus, no log entry is made
 * to imply that the page should be dropped or truncated later.
 *
 * Optionally, recent_buffer can be used to provide a hint about the location
 * of the page in the buffer pool; it does not have to be correct, but avoids
 * a buffer mapping table probe if it is.
 *
 * NB: A redo function should normally not call this directly. To get a page
 * to modify, use XLogReadBufferForRedoExtended instead. It is important that
 * all pages modified by a WAL record are registered in the WAL records, or
 * they will be invisible to tools that need to know which pages are modified.
 */
/*
 * 中文注释：
 * 恢复期间按物理位置读取一个页面，功能上类似 ReadBufferExtended()，但绕过
 * relcache，并针对 redo 场景调整了“页面不存在”时的行为。
 *
 * 参数：
 *   rlocator      —— 关系的 RelFileLocator；
 *   forknum       —— fork 编号；
 *   blkno         —— 目标块号，不能是 P_NEW；
 *   mode          —— 读取模式，决定页面不存在时的处理方式；
 *   recent_buffer —— 可选的 buffer 提示，若恰好有效可避免一次 buffer mapping
 *                    查找；允许不准确。
 *
 * 各 mode 的语义：
 *   RBM_NORMAL         ：页面不存在或全零时返回 InvalidBuffer，并调用
 *                        log_invalid_page() 记录引用，期待后续 DROP/TRUNCATE
 *                        解释；调用者应静默跳过该页的修改；
 *   RBM_NORMAL_NO_LOG  ：页面不存在时返回 InvalidBuffer，但不记录 invalid
 *                        page，也不检查全零；
 *   RBM_ZERO_AND_LOCK /
 *   RBM_ZERO_AND_CLEANUP_LOCK：页面不存在时把关系扩展到 blkno，返回全零且已
 *                        加锁的 buffer。
 *
 * 关键流程：
 *   1. 若 recent_buffer 有效且 mode 为 RBM_NORMAL，先尝试 ReadRecentBuffer()
 *      快路径；
 *   2. smgropen() 取得（必要时在缓存中创建）SMgrRelation 对象，并调用
 *      smgrcreate() 确保文件存在。这样即使 WAL 中先写页面、后面才删除关系，
 *      也能安全写入；相比直接忽略写操作，先写数据再按 WAL 删除更不容易在
 *      文件系统丢失 inode 时丢数据；
 *   3. smgrnblocks() 得到当前块数：blkno < lastblock 时用
 *      ReadBufferWithoutRelcache() 读取；否则按 mode 决定记录 invalid page、
 *      静默返回，或用 ExtendBufferedRelTo() 扩展（恢复期无需 relation
 *      extension lock，故带 EB_SKIP_EXTENSION_LOCK 和
 *      EB_PERFORMING_RECOVERY）；
 *   4. RBM_NORMAL 下还要检查 PageIsNew()。恢复期间没有其他写者，可以不加锁地
 *      检查；若页面全零，释放 buffer、记录 invalid page(present=true) 并返回
 *      InvalidBuffer。
 *
 * 返回值：pinned buffer；RBM_ZERO_AND_LOCK / RBM_ZERO_AND_CLEANUP_LOCK 模式下
 * 还持有独占锁（cleanup 模式为 cleanup lock）。RBM_NORMAL /
 * RBM_NORMAL_NO_LOG 下返回的 buffer 未加锁。调用者负责
 * ReleaseBuffer()/UnlockReleaseBuffer()。
 *
 * 注意：redo 函数通常不应直接调用本函数，而应使用
 * XLogReadBufferForRedoExtended()，以保证所有被修改的页面都出现在 WAL record
 * 的 block reference 中，便于工具追踪。
 */
Buffer
XLogReadBufferExtended(RelFileLocator rlocator, ForkNumber forknum,
					   BlockNumber blkno, ReadBufferMode mode,
					   Buffer recent_buffer)
{
	BlockNumber lastblock;
	Buffer		buffer;
	SMgrRelation smgr;

	Assert(blkno != P_NEW);

	/* Do we have a clue where the buffer might be already? */
	if (BufferIsValid(recent_buffer) &&
		mode == RBM_NORMAL &&
		ReadRecentBuffer(rlocator, forknum, blkno, recent_buffer))
	{
		buffer = recent_buffer;
		goto recent_buffer_fast_path;
	}

	/* Open the relation at smgr level */
	smgr = smgropen(rlocator, INVALID_PROC_NUMBER);

	/*
	 * Create the target file if it doesn't already exist.  This lets us cope
	 * if the replay sequence contains writes to a relation that is later
	 * deleted.  (The original coding of this routine would instead suppress
	 * the writes, but that seems like it risks losing valuable data if the
	 * filesystem loses an inode during a crash.  Better to write the data
	 * until we are actually told to delete the file.)
	 */
	smgrcreate(smgr, forknum, true);

	lastblock = smgrnblocks(smgr, forknum);

	if (blkno < lastblock)
	{
		/* page exists in file */
		buffer = ReadBufferWithoutRelcache(rlocator, forknum, blkno,
										   mode, NULL, true);
	}
	else
	{
		/* hm, page doesn't exist in file */
		if (mode == RBM_NORMAL)
		{
			log_invalid_page(rlocator, forknum, blkno, false);
			return InvalidBuffer;
		}
		if (mode == RBM_NORMAL_NO_LOG)
			return InvalidBuffer;
		/* OK to extend the file */
		/* we do this in recovery only - no rel-extension lock needed */
		Assert(InRecovery);
		buffer = ExtendBufferedRelTo(BMR_SMGR(smgr, RELPERSISTENCE_PERMANENT),
									 forknum,
									 NULL,
									 EB_PERFORMING_RECOVERY |
									 EB_SKIP_EXTENSION_LOCK,
									 blkno + 1,
									 mode);
	}

recent_buffer_fast_path:
	if (mode == RBM_NORMAL)
	{
		/* check that page has been initialized */
		Page		page = BufferGetPage(buffer);

		/*
		 * We assume that PageIsNew is safe without a lock. During recovery,
		 * there should be no other backends that could modify the buffer at
		 * the same time.
		 */
		if (PageIsNew(page))
		{
			ReleaseBuffer(buffer);
			log_invalid_page(rlocator, forknum, blkno, true);
			return InvalidBuffer;
		}
	}

	return buffer;
}

/*
 * Struct actually returned by CreateFakeRelcacheEntry, though the declared
 * return type is Relation.
 */
/*
 * 中文注释：
 * CreateFakeRelcacheEntry() 实际返回的结构体，声明返回类型为 Relation 只是
 * 为了能直接传给接受 Relation 的底层函数。RelationData 必须放在最前面，
 * 这样 Relation 指针与 FakeRelCacheEntry 指针可以互相转换。
 *
 * 内嵌的 FormData_pg_class 用于填充 rd_rel 指向的 pg_class 元组；只有与物理
 * 存储相关的字段会被初始化，因此这个假 relcache 项只能用于 ReadBuffer() 等
 * 低层操作，不能用于依赖完整 catalog 信息的高层逻辑。
 */
typedef struct
{
	RelationData reldata;		/* Note: this must be first */
	FormData_pg_class pgc;
} FakeRelCacheEntryData;

/*
 * 中文注释：
 * 指向上述 FakeRelCacheEntryData 的指针类型，便于访问 pgc 字段。
 */
typedef FakeRelCacheEntryData *FakeRelCacheEntry;

/*
 * Create a fake relation cache entry for a physical relation
 *
 * It's often convenient to use the same functions in XLOG replay as in the
 * main codepath, but those functions typically work with a relcache entry.
 * We don't have a working relation cache during XLOG replay, but this
 * function can be used to create a fake relcache entry instead. Only the
 * fields related to physical storage, like rd_rel, are initialized, so the
 * fake entry is only usable in low-level operations like ReadBuffer().
 *
 * This is also used for syncing WAL-skipped files.
 *
 * Caller must free the returned entry with FreeFakeRelcacheEntry().
 */
/*
 * 中文注释：
 * 为物理关系构造一个“假”的 relcache 项，使 redo 代码可以复用那些要求
 * Relation 参数的底层函数（如 ReadBuffer()、log_newpage_range()）。
 *
 * 参数 rlocator：目标关系的物理定位符。
 * 返回值：palloc 得到的 Relation（实际是 FakeRelCacheEntryData），调用者必须
 * 用 FreeFakeRelcacheEntry() 释放。
 *
 * 初始化内容：
 *   - rd_rel 指向内嵌的 FormData_pg_class，并强制 relpersistence 为
 *     RELPERSISTENCE_PERMANENT（恢复期间不会处理临时关系）；
 *   - rd_locator 保存物理位置；rd_backend 设为 INVALID_PROC_NUMBER；
 *   - 关系名用 relfilenumber 的十进制字符串代替（恢复时没有 pg_class 可查）；
 *   - rd_lockInfo.lockRelId 用 locator 填充。这个值并不严格等于关系 OID，
 *     但恢复时只有 startup 进程在跑，不会有锁冲突；同步 WAL-skipped 文件时
 *     调用者已经持有 AccessExclusiveLock，因此也无妨；
 *   - rd_smgr 通过 smgropen() 建立非 pinned 引用（INVALID_PROC_NUMBER），
 *     这样出错时无需担心 unpin。
 *
 * 调用场景：WAL redo 中的存储管理操作，以及 WAL-skipped 文件同步
 * （catalog/storage.c）。本函数不访问系统表，也不获取重量级锁。
 */
Relation
CreateFakeRelcacheEntry(RelFileLocator rlocator)
{
	FakeRelCacheEntry fakeentry;
	Relation	rel;

	/* Allocate the Relation struct and all related space in one block. */
	fakeentry = palloc0_object(FakeRelCacheEntryData);
	rel = (Relation) fakeentry;

	rel->rd_rel = &fakeentry->pgc;
	rel->rd_locator = rlocator;

	/*
	 * We will never be working with temp rels during recovery or while
	 * syncing WAL-skipped files.
	 */
	rel->rd_backend = INVALID_PROC_NUMBER;

	/* It must be a permanent table here */
	rel->rd_rel->relpersistence = RELPERSISTENCE_PERMANENT;

	/* We don't know the name of the relation; use relfilenumber instead */
	sprintf(RelationGetRelationName(rel), "%u", rlocator.relNumber);

	/*
	 * We set up the lockRelId in case anything tries to lock the dummy
	 * relation.  Note that this is fairly bogus since relNumber may be
	 * different from the relation's OID.  It shouldn't really matter though.
	 * In recovery, we are running by ourselves and can't have any lock
	 * conflicts.  While syncing, we already hold AccessExclusiveLock.
	 */
	rel->rd_lockInfo.lockRelId.dbId = rlocator.dbOid;
	rel->rd_lockInfo.lockRelId.relId = rlocator.relNumber;

	/*
	 * Set up a non-pinned SMgrRelation reference, so that we don't need to
	 * worry about unpinning it on error.
	 */
	rel->rd_smgr = smgropen(rlocator, INVALID_PROC_NUMBER);

	return rel;
}

/*
 * Free a fake relation cache entry.
 */
/*
 * 中文注释：
 * 释放 CreateFakeRelcacheEntry() 返回的假 relcache 项。
 *
 * 参数 fakerel：之前创建的假 Relation。
 * 行为：直接 pfree()。由于 rd_smgr 是非 pinned 引用，不需要 smgrclose()；
 * 也不存在需要清理的 relcache 注册项。调用后指针不可再使用。
 */
void
FreeFakeRelcacheEntry(Relation fakerel)
{
	pfree(fakerel);
}

/*
 * Drop a relation during XLOG replay
 *
 * This is called when the relation is about to be deleted; we need to remove
 * any open "invalid-page" records for the relation.
 */
/*
 * 中文注释：
 * 重放 DROP RELATION 类记录时的辅助函数：清除该关系指定 fork 上所有
 * invalid-page 记录，表示这些页面已经被合法删除，不应再被判定为悬空引用。
 *
 * 参数：rlocator 定位关系；forknum 指定 fork。
 * 实现：调用 forget_invalid_pages(rlocator, forknum, 0)，即从块号 0 开始全部
 * 清除。只在 startup 进程的 redo 路径中调用，无并发问题。
 */
void
XLogDropRelation(RelFileLocator rlocator, ForkNumber forknum)
{
	forget_invalid_pages(rlocator, forknum, 0);
}

/*
 * Drop a whole database during XLOG replay
 *
 * As above, but for DROP DATABASE instead of dropping a single rel
 */
/*
 * 中文注释：
 * 重放 DROP DATABASE 类记录时的辅助函数：清理该数据库相关的 invalid-page
 * 记录，并关闭所有 SMgrRelation 缓存。
 *
 * 参数 dbid：被删除数据库的 OID。
 * 行为：
 *   1. smgrdestroyall() 关闭本进程所有 SMgrRelation。这里确实“用力过猛”，会
 *      连带关闭其他数据库的 smgr 对象，但 DROP DATABASE 很少发生，不值得为此
 *      专门增加一个 smgrdestroy 变体；
 *   2. forget_invalid_pages_db(dbid) 删除该数据库的所有 invalid-page 条目。
 *
 * 只在 startup 进程的 redo 路径中调用；smgrdestroyall() 会影响本进程后续的
 * smgr 缓存命中，但语义上安全。
 */
void
XLogDropDatabase(Oid dbid)
{
	/*
	 * This is unnecessarily heavy-handed, as it will close SMgrRelation
	 * objects for other databases as well. DROP DATABASE occurs seldom enough
	 * that it's not worth introducing a variant of smgrdestroy for just this
	 * purpose.
	 */
	smgrdestroyall();

	forget_invalid_pages_db(dbid);
}

/*
 * Truncate a relation during XLOG replay
 *
 * We need to clean up any open "invalid-page" records for the dropped pages.
 */
/*
 * 中文注释：
 * 重放 TRUNCATE 类记录时的辅助函数：清除该关系指定 fork 中块号 >= nblocks
 * 的 invalid-page 记录，因为截断后这些页面已不存在。
 *
 * 参数：rlocator/forkNum 定位关系与 fork；nblocks 是截断后的新块数。
 * 实现：forget_invalid_pages(rlocator, forkNum, nblocks)。
 * 只在 startup 进程的 redo 路径中调用，无并发问题。
 */
void
XLogTruncateRelation(RelFileLocator rlocator, ForkNumber forkNum,
					 BlockNumber nblocks)
{
	forget_invalid_pages(rlocator, forkNum, nblocks);
}

/*
 * Determine which timeline to read an xlog page from and set the
 * XLogReaderState's currTLI to that timeline ID.
 *
 * We care about timelines in xlogreader when we might be reading xlog
 * generated prior to a promotion, either if we're currently a standby in
 * recovery or if we're a promoted primary reading xlogs generated by the old
 * primary before our promotion.
 *
 * wantPage must be set to the start address of the page to read and
 * wantLength to the amount of the page that will be read, up to
 * XLOG_BLCKSZ. If the amount to be read isn't known, pass XLOG_BLCKSZ.
 *
 * The currTLI argument should be the system-wide current timeline.
 * Note that this may be different from state->currTLI, which is the timeline
 * from which the caller is currently reading previous xlog records.
 *
 * We switch to an xlog segment from the new timeline eagerly when on a
 * historical timeline, as soon as we reach the start of the xlog segment
 * containing the timeline switch.  The server copied the segment to the new
 * timeline so all the data up to the switch point is the same, but there's no
 * guarantee the old segment will still exist. It may have been deleted or
 * renamed with a .partial suffix so we can't necessarily keep reading from
 * the old TLI even though tliSwitchPoint says it's OK.
 *
 * We can't just check the timeline when we read a page on a different segment
 * to the last page. We could've received a timeline switch from a cascading
 * upstream, so the current segment ends abruptly (possibly getting renamed to
 * .partial) and we have to switch to a new one.  Even in the middle of reading
 * a page we could have to dump the cached page and switch to a new TLI.
 *
 * Because of this, callers MAY NOT assume that currTLI is the timeline that
 * will be in a page's xlp_tli; the page may begin on an older timeline or we
 * might be reading from historical timeline data on a segment that's been
 * copied to a new timeline.
 *
 * The caller must also make sure it doesn't read past the current replay
 * position (using GetXLogReplayRecPtr) if executing in recovery, so it
 * doesn't fail to notice that the current timeline became historical.
 */
/*
 * 中文注释：
 * 为 XLogReader 选择“读取某个 WAL page 时应使用哪个 timeline”，并更新
 * state->currTLI / currTLIValidUntil / nextTLI。
 *
 * 背景：在 standby 或刚 promote 的 primary 上，可能读到 promotion 之前由旧
 * timeline 生成的 WAL。timeline switch 时，服务器会把包含切换点的整个 segment
 * 复制到新 timeline，因此切换点之前的数据相同；但旧 segment 可能被删除或改名
 * 为 .partial，不能保证一直可读。因此一旦到达“包含 timeline switch 的
 * segment”的起点，就应尽早切换到新 timeline。
 *
 * 参数：
 *   state      —— WAL reader 状态，函数会修改其 currTLI 相关字段；
 *   wantPage   —— 要读取的 page 起始地址，必须是 XLOG_BLCKSZ 对齐；
 *   wantLength —— 本次计划读取的字节数，未知时传 XLOG_BLCKSZ；
 *   currTLI    —— 系统级当前 timeline，可能与 state->currTLI（正在读取历史
 *                 记录所用的 timeline）不同。
 *
 * 快速路径（直接返回，不改变 timeline）：
 *   1. 目标页已经在 state 的 read buffer 中且范围足够；
 *   2. 当前 state->currTLI 就是系统当前 timeline，且是向前顺序读取；
 *   3. 正在读取已校验过的历史 timeline，且目标范围仍在 currTLIValidUntil
 *      所在 segment 之内。
 *
 * 慢路径：重新读取 currTLI 的 timeline history（因为 promotion 或级联 standby
 * 可能改变它），计算包含 wantPage 的 segment 末尾所处的 timeline
 * （tliOfPointInHistory），再用 tliSwitchPoint() 求出该 timeline 的有效范围
 * 和下一个 timeline。
 *
 * 重要约束：
 *   - 调用者不能假设 currTLI 等于页面头中的 xlp_tli：页面可能起始于更老的
 *     timeline，或者该 segment 是从旧 timeline 复制过来的；
 *   - 恢复期间调用者不得读到超过 GetXLogReplayRecPtr() 的位置，否则可能错过
 *     “当前 timeline 已变成历史”的事实；
 *   - timeline 可能在读取过程中变化（级联 standby 上游 promote），因此
 *     read_local_xlog_page_guts() 每轮循环都会重新调用本函数。
 *
 * 并发：state 是每个 reader 私有的；timeline history 从磁盘读取，可能被
 * StartupXLOG() 并发修改（重命名为 .partial），这种竞争无法完全避免。
 */
void
XLogReadDetermineTimeline(XLogReaderState *state, XLogRecPtr wantPage,
						  uint32 wantLength, TimeLineID currTLI)
{
	const XLogRecPtr lastReadPage = (state->seg.ws_segno *
									 state->segcxt.ws_segsize + state->segoff);

	Assert(XLogRecPtrIsValid(wantPage) && wantPage % XLOG_BLCKSZ == 0);
	Assert(wantLength <= XLOG_BLCKSZ);
	Assert(state->readLen == 0 || state->readLen <= XLOG_BLCKSZ);
	Assert(currTLI != 0);

	/*
	 * If the desired page is currently read in and valid, we have nothing to
	 * do.
	 *
	 * The caller should've ensured that it didn't previously advance readOff
	 * past the valid limit of this timeline, so it doesn't matter if the
	 * current TLI has since become historical.
	 */
	if (lastReadPage == wantPage &&
		state->readLen != 0 &&
		lastReadPage + state->readLen >= wantPage + Min(wantLength, XLOG_BLCKSZ - 1))
		return;

	/*
	 * If we're reading from the current timeline, it hasn't become historical
	 * and the page we're reading is after the last page read, we can again
	 * just carry on. (Seeking backwards requires a check to make sure the
	 * older page isn't on a prior timeline).
	 *
	 * currTLI might've become historical since the caller obtained the value,
	 * but the caller is required not to read past the flush limit it saw at
	 * the time it looked up the timeline. There's nothing we can do about it
	 * if StartupXLOG() renames it to .partial concurrently.
	 */
	if (state->currTLI == currTLI && wantPage >= lastReadPage)
	{
		Assert(!XLogRecPtrIsValid(state->currTLIValidUntil));
		return;
	}

	/*
	 * If we're just reading pages from a previously validated historical
	 * timeline and the timeline we're reading from is valid until the end of
	 * the current segment we can just keep reading.
	 */
	if (XLogRecPtrIsValid(state->currTLIValidUntil) &&
		state->currTLI != currTLI &&
		state->currTLI != 0 &&
		((wantPage + wantLength) / state->segcxt.ws_segsize) <
		(state->currTLIValidUntil / state->segcxt.ws_segsize))
		return;

	/*
	 * If we reach this point we're either looking up a page for random
	 * access, the current timeline just became historical, or we're reading
	 * from a new segment containing a timeline switch. In all cases we need
	 * to determine the newest timeline on the segment.
	 *
	 * If it's the current timeline we can just keep reading from here unless
	 * we detect a timeline switch that makes the current timeline historical.
	 * If it's a historical timeline we can read all the segment on the newest
	 * timeline because it contains all the old timelines' data too. So only
	 * one switch check is required.
	 */
	{
		/*
		 * We need to re-read the timeline history in case it's been changed
		 * by a promotion or replay from a cascaded replica.
		 */
		List	   *timelineHistory = readTimeLineHistory(currTLI);
		XLogRecPtr	endOfSegment;

		endOfSegment = ((wantPage / state->segcxt.ws_segsize) + 1) *
			state->segcxt.ws_segsize - 1;
		Assert(wantPage / state->segcxt.ws_segsize ==
			   endOfSegment / state->segcxt.ws_segsize);

		/*
		 * Find the timeline of the last LSN on the segment containing
		 * wantPage.
		 */
		state->currTLI = tliOfPointInHistory(endOfSegment, timelineHistory);
		state->currTLIValidUntil = tliSwitchPoint(state->currTLI, timelineHistory,
												  &state->nextTLI);

		Assert(!XLogRecPtrIsValid(state->currTLIValidUntil) ||
			   wantPage + wantLength < state->currTLIValidUntil);

		list_free_deep(timelineHistory);

		elog(DEBUG3, "switched to timeline %u valid until %X/%08X",
			 state->currTLI,
			 LSN_FORMAT_ARGS(state->currTLIValidUntil));
	}
}

/* XLogReaderRoutine->segment_open callback for local pg_wal files */
/*
 * 中文注释：
 * XLogReaderRoutine->segment_open 的本地实现：根据 timeline 和 segment 号拼出
 * pg_wal 下的完整路径，并以只读、二进制方式打开。
 *
 * 参数：
 *   state     —— WAL reader 状态，成功时把文件描述符写入 state->seg.ws_file；
 *   nextSegNo —— 要打开的 segment 编号；
 *   tli_p     —— 输入为期望的 timeline（本函数不修改它）。
 *
 * 错误处理：ENOENT 表示该 segment 已被删除（常见于归档/回收或 timeline 切换
 * 后旧段被清理），报 "requested WAL segment %s has already been removed"；
 * 其他 errno 统一报 "could not open file"。
 *
 * 副作用：打开的文件描述符由 wal_segment_close() 负责关闭；失败时通过
 * ereport(ERROR) 抛出，不会留下半打开状态。只在需要读取本地 WAL 文件的进程中
 * 使用（startup、walsender、逻辑解码等），每个 reader 的 state 私有。
 */
void
wal_segment_open(XLogReaderState *state, XLogSegNo nextSegNo,
				 TimeLineID *tli_p)
{
	TimeLineID	tli = *tli_p;
	char		path[MAXPGPATH];

	XLogFilePath(path, tli, nextSegNo, state->segcxt.ws_segsize);
	state->seg.ws_file = BasicOpenFile(path, O_RDONLY | PG_BINARY);
	if (state->seg.ws_file >= 0)
		return;

	if (errno == ENOENT)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("requested WAL segment %s has already been removed",
						path)));
	else
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not open file \"%s\": %m",
						path)));
}

/* stock XLogReaderRoutine->segment_close callback */
/*
 * 中文注释：
 * XLogReaderRoutine->segment_close 的默认实现：关闭当前打开的 WAL segment
 * 文件，并把 state->seg.ws_file 置为 -1，避免悬空描述符被重复关闭。
 *
 * 参数 state：WAL reader 状态。
 * 副作用：调用 close()；这里刻意忽略关闭错误（原注释也标注了
 * “need to check errno?”），因为只读文件的 close 失败通常没有可恢复动作。
 * 每个 reader 的 state 私有，无并发问题。
 */
void
wal_segment_close(XLogReaderState *state)
{
	close(state->seg.ws_file);
	/* need to check errno? */
	state->seg.ws_file = -1;
}

/*
 * XLogReaderRoutine->page_read callback for reading local xlog files
 *
 * Public because it would likely be very helpful for someone writing another
 * output method outside walsender, e.g. in a bgworker.
 */
/*
 * 中文注释：
 * XLogReaderRoutine->page_read 的本地实现：从 pg_wal 读取一个 WAL page，
 * 必要时等待未来 WAL 到达。它是
 * read_local_xlog_page_guts(..., wait_for_wal=true) 的薄封装。
 *
 * 参数：
 *   state         —— WAL reader 状态；
 *   targetPagePtr —— 目标 page 的起始 LSN；
 *   reqLen        —— 本次请求的字节数；
 *   targetRecPtr  —— 目标记录起始 LSN；本文件的实现未使用它，保留该参数是
 *                    为了符合 XLogReaderRoutine 的接口；
 *   cur_page      —— 输出缓冲区，至少 XLOG_BLCKSZ 字节。
 *
 * 返回值：实际读取的有效字节数；-1 表示当前可读 WAL 不足以满足请求（EOF）。
 * 读取失败会通过 WALReadRaiseError() 抛 ERROR。
 *
 * 调用场景：恢复、逻辑解码、两阶段提交检查、repack_worker 等需要读取本地
 * WAL 的进程。函数是 public 的，方便 walsender 之外的输出方式（如 bgworker）
 * 复用。
 */
int
read_local_xlog_page(XLogReaderState *state, XLogRecPtr targetPagePtr,
					 int reqLen, XLogRecPtr targetRecPtr, char *cur_page)
{
	return read_local_xlog_page_guts(state, targetPagePtr, reqLen,
									 targetRecPtr, cur_page, true);
}

/*
 * Same as read_local_xlog_page except that it doesn't wait for future WAL
 * to be available.
 */
/*
 * 中文注释：
 * 与 read_local_xlog_page() 相同，但不等待尚未产生的 WAL：当读到当前 WAL
 * 末尾时立即返回，并通过 state->private_data
 * （ReadLocalXLogPageNoWaitPrivate）把 end_of_wal 置为 true，供调用者判断
 * “已经到达 WAL 末尾”。
 *
 * 参数与返回值同 read_local_xlog_page()。
 * 调用场景：需要在有限 WAL 范围内扫描、不能阻塞等待的场景，例如
 * repack_worker 在寻找起始点时先以 no-wait 模式读取，再切换到普通模式。
 */
int
read_local_xlog_page_no_wait(XLogReaderState *state, XLogRecPtr targetPagePtr,
							 int reqLen, XLogRecPtr targetRecPtr,
							 char *cur_page)
{
	return read_local_xlog_page_guts(state, targetPagePtr, reqLen,
									 targetRecPtr, cur_page, false);
}

/*
 * Implementation of read_local_xlog_page and its no wait version.
 */
/*
 * 中文注释：
 * read_local_xlog_page() 与 read_local_xlog_page_no_wait() 的共同实现。
 *
 * 参数：
 *   state         —— WAL reader 状态；
 *   targetPagePtr —— 目标 page 起始 LSN；
 *   reqLen        —— 请求读取的字节数；
 *   targetRecPtr  —— 目标记录起始 LSN；本文件的实现未使用它，保留该参数是
 *                    为了符合 XLogReaderRoutine 的接口；
 *   cur_page      —— 输出缓冲区；
 *   wait_for_wal  —— true 时在 WAL 不足时睡眠等待，false 时立即返回。
 *
 * 返回值：读取到的有效字节数；-1 表示数据不足（调用者应视为 EOF/需要更多
 * WAL）。
 *
 * 主循环逻辑：
 *   1. 计算 loc = targetPagePtr + reqLen，即本次请求的结束位置；
 *   2. 确定可读上界 read_upto 和当前 timeline：
 *      - 不在恢复中：GetFlushRecPtr() 返回已刷盘 WAL 的上界；
 *      - 在恢复中：GetXLogReplayRecPtr() 返回已重放位置；若
 *        GetWALInsertionTimeLineIfSet() 已设置插入 timeline（逻辑解码场景），
 *        优先使用它；
 *   3. 每轮都调用 XLogReadDetermineTimeline()，因为级联 standby 的上游
 *      promote 可能让当前 timeline 变成历史；
 *   4. 若仍在当前 timeline：数据足够则跳出；不等待则设置 end_of_wal 后跳出；
 *      否则 CHECK_FOR_INTERRUPTS() 后睡眠 1ms 重试；
 *      若已切到历史 timeline：把 read_upto 限制到 currTLIValidUntil，并使用
 *      state->currTLI 作为读取 timeline，然后直接跳出（历史 timeline 不需要
 *      等待）；
 *   5. 根据 read_upto 计算本次可读字节数：若整个 page 可用则读 XLOG_BLCKSZ；
 *      若连请求长度都不够则返回 -1；否则读取 read_upto - targetPagePtr 字节；
 *   6. 调用 WALRead() 完成实际读取（可能触发 segment_open/segment_close），
 *      失败时 WALReadRaiseError() 抛错，成功返回字节数。
 *
 * 并发/恢复注意：
 *   - 本函数可能长时间睡眠等待 WAL，期间响应中断；
 *   - timeline 可能在“确定 TLI”和“真正读取”之间变化，导致旧 segment 被改名
 *     为 .partial 而读取失败；这种竞争只在级联 standby 的叶子节点 promote 时
 *     出现，一次性的 ERROR 可以接受；
 *   - state 及其 segment 缓存是 reader 私有的，不能跨线程/进程共享。
 */
static int
read_local_xlog_page_guts(XLogReaderState *state, XLogRecPtr targetPagePtr,
						  int reqLen, XLogRecPtr targetRecPtr,
						  char *cur_page, bool wait_for_wal)
{
	XLogRecPtr	read_upto,
				loc;
	TimeLineID	tli;
	int			count;
	WALReadError errinfo;
	TimeLineID	currTLI;

	loc = targetPagePtr + reqLen;

	/*
	 * Loop waiting for xlog to be available if necessary
	 *
	 * TODO: The walsender has its own version of this function, which uses a
	 * condition variable to wake up whenever WAL is flushed. We could use the
	 * same infrastructure here, instead of the check/sleep/repeat style of
	 * loop.
	 */
	while (1)
	{
		/*
		 * Determine the limit of xlog we can currently read to, and what the
		 * most recent timeline is.
		 */
		if (!RecoveryInProgress())
			read_upto = GetFlushRecPtr(&currTLI);
		else
		{
			TimeLineID	insertTLI;

			read_upto = GetXLogReplayRecPtr(&currTLI);

			/*
			 * If the insertion timeline has already been set, use it. See
			 * logical_read_xlog_page() for details.
			 */
			insertTLI = GetWALInsertionTimeLineIfSet();
			if (insertTLI != 0)
				currTLI = insertTLI;
		}
		tli = currTLI;

		/*
		 * Check which timeline to get the record from.
		 *
		 * We have to do it each time through the loop because if we're in
		 * recovery as a cascading standby, the current timeline might've
		 * become historical. We can't rely on RecoveryInProgress() because in
		 * a standby configuration like
		 *
		 * A => B => C
		 *
		 * if we're a logical decoding session on C, and B gets promoted, our
		 * timeline will change while we remain in recovery.
		 *
		 * We can't just keep reading from the old timeline as the last WAL
		 * archive in the timeline will get renamed to .partial by
		 * StartupXLOG().
		 *
		 * If that happens after our caller determined the TLI but before we
		 * actually read the xlog page, we might still try to read from the
		 * old (now renamed) segment and fail. There's not much we can do
		 * about this, but it can only happen when we're a leaf of a cascading
		 * standby whose primary gets promoted while we're decoding, so a
		 * one-off ERROR isn't too bad.
		 */
		XLogReadDetermineTimeline(state, targetPagePtr, reqLen, tli);

		if (state->currTLI == currTLI)
		{

			if (loc <= read_upto)
				break;

			/* If asked, let's not wait for future WAL. */
			if (!wait_for_wal)
			{
				ReadLocalXLogPageNoWaitPrivate *private_data;

				/*
				 * Inform the caller of read_local_xlog_page_no_wait that the
				 * end of WAL has been reached.
				 */
				private_data = (ReadLocalXLogPageNoWaitPrivate *)
					state->private_data;
				private_data->end_of_wal = true;
				break;
			}

			CHECK_FOR_INTERRUPTS();
			pg_usleep(1000L);
		}
		else
		{
			/*
			 * We're on a historical timeline, so limit reading to the switch
			 * point where we moved to the next timeline.
			 *
			 * We don't need to GetFlushRecPtr or GetXLogReplayRecPtr. We know
			 * about the new timeline, so we must've received past the end of
			 * it.
			 */
			read_upto = state->currTLIValidUntil;

			/*
			 * Setting tli to our wanted record's TLI is slightly wrong; the
			 * page might begin on an older timeline if it contains a timeline
			 * switch, since its xlog segment will have been copied from the
			 * prior timeline. This is pretty harmless though, as nothing
			 * cares so long as the timeline doesn't go backwards.  We should
			 * read the page header instead; FIXME someday.
			 */
			tli = state->currTLI;

			/* No need to wait on a historical timeline */
			break;
		}
	}

	if (targetPagePtr + XLOG_BLCKSZ <= read_upto)
	{
		/*
		 * more than one block available; read only that block, have caller
		 * come back if they need more.
		 */
		count = XLOG_BLCKSZ;
	}
	else if (targetPagePtr + reqLen > read_upto)
	{
		/* not enough data there */
		return -1;
	}
	else
	{
		/* enough bytes available to satisfy the request */
		count = read_upto - targetPagePtr;
	}

	if (!WALRead(state, cur_page, targetPagePtr, count, tli,
				 &errinfo))
		WALReadRaiseError(&errinfo);

	/* number of valid bytes in the buffer */
	return count;
}

/*
 * Backend-specific convenience code to handle read errors encountered by
 * WALRead().
 */
/*
 * 中文注释：
 * 把 WALRead() 返回的错误信息转换为 ereport(ERROR)。这是 backend 侧的便利
 * 封装，避免每个调用点重复拼错误消息。
 *
 * 参数 errinfo：WALRead() 填充的 WALReadError，包含失败的 segment
 * （timeline、segment 号）、文件内偏移、请求字节数和实际读取结果/errno。
 *
 * 行为：
 *   - wre_read < 0：真实的系统调用错误，恢复 wre_errno 后报
 *     "could not read from WAL segment %s, offset %u: %m"；
 *   - wre_read == 0：读到 0 字节（例如文件被截断），报
 *     ERRCODE_DATA_CORRUPTED，并给出实际读取字节数与请求字节数；
 *   - WALRead() 在读到部分字节（> 0）时会继续循环读取剩余部分，因此不会以
 *     这种状态调用本函数。
 *
 * 副作用：ereport(ERROR) 会 longjmp，不返回；设置 errno 以便 %m 输出正确。
 * 只在读取本地 WAL 的进程中使用。
 */
void
WALReadRaiseError(WALReadError *errinfo)
{
	WALOpenSegment *seg = &errinfo->wre_seg;
	char		fname[MAXFNAMELEN];

	XLogFileName(fname, seg->ws_tli, seg->ws_segno, wal_segment_size);

	if (errinfo->wre_read < 0)
	{
		errno = errinfo->wre_errno;
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from WAL segment %s, offset %u: %m",
						fname, errinfo->wre_off)));
	}
	else if (errinfo->wre_read == 0)
	{
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("could not read from WAL segment %s, offset %u: read %zd of %zu",
						fname, errinfo->wre_off, errinfo->wre_read,
						errinfo->wre_req)));
	}
}
