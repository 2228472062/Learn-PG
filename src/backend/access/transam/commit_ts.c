/*-------------------------------------------------------------------------
 *
 * commit_ts.c
 *		PostgreSQL commit timestamp manager
 *
 * This module is a pg_xact-like system that stores the commit timestamp
 * for each transaction.
 *
 * XLOG interactions: this module generates an XLOG record whenever a new
 * CommitTs page is initialized to zeroes.  Other writes of CommitTS come
 * from recording of transaction commit in xact.c, which generates its own
 * XLOG records for these events and will re-perform the status update on
 * redo; so we need make no additional XLOG entry here.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/commit_ts.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 的提交时间戳（commit timestamp）管理器。启用
 * track_commit_timestamp 后，每个提交成功且拥有 XID 的事务（含子事务）都会在
 * pg_commit_ts 这个 SLRU 中留下一条“提交时间戳 + 复制源（ReplOriginId）”记录，
 * 供 SQL 函数 pg_xact_commit_timestamp()、pg_xact_commit_timestamp_origin()、
 * pg_last_committed_xact() 以及逻辑复制、冲突检测等内部代码查询。
 *
 * 存储布局与寻址：
 *   - pg_commit_ts 与 pg_xact（CLOG）、pg_subtrans 一样，是按 XID 直接下标寻址
 *     的 SLRU；每个事务占 8 字节 TimestampTz 加 2 字节 ReplOriginId。按默认
 *     8KB 页面计算，每页可存 COMMIT_TS_XACTS_PER_PAGE（819）条记录，每个 SLRU
 *     segment 含 SLRU_PAGES_PER_SEGMENT（32）页。
 *   - 页号、页内下标分别由 TransactionIdToCTsPage()/TransactionIdToCTsEntry()
 *     计算；由于 XID 只有 32 位，页号和段号都会随 XID 回绕，回绕语义只在截断
 *     时通过 CommitTsPagePrecedes() 显式处理。
 *   - pg_commit_ts 目录下的文件名使用至少 4 位十六进制段号
 *     （long_segment_names = false，格式为 %04X，段号更大时会自动扩展）。
 *
 * 与 CLOG/transam 的关系：
 *   - CLOG（pg_xact）记录每个 XID 的提交/中止状态，是事务状态的权威来源；
 *     commit timestamp 只是已提交事务的附加元数据，本模块并不判断事务是否提交。
 *     查询方通常先用 CLOG 判断状态，再读取时间戳。
 *   - 中止（abort）的事务不会写入时间戳；读取不到记录时返回 false 且 *ts = 0。
 *     因此“没有时间戳”既可能表示事务中止，也可能表示事务在特性关闭期间提交、
 *     或记录已被截断。
 *
 * WAL、复制与恢复：
 *   - 普通提交不额外写 WAL：XLOG_XACT_COMMIT/XLOG_XACT_COMMIT_PREPARED 记录里
 *     已经带有提交时间和复制源，redo 时 xact.c 会再次调用
 *     TransactionTreeSetCommitTsData() 重建本 SLRU。只有“把新页清零”和“截断”
 *     会产生本模块自己的 WAL 记录（COMMIT_TS_ZEROPAGE、COMMIT_TS_TRUNCATE）。
 *   - 激活状态不直接跟随本地 GUC：备库通过 pg_control 中的标志以及回放
 *     XLOG_PARAMETER_CHANGE，获知主库是否启用了该特性，从而保证即使本地
 *     track_commit_timestamp 为 off，也能回放并保存主库产生的 commit timestamp。
 *   - 修改 track_commit_timestamp 需要重启（PGC_POSTMASTER）。主库开启后，备库
 *     会自动激活；主库关闭后，备库在回放参数变更记录时清空并删除所有
 *     pg_commit_ts 数据，避免返回陈旧或相互矛盾的信息。
 *
 * 截断与有效区间：
 *   - 共享内存 TransamVariables 中的 oldestCommitTsXid/newestCommitTsXid 标记
 *     可以查询的时间戳区间，并随 checkpoint 写入 pg_control。区间之外直接返回
 *     “无记录”，而不是让 SLRU 抛出“文件不存在”错误。
 *   - VACUUM 推进 datfrozenxid 时调用 AdvanceOldestCommitTsXid() 与
 *     TruncateCommitTs()，删除不再需要的 segment；截断前会写
 *     COMMIT_TS_TRUNCATE WAL 记录，保证备库按相同边界清理。
 *
 * 设计思想：
 *   - 用 SLRU 而不是普通表：写入发生在提交关键路径上，必须低延迟、可并发、
 *     能按 XID 直接定位；SLRU 的定长页和 bank 锁正好满足这一点。
 *   - 在共享内存缓存“最后一次提交”的 XID/时间戳/复制源，使
 *     pg_last_committed_xact() 和针对刚提交事务的查询无需访问磁盘。
 *   - 激活/去激活是显式状态机，而不是简单读取 GUC，因为备库的激活状态由主库
 *     通过 WAL 传播，且去激活需要清理历史文件。
 *   - 只记录已提交事务、不记录中止事务，用 0 时间戳表示“无值”，从而在不增加
 *     额外位图的情况下区分“有记录/无记录”。
 */
#include "postgres.h"

#include "access/commit_ts.h"
#include "access/htup_details.h"
#include "access/slru.h"
#include "access/transam.h"
#include "access/xloginsert.h"
#include "access/xlogutils.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"
#include "utils/fmgrprotos.h"
#include "utils/guc_hooks.h"
#include "utils/timestamp.h"

/*
 * Defines for CommitTs page sizes.  A page is the same BLCKSZ as is used
 * everywhere else in Postgres.
 *
 * Note: because TransactionIds are 32 bits and wrap around at 0xFFFFFFFF,
 * CommitTs page numbering also wraps around at
 * 0xFFFFFFFF/COMMIT_TS_XACTS_PER_PAGE, and CommitTs segment numbering at
 * 0xFFFFFFFF/COMMIT_TS_XACTS_PER_PAGE/SLRU_PAGES_PER_SEGMENT.  We need take no
 * explicit notice of that fact in this module, except when comparing segment
 * and page numbers in TruncateCommitTs (see CommitTsPagePrecedes).
 */
/*
 * 中文注释：
 * 这里给出 pg_commit_ts 的页面/段布局假设：页大小与 PostgreSQL 其余部分一致，
 * 都是 BLCKSZ。XID 是 32 位并在 0xFFFFFFFF 处回绕，因此页号在
 * 0xFFFFFFFF/COMMIT_TS_XACTS_PER_PAGE 处回绕，段号在再除以
 * SLRU_PAGES_PER_SEGMENT 后回绕。除 TruncateCommitTs() 中通过
 * CommitTsPagePrecedes() 比较页的新旧之外，本模块不需要显式处理回绕：
 * 所有运算都在 32 位 XID 的模运算语义下自洽。
 */

/*
 * We need 8+2 bytes per xact.  Note that enlarging this struct might mean
 * the largest possible file name is more than 5 chars long; see
 * SlruScanDirectory.
 */
/*
 * 中文注释：
 * pg_commit_ts 中单个事务的记录：提交时间戳 time 与产生该事务的复制源
 * nodeid。nodeid 为 InvalidReplOriginId 表示本地事务（或来源未知）。
 * 该结构体只用于在内存中组装/复制条目；落盘格式就是这两个字段的紧密排列，
 * 没有版本号或对齐填充。下面的 SizeOfCommitTimestampEntry 用 offsetof + sizeof
 * 计算实际占用字节数（默认 10 字节），避免编译器在 nodeid 之后插入尾部填充、
 * 浪费页面空间。
 *
 * 注意：条目不保证 8 字节对齐，读写都通过 memcpy 完成，不能直接把页面缓冲区
 * 强制转换为 CommitTimestampEntry * 后解引用。
 */
typedef struct CommitTimestampEntry
{
	TimestampTz time;
	ReplOriginId nodeid;
} CommitTimestampEntry;

#define SizeOfCommitTimestampEntry (offsetof(CommitTimestampEntry, nodeid) + \
									sizeof(ReplOriginId))

/*
 * 中文注释：
 * 每页可容纳的 commit timestamp 条目数，即 BLCKSZ / 每条记录大小。默认
 * BLCKSZ=8192、每条 10 字节时为 819。该值同时决定 XID→页号的换算，以及
 * CommitTsPagePrecedes() 中回绕比较的边界；修改记录大小会改变页容量，进而
 * 改变段文件能覆盖的 XID 范围与文件名长度。
 */
#define COMMIT_TS_XACTS_PER_PAGE \
	(BLCKSZ / SizeOfCommitTimestampEntry)


/*
 * Although we return an int64 the actual value can't currently exceed
 * 0xFFFFFFFF/COMMIT_TS_XACTS_PER_PAGE.
 */
/*
 * 中文注释：
 * 把 32 位 XID 映射到 pg_commit_ts 的 SLRU 页号：
 * xid / COMMIT_TS_XACTS_PER_PAGE。返回 int64 是为了与 SLRU 页号类型一致，并
 * 避免后续乘以页大小时发生 32 位溢出；由于 XID 只有 32 位，实际页号不会超过
 * 0xFFFFFFFF/COMMIT_TS_XACTS_PER_PAGE（默认约 524 万）。
 *
 * 调用场景：写入（SetXidCommitTsInPage）、读取
 * （TransactionIdGetCommitTsData）、扩展（ExtendCommitTs）、截断
 * （TruncateCommitTs）以及激活时定位当前页。纯函数，无副作用。
 */
static inline int64
TransactionIdToCTsPage(TransactionId xid)
{
	return xid / (int64) COMMIT_TS_XACTS_PER_PAGE;
}

/*
 * 中文注释：
 * 计算 XID 在所属页面内的条目下标：xid % COMMIT_TS_XACTS_PER_PAGE。与
 * TransactionIdToCTsPage() 配合即可定位页面缓冲区中的 10 字节槽位。
 * 宏会对参数求值两次，调用方不要传入带副作用的表达式。
 */
#define TransactionIdToCTsEntry(xid)	\
	((xid) % (TransactionId) COMMIT_TS_XACTS_PER_PAGE)

/*
 * Link to shared-memory data structures for CommitTs control
 */
/*
 * 中文注释：
 * 本模块的静态辅助函数前置声明：
 *   - CommitTsShmemRequest/CommitTsShmemInit：共享内存子系统的 request/init
 *     回调；
 *   - CommitTsPagePrecedes：截断时判断两个 SLRU 页的新旧关系（回绕安全）；
 *   - commit_ts_errdetail_for_io_error：SLRU I/O 失败时补充“哪个 XID 无法访问”
 *     的详细信息。
 * 具体语义见各函数定义处。
 */
static void CommitTsShmemRequest(void *arg);
static void CommitTsShmemInit(void *arg);
static bool CommitTsPagePrecedes(int64 page1, int64 page2);
static int	commit_ts_errdetail_for_io_error(const void *opaque_data);

/*
 * 中文注释：
 * 注册到共享内存框架的 CommitTs 回调集合。request_fn 在共享内存分配之前调用，
 * 负责确定缓冲区数量并向 SLRU 层登记本模块需求；init_fn 在共享内存就绪之后
 * 调用，用于初始化 commitTsShared 并执行页号比较函数的启动期自检。
 * arg 由框架传入，本模块不使用。
 */
const ShmemCallbacks CommitTsShmemCallbacks = {
	.request_fn = CommitTsShmemRequest,
	.init_fn = CommitTsShmemInit,
};

/*
 * 中文注释：
 * pg_commit_ts 的后端私有 SLRU 描述符（SlruDesc）。SimpleLruRequest() 会填充
 * 它，使其指向共享内存中的 SlruSharedData，并保存页数、bank 锁以及各种回调。
 * 该结构每个进程各有一份，本身不在共享内存中；CommitTsCtl 只是便于书写的
 * 别名，所有 SLRU 操作都通过它进行。
 */
static SlruDesc CommitTsSlruDesc;

#define CommitTsCtl (&CommitTsSlruDesc)

/*
 * We keep a cache of the last value set in shared memory.
 *
 * This is also good place to keep the activation status.  We keep this
 * separate from the GUC so that the standby can activate the module if the
 * primary has it active independently of the value of the GUC.
 *
 * This is protected by CommitTsLock.  In some places, we use commitTsActive
 * without acquiring the lock; where this happens, a comment explains the
 * rationale for it.
 */
/*
 * 中文注释：
 * 共享内存中的 CommitTs 全局状态：
 *   - xidLastCommit/dataLastCommit：最近一次成功记录提交时间戳的顶层 XID 及其
 *     时间戳、复制源。它作为读缓存，使 pg_last_committed_xact() 和针对刚提交
 *     事务的查询无需访问 SLRU；
 *   - commitTsActive：本模块当前是否激活。必须与 GUC track_commit_timestamp
 *     分开保存，因为备库可能在本地 GUC 为 off 时，仍因主库启用了该特性而需要
 *     激活本模块；恢复结束时也会根据 pg_control 重新确定状态。
 *
 * 并发：以上字段全部由 CommitTsLock 保护。少数不加锁读取 commitTsActive 的
 * 位置（TransactionTreeSetCommitTsData、ExtendCommitTs、
 * CommitTsParameterChange）都只在“唯一可能修改该标志的进程”中执行（恢复进程，
 * 或不可能运行在备库的 XID 分配路径），代码中另有注释说明。
 *
 * 注意：xidLastCommit 只用于缓存，不参与持久化；崩溃后由 WAL 重放和后续提交
 * 重新填充，初值为 InvalidTransactionId、time 为 -infinity。
 */
typedef struct CommitTimestampShared
{
	TransactionId xidLastCommit;
	CommitTimestampEntry dataLastCommit;
	bool		commitTsActive;
} CommitTimestampShared;

/*
 * 中文注释：
 * 指向共享内存中唯一的 CommitTimestampShared 实例，由
 * CommitTsShmemRequest() 通过 ShmemRequestStruct() 申请、由 shmem 框架回填
 * 地址。所有后端共享同一份状态；访问规则见上面的结构体注释。
 */
static CommitTimestampShared *commitTsShared;

/*
 * 中文注释：
 * 这里再次前置声明了 CommitTsShmemInit（文件上方已有一次），与上方声明重复；
 * 保留原样以免改动代码结构。定义与语义见文件后部。
 */
static void CommitTsShmemInit(void *arg);

/* GUC variable */
/*
 * 中文注释：
 * GUC 参数 track_commit_timestamp（PGC_POSTMASTER，默认 off）：是否收集并保存
 * 事务提交时间戳。只能在服务器启动时通过 postgresql.conf 修改，运行期不可
 * 改变，因此本模块可以在启动阶段一次性决定是否激活。主库上的取值会写入
 * pg_control，并通过 XLOG_PARAMETER_CHANGE 传播给备库。
 */
bool		track_commit_timestamp;

static void SetXidCommitTsInPage(TransactionId xid, int nsubxids,
								 TransactionId *subxids, TimestampTz ts,
								 ReplOriginId nodeid, int64 pageno);
static void TransactionIdSetCommitTs(TransactionId xid, TimestampTz ts,
									 ReplOriginId nodeid, int slotno);
static void error_commit_ts_disabled(void);
static void ActivateCommitTs(void);
static void DeactivateCommitTs(void);
static void WriteTruncateXlogRec(int64 pageno, TransactionId oldestXid);

/*
 * 中文注释：
 * 其余静态函数的前置声明：
 *   - SetXidCommitTsInPage：在单页上批量写入一个顶层 XID 及其同页子事务的
 *     时间戳；
 *   - TransactionIdSetCommitTs：写入单个 XID 的条目（调用方必须持 bank 锁）；
 *   - error_commit_ts_disabled：模块未激活时统一抛出 ERROR 及提示；
 *   - ActivateCommitTs/DeactivateCommitTs：激活/去激活状态机；
 *   - WriteTruncateXlogRec：为截断操作写 COMMIT_TS_TRUNCATE WAL 记录。
 */

/*
 * TransactionTreeSetCommitTsData
 *
 * Record the final commit timestamp of transaction entries in the commit log
 * for a transaction and its subtransaction tree, as efficiently as possible.
 *
 * xid is the top level transaction id.
 *
 * subxids is an array of xids of length nsubxids, representing subtransactions
 * in the tree of xid. In various cases nsubxids may be zero.
 * The reason why tracking just the parent xid commit timestamp is not enough
 * is that the subtrans SLRU does not stay valid across crashes (it's not
 * permanent) so we need to keep the information about them here. If the
 * subtrans implementation changes in the future, we might want to revisit the
 * decision of storing timestamp info for each subxid.
 */
/*
 * 中文注释：
 * 为一个顶层事务及其全部子事务批量记录提交时间戳和复制源。这是本模块最主要的
 * 写入入口。
 *
 * 调用场景：
 *   - 普通事务提交：xact.c 的 RecordTransactionCommit() 在写完
 *     XLOG_XACT_COMMIT 之后调用；
 *   - 两阶段事务提交：twophase.c 的 RecordTransactionCommitPrepared()；
 *   - 恢复重放：xact.c 的 xact_redo_commit() 在 redo XLOG_XACT_COMMIT/
 *     XLOG_XACT_COMMIT_PREPARED 时调用，用 WAL 中携带的时间戳重建 SLRU。
 *
 * 参数：
 *   xid       —— 顶层事务 XID，必须有效；
 *   nsubxids  —— 子事务数量，可以为 0；
 *   subxids   —— 子事务 XID 数组，按分配顺序（升序）排列；
 *   timestamp —— 提交时间戳；调用方通常使用事务停止时间或复制源时间；
 *   nodeid    —— 产生该事务的复制源；本地事务为 InvalidReplOriginId。
 *
 * 返回值：无。
 *
 * 实现要点：
 *   - 若模块未激活则直接返回（无操作）。这里的无锁读取是安全的：在备库上只有
 *     恢复进程会调用本函数，而它也是唯一能改变激活标志的进程。
 *   - 子事务必须逐个记录：pg_subtrans 不是永久数据，崩溃后可能丢失，因此不能
 *     只靠“子事务→父事务”的映射在查询时回溯到父事务的时间戳。
 *   - 为了减少加锁次数，把 XID 按所属 SLRU 页分组：每组的第一个 XID 作为
 *     “head”，对每组只加一次页所在 bank 的排他锁，见
 *     SetXidCommitTsInPage()。第一组的 head 是顶层 XID，后续组的 head 是上一组
 *     之后第一个子事务 XID。
 *   - 全部条目写完后，才在 CommitTsLock 保护下更新共享内存缓存
 *     （xidLastCommit/dataLastCommit），并推进 newestCommitTsXid。顺序很重要：
 *     读方看到新的缓存值时，对应 SLRU 条目必须已经可读。
 *   - 本函数不写 WAL：提交记录本身已包含时间和复制源，redo 会重新执行本函数。
 *     因此这里只修改共享缓冲区并置脏，由 checkpoint/LRU 负责落盘。
 */
void
TransactionTreeSetCommitTsData(TransactionId xid, int nsubxids,
							   TransactionId *subxids, TimestampTz timestamp,
							   ReplOriginId nodeid)
{
	int			i;
	TransactionId headxid;
	TransactionId newestXact;

	/*
	 * No-op if the module is not active.
	 *
	 * An unlocked read here is fine, because in a standby (the only place
	 * where the flag can change in flight) this routine is only called by the
	 * recovery process, which is also the only process which can change the
	 * flag.
	 */
	if (!commitTsShared->commitTsActive)
		return;

	/*
	 * Figure out the latest Xid in this batch: either the last subxid if
	 * there's any, otherwise the parent xid.
	 */
	if (nsubxids > 0)
		newestXact = subxids[nsubxids - 1];
	else
		newestXact = xid;

	/*
	 * We split the xids to set the timestamp to in groups belonging to the
	 * same SLRU page; the first element in each such set is its head.  The
	 * first group has the main XID as the head; subsequent sets use the first
	 * subxid not on the previous page as head.  This way, we only have to
	 * lock/modify each SLRU page once.
	 */
	headxid = xid;
	i = 0;
	for (;;)
	{
		int64		pageno = TransactionIdToCTsPage(headxid);
		int			j;

		for (j = i; j < nsubxids; j++)
		{
			if (TransactionIdToCTsPage(subxids[j]) != pageno)
				break;
		}
		/* subxids[i..j] are on the same page as the head */

		SetXidCommitTsInPage(headxid, j - i, subxids + i, timestamp, nodeid,
							 pageno);

		/* if we wrote out all subxids, we're done. */
		if (j >= nsubxids)
			break;

		/*
		 * Set the new head and skip over it, as well as over the subxids we
		 * just wrote.
		 */
		headxid = subxids[j];
		i = j + 1;
	}

	/* update the cached value in shared memory */
	LWLockAcquire(CommitTsLock, LW_EXCLUSIVE);
	commitTsShared->xidLastCommit = xid;
	commitTsShared->dataLastCommit.time = timestamp;
	commitTsShared->dataLastCommit.nodeid = nodeid;

	/* and move forwards our endpoint, if needed */
	if (TransactionIdPrecedes(TransamVariables->newestCommitTsXid, newestXact))
		TransamVariables->newestCommitTsXid = newestXact;
	LWLockRelease(CommitTsLock);
}

/*
 * Record the commit timestamp of transaction entries in the commit log for all
 * entries on a single page.  Atomic only on this page.
 */
/*
 * 中文注释：
 * 在单个 pg_commit_ts 页上，为 head XID 及同一页内的若干子事务写入相同的
 * 提交时间戳和复制源。调用方保证这些 XID 都落在 pageno 这一页。
 *
 * 参数：
 *   xid      —— 该组的 head XID；
 *   nsubxids —— 同页子事务个数；
 *   subxids  —— 同页子事务数组；
 *   ts/nodeid—— 要写入的时间戳和复制源；
 *   pageno   —— 目标页号。
 *
 * 并发/副作用：
 *   - 取得该页所属 bank 的 LWLock 排他锁，保证同页读写在 bank 粒度上互斥；
 *     不同 bank 的页可以并行写入。
 *   - SimpleLruReadPage(..., true, &xid) 会把页读入共享缓冲区（必要时从磁盘
 *     读取），第三个参数表示需要写权限；页面不存在属于错误情况，opaque_data
 *     用于在 I/O 错误时报告相关 XID。
 *   - 只修改共享内存并把 page_dirty 置 true，不写 WAL、不立即刷盘。
 *   - 锁在函数返回前释放；本函数只保证“单页原子”，跨页的一组写入不是原子的。
 */
static void
SetXidCommitTsInPage(TransactionId xid, int nsubxids,
					 TransactionId *subxids, TimestampTz ts,
					 ReplOriginId nodeid, int64 pageno)
{
	LWLock	   *lock = SimpleLruGetBankLock(CommitTsCtl, pageno);
	int			slotno;
	int			i;

	LWLockAcquire(lock, LW_EXCLUSIVE);

	slotno = SimpleLruReadPage(CommitTsCtl, pageno, true, &xid);

	TransactionIdSetCommitTs(xid, ts, nodeid, slotno);
	for (i = 0; i < nsubxids; i++)
		TransactionIdSetCommitTs(subxids[i], ts, nodeid, slotno);

	CommitTsCtl->shared->page_dirty[slotno] = true;

	LWLockRelease(lock);
}

/*
 * Sets the commit timestamp of a single transaction.
 *
 * Caller must hold the correct SLRU bank lock, will be held at exit
 */
/*
 * 中文注释：
 * 把一个事务的 CommitTimestampEntry（时间戳 + 复制源）写入指定 SLRU 页缓冲区
 * 的对应槽位。
 *
 * 参数：
 *   xid    —— 目标事务 XID，必须是普通事务 ID（Assert 检查；Bootstrap/Frozen
 *             XID 不应有提交时间戳）；
 *   ts     —— 提交时间戳；
 *   nodeid —— 复制源 ID；
 *   slotno —— 已由调用方读入并锁定的缓冲区槽号。
 *
 * 并发/副作用：
 *   - 调用方必须持有该页所属 bank 的排他锁，函数返回时锁仍由调用方持有；
 *     本函数自身不加锁。
 *   - 使用 memcpy 写入未对齐的 10 字节槽位，避免对齐相关的未定义行为。
 *   - 只修改共享缓冲区内容，不置脏、不写 WAL；置脏由
 *     SetXidCommitTsInPage() 统一完成。
 */
static void
TransactionIdSetCommitTs(TransactionId xid, TimestampTz ts,
						 ReplOriginId nodeid, int slotno)
{
	int			entryno = TransactionIdToCTsEntry(xid);
	CommitTimestampEntry entry;

	Assert(TransactionIdIsNormal(xid));

	entry.time = ts;
	entry.nodeid = nodeid;

	memcpy(CommitTsCtl->shared->page_buffer[slotno] +
		   SizeOfCommitTimestampEntry * entryno,
		   &entry, SizeOfCommitTimestampEntry);
}

/*
 * Interrogate the commit timestamp of a transaction.
 *
 * The return value indicates whether a commit timestamp record was found for
 * the given xid.  The timestamp value is returned in *ts (which may not be
 * null), and the origin node for the Xid is returned in *nodeid, if it's not
 * null.
 */
/*
 * 中文注释：
 * 查询指定事务的提交时间戳和复制源。这是本模块的主要读取入口，
 * pg_xact_commit_timestamp()、pg_xact_commit_timestamp_origin() 以及逻辑复制
 * 冲突检测等都经由它读取数据。
 *
 * 参数：
 *   xid    —— 要查询的事务 XID；
 *   ts     —— 输出参数，不能为 NULL；找到时写入时间戳，否则写 0；
 *   nodeid —— 可选输出参数；找到时写入复制源，否则写 InvalidReplOriginId。
 *
 * 返回值：
 *   true  —— 找到了该事务的提交时间戳记录；
 *   false —— 没有记录（事务中止、在特性关闭期间提交、已被截断，或 XID 是
 *            Bootstrap/Frozen 等特殊值），此时 *ts 为 0。
 *
 * 错误处理：
 *   - InvalidTransactionId 直接报 ERROR；
 *   - 模块未激活时报 ERROR（error_commit_ts_disabled）；
 *   - 其他特殊 XID（Bootstrap/Frozen）按“远在过去已提交”处理，返回 false。
 *
 * 并发与锁：
 *   - 先在 CommitTsLock 共享锁下检查缓存 xidLastCommit，命中则直接返回，
 *     避免 SLRU 访问；
 *   - 未命中时在锁内读取 oldest/newestCommitTsXid 快照，然后释放
 *     CommitTsLock，再按需读取 SLRU。这两个边界要么都有效、要么都无效
 *     （Assert 检查）；超出区间直接返回 false，避免访问可能已被删除的段文件；
 *   - SimpleLruReadPage_ReadOnly() 返回时持有该页 bank 锁（共享或排他），
 *     复制完条目后必须释放；
 *   - 缓存检查与 SLRU 读取之间没有全局锁：并发的边界推进可能使本次查询返回
 *     false；极端情况下，若记录恰好在区间检查之后被截断，SLRU 层也可能报告
 *     I/O 错误，调用方应把这些情况视为“无法获得时间戳”。
 */
bool
TransactionIdGetCommitTsData(TransactionId xid, TimestampTz *ts,
							 ReplOriginId *nodeid)
{
	int64		pageno = TransactionIdToCTsPage(xid);
	int			entryno = TransactionIdToCTsEntry(xid);
	int			slotno;
	CommitTimestampEntry entry;
	TransactionId oldestCommitTsXid;
	TransactionId newestCommitTsXid;

	if (!TransactionIdIsValid(xid))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("cannot retrieve commit timestamp for transaction %u", xid)));
	else if (!TransactionIdIsNormal(xid))
	{
		/* frozen and bootstrap xids are always committed far in the past */
		*ts = 0;
		if (nodeid)
			*nodeid = InvalidReplOriginId;
		return false;
	}

	LWLockAcquire(CommitTsLock, LW_SHARED);

	/* Error if module not enabled */
	if (!commitTsShared->commitTsActive)
		error_commit_ts_disabled();

	/*
	 * If we're asked for the cached value, return that.  Otherwise, fall
	 * through to read from SLRU.
	 */
	if (commitTsShared->xidLastCommit == xid)
	{
		*ts = commitTsShared->dataLastCommit.time;
		if (nodeid)
			*nodeid = commitTsShared->dataLastCommit.nodeid;

		LWLockRelease(CommitTsLock);
		return *ts != 0;
	}

	oldestCommitTsXid = TransamVariables->oldestCommitTsXid;
	newestCommitTsXid = TransamVariables->newestCommitTsXid;
	/* neither is invalid, or both are */
	Assert(TransactionIdIsValid(oldestCommitTsXid) == TransactionIdIsValid(newestCommitTsXid));
	LWLockRelease(CommitTsLock);

	/*
	 * Return empty if the requested value is outside our valid range.
	 */
	if (!TransactionIdIsValid(oldestCommitTsXid) ||
		TransactionIdPrecedes(xid, oldestCommitTsXid) ||
		TransactionIdPrecedes(newestCommitTsXid, xid))
	{
		*ts = 0;
		if (nodeid)
			*nodeid = InvalidReplOriginId;
		return false;
	}

	/* lock is acquired by SimpleLruReadPage_ReadOnly */
	slotno = SimpleLruReadPage_ReadOnly(CommitTsCtl, pageno, &xid);
	memcpy(&entry,
		   CommitTsCtl->shared->page_buffer[slotno] +
		   SizeOfCommitTimestampEntry * entryno,
		   SizeOfCommitTimestampEntry);

	*ts = entry.time;
	if (nodeid)
		*nodeid = entry.nodeid;

	LWLockRelease(SimpleLruGetBankLock(CommitTsCtl, pageno));
	return *ts != 0;
}

/*
 * Return the Xid of the latest committed transaction.  (As far as this module
 * is concerned, anyway; it's up to the caller to ensure the value is useful
 * for its purposes.)
 *
 * ts and nodeid are filled with the corresponding data; they can be passed
 * as NULL if not wanted.
 */
/*
 * 中文注释：
 * 返回本模块最近记录过提交时间戳的顶层事务 XID，并通过输出参数返回对应
 * 时间戳和复制源（调用方不需要时可传 NULL）。
 *
 * 调用场景：pg_last_committed_xact() 的直接实现；也可供需要“最后提交点”的
 * 内部代码使用。
 *
 * 返回值：缓存中的 xidLastCommit。若模块从未记录过任何提交，返回
 * InvalidTransactionId；此时若 ts/nodeid 非 NULL，则分别写 -infinity 和
 * InvalidReplOriginId。
 *
 * 错误/并发：模块未激活时 ERROR；在 CommitTsLock 共享锁下读取这三个字段，
 * 保证它们彼此一致。注意该值只反映共享内存缓存，未必是磁盘上最新，也未必
 * 对应某个对调用方可见的事务。
 */
TransactionId
GetLatestCommitTsData(TimestampTz *ts, ReplOriginId *nodeid)
{
	TransactionId xid;

	LWLockAcquire(CommitTsLock, LW_SHARED);

	/* Error if module not enabled */
	if (!commitTsShared->commitTsActive)
		error_commit_ts_disabled();

	xid = commitTsShared->xidLastCommit;
	if (ts)
		*ts = commitTsShared->dataLastCommit.time;
	if (nodeid)
		*nodeid = commitTsShared->dataLastCommit.nodeid;
	LWLockRelease(CommitTsLock);

	return xid;
}

/*
 * 中文注释：
 * 在 commit timestamp 模块未激活时抛出统一的 ERROR。
 *
 * 参数：无。
 * 返回值：不返回（总是 ERROR）。
 *
 * 提示信息会区分场景：如果当前处于恢复（RecoveryInProgress()），说明可能是
 * 主库没有设置 track_commit_timestamp，因此提示在 primary 上设置；否则提示在
 * 本机配置中设置。这样备库用户能明白需要修改的是主库配置，而不是备库。
 *
 * 副作用：可能释放当前持有的 LWLocks（PostgreSQL 错误处理会清理锁资源），
 * 因此调用点通常在已经取得必要信息之后。
 */
static void
error_commit_ts_disabled(void)
{
	ereport(ERROR,
			(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
			 errmsg("could not get commit timestamp data"),
			 RecoveryInProgress() ?
			 errhint("Make sure the configuration parameter \"%s\" is set on the primary server.",
					 "track_commit_timestamp") :
			 errhint("Make sure the configuration parameter \"%s\" is set.",
					 "track_commit_timestamp")));
}

/*
 * SQL-callable wrapper to obtain commit time of a transaction
 */
/*
 * 中文注释：
 * SQL 函数 pg_xact_commit_timestamp(xid)：返回指定事务的提交时间戳。
 *
 * 参数：xid（transactionid）—— 要查询的事务 ID。
 * 返回值：timestamptz；没有记录时返回 SQL NULL。
 *
 * 实现：直接调用 TransactionIdGetCommitTsData()，不返回复制源。该函数通常用于
 * 审计、逻辑复制和调试；对中止事务、过老或被截断的事务返回 NULL。
 */
Datum
pg_xact_commit_timestamp(PG_FUNCTION_ARGS)
{
	TransactionId xid = PG_GETARG_TRANSACTIONID(0);
	TimestampTz ts;
	bool		found;

	found = TransactionIdGetCommitTsData(xid, &ts, NULL);

	if (!found)
		PG_RETURN_NULL();

	PG_RETURN_TIMESTAMPTZ(ts);
}


/*
 * pg_last_committed_xact
 *
 * SQL-callable wrapper to obtain some information about the latest
 * committed transaction: transaction ID, timestamp and replication
 * origin.
 */
/*
 * 中文注释：
 * SQL 函数 pg_last_committed_xact()：返回最近一次记录提交时间戳的事务信息，
 * 结果为一行 (xid, timestamp, roident)，分别为事务 ID、提交时间戳和复制源 OID。
 *
 * 实现：
 *   - 调用 GetLatestCommitTsData() 取得缓存值；
 *   - 通过 get_call_result_type() 取得调用方期望的 RECORD 类型描述；
 *   - 若 XID 不是普通事务 ID（模块刚启动/尚未记录任何提交），整行三个字段
 *     都返回 NULL；
 *   - 否则用 heap_form_tuple() 组装并返回。
 *
 * 注意：这是“本模块最近记录”的事务，不一定等于数据库当前最新提交的事务；
 * 例如模块刚激活、或最近提交的事务没有 XID 时，结果可能为 NULL 或较旧。
 */
Datum
pg_last_committed_xact(PG_FUNCTION_ARGS)
{
	TransactionId xid;
	ReplOriginId nodeid;
	TimestampTz ts;
	Datum		values[3];
	bool		nulls[3];
	TupleDesc	tupdesc;
	HeapTuple	htup;

	/* and construct a tuple with our data */
	xid = GetLatestCommitTsData(&ts, &nodeid);

	if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
		elog(ERROR, "return type must be a row type");

	if (!TransactionIdIsNormal(xid))
	{
		memset(nulls, true, sizeof(nulls));
	}
	else
	{
		values[0] = TransactionIdGetDatum(xid);
		nulls[0] = false;

		values[1] = TimestampTzGetDatum(ts);
		nulls[1] = false;

		values[2] = ObjectIdGetDatum((Oid) nodeid);
		nulls[2] = false;
	}

	htup = heap_form_tuple(tupdesc, values, nulls);

	PG_RETURN_DATUM(HeapTupleGetDatum(htup));
}

/*
 * pg_xact_commit_timestamp_origin
 *
 * SQL-callable wrapper to obtain commit timestamp and replication origin
 * of a given transaction.
 */
/*
 * 中文注释：
 * SQL 函数 pg_xact_commit_timestamp_origin(xid)：返回指定事务的提交时间戳和
 * 复制源，结果为一行 (timestamp, roident)。
 *
 * 参数：xid（transactionid）。
 * 返回值：复合类型；没有记录时两个字段均为 NULL。
 *
 * 与 pg_xact_commit_timestamp() 的区别是额外返回复制源，便于判断事务最初在
 * 哪个节点提交（逻辑复制场景）。实现同样委托给
 * TransactionIdGetCommitTsData()。
 */
Datum
pg_xact_commit_timestamp_origin(PG_FUNCTION_ARGS)
{
	TransactionId xid = PG_GETARG_TRANSACTIONID(0);
	ReplOriginId nodeid;
	TimestampTz ts;
	Datum		values[2];
	bool		nulls[2];
	TupleDesc	tupdesc;
	HeapTuple	htup;
	bool		found;

	found = TransactionIdGetCommitTsData(xid, &ts, &nodeid);

	if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
		elog(ERROR, "return type must be a row type");

	if (!found)
	{
		memset(nulls, true, sizeof(nulls));
	}
	else
	{
		values[0] = TimestampTzGetDatum(ts);
		nulls[0] = false;

		values[1] = ObjectIdGetDatum((Oid) nodeid);
		nulls[1] = false;
	}

	htup = heap_form_tuple(tupdesc, values, nulls);

	PG_RETURN_DATUM(HeapTupleGetDatum(htup));
}

/*
 * Number of shared CommitTS buffers.
 *
 * If asked to autotune, use 2MB for every 1GB of shared buffers, up to 8MB.
 * Otherwise just cap the configured amount to be between 16 and the maximum
 * allowed.
 */
/*
 * 中文注释：
 * 计算 pg_commit_ts 使用的共享缓冲区数量。
 *
 * 参数：无（读取全局 GUC commit_timestamp_buffers）。
 * 返回值：缓冲区槽数。
 *
 * 规则：
 *   - commit_timestamp_buffers == 0 时自动调优，调用
 *     SimpleLruAutotuneBuffers(512, 1024)：大约每 1GB shared_buffers 分配
 *     2MB（即 NBuffers/512 个 8KB 槽），上限 8MB（1024 个槽），下限为一个
 *     SLRU bank 且结果按 bank 大小向下取整；
 *   - 否则把显式配置值限制在 [16, SLRU_MAX_ALLOWED_BUFFERS] 之间。
 *
 * 该结果只在启动阶段使用；自动调优后的值会写回 GUC 以便 SHOW 显示。
 */
static int
CommitTsShmemBuffers(void)
{
	/* auto-tune based on shared buffers */
	if (commit_timestamp_buffers == 0)
		return SimpleLruAutotuneBuffers(512, 1024);

	return Min(Max(16, commit_timestamp_buffers), SLRU_MAX_ALLOWED_BUFFERS);
}

/*
 * Register CommitTs shared memory needs at system startup (postmaster start
 * or standalone backend)
 */
/*
 * 中文注释：
 * 共享内存 request 回调：在 postmaster 启动、共享内存尚未分配时登记本模块的
 * 需求。它做两件事：
 *
 *   1. 若 commit_timestamp_buffers 为 0，先根据 shared_buffers 自动计算实际
 *      槽数，并用 SetConfigOption() 把结果写回 GUC（先尝试
 *      PGC_S_DYNAMIC_DEFAULT；若用户在配置文件中显式写了 0 导致覆盖失败，再用
 *      PGC_S_OVERRIDE 强制写入），使后续代码和 SHOW 看到确定值；
 *   2. 调用 SimpleLruRequest() 注册 pg_commit_ts SLRU，指定目录名
 *      "pg_commit_ts"、段名格式（long_segment_names = false，即 %04X 形式的
 *      短段名）、缓冲区数量、截断比较回调、I/O 错误详情回调、sync handler 以及
 *      buffer/bank 两套 LWLock tranche；同时用 ShmemRequestStruct() 申请
 *      CommitTimestampShared。
 *
 * 参数 arg：框架传入的 opaque 参数，未使用。
 * 副作用/并发：仅在启动的单进程阶段执行，无并发问题；此处只登记需求，真正
 * 分配和指针回填由 shmem 框架完成。
 */
static void
CommitTsShmemRequest(void *arg)
{
	/* If auto-tuning is requested, now is the time to do it */
	if (commit_timestamp_buffers == 0)
	{
		char		buf[32];

		snprintf(buf, sizeof(buf), "%d", CommitTsShmemBuffers());
		SetConfigOption("commit_timestamp_buffers", buf, PGC_POSTMASTER,
						PGC_S_DYNAMIC_DEFAULT);

		/*
		 * We prefer to report this value's source as PGC_S_DYNAMIC_DEFAULT.
		 * However, if the DBA explicitly set commit_timestamp_buffers = 0 in
		 * the config file, then PGC_S_DYNAMIC_DEFAULT will fail to override
		 * that and we must force the matter with PGC_S_OVERRIDE.
		 */
		if (commit_timestamp_buffers == 0)	/* failed to apply it? */
			SetConfigOption("commit_timestamp_buffers", buf, PGC_POSTMASTER,
							PGC_S_OVERRIDE);
	}
	Assert(commit_timestamp_buffers != 0);
	SimpleLruRequest(.desc = &CommitTsSlruDesc,
					 .name = "commit_timestamp",
					 .Dir = "pg_commit_ts",
					 .long_segment_names = false,

					 .nslots = CommitTsShmemBuffers(),

					 .PagePrecedes = CommitTsPagePrecedes,
					 .errdetail_for_io_error = commit_ts_errdetail_for_io_error,

					 .sync_handler = SYNC_HANDLER_COMMIT_TS,
					 .buffer_tranche_id = LWTRANCHE_COMMITTS_BUFFER,
					 .bank_tranche_id = LWTRANCHE_COMMITTS_SLRU,
		);

	ShmemRequestStruct(.name = "CommitTs shared",
					   .size = sizeof(CommitTimestampShared),
					   .ptr = (void **) &commitTsShared,
		);
}

/*
 * 中文注释：
 * 共享内存 init 回调：在共享内存分配完成后初始化 CommitTimestampShared。
 *
 * 参数 arg：框架传入的 opaque 参数，未使用。
 *
 * 初值：
 *   - xidLastCommit = InvalidTransactionId；
 *   - dataLastCommit.time = -infinity（TIMESTAMP_NOBEGIN）；
 *   - dataLastCommit.nodeid = InvalidReplOriginId；
 *   - commitTsActive = false（真正的激活由 StartupCommitTs/恢复流程决定）。
 *
 * 另外调用 SlruPagePrecedesUnitTests() 对 CommitTsPagePrecedes() 做启动期自检，
 * 确认页号在 XID 回绕边界上的比较行为符合预期。该函数只在启动时执行，
 * 无并发问题。
 */
static void
CommitTsShmemInit(void *arg)
{
	commitTsShared->xidLastCommit = InvalidTransactionId;
	TIMESTAMP_NOBEGIN(commitTsShared->dataLastCommit.time);
	commitTsShared->dataLastCommit.nodeid = InvalidReplOriginId;
	commitTsShared->commitTsActive = false;

	SlruPagePrecedesUnitTests(CommitTsCtl, COMMIT_TS_XACTS_PER_PAGE);
}

/*
 * GUC check_hook for commit_timestamp_buffers
 */
/*
 * 中文注释：
 * GUC commit_timestamp_buffers 的 check_hook。委托给通用的
 * check_slru_buffers()：要求取值为 SLRU bank 大小（SLRU_BANK_SIZE）的整数倍，
 * 否则给出 GUC_check_errdetail 并拒绝（非负等范围约束由 GUC 定义本身提供）。
 *
 * 参数：newval —— 待检查的新值；extra —— GUC 框架的附加数据，本实现不使用。
 * 返回值：合法返回 true，否则 false（由 GUC 框架报错）。
 */
bool
check_commit_ts_buffers(int *newval, void **extra, GucSource source)
{
	return check_slru_buffers("commit_timestamp_buffers", newval);
}

/*
 * This function must be called ONCE on system install.
 *
 * (The CommitTs directory is assumed to have been created by initdb, and
 * CommitTsShmemInit must have been called already.)
 */
/*
 * 中文注释：
 * 系统安装（initdb/bootstrap）阶段调用一次。与大多数其他 SLRU 不同，这里
 * 无需创建任何段文件：pg_commit_ts 的段在服务器以启用状态启动时由
 * ActivateCommitTs() 按需创建（见下方注释）。因此本函数是空实现。
 *
 * 参数/返回值：无。
 */
void
BootStrapCommitTs(void)
{
	/*
	 * Nothing to do here at present, unlike most other SLRU modules; segments
	 * are created when the server is started with this module enabled. See
	 * ActivateCommitTs.
	 */
}

/*
 * This must be called ONCE during postmaster or standalone-backend startup,
 * after StartupXLOG has initialized TransamVariables->nextXid.
 */
/*
 * 中文注释：
 * postmaster 或 standalone backend 启动期间调用一次，调用点位于 StartupXLOG()
 * 已经根据检查点恢复 TransamVariables->nextXid 之后。调用方只在 pg_control
 * 中记录 track_commit_timestamp 为 true 时才调用本函数；本函数直接调用
 * ActivateCommitTs()，激活模块并确保当前段文件存在。
 *
 * 参数/返回值：无。
 * 注意：此时可能仍处于恢复流程中，最终状态还会由
 * CompleteCommitTsInitialization() 和 CommitTsParameterChange() 调整。
 */
void
StartupCommitTs(void)
{
	ActivateCommitTs();
}

/*
 * This must be called ONCE during postmaster or standalone-backend startup,
 * after recovery has finished.
 */
/*
 * 中文注释：
 * 恢复结束后调用一次，用于确定本模块的最终状态：
 *   - 若 track_commit_timestamp 为 off，则调用 DeactivateCommitTs()，彻底关闭
 *     并删除遗留数据；
 *   - 若为 on，则调用 ActivateCommitTs()，确保模块可用。
 *
 * 为什么需要这一步：主库和备库的激活状态取决于恢复开始时 pg_control 的内容，
 * 以及恢复过程中回放的 XLOG_PARAMETER_CHANGE。恢复结束时本地 GUC 才是最终
 * 权威，必须据此校正一次。
 *
 * 参数/返回值：无。副作用是可能创建或删除 pg_commit_ts 段文件、修改共享内存
 * 状态和 TransamVariables 中的有效区间。
 */
void
CompleteCommitTsInitialization(void)
{
	/*
	 * If the feature is not enabled, turn it off for good.  This also removes
	 * any leftover data.
	 *
	 * Conversely, we activate the module if the feature is enabled.  This is
	 * necessary for primary and standby as the activation depends on the
	 * control file contents at the beginning of recovery or when a
	 * XLOG_PARAMETER_CHANGE is replayed.
	 */
	if (!track_commit_timestamp)
		DeactivateCommitTs();
	else
		ActivateCommitTs();
}

/*
 * Activate or deactivate CommitTs' upon reception of a XLOG_PARAMETER_CHANGE
 * XLog record during recovery.
 */
/*
 * 中文注释：
 * 在恢复过程中回放到 XLOG_PARAMETER_CHANGE 时调用，用主库的
 * track_commit_timestamp 新值同步备库的激活状态。
 *
 * 参数：
 *   newvalue —— 主库上的新取值（true 表示启用）；
 *   oldvalue —— 主库上的旧取值（当前实现未使用，保留以匹配调用约定）。
 *
 * 行为：
 *   - newvalue 为 true 且本地尚未激活：调用 ActivateCommitTs()，以便后续
 *     redo 能写入 commit timestamp；
 *   - newvalue 为 false 且本地已激活：调用 DeactivateCommitTs()，清空状态并
 *     删除历史段文件；
 *   - 其他情况无操作。
 *
 * 并发：只在恢复进程执行，因此可以无锁读取 commitTsActive；这也是
 * TransactionTreeSetCommitTsData() 能无锁读取该标志的依据。
 */
void
CommitTsParameterChange(bool newvalue, bool oldvalue)
{
	/*
	 * If the commit_ts module is disabled in this server and we get word from
	 * the primary server that it is enabled there, activate it so that we can
	 * replay future WAL records involving it; also mark it as active on
	 * pg_control.  If the old value was already set, we already did this, so
	 * don't do anything.
	 *
	 * If the module is disabled in the primary, disable it here too, unless
	 * the module is enabled locally.
	 *
	 * Note this only runs in the recovery process, so an unlocked read is
	 * fine.
	 */
	if (newvalue)
	{
		if (!commitTsShared->commitTsActive)
			ActivateCommitTs();
	}
	else if (commitTsShared->commitTsActive)
		DeactivateCommitTs();
}

/*
 * Activate this module whenever necessary.
 *		This must happen during postmaster or standalone-backend startup,
 *		or during WAL replay anytime the track_commit_timestamp setting is
 *		changed in the primary.
 *
 * The reason why this SLRU needs separate activation/deactivation functions is
 * that it can be enabled/disabled during start and the activation/deactivation
 * on the primary is propagated to the standby via replay. Other SLRUs don't
 * have this property and they can be just initialized during normal startup.
 *
 * This is in charge of creating the currently active segment, if it's not
 * already there.  The reason for this is that the server might have been
 * running with this module disabled for a while and thus might have skipped
 * the normal creation point.
 */
/*
 * 中文注释：
 * 激活本模块，使其可以记录和查询 commit timestamp。调用时机有三种：
 * 服务器启动（StartupCommitTs）、恢复结束按本地 GUC 校正
 * （CompleteCommitTsInitialization）、以及回放主库参数变更
 * （CommitTsParameterChange）。
 *
 * 参数/返回值：无。
 *
 * 主要步骤与设计考虑：
 *   1. bootstrap 模式直接返回：初始化系统目录时不应产生提交时间戳；
 *   2. 若已经激活则立即返回，保证幂等；检查在 CommitTsLock 下进行；
 *   3. 用当前 nextXid 计算活动页号，并写入 SLRU 的 latest_page_number，
 *      使 LRU 不把“当前页”换出；
 *   4. 若 oldestCommitTsXid 为 Invalid（说明上一次运行未启用或刚恢复），
 *      把 oldest/newest 都设为 ReadNextTransactionId()。这样可以避免查询
 *      一段“可能从未写入过时间戳”的 XID 区间；XXX 注释讨论了反复启停的
 *      边界情况；
 *   5. 如果当前页的物理段文件不存在，用 SimpleLruZeroAndWritePage() 创建
 *      并立即写出一个全零页。这样即使服务器在禁用状态下运行了很久、错过了
 *      正常的建页时机，也不会在第一次写入时遇到缺页；
 *   6. 最后在 CommitTsLock 下把 commitTsActive 置 true。必须放在所有准备
 *      工作之后，避免其他进程看到“已激活但页/边界尚未就绪”的中间状态。
 *
 * 并发：该函数可能在不同启动阶段被调用，但通过 CommitTsLock 和幂等检查保证
 * 只有一个调用真正完成初始化；已激活路径几乎无开销。
 */
static void
ActivateCommitTs(void)
{
	TransactionId xid;
	int64		pageno;

	/*
	 * During bootstrap, we should not register commit timestamps so skip the
	 * activation in this case.
	 */
	if (IsBootstrapProcessingMode())
		return;

	/* If we've done this already, there's nothing to do */
	LWLockAcquire(CommitTsLock, LW_EXCLUSIVE);
	if (commitTsShared->commitTsActive)
	{
		LWLockRelease(CommitTsLock);
		return;
	}
	LWLockRelease(CommitTsLock);

	xid = XidFromFullTransactionId(TransamVariables->nextXid);
	pageno = TransactionIdToCTsPage(xid);

	/*
	 * Re-Initialize our idea of the latest page number.
	 */
	pg_atomic_write_u64(&CommitTsCtl->shared->latest_page_number, pageno);

	/*
	 * If CommitTs is enabled, but it wasn't in the previous server run, we
	 * need to set the oldest and newest values to the next Xid; that way, we
	 * will not try to read data that might not have been set.
	 *
	 * XXX does this have a problem if a server is started with commitTs
	 * enabled, then started with commitTs disabled, then restarted with it
	 * enabled again?  It doesn't look like it does, because there should be a
	 * checkpoint that sets the value to InvalidTransactionId at end of
	 * recovery; and so any chance of injecting new transactions without
	 * CommitTs values would occur after the oldestCommitTsXid has been set to
	 * Invalid temporarily.
	 */
	LWLockAcquire(CommitTsLock, LW_EXCLUSIVE);
	if (TransamVariables->oldestCommitTsXid == InvalidTransactionId)
	{
		TransamVariables->oldestCommitTsXid =
			TransamVariables->newestCommitTsXid = ReadNextTransactionId();
	}
	LWLockRelease(CommitTsLock);

	/* Create the current segment file, if necessary */
	if (!SimpleLruDoesPhysicalPageExist(CommitTsCtl, pageno))
		SimpleLruZeroAndWritePage(CommitTsCtl, pageno);

	/* Change the activation status in shared memory. */
	LWLockAcquire(CommitTsLock, LW_EXCLUSIVE);
	commitTsShared->commitTsActive = true;
	LWLockRelease(CommitTsLock);
}

/*
 * Deactivate this module.
 *
 * This must be called when the track_commit_timestamp parameter is turned off.
 * This happens during postmaster or standalone-backend startup, or during WAL
 * replay.
 *
 * Resets CommitTs into invalid state to make sure we don't hand back
 * possibly-invalid data; also removes segments of old data.
 */
/*
 * 中文注释：
 * 关闭本模块：清空共享内存缓存、复位可查询区间，并删除所有 pg_commit_ts
 * 段文件。调用时机为启动时 track_commit_timestamp 为 off，或恢复过程中
 * 主库关闭了该特性。
 *
 * 参数/返回值：无。
 *
 * 步骤：
 *   1. 在 CommitTsLock 排他锁下把 commitTsActive 置 false，并重置
 *      xidLastCommit/dataLastCommit，防止备库在反复激活/去激活后返回令人
 *      困惑的“最后提交事务”；
 *   2. 把 TransamVariables 的 oldest/newestCommitTsXid 都设为
 *      InvalidTransactionId，表示当前没有可查询区间；
 *   3. 调用 SlruScanDirectory(SlruScanDirCbDeleteAll) 删除目录下所有文件。
 *      这是必要的：如果禁用一段时间后再次启用，段文件序列可能出现空洞，
 *      全部删除可以保持整洁（即使保留旧文件，回绕后也会被覆盖）。
 *
 * 并发/性能：整个删除过程持有 CommitTsLock 排他锁，属于非常“重”的做法；
 * 但该路径只在启动/恢复的极少数场景发生，且一旦去激活就不应再有进程访问
 * 本 SLRU，因此可以接受。
 */
static void
DeactivateCommitTs(void)
{
	/*
	 * Cleanup the status in the shared memory.
	 *
	 * We reset everything in the commitTsShared record to prevent user from
	 * getting confusing data about last committed transaction on the standby
	 * when the module was activated repeatedly on the primary.
	 */
	LWLockAcquire(CommitTsLock, LW_EXCLUSIVE);

	commitTsShared->commitTsActive = false;
	commitTsShared->xidLastCommit = InvalidTransactionId;
	TIMESTAMP_NOBEGIN(commitTsShared->dataLastCommit.time);
	commitTsShared->dataLastCommit.nodeid = InvalidReplOriginId;

	TransamVariables->oldestCommitTsXid = InvalidTransactionId;
	TransamVariables->newestCommitTsXid = InvalidTransactionId;

	/*
	 * Remove *all* files.  This is necessary so that there are no leftover
	 * files; in the case where this feature is later enabled after running
	 * with it disabled for some time there may be a gap in the file sequence.
	 * (We can probably tolerate out-of-sequence files, as they are going to
	 * be overwritten anyway when we wrap around, but it seems better to be
	 * tidy.)
	 *
	 * Note that we do this with CommitTsLock acquired in exclusive mode. This
	 * is very heavy-handed, but since this routine can only be called in the
	 * replica and should happen very rarely, we don't worry too much about
	 * it.  Note also that no process should be consulting this SLRU if we
	 * have just deactivated it.
	 */
	(void) SlruScanDirectory(CommitTsCtl, SlruScanDirCbDeleteAll, NULL);

	LWLockRelease(CommitTsLock);
}

/*
 * Perform a checkpoint --- either during shutdown, or on-the-fly
 */
/*
 * 中文注释：
 * 执行 checkpoint 时调用：把 pg_commit_ts 的所有脏页写出。
 *
 * 参数/返回值：无。
 * 实现：SimpleLruWriteAll(CommitTsCtl, true)。第二个参数 allow_redirtied 表示
 * 允许页面在写出过程中被再次弄脏（checkpoint 的典型场景），从而避免因并发
 * 修改而反复重试或触发断言。实际 fsync 可能被推迟到后续的
 * ProcessSyncRequests()，因此函数返回时页面数据未必已经持久化。
 *
 * 并发：SLRU 层内部按 bank 加锁，可与并发的读写操作安全共存。
 */
void
CheckPointCommitTs(void)
{
	/*
	 * Write dirty CommitTs pages to disk.  This may result in sync requests
	 * queued for later handling by ProcessSyncRequests(), as part of the
	 * checkpoint.
	 */
	SimpleLruWriteAll(CommitTsCtl, true);
}

/*
 * Make sure that CommitTs has room for a newly-allocated XID.
 *
 * NB: this is called while holding XidGenLock.  We want it to be very fast
 * most of the time; even when it's not so fast, no actual I/O need happen
 * unless we're forced to write out a dirty CommitTs or xlog page to make room
 * in shared memory.
 *
 * NB: the current implementation relies on track_commit_timestamp being
 * PGC_POSTMASTER.
 */
/*
 * 中文注释：
 * 为新分配的 XID 确保 pg_commit_ts 有对应空间。每个 SLRU 页第一次被使用时，
 * 在这里把该页清零并写一条 COMMIT_TS_ZEROPAGE WAL 记录。
 *
 * 调用场景：
 *   - varsup.c 的 GetNewTransactionId() 在推进 nextXid 之前调用；
 *   - 调用时持有 XidGenLock，因此本函数必须尽量快，且不能反向获取可能被其他
 *     路径以相反顺序持有的锁。
 *
 * 参数：newestXact —— 刚刚分配（或即将分配）的 XID。
 *
 * 快速路径：
 *   - 模块未激活则直接返回。这里的无锁读取是安全的：本函数只会在主库的
 *     GetNewTransactionId() 中调用（Assert(!InRecovery)），而主库上激活状态
 *     在启动后不再变化。
 *   - 只有页内第一个条目（entry 0）才需要建页；但 XID 回绕后 page 0 的第一个
 *     XID 是 FirstNormalTransactionId 而非 0，因此要单独判断。
 *
 * 慢路径：
 *   - 取目标页 bank 的排他锁，调用 SimpleLruZeroPage() 在共享缓冲区中建立
 *     全零页（该函数内部会更新 latest_page_number 并置脏）；
 *   - 若非恢复模式，写 COMMIT_TS_ZEROPAGE WAL 记录，保证崩溃恢复时页的清零
 *     动作可重放。回绕后页面会被复用，如果不记录清零动作，新 XID 可能读到
 *     上一轮遗留的陈旧时间戳；而普通提交记录本身并不包含“清页”信息；
 *   - WAL 记录在释放 bank 锁之前插入，顺序不能颠倒；
 *   - 本函数不立即把页写盘，脏页由 checkpoint/LRU 处理。
 */
void
ExtendCommitTs(TransactionId newestXact)
{
	int64		pageno;
	LWLock	   *lock;

	/*
	 * Nothing to do if module not enabled.  Note we do an unlocked read of
	 * the flag here, which is okay because this routine is only called from
	 * GetNewTransactionId, which is never called in a standby.
	 */
	Assert(!InRecovery);
	if (!commitTsShared->commitTsActive)
		return;

	/*
	 * No work except at first XID of a page.  But beware: just after
	 * wraparound, the first XID of page zero is FirstNormalTransactionId.
	 */
	if (TransactionIdToCTsEntry(newestXact) != 0 &&
		!TransactionIdEquals(newestXact, FirstNormalTransactionId))
		return;

	pageno = TransactionIdToCTsPage(newestXact);

	lock = SimpleLruGetBankLock(CommitTsCtl, pageno);

	LWLockAcquire(lock, LW_EXCLUSIVE);

	/* Zero the page ... */
	SimpleLruZeroPage(CommitTsCtl, pageno);

	/* and make a WAL entry about that, unless we're in REDO */
	if (!InRecovery)
		XLogSimpleInsertInt64(RM_COMMIT_TS_ID, COMMIT_TS_ZEROPAGE, pageno);

	LWLockRelease(lock);
}

/*
 * Remove all CommitTs segments before the one holding the passed
 * transaction ID.
 *
 * Note that we don't need to flush XLOG here.
 */
/*
 * 中文注释：
 * 删除包含 oldestXact 的段之前的全部 pg_commit_ts 段文件。VACUUM 计算完全局
 * frozenXID 后调用（见 vacuum.c 的 vac_truncate_clog），用于回收空间，并保证
 * 不再查询已经无法保证正确性的老事务。
 *
 * 参数：oldestXact —— 仍然需要保留时间戳的最老 XID；其所在页之前的页都可删除。
 *
 * 返回值：无。
 *
 * 实现：
 *   1. cutoffPage = TransactionIdToCTsPage(oldestXact)；
 *   2. 先用 SlruScanDirectory(SlruScanDirCbReportPresence) 快速判断是否真的
 *      有可删除的文件；没有就直接返回，避免无谓地写 WAL；
 *   3. 写 COMMIT_TS_TRUNCATE WAL 记录（其中包含 cutoffPage 和 oldestXact），
 *      使备库在 redo 时执行同样的截断并推进 oldestCommitTsXid；
 *   4. 调用 SimpleLruTruncate() 删除 cutoffPage 之前的段。
 *
 * 并发/持久化：
 *   - 调用方（VACUUM）已经在更早的步骤推进了 oldestCommitTsXid，因此新的查询
 *     会在区间检查处直接返回 NULL，而不是先访问即将被删除的文件；不过区间检查
 *     与文件删除之间没有锁保护，已经通过区间检查的并发查询理论上仍可能遇到
 *     文件已被删除的窄窗口；
 *   - 截断是幂等的、可重复执行；这里不强制 flush WAL，最坏情况下重启后重新
 *     VACUUM 会再次完成截断，不影响正确性；
 *   - SLRU 层会处理正在使用的页和并发读写，调用者不需要额外加 CommitTsLock。
 */
void
TruncateCommitTs(TransactionId oldestXact)
{
	int64		cutoffPage;

	/*
	 * The cutoff point is the start of the segment containing oldestXact. We
	 * pass the *page* containing oldestXact to SimpleLruTruncate.
	 */
	cutoffPage = TransactionIdToCTsPage(oldestXact);

	/* Check to see if there's any files that could be removed */
	if (!SlruScanDirectory(CommitTsCtl, SlruScanDirCbReportPresence,
						   &cutoffPage))
		return;					/* nothing to remove */

	/* Write XLOG record */
	WriteTruncateXlogRec(cutoffPage, oldestXact);

	/* Now we can remove the old CommitTs segment(s) */
	SimpleLruTruncate(CommitTsCtl, cutoffPage);
}

/*
 * Set the limit values between which commit TS can be consulted.
 */
/*
 * 中文注释：
 * 设置可以查询 commit timestamp 的 XID 区间 [oldestXact, newestXact]。
 *
 * 调用场景：
 *   - StartupXLOG() 根据 checkpoint 中保存的 oldestCommitTsXid/
 *     newestCommitTsXid 恢复边界（正常启动）；
 *   - 引导/无检查点启动时用 (InvalidTransactionId, InvalidTransactionId)
 *     表示“无有效区间”。
 *
 * 参数：oldestXact/newestXact —— 新的边界；两者应同时有效或同时无效。
 *
 * 行为：
 *   - 若当前边界有效，只允许“收紧”区间：oldest 只能增大（朝更新的 XID 方向
 *     推进），newest 只能减小，避免把已经明确的范围扩大后读到未写入/已删除的
 *     数据；
 *   - 若当前 oldest 无效，则断言 newest 也无效，然后直接设置两者。
 *
 * 并发：整个判断和赋值在 CommitTsLock 排他锁下完成，防止与并发提交推进
 * newestCommitTsXid，或与截断推进 oldestCommitTsXid 冲突。
 */
void
SetCommitTsLimit(TransactionId oldestXact, TransactionId newestXact)
{
	/*
	 * Be careful not to overwrite values that are either further into the
	 * "future" or signal a disabled committs.
	 */
	LWLockAcquire(CommitTsLock, LW_EXCLUSIVE);
	if (TransamVariables->oldestCommitTsXid != InvalidTransactionId)
	{
		if (TransactionIdPrecedes(TransamVariables->oldestCommitTsXid, oldestXact))
			TransamVariables->oldestCommitTsXid = oldestXact;
		if (TransactionIdPrecedes(newestXact, TransamVariables->newestCommitTsXid))
			TransamVariables->newestCommitTsXid = newestXact;
	}
	else
	{
		Assert(TransamVariables->newestCommitTsXid == InvalidTransactionId);
		TransamVariables->oldestCommitTsXid = oldestXact;
		TransamVariables->newestCommitTsXid = newestXact;
	}
	LWLockRelease(CommitTsLock);
}

/*
 * Move forwards the oldest commitTS value that can be consulted
 */
/*
 * 中文注释：
 * 单调地向前推进可查询区间下界 oldestCommitTsXid。
 *
 * 调用场景：
 *   - 回放 COMMIT_TS_TRUNCATE 时（commit_ts_redo）；
 *   - VACUUM 截断 pg_commit_ts 之前（vacuum.c 的 vac_truncate_clog），先缩小
 *     可查询区间，随后即使查询命中已被删除的段文件也会直接返回 NULL，而不是
 *     报“文件不存在”。
 *
 * 参数：oldestXact —— 新的下界。
 * 返回值：无。
 *
 * 行为：只有在当前值有效且确实早于 oldestXact 时才推进；Invalid 状态保持
 * Invalid（模块未启用/无有效区间），不会因为截断而“激活”区间。
 * 并发：在 CommitTsLock 排他锁下读改写，保证与提交、SetCommitTsLimit 的
 * 更新不丢失。
 */
void
AdvanceOldestCommitTsXid(TransactionId oldestXact)
{
	LWLockAcquire(CommitTsLock, LW_EXCLUSIVE);
	if (TransamVariables->oldestCommitTsXid != InvalidTransactionId &&
		TransactionIdPrecedes(TransamVariables->oldestCommitTsXid, oldestXact))
		TransamVariables->oldestCommitTsXid = oldestXact;
	LWLockRelease(CommitTsLock);
}


/*
 * Decide whether a commitTS page number is "older" for truncation purposes.
 * Analogous to CLOGPagePrecedes().
 *
 * At default BLCKSZ, (1 << 31) % COMMIT_TS_XACTS_PER_PAGE == 128.  This
 * introduces differences compared to CLOG and the other SLRUs having (1 <<
 * 31) % per_page == 0.  This function never tests exactly
 * TransactionIdPrecedes(x-2^31, x).  When the system reaches xidStopLimit,
 * there are two possible counts of page boundaries between oldestXact and the
 * latest XID assigned, depending on whether oldestXact is within the first
 * 128 entries of its page.  Since this function doesn't know the location of
 * oldestXact within page2, it returns false for one page that actually is
 * expendable.  This is a wider (yet still negligible) version of the
 * truncation opportunity that CLOGPagePrecedes() cannot recognize.
 *
 * For the sake of a worked example, number entries with decimal values such
 * that page1==1 entries range from 1.0 to 1.999.  Let N+0.15 be the number of
 * pages that 2^31 entries will span (N is an integer).  If oldestXact=N+2.1,
 * then the final safe XID assignment leaves newestXact=1.95.  We keep page 2,
 * because entry=2.85 is the border that toggles whether entries precede the
 * last entry of the oldestXact page.  While page 2 is expendable at
 * oldestXact=N+2.1, it would be precious at oldestXact=N+2.9.
 */
/*
 * 中文注释：
 * 判断两个 pg_commit_ts 页号在回绕意义下的先后关系，供 SLRU 截断
 * （SimpleLruTruncate）决定哪些页/段更老。语义类似 CLOGPagePrecedes()，
 * 但 commit timestamp 每页条目数不能整除 2^31，需要特殊处理。
 *
 * 参数：page1/page2 —— 两个 SLRU 页号（int64）。
 * 返回值：page1 在逻辑上早于 page2 时返回 true。
 *
 * 实现：把页号换算成“该页第一个普通 XID 附近”的 32 位 XID，再用
 * TransactionIdPrecedes() 做回绕安全比较。换算时加上
 * FirstNormalTransactionId + 1，避免落在特殊 XID 上；第二个比较额外加上
 * COMMIT_TS_XACTS_PER_PAGE - 1，覆盖整页范围。
 *
 * 精度说明：默认 BLCKSZ 下 (1 << 31) % COMMIT_TS_XACTS_PER_PAGE == 128，
 * 与 CLOG 等每页条目数能整除 2^31 的 SLRU 不同。本函数不知道 oldestXact
 * 在页内的具体位置，因此在极少数边界情况下会把一个实际可删除的页判为
 * “不可删除”。这只造成多保留一个页（及其段）的微小空间浪费，不影响正确性；
 * 上面的英文注释给出了具体数值示例。
 */
static bool
CommitTsPagePrecedes(int64 page1, int64 page2)
{
	TransactionId xid1;
	TransactionId xid2;

	xid1 = ((TransactionId) page1) * COMMIT_TS_XACTS_PER_PAGE;
	xid1 += FirstNormalTransactionId + 1;
	xid2 = ((TransactionId) page2) * COMMIT_TS_XACTS_PER_PAGE;
	xid2 += FirstNormalTransactionId + 1;

	return (TransactionIdPrecedes(xid1, xid2) &&
			TransactionIdPrecedes(xid1, xid2 + COMMIT_TS_XACTS_PER_PAGE - 1));
}

/*
 * 中文注释：
 * SLRU I/O 错误详情回调：当读取/写入 pg_commit_ts 页失败时，SLRU 层会把注册
 * 时传入的 opaque_data（这里是目标 XID 的指针）转交本函数，用于在错误报告中
 * 补充“无法访问哪个事务的提交时间戳”。
 *
 * 参数：opaque_data —— 指向 TransactionId 的指针（调用点传入 &xid）。
 * 返回值：errdetail() 生成的错误详情字符串（由错误报告机制管理生命周期）。
 *
 * 注意：该回调只做格式化，不进行 I/O；opaque_data 在调用期间必须保持有效。
 */
static int
commit_ts_errdetail_for_io_error(const void *opaque_data)
{
	TransactionId xid = *(const TransactionId *) opaque_data;

	return errdetail("Could not access commit timestamp of transaction %u.", xid);
}

/*
 * Write a TRUNCATE xlog record
 */
/*
 * 中文注释：
 * 写一条 COMMIT_TS_TRUNCATE WAL 记录，供备库/崩溃恢复重放截断动作。
 *
 * 参数：
 *   pageno    —— 截断边界页号（保留此页及之后的页）；
 *   oldestXid —— 对应的最老仍有效 XID，重放时用于推进 oldestCommitTsXid。
 * 返回值：无。
 *
 * 实现：填充 xl_commit_ts_truncate，XLogBeginInsert() + XLogRegisterData()
 * + XLogInsert(RM_COMMIT_TS_ID, COMMIT_TS_TRUNCATE)。记录没有备份块，
 * 也不需要 XLogFlush()（调用方 TruncateCommitTs 不要求同步落盘）。
 *
 * 并发：XLogInsert 自身线程安全；记录中不含任何指针，重放只依赖页号和 XID。
 */
static void
WriteTruncateXlogRec(int64 pageno, TransactionId oldestXid)
{
	xl_commit_ts_truncate xlrec;

	xlrec.pageno = pageno;
	xlrec.oldestXid = oldestXid;

	XLogBeginInsert();
	XLogRegisterData(&xlrec, SizeOfCommitTsTruncate);
	(void) XLogInsert(RM_COMMIT_TS_ID, COMMIT_TS_TRUNCATE);
}

/*
 * CommitTS resource manager's routines
 */
/*
 * 中文注释：
 * rmgr COMMIT_TS 的 redo 入口，处理 COMMIT_TS_ZEROPAGE 与
 * COMMIT_TS_TRUNCATE 两种记录。普通提交时间戳的写入不在这里：它们由
 * XLOG_XACT_COMMIT/XLOG_XACT_COMMIT_PREPARED 的 redo 调用
 * TransactionTreeSetCommitTsData() 完成。
 *
 * 参数：record —— 当前 WAL 记录及其解码状态。
 * 返回值：无；遇到未知 op code 时 PANIC。
 *
 * 分支：
 *   - COMMIT_TS_ZEROPAGE：从记录数据中读取 int64 页号，调用
 *     SimpleLruZeroAndWritePage() 在共享缓冲区中清零并立即写盘。立即写出可以
 *     确保即使该页之后没有被修改（因而是干净的、不会被 LRU 写回），对应段
 *     文件也确实存在，后续读取该页中的 XID 时不会报文件不存在；
 *   - COMMIT_TS_TRUNCATE：读取 xl_commit_ts_truncate，先
 *     AdvanceOldestCommitTsXid() 收紧可查询区间，再把 latest_page_number
 *     设为记录中的页号以绕过 SimpleLruTruncate() 的“不能截断当前页”健全性
 *     检查（recovery 阶段该值尚未初始化），最后执行截断。
 *
 * 并发/恢复注意：
 *   - 该函数只在恢复进程（startup process）中执行，不存在并发写入；
 *   - 断言记录不包含 backup block（本模块的 WAL 记录从不使用块引用）；
 *   - redo 必须幂等：重复回放同样的 ZEROPAGE/TRUNCATE 记录结果一致。
 */
void
commit_ts_redo(XLogReaderState *record)
{
	uint8		info = XLogRecGetInfo(record) & ~XLR_INFO_MASK;

	/* Backup blocks are not used in commit_ts records */
	Assert(!XLogRecHasAnyBlockRefs(record));

	if (info == COMMIT_TS_ZEROPAGE)
	{
		int64		pageno;

		memcpy(&pageno, XLogRecGetData(record), sizeof(pageno));
		SimpleLruZeroAndWritePage(CommitTsCtl, pageno);
	}
	else if (info == COMMIT_TS_TRUNCATE)
	{
		xl_commit_ts_truncate *trunc = (xl_commit_ts_truncate *) XLogRecGetData(record);

		AdvanceOldestCommitTsXid(trunc->oldestXid);

		/*
		 * During XLOG replay, latest_page_number isn't set up yet; insert a
		 * suitable value to bypass the sanity test in SimpleLruTruncate.
		 */
		pg_atomic_write_u64(&CommitTsCtl->shared->latest_page_number,
							trunc->pageno);

		SimpleLruTruncate(CommitTsCtl, trunc->pageno);
	}
	else
		elog(PANIC, "commit_ts_redo: unknown op code %u", info);
}

/*
 * Entrypoint for sync.c to sync commit_ts files.
 */
/*
 * 中文注释：
 * sync.c 的 sync handler 入口（SYNC_HANDLER_COMMIT_TS），用于在
 * checkpoint/fsync 请求处理阶段同步 pg_commit_ts 的段文件。
 *
 * 参数：
 *   ftag —— 文件标识（包含 segno 等），由 sync 机制保存；
 *   path —— 输出缓冲区，用于返回拼装好的完整文件路径。
 * 返回值：SlruSyncFileTag() 的返回值：0 表示 fsync 成功，-1 表示失败并设置
 * errno。
 *
 * 实现：直接委托 SlruSyncFileTag()，由 SLRU 层根据 CommitTsCtl 的目录和段号
 * 命名规则构造路径并执行 pg_fsync。
 */
int
committssyncfiletag(const FileTag *ftag, char *path)
{
	return SlruSyncFileTag(CommitTsCtl, ftag, path);
}
