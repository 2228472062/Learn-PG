/*-------------------------------------------------------------------------
 *
 * clog.c
 *		PostgreSQL transaction-commit-log manager
 *
 * This module stores two bits per transaction regarding its commit/abort
 * status; the status for four transactions fit in a byte.
 *
 * This would be a pretty simple abstraction on top of slru.c, except that
 * for performance reasons we allow multiple transactions that are
 * committing concurrently to form a queue, so that a single process can
 * update the status for all of them within a single lock acquisition run.
 *
 * XLOG interactions: this module generates an XLOG record whenever a new
 * CLOG page is initialized to zeroes.  Other writes of CLOG come from
 * recording of transaction commit or abort in xact.c, which generates its
 * own XLOG records for these events and will re-perform the status update
 * on redo; so we need make no additional XLOG entry here.  For synchronous
 * transaction commits, the XLOG is guaranteed flushed through the XLOG commit
 * record before we are called to log a commit, so the WAL rule "write xlog
 * before data" is satisfied automatically.  However, for async commits we
 * must track the latest LSN affecting each CLOG page, so that we can flush
 * XLOG that far and satisfy the WAL rule.  We don't have to worry about this
 * for aborts (whether sync or async), since the post-crash assumption would
 * be that such transactions failed anyway.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/clog.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 的事务提交日志（CLOG，Commit Log）管理器。CLOG 自
 * PostgreSQL 10 起在磁盘上的目录名为 pg_xact（旧版本为 pg_clog），本模块是
 * 该目录以及对共享内存中 CLOG 缓冲区进行读写的底层实现。
 *
 * 一、状态编码与布局
 *   - 每个事务只占 2 bit，一个字节容纳 4 个事务，一个 BLCKSZ 的页可记录
 *     CLOG_XACTS_PER_PAGE 个事务；状态取值为 0=IN_PROGRESS、1=COMMITTED、
 *     2=ABORTED、3=SUB_COMMITTED（见 clog.h 的 XidStatus）。
 *   - 页号由 XID 直接除以 CLOG_XACTS_PER_PAGE 得到，因此页和 SLRU segment 的
 *     编号会随 32 位 XID 一起回卷；文件由 slru.c 按 segment 管理，CLOG 使用
 *     短文件名（long_segment_names = false）。
 *   - 页内偏移由 XID 对 CLOG_XACTS_PER_PAGE 取模，再分解为字节下标和字节内
 *     的 bit 偏移；这些换算都是纯算术，不需要加锁。
 *
 * 二、SLRU 缓冲与并发
 *   - CLOG 页面存放在共享内存的 SLRU 缓冲池中，按页号映射到多个 bank，每个
 *     bank 有一把 LWLock（LWTRANCHE_XACT_SLRU）；访问某页前必须持有对应 bank
 *     的锁（读可共享，写必须独占）。slru.c 负责 LRU 淘汰、读写磁盘和 fsync。
 *   - 每个缓冲槽还带有一组 group_lsn[]，按每 CLOG_XACTS_PER_LSN_GROUP（32）个
 *     事务一组记录“影响该组的最新异步提交 LSN”，用于在写页前满足 WAL 规则。
 *
 * 三、组提交 / 异步提交
 *   - 同步提交：xact.c 在调用本模块前已把提交 WAL 记录 flush 到磁盘，因此这里
 *     只需更新状态位。
 *   - 异步提交（synchronous_commit = off 等）：提交记录可能尚未落盘，状态位
 *     绝不能先于对应 WAL 落盘。TransactionIdSetPageStatusInternal 会把
 *     write_ok=false 传给 SimpleLruReadPage 以等待正在进行的页写完成，并把
 *     提交 LSN 记入 group_lsn[]；slru.c 在真正写页前会先 XLogFlush 到该页所有
 *     group LSN 的最大值。
 *   - 多个后端同时提交时，TransactionGroupUpdateXidStatus 让一个 leader 在
 *     一次 bank 锁持有期间代所有 follower 更新状态，以减少锁争用（group
 *     commit 优化）；该优化只影响性能，不改变持久化语义。
 *
 * 四、WAL 交互与崩溃恢复
 *   - 本模块只在两种情况下自己产生 WAL：新 CLOG 页被清零时写 CLOG_ZEROPAGE，
 *     截断时写 CLOG_TRUNCATE；事务提交/中止本身由 xact.c 的提交/中止 WAL 记录
 *     描述，恢复时由 clog_redo / xact_redo 重新执行状态更新，因此这里不再为
 *     每次状态变更写 WAL。
 *   - 由于 WAL 规则“先写日志、后写数据”，异步提交路径必须借助 group_lsn 和
 *     slru.c 的写前 flush；同步提交则由调用者保证提交记录已经落盘。
 *   - 恢复期间 lsn 参数通常为 InvalidXLogRecPtr，不更新 group_lsn；恢复结束后
 *     的第一次状态变更会重新建立正确的 LSN。
 *
 * 五、查询、扩展与截断
 *   - TransactionIdGetStatus 供 transam.c 的 TransactionLogFetch 查询状态，并
 *     返回一个“足够大”的 LSN：flush 到该 LSN 即可保证提交记录已落盘；对早已
 *     换出到磁盘的旧页，该值可能是 InvalidXLogRecPtr。
 *   - GetNewTransactionId 在推进 nextXid 之前调用 ExtendCLOG，保证新 XID 对应
 *     的 CLOG 页已经存在；首次使用某页首 XID 时清零并写 CLOG_ZEROPAGE。
 *   - VACUUM 推进 datfrozenxid 后调用 TruncateCLOG 删除不再需要的 segment；
 *     截断前先把 oldestClogXid 推进（受 XactTruncationLock 保护）并 flush
 *     CLOG_TRUNCATE WAL 记录，避免崩溃后仍有未冻结元组引用已删除的 CLOG。
 *
 * 六、与其他模块的关系
 *   - transam.c：CLOG 的高层接口，负责状态缓存、子事务状态递归解析，并调用
 *     TransactionIdSetTreeStatus / TransactionIdGetStatus；
 *   - xact.c：在提交/中止以及两阶段提交恢复路径写事务 WAL 记录，然后调用
 *     transam.c 的 TransactionIdCommitTree / TransactionIdAbortTree 落到 CLOG；
 *   - varsup.c：分配 XID 前调用 ExtendCLOG，截断时调用 AdvanceOldestClogXid；
 *   - slru.c：提供页缓冲、bank 锁、LRU、磁盘 I/O 与 truncate 的通用机制；
 *   - xlog.c：启动时调用 BootStrapCLOG/StartupCLOG/TrimCLOG，检查点调用
 *     CheckPointCLOG；
 *   - procarray.c 与可见性判断：通过 transam.c 读取 CLOG，决定元组可见性。
 *
 * 七、设计思想
 *   - 每个事务仅 2 bit，使 CLOG 体量远小于数据本身，可长期保留并快速随机查询；
 *   - 状态变更不单独写 WAL，而是依附于事务提交/中止记录，减少 WAL 体积；
 *   - 用 SLRU + bank 锁把热点分散到多个 page/bank，并用 group commit 把多次
 *     状态更新合并到一次锁获取中；
 *   - 对异步提交用 group LSN 精确表达“数据页写盘前必须 flush 到哪”，在保证
 *     持久性的同时避免不必要的 WAL flush；
 *   - 截断采用“先推进安全下界、再 flush 截断 WAL、最后删文件”的顺序，兼顾
 *     并发查询安全、崩溃恢复和 Hot Standby 的目录膨胀控制。
 */
#include "postgres.h"

#include "access/clog.h"
#include "access/slru.h"
#include "access/transam.h"
#include "access/xlog.h"
#include "access/xloginsert.h"
#include "access/xlogutils.h"
#include "miscadmin.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "storage/proc.h"
#include "storage/subsystems.h"
#include "storage/sync.h"
#include "utils/guc_hooks.h"
#include "utils/wait_event.h"

/*
 * Defines for CLOG page sizes.  A page is the same BLCKSZ as is used
 * everywhere else in Postgres.
 *
 * Note: because TransactionIds are 32 bits and wrap around at 0xFFFFFFFF,
 * CLOG page numbering also wraps around at 0xFFFFFFFF/CLOG_XACTS_PER_PAGE,
 * and CLOG segment numbering at
 * 0xFFFFFFFF/CLOG_XACTS_PER_PAGE/SLRU_PAGES_PER_SEGMENT.  We need take no
 * explicit notice of that fact in this module, except when comparing segment
 * and page numbers in TruncateCLOG (see CLOGPagePrecedes).
 */
/*
 * 中文注释：
 * CLOG 的物理布局常量：
 *   - 一页大小就是 BLCKSZ，与 PostgreSQL 其他页一致；
 *   - 每事务 2 bit，每字节 4 个事务，因此一页可记录 CLOG_XACTS_PER_PAGE 个事务；
 *   - 页号 = XID / CLOG_XACTS_PER_PAGE，segment 号 = 页号 / SLRU_PAGES_PER_SEGMENT，
 *     两者都会随 32 位 XID 回卷而回卷；
 *   - 本模块一般不需要显式处理回卷，唯一例外是 TruncateCLOG 中比较页号新旧，
 *     必须使用 CLOGPagePrecedes 的模运算比较。
 */

/* We need two bits per xact, so four xacts fit in a byte */
/*
 * 中文注释：
 * 2 bit 状态编码相关宏：
 *   CLOG_BITS_PER_XACT  —— 每个事务占用的 bit 数（2）；
 *   CLOG_XACTS_PER_BYTE —— 每字节可容纳的事务数（4）；
 *   CLOG_XACTS_PER_PAGE —— 每页可容纳的事务数（BLCKSZ * 4）；
 *   CLOG_XACT_BITMASK   —— 提取 2 bit 状态的掩码（0x3）。
 * 状态值本身定义在 clog.h：0=IN_PROGRESS、1=COMMITTED、2=ABORTED、3=SUB_COMMITTED。
 */
#define CLOG_BITS_PER_XACT	2
#define CLOG_XACTS_PER_BYTE 4
#define CLOG_XACTS_PER_PAGE (BLCKSZ * CLOG_XACTS_PER_BYTE)
#define CLOG_XACT_BITMASK	((1 << CLOG_BITS_PER_XACT) - 1)

/*
 * Because space used in CLOG by each transaction is so small, we place a
 * smaller limit on the number of CLOG buffers than SLRU allows.  No other
 * SLRU needs this.
 */
/*
 * 中文注释：
 * CLOG 允许的最大共享缓冲槽数。由于每个事务只占 2 bit，CLOG 的空间消耗远小于
 * 其他 SLRU，因此这里在 SLRU 通用上限之外再加一个更小的上限：最多覆盖半个
 * XID 空间（同一时刻最老与最新 XID 的跨度不可能达到 2^32，实际可用范围是
 * 2^31）所对应的页数。这样既能满足缓存需求，又避免为几乎不可能出现的页数
 * 预留共享内存；其他 SLRU 没有这个限制。
 */
#define CLOG_MAX_ALLOWED_BUFFERS \
	Min(SLRU_MAX_ALLOWED_BUFFERS, \
		(((MaxTransactionId / 2) + (CLOG_XACTS_PER_PAGE - 1)) / CLOG_XACTS_PER_PAGE))


/*
 * Although we return an int64 the actual value can't currently exceed
 * 0xFFFFFFFF/CLOG_XACTS_PER_PAGE.
 */
/*
 * 中文注释：
 * 把 32 位事务 ID 映射为 CLOG 页号，即 xid / CLOG_XACTS_PER_PAGE。
 *
 * 参数 xid：任意 TransactionId（包括特殊 XID，按无符号整数参与除法）。
 * 返回值：int64 页号。使用 int64 是为了让 SLRU 的页号运算不因 32 位 XID 回卷
 * 而溢出；实际取值范围不会超过 0xFFFFFFFF / CLOG_XACTS_PER_PAGE。
 *
 * 该函数是纯算术、无副作用、无锁；页内字节/bit 偏移由下面的宏继续计算。
 * 注意：页号会随 XID 回卷而回卷，比较页号新旧时必须使用 CLOGPagePrecedes 的
 * 模运算语义，不能直接比大小。
 */
static inline int64
TransactionIdToPage(TransactionId xid)
{
	return xid / (int64) CLOG_XACTS_PER_PAGE;
}

/*
 * 中文注释：
 * 页内定位宏（均为纯算术，调用者无需加锁）：
 *   TransactionIdToPgIndex —— XID 在页内的序号（0 .. CLOG_XACTS_PER_PAGE-1）；
 *   TransactionIdToByte    —— 该序号对应的字节下标；
 *   TransactionIdToBIndex  —— 该 XID 在字节内的序号（0..3），乘以
 *                             CLOG_BITS_PER_XACT 即得到 2 bit 状态的移位量。
 * 这些宏的参数会被求值多次，调用时应传简单变量而非带副作用的表达式。
 */
#define TransactionIdToPgIndex(xid) ((xid) % (TransactionId) CLOG_XACTS_PER_PAGE)
#define TransactionIdToByte(xid)	(TransactionIdToPgIndex(xid) / CLOG_XACTS_PER_BYTE)
#define TransactionIdToBIndex(xid)	((xid) % (TransactionId) CLOG_XACTS_PER_BYTE)

/* We store the latest async LSN for each group of transactions */
/*
 * 中文注释：
 * 异步提交 LSN 分组：
 *   CLOG_XACTS_PER_LSN_GROUP —— 每 32 个连续 XID 共享一个 group LSN 槽；
 *   CLOG_LSNS_PER_PAGE       —— 每个 CLOG 页对应的 LSN 槽数；
 *   GetLSNIndex(slotno,xid)  —— 由缓冲槽号和 XID 计算 group_lsn[] 下标。
 * 这样每页只需 CLOG_XACTS_PER_PAGE/32 个 LSN，而不是每事务一个，显著节省共享
 * 内存；代价是返回的 LSN 可能比真实提交记录更晚（同组中后续事务的 LSN），但
 * 作为“flush 到这里即可保证提交记录落盘”的上界仍然正确。索引依赖 slotno，
 * 必须在持有该槽所属 bank 锁时使用。
 */
#define CLOG_XACTS_PER_LSN_GROUP	32	/* keep this a power of 2 */
#define CLOG_LSNS_PER_PAGE	(CLOG_XACTS_PER_PAGE / CLOG_XACTS_PER_LSN_GROUP)

#define GetLSNIndex(slotno, xid)	((slotno) * CLOG_LSNS_PER_PAGE + \
	((xid) % (TransactionId) CLOG_XACTS_PER_PAGE) / CLOG_XACTS_PER_LSN_GROUP)

/*
 * The number of subtransactions below which we consider to apply clog group
 * update optimization.  Testing reveals that the number higher than this can
 * hurt performance.
 */
/*
 * 中文注释：
 * 启用 CLOG group update 优化所允许的最大子事务数。子事务过多时，leader 代
 * 其他后端更新状态的临界区会变长、缓存行竞争也更严重，实测超过该阈值反而降低
 * 性能，因此 TransactionIdSetPageStatus 只在 nsubxids 不超过它时才尝试组更新。
 * 该值必须不超过 PGPROC_MAX_CACHED_SUBXIDS，否则 leader 无法从 PGPROC 的
 * 子事务缓存中取得完整子事务列表（函数内有 StaticAssertDecl 检查）。
 */
#define THRESHOLD_SUBTRANS_CLOG_OPT	5

/*
 * Link to shared-memory data structures for CLOG control
 */
/*
 * 中文注释：
 * 下面是本文件内部函数的前置声明，供 CLOGShmemCallbacks 以及彼此调用使用：
 *   CLOGShmemRequest/CLOGShmemInit —— shmem 子系统的 request/init 回调；
 *   CLOGPagePrecedes               —— SLRU 的页新旧比较回调；
 *   clog_errdetail_for_io_error    —— SLRU I/O 错误时的 errdetail 回调；
 *   WriteTruncateXlogRec           —— 写并 flush CLOG_TRUNCATE WAL 记录；
 *   TransactionId* / set_status_by_pages / TransactionGroupUpdateXidStatus
 *                                  —— 状态写入与 group commit 的内部实现。
 * 具体语义见各自的定义处。
 */
static void CLOGShmemRequest(void *arg);
static void CLOGShmemInit(void *arg);
static bool CLOGPagePrecedes(int64 page1, int64 page2);
static int	clog_errdetail_for_io_error(const void *opaque_data);

/*
 * 中文注释：
 * 注册给共享内存子系统的 CLOG 回调集合（通过 subsystemlist.h 中的
 * PG_SHMEM_SUBSYSTEM(CLOGShmemCallbacks) 引入）。request_fn 在 postmaster
 * 启动、共享内存尚未分配时登记 SLRU 所需的共享内存；init_fn 在共享内存挂接
 * 完成后执行断言构建下的页号比较自检。这两个回调都只在启动阶段单进程执行。
 */
const ShmemCallbacks CLOGShmemCallbacks = {
	.request_fn = CLOGShmemRequest,
	.init_fn = CLOGShmemInit,
};

/*
 * 中文注释：
 * CLOG 的 SLRU 描述符（进程私有）。SimpleLruRequest 会把 options 复制到共享内存
 * 并初始化 desc->shared 与 bank 数量；之后所有 CLOG 操作都通过 XactCtl 访问
 * 共享缓冲、bank 锁、group_lsn 和 latest_page_number。
 * XactCtl 只是取地址的便捷宏，不产生额外存储。
 */
static SlruDesc XactSlruDesc;

#define XactCtl (&XactSlruDesc)


static void WriteTruncateXlogRec(int64 pageno, TransactionId oldestXact,
								 Oid oldestXactDb);
static void TransactionIdSetPageStatus(TransactionId xid, int nsubxids,
									   TransactionId *subxids, XidStatus status,
									   XLogRecPtr lsn, int64 pageno,
									   bool all_xact_same_page);
static void TransactionIdSetStatusBit(TransactionId xid, XidStatus status,
									  XLogRecPtr lsn, int slotno);
static void set_status_by_pages(int nsubxids, TransactionId *subxids,
								XidStatus status, XLogRecPtr lsn);
static bool TransactionGroupUpdateXidStatus(TransactionId xid,
											XidStatus status, XLogRecPtr lsn, int64 pageno);
static void TransactionIdSetPageStatusInternal(TransactionId xid, int nsubxids,
											   TransactionId *subxids, XidStatus status,
											   XLogRecPtr lsn, int64 pageno);


/*
 * TransactionIdSetTreeStatus
 *
 * Record the final state of transaction entries in the commit log for
 * a transaction and its subtransaction tree. Take care to ensure this is
 * efficient, and as atomic as possible.
 *
 * xid is a single xid to set status for. This will typically be
 * the top level transactionid for a top level commit or abort. It can
 * also be a subtransaction when we record transaction aborts.
 *
 * subxids is an array of xids of length nsubxids, representing subtransactions
 * in the tree of xid. In various cases nsubxids may be zero.
 *
 * lsn must be the WAL location of the commit record when recording an async
 * commit.  For a synchronous commit it can be InvalidXLogRecPtr, since the
 * caller guarantees the commit record is already flushed in that case.  It
 * should be InvalidXLogRecPtr for abort cases, too.
 *
 * In the commit case, atomicity is limited by whether all the subxids are in
 * the same CLOG page as xid.  If they all are, then the lock will be grabbed
 * only once, and the status will be set to committed directly.  Otherwise
 * we must
 *	 1. set sub-committed all subxids that are not on the same page as the
 *		main xid
 *	 2. atomically set committed the main xid and the subxids on the same page
 *	 3. go over the first bunch again and set them committed
 * Note that as far as concurrent checkers are concerned, main transaction
 * commit as a whole is still atomic.
 *
 * Example:
 *		TransactionId t commits and has subxids t1, t2, t3, t4
 *		t is on page p1, t1 is also on p1, t2 and t3 are on p2, t4 is on p3
 *		1. update pages2-3:
 *					page2: set t2,t3 as sub-committed
 *					page3: set t4 as sub-committed
 *		2. update page1:
 *					page1: set t,t1 as committed
 *		3. update pages2-3:
 *					page2: set t2,t3 as committed
 *					page3: set t4 as committed
 *
 * NB: this is a low-level routine and is NOT the preferred entry point
 * for most uses; functions in transam.c are the intended callers.
 *
 * XXX Think about issuing POSIX_FADV_WILLNEED on pages that we will need,
 * but aren't yet in cache, as well as hinting pages not to fall out of
 * cache yet.
 */
/*
 * 中文注释：
 * 记录一个顶层事务及其子事务树在 CLOG 中的最终状态（提交或中止），是
 * transam.c 中 TransactionIdCommitTree / TransactionIdAsyncCommitTree /
 * TransactionIdAbortTree 的底层实现。
 *
 * 参数：
 *   xid       —— 顶层事务的 XID；中止路径也可能是某个子事务的 XID；
 *   nsubxids  —— 子事务个数，可以为 0；
 *   subxids   —— 子事务 XID 数组，长度 nsubxids；
 *   status    —— 只能是 TRANSACTION_STATUS_COMMITTED 或 ABORTED；
 *   lsn       —— 异步提交时为提交 WAL 记录的 LSN；同步提交或中止时为
 *                InvalidXLogRecPtr（同步提交由调用者保证 WAL 已 flush）。
 *
 * 返回值：无。
 *
 * 原子性策略：先找出与父事务同页的连续子事务前缀。
 *   - 若全部子事务都与父事务同页，则一次 TransactionIdSetPageStatus 调用即可，
 *     在该页锁内先写 sub-committed 再写 committed，对外表现为原子提交；
 *   - 否则先把不在首页的子事务标为 SUB_COMMITTED，再一次性提交父事务和首页
 *     子事务，最后把其余页的子事务补成 COMMITTED。并发观察者看到父事务提交时，
 *     所有子事务至少已是 sub-committed；不会看到“子事务已提交而父事务未提交”
 *     的非法组合。中止路径不需要中间状态，直接按页写 ABORTED。
 *
 * 并发/恢复：每次写页都由 TransactionIdSetPageStatus 获取对应 SLRU bank 锁；
 * 本函数自身不写 WAL，状态变更由 xact.c 的提交/中止 WAL 记录在恢复时重放。
 * 若子事务跨页，函数执行期间并非全局原子，但上述顺序保证了对外的可见性语义。
 */
void
TransactionIdSetTreeStatus(TransactionId xid, int nsubxids,
						   TransactionId *subxids, XidStatus status, XLogRecPtr lsn)
{
	int64		pageno = TransactionIdToPage(xid);	/* get page of parent */
	int			i;

	Assert(status == TRANSACTION_STATUS_COMMITTED ||
		   status == TRANSACTION_STATUS_ABORTED);

	/*
	 * See how many subxids, if any, are on the same page as the parent, if
	 * any.
	 */
	for (i = 0; i < nsubxids; i++)
	{
		if (TransactionIdToPage(subxids[i]) != pageno)
			break;
	}

	/*
	 * Do all items fit on a single page?
	 */
	if (i == nsubxids)
	{
		/*
		 * Set the parent and all subtransactions in a single call
		 */
		TransactionIdSetPageStatus(xid, nsubxids, subxids, status, lsn,
								   pageno, true);
	}
	else
	{
		int			nsubxids_on_first_page = i;

		/*
		 * If this is a commit then we care about doing this correctly (i.e.
		 * using the subcommitted intermediate status).  By here, we know
		 * we're updating more than one page of clog, so we must mark entries
		 * that are *not* on the first page so that they show as subcommitted
		 * before we then return to update the status to fully committed.
		 *
		 * To avoid touching the first page twice, skip marking subcommitted
		 * for the subxids on that first page.
		 */
		if (status == TRANSACTION_STATUS_COMMITTED)
			set_status_by_pages(nsubxids - nsubxids_on_first_page,
								subxids + nsubxids_on_first_page,
								TRANSACTION_STATUS_SUB_COMMITTED, lsn);

		/*
		 * Now set the parent and subtransactions on same page as the parent,
		 * if any
		 */
		pageno = TransactionIdToPage(xid);
		TransactionIdSetPageStatus(xid, nsubxids_on_first_page, subxids, status,
								   lsn, pageno, false);

		/*
		 * Now work through the rest of the subxids one clog page at a time,
		 * starting from the second page onwards, like we did above.
		 */
		set_status_by_pages(nsubxids - nsubxids_on_first_page,
							subxids + nsubxids_on_first_page,
							status, lsn);
	}
}

/*
 * Helper for TransactionIdSetTreeStatus: set the status for a bunch of
 * transactions, chunking in the separate CLOG pages involved. We never
 * pass the whole transaction tree to this function, only subtransactions
 * that are on different pages to the top level transaction id.
 */
/*
 * 中文注释：
 * TransactionIdSetTreeStatus 的辅助函数：把一组“不在父事务所在页”的子事务按
 * CLOG 页分组，逐页调用 TransactionIdSetPageStatus 写状态。
 *
 * 参数：
 *   nsubxids —— 子事务个数，必须大于 0（函数一开始就解引用 subxids[0]）；
 *   subxids  —— 子事务 XID 数组；
 *   status   —— 要写入的状态（SUB_COMMITTED 或 COMMITTED/ABORTED）；
 *   lsn      —— 异步提交 LSN，含义同 TransactionIdSetTreeStatus。
 *
 * 实现：顺序扫描数组，把页号相同的一段作为一个批次；每批把 xid 参数传
 * InvalidTransactionId，表示本批只写子事务、没有父事务。返回值：无。
 *
 * 副作用：可能触发 CLOG 页的读入、置脏和 bank 锁等待；不写 WAL。
 * 注意：函数按“连续同页”分段，并不要求整个数组按页排序；同一页的 XID 如果被
 * 其他页隔开，会产生多个批次，但每个子事务最终都会被覆盖。
 */
static void
set_status_by_pages(int nsubxids, TransactionId *subxids,
					XidStatus status, XLogRecPtr lsn)
{
	int64		pageno = TransactionIdToPage(subxids[0]);
	int			offset = 0;
	int			i = 0;

	Assert(nsubxids > 0);		/* else the pageno fetch above is unsafe */

	while (i < nsubxids)
	{
		int			num_on_page = 0;
		int64		nextpageno;

		do
		{
			nextpageno = TransactionIdToPage(subxids[i]);
			if (nextpageno != pageno)
				break;
			num_on_page++;
			i++;
		} while (i < nsubxids);

		TransactionIdSetPageStatus(InvalidTransactionId,
								   num_on_page, subxids + offset,
								   status, lsn, pageno, false);
		offset = i;
		pageno = nextpageno;
	}
}

/*
 * Record the final state of transaction entries in the commit log for all
 * entries on a single page.  Atomic only on this page.
 */
/*
 * 中文注释：
 * 记录单页 CLOG 上若干事务的最终状态，是状态写入的并发控制入口。
 *
 * 参数：
 *   xid                 —— 父事务 XID；只有子事务时为 InvalidTransactionId；
 *   nsubxids/subxids    —— 同页子事务及其个数；
 *   status              —— COMMITTED / ABORTED / SUB_COMMITTED；
 *   lsn                 —— 异步提交 LSN，同步提交或中止时为 InvalidXLogRecPtr；
 *   pageno              —— 目标 CLOG 页号；
 *   all_xact_same_page  —— 父事务与全部子事务是否都在本页，只有为 true 时才
 *                          允许尝试 group update（否则 PGPROC 中缓存的子事务
 *                          列表与本页更新范围不一致）。
 *
 * 流程：
 *   1. 计算目标页所属 bank 的锁；
 *   2. 若满足 group update 条件（同页、xid 等于 MyProc->xid、子事务数不超过
 *      THRESHOLD_SUBTRANS_CLOG_OPT、且与 MyProc 缓存的子事务完全一致），先尝试
 *      LWLockConditionalAcquire：拿到锁就直接更新并返回，避免睡眠；
 *   3. 拿不到锁则调用 TransactionGroupUpdateXidStatus，把本次更新交给 leader
 *      代做；若因目标页与组内其他成员不同而返回 false，则退回普通路径；
 *   4. 普通路径阻塞获取 bank 锁，调用 TransactionIdSetPageStatusInternal。
 *
 * 返回值：无。副作用：可能睡眠等待锁或 group leader，修改 CLOG 页并置脏；
 * 不直接写 WAL。并发安全性依赖调用者传入的 MyProc 子事务缓存与本次更新一致。
 */
static void
TransactionIdSetPageStatus(TransactionId xid, int nsubxids,
						   TransactionId *subxids, XidStatus status,
						   XLogRecPtr lsn, int64 pageno,
						   bool all_xact_same_page)
{
	LWLock	   *lock;

	/* Can't use group update when PGPROC overflows. */
	StaticAssertDecl(THRESHOLD_SUBTRANS_CLOG_OPT <= PGPROC_MAX_CACHED_SUBXIDS,
					 "group clog threshold less than PGPROC cached subxids");

	/* Get the SLRU bank lock for the page we are going to access. */
	lock = SimpleLruGetBankLock(XactCtl, pageno);

	/*
	 * When there is contention on the SLRU bank lock we need, we try to group
	 * multiple updates; a single leader process will perform transaction
	 * status updates for multiple backends so that the number of times the
	 * bank lock needs to be acquired is reduced.
	 *
	 * For this optimization to be safe, the XID and subxids in MyProc must be
	 * the same as the ones for which we're setting the status.  Check that
	 * this is the case.
	 *
	 * For this optimization to be efficient, we shouldn't have too many
	 * sub-XIDs and all of the XIDs for which we're adjusting clog should be
	 * on the same page.  Check those conditions, too.
	 */
	if (all_xact_same_page && xid == MyProc->xid &&
		nsubxids <= THRESHOLD_SUBTRANS_CLOG_OPT &&
		nsubxids == MyProc->subxidStatus.count &&
		(nsubxids == 0 ||
		 memcmp(subxids, MyProc->subxids.xids,
				nsubxids * sizeof(TransactionId)) == 0))
	{
		/*
		 * If we can immediately acquire the lock, we update the status of our
		 * own XID and release the lock.  If not, try use group XID update. If
		 * that doesn't work out, fall back to waiting for the lock to perform
		 * an update for this transaction only.
		 */
		if (LWLockConditionalAcquire(lock, LW_EXCLUSIVE))
		{
			/* Got the lock without waiting!  Do the update. */
			TransactionIdSetPageStatusInternal(xid, nsubxids, subxids, status,
											   lsn, pageno);
			LWLockRelease(lock);
			return;
		}
		else if (TransactionGroupUpdateXidStatus(xid, status, lsn, pageno))
		{
			/* Group update mechanism has done the work. */
			return;
		}

		/* Fall through only if update isn't done yet. */
	}

	/* Group update not applicable, or couldn't accept this page number. */
	LWLockAcquire(lock, LW_EXCLUSIVE);
	TransactionIdSetPageStatusInternal(xid, nsubxids, subxids, status,
									   lsn, pageno);
	LWLockRelease(lock);
}

/*
 * Record the final state of transaction entry in the commit log
 *
 * We don't do any locking here; caller must handle that.
 */
/*
 * 中文注释：
 * 在已持有目标页 SLRU bank 独占锁的前提下，真正把状态位写入 CLOG 页。
 * 调用者必须保证锁已持有（函数内有 Assert）；本函数不负责加锁/解锁。
 *
 * 参数含义同 TransactionIdSetPageStatus。xid 可以是 InvalidTransactionId，
 * 此时只写子事务（用于 set_status_by_pages 的 SUB_COMMITTED 阶段）。
 *
 * 关键点：
 *   - 若 lsn 有效（异步提交），向 SimpleLruReadPage 传 write_ok=false，等待该
 *     槽位上正在进行的页写完成；否则本次修改可能被那次写带到磁盘，而对应 WAL
 *     尚未 flush，破坏 WAL 规则。lsn 无效（同步提交/中止/恢复）时允许在写进
 *     行中修改，因为不介意更新提前落盘。
 *   - 提交时先把同页子事务标为 SUB_COMMITTED，再标父事务为 COMMITTED，最后
 *     统一标子事务为 COMMITTED；这样即使页正在被写出、部分 bit 落盘，也不会
 *     出现子事务已提交而父事务未提交的可见状态。
 *   - 状态位写完后把 page_dirty 置 true，由 SLRU 在淘汰/检查点时写盘。
 *
 * 返回值：无。崩溃恢复：本函数不写 WAL；恢复时由 xact.c 的 WAL 记录重放调用。
 */
static void
TransactionIdSetPageStatusInternal(TransactionId xid, int nsubxids,
								   TransactionId *subxids, XidStatus status,
								   XLogRecPtr lsn, int64 pageno)
{
	int			slotno;
	int			i;

	Assert(status == TRANSACTION_STATUS_COMMITTED ||
		   status == TRANSACTION_STATUS_ABORTED ||
		   (status == TRANSACTION_STATUS_SUB_COMMITTED && !TransactionIdIsValid(xid)));
	Assert(LWLockHeldByMeInMode(SimpleLruGetBankLock(XactCtl, pageno),
								LW_EXCLUSIVE));

	/*
	 * If we're doing an async commit (ie, lsn is valid), then we must wait
	 * for any active write on the page slot to complete.  Otherwise our
	 * update could reach disk in that write, which will not do since we
	 * mustn't let it reach disk until we've done the appropriate WAL flush.
	 * But when lsn is invalid, it's OK to scribble on a page while it is
	 * write-busy, since we don't care if the update reaches disk sooner than
	 * we think.
	 */
	slotno = SimpleLruReadPage(XactCtl, pageno, !XLogRecPtrIsValid(lsn), &xid);

	/*
	 * Set the main transaction id, if any.
	 *
	 * If we update more than one xid on this page while it is being written
	 * out, we might find that some of the bits go to disk and others don't.
	 * If we are updating commits on the page with the top-level xid that
	 * could break atomicity, so we subcommit the subxids first before we mark
	 * the top-level commit.
	 */
	if (TransactionIdIsValid(xid))
	{
		/* Subtransactions first, if needed ... */
		if (status == TRANSACTION_STATUS_COMMITTED)
		{
			for (i = 0; i < nsubxids; i++)
			{
				Assert(XactCtl->shared->page_number[slotno] == TransactionIdToPage(subxids[i]));
				TransactionIdSetStatusBit(subxids[i],
										  TRANSACTION_STATUS_SUB_COMMITTED,
										  lsn, slotno);
			}
		}

		/* ... then the main transaction */
		TransactionIdSetStatusBit(xid, status, lsn, slotno);
	}

	/* Set the subtransactions */
	for (i = 0; i < nsubxids; i++)
	{
		Assert(XactCtl->shared->page_number[slotno] == TransactionIdToPage(subxids[i]));
		TransactionIdSetStatusBit(subxids[i], status, lsn, slotno);
	}

	XactCtl->shared->page_dirty[slotno] = true;
}

/*
 * Subroutine for TransactionIdSetPageStatus, q.v.
 *
 * When we cannot immediately acquire the SLRU bank lock in exclusive mode at
 * commit time, add ourselves to a list of processes that need their XIDs
 * status update.  The first process to add itself to the list will acquire
 * the lock in exclusive mode and set transaction status as required on behalf
 * of all group members.  This avoids a great deal of contention when many
 * processes are trying to commit at once, since the lock need not be
 * repeatedly handed off from one committing process to the next.
 *
 * Returns true when transaction status has been updated in clog; returns
 * false if we decided against applying the optimization because the page
 * number we need to update differs from those processes already waiting.
 */
/*
 * 中文注释：
 * CLOG group commit 的核心：当无法立刻拿到目标页的 bank 锁时，把当前后端挂到
 * 一个由 ProcGlobal->clogGroupFirst 串起来的单向链表中，由链表的第一个成员
 * （leader）一次性代所有同页成员更新状态，从而把多次锁获取合并为一次。
 *
 * 参数：
 *   xid    —— 本后端要更新的事务 XID，必须有效；
 *   status —— 目标状态（通常为 COMMITTED，但接口也用于其他状态）；
 *   lsn    —— 异步提交 LSN；
 *   pageno —— 本后端目标 CLOG 页。
 *
 * 返回值：
 *   true  —— 本后端的状态已由 leader（可能是自己）更新完毕；
 *   false —— 链表头的成员目标页与本后端不同，未加入组，调用者应走普通加锁路径。
 *
 * 实现要点：
 *   1. 把 xid/status/page/lsn 以及 PGPROC 中缓存的子事务信息作为“委托数据”；
 *   2. 用 CAS 把 MyProcNumber 压入 clogGroupFirst；入链前若发现 head 的页号与
 *      自己不同，则撤销成员标记并返回 false，避免一个组跨页降低效率；
 *   3. 若入链时 head 非空，说明自己是 follower：在 proc->sem 上睡眠，直到
 *      leader 清掉 clogGroupMember；被多唤醒的次数用 extraWaits 归还信号量；
 *   4. 若 head 为空，自己是 leader：获取自己页的 bank 锁，用 atomic exchange
 *      一次性摘下列表头（避免逐元素 pop 的 ABA 问题），沿 clogGroupNext 遍历，
 *      对每个成员调用 TransactionIdSetPageStatusInternal；若成员页属于不同 bank，
 *      切换 bank 锁（极少见，但必须正确）；最后释放锁；
 *   5. 释放锁后再逐个清成员标记并 PGSemaphoreUnlock 唤醒 follower，避免在锁内
 *      做唤醒以缩短临界区。
 *
 * 并发/恢复注意：
 *   - clogGroupMember / clogGroupNext / clogGroupMember* 都是共享内存中的易失
 *     状态，崩溃后无需恢复；每个事务的 WAL 提交记录和 lsn 已由各自后端保证，
 *     leader 只是代写 CLOG 位。
 *   - 入链检查与真正入链之间存在竞态：leader 可能在检查后切换到了另一页的组，
 *     此时该组会包含不同页的成员；代码通过遍历时切换 bank 锁来兼容，只是效率
 *     略差，不影响正确性。
 *   - 等待事件为 WAIT_EVENT_XACT_GROUP_UPDATE；follower 醒来后必须看到 leader
 *     在清标记前写入的所有 CLOG 修改，代码用 pg_write_barrier() 保证顺序。
 */
static bool
TransactionGroupUpdateXidStatus(TransactionId xid, XidStatus status,
								XLogRecPtr lsn, int64 pageno)
{
	PGPROC	   *proc = MyProc;
	uint32		nextidx;
	uint32		wakeidx;
	int64		prevpageno;
	LWLock	   *prevlock = NULL;

	/* We should definitely have an XID whose status needs to be updated. */
	Assert(TransactionIdIsValid(xid));

	/*
	 * Prepare to add ourselves to the list of processes needing a group XID
	 * status update.
	 */
	proc->clogGroupMember = true;
	proc->clogGroupMemberXid = xid;
	proc->clogGroupMemberXidStatus = status;
	proc->clogGroupMemberPage = pageno;
	proc->clogGroupMemberLsn = lsn;

	/*
	 * We put ourselves in the queue by writing MyProcNumber to
	 * ProcGlobal->clogGroupFirst.  However, if there's already a process
	 * listed there, we compare our pageno with that of that process; if it
	 * differs, we cannot participate in the group, so we return for caller to
	 * update pg_xact in the normal way.
	 *
	 * If we're not the first process in the list, we must follow the leader.
	 * We do this by storing the data we want updated in our PGPROC entry
	 * where the leader can find it, then going to sleep.
	 *
	 * If no process is already in the list, we're the leader; our first step
	 * is to lock the SLRU bank to which our page belongs, then we close out
	 * the group by resetting the list pointer from ProcGlobal->clogGroupFirst
	 * (this lets other processes set up other groups later); finally we do
	 * the SLRU updates, release the SLRU bank lock, and wake up the sleeping
	 * processes.
	 *
	 * If another group starts to update a page in a different SLRU bank, they
	 * can proceed concurrently, since the bank lock they're going to use is
	 * different from ours.  If another group starts to update a page in the
	 * same bank as ours, they wait until we release the lock.
	 */
	nextidx = pg_atomic_read_u32(&ProcGlobal->clogGroupFirst);

	while (true)
	{
		/*
		 * Add the proc to list, if the clog page where we need to update the
		 * current transaction status is same as group leader's clog page.
		 *
		 * There is a race condition here, which is that after doing the below
		 * check and before adding this proc's clog update to a group, the
		 * group leader might have already finished the group update for this
		 * page and becomes group leader of another group, updating a
		 * different page.  This will lead to a situation where a single group
		 * can have different clog page updates.  This isn't likely and will
		 * still work, just less efficiently -- we handle this case by
		 * switching to a different bank lock in the loop below.
		 */
		if (nextidx != INVALID_PROC_NUMBER &&
			GetPGProcByNumber(nextidx)->clogGroupMemberPage != proc->clogGroupMemberPage)
		{
			/*
			 * Ensure that this proc is not a member of any clog group that
			 * needs an XID status update.
			 */
			proc->clogGroupMember = false;
			pg_atomic_write_u32(&proc->clogGroupNext, INVALID_PROC_NUMBER);
			return false;
		}

		pg_atomic_write_u32(&proc->clogGroupNext, nextidx);

		if (pg_atomic_compare_exchange_u32(&ProcGlobal->clogGroupFirst,
										   &nextidx,
										   (uint32) MyProcNumber))
			break;
	}

	/*
	 * If the list was not empty, the leader will update the status of our
	 * XID. It is impossible to have followers without a leader because the
	 * first process that has added itself to the list will always have
	 * nextidx as INVALID_PROC_NUMBER.
	 */
	if (nextidx != INVALID_PROC_NUMBER)
	{
		int			extraWaits = 0;

		/* Sleep until the leader updates our XID status. */
		pgstat_report_wait_start(WAIT_EVENT_XACT_GROUP_UPDATE);
		for (;;)
		{
			/* acts as a read barrier */
			PGSemaphoreLock(proc->sem);
			if (!proc->clogGroupMember)
				break;
			extraWaits++;
		}
		pgstat_report_wait_end();

		Assert(pg_atomic_read_u32(&proc->clogGroupNext) == INVALID_PROC_NUMBER);

		/* Fix semaphore count for any absorbed wakeups */
		while (extraWaits-- > 0)
			PGSemaphoreUnlock(proc->sem);
		return true;
	}

	/*
	 * By here, we know we're the leader process.  Acquire the SLRU bank lock
	 * that corresponds to the page we originally wanted to modify.
	 */
	prevpageno = proc->clogGroupMemberPage;
	prevlock = SimpleLruGetBankLock(XactCtl, prevpageno);
	LWLockAcquire(prevlock, LW_EXCLUSIVE);

	/*
	 * Now that we've got the lock, clear the list of processes waiting for
	 * group XID status update, saving a pointer to the head of the list.
	 * (Trying to pop elements one at a time could lead to an ABA problem.)
	 *
	 * At this point, any processes trying to do this would create a separate
	 * group.
	 */
	nextidx = pg_atomic_exchange_u32(&ProcGlobal->clogGroupFirst,
									 INVALID_PROC_NUMBER);

	/* Remember head of list so we can perform wakeups after dropping lock. */
	wakeidx = nextidx;

	/* Walk the list and update the status of all XIDs. */
	while (nextidx != INVALID_PROC_NUMBER)
	{
		PGPROC	   *nextproc = GetPGProcByNumber(nextidx);
		int64		thispageno = nextproc->clogGroupMemberPage;

		/*
		 * If the page to update belongs to a different bank than the previous
		 * one, exchange bank lock to the new one.  This should be quite rare,
		 * as described above.
		 *
		 * (We could try to optimize this by waking up the processes for which
		 * we have already updated the status while we exchange the lock, but
		 * the code doesn't do that at present.  I think it'd require
		 * additional bookkeeping, making the common path slower in order to
		 * improve an infrequent case.)
		 */
		if (thispageno != prevpageno)
		{
			LWLock	   *lock = SimpleLruGetBankLock(XactCtl, thispageno);

			if (prevlock != lock)
			{
				LWLockRelease(prevlock);
				LWLockAcquire(lock, LW_EXCLUSIVE);
			}
			prevlock = lock;
			prevpageno = thispageno;
		}

		/*
		 * Transactions with more than THRESHOLD_SUBTRANS_CLOG_OPT sub-XIDs
		 * should not use group XID status update mechanism.
		 */
		Assert(nextproc->subxidStatus.count <= THRESHOLD_SUBTRANS_CLOG_OPT);

		TransactionIdSetPageStatusInternal(nextproc->clogGroupMemberXid,
										   nextproc->subxidStatus.count,
										   nextproc->subxids.xids,
										   nextproc->clogGroupMemberXidStatus,
										   nextproc->clogGroupMemberLsn,
										   nextproc->clogGroupMemberPage);

		/* Move to next proc in list. */
		nextidx = pg_atomic_read_u32(&nextproc->clogGroupNext);
	}

	/* We're done with the lock now. */
	if (prevlock != NULL)
		LWLockRelease(prevlock);

	/*
	 * Now that we've released the lock, go back and wake everybody up.  We
	 * don't do this under the lock so as to keep lock hold times to a
	 * minimum.
	 *
	 * (Perhaps we could do this in two passes, the first setting
	 * clogGroupNext to invalid while saving the semaphores to an array, then
	 * a single write barrier, then another pass unlocking the semaphores.)
	 */
	while (wakeidx != INVALID_PROC_NUMBER)
	{
		PGPROC	   *wakeproc = GetPGProcByNumber(wakeidx);

		wakeidx = pg_atomic_read_u32(&wakeproc->clogGroupNext);
		pg_atomic_write_u32(&wakeproc->clogGroupNext, INVALID_PROC_NUMBER);

		/* ensure all previous writes are visible before follower continues. */
		pg_write_barrier();

		wakeproc->clogGroupMember = false;

		if (wakeproc != MyProc)
			PGSemaphoreUnlock(wakeproc->sem);
	}

	return true;
}

/*
 * Sets the commit status of a single transaction.
 *
 * Caller must hold the corresponding SLRU bank lock, will be held at exit.
 */
/*
 * 中文注释：
 * 在指定 CLOG 缓冲槽中设置单个 XID 的 2 bit 状态，并更新对应的 group LSN。
 * 调用者必须持有该页所属 bank 的独占锁（函数内有 Assert），且 slotno 必须
 * 确实对应 xid 所在页；本函数不做加锁和页读取。
 *
 * 参数：
 *   xid    —— 要设置状态的事务 ID；
 *   status —— 目标 XidStatus；
 *   lsn    —— 异步提交 LSN；InvalidXLogRecPtr 表示不需要更新 group_lsn；
 *   slotno —— 已读入共享内存的 CLOG 页槽号。
 *
 * 位操作：定位字节后，先取出原 2 bit 做合法性检查，再用掩码清除并写入新值；
 * 由于持有 bank 独占锁，读-改-写是原子的，不需要额外原子指令。
 *
 * 恢复特例：恢复重放时，某些事务可能已经被其他 WAL 记录正确标记为
 * COMMITTED；此时再写 SUB_COMMITTED 没有意义，直接视为 no-op，避免 Assert 失败。
 * 正常运行时状态只允许从 0 或 SUB_COMMITTED 迁移到目标状态，或保持不变。
 *
 * 副作用：修改共享内存页内容；若 lsn 有效且大于该 XID 所属 LSN 组的当前值，
 * 则提升 group_lsn[]（每 32 个 XID 一个槽），供 slru.c 写页前 flush WAL。
 * 本函数不写 WAL，也不负责置 page_dirty（由调用者统一置脏）。
 */
static void
TransactionIdSetStatusBit(TransactionId xid, XidStatus status, XLogRecPtr lsn, int slotno)
{
	int			byteno = TransactionIdToByte(xid);
	int			bshift = TransactionIdToBIndex(xid) * CLOG_BITS_PER_XACT;
	char	   *byteptr;
	char		byteval;
	char		curval;

	Assert(XactCtl->shared->page_number[slotno] == TransactionIdToPage(xid));
	Assert(LWLockHeldByMeInMode(SimpleLruGetBankLock(XactCtl,
													 XactCtl->shared->page_number[slotno]),
								LW_EXCLUSIVE));

	byteptr = XactCtl->shared->page_buffer[slotno] + byteno;
	curval = (*byteptr >> bshift) & CLOG_XACT_BITMASK;

	/*
	 * When replaying transactions during recovery we still need to perform
	 * the two phases of subcommit and then commit. However, some transactions
	 * are already correctly marked, so we just treat those as a no-op which
	 * allows us to keep the following Assert as restrictive as possible.
	 */
	if (InRecovery && status == TRANSACTION_STATUS_SUB_COMMITTED &&
		curval == TRANSACTION_STATUS_COMMITTED)
		return;

	/*
	 * Current state change should be from 0 or subcommitted to target state
	 * or we should already be there when replaying changes during recovery.
	 */
	Assert(curval == 0 ||
		   (curval == TRANSACTION_STATUS_SUB_COMMITTED &&
			status != TRANSACTION_STATUS_IN_PROGRESS) ||
		   curval == status);

	/* note this assumes exclusive access to the clog page */
	byteval = *byteptr;
	byteval &= ~(((1 << CLOG_BITS_PER_XACT) - 1) << bshift);
	byteval |= (status << bshift);
	*byteptr = byteval;

	/*
	 * Update the group LSN if the transaction completion LSN is higher.
	 *
	 * Note: lsn will be invalid when supplied during InRecovery processing,
	 * so we don't need to do anything special to avoid LSN updates during
	 * recovery. After recovery completes the next clog change will set the
	 * LSN correctly.
	 */
	if (XLogRecPtrIsValid(lsn))
	{
		int			lsnindex = GetLSNIndex(slotno, xid);

		if (XactCtl->shared->group_lsn[lsnindex] < lsn)
			XactCtl->shared->group_lsn[lsnindex] = lsn;
	}
}

/*
 * Interrogate the state of a transaction in the commit log.
 *
 * Aside from the actual commit status, this function returns (into *lsn)
 * an LSN that is late enough to be able to guarantee that if we flush up to
 * that LSN then we will have flushed the transaction's commit record to disk.
 * The result is not necessarily the exact LSN of the transaction's commit
 * record!	For example, for long-past transactions (those whose clog pages
 * already migrated to disk), we'll return InvalidXLogRecPtr.  Also, because
 * we group transactions on the same clog page to conserve storage, we might
 * return the LSN of a later transaction that falls into the same group.
 *
 * NB: this is a low-level routine and is NOT the preferred entry point
 * for most uses; TransactionLogFetch() in transam.c is the intended caller.
 */
/*
 * 中文注释：
 * 查询指定 XID 在 CLOG 中的状态，并返回一个“提交记录至少已 flush 到这里”的
 * LSN。transam.c 的 TransactionLogFetch 是本函数的主要调用者。
 *
 * 参数：
 *   xid —— 要查询的事务 ID；
 *   lsn —— 输出参数，返回该 XID 所在 group_lsn 槽的值。它不一定是该事务提交
 *          记录本身的 LSN：同一 LSN 组（32 个 XID）内的多个事务共享该值，
 *          可能是稍后事务的 LSN；对早已换出到磁盘的旧页，由于共享内存中的
 *          group_lsn 已丢失，可能返回 InvalidXLogRecPtr。
 *
 * 返回值：XidStatus（IN_PROGRESS/COMMITTED/ABORTED/SUB_COMMITTED）。
 *
 * 并发：SimpleLruReadPage_ReadOnly 会获取目标 bank 的共享锁并在返回时保持，
 * 因此读取状态位和 group_lsn 是一致的；函数在返回前释放该锁。读取本身无副作用，
 * 但可能触发缺页 I/O。若页文件不存在，非恢复状态下 SLRU 会通过 errdetail 回调
 * 报告具体 XID；恢复期间缺失的页则按全零页读取。
 *
 * 截断安全：对于用户提供的任意 XID，调用者必须先持有 XactTruncationLock、确认
 * 它不早于 oldestClogXid，并一直持锁到查询完成，否则页可能已被 TruncateCLOG
 * 删除；普通的可见性判断只查询仍处于有效范围内的 XID，不需要额外加这把锁。
 */
XidStatus
TransactionIdGetStatus(TransactionId xid, XLogRecPtr *lsn)
{
	int64		pageno = TransactionIdToPage(xid);
	int			byteno = TransactionIdToByte(xid);
	int			bshift = TransactionIdToBIndex(xid) * CLOG_BITS_PER_XACT;
	int			slotno;
	int			lsnindex;
	char	   *byteptr;
	XidStatus	status;

	/* lock is acquired by SimpleLruReadPage_ReadOnly */

	slotno = SimpleLruReadPage_ReadOnly(XactCtl, pageno, &xid);
	byteptr = XactCtl->shared->page_buffer[slotno] + byteno;

	status = (*byteptr >> bshift) & CLOG_XACT_BITMASK;

	lsnindex = GetLSNIndex(slotno, xid);
	*lsn = XactCtl->shared->group_lsn[lsnindex];

	LWLockRelease(SimpleLruGetBankLock(XactCtl, pageno));

	return status;
}

/*
 * Number of shared CLOG buffers.
 *
 * If asked to autotune, use 2MB for every 1GB of shared buffers, up to 8MB.
 * Otherwise just cap the configured amount to be between 16 and the maximum
 * allowed.
 */
/*
 * 中文注释：
 * 计算 CLOG 共享缓冲槽数量。
 *
 * 若 transaction_buffers 为 0（表示自动调优），调用 SimpleLruAutotuneBuffers(512,
 * 1024)：大致按 shared_buffers 的 1/512 取槽数，最少一个 SLRU bank，最多
 * 1024 个槽（约 8MB），对应文件头注释所说的“每 1GB shared_buffers 给 2MB”。
 * 否则把用户配置值限制在 [16, CLOG_MAX_ALLOWED_BUFFERS] 区间内。
 *
 * 返回值：槽数。无副作用，可在 shmem request 阶段安全调用。
 */
static int
CLOGShmemBuffers(void)
{
	/* auto-tune based on shared buffers */
	if (transaction_buffers == 0)
		return SimpleLruAutotuneBuffers(512, 1024);

	return Min(Max(16, transaction_buffers), CLOG_MAX_ALLOWED_BUFFERS);
}

/*
 * Register shared memory for CLOG
 */
/*
 * 中文注释：
 * CLOG 的 shmem request 回调：在 postmaster 启动、共享内存尚未分配时，向
 * SimpleLruRequest 登记 CLOG 的 SLRU 参数。
 *
 * 若 transaction_buffers 仍为 0，先按 CLOGShmemBuffers() 计算自动调优值，并以
 * PGC_S_DYNAMIC_DEFAULT 的优先级写回 GUC；若 DBA 在配置文件中显式写了 0，
 * 该优先级无法覆盖，则改用 PGC_S_OVERRIDE 强制写入，保证后续逻辑看到的不是 0。
 *
 * 登记内容：
 *   .desc = &XactSlruDesc         —— 接收初始化后的 SLRU 句柄；
 *   .name = "transaction"         —— SLRU 名称，用于统计和错误信息；
 *   .Dir = "pg_xact"              —— PGDATA 下的目录名；
 *   .long_segment_names = false   —— 使用短 segment 文件名；
 *   .nslots / .nlsns              —— 缓冲槽数和每页 LSN 组数；
 *   .sync_handler = SYNC_HANDLER_CLOG —— 由 checkpointer 处理 fsync 请求；
 *   .PagePrecedes                 —— 截断时的页新旧比较；
 *   .errdetail_for_io_error       —— I/O 错误时补充事务 ID；
 *   .buffer_tranche_id / .bank_tranche_id —— 预定义的 LWLock tranche。
 *
 * 参数 arg 未使用。仅启动阶段单进程调用，无并发问题；副作用是可能修改 GUC 值
 * 并登记共享内存需求。
 */
static void
CLOGShmemRequest(void *arg)
{
	/* If auto-tuning is requested, now is the time to do it */
	if (transaction_buffers == 0)
	{
		char		buf[32];

		snprintf(buf, sizeof(buf), "%d", CLOGShmemBuffers());
		SetConfigOption("transaction_buffers", buf, PGC_POSTMASTER,
						PGC_S_DYNAMIC_DEFAULT);

		/*
		 * We prefer to report this value's source as PGC_S_DYNAMIC_DEFAULT.
		 * However, if the DBA explicitly set transaction_buffers = 0 in the
		 * config file, then PGC_S_DYNAMIC_DEFAULT will fail to override that
		 * and we must force the matter with PGC_S_OVERRIDE.
		 */
		if (transaction_buffers == 0)	/* failed to apply it? */
			SetConfigOption("transaction_buffers", buf, PGC_POSTMASTER,
							PGC_S_OVERRIDE);
	}
	Assert(transaction_buffers != 0);
	SimpleLruRequest(.desc = &XactSlruDesc,
					 .name = "transaction",
					 .Dir = "pg_xact",
					 .long_segment_names = false,

					 .nslots = CLOGShmemBuffers(),
					 .nlsns = CLOG_LSNS_PER_PAGE,

					 .sync_handler = SYNC_HANDLER_CLOG,
					 .PagePrecedes = CLOGPagePrecedes,
					 .errdetail_for_io_error = clog_errdetail_for_io_error,

					 .buffer_tranche_id = LWTRANCHE_XACT_BUFFER,
					 .bank_tranche_id = LWTRANCHE_XACT_SLRU,
		);
}

/*
 * 中文注释：
 * CLOG 的 shmem init 回调：共享内存分配/挂接完成后调用。
 *
 * 在启用断言构建时执行 SlruPagePrecedesUnitTests(XactCtl, CLOG_XACTS_PER_PAGE)，
 * 用若干边界 XID（包括回卷附近和页边界）验证 CLOGPagePrecedes 的模运算语义；
 * 非断言构建中该宏展开为空。参数 arg 未使用，无返回值，无持久化副作用。
 */
static void
CLOGShmemInit(void *arg)
{
	SlruPagePrecedesUnitTests(XactCtl, CLOG_XACTS_PER_PAGE);
}

/*
 * GUC check_hook for transaction_buffers
 */
/*
 * 中文注释：
 * transaction_buffers GUC 的 check_hook，在配置加载或 SET 时校验取值。
 *
 * 直接委托 check_slru_buffers("transaction_buffers", newval)，要求新值是
 * SLRU_BANK_SIZE 的整数倍，否则在 GUC 系统中设置错误详情并返回 false。
 * 该参数是 PGC_POSTMASTER，实际只在启动时生效；extra 参数本函数不使用。
 *
 * 返回值：true 表示取值合法；false 表示拒绝。无其他副作用。
 */
bool
check_transaction_buffers(int *newval, void **extra, GucSource source)
{
	return check_slru_buffers("transaction_buffers", newval);
}

/*
 * This func must be called ONCE on system install.  It creates
 * the initial CLOG segment.  (The CLOG directory is assumed to
 * have been created by initdb, and CLOGShmemInit must have been
 * called already.)
 */
/*
 * 中文注释：
 * 系统初始化（initdb/bootstrap）时调用一次，创建最初的 CLOG segment。
 *
 * 通过 SimpleLruZeroAndWritePage(XactCtl, 0) 把第 0 页清零并立即写盘，保证
 * BootstrapTransactionId / FrozenTransactionId 等特殊 XID 以及最初几个普通
 * XID 的查询有页可读。调用时假定 pg_xact 目录已由 initdb 创建、CLOGShmemInit
 * 已执行；本函数不写 WAL（bootstrap 阶段没有常规 WAL 机制），也没有并发。
 */
void
BootStrapCLOG(void)
{
	/* Zero the initial page and flush it to disk */
	SimpleLruZeroAndWritePage(XactCtl, 0);
}

/*
 * This must be called ONCE during postmaster or standalone-backend startup,
 * after StartupXLOG has initialized TransamVariables->nextXid.
 */
/*
 * 中文注释：
 * postmaster 或 standalone 后端启动时调用一次，且必须在 StartupXLOG 已经根据
 * 检查点/恢复结果初始化 TransamVariables->nextXid 之后调用。
 *
 * 作用：把 nextXid 所在的页号写入 XactCtl->shared->latest_page_number。该值只是
 * SLRU 的提示信息，用于避免把“当前最新页”当作 LRU 淘汰对象，不是关键数据，因此
 * 用原子写且不加 bank 锁。此时该页可能尚未在内存中甚至尚未创建，后续 ExtendCLOG
 * 会按需清零并建立它。无返回值，无持久化副作用。
 */
void
StartupCLOG(void)
{
	TransactionId xid = XidFromFullTransactionId(TransamVariables->nextXid);
	int64		pageno = TransactionIdToPage(xid);

	/*
	 * Initialize our idea of the latest page number.
	 */
	pg_atomic_write_u64(&XactCtl->shared->latest_page_number, pageno);
}

/*
 * This must be called ONCE at the end of startup/recovery.
 */
/*
 * 中文注释：
 * 启动/恢复结束时调用一次，清理 nextXid 所在 CLOG 页中“尚未使用”的尾部。
 *
 * 背景：子事务提交只写 CLOG、不写 WAL，因此崩溃后 XLOG 重放得到的 nextXid 可能
 * 小于崩溃前实际用过并标记过的最大 XID；如果这些残留状态位在下一轮被重新分配给
 * 新事务，就会被误读为已提交/已中止。虽然扩展新页时会清零，但当前页的尾部不会
 * 重新清零，所以这里显式处理。
 *
 * 实现：
 *   - 若 TransactionIdToPgIndex(xid) == 0，说明 nextXid 正好在页首，整页都是新页，
 *     无需处理（甚至该页可能还不存在）；
 *   - 否则在 bank 独占锁下读入当前页，保留 nextXid 所在字节中低于其 bit 偏移的
 *     已有位（这些属于更早的 XID），把该字节剩余位和本页后续所有字节清零；
 *   - 置 page_dirty，由后续检查点/淘汰写盘。
 * 参数无；不写 WAL，因为清零是幂等的恢复后整理，且新页本来就会被 CLOG_ZEROPAGE
 * 覆盖。并发：启动阶段单进程执行，但仍按常规获取 bank 锁。
 */
void
TrimCLOG(void)
{
	TransactionId xid = XidFromFullTransactionId(TransamVariables->nextXid);
	int64		pageno = TransactionIdToPage(xid);
	LWLock	   *lock = SimpleLruGetBankLock(XactCtl, pageno);

	LWLockAcquire(lock, LW_EXCLUSIVE);

	/*
	 * Zero out the remainder of the current clog page.  Under normal
	 * circumstances it should be zeroes already, but it seems at least
	 * theoretically possible that XLOG replay will have settled on a nextXID
	 * value that is less than the last XID actually used and marked by the
	 * previous database lifecycle (since subtransaction commit writes clog
	 * but makes no WAL entry).  Let's just be safe. (We need not worry about
	 * pages beyond the current one, since those will be zeroed when first
	 * used.  For the same reason, there is no need to do anything when
	 * nextXid is exactly at a page boundary; and it's likely that the
	 * "current" page doesn't exist yet in that case.)
	 */
	if (TransactionIdToPgIndex(xid) != 0)
	{
		int			byteno = TransactionIdToByte(xid);
		int			bshift = TransactionIdToBIndex(xid) * CLOG_BITS_PER_XACT;
		int			slotno;
		char	   *byteptr;

		slotno = SimpleLruReadPage(XactCtl, pageno, false, &xid);
		byteptr = XactCtl->shared->page_buffer[slotno] + byteno;

		/* Zero so-far-unused positions in the current byte */
		*byteptr &= (1 << bshift) - 1;
		/* Zero the rest of the page */
		MemSet(byteptr + 1, 0, BLCKSZ - byteno - 1);

		XactCtl->shared->page_dirty[slotno] = true;
	}

	LWLockRelease(lock);
}

/*
 * Perform a checkpoint --- either during shutdown, or on-the-fly
 */
/*
 * 中文注释：
 * 执行 CLOG 部分的检查点：把所有脏 CLOG 页写回磁盘。
 *
 * 调用 SimpleLruWriteAll(XactCtl, true)，allow_redirtied=true 表示允许在写出
 * 过程中页面又被并发事务置脏（检查点不要求 CLOG 在某一瞬间完全静止；下一页
 * 检查点会再次处理）。写页前 slru.c 会根据 group_lsn 先 flush 相应 WAL，因此
 * 异步提交的 WAL 规则仍然成立。写操作可能把 fsync 请求排入队列，由
 * ProcessSyncRequests() 在检查点后续阶段统一处理。
 *
 * TRACE 宏仅用于 dtrace 探针。无参数、无返回值；可能在 I/O 上阻塞。
 */
void
CheckPointCLOG(void)
{
	/*
	 * Write dirty CLOG pages to disk.  This may result in sync requests
	 * queued for later handling by ProcessSyncRequests(), as part of the
	 * checkpoint.
	 */
	TRACE_POSTGRESQL_CLOG_CHECKPOINT_START(true);
	SimpleLruWriteAll(XactCtl, true);
	TRACE_POSTGRESQL_CLOG_CHECKPOINT_DONE(true);
}


/*
 * Make sure that CLOG has room for a newly-allocated XID.
 *
 * NB: this is called while holding XidGenLock.  We want it to be very fast
 * most of the time; even when it's not so fast, no actual I/O need happen
 * unless we're forced to write out a dirty clog or xlog page to make room
 * in shared memory.
 */
/*
 * 中文注释：
 * 为刚分配的 XID 确保对应 CLOG 页存在。调用者是 varsup.c 的
 * GetNewTransactionId()，并且必须在持有 XidGenLock、推进 nextXid 之前调用，
 * 以保证“先有 CLOG 页，后有可用 XID”的顺序。
 *
 * 参数 newestXact：最新分配的 XID。
 *
 * 快速路径：只有当一个页的第一个 XID 被使用时才需要工作；但 XID 回卷后页 0 的
 * 第一个普通 XID 是 FirstNormalTransactionId（而不是 0），因此对这种情况也要
 * 处理。
 *
 * 慢路径：获取目标页 bank 独占锁，SimpleLruZeroPage 在共享内存中建立清零页并
 * 置脏，然后写一条 CLOG_ZEROPAGE WAL 记录（XLogSimpleInsertInt64）。写 WAL 的
 * 目的是让崩溃恢复和 Hot Standby 也能把该页清零；这里不立即 XLogFlush，因为
 * nextXid 的推进本身要等检查点才持久化，且即使该 WAL 丢失，恢复也会从更早的
 * nextXid 重新走到这里。
 *
 * 副作用：可能读/建页、置脏、插入 WAL；受 XidGenLock 串行化，bank 锁保护页本身。
 * 无返回值。
 */
void
ExtendCLOG(TransactionId newestXact)
{
	int64		pageno;
	LWLock	   *lock;

	/*
	 * No work except at first XID of a page.  But beware: just after
	 * wraparound, the first XID of page zero is FirstNormalTransactionId.
	 */
	if (TransactionIdToPgIndex(newestXact) != 0 &&
		!TransactionIdEquals(newestXact, FirstNormalTransactionId))
		return;

	pageno = TransactionIdToPage(newestXact);
	lock = SimpleLruGetBankLock(XactCtl, pageno);

	LWLockAcquire(lock, LW_EXCLUSIVE);

	/* Zero the page and make a WAL entry about it */
	SimpleLruZeroPage(XactCtl, pageno);
	XLogSimpleInsertInt64(RM_CLOG_ID, CLOG_ZEROPAGE, pageno);

	LWLockRelease(lock);
}


/*
 * Remove all CLOG segments before the one holding the passed transaction ID
 *
 * Before removing any CLOG data, we must flush XLOG to disk, to ensure that
 * any recently-emitted records with freeze plans have reached disk; otherwise
 * a crash and restart might leave us with some unfrozen tuples referencing
 * removed CLOG data.  We choose to emit a special TRUNCATE XLOG record too.
 * Replaying the deletion from XLOG is not critical, since the files could
 * just as well be removed later, but doing so prevents a long-running hot
 * standby server from acquiring an unreasonably bloated CLOG directory.
 *
 * Since CLOG segments hold a large number of transactions, the opportunity to
 * actually remove a segment is fairly rare, and so it seems best not to do
 * the XLOG flush unless we have confirmed that there is a removable segment.
 */
/*
 * 中文注释：
 * 删除不再需要的 CLOG segment，使 pg_xact 目录不会无限增长。调用者是 VACUUM
 * （vacuum.c），在成功推进 datfrozenxid 之后调用。
 *
 * 参数：
 *   oldestXact       —— 仍需保留状态的最老 XID，其所在页作为截断边界；
 *   oldestxid_datoid —— 拥有该最老 XID 的数据库 OID，写入 WAL 记录供恢复和
 *                       Hot Standby 使用。
 *
 * 流程：
 *   1. 计算 cutoffPage = TransactionIdToPage(oldestXact)，用
 *      SlruScanDirectory + SlruScanDirCbReportPresence 检查是否确实存在可删除的
 *      完整 segment；没有则直接返回，避免无谓的 WAL flush（CLOG segment 覆盖
 *      大量事务，真正可删的机会很少）；
 *   2. 调用 AdvanceOldestClogXid 推进集群级安全下界。必须放在真正删除之前：
 *      查询任意 XID 的代码会持有 XactTruncationLock，从检查 oldestClogXid 一直
 *      持到完成 CLOG 查找，因此推进后新查询不会再访问即将被删的页；
 *   3. WriteTruncateXlogRec 写入并 flush CLOG_TRUNCATE 记录，确保“冻结计划”
 *      等更早的 WAL 已落盘，再删除文件；这样崩溃重启不会出现未冻结元组引用
 *      已删除 CLOG 的情况，Hot Standby 也能及时重放截断、避免目录膨胀；
 *   4. SimpleLruTruncate 清理共享内存中的旧页并删除旧 segment 文件。
 *
 * 返回值：无。副作用：推进 oldestClogXid、写并 flush WAL、删文件、可能阻塞 I/O。
 * 崩溃恢复：删除本身不是关键操作（文件晚删也无害），但 WAL 记录保证恢复端
 * oldestClogXid 和目录状态不会倒退。
 */
void
TruncateCLOG(TransactionId oldestXact, Oid oldestxid_datoid)
{
	int64		cutoffPage;

	/*
	 * The cutoff point is the start of the segment containing oldestXact. We
	 * pass the *page* containing oldestXact to SimpleLruTruncate.
	 */
	cutoffPage = TransactionIdToPage(oldestXact);

	/* Check to see if there's any files that could be removed */
	if (!SlruScanDirectory(XactCtl, SlruScanDirCbReportPresence, &cutoffPage))
		return;					/* nothing to remove */

	/*
	 * Advance oldestClogXid before truncating clog, so concurrent xact status
	 * lookups can ensure they don't attempt to access truncated-away clog.
	 *
	 * It's only necessary to do this if we will actually truncate away clog
	 * pages.
	 */
	AdvanceOldestClogXid(oldestXact);

	/*
	 * Write XLOG record and flush XLOG to disk. We record the oldest xid
	 * we're keeping information about here so we can ensure that it's always
	 * ahead of clog truncation in case we crash, and so a standby finds out
	 * the new valid xid before the next checkpoint.
	 */
	WriteTruncateXlogRec(cutoffPage, oldestXact, oldestxid_datoid);

	/* Now we can remove the old CLOG segment(s) */
	SimpleLruTruncate(XactCtl, cutoffPage);
}


/*
 * Decide whether a CLOG page number is "older" for truncation purposes.
 *
 * We need to use comparison of TransactionIds here in order to do the right
 * thing with wraparound XID arithmetic.  However, TransactionIdPrecedes()
 * would get weird about permanent xact IDs.  So, offset both such that xid1,
 * xid2, and xid2 + CLOG_XACTS_PER_PAGE - 1 are all normal XIDs; this offset
 * is relevant to page 0 and to the page preceding page 0.
 *
 * The page containing oldestXact-2^31 is the important edge case.  The
 * portion of that page equaling or following oldestXact-2^31 is expendable,
 * but the portion preceding oldestXact-2^31 is not.  When oldestXact-2^31 is
 * the first XID of a page and segment, the entire page and segment is
 * expendable, and we could truncate the segment.  Recognizing that case would
 * require making oldestXact, not just the page containing oldestXact,
 * available to this callback.  The benefit would be rare and small, so we
 * don't optimize that edge case.
 */
/*
 * 中文注释：
 * SLRU 的 PagePrecedes 回调：判断 CLOG 页 page1 是否完全“早于” page2，用于
 * SimpleLruTruncate 决定哪些 segment 可以删除，也用于断言构建下的自检。
 *
 * 难点：页号会随 32 位 XID 回卷，不能直接比较整数大小。这里把页号还原成 XID
 * 后使用 TransactionIdPrecedes 的模运算语义；同时给两个 XID 都加上
 * FirstNormalTransactionId + 1 的偏移，避开特殊 XID（0、1、2）让
 * TransactionIdPrecedes 产生怪异结果。偏移对页 0 和页 0 前一页都适用。
 *
 * 边界情况：最老 XID - 2^31 所在页中，等于/晚于该点的部分可丢弃，早于该点的
 * 部分不可丢弃；若该 XID 恰好是页/segment 首 XID，整页本可删除，但本回调只拿到
 * 页号、拿不到精确 XID，因此保守地不优化该罕见情形。
 *
 * 参数：page1/page2 为 CLOG 页号（int64）。返回值：page1 完全早于 page2 时为
 * true。纯函数，无锁、无副作用。
 */
static bool
CLOGPagePrecedes(int64 page1, int64 page2)
{
	TransactionId xid1;
	TransactionId xid2;

	xid1 = ((TransactionId) page1) * CLOG_XACTS_PER_PAGE;
	xid1 += FirstNormalTransactionId + 1;
	xid2 = ((TransactionId) page2) * CLOG_XACTS_PER_PAGE;
	xid2 += FirstNormalTransactionId + 1;

	return (TransactionIdPrecedes(xid1, xid2) &&
			TransactionIdPrecedes(xid1, xid2 + CLOG_XACTS_PER_PAGE - 1));
}

/*
 * 中文注释：
 * SLRU 的 errdetail_for_io_error 回调：当读写 CLOG 页发生 I/O 错误、slru.c 需要
 * 生成详细的 ereport 信息时调用。
 *
 * 参数 opaque_data 是调用 SimpleLruReadPage/SimpleLruReadPage_ReadOnly 时传入的
 * 上下文指针；本模块传的是 XID 的地址，因此这里解引用为 TransactionId，并用
 * errdetail 输出“无法访问事务 %u 的提交状态”。
 *
 * 返回值：errdetail() 的返回值（int），供 ereport 内部使用。
 *
 * 注意：该回调运行在错误报告路径上，只能做格式化，不能抛出新的错误或获取可能
 * 阻塞的锁。某些只更新子事务的路径会传入 InvalidTransactionId，此时错误信息中
 * 的 XID 显示为 0，属于已知的提示信息不精确，不影响错误处理本身。
 */
static int
clog_errdetail_for_io_error(const void *opaque_data)
{
	TransactionId xid = *(const TransactionId *) opaque_data;

	return errdetail("Could not access commit status of transaction %u.", xid);
}


/*
 * Write a TRUNCATE xlog record
 *
 * We must flush the xlog record to disk before returning --- see notes
 * in TruncateCLOG().
 */
/*
 * 中文注释：
 * 写入并 flush 一条 CLOG_TRUNCATE WAL 记录，把截断意图持久化。
 *
 * 参数：
 *   pageno       —— 截断边界页号，重放时传给 SimpleLruTruncate；
 *   oldestXact   —— 仍需保留的最老 XID，重放时用于 AdvanceOldestClogXid；
 *   oldestXactDb —— 该 XID 所属数据库 OID，供恢复/standby 诊断使用。
 *
 * 流程：填充 xl_clog_truncate，XLogBeginInsert + XLogRegisterData +
 * XLogInsert(RM_CLOG_ID, CLOG_TRUNCATE)，最后 XLogFlush 到该记录 LSN。
 *
 * 为什么必须 flush：TruncateCLOG 在返回后会删除 CLOG 文件；只有确保截断记录
 * （以及此前带 freeze plan 的记录）已经落盘，崩溃后才不会出现“元组未冻结但
 * CLOG 已被删”的窗口。flush 可能阻塞在 I/O 上，但截断本身很少发生，可以接受。
 *
 * 返回值：无。副作用：插入 WAL 并 flush。调用时不应持有会与 WAL flush 形成
 * 环路的锁；本函数由 TruncateCLOG 在推进 oldestClogXid 之后调用。
 */
static void
WriteTruncateXlogRec(int64 pageno, TransactionId oldestXact, Oid oldestXactDb)
{
	XLogRecPtr	recptr;
	xl_clog_truncate xlrec;

	xlrec.pageno = pageno;
	xlrec.oldestXact = oldestXact;
	xlrec.oldestXactDb = oldestXactDb;

	XLogBeginInsert();
	XLogRegisterData(&xlrec, sizeof(xl_clog_truncate));
	recptr = XLogInsert(RM_CLOG_ID, CLOG_TRUNCATE);
	XLogFlush(recptr);
}

/*
 * CLOG resource manager's routines
 */
/*
 * 中文注释：
 * CLOG 的 resource manager redo 例程，由恢复/Hot Standby 的 rmgr 框架调用，
 * 重放 RM_CLOG_ID 的 WAL 记录。
 *
 * 参数 record：已定位到本条记录的 XLogReaderState。
 *
 * 支持两种操作码（先从 info 中屏蔽 XLR_INFO_MASK）：
 *   CLOG_ZEROPAGE —— 读取 int64 页号，调用 SimpleLruZeroAndWritePage 清零并
 *                    立即写盘。该操作幂等，重复重放安全；WAL 中没有 backup
 *                    block，函数开头断言记录不含 block reference。
 *   CLOG_TRUNCATE —— 读取 xl_clog_truncate，先 AdvanceOldestClogXid 推进安全
 *                    下界，再 SimpleLruTruncate 删除旧页/旧 segment。重放时
 *                    文件可能已被删除，SLRU 的截断逻辑允许这种情况。
 *   其他操作码 —— PANIC，说明 WAL 损坏或版本不匹配。
 *
 * 返回值：无。副作用：修改共享内存中的 SLRU 页、推进 oldestClogXid、删除文件；
 * 只在恢复进程的单线程上下文中执行，但仍遵循 SLRU 的锁规则。
 */
void
clog_redo(XLogReaderState *record)
{
	uint8		info = XLogRecGetInfo(record) & ~XLR_INFO_MASK;

	/* Backup blocks are not used in clog records */
	Assert(!XLogRecHasAnyBlockRefs(record));

	if (info == CLOG_ZEROPAGE)
	{
		int64		pageno;

		memcpy(&pageno, XLogRecGetData(record), sizeof(pageno));
		SimpleLruZeroAndWritePage(XactCtl, pageno);
	}
	else if (info == CLOG_TRUNCATE)
	{
		xl_clog_truncate xlrec;

		memcpy(&xlrec, XLogRecGetData(record), sizeof(xl_clog_truncate));

		AdvanceOldestClogXid(xlrec.oldestXact);

		SimpleLruTruncate(XactCtl, xlrec.pageno);
	}
	else
		elog(PANIC, "clog_redo: unknown op code %u", info);
}

/*
 * Entrypoint for sync.c to sync clog files.
 */
/*
 * 中文注释：
 * sync.c 的 CLOG 同步处理器入口：checkpointer 处理 fsync 请求队列时，对某个
 * CLOG segment 文件执行 fsync。
 *
 * 参数：
 *   ftag —— 文件标签，其中 segno 指定 CLOG segment 号；
 *   path —— 输出缓冲区，SlruSyncFileTag 会把拼好的文件路径写入其中。
 *
 * 返回值：0 表示成功；-1 表示打开文件失败；其他值来自 pg_fsync（通常也是 -1
 * 并设置 errno），由调用者决定如何报告。
 *
 * 实现直接委托 SlruSyncFileTag：按 SLRU 命名规则生成路径、以 O_RDWR 打开、
 * pg_fsync、关闭文件，并用 WAIT_EVENT_SLRU_FLUSH_SYNC 统计等待事件。
 * 该函数不在 CLOG bank 锁的保护范围内运行，只操作磁盘文件，不触碰共享缓冲。
 */
int
clogsyncfiletag(const FileTag *ftag, char *path)
{
	return SlruSyncFileTag(XactCtl, ftag, path);
}
