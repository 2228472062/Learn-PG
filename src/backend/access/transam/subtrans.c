/*-------------------------------------------------------------------------
 *
 * subtrans.c
 *		PostgreSQL subtransaction-log manager
 *
 * The pg_subtrans manager is a pg_xact-like manager that stores the parent
 * transaction Id for each transaction.  It is a fundamental part of the
 * nested transactions implementation.  A main transaction has a parent
 * of InvalidTransactionId, and each subtransaction has its immediate parent.
 * The tree can easily be walked from child to parent, but not in the
 * opposite direction.
 *
 * This code is based on xact.c, but the robustness requirements
 * are completely different from pg_xact, because we only need to remember
 * pg_subtrans information for currently-open transactions.  Thus, there is
 * no need to preserve data over a crash and restart.
 *
 * There are no XLOG interactions since we do not care about preserving
 * data across crashes.  During database startup, we simply force the
 * currently-active page of SUBTRANS to zeroes.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/subtrans.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 的子事务日志管理器（subtransaction-log manager），
 * 在共享内存与磁盘上的 pg_subtrans SLRU 中维护
 * “子事务 XID -> 直接父事务 XID”的单向映射，是嵌套事务（subtransaction）
 * 实现的基础。
 *
 * 核心数据结构与寻址方式：
 *   - pg_subtrans 与 pg_xact（CLOG）类似，都是基于 SLRU 的定长页日志；
 *     每个 XID 占用 4 字节（TransactionId），一页（BLCKSZ）可容纳
 *     SUBTRANS_XACTS_PER_PAGE 个 XID 的父 XID。
 *   - 页号由 TransactionIdToPage() 计算，页内条目的下标由
 *     TransactionIdToEntry() 计算，因此定位某个 XID 的父 XID 是 O(1) 的
 *     直接下标运算，无需额外索引。
 *   - 顶层事务不在 pg_subtrans 中登记，其槽位保持全零，即父 XID 为
 *     InvalidTransactionId；因此只能从子事务沿 parent 指针向上走，
 *     无法由父事务反向查找子事务。
 *
 * 与其他模块的关系：
 *   - xact.c 的 AssignTransactionId() 在子事务首次分配 XID 时调用
 *     SubTransSetParent() 写入父 XID；twophase.c 在恢复两阶段事务时重建
 *     其子事务映射；procarray.c 在同步 KnownAssignedXids 时也会补写。
 *   - transam.c（TransactionIdDidCommit/TransactionIdDidAbort）、
 *     procarray.c（TransactionIdIsInProgress）、lmgr.c、snapmgr.c、
 *     heapam.c 等通过 SubTransGetParent()/SubTransGetTopmostTransaction()
 *     把子事务 XID 归并到其顶层事务，以判断提交状态、是否仍在运行以及
 *     可见性。
 *   - 共享缓冲区、页面读写、LRU 淘汰与截断由 access/slru.c 统一实现；
 *     本文件只提供 SLRU 参数和回调。GUC 参数 subtransaction_buffers
 *     控制缓冲区数量。
 *
 * 关键设计思想：
 *   - 只需要记住“当前仍打开”的事务的父子关系：崩溃后这些信息没有保留
 *     价值，因此本模块不写 WAL，也不参与恢复重放；数据库启动时直接清零
 *     当前活动页，而不是从 WAL 恢复。
 *   - 页面在首次使用（ExtendSUBTRANS）和启动（StartupSUBTRANS）时清零，
 *     避免把上一次运行遗留的陈旧父 XID 误认为有效数据；读取到零即表示
 *     “无父事务/信息不可用”。
 *   - 父 XID 总是先于子 XID 分配。该顺序不变量既用于检测损坏和死循环，
 *     也是 SubTransPagePrecedes() 中回绕安全比较的基础。
 *   - 由于不保证 TransactionXmin 之前的数据仍然存在，调用方约定不查询更老
 *     的 XID；SubTransGetTopmostTransaction() 在这种边界情况下允许返回一个
 *     中间层父事务，这对它的调用者来说已经足够。
 */
#include "postgres.h"

#include "access/slru.h"
#include "access/subtrans.h"
#include "access/transam.h"
#include "miscadmin.h"
#include "pg_trace.h"
#include "storage/subsystems.h"
#include "utils/guc_hooks.h"
#include "utils/snapmgr.h"


/*
 * Defines for SubTrans page sizes.  A page is the same BLCKSZ as is used
 * everywhere else in Postgres.
 *
 * Note: because TransactionIds are 32 bits and wrap around at 0xFFFFFFFF,
 * SubTrans page numbering also wraps around at
 * 0xFFFFFFFF/SUBTRANS_XACTS_PER_PAGE, and segment numbering at
 * 0xFFFFFFFF/SUBTRANS_XACTS_PER_PAGE/SLRU_PAGES_PER_SEGMENT.  We need take no
 * explicit notice of that fact in this module, except when comparing segment
 * and page numbers in TruncateSUBTRANS (see SubTransPagePrecedes) and zeroing
 * them in StartupSUBTRANS.
 */
/*
 * 中文注释：
 * SUBTRANS_XACTS_PER_PAGE 定义每个 SLRU 页面能容纳的 XID 条目数：每个事务
 * 的父 XID 用 4 字节的 TransactionId 保存，故一页可存 BLCKSZ / 4 个条目
 * （默认 8KB 页面即 2048 个）。页号和段号都会随 32 位 XID 回绕，本模块只在
 * TruncateSUBTRANS() 的页比较（SubTransPagePrecedes）和 StartupSUBTRANS()
 * 的清零循环中显式处理这一事实。
 */

/* We need four bytes per xact */
#define SUBTRANS_XACTS_PER_PAGE (BLCKSZ / sizeof(TransactionId))

/*
 * Although we return an int64 the actual value can't currently exceed
 * 0xFFFFFFFF/SUBTRANS_XACTS_PER_PAGE.
 */
/*
 * 中文注释：
 * 把 32 位 XID 映射为它所属的 SLRU 页号（xid / SUBTRANS_XACTS_PER_PAGE）。
 * 返回 int64 是为了与 SLRU 的页号类型一致并避免中间乘法/比较溢出；由于 XID
 * 只有 32 位，实际页号不会超过 0xFFFFFFFF / SUBTRANS_XACTS_PER_PAGE。
 */
static inline int64
TransactionIdToPage(TransactionId xid)
{
	return xid / (int64) SUBTRANS_XACTS_PER_PAGE;
}

/*
 * 中文注释：
 * 计算 XID 在所属页面内的条目下标（xid % SUBTRANS_XACTS_PER_PAGE），与
 * TransactionIdToPage() 配合即可定位该 XID 对应的 4 字节父 XID 槽位。
 * 注意该宏会对参数 xid 求值两次，调用方不应传入带副作用的表达式。
 */
#define TransactionIdToEntry(xid) ((xid) % (TransactionId) SUBTRANS_XACTS_PER_PAGE)


/*
 * 中文注释：
 * 本文件的静态辅助函数与共享内存注册回调。SUBTRANSShmemCallbacks 会在
 * postmaster 启动的“申请共享内存”阶段调用 SUBTRANSShmemRequest() 声明 SLRU
 * 所需空间，并在共享内存分配完成后调用 SUBTRANSShmemInit() 做初始化与自检。
 * SubTransPagePrecedes() 作为 SLRU 回调用于截断时的页新旧比较；
 * subtrans_errdetail_for_io_error() 作为 SLRU 回调为 I/O 错误补充诊断信息。
 */
static void SUBTRANSShmemRequest(void *arg);
static void SUBTRANSShmemInit(void *arg);
static bool SubTransPagePrecedes(int64 page1, int64 page2);
static int	subtrans_errdetail_for_io_error(const void *opaque_data);

/*
 * 中文注释：
 * 注册到 storage/shmem.h 共享内存子系统框架的 SUBTRANS 回调集合。
 * request_fn 在共享内存分配之前执行，负责确定缓冲区数目并向 SLRU 层登记
 * 本模块的共享内存需求；init_fn 在共享内存就绪之后执行，用于运行页号比较
 * 函数的自检。回调的 arg 参数由框架传入，本模块不使用。
 */
const ShmemCallbacks SUBTRANSShmemCallbacks = {
	.request_fn = SUBTRANSShmemRequest,
	.init_fn = SUBTRANSShmemInit,
};

/*
 * Link to shared-memory data structures for SUBTRANS control
 */
/*
 * 中文注释：
 * SUBTRANS SLRU 的后端私有描述符（SlruDesc）。它在 SUBTRANSShmemRequest()
 * 调用 SimpleLruRequest() 时被初始化，保存指向共享内存控制结构、页数、
 * 回调函数等信息的指针。该描述符每个进程各有一份，本身不在共享内存中。
 * 下面用 SubTransCtl 作为简写别名，后续所有 SLRU 操作都通过它进行。
 */
static SlruDesc SubTransSlruDesc;

#define SubTransCtl  (&SubTransSlruDesc)


/*
 * Record the parent of a subtransaction in the subtrans log.
 */
/*
 * 中文注释：
 * 在 pg_subtrans 中记录子事务 xid 的直接父事务 parent。
 *
 * 调用场景：
 *   - xact.c 的 AssignTransactionId() 为子事务首次分配 XID 后立即调用，
 *     且必须早于该 XID 出现在 PGPROC 之外的共享存储中，这样即使 PGPROC
 *     的子事务缓存已满，其他后端也能通过 pg_subtrans 判断该 XID 仍在运行。
 *   - twophase.c 恢复准备好的两阶段事务、procarray.c 同步 KnownAssignedXids
 *     时也会调用，用于重建或补齐父子链。
 *
 * 参数：
 *   xid    —— 已分配的子事务 XID，必须晚于 parent；
 *   parent —— 其直接父事务（可能是顶层事务，也可能是另一个子事务）的 XID。
 *
 * 并发与副作用：
 *   - 先取得该页所属 bank 的 LWLock 排他锁，再调用 SimpleLruReadPage()，
 *     因此对页面的读、改、标脏是原子的；页面内容可能来自共享缓冲区，也可能
 *     需要从磁盘读入。该页必须已由 ExtendSUBTRANS() 在分配 XID 时清零。
 *   - 只修改共享内存并置 page_dirty，不写 WAL、不立即刷盘；脏页由检查点或
 *     LRU 淘汰时写出。由于数据不要求跨崩溃保留，这是安全的。
 *   - 该操作允许重复执行并写入相同的 parent（例如恢复路径可能重复登记），
 *     但绝不允许把已有有效 parent 改成另一个有效值，否则会使父子链损坏；
 *     因此仅当槽位为 InvalidTransactionId 时才写入，并用 Assert 捕获违例。
 */
void
SubTransSetParent(TransactionId xid, TransactionId parent)
{
	int64		pageno = TransactionIdToPage(xid);
	int			entryno = TransactionIdToEntry(xid);
	int			slotno;
	LWLock	   *lock;
	TransactionId *ptr;

	Assert(TransactionIdIsValid(parent));
	Assert(TransactionIdFollows(xid, parent));

	lock = SimpleLruGetBankLock(SubTransCtl, pageno);
	LWLockAcquire(lock, LW_EXCLUSIVE);

	slotno = SimpleLruReadPage(SubTransCtl, pageno, true, &xid);
	ptr = (TransactionId *) SubTransCtl->shared->page_buffer[slotno];
	ptr += entryno;

	/*
	 * It's possible we'll try to set the parent xid multiple times but we
	 * shouldn't ever be changing the xid from one valid xid to another valid
	 * xid, which would corrupt the data structure.
	 */
	if (*ptr != parent)
	{
		Assert(*ptr == InvalidTransactionId);
		*ptr = parent;
		SubTransCtl->shared->page_dirty[slotno] = true;
	}

	LWLockRelease(lock);
}

/*
 * Interrogate the parent of a transaction in the subtrans log.
 */
/*
 * 中文注释：
 * 查询 xid 在 pg_subtrans 中记录的直接父事务 XID。
 *
 * 参数与返回值：
 *   xid —— 要查询的事务 XID。调用者必须保证 xid >= TransactionXmin，因为更老
 *          的事务的子事务信息可能已被截断或清零，不再可信（函数内用 Assert
 *          检查）。Bootstrap/Frozen 等特殊 XID 没有父事务，直接返回
 *          InvalidTransactionId。
 *   返回值 —— 直接父 XID；若该 XID 是顶层事务、信息已被清零或页面中尚无记录，
 *          则返回 InvalidTransactionId。
 *
 * 并发与锁：
 *   - 使用 SimpleLruReadPage_ReadOnly() 读取；它会按需取得该页所在 bank 的
 *     LWLock 共享锁（必要时先释放再升级为排他锁完成 I/O），函数返回时锁仍被
 *     持有，因此调用者必须用 LWLockRelease(SimpleLruGetBankLock(...)) 释放。
 *   - 读路径通常只访问共享缓冲区；若页面不在内存中会触发磁盘 I/O，失败时
 *     通过注册的 errdetail 回调报告具体是哪个 XID 无法访问。
 *   - 本函数只读取一个条目，不验证父子链是否完整；链式遍历由
 *     SubTransGetTopmostTransaction() 完成。
 */
TransactionId
SubTransGetParent(TransactionId xid)
{
	int64		pageno = TransactionIdToPage(xid);
	int			entryno = TransactionIdToEntry(xid);
	int			slotno;
	TransactionId *ptr;
	TransactionId parent;

	/* Can't ask about stuff that might not be around anymore */
	Assert(TransactionIdFollowsOrEquals(xid, TransactionXmin));

	/* Bootstrap and frozen XIDs have no parent */
	if (!TransactionIdIsNormal(xid))
		return InvalidTransactionId;

	/* lock is acquired by SimpleLruReadPage_ReadOnly */

	slotno = SimpleLruReadPage_ReadOnly(SubTransCtl, pageno, &xid);
	ptr = (TransactionId *) SubTransCtl->shared->page_buffer[slotno];
	ptr += entryno;

	parent = *ptr;

	LWLockRelease(SimpleLruGetBankLock(SubTransCtl, pageno));

	return parent;
}

/*
 * SubTransGetTopmostTransaction
 *
 * Returns the topmost transaction of the given transaction id.
 *
 * Because we cannot look back further than TransactionXmin, it is possible
 * that this function will lie and return an intermediate subtransaction ID
 * instead of the true topmost parent ID.  This is OK, because in practice
 * we only care about detecting whether the topmost parent is still running
 * or is part of a current snapshot's list of still-running transactions.
 * Therefore, any XID before TransactionXmin is as good as any other.
 */
/*
 * 中文注释：
 * 沿 pg_subtrans 的 parent 指针不断上溯，返回 xid 能够确定的最高层祖先
 * 事务 XID。
 *
 * 调用场景：
 *   - procarray.c 判断 XID 是否仍在运行时，需要把子事务归并到顶层事务；
 *   - lmgr.c 做锁冲突/等待判断、snapmgr.c 处理快照、heapam.c 判断元组
 *     可见性时，也会先求顶层 XID。
 *
 * 参数与返回值：
 *   xid —— 起始事务 XID，调用者必须保证 xid >= TransactionXmin。
 *   返回值 —— 找到的最高层父事务 XID。由于 TransactionXmin 之前的数据可能
 *             已被清理，函数可能在到达真正顶层事务之前停止，此时返回一个
 *             中间层子事务 XID；这对上述调用者没有影响，因为它们只关心
 *             顶层事务是否仍在运行或是否出现在当前快照中。
 *
 * 实现与并发注意：
 *   - 每次循环调用 SubTransGetParent()，该函数内部加锁、返回前释放，因此
 *     本函数不会跨多次查询持锁，也不会长时间阻塞其他后端。
 *   - 不变量：父 XID 必须先于子 XID 分配。若发现 parentXid 没有严格小于
 *     previousXid，说明数据损坏且可能形成环，函数直接 elog(ERROR) 终止，
 *     避免无限循环。
 *   - 当父 XID 已早于 TransactionXmin 时主动停止，不再查询不可靠的数据。
 *   - 起始 xid 本身有效，previousXid 在每次循环中都会被赋值为有效 XID，
 *     因此最终返回值一定是有效 XID（末尾 Assert 保证）。
 */
TransactionId
SubTransGetTopmostTransaction(TransactionId xid)
{
	TransactionId parentXid = xid,
				previousXid = xid;

	/* Can't ask about stuff that might not be around anymore */
	Assert(TransactionIdFollowsOrEquals(xid, TransactionXmin));

	while (TransactionIdIsValid(parentXid))
	{
		previousXid = parentXid;
		if (TransactionIdPrecedes(parentXid, TransactionXmin))
			break;
		parentXid = SubTransGetParent(parentXid);

		/*
		 * By convention the parent xid gets allocated first, so should always
		 * precede the child xid. Anything else points to a corrupted data
		 * structure that could lead to an infinite loop, so exit.
		 */
		if (!TransactionIdPrecedes(parentXid, previousXid))
			elog(ERROR, "pg_subtrans contains invalid entry: xid %u points to parent xid %u",
				 previousXid, parentXid);
	}

	Assert(TransactionIdIsValid(previousXid));

	return previousXid;
}

/*
 * Number of shared SUBTRANS buffers.
 *
 * If asked to autotune, use 2MB for every 1GB of shared buffers, up to 8MB.
 * Otherwise just cap the configured amount to be between 16 and the maximum
 * allowed.
 */
/*
 * 中文注释：
 * 计算 SUBTRANS SLRU 应使用的共享缓冲区（页槽）数量。
 *
 *   - 当 GUC 参数 subtransaction_buffers 为 0（表示自动调优）时，调用
 *     SimpleLruAutotuneBuffers(512, 1024)：按 shared_buffers 的 1/512 估算，
 *     结果按 SLRU bank 大小对齐，并限制在 bank 大小到 1024 个缓冲区之间；
 *     按 8KB 页计算，即每 1GB shared_buffers 约使用 2MB，最多 8MB。
 *   - 否则使用用户配置值，并强制夹在 16 与 SLRU_MAX_ALLOWED_BUFFERS 之间，
 *     防止过小导致频繁换页、过大导致共享内存或 size_t 运算溢出。
 *
 * 本函数是纯计算函数，无副作用，可在共享内存申请阶段安全调用。
 */
static int
SUBTRANSShmemBuffers(void)
{
	/* auto-tune based on shared buffers */
	if (subtransaction_buffers == 0)
		return SimpleLruAutotuneBuffers(512, 1024);

	return Min(Max(16, subtransaction_buffers), SLRU_MAX_ALLOWED_BUFFERS);
}



/*
 * Register shared memory for SUBTRANS
 */
/*
 * 中文注释：
 * ShmemCallbacks.request_fn：在 postmaster 启动、共享内存尚未分配时调用，
 * 负责确定缓冲区数量并向 SLRU 框架登记 SUBTRANS 的共享内存需求。
 *
 * 自动调优：
 *   - 若 GUC subtransaction_buffers 为 0，先用 SUBTRANSShmemBuffers() 算出
 *     数值，再通过 SetConfigOption() 以 PGC_POSTMASTER 和
 *     PGC_S_DYNAMIC_DEFAULT 来源写回该 GUC，这样 pg_settings 中能显示实际
 *     采用的值及其来源。
 *   - 如果 DBA 在配置文件中显式写了 subtransaction_buffers = 0，
 *     PGC_S_DYNAMIC_DEFAULT 的优先级不足以覆盖它，因此检测到仍为 0 时改用
 *     PGC_S_OVERRIDE 强制写入。最后由 Assert 保证不会以 0 个缓冲区注册。
 *
 * SimpleLruRequest() 登记的内容：
 *   - 名称 "subtransaction" 与数据目录 "pg_subtrans"；
 *   - 短段文件名（long_segment_names = false）；
 *   - 页槽数 SUBTRANSShmemBuffers()；
 *   - 不注册 sync handler（SYNC_HANDLER_NONE）：本 SLRU 不要求崩溃后持久，
 *     无需 fsync，也不向 checkpointer 发送同步请求；
 *   - 页新旧比较回调 SubTransPagePrecedes() 和 I/O 错误详情回调；
 *   - 每缓冲区与每 bank 的 LWLock tranche ID。
 * 此处只是“申请”，实际共享内存分配和初始化由框架在后续阶段完成；函数参数
 * arg 是框架传入的 opaque 参数，本模块不使用。
 */
static void
SUBTRANSShmemRequest(void *arg)
{
	/* If auto-tuning is requested, now is the time to do it */
	if (subtransaction_buffers == 0)
	{
		char		buf[32];

		snprintf(buf, sizeof(buf), "%d", SUBTRANSShmemBuffers());
		SetConfigOption("subtransaction_buffers", buf, PGC_POSTMASTER,
						PGC_S_DYNAMIC_DEFAULT);

		/*
		 * We prefer to report this value's source as PGC_S_DYNAMIC_DEFAULT.
		 * However, if the DBA explicitly set subtransaction_buffers = 0 in
		 * the config file, then PGC_S_DYNAMIC_DEFAULT will fail to override
		 * that and we must force the matter with PGC_S_OVERRIDE.
		 */
		if (subtransaction_buffers == 0)	/* failed to apply it? */
			SetConfigOption("subtransaction_buffers", buf, PGC_POSTMASTER,
							PGC_S_OVERRIDE);
	}
	Assert(subtransaction_buffers != 0);

	SimpleLruRequest(.desc = &SubTransSlruDesc,
					 .name = "subtransaction",
					 .Dir = "pg_subtrans",
					 .long_segment_names = false,

					 .nslots = SUBTRANSShmemBuffers(),

					 .sync_handler = SYNC_HANDLER_NONE,
					 .PagePrecedes = SubTransPagePrecedes,
					 .errdetail_for_io_error = subtrans_errdetail_for_io_error,

					 .buffer_tranche_id = LWTRANCHE_SUBTRANS_BUFFER,
					 .bank_tranche_id = LWTRANCHE_SUBTRANS_SLRU,
		);
}

/*
 * 中文注释：
 * ShmemCallbacks.init_fn：在共享内存已经分配完成后由子系统框架调用一次，
 * 此时 SUBTRANSShmemRequest() 已通过 SimpleLruRequest() 初始化描述符。
 *
 * 本函数不做运行数据的初始化（活动页清零由 StartupSUBTRANS() 负责），只调用
 * SlruPagePrecedesUnitTests() 对 SubTransPagePrecedes() 做单元测试：验证页号
 * 在 32 位 XID 回绕边界附近的新旧比较仍然自洽，且 !precedes(a,b) &&
 * !precedes(b,a) 只出现在允许的情形。该检查只在启用断言（USE_ASSERT_CHECKING）
 * 的构建中编译出实际代码，否则展开为空操作。
 *
 * 参数 arg 为框架传入的 opaque 参数，本模块不使用；函数无返回值。
 */
static void
SUBTRANSShmemInit(void *arg)
{
	SlruPagePrecedesUnitTests(SubTransCtl, SUBTRANS_XACTS_PER_PAGE);
}

/*
 * GUC check_hook for subtransaction_buffers
 */
/*
 * 中文注释：
 * GUC 参数 subtransaction_buffers 的检查钩子（check_hook）。在配置值被接受
 * 之前调用，用于拒绝非法值。
 *
 * 参数：
 *   newval —— 待检查的新值（缓冲区个数）；
 *   extra  —— GUC 框架用于传递附加数据的指针，本函数不使用；
 *   source —— 配置来源，本函数不使用。
 * 返回值：合法返回 true；非法返回 false（由 check_slru_buffers() 通过
 *         GUC_check_errdetail() 给出具体原因）。
 *
 * 实际规则由 check_slru_buffers() 统一实现：值必须为正、必须是 SLRU bank
 * 大小（SLRU_BANK_SIZE）的整数倍，且不能超过 SLRU_MAX_ALLOWED_BUFFERS，
 * 以保证 SLRU 内部的 size_t 运算不会溢出。
 */
bool
check_subtrans_buffers(int *newval, void **extra, GucSource source)
{
	return check_slru_buffers("subtransaction_buffers", newval);
}

/*
 * This func must be called ONCE on system install.  It creates
 * the initial SUBTRANS segment.  (The SUBTRANS directory is assumed to
 * have been created by the initdb shell script, and SUBTRANSShmemInit
 * must have been called already.)
 *
 * Note: it's not really necessary to create the initial segment now,
 * since slru.c would create it on first write anyway.  But we may as well
 * do it to be sure the directory is set up correctly.
 */
/*
 * 中文注释：
 * 在系统初始化（initdb/bootstrap）阶段调用一次，创建 SUBTRANS 的初始段。
 *
 * 具体做法是 SimpleLruZeroAndWritePage(SubTransCtl, 0)：把 0 号页清零并立即
 * 写盘，从而确保 pg_subtrans 目录和初始段文件确实存在且格式正确。
 *
 * 说明：
 *   - 调用前必须已执行 SUBTRANSShmemInit()（共享内存描述符可用），且
 *     pg_subtrans 目录已由 initdb 脚本创建。
 *   - 严格来说这一步并非必需：SLRU 在第一次写入时会自动创建段文件。这里
 *     提前创建只是为了让目录/文件权限和布局问题在 initdb 阶段就暴露出来。
 *   - 该函数只用于 bootstrap，正常启动路径不会调用；无参数、无返回值。
 */
void
BootStrapSUBTRANS(void)
{
	/* Zero the initial page and flush it to disk */
	SimpleLruZeroAndWritePage(SubTransCtl, 0);
}

/*
 * This must be called ONCE during postmaster or standalone-backend startup,
 * after StartupXLOG has initialized TransamVariables->nextXid.
 *
 * oldestActiveXID is the oldest XID of any prepared transaction, or nextXid
 * if there are none.
 */
/*
 * 中文注释：
 * 在 postmaster 或单用户后端启动时调用一次，且必须在 StartupXLOG 已经初始化
 * TransamVariables->nextXid 之后、任何普通事务开始之前执行。
 *
 * 作用：
 *   由于 pg_subtrans 不写 WAL、不保证跨崩溃有效，这里把所有可能仍需使用的页
 *   在共享内存中清零，防止把上一次运行遗留的陈旧父 XID 当成有效数据。之后每当
 *   XID 推进到新的一页，ExtendSUBTRANS() 也会同样清零新页，而不管磁盘上原有
 *   内容是什么。
 *
 * 参数：
 *   oldestActiveXID —— 所有 prepared transaction 中最老的 XID；若没有 prepared
 *   transaction，则为 nextXid。它给出了仍需保留的子事务映射的下界。
 *
 * 实现细节：
 *   - startPage 是 oldestActiveXID 所在页，endPage 是 nextXid 所在页；
 *     循环对闭区间 [startPage, endPage] 逐页调用 SimpleLruZeroPage()，只清零
 *     共享缓冲区中的页并标脏，不立即写盘。
 *   - 页号按 32 位 XID 回绕：startPage 递增后若超过 MaxTransactionId 所在页，
 *     就回到 0。这样即使区间跨越回绕点也能正确覆盖。
 *   - 并发：此时只有启动进程在操作 SUBTRANS，但仍按 SLRU 约定对每页所在 bank
 *     取 LWLock 排他锁。为避免同时持有多个 bank 锁导致死锁，切换到不同 bank 时
 *     先释放上一把锁；同一 bank 的连续页则复用（prevlock 优化）。循环结束后
 *     释放最后持有的锁。
 */
void
StartupSUBTRANS(TransactionId oldestActiveXID)
{
	FullTransactionId nextXid;
	int64		startPage;
	int64		endPage;
	LWLock	   *prevlock = NULL;
	LWLock	   *lock;

	/*
	 * Since we don't expect pg_subtrans to be valid across crashes, we
	 * initialize the currently-active page(s) to zeroes during startup.
	 * Whenever we advance into a new page, ExtendSUBTRANS will likewise zero
	 * the new page without regard to whatever was previously on disk.
	 */
	startPage = TransactionIdToPage(oldestActiveXID);
	nextXid = TransamVariables->nextXid;
	endPage = TransactionIdToPage(XidFromFullTransactionId(nextXid));

	for (;;)
	{
		lock = SimpleLruGetBankLock(SubTransCtl, startPage);
		if (prevlock != lock)
		{
			if (prevlock)
				LWLockRelease(prevlock);
			LWLockAcquire(lock, LW_EXCLUSIVE);
			prevlock = lock;
		}

		(void) SimpleLruZeroPage(SubTransCtl, startPage);
		if (startPage == endPage)
			break;

		startPage++;
		/* must account for wraparound */
		if (startPage > TransactionIdToPage(MaxTransactionId))
			startPage = 0;
	}

	LWLockRelease(lock);
}

/*
 * Perform a checkpoint --- either during shutdown, or on-the-fly
 */
/*
 * 中文注释：
 * 在检查点（checkpoint）期间调用，负责把 SUBTRANS 的所有脏页刷到磁盘，包括
 * 关闭数据库时的最后检查点和运行中的在线检查点。调用者是 xlog.c 的
 * CheckPointGuts()。
 *
 * 行为与参数：
 *   SimpleLruWriteAll(SubTransCtl, true) 中的 true 表示 allow_redirtied：即使
 *   某页在写出过程中又被其他后端标脏，也只保留其脏状态，不视为错误。
 *   TRACE_POSTGRESQL_SUBTRANS_CHECKPOINT_START/DONE 是 DTrace 探针，其 bool
 *   参数当前固定为 true；历史上该参数用于区分 checkpoint 与已删除的 shutdown
 *   刷新路径。
 *
 * 为什么不是正确性所必需：
 *   pg_subtrans 不要求跨崩溃保留，脏页即使丢失也可以在启动时清零重建。这里刷盘
 *   只是把 I/O 从普通后端转移到检查点进程，并限制共享内存中脏页的数量，从而
 *   降低后端在分配/查询子事务时被迫同步写盘的概率。
 *
 * 注意：本函数只负责写脏页，不负责截断旧段；截断由 TruncateSUBTRANS() 在检查点
 * 的相应阶段另行完成。
 */
void
CheckPointSUBTRANS(void)
{
	/*
	 * Write dirty SUBTRANS pages to disk
	 *
	 * This is not actually necessary from a correctness point of view. We do
	 * it merely to improve the odds that writing of dirty pages is done by
	 * the checkpoint process and not by backends.
	 */
	TRACE_POSTGRESQL_SUBTRANS_CHECKPOINT_START(true);
	SimpleLruWriteAll(SubTransCtl, true);
	TRACE_POSTGRESQL_SUBTRANS_CHECKPOINT_DONE(true);
}


/*
 * Make sure that SUBTRANS has room for a newly-allocated XID.
 *
 * NB: this is called while holding XidGenLock.  We want it to be very fast
 * most of the time; even when it's not so fast, no actual I/O need happen
 * unless we're forced to write out a dirty subtrans page to make room
 * in shared memory.
 */
/*
 * 中文注释：
 * 确保 pg_subtrans 已经为新分配的 XID newestXact 准备好干净的页面。
 *
 * 调用场景：
 *   - varsup.c 的 GetNewTransactionId() 每分配一个新 XID 就调用一次；
 *   - procarray.c 在启动/恢复阶段按已知 XID 范围补齐页时也会调用。
 *   调用者持有 XidGenLock，因此本函数必须是快路径：绝大多数调用会在下面的
 *   提前返回处直接结束，不取锁、不做任何工作。
 *
 * 为什么只在页首动作：
 *   只有当一个 XID 是其所在页的第一个条目时，才需要初始化该页；页内后续 XID
 *   的父 XID 槽位已经随整页一起清零。特殊地，刚发生回绕后 0 号页的第一个
 *   有效 XID 是 FirstNormalTransactionId（而不是条目 0，因为 0/1 号槽位保留给
 *   Invalid/Bootstrap XID），所以该 XID 也要触发清零。
 *
 * 实现：
 *   取得目标页所在 bank 的 LWLock 排他锁，调用 SimpleLruZeroPage() 在共享
 *   内存中把整页清零并标脏，然后释放锁。
 *
 * 并发/性能注意：
 *   - 锁顺序为 XidGenLock -> SLRU bank lock；其他代码不得反向获取，以免死锁。
 *   - SimpleLruZeroPage() 可能需要淘汰一个脏页，从而间接触发磁盘写；这是
 *     “通常很快、但极端情况下仍可能 I/O”的原因（见原有英文注释）。
 */
void
ExtendSUBTRANS(TransactionId newestXact)
{
	int64		pageno;
	LWLock	   *lock;

	/*
	 * No work except at first XID of a page.  But beware: just after
	 * wraparound, the first XID of page zero is FirstNormalTransactionId.
	 */
	if (TransactionIdToEntry(newestXact) != 0 &&
		!TransactionIdEquals(newestXact, FirstNormalTransactionId))
		return;

	pageno = TransactionIdToPage(newestXact);

	lock = SimpleLruGetBankLock(SubTransCtl, pageno);
	LWLockAcquire(lock, LW_EXCLUSIVE);

	/* Zero the page */
	SimpleLruZeroPage(SubTransCtl, pageno);

	LWLockRelease(lock);
}


/*
 * Remove all SUBTRANS segments before the one holding the passed transaction ID
 *
 * oldestXact is the oldest TransactionXmin of any running transaction.  This
 * is called only during checkpoint.
 */
/*
 * 中文注释：
 * 删除所有位于 oldestXact 所在段之前的 SUBTRANS 段，回收旧子事务映射占用的
 * 磁盘空间。
 *
 * 参数：
 *   oldestXact —— 所有运行中事务中最老的 TransactionXmin。比它更老的子事务
 *   映射不会再被任何活动事务查询，因此可以安全删除。
 *
 * 调用场景与并发：
 *   只在检查点期间调用（xlog.c 的 CheckPointGuts 路径）。SimpleLruTruncate()
 *   要求调用者保证互斥：互斥必须在计算 cutoffPage 之前开始，并持续到允许其他
 *   后端向 cutoff 前一段写入新数据的限制更新之后，否则可能删掉刚写入数据的段。
 *   检查点天然满足这一要求。
 *
 * cutoff 的计算：
 *   cutoffPage 取 oldestXact 所在页。计算前先 TransactionIdRetreat(oldestXact)
 *   回退一个 XID，目的是避免一种罕见情形：oldestXact 恰是某页第一个条目且等于
 *   nextXid，此时该页可能尚未创建，直接传该页会触发 SimpleLruTruncate() 的
 *   回绕检测并误报。回退一个 XID 后，cutoff 落到前一页，语义上仍然安全。
 *
 * 副作用：
 *   SimpleLruTruncate() 会清理共享缓冲区中 cutoff 之前的页，并删除整个段文件。
 *   该操作不写 WAL；由于 pg_subtrans 本身不要求崩溃可恢复，删除后无需重做。
 */
void
TruncateSUBTRANS(TransactionId oldestXact)
{
	int64		cutoffPage;

	/*
	 * The cutoff point is the start of the segment containing oldestXact. We
	 * pass the *page* containing oldestXact to SimpleLruTruncate.  We step
	 * back one transaction to avoid passing a cutoff page that hasn't been
	 * created yet in the rare case that oldestXact would be the first item on
	 * a page and oldestXact == next XID.  In that case, if we didn't subtract
	 * one, we'd trigger SimpleLruTruncate's wraparound detection.
	 */
	TransactionIdRetreat(oldestXact);
	cutoffPage = TransactionIdToPage(oldestXact);

	SimpleLruTruncate(SubTransCtl, cutoffPage);
}


/*
 * Decide whether a SUBTRANS page number is "older" for truncation purposes.
 * Analogous to CLOGPagePrecedes().
 */
/*
 * 中文注释：
 * SLRU 的 PagePrecedes 回调：判断 page1 是否整体“更旧”于 page2。该判断同时
 * 用于 SimpleLruTruncate() 决定哪些段可以删除，以及 LRU 淘汰时的顺序提示。
 *
 * 为什么需要回绕比较：
 *   SUBTRANS 的页号直接由 32 位 XID 推导，XID 回绕时页号也会回绕。因此不能简单
 *   比较整数大小，必须按 TransactionId 的模 2^32 顺序比较。
 *
 * 具体算法：
 *   1. 把页号乘以每页条目数，得到该页 XID 区间的基准值，再加上
 *      FirstNormalTransactionId + 1 的固定偏移，使 0 号页的基准值落在第一个
 *      正常 XID 附近，避开 Invalid/Bootstrap/Frozen 等特殊 XID。
 *   2. 第一个条件要求 xid1 按回绕顺序早于 xid2（page1 的基准值早于 page2 的
 *      基准值）。
 *   3. 第二个条件进一步要求 xid1 早于 page2 区间的最后一个条目
 *      （xid2 + SUBTRANS_XACTS_PER_PAGE - 1，unsigned 加法按 32 位回绕），
 *      从而排除两页跨越回绕点、区间部分重叠时被误判为“整体更旧”的情况。
 *   只有两个条件同时成立才返回 true，保证“page1 的所有条目都早于 page2 的所有
 *   条目”。函数无副作用，比较逻辑由 SUBTRANSShmemInit() 中的
 *   SlruPagePrecedesUnitTests() 在断言构建下做单元测试。
 */
static bool
SubTransPagePrecedes(int64 page1, int64 page2)
{
	TransactionId xid1;
	TransactionId xid2;

	xid1 = ((TransactionId) page1) * SUBTRANS_XACTS_PER_PAGE;
	xid1 += FirstNormalTransactionId + 1;
	xid2 = ((TransactionId) page2) * SUBTRANS_XACTS_PER_PAGE;
	xid2 += FirstNormalTransactionId + 1;

	return (TransactionIdPrecedes(xid1, xid2) &&
			TransactionIdPrecedes(xid1, xid2 + SUBTRANS_XACTS_PER_PAGE - 1));
}

/*
 * 中文注释：
 * SLRU 的 errdetail_for_io_error 回调：当读取或写入 pg_subtrans 页面发生 I/O
 * 错误时，为 ereport() 生成的错误消息补充“具体是哪个 XID 访问失败”的详情。
 *
 * 参数：
 *   opaque_data —— 调用 SimpleLruReadPage()/SimpleLruReadPage_ReadOnly() 时
 *   传入的 TransactionId 指针。该指针通常指向调用者栈上的局部变量，只在当前
 *   ereport 期间有效，本函数不得保存它。
 *
 * 实现与约束：
 *   取出 XID 后调用 errdetail() 输出 “Could not access subtransaction status
 *   of transaction %u.”，并返回 errdetail() 的返回值（通常为 0，实际由
 *   ereport 机制消费）。本函数处于错误报告路径，且可能仍持有 SLRU 的 bank
 *   lock，因此只做最小限度的格式化，不应再执行 I/O、获取锁或抛出新的错误。
 */
static int
subtrans_errdetail_for_io_error(const void *opaque_data)
{
	TransactionId xid = *(const TransactionId *) opaque_data;

	return errdetail("Could not access subtransaction status of transaction %u.", xid);
}
