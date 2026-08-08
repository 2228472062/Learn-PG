/*-------------------------------------------------------------------------
 *
 * aio.c
 *    AIO - Core Logic
 *
 * For documentation about how AIO works on a higher level, including a
 * schematic example, see README.md.
 *
 *
 * AIO is a complicated subsystem. To keep things navigable, it is split
 * across a number of files:
 *
 * - method_*.c - different ways of executing AIO (e.g. worker process)
 *
 * - aio_target.c - IO on different kinds of targets
 *
 * - aio_io.c - method-independent code for specific IO ops (e.g. readv)
 *
 * - aio_callback.c - callbacks at IO operation lifecycle events
 *
 * - aio_init.c - per-server and per-backend initialization
 *
 * - aio.c - all other topics
 *
 * - read_stream.c - helper for reading buffered relation data
 *
 * - README.md - higher-level overview over AIO
 *
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 异步 I/O(AIO)子系统的"中央调度"与"句柄管理"核心。
 * AIO 的整体架构见 README.md;各文件职责划分见上方的英文说明。
 * 本文件承担的具体职责:
 *
 * 1) IO 句柄(PgAioHandle)生命周期管理:
 *    - pgaio_io_acquire()/pgaio_io_acquire_nb() 从本进程的空闲句柄池取出
 *      句柄并登记到资源所有者;pgaio_io_release()/pgaio_io_release_resowner()
 *      释放不需要(或出错时)的句柄;
 *    - pgaio_io_reclaim() 在 IO 完成(或句柄被放弃)后把句柄恢复为 IDLE
 *      状态、清空全部字段、递增 generation(代数)并放回空闲链表。因为
 *      句柄会被复用,外部代码一律用 PgAioWaitRef(句柄索引 + 代数)等待
 *      "某一次" IO 完成,而不是直接引用句柄。
 *
 * 2) 句柄状态机驱动(PGAIO_HS_*):IDLE → HANDED_OUT → DEFINED → STAGED
 *    → SUBMITTED → COMPLETED_IO → COMPLETED_SHARED → COMPLETED_LOCAL →
 *    (回到 IDLE)。所有状态迁移必须经过 pgaio_io_update_state(),它负责
 *    debug 日志与写内存屏障(保证状态更新前的新字段对观察者可见)。
 *    该状态机在 aio_internal.h 中有逐状态说明。
 *
 * 3) 提交(staging/submit)与批处理(batch mode):
 *    - pgaio_io_stage() 被各 pgaio_io_start_*() 调用,把已"定义"好的 IO
 *      放入本进程的 staged_ios 数组;非批处理模式立即提交;
 *    - pgaio_enter_batchmode()/pgaio_exit_batchmode() 允许一批 IO 攒齐后
 *      一次性提交(性能好),但要求代码保证"存在未提交 IO 时绝不等待其他
 *      后端",否则会死锁(详见 pgaio_enter_batchmode 注释);
 *    - pgaio_submit_staged() 在临界区内调用当前 IO 方法(method)的 submit
 *      回调,把一批 IO 交给 io_uring / worker / sync 执行。
 *
 * 4) 等待与回收:
 *    - pgaio_io_wait() 是内部等待原语:根据状态决定走 IO 方法的 wait_one
 *      (例如 io_uring 的收割)、还是条件变量(等待其他后端/提交方推进);
 *    - pgaio_io_process_completion() 是 IO 完成的统一入口,必须在临界区
 *      内调用,依次运行共享完成回调、广播条件变量,若本后端是发起者则
 *      顺手执行本地回调并回收句柄;
 *    - pgaio_io_wait_for_free() 在句柄池耗尽时复用:先回收已完成的句柄、
 *      提交所有未提交 IO,最后等待最老的 in-flight IO 完成。
 *
 * 5) 生命周期钩子:错误清理(pgaio_error_cleanup)、事务边界校验
 *    (AtEOXact_Aio)、文件描述符关闭前的冲刷(pgaio_closing_fd)、进程退出
 *    前等待全部 IO 完成(pgaio_shutdown)。
 *
 * 6) GUC 与实现选择:io_method(枚举)经 assign_io_method 把
 *    pgaio_method_ops 指向三种实现(sync / worker / io_uring)之一;
 *    io_max_concurrency 由 check_io_max_concurrency 校验(-1 表示启动时
 *    自动整定,0 非法)。
 *
 * 【关键并发设计思想】
 * - 共享内存中的句柄池(io_handles)按后端静态划分(每后端一组),普通
 *   字段无需加锁;跨进程的可见性由"状态字段 + 内存屏障 + 条件变量广播"
 *   保证;完成回调可在任意后端执行(见 aio_callback.c);
 * - 句柄被其他后端"收割"(处理完成)后,发起者依靠"读屏障 + 状态检查 +
 *   generation 变化"来安全识别"句柄已被复用",绝不在中断点之间做
 *   "检查后再操作"的非原子序列(pgaio_io_reclaim 与各等待路径都对此有
 *   明确说明);
 * - IO 完成路径运行在临界区内(可被用于 WAL 等关键路径),因此完成回调
 *   不能直接报错,而是把错误编码进 PgAioResult,由发起者在
 *   pgaio_wref_wait() 之后用 pgaio_result_report() 决定是否 raise。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *    src/backend/storage/aio/aio.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "lib/ilist.h"
#include "miscadmin.h"
#include "port/atomics.h"
#include "storage/aio.h"
#include "storage/aio_internal.h"
#include "storage/aio_subsys.h"
#include "utils/guc.h"
#include "utils/guc_hooks.h"
#include "utils/injection_point.h"
#include "utils/resowner.h"
#include "utils/wait_event_types.h"


static inline void pgaio_io_update_state(PgAioHandle *ioh, PgAioHandleState new_state);
static void pgaio_io_reclaim(PgAioHandle *ioh);
static void pgaio_io_resowner_register(PgAioHandle *ioh, struct ResourceOwnerData *resowner);
static void pgaio_io_wait_for_free(void);
static PgAioHandle *pgaio_io_from_wref(PgAioWaitRef *iow, uint64 *ref_generation);
static const char *pgaio_io_state_get_name(PgAioHandleState s);
static void pgaio_io_wait(PgAioHandle *ioh, uint64 ref_generation);


/* Options for io_method. */
/* (中文)io_method GUC 的合法取值表(enum 值 → 字符串名):
 * "sync" / "worker" / "io_uring"(后者仅当编译时启用 liburing 且非
 * EXEC_BACKEND 构建)。此表与 pgaio_method_ops_table 用下标严格对应
 * (见文件下方的 StaticAssertDecl 校验)。 */
const struct config_enum_entry io_method_options[] = {
	{"sync", IOMETHOD_SYNC, false},
	{"worker", IOMETHOD_WORKER, false},
#ifdef IOMETHOD_IO_URING_ENABLED
	{"io_uring", IOMETHOD_IO_URING, false},
#endif
	{NULL, 0, false}
};

/* GUCs */
/* (中文)io_method:当前配置的 AIO 实现方式(0=sync,1=worker,2=io_uring),
 * 默认 worker(DEFAULT_IO_METHOD)。由 assign_io_method 钩子在 GUC 赋值时
 * 同步维护 pgaio_method_ops。
 * io_max_concurrency:每个后端允许并发在途的 IO 个数;-1 表示"启动时按
 * 系统环境自动整定"(见 aio_init.c),0 非法。 */
int			io_method = DEFAULT_IO_METHOD;
int			io_max_concurrency = -1;

/* global control for AIO */
/* (中文)全局 AIO 控制结构(位于共享内存,各进程共享):句柄池 io_handles、
 * iovec 池、handle_data 池与每后端的 PgAioBackend 状态数组,详见
 * aio_internal.h 中的 PgAioCtl 定义。启动时在 pgaio_init_shmem() 中分配。 */
PgAioCtl   *pgaio_ctl;

/* current backend's per-backend state */
/* (中文)当前后端的 AIO 私有状态(进程本地,不在共享内存):空闲句柄链表
 * idle_ios、in-flight 链表 in_flight_ios、未提交的 staged_ios 数组、
 * in_batchmode 标志等,详见 aio_internal.h 中的 PgAioBackend 定义。
 * 由 pgaio_init_backend() 初始化,退出时在 pgaio_shutdown() 里置回 NULL。 */
PgAioBackend *pgaio_my_backend;


/* (中文)IO 方法分发表:以 IoMethod 枚举值为下标的函数指针表,把三种
 * AIO 实现(sync 回退 / worker 线程 / io_uring)统一封装成 IoMethodOps。
 * 数组长度必须与 io_method_options 一一对应(有 StaticAssertDecl 校验)。 */
static const IoMethodOps *const pgaio_method_ops_table[] = {
	[IOMETHOD_SYNC] = &pgaio_sync_ops,
	[IOMETHOD_WORKER] = &pgaio_worker_ops,
#ifdef IOMETHOD_IO_URING_ENABLED
	[IOMETHOD_IO_URING] = &pgaio_uring_ops,
#endif
};

StaticAssertDecl(lengthof(io_method_options) == lengthof(pgaio_method_ops_table) + 1,
				 "io_method_options out of sync with pgaio_method_ops_table");

/* callbacks for the configured io_method, set by assign_io_method */
/* (中文)当前生效 IO 方法的操作集(指针,非 const 以便运行时切换):
 * 由 assign_io_method 在 GUC io_method 变更时从 pgaio_method_ops_table
 * 选中。AIO 核心代码一律经由该指针调用方法回调,因此切换实现不需要
 * 修改调度逻辑。 */
const IoMethodOps *pgaio_method_ops;


/* --------------------------------------------------------------------------------
 * Public Functions related to PgAioHandle
 * --------------------------------------------------------------------------------
 */

/*
 * Acquire an AioHandle, waiting for IO completion if necessary.
 *
 * Each backend can only have one AIO handle that has been "handed out" to
 * code, but not yet submitted or released. This restriction is necessary to
 * ensure that it is possible for code to wait for an unused handle by waiting
 * for in-flight IO to complete. There is a limited number of handles in each
 * backend, if multiple handles could be handed out without being submitted,
 * waiting for all in-flight IO to complete would not guarantee that handles
 * free up.
 *
 * It is cheap to acquire an IO handle, unless all handles are in use. In that
 * case this function waits for the oldest IO to complete. If that is not
 * desirable, use pgaio_io_acquire_nb().
 *
 * If a handle was acquired but then does not turn out to be needed,
 * e.g. because pgaio_io_acquire() is called before starting an IO in a
 * critical section, the handle needs to be released with pgaio_io_release().
 *
 *
 * To react to the completion of the IO as soon as it is known to have
 * completed, callbacks can be registered with pgaio_io_register_callbacks().
 *
 * To actually execute IO using the returned handle, the pgaio_io_start_*()
 * family of functions is used. In many cases the pgaio_io_start_*() call will
 * not be done directly by code that acquired the handle, but by lower level
 * code that gets passed the handle. E.g. if code in bufmgr.c wants to perform
 * AIO, it typically will pass the handle to smgr.c, which will pass it on to
 * md.c, on to fd.c, which then finally calls pgaio_io_start_*().  This
 * forwarding allows the various layers to react to the IO's completion by
 * registering callbacks. These callbacks in turn can translate a lower
 * layer's result into a result understandable by a higher layer.
 *
 * During pgaio_io_start_*() the IO is staged (i.e. prepared for execution but
 * not submitted to the kernel). Unless in batchmode
 * (c.f. pgaio_enter_batchmode()), the IO will also get submitted for
 * execution. Note that, whether in batchmode or not, the IO might even
 * complete before the functions return.
 *
 * After pgaio_io_start_*() the AioHandle is "consumed" and may not be
 * referenced by the IO issuing code. To e.g. wait for IO, references to the
 * IO can be established with pgaio_io_get_wref() *before* pgaio_io_start_*()
 * is called.  pgaio_wref_wait() can be used to wait for the IO to complete.
 *
 *
 * To know if the IO [partially] succeeded or failed, a PgAioReturn * can be
 * passed to pgaio_io_acquire(). Once the issuing backend has called
 * pgaio_wref_wait(), the PgAioReturn contains information about whether the
 * operation succeeded and details about the first failure, if any. The error
 * can be raised / logged with pgaio_result_report().
 *
 * The lifetime of the memory pointed to be *ret needs to be at least as long
 * as the passed in resowner. If the resowner releases resources before the IO
 * completes (typically due to an error), the reference to *ret will be
 * cleared. In case of resowner cleanup *ret will not be updated with the
 * results of the IO operation.
 */
/*
 * pgaio_io_acquire - (中文)获取一个 AIO 句柄;若本后端句柄池耗尽则阻塞等待
 *
 * 【作用】发起异步 I/O 的第一步:向 AIO 子系统"借用"一个空闲的
 * PgAioHandle,为接下来用 pgaio_io_start_*() 定义具体的读/写操作做准备。
 * 句柄获取成功后进入 PGAIO_HS_HANDED_OUT 状态,并登记到传入的资源所有者
 * (resowner),保证事务出错回滚时句柄会被自动清理(见
 * pgaio_io_release_resowner)。若随后发现不需要这个句柄(例如持有锁之前
 * 预先获取的句柄),必须调用 pgaio_io_release() 归还,否则会违反"同一
 * 时刻每后端至多一个已发放未定义句柄"的规则,阻塞后续获取。
 *
 * 【设计思想】
 * - 为什么必须"永远能获取到句柄"?因为 AIO 可能要在临界区(critical
 *   section)内发起(WAL 写入等场景),那时不允许报错。本函数通过"句柄
 *   不足就等待在途 IO 完成、腾出句柄再重试"保证必然成功(除非 PANIC)。
 * - 为什么每后端同时只能发放一个句柄?句柄池大小有限,若允许多个句柄
 *   同时"已发放未提交",等待全部在途 IO 完成也无法保证能腾出空闲句柄,
 *   代码可能自死锁。该限制由 pgaio_my_backend->handed_out_io 强制执行
 *   (见 pgaio_io_acquire_nb 的报错)。
 * - 想避免阻塞?句柄不足时本函数会等待;不想等待请用
 *   pgaio_io_acquire_nb(),它在无空闲句柄时直接返回 NULL。
 *
 * 【参数】
 *   resowner —— 句柄所属的资源所有者;句柄会登记到它名下,资源释放时
 *               (典型场景:出错回滚)由 pgaio_io_release_resowner() 负责
 *               回收。可以为 NULL(此时不登记,但调用者必须自行保证清理)。
 *   ret      —— 可空。指向调用者本地内存中的 PgAioReturn;IO 完成且本
 *               后端获知结果后,该结构会被填入结果(状态 + 出错细节 +
 *               目标信息),供调用者在 pgaio_wref_wait() 之后检查或用
 *               pgaio_result_report() 报错。其内存生命周期必须不短于
 *               resowner 的生命周期。
 * 【返回值】获取到的句柄指针(必然非 NULL;除非 PANIC)。
 * 注意:返回后句柄已被"发放",只能有一个后续动作——定义(pgaio_io_start_*)
 * 或归还(pgaio_io_release)。
 */
PgAioHandle *
pgaio_io_acquire(struct ResourceOwnerData *resowner, PgAioReturn *ret)
{
	PgAioHandle *h;

	while (true)
	{
		h = pgaio_io_acquire_nb(resowner, ret);

		if (h != NULL)
			return h;

		/*
		 * Evidently all handles by this backend are in use. Just wait for
		 * some to complete.
		 */
		pgaio_io_wait_for_free();
	}
}

/*
 * Acquire an AioHandle, returning NULL if no handles are free.
 *
 * See pgaio_io_acquire(). The only difference is that this function will return
 * NULL if there are no idle handles, instead of blocking.
 */
/*
 * pgaio_io_acquire_nb - (中文)获取一个 AIO 句柄,无空闲句柄时直接返回 NULL(不阻塞)
 *
 * 【作用】pgaio_io_acquire() 的非阻塞版本。执行顺序:
 * 1. 若 staged(已定义未提交)IO 已攒满一整批(PGAIO_SUBMIT_BATCH_SIZE),
 *    先提交,避免后续 IO 没地方排队;
 * 2. 若已有"已发放未定义"的句柄,属 API 违规,报错;
 * 3. 在 HOLD_INTERRUPTS() 保护下从空闲链表弹出一个 IDLE 句柄:置为
 *    HANDED_OUT、记录为 handed_out_io、登记 resowner、可选地把 *ret
 *    置为"结果未知"初始状态(PGAIO_RS_UNKNOWN);
 * 4. RESUME_INTERRUPTS() 后返回。
 *
 * 【设计思想】
 * - 为什么需要 HOLD_INTERRUPTS()?空闲链表是进程私有数据结构,且句柄
 *   的"发放"与状态切换必须与中断处理(它可能去回收句柄)互斥,防止
 *   状态混乱。
 * - 只在"确实拿到句柄"时才给 *ret 填 UNKNOWN:调用者通常以 ret 的
 *   status 是否 UNKNOWN 判断"IO 是否已经开始",因此获取失败(NULL)时
 *   必须保持 *ret 原样。
 *
 * 【参数】resowner —— 句柄登记的资源所有者(可空,含义同 pgaio_io_acquire);
 *        ret      —— 可空,指向 PgAioReturn 输出区(成功获取时初始化为
 *                     PGAIO_RS_UNKNOWN)。
 * 【返回值】空闲句柄指针;本后端句柄池全部在用时返回 NULL(调用者应改用
 * pgaio_io_acquire() 等待,或自行决定放弃发起 IO)。
 */
PgAioHandle *
pgaio_io_acquire_nb(struct ResourceOwnerData *resowner, PgAioReturn *ret)
{
	PgAioHandle *ioh = NULL;

	if (pgaio_my_backend->num_staged_ios >= PGAIO_SUBMIT_BATCH_SIZE)
	{
		Assert(pgaio_my_backend->num_staged_ios == PGAIO_SUBMIT_BATCH_SIZE);
		pgaio_submit_staged();
	}

	if (pgaio_my_backend->handed_out_io)
		elog(ERROR, "API violation: Only one IO can be handed out");

	/*
	 * Probably not needed today, as interrupts should not process this IO,
	 * but...
	 */
	HOLD_INTERRUPTS();

	if (!dclist_is_empty(&pgaio_my_backend->idle_ios))
	{
		dlist_node *ion = dclist_pop_head_node(&pgaio_my_backend->idle_ios);

		ioh = dclist_container(PgAioHandle, node, ion);

		Assert(ioh->state == PGAIO_HS_IDLE);
		Assert(ioh->owner_procno == MyProcNumber);

		pgaio_io_update_state(ioh, PGAIO_HS_HANDED_OUT);
		pgaio_my_backend->handed_out_io = ioh;

		if (resowner)
			pgaio_io_resowner_register(ioh, resowner);

		if (ret)
		{
			ioh->report_return = ret;
			ret->result.status = PGAIO_RS_UNKNOWN;
		}
	}

	RESUME_INTERRUPTS();

	return ioh;
}

/*
 * Release IO handle that turned out to not be required.
 *
 * See pgaio_io_acquire() for more details.
 */
/*
 * pgaio_io_release - (中文)归还"获取了但最终没用上"的 AIO 句柄
 *
 * 【作用】句柄处于 HANDED_OUT(已发放未定义)状态时调用:清空
 * handed_out_io 标志,然后 pgaio_io_reclaim() 把它恢复到 IDLE 并放回
 * 空闲链表。典型场景:在可能持锁的路径上预先获取了句柄,结果发现不需要
 * 发起 IO(例如拿到了缓冲区锁后才发现缓冲已有效)。
 *
 * 【设计思想】若句柄已进入 DEFINED 及以后的状态,说明 IO 已被定义,此时
 * 调用本函数属于 API 违规(报错)。注意"检查 handed_out_io 是否等于 ioh"
 * 与"调用 reclaim"之间不允许处理中断,否则中断处理可能已经把这个句柄
 * 回收了(见函数体注释)。
 *
 * 【参数】ioh —— 要归还的句柄(必须 == pgaio_my_backend->handed_out_io)。
 * 【返回值】无。
 */
void
pgaio_io_release(PgAioHandle *ioh)
{
	if (ioh == pgaio_my_backend->handed_out_io)
	{
		Assert(ioh->state == PGAIO_HS_HANDED_OUT);
		Assert(ioh->resowner);

		pgaio_my_backend->handed_out_io = NULL;

		/*
		 * Note that no interrupts are processed between the handed_out_io
		 * check and the call to reclaim - that's important as otherwise an
		 * interrupt could have already reclaimed the handle.
		 */
		pgaio_io_reclaim(ioh);
	}
	else
	{
		elog(ERROR, "release in unexpected state");
	}
}

/*
 * Release IO handle during resource owner cleanup.
 */
/*
 * pgaio_io_release_resowner - (中文)资源所有者清理期间释放 AIO 句柄
 *
 * 【作用】句柄登记到的资源所有者(resowner)被释放时(典型场景:事务/
 * 子事务出错回滚、或显式 RELEASE),由资源所有者框架回调本函数,针对句柄
 * 所处状态做对应处理:
 * - HANDED_OUT(获取后未定义):回收句柄;若并非因错误而释放(on_error
 *   == false),说明代码泄漏了句柄,发 WARNING 提示;
 * - DEFINED / STAGED(已定义未提交):报 WARNING 后调用
 *   pgaio_submit_staged() 把 IO 提交出去。不能丢弃:其他后端可能正在
 *   等待该 IO 完成;
 * - SUBMITTED 及之后的各完成态:IO 已在途/已完成,无需处理(resowner
 *   释放只是解除登记,等待方仍能正常拿到结果);
 * - IDLE:不可能出现(资源所有者只登记非空闲句柄),报错。
 *
 * 【设计思想】本函数必须先解除句柄与 resowner 的登记(ResourceOwnerForget),
 * 因为 resowner 框架对"同一资源被释放两次"会报错;而句柄的状态迁移、
 * 提交等动作放在解除登记之后,逻辑上仍安全(句柄本身在共享内存,不随
 * resowner 消失)。全程 HOLD_INTERRUPTS(),防止中断在清理中途来等待
 * 该 IO 造成状态混乱。最后清空 report_return:其指向的内存(resowner
 * 下的局部变量)已经或即将消失,不能再往里写结果。
 *
 * 【参数】
 *   ioh_node —— 资源所有者持有的链表节点(其宿主即要释放的句柄);
 *   on_error —— 本次释放是否由错误触发(resowner 出错回滚时为 true,
 *                正常提交路径释放为 false;决定泄漏警告是否发出)。
 * 【返回值】无。
 */
void
pgaio_io_release_resowner(dlist_node *ioh_node, bool on_error)
{
	PgAioHandle *ioh = dlist_container(PgAioHandle, resowner_node, ioh_node);

	Assert(ioh->resowner);

	/*
	 * Otherwise an interrupt, in the middle of releasing the IO, could end up
	 * trying to wait for the IO, leading to state confusion.
	 */
	HOLD_INTERRUPTS();

	ResourceOwnerForgetAioHandle(ioh->resowner, &ioh->resowner_node);
	ioh->resowner = NULL;

	switch ((PgAioHandleState) ioh->state)
	{
		case PGAIO_HS_IDLE:
			elog(ERROR, "unexpected");
			break;
		case PGAIO_HS_HANDED_OUT:
			Assert(ioh == pgaio_my_backend->handed_out_io || pgaio_my_backend->handed_out_io == NULL);

			if (ioh == pgaio_my_backend->handed_out_io)
			{
				pgaio_my_backend->handed_out_io = NULL;
				if (!on_error)
					elog(WARNING, "leaked AIO handle");
			}

			pgaio_io_reclaim(ioh);
			break;
		case PGAIO_HS_DEFINED:
		case PGAIO_HS_STAGED:
			if (!on_error)
				elog(WARNING, "AIO handle was not submitted");
			pgaio_submit_staged();
			break;
		case PGAIO_HS_SUBMITTED:
		case PGAIO_HS_COMPLETED_IO:
		case PGAIO_HS_COMPLETED_SHARED:
		case PGAIO_HS_COMPLETED_LOCAL:
			/* this is expected to happen */
			break;
	}

	/*
	 * Need to unregister the reporting of the IO's result, the memory it's
	 * referencing likely has gone away.
	 */
	if (ioh->report_return)
		ioh->report_return = NULL;

	RESUME_INTERRUPTS();
}

/*
 * Add a [set of] flags to the IO.
 *
 * Note that this combines flags with already set flags, rather than set flags
 * to explicitly the passed in parameters. This is to allow multiple callsites
 * to set flags.
 */
/*
 * pgaio_io_set_flag - (中文)给句柄设置一个/一组标志(与已有标志做按位或)
 *
 * 【作用】在句柄处于 HANDED_OUT(已发放、尚未定义 IO)状态时,设置
 * PgAioHandleFlags 中的若干位,例如:
 * - PGAIO_HF_REFERENCES_LOCAL:IO 涉及本进程私有内存,某些方法(worker)
 *   无法直接执行,会退化为同步执行;
 * - PGAIO_HF_SYNCHRONOUS:提示本 IO 将同步执行,可以省去异步路径的开销;
 * - PGAIO_HF_BUFFERED:使用缓冲 I/O,供某些方法做启发式决策。
 * 采用"或"而非"覆盖"语义,允许链路上多个调用点各自追加标志。
 *
 * 【参数】ioh —— 目标句柄;flag —— 要追加的标志位组合。
 * 【返回值】无。
 */
void
pgaio_io_set_flag(PgAioHandle *ioh, PgAioHandleFlags flag)
{
	Assert(ioh->state == PGAIO_HS_HANDED_OUT);

	ioh->flags |= flag;
}

/*
 * Returns an ID uniquely identifying the IO handle. This is only really
 * useful for logging, as handles are reused across multiple IOs.
 */
/*
 * pgaio_io_get_id - (中文)返回句柄的唯一编号(在句柄池中的下标)
 *
 * 【作用】把句柄指针换算成 [0, io_handle_count) 内的整数编号。句柄在
 * 共享内存数组中连续排列,下标即编号。该编号只用于日志/调试输出(例如
 * pgaio_debug_io 前缀的 "io %d");注意句柄会被复用,同一编号在不同时间
 * 代表不同的 IO,不要把它当作 IO 的全局唯一标识。
 *
 * 【参数】ioh —— 目标句柄(必须是共享内存句柄池内的合法指针)。
 * 【返回值】句柄编号(0 基)。
 */
int
pgaio_io_get_id(PgAioHandle *ioh)
{
	Assert(ioh >= pgaio_ctl->io_handles &&
		   ioh < (pgaio_ctl->io_handles + pgaio_ctl->io_handle_count));
	return ioh - pgaio_ctl->io_handles;
}

/*
 * Return the ProcNumber for the process that can use an IO handle. The
 * mapping from IO handles to PGPROCs is static, therefore this even works
 * when the corresponding PGPROC is not in use.
 */
/*
 * pgaio_io_get_owner - (中文)返回句柄所属后端(发起者)的 ProcNumber
 *
 * 【作用】句柄池在共享内存初始化时就按后端静态划分:每个后端固定拥有
 * 一段连续句柄(owner_procno 在分配时写死,不再变化)。因此本函数随时
 * 可查,即使对应后端进程已经退出。调用方用它判断"完成回调该由谁执行"
 * (发起者负责本地回调)或生成日志。
 *
 * 【参数】ioh —— 目标句柄。
 * 【返回值】句柄归属后端的 ProcNumber。
 */
ProcNumber
pgaio_io_get_owner(PgAioHandle *ioh)
{
	return ioh->owner_procno;
}

/*
 * Return a wait reference for the IO. Only wait references can be used to
 * wait for an IOs completion, as handles themselves can be reused after
 * completion.  See also the comment above pgaio_io_acquire().
 */
/*
 * pgaio_io_get_wref - (中文)为句柄生成一个"等待引用"(PgAioWaitRef)
 *
 * 【作用】把句柄压缩成一个轻量借据:句柄池下标 + 当前代数(generation,
 * 64 位拆成高/低两个 32 位)。调用者把这个借据保存下来,之后可以跨函数、
 * 甚至跨进程地用 pgaio_wref_wait() 等待该 IO 完成。
 *
 * 【设计思想】句柄在 IO 完成后会被复用(归还空闲池),因此"句柄指针"
 * 不能用来等待——等到的可能是下一次 IO。等待引用里带上代数,等待方
 * 通过"代数是否变化"判断句柄是否已被复用、从而避免误等新 IO(见
 * pgaio_io_was_recycled)。必须在本后端句柄的 HANDED_OUT 之后、尚未
 * 提交之前的窗口内获取引用,此时代数尚未被 reclaim 递增。引用可从
 * 任何进程发出等待,故 PgAioWaitRef 可在共享内存中传递。
 *
 * 【参数】ioh —— 已发放(或已定义/已 staged,即尚未提交)的句柄;
 *        iow —— 输出参数,接收生成的等待引用。
 * 【返回值】无。
 */
void
pgaio_io_get_wref(PgAioHandle *ioh, PgAioWaitRef *iow)
{
	Assert(ioh->state == PGAIO_HS_HANDED_OUT ||
		   ioh->state == PGAIO_HS_DEFINED ||
		   ioh->state == PGAIO_HS_STAGED);
	Assert(ioh->generation != 0);

	iow->aio_index = ioh - pgaio_ctl->io_handles;
	iow->generation_upper = (uint32) (ioh->generation >> 32);
	iow->generation_lower = (uint32) ioh->generation;
}



/* --------------------------------------------------------------------------------
 * Internal Functions related to PgAioHandle
 * --------------------------------------------------------------------------------
 */

/*
 * pgaio_io_update_state - (中文)句柄状态机唯一合法的状态迁移入口
 *
 * 【作用】把句柄从当前状态推进到 new_state,并:
 * 1. 输出 DEBUG5 日志(含句柄 id / op / target / 新旧状态);
 * 2. 写内存屏障(pg_write_barrier)——确保"状态新值所代表的所有字段
 *    更新"先于"状态新值本身"对其他进程可见。
 *
 * 【设计思想】状态字段被多个进程读取(完成收割的后端、等待中的后端),
 * 而其他字段(结果、回调数据等)是普通内存写。若没有屏障,读者可能先
 * 看到"状态已变"而后看到"新字段的旧值",得出错误结论。所有状态迁移
 * 必须经由本函数,便于集中审计与调试。调用者必须保证当前不允许处理
 * 中断(interrupts held),否则中断处理可能在中间态去等待该 IO,造成
 * 状态混乱(见函数内 Assert)。
 *
 * 【参数】ioh —— 目标句柄;new_state —— 要迁移到的状态。
 * 【返回值】无。
 */
static inline void
pgaio_io_update_state(PgAioHandle *ioh, PgAioHandleState new_state)
{
	/*
	 * All callers need to have held interrupts in some form, otherwise
	 * interrupt processing could wait for the IO to complete, while in an
	 * intermediary state.
	 */
	Assert(!INTERRUPTS_CAN_BE_PROCESSED());

	pgaio_debug_io(DEBUG5, ioh,
				   "updating state to %s",
				   pgaio_io_state_get_name(new_state));

	/*
	 * Ensure the changes signified by the new state are visible before the
	 * new state becomes visible.
	 */
	pg_write_barrier();

	ioh->state = new_state;
}

/*
 * pgaio_io_resowner_register - (中文)把句柄登记到资源所有者名下
 *
 * 【作用】把句柄的 resowner_node 挂到 resowner 的资源链上,并在句柄里
 * 记录所属 resowner。此后若该 resowner 被释放(典型:出错回滚),框架会
 * 经 pgaio_io_release_resowner() 回调,自动处理句柄,避免泄漏与
 * report_return 悬垂。
 *
 * 【前置条件】句柄此前未登记过任何 resowner(Assert 强制),且 resowner
 * 非空。解除登记使用 ResourceOwnerForgetAioHandle(见 reclaim)。
 *
 * 【参数】ioh —— 要登记的句柄;resowner —— 目标资源所有者。
 * 【返回值】无。
 */
static void
pgaio_io_resowner_register(PgAioHandle *ioh, struct ResourceOwnerData *resowner)
{
	Assert(!ioh->resowner);
	Assert(resowner);

	ResourceOwnerRememberAioHandle(resowner, &ioh->resowner_node);
	ioh->resowner = resowner;
}

/*
 * Stage IO for execution and, if appropriate, submit it immediately.
 *
 * Should only be called from pgaio_io_start_*().
 */
/*
 * pgaio_io_stage - (中文)把已定义好的 IO 送入"排队/提交"流程(staging)
 *
 * 【作用】被各 pgaio_io_start_*(readv/writev)调用,是句柄从"已定义"到
 * "真正执行"的唯一通道,流程:
 * 1. HOLD_INTERRUPTS(),记录 op、清空 result,状态 → DEFINED;
 *    此刻句柄已"消费"完毕:清空 handed_out_io,允许下一个句柄被发放;
 * 2. 调用 stage 回调链(pgaio_io_call_stage,见 aio_callback.c)——下层
 *    借此对 IO 涉及资源做预备(例如给缓冲区 pin 追加引用计数);
 * 3. 状态 → STAGED;然后判断执行方式:
 *    - 需要同步执行(调用方打了 PGAIO_HF_SYNCHRONOUS 标志,或当前 IO
 *      方法不支持该 IO,见 pgaio_io_needs_synchronous_execution):直接
 *      pgaio_io_prepare_submit() + pgaio_io_perform_synchronously()
 *      当场完成;
 *    - 否则:把句柄放入本进程 staged_ios 数组(攒批);除非处于批处理
 *      模式(in_batchmode),立即 pgaio_submit_staged() 提交给 IO 方法。
 * 4. RESUME_INTERRUPTS()。
 *
 * 【设计思想】
 * - "staged 数组"把多次 IO 攒成一批再提交:批量提交(尤其 io_uring 的
 *   SQE 批量入队)比逐个提交开销小得多;
 * - 同步与异步两条路径在此分叉,使上层代码只需写一套接口;
 * - 即使走异步路径,提交后 IO 也可能立即完成(甚至在本函数返回前),
 *   调用方必须对"句柄已被回收"免疫(即:返回后不得再触碰句柄)。
 *
 * 【参数】ioh —— HANDED_OUT 状态、已设置好 target 与 op_data 的句柄;
 *        op  —— 本次 IO 的操作类型(PGAIO_OP_READV / PGAIO_OP_WRITEV)。
 * 【返回值】无。返回后句柄已"消费",不得再引用(除非持有等待引用)。
 */
void
pgaio_io_stage(PgAioHandle *ioh, PgAioOp op)
{
	bool		needs_synchronous;

	Assert(ioh->state == PGAIO_HS_HANDED_OUT);
	Assert(pgaio_my_backend->handed_out_io == ioh);
	Assert(pgaio_io_has_target(ioh));

	/*
	 * Otherwise an interrupt, in the middle of staging and possibly executing
	 * the IO, could end up trying to wait for the IO, leading to state
	 * confusion.
	 */
	HOLD_INTERRUPTS();

	ioh->op = op;
	ioh->result = 0;

	pgaio_io_update_state(ioh, PGAIO_HS_DEFINED);

	/* allow a new IO to be staged */
	pgaio_my_backend->handed_out_io = NULL;

	pgaio_io_call_stage(ioh);

	pgaio_io_update_state(ioh, PGAIO_HS_STAGED);

	/*
	 * Synchronous execution has to be executed, well, synchronously, so check
	 * that first.
	 */
	needs_synchronous = pgaio_io_needs_synchronous_execution(ioh);

	pgaio_debug_io(DEBUG3, ioh,
				   "staged (synchronous: %d, in_batch: %d)",
				   needs_synchronous, pgaio_my_backend->in_batchmode);

	if (!needs_synchronous)
	{
		pgaio_my_backend->staged_ios[pgaio_my_backend->num_staged_ios++] = ioh;
		Assert(pgaio_my_backend->num_staged_ios <= PGAIO_SUBMIT_BATCH_SIZE);

		/*
		 * Unless code explicitly opted into batching IOs, submit the IO
		 * immediately.
		 */
		if (!pgaio_my_backend->in_batchmode)
			pgaio_submit_staged();
	}
	else
	{
		pgaio_io_prepare_submit(ioh);
		pgaio_io_perform_synchronously(ioh);
	}

	RESUME_INTERRUPTS();
}

/*
 * pgaio_io_needs_synchronous_execution - (中文)判断该 IO 是否必须同步执行
 *
 * 【作用】决定句柄走异步提交还是同步执行路径,两个判据(任一为真即同步):
 * 1. 调用方显式打了 PGAIO_HF_SYNCHRONOUS 标志(意图就是同步执行,
 *    例如只想复用 AIO 接口、避免维护两套代码);
 * 2. 当前 IO 方法声明"不支持异步执行此类 IO"——典型是 IO 引用本进程
 *    私有内存(PGAIO_HF_REFERENCES_LOCAL)而当前方法(如 worker)无法在
 *    别的进程里安全访问该内存,只能退化同步。
 *
 * 【设计思想】同步执行其实也是通过同一套状态机与完成回调完成的,只是
 * "提交"与"完成"发生在同一次调用内,因此上层无需区分。XXX 注释提示:
 * 未来可优化——先看是否有在途 IO,若没有就不必同步等待(但收益待评估)。
 *
 * 【参数】ioh —— STAGED 状态的句柄。
 * 【返回值】true = 应同步执行;false = 可异步提交。
 */
bool
pgaio_io_needs_synchronous_execution(PgAioHandle *ioh)
{
	/*
	 * If the caller said to execute the IO synchronously, do so.
	 *
	 * XXX: We could optimize the logic when to execute synchronously by first
	 * checking if there are other IOs in flight and only synchronously
	 * executing if not. Unclear whether that'll be sufficiently common to be
	 * worth worrying about.
	 */
	if (ioh->flags & PGAIO_HF_SYNCHRONOUS)
		return true;

	/* Check if the IO method requires synchronous execution of IO */
	if (pgaio_method_ops->needs_synchronous_execution)
		return pgaio_method_ops->needs_synchronous_execution(ioh);

	return false;
}

/*
 * Handle IO being processed by IO method.
 *
 * Should be called by IO methods / synchronous IO execution, just before the
 * IO is performed.
 */
/*
 * pgaio_io_prepare_submit - (中文)IO 即将交给方法执行前的统一准备
 *
 * 【作用】把句柄状态推进到 SUBMITTED,并把它挂到本后端的 in_flight_ios
 * 链表尾部(按提交时间排序,头元素是最老的)。之后方法(或其同步执行
 * 路径)执行实际的 readv/writev。
 *
 * 【设计思想】in_flight 链表是"本后端发起的、尚未被本后端回收"的句柄
 * 清单:句柄不足时 pgaio_io_wait_for_free() 等它;关闭 fd 时
 * pgaio_closing_fd() 扫它;退出时 pgaio_shutdown() 等它。挂在尾部保证
 * 等待"最老 IO"时从头取即可。
 *
 * 【参数】ioh —— STAGED 状态、即将提交的句柄。
 * 【返回值】无。
 */
void
pgaio_io_prepare_submit(PgAioHandle *ioh)
{
	pgaio_io_update_state(ioh, PGAIO_HS_SUBMITTED);

	dclist_push_tail(&pgaio_my_backend->in_flight_ios, &ioh->node);
}

/*
 * Handle IO getting completed by a method.
 *
 * Should be called by IO methods / synchronous IO execution, just after the
 * IO has been performed.
 *
 * Expects to be called in a critical section. We expect IOs to be usable for
 * WAL etc, which requires being able to execute completion callbacks in a
 * critical section.
 */
/*
 * pgaio_io_process_completion - (中文)IO 完成结果的统一处理入口
 *
 * 【作用】由 IO 方法(io_uring 的收割 / worker 的消息 / sync 的直接返回)
 * 在"一次 IO 执行完毕后"调用,完成从"结果已知"到"对外可见"的推进:
 * 1. 记录原始结果(result,即 readv/writev 的返回值);
 * 2. 状态 → COMPLETED_IO;
 * 3. 运行共享完成回调链(pgaio_io_call_complete_shared):各注册层
 *    (md.c 校验长度、bufmgr 更新 BufferDesc 等)逐层处理结果,把成败
 *    蒸馏成 PgAioResult(注意运行在临界区内,回调不得报错);
 * 4. 状态 → COMPLETED_SHARED;
 * 5. 广播句柄条件变量:等待者(可能在其他进程)被唤醒;
 * 6. 若本进程恰好是发起者,立即执行本地完成回调并回收句柄(见
 *    pgaio_io_reclaim)——此时 COMPLETED_LOCAL 与 IDLE 会在返回前达成;
 *    否则句柄停在 COMPLETED_SHARED,等发起者自己来取(见 pgaio_io_wait)。
 *
 * 【设计思想】本函数必须在临界区内调用(CritSectionCount > 0,函数内有
 * Assert),因为它可能服务于"在临界区中发起的 IO"(如 WAL 写):完成
 * 处理不允许抛错。共享回调与条件变量广播的顺序很重要——广播前必须
 * 完成状态更新,否则等待者醒来看不到新状态(条件变量的内存语义保证
 * 唤醒后可见,见代码注释)。
 *
 * 【参数】ioh —— SUBMITTED 状态的句柄;result —— 底层系统调用的返回
 *        值(如 readv 的字节数或 -1 的 errno)。
 * 【返回值】无。
 */
void
pgaio_io_process_completion(PgAioHandle *ioh, int result)
{
	Assert(ioh->state == PGAIO_HS_SUBMITTED);

	Assert(CritSectionCount > 0);

	ioh->result = result;

	pgaio_io_update_state(ioh, PGAIO_HS_COMPLETED_IO);

	INJECTION_POINT("aio-process-completion-before-shared", ioh);

	pgaio_io_call_complete_shared(ioh);

	pgaio_io_update_state(ioh, PGAIO_HS_COMPLETED_SHARED);

	/* condition variable broadcast ensures state is visible before wakeup */
	ConditionVariableBroadcast(&ioh->cv);

	/* contains call to pgaio_io_call_complete_local() */
	if (ioh->owner_procno == MyProcNumber)
		pgaio_io_reclaim(ioh);
}

/*
 * Has the IO completed and thus the IO handle been reused?
 *
 * This is useful when waiting for IO completion at a low level (e.g. in an IO
 * method's ->wait_one() callback).
 */
/*
 * pgaio_io_was_recycled - (中文)判断句柄自某个等待引用建立后是否已被复用
 *
 * 【作用】等待方持有"句柄 + 期望代数(ref_generation)"时,调用本函数
 * 判断句柄是否已经被回收并重新分配给了新 IO:把句柄当前代数与期望代数
 * 比较,不同即"已被复用"。同时通过输出参数返回读到的当前状态。
 *
 * 【设计思想】句柄复用后所有字段都会被清零重填,继续等待同一指针毫无
 * 意义(可能等到毫不相干的后续 IO)。代数(每次回收 +1)是识别复用的
 * 唯一可靠手段。函数先读状态、再做读屏障再读代数:屏障保证不会因
 * 编译器/CPU 重排而"看到比 state 更旧的代数",从而既保护了代数判断,
 * 也保护了调用方在"未被复用"前提下继续读取句柄其他字段的正确性。
 *
 * 【参数】ioh —— 共享内存句柄;ref_generation —— 建立等待时的期望代数;
 *        state —— 输出参数,句柄当前状态(即使被复用也会给出)。
 * 【返回值】true = 句柄已被复用(等待目标已完成,应停止等待);
 * false = 还是同一个 IO,可按 *state 继续等待。
 */
bool
pgaio_io_was_recycled(PgAioHandle *ioh, uint64 ref_generation, PgAioHandleState *state)
{
	*state = ioh->state;

	/*
	 * Ensure that we don't see an earlier state of the handle than ioh->state
	 * due to compiler or CPU reordering. This protects both ->generation as
	 * directly used here, and other fields in the handle accessed in the
	 * caller if the handle was not reused.
	 */
	pg_read_barrier();

	return ioh->generation != ref_generation;
}

/*
 * Wait for IO to complete. External code should never use this, outside of
 * the AIO subsystem waits are only allowed via pgaio_wref_wait().
 */
/*
 * pgaio_io_wait - (中文)句柄级等待原语:等到该 IO 完成或被复用
 *
 * 【作用】内部等待实现(对外统一走 pgaio_wref_wait)。根据句柄当前状态
 * 走不同路径:
 * - 已复用(recycled):直接返回,等待目的达成;
 * - SUBMITTED 且方法提供了 wait_one(如 io_uring 需要主动收割):调用
 *   wait_one 推进完成,再重新检查;若 IO 是同步执行(PGAIO_HF_SYNCHRONOUS)
 *   则跳过 wait_one(同步路径必然当场完成);
 * - DEFINED / STAGED / COMPLETED_IO:在句柄条件变量上睡眠,直到状态
 *   到达 COMPLETED_SHARED / COMPLETED_LOCAL(COMPLETED_IO 说明等待
 *   "提交方"或"收割方"推进,睡眠即可被唤醒);
 * - COMPLETED_SHARED / COMPLETED_LOCAL:完成;若本进程是发起者,顺手
 *   pgaio_io_reclaim() 回收句柄(执行本地回调、写回 PgAioReturn)。
 *
 * 【设计思想】
 * - 发起者自检:等待"自己的" IO 时,若状态还停在 HANDED_OUT 之前,
 *   说明状态机被破坏(该 IO 应当早已定义/提交),PANIC 立即暴露编程
 *   错误,而不是无限等待;
 * - "was_recycled 检查 → 分支动作"之间不允许处理中断:中断可能已经
 *   回收了句柄,继续按旧状态操作会出错(代码多处注明);
 * - 条件变量睡眠前先 PrepareToSleep,醒来统一 CancelSleep,避免丢失
 *   唤醒。
 *
 * 【参数】ioh —— 共享内存句柄;ref_generation —— 期望代数(判复用)。
 * 【返回值】无。返回时该 IO 已完成(结果可经回调/返回值渠道获取)或
 * 句柄已被复用。
 */
static void
pgaio_io_wait(PgAioHandle *ioh, uint64 ref_generation)
{
	PgAioHandleState state;
	bool		am_owner;

	am_owner = ioh->owner_procno == MyProcNumber;

	if (pgaio_io_was_recycled(ioh, ref_generation, &state))
		return;

	if (am_owner)
	{
		if (state != PGAIO_HS_SUBMITTED
			&& state != PGAIO_HS_COMPLETED_IO
			&& state != PGAIO_HS_COMPLETED_SHARED
			&& state != PGAIO_HS_COMPLETED_LOCAL)
		{
			elog(PANIC, "waiting for own IO %d in wrong state: %s",
				 pgaio_io_get_id(ioh), pgaio_io_get_state_name(ioh));
		}
	}

	while (true)
	{
		if (pgaio_io_was_recycled(ioh, ref_generation, &state))
			return;

		switch (state)
		{
			case PGAIO_HS_IDLE:
			case PGAIO_HS_HANDED_OUT:
				elog(ERROR, "IO in wrong state: %d", state);
				break;

			case PGAIO_HS_SUBMITTED:

				/*
				 * If we need to wait via the IO method, do so now. Don't
				 * check via the IO method if the issuing backend is executing
				 * the IO synchronously.
				 */
				if (pgaio_method_ops->wait_one && !(ioh->flags & PGAIO_HF_SYNCHRONOUS))
				{
					pgaio_method_ops->wait_one(ioh, ref_generation);
					continue;
				}
				pg_fallthrough;

				/* waiting for owner to submit */
			case PGAIO_HS_DEFINED:
			case PGAIO_HS_STAGED:
				/* waiting for reaper to complete */
				/* fallthrough */
			case PGAIO_HS_COMPLETED_IO:
				/* shouldn't be able to hit this otherwise */
				Assert(IsUnderPostmaster);
				/* ensure we're going to get woken up */
				ConditionVariablePrepareToSleep(&ioh->cv);

				while (!pgaio_io_was_recycled(ioh, ref_generation, &state))
				{
					if (state == PGAIO_HS_COMPLETED_SHARED ||
						state == PGAIO_HS_COMPLETED_LOCAL)
						break;
					ConditionVariableSleep(&ioh->cv, WAIT_EVENT_AIO_IO_COMPLETION);
				}

				ConditionVariableCancelSleep();
				break;

			case PGAIO_HS_COMPLETED_SHARED:
			case PGAIO_HS_COMPLETED_LOCAL:

				/*
				 * Note that no interrupts are processed between
				 * pgaio_io_was_recycled() and this check - that's important
				 * as otherwise an interrupt could have already reclaimed the
				 * handle.
				 */
				if (am_owner)
					pgaio_io_reclaim(ioh);
				return;
		}
	}
}

/*
 * Make IO handle ready to be reused after IO has completed or after the
 * handle has been released without being used.
 *
 * Note that callers need to be careful about only calling this in the right
 * state and that no interrupts can be processed between the state check and
 * the call to pgaio_io_reclaim(). Otherwise interrupt processing could
 * already have reclaimed the handle.
 */
/*
 * pgaio_io_reclaim - (中文)回收句柄:执行本地回调、写回结果、恢复 IDLE 状态
 *
 * 【作用】句柄"生命周期终点":只允许句柄所属后端调用。按顺序完成:
 * 1. 若状态为 COMPLETED_SHARED(共享回调已完成、本地回调未跑),先运行
 *    本地完成回调链(pgaio_io_call_complete_local),状态 →
 *    COMPLETED_LOCAL,并把蒸馏结果与 target_data 写入 report_return
 *    (发起者经 pgaio_wref_wait() 后即可读到成败);
 * 2. 若句柄已定义过(非 HANDED_OUT),从 in_flight_ios 链表摘下;
 * 3. 解除 resowner 登记;
 * 4. 代数 generation++(标识一次新生命周期),状态 → IDLE,写屏障后再
 *    清零全部字段(op/target/flags/callbacks/result 等),确保并发观察者
 *    不会把"正在被清空的旧字段"误当有效数据;
 * 5. 挂回空闲链表头部(最近释放的优先复用,缓存更友好)。
 *
 * 【设计思想】本地完成回调的执行点集中在本函数,是因为"执行本地回调 +
 * 回收"总是成对出现,集中一处避免漏跑。状态先置 IDLE 再清字段,配合
 * 屏障,让"等待方"看到 IDLE 即知句柄已可复用、字段不可再读。调用方
 * 必须保证"状态检查"与"调用本函数"之间无中断(否则中断里可能已回收,
 * 造成双重回收),本函数内部也 HOLD_INTERRUPTS() 自保。
 *
 * 【参数】ioh —— 本后端的句柄,状态 ∈ {HANDED_OUT, COMPLETED_SHARED}
 *        (HANDED_OUT 表示"未使用即归还",COMPLETED_SHARED 表示"完成待回收")。
 * 【返回值】无。返回后句柄处于 IDLE,可被再次发放。
 */
static void
pgaio_io_reclaim(PgAioHandle *ioh)
{
	/* This is only ok if it's our IO */
	Assert(ioh->owner_procno == MyProcNumber);
	Assert(ioh->state != PGAIO_HS_IDLE);

	/* see comment in function header */
	HOLD_INTERRUPTS();

	/*
	 * It's a bit ugly, but right now the easiest place to put the execution
	 * of local completion callbacks is this function, as we need to execute
	 * local callbacks just before reclaiming at multiple callsites.
	 */
	if (ioh->state == PGAIO_HS_COMPLETED_SHARED)
	{
		PgAioResult local_result;

		local_result = pgaio_io_call_complete_local(ioh);
		pgaio_io_update_state(ioh, PGAIO_HS_COMPLETED_LOCAL);

		if (ioh->report_return)
		{
			ioh->report_return->result = local_result;
			ioh->report_return->target_data = ioh->target_data;
		}
	}

	pgaio_debug_io(DEBUG4, ioh,
				   "reclaiming: distilled_result: (status %s, id %u, error_data %d), raw_result: %d",
				   pgaio_result_status_string(ioh->distilled_result.status),
				   ioh->distilled_result.id,
				   ioh->distilled_result.error_data,
				   ioh->result);

	/* if the IO has been defined, it's on the in-flight list, remove */
	if (ioh->state != PGAIO_HS_HANDED_OUT)
		dclist_delete_from(&pgaio_my_backend->in_flight_ios, &ioh->node);

	if (ioh->resowner)
	{
		ResourceOwnerForgetAioHandle(ioh->resowner, &ioh->resowner_node);
		ioh->resowner = NULL;
	}

	Assert(!ioh->resowner);

	/*
	 * Update generation & state first, before resetting the IO's fields,
	 * otherwise a concurrent "viewer" could think the fields are valid, even
	 * though they are being reset.  Increment the generation first, so that
	 * we can assert elsewhere that we never wait for an IDLE IO.  While it's
	 * a bit weird for the state to go backwards for a generation, it's OK
	 * here, as there cannot be references to the "reborn" IO yet.  Can't
	 * update both at once, so something has to give.
	 */
	ioh->generation++;
	pgaio_io_update_state(ioh, PGAIO_HS_IDLE);

	/* ensure the state update is visible before we reset fields */
	pg_write_barrier();

	ioh->op = PGAIO_OP_INVALID;
	ioh->target = PGAIO_TID_INVALID;
	ioh->flags = 0;
	ioh->num_callbacks = 0;
	ioh->handle_data_len = 0;
	ioh->report_return = NULL;
	ioh->result = 0;
	ioh->distilled_result.status = PGAIO_RS_UNKNOWN;

	/*
	 * We push the IO to the head of the idle IO list, that seems more cache
	 * efficient in cases where only a few IOs are used.
	 */
	dclist_push_head(&pgaio_my_backend->idle_ios, &ioh->node);

	RESUME_INTERRUPTS();
}

/*
 * Wait for an IO handle to become usable.
 *
 * This only really is useful for pgaio_io_acquire().
 */
/*
 * pgaio_io_wait_for_free - (中文)等待本后端至少有一个空闲句柄可用
 *
 * 【作用】pgaio_io_acquire() 发现句柄池耗尽时的兜底逻辑,按代价从低到高:
 * 1. 先扫描本后端全部 io_max_concurrency 个句柄,回收处于
 *    COMPLETED_SHARED 的(worker 模式下这种"已完成待回收"很常见);
 * 2. 还有未提交的 staged IO?先提交(马上要开始等待了,让它们在途,
 *    也消除"全部 IO 都未提交"导致无人推进的边角情形);
 * 3. 提交期间可能已有 IO 完成,再查空闲链表;
 * 4. 一个在途 IO 都没有却仍无空闲句柄 → 状态机损坏,报错;
 * 5. 否则等待"最老的 in-flight IO"完成(pgaio_io_wait 或直接回收),
 *    等待一个 IO 完成可能连带多个完成,结束后必有空闲句柄。
 *
 * 【设计思想】"先回收后等待"顺序可避免不必要的等待;等待最老 IO 而非
 * 任意 IO 是次优解(注释里 XXX 承认)——本意只是"腾出一个空闲句柄"。
 * 各"读状态 → 回收"处都必须保证不跨中断点(见各注释),避免回收
 * 已被并发回收的句柄。
 *
 * 【参数】无。
 * 【返回值】无。返回后保证空闲链表非空(否则 PANIC/ERROR)。
 */
static void
pgaio_io_wait_for_free(void)
{
	int			reclaimed = 0;

	pgaio_debug(DEBUG2, "waiting for free IO with %d pending, %u in-flight, %u idle IOs",
				pgaio_my_backend->num_staged_ios,
				dclist_count(&pgaio_my_backend->in_flight_ios),
				dclist_count(&pgaio_my_backend->idle_ios));

	/*
	 * First check if any of our IOs actually have completed - when using
	 * worker, that'll often be the case. We could do so as part of the loop
	 * below, but that'd potentially lead us to wait for some IO submitted
	 * before.
	 */
	for (int i = 0; i < io_max_concurrency; i++)
	{
		PgAioHandle *ioh = &pgaio_ctl->io_handles[pgaio_my_backend->io_handle_off + i];

		if (ioh->state == PGAIO_HS_COMPLETED_SHARED)
		{
			/*
			 * Note that no interrupts are processed between the state check
			 * and the call to reclaim - that's important as otherwise an
			 * interrupt could have already reclaimed the handle.
			 *
			 * Need to ensure that there's no reordering, in the more common
			 * paths, where we wait for IO, that's done by
			 * pgaio_io_was_recycled().
			 */
			pg_read_barrier();
			pgaio_io_reclaim(ioh);
			reclaimed++;
		}
	}

	if (reclaimed > 0)
		return;

	/*
	 * If we have any unsubmitted IOs, submit them now. We'll start waiting in
	 * a second, so it's better they're in flight. This also addresses the
	 * edge-case that all IOs are unsubmitted.
	 */
	if (pgaio_my_backend->num_staged_ios > 0)
		pgaio_submit_staged();

	/* possibly some IOs finished during submission */
	if (!dclist_is_empty(&pgaio_my_backend->idle_ios))
		return;

	if (dclist_count(&pgaio_my_backend->in_flight_ios) == 0)
		ereport(ERROR,
				errmsg_internal("no free IOs despite no in-flight IOs"),
				errdetail_internal("%d pending, %u in-flight, %u idle IOs",
								   pgaio_my_backend->num_staged_ios,
								   dclist_count(&pgaio_my_backend->in_flight_ios),
								   dclist_count(&pgaio_my_backend->idle_ios)));

	/*
	 * Wait for the oldest in-flight IO to complete.
	 *
	 * XXX: Reusing the general IO wait is suboptimal, we don't need to wait
	 * for that specific IO to complete, we just need *any* IO to complete.
	 */
	{
		PgAioHandle *ioh = dclist_head_element(PgAioHandle, node,
											   &pgaio_my_backend->in_flight_ios);
		uint64		generation = ioh->generation;

		switch ((PgAioHandleState) ioh->state)
		{
				/* should not be in in-flight list */
			case PGAIO_HS_IDLE:
			case PGAIO_HS_DEFINED:
			case PGAIO_HS_HANDED_OUT:
			case PGAIO_HS_STAGED:
			case PGAIO_HS_COMPLETED_LOCAL:
				elog(ERROR, "shouldn't get here with io:%d in state %d",
					 pgaio_io_get_id(ioh), ioh->state);
				break;

			case PGAIO_HS_COMPLETED_IO:
			case PGAIO_HS_SUBMITTED:
				pgaio_debug_io(DEBUG2, ioh,
							   "waiting for free io with %u in flight",
							   dclist_count(&pgaio_my_backend->in_flight_ios));

				/*
				 * In a more general case this would be racy, because the
				 * generation could increase after we read ioh->state above.
				 * But we are only looking at IOs by the current backend and
				 * the IO can only be recycled by this backend.  Even this is
				 * only OK because we get the handle's generation before
				 * potentially processing interrupts, e.g. as part of
				 * pgaio_debug_io().
				 */
				pgaio_io_wait(ioh, generation);
				break;

			case PGAIO_HS_COMPLETED_SHARED:

				/*
				 * It's possible that another backend just finished this IO.
				 *
				 * Note that no interrupts are processed between the state
				 * check and the call to reclaim - that's important as
				 * otherwise an interrupt could have already reclaimed the
				 * handle.
				 *
				 * Need to ensure that there's no reordering, in the more
				 * common paths, where we wait for IO, that's done by
				 * pgaio_io_was_recycled().
				 */
				pg_read_barrier();
				pgaio_io_reclaim(ioh);
				break;
		}

		if (dclist_count(&pgaio_my_backend->idle_ios) == 0)
			elog(PANIC, "no idle IO after waiting for IO to terminate");
		return;
	}
}

/*
 * Internal - code outside of AIO should never need this and it'd be hard for
 * such code to be safe.
 */
/*
 * pgaio_io_from_wref - (中文)从等待引用还原句柄指针与期望代数
 *
 * 【作用】把 PgAioWaitRef(句柄池下标 + 高/低 32 位代数)解包为
 * "共享内存句柄指针 + 拼装好的 64 位代数"。pgaio_wref_wait() /
 * pgaio_wref_check_done() 的公共前置步骤。
 *
 * 【设计思想】等待引用本质是"跨进程可传递的句柄快照":句柄池下标恒定
 * (每后端静态划分),代数在句柄每次回收时递增,二者组合足以唯一标识
 * "一次" IO 生命周期。
 *
 * 【参数】iow —— 等待引用;aio_index 必须小于句柄总数(Assert 校验);
 *        ref_generation —— 输出参数,拼装后的 64 位代数(保证非 0,
 *        因为句柄首次发放前代数已被 +1)。
 * 【返回值】对应的共享内存句柄指针。
 */
static PgAioHandle *
pgaio_io_from_wref(PgAioWaitRef *iow, uint64 *ref_generation)
{
	PgAioHandle *ioh;

	Assert(iow->aio_index < pgaio_ctl->io_handle_count);

	ioh = &pgaio_ctl->io_handles[iow->aio_index];

	*ref_generation = ((uint64) iow->generation_upper) << 32 |
		iow->generation_lower;

	Assert(*ref_generation != 0);

	return ioh;
}

/*
 * pgaio_io_state_get_name - (中文)句柄状态枚举 → 字符串(调试日志用)
 *
 * 【作用】把 PgAioHandleState 值翻译成宏名文本(IDLE/HANDED_OUT/...)。
 * 供 pgaio_io_update_state 的日志与 pgaio_io_get_state_name 使用。
 *
 * 【参数】s —— 状态枚举值。
 * 【返回值】状态名常量字符串;未知值返回 NULL(仅静态分析时可达)。
 */
static const char *
pgaio_io_state_get_name(PgAioHandleState s)
{
#define PGAIO_HS_TOSTR_CASE(sym) case PGAIO_HS_##sym: return #sym
	switch (s)
	{
			PGAIO_HS_TOSTR_CASE(IDLE);
			PGAIO_HS_TOSTR_CASE(HANDED_OUT);
			PGAIO_HS_TOSTR_CASE(DEFINED);
			PGAIO_HS_TOSTR_CASE(STAGED);
			PGAIO_HS_TOSTR_CASE(SUBMITTED);
			PGAIO_HS_TOSTR_CASE(COMPLETED_IO);
			PGAIO_HS_TOSTR_CASE(COMPLETED_SHARED);
			PGAIO_HS_TOSTR_CASE(COMPLETED_LOCAL);
	}
#undef PGAIO_HS_TOSTR_CASE

	return NULL;				/* silence compiler */
}

/*
 * pgaio_io_get_state_name - (中文)返回指定句柄当前状态的字符串表示
 *
 * 【作用】对外暴露的调试接口:包装内部 pgaio_io_state_get_name,供日志、
 * 错误消息与可能的 SQL 视图使用。
 *
 * 【参数】ioh —— 目标句柄。
 * 【返回值】状态名(如 "SUBMITTED")。
 */
const char *
pgaio_io_get_state_name(PgAioHandle *ioh)
{
	return pgaio_io_state_get_name(ioh->state);
}

/*
 * pgaio_result_status_string - (中文)IO 结果状态枚举 → 字符串
 *
 * 【作用】把 PgAioResultStatus(UNKNOWN/OK/WARNING/PARTIAL/ERROR)翻译成
 * 大写文本,供 pgaio_debug_io 等日志输出与 pgaio_funcs.c 的 SQL 视图使用。
 *
 * 【参数】rs —— 结果状态枚举值。
 * 【返回值】状态名常量字符串;未知值返回 NULL(静态分析兜底)。
 */
const char *
pgaio_result_status_string(PgAioResultStatus rs)
{
	switch (rs)
	{
		case PGAIO_RS_UNKNOWN:
			return "UNKNOWN";
		case PGAIO_RS_OK:
			return "OK";
		case PGAIO_RS_WARNING:
			return "WARNING";
		case PGAIO_RS_PARTIAL:
			return "PARTIAL";
		case PGAIO_RS_ERROR:
			return "ERROR";
	}

	return NULL;				/* silence compiler */
}



/* --------------------------------------------------------------------------------
 * Functions primarily related to IO Wait References
 * --------------------------------------------------------------------------------
 */

/*
 * Mark a wait reference as invalid
 */
/*
 * pgaio_wref_clear - (中文)把等待引用标记为无效
 *
 * 【作用】把 aio_index 置为 PG_UINT32_MAX 这一哨兵值,使
 * pgaio_wref_valid() 返回 false。用于"用后即弃"的等待引用——例如
 * 函数返回前确认某个 IO 已不需要再等待,主动作废引用,避免误用。
 *
 * 【参数】iow —— 要作废的等待引用。
 * 【返回值】无。
 */
void
pgaio_wref_clear(PgAioWaitRef *iow)
{
	iow->aio_index = PG_UINT32_MAX;
}

/*
 * pgaio_wref_valid - (中文)判断等待引用是否有效
 *
 * 【作用】通过 aio_index 是否为哨兵值 PG_UINT32_MAX 判断引用是否被
 * pgaio_wref_clear() 作废过(注意:有效 ≠ 对应 IO 已完成,只表示
 * "引用还活着")。
 *
 * 【参数】iow —— 待检查的等待引用。
 * 【返回值】true = 有效;false = 已被作废。
 */
bool
pgaio_wref_valid(PgAioWaitRef *iow)
{
	return iow->aio_index != PG_UINT32_MAX;
}

/*
 * pgaio_wref_get_id - (中文)返回等待引用对应的句柄编号
 *
 * 【作用】pgaio_io_get_id() 的"等待引用版":直接返回引用里的句柄池
 * 下标。仅用于日志与调试。调用者必须先确认引用有效(Assert)。
 *
 * 【参数】iow —— 有效等待引用。
 * 【返回值】句柄编号(0 基)。
 */
int
pgaio_wref_get_id(PgAioWaitRef *iow)
{
	Assert(pgaio_wref_valid(iow));
	return iow->aio_index;
}

/*
 * Wait for the IO to have completed. Can be called in any process, not just
 * in the issuing backend.
 */
/*
 * pgaio_wref_wait - (中文)等待引用的 IO 完成(可在任意进程调用)
 *
 * 【作用】对外等待接口:从引用还原句柄与期望代数后调用内部
 * pgaio_io_wait(),一直阻塞到该 IO 完成(或被复用,等价于完成)。
 * 允许在发起者之外的进程调用——例如并行 worker 等待另一个进程发起的
 * 预读完成。返回后,若本进程是发起者,句柄已被回收,调用者持有的
 * PgAioReturn(acquire 时传入的)已填入结果,可据此判断成败。
 *
 * 【参数】iow —— 指向 IO 的等待引用(必须有效)。
 * 【返回值】无。
 */
void
pgaio_wref_wait(PgAioWaitRef *iow)
{
	uint64		ref_generation;
	PgAioHandle *ioh;

	ioh = pgaio_io_from_wref(iow, &ref_generation);

	pgaio_io_wait(ioh, ref_generation);
}

/*
 * Check if the referenced IO completed, without blocking.
 */
/*
 * pgaio_wref_check_done - (中文)非阻塞地检查引用的 IO 是否已完成
 *
 * 【作用】轮询式检查,绝不阻塞,判定顺序:
 * 1. 句柄已被复用(recycled)→ 目标 IO 必然已结束,返回 true;
 * 2. 状态是 IDLE → 句柄空闲,也视为已完成,返回 true;
 * 3. 方法提供 check_one(如 io_uring 需要主动看一眼内核完成队列)且 IO
 *    非同步执行 → 调用 check_one 收割已完成的 CQE(不等待),之后复查;
 * 4. 状态 ∈ {COMPLETED_SHARED, COMPLETED_LOCAL} → 完成;若本进程是
 *    发起者,顺手 pgaio_io_reclaim() 回收句柄,返回 true;
 * 5. 其余状态(还在跑/还没提交)→ 返回 false。
 *
 * 【设计思想】与 pgaio_wref_wait() 的区别只在"不阻塞":等待方可以借此
 * 搭进自己的事件循环(例如与 latch 一起轮询)。check_one 是可选钩子,
 * 无此钩子的方法(worker/sync)靠状态字段本身即可判断。
 *
 * 【参数】iow —— 指向 IO 的等待引用(必须有效)。
 * 【返回值】true = IO 已完成(或句柄已被复用);false = 尚未完成,稍后
 * 可再次检查或改用 pgaio_wref_wait() 阻塞等待。
 */
bool
pgaio_wref_check_done(PgAioWaitRef *iow)
{
	uint64		ref_generation;
	PgAioHandleState state;
	bool		am_owner;
	PgAioHandle *ioh;

	ioh = pgaio_io_from_wref(iow, &ref_generation);

	if (pgaio_io_was_recycled(ioh, ref_generation, &state))
		return true;

	if (state == PGAIO_HS_IDLE)
		return true;

	am_owner = ioh->owner_procno == MyProcNumber;

	/*
	 * If the IO is not executing synchronously, allow the IO method to check
	 * if the IO already has completed.
	 */
	if (pgaio_method_ops->check_one && !(ioh->flags & PGAIO_HF_SYNCHRONOUS))
	{
		pgaio_method_ops->check_one(ioh, ref_generation);

		if (pgaio_io_was_recycled(ioh, ref_generation, &state))
			return true;

		if (state == PGAIO_HS_IDLE)
			return true;
	}

	if (state == PGAIO_HS_COMPLETED_SHARED ||
		state == PGAIO_HS_COMPLETED_LOCAL)
	{
		/*
		 * Note that no interrupts are processed between
		 * pgaio_io_was_recycled() and this check - that's important as
		 * otherwise an interrupt could have already reclaimed the handle.
		 */
		if (am_owner)
			pgaio_io_reclaim(ioh);
		return true;
	}

	return false;
}



/* --------------------------------------------------------------------------------
 * Actions on multiple IOs.
 * --------------------------------------------------------------------------------
 */

/*
 * Submit IOs in batches going forward.
 *
 * Submitting multiple IOs at once can be substantially faster than doing so
 * one-by-one. At the same time, submitting multiple IOs at once requires more
 * care to avoid deadlocks.
 *
 * Consider backend A staging an IO for buffer 1 and then trying to start IO
 * on buffer 2, while backend B does the inverse. If A submitted the IO before
 * moving on to buffer 2, this works just fine, B will wait for the IO to
 * complete. But if batching were used, each backend will wait for IO that has
 * not yet been submitted to complete, i.e. forever.
 *
 * End batch submission mode with pgaio_exit_batchmode().  (Throwing errors is
 * allowed; error recovery will end the batch.)
 *
 * To avoid deadlocks, code needs to ensure that it will not wait for another
 * backend while there is unsubmitted IO. E.g. by using conditional lock
 * acquisition when acquiring buffer locks. To check if there currently are
 * staged IOs, call pgaio_have_staged() and to submit all staged IOs call
 * pgaio_submit_staged().
 *
 * It is not allowed to enter batchmode while already in batchmode, it's
 * unlikely to ever be needed, as code needs to be explicitly aware of being
 * called in batchmode, to avoid the deadlock risks explained above.
 *
 * Note that IOs may get submitted before pgaio_exit_batchmode() is called,
 * e.g. because too many IOs have been staged or because pgaio_submit_staged()
 * was called.
 */
/*
 * pgaio_enter_batchmode - (中文)进入批处理模式:IO 攒批后统一提交
 *
 * 【作用】置位本后端的 in_batchmode。此后 pgaio_io_stage() 只把句柄放
 * 进 staged 数组、不立即提交,直到 pgaio_exit_batchmode()(或攒满
 * PGAIO_SUBMIT_BATCH_SIZE、或显式 pgaio_submit_staged())才统一提交。
 * 批量提交(尤其 io_uring 的 SQE 批量入队)比逐条提交快得多。
 *
 * 【设计思想】批量提交带来了死锁风险,必须遵守纪律:只要存在未提交的
 * staged IO,就不能阻塞等待其他后端(否则对方可能正在等我们的 IO 完成,
 * 双方互等)。因此:
 * - 批处理期间获取缓冲区锁等可能阻塞的锁时,应使用"条件获取"变体;
 * - 在将要等待其他后端之前,应调用 pgaio_have_staged() 检查、必要时
 *   pgaio_submit_staged() 提交;
 * - 不允许嵌套进入批处理模式(代码需要显式感知自己是否在批内,嵌套
 *   语义说不清,报错);
 * - 错误恢复会自动退出批模式(pgaio_error_cleanup 兜底)。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
pgaio_enter_batchmode(void)
{
	if (pgaio_my_backend->in_batchmode)
		elog(ERROR, "starting batch while batch already in progress");
	pgaio_my_backend->in_batchmode = true;
}

/*
 * Stop submitting IOs in batches.
 */
/*
 * pgaio_exit_batchmode - (中文)退出批处理模式:提交剩余 IO
 *
 * 【作用】pgaio_enter_batchmode() 的配对操作:先把批内所有 staged 未提交
 * 的 IO 一次性提交(pgaio_submit_staged()),再清除 in_batchmode。此后
 * 新 IO 恢复"随 stage 随提交"。
 *
 * 【设计思想】"先提交再清标志"的顺序是必要的:批内攒下的 IO 不提交,
 * 其他后端等不到它们完成可能死锁;提交必须在退出标志之前完成。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
pgaio_exit_batchmode(void)
{
	Assert(pgaio_my_backend->in_batchmode);

	pgaio_submit_staged();
	pgaio_my_backend->in_batchmode = false;
}

/*
 * pgaio_have_staged - (中文)是否存在已定义未提交的 IO
 *
 * 【作用】供批处理模式下的代码在"即将等待其他后端/持锁阻塞"之前自查:
 * 返回本后端 staged 数组中是否还有未提交的 IO(若有,应先提交再等,
 * 否则有死锁风险,见 pgaio_enter_batchmode 注释)。
 *
 * 【设计思想】Assert 同时保证:不在批处理模式下时,num_staged_ios 必为
 * 0(非批模式随 stage 随提交),因此本函数在批模式外恒为 false。
 *
 * 【参数】无。
 * 【返回值】true = 存在未提交的 staged IO,请先 pgaio_submit_staged()。
 */
bool
pgaio_have_staged(void)
{
	Assert(pgaio_my_backend->in_batchmode ||
		   pgaio_my_backend->num_staged_ios == 0);
	return pgaio_my_backend->num_staged_ios > 0;
}

/*
 * Submit all staged but not yet submitted IOs.
 *
 * Unless in batch mode, this never needs to be called, as IOs get submitted
 * as soon as possible. While in batchmode pgaio_submit_staged() can be called
 * before waiting on another backend, to avoid the risk of deadlocks. See
 * pgaio_enter_batchmode().
 */
/*
 * pgaio_submit_staged - (中文)把本后端所有 staged 未提交的 IO 批量提交
 *
 * 【作用】把 staged_ios 数组里的全部句柄交给当前 IO 方法的 submit 回调
 * (方法负责把 iovec/目标信息翻译成内核调用:io_uring 入队 SQE、worker
 * 投递任务、sync 直接执行),然后清空 staged 计数。调用时机:
 * - 非批处理模式:pgaio_io_stage() 内部每 stage 一个就调用一次;
 * - 批处理模式:exit_batchmode、或要在等待别人之前主动冲刷、或 error
 *   清理时调用。
 *
 * 【设计思想】整个提交过程包在临界区(START/END_CRIT_SECTION)里:方法
 * 的 submit 回调可能触发 IO 完成(进而运行完成回调链),而完成回调
 * 要求运行在临界区内;同时批内后续 IO 的提交也可能因"完成钩子"报错,
 * 临界区保证这里不会抛错中断提交流程。方法回调的返回值是被实际接收
 * 的 IO 个数(应为全部)。
 *
 * 【参数】无。
 * 【返回值】无。返回后 num_staged_ios == 0(全部移交或已执行)。
 */
void
pgaio_submit_staged(void)
{
	int			total_submitted = 0;
	int			did_submit;

	if (pgaio_my_backend->num_staged_ios == 0)
		return;


	START_CRIT_SECTION();

	did_submit = pgaio_method_ops->submit(pgaio_my_backend->num_staged_ios,
										  pgaio_my_backend->staged_ios);

	END_CRIT_SECTION();

	total_submitted += did_submit;

	Assert(total_submitted == did_submit);

	pgaio_my_backend->num_staged_ios = 0;

	pgaio_debug(DEBUG4,
				"aio: submitted %d IOs",
				total_submitted);
}



/* --------------------------------------------------------------------------------
 * Other
 * --------------------------------------------------------------------------------
 */


/*
 * Perform AIO related cleanup after an error.
 *
 * This should be called early in the error recovery paths, as later steps may
 * need to issue AIO (e.g. to record a transaction abort WAL record).
 */
/*
 * pgaio_error_cleanup - (中文)出错恢复路径上的 AIO 清理
 *
 * 【作用】必须在错误恢复流程早期调用(后续步骤可能还要发起 AIO,例如
 * 记录事务中止的 WAL 记录):若错误发生时尚处于批处理模式(enter 之后
 * 没来得及 exit),立即退出批模式并提交全部 staged IO——不能把这些 IO
 * 丢弃,其他后端可能正等着它们完成。
 *
 * 【设计思想】错误路径上无法保证"enter/exit 成对",本函数作为兜底把
 * 系统恢复到"无批模式、无未提交 IO"的稳定基态;清理完成后用 Assert
 * 确认已无未提交 IO。调用方(如 xact.c 的 AbortTransaction 路径)保证
 * 在"还可能使用 AIO 的步骤"之前调用它。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
pgaio_error_cleanup(void)
{
	/*
	 * It is possible that code errored out after pgaio_enter_batchmode() but
	 * before pgaio_exit_batchmode() was called. In that case we need to
	 * submit the IO now.
	 */
	if (pgaio_my_backend->in_batchmode)
	{
		pgaio_my_backend->in_batchmode = false;

		pgaio_submit_staged();
	}

	/*
	 * As we aren't in batchmode, there shouldn't be any unsubmitted IOs.
	 */
	Assert(pgaio_my_backend->num_staged_ios == 0);
}

/*
 * Perform AIO related checks at (sub-)transactional boundaries.
 *
 * This should be called late during (sub-)transactional commit/abort, after
 * all steps that might need to perform AIO, so that we can verify that the
 * AIO subsystem is in a valid state at the end of a transaction.
 */
/*
 * AtEOXact_Aio - (中文)(子)事务边界上的 AIO 状态校验
 *
 * 【作用】在(子)事务提交/中止流程的晚期、所有可能发起 AIO 的步骤都
 * 完成之后调用,校验 AIO 子系统处于合法基态:
 * - 不应仍处于批处理模式(若出错且未清理,应由 pgaio_error_cleanup
 *   早前处理过);万一仍在批模式,则提交全部 staged IO 并告警——残留
 *   未提交 IO 会阻塞其他等待它的后端;
 * - 确认没有未提交的 staged IO。
 *
 * 【设计思想】事务边界是"检查子系统一致性"的理想锚点:批模式与 staged
 * IO 都要求在同一事务内闭环,遗留到事务边界即是编程错误的信号。注意
 * 本函数不等待在途 IO(它们可以在事务结束后继续跑,由句柄的资源
 * 所有者管理;错误路径下 resowner 会兜底回收)。
 *
 * 【参数】is_commit —— 是否为提交(仅用于日志语义;清理逻辑相同)。
 * 【返回值】无。
 */
void
AtEOXact_Aio(bool is_commit)
{
	/*
	 * We should never be in batch mode at transactional boundaries. In case
	 * an error was thrown while in batch mode, pgaio_error_cleanup() should
	 * have exited batchmode.
	 *
	 * In case we are in batchmode somehow, make sure to submit all staged
	 * IOs, other backends may need them to complete to continue.
	 */
	if (pgaio_my_backend->in_batchmode)
	{
		pgaio_error_cleanup();
		elog(WARNING, "open AIO batch at end of (sub-)transaction");
	}

	/*
	 * As we aren't in batchmode, there shouldn't be any unsubmitted IOs.
	 */
	Assert(pgaio_my_backend->num_staged_ios == 0);
}

/*
 * Need to submit staged but not yet submitted IOs using the fd, otherwise
 * the IO would end up targeting something bogus.
 */
/*
 * pgaio_closing_fd - (中文)文件描述符关闭前的 AIO 配合处理
 *
 * 【作用】在 fd.c 关闭一个文件描述符之前由调用方(FileClose 等)调用:
 * 1. 若存在 staged 未提交的 IO(它们都引用这个即将关闭的 fd),先全部
 *    提交——否则这些 IO 将来提交时 fd 已失效,会指向错乱的目标;
 *    当前实现"一刀切"提交全部 staged IO(可做得更精准,但注释认为
 *    不值得为此增加复杂度);
 * 2. 若当前 IO 方法要求"关闭前等待引用该 fd 的 IO 全部完成"
 *    (wait_on_fd_before_close,如 worker 方法需要在进程退出前收尾),
 *    则反复扫描 in_flight 链表,找到使用该 fd 的 IO 并等待它完成;
 *    等待一个 IO 可能连带完成多个,且链表在等待期间会变化,所以每次
 *    等待后重头再扫。
 *
 * 【设计思想】本函数既处理"未提交"也处理"在途"两种滞留状态,保证
 * 关闭 fd 后不再有任何引用它的 AIO 活动;在 AIO 尚未初始化或本进程
 * 不使用 AIO 的子进程里安全跳过(pgaio_my_backend == NULL 直接返回)。
 *
 * 【参数】fd —— 即将被关闭的文件描述符。
 * 【返回值】无。
 */
void
pgaio_closing_fd(int fd)
{
	/*
	 * Might be called before AIO is initialized or in a subprocess that
	 * doesn't use AIO.
	 */
	if (!pgaio_my_backend)
		return;

	/*
	 * For now just submit all staged IOs - we could be more selective, but
	 * it's probably not worth it.
	 */
	if (pgaio_my_backend->num_staged_ios > 0)
	{
		pgaio_debug(DEBUG2,
					"submitting %d IOs before FD %d gets closed",
					pgaio_my_backend->num_staged_ios, fd);
		pgaio_submit_staged();
	}

	/*
	 * If requested by the IO method, wait for all IOs that use the
	 * to-be-closed FD.
	 */
	if (pgaio_method_ops->wait_on_fd_before_close)
	{
		/*
		 * As waiting for one IO to complete may complete multiple IOs, we
		 * can't just use a mutable list iterator. The maximum number of
		 * in-flight IOs is fairly small, so just restart the loop after
		 * waiting for an IO.
		 */
		while (!dclist_is_empty(&pgaio_my_backend->in_flight_ios))
		{
			dlist_iter	iter;
			PgAioHandle *ioh = NULL;
			uint64		generation;

			dclist_foreach(iter, &pgaio_my_backend->in_flight_ios)
			{
				ioh = dclist_container(PgAioHandle, node, iter.cur);

				generation = ioh->generation;

				if (pgaio_io_uses_fd(ioh, fd))
					break;
				else
					ioh = NULL;
			}

			if (!ioh)
				break;

			pgaio_debug_io(DEBUG2, ioh,
						   "waiting for IO before FD %d gets closed, %u in-flight IOs",
						   fd, dclist_count(&pgaio_my_backend->in_flight_ios));

			/* see comment in pgaio_io_wait_for_free() about raciness */
			pgaio_io_wait(ioh, generation);
		}
	}
}

/*
 * Registered as before_shmem_exit() callback in pgaio_init_backend()
 */
/*
 * pgaio_shutdown - (中文)后端进程退出前的 AIO 收尾
 *
 * 【作用】以 before_shmem_exit() 回调的形式在进程退出时执行:
 * 1. 先按事务边界语义清理(AtEOXact_Aio,处理可能残留的批模式);
 * 2. 等待全部 in-flight IO 完成(反复取链表头等待,原因同
 *    pgaio_closing_fd)。目的有二:
 *    - 部分内核级 AIO 机制(如 io_uring)对"发起者先于 IO 完成退出"
 *      的处理不友好,可能丢完成事件;
 *    - 避免统计视图里残留"半截" IO,便于排查。
 * 3. 把 pgaio_my_backend 置 NULL,标志本进程 AIO 已退役。
 *
 * 【参数】code —— 进程退出码(传给 AtEOXact_Aio 判断是否正常退出);
 *        arg  —— 未使用。
 * 【返回值】无。
 */
void
pgaio_shutdown(int code, Datum arg)
{
	Assert(pgaio_my_backend);
	Assert(!pgaio_my_backend->handed_out_io);

	/* first clean up resources as we would at a transaction boundary */
	AtEOXact_Aio(code == 0);

	/*
	 * Before exiting, make sure that all IOs are finished. That has two main
	 * purposes:
	 *
	 * - Some kernel-level AIO mechanisms don't deal well with the issuer of
	 * an AIO exiting before IO completed
	 *
	 * - It'd be confusing to see partially finished IOs in stats views etc
	 */
	while (!dclist_is_empty(&pgaio_my_backend->in_flight_ios))
	{
		PgAioHandle *ioh = dclist_head_element(PgAioHandle, node, &pgaio_my_backend->in_flight_ios);
		uint64		generation = ioh->generation;

		pgaio_debug_io(DEBUG2, ioh,
					   "waiting for IO to complete during shutdown, %u in-flight IOs",
					   dclist_count(&pgaio_my_backend->in_flight_ios));

		/* see comment in pgaio_io_wait_for_free() about raciness */
		pgaio_io_wait(ioh, generation);
	}

	pgaio_my_backend = NULL;
}

/*
 * assign_io_method - (中文)io_method GUC 的赋值钩子:切换 AIO 实现
 *
 * 【作用】每次给 io_method GUC 赋值(含启动时按默认值装载)都会调用:
 * 从 pgaio_method_ops_table 按新值选取对应的 IoMethodOps,存入全局
 * pgaio_method_ops。此后所有方法调用(提交/等待/检查)自动走新实现。
 *
 * 【设计思想】用"数据表 + 指针"而非 switch 散落各处,新增实现只需
 * 在表里加一行。赋值钩子即时生效,便于运行中调试切换(sync 模式也
 * 被用于验证无 AIO 时的正确性)。
 *
 * 【参数】newval —— 新枚举值(IOMETHOD_SYNC/WORKER/IO_URING);
 *        extra  —— 未使用。
 * 【返回值】无。
 */
void
assign_io_method(int newval, void *extra)
{
	Assert(newval < lengthof(pgaio_method_ops_table));
	Assert(pgaio_method_ops_table[newval] != NULL);

	pgaio_method_ops = pgaio_method_ops_table[newval];
}

/*
 * check_io_max_concurrency - (中文)io_max_concurrency GUC 的校验钩子
 *
 * 【作用】GUC 赋值前校验:允许 -1(表示"启动时再按系统环境自动整定",
 * 因为整定依赖其他 GUC 的最终值)或任意正整数;0 非法(没有并发度
 * 的 AIO 没有意义),给出明确错误详情。
 *
 * 【参数】newval —— 待赋值(可被修改);extra —— 输出 GUC 附加数据;
 *        source —— 赋值来源(会话/PGC_POSTMASTER 等)。
 * 【返回值】true = 接受该值;false = 拒绝(附错误详情)。
 */
bool
check_io_max_concurrency(int *newval, void **extra, GucSource source)
{
	if (*newval == -1)
	{
		/*
		 * Auto-tuning will be applied later during startup, as auto-tuning
		 * depends on the value of various GUCs.
		 */
		return true;
	}
	else if (*newval == 0)
	{
		GUC_check_errdetail("Only -1 or values bigger than 0 are valid.");
		return false;
	}

	return true;
}
