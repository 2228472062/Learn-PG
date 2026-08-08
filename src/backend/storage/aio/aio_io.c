/*-------------------------------------------------------------------------
 *
 * aio_io.c
 *    AIO - Low Level IO Handling
 *
 * Functions related to associating IO operations to IO Handles and IO-method
 * independent support functions for actually performing IO.
 *
 * 【模块总览(中文)】
 * 本文件是 AIO 子系统的"操作定义层":把一次具体的 I/O 操作(读/写、
 * 哪个文件、偏移多少、哪些缓冲区)绑定到 AIO 句柄上,并提供与具体
 * IO 方法(io_uring / worker / sync)无关的底层执行函数。
 *
 * 主要内容:
 * 1) 句柄信息访问器:pgaio_io_get_iovec() 返回句柄在共享内存 iovec
 *    池中的预留区(调用方直接往里填 iov_base/iov_len);op 与 op_data
 *    的读取接口。
 * 2) 操作启动入口:pgaio_io_start_readv() / pgaio_io_start_writev()。
 *    这是"最低层"的接口,通常由 fd.c 在收到上层(通过 smgr/md 传递
 *    下来的句柄)后调用。统一套路:先 pgaio_io_before_start() 做前置
 *    断言,再填 op_data(文件描述符、偏移、段数),最后
 *    pgaio_io_stage() 把句柄送入提交流程(见 aio.c)。
 * 3) 同步执行兜底:pgaio_io_perform_synchronously() 直接用
 *    pg_preadv/pg_pwritev 执行 IO,并通过标准完成路径
 *    (pgaio_io_process_completion) 处理结果。放在本文件而不是
 *    method_sync.c,是因为 worker 等方法也要用它对"无法异步执行的
 *    IO"(如引用进程本地内存的 IO)做回退——方法无关。
 *
 * 【关键设计思想】
 * - iovec 必须放在共享内存(而非进程本地):worker 模式下真正的
 *   readv/writev 由别的进程执行,只有共享内存中的数据才可见;
 * - 句柄里的 fd 不能长期依赖:跨进程时 fd 无效,需经 target 的
 *   reopen 回调重开(见 aio_target.c);本文件只负责"填好参数";
 * - 同步执行也在临界区内完成(完成回调要求),并通过与异步完全相同的
 *   状态机/回调路径收尾,保证上层代码无须区分同步/异步。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *    src/backend/storage/aio/aio_io.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "miscadmin.h"
#include "storage/aio.h"
#include "storage/aio_internal.h"
#include "storage/fd.h"
#include "utils/wait_event.h"


static void pgaio_io_before_start(PgAioHandle *ioh);



/* --------------------------------------------------------------------------------
 * Public IO related functions operating on IO Handles
 * --------------------------------------------------------------------------------
 */

/*
 * Scatter/gather IO needs to associate an iovec with the Handle. To support
 * worker mode this data needs to be in shared memory.
 */
/*
 * pgaio_io_get_iovec - (中文)获取句柄预留的 iovec 数组写入区
 *
 * 【作用】散聚(向量) I/O 需要一组 iovec(每项 = 一块缓冲区的地址与
 * 长度)。本函数返回共享内存 iovec 池中属于该句柄的那一段,调用方
 * (通常是最底层发起 IO 的 fd.c)直接向其中填写 iov_base/iov_len。
 *
 * 【设计思想】iovec 必须放共享内存:worker 模式下真正的读写由其他
 * 进程执行,进程本地地址对它们无效。每句柄固定预留
 * io_max_combine_limit 个槽(启动时按 GUC 配置),故返回值恒为
 * PG_IOV_MAX(即 io_max_combine_limit 的最大允许值)——调用方填满
 * 剩余槽也没关系,执行时以 op_data 里的 iov_length 为准。
 *
 * 【参数】ioh —— HANDED_OUT 状态的句柄;
 *        iov —— 输出参数,指向共享内存 iovec 池中本句柄的段起点。
 * 【返回值】可用的 iovec 槽位数(PG_IOV_MAX)。
 */
int
pgaio_io_get_iovec(PgAioHandle *ioh, struct iovec **iov)
{
	Assert(ioh->state == PGAIO_HS_HANDED_OUT);

	*iov = &pgaio_ctl->iovecs[ioh->iovec_off];

	return PG_IOV_MAX;
}

/*
 * pgaio_io_get_op - (中文)返回句柄当前绑定的操作类型
 *
 * 【作用】读取句柄的 op 字段(PGAIO_OP_READV / PGAIO_OP_WRITEV 等)。
 * 供调试、SQL 视图与 IO 方法(决定如何执行)使用。
 *
 * 【参数】ioh —— 目标句柄。
 * 【返回值】操作类型枚举值。
 */
PgAioOp
pgaio_io_get_op(PgAioHandle *ioh)
{
	return ioh->op;
}

/*
 * pgaio_io_get_op_data - (中文)返回句柄的操作参数区指针
 *
 * 【作用】返回句柄内 PgAioOpData(fd/偏移/iovec 段数等操作参数)的
 * 指针,供 IO 方法执行时直接使用。
 *
 * 【参数】ioh —— 目标句柄。
 * 【返回值】指向句柄 op_data 字段的指针(生命周期 = 句柄生命周期)。
 */
PgAioOpData *
pgaio_io_get_op_data(PgAioHandle *ioh)
{
	return &ioh->op_data;
}



/* --------------------------------------------------------------------------------
 * "Start" routines for individual IO operations
 *
 * These are called by the code actually initiating an IO, to associate the IO
 * specific data with an AIO handle.
 *
 * Each of the "start" routines first needs to call pgaio_io_before_start(),
 * then fill IO specific fields in the handle and then finally call
 * pgaio_io_stage().
 * --------------------------------------------------------------------------------
 */
/*
 * pgaio_io_start_readv - (中文)把句柄定义为"一次读操作"并送入提交流程
 *
 * 【作用】"发起一次异步读"的最底层入口(通常由 fd.c 在句柄经
 * smgr/md 层层传递后调用):前置检查 → 填入 fd/偏移/段数 → 调用
 * pgaio_io_stage()。此后句柄被"消费",调用方不得再访问。
 *
 * 【设计思想】iov 内容由调用方在之前(获取句柄后)通过
 * pgaio_io_get_iovec() 填入,本函数只记录"段数"作为执行依据。
 * 提交后 IO 可能立即执行完毕(尤其同步回退),因此本函数返回后句柄
 * 可能已被回收。
 *
 * 【参数】
 *   ioh    —— HANDED_OUT 状态、已设置 target 与 iovec 的句柄;
 *   fd     —— 目标文件描述符;
 *   iovcnt —— iovec 段数(即要读几段连续/不连续的缓冲区);
 *   offset —— 文件内的起始偏移(字节)。
 * 【返回值】无。
 */
void
pgaio_io_start_readv(PgAioHandle *ioh,
					 int fd, int iovcnt, uint64 offset)
{
	pgaio_io_before_start(ioh);

	ioh->op_data.read.fd = fd;
	ioh->op_data.read.offset = offset;
	ioh->op_data.read.iov_length = iovcnt;

	pgaio_io_stage(ioh, PGAIO_OP_READV);
}

/*
 * pgaio_io_start_writev - (中文)把句柄定义为"一次写操作"并送入提交流程
 *
 * 【作用】pgaio_io_start_readv() 的写对称版本:填入 fd/偏移/段数后
 * 以 PGAIO_OP_WRITEV 提交。参数与语义完全对应,不再赘述。
 *
 * 【参数】
 *   ioh    —— HANDED_OUT 状态、已设置 target 与 iovec 的句柄;
 *   fd     —— 目标文件描述符;
 *   iovcnt —— iovec 段数;
 *   offset —— 文件内的起始偏移(字节)。
 * 【返回值】无。
 */
void
pgaio_io_start_writev(PgAioHandle *ioh,
					  int fd, int iovcnt, uint64 offset)
{
	pgaio_io_before_start(ioh);

	ioh->op_data.write.fd = fd;
	ioh->op_data.write.offset = offset;
	ioh->op_data.write.iov_length = iovcnt;

	pgaio_io_stage(ioh, PGAIO_OP_WRITEV);
}



/* --------------------------------------------------------------------------------
 * Internal IO related functions operating on IO Handles
 * --------------------------------------------------------------------------------
 */

/*
 * Execute IO operation synchronously. This is implemented here, not in
 * method_sync.c, because other IO methods also might use it / fall back to
 * it.
 */
/*
 * pgaio_io_perform_synchronously - (中文)同步执行句柄上的 IO(方法无关的兜底)
 *
 * 【作用】直接在本进程、用阻塞式系统调用执行句柄定义好的 IO:
 * READV → pg_preadv;WRITEV → pg_pwritev,并用 pgstat 报告等待事件。
 * 系统调用结果统一换算成"负数 = -errno"存进句柄,然后走标准完成
 * 路径 pgaio_io_process_completion()(运行共享/本地回调、唤醒等待者),
 * 与异步 IO 的收尾完全一致。
 *
 * 【设计思想】放在本文件(而非 method_sync.c)是因为它是"方法无关"
 * 的公共设施:
 * - sync 方法用它执行所有 IO(退化为阻塞,但保持同一套接口/状态机,
 *   便于调试);
 * - worker 方法用它执行"无法交给 worker"的 IO(如引用进程本地内存
 *   的 IO,见 PGAIO_HF_REFERENCES_LOCAL);
 * - 调用方(method_sync.c / pgaio_io_stage)必须已执行过
 *   pgaio_io_prepare_submit()(状态 SUBMITTED),本函数只负责"执行 +
 *   收尾"。整体包在临界区内:底层系统调用本身不在临界区语义内报错,
 *   完成回调链要求临界区环境(注意 START_CRIT_SECTION 在本函数内部
 *   再次开启,与调用方是否已开临界区兼容)。
 *
 * 【参数】ioh —— SUBMITTED 状态、已定义好 op 与 op_data 的句柄。
 * 【返回值】无。返回后 IO 已完成(状态至少到 COMPLETED_SHARED;
 * 若本后端是发起者,句柄会被回收)。
 */
void
pgaio_io_perform_synchronously(PgAioHandle *ioh)
{
	ssize_t		result = 0;
	struct iovec *iov = &pgaio_ctl->iovecs[ioh->iovec_off];

	START_CRIT_SECTION();

	/* Perform IO. */
	switch ((PgAioOp) ioh->op)
	{
		case PGAIO_OP_READV:
			pgstat_report_wait_start(WAIT_EVENT_DATA_FILE_READ);
			result = pg_preadv(ioh->op_data.read.fd, iov,
							   ioh->op_data.read.iov_length,
							   ioh->op_data.read.offset);
			pgstat_report_wait_end();
			break;
		case PGAIO_OP_WRITEV:
			pgstat_report_wait_start(WAIT_EVENT_DATA_FILE_WRITE);
			result = pg_pwritev(ioh->op_data.write.fd, iov,
								ioh->op_data.write.iov_length,
								ioh->op_data.write.offset);
			pgstat_report_wait_end();
			break;
		case PGAIO_OP_INVALID:
			elog(ERROR, "trying to execute invalid IO operation");
	}

	/*
	 * ssize_t to int conversion should be ok because result should be no more
	 * than PG_IOV_MAX times BLCKSZ.
	 */
	Assert(result <= INT_MAX);
	ioh->result = result < 0 ? -errno : result;

	pgaio_io_process_completion(ioh, ioh->result);

	END_CRIT_SECTION();
}

/*
 * Helper function to be called by IO operation preparation functions, before
 * any data in the handle is set.  Mostly to centralize assertions.
 */
/*
 * pgaio_io_before_start - (中文)操作启动前的统一前置检查
 *
 * 【作用】pgaio_io_start_*() 系列共用的前置断言集合,集中检查:
 * - 句柄确为 HANDED_OUT 且正是本后端当前"已发放"的那一个(不允许
 *   越权使用其他句柄);
 * - 已设置 target(没有目标对象无法执行 IO);
 * - op 尚未被设置(一个句柄只能定义一次操作);
 * - 当前禁止处理中断(INTERRUPTS_CAN_BE_PROCESSED 为假):否则中断
 *   处理可能顺手关闭句柄引用到的文件描述符,或扰乱状态机。
 *
 * 【参数】ioh —— 准备定义操作的句柄。
 * 【返回值】无(纯检查,失败即 Assert/ERROR)。
 */
static void
pgaio_io_before_start(PgAioHandle *ioh)
{
	Assert(ioh->state == PGAIO_HS_HANDED_OUT);
	Assert(pgaio_my_backend->handed_out_io == ioh);
	Assert(pgaio_io_has_target(ioh));
	Assert(ioh->op == PGAIO_OP_INVALID);

	/*
	 * Otherwise the FDs referenced by the IO could be closed due to interrupt
	 * processing.
	 */
	Assert(!INTERRUPTS_CAN_BE_PROCESSED());
}

/*
 * Could be made part of the public interface, but it's not clear there's
 * really a use case for that.
 */
/*
 * pgaio_io_get_op_name - (中文)操作类型 → 字符串(日志/调试/视图用)
 *
 * 【作用】把句柄的操作类型翻译成小写文本("readv"/"writev"/"invalid"),
 * 用于 pgaio_debug_io 前缀、pg_aios 视图与错误消息。
 *
 * 【参数】ioh —— 目标句柄(op 必须落在合法枚举范围内,Assert 校验)。
 * 【返回值】操作名常量字符串。
 */
const char *
pgaio_io_get_op_name(PgAioHandle *ioh)
{
	Assert(ioh->op >= 0 && ioh->op < PGAIO_OP_COUNT);

	switch ((PgAioOp) ioh->op)
	{
		case PGAIO_OP_INVALID:
			return "invalid";
		case PGAIO_OP_READV:
			return "readv";
		case PGAIO_OP_WRITEV:
			return "writev";
	}

	return NULL;				/* silence compiler */
}

/*
 * Used to determine if an IO needs to be waited upon before the file
 * descriptor can be closed.
 */
/*
 * pgaio_io_uses_fd - (中文)判断句柄引用的操作是否使用指定文件描述符
 *
 * 【作用】供 pgaio_closing_fd() 使用:文件描述符即将关闭时,遍历
 * in-flight 链表,用本函数找出"引用该 fd 的 IO"(已定义及以上状态,
 * Assert 保证),以便在关闭前等待它们完成。op 为 INVALID 或 fd 不匹配
 * 返回 false。
 *
 * 【参数】ioh —— 目标句柄(状态 ≥ DEFINED);fd —— 待比对的文件描述符。
 * 【返回值】true = 该 IO 将使用此 fd;false = 不相关。
 */
bool
pgaio_io_uses_fd(PgAioHandle *ioh, int fd)
{
	Assert(ioh->state >= PGAIO_HS_DEFINED);

	switch ((PgAioOp) ioh->op)
	{
		case PGAIO_OP_READV:
			return ioh->op_data.read.fd == fd;
		case PGAIO_OP_WRITEV:
			return ioh->op_data.write.fd == fd;
		case PGAIO_OP_INVALID:
			return false;
	}

	return false;				/* silence compiler */
}

/*
 * Return the iovec and its length. Currently only expected to be used by
 * debugging infrastructure
 */
/*
 * pgaio_io_get_iovec_length - (中文)返回句柄的 iovec 指针与有效段数
 *
 * 【作用】调试基础设施(pgaio_debug_io 输出完整 iovec 列表等)使用:
 * 返回共享内存 iovec 池中该句柄段起点,以及 op_data 里记录的有效
 * 段数(区别于 pgaio_io_get_iovec() 返回的"容量上限")。
 *
 * 【参数】ioh —— 目标句柄(状态 ≥ DEFINED);iov —— 输出参数,iovec
 *        段起点。
 * 【返回值】有效段数(调用者按此遍历 *iov)。
 */
int
pgaio_io_get_iovec_length(PgAioHandle *ioh, struct iovec **iov)
{
	Assert(ioh->state >= PGAIO_HS_DEFINED);

	*iov = &pgaio_ctl->iovecs[ioh->iovec_off];

	switch ((PgAioOp) ioh->op)
	{
		case PGAIO_OP_READV:
			return ioh->op_data.read.iov_length;
		case PGAIO_OP_WRITEV:
			return ioh->op_data.write.iov_length;
		default:
			pg_unreachable();
			return 0;
	}
}
