/*-------------------------------------------------------------------------
 *
 * method_sync.c
 *    AIO - perform "AIO" by executing it synchronously
 *
 * This method is mainly to check if AIO use causes regressions. Other IO
 * methods might also fall back to the synchronous method for functionality
 * they cannot provide.
 *
 * 【模块总览(中文)】
 * 本文件实现"同步方法"(io_method=sync):名义上是三种 AIO 实现之一,
 * 实际上不做任何异步——把所有 IO 统统退化为"在本进程内、当场阻塞
 * 执行"。实现极其简洁,只有两个回调:
 *
 * - pgaio_sync_needs_synchronous_execution():无条件返回 true,即
 *   "所有 IO 都必须同步执行"。这使 pgaio_io_stage() 走同步分支,
 *   直接调用 pgaio_io_perform_synchronously()(实现在 aio_io.c,
 *   方法无关)执行 IO 并通过标准完成路径收尾;
 * - pgaio_sync_submit():理论上永不该被调用(因为上面那个回调已经
 *   把所有 IO 挡在异步路径之外),一旦被调用说明状态机逻辑出了
 *   bug,直接报错。
 *
 * 该方法的用途:
 * 1) 回归测试:在"代码全部走 AIO 接口、但实际同步执行"的配置下
 *    跑测试,可以隔离出"异步性"本身引入的回归;
 * 2) 其他方法(如 worker)对"自己无法执行的 IO"(例如引用进程本地
 *    内存、无法重开文件的 IO)也回退到同一套同步执行机制,但那是
 *    复用 aio_io.c 的函数,与本文件无关。
 *
 * 因为无共享内存需求,本方法的 IoMethodOps 里所有 shmem 回调与
 * init_backend 均为 NULL。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/aio/method_sync.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "storage/aio.h"
#include "storage/aio_internal.h"

static bool pgaio_sync_needs_synchronous_execution(PgAioHandle *ioh);
static int	pgaio_sync_submit(uint16 num_staged_ios, PgAioHandle **staged_ios);


/* (中文)同步方法的 IoMethodOps 定义:注册两个回调。
 * 注意全部共享内存回调与 init_backend 均缺省(NULL):同步方法不需要
 * 任何共享内存与进程本地初始化。 */
const IoMethodOps pgaio_sync_ops = {
	.needs_synchronous_execution = pgaio_sync_needs_synchronous_execution,
	.submit = pgaio_sync_submit,
};



/*
 * pgaio_sync_needs_synchronous_execution - (中文)判"需要同步执行":恒真
 *
 * 【作用】同步方法的 needs_synchronous_execution 实现:对任何 IO 都
 * 返回 true。这保证所有 IO 在 pgaio_io_stage() 里走同步分支,由
 * pgaio_io_perform_synchronously() 当场执行,永远不会进入异步提交
 * 通道(pgaio_method_ops->submit)。
 *
 * 【参数】ioh —— 目标句柄(未使用)。
 * 【返回值】恒为 true。
 */
static bool
pgaio_sync_needs_synchronous_execution(PgAioHandle *ioh)
{
	return true;
}

/*
 * pgaio_sync_submit - (中文)异步提交回调:不应被调用,被调用即报错
 *
 * 【作用】同步方法没有异步提交能力;由于 needs_synchronous_execution
 * 恒真,正常流程永远不会走到本函数。若走到了,说明"同步判定"与
 * "提交调度"之间的逻辑失配(编程错误),直接 elog(ERROR) 暴露问题,
 * 而不是静默丢 IO。
 *
 * 【参数】num_staged_ios —— 待提交 IO 数;staged_ios —— 句柄数组。
 *        (参数实际上不会被使用,因为函数必然报错)。
 * 【返回值】不会正常返回(报错);形式上的返回值 0 仅用于安抚编译器。
 */
static int
pgaio_sync_submit(uint16 num_staged_ios, PgAioHandle **staged_ios)
{
	elog(ERROR, "IO should have been executed synchronously");

	return 0;
}
