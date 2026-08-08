/*-------------------------------------------------------------------------
 *
 * aio_target.c
 *	  AIO - Functionality related to executing IO for different targets
 *
 * 【模块总览(中文)】
 * 本文件实现 AIO 的"目标(target)"抽象:一次 IO 是对"某个对象"
 * (目前只有存储管理器 smgr 这一类)执行的,而不同目标在
 * 日志/重开文件等方面行为不同。设计动机详见 README.md 的
 * "AIO Targets" 一节,要点:
 *
 * - 每个句柄恰好有一个目标(PgAioTargetID),在句柄里只占一个字节
 *   (target 字段);目标相关的描述信息(如 relfilenode、块号)放句柄的
 *   target_data 联合体里,由各目标的实现代码填写;
 * - 目标的行为差异通过 pgaio_target_info 注册表(PgAioTargetInfo)统一
 *   描述,每个目标实现提供三个回调/字段:
 *   - reopen   : 在"另一个进程"里执行 IO 前重开文件描述符(worker
 *     模式下发起者的 fd 在其他进程无效);可缺省(不能重开的 IO 会被
 *     判为必须同步执行,见 pgaio_io_needs_synchronous_execution);
 *   - describe_identity : 把 target_data 渲染成人类可读的字符串,用于
 *     日志与 pg_aios 视图(如 "rel 1663/16384/12345 block 42");
 *   - name     : 目标类别名("smgr" 等),用于日志前缀。
 * - 两个目标若能以同样方式描述 IO 身份(如不同 smgr 实现都以
 *   RelFileLocator+Fork+BlockNumber 描述),就应共用同一个目标条目,
 *   避免重复实现。
 *
 * 本文件是"目标无关"的转发层:根据句柄的目标 ID 查表并转调对应
 * 实现,自身不含任何具体目标的逻辑(具体实现 aio_smgr_target_info
 * 定义于 smgr.c)。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *    src/backend/storage/aio/aio_target.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "storage/aio.h"
#include "storage/aio_internal.h"
#include "storage/smgr.h"


/*
 * Registry for entities that can be the target of AIO.
 */
/* (中文)目标注册表:以 PgAioTargetID 为下标的数组,把目标 ID 映射到
 * 其 PgAioTargetInfo 行为描述:
 * - PGAIO_TID_INVALID : 占位条目(名称 "invalid",无回调),用于
 *   句柄尚未设置目标的状态与调试输出;
 * - PGAIO_TID_SMGR    : 存储管理器目标(aio_smgr_target_info,
 *   定义在 smgr.c),覆盖对数据文件/临时文件的 IO。 */
static const PgAioTargetInfo *pgaio_target_info[] = {
	[PGAIO_TID_INVALID] = &(PgAioTargetInfo) {
		.name = "invalid",
	},
	[PGAIO_TID_SMGR] = &aio_smgr_target_info,
};



/* --------------------------------------------------------------------------------
 * Public target related functions operating on IO Handles
 * --------------------------------------------------------------------------------
 */

/*
 * pgaio_io_has_target - (中文)句柄是否已设置目标
 *
 * 【作用】判断句柄的 target 是否还是 INVALID(未设置)。用于
 * pgaio_io_stage / pgaio_io_before_start 的前置校验(IO 必须有目标
 * 才能执行)。
 *
 * 【参数】ioh —— 目标句柄。
 * 【返回值】true = 已设置合法目标;false = 尚未设置。
 */
bool
pgaio_io_has_target(PgAioHandle *ioh)
{
	return ioh->target != PGAIO_TID_INVALID;
}

/*
 * Return the name for the target associated with the IO. Mostly useful for
 * debugging/logging.
 */
/*
 * pgaio_io_get_target_name - (中文)返回句柄目标的类别名(如 "smgr")
 *
 * 【作用】从注册表取目标的 name 字段,用于调试日志前缀(pgaio_debug_io
 * 的 "target %-4s" 段)与 pg_aios 视图。特意允许 INVALID 目标(调试
 * 消息可能在目标设置前打印),但值域仍受 Assert 约束。
 *
 * 【参数】ioh —— 目标句柄。
 * 【返回值】目标名常量字符串(非 NULL)。
 */
const char *
pgaio_io_get_target_name(PgAioHandle *ioh)
{
	/* explicitly allow INVALID here, function used by debug messages */
	Assert(ioh->target >= PGAIO_TID_INVALID && ioh->target < PGAIO_TID_COUNT);

	return pgaio_target_info[ioh->target]->name;
}

/*
 * Assign a target to the IO.
 *
 * This has to be called exactly once before pgaio_io_start_*() is called.
 */
/*
 * pgaio_io_set_target - (中文)为句柄设置 IO 目标
 *
 * 【作用】把句柄的目标 ID 设为 targetid。必须在 pgaio_io_start_*() 之前
 * 恰好调用一次(句柄处于 HANDED_OUT 且 target 仍为 INVALID,双重
 * Assert 强制)。目标确定后,具体的目标描述数据由上层(如 smgr 的
 * 各级)经 pgaio_io_get_target_data() 取得指针后自行填写。
 *
 * 【参数】ioh —— HANDED_OUT 状态的句柄;targetid —— 目标类型
 *        (目前仅 PGAIO_TID_SMGR)。
 * 【返回值】无。
 */
void
pgaio_io_set_target(PgAioHandle *ioh, PgAioTargetID targetid)
{
	Assert(ioh->state == PGAIO_HS_HANDED_OUT);
	Assert(ioh->target == PGAIO_TID_INVALID);

	ioh->target = targetid;
}

/*
 * pgaio_io_get_target_data - (中文)返回句柄的目标描述数据区指针
 *
 * 【作用】返回句柄内 PgAioTargetData(目标身份的联合体:smgr 场景下为
 * RelFileLocator + 块号 + fork 等)的指针。发起方在设置目标后向其中
 * 填身份信息;完成回调、错误消息与 worker 重开文件时读取。
 *
 * 【参数】ioh —— 目标句柄。
 * 【返回值】指向句柄 target_data 字段的指针。
 */
PgAioTargetData *
pgaio_io_get_target_data(PgAioHandle *ioh)
{
	return &ioh->target_data;
}

/*
 * Return a stringified description of the IO's target.
 *
 * The string is localized and allocated in the current memory context.
 */
/*
 * pgaio_io_get_target_description - (中文)生成目标的人类可读描述字符串
 *
 * 【作用】调用目标实现的 describe_identity 回调,把 target_data 渲染
 * 成带对象身份的说明文字(如 "rel 1663/16384/12345 block 42"),供
 * 错误消息与 pg_aios 视图的 target description 列使用。
 *
 * 【设计思想】要求目标已设置(禁止 INVALID,否则没有可描述的对象)。
 * 字符串本地化并在当前内存上下文中分配,调用方按需释放。
 *
 * 【参数】ioh —— 目标句柄(目标已设置)。
 * 【返回值】新分配的描述字符串(属调用方内存上下文)。
 */
char *
pgaio_io_get_target_description(PgAioHandle *ioh)
{
	/* disallow INVALID, there wouldn't be a description */
	Assert(ioh->target > PGAIO_TID_INVALID && ioh->target < PGAIO_TID_COUNT);

	return pgaio_target_info[ioh->target]->describe_identity(&ioh->target_data);
}



/* --------------------------------------------------------------------------------
 * Internal target related functions operating on IO Handles
 * --------------------------------------------------------------------------------
 */

/*
 * Internal: Check if pgaio_io_reopen() is available for the IO.
 */
/*
 * pgaio_io_can_reopen - (中文)句柄的目标是否支持重开文件(供 worker 用)
 *
 * 【作用】判断目标注册表里是否提供了 reopen 回调。worker 方法在把
 * IO 派发给 worker 进程前调用:若不能重开文件,该 IO 无法在其他进程
 * 执行,必须回退为同步执行(见 pgaio_io_needs_synchronous_execution)。
 *
 * 【参数】ioh —— 目标句柄(目标已设置)。
 * 【返回值】true = 可在其他进程重开文件执行;false = 只能本进程执行。
 */
bool
pgaio_io_can_reopen(PgAioHandle *ioh)
{
	Assert(ioh->target > PGAIO_TID_INVALID && ioh->target < PGAIO_TID_COUNT);

	return pgaio_target_info[ioh->target]->reopen != NULL;
}

/*
 * Internal: Before executing an IO outside of the context of the process the
 * IO has been staged in, the file descriptor has to be reopened - any FD
 * referenced in the IO itself, won't be valid in the separate process.
 */
/*
 * pgaio_io_reopen - (中文)在目标进程里重开 IO 所需的数据文件
 *
 * 【作用】在"非发起进程"(如 worker)执行 IO 之前调用:目标实现按
 * target_data 里的身份信息(relfilenode 等)重新打开文件,并把新 fd
 * 写回句柄的 op_data(此后 worker 用新 fd 执行 readv/writev)。
 * 发起者句柄里的 fd 在其他进程无效,必须重开。
 *
 * 【设计思想】这也解释了为何句柄的 op_data 与 target_data 必须放在
 * 共享内存:worker 进程要能读身份、写回 fd。reopen 的可行性由
 * pgaio_io_can_reopen() 先行确认(否则 IO 会同步执行,不会走到这里)。
 *
 * 【参数】ioh —— 已定义操作的目标句柄(目标与 op 均已设置)。
 * 【返回值】无。句柄 op_data 中的 fd 被更新为重开后的新 fd。
 */
void
pgaio_io_reopen(PgAioHandle *ioh)
{
	Assert(ioh->target > PGAIO_TID_INVALID && ioh->target < PGAIO_TID_COUNT);
	Assert(ioh->op > PGAIO_OP_INVALID && ioh->op < PGAIO_OP_COUNT);

	pgaio_target_info[ioh->target]->reopen(ioh);
}
