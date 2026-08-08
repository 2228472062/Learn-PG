/*-------------------------------------------------------------------------
 *
 * aio_callback.c
 *	  AIO - Functionality related to callbacks that can be registered on IO
 *	  Handles
 *
 * 【模块总览(中文)】
 * 本文件实现 AIO 的"完成回调"机制,即:如何把一个 IO 的生命周期事件
 * (stage / complete_shared / complete_local / report)分发到各层子系统
 * 注册的处理函数。整体设计动机见 README.md 的 "AIO Callbacks" 一节,
 * 核心要点:
 *
 * 1) 回调用"ID 而非函数指针"标识:
 *    - 共享内存(句柄池)中不能直接存函数指针——EXEC_BACKEND 构建下
 *      各进程因 ASLR 地址空间不同,同一函数在不同进程里的地址不一致;
 *    - 因此句柄里只存一个字节的 PgAioHandleCallbackID,由本文件的
 *      aio_handle_cbs 表把 ID 映射回本进程的函数指针与名字。
 *
 * 2) 一条句柄可以注册多个回调(PGAIO_HANDLE_MAX_CALLBACKS 个),
 *    例如一次读共享缓冲区的 IO 会同时注册 md.c 的回调(校验 IO 长度/
 *    成败)与 bufmgr.c 的回调(校验页面合法、更新 BufferDesc 状态)。
 *    执行顺序固定为"后注册的先执行"(从外层到内层),这样高层代码的
 *    回调可以依赖低层回调已经完成的结果。
 *
 * 3) 三类回调各自职责(对应 PgAioHandleCallbacks 的字段):
 *    - stage:    IO 定义完成、即将提交前调用,用于预备资源(如把缓冲区
 *                pin 的所有权转移给 AIO 子系统,防止发起者出错释放 pin
 *                后 IO 还在使用该缓冲区);
 *    - complete_shared: IO 完成后调用,可修改共享内存中的资源状态(如
 *                BufferDesc);可能在任意进程执行(完成该 IO 的后端),
 *                且运行在临界区内,只能通过返回值报告错误;
 *    - complete_local: 类似 complete_shared,但只在本后端(发起者)执行,
 *                用于更新进程私有状态(如临时缓冲区的 BufferDesc);
 *    - report:   把蒸馏后的 PgAioResult 转成日志/错误(由发起者在合适的
 *                时机显式调用)。
 *
 * 4) 结果蒸馏(distilled result):complete_shared 链逐层传递并修改一个
 *    PgAioResult(状态 + 出错回调 ID + error_data + 原始返回值),最终
 *    存入句柄的 distilled_result;complete_local 链在其基础上继续修改,
 *    最终写入发起者的 PgAioReturn。因为完成回调运行在临界区且可能跨
 *    进程,错误不能当场 raise,只能以这种紧凑编码传递(内存预算极小:
 *    PGAIO_RESULT_ERROR_BITS 23 位)。
 *
 * 5) 句柄数据(handle data):本文件还提供 pgaio_io_set_handle_data_*()
 *    系列,把"该 IO 涉及哪些缓冲区"这类 32/64 位数组拷贝进共享内存
 *    的 handle_data 池,供完成回调(如 bufmgr 的回调)读取,从而知道
 *    要更新哪些 BufferDesc。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *    src/backend/storage/aio/aio_callback.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "miscadmin.h"
#include "storage/aio.h"
#include "storage/aio_internal.h"
#include "storage/bufmgr.h"
#include "storage/md.h"


/* just to have something to put into aio_handle_cbs */
/* (中文)空回调占位对象:所有函数指针为 NULL/0,供 ID 为
 * PGAIO_HCB_INVALID(0) 的槽位使用,避免该槽位是空指针表项。 */
static const PgAioHandleCallbacks aio_invalid_cb = {0};

/* (中文)回调表项:一个回调 ID 对应的"函数集 + 名称"。
 * - cb   : PgAioHandleCallbacks 函数集(stage/complete_shared/
 *          complete_local/report 可缺省为 NULL);
 * - name : 回调名的字符串,用于日志/错误消息。 */
typedef struct PgAioHandleCallbacksEntry
{
	const PgAioHandleCallbacks *const cb;
	const char *const name;
} PgAioHandleCallbacksEntry;

/*
 * Callback definition for the callbacks that can be registered on an IO
 * handle.  See PgAioHandleCallbackID's definition for an explanation for why
 * callbacks are not identified by a pointer.
 */
/* (中文)回调注册表:以 PgAioHandleCallbackID 为下标的数组,把 ID 映射到
 * 本进程的函数集。目前支持三种回调(其余子系统可扩展):
 * - PGAIO_HCB_MD_READV            : 存储管理器(md.c)的读回调,校验
 *   IO 是否完整成功(读够字节数);
 * - PGAIO_HCB_SHARED_BUFFER_READV : bufmgr 的共享缓冲区读回调,校验
 *   页面合法性、更新 BufferDesc 状态、让等待者可用缓冲区;
 * - PGAIO_HCB_LOCAL_BUFFER_READV  : 本地(临时)缓冲区读回调,与
 *   SHARED_BUFFER 版类似但只在本后端执行(临时缓冲区的 BufferDesc
 *   不在共享内存)。 */
static const PgAioHandleCallbacksEntry aio_handle_cbs[] = {
#define CALLBACK_ENTRY(id, callback)  [id] = {.cb = &callback, .name = #callback}
	CALLBACK_ENTRY(PGAIO_HCB_INVALID, aio_invalid_cb),

	CALLBACK_ENTRY(PGAIO_HCB_MD_READV, aio_md_readv_cb),

	CALLBACK_ENTRY(PGAIO_HCB_SHARED_BUFFER_READV, aio_shared_buffer_readv_cb),

	CALLBACK_ENTRY(PGAIO_HCB_LOCAL_BUFFER_READV, aio_local_buffer_readv_cb),
#undef CALLBACK_ENTRY
};



/* --------------------------------------------------------------------------------
 * Public callback related functions operating on IO Handles
 * --------------------------------------------------------------------------------
 */

/*
 * Register callback for the IO handle.
 *
 * Only a limited number (PGAIO_HANDLE_MAX_CALLBACKS) of callbacks can be
 * registered for each IO.
 *
 * Callbacks need to be registered before [indirectly] calling
 * pgaio_io_start_*(), as the IO may be executed immediately.
 *
 * A callback can be passed a small bit of data, e.g. to indicate whether to
 * zero a buffer if it is invalid.
 *
 *
 * Note that callbacks are executed in critical sections.  This is necessary
 * to be able to execute IO in critical sections (consider e.g. WAL
 * logging). To perform AIO we first need to acquire a handle, which, if there
 * are no free handles, requires waiting for IOs to complete and to execute
 * their completion callbacks.
 *
 * Callbacks may be executed in the issuing backend but also in another
 * backend (because that backend is waiting for the IO) or in IO workers (if
 * io_method=worker is used).
 *
 *
 * See PgAioHandleCallbackID's definition for an explanation for why
 * callbacks are not identified by a pointer.
 */
/*
 * pgaio_io_register_callbacks - (中文)为句柄注册一个完成回调
 *
 * 【作用】在"发起 IO 之前"把某个回调 ID 挂到句柄上(连同一个小数据
 * 载荷 cb_data)。必须早于(直接或间接的)pgaio_io_start_*() 调用——
 * 一旦开始,IO 可能立刻被执行甚至完成,回调就来不及注册了。一个句柄
 * 最多注册 PGAIO_HANDLE_MAX_CALLBACKS 个(超出 PANIC,属编程错误)。
 *
 * 【设计思想】完成回调可能运行在临界区中(保证 WAL 等临界区 IO 能被
 * 完成),也可能在别的后端/IO worker 中执行,因此注册进来的回调本身
 * 必须"只改共享内存、不报错、不申请内存"。cb_data 是一个字节的载荷,
 * 常见用法:告诉回调"失败时是否把缓冲区清零"等布尔/枚举参数。
 *
 * 【参数】ioh —— 目标句柄(必须处于 HANDED_OUT 状态);
 *        cb_id —— 回调 ID(PGAIO_HCB_*);cb_data —— 传给回调的 1 字节载荷。
 * 【返回值】无。
 */
void
pgaio_io_register_callbacks(PgAioHandle *ioh, PgAioHandleCallbackID cb_id,
							uint8 cb_data)
{
	const PgAioHandleCallbacksEntry *ce = &aio_handle_cbs[cb_id];

	Assert(cb_id <= PGAIO_HCB_MAX);
	if (cb_id >= lengthof(aio_handle_cbs))
		elog(ERROR, "callback %d is out of range", cb_id);
	if (aio_handle_cbs[cb_id].cb->complete_shared == NULL &&
		aio_handle_cbs[cb_id].cb->complete_local == NULL)
		elog(ERROR, "callback %d does not have a completion callback", cb_id);
	if (ioh->num_callbacks >= PGAIO_HANDLE_MAX_CALLBACKS)
		elog(PANIC, "too many callbacks, the max is %d",
			 PGAIO_HANDLE_MAX_CALLBACKS);
	ioh->callbacks[ioh->num_callbacks] = cb_id;
	ioh->callbacks_data[ioh->num_callbacks] = cb_data;

	pgaio_debug_io(DEBUG3, ioh,
				   "adding cb #%d, id %d/%s",
				   ioh->num_callbacks + 1,
				   cb_id, ce->name);

	ioh->num_callbacks++;
}

/*
 * Associate an array of data with the Handle. This is e.g. useful to the
 * transport knowledge about which buffers a multi-block IO affects to
 * completion callbacks.
 *
 * Right now this can be done only once for each IO, even though multiple
 * callbacks can be registered. There aren't any known usecases requiring more
 * and the required amount of shared memory does add up, so it doesn't seem
 * worth multiplying memory usage by PGAIO_HANDLE_MAX_CALLBACKS.
 */
/*
 * pgaio_io_set_handle_data_64 - (中文)把 64 位元素数组关联到句柄
 *
 * 【作用】把调用者提供的 uint64 数组(长度 len)拷贝到共享内存的
 * handle_data 池(句柄自己的 iovec_off 偏移处),并记录句柄的
 * handle_data_len。完成回调(如 SHARED_BUFFER_READV)在执行时会用
 * pgaio_io_get_handle_data() 读回这些数据,得知"这次 IO 影响了哪些
 * 缓冲区",从而更新对应的 BufferDesc。
 *
 * 【设计思想】数组放在共享内存而非句柄内:一次多块 IO 的块数最多可达
 * io_combine_limit,而共享内存的 handle_data 池按后端静态分配,总量
 * 可控。目前限制"每个 IO 只能设置一次"(Assert handle_data_len == 0),
 * 虽然一个句柄可有多个回调——没有已知场景需要为不同回调存不同的数据,
 * 而共享内存按最大回调数翻倍开销不值得。数组元素是 64 位,足以容纳
 * Buffer ID(见 aio_internal.h 中 PgAioCtl->handle_data 的注释)。
 *
 * 【参数】ioh —— HANDED_OUT 状态的句柄;
 *        data —— 源数组(进程本地内存);len —— 元素个数(≤ PG_IOV_MAX,
 *               且 ≤ io_max_combine_limit)。
 * 【返回值】无。
 */
void
pgaio_io_set_handle_data_64(PgAioHandle *ioh, uint64 *data, uint8 len)
{
	Assert(ioh->state == PGAIO_HS_HANDED_OUT);
	Assert(ioh->handle_data_len == 0);
	Assert(len <= PG_IOV_MAX);
	Assert(len <= io_max_combine_limit);

	for (int i = 0; i < len; i++)
		pgaio_ctl->handle_data[ioh->iovec_off + i] = data[i];
	ioh->handle_data_len = len;
}

/*
 * Convenience version of pgaio_io_set_handle_data_64() that converts a 32bit
 * array to a 64bit array. Without it callers would end up needing to
 * open-code equivalent code.
 */
/*
 * pgaio_io_set_handle_data_32 - (中文)32 位数组版的数据关联(自动零扩展)
 *
 * 【作用】pgaio_io_set_handle_data_64() 的便捷版本:调用方的数据是
 * uint32 数组(常见:Buffer ID 就是 32 位),逐元素零扩展成 64 位后
 * 拷贝进共享内存池,其余语义完全一致。省去调用方手写转换循环。
 *
 * 【参数】ioh —— HANDED_OUT 状态的句柄;
 *        data —— uint32 源数组;len —— 元素个数(上限同 64 位版)。
 * 【返回值】无。
 */
void
pgaio_io_set_handle_data_32(PgAioHandle *ioh, uint32 *data, uint8 len)
{
	Assert(ioh->state == PGAIO_HS_HANDED_OUT);
	Assert(ioh->handle_data_len == 0);
	Assert(len <= PG_IOV_MAX);
	Assert(len <= io_max_combine_limit);

	for (int i = 0; i < len; i++)
		pgaio_ctl->handle_data[ioh->iovec_off + i] = data[i];
	ioh->handle_data_len = len;
}

/*
 * Return data set with pgaio_io_set_handle_data_*().
 */
/*
 * pgaio_io_get_handle_data - (中文)读回句柄关联的数据数组(完成回调用)
 *
 * 【作用】完成回调(pgaio_io_call_* 的调用对象)在 IO 完成后读取
 * pgaio_io_set_handle_data_*() 写入的数组:返回共享内存池中该句柄
 * 数据区起点,长度经输出参数返回。数据在共享内存,因此任何进程里的
 * 完成回调(包括 worker)都能读取。
 *
 * 【参数】ioh —— 目标句柄;len —— 输出参数,数组元素个数。
 * 【返回值】指向共享内存 handle_data 池中该句柄数据区起点的指针
 * (调用者按 *len 个元素访问)。
 */
uint64 *
pgaio_io_get_handle_data(PgAioHandle *ioh, uint8 *len)
{
	Assert(ioh->handle_data_len > 0);

	*len = ioh->handle_data_len;

	return &pgaio_ctl->handle_data[ioh->iovec_off];
}



/* --------------------------------------------------------------------------------
 * Public IO Result related functions
 * --------------------------------------------------------------------------------
 */

/*
 * pgaio_result_report - (中文)按结果 ID 转调对应回调的 report 函数
 *
 * 【作用】IO 失败/部分成功时,由发起者在"合适的时机"(通常
 * pgaio_wref_wait() 返回之后、仍在事务上下文中)调用:根据结果中编码的
 * 回调 ID 找到 report 回调,把 PgAioResult 与目标信息交给它,由它决定
 * 具体报什么错/什么级别的日志(例如 md 层报 "could not read block",
 * bufmgr 层报 "invalid page" 并附上 relation 信息)。这样错误消息的
 * 生成完全由各层自己负责,与完成回调的跨进程/临界区限制无关。
 *
 * 【前置条件】result.status 不得是 UNKNOWN(未完成)或 OK(无需报告),
 * 函数内 Assert 强制;目标回调必须实现了 report(否则编程错误)。
 *
 * 【参数】
 *   result      —— 蒸馏后的 IO 结果(含成败状态、出错回调 ID、error_data);
 *   target_data —— IO 目标的描述信息(用于生成带对象身份的错误消息);
 *   elevel      —— 日志级别(典型 ERROR 或 LOG)。
 * 【返回值】无。可能抛错(若 elevel 是 ERROR)。
 */
void
pgaio_result_report(PgAioResult result, const PgAioTargetData *target_data, int elevel)
{
	PgAioHandleCallbackID cb_id = result.id;
	const PgAioHandleCallbacksEntry *ce = &aio_handle_cbs[cb_id];

	Assert(result.status != PGAIO_RS_UNKNOWN);
	Assert(result.status != PGAIO_RS_OK);

	if (ce->cb->report == NULL)
		elog(ERROR, "callback %d/%s does not have report callback",
			 result.id, ce->name);

	ce->cb->report(result, target_data, elevel);
}



/* --------------------------------------------------------------------------------
 * Internal callback related functions operating on IO Handles
 * --------------------------------------------------------------------------------
 */

/*
 * Internal function which invokes ->stage for all the registered callbacks.
 */
/*
 * pgaio_io_call_stage - (中文)运行句柄上全部回调的 stage 阶段
 *
 * 【作用】在句柄进入 STAGED 状态之前(由 pgaio_io_stage 调用),逆序
 * (后注册的先执行)调用所有注册回调的 stage 函数。stage 回调的典型
 * 职责:为 IO 预备资源,例如把缓冲区 pin 的所有权转移给 AIO 子系统
 * (额外增加引用计数)——这样即使发起者在 IO 在途期间出错、释放了自己
 * 的 pin,缓冲区也不会被提前淘汰。
 *
 * 【设计思想】此阶段运行在本后端、临界区外,但实现仍应轻量。逆序执行
 * 与 complete_shared 一致(外层先跑),保持各阶段回调顺序统一。
 * 无 stage 实现的回调直接跳过(经 ID 表查询,不用 null 检查以外的
 * 代价)。target/op 必须已经设置(Assert 校验)。
 *
 * 【参数】ioh —— DEFINED 状态、已设置 target 与 op 的句柄。
 * 【返回值】无。
 */
void
pgaio_io_call_stage(PgAioHandle *ioh)
{
	Assert(ioh->target > PGAIO_TID_INVALID && ioh->target < PGAIO_TID_COUNT);
	Assert(ioh->op > PGAIO_OP_INVALID && ioh->op < PGAIO_OP_COUNT);

	for (int i = ioh->num_callbacks; i > 0; i--)
	{
		PgAioHandleCallbackID cb_id = ioh->callbacks[i - 1];
		uint8		cb_data = ioh->callbacks_data[i - 1];
		const PgAioHandleCallbacksEntry *ce = &aio_handle_cbs[cb_id];

		if (!ce->cb->stage)
			continue;

		pgaio_debug_io(DEBUG3, ioh,
					   "calling cb #%d %d/%s->stage(%u)",
					   i, cb_id, ce->name, cb_data);
		ce->cb->stage(ioh, cb_data);
	}
}

/*
 * Internal function which invokes ->complete_shared for all the registered
 * callbacks.
 */
/*
 * pgaio_io_call_complete_shared - (中文)运行句柄上全部回调的共享完成阶段
 *
 * 【作用】IO 底层执行完毕后(由 pgaio_io_process_completion 调用,它
 * 自身已在临界区内),逆序调用所有回调的 complete_shared,把结果从
 * 低层逐层"蒸馏"到高层:
 * - 起始结果固定为"底层 IO 成功"(status = OK),携带原始返回值
 *   (readv/writev 的字节数)与原始 result;
 * - 每个回调读取/修改这个 PgAioResult(如 md 层发现读得不够长 → 置为
 *   PARTIAL/ERROR 并带上自己的 id),把新结果传给下一个回调;
 * - 最终结果存入句柄的 distilled_result,供 complete_local 与
 *   PgAioReturn 使用。
 *
 * 【设计思想】
 * - 调用顺序"后注册先执行"(从外层到内层):例如 bufmgr 的回调后注册,
 *   先执行,它的结果会被 md 的回调修正;反过来则高层永远看不到低层
 *   的处理结果;
 * - 整个链运行在临界区(START/END_CRIT_SECTION 包住):回调只能通过
 *   返回值表达错误,绝不能抛错;回调绝不能把结果重置回 UNKNOWN
 *   (函数内 Assert 强制,避免下游误判);
 * - 共享回调可能在"任何"后端执行(完成该 IO 的进程),因此只能操作
 *   共享内存中的资源。
 *
 * 【参数】ioh —— COMPLETED_IO 状态的句柄。
 * 【返回值】无。结果存于 ioh->distilled_result。
 */
void
pgaio_io_call_complete_shared(PgAioHandle *ioh)
{
	PgAioResult result;

	START_CRIT_SECTION();

	Assert(ioh->target > PGAIO_TID_INVALID && ioh->target < PGAIO_TID_COUNT);
	Assert(ioh->op > PGAIO_OP_INVALID && ioh->op < PGAIO_OP_COUNT);

	result.status = PGAIO_RS_OK;	/* low level IO is always considered OK */
	result.result = ioh->result;
	result.id = PGAIO_HCB_INVALID;
	result.error_data = 0;

	/*
	 * Call callbacks with the last registered (innermost) callback first.
	 * Each callback can modify the result forwarded to the next callback.
	 */
	for (int i = ioh->num_callbacks; i > 0; i--)
	{
		PgAioHandleCallbackID cb_id = ioh->callbacks[i - 1];
		uint8		cb_data = ioh->callbacks_data[i - 1];
		const PgAioHandleCallbacksEntry *ce = &aio_handle_cbs[cb_id];

		if (!ce->cb->complete_shared)
			continue;

		pgaio_debug_io(DEBUG4, ioh,
					   "calling cb #%d, id %d/%s->complete_shared(%u) with distilled result: (status %s, id %u, error_data %d, result %d)",
					   i, cb_id, ce->name,
					   cb_data,
					   pgaio_result_status_string(result.status),
					   result.id, result.error_data, result.result);
		result = ce->cb->complete_shared(ioh, result, cb_data);

		/* the callback should never transition to unknown */
		Assert(result.status != PGAIO_RS_UNKNOWN);
	}

	ioh->distilled_result = result;

	pgaio_debug_io(DEBUG3, ioh,
				   "after shared completion: distilled result: (status %s, id %u, error_data: %d, result %d), raw_result: %d",
				   pgaio_result_status_string(result.status),
				   result.id, result.error_data, result.result,
				   ioh->result);

	END_CRIT_SECTION();
}

/*
 * Internal function which invokes ->complete_local for all the registered
 * callbacks.
 *
 * Returns ioh->distilled_result after, possibly, being modified by local
 * callbacks.
 *
 * XXX: It'd be nice to deduplicate with pgaio_io_call_complete_shared().
 */
/*
 * pgaio_io_call_complete_local - (中文)运行句柄上全部回调的本地完成阶段
 *
 * 【作用】complete_shared 链的"本地收尾":在发起者本后端内(由
 * pgaio_io_reclaim 调用)逆序执行所有回调的 complete_local。从
 * distilled_result(共享阶段的结果)出发,允许各回调进一步修改,处理
 * 那些"共享阶段无法访问的进程私有资源",例如:
 * - 临时(本地)缓冲区的 BufferDesc(不在共享内存);
 * - 本进程内的统计、记账等。
 *
 * 【设计思想】
 * - 与 complete_shared 的分工:共享阶段保证"任何进程都能看到一致的
 *   完成结果",本地阶段只服务发起者自己,因此其结果**不会**写回
 *   distilled_result(其他等待者不关心,也不应看到),而是作为返回值
 *   交给调用者,由它写入发起者的 PgAioReturn(见 pgaio_io_reclaim);
 * - 同样运行在临界区内、逆序执行、结果不得回到 UNKNOWN;
 * - 注释中的 XXX 提示:本函数与共享版高度相似,未来可考虑去重。
 *
 * 【参数】ioh —— COMPLETED_SHARED 状态的句柄(本后端是其所有者)。
 * 【返回值】本地链处理后的最终 PgAioResult(供写入 report_return)。
 */
PgAioResult
pgaio_io_call_complete_local(PgAioHandle *ioh)
{
	PgAioResult result;

	START_CRIT_SECTION();

	Assert(ioh->target > PGAIO_TID_INVALID && ioh->target < PGAIO_TID_COUNT);
	Assert(ioh->op > PGAIO_OP_INVALID && ioh->op < PGAIO_OP_COUNT);

	/* start with distilled result from shared callback */
	result = ioh->distilled_result;
	Assert(result.status != PGAIO_RS_UNKNOWN);

	for (int i = ioh->num_callbacks; i > 0; i--)
	{
		PgAioHandleCallbackID cb_id = ioh->callbacks[i - 1];
		uint8		cb_data = ioh->callbacks_data[i - 1];
		const PgAioHandleCallbacksEntry *ce = &aio_handle_cbs[cb_id];

		if (!ce->cb->complete_local)
			continue;

		pgaio_debug_io(DEBUG4, ioh,
					   "calling cb #%d, id %d/%s->complete_local(%u) with distilled result: status %s, id %u, error_data %d, result %d",
					   i, cb_id, ce->name, cb_data,
					   pgaio_result_status_string(result.status),
					   result.id, result.error_data, result.result);
		result = ce->cb->complete_local(ioh, result, cb_data);

		/* the callback should never transition to unknown */
		Assert(result.status != PGAIO_RS_UNKNOWN);
	}

	/*
	 * Note that we don't save the result in ioh->distilled_result, the local
	 * callback's result should not ever matter to other waiters. However, the
	 * local backend does care, so we return the result as modified by local
	 * callbacks, which then can be passed to ioh->report_return->result.
	 */
	pgaio_debug_io(DEBUG3, ioh,
				   "after local completion: result: (status %s, id %u, error_data %d, result %d), raw_result: %d",
				   pgaio_result_status_string(result.status),
				   result.id, result.error_data, result.result,
				   ioh->result);

	END_CRIT_SECTION();

	return result;
}
