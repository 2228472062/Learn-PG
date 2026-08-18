/*-------------------------------------------------------------------------
 *
 * execUtils.c
 *	  执行器公共工具函数集——"什么都放一点"的执行期支撑库
 *
 * 【业务作用】
 *   本文件承载执行器运行期间被广泛复用的基础设施：
 *   - 执行状态与内存管理：CreateExecutorState / FreeExecutorState 创建与
 *     销毁整个执行器的状态根（EState 及其 per-query 内存上下文）；
 *   - 表达式求值环境：ExprContext 的创建/释放/重置（表达式求值必须在
 *     ExprContext 的 per-tuple 内存中做，保证逐行回收临时结果）；
 *   - 节点初始化辅助：ExecAssignExprContext（装配节点表达式上下文）、
 *     ExecAssignProjectionInfo（构建投影）、各种结果/扫描槽信息查询；
 *   - 范围表支撑：ExecInitRangeTable 初始化 RTE 相关数组、按 RTE 索引
 *     惰性打开关系（ExecGetRangeTableRelation）、注册结果关系
 *     （ExecInitResultRelation）；
 *   - 错误定位：executor_errposition 把语法位置（字节偏移）转成可报告的
 *     字符位置；
 *   - 表达式上下文回调：Register/UnregisterExprContextCallback，用于
 *     SRF（集合返回函数）等"表达式执行中持有外部资源"的场景；
 *   - 元组属性访问：GetAttributeByName / GetAttributeByNum（C 函数处理
 *     tuple 参数时的标准取列方式）；
 *   - 分区/触发器支撑：OLD/NEW/RETURNING 槽、根表↔子表列映射
 *     （ExecGetChildToRootMap / ExecGetRootToChildMap）、已插入/已更新列
 *     位图查询等。
 *
 * 内存模型（重要）：
 *   EState（es_query_cxt）┐
 *     ├─ ExprContext ── ecxt_per_tuple_memory  ← 每行求值的内存，逐行重置
 *     ├─ ResultRelInfo/PlanState 等执行期对象
 *     └─ 元组表、参数表……
 *   一切随 ExecutorEnd 一次性释放。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execUtils.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/parallel.h"
#include "access/table.h"
#include "access/tableam.h"
#include "access/tupconvert.h"
#include "executor/executor.h"
#include "executor/nodeModifyTable.h"
#include "jit/jit.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "parser/parse_relation.h"
#include "partitioning/partdesc.h"
#include "port/pg_bitutils.h"
#include "storage/lmgr.h"
#include "utils/builtins.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/typcache.h"


static bool tlist_matches_tupdesc(PlanState *ps, List *tlist, int varno, TupleDesc tupdesc);
static void ShutdownExprContext(ExprContext *econtext, bool isCommit);
static RTEPermissionInfo *GetResultRTEPermissionInfo(ResultRelInfo *relinfo, EState *estate);


/* ----------------------------------------------------------------
 *				 Executor state and memory management functions
 * ----------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】CreateExecutorState —— 创建执行器状态根（EState）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   创建并初始化 EState 节点——一次 Executor 调用的全部工作存储的根。
 *   核心动作是创建 per-query 内存上下文（"ExecutorState"，本查询所有
 *   长期数据都在其下分配，随查询结束整体释放）。
 *
 * 返回/副作用：
 *   新 EState；其 es_query_cxt 是调用方 CurrentMemoryContext 的子上下文。
 *
 * 设计思想：
 *   - 结构与内存一体：EState 节点本身也分配在 per-query 上下文里，关闭时
 *     无需单独 pfree 它；
 *   - 所有字段显式初始化（方向=正向、快照待填、各列表为空），保证后续
 *     代码可在无"脏字段"的前提下直接使用；
 *   - es_snapshot 等由调用方（standard_ExecutorStart）在后续步骤填充，
 *     这里只设初值占位。
 * ============================================================================
 */
EState *
CreateExecutorState(void)
{
	EState	   *estate;
	MemoryContext qcontext;
	MemoryContext oldcontext;

	/*
	 * Create the per-query context for this Executor run.
	 */
	qcontext = AllocSetContextCreate(CurrentMemoryContext,
									 "ExecutorState",
									 ALLOCSET_DEFAULT_SIZES);

	/*
	 * Make the EState node within the per-query context.  This way, we don't
	 * need a separate pfree() operation for it at shutdown.
	 */
	oldcontext = MemoryContextSwitchTo(qcontext);

	estate = makeNode(EState);

	/*
	 * Initialize all fields of the Executor State structure
	 */
	estate->es_direction = ForwardScanDirection;
	estate->es_snapshot = InvalidSnapshot;	/* caller must initialize this */
	estate->es_crosscheck_snapshot = InvalidSnapshot;	/* no crosscheck */
	estate->es_range_table = NIL;
	estate->es_range_table_size = 0;
	estate->es_relations = NULL;
	estate->es_rowmarks = NULL;
	estate->es_rteperminfos = NIL;
	estate->es_plannedstmt = NULL;
	estate->es_part_prune_infos = NIL;
	estate->es_part_prune_states = NIL;
	estate->es_part_prune_results = NIL;
	estate->es_unpruned_relids = NULL;

	estate->es_junkFilter = NULL;

	estate->es_output_cid = (CommandId) 0;

	estate->es_result_relations = NULL;
	estate->es_opened_result_relations = NIL;
	estate->es_tuple_routing_result_relations = NIL;
	estate->es_trig_target_relations = NIL;

	estate->es_insert_pending_result_relations = NIL;
	estate->es_insert_pending_modifytables = NIL;

	estate->es_param_list_info = NULL;
	estate->es_param_exec_vals = NULL;

	estate->es_queryEnv = NULL;

	estate->es_query_cxt = qcontext;

	estate->es_tupleTable = NIL;

	estate->es_processed = 0;
	estate->es_total_processed = 0;

	estate->es_top_eflags = 0;
	estate->es_instrument = 0;
	estate->es_finished = false;

	estate->es_exprcontexts = NIL;

	estate->es_subplanstates = NIL;

	estate->es_auxmodifytables = NIL;

	estate->es_per_tuple_exprcontext = NULL;

	estate->es_sourceText = NULL;

	estate->es_use_parallel_mode = false;
	estate->es_parallel_workers_to_launch = 0;
	estate->es_parallel_workers_launched = 0;

	estate->es_jit_flags = 0;
	estate->es_jit = NULL;

	/*
	 * Return the executor state structure
	 */
	MemoryContextSwitchTo(oldcontext);

	return estate;
}

/*
 * ============================================================================
 * 【中文注释】FreeExecutorState —— 释放 EState 及全部执行工作存储
 * ----------------------------------------------------------------------------
 * 函数作用（清理顺序）：
 *   1. 显式关停所有仍在活动的 ExprContext（FreeExprContext）——触发其中
 *      注册的 shutdown 回调（例如终止进行中的集合返回函数），因为这类资源
 *      不单纯是 per-query 上下文里的内存；
 *   2. 释放 JIT 编译上下文（jit_release_context）；
 *   3. 释放分区目录（es_partition_directory，若独立持有）；
 *   4. 删除 per-query 内存上下文——其余一切工作内存（含 EState 自身）
 *      随之一并释放。
 *
 * 职责边界：
 *   - 本函数不负责释放非内存资源（打开的关系、Buffer pin 等，那是
 *     ExecEndPlan 的职责）；但足以满足"仅用于表达式求值、没跑完整计划"
 *     的 EState 使用场景。
 *   - 可在任意内存上下文调用（只要不是待释放的上下文本身）。
 * ============================================================================
 */
void
FreeExecutorState(EState *estate)
{
	/*
	 * Shut down and free any remaining ExprContexts.  We do this explicitly
	 * to ensure that any remaining shutdown callbacks get called (since they
	 * might need to release resources that aren't simply memory within the
	 * per-query memory context).
	 */
	while (estate->es_exprcontexts)
	{
		/*
		 * XXX: seems there ought to be a faster way to implement this than
		 * repeated list_delete(), no?
		 */
		FreeExprContext((ExprContext *) linitial(estate->es_exprcontexts),
						true);
		/* FreeExprContext removed the list link for us */
	}

	/* release JIT context, if allocated */
	if (estate->es_jit)
	{
		jit_release_context(estate->es_jit);
		estate->es_jit = NULL;
	}

	/* release partition directory, if allocated */
	if (estate->es_partition_directory)
	{
		DestroyPartitionDirectory(estate->es_partition_directory);
		estate->es_partition_directory = NULL;
	}

	/*
	 * Free the per-query memory context, thereby releasing all working
	 * memory, including the EState node itself.
	 */
	MemoryContextDelete(estate->es_query_cxt);
}

/*
 * ============================================================================
 * 【中文注释】CreateExprContextInternal —— ExprContext 创建的内部实现
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在 per-query 上下文内创建 ExprContext 节点，并为其创建独立的
 *   per-tuple 内存上下文（ecxt_per_tuple_memory），同时初始化：
 *   - 三个元组槽指针（scantuple/innertuple/outertuple，表达式可引用的
 *     行值来源）；
 *   - 参数指针（es_param_exec_vals / es_param_list_info，与 EState 共享）；
 *   - CASE 求值中间值（caseValue）与域类型求值中间值（domainValue）；
 *   - 回调链表与 EState 反向指针。
 *   最后把自己链入 estate->es_exprcontexts（lcons 头插）——保证 EState
 *   释放时按创建逆序关停。
 *
 * 参数：
 *   estate        - 所属 EState；
 *   min/init/max  - per-tuple 内存上下文的分配器参数（控制块大小，
 *                   由 CreateExprContext / CreateWorkExprContext 传入）。
 *
 * 设计思想：
 *   - 每个计划节点通常一个 ExprContext，另有一个"每输出行"专用上下文
 *     （约束检查等）；各自拥有独立 per-tuple 内存，互不干扰；
 *   - per-tuple 内存是"临时结果回收站"：表达式求值产生的临时对象
 *     全部落在其中，每处理一行 reset 一次（ReScanExprContext），避免
 *     长查询中内存无限增长。
 * ============================================================================
 */
static ExprContext *
CreateExprContextInternal(EState *estate, Size minContextSize,
						  Size initBlockSize, Size maxBlockSize)
{
	ExprContext *econtext;
	MemoryContext oldcontext;

	/* Create the ExprContext node within the per-query memory context */
	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	econtext = makeNode(ExprContext);

	/* Initialize fields of ExprContext */
	econtext->ecxt_scantuple = NULL;
	econtext->ecxt_innertuple = NULL;
	econtext->ecxt_outertuple = NULL;

	econtext->ecxt_per_query_memory = estate->es_query_cxt;

	/*
	 * Create working memory for expression evaluation in this context.
	 */
	econtext->ecxt_per_tuple_memory =
		AllocSetContextCreate(estate->es_query_cxt,
							  "ExprContext",
							  minContextSize,
							  initBlockSize,
							  maxBlockSize);

	econtext->ecxt_param_exec_vals = estate->es_param_exec_vals;
	econtext->ecxt_param_list_info = estate->es_param_list_info;

	econtext->ecxt_aggvalues = NULL;
	econtext->ecxt_aggnulls = NULL;

	econtext->caseValue_datum = (Datum) 0;
	econtext->caseValue_isNull = true;

	econtext->domainValue_datum = (Datum) 0;
	econtext->domainValue_isNull = true;

	econtext->ecxt_estate = estate;

	econtext->ecxt_callbacks = NULL;

	/*
	 * Link the ExprContext into the EState to ensure it is shut down when the
	 * EState is freed.  Because we use lcons(), shutdowns will occur in
	 * reverse order of creation, which may not be essential but can't hurt.
	 */
	estate->es_exprcontexts = lcons(econtext, estate->es_exprcontexts);

	MemoryContextSwitchTo(oldcontext);

	return econtext;
}

/*
 * ============================================================================
 * 【中文注释】CreateExprContext —— 创建标准表达式求值上下文
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   CreateExprContextInternal 的标准配置版（ALLOCSET_DEFAULT_SIZES）。
 *   一次执行通常需要多个 ExprContext：每个计划节点一个 + 每输出行处理
 *   （约束检查等）单独一个。不对调用方内存上下文做任何假设。
 * ============================================================================
 */
ExprContext *
CreateExprContext(EState *estate)
{
	return CreateExprContextInternal(estate, ALLOCSET_DEFAULT_SIZES);
}


/*
 * ============================================================================
 * 【中文注释】CreateWorkExprContext —— 创建"工作型"表达式上下文
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 CreateExprContext 类似，但按 work_mem 比例确定 per-tuple 内存的
 *   最大块尺寸（maxBlockSize = 2 的幂 ≤ work_mem/16），并把最小值/初始块
 *   设为默认初始尺寸。
 *
 * 设计思想：
 *   供内存敏感的工作量（如 Hash/Sort 节点内部用 ExprContext 求值哈希/排序
 *   键）使用：若单个块允许分配过大，一次分配就可能瞬间越过 work_mem 上限，
 *   破坏 work_mem 语义（work_mem 的意义在于限制"单操作内存"）；把块尺寸
 *   钳制在 work_mem/16 量级可让分配器更平滑地逼近上限。
 * ============================================================================
 */
ExprContext *
CreateWorkExprContext(EState *estate)
{
	Size		maxBlockSize;

	maxBlockSize = pg_prevpower2_size_t(work_mem * (Size) 1024 / 16);

	/* But no bigger than ALLOCSET_DEFAULT_MAXSIZE */
	maxBlockSize = Min(maxBlockSize, ALLOCSET_DEFAULT_MAXSIZE);

	/* and no smaller than ALLOCSET_DEFAULT_INITSIZE */
	maxBlockSize = Max(maxBlockSize, ALLOCSET_DEFAULT_INITSIZE);

	return CreateExprContextInternal(estate, ALLOCSET_DEFAULT_MINSIZE,
									 ALLOCSET_DEFAULT_INITSIZE, maxBlockSize);
}

/*
 * ============================================================================
 * 【中文注释】CreateStandaloneExprContext —— 创建"独立"表达式求值环境
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   不依赖 EState 的表达式求值环境：结构体分配在调用方当前上下文，per-tuple
 *   内存挂在调用方当前上下文下。适用于求值"无参数、无子计划、无 Var 引用"
 *   的纯表达式（如 SPI 里的常量折叠）。
 *
 * 设计思想：
 *   - 正因为不与 EState 挂钩，释放责任完全在调用方：用完必须自行释放或
 *     至少调用 ReScanExprContext 触发 shutdown 回调，否则非内存资源可能
 *     泄漏；
 *   - 若强行把元组引用放进 scantuple 字段，理论上也能工作，但违背设计
 *     意图（不鼓励）。
 * ============================================================================
 */
ExprContext *
CreateStandaloneExprContext(void)
{
	ExprContext *econtext;

	/* Create the ExprContext node within the caller's memory context */
	econtext = makeNode(ExprContext);

	/* Initialize fields of ExprContext */
	econtext->ecxt_scantuple = NULL;
	econtext->ecxt_innertuple = NULL;
	econtext->ecxt_outertuple = NULL;

	econtext->ecxt_per_query_memory = CurrentMemoryContext;

	/*
	 * Create working memory for expression evaluation in this context.
	 */
	econtext->ecxt_per_tuple_memory =
		AllocSetContextCreate(CurrentMemoryContext,
							  "ExprContext",
							  ALLOCSET_DEFAULT_SIZES);

	econtext->ecxt_param_exec_vals = NULL;
	econtext->ecxt_param_list_info = NULL;

	econtext->ecxt_aggvalues = NULL;
	econtext->ecxt_aggnulls = NULL;

	econtext->caseValue_datum = (Datum) 0;
	econtext->caseValue_isNull = true;

	econtext->domainValue_datum = (Datum) 0;
	econtext->domainValue_isNull = true;

	econtext->ecxt_estate = NULL;

	econtext->ecxt_callbacks = NULL;

	return econtext;
}

/*
 * ============================================================================
 * 【中文注释】FreeExprContext —— 释放表达式求值上下文
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   1. 调用所有已注册的 shutdown 回调（ShutdownExprContext）；
 *   2. 删除 per-tuple 内存上下文——注意：此前算出的所有传引用（pass-by-
 *      reference）表达式结果随之一并失效！调用方不得再引用旧结果；
 *   3. 若归属某 EState，从 es_exprcontexts 链表摘除自己；
 *   4. pfree 结构体本身。
 *
 * 参数：
 *   isCommit - true=正常清理（回调会被调用）；false=错误清理路径（只释放
 *              内存、不调用回调——错误处理期间调用回调可能不安全/无意义）。
 * ============================================================================
 */
void
FreeExprContext(ExprContext *econtext, bool isCommit)
{
	EState	   *estate;

	/* Call any registered callbacks */
	ShutdownExprContext(econtext, isCommit);
	/* And clean up the memory used */
	MemoryContextDelete(econtext->ecxt_per_tuple_memory);
	/* Unlink self from owning EState, if any */
	estate = econtext->ecxt_estate;
	if (estate)
		estate->es_exprcontexts = list_delete_ptr(estate->es_exprcontexts,
												  econtext);
	/* And delete the ExprContext node */
	pfree(econtext);
}

/*
 * ============================================================================
 * 【中文注释】ReScanExprContext —— 重置表达式上下文（重扫前的准备）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   计划节点重扫描（ReScan）前调用：先执行所有 shutdown 回调（半途而废
 *   的集合返回函数必须被取消），再重置 per-tuple 内存。
 *
 * 设计思想：
 *   与 FreeExprContext 的区别：只"清空"不"销毁"，上下文可继续复用。
 *   （对调用方内存上下文不做假设。）
 * ============================================================================
 */
void
ReScanExprContext(ExprContext *econtext)
{
	/* Call any registered callbacks */
	ShutdownExprContext(econtext, true);
	/* And clean up the memory used */
	MemoryContextReset(econtext->ecxt_per_tuple_memory);
}

/*
 * ============================================================================
 * 【中文注释】MakePerTupleExprContext —— 惰性创建"每输出行"表达式上下文
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回 EState 的每输出行专用 ExprContext（首次调用时创建并缓存到
 *   es_per_tuple_exprcontext）。通常经由 GetPerTupleExprContext 宏间接调用。
 *
 * 业务场景：
 *   约束检查、WITH CHECK OPTION 求值等"处理每一行输出"的工作统一使用该
 *   上下文；ExecutePlan 主循环每行开头 ResetPerTupleExprContext 重置它，
 *   保证行间不累积。
 * ============================================================================
 */
ExprContext *
MakePerTupleExprContext(EState *estate)
{
	if (estate->es_per_tuple_exprcontext == NULL)
		estate->es_per_tuple_exprcontext = CreateExprContext(estate);

	return estate->es_per_tuple_exprcontext;
}


/* ----------------------------------------------------------------
 *				 miscellaneous node-init support functions
 *
 * Note: all of these are expected to be called with CurrentMemoryContext
 * equal to the per-query memory context.
 * ----------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】ExecAssignExprContext —— 为计划节点装配表达式上下文
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   初始化 planstate->ps_ExprContext。只有需要 ExecQual / ExecProject 的
 *   节点才必须调用（这两类求值都要求 econtext）；不涉及表达式求值的节点
 *   可跳过。
 * 注意：调用前提是 CurrentMemoryContext 为 per-query 上下文。
 * ============================================================================
 */
void
ExecAssignExprContext(EState *estate, PlanState *planstate)
{
	planstate->ps_ExprContext = CreateExprContext(estate);
}

/*
 * ============================================================================
 * 【中文注释】ExecGetResultType —— 获取节点输出元组的描述符
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回节点结果元组描述符（ps_ResultTupleDesc），供上层（如父节点/主循环/
 *   InitPlan 的 tupType 获取）了解该节点输出行的结构。
 * ============================================================================
 */
TupleDesc
ExecGetResultType(PlanState *planstate)
{
	return planstate->ps_ResultTupleDesc;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetResultSlotOps / ExecGetCommonSlotOps / ExecGetCommonChildSlotOps
 * ----------------------------------------------------------------------------
 * 函数作用（三连配套）：
 *   - ExecGetResultSlotOps：返回节点结果槽的实现类型（TTSOps*）及其是否
 *     固定（fixed：该节点所有输出槽一定是此类型）。节点显式设置过
 *     （resultopsset）则用设置值；否则回退到其结果槽的 tts_ops；连结果槽
 *     都没有则默认虚拟槽 TTSOpsVirtual；
 *   - ExecGetCommonSlotOps：给定一组 PlanState，若它们全部输出"同一固定
 *     槽类型"，返回该类型；否则返回 NULL（无法共用优化路径）；
 *   - ExecGetCommonChildSlotOps：对某节点的外/内子节点执行上述判断。
 *
 * 业务场景：
 *   Append/MergeAppend 等"多子节点"节点希望确定所有子节点是否产出同构
 *   槽（如都产 heap 槽），以便一次性分配统一的输出槽并做批量拷贝优化
 *   （avoid per-child slot conversion）。
 * ============================================================================
 */
const TupleTableSlotOps *
ExecGetResultSlotOps(PlanState *planstate, bool *isfixed)
{
	if (planstate->resultopsset && planstate->resultops)
	{
		if (isfixed)
			*isfixed = planstate->resultopsfixed;
		return planstate->resultops;
	}

	if (isfixed)
	{
		if (planstate->resultopsset)
			*isfixed = planstate->resultopsfixed;
		else if (planstate->ps_ResultTupleSlot)
			*isfixed = TTS_FIXED(planstate->ps_ResultTupleSlot);
		else
			*isfixed = false;
	}

	if (!planstate->ps_ResultTupleSlot)
		return &TTSOpsVirtual;

	return planstate->ps_ResultTupleSlot->tts_ops;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetCommonSlotOps —— 求多个子计划的"公共元组槽类型"
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   依次查询传入的全部 PlanState 的结果槽类型；仅当所有子计划返回
 *   相同的"固定"槽类型时才返回对应 tts_ops，否则返回 NULL。
 *
 * 固定（fixed）的含义：槽类型在生产阶段就已确定、不再随行变化。若任一
 * 子计划槽类型不固定（或各不相同），都无法共用一套槽描述，返回 NULL。
 *
 * 业务场景：
 *   nodeAppend / nodeMergeAppend 等混合节点需要知道所有子计划是否共用
 *   同一槽类型，从而决定能否直接复用父节点槽、跳过打包/解包转换。
 * ============================================================================
 */
const TupleTableSlotOps *
ExecGetCommonSlotOps(PlanState **planstates, int nplans)
{
	const TupleTableSlotOps *result;
	bool		isfixed;

	if (nplans <= 0)
		return NULL;
	result = ExecGetResultSlotOps(planstates[0], &isfixed);
	if (!isfixed)
		return NULL;
	for (int i = 1; i < nplans; i++)
	{
		const TupleTableSlotOps *thisops;

		thisops = ExecGetResultSlotOps(planstates[i], &isfixed);
		if (!isfixed)
			return NULL;
		if (result != thisops)
			return NULL;
	}
	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetCommonChildSlotOps —— 子计划的公共槽类型（便捷封装）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   ExecGetCommonSlotOps 的便捷封装：直接传入 ps 的标准左右子计划
 *   （outerPlan / innerPlan，可能为 NULL）构成的数组，求公共槽类型。
 *
 * 设计要点：
 *   - 子计划为 NULL 时其结果槽视为"未初始化"；ExecGetResultSlotOps 对
 *     无结果槽的计划返回 TTSOpsVirtual（虚拟槽）。深究历史可见：早期
 *     实现里 NULL 子计划会让数组元素为 NULL 导致直接行为异常，因此这里
 *     只是把 NULL 子计划与"返回虚拟槽"视为等价，从而允许简化调用。
 * ============================================================================
 */
const TupleTableSlotOps *
ExecGetCommonChildSlotOps(PlanState *ps)
{
	PlanState  *planstates[2];

	planstates[0] = outerPlanState(ps);
	planstates[1] = innerPlanState(ps);
	return ExecGetCommonSlotOps(planstates, 2);
}


/*
 * ============================================================================
 * 【中文注释】ExecAssignProjectionInfo —— 构建节点投影信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   用节点的 targetlist 构建投影（ProjectionInfo）：把子节点输出的行"投影"
 *   成节点的结果行。投影含义：按 targetlist 逐列计算输出列（含表达式求
 *   值、列重排、列裁剪）。
 *
 * 参数：
 *   planstate - 目标节点（从 plan->targetlist 取表达式列表）；
 *   inputDesc - 输入行的描述符——关系扫描类节点必须传（获取列号映射），
 *               上层非扫描节点可传 NULL。
 * ============================================================================
 */
void
ExecAssignProjectionInfo(PlanState *planstate,
						 TupleDesc inputDesc)
{
	planstate->ps_ProjInfo =
		ExecBuildProjectionInfo(planstate->plan->targetlist,
								planstate->ps_ExprContext,
								planstate->ps_ResultTupleSlot,
								planstate,
								inputDesc);
}


/*
 * ============================================================================
 * 【中文注释】ExecConditionalAssignProjectionInfo —— 有需要才建投影
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 ExecAssignProjectionInfo 相同，但如果"不需要投影"则直接存 NULL。
 *
 * 不需要投影的判定：targetlist 恰好按顺序引用 varno 的每一列（identity
 *   mapping），即子节点输出的行结构与目标行完全一致（tlist_matches_tupdesc
 *   判定）——此时直接复用子节点输出槽（scanops），省掉一次逐列拷贝/求值。
 *
 * 设计思想（性能优化）：
 *   - 这是执行器重要的捷径优化：投影是逐行开销，能省则省；
 *   - 注意判定必须保守（宁可不省，不可省错）：
 *     * 表含丢弃列（attisdropped）→ 不省（列号对不上）；
 *     * 表含缺失值列（atthasmissing，如 ALTER TABLE ADD COLUMN 带默认值，
 *       部分旧行没有该列值）→ 不省（需要补值逻辑）；
 *     * 类型不严格匹配（typmod 不一致，允许 Var 用 typmod=-1）→ 不省。
 * ============================================================================
 */
void
ExecConditionalAssignProjectionInfo(PlanState *planstate, TupleDesc inputDesc,
									int varno)
{
	if (tlist_matches_tupdesc(planstate,
							  planstate->plan->targetlist,
							  varno,
							  inputDesc))
	{
		planstate->ps_ProjInfo = NULL;
		planstate->resultopsset = planstate->scanopsset;
		planstate->resultopsfixed = planstate->scanopsfixed;
		planstate->resultops = planstate->scanops;
	}
	else
	{
		if (!planstate->ps_ResultTupleSlot)
		{
			ExecInitResultSlot(planstate, &TTSOpsVirtual);
			planstate->resultops = &TTSOpsVirtual;
			planstate->resultopsfixed = true;
			planstate->resultopsset = true;
		}
		ExecAssignProjectionInfo(planstate, inputDesc);
	}
}

/*
 * ============================================================================
 * 【中文注释】tlist_matches_tupdesc —— 判定"无需投影直接透传"
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查 targetlist 是否恰好以"顺序、一一对应、类型相符"的方式引用
 *   varno 关系/子查询的每一列（Identity mapping）。
 *
 * 返回 true 表示：整行原样传递即可，不需要任何列级加工。
 *
 * 判定不通过的典型情况：
 *   - tlist 比表列多/少（长度不匹配）；
 *   - 某条目不是简单 Var（含表达式 → 必须投影）；
 *   - Var 列号不按 1..n 顺序出现；
 *   - 表含丢弃列（占位仍占列号，但值无效）；
 *   - 表含缺失值列（需要按缺失值补填）；
 *   - 类型/typmod 不一致（Union 等场景 Var 可能是 typmod=-1，合法但需
 *     转换层处理）。
 * ============================================================================
 */
static bool
tlist_matches_tupdesc(PlanState *ps, List *tlist, int varno, TupleDesc tupdesc)
{
	int			numattrs = tupdesc->natts;
	int			attrno;
	ListCell   *tlist_item = list_head(tlist);

	/* Check the tlist attributes */
	for (attrno = 1; attrno <= numattrs; attrno++)
	{
		Form_pg_attribute att_tup = TupleDescAttr(tupdesc, attrno - 1);
		Var		   *var;

		if (tlist_item == NULL)
			return false;		/* tlist too short */
		var = (Var *) ((TargetEntry *) lfirst(tlist_item))->expr;
		if (!var || !IsA(var, Var))
			return false;		/* tlist item not a Var */
		/* if these Asserts fail, planner messed up */
		Assert(var->varno == varno);
		Assert(var->varlevelsup == 0);
		if (var->varattno != attrno)
			return false;		/* out of order */
		if (att_tup->attisdropped)
			return false;		/* table contains dropped columns */
		if (att_tup->atthasmissing)
			return false;		/* table contains cols with missing values */

		/*
		 * Note: usually the Var's type should match the tupdesc exactly, but
		 * in situations involving unions of columns that have different
		 * typmods, the Var may have come from above the union and hence have
		 * typmod -1.  This is a legitimate situation since the Var still
		 * describes the column, just not as exactly as the tupdesc does. We
		 * could change the planner to prevent it, but it'd then insert
		 * projection steps just to convert from specific typmod to typmod -1,
		 * which is pretty silly.
		 */
		if (var->vartype != att_tup->atttypid ||
			(var->vartypmod != att_tup->atttypmod &&
			 var->vartypmod != -1))
			return false;		/* type mismatch */

		tlist_item = lnext(tlist, tlist_item);
	}

	if (tlist_item)
		return false;			/* tlist too long */

	return true;
}


/* ----------------------------------------------------------------
 *				  Scan node support
 * ----------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】ExecAssignScanType / ExecCreateScanSlotFromOuterPlan
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   - ExecAssignScanType：给扫描节点的扫描槽（ss_ScanTupleSlot）设置元组
 *     描述符（表结构变化的场景需要运行时更新）；
 *   - ExecCreateScanSlotFromOuterPlan：从外层计划的结果描述符建立扫描槽
 *     （子查询扫描等"消费上层输出"的扫描节点使用）。
 * ============================================================================
 */
void
ExecAssignScanType(ScanState *scanstate, TupleDesc tupDesc)
{
	TupleTableSlot *slot = scanstate->ss_ScanTupleSlot;

	ExecSetSlotDescriptor(slot, tupDesc);
}

/* ----------------
 *		ExecCreateScanSlotFromOuterPlan
 * ----------------
 */
void
ExecCreateScanSlotFromOuterPlan(EState *estate,
								ScanState *scanstate,
								const TupleTableSlotOps *tts_ops)
{
	PlanState  *outerPlan;
	TupleDesc	tupDesc;

	outerPlan = outerPlanState(scanstate);
	tupDesc = ExecGetResultType(outerPlan);

	ExecInitScanTupleSlot(estate, scanstate, tupDesc, tts_ops, 0);
}

/*
 * ============================================================================
 * 【中文注释】ExecRelationIsTargetRelation —— 判断关系是否为查询的目标关系
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按范围表索引判断某关系是否在 resultRelationRelids 中（即是否为
 *   INSERT/UPDATE/DELETE/MERGE 的目标）。核心代码已不用，保留给 FDW 判断
 *   外部表是否为目标关系。
 * ============================================================================
 */
bool
ExecRelationIsTargetRelation(EState *estate, Index scanrelid)
{
	return bms_is_member(scanrelid, estate->es_plannedstmt->resultRelationRelids);
}

/*
 * ============================================================================
 * 【中文注释】ScanRelIsReadOnly —— 判断扫描关系在本查询中是否只读
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回 true 当且仅当该扫描关系既不在结果关系集合（不会被 DML 修改），
 *   也没有行标记（不会被 SELECT FOR UPDATE/SHARE 锁定）。
 *
 * 精度说明（非完美）：
 *   - INSERT ... SELECT 同一张表：扫描侧不加入 resultRelationRelids，
 *     会被误报为只读；
 *   - 当查询中任意关系带修改型行标记时，其他所有关系都会得到
 *     ROW_MARK_REFERENCE 行标记，从而被误报为非只读。
 * 用途：PostgreSQL 历史遗留/调试与扩展探测用，见调用方注释。
 * ============================================================================
 */
bool
ScanRelIsReadOnly(ScanState *ss)
{
	Index		scanrelid = ((Scan *) ss->ps.plan)->scanrelid;
	PlannedStmt *pstmt = ss->ps.state->es_plannedstmt;

	return !bms_is_member(scanrelid, pstmt->resultRelationRelids) &&
		!bms_is_member(scanrelid, pstmt->rowMarkRelids);
}

/*
 * ============================================================================
 * 【中文注释】ExecOpenScanRelation —— 打开基础扫描节点的目标关系
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   节点 ExecInitXXX 期间调用：打开 (scanrelid) 对应的堆关系。
 *   额外防御：非 EXPLAIN/WITH_NO_DATA 模式下，若关系不可扫描（未填充的
 *   物化视图），直接报错 "materialized view ... has not been populated"，
 *   提示用户先 REFRESH。
 *
 * 参数：
 *   estate    - 执行状态；scanrelid - 范围表索引；eflags - 执行标志。
 * ============================================================================
 */
Relation
ExecOpenScanRelation(EState *estate, Index scanrelid, int eflags)
{
	Relation	rel;

	/* Open the relation. */
	rel = ExecGetRangeTableRelation(estate, scanrelid, false);

	/*
	 * Complain if we're attempting a scan of an unscannable relation, except
	 * when the query won't actually be run.  This is a slightly klugy place
	 * to do this, perhaps, but there is no better place.
	 */
	if ((eflags & (EXEC_FLAG_EXPLAIN_ONLY | EXEC_FLAG_WITH_NO_DATA)) == 0 &&
		!RelationIsScannable(rel))
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("materialized view \"%s\" has not been populated",
						RelationGetRelationName(rel)),
				 errhint("Use the REFRESH MATERIALIZED VIEW command.")));

	return rel;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitRangeTable —— 初始化执行器的范围表相关数据
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   记录范围表列表与权限信息列表，设置 es_range_table_size，并把调用方
 *   传入的 es_unpruned_relids（未被裁剪的关系 RTI 位图，初始由计划器给，
 *   之后 ExecDoInitialPruning 可能补充未裁剪的叶分区）保存下来。
 *   同时分配两个与 RTE 平行的数组：
 *   - es_relations[]：每个 RTE 对应的已打开 Relation（初始全 NULL，按需
 *     惰性打开）；
 *   - es_result_relations[] / es_rowmarks[]：按需才分配（先置 NULL）。
 * ============================================================================
 */
void
ExecInitRangeTable(EState *estate, List *rangeTable, List *permInfos,
				   Bitmapset *unpruned_relids)
{
	/* Remember the range table List as-is */
	estate->es_range_table = rangeTable;

	/* ... and the RTEPermissionInfo List too */
	estate->es_rteperminfos = permInfos;

	/* Set size of associated arrays */
	estate->es_range_table_size = list_length(rangeTable);

	/*
	 * Initialize the bitmapset of RT indexes (es_unpruned_relids)
	 * representing relations that will be scanned during execution. This set
	 * is initially populated by the caller and may be extended later by
	 * ExecDoInitialPruning() to include RT indexes of unpruned leaf
	 * partitions.
	 */
	estate->es_unpruned_relids = unpruned_relids;

	/*
	 * Allocate an array to store an open Relation corresponding to each
	 * rangetable entry, and initialize entries to NULL.  Relations are opened
	 * and stored here as needed.
	 */
	estate->es_relations = (Relation *)
		palloc0(estate->es_range_table_size * sizeof(Relation));

	/*
	 * es_result_relations and es_rowmarks are also parallel to
	 * es_range_table, but are allocated only if needed.
	 */
	estate->es_result_relations = NULL;
	estate->es_rowmarks = NULL;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetRangeTableRelation —— 打开（或复用）范围表项对应的关系
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回 rti 对应 RTE 的 Relation，首次访问时惰性打开并缓存到
 *   es_relations[rti-1]，之后直接复用；由 ExecEndPlan 统一关闭。
 *
 * 参数：
 *   isResultRel - 是否作为结果关系打开（结果关系允许是"已被分区裁剪"的，
 *                 扫描关系绝不允许）。
 *
 * 加锁策略（并行语义是关键）：
 *   - 普通后端：表锁在执行开始前已由上层获取（AcquireExecutorLocks），
 *     这里 NoLock 打开即可，仅用 Assert 校验锁级别足够（对行级锁较弱的
 *     rellockmode 场景不做强校验，因为 table_open 本身断言持有某种锁）；
 *   - 并行 worker：必须自行以 rte->rellockmode 加本地锁打开——父进程可能
 *     先于 worker 结束，worker 必须独立持锁保证行为正常。
 * 防护：isResultRel=false 时若 rti 不在 es_unpruned_relids（被裁剪），
 * 直接 ERROR（"trying to open a pruned relation"）。
 * ============================================================================
 */
Relation
ExecGetRangeTableRelation(EState *estate, Index rti, bool isResultRel)
{
	Relation	rel;

	Assert(rti > 0 && rti <= estate->es_range_table_size);

	if (!isResultRel && !bms_is_member(rti, estate->es_unpruned_relids))
		elog(ERROR, "trying to open a pruned relation");

	rel = estate->es_relations[rti - 1];
	if (rel == NULL)
	{
		/* First time through, so open the relation */
		RangeTblEntry *rte = exec_rt_fetch(rti, estate);

		Assert(rte->rtekind == RTE_RELATION);

		if (!IsParallelWorker())
		{
			/*
			 * In a normal query, we should already have the appropriate lock,
			 * but verify that through an Assert.  Since there's already an
			 * Assert inside table_open that insists on holding some lock, it
			 * seems sufficient to check this only when rellockmode is higher
			 * than the minimum.
			 */
			rel = table_open(rte->relid, NoLock);
			Assert(rte->rellockmode == AccessShareLock ||
				   CheckRelationLockedByMe(rel, rte->rellockmode, false));
		}
		else
		{
			/*
			 * If we are a parallel worker, we need to obtain our own local
			 * lock on the relation.  This ensures sane behavior in case the
			 * parent process exits before we do.
			 */
			rel = table_open(rte->relid, rte->rellockmode);
		}

		estate->es_relations[rti - 1] = rel;
	}

	return rel;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitResultRelation —— 初始化结果关系并登记
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   打开 rti 指向的关系，调用 InitResultRelInfo 填充 ResultRelInfo，然后：
 *   1. 存入 es_result_relations[rti-1]（按 RTI 快速访问）；
 *   2. 追加到 es_opened_result_relations 链表——执行结束关闭时只需遍历
 *      链表而非整个数组（多数查询结果关系极少，数组绝大多数为 NULL）。
 *
 * 业务场景：
 *   被 ExecInitModifyTable 等调用，为 INSERT/UPDATE/DELETE/MERGE 的目标
 *   关系建立执行期上下文。
 * ============================================================================
 */
void
ExecInitResultRelation(EState *estate, ResultRelInfo *resultRelInfo,
					   Index rti)
{
	Relation	resultRelationDesc;

	resultRelationDesc = ExecGetRangeTableRelation(estate, rti, true);
	InitResultRelInfo(resultRelInfo,
					  resultRelationDesc,
					  rti,
					  NULL,
					  estate->es_instrument);

	if (estate->es_result_relations == NULL)
		estate->es_result_relations = (ResultRelInfo **)
			palloc0(estate->es_range_table_size * sizeof(ResultRelInfo *));
	estate->es_result_relations[rti - 1] = resultRelInfo;

	/*
	 * Saving in the list allows to avoid needlessly traversing the whole
	 * array when only a few of its entries are possibly non-NULL.
	 */
	estate->es_opened_result_relations =
		lappend(estate->es_opened_result_relations, resultRelInfo);
}

/*
 * ============================================================================
 * 【中文注释】UpdateChangedParamSet —— 把"已变化的参数"并入节点变更集合
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   当 Executor 某处求得新的参数值后，把"真正影响本节点"的那部分参数
 *   位图并入 node->chgParam。下一轮 ExecProcNode 时节点看到 chgParam 非空
 *   会触发 ReScan（重新扫描），从而基于新参数重新计算。
 *
 * 设计思想（参数依赖裁剪）：
 *   节点只依赖自己 allParam 集合中的参数（计划器预计算）；取交集即可
 *   精确过滤无关参数，避免无谓的重扫描。chgParam 采用并集累积，保证
 *   多参数连续变更都得到反映。
 * ============================================================================
 */
void
UpdateChangedParamSet(PlanState *node, Bitmapset *newchg)
{
	Bitmapset  *parmset;

	/*
	 * The plan node only depends on params listed in its allParam set. Don't
	 * include anything else into its chgParam set.
	 */
	parmset = bms_intersect(node->plan->allParam, newchg);
	node->chgParam = bms_join(node->chgParam, parmset);
}

/*
 * ============================================================================
 * 【中文注释】executor_errposition —— 报告执行期错误的语法位置
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   供 ereport() 内部使用（返回 errposition 结果），把解析树中记录的
 *   location（源字符串的字节偏移）转换为 1 起始的字符位置报告给客户端。
 *   无法定位时返回 0（无位置信息）。
 *
 * 设计思想：
 *   - 解析阶段存储"字节偏移"而非字符位置：正常执行时定位计算是完全多余
 *     的开销，出错才转换（pg_mbstrlen_with_len 按多字节安全计数）；
 *   - 需要 es_sourceText（原始 SQL 文本）才能换算；EXPLAIN/无文本场景
 *     直接放弃。
 * ============================================================================
 */
int
executor_errposition(EState *estate, int location)
{
	int			pos;

	/* No-op if location was not provided */
	if (location < 0)
		return 0;
	/* Can't do anything if source text is not available */
	if (estate == NULL || estate->es_sourceText == NULL)
		return 0;
	/* Convert offset to character number */
	pos = pg_mbstrlen_with_len(estate->es_sourceText, location) + 1;
	/* And pass it to the ereport mechanism */
	return errposition(pos);
}

/*
 * ============================================================================
 * 【中文注释】RegisterExprContextCallback / UnregisterExprContextCallback
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在 ExprContext 上登记/注销"shutdown 回调"：
 *   - 登记：把 (function, arg) 压入 ecxt_callbacks 链表头（后登记先调用）；
 *   - 注销：按函数与参数同时匹配删除全部对应条目。
 *
 * 业务背景：
 *   ExprContext 被删除或重置（ReScan/Free）时回调会被触发，用于释放
 *   "表达式求值期间占用的非纯内存资源"——最典型的是集合返回函数（SRF）：
 *   求值到一半被中断时，若不取消其内部状态（如文件句柄/游标），会造成
 *   泄漏。
 *
 * 注意：出错（ereport ERROR）导致的清理路径不会调用回调（见
 * ShutdownExprContext 的 isCommit 语义）。
 * 分配位置：回调节点分配在 per-query 内存（随查询释放）。
 * ============================================================================
 */
void
RegisterExprContextCallback(ExprContext *econtext,
							ExprContextCallbackFunction function,
							Datum arg)
{
	ExprContext_CB *ecxt_callback;

	/* Save the info in appropriate memory context */
	ecxt_callback = (ExprContext_CB *)
		MemoryContextAlloc(econtext->ecxt_per_query_memory,
						   sizeof(ExprContext_CB));

	ecxt_callback->function = function;
	ecxt_callback->arg = arg;

	/* link to front of list for appropriate execution order */
	ecxt_callback->next = econtext->ecxt_callbacks;
	econtext->ecxt_callbacks = ecxt_callback;
}

/*
 * ============================================================================
 * 【中文注释】UnregisterExprContextCallback —— 注销 shutdown 回调
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从 ecxt_callbacks 链表中删除所有 (function,arg) 完全匹配的条目并释放。
 *   用于"已不再需要该回调"的场景（例如目标函数已完成、其资源已回收）。
 * ============================================================================
 */
void
UnregisterExprContextCallback(ExprContext *econtext,
							  ExprContextCallbackFunction function,
							  Datum arg)
{
	ExprContext_CB **prev_callback;
	ExprContext_CB *ecxt_callback;

	prev_callback = &econtext->ecxt_callbacks;

	while ((ecxt_callback = *prev_callback) != NULL)
	{
		if (ecxt_callback->function == function && ecxt_callback->arg == arg)
		{
			*prev_callback = ecxt_callback->next;
			pfree(ecxt_callback);
		}
		else
			prev_callback = &ecxt_callback->next;
	}
}

/*
 * ============================================================================
 * 【中文注释】ShutdownExprContext —— 执行/清理 ExprContext 的全部回调
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按"后登记先调用"的顺序逐个执行回调并释放回调节点（同时清空链表——
 *   重置（rescan）场景下链表必须清空，避免重复触发）。
 *
 * 参数：
 *   isCommit - true：真正调用回调函数（正常清理）；
 *              false：仅清掉链表不调用（错误清理路径，见 FreeExprContext）。
 *
 * 设计思想：
 *   在 per-tuple 内存上下文中执行回调：回调自身可能泄漏的内存随下一次
 *   reset 被回收，保证整体可控。
 * ============================================================================
 */
static void
ShutdownExprContext(ExprContext *econtext, bool isCommit)
{
	ExprContext_CB *ecxt_callback;
	MemoryContext oldcontext;

	/* Fast path in normal case where there's nothing to do. */
	if (econtext->ecxt_callbacks == NULL)
		return;

	/*
	 * Call the callbacks in econtext's per-tuple context.  This ensures that
	 * any memory they might leak will get cleaned up.
	 */
	oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

	/*
	 * Call each callback function in reverse registration order.
	 */
	while ((ecxt_callback = econtext->ecxt_callbacks) != NULL)
	{
		econtext->ecxt_callbacks = ecxt_callback->next;
		if (isCommit)
			ecxt_callback->function(ecxt_callback->arg);
		pfree(ecxt_callback);
	}

	MemoryContextSwitchTo(oldcontext);
}

/*
 * ============================================================================
 * 【中文注释】GetAttributeByName / GetAttributeByNum —— 从元组中取属性值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从 HeapTupleHeader（C 函数收到的 record/tuple 参数）中按列名或列号
 *   提取属性值。例如 SQL 函数 f(EMP) 的 C 实现可通过 GetAttributeByNum 读取
 *   具体列。
 *
 * 参数：
 *   tuple   - 元组头（NULL 时返回 isNull=true、Datum 0，兼容历史行为）；
 *   attname / attrno - 列名/列号；
 *   isNull  - 输出：该列为 NULL 则置 true。
 *
 * 设计思想：
 *   - 两步取数：先按元组头内的 typeid/typmod 查其行类型描述符
 *     （lookup_rowtype_tupdesc），按名/号定位 attno，再用 heap_getattr
 *     做物理解包；
 *   - 性能较弱：每次调用都做 typcache 查找——适合"低频取列"，不适合
 *     热路径（热路径应把列号缓存下来后用 heap_getattr 直取）；
 *   - 将 HeapTupleHeader 包装成 HeapTuple 供 heap_getattr 使用（同时把
 *     t_self/t_tableOid 置无效值以防用户探测系统列）。
 * ============================================================================
 */
Datum
GetAttributeByName(HeapTupleHeader tuple, const char *attname, bool *isNull)
{
	AttrNumber	attrno;
	Datum		result;
	Oid			tupType;
	int32		tupTypmod;
	TupleDesc	tupDesc;
	HeapTupleData tmptup;
	int			i;

	if (attname == NULL)
		elog(ERROR, "invalid attribute name");

	if (isNull == NULL)
		elog(ERROR, "a NULL isNull pointer was passed");

	if (tuple == NULL)
	{
		/* Kinda bogus but compatible with old behavior... */
		*isNull = true;
		return (Datum) 0;
	}

	tupType = HeapTupleHeaderGetTypeId(tuple);
	tupTypmod = HeapTupleHeaderGetTypMod(tuple);
	tupDesc = lookup_rowtype_tupdesc(tupType, tupTypmod);

	attrno = InvalidAttrNumber;
	for (i = 0; i < tupDesc->natts; i++)
	{
		Form_pg_attribute att = TupleDescAttr(tupDesc, i);

		if (namestrcmp(&(att->attname), attname) == 0)
		{
			attrno = att->attnum;
			break;
		}
	}

	if (attrno == InvalidAttrNumber)
		elog(ERROR, "attribute \"%s\" does not exist", attname);

	/*
	 * heap_getattr needs a HeapTuple not a bare HeapTupleHeader.  We set all
	 * the fields in the struct just in case user tries to inspect system
	 * columns.
	 */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
	ItemPointerSetInvalid(&(tmptup.t_self));
	tmptup.t_tableOid = InvalidOid;
	tmptup.t_data = tuple;

	result = heap_getattr(&tmptup,
						  attrno,
						  tupDesc,
						  isNull);

	ReleaseTupleDesc(tupDesc);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】GetAttributeByNum —— 按列号版属性提取
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 GetAttributeByName 等价，但按列号访问（免去属性名遍历），语义与
 *   注意事项完全相同：先查行类型描述符、再 heap_getattr 解包。
 * ============================================================================
 */
Datum
GetAttributeByNum(HeapTupleHeader tuple,
				  AttrNumber attrno,
				  bool *isNull)
{
	Datum		result;
	Oid			tupType;
	int32		tupTypmod;
	TupleDesc	tupDesc;
	HeapTupleData tmptup;

	if (!AttributeNumberIsValid(attrno))
		elog(ERROR, "invalid attribute number %d", attrno);

	if (isNull == NULL)
		elog(ERROR, "a NULL isNull pointer was passed");

	if (tuple == NULL)
	{
		/* Kinda bogus but compatible with old behavior... */
		*isNull = true;
		return (Datum) 0;
	}

	tupType = HeapTupleHeaderGetTypeId(tuple);
	tupTypmod = HeapTupleHeaderGetTypMod(tuple);
	tupDesc = lookup_rowtype_tupdesc(tupType, tupTypmod);

	/*
	 * heap_getattr needs a HeapTuple not a bare HeapTupleHeader.  We set all
	 * the fields in the struct just in case user tries to inspect system
	 * columns.
	 */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
	ItemPointerSetInvalid(&(tmptup.t_self));
	tmptup.t_tableOid = InvalidOid;
	tmptup.t_data = tuple;

	result = heap_getattr(&tmptup,
						  attrno,
						  tupDesc,
						  isNull);

	ReleaseTupleDesc(tupDesc);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecTargetListLength / ExecCleanTargetListLength —— 目标列表长度
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   - ExecTargetListLength：含 resjunk 项的全长（历史上还处理过 fjoin 合并
 *     投影，现已简化）；
 *   - ExecCleanTargetListLength：仅统计非 resjunk（对用户可见）项的数量。
 * 用途：上层用于结果元组列数推导、投影建立等场景。
 * ============================================================================
 */
int
ExecTargetListLength(List *targetlist)
{
	/* This used to be more complex, but fjoins are dead */
	return list_length(targetlist);
}

/*
 * ============================================================================
 * 【中文注释】ExecCleanTargetListLength —— 非内部列的目标列表长度
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   统计 targetlist 中非 resjunk（非内部）条目数。
 * ============================================================================
 */
int
ExecCleanTargetListLength(List *targetlist)
{
	int			len = 0;
	ListCell   *tl;

	foreach(tl, targetlist)
	{
		TargetEntry *curTle = lfirst_node(TargetEntry, tl);

		if (!curTle->resjunk)
			len++;
	}
	return len;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetTriggerOldSlot / ExecGetTriggerNewSlot / ExecGetReturningSlot
 * ----------------------------------------------------------------------------
 * 函数作用（三胞胎，惰性创建模式）：
 *   - ExecGetTriggerOldSlot：返回结果的 OLD 元组槽；
 *   - ExecGetTriggerNewSlot：返回结果的 NEW 元组槽；
 *   - ExecGetReturningSlot：返回 RETURNING 投影计算用的元组槽。
 *   三者都在首次调用时按关系行类型惰性创建（table_slot_callbacks 决定槽
 *   实现类型），缓存进 ResultRelInfo，之后直接复用。
 *
 * 业务场景：
 *   nodeModifyTable 执行触发器（OLD/NEW 行必须放进"触发器兼容"的槽里，
 *   否则触发器内部按行类型解包可能出错）与 RETURNING 求值时使用。
 * ============================================================================
 */
TupleTableSlot *
ExecGetTriggerOldSlot(EState *estate, ResultRelInfo *relInfo)
{
	if (relInfo->ri_TrigOldSlot == NULL)
	{
		Relation	rel = relInfo->ri_RelationDesc;
		MemoryContext oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

		relInfo->ri_TrigOldSlot =
			ExecInitExtraTupleSlot(estate,
								   RelationGetDescr(rel),
								   table_slot_callbacks(rel));

		MemoryContextSwitchTo(oldcontext);
	}

	return relInfo->ri_TrigOldSlot;
}

/*
 * Return a relInfo's tuple slot for a trigger's NEW tuples.
 */
TupleTableSlot *
ExecGetTriggerNewSlot(EState *estate, ResultRelInfo *relInfo)
{
	if (relInfo->ri_TrigNewSlot == NULL)
	{
		Relation	rel = relInfo->ri_RelationDesc;
		MemoryContext oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

		relInfo->ri_TrigNewSlot =
			ExecInitExtraTupleSlot(estate,
								   RelationGetDescr(rel),
								   table_slot_callbacks(rel));

		MemoryContextSwitchTo(oldcontext);
	}

	return relInfo->ri_TrigNewSlot;
}

/*
 * Return a relInfo's tuple slot for processing returning tuples.
 */
TupleTableSlot *
ExecGetReturningSlot(EState *estate, ResultRelInfo *relInfo)
{
	if (relInfo->ri_ReturningSlot == NULL)
	{
		Relation	rel = relInfo->ri_RelationDesc;
		MemoryContext oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

		relInfo->ri_ReturningSlot =
			ExecInitExtraTupleSlot(estate,
								   RelationGetDescr(rel),
								   table_slot_callbacks(rel));

		MemoryContextSwitchTo(oldcontext);
	}

	return relInfo->ri_ReturningSlot;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetAllNullSlot —— 返回"全 NULL"元组槽（只读）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   惰性创建"所有列全部为 NULL"的元组槽并缓存。该槽只读，调用方不得
 *   更新其中数据。
 *
 * 业务场景：
 *   UPDATE 不修改任何列却仍需构造新行（例如仅为了触发器/RETURNING 语义）
 *   时，用全 NULL 槽占位，省去逐列置空。
 * ============================================================================
 */
TupleTableSlot *
ExecGetAllNullSlot(EState *estate, ResultRelInfo *relInfo)
{
	if (relInfo->ri_AllNullSlot == NULL)
	{
		Relation	rel = relInfo->ri_RelationDesc;
		MemoryContext oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);
		TupleTableSlot *slot;

		slot = ExecInitExtraTupleSlot(estate,
									  RelationGetDescr(rel),
									  table_slot_callbacks(rel));
		ExecStoreAllNullTuple(slot);

		relInfo->ri_AllNullSlot = slot;

		MemoryContextSwitchTo(oldcontext);
	}

	return relInfo->ri_AllNullSlot;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetChildToRootMap / ExecGetRootToChildMap —— 分区子表↔根表
 * 列映射
 * ----------------------------------------------------------------------------
 * 函数作用（成对提供，惰性构建并缓存，返回 NULL 表示无需转换）：
 *   - ExecGetChildToRootMap：把"子（分区/继承）结果关系行类型"转换为
 *     "查询主目标（根）关系行类型"的映射。按列名匹配
 *     （convert_tuples_by_name）；
 *   - ExecGetRootToChildMap：反向映射（根→子）。要求必须是分区子关系；
 *     非分区子表（继承表）可能含根表没有的列，用 missing_ok=true 忽略。
 *
 * 业务场景：
 *   分区路由后元组的行类型是目标分区的；而约束检查、WITH CHECK OPTION、
 *   RETURNING、错误消息等常需要根表行类型（或相反），因此需要按属性名
 *   建立转换映射，把同名列的值对应搬运并补齐缺失列。
 *
 * 设计要点：
 *   - 映射对象（TupleConversionMap）分配在 per-query 上下文；
 *   - "Valid" 标志位保证只构建一次（结果缓存于 ResultRelInfo）。
 * ============================================================================
 */
TupleConversionMap *
ExecGetChildToRootMap(ResultRelInfo *resultRelInfo)
{
	/* If we didn't already do so, compute the map for this child. */
	if (!resultRelInfo->ri_ChildToRootMapValid)
	{
		ResultRelInfo *rootRelInfo = resultRelInfo->ri_RootResultRelInfo;

		if (rootRelInfo)
			resultRelInfo->ri_ChildToRootMap =
				convert_tuples_by_name(RelationGetDescr(resultRelInfo->ri_RelationDesc),
									   RelationGetDescr(rootRelInfo->ri_RelationDesc));
		else					/* this isn't a child result rel */
			resultRelInfo->ri_ChildToRootMap = NULL;

		resultRelInfo->ri_ChildToRootMapValid = true;
	}

	return resultRelInfo->ri_ChildToRootMap;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetRootToChildMap —— 根表→子表列映射（惰性构建）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   构建"根表行类型 → 子结果关系行类型"的元组转换映射（按属性名匹配），
 *   首次调用构建并缓存到 ri_RootToChildMap。返回 NULL 表示无需转换
 *   （列布局完全一致）。仅允许对分区子结果关系调用（Assert 强制）。
 *
 * 设计细节：
 *   - 非分区继承人子表可能含根表没有的列，build_attrmap_by_name_if_req
 *     的 missing_ok=true 忽略这类列（不参与转换）；
 *   - 映射分配在 per-query 上下文，随查询释放。
 * ============================================================================
 */
TupleConversionMap *
ExecGetRootToChildMap(ResultRelInfo *resultRelInfo, EState *estate)
{
	/* Mustn't get called for a non-child result relation. */
	Assert(resultRelInfo->ri_RootResultRelInfo);

	/* If we didn't already do so, compute the map for this child. */
	if (!resultRelInfo->ri_RootToChildMapValid)
	{
		ResultRelInfo *rootRelInfo = resultRelInfo->ri_RootResultRelInfo;
		TupleDesc	indesc = RelationGetDescr(rootRelInfo->ri_RelationDesc);
		TupleDesc	outdesc = RelationGetDescr(resultRelInfo->ri_RelationDesc);
		Relation	childrel = resultRelInfo->ri_RelationDesc;
		AttrMap    *attrMap;
		MemoryContext oldcontext;

		/*
		 * When this child table is not a partition (!relispartition), it may
		 * have columns that are not present in the root table, which we ask
		 * to ignore by passing true for missing_ok.
		 */
		oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);
		attrMap = build_attrmap_by_name_if_req(indesc, outdesc,
											   !childrel->rd_rel->relispartition);
		if (attrMap)
			resultRelInfo->ri_RootToChildMap =
				convert_tuples_by_name_attrmap(indesc, outdesc, attrMap);
		MemoryContextSwitchTo(oldcontext);
		resultRelInfo->ri_RootToChildMapValid = true;
	}

	return resultRelInfo->ri_RootToChildMap;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetInsertedCols / ExecGetUpdatedCols —— 获取被插/被更新列位图
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回 ResultRelInfo 对应的"被插入列/被更新列"位图（来自 RTE 权限信息
 *   perminfo->insertedCols/updatedCols）。
 *
 * 关键逻辑（位图列号映射）：
 *   子结果关系（分区路由目标）的列号可能与根表不同：权限信息按根表 RTE
 *   登记，列号是根表列号；这里先用 ExecGetRootToChildMap 的 attrMap 把
 *   位图映射到子表的列号（execute_attr_map_cols）再返回。
 *
 * 业务场景：
 *   - 行级安全（RLS）/触发器判断"用户写了哪些列"；
 *   - 幂等更新（UPDATE 未真正改值不触发）判定；
 *   - UPDATE 加锁模式判定（键列是否被更新）等。
 *
 * 配套函数：
 *   ExecGetExtraUpdatedCols：多算上生成列（需要重算的生成列集合）；
 *   ExecGetAllUpdatedCols：被更新列 ∪ 额外生成列（分配在 per-tuple 内存，
 *   调用方需要更长生命周期时自行拷贝）。
 * ============================================================================
 */
Bitmapset *
ExecGetInsertedCols(ResultRelInfo *relinfo, EState *estate)
{
	RTEPermissionInfo *perminfo = GetResultRTEPermissionInfo(relinfo, estate);

	if (perminfo == NULL)
		return NULL;

	/* Map the columns to child's attribute numbers if needed. */
	if (relinfo->ri_RootResultRelInfo)
	{
		TupleConversionMap *map = ExecGetRootToChildMap(relinfo, estate);

		if (map)
			return execute_attr_map_cols(map->attrMap, perminfo->insertedCols);
	}

	return perminfo->insertedCols;
}

/* Return a bitmap representing columns being updated */
Bitmapset *
ExecGetUpdatedCols(ResultRelInfo *relinfo, EState *estate)
{
	RTEPermissionInfo *perminfo = GetResultRTEPermissionInfo(relinfo, estate);

	if (perminfo == NULL)
		return NULL;

	/* Map the columns to child's attribute numbers if needed. */
	if (relinfo->ri_RootResultRelInfo)
	{
		TupleConversionMap *map = ExecGetRootToChildMap(relinfo, estate);

		if (map)
			return execute_attr_map_cols(map->attrMap, perminfo->updatedCols);
	}

	return perminfo->updatedCols;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetExtraUpdatedCols —— 获取需要重算的生成列位图
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   惰性调用 ExecInitGenerated 计算"UPDATE 需要重新求值的生成列"集合
 *   （ri_extraUpdatedCols，含因被更新列而级联变化的所有存储生成列），返回。
 * ============================================================================
 */
Bitmapset *
ExecGetExtraUpdatedCols(ResultRelInfo *relinfo, EState *estate)
{
	/* Compute the info if we didn't already */
	if (!relinfo->ri_extraUpdatedCols_valid)
		ExecInitGenerated(relinfo, estate, CMD_UPDATE);
	return relinfo->ri_extraUpdatedCols;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetAllUpdatedCols —— 全部被更新列（含生成列）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回"用户显式更新的列 ∪ 需重算的生成列"的并集位图。
 * 注意：结果分配在 per-tuple 内存上下文，需要更长久生命周期时调用方自行
 * 拷贝（例如 ExecUpdateLockMode 的键重叠判定可安全使用，因为位图只用于
 * 本次判断）。
 * ============================================================================
 */
Bitmapset *
ExecGetAllUpdatedCols(ResultRelInfo *relinfo, EState *estate)
{
	Bitmapset  *ret;
	MemoryContext oldcxt;

	oldcxt = MemoryContextSwitchTo(GetPerTupleMemoryContext(estate));

	ret = bms_union(ExecGetUpdatedCols(relinfo, estate),
					ExecGetExtraUpdatedCols(relinfo, estate));

	MemoryContextSwitchTo(oldcxt);

	return ret;
}

/*
 * ============================================================================
 * 【中文注释】GetResultRTEPermissionInfo —— 定位结果关系的权限信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为 ExecGet*Cols 系列函数解析 ResultRelInfo 对应的 RTEPermissionInfo：
 *   - 分区/继承子结果关系：使用其根关系（ri_RootResultRelInfo）的 RTE 索引
 *     （子关系没有独立的权限信息 RTE）；
 *   - 普通结果关系：用自身 RTE 索引（须非 0）；
 *   - 触发器专用哑条目（RTE 索引为 0）：返回 NULL（该关系未被写入）。
 * ============================================================================
 */
static RTEPermissionInfo *
GetResultRTEPermissionInfo(ResultRelInfo *relinfo, EState *estate)
{
	Index		rti;
	RangeTblEntry *rte;
	RTEPermissionInfo *perminfo = NULL;

	if (relinfo->ri_RootResultRelInfo)
	{
		/*
		 * For inheritance child result relations (a partition routing target
		 * of an INSERT or a child UPDATE target), this returns the root
		 * parent's RTE to fetch the RTEPermissionInfo because that's the only
		 * one that has one assigned.
		 */
		rti = relinfo->ri_RootResultRelInfo->ri_RangeTableIndex;
	}
	else if (relinfo->ri_RangeTableIndex != 0)
	{
		/*
		 * Non-child result relation should have their own RTEPermissionInfo.
		 */
		rti = relinfo->ri_RangeTableIndex;
	}
	else
	{
		/*
		 * The relation isn't in the range table and it isn't a partition
		 * routing target.  This ResultRelInfo must've been created only for
		 * firing triggers and the relation is not being inserted into.  (See
		 * ExecGetTriggerResultRel.)
		 */
		rti = 0;
	}

	if (rti > 0)
	{
		rte = exec_rt_fetch(rti, estate);
		perminfo = getRTEPermissionInfo(estate->es_rteperminfos, rte);
	}

	return perminfo;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetResultRelCheckAsUser —— 确定"以谁的身份"修改结果关系
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回操作结果关系时应使用的用户 OID：优先取 RTE 权限信息中的
 *   checkAsUser（SECURITY DEFINER 场景：函数以定义者身份执行），否则
 *   当前用户 GetUserId()。子关系自动回溯到根关系取权限信息。
 *
 * 业务场景：
 *   触发器等需要对"结果关系权限判断/行级安全判断"以正确用户身份执行的
 *   场合（ES 判断权限时不能用当前 session 用户，而应使用效果上的用户）。
 * ============================================================================
 */
Oid
ExecGetResultRelCheckAsUser(ResultRelInfo *relInfo, EState *estate)
{
	RTEPermissionInfo *perminfo = GetResultRTEPermissionInfo(relInfo, estate);

	/* XXX - maybe ok to return GetUserId() in this case? */
	if (perminfo == NULL)
		elog(ERROR, "no RTEPermissionInfo found for result relation with OID %u",
			 RelationGetRelid(relInfo->ri_RelationDesc));

	return perminfo->checkAsUser ? perminfo->checkAsUser : GetUserId();
}
