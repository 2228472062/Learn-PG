/*-------------------------------------------------------------------------
 *
 * execMain.c
 *	  执行器（Executor）对外顶级接口 —— 执行器的"总开关"与"总管家"
 *
 * 【业务背景】
 *   优化器把 SQL 生成执行计划（PlannedStmt）后，无论 SELECT 还是
 *   INSERT/UPDATE/DELETE/MERGE，最终都会经由本文件对外提供的四个接口
 *   完成全部执行工作：
 *
 *     ExecutorStart  —— 启动执行：权限检查、创建 EState、递归初始化计划树
 *     ExecutorRun    —— 逐行拉取元组，交给目标接收器（DestReceiver）输出
 *     ExecutorFinish —— 事后收尾：辅助修改节点跑完、触发排队中的 AFTER 触发器
 *     ExecutorEnd    —— 清理现场：关闭关系/索引、释放快照、释放查询内存上下文
 *
 * 【典型执行流程（生命周期图）】
 *
 *   PortalRun（门户驱动，来自 tcop/pquery.c）
 *      │
 *      ▼
 *   ExecutorStart ─┬─> ExecCheckPermissions   （表级 + 列级权限检查）
 *                  ├─> CreateExecutorState    （创建 EState，一切执行状态的根）
 *                  ├─> InitPlan               （ExecInitNode 递归初始化计划树）
 *                  └─> 填充 queryDesc->tupDesc / planstate，供上层使用
 *      │
 *      ▼
 *   ExecutorRun（可调用多次：游标分批取数时每次取 count 行）
 *      └─> ExecutePlan 主循环：
 *            ExecProcNode(planstate) 取一行
 *              →（可选）JunkFilter 剔除内部列（如 ctid/tableoid）
 *              → dest->receiveSlot() 输出给客户端/物化/EXPLAIN 等
 *            直到计划树返回空行、或已取够 count 行而退出
 *      │
 *      ▼
 *   ExecutorFinish ─┬─> ExecPostprocessPlan（把辅助 ModifyTable 节点跑到完）
 *                   └─> AfterTriggerEndQuery（执行累积的 AFTER 触发器）
 *      │
 *      ▼
 *   ExecutorEnd ─┬─> ExecEndPlan ─┬─> ExecEndNode（各节点逆序关闭、释放Buffer pin）
 *                │                └─> 关闭结果关系与范围表关系
 *                └─> FreeExecutorState（整体释放本次查询的全部内存）
 *
 * 【设计思想】
 *   1. 分层钩子：四个接口都提供"全局 Hook 变量 + standard_* 默认实现"两层。
 *      插件（pg_stat_statements、auto_explain、pg_hint_plan 等）设置钩子即可
 *      拦截执行流程，无需修改内核代码。
 *   2. 生命周期强制约束：Start 必须最先调用，End 必须最后调用；Run 可以
 *      多次、也可提前截断（截断仅允许 SELECT）；Finish 介于最后一次 Run 与
 *      End 之间（EXPLAIN ONLY 模式可省略 Run 与 Finish）。
 *   3. 内存管理：执行期间所有对象都挂在 EState 的 per-query 内存上下文下，
 *      End 时整棵子树一次性释放，避免逐节点手工 pfree 的繁琐与遗漏。
 *
 * 【本文件还承担的执行期公共服务】
 *   - 约束检查：NOT NULL、CHECK、分区约束、WITH CHECK OPTION、RLS 策略；
 *   - 行标记（RowMark）：SELECT FOR UPDATE/SHARE 的加锁信息准备；
 *   - EvalPlanQual（EPQ）：READ COMMITTED 下并发修改后的元组重检查机制；
 *   - 分区路由：分区插入所需的 ResultRelInfo 构建与祖先关系维护。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execMain.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/sysattr.h"
#include "access/table.h"
#include "access/tableam.h"
#include "access/tupconvert.h"
#include "access/xact.h"
#include "catalog/namespace.h"
#include "catalog/partition.h"
#include "commands/matview.h"
#include "commands/trigger.h"
#include "executor/executor.h"
#include "executor/execPartition.h"
#include "executor/instrument.h"
#include "executor/nodeSubplan.h"
#include "foreign/fdwapi.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "nodes/queryjumble.h"
#include "parser/parse_relation.h"
#include "pgstat.h"
#include "rewrite/rewriteHandler.h"
#include "tcop/utility.h"
#include "utils/acl.h"
#include "utils/backend_status.h"
#include "utils/lsyscache.h"
#include "utils/partcache.h"
#include "utils/rls.h"
#include "utils/snapmgr.h"


/* Hooks for plugins to get control in ExecutorStart/Run/Finish/End */
ExecutorStart_hook_type ExecutorStart_hook = NULL;
ExecutorRun_hook_type ExecutorRun_hook = NULL;
ExecutorFinish_hook_type ExecutorFinish_hook = NULL;
ExecutorEnd_hook_type ExecutorEnd_hook = NULL;

/* Hook for plugin to get control in ExecCheckPermissions() */
ExecutorCheckPerms_hook_type ExecutorCheckPerms_hook = NULL;

/* decls for local routines only used within this module */
static void InitPlan(QueryDesc *queryDesc, int eflags);
static void CheckValidRowMarkRel(Relation rel, RowMarkType markType);
static void ExecPostprocessPlan(EState *estate);
static void ExecEndPlan(PlanState *planstate, EState *estate);
static void ExecutePlan(QueryDesc *queryDesc,
						CmdType operation,
						bool sendTuples,
						uint64 numberTuples,
						ScanDirection direction,
						DestReceiver *dest);
static bool ExecCheckPermissionsModified(Oid relOid, Oid userid,
										 Bitmapset *modifiedCols,
										 AclMode requiredPerms);
static void ExecCheckXactReadOnly(PlannedStmt *plannedstmt);
static void EvalPlanQualStart(EPQState *epqstate, Plan *planTree);
static void ReportNotNullViolationError(ResultRelInfo *resultRelInfo,
										TupleTableSlot *slot,
										EState *estate, int attnum);

/* end of local decls */


/*
 * ============================================================================
 * 【中文注释】ExecutorStart —— 执行器启动入口（Hook 分发层）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   执行任何查询计划之前必须先调用本函数。它负责：
 *   1) 上报 query_id 给 pgstat（供 pg_stat_statements 等统计模块使用）；
 *   2) 按是否注册了 ExecutorStart_hook 决定调用插件钩子，还是调用默认实现
 *      standard_ExecutorStart() 完成真正的启动工作。
 *
 * 参数：
 *   queryDesc - 查询描述符，由上层（PortalRun/ExecutePlan）用 CreateQueryDesc
 *               创建；执行前会填充其 estate、planstate、tupDesc 等字段。
 *   eflags    - 执行标志位（executor.h 中 EXEC_FLAG_* 的按位或），用于说明本次
 *               执行方式：EXPLAIN_ONLY（仅输出计划）、BACKWARD（允许反向扫描）、
 *               MARK（允许 MARK/RESTORE）、SKIP_TRIGGERS（跳过触发器）等。
 *
 * 设计思想：
 *   1. 钩子分层模式：PostgreSQL 在整条执行链路上都预留了"全局函数钩子变量 +
 *      standard_* 默认实现"。插件（如 auto_explain）只要设置钩子变量，就能在
 *      不动内核代码的前提下拦截、扩展执行流程；钩子内部通常会先处理自身逻辑，
 *      再调用 standard_* 完成默认职责。
 *   2. query_id 兜底上报：extended query 协议下（PARSE/BIND/EXECUTE），query_id
 *      可能在 Prepare 阶段就丢失，这里补报一次。重复上报是无害的（顶层已上报
 *      后会被忽略）。
 * 注意：调用本函数时进程的 CurrentMemoryContext 将成为本次执行的 per-query
 * 内存上下文的父上下文——查询期间分配的所有内存都挂在其下，随 ExecutorEnd
 * 一并释放。
 * ============================================================================
 */
void
ExecutorStart(QueryDesc *queryDesc, int eflags)
{
	/*
	 * In some cases (e.g. an EXECUTE statement or an execute message with the
	 * extended query protocol) the query_id won't be reported, so do it now.
	 *
	 * Note that it's harmless to report the query_id multiple times, as the
	 * call will be ignored if the top level query_id has already been
	 * reported.
	 */
	pgstat_report_query_id(queryDesc->plannedstmt->queryId, false);

	if (ExecutorStart_hook)
		(*ExecutorStart_hook) (queryDesc, eflags);
	else
		standard_ExecutorStart(queryDesc, eflags);
}

/*
 * ============================================================================
 * 【中文注释】standard_ExecutorStart —— 执行器启动的默认实现（核心初始化）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   完成查询执行的"预热"工作，步骤拆解：
 *   1. 只读事务 / 并行模式下的写入合规检查（ExecCheckXactReadOnly）；
 *   2. 创建 EState（CreateExecutorState），切换进 per-query 内存上下文；
 *   3. 注入外部参数（ext_params）、预留内部参数数组（es_param_exec_vals）；
 *   4. 按命令类型确定 es_output_cid（COMMAND ID：写操作/行锁需要标记元组）；
 *      纯 SELECT 且无修改 CTE 时附加 EXEC_FLAG_SKIP_TRIGGERS 优化标志；
 *   5. 注册快照、记录顶层 eflags、instrument/JIT 选项；
 *   6. 开启 AFTER 触发器语句级环境（AfterTriggerBeginQuery）；
 *   7. 调用 InitPlan 递归初始化整棵计划树（含子计划）。
 *
 * 参数：
 *   queryDesc - 查询描述符（已校验 estate 为 NULL、快照处于激活状态）。
 *   eflags    - 顶层执行标志位（会保存到 estate->es_top_eflags）。
 *
 * 设计思想：
 *   1. es_output_cid 的用途：元组被修改时要在其上打上"当前命令 ID"水印，
 *      同一事务内后发起的命令才能"看见"本次修改（可见性判断与命令 ID 有关，
 *      见 CommandId 机制）。SELECT 只有带行锁或修改 CTE 才需要标记。
 *   2. 并行模式约束：并行执行中不允许写操作——维护 combo CID 哈希需要共享
 *      内存、且 heap_update 依赖 xmax 做互斥，暂不支持；这里宁可多检查一次，
 *      给出更友好的报错信息。
 *   3. EXPLAIN（EXEC_FLAG_EXPLAIN_ONLY）：只出计划不执行，因此跳过 AFTER
 *      触发器环境（ExecutorFinish 不会被调用，触发器队列无人收拾）。
 *   4. 状态一致性：先 Assert 快照必须是激活的（GetActiveSnapshot），保证后续
 *      任何访问快照的操作都不需要临时切换，且快照生命周期安全。
 * ============================================================================
 */
void
standard_ExecutorStart(QueryDesc *queryDesc, int eflags)
{
	EState	   *estate;
	MemoryContext oldcontext;

	/* sanity checks: queryDesc must not be started already */
	Assert(queryDesc != NULL);
	Assert(queryDesc->estate == NULL);

	/* caller must ensure the query's snapshot is active */
	Assert(GetActiveSnapshot() == queryDesc->snapshot);

	/*
	 * If the transaction is read-only, we need to check if any writes are
	 * planned to non-temporary tables.  EXPLAIN is considered read-only.
	 *
	 * Don't allow writes in parallel mode.  Supporting UPDATE and DELETE
	 * would require (a) storing the combo CID hash in shared memory, rather
	 * than synchronizing it just once at the start of parallelism, and (b) an
	 * alternative to heap_update()'s reliance on xmax for mutual exclusion.
	 * INSERT may have no such troubles, but we forbid it to simplify the
	 * checks.
	 *
	 * We have lower-level defenses in CommandCounterIncrement and elsewhere
	 * against performing unsafe operations in parallel mode, but this gives a
	 * more user-friendly error message.
	 */
	if ((XactReadOnly || IsInParallelMode()) &&
		!(eflags & EXEC_FLAG_EXPLAIN_ONLY))
		ExecCheckXactReadOnly(queryDesc->plannedstmt);

	/*
	 * Build EState, switch into per-query memory context for startup.
	 */
	estate = CreateExecutorState();
	queryDesc->estate = estate;

	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	/*
	 * Fill in external parameters, if any, from queryDesc; and allocate
	 * workspace for internal parameters
	 */
	estate->es_param_list_info = queryDesc->params;

	if (queryDesc->plannedstmt->paramExecTypes != NIL)
	{
		int			nParamExec;

		nParamExec = list_length(queryDesc->plannedstmt->paramExecTypes);
		estate->es_param_exec_vals = (ParamExecData *)
			palloc0_array(ParamExecData, nParamExec);
	}

	/* We now require all callers to provide sourceText */
	Assert(queryDesc->sourceText != NULL);
	estate->es_sourceText = queryDesc->sourceText;

	/*
	 * Fill in the query environment, if any, from queryDesc.
	 */
	estate->es_queryEnv = queryDesc->queryEnv;

	/*
	 * If non-read-only query, set the command ID to mark output tuples with
	 */
	switch (queryDesc->operation)
	{
		case CMD_SELECT:

			/*
			 * SELECT FOR [KEY] UPDATE/SHARE and modifying CTEs need to mark
			 * tuples
			 */
			if (queryDesc->plannedstmt->rowMarks != NIL ||
				queryDesc->plannedstmt->hasModifyingCTE)
				estate->es_output_cid = GetCurrentCommandId(true);

			/*
			 * A SELECT without modifying CTEs can't possibly queue triggers,
			 * so force skip-triggers mode. This is just a marginal efficiency
			 * hack, since AfterTriggerBeginQuery/AfterTriggerEndQuery aren't
			 * all that expensive, but we might as well do it.
			 */
			if (!queryDesc->plannedstmt->hasModifyingCTE)
				eflags |= EXEC_FLAG_SKIP_TRIGGERS;
			break;

		case CMD_INSERT:
		case CMD_DELETE:
		case CMD_UPDATE:
		case CMD_MERGE:
			estate->es_output_cid = GetCurrentCommandId(true);
			break;

		default:
			elog(ERROR, "unrecognized operation code: %d",
				 (int) queryDesc->operation);
			break;
	}

	/*
	 * Copy other important information into the EState
	 */
	estate->es_snapshot = RegisterSnapshot(queryDesc->snapshot);
	estate->es_crosscheck_snapshot = RegisterSnapshot(queryDesc->crosscheck_snapshot);
	estate->es_top_eflags = eflags;
	estate->es_instrument = queryDesc->instrument_options;
	estate->es_jit_flags = queryDesc->plannedstmt->jitFlags;

	/*
	 * Set up query-level instrumentation if extensions have requested it via
	 * query_instr_options. Ensure an extension has not allocated query_instr
	 * itself.
	 */
	Assert(queryDesc->query_instr == NULL);
	if (queryDesc->query_instr_options)
		queryDesc->query_instr = InstrAlloc(queryDesc->query_instr_options);

	/*
	 * Set up an AFTER-trigger statement context, unless told not to, or
	 * unless it's EXPLAIN-only mode (when ExecutorFinish won't be called).
	 */
	if (!(eflags & (EXEC_FLAG_SKIP_TRIGGERS | EXEC_FLAG_EXPLAIN_ONLY)))
		AfterTriggerBeginQuery();

	/*
	 * Initialize the plan state tree
	 */
	InitPlan(queryDesc, eflags);

	MemoryContextSwitchTo(oldcontext);
}

/*
 * ============================================================================
 * 【中文注释】ExecutorRun —— 执行器主执行入口（Hook 分发层）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   执行器模块的核心例行程序：接收交通指挥模块（traffic cop）传来的查询描述
 *   符并按指定方向/数量执行计划，输出元组通过 QueryDesc->dest 送往目的地。
 *   本函数仅做钩子分发，实际工作在 standard_ExecutorRun() 中。
 *
 * 参数：
 *   queryDesc - 查询描述符（ExecutorStart 必须已调用过）。
 *   direction - 扫描方向（Forward/Backward/NoMovement）。NoMovement 表示
 *               不取任何行，仅做接收器的启动/关闭（游标到达尾端后的补调用）。
 *   count     - 最多取多少行。0 表示"无限制，一直跑到计划结束"。
 *
 * 约束与语义：
 *   - 计数只作用于"取出的行"，不作用于 ModifyTable 改动行数；
 *   - 可在未跑完整个计划的情况下提前停止（仅适用于 SELECT）；
 *   - 多次调用的累计处理行数记录在 estate->es_total_processed。
 * ============================================================================
 */
void
ExecutorRun(QueryDesc *queryDesc,
			ScanDirection direction, uint64 count)
{
	if (ExecutorRun_hook)
		(*ExecutorRun_hook) (queryDesc, direction, count);
	else
		standard_ExecutorRun(queryDesc, direction, count);
}

/*
 * ============================================================================
 * 【中文注释】standard_ExecutorRun —— 执行器运行（默认实现）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   1. 清零 es_processed（本次调用的处理行数），判断是否需要向客户端
 *      发送元组（纯 SELECT 或含 RETURNING 子句的 DML）；
 *   2. 若需发送，调用 dest->rStartup 启动接收器（如打印表头）；
 *   3. 方向不为 NoMovement 时，调用 ExecutePlan 驱动计划树取行并输出；
 *   4. 累加 es_total_processed，调用 dest->rShutdown 关闭接收器。
 *
 * 参数：
 *   queryDesc - 查询描述符；direction/count 语义同 ExecutorRun。
 *
 * 设计思想：
 *   1. sendTuples 判定：SELECT 一定有输出；INSERT/UPDATE/DELETE 只有带
 *      RETURNING 时才需要把行送回客户端（否则静默改动即可）。
 *   2. NoMovement 方向的由来：pquery.c 在"上次调用已取到数据末尾"时，会再补
 *      调用一次 ExecutorRun 以正确关闭接收器；此时绝不能再次驱动计划树——
 *      heap 扫描会从头再扫一遍返回全部数据，并行计划也可能因二次非并行执行
 *      而行为异常。故 NoMovement 仅做接收器启停。
 *   3. 计数语义：count 限制的是"取出行数"，修改类节点（ModifyTable）造成的
 *      实际影响行数由节点内部统计，二者互不干扰。
 * ============================================================================
 */
void
standard_ExecutorRun(QueryDesc *queryDesc,
					 ScanDirection direction, uint64 count)
{
	EState	   *estate;
	CmdType		operation;
	DestReceiver *dest;
	bool		sendTuples;
	MemoryContext oldcontext;

	/* sanity checks */
	Assert(queryDesc != NULL);

	estate = queryDesc->estate;

	Assert(estate != NULL);
	Assert(!(estate->es_top_eflags & EXEC_FLAG_EXPLAIN_ONLY));

	/* caller must ensure the query's snapshot is active */
	Assert(GetActiveSnapshot() == estate->es_snapshot);

	/*
	 * Switch into per-query memory context
	 */
	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	/* Allow instrumentation of Executor overall runtime */
	if (queryDesc->query_instr)
		InstrStart(queryDesc->query_instr);

	/*
	 * extract information from the query descriptor and the query feature.
	 */
	operation = queryDesc->operation;
	dest = queryDesc->dest;

	/*
	 * startup tuple receiver, if we will be emitting tuples
	 */
	estate->es_processed = 0;

	sendTuples = (operation == CMD_SELECT ||
				  queryDesc->plannedstmt->hasReturning);

	if (sendTuples)
		dest->rStartup(dest, operation, queryDesc->tupDesc);

	/*
	 * Run plan, unless direction is NoMovement.
	 *
	 * Note: pquery.c selects NoMovement if a prior call already reached
	 * end-of-data in the user-specified fetch direction.  This is important
	 * because various parts of the executor can misbehave if called again
	 * after reporting EOF.  For example, heapam.c would actually restart a
	 * heapscan and return all its data afresh.  There is also some doubt
	 * about whether a parallel plan would operate properly if an additional,
	 * necessarily non-parallel execution request occurs after completing a
	 * parallel execution.  (That case should work, but it's untested.)
	 */
	if (!ScanDirectionIsNoMovement(direction))
		ExecutePlan(queryDesc,
					operation,
					sendTuples,
					count,
					direction,
					dest);

	/*
	 * Update es_total_processed to keep track of the number of tuples
	 * processed across multiple ExecutorRun() calls.
	 */
	estate->es_total_processed += estate->es_processed;

	/*
	 * shutdown tuple receiver, if we started it
	 */
	if (sendTuples)
		dest->rShutdown(dest);

	if (queryDesc->query_instr)
		InstrStop(queryDesc->query_instr);

	MemoryContextSwitchTo(oldcontext);
}

/*
 * ============================================================================
 * 【中文注释】ExecutorFinish —— 执行收尾入口（Hook 分发层）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   最后一次 ExecutorRun 之后、ExecutorEnd 之前必须调用（仅 EXPLAIN 模式可
 *   省略）。负责执行"事后清理"：把修改类节点跑到完、触发排队的 AFTER 触发器。
 *   与 ExecutorEnd 分离的原因：EXPLAIN ANALYZE 需要把这些动作计入总耗时，
 *   而 ExecutorEnd 会摧毁整个执行上下文，无法再计时。
 * ============================================================================
 */
void
ExecutorFinish(QueryDesc *queryDesc)
{
	if (ExecutorFinish_hook)
		(*ExecutorFinish_hook) (queryDesc);
	else
		standard_ExecutorFinish(queryDesc);
}

/*
 * ============================================================================
 * 【中文注释】standard_ExecutorFinish —— 执行收尾（默认实现）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   1. ExecPostprocessPlan：主查询可能没有把辅助 ModifyTable 节点（修改
 *      CTE 对应的 DML 节点）取完，这里强制把它们跑到完，保证修改结果确定；
 *   2. AfterTriggerEndQuery：执行本语句累积的全部 AFTER 触发器（含外键
 *      RI 触发器与用户定义的 AFTER 触发器）。
 *   全程计入 query_instr 计时（供 EXPLAIN ANALYZE 展示"收尾阶段"耗时）。
 *
 * 设计思想：
 *   - 用 es_finished 标志保证本函数每套 Executor 实例只执行一次；
 *   - SKIP_TRIGGERS 标志（纯 SELECT 优化、EXPLAIN）下跳过触发器处理。
 * ============================================================================
 */
void
standard_ExecutorFinish(QueryDesc *queryDesc)
{
	EState	   *estate;
	MemoryContext oldcontext;

	/* sanity checks */
	Assert(queryDesc != NULL);

	estate = queryDesc->estate;

	Assert(estate != NULL);
	Assert(!(estate->es_top_eflags & EXEC_FLAG_EXPLAIN_ONLY));

	/* This should be run once and only once per Executor instance */
	Assert(!estate->es_finished);

	/* Switch into per-query memory context */
	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	/* Allow instrumentation of Executor overall runtime */
	if (queryDesc->query_instr)
		InstrStart(queryDesc->query_instr);

	/* Run ModifyTable nodes to completion */
	ExecPostprocessPlan(estate);

	/* Execute queued AFTER triggers, unless told not to */
	if (!(estate->es_top_eflags & EXEC_FLAG_SKIP_TRIGGERS))
		AfterTriggerEndQuery(estate);

	if (queryDesc->query_instr)
		InstrStop(queryDesc->query_instr);

	MemoryContextSwitchTo(oldcontext);

	estate->es_finished = true;
}

/*
 * ============================================================================
 * 【中文注释】ExecutorEnd —— 执行器收尾销毁入口（Hook 分发层）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   任何查询计划执行完毕后必须调用（中途出错被 abort 的情形除外）。负责把
 *   执行现场彻底清理干净；本函数做钩子分发，默认实现见 standard_ExecutorEnd。
 * ============================================================================
 */
void
ExecutorEnd(QueryDesc *queryDesc)
{
	if (ExecutorEnd_hook)
		(*ExecutorEnd_hook) (queryDesc);
	else
		standard_ExecutorEnd(queryDesc);
}

/*
 * ============================================================================
 * 【中文注释】standard_ExecutorEnd —— 执行器清理（默认实现）
 * ----------------------------------------------------------------------------
 * 函数作用（清理流程）：
 *   1. 更新并行工作进程数统计；
 *   2. ExecEndPlan：ExecEndNode 递归关闭计划树节点（释放 Buffer pin、关闭
 *      子计划）、重置元组表、关闭结果关系与范围表关系；
 *   3. 注销两个快照（es_snapshot / es_crosscheck_snapshot 的引用计数减一）；
 *   4. FreeExecutorState：释放 EState 及其挂载的整个 per-query 内存上下文；
 *   5. 将 queryDesc 中已失效的字段全部置空，防止悬垂指针。
 *
 * 设计思想：
 *   - 内存不逐项释放：PostgreSQL 采用"内存上下文整体释放"策略，只要关闭了
 *     关系（释放锁与 relcache 引用）并释放 Buffer pin，其余内存随上下文消失，
 *     因此 ExecEndPlan 内部只关心"必须显式清理的资源"；
 *   - 强校验 es_finished：从 9.1 起 ExecutorFinish 成为必调接口，此处 Assert
 *     防止调用方忘记调用而漏掉 AFTER 触发器。
 * ============================================================================
 */
void
standard_ExecutorEnd(QueryDesc *queryDesc)
{
	EState	   *estate;
	MemoryContext oldcontext;

	/* sanity checks */
	Assert(queryDesc != NULL);

	estate = queryDesc->estate;

	Assert(estate != NULL);

	if (estate->es_parallel_workers_to_launch > 0)
		pgstat_update_parallel_workers_stats((PgStat_Counter) estate->es_parallel_workers_to_launch,
											 (PgStat_Counter) estate->es_parallel_workers_launched);

	/*
	 * Check that ExecutorFinish was called, unless in EXPLAIN-only mode. This
	 * Assert is needed because ExecutorFinish is new as of 9.1, and callers
	 * might forget to call it.
	 */
	Assert(estate->es_finished ||
		   (estate->es_top_eflags & EXEC_FLAG_EXPLAIN_ONLY));

	/*
	 * Switch into per-query memory context to run ExecEndPlan
	 */
	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	ExecEndPlan(queryDesc->planstate, estate);

	/* do away with our snapshots */
	UnregisterSnapshot(estate->es_snapshot);
	UnregisterSnapshot(estate->es_crosscheck_snapshot);

	/*
	 * Must switch out of context before destroying it
	 */
	MemoryContextSwitchTo(oldcontext);

	/*
	 * Release EState and per-query memory context.  This should release
	 * everything the executor has allocated.
	 */
	FreeExecutorState(estate);

	/* Reset queryDesc fields that no longer point to anything */
	queryDesc->tupDesc = NULL;
	queryDesc->estate = NULL;
	queryDesc->planstate = NULL;
	queryDesc->query_instr = NULL;
}

/*
 * ============================================================================
 * 【中文注释】ExecutorRewind —— 把已打开的 QueryDesc 回卷到起点
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对已执行过的查询描述符做"倒带"：调用 ExecReScan 重置整棵计划树，使其
 *   可以重新从头执行一遍。用于 Portal（游标）重用同一计划多次执行的情形。
 *
 * 设计思想：
 *   - 只允许对 SELECT 回卷（更新型查询无意义，直接 Assert 拒绝）；
 *   - 回卷依赖各节点 ExecReScan 的正确联动（扫描节点重置游标、排序/物化
 *     节点丢弃已缓冲数据等），倒带后一切从头再来。
 * ============================================================================
 */
void
ExecutorRewind(QueryDesc *queryDesc)
{
	EState	   *estate;
	MemoryContext oldcontext;

	/* sanity checks */
	Assert(queryDesc != NULL);

	estate = queryDesc->estate;

	Assert(estate != NULL);

	/* It's probably not sensible to rescan updating queries */
	Assert(queryDesc->operation == CMD_SELECT);

	/*
	 * Switch into per-query memory context
	 */
	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	/*
	 * rescan plan
	 */
	ExecReScan(queryDesc->planstate);

	MemoryContextSwitchTo(oldcontext);
}


/*
 * ============================================================================
 * 【中文注释】ExecCheckPermissions —— 检查查询涉及关系的访问权限（顶层入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对查询中的每个 RTE 逐一做 ACL 权限检查（rteperminfos 是计划器生成的
 *   每关系权限信息列表）。全部通过返回 true；否则若 ereport_on_violation
 *   为 true 则直接抛权限错误，为 false 则静默返回 false。
 *
 * 参数：
 *   rangeTable          - 范围表（仅保留给钩子使用，常规检查不再依赖它）；
 *   rteperminfos        - RTEPermissionInfo 列表（含各关系需要的权限位、
 *                         选中列/插入列/更新列的位图）；
 *   ereport_on_violation- 违规时是否立即报错。
 *
 * 设计思想：
 *   1. 权限粒度：先查表级权限，表级不足时逐列查（SELECT/INSERT/UPDATE
 *      支持列级授权），见 ExecCheckOneRelPerms；
 *   2. ASSERT 自检：编译期校验 rteperminfos 与 rangeTable 完全对应、一一
 *      映射无重复，防止计划器与执行器信息脱节；
 *   3. 注意本函数只做 ACL 检查，不涉及行级安全（RLS）——RLS 的 USING/WITH
 *      CHECK 策略在下一阶段（节点执行时）另行评估；
 *   4. 最后调用 ExecutorCheckPerms_hook，给插件（如 sepgsql）追加权限
 *      判定的机会——返回 false 时同样走报错/静默分支。
 * ============================================================================
 */
bool
ExecCheckPermissions(List *rangeTable, List *rteperminfos,
					 bool ereport_on_violation)
{
	ListCell   *l;
	bool		result = true;

#ifdef USE_ASSERT_CHECKING
	Bitmapset  *indexset = NULL;

	/* Check that rteperminfos is consistent with rangeTable */
	foreach(l, rangeTable)
	{
		RangeTblEntry *rte = lfirst_node(RangeTblEntry, l);

		if (rte->perminfoindex != 0)
		{
			/* Sanity checks */

			/*
			 * Only relation RTEs and subquery RTEs that were once relation
			 * RTEs (views, property graphs) have their perminfoindex set.
			 */
			Assert(rte->rtekind == RTE_RELATION ||
				   (rte->rtekind == RTE_SUBQUERY &&
					(rte->relkind == RELKIND_VIEW || rte->relkind == RELKIND_PROPGRAPH)));

			(void) getRTEPermissionInfo(rteperminfos, rte);
			/* Many-to-one mapping not allowed */
			Assert(!bms_is_member(rte->perminfoindex, indexset));
			indexset = bms_add_member(indexset, rte->perminfoindex);
		}
	}

	/* All rteperminfos are referenced */
	Assert(bms_num_members(indexset) == list_length(rteperminfos));
#endif

	foreach(l, rteperminfos)
	{
		RTEPermissionInfo *perminfo = lfirst_node(RTEPermissionInfo, l);

		Assert(OidIsValid(perminfo->relid));
		result = ExecCheckOneRelPerms(perminfo);
		if (!result)
		{
			if (ereport_on_violation)
				aclcheck_error(ACLCHECK_NO_PRIV,
							   get_relkind_objtype(get_rel_relkind(perminfo->relid)),
							   get_rel_name(perminfo->relid));
			return false;
		}
	}

	if (ExecutorCheckPerms_hook)
		result = (*ExecutorCheckPerms_hook) (rangeTable, rteperminfos,
											 ereport_on_violation);
	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecCheckOneRelPerms —— 检查单个关系的访问权限
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   先检查所需权限中能被"表级授权"满足的部分；不足的部分（SELECT/INSERT/
 *   UPDATE 支持列级授权）再逐列检查 selectedCols / insertedCols / updatedCols
 *   位图对应的列权限。全部满足返回 true。
 *
 * 参数：
 *   perminfo - 单个关系的权限信息（relid、requiredPerms、checkAsUser、
 *              各列位图）。
 *
 * 设计思想：
 *   1. 权限归属主体：默认用当前用户 GetUserId()；若设置了 checkAsUser
 *      （例如 SECURITY DEFINER 函数内以被定义者身份执行），则以该用户为准。
 *   2. 权限位分解：
 *      - ACLMASK_ALL 取表级结果，能覆盖的先抹掉（remainingPerms）；
 *      - 剩余位若包含"只能表级授予"的权限（如 TRUNCATE、REFERENCES、
 *        DELETE、ALTER 等）→ 直接失败；
 *      - 剩下可列级满足的 SELECT/INSERT/UPDATE 进入逐列检查。
 *   3. 列位图偏移：位图 bit0 对应 FirstLowInvalidHeapAttributeNumber
 *      （= -8，系统列编号），因此 AttrNumber = bit + FirstLow...；特判
 *      InvalidAttrNumber（= 0，位列编号 0）表示"整行引用"（如 SELECT t.*
 *      或 ROW(t)），整行引用要求所有列都有权限。
 *   4. 特殊情况：查询未显式引用任何列（如 SELECT COUNT(*)）时，SQL 规范
 *      允许"对任一列有权限即可放行"，用 ACLMASK_ANY 达成。
 * ============================================================================
 */
bool
ExecCheckOneRelPerms(RTEPermissionInfo *perminfo)
{
	AclMode		requiredPerms;
	AclMode		relPerms;
	AclMode		remainingPerms;
	Oid			userid;
	Oid			relOid = perminfo->relid;

	requiredPerms = perminfo->requiredPerms;
	Assert(requiredPerms != 0);

	/*
	 * userid to check as: current user unless we have a setuid indication.
	 *
	 * Note: GetUserId() is presently fast enough that there's no harm in
	 * calling it separately for each relation.  If that stops being true, we
	 * could call it once in ExecCheckPermissions and pass the userid down
	 * from there.  But for now, no need for the extra clutter.
	 */
	userid = OidIsValid(perminfo->checkAsUser) ?
		perminfo->checkAsUser : GetUserId();

	/*
	 * We must have *all* the requiredPerms bits, but some of the bits can be
	 * satisfied from column-level rather than relation-level permissions.
	 * First, remove any bits that are satisfied by relation permissions.
	 */
	relPerms = pg_class_aclmask(relOid, userid, requiredPerms, ACLMASK_ALL);
	remainingPerms = requiredPerms & ~relPerms;
	if (remainingPerms != 0)
	{
		int			col = -1;

		/*
		 * If we lack any permissions that exist only as relation permissions,
		 * we can fail straight away.
		 */
		if (remainingPerms & ~(ACL_SELECT | ACL_INSERT | ACL_UPDATE))
			return false;

		/*
		 * Check to see if we have the needed privileges at column level.
		 *
		 * Note: failures just report a table-level error; it would be nicer
		 * to report a column-level error if we have some but not all of the
		 * column privileges.
		 */
		if (remainingPerms & ACL_SELECT)
		{
			/*
			 * When the query doesn't explicitly reference any columns (for
			 * example, SELECT COUNT(*) FROM table), allow the query if we
			 * have SELECT on any column of the rel, as per SQL spec.
			 */
			if (bms_is_empty(perminfo->selectedCols))
			{
				if (pg_attribute_aclcheck_all(relOid, userid, ACL_SELECT,
											  ACLMASK_ANY) != ACLCHECK_OK)
					return false;
			}

			while ((col = bms_next_member(perminfo->selectedCols, col)) >= 0)
			{
				/* bit #s are offset by FirstLowInvalidHeapAttributeNumber */
				AttrNumber	attno = col + FirstLowInvalidHeapAttributeNumber;

				if (attno == InvalidAttrNumber)
				{
					/* Whole-row reference, must have priv on all cols */
					if (pg_attribute_aclcheck_all(relOid, userid, ACL_SELECT,
												  ACLMASK_ALL) != ACLCHECK_OK)
						return false;
				}
				else
				{
					if (pg_attribute_aclcheck(relOid, attno, userid,
											  ACL_SELECT) != ACLCHECK_OK)
						return false;
				}
			}
		}

		/*
		 * Basically the same for the mod columns, for both INSERT and UPDATE
		 * privilege as specified by remainingPerms.
		 */
		if (remainingPerms & ACL_INSERT &&
			!ExecCheckPermissionsModified(relOid,
										  userid,
										  perminfo->insertedCols,
										  ACL_INSERT))
			return false;

		if (remainingPerms & ACL_UPDATE &&
			!ExecCheckPermissionsModified(relOid,
										  userid,
										  perminfo->updatedCols,
										  ACL_UPDATE))
			return false;
	}
	return true;
}

/*
 * ============================================================================
 * 【中文注释】ExecCheckPermissionsModified —— 检查单表的 INSERT/UPDATE 列权限
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为 INSERT（requiredPerms=ACL_INSERT，位图 insertedCols）与 UPDATE
 *   （requiredPerms=ACL_UPDATE，位图 updatedCols）两个场景检查"被修改列"的
 *   列级权限。这两种检查逻辑完全一致，故合并为一个函数。
 *
 * 设计思想：
 *   - 位图为空（没有显式列出被插/改的列）时用 ACLMASK_ANY 兜底——例如
 *     SELECT FOR UPDATE 需要对整行加锁但未真正改任何列、或 UPDATE 的极端
 *     边界情况，规范允许"对任一列有权限即可"；
 *   - 整行更新（whole-row reference）在此场景下不可能出现，直接报错防御；
 *   - 其余逐列检查 attno 的 requiredPerms 权限。
 * ============================================================================
 */
static bool
ExecCheckPermissionsModified(Oid relOid, Oid userid, Bitmapset *modifiedCols,
							 AclMode requiredPerms)
{
	int			col = -1;

	/*
	 * When the query doesn't explicitly update any columns, allow the query
	 * if we have permission on any column of the rel.  This is to handle
	 * SELECT FOR UPDATE as well as possible corner cases in UPDATE.
	 */
	if (bms_is_empty(modifiedCols))
	{
		if (pg_attribute_aclcheck_all(relOid, userid, requiredPerms,
									  ACLMASK_ANY) != ACLCHECK_OK)
			return false;
	}

	while ((col = bms_next_member(modifiedCols, col)) >= 0)
	{
		/* bit #s are offset by FirstLowInvalidHeapAttributeNumber */
		AttrNumber	attno = col + FirstLowInvalidHeapAttributeNumber;

		if (attno == InvalidAttrNumber)
		{
			/* whole-row reference can't happen here */
			elog(ERROR, "whole-row update is not implemented");
		}
		else
		{
			if (pg_attribute_aclcheck(relOid, attno, userid,
									  requiredPerms) != ACLCHECK_OK)
				return false;
		}
	}
	return true;
}

/*
 * ============================================================================
 * 【中文注释】ExecCheckXactReadOnly —— 只读事务/并行模式下的写入合规检查
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在事务只读（BEGIN READ ONLY / default_transaction_read_only）或正处于
 *   并行模式下时，逐关系检查计划是否包含（除 SELECT 之外的）写权限请求；
 *   若有，则调用 PreventCommandIfReadOnly / PreventCommandIfParallelMode
 *   抛出友好错误。
 *
 * 设计思想：
 *   1. 只读事务：temp 表的数据写放行（本地数据，不影响持久化）；普通表一律
 *      拒绝。
 *   2. 并行模式：条件更严格——连 temp 表也不允许写，因为并行支撑层尚未支持
 *      写操作（combo CID 哈希共享、heap_update 的 xmax 互斥等），宁可都禁。
 *   3. 之所以放行"只请求 SELECT 权限"的关系：SELECT FOR UPDATE 等带锁 SELECT
 *      的 perminfo 中只有 SELECT 位，其加锁动作由行锁路径单独管控，不在此列。
 *   4. 底层已有 CommandCounterIncrement 等处的防御性检查，这里属于"提前、
 *      友好地"把问题暴露出来（错误信息更人性化）。
 *   注：热备（Hot Standby）节点上不可能创建临时表，故无需区分对待。
 * ============================================================================
 */
static void
ExecCheckXactReadOnly(PlannedStmt *plannedstmt)
{
	ListCell   *l;

	/*
	 * Fail if write permissions are requested in parallel mode for table
	 * (temp or non-temp), otherwise fail for any non-temp table.
	 */
	foreach(l, plannedstmt->permInfos)
	{
		RTEPermissionInfo *perminfo = lfirst_node(RTEPermissionInfo, l);

		if ((perminfo->requiredPerms & (~ACL_SELECT)) == 0)
			continue;

		if (isTempNamespace(get_rel_namespace(perminfo->relid)))
			continue;

		PreventCommandIfReadOnly(CreateCommandName((Node *) plannedstmt));
	}

	if (plannedstmt->commandType != CMD_SELECT || plannedstmt->hasModifyingCTE)
		PreventCommandIfParallelMode(CreateCommandName((Node *) plannedstmt));
}


/*
 * ============================================================================
 * 【中文注释】InitPlan —— 计划树初始化（执行器启动的关键一步）
 * ----------------------------------------------------------------------------
 * 函数作用（按执行顺序）：
 *   1. 权限检查 ExecCheckPermissions；
 *   2. ExecInitRangeTable：初始化范围表（打开每个 RTE 对应的关系/子查询）；
 *   3. ExecDoInitialPruning：分区初始裁剪——按分区约束求出"本次执行不会触
 *      及的 Append/MergeAppend 子计划"，结果存 es_part_prune_results 位图，
 *      用于跳过无效子计划的初始化与执行；
 *   4. 由 PlanRowMark 列表构建 es_rowmarks（ExecRowMark 数组）。跳过：
 *      - 父关系行标记（isParent，运行时无用）;
 *      - 已被裁剪掉的子分区行标记；
 *      并按 markType 决定是否真正打开物理表（ROW_MARK_COPY 无需开表）。
 *   5. 逐个初始化子计划（subplan）：子计划不允许 BACKWARD/MARK/RESTORE，
 *      仅允许 REWIND 优化（id 在 plannedstmt->rewindPlanIDs 中的无参子计划）；
 *      必须先于主树初始化（ExecInitSubPlan 需要在 es_subplanstates 中登记）；
 *   6. ExecInitNode 初始化主计划树，得到 planstate；
 *   7. 取结果元组描述符 ExecGetResultType；SELECT 且顶层 tlist 含 resjunk
 *      （内部列，如 ctid/tableoid）时构造 JunkFilter，将结果类型换成"净化"
 *      后的类型（jf_cleanTupType），运行时逐行剔除这些内部列；
 *   8. 回填 queryDesc->tupDesc 与 queryDesc->planstate。
 *
 * 参数：
 *   queryDesc - 查询描述符（其 estate/plannedstmt 已在 standard_ExecutorStart
 *               中就绪）。
 *   eflags    - 顶层执行标志位，向下传导给所有子节点初始化。
 *
 * 设计思想：
 *   - "初始化与执行分离"：本函数只做准备工作（开文件、分配存储、建立状态），
 *     真正的取数发生在 ExecutorRun 阶段；
 *   - eflags 传导：BACKWARD/MARK/REWIND 等能力标志由顶层逐层传到 ExecutionNode，
 *     节点据此决定是否启用物化等可回退机制（例如支持 REVERSE-SCAN 的节点才能
 *     被游标反向滚动使用）。
 * ============================================================================
 */
static void
InitPlan(QueryDesc *queryDesc, int eflags)
{
	CmdType		operation = queryDesc->operation;
	PlannedStmt *plannedstmt = queryDesc->plannedstmt;
	Plan	   *plan = plannedstmt->planTree;
	List	   *rangeTable = plannedstmt->rtable;
	EState	   *estate = queryDesc->estate;
	PlanState  *planstate;
	TupleDesc	tupType;
	ListCell   *l;
	int			i;

	/*
	 * Do permissions checks
	 */
	ExecCheckPermissions(rangeTable, plannedstmt->permInfos, true);

	/*
	 * initialize the node's execution state
	 */
	ExecInitRangeTable(estate, rangeTable, plannedstmt->permInfos,
					   bms_copy(plannedstmt->unprunableRelids));

	estate->es_plannedstmt = plannedstmt;
	estate->es_part_prune_infos = plannedstmt->partPruneInfos;

	/*
	 * Perform runtime "initial" pruning to identify which child subplans,
	 * corresponding to the children of plan nodes that contain
	 * PartitionPruneInfo such as Append, will not be executed. The results,
	 * which are bitmapsets of indexes of the child subplans that will be
	 * executed, are saved in es_part_prune_results.  These results correspond
	 * to each PartitionPruneInfo entry, and the es_part_prune_results list is
	 * parallel to es_part_prune_infos.
	 */
	ExecDoInitialPruning(estate);

	/*
	 * Next, build the ExecRowMark array from the PlanRowMark(s), if any.
	 */
	if (plannedstmt->rowMarks)
	{
		estate->es_rowmarks = (ExecRowMark **)
			palloc0_array(ExecRowMark *, estate->es_range_table_size);
		foreach(l, plannedstmt->rowMarks)
		{
			PlanRowMark *rc = (PlanRowMark *) lfirst(l);
			RangeTblEntry *rte = exec_rt_fetch(rc->rti, estate);
			Oid			relid;
			Relation	relation;
			ExecRowMark *erm;

			/* ignore "parent" rowmarks; they are irrelevant at runtime */
			if (rc->isParent)
				continue;

			/*
			 * Also ignore rowmarks belonging to child tables that have been
			 * pruned in ExecDoInitialPruning().
			 */
			if (rte->rtekind == RTE_RELATION &&
				!bms_is_member(rc->rti, estate->es_unpruned_relids))
				continue;

			/* get relation's OID (will produce InvalidOid if subquery) */
			relid = rte->relid;

			/* open relation, if we need to access it for this mark type */
			switch (rc->markType)
			{
				case ROW_MARK_EXCLUSIVE:
				case ROW_MARK_NOKEYEXCLUSIVE:
				case ROW_MARK_SHARE:
				case ROW_MARK_KEYSHARE:
				case ROW_MARK_REFERENCE:
					relation = ExecGetRangeTableRelation(estate, rc->rti, false);
					break;
				case ROW_MARK_COPY:
					/* no physical table access is required */
					relation = NULL;
					break;
				default:
					elog(ERROR, "unrecognized markType: %d", rc->markType);
					relation = NULL;	/* keep compiler quiet */
					break;
			}

			/* Check that relation is a legal target for marking */
			if (relation)
				CheckValidRowMarkRel(relation, rc->markType);

			erm = palloc_object(ExecRowMark);
			erm->relation = relation;
			erm->relid = relid;
			erm->rti = rc->rti;
			erm->prti = rc->prti;
			erm->rowmarkId = rc->rowmarkId;
			erm->markType = rc->markType;
			erm->strength = rc->strength;
			erm->waitPolicy = rc->waitPolicy;
			erm->ermActive = false;
			ItemPointerSetInvalid(&(erm->curCtid));
			erm->ermExtra = NULL;

			Assert(erm->rti > 0 && erm->rti <= estate->es_range_table_size &&
				   estate->es_rowmarks[erm->rti - 1] == NULL);

			estate->es_rowmarks[erm->rti - 1] = erm;
		}
	}

	/*
	 * Initialize the executor's tuple table to empty.
	 */
	estate->es_tupleTable = NIL;

	/* signal that this EState is not used for EPQ */
	estate->es_epq_active = NULL;

	/*
	 * Initialize private state information for each SubPlan.  We must do this
	 * before running ExecInitNode on the main query tree, since
	 * ExecInitSubPlan expects to be able to find these entries.
	 */
	Assert(estate->es_subplanstates == NIL);
	i = 1;						/* subplan indices count from 1 */
	foreach(l, plannedstmt->subplans)
	{
		Plan	   *subplan = (Plan *) lfirst(l);
		PlanState  *subplanstate;
		int			sp_eflags;

		/*
		 * A subplan will never need to do BACKWARD scan nor MARK/RESTORE. If
		 * it is a parameterless subplan (not initplan), we suggest that it be
		 * prepared to handle REWIND efficiently; otherwise there is no need.
		 */
		sp_eflags = eflags
			& ~(EXEC_FLAG_REWIND | EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK);
		if (bms_is_member(i, plannedstmt->rewindPlanIDs))
			sp_eflags |= EXEC_FLAG_REWIND;

		subplanstate = ExecInitNode(subplan, estate, sp_eflags);

		estate->es_subplanstates = lappend(estate->es_subplanstates,
										   subplanstate);

		i++;
	}

	/*
	 * Initialize the private state information for all the nodes in the query
	 * tree.  This opens files, allocates storage and leaves us ready to start
	 * processing tuples.
	 */
	planstate = ExecInitNode(plan, estate, eflags);

	/*
	 * Get the tuple descriptor describing the type of tuples to return.
	 */
	tupType = ExecGetResultType(planstate);

	/*
	 * Initialize the junk filter if needed.  SELECT queries need a filter if
	 * there are any junk attrs in the top-level tlist.
	 */
	if (operation == CMD_SELECT)
	{
		bool		junk_filter_needed = false;
		ListCell   *tlist;

		foreach(tlist, plan->targetlist)
		{
			TargetEntry *tle = (TargetEntry *) lfirst(tlist);

			if (tle->resjunk)
			{
				junk_filter_needed = true;
				break;
			}
		}

		if (junk_filter_needed)
		{
			JunkFilter *j;
			TupleTableSlot *slot;

			slot = ExecInitExtraTupleSlot(estate, NULL, &TTSOpsVirtual);
			j = ExecInitJunkFilter(planstate->plan->targetlist,
								   slot);
			estate->es_junkFilter = j;

			/* Want to return the cleaned tuple type */
			tupType = j->jf_cleanTupType;
		}
	}

	queryDesc->tupDesc = tupType;
	queryDesc->planstate = planstate;
}

/*
 * ============================================================================
 * 【中文注释】CheckValidResultRel —— 校验"结果关系"是否为合法操作目标
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在（可能带分区路由的）DML 执行前，按结果关系的 relkind 校验是否允许执行
 *   该操作；通常解析器/计划器已经拦过一遍，这里是执行器的最后防线。
 *
 * 参数：
 *   resultRelInfo    - 目标关系信息（ri_RelationDesc 即目标 Relation）；
 *   operation        - 命令类型（INSERT/UPDATE/DELETE/MERGE）；
 *   onConflictAction - INSERT 的 ON CONFLICT 动作（ONCONFLICT_NONE 表示无）；
 *   mergeActions     - MERGE 的各 WHEN 动作列表（非 MERGE 传 NIL）；
 *   mtnode           - 所属 ModifyTable 计划节点（判断 FOR PORTION OF 用）。
 *
 * 各类 relkind 的合规规则（业务含义）：
 *   - 普通表/分区表：需 CheckCmdReplicaIdentity（逻辑复制要求复制标识位图上
 *     的关系才可更新/删除）；INSERT ON CONFLICT DO UPDATE 额外要求支持 UPDATE；
 *   - 序列/TOAST/属性图：绝不可改；
 *   - 视图：仅在存在匹配的 INSTEAD OF 触发器时可改；
 *   - 物化视图：当前仅允许"增量维护"模式下的改动；
 *   - 外部表：要求 FDW 提供 ExecForeignInsert/Update/Delete 能力，且
 *     IsForeignRelUpdatable 允许该操作；
 *   - 冲突日志表（逻辑复制冲突记录表）：系统托管，仅放行 DELETE 清理。
 * ============================================================================
 */
void
CheckValidResultRel(ResultRelInfo *resultRelInfo, CmdType operation,
					OnConflictAction onConflictAction, List *mergeActions,
					ModifyTable *mtnode)
{
	Relation	resultRel = resultRelInfo->ri_RelationDesc;
	FdwRoutine *fdwroutine;

	/* Expect a fully-formed ResultRelInfo from InitResultRelInfo(). */
	Assert(resultRelInfo->ri_needLockTagTuple ==
		   IsInplaceUpdateRelation(resultRel));

	switch (resultRel->rd_rel->relkind)
	{
		case RELKIND_RELATION:
		case RELKIND_PARTITIONED_TABLE:

			/*
			 * For MERGE, check that the target relation supports each action.
			 * For other operations, just check the operation itself.
			 */
			if (operation == CMD_MERGE)
				foreach_node(MergeAction, action, mergeActions)
					CheckCmdReplicaIdentity(resultRel, action->commandType);
			else
				CheckCmdReplicaIdentity(resultRel, operation);

			/*
			 * For INSERT ON CONFLICT DO UPDATE, additionally check that the
			 * target relation supports UPDATE.
			 */
			if (onConflictAction == ONCONFLICT_UPDATE)
				CheckCmdReplicaIdentity(resultRel, CMD_UPDATE);
			break;
		case RELKIND_SEQUENCE:
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot change sequence \"%s\"",
							RelationGetRelationName(resultRel))));
			break;
		case RELKIND_TOASTVALUE:
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot change TOAST relation \"%s\"",
							RelationGetRelationName(resultRel))));
			break;
		case RELKIND_VIEW:

			/*
			 * Okay only if there's a suitable INSTEAD OF trigger.  Otherwise,
			 * complain, but omit errdetail because we haven't got the
			 * information handy (and given that it really shouldn't happen,
			 * it's not worth great exertion to get).
			 */
			if (!view_has_instead_trigger(resultRel, operation, mergeActions))
				error_view_not_updatable(resultRel, operation, mergeActions,
										 NULL);
			break;
		case RELKIND_MATVIEW:
			if (!MatViewIncrementalMaintenanceIsEnabled())
				ereport(ERROR,
						(errcode(ERRCODE_WRONG_OBJECT_TYPE),
						 errmsg("cannot change materialized view \"%s\"",
								RelationGetRelationName(resultRel))));
			break;
		case RELKIND_FOREIGN_TABLE:
			/* We don't support FOR PORTION OF FDW queries. */
			if (mtnode && mtnode->forPortionOf)
				ereport(ERROR,
						errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						errmsg("foreign tables don't support FOR PORTION OF"),
						errdetail("\"%s\" is a foreign table.",
								  RelationGetRelationName(resultRel)));

			/* Okay only if the FDW supports it */
			fdwroutine = resultRelInfo->ri_FdwRoutine;
			switch (operation)
			{
				case CMD_INSERT:
					if (fdwroutine->ExecForeignInsert == NULL)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("cannot insert into foreign table \"%s\"",
										RelationGetRelationName(resultRel))));
					if (fdwroutine->IsForeignRelUpdatable != NULL &&
						(fdwroutine->IsForeignRelUpdatable(resultRel) & (1 << CMD_INSERT)) == 0)
						ereport(ERROR,
								(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
								 errmsg("foreign table \"%s\" does not allow inserts",
										RelationGetRelationName(resultRel))));
					break;
				case CMD_UPDATE:
					if (fdwroutine->ExecForeignUpdate == NULL)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("cannot update foreign table \"%s\"",
										RelationGetRelationName(resultRel))));
					if (fdwroutine->IsForeignRelUpdatable != NULL &&
						(fdwroutine->IsForeignRelUpdatable(resultRel) & (1 << CMD_UPDATE)) == 0)
						ereport(ERROR,
								(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
								 errmsg("foreign table \"%s\" does not allow updates",
										RelationGetRelationName(resultRel))));
					break;
				case CMD_DELETE:
					if (fdwroutine->ExecForeignDelete == NULL)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("cannot delete from foreign table \"%s\"",
										RelationGetRelationName(resultRel))));
					if (fdwroutine->IsForeignRelUpdatable != NULL &&
						(fdwroutine->IsForeignRelUpdatable(resultRel) & (1 << CMD_DELETE)) == 0)
						ereport(ERROR,
								(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
								 errmsg("foreign table \"%s\" does not allow deletes",
										RelationGetRelationName(resultRel))));
					break;
				default:
					elog(ERROR, "unrecognized CmdType: %d", (int) operation);
					break;
			}
			break;
		case RELKIND_PROPGRAPH:
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot change property graph \"%s\"",
							RelationGetRelationName(resultRel))));
			break;
		default:
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot change relation \"%s\"",
							RelationGetRelationName(resultRel))));
			break;
	}

	/*
	 * Conflict log tables are managed by the system to record logical
	 * replication conflicts.  We allow DELETE and TRUNCATE to permit users to
	 * manually prune these logs, but manual data insertion or modification
	 * (INSERT, UPDATE, MERGE) is prohibited to maintain the integrity of the
	 * system-generated logs.
	 *
	 * Since TRUNCATE is handled as a separate utility command, we only need
	 * to explicitly permit CMD_DELETE here.
	 */
	if (IsConflictLogTableNamespace(RelationGetNamespace(resultRel)) &&
		operation != CMD_DELETE)
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("cannot modify or insert data into conflict log table \"%s\"",
						RelationGetRelationName(resultRel)),
				 errdetail("Conflict log tables are system-managed and only support cleanup using DELETE or TRUNCATE.")));
}

/*
 * ============================================================================
 * 【中文注释】CheckValidRowMarkRel —— 校验"行标记目标"是否为合法锁定目标
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   SELECT FOR [KEY] UPDATE/SHARE 中每个被锁定的关系，在执行前校验其
 *   relkind 是否允许加行锁。大部分情况解析器/计划器已拦截，这里是兜底。
 *
 * 参数：
 *   rel      - 被锁定关系；
 *   markType - 行标记类型（EXCLUSIVE / NOKEYEXCLUSIVE / SHARE / KEYSHARE /
 *              REFERENCE / COPY）。
 *
 * 各类 relkind 的合规规则：
 *   - 普通表/分区表：允许；
 *   - 序列：不允许（VACUUM 不清理序列，行锁管理无从谈起）；
 *   - TOAST：无理由放行，拒绝；
 *   - 视图：不应出现（计划器必然先展开视图）；
 *   - 物化视图：仅允许 ROW_MARK_REFERENCE（普通子查询式的整行引用），
 *     真正的 SELECT FOR UPDATE 锁定不允许；
 *   - 外部表：要求 FDW 提供 RefetchForeignRow（EPQ 重取行版本能力）；
 *   - 冲突日志表：系统托管，一律拒绝。
 * ============================================================================
 */
static void
CheckValidRowMarkRel(Relation rel, RowMarkType markType)
{
	FdwRoutine *fdwroutine;

	switch (rel->rd_rel->relkind)
	{
		case RELKIND_RELATION:
		case RELKIND_PARTITIONED_TABLE:
			/* OK */
			break;
		case RELKIND_SEQUENCE:
			/* Must disallow this because we don't vacuum sequences */
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot lock rows in sequence \"%s\"",
							RelationGetRelationName(rel))));
			break;
		case RELKIND_TOASTVALUE:
			/* We could allow this, but there seems no good reason to */
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot lock rows in TOAST relation \"%s\"",
							RelationGetRelationName(rel))));
			break;
		case RELKIND_VIEW:
			/* Should not get here; planner should have expanded the view */
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot lock rows in view \"%s\"",
							RelationGetRelationName(rel))));
			break;
		case RELKIND_MATVIEW:
			/* Allow referencing a matview, but not actual locking clauses */
			if (markType != ROW_MARK_REFERENCE)
				ereport(ERROR,
						(errcode(ERRCODE_WRONG_OBJECT_TYPE),
						 errmsg("cannot lock rows in materialized view \"%s\"",
								RelationGetRelationName(rel))));
			break;
		case RELKIND_FOREIGN_TABLE:
			/* Okay only if the FDW supports it */
			fdwroutine = GetFdwRoutineForRelation(rel, false);
			if (fdwroutine->RefetchForeignRow == NULL)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("cannot lock rows in foreign table \"%s\"",
								RelationGetRelationName(rel))));
			break;
		case RELKIND_PROPGRAPH:
			/* Should not get here; rewriter should have expanded the graph */
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg_internal("cannot lock rows in property graph \"%s\"",
									 RelationGetRelationName(rel))));
			break;
		default:
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot lock rows in relation \"%s\"",
							RelationGetRelationName(rel))));
			break;
	}

	/*
	 * Conflict log tables are managed by the system to record logical
	 * replication conflicts.
	 */
	if (IsConflictLogTableNamespace(RelationGetNamespace(rel)))
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("cannot lock rows in the conflict log table \"%s\"",
						RelationGetRelationName(rel))));
}

/*
 * ============================================================================
 * 【中文注释】InitResultRelInfo —— 初始化一个结果关系的 ResultRelInfo
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   清零并填充 ResultRelInfo 的基础字段：RTE 索引、关系描述符、触发器描述
 *   拷贝（TrigDesc）、触发器函数数组（ri_TrigFunctions）、FDW 例程句柄
 *   （外部表时）、分区路由相关的根关系/映射字段等。索引与约束等字段留待
 *   调用方（ExecInitModifyTable / ExecInitPartitionInfo）按需补充。
 *
 * 参数：
 *   resultRelInfo      - 待初始化结构（由调用方分配）;
 *   resultRelationDesc - 目标 Relation（relcache 项）;
 *   resultRelationIndex- 范围表索引（触发器专用 ResultRelInfo 传 0 占位）;
 *   partition_root_rri - 分区根结果关系（仅分区路由初始化时传非 NULL）;
 *   instrument_options - 触发器计时选项（EXPLAIN ANALYZE 用，0 表示不计时）。
 *
 * 设计思想：
 *   1. 深拷贝 TrigDesc：relcache 中的触发器描述可能在语句执行期间因 DDL 而
 *      失效重建，故执行器持有独立拷贝，保证执行期触发器集合稳定；
 *   2. ri_needLockTagTuple：行级 LOCK 语义需要的"锁标签元组"仅对就地更新
 *      关系（in-place update，例如无 toast 的主键修改）为真，由
 *      IsInplaceUpdateRelation 判定并缓存；
 *   3. ri_RootResultRelInfo / 根子映射：分区表插入时，输入元组按根表行类型
 *      计算路由，到达具体分区后按需做列映射（RootToChild / ChildToRoot），
 *      这些字段在 ExecInitPartitionInfo 等阶段填充。
 * ============================================================================
 */
void
InitResultRelInfo(ResultRelInfo *resultRelInfo,
				  Relation resultRelationDesc,
				  Index resultRelationIndex,
				  ResultRelInfo *partition_root_rri,
				  int instrument_options)
{
	MemSet(resultRelInfo, 0, sizeof(ResultRelInfo));
	resultRelInfo->type = T_ResultRelInfo;
	resultRelInfo->ri_RangeTableIndex = resultRelationIndex;
	resultRelInfo->ri_RelationDesc = resultRelationDesc;
	resultRelInfo->ri_NumIndices = 0;
	resultRelInfo->ri_IndexRelationDescs = NULL;
	resultRelInfo->ri_IndexRelationInfo = NULL;
	resultRelInfo->ri_needLockTagTuple =
		IsInplaceUpdateRelation(resultRelationDesc);
	/* make a copy so as not to depend on relcache info not changing... */
	resultRelInfo->ri_TrigDesc = CopyTriggerDesc(resultRelationDesc->trigdesc);
	if (resultRelInfo->ri_TrigDesc)
	{
		int			n = resultRelInfo->ri_TrigDesc->numtriggers;

		resultRelInfo->ri_TrigFunctions = (FmgrInfo *)
			palloc0_array(FmgrInfo, n);
		resultRelInfo->ri_TrigWhenExprs = (ExprState **)
			palloc0_array(ExprState *, n);
		if (instrument_options)
			resultRelInfo->ri_TrigInstrument = InstrAllocTrigger(n, instrument_options);
	}
	else
	{
		resultRelInfo->ri_TrigFunctions = NULL;
		resultRelInfo->ri_TrigWhenExprs = NULL;
		resultRelInfo->ri_TrigInstrument = NULL;
	}
	if (resultRelationDesc->rd_rel->relkind == RELKIND_FOREIGN_TABLE)
		resultRelInfo->ri_FdwRoutine = GetFdwRoutineForRelation(resultRelationDesc, true);
	else
		resultRelInfo->ri_FdwRoutine = NULL;

	/* The following fields are set later if needed */
	resultRelInfo->ri_RowIdAttNo = 0;
	resultRelInfo->ri_extraUpdatedCols = NULL;
	resultRelInfo->ri_projectNew = NULL;
	resultRelInfo->ri_newTupleSlot = NULL;
	resultRelInfo->ri_oldTupleSlot = NULL;
	resultRelInfo->ri_projectNewInfoValid = false;
	resultRelInfo->ri_FdwState = NULL;
	resultRelInfo->ri_usesFdwDirectModify = false;
	resultRelInfo->ri_CheckConstraintExprs = NULL;
	resultRelInfo->ri_GenVirtualNotNullConstraintExprs = NULL;
	resultRelInfo->ri_GeneratedExprsI = NULL;
	resultRelInfo->ri_GeneratedExprsU = NULL;
	resultRelInfo->ri_projectReturning = NULL;
	resultRelInfo->ri_onConflictArbiterIndexes = NIL;
	resultRelInfo->ri_onConflict = NULL;
	resultRelInfo->ri_forPortionOf = NULL;
	resultRelInfo->ri_ReturningSlot = NULL;
	resultRelInfo->ri_TrigOldSlot = NULL;
	resultRelInfo->ri_TrigNewSlot = NULL;
	resultRelInfo->ri_AllNullSlot = NULL;
	resultRelInfo->ri_MergeActions[MERGE_WHEN_MATCHED] = NIL;
	resultRelInfo->ri_MergeActions[MERGE_WHEN_NOT_MATCHED_BY_SOURCE] = NIL;
	resultRelInfo->ri_MergeActions[MERGE_WHEN_NOT_MATCHED_BY_TARGET] = NIL;
	resultRelInfo->ri_MergeJoinCondition = NULL;

	/*
	 * Only ExecInitPartitionInfo() and ExecInitPartitionDispatchInfo() pass
	 * non-NULL partition_root_rri.  For child relations that are part of the
	 * initial query rather than being dynamically added by tuple routing,
	 * this field is filled in ExecInitModifyTable().
	 */
	resultRelInfo->ri_RootResultRelInfo = partition_root_rri;
	/* Set by ExecGetRootToChildMap */
	resultRelInfo->ri_RootToChildMap = NULL;
	resultRelInfo->ri_RootToChildMapValid = false;
	/* Set by ExecInitRoutingInfo */
	resultRelInfo->ri_PartitionTupleSlot = NULL;
	resultRelInfo->ri_ChildToRootMap = NULL;
	resultRelInfo->ri_ChildToRootMapValid = false;
	resultRelInfo->ri_CopyMultiInsertBuffer = NULL;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetTriggerResultRel —— 获取（或新建缓存）触发器目标关系信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回 relid 对应关系的 ResultRelInfo，用于该关系上触发器的执行环境。
 *
 * 触发器的目标关系多数情况就是查询的结果关系，直接复用已有条目；但有时
 * 需要把触发器开在"其他表"上——典型场景：外键（RI）UPDATE 触发器由被引用
 * 表上新增的触发器事件级联触发，此时引用表并非本查询的结果关系。为了避免
 * 反复打开表，这里把新创建的 ResultRelInfo 缓存在 es_trig_target_relations。
 *
 * 参数：
 *   estate       - 执行状态；
 *   relid        - 目标关系 OID；
 *   rootRelInfo  - 触发发生时的根结果关系（分区场景下，不同分区触发可能要求
 *                  不同的根关系，做匹配缓存以区分）。
 *
 * 设计思想：
 *   1. 三级查找缓存：先查 es_opened_result_relations（查询结果关系）、再查
 *      es_tuple_routing_result_relations（分区路由期动态创建的分区结果关系）、
 *      最后查 es_trig_target_relations（历史触发器目标），命中即返回，避免
 *      重复 open/close；
 *   2. 新建条目放 es_query_cxt（随查询整体释放）；
 *   3. 不检查 relkind、不加锁：假定触发器事件入队时锁仍被持有（事件入队即
 *      意味着该关系已在本事务加锁）；暂不 OpenIndices——触发器执行不需要
 *      索引信息；
 *   4. 结果关系复用注意：ri_RootResultRelInfo 必须一致才命中，防止分区混合
 *      触发场景下根关系语义错乱。
 * ============================================================================
 */
ResultRelInfo *
ExecGetTriggerResultRel(EState *estate, Oid relid,
						ResultRelInfo *rootRelInfo)
{
	ResultRelInfo *rInfo;
	ListCell   *l;
	Relation	rel;
	MemoryContext oldcontext;

	/*
	 * Before creating a new ResultRelInfo, check if we've already made and
	 * cached one for this relation.  We must ensure that the given
	 * 'rootRelInfo' matches the one stored in the cached ResultRelInfo as
	 * trigger handling for partitions can result in mixed requirements for
	 * what ri_RootResultRelInfo is set to.
	 */

	/* Search through the query result relations */
	foreach(l, estate->es_opened_result_relations)
	{
		rInfo = lfirst(l);
		if (RelationGetRelid(rInfo->ri_RelationDesc) == relid &&
			rInfo->ri_RootResultRelInfo == rootRelInfo)
			return rInfo;
	}

	/*
	 * Search through the result relations that were created during tuple
	 * routing, if any.
	 */
	foreach(l, estate->es_tuple_routing_result_relations)
	{
		rInfo = (ResultRelInfo *) lfirst(l);
		if (RelationGetRelid(rInfo->ri_RelationDesc) == relid &&
			rInfo->ri_RootResultRelInfo == rootRelInfo)
			return rInfo;
	}

	/* Nope, but maybe we already made an extra ResultRelInfo for it */
	foreach(l, estate->es_trig_target_relations)
	{
		rInfo = (ResultRelInfo *) lfirst(l);
		if (RelationGetRelid(rInfo->ri_RelationDesc) == relid &&
			rInfo->ri_RootResultRelInfo == rootRelInfo)
			return rInfo;
	}
	/* Nope, so we need a new one */

	/*
	 * Open the target relation's relcache entry.  We assume that an
	 * appropriate lock is still held by the backend from whenever the trigger
	 * event got queued, so we need take no new lock here.  Also, we need not
	 * recheck the relkind, so no need for CheckValidResultRel.
	 */
	rel = table_open(relid, NoLock);

	/*
	 * Make the new entry in the right context.
	 */
	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);
	rInfo = makeNode(ResultRelInfo);
	InitResultRelInfo(rInfo,
					  rel,
					  0,		/* dummy rangetable index */
					  rootRelInfo,
					  estate->es_instrument);
	estate->es_trig_target_relations =
		lappend(estate->es_trig_target_relations, rInfo);
	MemoryContextSwitchTo(oldcontext);

	/*
	 * Currently, we don't need any index information in ResultRelInfos used
	 * only for triggers, so no need to call ExecOpenIndices.
	 */

	return rInfo;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetAncestorResultRels —— 获取分区叶节点到查询根目标的祖宗链
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对给定的叶分区结果关系，返回从"查询中的根目标表"到该叶分区之间所有
 *   中间分区祖先的 ResultRelInfo 列表（含根表本身）。首次调用时构建并缓存
 *   在 ri_ancestorResultRels，后续直接复用。
 *
 * 业务场景：
 *   分区表上触发器的执行需要沿分区层级逐级生成 OLD/NEW 行（例如上级分区
 *   的 BEFORE UPDATE 触发器要看到的是"按上级行类型转换"的行），故需要整条
 *   祖先链。
 *
 * 设计思想：
 *   - get_partition_ancestors 返回从叶向上到根的 OID 列表；遍历时遇到根表
 *     OID 即停止（根表用 ri_RootResultRelInfo 而非新建条目）；
 *   - 祖先关系用 NoLock 打开：计划器或 AcquireExecutorLocks 已经持有锁；
 *   - 祖先列表存于叶节点自己的上下文，随查询结束释放；也不 OpenIndices。
 *   - 该列表与 ExecGetTriggerResultRel 的缓存分开维护，由
 *     ExecCloseResultRelations 统一关闭。
 * ============================================================================
 */
List *
ExecGetAncestorResultRels(EState *estate, ResultRelInfo *resultRelInfo)
{
	ResultRelInfo *rootRelInfo = resultRelInfo->ri_RootResultRelInfo;
	Relation	partRel = resultRelInfo->ri_RelationDesc;
	Oid			rootRelOid;

	if (!partRel->rd_rel->relispartition)
		elog(ERROR, "cannot find ancestors of a non-partition result relation");
	Assert(rootRelInfo != NULL);
	rootRelOid = RelationGetRelid(rootRelInfo->ri_RelationDesc);
	if (resultRelInfo->ri_ancestorResultRels == NIL)
	{
		ListCell   *lc;
		List	   *oids = get_partition_ancestors(RelationGetRelid(partRel));
		List	   *ancResultRels = NIL;

		foreach(lc, oids)
		{
			Oid			ancOid = lfirst_oid(lc);
			Relation	ancRel;
			ResultRelInfo *rInfo;

			/*
			 * Ignore the root ancestor here, and use ri_RootResultRelInfo
			 * (below) for it instead.  Also, we stop climbing up the
			 * hierarchy when we find the table that was mentioned in the
			 * query.
			 */
			if (ancOid == rootRelOid)
				break;

			/*
			 * All ancestors up to the root target relation must have been
			 * locked by the planner or AcquireExecutorLocks().
			 */
			ancRel = table_open(ancOid, NoLock);
			rInfo = makeNode(ResultRelInfo);

			/* dummy rangetable index */
			InitResultRelInfo(rInfo, ancRel, 0, NULL,
							  estate->es_instrument);
			ancResultRels = lappend(ancResultRels, rInfo);
		}
		ancResultRels = lappend(ancResultRels, rootRelInfo);
		resultRelInfo->ri_ancestorResultRels = ancResultRels;
	}

	/* We must have found some ancestor */
	Assert(resultRelInfo->ri_ancestorResultRels != NIL);

	return resultRelInfo->ri_ancestorResultRels;
}

/*
 * ============================================================================
 * 【中文注释】ExecPostprocessPlan —— 计划收尾处理（ExecutorFinish 的第一步）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 es_auxmodifytables 中的每个"辅助 ModifyTable 节点"（修改 CTE 对应的
 *   DML 子树）驱动到结束（一直取行直到返回 NULL），确保其副作用完整、可预测。
 *
 * 业务背景：
 *   形如 "WITH ins AS (INSERT ... RETURNING ...) SELECT ... FROM ins" 的语句
 *   中，主 SELECT 由 ModifyTable 左侧子节点输出；若主查询提前截断（LIMIT /
 *   游标分批），插入可能只做了一部分——SQL 规范要求 WITH 里的 DML 必须全部
 *   执行完毕，因此 Finish 阶段兜底跑完。
 *
 * 设计思想：
 *   - 先把 es_direction 强制设为正向：截断发生时方向可能停留在其他状态；
 *   - 每轮取数前 ResetPerTupleExprContext，保证表达式求值上下文不累积；
 *   - 此阶段运行时已无 `count` 限制，一直跑到计划树返回空行。
 * ============================================================================
 */
static void
ExecPostprocessPlan(EState *estate)
{
	ListCell   *lc;

	/*
	 * Make sure nodes run forward.
	 */
	estate->es_direction = ForwardScanDirection;

	/*
	 * Run any secondary ModifyTable nodes to completion, in case the main
	 * query did not fetch all rows from them.  (We do this to ensure that
	 * such nodes have predictable results.)
	 */
	foreach(lc, estate->es_auxmodifytables)
	{
		PlanState  *ps = (PlanState *) lfirst(lc);

		for (;;)
		{
			TupleTableSlot *slot;

			/* Reset the per-output-tuple exprcontext each time */
			ResetPerTupleExprContext(estate);

			slot = ExecProcNode(ps);

			if (TupIsNull(slot))
				break;
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEndPlan —— 计划树清理（ExecutorEnd 的核心）
 * ----------------------------------------------------------------------------
 * 函数作用（按顺序）：
 *   1. ExecEndNode 关闭主计划树；
 *   2. 逐个关闭子计划（subplanstate）；
 *   3. ExecResetTupleTable(es_tupleTable, false)：释放元组表（重点：释放
 *      Buffer pin 与 tupdesc 引用计数；槽对象内存随上下文整体释放，无需 pfree）；
 *   4. ExecCloseResultRelations：关闭结果关系及其索引、祖先关系、触发器目标；
 *   5. ExecCloseRangeTableRelations：关闭范围表打开的全部关系（不加锁释放，
 *      锁由事务级别统一管理）。
 *
 * 设计思想：
 *   内存管理哲学：本文件刻意"不逐一担心内存释放"——FreeExecutorState 会
 *   保证释放所有内存；这里只做"必须显式做"的事：关闭关系（含锁标签语义）、
 *   丢弃 Buffer pin。
 * ============================================================================
 */
static void
ExecEndPlan(PlanState *planstate, EState *estate)
{
	ListCell   *l;

	/*
	 * shut down the node-type-specific query processing
	 */
	ExecEndNode(planstate);

	/*
	 * for subplans too
	 */
	foreach(l, estate->es_subplanstates)
	{
		PlanState  *subplanstate = (PlanState *) lfirst(l);

		ExecEndNode(subplanstate);
	}

	/*
	 * destroy the executor's tuple table.  Actually we only care about
	 * releasing buffer pins and tupdesc refcounts; there's no need to pfree
	 * the TupleTableSlots, since the containing memory context is about to go
	 * away anyway.
	 */
	ExecResetTupleTable(estate->es_tupleTable, false);

	/*
	 * Close any Relations that have been opened for range table entries or
	 * result relations.
	 */
	ExecCloseResultRelations(estate);
	ExecCloseRangeTableRelations(estate);
}

/*
 * ============================================================================
 * 【中文注释】ExecCloseResultRelations —— 关闭所有结果关系及其伴随关系
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   1. 对每个查询结果关系：ExecCloseIndices 关闭其索引（关系本身由
 *      ExecCloseRangeTableRelations 关闭）；再关闭其祖先链中 RTE 索引为 0
 *      （动态建立的 stub 祖先）的关系——根祖先（RTE 索引 > 0）归范围表关闭；
 *   2. 关闭 es_trig_target_relations 中为触发器打开的关系（全部为 RTE 索引 0
 *      的"哑"条目，且未开索引，直接 table_close 即可）。
 *
 * 设计思想：
 *   关闭顺序与所有权清晰划分：Query 直接引用的关系由范围表模块统一关闭；
 *   执行期动态打开的关系（分区祖先、触发器目标）在这里关闭，避免重复关闭。
 * ============================================================================
 */
void
ExecCloseResultRelations(EState *estate)
{
	ListCell   *l;

	/*
	 * close indexes of result relation(s) if any.  (Rels themselves are
	 * closed in ExecCloseRangeTableRelations())
	 *
	 * In addition, close the stub RTs that may be in each resultrel's
	 * ri_ancestorResultRels.
	 */
	foreach(l, estate->es_opened_result_relations)
	{
		ResultRelInfo *resultRelInfo = lfirst(l);
		ListCell   *lc;

		ExecCloseIndices(resultRelInfo);
		foreach(lc, resultRelInfo->ri_ancestorResultRels)
		{
			ResultRelInfo *rInfo = lfirst(lc);

			/*
			 * Ancestors with RTI > 0 (should only be the root ancestor) are
			 * closed by ExecCloseRangeTableRelations.
			 */
			if (rInfo->ri_RangeTableIndex > 0)
				continue;

			table_close(rInfo->ri_RelationDesc, NoLock);
		}
	}

	/* Close any relations that have been opened by ExecGetTriggerResultRel(). */
	foreach(l, estate->es_trig_target_relations)
	{
		ResultRelInfo *resultRelInfo = (ResultRelInfo *) lfirst(l);

		/*
		 * Assert this is a "dummy" ResultRelInfo, see above.  Otherwise we
		 * might be issuing a duplicate close against a Relation opened by
		 * ExecGetRangeTableRelation.
		 */
		Assert(resultRelInfo->ri_RangeTableIndex == 0);

		/*
		 * Since ExecGetTriggerResultRel doesn't call ExecOpenIndices for
		 * these rels, we needn't call ExecCloseIndices either.
		 */
		Assert(resultRelInfo->ri_NumIndices == 0);

		table_close(resultRelInfo->ri_RelationDesc, NoLock);
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecCloseRangeTableRelations —— 关闭范围表打开的全部关系
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历 estate->es_relations[]，把所有 ExecGetRangeTableRelation 打开的关系
 *   用 table_close(NoLock) 关闭。注意：不释放任何行锁/表锁——锁由事务系统
 *   统一管理，将在提交/回滚时自动释放。
 * ============================================================================
 */
void
ExecCloseRangeTableRelations(EState *estate)
{
	int			i;

	for (i = 0; i < estate->es_range_table_size; i++)
	{
		if (estate->es_relations[i])
			table_close(estate->es_relations[i], NoLock);
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecutePlan —— 执行器主取数循环（ExecutorRun 的核心）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按给定方向驱动计划树，直至：
 *   - 取到 numberTuples 行（numberTuples=0 表示不限量，跑到计划结束）；或
 *   - 计划树返回空行（TupIsNull）；或
 *   - 目标接收器表示不再接收（receiveSlot 返回 false，通常客户端断开）。
 *
 * 主循环流程图：
 *
 *   ┌──────────── 循环开始 ────────────┐
 *   │ ResetPerTupleExprContext         │  ← 重置每行表达式上下文（防泄漏）
 *   │ slot = ExecProcNode(planstate)   │  ← 自顶向下驱动计划树取一行
 *   │ slot 为空 ? ─── 是 ──→ 退出循环
 *   │ 否 │
 *   │ 有 junkFilter ? ── 是 ──→ slot = ExecFilterJunk(...)  ← 剔除内部列
 *   │ sendTuples ? ── 是 ──→ dest->receiveSlot(slot, dest)  ← 输出
 *   │                       接收器拒绝 ? ── 是 ──→ 退出循环
 *   │ SELECT ? ── 是 ──→ es_processed++   （DML 行数由 ModifyTable 自计）
 *   │ count 达限 ? ── 是 ──→ 退出循环
 *   └─────────────────────────────────┘
 *
 * 其他要点：
 *   - 并行模式（use_parallel_mode）：仅当"未执行过"且"无行数上限"时启用；
 *     并行计划只支持一口气跑完，中途截断或二次执行都必须退回串行；
 *   - 明确不需要向后退（无 EXEC_FLAG_BACKWARD）时，提前 ExecShutdownNode
 *     释放并行 worker 等资源，优化内存占用；
 *   - 每次 ExecutorRun 调用前 queryDesc->already_executed 置 1，保证
 *     二次调用不会意外进入并行。
 *
 * 参数：
 *   queryDesc    - 查询描述符；operation/sendTuples/direction/count 见上。
 * ============================================================================
 */
static void
ExecutePlan(QueryDesc *queryDesc,
			CmdType operation,
			bool sendTuples,
			uint64 numberTuples,
			ScanDirection direction,
			DestReceiver *dest)
{
	EState	   *estate = queryDesc->estate;
	PlanState  *planstate = queryDesc->planstate;
	bool		use_parallel_mode;
	TupleTableSlot *slot;
	uint64		current_tuple_count;

	/*
	 * initialize local variables
	 */
	current_tuple_count = 0;

	/*
	 * Set the direction.
	 */
	estate->es_direction = direction;

	/*
	 * Set up parallel mode if appropriate.
	 *
	 * Parallel mode only supports complete execution of a plan.  If we've
	 * already partially executed it, or if the caller asks us to exit early,
	 * we must force the plan to run without parallelism.
	 */
	if (queryDesc->already_executed || numberTuples != 0)
		use_parallel_mode = false;
	else
		use_parallel_mode = queryDesc->plannedstmt->parallelModeNeeded;
	queryDesc->already_executed = true;

	estate->es_use_parallel_mode = use_parallel_mode;
	if (use_parallel_mode)
		EnterParallelMode();

	/*
	 * Loop until we've processed the proper number of tuples from the plan.
	 */
	for (;;)
	{
		/* Reset the per-output-tuple exprcontext */
		ResetPerTupleExprContext(estate);

		/*
		 * Execute the plan and obtain a tuple
		 */
		slot = ExecProcNode(planstate);

		/*
		 * if the tuple is null, then we assume there is nothing more to
		 * process so we just end the loop...
		 */
		if (TupIsNull(slot))
			break;

		/*
		 * If we have a junk filter, then project a new tuple with the junk
		 * removed.
		 *
		 * Store this new "clean" tuple in the junkfilter's resultSlot.
		 * (Formerly, we stored it back over the "dirty" tuple, which is WRONG
		 * because that tuple slot has the wrong descriptor.)
		 */
		if (estate->es_junkFilter != NULL)
			slot = ExecFilterJunk(estate->es_junkFilter, slot);

		/*
		 * If we are supposed to send the tuple somewhere, do so. (In
		 * practice, this is probably always the case at this point.)
		 */
		if (sendTuples)
		{
			/*
			 * If we are not able to send the tuple, we assume the destination
			 * has closed and no more tuples can be sent. If that's the case,
			 * end the loop.
			 */
			if (!dest->receiveSlot(slot, dest))
				break;
		}

		/*
		 * Count tuples processed, if this is a SELECT.  (For other operation
		 * types, the ModifyTable plan node must count the appropriate
		 * events.)
		 */
		if (operation == CMD_SELECT)
			(estate->es_processed)++;

		/*
		 * check our tuple count.. if we've processed the proper number then
		 * quit, else loop again and process more tuples.  Zero numberTuples
		 * means no limit.
		 */
		current_tuple_count++;
		if (numberTuples && numberTuples == current_tuple_count)
			break;
	}

	/*
	 * If we know we won't need to back up, we can release resources at this
	 * point.
	 */
	if (!(estate->es_top_eflags & EXEC_FLAG_BACKWARD))
		ExecShutdownNode(planstate);

	if (use_parallel_mode)
		ExitParallelMode();
}


/*
 * ============================================================================
 * 【中文注释】ExecRelCheck —— 检查元组是否满足结果关系的 CHECK 约束
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   逐条评估目标表的 CHECK 约束表达式（配置在系统表 pg_constraint 中，经
 *   relcache 的 rd_att->constr 缓存为可执行形式）。全部通过返回 NULL；
 *   违反则返回约束名 ccname（由调用方构造报错）。
 *
 * 参数：
 *   resultRelInfo - 目标关系信息；slot - 待检查元组；estate - 执行状态。
 *
 * 设计思想：
 *   1. 惰性编译：首次调用时把每个约束的 ccbin（存储的表达式树文本）经
 *      stringToNode 反序列化、展开生成列表达式（expand_generated_columns_
 *      in_expr）、再用 ExecPrepareExpr 编译成 ExprState，缓存进
 *      ri_CheckConstraintExprs（按约束下标一一对应，NOT ENFORCED 的约束
 *      留 NULL 跳过）——编译开销只付一次（首次触碰该结果关系的那一行）；
 *   2. 求值语义：用 ExecCheck 而非 ExecQual——SQL 规定约束表达式结果为
 *      NULL 视为通过（NULL 不是失败）；
 *   3. 一致性防御：relcache 中实际装载的约束条数少于 relchecks 时直接
 *      ERROR，防止静默漏检（可能破坏数据完整性）。
 * ============================================================================
 */
static const char *
ExecRelCheck(ResultRelInfo *resultRelInfo,
			 TupleTableSlot *slot, EState *estate)
{
	Relation	rel = resultRelInfo->ri_RelationDesc;
	int			ncheck = rel->rd_att->constr->num_check;
	ConstrCheck *check = rel->rd_att->constr->check;
	ExprContext *econtext;
	MemoryContext oldContext;

	/*
	 * CheckNNConstraintFetch let this pass with only a warning, but now we
	 * should fail rather than possibly failing to enforce an important
	 * constraint.
	 */
	if (ncheck != rel->rd_rel->relchecks)
		elog(ERROR, "%d pg_constraint record(s) missing for relation \"%s\"",
			 rel->rd_rel->relchecks - ncheck, RelationGetRelationName(rel));

	/*
	 * If first time through for this result relation, build expression
	 * nodetrees for rel's constraint expressions.  Keep them in the per-query
	 * memory context so they'll survive throughout the query.
	 */
	if (resultRelInfo->ri_CheckConstraintExprs == NULL)
	{
		oldContext = MemoryContextSwitchTo(estate->es_query_cxt);
		resultRelInfo->ri_CheckConstraintExprs = palloc0_array(ExprState *, ncheck);
		for (int i = 0; i < ncheck; i++)
		{
			Expr	   *checkconstr;

			/* Skip not enforced constraint */
			if (!check[i].ccenforced)
				continue;

			checkconstr = stringToNode(check[i].ccbin);
			checkconstr = (Expr *) expand_generated_columns_in_expr((Node *) checkconstr, rel, 1);
			resultRelInfo->ri_CheckConstraintExprs[i] =
				ExecPrepareExpr(checkconstr, estate);
		}
		MemoryContextSwitchTo(oldContext);
	}

	/*
	 * We will use the EState's per-tuple context for evaluating constraint
	 * expressions (creating it if it's not already there).
	 */
	econtext = GetPerTupleExprContext(estate);

	/* Arrange for econtext's scan tuple to be the tuple under test */
	econtext->ecxt_scantuple = slot;

	/* And evaluate the constraints */
	for (int i = 0; i < ncheck; i++)
	{
		ExprState  *checkconstr = resultRelInfo->ri_CheckConstraintExprs[i];

		/*
		 * NOTE: SQL specifies that a NULL result from a constraint expression
		 * is not to be treated as a failure.  Therefore, use ExecCheck not
		 * ExecQual.
		 */
		if (checkconstr && !ExecCheck(checkconstr, econtext))
			return check[i].ccname;
	}

	/* NULL result means no error */
	return NULL;
}

/*
 * ============================================================================
 * 【中文注释】ExecPartitionCheck —— 检查元组是否满足所在分区的分区约束
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   用 RelationGetPartitionQual 得到该分区"隐含的分区条件"（例如分区是
 *   range(c1 < 100)，约束就是 c1 < 100），编译并求值。满足返回 true；
 *   不满足且 emitError 为 true 时，调 ExecPartitionCheckEmitError 抛错
 *   （不返回）；不满足且 emitError 为 false 时静默返回 false（供路由探测）。
 *
 * 业务场景：
 *   - 显式向分区表 INSERT/COPY 时主路径校验；
 *   - 元组路由（tuple routing）探测目标分区的预检。
 *
 * 设计思想：
 *   - 同样惰性编译到 ri_PartitionCheckExpr（es_query_cxt 生命周期）；
 *   - NULL 结果视为通过——与 CHECK 约束一致，但注意 NULL 通过仅发生在
 *     约束可空时（分区约束中空值落入分区的情形另由路由逻辑处理）。
 * ============================================================================
 */
bool
ExecPartitionCheck(ResultRelInfo *resultRelInfo, TupleTableSlot *slot,
				   EState *estate, bool emitError)
{
	ExprContext *econtext;
	bool		success;

	/*
	 * If first time through, build expression state tree for the partition
	 * check expression.  (In the corner case where the partition check
	 * expression is empty, ie there's a default partition and nothing else,
	 * we'll be fooled into executing this code each time through.  But it's
	 * pretty darn cheap in that case, so we don't worry about it.)
	 */
	if (resultRelInfo->ri_PartitionCheckExpr == NULL)
	{
		/*
		 * Ensure that the qual tree and prepared expression are in the
		 * query-lifespan context.
		 */
		MemoryContext oldcxt = MemoryContextSwitchTo(estate->es_query_cxt);
		List	   *qual = RelationGetPartitionQual(resultRelInfo->ri_RelationDesc);

		resultRelInfo->ri_PartitionCheckExpr = ExecPrepareCheck(qual, estate);
		MemoryContextSwitchTo(oldcxt);
	}

	/*
	 * We will use the EState's per-tuple context for evaluating constraint
	 * expressions (creating it if it's not already there).
	 */
	econtext = GetPerTupleExprContext(estate);

	/* Arrange for econtext's scan tuple to be the tuple under test */
	econtext->ecxt_scantuple = slot;

	/*
	 * As in case of the cataloged constraints, we treat a NULL result as
	 * success here, not a failure.
	 */
	success = ExecCheck(resultRelInfo->ri_PartitionCheckExpr, econtext);

	/* if asked to emit error, don't actually return on failure */
	if (!success && emitError)
		ExecPartitionCheckEmitError(resultRelInfo, slot, estate);

	return success;
}

/*
 * ============================================================================
 * 【中文注释】ExecPartitionCheckEmitError —— 分区约束失败后的报错构造
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   分区约束检查失败时，构造形如
 *   "new row for relation ... violates partition constraint" 的报错，并附上
 *   失败行内容（val_desc，"Failing row contains (col1=..., ...)"）。
 *
 * 设计思想：
 *   - 行类型还原：若元组经过分区路由已被转换为"分区行类型"（列序可能与
 *     根表不同），先用 ChildToRoot 反向 AttrMap（build_attrmap_by_name_If_req）
 *     转回根表行类型，保证错误消息里的列/值与用户输入一致；
 *   - 因分区槽的描述符不可变，转换需要新建虚拟槽（MakeTupleTableSlot +
 *     执行 execute_attr_map_slot）；
 *   - 列集合取"插入列 ∪ 更新列"，用于权限受限时报错消息只体现用户有权
 *     看到的列（ExecBuildSlotValueDescription 的过滤依据）。
 * ============================================================================
 */
void
ExecPartitionCheckEmitError(ResultRelInfo *resultRelInfo,
							TupleTableSlot *slot,
							EState *estate)
{
	Oid			root_relid;
	TupleDesc	tupdesc;
	char	   *val_desc;
	Bitmapset  *modifiedCols;

	/*
	 * If the tuple has been routed, it's been converted to the partition's
	 * rowtype, which might differ from the root table's.  We must convert it
	 * back to the root table's rowtype so that val_desc in the error message
	 * matches the input tuple.
	 */
	if (resultRelInfo->ri_RootResultRelInfo)
	{
		ResultRelInfo *rootrel = resultRelInfo->ri_RootResultRelInfo;
		TupleDesc	old_tupdesc;
		AttrMap    *map;

		root_relid = RelationGetRelid(rootrel->ri_RelationDesc);
		tupdesc = RelationGetDescr(rootrel->ri_RelationDesc);

		old_tupdesc = RelationGetDescr(resultRelInfo->ri_RelationDesc);
		/* a reverse map */
		map = build_attrmap_by_name_if_req(old_tupdesc, tupdesc, false);

		/*
		 * Partition-specific slot's tupdesc can't be changed, so allocate a
		 * new one.
		 */
		if (map != NULL)
			slot = execute_attr_map_slot(map, slot,
										 MakeTupleTableSlot(tupdesc, &TTSOpsVirtual, 0));
		modifiedCols = bms_union(ExecGetInsertedCols(rootrel, estate),
								 ExecGetUpdatedCols(rootrel, estate));
	}
	else
	{
		root_relid = RelationGetRelid(resultRelInfo->ri_RelationDesc);
		tupdesc = RelationGetDescr(resultRelInfo->ri_RelationDesc);
		modifiedCols = bms_union(ExecGetInsertedCols(resultRelInfo, estate),
								 ExecGetUpdatedCols(resultRelInfo, estate));
	}

	val_desc = ExecBuildSlotValueDescription(root_relid,
											 slot,
											 tupdesc,
											 modifiedCols,
											 64);
	ereport(ERROR,
			(errcode(ERRCODE_CHECK_VIOLATION),
			 errmsg("new row for relation \"%s\" violates partition constraint",
					RelationGetRelationName(resultRelInfo->ri_RelationDesc)),
			 val_desc ? errdetail("Failing row contains %s.", val_desc) : 0,
			 errtable(resultRelInfo->ri_RelationDesc)));
}

/*
 * ============================================================================
 * 【中文注释】ExecConstraints —— 元组入表前的完整性约束总检查
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对最终目标关系（可能已由元组路由决定）做三类检查：
 *   1. NOT NULL：逐个非空列检查 NULL（虚拟生成列收集后单独处理）；
 *   2. 虚拟生成列的非空：先求值生成表达式再判空（ExecRelGenVirtualNotNull）；
 *   3. CHECK 约束（ExecRelCheck）。
 *   任一失败即抛错。注意：分区约束不在此检查（调用方另行 ExecPartitionCheck）。
 *
 * 业务语义：
 *   INSERT/UPDATE/COPY 等所有写路径、以及 UPDATE 改列后行触发的
 *   ExecConstraints 调用，是用户定义的完整性规则最后一道关卡。
 *
 * 设计思想：
 *   - slot 中的元组在分区路由后可能是"分区行类型"，报错前统一转换回根表
 *     行类型再构造错误描述，让用户看到的列名与输入一致；
 *   - NOT NULL 位在 attnotnull；虚拟生成列（attgenerated=VIRTUAL）的值本身
 *     不入库，必须动态求值后才能判空，故单独收集列表逐列求值。
 * ============================================================================
 */
void
ExecConstraints(ResultRelInfo *resultRelInfo,
				TupleTableSlot *slot, EState *estate)
{
	Relation	rel = resultRelInfo->ri_RelationDesc;
	TupleDesc	tupdesc = RelationGetDescr(rel);
	TupleConstr *constr = tupdesc->constr;
	Bitmapset  *modifiedCols;
	List	   *notnull_virtual_attrs = NIL;

	Assert(constr);				/* we should not be called otherwise */

	/*
	 * Verify not-null constraints.
	 *
	 * Not-null constraints on virtual generated columns are collected and
	 * checked separately below.
	 */
	if (constr->has_not_null)
	{
		for (AttrNumber attnum = 1; attnum <= tupdesc->natts; attnum++)
		{
			Form_pg_attribute att = TupleDescAttr(tupdesc, attnum - 1);

			if (att->attnotnull && att->attgenerated == ATTRIBUTE_GENERATED_VIRTUAL)
				notnull_virtual_attrs = lappend_int(notnull_virtual_attrs, attnum);
			else if (att->attnotnull && slot_attisnull(slot, attnum))
				ReportNotNullViolationError(resultRelInfo, slot, estate, attnum);
		}
	}

	/*
	 * Verify not-null constraints on virtual generated column, if any.
	 */
	if (notnull_virtual_attrs)
	{
		AttrNumber	attnum;

		attnum = ExecRelGenVirtualNotNull(resultRelInfo, slot, estate,
										  notnull_virtual_attrs);
		if (attnum != InvalidAttrNumber)
			ReportNotNullViolationError(resultRelInfo, slot, estate, attnum);
	}

	/*
	 * Verify check constraints.
	 */
	if (rel->rd_rel->relchecks > 0)
	{
		const char *failed;

		if ((failed = ExecRelCheck(resultRelInfo, slot, estate)) != NULL)
		{
			char	   *val_desc;
			Relation	orig_rel = rel;

			/*
			 * If the tuple has been routed, it's been converted to the
			 * partition's rowtype, which might differ from the root table's.
			 * We must convert it back to the root table's rowtype so that
			 * val_desc shown error message matches the input tuple.
			 */
			if (resultRelInfo->ri_RootResultRelInfo)
			{
				ResultRelInfo *rootrel = resultRelInfo->ri_RootResultRelInfo;
				TupleDesc	old_tupdesc = RelationGetDescr(rel);
				AttrMap    *map;

				tupdesc = RelationGetDescr(rootrel->ri_RelationDesc);
				/* a reverse map */
				map = build_attrmap_by_name_if_req(old_tupdesc,
												   tupdesc,
												   false);

				/*
				 * Partition-specific slot's tupdesc can't be changed, so
				 * allocate a new one.
				 */
				if (map != NULL)
					slot = execute_attr_map_slot(map, slot,
												 MakeTupleTableSlot(tupdesc, &TTSOpsVirtual, 0));
				modifiedCols = bms_union(ExecGetInsertedCols(rootrel, estate),
										 ExecGetUpdatedCols(rootrel, estate));
				rel = rootrel->ri_RelationDesc;
			}
			else
				modifiedCols = bms_union(ExecGetInsertedCols(resultRelInfo, estate),
										 ExecGetUpdatedCols(resultRelInfo, estate));
			val_desc = ExecBuildSlotValueDescription(RelationGetRelid(rel),
													 slot,
													 tupdesc,
													 modifiedCols,
													 64);
			ereport(ERROR,
					(errcode(ERRCODE_CHECK_VIOLATION),
					 errmsg("new row for relation \"%s\" violates check constraint \"%s\"",
							RelationGetRelationName(orig_rel), failed),
					 val_desc ? errdetail("Failing row contains %s.", val_desc) : 0,
					 errtableconstraint(orig_rel, failed)));
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecRelGenVirtualNotNull —— 虚拟生成列的非空约束检查
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对给定虚拟生成列集合（notnull_virtual_attrs，均为 attnotnull 的虚拟
 *   生成列），构造并缓存"生成表达式 IS NOT NULL"的表达式状态，逐列求值。
 *   全部通过返回 InvalidAttrNumber；违反返回第一个违规列的 attnum。
 *
 * 业务背景：
 *   虚拟生成列（GENERATED ALWAYS AS (...) STORED 的对立面：VIRTUAL）不落盘，
 *   其值由生成表达式即时计算。声明了 NOT NULL 的虚拟生成列必须在每次写入时
 *   重新求值判空，故不能走普通的"看槽值"路径。
 *
 * 设计思想：
 *   - 惰性构造：首次调用把每个列构造成 NullTest(IS_NOT_NULL, arg=生成表达式)
 *     编译成 ExprState 缓存于 ri_GenVirtualNotNullConstraintExprs；
 *   - 求值语义同 ExecRelCheck：NULL 通过 / 为假违规。
 * ============================================================================
 */
AttrNumber
ExecRelGenVirtualNotNull(ResultRelInfo *resultRelInfo, TupleTableSlot *slot,
						 EState *estate, List *notnull_virtual_attrs)
{
	Relation	rel = resultRelInfo->ri_RelationDesc;
	ExprContext *econtext;
	MemoryContext oldContext;

	/*
	 * We implement this by building a NullTest node for each virtual
	 * generated column, which we cache in resultRelInfo, and running those
	 * through ExecCheck().
	 */
	if (resultRelInfo->ri_GenVirtualNotNullConstraintExprs == NULL)
	{
		oldContext = MemoryContextSwitchTo(estate->es_query_cxt);
		resultRelInfo->ri_GenVirtualNotNullConstraintExprs =
			palloc0_array(ExprState *, list_length(notnull_virtual_attrs));

		foreach_int(attnum, notnull_virtual_attrs)
		{
			int			i = foreach_current_index(attnum);
			NullTest   *nnulltest;

			/* "generated_expression IS NOT NULL" check. */
			nnulltest = makeNode(NullTest);
			nnulltest->arg = (Expr *) build_generation_expression(rel, attnum);
			nnulltest->nulltesttype = IS_NOT_NULL;
			nnulltest->argisrow = false;
			nnulltest->location = -1;

			resultRelInfo->ri_GenVirtualNotNullConstraintExprs[i] =
				ExecPrepareExpr((Expr *) nnulltest, estate);
		}
		MemoryContextSwitchTo(oldContext);
	}

	/*
	 * We will use the EState's per-tuple context for evaluating virtual
	 * generated column not null constraint expressions (creating it if it's
	 * not already there).
	 */
	econtext = GetPerTupleExprContext(estate);

	/* Arrange for econtext's scan tuple to be the tuple under test */
	econtext->ecxt_scantuple = slot;

	/* And evaluate the check constraints for virtual generated column */
	foreach_int(attnum, notnull_virtual_attrs)
	{
		int			i = foreach_current_index(attnum);
		ExprState  *exprstate = resultRelInfo->ri_GenVirtualNotNullConstraintExprs[i];

		Assert(exprstate != NULL);
		if (!ExecCheck(exprstate, econtext))
			return attnum;
	}

	/* InvalidAttrNumber result means no error */
	return InvalidAttrNumber;
}

/*
 * ============================================================================
 * 【中文注释】ReportNotNullViolationError —— 报告已发现的 NOT NULL 违规
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   构造并抛出形如
 *   "null value in column \"c1\" of relation \"t\" violates not-null constraint"
 *   的错误，并附上失败行内容（权限受限时仅列有权查看的列）。
 *   注意：本函数只负责"报告"，违规判定由调用方（ExecConstraints）完成。
 * ============================================================================
 */
static void
ReportNotNullViolationError(ResultRelInfo *resultRelInfo, TupleTableSlot *slot,
							EState *estate, int attnum)
{
	Bitmapset  *modifiedCols;
	char	   *val_desc;
	Relation	rel = resultRelInfo->ri_RelationDesc;
	Relation	orig_rel = rel;
	TupleDesc	tupdesc = RelationGetDescr(rel);
	TupleDesc	orig_tupdesc = RelationGetDescr(rel);
	Form_pg_attribute att = TupleDescAttr(tupdesc, attnum - 1);

	Assert(attnum > 0);

	/*
	 * If the tuple has been routed, it's been converted to the partition's
	 * rowtype, which might differ from the root table's.  We must convert it
	 * back to the root table's rowtype so that val_desc shown error message
	 * matches the input tuple.
	 */
	if (resultRelInfo->ri_RootResultRelInfo)
	{
		ResultRelInfo *rootrel = resultRelInfo->ri_RootResultRelInfo;
		AttrMap    *map;

		tupdesc = RelationGetDescr(rootrel->ri_RelationDesc);
		/* a reverse map */
		map = build_attrmap_by_name_if_req(orig_tupdesc,
										   tupdesc,
										   false);

		/*
		 * Partition-specific slot's tupdesc can't be changed, so allocate a
		 * new one.
		 */
		if (map != NULL)
			slot = execute_attr_map_slot(map, slot,
										 MakeTupleTableSlot(tupdesc, &TTSOpsVirtual, 0));
		modifiedCols = bms_union(ExecGetInsertedCols(rootrel, estate),
								 ExecGetUpdatedCols(rootrel, estate));
		rel = rootrel->ri_RelationDesc;
	}
	else
		modifiedCols = bms_union(ExecGetInsertedCols(resultRelInfo, estate),
								 ExecGetUpdatedCols(resultRelInfo, estate));

	val_desc = ExecBuildSlotValueDescription(RelationGetRelid(rel),
											 slot,
											 tupdesc,
											 modifiedCols,
											 64);
	ereport(ERROR,
			errcode(ERRCODE_NOT_NULL_VIOLATION),
			errmsg("null value in column \"%s\" of relation \"%s\" violates not-null constraint",
				   NameStr(att->attname),
				   RelationGetRelationName(orig_rel)),
			val_desc ? errdetail("Failing row contains %s.", val_desc) : 0,
			errtablecol(orig_rel, attnum));
}

/*
 * ============================================================================
 * 【中文注释】ExecWithCheckOptions —— 检查元组是否满足 WITH CHECK OPTION
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对结果关系上的 WITH CHECK OPTION 列表（ri_WithCheckOptions）逐项求值，
 *   只处理 kind 匹配的那一类（视图 WCO_VIEW_CHECK 或 RLS 策略的各检查类）。
 *   任一不通过即抛出对应错误（视图违规 / RLS 策略违规）。
 *
 * 参数：
 *   kind          - 本次要检查的类别：WCO_VIEW_CHECK / WCO_RLS_INSERT_CHECK /
 *                   WCO_RLS_UPDATE_CHECK / WCO_RLS_MERGE_*_CHECK /
 *                   WCO_RLS_CONFLICT_CHECK。
 *   resultRelInfo - 结果关系（内含 wco 列表与已编译表达式对）；
 *   slot          - 待检查的新元组；estate - 执行状态。
 *
 * 业务背景：
 *   - 视图的 WITH CHECK OPTION：新行必须仍然"在视图内"（否则视图中将出现
 *     用户通过视图看不见的行）；
 *   - RLS 的 WITH CHECK 策略：新行必须通过该策略，否则直接禁止写入。
 *   两个来源的 WCO 都挂在同一列表上，因此需按 kind 过滤逐次调用
 *   （ExecInsert/ExecUpdate 分别对每个 kind 调用一次本函数）。
 *
 * 设计思想：
 *   - 求值用 ExecQual：NULL 或 FALSE 均视为违规（与 SELECT 过滤语义一致）；
 *   - RLS 违规不展示行内容（避免泄露无权查看的数据），视图违规在权限允许
 *     时展示失败行（沿用 ExecConstraints 的"转回根表行类型"技巧）；
 *   - 表达式与 wco 节点一一对应（ri_WithCheckOptionExprs 与
 *     ri_WithCheckOptions 并行列表），用 forboth 同步遍历。
 * ============================================================================
 */
void
ExecWithCheckOptions(WCOKind kind, ResultRelInfo *resultRelInfo,
					 TupleTableSlot *slot, EState *estate)
{
	Relation	rel = resultRelInfo->ri_RelationDesc;
	TupleDesc	tupdesc = RelationGetDescr(rel);
	ExprContext *econtext;
	ListCell   *l1,
			   *l2;

	/*
	 * We will use the EState's per-tuple context for evaluating constraint
	 * expressions (creating it if it's not already there).
	 */
	econtext = GetPerTupleExprContext(estate);

	/* Arrange for econtext's scan tuple to be the tuple under test */
	econtext->ecxt_scantuple = slot;

	/* Check each of the constraints */
	forboth(l1, resultRelInfo->ri_WithCheckOptions,
			l2, resultRelInfo->ri_WithCheckOptionExprs)
	{
		WithCheckOption *wco = (WithCheckOption *) lfirst(l1);
		ExprState  *wcoExpr = (ExprState *) lfirst(l2);

		/*
		 * Skip any WCOs which are not the kind we are looking for at this
		 * time.
		 */
		if (wco->kind != kind)
			continue;

		/*
		 * WITH CHECK OPTION checks are intended to ensure that the new tuple
		 * is visible (in the case of a view) or that it passes the
		 * 'with-check' policy (in the case of row security). If the qual
		 * evaluates to NULL or FALSE, then the new tuple won't be included in
		 * the view or doesn't pass the 'with-check' policy for the table.
		 */
		if (!ExecQual(wcoExpr, econtext))
		{
			char	   *val_desc;
			Bitmapset  *modifiedCols;

			switch (wco->kind)
			{
					/*
					 * For WITH CHECK OPTIONs coming from views, we might be
					 * able to provide the details on the row, depending on
					 * the permissions on the relation (that is, if the user
					 * could view it directly anyway).  For RLS violations, we
					 * don't include the data since we don't know if the user
					 * should be able to view the tuple as that depends on the
					 * USING policy.
					 */
				case WCO_VIEW_CHECK:
					/* See the comment in ExecConstraints(). */
					if (resultRelInfo->ri_RootResultRelInfo)
					{
						ResultRelInfo *rootrel = resultRelInfo->ri_RootResultRelInfo;
						TupleDesc	old_tupdesc = RelationGetDescr(rel);
						AttrMap    *map;

						tupdesc = RelationGetDescr(rootrel->ri_RelationDesc);
						/* a reverse map */
						map = build_attrmap_by_name_if_req(old_tupdesc,
														   tupdesc,
														   false);

						/*
						 * Partition-specific slot's tupdesc can't be changed,
						 * so allocate a new one.
						 */
						if (map != NULL)
							slot = execute_attr_map_slot(map, slot,
														 MakeTupleTableSlot(tupdesc, &TTSOpsVirtual, 0));

						modifiedCols = bms_union(ExecGetInsertedCols(rootrel, estate),
												 ExecGetUpdatedCols(rootrel, estate));
						rel = rootrel->ri_RelationDesc;
					}
					else
						modifiedCols = bms_union(ExecGetInsertedCols(resultRelInfo, estate),
												 ExecGetUpdatedCols(resultRelInfo, estate));
					val_desc = ExecBuildSlotValueDescription(RelationGetRelid(rel),
															 slot,
															 tupdesc,
															 modifiedCols,
															 64);

					ereport(ERROR,
							(errcode(ERRCODE_WITH_CHECK_OPTION_VIOLATION),
							 errmsg("new row violates check option for view \"%s\"",
									wco->relname),
							 val_desc ? errdetail("Failing row contains %s.",
												  val_desc) : 0));
					break;
				case WCO_RLS_INSERT_CHECK:
				case WCO_RLS_UPDATE_CHECK:
					if (wco->polname != NULL)
						ereport(ERROR,
								(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
								 errmsg("new row violates row-level security policy \"%s\" for table \"%s\"",
										wco->polname, wco->relname)));
					else
						ereport(ERROR,
								(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
								 errmsg("new row violates row-level security policy for table \"%s\"",
										wco->relname)));
					break;
				case WCO_RLS_MERGE_UPDATE_CHECK:
				case WCO_RLS_MERGE_DELETE_CHECK:
					if (wco->polname != NULL)
						ereport(ERROR,
								(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
								 errmsg("target row violates row-level security policy \"%s\" (USING expression) for table \"%s\"",
										wco->polname, wco->relname)));
					else
						ereport(ERROR,
								(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
								 errmsg("target row violates row-level security policy (USING expression) for table \"%s\"",
										wco->relname)));
					break;
				case WCO_RLS_CONFLICT_CHECK:
					if (wco->polname != NULL)
						ereport(ERROR,
								(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
								 errmsg("new row violates row-level security policy \"%s\" (USING expression) for table \"%s\"",
										wco->polname, wco->relname)));
					else
						ereport(ERROR,
								(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
								 errmsg("new row violates row-level security policy (USING expression) for table \"%s\"",
										wco->relname)));
					break;
				default:
					elog(ERROR, "unrecognized WCO kind: %u", wco->kind);
					break;
			}
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildSlotValueDescription —— 构造元组的可读描述串
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把槽中元组格式化为 "(col1=val1, col2=val2, ...)" 字符串，用于
 *   约束违规、唯一冲突等错误消息中展示失败行。
 *
 * 参数：
 *   reloid       - 关系 OID（用于权限检查与类型输出函数查找）；
 *   slot         - 待描述元组；tupdesc - 关系（根表）的元组描述符；
 *   modifiedCols - 用户显式写入的列位图（这些列即使无 SELECT 权限也展示，
 *                  因为用户自己提供了这些数据）；
 *   maxfieldlen  - 单字段最大展示字节数，超出则截断并追加 "..."。
 *
 * 设计思想（安全性优先）：
 *   1. RLS 启用时一律返回 NULL（不泄露任何行内容）；
 *   2. 无表级 SELECT 权限时降级为列级过滤：只展示"有 SELECT 权限的列 ∪
 *      用户显式写入的列"，并在结果前加列名清单 (c1, c3) = (v1, v3)；
 *      任一列都无权查看时返回 NULL；
 *   3. 虚拟生成列（不落盘）展示为 "virtual"；NULL 展示为 "null"；
 *   4. 字段值经类型的 output 函数转字符串；超长按多字节安全截断
 *      （pg_mbcliplen，避免切断多字节字符产生乱码）；
 *   5. 丢弃列（attisdropped）跳过。
 * ============================================================================
 */
char *
ExecBuildSlotValueDescription(Oid reloid,
							  TupleTableSlot *slot,
							  TupleDesc tupdesc,
							  Bitmapset *modifiedCols,
							  int maxfieldlen)
{
	StringInfoData buf;
	StringInfoData collist;
	bool		write_comma = false;
	bool		write_comma_collist = false;
	int			i;
	AclResult	aclresult;
	bool		table_perm = false;
	bool		any_perm = false;

	/*
	 * Check if RLS is enabled and should be active for the relation; if so,
	 * then don't return anything.  Otherwise, go through normal permission
	 * checks.
	 */
	if (check_enable_rls(reloid, InvalidOid, true) == RLS_ENABLED)
		return NULL;

	initStringInfo(&buf);

	appendStringInfoChar(&buf, '(');

	/*
	 * Check if the user has permissions to see the row.  Table-level SELECT
	 * allows access to all columns.  If the user does not have table-level
	 * SELECT then we check each column and include those the user has SELECT
	 * rights on.  Additionally, we always include columns the user provided
	 * data for.
	 */
	aclresult = pg_class_aclcheck(reloid, GetUserId(), ACL_SELECT);
	if (aclresult != ACLCHECK_OK)
	{
		/* Set up the buffer for the column list */
		initStringInfo(&collist);
		appendStringInfoChar(&collist, '(');
	}
	else
		table_perm = any_perm = true;

	/* Make sure the tuple is fully deconstructed */
	slot_getallattrs(slot);

	for (i = 0; i < tupdesc->natts; i++)
	{
		bool		column_perm = false;
		char	   *val;
		int			vallen;
		Form_pg_attribute att = TupleDescAttr(tupdesc, i);

		/* ignore dropped columns */
		if (att->attisdropped)
			continue;

		if (!table_perm)
		{
			/*
			 * No table-level SELECT, so need to make sure they either have
			 * SELECT rights on the column or that they have provided the data
			 * for the column.  If not, omit this column from the error
			 * message.
			 */
			aclresult = pg_attribute_aclcheck(reloid, att->attnum,
											  GetUserId(), ACL_SELECT);
			if (bms_is_member(att->attnum - FirstLowInvalidHeapAttributeNumber,
							  modifiedCols) || aclresult == ACLCHECK_OK)
			{
				column_perm = any_perm = true;

				if (write_comma_collist)
					appendStringInfoString(&collist, ", ");
				else
					write_comma_collist = true;

				appendStringInfoString(&collist, NameStr(att->attname));
			}
		}

		if (table_perm || column_perm)
		{
			if (att->attgenerated == ATTRIBUTE_GENERATED_VIRTUAL)
				val = "virtual";
			else if (slot->tts_isnull[i])
				val = "null";
			else
			{
				Oid			foutoid;
				bool		typisvarlena;

				getTypeOutputInfo(att->atttypid,
								  &foutoid, &typisvarlena);
				val = OidOutputFunctionCall(foutoid, slot->tts_values[i]);
			}

			if (write_comma)
				appendStringInfoString(&buf, ", ");
			else
				write_comma = true;

			/* truncate if needed */
			vallen = strlen(val);
			if (vallen <= maxfieldlen)
				appendBinaryStringInfo(&buf, val, vallen);
			else
			{
				vallen = pg_mbcliplen(val, vallen, maxfieldlen);
				appendBinaryStringInfo(&buf, val, vallen);
				appendStringInfoString(&buf, "...");
			}
		}
	}

	/* If we end up with zero columns being returned, then return NULL. */
	if (!any_perm)
		return NULL;

	appendStringInfoChar(&buf, ')');

	if (!table_perm)
	{
		appendStringInfoString(&collist, ") = ");
		appendBinaryStringInfo(&collist, buf.data, buf.len);

		return collist.data;
	}

	return buf.data;
}


/*
 * ============================================================================
 * 【中文注释】ExecUpdateLockMode —— 确定 UPDATE 需要的元组锁模式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   根据"被更新的列"与"键列"（构成任意唯一/主键索引的列集合）是否重叠，
 *   决定 UPDATE 目标元组应加的锁：
 *   - 重叠（键被修改）→ LockTupleExclusive（最严格，防并发更新键）；
 *   - 不重叠 → LockTupleNoKeyExclusive（较宽松，提升并发度）。
 *
 * 业务背景：
 *   PostgreSQL 区分"键更新"与"非键更新"：非键更新可与同时进行的其他非键
 *   更新并行（不需要互斥），键更新则必须串行，否则可能违反唯一性/破坏
 *   外键引用。加锁阶段就根据成本差异选择锁级，避免过度加锁。
 *
 * 设计思想：
 *   INDEX_ATTR_BITMAP_KEY 返回键属性位图；bms_overlap 判断两类列是否有
 *   交集。注意：这是"如果列集与键重叠则用强锁"的保守策略——实际执行时
 *   若最终没有真正改键值，锁仍偏强，换取实现简单与正确性。
 * ============================================================================
 */
LockTupleMode
ExecUpdateLockMode(EState *estate, ResultRelInfo *relinfo)
{
	Bitmapset  *keyCols;
	Bitmapset  *updatedCols;

	/*
	 * Compute lock mode to use.  If columns that are part of the key have not
	 * been modified, then we can use a weaker lock, allowing for better
	 * concurrency.
	 */
	updatedCols = ExecGetAllUpdatedCols(relinfo, estate);
	keyCols = RelationGetIndexAttrBitmap(relinfo->ri_RelationDesc,
										 INDEX_ATTR_BITMAP_KEY);

	if (bms_overlap(keyCols, updatedCols))
		return LockTupleExclusive;

	return LockTupleNoKeyExclusive;
}

/*
 * ============================================================================
 * 【中文注释】ExecFindRowMark —— 按范围表索引查找 ExecRowMark
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从 estate->es_rowmarks[rti-1] 取出对应的行标记结构。
 *   找不到时：missing_ok=false 直接 ERROR（行标记缺失属内核级 bug）；
 *   missing_ok=true 返回 NULL（用于选择性行标记查询）。
 *
 * 业务背景：
 *   SELECT FOR UPDATE/SHARE 以及 EPQ 机制需要按 RTE 编号快速定位
 *   ExecRowMark（含加锁强度、等待策略、当前 ctid 等信息）。
 * ============================================================================
 */
ExecRowMark *
ExecFindRowMark(EState *estate, Index rti, bool missing_ok)
{
	if (rti > 0 && rti <= estate->es_range_table_size &&
		estate->es_rowmarks != NULL)
	{
		ExecRowMark *erm = estate->es_rowmarks[rti - 1];

		if (erm)
			return erm;
	}
	if (!missing_ok)
		elog(ERROR, "failed to find ExecRowMark for rangetable index %u", rti);
	return NULL;
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildAuxRowMark —— 构建行标记的辅助结构
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在计划节点初始化时，根据 ExecRowMark 与输入计划的 targetlist，找出该
 *   行标记对应的 resjunk（内部）列号，构建 ExecAuxRowMark 挂在节点上。
 *
 * 参数：
 *   erm        - 基础行标记（由 InitPlan 构建）；
 *   targetlist - 输入计划节点的（而非 planstate 的）目标列表。
 *
 * 设计思想（junk 列的命名约定，由计划器保证）：
 *   - 非 COPY 型行标记：ctidN（元组物理位置，EPQ 重取/加锁用）；
 *   - COPY 型（子查询 RTE）：wholerowN（整行值快照）；
 *   - 分区子表（rti != prti）：tableoidN（标记该行来自哪个子表，用于
 *     EPQ 重检查时判断"当前子表是否就是产生该行的表"）。
 *   通过 ExecFindJunkAttributeInTlist 按名反查列号；缺失即 ERROR——说明
 *   计划器与执行器的约定被破坏。
 * ============================================================================
 */
ExecAuxRowMark *
ExecBuildAuxRowMark(ExecRowMark *erm, List *targetlist)
{
	ExecAuxRowMark *aerm = palloc0_object(ExecAuxRowMark);
	char		resname[32];

	aerm->rowmark = erm;

	/* Look up the resjunk columns associated with this rowmark */
	if (erm->markType != ROW_MARK_COPY)
	{
		/* need ctid for all methods other than COPY */
		snprintf(resname, sizeof(resname), "ctid%u", erm->rowmarkId);
		aerm->ctidAttNo = ExecFindJunkAttributeInTlist(targetlist,
													   resname);
		if (!AttributeNumberIsValid(aerm->ctidAttNo))
			elog(ERROR, "could not find junk %s column", resname);
	}
	else
	{
		/* need wholerow if COPY */
		snprintf(resname, sizeof(resname), "wholerow%u", erm->rowmarkId);
		aerm->wholeAttNo = ExecFindJunkAttributeInTlist(targetlist,
														resname);
		if (!AttributeNumberIsValid(aerm->wholeAttNo))
			elog(ERROR, "could not find junk %s column", resname);
	}

	/* if child rel, need tableoid */
	if (erm->rti != erm->prti)
	{
		snprintf(resname, sizeof(resname), "tableoid%u", erm->rowmarkId);
		aerm->toidAttNo = ExecFindJunkAttributeInTlist(targetlist,
													   resname);
		if (!AttributeNumberIsValid(aerm->toidAttNo))
			elog(ERROR, "could not find junk %s column", resname);
	}

	return aerm;
}


/*
 * ============================================================================
 * 【中文注释】EPQ 机制总览（EvalPlanQual / 计划资格重评估）
 * ----------------------------------------------------------------------------
 * 业务背景：
 *   READ COMMITTED 隔离级别下，UPDATE/DELETE/SELECT FOR UPDATE 用"先锁定
 *   再操作"的方式处理并发：加锁时发现目标元组已被其他并发事务修改（或正
 *   在修改中），必须等待对方提交后，取回最新版本并重新评估 WHERE 条件——
 *   若最新版本仍满足条件，则对最新版本继续操作；否则跳过该行。
 *   这套"重新评估"机制就是 EPQ，早期称为 "EvalPlanQual"（SQL 标准概念）。
 *
 * 工作机制（流程）：
 *
 *   上层（nodeLockRows / nodeModifyTable）发现行被并发修改
 *      │
 *      ▼
 *   EvalPlanQual(epqstate, rel, rti, inputslot)
 *      ├─> EvalPlanQualBegin：启动/重置子查询环境（必要时 EvalPlanQualStart）
 *      ├─> 把"测试元组"放入 EvalPlanQualSlot（复用槽，避免拷贝）
 *      ├─> 标记该关系"有可用元组"（relsubs_done[rti]=false）
 *      ├─> EvalPlanQualNext：在独立的"重检查 EState + 重检查计划树"上
 *      │      重新执行整条查询（重新扫描所有关系、重新求值 WHERE）
 *      ├─> 返回最新版本元组（若满足条件）或 NULL（不满足/已被删除）
 *      └─> 清空测试槽，标记"无可用元组"（relsubs_blocked[rti]=true）
 *
 * 设计思想（关键点）：
 *   1. 重检查使用独立 EState（recheckestate）与独立计划树
 *      （recheckplanstate，即 ModifyTable/LockRows 的输入子树），但共享父
 *      事务的快照、范围表与行标记——保证"看到的数据版本"与并发语义一致；
 *   2. relsubs_done/relsubs_blocked 双标志按 rti 维护：
 *      - blocked：该关系是结果关系（禁止为其取测试元组，防止循环重评估）；
 *      - done：该关系本轮是否已有可用元组（可被重检查计划消费）；
 *      行标记（非加锁）关系的元组由 EvalPlanQualFetchRowMark 按需取回；
 *   3. 惰性启动：EvalPlanQualSlot 可在不 Begin 的情况下使用（把"可能被
 *      修改"的元组先暂存在 EPQ 槽里），Begin 才真正初始化子计划树——
 *      绝大多数行从未被并发修改，因此避免为每行重建执行环境；
 *   4. 理论上重检查最多返回一行（同一时刻仅一个版本会胜出）。
 *
 * 详细机制见 src/backend/executor/README 的 "EvalPlanQual" 小节。
 * ============================================================================
 */

/*
 * ============================================================================
 * 【中文注释】EvalPlanQual —— READ COMMITTED 下对"最新版本元组"的资格重检
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   给定"疑似被并发修改"的测试元组 inputslot，重新执行一遍查询，判断其
 *   最新已提交版本是否仍然满足查询条件。
 *
 * 参数：
 *   epqstate  - EPQ 状态（由 EvalPlanQualInit 初始化）；
 *   relation  - 元组所在表；
 *   rti       - 该表在范围表中的编号；
 *   inputslot - 待测试元组（优先使用 EvalPlanQualSlot 返回的槽，可省拷贝）。
 *
 * 返回值：
 *   满足条件的最新元组槽（返回前已被物化，不依赖子查询的临时状态）；
 *   不满足/已删除则返回 NULL。
 *
 * 设计思想：
 *   - 槽复用：调用方通常已把元组放进 EvalPlanQualSlot，传入同槽可避免
 *     一次 ExecCopySlot；
 *   - 物化保证：返回的槽内数据被 Materialize（pass-by-ref 字段拷贝到独立
 *     内存），因为子查询的求值上下文随后即被复用/丢弃；
 *   - 收尾标记：测试完成后把 relsubs_blocked[rti] 置回 true，防止该关系
 *     在下一次重检查时被当作"有可用元组"——EPQ 状态会被复用于测试其他
 *     关系的元组。
 * ============================================================================
 */
TupleTableSlot *
EvalPlanQual(EPQState *epqstate, Relation relation,
			 Index rti, TupleTableSlot *inputslot)
{
	TupleTableSlot *slot;
	TupleTableSlot *testslot;

	Assert(rti > 0);

	/*
	 * Need to run a recheck subquery.  Initialize or reinitialize EPQ state.
	 */
	EvalPlanQualBegin(epqstate);

	/*
	 * Callers will often use the EvalPlanQualSlot to store the tuple to avoid
	 * an unnecessary copy.
	 */
	testslot = EvalPlanQualSlot(epqstate, relation, rti);
	if (testslot != inputslot)
		ExecCopySlot(testslot, inputslot);

	/*
	 * Mark that an EPQ tuple is available for this relation.  (If there is
	 * more than one result relation, the others remain marked as having no
	 * tuple available.)
	 */
	epqstate->relsubs_done[rti - 1] = false;
	epqstate->relsubs_blocked[rti - 1] = false;

	/*
	 * Run the EPQ query.  We assume it will return at most one tuple.
	 */
	slot = EvalPlanQualNext(epqstate);

	/*
	 * If we got a tuple, force the slot to materialize the tuple so that it
	 * is not dependent on any local state in the EPQ query (in particular,
	 * it's highly likely that the slot contains references to any pass-by-ref
	 * datums that may be present in copyTuple).  As with the next step, this
	 * is to guard against early re-use of the EPQ query.
	 */
	if (!TupIsNull(slot))
		ExecMaterializeSlot(slot);

	/*
	 * Clear out the test tuple, and mark that no tuple is available here.
	 * This is needed in case the EPQ state is re-used to test a tuple for a
	 * different target relation.
	 */
	ExecClearTuple(testslot);
	epqstate->relsubs_blocked[rti - 1] = true;

	return slot;
}

/*
 * ============================================================================
 * 【中文注释】EvalPlanQualInit —— 初始化 EPQ 状态（节点初始化阶段调用）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在可能触发 EPQ 的节点（ModifyTable/LockRows）初始化时注册 EPQ 状态：
 *   记录父 EState、绑定重检查子计划与辅助行标记、记录"结果关系集合"
 *   （resultRelations，这些关系的元组在重检查中不取，防止无限循环）。
 *
 * 参数：
 *   epqstate       - 待初始化状态（通常嵌在节点状态结构里）；
 *   parentestate   - 外层查询的 EState；
 *   subplan        - 重检查用的子计划（ModifyTable 的输入子树）；
 *   auxrowmarks    - 辅助行标记列表（可随后用 EvalPlanQualSetPlan 再设）；
 *   epqParam       - EPQ 参数编号：重检查计划通过该参数向父查询传递"已消费
 *                    测试元组"的信号（chgParam 机制触发重扫描）；
 *   resultRelations- 结果关系 RTI 列表（EPQ 时这些关系不取元组）。
 *
 * 设计思想：
 *   - 在此即分配 relsubs_slot 数组（每 rti 一个槽）：EvalPlanQualSlot 可在
 *     未 Begin 前安全使用——把"可能被并发修改"的元组先放进去，绝大多数
 *     行用不上 EPQ，省掉 Begin 的初始化开销；
 *   - 其余动态资源（子计划、行标记、done/blocked 数组）留到 Begin/Start。
 * ============================================================================
 */
void
EvalPlanQualInit(EPQState *epqstate, EState *parentestate,
				 Plan *subplan, List *auxrowmarks,
				 int epqParam, List *resultRelations)
{
	Index		rtsize = parentestate->es_range_table_size;

	/* initialize data not changing over EPQState's lifetime */
	epqstate->parentestate = parentestate;
	epqstate->epqParam = epqParam;
	epqstate->resultRelations = resultRelations;

	/*
	 * Allocate space to reference a slot for each potential rti - do so now
	 * rather than in EvalPlanQualBegin(), as done for other dynamically
	 * allocated resources, so EvalPlanQualSlot() can be used to hold tuples
	 * that *may* need EPQ later, without forcing the overhead of
	 * EvalPlanQualBegin().
	 */
	epqstate->tuple_table = NIL;
	epqstate->relsubs_slot = palloc0_array(TupleTableSlot *, rtsize);

	/* ... and remember data that EvalPlanQualBegin will need */
	epqstate->plan = subplan;
	epqstate->arowMarks = auxrowmarks;

	/* ... and mark the EPQ state inactive */
	epqstate->origslot = NULL;
	epqstate->recheckestate = NULL;
	epqstate->recheckplanstate = NULL;
	epqstate->relsubs_rowmark = NULL;
	epqstate->relsubs_done = NULL;
	epqstate->relsubs_blocked = NULL;
}

/*
 * ============================================================================
 * 【中文注释】EvalPlanQualSetPlan —— 设置/更换 EPQ 重检查子计划
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   若当前已有活动的重检查查询，先 EvalPlanQualEnd 关掉，再替换子计划指针
 *   与辅助行标记。历史上用于支持 ModifyTable 的多子计划场景，现仅作为
 *   便捷设置接口保留。
 * ============================================================================
 */
void
EvalPlanQualSetPlan(EPQState *epqstate, Plan *subplan, List *auxrowmarks)
{
	/* If we have a live EPQ query, shut it down */
	EvalPlanQualEnd(epqstate);
	/* And set/change the plan pointer */
	epqstate->plan = subplan;
	/* The rowmarks depend on the plan, too */
	epqstate->arowMarks = auxrowmarks;
}

/*
 * ============================================================================
 * 【中文注释】EvalPlanQualSlot —— 获取（按需创建）某 RTI 的 EPQ 测试元组槽
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回 epqstate->relsubs_slot[rti-1]，首次使用时惰性创建并挂入
 *   epqstate->tuple_table（一个私有元组表，随 EPQ 状态生命周期管理）。
 *
 * 设计思想：
 *   只需要 EvalPlanQualInit 调用过即可使用本函数（无需 Begin）——调用方
 *   可以先"预订"槽位暂存元组，等真正需要重检查时才触发 Begin 初始化，
 *   把热路径开销压到最低。槽的元组描述符与 relation 的行类型一致
 *   （table_slot_create）。
 * ============================================================================
 */
TupleTableSlot *
EvalPlanQualSlot(EPQState *epqstate,
				 Relation relation, Index rti)
{
	TupleTableSlot **slot;

	Assert(relation);
	Assert(rti > 0 && rti <= epqstate->parentestate->es_range_table_size);
	slot = &epqstate->relsubs_slot[rti - 1];

	if (*slot == NULL)
	{
		MemoryContext oldcontext;

		oldcontext = MemoryContextSwitchTo(epqstate->parentestate->es_query_cxt);
		*slot = table_slot_create(relation, &epqstate->tuple_table);
		MemoryContextSwitchTo(oldcontext);
	}

	return *slot;
}

/*
 * ============================================================================
 * 【中文注释】EvalPlanQualFetchRowMark —— 为 EPQ 重检查取回非锁定关系的行
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对"非加锁型"行标记关系（ROW_MARK_REFERENCE 或 ROW_MARK_COPY），在
 *   EPQ 重检查期间按当前结果行中记录的 ctid/整行值，重新取回该关系的最新
 *   行版本放入 slot，供重检查计划作为"替换元组"消费。
 *
 * 参数：
 *   epqstate - EPQ 状态（origslot 必须已装载当前结果行）；
 *   rti      - 待取行所属关系的范围表编号；
 *   slot     - 存放取回元组的槽（重检查子查询会从这个槽取数据）。
 *
 * 返回值：
 *   true  - 找到替换元组；false - 该行无效（如外连接内侧无行、子表不匹配）。
 *
 * 设计思想：
 *   1. 加锁型行标记（EXCLUSIVE/SHARE 等）不允许在此路径取行——锁语义由
 *      LockRows 节点另行处理，这里直接 ERROR 防御；
 *   2. 分区子表判定：若 rti != prti（父/子行标记），先取 tableoidN junk 列
 *      判断"产生该行的子表"是否就是当前标记的子表；不匹配（NULL，外连接
 *      内侧；或 OID 不同，该子表本轮未产生行）则返回 false；
 *   3. REFERENCE 型：用 ctid 重新抓取——外部表走 FDW 的 RefetchForeignRow
 *      （updated 标志仅记录、不强制要求，FDW 可能无法精确跟踪）；普通表用
 *      table_tuple_fetch_row_version 以 SnapshotAny 抓取（并发安全：锁已由
 *      调用方持有，抓不到即 ERROR——说明并发语义被破坏）；
 *   4. COPY 型（子查询 RTE）：直接用缓存的整行值（wholerowN）快照放入槽，
 *      无需访问物理表。
 * ============================================================================
 */
bool
EvalPlanQualFetchRowMark(EPQState *epqstate, Index rti, TupleTableSlot *slot)
{
	ExecAuxRowMark *earm = epqstate->relsubs_rowmark[rti - 1];
	ExecRowMark *erm;
	Datum		datum;
	bool		isNull;

	Assert(earm != NULL);
	Assert(epqstate->origslot != NULL);

	erm = earm->rowmark;

	if (RowMarkRequiresRowShareLock(erm->markType))
		elog(ERROR, "EvalPlanQual doesn't support locking rowmarks");

	/* if child rel, must check whether it produced this row */
	if (erm->rti != erm->prti)
	{
		Oid			tableoid;

		datum = ExecGetJunkAttribute(epqstate->origslot,
									 earm->toidAttNo,
									 &isNull);
		/* non-locked rels could be on the inside of outer joins */
		if (isNull)
			return false;

		tableoid = DatumGetObjectId(datum);

		Assert(OidIsValid(erm->relid));
		if (tableoid != erm->relid)
		{
			/* this child is inactive right now */
			return false;
		}
	}

	if (erm->markType == ROW_MARK_REFERENCE)
	{
		Assert(erm->relation != NULL);

		/* fetch the tuple's ctid */
		datum = ExecGetJunkAttribute(epqstate->origslot,
									 earm->ctidAttNo,
									 &isNull);
		/* non-locked rels could be on the inside of outer joins */
		if (isNull)
			return false;

		/* fetch requests on foreign tables must be passed to their FDW */
		if (erm->relation->rd_rel->relkind == RELKIND_FOREIGN_TABLE)
		{
			FdwRoutine *fdwroutine;
			bool		updated = false;

			fdwroutine = GetFdwRoutineForRelation(erm->relation, false);
			/* this should have been checked already, but let's be safe */
			if (fdwroutine->RefetchForeignRow == NULL)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("cannot lock rows in foreign table \"%s\"",
								RelationGetRelationName(erm->relation))));

			fdwroutine->RefetchForeignRow(epqstate->recheckestate,
										  erm,
										  datum,
										  slot,
										  &updated);
			if (TupIsNull(slot))
				elog(ERROR, "failed to fetch tuple for EvalPlanQual recheck");

			/*
			 * Ideally we'd insist on updated == false here, but that assumes
			 * that FDWs can track that exactly, which they might not be able
			 * to.  So just ignore the flag.
			 */
			return true;
		}
		else
		{
			/* ordinary table, fetch the tuple */
			if (!table_tuple_fetch_row_version(erm->relation,
											   (ItemPointer) DatumGetPointer(datum),
											   SnapshotAny, slot))
				elog(ERROR, "failed to fetch tuple for EvalPlanQual recheck");
			return true;
		}
	}
	else
	{
		Assert(erm->markType == ROW_MARK_COPY);

		/* fetch the whole-row Var for the relation */
		datum = ExecGetJunkAttribute(epqstate->origslot,
									 earm->wholeAttNo,
									 &isNull);
		/* non-locked rels could be on the inside of outer joins */
		if (isNull)
			return false;

		ExecStoreHeapTupleDatum(datum, slot);
		return true;
	}
}

/*
 * ============================================================================
 * 【中文注释】EvalPlanQualNext —— 驱动重检查计划树取下一行
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在重检查 EState（recheckestate）的查询上下文中调用 ExecProcNode 驱动
 *   重检查计划树，返回其产出的元组（EPQ 场景下至多一行）。
 *
 * 设计思想：
 *   显式切换内存上下文的原因：子查询执行可能造成上下文栈累积（例如中途
 *   ERROR 前的分配），切换回调用方上下文可让上层"按自己节奏"决定何时释放；
 *   槽中数据由上层 EvalPlanQual 负责物化，与本函数无关。
 * ============================================================================
 */
TupleTableSlot *
EvalPlanQualNext(EPQState *epqstate)
{
	MemoryContext oldcontext;
	TupleTableSlot *slot;

	oldcontext = MemoryContextSwitchTo(epqstate->recheckestate->es_query_cxt);
	slot = ExecProcNode(epqstate->recheckplanstate);
	MemoryContextSwitchTo(oldcontext);

	return slot;
}

/*
 * ============================================================================
 * 【中文注释】EvalPlanQualBegin —— 启动/重置一轮 EPQ 重检查
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   首次调用时执行 EvalPlanQualStart（创建子 EState + 初始化重检查计划树），
 *   后续调用仅做"复位"：
 *   1. relsubs_done[] 恢复为 relsubs_blocked[] 的拷贝——上一轮已消费的
 *      测试元组作废，且被封锁的关系继续保持封锁；
 *   2. 从父 EState 重新拷贝内部参数值（含强制求值 InitPlan 输出参数，防止
 *      因父计划树重扫而失效的参数值）；
 *   3. 在重检查计划根上设置 chgParam 位（epqParam），触发各扫描节点
 *      重扫描（Rescan），以最新数据重新求值。
 *
 * 设计思想：
 *   - "每次重检查都用全新的参数/扫描状态"：READ COMMITTED 下并发提交随时
 *     可能发生，必须确保重检查看到的是最新已提交版本；
 *   - epqParam 是连接"测试元组是否被消费"的纽带：EPQ 计划中的 EPQ 节点在
 *     消费掉测试元组后清除该参数位，使父节点（ModifyTable）正确感知
 *     "本轮重检查已取过行"。
 * ============================================================================
 */
void
EvalPlanQualBegin(EPQState *epqstate)
{
	EState	   *parentestate = epqstate->parentestate;
	EState	   *recheckestate = epqstate->recheckestate;

	if (recheckestate == NULL)
	{
		/* First time through, so create a child EState */
		EvalPlanQualStart(epqstate, epqstate->plan);
	}
	else
	{
		/*
		 * We already have a suitable child EPQ tree, so just reset it.
		 */
		Index		rtsize = parentestate->es_range_table_size;
		PlanState  *rcplanstate = epqstate->recheckplanstate;

		/*
		 * Reset the relsubs_done[] flags to equal relsubs_blocked[], so that
		 * the EPQ run will never attempt to fetch tuples from blocked target
		 * relations.
		 */
		memcpy(epqstate->relsubs_done, epqstate->relsubs_blocked,
			   rtsize * sizeof(bool));

		/* Recopy current values of parent parameters */
		if (parentestate->es_plannedstmt->paramExecTypes != NIL)
		{
			int			i;

			/*
			 * Force evaluation of any InitPlan outputs that could be needed
			 * by the subplan, just in case they got reset since
			 * EvalPlanQualStart (see comments therein).
			 */
			ExecSetParamPlanMulti(rcplanstate->plan->extParam,
								  GetPerTupleExprContext(parentestate));

			i = list_length(parentestate->es_plannedstmt->paramExecTypes);

			while (--i >= 0)
			{
				/* copy value if any, but not execPlan link */
				recheckestate->es_param_exec_vals[i].value =
					parentestate->es_param_exec_vals[i].value;
				recheckestate->es_param_exec_vals[i].isnull =
					parentestate->es_param_exec_vals[i].isnull;
			}
		}

		/*
		 * Mark child plan tree as needing rescan at all scan nodes.  The
		 * first ExecProcNode will take care of actually doing the rescan.
		 */
		rcplanstate->chgParam = bms_add_member(rcplanstate->chgParam,
											   epqstate->epqParam);
	}
}

/*
 * ============================================================================
 * 【中文注释】EvalPlanQualStart —— 建立 EPQ 重检查执行环境（精简版 ExecutorStart）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   创建独立的重检查 EState 并初始化重检查计划树。与 ExecutorStart 不同，
 *   大量状态直接从父 EState 共享/拷贝，而非重新创建。
 *
 * 状态共享/拷贝策略（设计思想）：
 *   [共享——值语义不变的部分]
 *     es_snapshot / es_crosscheck_snapshot：与父查询同一快照，保证重检查
 *     与首轮执行看到的数据版本一致；
 *     es_range_table / es_relations / es_rowmarks / es_rteperminfos：
 *     范围表、已打开关系、行标记完全复用（重检查不会新增关系）；
 *     es_output_cid / es_queryEnv / es_top_eflags / es_instrument；
 *     es_unpruned_relids、分区裁剪信息（es_part_prune_infos/states/results）
 *     与 es_partition_directory：必须与父计划完全一致，才能初始化出相同的
 *     Append/MergeAppend 子计划集合；
 *     es_param_list_info：外部参数列表共享。
 *   [独立——每轮重检查需要自己的状态]
 *     es_param_exec_vals：内部参数工作区；先强制求值父计划中（重检查计划
 *     会引用到的）InitPlan 输出参数（ExecSetParamPlanMulti），再把全部值
 *     拷贝过来（不拷贝 execPlan 执行链）；
 *     es_result_relations / es_trig_target_relations / es_auxmodifytables：
 *     全部从零构建（重检查子计划自己的 ResultRelInfo 由 ExecInitModifyTable
 *     初始化），绝不能从父拷贝；
 *     es_epq_active：标记"本 EState 正被 EPQ 使用"（供 ExecInitLockRows /
 *     ExecInitModifyTable 识别并调整初始化行为）。
 *
 * 其他要点：
 *   - 子计划（subplans）也全部在此初始化（数量少、防遗漏）；
 *   - relsubs_rowmark[] 按 rti 建索引，供 EvalPlanQualFetchRowMark 快速访问；
 *   - relsubs_blocked[] 中结果关系（resultRelations）位置初始化为 true，
 *     done 与 blocked 初始一致——封锁的永远不取。
 * ============================================================================
 */
static void
EvalPlanQualStart(EPQState *epqstate, Plan *planTree)
{
	EState	   *parentestate = epqstate->parentestate;
	Index		rtsize = parentestate->es_range_table_size;
	EState	   *rcestate;
	MemoryContext oldcontext;
	ListCell   *l;

	epqstate->recheckestate = rcestate = CreateExecutorState();

	oldcontext = MemoryContextSwitchTo(rcestate->es_query_cxt);

	/* signal that this is an EState for executing EPQ */
	rcestate->es_epq_active = epqstate;

	/*
	 * Child EPQ EStates share the parent's copy of unchanging state such as
	 * the snapshot, rangetable, and external Param info.  They need their own
	 * copies of local state, including a tuple table, es_param_exec_vals,
	 * result-rel info, etc.
	 */
	rcestate->es_direction = ForwardScanDirection;
	rcestate->es_snapshot = parentestate->es_snapshot;
	rcestate->es_crosscheck_snapshot = parentestate->es_crosscheck_snapshot;
	rcestate->es_range_table = parentestate->es_range_table;
	rcestate->es_range_table_size = parentestate->es_range_table_size;
	rcestate->es_relations = parentestate->es_relations;
	rcestate->es_rowmarks = parentestate->es_rowmarks;
	rcestate->es_rteperminfos = parentestate->es_rteperminfos;
	rcestate->es_plannedstmt = parentestate->es_plannedstmt;
	rcestate->es_junkFilter = parentestate->es_junkFilter;
	rcestate->es_output_cid = parentestate->es_output_cid;
	rcestate->es_queryEnv = parentestate->es_queryEnv;

	/*
	 * ResultRelInfos needed by subplans are initialized from scratch when the
	 * subplans themselves are initialized.
	 */
	rcestate->es_result_relations = NULL;
	/* es_trig_target_relations must NOT be copied */
	rcestate->es_top_eflags = parentestate->es_top_eflags;
	rcestate->es_instrument = parentestate->es_instrument;
	/* es_auxmodifytables must NOT be copied */

	/*
	 * The external param list is simply shared from parent.  The internal
	 * param workspace has to be local state, but we copy the initial values
	 * from the parent, so as to have access to any param values that were
	 * already set from other parts of the parent's plan tree.
	 */
	rcestate->es_param_list_info = parentestate->es_param_list_info;
	if (parentestate->es_plannedstmt->paramExecTypes != NIL)
	{
		int			i;

		/*
		 * Force evaluation of any InitPlan outputs that could be needed by
		 * the subplan.  (With more complexity, maybe we could postpone this
		 * till the subplan actually demands them, but it doesn't seem worth
		 * the trouble; this is a corner case already, since usually the
		 * InitPlans would have been evaluated before reaching EvalPlanQual.)
		 *
		 * This will not touch output params of InitPlans that occur somewhere
		 * within the subplan tree, only those that are attached to the
		 * ModifyTable node or above it and are referenced within the subplan.
		 * That's OK though, because the planner would only attach such
		 * InitPlans to a lower-level SubqueryScan node, and EPQ execution
		 * will not descend into a SubqueryScan.
		 *
		 * The EState's per-output-tuple econtext is sufficiently short-lived
		 * for this, since it should get reset before there is any chance of
		 * doing EvalPlanQual again.
		 */
		ExecSetParamPlanMulti(planTree->extParam,
							  GetPerTupleExprContext(parentestate));

		/* now make the internal param workspace ... */
		i = list_length(parentestate->es_plannedstmt->paramExecTypes);
		rcestate->es_param_exec_vals = palloc0_array(ParamExecData, i);
		/* ... and copy down all values, whether really needed or not */
		while (--i >= 0)
		{
			/* copy value if any, but not execPlan link */
			rcestate->es_param_exec_vals[i].value =
				parentestate->es_param_exec_vals[i].value;
			rcestate->es_param_exec_vals[i].isnull =
				parentestate->es_param_exec_vals[i].isnull;
		}
	}

	/*
	 * Copy es_unpruned_relids so that pruned relations are ignored by
	 * ExecInitLockRows() and ExecInitModifyTable() when initializing the plan
	 * trees below.
	 */
	rcestate->es_unpruned_relids = parentestate->es_unpruned_relids;

	/*
	 * Also make the PartitionPruneInfo and the results of pruning available.
	 * These need to match exactly so that we initialize all the same Append
	 * and MergeAppend subplans as the parent did.
	 */
	rcestate->es_part_prune_infos = parentestate->es_part_prune_infos;
	rcestate->es_part_prune_states = parentestate->es_part_prune_states;
	rcestate->es_part_prune_results = parentestate->es_part_prune_results;

	/* We'll also borrow the es_partition_directory from the parent state */
	rcestate->es_partition_directory = parentestate->es_partition_directory;

	/*
	 * Initialize private state information for each SubPlan.  We must do this
	 * before running ExecInitNode on the main query tree, since
	 * ExecInitSubPlan expects to be able to find these entries. Some of the
	 * SubPlans might not be used in the part of the plan tree we intend to
	 * run, but since it's not easy to tell which, we just initialize them
	 * all.
	 */
	Assert(rcestate->es_subplanstates == NIL);
	foreach(l, parentestate->es_plannedstmt->subplans)
	{
		Plan	   *subplan = (Plan *) lfirst(l);
		PlanState  *subplanstate;

		subplanstate = ExecInitNode(subplan, rcestate, 0);
		rcestate->es_subplanstates = lappend(rcestate->es_subplanstates,
											 subplanstate);
	}

	/*
	 * Build an RTI indexed array of rowmarks, so that
	 * EvalPlanQualFetchRowMark() can efficiently access the to be fetched
	 * rowmark.
	 */
	epqstate->relsubs_rowmark = palloc0_array(ExecAuxRowMark *, rtsize);
	foreach(l, epqstate->arowMarks)
	{
		ExecAuxRowMark *earm = (ExecAuxRowMark *) lfirst(l);

		epqstate->relsubs_rowmark[earm->rowmark->rti - 1] = earm;
	}

	/*
	 * Initialize per-relation EPQ tuple states.  Result relations, if any,
	 * get marked as blocked; others as not-fetched.
	 */
	epqstate->relsubs_done = palloc_array(bool, rtsize);
	epqstate->relsubs_blocked = palloc0_array(bool, rtsize);

	foreach(l, epqstate->resultRelations)
	{
		int			rtindex = lfirst_int(l);

		Assert(rtindex > 0 && rtindex <= rtsize);
		epqstate->relsubs_blocked[rtindex - 1] = true;
	}

	memcpy(epqstate->relsubs_done, epqstate->relsubs_blocked,
		   rtsize * sizeof(bool));

	/*
	 * Initialize the private state information for all the nodes in the part
	 * of the plan tree we need to run.  This opens files, allocates storage
	 * and leaves us ready to start processing tuples.
	 */
	epqstate->recheckplanstate = ExecInitNode(planTree, rcestate, 0);

	MemoryContextSwitchTo(oldcontext);
}

/*
 * ============================================================================
 * 【中文注释】EvalPlanQualEnd —— 关闭 EPQ 重检查环境（精简版 ExecutorEnd）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在父计划节点关闭时（或更换子计划时）回收重检查环境：
 *   1. 清理元组表（epqstate->tuple_table，即使从未 Begin 也可能存在——
 *      因为 EvalPlanQualSlot 允许未 Begin 使用），并置空 relsubs_slot；
 *   2. 若重检查 EState 存在：ExecEndNode 关闭重检查计划树与其子计划、
 *      重置其元组表、关闭其结果关系与触发器目标关系；
 *   3. 置空 es_partition_directory（那是从父 EState 借用的，归父释放）；
 *   4. FreeExecutorState 释放整个重检查 EState；EPQ 状态字段归零，标记空闲。
 *
 * 设计思想：
 *   - 与 ExecutorEnd 的差异：绝不关闭共享的结果关系（属于外层查询）；
 *     但重检查 EState 自己动态打开的结果关系/触发器目标必须关闭；
 *   - 关闭顺序：先关计划树（依赖打开的 Relation），再关关系，最后释放
 *     内存上下文——与 ExecutorEnd 的层次一致。
 * ============================================================================
 */
void
EvalPlanQualEnd(EPQState *epqstate)
{
	EState	   *estate = epqstate->recheckestate;
	Index		rtsize;
	MemoryContext oldcontext;
	ListCell   *l;

	rtsize = epqstate->parentestate->es_range_table_size;

	/*
	 * We may have a tuple table, even if EPQ wasn't started, because we allow
	 * use of EvalPlanQualSlot() without calling EvalPlanQualBegin().
	 */
	if (epqstate->tuple_table != NIL)
	{
		memset(epqstate->relsubs_slot, 0,
			   rtsize * sizeof(TupleTableSlot *));
		ExecResetTupleTable(epqstate->tuple_table, true);
		epqstate->tuple_table = NIL;
	}

	/* EPQ wasn't started, nothing further to do */
	if (estate == NULL)
		return;

	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	ExecEndNode(epqstate->recheckplanstate);

	foreach(l, estate->es_subplanstates)
	{
		PlanState  *subplanstate = (PlanState *) lfirst(l);

		ExecEndNode(subplanstate);
	}

	/* throw away the per-estate tuple table, some node may have used it */
	ExecResetTupleTable(estate->es_tupleTable, false);

	/* Close any result and trigger target relations attached to this EState */
	ExecCloseResultRelations(estate);

	MemoryContextSwitchTo(oldcontext);

	/*
	 * NULLify the partition directory before freeing the executor state.
	 * Since EvalPlanQualStart() just borrowed the parent EState's directory,
	 * we'd better leave it up to the parent to delete it.
	 */
	estate->es_partition_directory = NULL;

	FreeExecutorState(estate);

	/* Mark EPQState idle */
	epqstate->origslot = NULL;
	epqstate->recheckestate = NULL;
	epqstate->recheckplanstate = NULL;
	epqstate->relsubs_rowmark = NULL;
	epqstate->relsubs_done = NULL;
	epqstate->relsubs_blocked = NULL;
}
