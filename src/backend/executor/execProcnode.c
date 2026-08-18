/*-------------------------------------------------------------------------
 *
 * execProcnode.c
 *	  执行器的"节点调度分发器"——按节点类型把调用路由到对应的节点实现
 *
 * 【业务作用】
 *   执行器以"计划树（Plan）→ 计划状态树（PlanState）"双层结构工作。每个
 *   节点类型（SeqScan/IndexScan/NestLoop/HashJoin/Agg/Sort/...）都有各自的
 *   Init/Exec/End 实现，本文件提供三个总入口，根据 nodeTag 分发调用：
 *
 *     ExecInitNode  —— 递归初始化：Plan 树 → PlanState 树
 *     ExecProcNode  —— 逐行取数：驱动节点产生下一行（顶层包装见
 *                      ExecProcNodeFirst / ExecSetExecProcNode）
 *     ExecEndNode   —— 递归清理：逆序关闭 PlanState 树
 *     另有 MultiExecProcNode（一次执行返回整体结果，如哈希表/位图）与
 *     ExecShutdownNode（提前停止异步资源，如并行 worker）。
 *
 * 【执行流程示例（传统教材中的三文件时代示例）】
 *   查询：SELECT DEPT.no_emps, EMP.age FROM DEPT, EMP
 *         WHERE EMP.name = DEPT.mgr AND DEPT.name = 'shoe'
 *   计划树（计划器输出）：
 *
 *            NestLoop (DEPT.mgr = EMP.name)
 *            /                         \
 *        SeqScan (DEPT)           SeqScan (EMP)
 *        (name = 'shoe')
 *
 *   生命周期：
 *     ExecutorStart ──> InitPlan ──> ExecInitNode(NestLoop) ──> ExecInitNestLoop
 *        ├─> ExecInitNode(左子 SeqScan) ──> ExecInitSeqScan
 *        └─> ExecInitNode(右子 SeqScan) ──> ExecInitSeqScan
 *        （递归完成后得到结构相同的 PlanState 树，挂在 estate 下）
 *
 *     ExecutorRun ──> ExecutePlan ──> 循环调用 ExecProcNode(顶层节点)
 *        ──> ExecNestLoop：反复调用其两个子节点的 ExecProcNode
 *            ──> ExecSeqScan：从堆扫描器取槽（内含 DEPT/EMP 各列数据）
 *            ──> 连接条件匹配则合成连接元组返回；否则继续取
 *
 *     ExecutorEnd ──> ExecEndPlan ──> ExecEndNode(顶层节点) ──> ExecEndNestLoop
 *        ├─> ExecEndNode(左子) ──> ExecEndSeqScan
 *        └─> ExecEndNode(右子) ──> ExecEndSeqScan
 *
 * 【设计思想】
 *   1. 统一分派、集中管理：所有节点类型的入口都收敛到本文件的几个 switch
 *      里。新增节点类型只需：加 case 分支 + 实现节点自己的三个函数，无需
 *      改动执行框架的其他部分（这也正是历史上把三个文件合并成一个的原因
 *      ——防止分发逻辑彼此脱节）；
 *   2. 初始化/取数/清理三阶段协议：任何节点都遵循同一"协议"，因此上层
 *      （ExecMain/各节点）可以透明地组合任意节点树；
 *   3. 包装器机制（ExecSetExecProcNode/ExecProcNodeFirst）：节点"真实"的
 *      取数函数存 ExecProcNodeReal，对外指针 ExecProcNode 先指向一次性包装
 *      函数（栈深度检查 + 挂载计时器包装），首跑后解除包装、直连真实函数，
 *      把每行执行开销压到最小；
 *   4. 所有分发入口统一做 check_stack_depth：计划树可能非常深（深层嵌套
 *      子查询/连接），防止递归击穿调用栈。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execProcnode.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "executor/executor.h"
#include "executor/instrument.h"
#include "executor/nodeAgg.h"
#include "executor/nodeAppend.h"
#include "executor/nodeBitmapAnd.h"
#include "executor/nodeBitmapHeapscan.h"
#include "executor/nodeBitmapIndexscan.h"
#include "executor/nodeBitmapOr.h"
#include "executor/nodeCtescan.h"
#include "executor/nodeCustom.h"
#include "executor/nodeForeignscan.h"
#include "executor/nodeFunctionscan.h"
#include "executor/nodeGather.h"
#include "executor/nodeGatherMerge.h"
#include "executor/nodeGroup.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "executor/nodeIncrementalSort.h"
#include "executor/nodeIndexonlyscan.h"
#include "executor/nodeIndexscan.h"
#include "executor/nodeLimit.h"
#include "executor/nodeLockRows.h"
#include "executor/nodeMaterial.h"
#include "executor/nodeMemoize.h"
#include "executor/nodeMergeAppend.h"
#include "executor/nodeMergejoin.h"
#include "executor/nodeModifyTable.h"
#include "executor/nodeNamedtuplestorescan.h"
#include "executor/nodeNestloop.h"
#include "executor/nodeProjectSet.h"
#include "executor/nodeRecursiveunion.h"
#include "executor/nodeResult.h"
#include "executor/nodeSamplescan.h"
#include "executor/nodeSeqscan.h"
#include "executor/nodeSetOp.h"
#include "executor/nodeSort.h"
#include "executor/nodeSubplan.h"
#include "executor/nodeSubqueryscan.h"
#include "executor/nodeTableFuncscan.h"
#include "executor/nodeTidrangescan.h"
#include "executor/nodeTidscan.h"
#include "executor/nodeUnique.h"
#include "executor/nodeValuesscan.h"
#include "executor/nodeWindowAgg.h"
#include "executor/nodeWorktablescan.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"

static TupleTableSlot *ExecProcNodeFirst(PlanState *node);
static bool ExecShutdownNode_walker(PlanState *node, void *context);


/*
 * ============================================================================
 * 【中文注释】ExecInitNode —— 递归初始化计划树（Plan → PlanState）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按节点类型分发调用对应节点的 ExecInitXXX，把计划树转换为等价的
 *   PlanState 状态树（节点状态含执行期上下文：表达式状态、元组槽、子计划
 *   状态等）。
 *
 * 参数：
 *   node   - 当前待初始化的计划节点（叶子（NULL）直接返回 NULL）；
 *   estate - 共享的执行状态（全树共用）；
 *   eflags - 执行标志位按位或（executor.h 的 EXEC_FLAG_*），向子节点传导。
 *
 * 返回值：
 *   与该 Plan 对应的 PlanState（挂在 estats 的 per-query 上下文内）。
 *
 * 流程（除分发外的固定工作）：
 *   1. check_stack_depth：初始化路径可能递归很深，防栈溢出；
 *   2. switch(nodeTag)：按节点类型分派（Result/ModifyTable/Append/各种
 *      Scan/各种 Join/物化与聚合节点等），具体初始化由各节点实现完成
 *      （它们内部会继续对子节点递归调用本函数）；
 *   3. ExecSetExecProcNode(result, result->ExecProcNode)：把节点的取数
 *      指针改为 ExecProcNodeFirst 包装（首跑做栈深检查与计时器包装）；
 *   4. 初始化本节点的 initPlan（无参子计划，如常量折叠需要的表达式求值
 *      计划）——它们没有参数，不需要执行期求值，只需建好状态；
 *   5. 若启用了 instrumentation（EXPLAIN ANALYZE），为本节点分配计时器。
 *
 * 设计思想：
 *   - 递归架构：每个节点负责初始化自己的子节点（左子/右子/多子），保证
 *     计划树与状态树结构严格同构；
 *   - initPlan 与 subPlan 的区分：initPlan 无条件预先执行一次（结果可被
 *     多处引用）；subPlan 带参数、按需执行，由 ExecInitSubPlanExpr 处理。
 * ============================================================================
 */
PlanState *
ExecInitNode(Plan *node, EState *estate, int eflags)
{
	PlanState  *result;
	List	   *subps;
	ListCell   *l;

	/*
	 * do nothing when we get to the end of a leaf on tree.
	 */
	if (node == NULL)
		return NULL;

	/*
	 * Make sure there's enough stack available. Need to check here, in
	 * addition to ExecProcNode() (via ExecProcNodeFirst()), to ensure the
	 * stack isn't overrun while initializing the node tree.
	 */
	check_stack_depth();

	switch (nodeTag(node))
	{
			/*
			 * control nodes
			 */
		case T_Result:
			result = (PlanState *) ExecInitResult((Result *) node,
												  estate, eflags);
			break;

		case T_ProjectSet:
			result = (PlanState *) ExecInitProjectSet((ProjectSet *) node,
													  estate, eflags);
			break;

		case T_ModifyTable:
			result = (PlanState *) ExecInitModifyTable((ModifyTable *) node,
													   estate, eflags);
			break;

		case T_Append:
			result = (PlanState *) ExecInitAppend((Append *) node,
												  estate, eflags);
			break;

		case T_MergeAppend:
			result = (PlanState *) ExecInitMergeAppend((MergeAppend *) node,
													   estate, eflags);
			break;

		case T_RecursiveUnion:
			result = (PlanState *) ExecInitRecursiveUnion((RecursiveUnion *) node,
														  estate, eflags);
			break;

		case T_BitmapAnd:
			result = (PlanState *) ExecInitBitmapAnd((BitmapAnd *) node,
													 estate, eflags);
			break;

		case T_BitmapOr:
			result = (PlanState *) ExecInitBitmapOr((BitmapOr *) node,
													estate, eflags);
			break;

			/*
			 * scan nodes
			 */
		case T_SeqScan:
			result = (PlanState *) ExecInitSeqScan((SeqScan *) node,
												   estate, eflags);
			break;

		case T_SampleScan:
			result = (PlanState *) ExecInitSampleScan((SampleScan *) node,
													  estate, eflags);
			break;

		case T_IndexScan:
			result = (PlanState *) ExecInitIndexScan((IndexScan *) node,
													 estate, eflags);
			break;

		case T_IndexOnlyScan:
			result = (PlanState *) ExecInitIndexOnlyScan((IndexOnlyScan *) node,
														 estate, eflags);
			break;

		case T_BitmapIndexScan:
			result = (PlanState *) ExecInitBitmapIndexScan((BitmapIndexScan *) node,
														   estate, eflags);
			break;

		case T_BitmapHeapScan:
			result = (PlanState *) ExecInitBitmapHeapScan((BitmapHeapScan *) node,
														  estate, eflags);
			break;

		case T_TidScan:
			result = (PlanState *) ExecInitTidScan((TidScan *) node,
												   estate, eflags);
			break;

		case T_TidRangeScan:
			result = (PlanState *) ExecInitTidRangeScan((TidRangeScan *) node,
														estate, eflags);
			break;

		case T_SubqueryScan:
			result = (PlanState *) ExecInitSubqueryScan((SubqueryScan *) node,
														estate, eflags);
			break;

		case T_FunctionScan:
			result = (PlanState *) ExecInitFunctionScan((FunctionScan *) node,
														estate, eflags);
			break;

		case T_TableFuncScan:
			result = (PlanState *) ExecInitTableFuncScan((TableFuncScan *) node,
														 estate, eflags);
			break;

		case T_ValuesScan:
			result = (PlanState *) ExecInitValuesScan((ValuesScan *) node,
													  estate, eflags);
			break;

		case T_CteScan:
			result = (PlanState *) ExecInitCteScan((CteScan *) node,
												   estate, eflags);
			break;

		case T_NamedTuplestoreScan:
			result = (PlanState *) ExecInitNamedTuplestoreScan((NamedTuplestoreScan *) node,
															   estate, eflags);
			break;

		case T_WorkTableScan:
			result = (PlanState *) ExecInitWorkTableScan((WorkTableScan *) node,
														 estate, eflags);
			break;

		case T_ForeignScan:
			result = (PlanState *) ExecInitForeignScan((ForeignScan *) node,
													   estate, eflags);
			break;

		case T_CustomScan:
			result = (PlanState *) ExecInitCustomScan((CustomScan *) node,
													  estate, eflags);
			break;

			/*
			 * join nodes
			 */
		case T_NestLoop:
			result = (PlanState *) ExecInitNestLoop((NestLoop *) node,
													estate, eflags);
			break;

		case T_MergeJoin:
			result = (PlanState *) ExecInitMergeJoin((MergeJoin *) node,
													 estate, eflags);
			break;

		case T_HashJoin:
			result = (PlanState *) ExecInitHashJoin((HashJoin *) node,
													estate, eflags);
			break;

			/*
			 * materialization nodes
			 */
		case T_Material:
			result = (PlanState *) ExecInitMaterial((Material *) node,
													estate, eflags);
			break;

		case T_Sort:
			result = (PlanState *) ExecInitSort((Sort *) node,
												estate, eflags);
			break;

		case T_IncrementalSort:
			result = (PlanState *) ExecInitIncrementalSort((IncrementalSort *) node,
														   estate, eflags);
			break;

		case T_Memoize:
			result = (PlanState *) ExecInitMemoize((Memoize *) node, estate,
												   eflags);
			break;

		case T_Group:
			result = (PlanState *) ExecInitGroup((Group *) node,
												 estate, eflags);
			break;

		case T_Agg:
			result = (PlanState *) ExecInitAgg((Agg *) node,
											   estate, eflags);
			break;

		case T_WindowAgg:
			result = (PlanState *) ExecInitWindowAgg((WindowAgg *) node,
													 estate, eflags);
			break;

		case T_Unique:
			result = (PlanState *) ExecInitUnique((Unique *) node,
												  estate, eflags);
			break;

		case T_Gather:
			result = (PlanState *) ExecInitGather((Gather *) node,
												  estate, eflags);
			break;

		case T_GatherMerge:
			result = (PlanState *) ExecInitGatherMerge((GatherMerge *) node,
													   estate, eflags);
			break;

		case T_Hash:
			result = (PlanState *) ExecInitHash((Hash *) node,
												estate, eflags);
			break;

		case T_SetOp:
			result = (PlanState *) ExecInitSetOp((SetOp *) node,
												 estate, eflags);
			break;

		case T_LockRows:
			result = (PlanState *) ExecInitLockRows((LockRows *) node,
													estate, eflags);
			break;

		case T_Limit:
			result = (PlanState *) ExecInitLimit((Limit *) node,
												 estate, eflags);
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			result = NULL;		/* keep compiler quiet */
			break;
	}

	ExecSetExecProcNode(result, result->ExecProcNode);

	/*
	 * Initialize any initPlans present in this node.  The planner put them in
	 * a separate list for us.
	 *
	 * The defining characteristic of initplans is that they don't have
	 * arguments, so we don't need to evaluate them (in contrast to
	 * ExecInitSubPlanExpr()).
	 */
	subps = NIL;
	foreach(l, node->initPlan)
	{
		SubPlan    *subplan = (SubPlan *) lfirst(l);
		SubPlanState *sstate;

		Assert(IsA(subplan, SubPlan));
		Assert(subplan->args == NIL);
		sstate = ExecInitSubPlan(subplan, result);
		subps = lappend(subps, sstate);
	}
	result->initPlan = subps;

	/* Set up instrumentation for this node if requested */
	if (estate->es_instrument)
		result->instrument = InstrAllocNode(estate->es_instrument,
											result->async_capable);

	return result;
}


/*
 * ============================================================================
 * 【中文注释】ExecSetExecProcNode —— 重新安装节点的取数函数（带包装）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   节点在初始化完成后若需要更换自己的取数函数（例如 Append 切换到
 *   ExecAppendNext、节点类型特化），必须通过本函数设置——它会记录真实函数
 *   到 ExecProcNodeReal，并把对外指针 ExecProcNode 指向包装函数
 *   ExecProcNodeFirst。
 *
 * 设计思想：
 *   - 包装器分两层职责：首跑时做栈深度检查（一次性开销），并按需挂上
 *     instrumentation 包装（ExecProcNodeInstr，统计节点耗时/行数）；
 *   - 包装层对节点透明：节点只感知"设置函数"这一操作，不必了解包装细节；
 *   - 执行开始后更换函数也无碍：只是多余地再跑一次 ExecProcNodeFirst，
 *     开销可忽略。
 * ============================================================================
 */
void
ExecSetExecProcNode(PlanState *node, ExecProcNodeMtd function)
{
	/*
	 * Add a wrapper around the ExecProcNode callback that checks stack depth
	 * during the first execution and maybe adds an instrumentation wrapper.
	 * When the callback is changed after execution has already begun that
	 * means we'll superfluously execute ExecProcNodeFirst, but that seems ok.
	 */
	node->ExecProcNodeReal = function;
	node->ExecProcNode = ExecProcNodeFirst;
}


/*
 * ============================================================================
 * 【中文注释】ExecProcNodeFirst —— 取数函数的一次性前置包装
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   节点首次被驱动取数时先执行本包装：检查栈深度，然后根据是否需要计时
 *   决定把 ExecProcNode 换成 ExecProcNodeInstr（计时包装）还是直接换成
 *   ExecProcNodeReal（真实函数），并立即转调。
 *
 * 设计思想：
 *   - 栈深检查只做一次：实测在部分 CPU 架构（如 x86）上 check_stack_depth
 *     并不便宜；且对同一节点，各次 ExecProcNode 调用的栈深基本一致，首跑
 *     检查足以代表后续——这正是"包装函数一次化"的依据；
 *   - 免包装直连：不需要计时的节点，第二次调用起就是函数指针直呼，
 *     每行执行零额外开销。
 * ============================================================================
 */
static TupleTableSlot *
ExecProcNodeFirst(PlanState *node)
{
	/*
	 * Perform stack depth check during the first execution of the node.  We
	 * only do so the first time round because it turns out to not be cheap on
	 * some common architectures (eg. x86).  This relies on the assumption
	 * that ExecProcNode calls for a given plan node will always be made at
	 * roughly the same stack depth.
	 */
	check_stack_depth();

	/*
	 * If instrumentation is required, change the wrapper to one that just
	 * does instrumentation.  Otherwise we can dispense with all wrappers and
	 * have ExecProcNode() directly call the relevant function from now on.
	 */
	if (node->instrument)
		node->ExecProcNode = ExecProcNodeInstr;
	else
		node->ExecProcNode = node->ExecProcNodeReal;

	return node->ExecProcNode(node);
}



/*
 * ============================================================================
 * 【中文注释】MultiExecProcNode —— 执行"一次性产出整体结果"的节点
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   驱动不按"逐行取数"工作、而是"一次执行产出整个对象"的节点：
 *   - Hash 节点：产出整个哈希表（供 HashJoin 探测）；
 *   - BitmapIndexScan：产出候选 TID 位图；
 *   - BitmapAnd/BitmapOr：对多个位图做交集/并集。
 *   返回值 Node*，调用方自行断言类型（哈希表/位图等）。
 *
 * 设计思想：
 *   - 与 ExecProcNode 的分工：逐行协议走 ExecProcNode；整体结果走本函数。
 *     因此本函数不做 InstrStartNode/InstrStopNode 自动计时——它不知道"产出
 *     了几行"，每个节点的 MultiExecXXX 必须自带计时支持；
 *   - 同样先处理 chgParam（参数已变则先 ReScan），再分发；
 *   - 栈深检查与中断检查（CHECK_FOR_INTERRUPTS）在进入分发前统一做。
 * ============================================================================
 */
Node *
MultiExecProcNode(PlanState *node)
{
	Node	   *result;

	check_stack_depth();

	CHECK_FOR_INTERRUPTS();

	if (node->chgParam != NULL) /* something changed */
		ExecReScan(node);		/* let ReScan handle this */

	switch (nodeTag(node))
	{
			/*
			 * Only node types that actually support multiexec will be listed
			 */

		case T_HashState:
			result = MultiExecHash((HashState *) node);
			break;

		case T_BitmapIndexScanState:
			result = MultiExecBitmapIndexScan((BitmapIndexScanState *) node);
			break;

		case T_BitmapAndState:
			result = MultiExecBitmapAnd((BitmapAndState *) node);
			break;

		case T_BitmapOrState:
			result = MultiExecBitmapOr((BitmapOrState *) node);
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			result = NULL;
			break;
	}

	return result;
}


/*
 * ============================================================================
 * 【中文注释】ExecEndNode —— 递归清理计划状态树
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 ExecInitNode 对称的逆向过程：按节点类型分发调用 ExecEndXXX，逐层
 *   关闭节点（释放缓冲 pin、关闭关系/游标、清理临时文件等）。清理后该计划
 *   树不可再执行。
 *
 * 设计思想：
 *   - 递归：每个节点的 ExecEndXXX 内部会先 End 自己的子节点再释放自身
 *     资源（先内后外），保证依赖顺序正确；
 *   - 特殊节点免清理：ValuesScan/NamedTuplestoreScan/WorkTableScan 无持有
 *     资源，直接跳过（省一次函数调用）；
 *   - 顺带释放 chgParam 位图（参数变更标记，执行结束后不再需要）；
 *   - 内存本身不需要逐节点释放——整体由所属内存上下文回收，这里只关
 *     闭"有外部资源"的句柄。
 * ============================================================================
 */
void
ExecEndNode(PlanState *node)
{
	/*
	 * do nothing when we get to the end of a leaf on tree.
	 */
	if (node == NULL)
		return;

	/*
	 * Make sure there's enough stack available. Need to check here, in
	 * addition to ExecProcNode() (via ExecProcNodeFirst()), because it's not
	 * guaranteed that ExecProcNode() is reached for all nodes.
	 */
	check_stack_depth();

	if (node->chgParam != NULL)
	{
		bms_free(node->chgParam);
		node->chgParam = NULL;
	}

	switch (nodeTag(node))
	{
			/*
			 * control nodes
			 */
		case T_ResultState:
			ExecEndResult((ResultState *) node);
			break;

		case T_ProjectSetState:
			ExecEndProjectSet((ProjectSetState *) node);
			break;

		case T_ModifyTableState:
			ExecEndModifyTable((ModifyTableState *) node);
			break;

		case T_AppendState:
			ExecEndAppend((AppendState *) node);
			break;

		case T_MergeAppendState:
			ExecEndMergeAppend((MergeAppendState *) node);
			break;

		case T_RecursiveUnionState:
			ExecEndRecursiveUnion((RecursiveUnionState *) node);
			break;

		case T_BitmapAndState:
			ExecEndBitmapAnd((BitmapAndState *) node);
			break;

		case T_BitmapOrState:
			ExecEndBitmapOr((BitmapOrState *) node);
			break;

			/*
			 * scan nodes
			 */
		case T_SeqScanState:
			ExecEndSeqScan((SeqScanState *) node);
			break;

		case T_SampleScanState:
			ExecEndSampleScan((SampleScanState *) node);
			break;

		case T_GatherState:
			ExecEndGather((GatherState *) node);
			break;

		case T_GatherMergeState:
			ExecEndGatherMerge((GatherMergeState *) node);
			break;

		case T_IndexScanState:
			ExecEndIndexScan((IndexScanState *) node);
			break;

		case T_IndexOnlyScanState:
			ExecEndIndexOnlyScan((IndexOnlyScanState *) node);
			break;

		case T_BitmapIndexScanState:
			ExecEndBitmapIndexScan((BitmapIndexScanState *) node);
			break;

		case T_BitmapHeapScanState:
			ExecEndBitmapHeapScan((BitmapHeapScanState *) node);
			break;

		case T_TidScanState:
			ExecEndTidScan((TidScanState *) node);
			break;

		case T_TidRangeScanState:
			ExecEndTidRangeScan((TidRangeScanState *) node);
			break;

		case T_SubqueryScanState:
			ExecEndSubqueryScan((SubqueryScanState *) node);
			break;

		case T_FunctionScanState:
			ExecEndFunctionScan((FunctionScanState *) node);
			break;

		case T_TableFuncScanState:
			ExecEndTableFuncScan((TableFuncScanState *) node);
			break;

		case T_CteScanState:
			ExecEndCteScan((CteScanState *) node);
			break;

		case T_ForeignScanState:
			ExecEndForeignScan((ForeignScanState *) node);
			break;

		case T_CustomScanState:
			ExecEndCustomScan((CustomScanState *) node);
			break;

			/*
			 * join nodes
			 */
		case T_NestLoopState:
			ExecEndNestLoop((NestLoopState *) node);
			break;

		case T_MergeJoinState:
			ExecEndMergeJoin((MergeJoinState *) node);
			break;

		case T_HashJoinState:
			ExecEndHashJoin((HashJoinState *) node);
			break;

			/*
			 * materialization nodes
			 */
		case T_MaterialState:
			ExecEndMaterial((MaterialState *) node);
			break;

		case T_SortState:
			ExecEndSort((SortState *) node);
			break;

		case T_IncrementalSortState:
			ExecEndIncrementalSort((IncrementalSortState *) node);
			break;

		case T_MemoizeState:
			ExecEndMemoize((MemoizeState *) node);
			break;

		case T_GroupState:
			ExecEndGroup((GroupState *) node);
			break;

		case T_AggState:
			ExecEndAgg((AggState *) node);
			break;

		case T_WindowAggState:
			ExecEndWindowAgg((WindowAggState *) node);
			break;

		case T_UniqueState:
			ExecEndUnique((UniqueState *) node);
			break;

		case T_HashState:
			ExecEndHash((HashState *) node);
			break;

		case T_SetOpState:
			ExecEndSetOp((SetOpState *) node);
			break;

		case T_LockRowsState:
			ExecEndLockRows((LockRowsState *) node);
			break;

		case T_LimitState:
			ExecEndLimit((LimitState *) node);
			break;

			/* No clean up actions for these nodes. */
		case T_ValuesScanState:
		case T_NamedTuplestoreScanState:
		case T_WorkTableScanState:
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			break;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecShutdownNode —— 提前停止节点的异步资源消耗
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在查询提前结束（如 LIMIT 截断、非 BACKWARD 模式跑完）时，主动让
 *   Gather/GatherMerge 停止并回收并行 worker、让 ForeignScan 关闭其外部
 *   异步资源等，避免后台任务继续占用资源。
 *
 * 设计思想：
 *   递归遍历整棵树（planstate_tree_walker 先子后父），对支持提前停止的
 *   节点调用 ExecShutdownXXX。与 ExecEndNode 的区别：本函数只做"停止"，
 *   不销毁节点状态（随后仍可能 ReScan 复用）。
 * ============================================================================
 */
void
ExecShutdownNode(PlanState *node)
{
	(void) ExecShutdownNode_walker(node, NULL);
}

/*
 * ============================================================================
 * 【中文注释】ExecShutdownNode_walker —— 关闭遍历器（先子后父）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   实现 ExecShutdownNode 的递归：依次对每个节点
 *   1. 若节点计时器正在运行（曾被执行过），先 InstrStartNode 重新"续时"，
 *      使关闭阶段的 CPU/缓冲消耗计入该节点（Gather 回收 worker 时其缓冲
 *      使用量会汇入 pgBufferUsage）；
 *   2. 先遍历子树（子节点先关闭），再对自身做类型分派的 ExecShutdownXXX；
 *   3. 若上面启动了计时器，用 InstrStopNode(0 行) 停止。
 *
 * 设计思想：
 *   计时器的续停技巧：正常 ExecProcNode 会 InstrStart/Stop 配对；关闭阶段
 *   不在 ExecProcNode 内，这里手动配对，把关闭耗时正确归属到节点统计，
 *   但行数计 0（不产出元组）。从未执行过的节点跳过（避免假象的"运行过"）。
 * ============================================================================
 */
static bool
ExecShutdownNode_walker(PlanState *node, void *context)
{
	if (node == NULL)
		return false;

	check_stack_depth();

	/*
	 * Treat the node as running while we shut it down, but only if it's run
	 * at least once already.  We don't expect much CPU consumption during
	 * node shutdown, but in the case of Gather or Gather Merge, we may shut
	 * down workers at this stage.  If so, their buffer usage will get
	 * propagated into pgBufferUsage at this point, and we want to make sure
	 * that it gets associated with the Gather node.  We skip this if the node
	 * has never been executed, so as to avoid incorrectly making it appear
	 * that it has.
	 */
	if (node->instrument && node->instrument->running)
		InstrStartNode(node->instrument);

	planstate_tree_walker(node, ExecShutdownNode_walker, context);

	switch (nodeTag(node))
	{
		case T_GatherState:
			ExecShutdownGather((GatherState *) node);
			break;
		case T_ForeignScanState:
			ExecShutdownForeignScan((ForeignScanState *) node);
			break;
		case T_CustomScanState:
			ExecShutdownCustomScan((CustomScanState *) node);
			break;
		case T_GatherMergeState:
			ExecShutdownGatherMerge((GatherMergeState *) node);
			break;
		case T_HashState:
			ExecShutdownHash((HashState *) node);
			break;
		case T_HashJoinState:
			ExecShutdownHashJoin((HashJoinState *) node);
			break;
		default:
			break;
	}

	/* Stop the node if we started it above, reporting 0 tuples. */
	if (node->instrument && node->instrument->running)
		InstrStopNode(node->instrument, 0);

	return false;
}

/*
 * ============================================================================
 * 【中文注释】ExecSetTupleBound —— 向下级节点传递"父节点最多需要多少行"
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把元组数量上限（tuples_needed）通知给（并尽力传导给）子计划树上的
 *   相关节点，使它们能做针对性优化。tuples_needed < 0 表示"无限制"
 *   （清除此前设置的界限）。仅在两次扫描之间允许调用（初始化后或
 *   ExecReScan 前）。
 *
 * 业务场景与优化效果：
 *   - LIMIT n 场景下，n 会传导给 Sort/IncrementalSort（bounded sort——
 *     只保留最小的 n 个元素，内存占用与耗时大幅下降）与 Gather/GatherMerge
 *     （tuples_needed 传给 worker 提前停止取数）；
 *   - 向下穿透规则：只穿透"不吞行/不合并行"的节点——
 *       Append/MergeAppend：任一路输入最多也只需这么多行（逐子传导）；
 *       Result：只做投影（无 qual 时）→ 穿透到其子节点；
 *       SubqueryScan：无 qual 时穿透（有 qual 可能丢弃行，不能传）；
 *       Gather/GatherMerge：任意单 worker 不会产出超过总数（穿透）；
 *     Sort/IncrementalSort 自身是"边界节点"（消费全部输入），作为终点；
 *     其他可能丢弃/合并行的节点（Group/Agg/Join/Filter）一律不穿透。
 *
 * 参数：
 *   tuples_needed - 上限（负数 = 无限制）；child_node - 目标子计划节点。
 *
 * 注意：对同一计划树多次调用时，每次必须更新同一组节点，故这里的判断
 * 只能依赖"不变的条件"（节点类型），不能依赖会变的执行状态。
 * ============================================================================
 */
void
ExecSetTupleBound(int64 tuples_needed, PlanState *child_node)
{
	/*
	 * Since this function recurses, in principle we should check stack depth
	 * here.  In practice, it's probably pointless since the earlier node
	 * initialization tree traversal would surely have consumed more stack.
	 */

	if (IsA(child_node, SortState))
	{
		/*
		 * If it is a Sort node, notify it that it can use bounded sort.
		 *
		 * Note: it is the responsibility of nodeSort.c to react properly to
		 * changes of these parameters.  If we ever redesign this, it'd be a
		 * good idea to integrate this signaling with the parameter-change
		 * mechanism.
		 */
		SortState  *sortState = (SortState *) child_node;

		if (tuples_needed < 0)
		{
			/* make sure flag gets reset if needed upon rescan */
			sortState->bounded = false;
		}
		else
		{
			sortState->bounded = true;
			sortState->bound = tuples_needed;
		}
	}
	else if (IsA(child_node, IncrementalSortState))
	{
		/*
		 * If it is an IncrementalSort node, notify it that it can use bounded
		 * sort.
		 *
		 * Note: it is the responsibility of nodeIncrementalSort.c to react
		 * properly to changes of these parameters.  If we ever redesign this,
		 * it'd be a good idea to integrate this signaling with the
		 * parameter-change mechanism.
		 */
		IncrementalSortState *sortState = (IncrementalSortState *) child_node;

		if (tuples_needed < 0)
		{
			/* make sure flag gets reset if needed upon rescan */
			sortState->bounded = false;
		}
		else
		{
			sortState->bounded = true;
			sortState->bound = tuples_needed;
		}
	}
	else if (IsA(child_node, AppendState))
	{
		/*
		 * If it is an Append, we can apply the bound to any nodes that are
		 * children of the Append, since the Append surely need read no more
		 * than that many tuples from any one input.
		 */
		AppendState *aState = (AppendState *) child_node;
		int			i;

		for (i = 0; i < aState->as_nplans; i++)
			ExecSetTupleBound(tuples_needed, aState->appendplans[i]);
	}
	else if (IsA(child_node, MergeAppendState))
	{
		/*
		 * If it is a MergeAppend, we can apply the bound to any nodes that
		 * are children of the MergeAppend, since the MergeAppend surely need
		 * read no more than that many tuples from any one input.
		 */
		MergeAppendState *maState = (MergeAppendState *) child_node;
		int			i;

		for (i = 0; i < maState->ms_nplans; i++)
			ExecSetTupleBound(tuples_needed, maState->mergeplans[i]);
	}
	else if (IsA(child_node, ResultState))
	{
		/*
		 * Similarly, for a projecting Result, we can apply the bound to its
		 * child node.
		 *
		 * If Result supported qual checking, we'd have to punt on seeing a
		 * qual.  Note that having a resconstantqual is not a showstopper: if
		 * that condition succeeds it affects nothing, while if it fails, no
		 * rows will be demanded from the Result child anyway.
		 */
		if (outerPlanState(child_node))
			ExecSetTupleBound(tuples_needed, outerPlanState(child_node));
	}
	else if (IsA(child_node, SubqueryScanState))
	{
		/*
		 * We can also descend through SubqueryScan, but only if it has no
		 * qual (otherwise it might discard rows).
		 */
		SubqueryScanState *subqueryState = (SubqueryScanState *) child_node;

		if (subqueryState->ss.ps.qual == NULL)
			ExecSetTupleBound(tuples_needed, subqueryState->subplan);
	}
	else if (IsA(child_node, GatherState))
	{
		/*
		 * A Gather node can propagate the bound to its workers.  As with
		 * MergeAppend, no one worker could possibly need to return more
		 * tuples than the Gather itself needs to.
		 *
		 * Note: As with Sort, the Gather node is responsible for reacting
		 * properly to changes to this parameter.
		 */
		GatherState *gstate = (GatherState *) child_node;

		gstate->tuples_needed = tuples_needed;

		/* Also pass down the bound to our own copy of the child plan */
		ExecSetTupleBound(tuples_needed, outerPlanState(child_node));
	}
	else if (IsA(child_node, GatherMergeState))
	{
		/* Same comments as for Gather */
		GatherMergeState *gstate = (GatherMergeState *) child_node;

		gstate->tuples_needed = tuples_needed;

		ExecSetTupleBound(tuples_needed, outerPlanState(child_node));
	}

	/*
	 * In principle we could descend through any plan node type that is
	 * certain not to discard or combine input rows; but on seeing a node that
	 * can do that, we can't propagate the bound any further.  For the moment
	 * it's unclear that any other cases are worth checking here.
	 */
}
