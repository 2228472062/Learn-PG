/*-------------------------------------------------------------------------
 *
 * execAmi.c
 *	  miscellaneous executor access method routines
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *	src/backend/executor/execAmi.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * ============================================================================
 * 【中文注释】execAmi.c —— 执行器访问方法杂项（全局能力分发）
 * ----------------------------------------------------------------------------
 * 文件定位：
 *   与"节点类型无关"的执行器级入口，全部以"按节点类型分发到具体节点
 *   实现"为工作方式，类似 execProcnode.c 但服务于扫描/重扫控制面：
 *   - ExecReScan：让计划节点可重新扫描（参数变化后的重执行、嵌套循环
 *     内层重扫等），分发到各节点的 ExecReScanXxx；
 *   - ExecMarkPos / ExecRestrPos：标记/恢复扫描位置（MergeJoin 的内层
 *     回退需要），仅少数节点支持；
 *   - ExecSupportsMarkRestore / ExecSupportsBackwardScan / 
 *     ExecMaterializesOutput：给规划器用的"能力查询"（输入是 Path/Plan，
 *     在规划期静态回答）。
 * ============================================================================
 */
#include "postgres.h"

#include "access/amapi.h"
#include "access/htup_details.h"
#include "catalog/pg_class.h"
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
#include "nodes/extensible.h"
#include "nodes/pathnodes.h"
#include "utils/syscache.h"

static bool IndexSupportsBackwardScan(Oid indexid);


/*
 * ============================================================================
 * 【中文注释】ExecReScan —— 重置节点以便重新扫描（分发入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   执行器的"重扫"总入口，做四件事：
 *   1. 计费收尾（InstrEndLoop）；
 *   2. 参数传播——若本节点 chgParam 非空（本节点依赖的参数已变化）：
 *      先通知 InitPlan（其输出参数可能因此需重算，且 InitPlan 之间的
 *      依赖顺序受遍历顺序约束）、SubPlan，再向下传播给左右子计划，
 *      并继续递归（子计划 ExecReScan 时自身 chgParam 也按此法处理）；
 *   3. 表达式上下文重扫（ReScanExprContext 执行注册的重扫回调，如
 *      hash 桶位置重算）；
 *   4. 按节点类型分发到具体 ExecReScanXxx（各节点重开游标/清空状态），
 *      最后清空本节点 chgParam。
 *
 * 注意：参数值变了，重扫结果可能与上次不同——这正是 chgParam 机制
 * 存在的意义（参数化路径/嵌套循环/InitPlan 联动）。
 * ============================================================================
 */
void
ExecReScan(PlanState *node)
{
	/* If collecting timing stats, update them */
	if (node->instrument)
		InstrEndLoop(node->instrument);

	/*
	 * If we have changed parameters, propagate that info.
	 *
	 * Note: ExecReScanSetParamPlan() can add bits to node->chgParam,
	 * corresponding to the output param(s) that the InitPlan will update.
	 * Since we make only one pass over the list, that means that an InitPlan
	 * can depend on the output param(s) of a sibling InitPlan only if that
	 * sibling appears earlier in the list.  This is workable for now given
	 * the limited ways in which one InitPlan could depend on another, but
	 * eventually we might need to work harder (or else make the planner
	 * enlarge the extParam/allParam sets to include the params of depended-on
	 * InitPlans).
	 */
	if (node->chgParam != NULL)
	{
		ListCell   *l;

		foreach(l, node->initPlan)
		{
			SubPlanState *sstate = (SubPlanState *) lfirst(l);
			PlanState  *splan = sstate->planstate;

			if (splan->plan->extParam != NULL)	/* don't care about child
												 * local Params */
				UpdateChangedParamSet(splan, node->chgParam);
			if (splan->chgParam != NULL)
				ExecReScanSetParamPlan(sstate, node);
		}
		foreach(l, node->subPlan)
		{
			SubPlanState *sstate = (SubPlanState *) lfirst(l);
			PlanState  *splan = sstate->planstate;

			if (splan->plan->extParam != NULL)
				UpdateChangedParamSet(splan, node->chgParam);
		}
		/* Well. Now set chgParam for child trees. */
		if (outerPlanState(node) != NULL)
			UpdateChangedParamSet(outerPlanState(node), node->chgParam);
		if (innerPlanState(node) != NULL)
			UpdateChangedParamSet(innerPlanState(node), node->chgParam);
	}

	/* Call expression callbacks */
	if (node->ps_ExprContext)
		ReScanExprContext(node->ps_ExprContext);

	/* And do node-type-specific processing */
	switch (nodeTag(node))
	{
		case T_ResultState:
			ExecReScanResult((ResultState *) node);
			break;

		case T_ProjectSetState:
			ExecReScanProjectSet((ProjectSetState *) node);
			break;

		case T_ModifyTableState:
			ExecReScanModifyTable((ModifyTableState *) node);
			break;

		case T_AppendState:
			ExecReScanAppend((AppendState *) node);
			break;

		case T_MergeAppendState:
			ExecReScanMergeAppend((MergeAppendState *) node);
			break;

		case T_RecursiveUnionState:
			ExecReScanRecursiveUnion((RecursiveUnionState *) node);
			break;

		case T_BitmapAndState:
			ExecReScanBitmapAnd((BitmapAndState *) node);
			break;

		case T_BitmapOrState:
			ExecReScanBitmapOr((BitmapOrState *) node);
			break;

		case T_SeqScanState:
			ExecReScanSeqScan((SeqScanState *) node);
			break;

		case T_SampleScanState:
			ExecReScanSampleScan((SampleScanState *) node);
			break;

		case T_GatherState:
			ExecReScanGather((GatherState *) node);
			break;

		case T_GatherMergeState:
			ExecReScanGatherMerge((GatherMergeState *) node);
			break;

		case T_IndexScanState:
			ExecReScanIndexScan((IndexScanState *) node);
			break;

		case T_IndexOnlyScanState:
			ExecReScanIndexOnlyScan((IndexOnlyScanState *) node);
			break;

		case T_BitmapIndexScanState:
			ExecReScanBitmapIndexScan((BitmapIndexScanState *) node);
			break;

		case T_BitmapHeapScanState:
			ExecReScanBitmapHeapScan((BitmapHeapScanState *) node);
			break;

		case T_TidScanState:
			ExecReScanTidScan((TidScanState *) node);
			break;

		case T_TidRangeScanState:
			ExecReScanTidRangeScan((TidRangeScanState *) node);
			break;

		case T_SubqueryScanState:
			ExecReScanSubqueryScan((SubqueryScanState *) node);
			break;

		case T_FunctionScanState:
			ExecReScanFunctionScan((FunctionScanState *) node);
			break;

		case T_TableFuncScanState:
			ExecReScanTableFuncScan((TableFuncScanState *) node);
			break;

		case T_ValuesScanState:
			ExecReScanValuesScan((ValuesScanState *) node);
			break;

		case T_CteScanState:
			ExecReScanCteScan((CteScanState *) node);
			break;

		case T_NamedTuplestoreScanState:
			ExecReScanNamedTuplestoreScan((NamedTuplestoreScanState *) node);
			break;

		case T_WorkTableScanState:
			ExecReScanWorkTableScan((WorkTableScanState *) node);
			break;

		case T_ForeignScanState:
			ExecReScanForeignScan((ForeignScanState *) node);
			break;

		case T_CustomScanState:
			ExecReScanCustomScan((CustomScanState *) node);
			break;

		case T_NestLoopState:
			ExecReScanNestLoop((NestLoopState *) node);
			break;

		case T_MergeJoinState:
			ExecReScanMergeJoin((MergeJoinState *) node);
			break;

		case T_HashJoinState:
			ExecReScanHashJoin((HashJoinState *) node);
			break;

		case T_MaterialState:
			ExecReScanMaterial((MaterialState *) node);
			break;

		case T_MemoizeState:
			ExecReScanMemoize((MemoizeState *) node);
			break;

		case T_SortState:
			ExecReScanSort((SortState *) node);
			break;

		case T_IncrementalSortState:
			ExecReScanIncrementalSort((IncrementalSortState *) node);
			break;

		case T_GroupState:
			ExecReScanGroup((GroupState *) node);
			break;

		case T_AggState:
			ExecReScanAgg((AggState *) node);
			break;

		case T_WindowAggState:
			ExecReScanWindowAgg((WindowAggState *) node);
			break;

		case T_UniqueState:
			ExecReScanUnique((UniqueState *) node);
			break;

		case T_HashState:
			ExecReScanHash((HashState *) node);
			break;

		case T_SetOpState:
			ExecReScanSetOp((SetOpState *) node);
			break;

		case T_LockRowsState:
			ExecReScanLockRows((LockRowsState *) node);
			break;

		case T_LimitState:
			ExecReScanLimit((LimitState *) node);
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			break;
	}

	if (node->chgParam != NULL)
	{
		bms_free(node->chgParam);
		node->chgParam = NULL;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecMarkPos / ExecRestrPos —— 扫描位置标记与恢复
 * ----------------------------------------------------------------------------
 * 业务场景（成对使用）：
 *   MergeJoin 的内层输入需要"回退"（外层新行的键比当前内层键小）：
 *   MergeJoin 发出 ExecMarkPos 记下当前位置，随后继续推进；需要回退时
 *   调 ExecRestrPos 恢复到标记位置——恢复后第一次 ExecProcNode 将重放
 *   标记后的那一行。标记期间节点可以自由移动（甚至到 EOF），恢复即回溯。
 *
 * 支持节点：Index/IndexOnly（索引 AM 提供 ammarkpos）、CustomScan（标志
 * 位）、Material/Sort（tuplestore 回溯）、Result（透传子计划）。
 * 恢复的语义不保证节点结果槽内容：调用方拿到恢复前的结果槽应丢弃。
 *
 * 注意：mark/restore 只有 MergeJoin 内层需要；不支持时规划器会自动在
 * 上方插入 Material 节点兜底（见 ExecSupportsMarkRestore）。
 * ============================================================================
 */
void
ExecMarkPos(PlanState *node)
{
	switch (nodeTag(node))
	{
		case T_IndexScanState:
			ExecIndexMarkPos((IndexScanState *) node);
			break;

		case T_IndexOnlyScanState:
			ExecIndexOnlyMarkPos((IndexOnlyScanState *) node);
			break;

		case T_CustomScanState:
			ExecCustomMarkPos((CustomScanState *) node);
			break;

		case T_MaterialState:
			ExecMaterialMarkPos((MaterialState *) node);
			break;

		case T_SortState:
			ExecSortMarkPos((SortState *) node);
			break;

		case T_ResultState:
			ExecResultMarkPos((ResultState *) node);
			break;

		default:
			/* don't make hard error unless caller asks to restore... */
			elog(DEBUG2, "unrecognized node type: %d", (int) nodeTag(node));
			break;
	}
}

/*
 * ExecRestrPos
 *
 * restores the scan position previously saved with ExecMarkPos()
 *
 * NOTE: the semantics of this are that the first ExecProcNode following
 * the restore operation will yield the same tuple as the first one following
 * the mark operation.  It is unspecified what happens to the plan node's
 * result TupleTableSlot.  (In most cases the result slot is unchanged by
 * a restore, but the node may choose to clear it or to load it with the
 * restored-to tuple.)	Hence the caller should discard any previously
 * returned TupleTableSlot after doing a restore.
 */
void
ExecRestrPos(PlanState *node)
{
	switch (nodeTag(node))
	{
		case T_IndexScanState:
			ExecIndexRestrPos((IndexScanState *) node);
			break;

		case T_IndexOnlyScanState:
			ExecIndexOnlyRestrPos((IndexOnlyScanState *) node);
			break;

		case T_CustomScanState:
			ExecCustomRestrPos((CustomScanState *) node);
			break;

		case T_MaterialState:
			ExecMaterialRestrPos((MaterialState *) node);
			break;

		case T_SortState:
			ExecSortRestrPos((SortState *) node);
			break;

		case T_ResultState:
			ExecResultRestrPos((ResultState *) node);
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			break;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecSupportsMarkRestore —— 规划期问询：该 Path 支持 mark/restore 吗
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   规划器在构造 MergeJoin 时用来判断"是否需要给内层垫 Material"。
 * 关键点：输入是 Path（规划期对象）而非 Plan，看的是 pathtype。
 * 判断规则：
 *   - Index/IndexOnly：取决于索引 AM 的 amcanmarkpos（btree 支持，
 *     hash 等不支持）；
 *   - Material/Sort：支持（tuplestore 天然可回溯）；
 *   - CustomScan：看 CUSTOMPATH_SUPPORT_MARK_RESTORE 标志；
 *   - Result：有子计划且子计划支持才支持（三类无子计划的 Result 变体
 *     均不支持）；
 *   - Append/MergeAppend：仅当最终会折叠成单子计划时按子计划回答。
 * ============================================================================
 */
bool
ExecSupportsMarkRestore(Path *pathnode)
{
	/*
	 * For consistency with the routines above, we do not examine the nodeTag
	 * but rather the pathtype, which is the Plan node type the Path would
	 * produce.
	 */
	switch (pathnode->pathtype)
	{
		case T_IndexScan:
		case T_IndexOnlyScan:

			/*
			 * Not all index types support mark/restore.
			 */
			return castNode(IndexPath, pathnode)->indexinfo->amcanmarkpos;

		case T_Material:
		case T_Sort:
			return true;

		case T_CustomScan:
			if (castNode(CustomPath, pathnode)->flags & CUSTOMPATH_SUPPORT_MARK_RESTORE)
				return true;
			return false;

		case T_Result:

			/*
			 * Result supports mark/restore iff it has a child plan that does.
			 *
			 * We have to be careful here because there is more than one Path
			 * type that can produce a Result plan node.
			 */
			if (IsA(pathnode, ProjectionPath))
				return ExecSupportsMarkRestore(((ProjectionPath *) pathnode)->subpath);
			else if (IsA(pathnode, MinMaxAggPath))
				return false;	/* childless Result */
			else if (IsA(pathnode, GroupResultPath))
				return false;	/* childless Result */
			else
			{
				/* Simple RTE_RESULT base relation */
				Assert(IsA(pathnode, Path));
				return false;	/* childless Result */
			}

		case T_Append:
			{
				AppendPath *appendPath = castNode(AppendPath, pathnode);

				/*
				 * If there's exactly one child, then there will be no Append
				 * in the final plan, so we can handle mark/restore if the
				 * child plan node can.
				 */
				if (list_length(appendPath->subpaths) == 1)
					return ExecSupportsMarkRestore((Path *) linitial(appendPath->subpaths));
				/* Otherwise, Append can't handle it */
				return false;
			}

		case T_MergeAppend:
			{
				MergeAppendPath *mapath = castNode(MergeAppendPath, pathnode);

				/*
				 * Like the Append case above, single-subpath MergeAppends
				 * won't be in the final plan, so just return the child's
				 * mark/restore ability.
				 */
				if (list_length(mapath->subpaths) == 1)
					return ExecSupportsMarkRestore((Path *) linitial(mapath->subpaths));
				/* Otherwise, MergeAppend can't handle it */
				return false;
			}

		default:
			break;
	}

	return false;
}

/*
 * ============================================================================
 * 【中文注释】ExecSupportsBackwardScan —— 规划期问询：支持反向扫描吗
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判定给定计划子树能否从后往前扫（DECLARE CURSOR ... SCROLL / 游标
 *   倒退需要）。传递整个计划树——因为许多节点把反向能力"借用"给子计划。
 *
 * 规则速览：
 *   - parallel_aware 一律不支持（各 worker 各扫一段，无回溯记账）；
 *   - 透传类：Result/SubqueryScan 看子计划，LockRows/Limit 看外子计划；
 *   - Append：全部子计划支持且无异步计划（异步交错打乱了顺序）才行；
 *   - Index/IndexOnly：看索引 AM 的 amcanbackward（见 IndexSupports
 *     BackwardScan，查 pg_class+AM API 表）；
 *   - 天然支持：SeqScan/Tid(范围)/Function/Values/Cte/Material/Sort
 *     （都不求值 tlist，重扫即回溯）；
 *   - 不支持：SampleScan（TABLESAMPLE 简化）、Gather、IncrementalSort
 *     （只缓冲当前组）、CustomScan（除非标志位）及其他。
 * ============================================================================
 */
bool
ExecSupportsBackwardScan(Plan *node)
{
	if (node == NULL)
		return false;

	/*
	 * Parallel-aware nodes return a subset of the tuples in each worker, and
	 * in general we can't expect to have enough bookkeeping state to know
	 * which ones we returned in this worker as opposed to some other worker.
	 */
	if (node->parallel_aware)
		return false;

	switch (nodeTag(node))
	{
		case T_Result:
			if (outerPlan(node) != NULL)
				return ExecSupportsBackwardScan(outerPlan(node));
			else
				return false;

		case T_Append:
			{
				ListCell   *l;

				/* With async, tuples may be interleaved, so can't back up. */
				if (((Append *) node)->nasyncplans > 0)
					return false;

				foreach(l, ((Append *) node)->appendplans)
				{
					if (!ExecSupportsBackwardScan((Plan *) lfirst(l)))
						return false;
				}
				/* need not check tlist because Append doesn't evaluate it */
				return true;
			}

		case T_SampleScan:
			/* Simplify life for tablesample methods by disallowing this */
			return false;

		case T_Gather:
			return false;

		case T_IndexScan:
			return IndexSupportsBackwardScan(((IndexScan *) node)->indexid);

		case T_IndexOnlyScan:
			return IndexSupportsBackwardScan(((IndexOnlyScan *) node)->indexid);

		case T_SubqueryScan:
			return ExecSupportsBackwardScan(((SubqueryScan *) node)->subplan);

		case T_CustomScan:
			if (((CustomScan *) node)->flags & CUSTOMPATH_SUPPORT_BACKWARD_SCAN)
				return true;
			return false;

		case T_SeqScan:
		case T_TidScan:
		case T_TidRangeScan:
		case T_FunctionScan:
		case T_ValuesScan:
		case T_CteScan:
		case T_Material:
		case T_Sort:
			/* these don't evaluate tlist */
			return true;

		case T_IncrementalSort:

			/*
			 * Unlike full sort, incremental sort keeps only a single group of
			 * tuples in memory, so it can't scan backwards.
			 */
			return false;

		case T_LockRows:
		case T_Limit:
			return ExecSupportsBackwardScan(outerPlan(node));

		default:
			return false;
	}
}

/*
 * ============================================================================
 * 【中文注释】IndexSupportsBackwardScan —— 索引 AM 是否支持反向扫描
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   经 pg_class（取 relam）→ GetIndexAmRoutineByAmId（取 AM API 结构）
 *   两步查询索引 AM 的 amcanbackward 能力位。
 * ============================================================================
 */
static bool
IndexSupportsBackwardScan(Oid indexid)
{
	bool		result;
	HeapTuple	ht_idxrel;
	Form_pg_class idxrelrec;
	const IndexAmRoutine *amroutine;

	/* Fetch the pg_class tuple of the index relation */
	ht_idxrel = SearchSysCache1(RELOID, ObjectIdGetDatum(indexid));
	if (!HeapTupleIsValid(ht_idxrel))
		elog(ERROR, "cache lookup failed for relation %u", indexid);
	idxrelrec = (Form_pg_class) GETSTRUCT(ht_idxrel);

	/* Fetch the index AM's API struct */
	amroutine = GetIndexAmRoutineByAmId(idxrelrec->relam, false);

	result = amroutine->amcanbackward;

	ReleaseSysCache(ht_idxrel);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecMaterializesOutput —— 该节点会物化输出吗
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判定节点类型是否把输出整存（典型是 tuplestore）：Material、Sort、
 *   FunctionScan、TableFuncScan、CteScan、NamedTuplestoreScan、
 *   WorkTableScan 是。这类计划"无参数变化的重扫"启动成本≈0、逐行成本
 *   极低——规划器据此评估重复扫描代价（嵌套循环内层重扫等）。
 * ============================================================================
 */
bool
ExecMaterializesOutput(NodeTag plantype)
{
	switch (plantype)
	{
		case T_Material:
		case T_FunctionScan:
		case T_TableFuncScan:
		case T_CteScan:
		case T_NamedTuplestoreScan:
		case T_WorkTableScan:
		case T_Sort:
			return true;

		default:
			break;
	}

	return false;
}
