/*-------------------------------------------------------------------------
 *
 * execScan.c
 *	  This code provides support for generalized relation scans. ExecScan
 *	  is passed a node and a pointer to a function to "do the right thing"
 *	  and return a tuple from the relation. ExecScan then does the tedious
 *	  stuff - checking the qualification and projecting the tuple
 *	  appropriately.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execScan.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * ============================================================================
 * 【中文注释】execScan.c —— 通用扫描框架（访问方法与通用逻辑解耦）
 * ----------------------------------------------------------------------------
 * 文件定位：
 *   几乎所有扫描节点（SeqScan/IndexScan/BitmapHeapScan/ForeignScan/
 *   CustomScan...）的"公共骨架"都收敛到本文件的 ExecScan：
 *   具体怎么取下一行由各节点传入的 accessMtd（访问方法回调）负责
 *   （比如 SeqNext 读一个堆页，IndexNext 走一次索引），而"取到行之后"
 *   的通用处理——EPQ 重检查、WHERE 条件过滤（qual）、目标列投影
 *   （projection）——全部由 ExecScan 统一完成。
 *
 * 流程（ExecScanExtended 内部）：
 *   循环调用 accessMtd 取行 → 若需 EPQ 则按 recheckMtd 重查该行 →
 *   对满足条件的行求 qual（不满足就换下一行）→ 需要时投影到结果槽
 *   → 返回。省去投影的前提是 tlist 与扫描行类型逐列一致
 *   （tlist_matches_tupdesc 判定，见 execUtils.c）。
 *
 * 配套函数：
 *   - ExecAssignScanProjectionInfo[WithVarno]：按需建立投影（类型匹配则
 *     不建，ps_ProjInfo 置 NULL 省一次投影）；
 *   - ExecScanReScan：重扫公共逻辑——清空扫描槽（让 execCurrent.c 等
 *     观察者知道"未定位在行上"）、并按 EPQ 状态重置 relsubs_done
 *     （保持 blocked 状态不丢失）。
 * ============================================================================
 */
#include "postgres.h"

#include "executor/executor.h"
#include "executor/execScan.h"
#include "miscadmin.h"

/*
 * ============================================================================
 * 【中文注释】ExecScan —— 扫描通用骨架入口（见文件头流程图）
 * ----------------------------------------------------------------------------
 * 参数：
 *   node：扫描节点状态（ScanState）；
 *   accessMtd：各扫描类型自己提供的"取下一物理行"回调；
 *   recheckMtd：重查回调——EPQ 时用它对任意一行重新评估"访问方法内部
 *   实现的条件"（如索引条件）。
 * 返回值：满足条件并投影后的结果槽（可能为 NULL/空，表示扫描结束）。
 *
 * 实现：从 node 取出 EPQ 状态、qual、投影信息，整体委托 ExecScanExtended
 * （在 execScan.h 内联实现）执行主循环。
 * ============================================================================
 */
TupleTableSlot *
ExecScan(ScanState *node,
		 ExecScanAccessMtd accessMtd,	/* function returning a tuple */
		 ExecScanRecheckMtd recheckMtd)
{
	EPQState   *epqstate;
	ExprState  *qual;
	ProjectionInfo *projInfo;

	epqstate = node->ps.state->es_epq_active;
	qual = node->ps.qual;
	projInfo = node->ps.ps_ProjInfo;

	return ExecScanExtended(node,
							accessMtd,
							recheckMtd,
							epqstate,
							qual,
							projInfo);
}

/*
 * ============================================================================
 * 【中文注释】ExecAssignScanProjectionInfo —— 为扫描节点按需建立投影
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   若目标列表与扫描行类型一致则免投影（ps_ProjInfo = NULL），否则建投影
 *   （ExecConditionalAssignProjectionInfo 内部用 tlist_matches_tupdesc
 *   判定）。"SELECT *"或上层连接节点生成的匹配 tlist 都走免投影快路径。
 * 前置条件：扫描槽描述符已设置。
 * 变体 ExecAssignScanProjectionInfoWithVarno：调用方显式指定 tlist 中
 * Var 应匹配的 varno（用于扫描槽行类型与 tlist 基表不完全对应的节点）。
 * ============================================================================
 */
void
ExecAssignScanProjectionInfo(ScanState *node)
{
	Scan	   *scan = (Scan *) node->ps.plan;
	TupleDesc	tupdesc = node->ss_ScanTupleSlot->tts_tupleDescriptor;

	ExecConditionalAssignProjectionInfo(&node->ps, tupdesc, scan->scanrelid);
}

/*
 * ExecAssignScanProjectionInfoWithVarno
 *		As above, but caller can specify varno expected in Vars in the tlist.
 */
void
ExecAssignScanProjectionInfoWithVarno(ScanState *node, int varno)
{
	TupleDesc	tupdesc = node->ss_ScanTupleSlot->tts_tupleDescriptor;

	ExecConditionalAssignProjectionInfo(&node->ps, tupdesc, varno);
}

/*
 * ============================================================================
 * 【中文注释】ExecScanReScan —— 扫描公共重扫逻辑
 * ----------------------------------------------------------------------------
 * 函数作用（凡用 ExecScan 的节点，其 ExecReScan 都必须调用本函数）：
 *   1. 清空扫描槽——execCurrent.c 等"观察者"据此判断该节点当前不在任何
 *      行上；
 *   2. EPQ 联动——处于 EPQ 重查时，把本节点负责的基表"已重查完成"标志
 *      （relsubs_done）重置为"被阻塞"标志（relsubs_blocked）：若本表
 *      结果被阻塞说明它还没找到可重查的候选行，重扫后仍需重试。
 *      scanrelid==0 的场景是 FDW/CustomScan 把 join 整体替换成扫描
 *      （fs_base_relids / custom_relids 含多个基表），全部一并重置。
 * ============================================================================
 */
void
ExecScanReScan(ScanState *node)
{
	EState	   *estate = node->ps.state;

	/*
	 * We must clear the scan tuple so that observers (e.g., execCurrent.c)
	 * can tell that this plan node is not positioned on a tuple.
	 */
	ExecClearTuple(node->ss_ScanTupleSlot);

	/*
	 * Rescan EvalPlanQual tuple(s) if we're inside an EvalPlanQual recheck.
	 * But don't lose the "blocked" status of blocked target relations.
	 */
	if (estate->es_epq_active != NULL)
	{
		EPQState   *epqstate = estate->es_epq_active;
		Index		scanrelid = ((Scan *) node->ps.plan)->scanrelid;

		if (scanrelid > 0)
			epqstate->relsubs_done[scanrelid - 1] =
				epqstate->relsubs_blocked[scanrelid - 1];
		else
		{
			Bitmapset  *relids;
			int			rtindex = -1;

			/*
			 * If an FDW or custom scan provider has replaced the join with a
			 * scan, there are multiple RTIs; reset the relsubs_done flag for
			 * all of them.
			 */
			if (IsA(node->ps.plan, ForeignScan))
				relids = ((ForeignScan *) node->ps.plan)->fs_base_relids;
			else if (IsA(node->ps.plan, CustomScan))
				relids = ((CustomScan *) node->ps.plan)->custom_relids;
			else
				elog(ERROR, "unexpected scan node: %d",
					 (int) nodeTag(node->ps.plan));

			while ((rtindex = bms_next_member(relids, rtindex)) >= 0)
			{
				Assert(rtindex > 0);
				epqstate->relsubs_done[rtindex - 1] =
					epqstate->relsubs_blocked[rtindex - 1];
			}
		}
	}
}
