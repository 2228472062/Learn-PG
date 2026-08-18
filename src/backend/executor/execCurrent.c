/*-------------------------------------------------------------------------
 *
 * execCurrent.c
 *	  executor support for WHERE CURRENT OF cursor
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *	src/backend/executor/execCurrent.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * ============================================================================
 * 【中文注释】execCurrent.c —— WHERE CURRENT OF 游标定位
 * ----------------------------------------------------------------------------
 * 业务场景：
 *   UPDATE/DELETE ... WHERE CURRENT OF cursor：不指定行条件，而是"改/删
 *   游标当前正指着的那一行"。执行器需要回答一个问题：给定游标名和表 OID，
 *   该表当前被游标扫到的行是哪个（返回其 TID）。
 *
 * 两条实现策略（execCurrentOf）：
 *   1. 游标带 FOR UPDATE/SHARE（有 es_rowmarks）：
 *      ExecRowMark 里已经记录了当前行的 curCtid（加锁时就拿到了），直接
 *      取出来即可。要求游标对该表恰好有一个 FOR UPDATE/SHARE 引用。
 *   2. 普通（不可更新/不敏感）游标：
 *      沿游标计划树找"扫这个表的扫描节点"（search_plan_tree），从其扫描
 *      槽/索引扫描描述里取出当前 TID。要求计划是"简单可更新"形态
 *      （扫描没有被聚合/MergeAppend 等遮挡），否则报错。
 *
 * 返回值语义：true=找到 TID；false=游标合法但当前不在该表的行上
 * （继承场景：当前行来自兄弟子表，本表无事可做）；其余情况报错。
 *
 * 配套：
 *   - fetch_cursor_param_value：CURRENT OF 后跟参数时取 REFCURSOR 参数值；
 *   - search_plan_tree：递归搜计划树找候选扫描，多个候选必须拒绝
 *     （无法确定哪个贡献了当前输出行），并汇总 chgParam 指示的
 *     待重扫（pending_rescan）状态。
 * ============================================================================
 */
#include "postgres.h"

#include "access/genam.h"
#include "access/relscan.h"
#include "access/sysattr.h"
#include "catalog/pg_type.h"
#include "executor/executor.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/portal.h"
#include "utils/rel.h"


static char *fetch_cursor_param_value(ExprContext *econtext, int paramId);
static ScanState *search_plan_tree(PlanState *node, Oid table_oid,
								   bool *pending_rescan);


/*
 * ============================================================================
 * 【中文注释】execCurrentOf —— CURRENT OF 表达式求值（主入口）
 * ----------------------------------------------------------------------------
 * 参数：
 *   cexpr：CURRENT OF 表达式（含游标名或参数号）；
 *   econtext：求值上下文（取参数用）；
 *   table_oid：目标表 OID；
 *   current_tid：输出参数，填当前行 TID。
 *
 * 流程：
 *   1. 解析游标名（可能藏在参数里）→ 查 Portal → 校验是单 SELECT 且
 *      非 held 游标；
 *   2. 按是否有行锁（es_rowmarks）分两条路取 TID（见文件头）；
 *   3. 游标未定位在行上（atStart/atEnd）按 SQL 规范报错；
 *   4. 返回 true/false。
 *
 * 错误消息统一带上游标名与表名，方便用户定位。
 * ============================================================================
 */
bool
execCurrentOf(CurrentOfExpr *cexpr,
			  ExprContext *econtext,
			  Oid table_oid,
			  ItemPointer current_tid)
{
	char	   *cursor_name;
	char	   *table_name;
	Portal		portal;
	QueryDesc  *queryDesc;

	/* Get the cursor name --- may have to look up a parameter reference */
	if (cexpr->cursor_name)
		cursor_name = cexpr->cursor_name;
	else
		cursor_name = fetch_cursor_param_value(econtext, cexpr->cursor_param);

	/* Fetch table name for possible use in error messages */
	table_name = get_rel_name(table_oid);
	if (table_name == NULL)
		elog(ERROR, "cache lookup failed for relation %u", table_oid);

	/* Find the cursor's portal */
	portal = GetPortalByName(cursor_name);
	if (!PortalIsValid(portal))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_CURSOR),
				 errmsg("cursor \"%s\" does not exist", cursor_name)));

	/*
	 * We have to watch out for non-SELECT queries as well as held cursors,
	 * both of which may have null queryDesc.
	 */
	if (portal->strategy != PORTAL_ONE_SELECT)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_CURSOR_STATE),
				 errmsg("cursor \"%s\" is not a SELECT query",
						cursor_name)));
	queryDesc = portal->queryDesc;
	if (queryDesc == NULL || queryDesc->estate == NULL)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_CURSOR_STATE),
				 errmsg("cursor \"%s\" is held from a previous transaction",
						cursor_name)));

	/*
	 * We have two different strategies depending on whether the cursor uses
	 * FOR UPDATE/SHARE or not.  The reason for supporting both is that the
	 * FOR UPDATE code is able to identify a target table in many cases where
	 * the other code can't, while the non-FOR-UPDATE case allows use of WHERE
	 * CURRENT OF with an insensitive cursor.
	 */
	if (queryDesc->estate->es_rowmarks)
	{
		ExecRowMark *erm;

		/*
		 * Here, the query must have exactly one FOR UPDATE/SHARE reference to
		 * the target table, and we dig the ctid info out of that.
		 */
		erm = NULL;
		for (int i = 0; i < queryDesc->estate->es_range_table_size; i++)
		{
			ExecRowMark *thiserm = queryDesc->estate->es_rowmarks[i];

			if (thiserm == NULL ||
				!RowMarkRequiresRowShareLock(thiserm->markType))
				continue;		/* ignore non-FOR UPDATE/SHARE items */

			if (thiserm->relid == table_oid)
			{
				if (erm)
					ereport(ERROR,
							(errcode(ERRCODE_INVALID_CURSOR_STATE),
							 errmsg("cursor \"%s\" has multiple FOR UPDATE/SHARE references to table \"%s\"",
									cursor_name, table_name)));
				erm = thiserm;
			}
		}

		if (erm == NULL)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_CURSOR_STATE),
					 errmsg("cursor \"%s\" does not have a FOR UPDATE/SHARE reference to table \"%s\"",
							cursor_name, table_name)));

		/*
		 * The cursor must have a current result row: per the SQL spec, it's
		 * an error if not.
		 */
		if (portal->atStart || portal->atEnd)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_CURSOR_STATE),
					 errmsg("cursor \"%s\" is not positioned on a row",
							cursor_name)));

		/* Return the currently scanned TID, if there is one */
		if (ItemPointerIsValid(&(erm->curCtid)))
		{
			*current_tid = erm->curCtid;
			return true;
		}

		/*
		 * This table didn't produce the cursor's current row; some other
		 * inheritance child of the same parent must have.  Signal caller to
		 * do nothing on this table.
		 */
		return false;
	}
	else
	{
		/*
		 * Without FOR UPDATE, we dig through the cursor's plan to find the
		 * scan node.  Fail if it's not there or buried underneath
		 * aggregation.
		 */
		ScanState  *scanstate;
		bool		pending_rescan = false;

		scanstate = search_plan_tree(queryDesc->planstate, table_oid,
									 &pending_rescan);
		if (!scanstate)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_CURSOR_STATE),
					 errmsg("cursor \"%s\" is not a simply updatable scan of table \"%s\"",
							cursor_name, table_name)));

		/*
		 * The cursor must have a current result row: per the SQL spec, it's
		 * an error if not.  We test this at the top level, rather than at the
		 * scan node level, because in inheritance cases any one table scan
		 * could easily not be on a row. We want to return false, not raise
		 * error, if the passed-in table OID is for one of the inactive scans.
		 */
		if (portal->atStart || portal->atEnd)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_CURSOR_STATE),
					 errmsg("cursor \"%s\" is not positioned on a row",
							cursor_name)));

		/*
		 * Now OK to return false if we found an inactive scan.  It is
		 * inactive either if it's not positioned on a row, or there's a
		 * rescan pending for it.
		 */
		if (TupIsNull(scanstate->ss_ScanTupleSlot) || pending_rescan)
			return false;

		/*
		 * Extract TID of the scan's current row.  The mechanism for this is
		 * in principle scan-type-dependent, but for most scan types, we can
		 * just dig the TID out of the physical scan tuple.
		 */
		if (IsA(scanstate, IndexOnlyScanState))
		{
			/*
			 * For IndexOnlyScan, the tuple stored in ss_ScanTupleSlot may be
			 * a virtual tuple that does not have the ctid column, so we have
			 * to get the TID from xs_heaptid.
			 */
			IndexScanDesc scan = ((IndexOnlyScanState *) scanstate)->ioss_ScanDesc;

			*current_tid = scan->xs_heaptid;
		}
		else
		{
			/*
			 * Default case: try to fetch TID from the scan node's current
			 * tuple.  As an extra cross-check, verify tableoid in the current
			 * tuple.  If the scan hasn't provided a physical tuple, we have
			 * to fail.
			 */
			Datum		ldatum;
			bool		lisnull;
			ItemPointer tuple_tid;

#ifdef USE_ASSERT_CHECKING
			ldatum = slot_getsysattr(scanstate->ss_ScanTupleSlot,
									 TableOidAttributeNumber,
									 &lisnull);
			if (lisnull)
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_CURSOR_STATE),
						 errmsg("cursor \"%s\" is not a simply updatable scan of table \"%s\"",
								cursor_name, table_name)));
			Assert(DatumGetObjectId(ldatum) == table_oid);
#endif

			ldatum = slot_getsysattr(scanstate->ss_ScanTupleSlot,
									 SelfItemPointerAttributeNumber,
									 &lisnull);
			if (lisnull)
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_CURSOR_STATE),
						 errmsg("cursor \"%s\" is not a simply updatable scan of table \"%s\"",
								cursor_name, table_name)));
			tuple_tid = (ItemPointer) DatumGetPointer(ldatum);

			*current_tid = *tuple_tid;
		}

		Assert(ItemPointerIsValid(current_tid));

		return true;
	}
}

/*
 * ============================================================================
 * 【中文注释】fetch_cursor_param_value —— 取 REFCURSOR 类型参数值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   CURRENT OF 游标名是 PREPARE 参数时，从 ParamListInfo 取字符串值并
 *   校验参数类型确实是 refcursor（预防钩子返回意外内容）。refcursor 的
 *   I/O 复用 text 的，直接 TextDatumGetCString 得到游标名。
 * ============================================================================
 */
static char *
fetch_cursor_param_value(ExprContext *econtext, int paramId)
{
	ParamListInfo paramInfo = econtext->ecxt_param_list_info;

	if (paramInfo &&
		paramId > 0 && paramId <= paramInfo->numParams)
	{
		ParamExternData *prm;
		ParamExternData prmdata;

		/* give hook a chance in case parameter is dynamic */
		if (paramInfo->paramFetch != NULL)
			prm = paramInfo->paramFetch(paramInfo, paramId, false, &prmdata);
		else
			prm = &paramInfo->params[paramId - 1];

		if (OidIsValid(prm->ptype) && !prm->isnull)
		{
			/* safety check in case hook did something unexpected */
			if (prm->ptype != REFCURSOROID)
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("type of parameter %d (%s) does not match that when preparing the plan (%s)",
								paramId,
								format_type_be(prm->ptype),
								format_type_be(REFCURSOROID))));

			/* We know that refcursor uses text's I/O routines */
			return TextDatumGetCString(prm->value);
		}
	}

	ereport(ERROR,
			(errcode(ERRCODE_UNDEFINED_OBJECT),
			 errmsg("no value found for parameter %d", paramId)));
	return NULL;
}

/*
 * ============================================================================
 * 【中文注释】search_plan_tree —— 计划树中定位目标表的扫描节点
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   递归下钻找"扫描 table_oid 的扫描节点"。目标不只是"找到一个"，而是
 *   "找到且唯一"——必须能确定是它贡献了计划树当前的输出行，因此多个
 *   候选一律返回 NULL（拒绝）。
 *
 * 可穿透的节点：关系扫描（直接比对 ss_currentRelation）、Append（只当前
 * 激活的那个输入才可能定位在行上，其余在 EOF 或未启动；注意 MergeAppend
 * 不可穿透——所有输入都活跃）、Result/Limit（始终透传输入当前行）、
 * SubqueryScan（子计划在 subplan 字段）。ForeignScan/CustomScan 不向下
 * 钻（无法知道输出行与子计划的对应关系）。
 *
 * 附带输出 pending_rescan：候选节点及其祖先任一有 chgParam（参数变了、
 * 即将重扫）时置 true——即使节点看起来定位在行上也不能算数。
 * ============================================================================
 */
static ScanState *
search_plan_tree(PlanState *node, Oid table_oid,
				 bool *pending_rescan)
{
	ScanState  *result = NULL;

	if (node == NULL)
		return NULL;
	switch (nodeTag(node))
	{
			/*
			 * Relation scan nodes can all be treated alike: check to see if
			 * they are scanning the specified table.
			 *
			 * ForeignScan and CustomScan might not have a currentRelation, in
			 * which case we just ignore them.  (We dare not descend to any
			 * child plan nodes they might have, since we do not know the
			 * relationship of such a node's current output tuple to the
			 * children's current outputs.)
			 */
		case T_SeqScanState:
		case T_SampleScanState:
		case T_IndexScanState:
		case T_IndexOnlyScanState:
		case T_BitmapHeapScanState:
		case T_TidScanState:
		case T_TidRangeScanState:
		case T_ForeignScanState:
		case T_CustomScanState:
			{
				ScanState  *sstate = (ScanState *) node;

				if (sstate->ss_currentRelation &&
					RelationGetRelid(sstate->ss_currentRelation) == table_oid)
					result = sstate;
				break;
			}

			/*
			 * For Append, we can check each input node.  It is safe to
			 * descend to the inputs because only the input that resulted in
			 * the Append's current output node could be positioned on a tuple
			 * at all; the other inputs are either at EOF or not yet started.
			 * Hence, if the desired table is scanned by some
			 * currently-inactive input node, we will find that node but then
			 * our caller will realize that it didn't emit the tuple of
			 * interest.
			 *
			 * We do need to watch out for multiple matches (possible if
			 * Append was from UNION ALL rather than an inheritance tree).
			 *
			 * Note: we can NOT descend through MergeAppend similarly, since
			 * its inputs are likely all active, and we don't know which one
			 * returned the current output tuple.  (Perhaps that could be
			 * fixed if we were to let this code know more about MergeAppend's
			 * internal state, but it does not seem worth the trouble.  Users
			 * should not expect plans for ORDER BY queries to be considered
			 * simply-updatable, since they won't be if the sorting is
			 * implemented by a Sort node.)
			 */
		case T_AppendState:
			{
				AppendState *astate = (AppendState *) node;
				int			i;

				for (i = 0; i < astate->as_nplans; i++)
				{
					ScanState  *elem = search_plan_tree(astate->appendplans[i],
														table_oid,
														pending_rescan);

					if (!elem)
						continue;
					if (result)
						return NULL;	/* multiple matches */
					result = elem;
				}
				break;
			}

			/*
			 * Result and Limit can be descended through (these are safe
			 * because they always return their input's current row)
			 */
		case T_ResultState:
		case T_LimitState:
			result = search_plan_tree(outerPlanState(node),
									  table_oid,
									  pending_rescan);
			break;

			/*
			 * SubqueryScan too, but it keeps the child in a different place
			 */
		case T_SubqueryScanState:
			result = search_plan_tree(((SubqueryScanState *) node)->subplan,
									  table_oid,
									  pending_rescan);
			break;

		default:
			/* Otherwise, assume we can't descend through it */
			break;
	}

	/*
	 * If we found a candidate at or below this node, then this node's
	 * chgParam indicates a pending rescan that will affect the candidate.
	 */
	if (result && node->chgParam != NULL)
		*pending_rescan = true;

	return result;
}
