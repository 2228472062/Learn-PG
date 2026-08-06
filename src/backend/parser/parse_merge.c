/*-------------------------------------------------------------------------
 *
 * parse_merge.c
 *	  handle merge-statement in parser
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/parser/parse_merge.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/sysattr.h"
#include "nodes/makefuncs.h"
#include "parser/analyze.h"
#include "parser/parse_clause.h"
#include "parser/parse_collate.h"
#include "parser/parse_cte.h"
#include "parser/parse_expr.h"
#include "parser/parse_merge.h"
#include "parser/parse_relation.h"
#include "parser/parse_target.h"
#include "parser/parsetree.h"
#include "utils/rel.h"

static void setNamespaceForMergeWhen(ParseState *pstate,
									 MergeWhenClause *mergeWhenClause,
									 Index targetRTI,
									 Index sourceRTI);
static void setNamespaceVisibilityForRTE(List *namespace, RangeTblEntry *rte,
										 bool rel_visible,
										 bool cols_visible);

/*
 * Make appropriate changes to the namespace visibility while transforming
 * individual action's quals and targetlist expressions. In particular, for
 * INSERT actions we must only see the source relation (since INSERT action is
 * invoked for NOT MATCHED [BY TARGET] tuples and hence there is no target
 * tuple to deal with). On the other hand, UPDATE and DELETE actions can see
 * both source and target relations, unless invoked for NOT MATCHED BY SOURCE.
 *
 * Also, since the internal join node can hide the source and target
 * relations, we must explicitly make the respective relation as visible so
 * that columns can be referenced unqualified from these relations.
 *
 * 【中文总述】根据 MERGE WHEN 子句的类型（MATCHED /
 * NOT MATCHED BY SOURCE / NOT MATCHED BY TARGET），设置命名空间中
 * 目标表和源表的可见性。MATCHED 动作可见两张表；
 * NOT MATCHED BY SOURCE 仅可见目标表；
 * NOT MATCHED BY TARGET 仅可见源表。
 * 【调用链】被 transformMergeStmt() 调用，
 * 在处理每个 WHEN 子句的动作之前设置正确的命名空间可见性。
 */
static void
setNamespaceForMergeWhen(ParseState *pstate, MergeWhenClause *mergeWhenClause,
						 Index targetRTI, Index sourceRTI)
{
	RangeTblEntry *targetRelRTE,
			   *sourceRelRTE;

	targetRelRTE = rt_fetch(targetRTI, pstate->p_rtable);
	sourceRelRTE = rt_fetch(sourceRTI, pstate->p_rtable);

	if (mergeWhenClause->matchKind == MERGE_WHEN_MATCHED)
	{
		Assert(mergeWhenClause->commandType == CMD_UPDATE ||
			   mergeWhenClause->commandType == CMD_DELETE ||
			   mergeWhenClause->commandType == CMD_NOTHING);

		/* MATCHED actions can see both target and source relations. */
		setNamespaceVisibilityForRTE(pstate->p_namespace,
									 targetRelRTE, true, true);
		setNamespaceVisibilityForRTE(pstate->p_namespace,
									 sourceRelRTE, true, true);
	}
	else if (mergeWhenClause->matchKind == MERGE_WHEN_NOT_MATCHED_BY_SOURCE)
	{
		/*
		 * NOT MATCHED BY SOURCE actions can see the target relation, but they
		 * can't see the source relation.
		 */
		Assert(mergeWhenClause->commandType == CMD_UPDATE ||
			   mergeWhenClause->commandType == CMD_DELETE ||
			   mergeWhenClause->commandType == CMD_NOTHING);
		setNamespaceVisibilityForRTE(pstate->p_namespace,
									 targetRelRTE, true, true);
		setNamespaceVisibilityForRTE(pstate->p_namespace,
									 sourceRelRTE, false, false);
	}
	else						/* MERGE_WHEN_NOT_MATCHED_BY_TARGET */
	{
		/*
		 * NOT MATCHED [BY TARGET] actions can't see target relation, but they
		 * can see source relation.
		 */
		Assert(mergeWhenClause->commandType == CMD_INSERT ||
			   mergeWhenClause->commandType == CMD_NOTHING);
		setNamespaceVisibilityForRTE(pstate->p_namespace,
									 targetRelRTE, false, false);
		setNamespaceVisibilityForRTE(pstate->p_namespace,
									 sourceRelRTE, true, true);
	}
}

/*
 * transformMergeStmt -
 *	  transforms a MERGE statement
 *
 * 【中文总述】将 MERGE 语句转换为 Query 节点：处理 WITH 子句、
 * 检查 WHEN 子句权限和可达性、设置目标表和源表、
 * 转换连接条件和动作列表。这是 MERGE 语句解析的核心入口。
 * 【调用链】由 raw_parser() → gram.y 中的 MergeStmt 规则调用；
 * 内部调用 transformWithClause、transformFromClause、
 * transformExpr、transformWhereClause、transformReturningClause 等子函数。
 */
Query *
transformMergeStmt(ParseState *pstate, MergeStmt *stmt)
{
	Query	   *qry = makeNode(Query);
	ListCell   *l;
	AclMode		targetPerms = ACL_NO_RIGHTS;
	bool		is_terminal[NUM_MERGE_MATCH_KINDS];
	Index		sourceRTI;
	List	   *mergeActionList;
	ParseNamespaceItem *nsitem;

	/* There can't be any outer WITH to worry about */
	Assert(pstate->p_ctenamespace == NIL);

	/* 【中文】初始化 Query 节点，设置命令类型为 CMD_MERGE */
	qry->commandType = CMD_MERGE;
	qry->hasRecursive = false;

	/* 【中文】处理 WITH 子句：不支持 RECURSIVE，转换 CTE 列表 */

	/* process the WITH clause independently of all else */
	if (stmt->withClause)
	{
		if (stmt->withClause->recursive)
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("WITH RECURSIVE is not supported for MERGE statement")));

		qry->cteList = transformWithClause(pstate, stmt->withClause);
		qry->hasModifyingCTE = pstate->p_hasModifyingCTE;
	}

/*
		 * Check WHEN clauses for permissions and sanity
		 *
		 * 【中文】初始化三种 WHEN 匹配类型的终止标志，
		 * 然后遍历所有 WHEN 子句，收集权限需求并检查
		 * 不可达的 WHEN 子句（如无条件 WHEN 之后的子句）。
		 */
	is_terminal[MERGE_WHEN_MATCHED] = false;
	is_terminal[MERGE_WHEN_NOT_MATCHED_BY_SOURCE] = false;
	is_terminal[MERGE_WHEN_NOT_MATCHED_BY_TARGET] = false;
	foreach(l, stmt->mergeWhenClauses)
	{
		MergeWhenClause *mergeWhenClause = (MergeWhenClause *) lfirst(l);

		/*
		 * Collect permissions to check, according to action types. We require
		 * SELECT privileges for DO NOTHING because it'd be irregular to have
		 * a target relation with zero privileges checked, in case DO NOTHING
		 * is the only action.  There's no damage from that: any meaningful
		 * MERGE command requires at least some access to the table anyway.
		 */
		switch (mergeWhenClause->commandType)
		{
			case CMD_INSERT:
				targetPerms |= ACL_INSERT;
				break;
			case CMD_UPDATE:
				targetPerms |= ACL_UPDATE;
				break;
			case CMD_DELETE:
				targetPerms |= ACL_DELETE;
				break;
			case CMD_NOTHING:
				targetPerms |= ACL_SELECT;
				break;
			default:
				elog(ERROR, "unknown action in MERGE WHEN clause");
		}

		/*
		 * Check for unreachable WHEN clauses
		 *
		 * 【中文】若当前 WHEN 类型已被标记为终止（无条件 WHEN），
		 * 则后续的同类型 WHEN 子句不可达，报错。
		 * 若 WHEN 条件为空，则标记该类型为终止。
		 */
		if (is_terminal[mergeWhenClause->matchKind])
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("unreachable WHEN clause specified after unconditional WHEN clause")));
		if (mergeWhenClause->condition == NULL)
			is_terminal[mergeWhenClause->matchKind] = true;
	}

	/*
	 * Set up the MERGE target table.  The target table is added to the
	 * namespace below and to joinlist in transform_MERGE_to_join, so don't do
	 * it here.
	 *
	 * Initially mergeTargetRelation is the same as resultRelation, so data is
	 * read from the table being updated.  However, that might be changed by
	 * the rewriter, if the target is a trigger-updatable view, to allow
	 * target data to be read from the expanded view query while updating the
	 * original view relation.
	 *
	 * 【中文】设置 MERGE 目标表：调用 setTargetTable 获取目标表的 RTE 索引，
	 * 并初始化 mergeTargetRelation（可能被重写器修改为视图展开后的查询）。
	 */
	qry->resultRelation = setTargetTable(pstate, stmt->relation,
										 stmt->relation->inh,
										 false, targetPerms);
	qry->mergeTargetRelation = qry->resultRelation;

	/* The target relation must be a table or a view */
	if (pstate->p_target_relation->rd_rel->relkind != RELKIND_RELATION &&
		pstate->p_target_relation->rd_rel->relkind != RELKIND_PARTITIONED_TABLE &&
		pstate->p_target_relation->rd_rel->relkind != RELKIND_VIEW)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot execute MERGE on relation \"%s\"",
						RelationGetRelationName(pstate->p_target_relation)),
				 errdetail_relkind_not_supported(pstate->p_target_relation->rd_rel->relkind)));

	/* Now transform the source relation to produce the source RTE. */
	transformFromClause(pstate,
						list_make1(stmt->sourceRelation));
	sourceRTI = list_length(pstate->p_rtable);
	nsitem = GetNSItemByRangeTablePosn(pstate, sourceRTI, 0);

	/*
	 * Check that the target table doesn't conflict with the source table.
	 * This would typically be a checkNameSpaceConflicts call, but we want a
	 * more specific error message.
	 *
	 * 【中文】检查目标表与源表是否同名（冲突），
	 * 若同名则报错，因为 MERGE 不允许目标和数据源是同一张表。
	 */
	if (strcmp(pstate->p_target_nsitem->p_names->aliasname,
			   nsitem->p_names->aliasname) == 0)
		ereport(ERROR,
				errcode(ERRCODE_DUPLICATE_ALIAS),
				errmsg("name \"%s\" specified more than once",
					   pstate->p_target_nsitem->p_names->aliasname),
				errdetail("The name is used both as MERGE target table and data source."));

	/*
	 * There's no need for a targetlist here; it'll be set up by
	 * preprocess_targetlist later.
	 */
	qry->targetList = NIL;
	qry->rtable = pstate->p_rtable;
	qry->rteperminfos = pstate->p_rteperminfos;

	/*
	 * Transform the join condition.  This includes references to the target
	 * side, so add that to the namespace.
	 *
	 * 【中文】将目标表加入命名空间，然后转换 MERGE 的连接条件
	 *（ON 子句），使用 EXPR_KIND_JOIN_ON 上下文。
	 */
	addNSItemToQuery(pstate, pstate->p_target_nsitem, false, true, true);
	qry->mergeJoinCondition = transformExpr(pstate, stmt->joinCondition,
											EXPR_KIND_JOIN_ON);

	/*
	 * Create the temporary query's jointree using the joinlist we built using
	 * just the source relation; the target relation is not included. The join
	 * will be constructed fully by transform_MERGE_to_join.
	 *
	 * 【中文】创建临时查询的 join tree（仅含源表），
	 * 完整的连接将在 transform_MERGE_to_join 中构建。
	 */
	qry->jointree = makeFromExpr(pstate->p_joinlist, NULL);

	/* Transform the RETURNING list, if any */
	transformReturningClause(pstate, qry, stmt->returningClause,
							 EXPR_KIND_MERGE_RETURNING);

	/*
	 * We now have a good query shape, so now look at the WHEN conditions and
	 * action targetlists.
	 *
	 * Overall, the MERGE Query's targetlist is NIL.
	 *
	 * Each individual action has its own targetlist that needs separate
	 * transformation. These transforms don't do anything to the overall
	 * targetlist, since that is only used for resjunk columns.
	 *
	 * We can reference any column in Target or Source, which is OK because
	 * both of those already have RTEs. There is nothing like the EXCLUDED
	 * pseudo-relation for INSERT ON CONFLICT.
	 *
	 * 【中文】遍历所有 WHEN 子句，为每个动作设置命名空间、
	 * 转换 WHEN 条件（qual）和目标列表（targetList）。
	 * INSERT 动作需要特殊处理 VALUES 列表，
	 * UPDATE 动作转换目标列赋值，
	 * DELETE 和 DO NOTHING 动作无需目标列表。
	 */
	mergeActionList = NIL;
	foreach(l, stmt->mergeWhenClauses)
	{
		MergeWhenClause *mergeWhenClause = lfirst_node(MergeWhenClause, l);
		MergeAction *action;

		action = makeNode(MergeAction);
		action->commandType = mergeWhenClause->commandType;
		action->matchKind = mergeWhenClause->matchKind;

		/*
		 * Set namespace for the specific action. This must be done before
		 * analyzing the WHEN quals and the action targetlist.
		 *
		 * 【中文】根据当前 WHEN 子句的类型设置命名空间可见性，
		 * 必须在分析 WHEN 条件和动作目标列表之前完成。
		 */
		setNamespaceForMergeWhen(pstate, mergeWhenClause,
								 qry->resultRelation,
								 sourceRTI);

		/*
		 * Transform the WHEN condition.
		 *
		 * Note that these quals are NOT added to the join quals; instead they
		 * are evaluated separately during execution to decide which of the
		 * WHEN MATCHED or WHEN NOT MATCHED actions to execute.
		 *
		 * 【中文】转换 WHEN 条件表达式，使用 EXPR_KIND_MERGE_WHEN
		 * 上下文。注意这些条件不会加入连接条件，
		 * 而是在执行阶段单独评估以决定执行哪个动作。
		 */
		action->qual = transformWhereClause(pstate, mergeWhenClause->condition,
											EXPR_KIND_MERGE_WHEN, "WHEN");

		/*
		 * Transform target lists for each INSERT and UPDATE action stmt
		 *
		 * 【中文】根据动作类型分别处理：
		 * INSERT - 处理 VALUES 列表或 DEFAULT VALUES，
		 *         构建目标列表并标记插入权限；
		 * UPDATE - 转换更新目标列表；
		 * DELETE - 无需目标列表；
		 * DO NOTHING - 目标列表为空。
		 */
		switch (action->commandType)
		{
			case CMD_INSERT:
				{
					List	   *exprList = NIL;
					ListCell   *lc;
					RTEPermissionInfo *perminfo;
					ListCell   *icols;
					ListCell   *attnos;
					List	   *icolumns;
					List	   *attrnos;

					icolumns = checkInsertTargets(pstate,
												  mergeWhenClause->targetList,
												  &attrnos);
					Assert(list_length(icolumns) == list_length(attrnos));

					action->override = mergeWhenClause->override;

					/*
					 * Handle INSERT much like in transformInsertStmt
					 *
					 * 【中文】INSERT 动作处理：
					 * 若为 DEFAULT VALUES 则目标列表为空（由规划器展开默认值）；
					 * 否则转换 VALUES 表达式列表并构建目标行。
					 */
					if (mergeWhenClause->values == NIL)
					{
						/*
						 * We have INSERT ... DEFAULT VALUES.  We can handle
						 * this case by emitting an empty targetlist --- all
						 * columns will be defaulted when the planner expands
						 * the targetlist.
						 */
						exprList = NIL;
					}
					else
					{
/*
					 * Process INSERT ... VALUES with a single VALUES
					 * sublist.  We treat this case separately for
					 * efficiency.  The sublist is just computed directly
					 * as the Query's targetlist, with no VALUES RTE.  So
					 * it works just like a SELECT without any FROM.
					 *
					 * 【中文】处理 INSERT ... VALUES (单值列表)：
					 * 直接作为查询目标列表计算，
					 * 不需要 VALUES RTE，类似无 FROM 的 SELECT。
					 */

/*
					 * Do basic expression transformation (same as a ROW()
					 * expr, but allow SetToDefault at top level)
					 *
					 * 【中文】对 VALUES 列表做基础表达式转换，
					 * 类似 ROW() 表达式，但允许顶层使用 SetToDefault。
					 */
						exprList = transformExpressionList(pstate,
														   mergeWhenClause->values,
														   EXPR_KIND_VALUES_SINGLE,
														   true);

						/* Prepare row for assignment to target table
					 *
					 * 【中文】将 VALUES 表达式转换为适合目标表赋值的行格式。
					 */
						exprList = transformInsertRow(pstate, exprList,
													  mergeWhenClause->targetList,
													  icolumns, attrnos,
													  false);
					}

					/*
					 * Generate action's target list using the computed list
					 * of expressions. Also, mark all the target columns as
					 * needing insert permissions.
					 *
					 * 【中文】用计算好的表达式列表生成动作的目标列表，
					 * 并标记所有目标列需要 INSERT 权限。
					 */
					perminfo = pstate->p_target_nsitem->p_perminfo;
					forthree(lc, exprList, icols, icolumns, attnos, attrnos)
					{
						Expr	   *expr = (Expr *) lfirst(lc);
						ResTarget  *col = lfirst_node(ResTarget, icols);
						AttrNumber	attr_num = (AttrNumber) lfirst_int(attnos);
						TargetEntry *tle;

						tle = makeTargetEntry(expr,
											  attr_num,
											  col->name,
											  false);
						action->targetList = lappend(action->targetList, tle);

						perminfo->insertedCols =
							bms_add_member(perminfo->insertedCols,
										   attr_num - FirstLowInvalidHeapAttributeNumber);
					}
				}
				break;
			case CMD_UPDATE:
				action->targetList =
					transformUpdateTargetList(pstate,
											  mergeWhenClause->targetList, NULL);
				break;
			case CMD_DELETE:
				break;

			case CMD_NOTHING:
				action->targetList = NIL;
				break;
			default:
				elog(ERROR, "unknown action in MERGE WHEN clause");
		}

		mergeActionList = lappend(mergeActionList, action);
	}

	qry->mergeActionList = mergeActionList;

	qry->hasTargetSRFs = false;
	qry->hasSubLinks = pstate->p_hasSubLinks;

	assign_query_collations(pstate, qry);

	return qry;
}

/*
 * 【中文总述】在命名空间列表中查找指定的 RTE，
 * 并设置其关系可见性（p_rel_visible）和列可见性
 * （p_cols_visible）标志。
 * 【调用链】被 setNamespaceForMergeWhen() 调用，
 * 用于控制 MERGE 各动作中源表和目标表的列可见范围。
 */
static void
setNamespaceVisibilityForRTE(List *namespace, RangeTblEntry *rte,
							 bool rel_visible,
							 bool cols_visible)
{
	ListCell   *lc;

	foreach(lc, namespace)
	{
		ParseNamespaceItem *nsitem = (ParseNamespaceItem *) lfirst(lc);

		if (nsitem->p_rte == rte)
		{
			nsitem->p_rel_visible = rel_visible;
			nsitem->p_cols_visible = cols_visible;
			break;
		}
	}
}
