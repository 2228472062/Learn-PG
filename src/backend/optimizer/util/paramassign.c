/*-------------------------------------------------------------------------
 *
 * paramassign.c
 *		Functions for assigning PARAM_EXEC slots during planning.
 *
 * This module is responsible for managing three planner data structures:
 *
 * root->glob->paramExecTypes: records actual assignments of PARAM_EXEC slots.
 * The i'th list element holds the data type OID of the i'th parameter slot.
 * (Elements can be InvalidOid if they represent slots that are needed for
 * chgParam signaling, but will never hold a value at runtime.)  This list is
 * global to the whole plan since the executor has only one PARAM_EXEC array.
 * Assignments are permanent for the plan: we never remove entries once added.
 *
 * root->plan_params: a list of PlannerParamItem nodes, recording Vars and
 * PlaceHolderVars that the root's query level needs to supply to lower-level
 * subqueries, along with the PARAM_EXEC number to use for each such value.
 * Elements are added to this list while planning a subquery, and the list
 * is reset to empty after completion of each subquery.
 *
 * root->curOuterParams: a list of NestLoopParam nodes, recording Vars and
 * PlaceHolderVars that some outer level of nestloop needs to pass down to
 * a lower-level plan node in its righthand side.  Elements are added to this
 * list as createplan.c creates lower Plan nodes that need such Params, and
 * are removed when it creates a NestLoop Plan node that will supply those
 * values.
 *
 * The latter two data structures are used to prevent creating multiple
 * PARAM_EXEC slots (each requiring work to fill) when the same upper
 * SubPlan or NestLoop supplies a value that is referenced in more than
 * one place in its child plan nodes.  However, when the same Var has to
 * be supplied to different subplan trees by different SubPlan or NestLoop
 * parent nodes, we don't recognize any commonality; a fresh plan_params or
 * curOuterParams entry will be made (since the old one has been removed
 * when we finished processing the earlier SubPlan or NestLoop) and a fresh
 * PARAM_EXEC number will be assigned.  At one time we tried to avoid
 * allocating duplicate PARAM_EXEC numbers in such cases, but it's harder
 * than it seems to avoid bugs due to overlapping Param lifetimes, so we
 * don't risk that anymore.  Minimizing the number of PARAM_EXEC slots
 * doesn't really save much executor work anyway.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件在规划期为 PARAM_EXEC 槽位分配编号,是"参数化执行"的幕后功臣。
 * 计划树执行时,上层节点通过 PARAM_EXEC 向低层节点传值:例如嵌套循环
 * (NestLoop)把外层列值传给内层扫描、SubPlan 把子查询结果传给外层引用。
 * 本模块的核心职责就是在规划期间把这些"跨层取值"映射成全局唯一的
 * PARAM_EXEC 编号,并登记它们的数据类型。
 *
 * 【核心数据结构】
 * - root->glob->paramExecTypes:全局 PARAM_EXEC 槽位表(第 i 个元素是第 i
 *   个槽的类型 OID;InvalidOid 表示仅供 chgParam 信号、运行时不携带值)。
 *   因执行器只有一个 PARAM_EXEC 数组,故整个计划共享该表;已分配的槽
 *   永不回收;
 * - root->plan_params:当前查询层需要向上层子查询"索取"的 Var/PHV/Aggref
 *   等表达式及其 PARAM_EXEC 编号(规划子查询期间填充,子查询结束后清空);
 * - root->curOuterParams:NestLoopParam 列表,记录外层 nestloop 需要向内层
 *   传递的 Var/PHV。createplan.c 在创建内层计划节点时加入、在创建
 *   NestLoop 节点时取出。
 *
 * 【主要函数关系】
 * 向子查询取值的两类:replace_outer_var / replace_outer_placeholdervar
 * (走 assign_param_for_var / assign_param_for_placeholdervar 去重),
 * replace_outer_agg / replace_outer_grouping / replace_outer_merge_support /
 * replace_outer_returning(每次新建槽,不去重);nestloop 传值的两类:
 * replace_nestloop_param_var / replace_nestloop_param_placeholdervar,
 * 配套 process_subquery_nestloop_params 与 identify_current_nestloop_params;
 * generate_new_exec_param 分配普通新槽,assign_special_exec_param 分配
 * 仅供信号使用(类型为 InvalidOid)的槽。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/paramassign.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "optimizer/paramassign.h"
#include "optimizer/placeholder.h"
#include "rewrite/rewriteManip.h"


/*
 * Select a PARAM_EXEC number to identify the given Var as a parameter for
 * the current subquery.  (It might already have one.)
 * Record the need for the Var in the proper upper-level root->plan_params.
 */
/*
 * assign_param_for_var - (中文)为当前子查询中的 Var 选择(或复用)一个
 * PARAM_EXEC 编号
 *
 * 【作用】把 var 视为"来自上层查询的引用",在它所属的那个上层查询层的
 * root->plan_params 里查找已登记的同名 Var:找到则复用其 paramId,否则
 * 复制一份(置 varlevelsup = 0)登记为新项并分配新槽位。
 *
 * 【设计思想】复用判定的关键是与 _equalVar 保持一致(但忽略 varlevelsup,
 * 因为上拉后同一 Var 的所有引用 level 一致):比较 varno、varattno、
 * vartype、vartypmod、varcollid、varreturningtype 与 varnullingrels
 * (varnosyn/vartypnosyn/location 同 _equalVar 一样被忽略)。复用机制保证
 * 同一个上层 Var 的多处引用共用同一 PARAM_EXEC 槽,避免重复填值。
 *
 * 【参数】
 *   root —— 当前查询层上下文;
 *   var  —— 待参数化的 Var(其 varlevelsup > 0)。
 * 【返回值】该 Var 对应的 PARAM_EXEC 编号。
 */
static int
assign_param_for_var(PlannerInfo *root, Var *var)
{
	ListCell   *ppl;
	PlannerParamItem *pitem;
	Index		levelsup;

	/* Find the query level the Var belongs to */
	for (levelsup = var->varlevelsup; levelsup > 0; levelsup--)
		root = root->parent_root;

	/* If there's already a matching PlannerParamItem there, just use it */
	foreach(ppl, root->plan_params)
	{
		pitem = (PlannerParamItem *) lfirst(ppl);
		if (IsA(pitem->item, Var))
		{
			Var		   *pvar = (Var *) pitem->item;

			/*
			 * This comparison must match _equalVar(), except for ignoring
			 * varlevelsup.  Note that _equalVar() ignores varnosyn,
			 * varattnosyn, and location, so this does too.
			 */
			if (pvar->varno == var->varno &&
				pvar->varattno == var->varattno &&
				pvar->vartype == var->vartype &&
				pvar->vartypmod == var->vartypmod &&
				pvar->varcollid == var->varcollid &&
				pvar->varreturningtype == var->varreturningtype &&
				bms_equal(pvar->varnullingrels, var->varnullingrels))
				return pitem->paramId;
		}
	}

	/* Nope, so make a new one */
	var = copyObject(var);
	var->varlevelsup = 0;

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) var;
	pitem->paramId = list_length(root->glob->paramExecTypes);
	root->glob->paramExecTypes = lappend_oid(root->glob->paramExecTypes,
											 var->vartype);

	root->plan_params = lappend(root->plan_params, pitem);

	return pitem->paramId;
}

/*
 * Generate a Param node to replace the given Var,
 * which is expected to have varlevelsup > 0 (ie, it is not local).
 * Record the need for the Var in the proper upper-level root->plan_params.
 */
/*
 * replace_outer_var - (中文)生成替换外层 Var 的 PARAM_EXEC Param 节点
 *
 * 【作用】在规划某子查询时,把对上层查询 Var 的引用(要求 varlevelsup
 * 在 1..query_level-1 之间)替换为 Param(PARAM_EXEC),并在上层登记该
 * Var 的提供需求。由子计划/子查询规划代码调用。
 *
 * 【设计思想】先通过 assign_param_for_var 拿到/分配编号,再构造一个
 * 类型信息与 Var 一致的 Param 节点(类型、typmod、collation、location)。
 *
 * 【参数】
 *   root —— 当前(子)查询层上下文;
 *   var  —— 来自上层查询的 Var 引用。
 * 【返回值】替换用的 Param 节点(PARAM_EXEC)。
 */
Param *
replace_outer_var(PlannerInfo *root, Var *var)
{
	Param	   *retval;
	int			i;

	Assert(var->varlevelsup > 0 && var->varlevelsup < root->query_level);

	/* Find the Var in the appropriate plan_params, or add it if not present */
	i = assign_param_for_var(root, var);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = i;
	retval->paramtype = var->vartype;
	retval->paramtypmod = var->vartypmod;
	retval->paramcollid = var->varcollid;
	retval->location = var->location;

	return retval;
}

/*
 * Select a PARAM_EXEC number to identify the given PlaceHolderVar as a
 * parameter for the current subquery.  (It might already have one.)
 * Record the need for the PHV in the proper upper-level root->plan_params.
 *
 * This is just like assign_param_for_var, except for PlaceHolderVars.
 */
/*
 * assign_param_for_placeholdervar - (中文)为当前子查询中的 PHV 选择(或
 * 复用)一个 PARAM_EXEC 编号
 *
 * 【作用】assign_param_for_var 的 PlaceHolderVar 版:沿 parent_root 上溯
 * 到 PHV 所属查询层,在 plan_params 中按 phid 比对(相等即复用编号),否则
 * 复制 PHV 并把其 phlevelsup 归零后登记、分配新槽位。
 *
 * 【设计思想】PHV 的判等直接比 phid 即可(全局唯一)。复制后用
 * IncrementVarSublevelsUp 把内部所有 Var 的层级一并下移对应层数,保证
 * 登记在目标层的 PHV 树中无跨层引用。
 *
 * 【参数】
 *   root —— 当前查询层上下文;
 *   phv  —— 待参数化的 PHV(其 phlevelsup > 0)。
 * 【返回值】该 PHV 对应的 PARAM_EXEC 编号。
 */
static int
assign_param_for_placeholdervar(PlannerInfo *root, PlaceHolderVar *phv)
{
	ListCell   *ppl;
	PlannerParamItem *pitem;
	Index		levelsup;

	/* Find the query level the PHV belongs to */
	for (levelsup = phv->phlevelsup; levelsup > 0; levelsup--)
		root = root->parent_root;

	/* If there's already a matching PlannerParamItem there, just use it */
	foreach(ppl, root->plan_params)
	{
		pitem = (PlannerParamItem *) lfirst(ppl);
		if (IsA(pitem->item, PlaceHolderVar))
		{
			PlaceHolderVar *pphv = (PlaceHolderVar *) pitem->item;

			/* We assume comparing the PHIDs is sufficient */
			if (pphv->phid == phv->phid)
				return pitem->paramId;
		}
	}

	/* Nope, so make a new one */
	phv = copyObject(phv);
	IncrementVarSublevelsUp((Node *) phv, -((int) phv->phlevelsup), 0);
	Assert(phv->phlevelsup == 0);

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) phv;
	pitem->paramId = list_length(root->glob->paramExecTypes);
	root->glob->paramExecTypes = lappend_oid(root->glob->paramExecTypes,
											 exprType((Node *) phv->phexpr));

	root->plan_params = lappend(root->plan_params, pitem);

	return pitem->paramId;
}

/*
 * Generate a Param node to replace the given PlaceHolderVar,
 * which is expected to have phlevelsup > 0 (ie, it is not local).
 * Record the need for the PHV in the proper upper-level root->plan_params.
 *
 * This is just like replace_outer_var, except for PlaceHolderVars.
 */
/*
 * replace_outer_placeholdervar - (中文)生成替换外层 PHV 的 PARAM_EXEC
 * Param 节点
 *
 * 【作用】replace_outer_var 的 PlaceHolderVar 版:把对上层查询 PHV 的
 * 引用替换为 Param。类型信息取自 phexpr(类型、typmod、collation),
 * location 固定为 -1。
 *
 * 【设计思想】与 replace_outer_var 一一对应,只是把 PHV 委托给
 * assign_param_for_placeholdervar 处理。
 *
 * 【参数】
 *   root —— 当前查询层上下文;
 *   phv  —— 来自上层查询的 PHV 引用(phlevelsup > 0)。
 * 【返回值】替换用的 Param 节点(PARAM_EXEC)。
 */
Param *
replace_outer_placeholdervar(PlannerInfo *root, PlaceHolderVar *phv)
{
	Param	   *retval;
	int			i;

	Assert(phv->phlevelsup > 0 && phv->phlevelsup < root->query_level);

	/* Find the PHV in the appropriate plan_params, or add it if not present */
	i = assign_param_for_placeholdervar(root, phv);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = i;
	retval->paramtype = exprType((Node *) phv->phexpr);
	retval->paramtypmod = exprTypmod((Node *) phv->phexpr);
	retval->paramcollid = exprCollation((Node *) phv->phexpr);
	retval->location = -1;

	return retval;
}

/*
 * Generate a Param node to replace the given Aggref
 * which is expected to have agglevelsup > 0 (ie, it is not local).
 * Record the need for the Aggref in the proper upper-level root->plan_params.
 */
/*
 * replace_outer_agg - (中文)生成替换外层 Aggref 的 PARAM_EXEC Param 节点
 *
 * 【作用】当子查询引用上层聚合的结果时,把该 Aggref(agglevelsup > 0)
 * 替换为 Param,并在其所属上层查询层登记提供需求。
 *
 * 【设计思想】与 Var 版不同,聚合引用不去重——每个出现都新建一个槽
 * (注释解释:去重收益不值当,徒增实现复杂度)。同样用
 * IncrementVarSublevelsUp 把聚合内引用的层级下调。Param 类型取 aggtype,
 * collation 取 aggcollid。
 *
 * 【参数】
 *   root —— 当前查询层上下文;
 *   agg  —— 来自上层查询的 Aggref(agglevelsup > 0)。
 * 【返回值】替换用的 Param 节点(PARAM_EXEC)。
 */
Param *
replace_outer_agg(PlannerInfo *root, Aggref *agg)
{
	Param	   *retval;
	PlannerParamItem *pitem;
	Index		levelsup;

	Assert(agg->agglevelsup > 0 && agg->agglevelsup < root->query_level);

	/* Find the query level the Aggref belongs to */
	for (levelsup = agg->agglevelsup; levelsup > 0; levelsup--)
		root = root->parent_root;

	/*
	 * It does not seem worthwhile to try to de-duplicate references to outer
	 * aggs.  Just make a new slot every time.
	 */
	agg = copyObject(agg);
	IncrementVarSublevelsUp((Node *) agg, -((int) agg->agglevelsup), 0);
	Assert(agg->agglevelsup == 0);

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) agg;
	pitem->paramId = list_length(root->glob->paramExecTypes);
	root->glob->paramExecTypes = lappend_oid(root->glob->paramExecTypes,
											 agg->aggtype);

	root->plan_params = lappend(root->plan_params, pitem);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = pitem->paramId;
	retval->paramtype = agg->aggtype;
	retval->paramtypmod = -1;
	retval->paramcollid = agg->aggcollid;
	retval->location = agg->location;

	return retval;
}

/*
 * Generate a Param node to replace the given GroupingFunc expression which is
 * expected to have agglevelsup > 0 (ie, it is not local).
 * Record the need for the GroupingFunc in the proper upper-level
 * root->plan_params.
 */
/*
 * replace_outer_grouping - (中文)生成替换外层 GroupingFunc 的 PARAM_EXEC
 * Param 节点
 *
 * 【作用】把来自上层查询的 GroupingFunc(在带 GROUPING SETS 的查询中用于
 * 区分分组函数输出的表达式,agglevelsup > 0)替换为 Param 并登记提供需求。
 *
 * 【设计思想】与 replace_outer_agg 同构:不去重、每处新建槽位,用
 * IncrementVarSublevelsUp 下调内部层级。类型取 exprType(grp),collation
 * 为 InvalidOid。
 *
 * 【参数】
 *   root —— 当前查询层上下文;
 *   grp  —— 来自上层查询的 GroupingFunc(agglevelsup > 0)。
 * 【返回值】替换用的 Param 节点(PARAM_EXEC)。
 */
Param *
replace_outer_grouping(PlannerInfo *root, GroupingFunc *grp)
{
	Param	   *retval;
	PlannerParamItem *pitem;
	Index		levelsup;
	Oid			ptype = exprType((Node *) grp);

	Assert(grp->agglevelsup > 0 && grp->agglevelsup < root->query_level);

	/* Find the query level the GroupingFunc belongs to */
	for (levelsup = grp->agglevelsup; levelsup > 0; levelsup--)
		root = root->parent_root;

	/*
	 * It does not seem worthwhile to try to de-duplicate references to outer
	 * aggs.  Just make a new slot every time.
	 */
	grp = copyObject(grp);
	IncrementVarSublevelsUp((Node *) grp, -((int) grp->agglevelsup), 0);
	Assert(grp->agglevelsup == 0);

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) grp;
	pitem->paramId = list_length(root->glob->paramExecTypes);
	root->glob->paramExecTypes = lappend_oid(root->glob->paramExecTypes,
											 ptype);

	root->plan_params = lappend(root->plan_params, pitem);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = pitem->paramId;
	retval->paramtype = ptype;
	retval->paramtypmod = -1;
	retval->paramcollid = InvalidOid;
	retval->location = grp->location;

	return retval;
}

/*
 * Generate a Param node to replace the given MergeSupportFunc expression
 * which is expected to be in the RETURNING list of an upper-level MERGE
 * query.  Record the need for the MergeSupportFunc in the proper upper-level
 * root->plan_params.
 */
/*
 * replace_outer_merge_support - (中文)生成替换上层 MERGE 的
 * MergeSupportFunc 的 PARAM_EXEC Param 节点
 *
 * 【作用】把来自上层 MERGE 查询 RETURNING 列表的 MergeSupportFunc 表达式
 * 替换为 Param:沿 parent_root 逐层上溯,直到找到命令类型为 CMD_MERGE 的
 * 查询层(找不到则报错),在那里登记提供需求。
 *
 * 【设计思想】MergeSupportFunc 专用于 MERGE 的 RETURNING,故其所属层必
 * 是 MERGE 查询;用 do-while 上溯而非按 level 数跳,因为解析器已保证它
 * 就在上层 MERGE 的 RETURNING 中,只需找到那一层。不去重、每处新建槽。
 *
 * 【参数】
 *   root —— 当前查询层上下文;
 *   msf  —— 来自上层 MERGE 的 MergeSupportFunc 表达式。
 * 【返回值】替换用的 Param 节点(PARAM_EXEC)。
 */
Param *
replace_outer_merge_support(PlannerInfo *root, MergeSupportFunc *msf)
{
	Param	   *retval;
	PlannerParamItem *pitem;
	Oid			ptype = exprType((Node *) msf);

	Assert(root->parse->commandType != CMD_MERGE);

	/*
	 * The parser should have ensured that the MergeSupportFunc is in the
	 * RETURNING list of an upper-level MERGE query, so find that query.
	 */
	do
	{
		root = root->parent_root;
		if (root == NULL)
			elog(ERROR, "MergeSupportFunc found outside MERGE");
	} while (root->parse->commandType != CMD_MERGE);

	/*
	 * It does not seem worthwhile to try to de-duplicate references to outer
	 * MergeSupportFunc expressions.  Just make a new slot every time.
	 */
	msf = copyObject(msf);

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) msf;
	pitem->paramId = list_length(root->glob->paramExecTypes);
	root->glob->paramExecTypes = lappend_oid(root->glob->paramExecTypes,
											 ptype);

	root->plan_params = lappend(root->plan_params, pitem);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = pitem->paramId;
	retval->paramtype = ptype;
	retval->paramtypmod = -1;
	retval->paramcollid = InvalidOid;
	retval->location = msf->location;

	return retval;
}

/*
 * Generate a Param node to replace the given ReturningExpr expression which
 * is expected to have retlevelsup > 0 (ie, it is not local).  Record the need
 * for the ReturningExpr in the proper upper-level root->plan_params.
 */
/*
 * replace_outer_returning - (中文)生成替换外层 ReturningExpr 的
 * PARAM_EXEC Param 节点
 *
 * 【作用】把来自上层查询的 ReturningExpr(INSERT ... ON CONFLICT / MERGE
 * 中引用被更新行值的表达式,retlevelsup > 0)替换为 Param 并登记。
 *
 * 【设计思想】与 replace_outer_agg 同构:按 retlevelsup 上溯、复制后用
 * IncrementVarSublevelsUp 下移层级、不去重新建槽。类型/typmod/collation/
 * location 均取自其内含表达式 retexpr。
 *
 * 【参数】
 *   root  —— 当前查询层上下文;
 *   rexpr —— 来自上层查询的 ReturningExpr(retlevelsup > 0)。
 * 【返回值】替换用的 Param 节点(PARAM_EXEC)。
 */
Param *
replace_outer_returning(PlannerInfo *root, ReturningExpr *rexpr)
{
	Param	   *retval;
	PlannerParamItem *pitem;
	Index		levelsup;
	Oid			ptype = exprType((Node *) rexpr->retexpr);

	Assert(rexpr->retlevelsup > 0 && rexpr->retlevelsup < root->query_level);

	/* Find the query level the ReturningExpr belongs to */
	for (levelsup = rexpr->retlevelsup; levelsup > 0; levelsup--)
		root = root->parent_root;

	/*
	 * It does not seem worthwhile to try to de-duplicate references to outer
	 * ReturningExprs.  Just make a new slot every time.
	 */
	rexpr = copyObject(rexpr);
	IncrementVarSublevelsUp((Node *) rexpr, -((int) rexpr->retlevelsup), 0);
	Assert(rexpr->retlevelsup == 0);

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) rexpr;
	pitem->paramId = list_length(root->glob->paramExecTypes);
	root->glob->paramExecTypes = lappend_oid(root->glob->paramExecTypes,
											 ptype);

	root->plan_params = lappend(root->plan_params, pitem);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = pitem->paramId;
	retval->paramtype = ptype;
	retval->paramtypmod = exprTypmod((Node *) rexpr->retexpr);
	retval->paramcollid = exprCollation((Node *) rexpr->retexpr);
	retval->location = exprLocation((Node *) rexpr->retexpr);

	return retval;
}

/*
 * Generate a Param node to replace the given Var,
 * which is expected to come from some upper NestLoop plan node.
 * Record the need for the Var in root->curOuterParams.
 */
/*
 * replace_nestloop_param_var - (中文)生成替换来自外层 NestLoop 的 Var 的
 * PARAM_EXEC Param 节点
 *
 * 【作用】当内层计划节点需要外层 nestloop 左端提供的 Var 值时,把该 Var
 * 替换为 Param,并在 root->curOuterParams 中登记对应的 NestLoopParam
 * (若已存在相同的则直接复用其槽位)。
 *
 * 【设计思想】与子查询参数化不同,这里用 equal() 全等比较做去重,复用
 * 已登记 NLP 的 paramno,避免同一 Var 创建多个 PARAM_EXEC 槽。新 Var 用
 * generate_new_exec_param 分配槽位,并把 Var 副本(供外层真正求值)记入
 * curOuterParams。
 *
 * 【参数】
 *   root —— 当前查询层上下文;
 *   var  —— 需要由外层 nestloop 提供的 Var。
 * 【返回值】替换用的 Param 节点(PARAM_EXEC)。
 */
Param *
replace_nestloop_param_var(PlannerInfo *root, Var *var)
{
	Param	   *param;
	NestLoopParam *nlp;
	ListCell   *lc;

	/* Is this Var already listed in root->curOuterParams? */
	foreach(lc, root->curOuterParams)
	{
		nlp = (NestLoopParam *) lfirst(lc);
		if (equal(var, nlp->paramval))
		{
			/* Yes, so just make a Param referencing this NLP's slot */
			param = makeNode(Param);
			param->paramkind = PARAM_EXEC;
			param->paramid = nlp->paramno;
			param->paramtype = var->vartype;
			param->paramtypmod = var->vartypmod;
			param->paramcollid = var->varcollid;
			param->location = var->location;
			return param;
		}
	}

	/* No, so assign a PARAM_EXEC slot for a new NLP */
	param = generate_new_exec_param(root,
									var->vartype,
									var->vartypmod,
									var->varcollid);
	param->location = var->location;

	/* Add it to the list of required NLPs */
	nlp = makeNode(NestLoopParam);
	nlp->paramno = param->paramid;
	nlp->paramval = copyObject(var);
	root->curOuterParams = lappend(root->curOuterParams, nlp);

	/* And return the replacement Param */
	return param;
}

/*
 * Generate a Param node to replace the given PlaceHolderVar,
 * which is expected to come from some upper NestLoop plan node.
 * Record the need for the PHV in root->curOuterParams.
 *
 * This is just like replace_nestloop_param_var, except for PlaceHolderVars.
 */
/*
 * replace_nestloop_param_placeholdervar - (中文)生成替换来自外层 NestLoop
 * 的 PHV 的 PARAM_EXEC Param 节点
 *
 * 【作用】replace_nestloop_param_var 的 PlaceHolderVar 版:把需要由外层
 * nestloop 提供的 PHV 替换为 Param 并登记 NLP。
 *
 * 【设计思想】类型信息取自 phexpr,location 为 -1;去重与登记逻辑同 Var
 * 版。复制 PHV 时强转成 (Var *) 存入 paramval——NestLoopParam 的
 * paramval 字段按 Var 声明,PHV 节点在内存布局上可被安全地放入该字段
 * (规划器内部约定)。
 *
 * 【参数】
 *   root —— 当前查询层上下文;
 *   phv  —— 需要由外层 nestloop 提供的 PHV。
 * 【返回值】替换用的 Param 节点(PARAM_EXEC)。
 */
Param *
replace_nestloop_param_placeholdervar(PlannerInfo *root, PlaceHolderVar *phv)
{
	Param	   *param;
	NestLoopParam *nlp;
	ListCell   *lc;

	/* Is this PHV already listed in root->curOuterParams? */
	foreach(lc, root->curOuterParams)
	{
		nlp = (NestLoopParam *) lfirst(lc);
		if (equal(phv, nlp->paramval))
		{
			/* Yes, so just make a Param referencing this NLP's slot */
			param = makeNode(Param);
			param->paramkind = PARAM_EXEC;
			param->paramid = nlp->paramno;
			param->paramtype = exprType((Node *) phv->phexpr);
			param->paramtypmod = exprTypmod((Node *) phv->phexpr);
			param->paramcollid = exprCollation((Node *) phv->phexpr);
			param->location = -1;
			return param;
		}
	}

	/* No, so assign a PARAM_EXEC slot for a new NLP */
	param = generate_new_exec_param(root,
									exprType((Node *) phv->phexpr),
									exprTypmod((Node *) phv->phexpr),
									exprCollation((Node *) phv->phexpr));

	/* Add it to the list of required NLPs */
	nlp = makeNode(NestLoopParam);
	nlp->paramno = param->paramid;
	nlp->paramval = (Var *) copyObject(phv);
	root->curOuterParams = lappend(root->curOuterParams, nlp);

	/* And return the replacement Param */
	return param;
}

/*
 * process_subquery_nestloop_params
 *	  Handle params of a parameterized subquery that need to be fed
 *	  from an outer nestloop.
 *
 * Currently, that would be *all* params that a subquery in FROM has demanded
 * from the current query level, since they must be LATERAL references.
 *
 * subplan_params is a list of PlannerParamItems that we intend to pass to
 * a subquery-in-FROM.  (This was constructed in root->plan_params while
 * planning the subquery, but isn't there anymore when this is called.)
 *
 * The subplan's references to the outer variables are already represented
 * as PARAM_EXEC Params, since that conversion was done by the routines above
 * while planning the subquery.  So we need not modify the subplan or the
 * PlannerParamItems here.  What we do need to do is add entries to
 * root->curOuterParams to signal the parent nestloop plan node that it must
 * provide these values.  This differs from replace_nestloop_param_var in
 * that the PARAM_EXEC slots to use have already been determined.
 *
 * Note that we also use root->curOuterRels as an implicit parameter for
 * sanity checks.
 */
/*
 * process_subquery_nestloop_params - (中文)处理需要由外层 nestloop 提供的
 * 子查询参数
 *
 * 【作用】当 FROM 中的子查询(含 LATERAL 引用)需要当前查询层的值时,
 * 把这些子查询参数(subplan_params,即规划子查询时在 plan_params 里生成
 * 的条目)转为当前层的 curOuterParams 登记,通知未来的 nestloop 节点必须
 * 提供它们。此时子查询内部引用已被替换为 PARAM_EXEC,故无需再改子计划。
 *
 * 【设计思想】按条目类型(Var / PHV)处理:
 * - 检查其来源确在当前层的外层 rels(curOuterRels)内,否则报
 *   "non-LATERAL parameter required by subquery";
 * - 与已有 curOuterParams 按 paramno 去重(已有则 Assert 值一致,无事可
 *   做);否则新建 NestLoopParam。
 * PHV 的检查用 find_placeholder_info 的 ph_eval_at ⊆ curOuterRels。
 * 注意 curOuterRels 仅用作健全性检查的隐式参数。
 *
 * 【参数】
 *   root           —— 当前查询层上下文;
 *   subplan_params —— 准备传给子查询的 PlannerParamItem 列表。
 * 【返回值】无。
 */
void
process_subquery_nestloop_params(PlannerInfo *root, List *subplan_params)
{
	ListCell   *lc;

	foreach(lc, subplan_params)
	{
		PlannerParamItem *pitem = lfirst_node(PlannerParamItem, lc);

		if (IsA(pitem->item, Var))
		{
			Var		   *var = (Var *) pitem->item;
			NestLoopParam *nlp;
			ListCell   *lc2;

			/* If not from a nestloop outer rel, complain */
			if (!bms_is_member(var->varno, root->curOuterRels))
				elog(ERROR, "non-LATERAL parameter required by subquery");

			/* Is this param already listed in root->curOuterParams? */
			foreach(lc2, root->curOuterParams)
			{
				nlp = (NestLoopParam *) lfirst(lc2);
				if (nlp->paramno == pitem->paramId)
				{
					Assert(equal(var, nlp->paramval));
					/* Present, so nothing to do */
					break;
				}
			}
			if (lc2 == NULL)
			{
				/* No, so add it */
				nlp = makeNode(NestLoopParam);
				nlp->paramno = pitem->paramId;
				nlp->paramval = copyObject(var);
				root->curOuterParams = lappend(root->curOuterParams, nlp);
			}
		}
		else if (IsA(pitem->item, PlaceHolderVar))
		{
			PlaceHolderVar *phv = (PlaceHolderVar *) pitem->item;
			NestLoopParam *nlp;
			ListCell   *lc2;

			/* If not from a nestloop outer rel, complain */
			if (!bms_is_subset(find_placeholder_info(root, phv)->ph_eval_at,
							   root->curOuterRels))
				elog(ERROR, "non-LATERAL parameter required by subquery");

			/* Is this param already listed in root->curOuterParams? */
			foreach(lc2, root->curOuterParams)
			{
				nlp = (NestLoopParam *) lfirst(lc2);
				if (nlp->paramno == pitem->paramId)
				{
					Assert(equal(phv, nlp->paramval));
					/* Present, so nothing to do */
					break;
				}
			}
			if (lc2 == NULL)
			{
				/* No, so add it */
				nlp = makeNode(NestLoopParam);
				nlp->paramno = pitem->paramId;
				nlp->paramval = (Var *) copyObject(phv);
				root->curOuterParams = lappend(root->curOuterParams, nlp);
			}
		}
		else
			elog(ERROR, "unexpected type of subquery parameter");
	}
}

/*
 * Identify any NestLoopParams that should be supplied by a NestLoop
 * plan node with the specified lefthand rels and required-outer rels.
 * Remove them from the active root->curOuterParams list and return
 * them as the result list.
 *
 * Vars and PHVs appearing in the result list must have nullingrel sets
 * that could validly appear in the lefthand rel's output.  Ordinarily that
 * would be true already, but if we have applied outer join identity 3,
 * there could be more or fewer nullingrel bits in the nodes appearing in
 * curOuterParams than are in the nominal leftrelids.  We deal with that by
 * forcing their nullingrel sets to include exactly the outer-join relids
 * that appear in leftrelids and can null the respective Var or PHV.
 * This fix is a bit ad-hoc and intellectually unsatisfactory, because it's
 * essentially jumping to the conclusion that we've placed evaluation of
 * the nestloop parameters correctly, and thus it defeats the intent of the
 * subsequent nullingrel cross-checks in setrefs.c.  But the alternative
 * seems to be to generate multiple versions of each laterally-parameterized
 * subquery, which'd be unduly expensive.
 */
/*
 * identify_current_nestloop_params - (中文)找出应由指定 NestLoop 供值的
 * NestLoopParam,并从活动列表移除
 *
 * 【作用】createplan.c 创建 NestLoop 节点时调用:从 root->curOuterParams
 * 中挑出"可以由给定左端关系(leftrelids)及其外参数(outerrelids)提供"
 * 的条目,从活动列表删除并作为结果返回,交给 NestLoop 节点执行。
 *
 * 【设计思想】
 * - 对 Var:只要其 varno 属于 leftrelids 即命中;对 PHV:要求 ph_eval_at
 *   ⊆ (leftrelids ∪ outerrelids) 且与 leftrelids 有交集(只用外层参数、
 *   自己什么都算不了的 PHV 应留到更高层求值);
 * - nullingrels 修正:命中条目(取自 curOuterParams 的是全新副本,可放心
 *   就地改)按"leftrelids 中能置空该 Var/PHV 的外连接"重算其
 *   varnullingrels / phnullingrels。这是为外连接恒等式 3 处理带来的
 *   "多于/少于名义 leftrelids"的不一致,手段稍显 ad-hoc,但可避免为每个
 *   LATERAL 子查询生成多个版本;
 * - PHV 特例:若查询含 SubLink,从本层 placeholder_list 取"含 SubPlan"
 *   的 PHV 版本替换 paramval(内层子查询不会递归进外层 PHV 处理 SubLink),
 *   否则执行期会拿不到正确值的版本。
 *
 * 【参数】
 *   root        —— 当前查询层上下文;
 *   leftrelids  —— NestLoop 左端关系集合;
 *   outerrelids —— 该连接允许的外部参数关系集合(可为 NULL)。
 * 【返回值】应从左端提供的 NestLoopParam 列表。
 */
List *
identify_current_nestloop_params(PlannerInfo *root,
								 Relids leftrelids,
								 Relids outerrelids)
{
	List	   *result;
	Relids		allleftrelids;
	ListCell   *cell;

	/*
	 * We'll be able to evaluate a PHV in the lefthand path if it uses the
	 * lefthand rels plus any available required-outer rels.  But don't do so
	 * if it uses *only* required-outer rels; in that case it should be
	 * evaluated higher in the tree.  For Vars, no such hair-splitting is
	 * necessary since they depend on only one relid.
	 */
	if (outerrelids)
		allleftrelids = bms_union(leftrelids, outerrelids);
	else
		allleftrelids = leftrelids;

	result = NIL;
	foreach(cell, root->curOuterParams)
	{
		NestLoopParam *nlp = (NestLoopParam *) lfirst(cell);

		/*
		 * We are looking for Vars and PHVs that can be supplied by the
		 * lefthand rels.  When we find one, it's okay to modify it in-place
		 * because all the routines above make a fresh copy to put into
		 * curOuterParams.
		 */
		if (IsA(nlp->paramval, Var) &&
			bms_is_member(nlp->paramval->varno, leftrelids))
		{
			Var		   *var = (Var *) nlp->paramval;
			RelOptInfo *rel = root->simple_rel_array[var->varno];

			root->curOuterParams = foreach_delete_current(root->curOuterParams,
														  cell);
			var->varnullingrels = bms_intersect(rel->nulling_relids,
												leftrelids);
			result = lappend(result, nlp);
		}
		else if (IsA(nlp->paramval, PlaceHolderVar))
		{
			PlaceHolderVar *phv = (PlaceHolderVar *) nlp->paramval;
			PlaceHolderInfo *phinfo = find_placeholder_info(root, phv);
			Relids		eval_at = phinfo->ph_eval_at;

			if (bms_is_subset(eval_at, allleftrelids) &&
				bms_overlap(eval_at, leftrelids))
			{
				root->curOuterParams = foreach_delete_current(root->curOuterParams,
															  cell);

				/*
				 * Deal with an edge case: if the PHV was pulled up out of a
				 * subquery and it contains a subquery that was originally
				 * pushed down from this query level, then that will still be
				 * represented as a SubLink, because SS_process_sublinks won't
				 * recurse into outer PHVs, so it didn't get transformed
				 * during expression preprocessing in the subquery.  We need a
				 * version of the PHV that has a SubPlan, which we can get
				 * from the current query level's placeholder_list.  This is
				 * quite grotty of course, but dealing with it earlier in the
				 * handling of subplan params would be just as grotty, and it
				 * might end up being a waste of cycles if we don't decide to
				 * treat the PHV as a NestLoopParam.  (Perhaps that whole
				 * mechanism should be redesigned someday, but today is not
				 * that day.)
				 */
				if (root->parse->hasSubLinks)
				{
					phv = copyObject(phinfo->ph_var);

					/*
					 * The ph_var will have empty nullingrels, but that
					 * doesn't matter since we're about to overwrite
					 * phv->phnullingrels.  Other fields should be OK already.
					 */
					nlp->paramval = (Var *) phv;
				}

				phv->phnullingrels =
					bms_intersect(get_placeholder_nulling_relids(root, phinfo),
								  leftrelids);

				result = lappend(result, nlp);
			}
		}
	}
	return result;
}

/*
 * Generate a new Param node that will not conflict with any other.
 *
 * This is used to create Params representing subplan outputs or
 * NestLoop parameters.
 *
 * We don't need to build a PlannerParamItem for such a Param, but we do
 * need to make sure we record the type in paramExecTypes (otherwise,
 * there won't be a slot allocated for it).
 */
/*
 * generate_new_exec_param - (中文)生成一个新的、与既有槽不冲突的
 * PARAM_EXEC Param 节点
 *
 * 【作用】为 SubPlan 输出或 NestLoop 参数创建全新的 Param(PARAM_EXEC):
 * 分配下一个槽位编号并在 paramExecTypes 里登记类型。不需要构造
 * PlannerParamItem,但必须在 paramExecTypes 里占位,否则执行期没有对应
 * 槽位。
 *
 * 【设计思想】编号恒取 paramExecTypes 当前长度,类型直接入表;location
 * 默认 -1。调用方(如 replace_nestloop_param_*)可自行覆盖 location。
 *
 * 【参数】
 *   root           —— 当前查询层上下文;
 *   paramtype      —— 参数类型 OID;
 *   paramtypmod    —— 参数类型修饰符;
 *   paramcollation —— 参数排序规则 OID。
 * 【返回值】新分配的 PARAM_EXEC Param 节点。
 */
Param *
generate_new_exec_param(PlannerInfo *root, Oid paramtype, int32 paramtypmod,
						Oid paramcollation)
{
	Param	   *retval;

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = list_length(root->glob->paramExecTypes);
	root->glob->paramExecTypes = lappend_oid(root->glob->paramExecTypes,
											 paramtype);
	retval->paramtype = paramtype;
	retval->paramtypmod = paramtypmod;
	retval->paramcollid = paramcollation;
	retval->location = -1;

	return retval;
}

/*
 * Assign a (nonnegative) PARAM_EXEC ID for a special parameter (one that
 * is not actually used to carry a value at runtime).  Such parameters are
 * used for special runtime signaling purposes, such as connecting a
 * recursive union node to its worktable scan node or forcing plan
 * re-evaluation within the EvalPlanQual mechanism.  No actual Param node
 * exists with this ID, however.
 */
/*
 * assign_special_exec_param - (中文)为"特殊参数"分配一个 PARAM_EXEC 编号
 *
 * 【作用】分配一个运行时不携带值的 PARAM_EXEC 槽(类型登记为
 * InvalidOid),供特殊运行期信号使用,例如递归 UNION 的工作表扫描节点与
 * 递归节点之间的 chgParam 连接、或 EvalPlanQual 机制中强制计划重求值。
 * 注意:并不存在真正使用该编号的 Param 节点。
 *
 * 【设计思想】直接在 paramExecTypes 末尾追加一个 InvalidOid 占位,占用
 * 一个编号。这类槽只用于位图信号(chgParam),执行器按编号识别。
 *
 * 【参数】root —— 当前查询层上下文。
 * 【返回值】新分配的特殊参数编号。
 */
int
assign_special_exec_param(PlannerInfo *root)
{
	int			paramId = list_length(root->glob->paramExecTypes);

	root->glob->paramExecTypes = lappend_oid(root->glob->paramExecTypes,
											 InvalidOid);
	return paramId;
}
