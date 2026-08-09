/*-------------------------------------------------------------------------
 *
 * placeholder.c
 *	  PlaceHolderVar and PlaceHolderInfo manipulation routines
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件提供 PlaceHolderVar(PHV)与 PlaceHolderInfo(PHI)的操纵例程。
 * PHV 是在子查询上拉(pullup)过程中产生的占位符节点:当一个本该在低层
 * 查询中计算的表达式被提升到上层查询后,就用一个 PHV 包裹该表达式,并
 * 记录它"应该在何处计算"(phrels 语法位置)、"哪些关系引用它"等信息,
 * 供规划器在正确的扫描/连接层把它算出来。
 *
 * 【核心数据结构】
 * - PlaceHolderVar(PHV):表达式树里的节点,含 phexpr(被包裹的表达式)、
 *   phrels(语法作用域)、phnullingrels(其上方的可置空外连接集合)、
 *   phlevelsup、phid(全局唯一编号);
 * - PlaceHolderInfo(PHI):规划期的登记信息,含 ph_eval_at(应在哪组关系
 *   之上计算)、ph_lateral(其中的 LATERAL 引用)、ph_needed(哪些上层
 *   关系还需要它)、ph_width(宽度估算)。PHI 同时链入 root->placeholder_list
 *   与以 phid 为下标的 root->placeholder_array,以便按 phid 快速查找。
 *
 * 【主要函数关系】
 * make_placeholder_expr 负责创建 PHV;find_placeholder_info 负责按 PHV
 * 查找/创建 PHI;find_placeholders_in_jointree(+递归子函数)在 jointree
 * 里搜集所有 PHV 并建立对应 PHI;fix_placeholder_input_needed_levels 与
 * rebuild_placeholder_attr_needed 保证 PHV 的输入在最需要的层可见;
 * add_placeholders_to_base_rels / add_placeholders_to_joinrel 把 PHV 加进
 * 相应关系的关系目标列;contain_placeholder_references_to 判断子句是否
 * 引用了某(外连接)关系的 PHV;get_placeholder_nulling_relids 计算能
 * 置空某 PHV 的外连接集合;strip_noop_phvs 系列用于剥掉"无操作"PHV。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/placeholder.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "nodes/nodeFuncs.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/placeholder.h"
#include "optimizer/planmain.h"
#include "utils/lsyscache.h"


typedef struct contain_placeholder_references_context
{
	int			relid;
	int			sublevels_up;
} contain_placeholder_references_context;

/* Local functions */
static void find_placeholders_recurse(PlannerInfo *root, Node *jtnode);
static void find_placeholders_in_expr(PlannerInfo *root, Node *expr);
static bool contain_placeholder_references_walker(Node *node,
												  contain_placeholder_references_context *context);
static bool contain_noop_phv_walker(Node *node, void *context);
static Node *strip_noop_phvs_mutator(Node *node, void *context);


/*
 * make_placeholder_expr
 *		Make a PlaceHolderVar for the given expression.
 *
 * phrels is the syntactic location (as a set of relids) to attribute
 * to the expression.
 *
 * The caller is responsible for adjusting phlevelsup and phnullingrels
 * as needed.  Because we do not know here which query level the PHV
 * will be associated with, it's important that this function touches
 * only root->glob; messing with other parts of PlannerInfo would be
 * likely to do the wrong thing.
 */
/*
 * make_placeholder_expr - (中文)为给定表达式创建一个 PlaceHolderVar
 *
 * 【作用】把 expr 包装成 PHV 节点并返回,供子查询上拉等场景使用。调用者
 * 后续负责按需调整 phlevelsup 与 phnullingrels。该函数只改写
 * root->glob(递增 lastPHId 取得全局唯一 phid),不碰 PlannerInfo 的其他
 * 部分——因为此刻尚不确定该 PHV 属于哪个查询层,乱动会出错。
 *
 * 【设计思想】phid 取自全局计数器 root->glob->lastPHId 并自增,保证整个
 * 计划里每个 PHV 有唯一编号,可用于数组索引与相等比较。phrels 是"语法
 * 位置"——即该表达式原本出现在哪组关系的范围内,决定它最迟可在哪里求值。
 *
 * 【参数】
 *   root   —— 规划上下文,使用其 glob->lastPHId 分配编号;
 *   expr   —— 被包裹的原始表达式;
 *   phrels —— 表达式的语法作用域(关系 id 的位图)。
 * 【返回值】新构造的 PlaceHolderVar 节点。
 */
PlaceHolderVar *
make_placeholder_expr(PlannerInfo *root, Expr *expr, Relids phrels)
{
	PlaceHolderVar *phv = makeNode(PlaceHolderVar);

	phv->phexpr = expr;
	phv->phrels = phrels;
	phv->phnullingrels = NULL;	/* caller may change this later */
	phv->phid = ++(root->glob->lastPHId);
	phv->phlevelsup = 0;		/* caller may change this later */

	return phv;
}

/*
 * find_placeholder_info
 *		Fetch the PlaceHolderInfo for the given PHV
 *
 * If the PlaceHolderInfo doesn't exist yet, create it if we haven't yet
 * frozen the set of PlaceHolderInfos for the query; else throw an error.
 *
 * This is separate from make_placeholder_expr because subquery pullup has
 * to make PlaceHolderVars for expressions that might not be used at all in
 * the upper query, or might not remain after const-expression simplification.
 * We build PlaceHolderInfos only for PHVs that are still present in the
 * simplified query passed to query_planner().
 *
 * Note: this should only be called after query_planner() has started.
 */
/*
 * find_placeholder_info - (中文)按 PHV 查找(必要时创建)对应的
 * PlaceHolderInfo
 *
 * 【作用】规划期(在 query_planner 开始之后、placeholdersFrozen 置位之前)
 * 根据 PHV 取得/创建其 PHI。若 PHI 尚不存在则创建并登记;若集合已冻结
 * (placeholdersFrozen)仍发现新 PHV,说明逻辑错误,直接报错。
 *
 * 【设计思想】与 make_placeholder_expr 分开的原因:子查询上拉会为"上层
 * 查询可能根本不用、或经常量化简后可能消失"的表达式创建 PHV,但只有
 * 最终留在简化查询里的 PHV 才值得建 PHI。创建 PHI 时要算三组关系集合:
 * - ph_lateral = 表达式引用的、但位于语法作用域之外的关系(即 LATERAL
 *   引用),它们应算入 lateral 依赖但不影响 eval_at;
 * - ph_eval_at = 引用关系与语法作用域的交集,即"最早可在哪里求值";
 *   若为空(表达式不含任何 Var,或引用的全是作用域外的关系),则强制在
 *   语法位置求值。
 * 该 PHI 同时加入 placeholder_list 与按 phid 索引的 placeholder_array
 * (数组按需翻倍扩容),因此注意:不能把整个 placeholder_list 交给
 * expression_tree_mutator 之类的工具处理,否则数组与列表会失去一致性。
 * 创建后立即递归处理其内含的低层 PHV,确保它们也有 PHI。
 *
 * 【参数】
 *   root —— 规划上下文;
 *   phv  —— 要查找/登记其 PHI 的 PlaceHolderVar(要求 phlevelsup == 0)。
 * 【返回值】对应的 PlaceHolderInfo(新建或已存在)。
 */
PlaceHolderInfo *
find_placeholder_info(PlannerInfo *root, PlaceHolderVar *phv)
{
	PlaceHolderInfo *phinfo;
	Relids		rels_used;

	/* if this ever isn't true, we'd need to be able to look in parent lists */
	Assert(phv->phlevelsup == 0);

	/* Use placeholder_array to look up existing PlaceHolderInfo quickly */
	if (phv->phid < root->placeholder_array_size)
		phinfo = root->placeholder_array[phv->phid];
	else
		phinfo = NULL;
	if (phinfo != NULL)
	{
		Assert(phinfo->phid == phv->phid);
		return phinfo;
	}

	/* Not found, so create it */
	if (root->placeholdersFrozen)
		elog(ERROR, "too late to create a new PlaceHolderInfo");

	phinfo = makeNode(PlaceHolderInfo);

	phinfo->phid = phv->phid;
	phinfo->ph_var = copyObject(phv);

	/*
	 * By convention, phinfo->ph_var->phnullingrels is always empty, since the
	 * PlaceHolderInfo represents the initially-calculated state of the
	 * PlaceHolderVar.  PlaceHolderVars appearing in the query tree might have
	 * varying values of phnullingrels, reflecting outer joins applied above
	 * the calculation level.
	 */
	phinfo->ph_var->phnullingrels = NULL;

	/*
	 * Any referenced rels that are outside the PHV's syntactic scope are
	 * LATERAL references, which should be included in ph_lateral but not in
	 * ph_eval_at.  If no referenced rels are within the syntactic scope,
	 * force evaluation at the syntactic location.
	 */
	rels_used = pull_varnos(root, (Node *) phv->phexpr);
	phinfo->ph_lateral = bms_difference(rels_used, phv->phrels);
	phinfo->ph_eval_at = bms_int_members(rels_used, phv->phrels);
	/* If no contained vars, force evaluation at syntactic location */
	if (bms_is_empty(phinfo->ph_eval_at))
	{
		phinfo->ph_eval_at = bms_copy(phv->phrels);
		Assert(!bms_is_empty(phinfo->ph_eval_at));
	}
	phinfo->ph_needed = NULL;	/* initially it's unused */
	/* for the moment, estimate width using just the datatype info */
	phinfo->ph_width = get_typavgwidth(exprType((Node *) phv->phexpr),
									   exprTypmod((Node *) phv->phexpr));

	/*
	 * Add to both placeholder_list and placeholder_array.  Note: because we
	 * store pointers to the PlaceHolderInfos in two data structures, it'd be
	 * unsafe to pass the whole placeholder_list structure through
	 * expression_tree_mutator or the like --- or at least, you'd have to
	 * rebuild the placeholder_array afterwards.
	 */
	root->placeholder_list = lappend(root->placeholder_list, phinfo);

	if (phinfo->phid >= root->placeholder_array_size)
	{
		/* Must allocate or enlarge placeholder_array */
		int			new_size;

		new_size = root->placeholder_array_size ? root->placeholder_array_size * 2 : 8;
		while (phinfo->phid >= new_size)
			new_size *= 2;
		if (root->placeholder_array)
			root->placeholder_array =
				repalloc0_array(root->placeholder_array, PlaceHolderInfo *, root->placeholder_array_size, new_size);
		else
			root->placeholder_array =
				palloc0_array(PlaceHolderInfo *, new_size);
		root->placeholder_array_size = new_size;
	}
	root->placeholder_array[phinfo->phid] = phinfo;

	/*
	 * The PHV's contained expression may contain other, lower-level PHVs.  We
	 * now know we need to get those into the PlaceHolderInfo list, too, so we
	 * may as well do that immediately.
	 */
	find_placeholders_in_expr(root, (Node *) phinfo->ph_var->phexpr);

	return phinfo;
}

/*
 * find_placeholders_in_jointree
 *		Search the jointree for PlaceHolderVars, and build PlaceHolderInfos
 *
 * We don't need to look at the targetlist because build_base_rel_tlists()
 * will already have made entries for any PHVs in the tlist.
 */
/*
 * find_placeholders_in_jointree - (中文)扫描 jointree,为其中的每个 PHV
 * 建立 PlaceHolderInfo
 *
 * 【作用】由 query_planner 在冻结 PHI 集合之前调用:只要查询里出现过 PHV
 * (root->glob->lastPHId != 0),就递归遍历 jointree 找出所有 PHV 并调用
 * find_placeholder_info 建立登记信息。
 *
 * 【设计思想】无需检查目标列表——build_base_rel_tlists 已经为 tlist 中的
 * PHV 建过 PHI。递归从解析树的 jointree 顶部(FromExpr)开始,沿 fromlist
 * 与 JoinExpr 的左右子树深入,处理各层 quals。
 *
 * 【参数】root —— 规划上下文。
 * 【返回值】无。
 */
void
find_placeholders_in_jointree(PlannerInfo *root)
{
	/* This must be done before freezing the set of PHIs */
	Assert(!root->placeholdersFrozen);

	/* We need do nothing if the query contains no PlaceHolderVars */
	if (root->glob->lastPHId != 0)
	{
		/* Start recursion at top of jointree */
		Assert(root->parse->jointree != NULL &&
			   IsA(root->parse->jointree, FromExpr));
		find_placeholders_recurse(root, (Node *) root->parse->jointree);
	}
}

/*
 * find_placeholders_recurse
 *	  One recursion level of find_placeholders_in_jointree.
 *
 * jtnode is the current jointree node to examine.
 */
/*
 * find_placeholders_recurse - (中文)find_placeholders_in_jointree 的一层
 * 递归
 *
 * 【作用】按节点类型分派:RangeTblRef 无 quals 直接返回;FromExpr 先递归
 * 处理 fromlist 中的子连接,再处理顶层 quals;JoinExpr 先递归左右子树,
 * 再处理本连接层的 quals。未知节点类型报错。
 *
 * 【设计思想】先深后横的顺序保证下层连接中的 PHV 先被登记,从而在递归
 * 返回处理上层 quals 时,若有嵌套 PHV 依赖也能按正确顺序建立。
 *
 * 【参数】
 *   root   —— 规划上下文;
 *   jtnode —— 当前 jointree 节点。
 * 【返回值】无。
 */
static void
find_placeholders_recurse(PlannerInfo *root, Node *jtnode)
{
	if (jtnode == NULL)
		return;
	if (IsA(jtnode, RangeTblRef))
	{
		/* No quals to deal with here */
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		/*
		 * First, recurse to handle child joins.
		 */
		foreach(l, f->fromlist)
		{
			find_placeholders_recurse(root, lfirst(l));
		}

		/*
		 * Now process the top-level quals.
		 */
		find_placeholders_in_expr(root, f->quals);
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		/*
		 * First, recurse to handle child joins.
		 */
		find_placeholders_recurse(root, j->larg);
		find_placeholders_recurse(root, j->rarg);

		/* Process the qual clauses */
		find_placeholders_in_expr(root, j->quals);
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
}

/*
 * find_placeholders_in_expr
 *		Find all PlaceHolderVars in the given expression, and create
 *		PlaceHolderInfo entries for them.
 */
/*
 * find_placeholders_in_expr - (中文)在给定表达式中找出所有 PHV 并为其
 * 创建 PlaceHolderInfo
 *
 * 【作用】用 pull_var_clause 提取表达式中所有 Var 与 PHV(含聚合、窗口
 * 函数内部),对每个 PHV 调用 find_placeholder_info 登记;普通 Var 忽略。
 *
 * 【设计思想】pull_var_clause 比实际需要的功能更强,但现成且方便。标记
 * PVC_INCLUDE_PLACEHOLDERS 保证 PHV 也被视为"变量"一并取出。用完的
 * vars 列表要 list_free 释放。
 *
 * 【参数】
 *   root —— 规划上下文;
 *   expr —— 待扫描的表达式树。
 * 【返回值】无。
 */
static void
find_placeholders_in_expr(PlannerInfo *root, Node *expr)
{
	List	   *vars;
	ListCell   *vl;

	/*
	 * pull_var_clause does more than we need here, but it'll do and it's
	 * convenient to use.
	 */
	vars = pull_var_clause(expr,
						   PVC_RECURSE_AGGREGATES |
						   PVC_RECURSE_WINDOWFUNCS |
						   PVC_INCLUDE_PLACEHOLDERS);
	foreach(vl, vars)
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) lfirst(vl);

		/* Ignore any plain Vars */
		if (!IsA(phv, PlaceHolderVar))
			continue;

		/* Create a PlaceHolderInfo entry if there's not one already */
		(void) find_placeholder_info(root, phv);
	}
	list_free(vars);
}

/*
 * fix_placeholder_input_needed_levels
 *		Adjust the "needed at" levels for placeholder inputs
 *
 * This is called after we've finished determining the eval_at levels for
 * all placeholders.  We need to make sure that all vars and placeholders
 * needed to evaluate each placeholder will be available at the scan or join
 * level where the evaluation will be done.  (It might seem that scan-level
 * evaluations aren't interesting, but that's not so: a LATERAL reference
 * within a placeholder's expression needs to cause the referenced var or
 * placeholder to be marked as needed in the scan where it's evaluated.)
 * Note that this loop can have side-effects on the ph_needed sets of other
 * PlaceHolderInfos; that's okay because we don't examine ph_needed here, so
 * there are no ordering issues to worry about.
 */
/*
 * fix_placeholder_input_needed_levels - (中文)修正占位符输入在"何处需要
 * 被提供"的层位标记
 *
 * 【作用】在确定所有 PHV 的 ph_eval_at 之后调用:对每个 PHV,将其内部
 * 引用的所有 Var/PHV 标记为"在 ph_eval_at 这一层(扫描或连接)就必须可
 * 用",即加入相应关系的目标列表(add_vars_to_targetlist)。看似扫描层
 * 的求值无关紧要,实则不然:PHV 表达式里的 LATERAL 引用必须让被引用
 * 的 Var/PHV 在对应扫描层被标记为需要。
 *
 * 【设计思想】本循环会修改其他 PHI 的 ph_needed 集合,但由于本函数从不
 * 读 ph_needed,因此处理顺序无关紧要,不会有次序依赖问题。
 *
 * 【参数】root —— 规划上下文,遍历 root->placeholder_list。
 * 【返回值】无。
 */
void
fix_placeholder_input_needed_levels(PlannerInfo *root)
{
	ListCell   *lc;

	foreach(lc, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(lc);
		List	   *vars = pull_var_clause((Node *) phinfo->ph_var->phexpr,
										   PVC_RECURSE_AGGREGATES |
										   PVC_RECURSE_WINDOWFUNCS |
										   PVC_INCLUDE_PLACEHOLDERS);

		add_vars_to_targetlist(root, vars, phinfo->ph_eval_at);
		list_free(vars);
	}
}

/*
 * rebuild_placeholder_attr_needed
 *	  Put back attr_needed bits for Vars/PHVs needed in PlaceHolderVars.
 *
 * This is used to rebuild attr_needed/ph_needed sets after removal of a
 * useless outer join.  It should match what
 * fix_placeholder_input_needed_levels did, except that we call
 * add_vars_to_attr_needed not add_vars_to_targetlist.
 */
/*
 * rebuild_placeholder_attr_needed - (中文)重建 PHV 内 Var/PHV 的
 * attr_needed 位
 *
 * 【作用】当移除一个无用的外连接后,基表列的 attr_needed 位图需要重建:
 * 本函数对每个 PHV 重做 fix_placeholder_input_needed_levels 的工作,区别
 * 是改用 add_vars_to_attr_needed 而非 add_vars_to_targetlist。
 *
 * 【设计思想】逻辑与 fix_placeholder_input_needed_levels 保持一一对应,
 * 只是写入的目标不同——前者把依赖记到关系目标列(最终进入计划),后者
 * 只重算 attr_needed 位(供后续去除无用列使用)。任何一处改动都须与
 * 对方同步。
 *
 * 【参数】root —— 规划上下文。
 * 【返回值】无。
 */
void
rebuild_placeholder_attr_needed(PlannerInfo *root)
{
	ListCell   *lc;

	foreach(lc, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(lc);
		List	   *vars = pull_var_clause((Node *) phinfo->ph_var->phexpr,
										   PVC_RECURSE_AGGREGATES |
										   PVC_RECURSE_WINDOWFUNCS |
										   PVC_INCLUDE_PLACEHOLDERS);

		add_vars_to_attr_needed(root, vars, phinfo->ph_eval_at);
		list_free(vars);
	}
}

/*
 * add_placeholders_to_base_rels
 *		Add any required PlaceHolderVars to base rels' targetlists.
 *
 * If any placeholder can be computed at a base rel and is needed above it,
 * add it to that rel's targetlist.  This might look like it could be merged
 * with fix_placeholder_input_needed_levels, but it must be separate because
 * join removal happens in between, and can change the ph_eval_at sets.  There
 * is essentially the same logic in add_placeholders_to_joinrel, but we can't
 * do that part until joinrels are formed.
 */
/*
 * add_placeholders_to_base_rels - (中文)把需要在基表之上计算的 PHV 加入
 * 该基表的关系目标列
 *
 * 【作用】对每个"可在单个基表上计算(ph_eval_at 只有一个成员)且其上仍有
 * 需要者(ph_needed 超出 eval_at)"的 PHV,复制一份 PHV 追加到该基表的
 * reltarget->exprs,让扫描层把它算出来供上层使用。
 *
 * 【设计思想】必须独立于 fix_placeholder_input_needed_levels 的原因:两者
 * 之间隔着一个"外连接消除"(join removal)阶段,它可能改变 ph_eval_at
 * 集合。扫描层算出的值尚未被任何外连接置空,故断言 phnullingrels 为空。
 * 复制 PHV 也许多余,但保持安全习惯。关系目标列的成本与宽度字段稍后由
 * 其他模块统一更新。
 *
 * 【参数】root —— 规划上下文。
 * 【返回值】无。
 */
void
add_placeholders_to_base_rels(PlannerInfo *root)
{
	ListCell   *lc;

	foreach(lc, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(lc);
		Relids		eval_at = phinfo->ph_eval_at;
		int			varno;

		if (bms_get_singleton_member(eval_at, &varno) &&
			bms_nonempty_difference(phinfo->ph_needed, eval_at))
		{
			RelOptInfo *rel = find_base_rel(root, varno);

			/*
			 * As in add_vars_to_targetlist(), a value computed at scan level
			 * has not yet been nulled by any outer join, so its phnullingrels
			 * should be empty.
			 */
			Assert(phinfo->ph_var->phnullingrels == NULL);

			/* Copying the PHV might be unnecessary here, but be safe */
			rel->reltarget->exprs = lappend(rel->reltarget->exprs,
											copyObject(phinfo->ph_var));
			/* reltarget's cost and width fields will be updated later */
		}
	}
}

/*
 * add_placeholders_to_joinrel
 *		Add any newly-computable PlaceHolderVars to a join rel's targetlist;
 *		and if computable PHVs contain lateral references, add those
 *		references to the joinrel's direct_lateral_relids.
 *
 * A join rel should emit a PlaceHolderVar if (a) the PHV can be computed
 * at or below this join level and (b) the PHV is needed above this level.
 * Our caller build_join_rel() has already added any PHVs that were computed
 * in either join input rel, so we need add only newly-computable ones to
 * the targetlist.  However, direct_lateral_relids must be updated for every
 * PHV computable at or below this join, as explained below.
 */
/*
 * add_placeholders_to_joinrel - (中文)把"在本次连接处新可计算"的 PHV 加入
 * 连接关系的目标列,并维护其 LATERAL 依赖
 *
 * 【作用】由 build_join_rel 在创建连接关系时调用。两个输入关系已经贡献了
 * 各自目标列里算好的 PHV,本函数只需补充"在本次连接处才首次可计算、且
 * 上方仍需要"的 PHV;同时无论是否真正输出,都要把 PHV 的 LATERAL 源关系
 * 并入 joinrel->direct_lateral_relids。
 *
 * 【设计思想】
 * - 计算位置判定:ph_eval_at ⊆ joinrel->relids 说明本层(或之下)可算;
 *   ph_needed 仍包含本层之上需要者,则应当输出;
 * - 是否重复计费:仅当 ph_eval_at 不能被子集到任一输入关系时,才在目标列
 *   追加 PHV 并计入其求值代价。注意这是基于"第一个考察到的输入对"做出的
 *   决定,对其他输入对可能造成重复计费——当前接受此近似,将来可针对每个
 *   输入对重算目标列代价;
 * - direct_lateral_relids 必须无条件并入 ph_lateral,否则 join_is_legal
 *   会拒绝合法的连接顺序。虽然调用者 build_join_rel 稍后会去掉本连接
 *   自己的 relids,但这里只需累加即可。
 *
 * 【参数】
 *   root      —— 规划上下文;
 *   joinrel   —— 新建立的连接关系;
 *   outer_rel —— 外部输入关系;
 *   inner_rel —— 内部输入关系;
 *   sjinfo    —— 描述本次连接的 SpecialJoinInfo(本函数当前不使用)。
 * 【返回值】无。
 */
void
add_placeholders_to_joinrel(PlannerInfo *root, RelOptInfo *joinrel,
							RelOptInfo *outer_rel, RelOptInfo *inner_rel,
							SpecialJoinInfo *sjinfo)
{
	Relids		relids = joinrel->relids;
	int64		tuple_width = joinrel->reltarget->width;
	ListCell   *lc;

	foreach(lc, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(lc);

		/* Is it computable here? */
		if (bms_is_subset(phinfo->ph_eval_at, relids))
		{
			/* Is it still needed above this joinrel? */
			if (bms_nonempty_difference(phinfo->ph_needed, relids))
			{
				/*
				 * Yes, but only add to tlist if it wasn't computed in either
				 * input; otherwise it should be there already.  Also, we
				 * charge the cost of evaluating the contained expression if
				 * the PHV can be computed here but not in either input.  This
				 * is a bit bogus because we make the decision based on the
				 * first pair of possible input relations considered for the
				 * joinrel.  With other pairs, it might be possible to compute
				 * the PHV in one input or the other, and then we'd be double
				 * charging the PHV's cost for some join paths.  For now, live
				 * with that; but we might want to improve it later by
				 * refiguring the reltarget costs for each pair of inputs.
				 */
				if (!bms_is_subset(phinfo->ph_eval_at, outer_rel->relids) &&
					!bms_is_subset(phinfo->ph_eval_at, inner_rel->relids))
				{
					/* Copying might be unnecessary here, but be safe */
					PlaceHolderVar *phv = copyObject(phinfo->ph_var);
					QualCost	cost;

					/*
					 * It'll start out not nulled by anything.  Joins above
					 * this one might add to its phnullingrels later, in much
					 * the same way as for Vars.
					 */
					Assert(phv->phnullingrels == NULL);

					joinrel->reltarget->exprs = lappend(joinrel->reltarget->exprs,
														phv);
					cost_qual_eval_node(&cost, (Node *) phv->phexpr, root);
					joinrel->reltarget->cost.startup += cost.startup;
					joinrel->reltarget->cost.per_tuple += cost.per_tuple;
					tuple_width += phinfo->ph_width;
				}
			}

			/*
			 * Also adjust joinrel's direct_lateral_relids to include the
			 * PHV's source rel(s).  We must do this even if we're not
			 * actually going to emit the PHV, otherwise join_is_legal() will
			 * reject valid join orderings.  (In principle maybe we could
			 * instead remove the joinrel's lateral_relids dependency; but
			 * that's complicated to get right, and cases where we're not
			 * going to emit the PHV are too rare to justify the work.)
			 *
			 * In principle we should only do this if the join doesn't yet
			 * include the PHV's source rel(s).  But our caller
			 * build_join_rel() will clean things up by removing the join's
			 * own relids from its direct_lateral_relids, so we needn't
			 * account for that here.
			 */
			joinrel->direct_lateral_relids =
				bms_add_members(joinrel->direct_lateral_relids,
								phinfo->ph_lateral);
		}
	}

	joinrel->reltarget->width = clamp_width_est(tuple_width);
}

/*
 * contain_placeholder_references_to
 *		Detect whether any PlaceHolderVars in the given clause contain
 *		references to the given relid (typically an OJ relid).
 *
 * "Contain" means that there's a use of the relid inside the PHV's
 * contained expression, so that changing the nullability status of
 * the rel might change what the PHV computes.
 *
 * The code here to cope with upper-level PHVs is likely dead, but keep it
 * anyway just in case.
 */
/*
 * contain_placeholder_references_to - (中文)判断给定子句中是否有 PHV 包含
 * 对指定 relid(通常是某个外连接的 relid)的引用
 *
 * 【作用】在规划阶段,当想知道"把某个外连接置空之后是否会改变该子句的
 * 计算结果"时使用:只要子句内某个 PHV 的内含表达式用到了 relid,答案
 * 就为真。典型调用者见外连接消除逻辑。
 *
 * 【设计思想】先快速判断:查询里根本没有 PHV(lastPHId == 0)直接返回
 * false。否则用 contain_placeholder_references_walker 递归扫描。对"同层"
 * PHV 只需检查其 phrels 是否包含 relid——phrels 已经概括了内含表达式
 * 引用的关系,不必再下钻 phexpr,也不必看 phnullingrels(那表示之后的外
 * 连接置空,不是内含引用)。处理上层查询(Query)时维护 sublevels_up。
 *
 * 【参数】
 *   root   —— 规划上下文;
 *   clause —— 待扫描的表达式;
 *   relid  —— 关心的关系 id。
 * 【返回值】true:子句中有 PHV 内含对该 relid 的引用;false:没有。
 */
bool
contain_placeholder_references_to(PlannerInfo *root, Node *clause,
								  int relid)
{
	contain_placeholder_references_context context;

	/* We can answer quickly in the common case that there's no PHVs at all */
	if (root->glob->lastPHId == 0)
		return false;
	/* Else run the recursive search */
	context.relid = relid;
	context.sublevels_up = 0;
	return contain_placeholder_references_walker(clause, &context);
}

/*
 * contain_placeholder_references_walker - (中文)
 * contain_placeholder_references_to 的递归遍历器
 *
 * 【作用】expression_tree_walker 风格的深度优先遍历:命中"同层"PHV 时,
 * 检查其 phrels 是否含目标 relid;遇到 Query 节点时递增 sublevels_up 递归
 * 其内部(处理 RTE 子查询或尚未规划的子链接子查询)。
 *
 * 【设计思想】对 PHV 只判断 phrels 而不下钻内含表达式,是刻意为之——
 * phrels 已足以概括表达式的引用关系。对跨层 PHV(phlevelsup !=
 * sublevels_up)直接放行(看作普通节点继续遍历)。处理上层 Query 的逻辑
 * 在单层规划中可能用不到,但保留以防万一。
 *
 * 【参数】
 *   node    —— 当前访问的节点;
 *   context —— 携带 relid 与当前 sublevels_up。
 * 【返回值】true 表示已发现目标引用(可提前终止遍历)。
 */
static bool
contain_placeholder_references_walker(Node *node,
									  contain_placeholder_references_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		/* We should just look through PHVs of other query levels */
		if (phv->phlevelsup == context->sublevels_up)
		{
			/* If phrels matches, we found what we came for */
			if (bms_is_member(context->relid, phv->phrels))
				return true;

			/*
			 * We should not examine phnullingrels: what we are looking for is
			 * references in the contained expression, not OJs that might null
			 * the result afterwards.  Also, we don't need to recurse into the
			 * contained expression, because phrels should adequately
			 * summarize what's in there.  So we're done here.
			 */
			return false;
		}
	}
	else if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node,
								   contain_placeholder_references_walker,
								   context,
								   0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, contain_placeholder_references_walker,
								  context);
}

/*
 * Compute the set of outer-join relids that can null a placeholder.
 *
 * This is analogous to RelOptInfo.nulling_relids for Vars, but we compute it
 * on-the-fly rather than saving it somewhere.  Currently the value is needed
 * at most once per query, so there's little value in doing otherwise.  If it
 * ever gains more widespread use, perhaps we should cache the result in
 * PlaceHolderInfo.
 */
/*
 * get_placeholder_nulling_relids - (中文)计算能够置空给定 PHV 的外连接
 * relid 集合
 *
 * 【作用】对 PHV 而言,任何在 ph_eval_at 之上、且能置空其任一组件的变量
 * 的外连接,都能影响该 PHV 最终结果。本函数算出"应该包含在 PHV 的
 * phnullingrels 里"的那些外连接,供外层在 PHV 被提升/复制时设置
 * nullingrels。
 *
 * 【设计思想】类比 Var 的 RelOptInfo.nulling_relids,但这里按需现场计算
 * 而非预存:因为目前每个查询最多用一次,不值得缓存。算法:对 ph_eval_at
 * 中每个基表 relid,取其 nulling_relids 求并;跳过 RTE_GROUP 的伪 RTE 与
 * 本身就是外连接占位的 relid(它们已在 outer_join_rels 中);最后去掉
 * 已包含在 ph_eval_at 中的外连接(那些在求值点之下,不会置空结果)。
 *
 * 【参数】
 *   root   —— 规划上下文;
 *   phinfo —— 目标 PlaceHolderInfo。
 * 【返回值】能置空该 PHV 的外连接 relid 位图。
 */
Relids
get_placeholder_nulling_relids(PlannerInfo *root, PlaceHolderInfo *phinfo)
{
	Relids		result = NULL;
	int			relid = -1;

	/*
	 * Form the union of all potential nulling OJs for each baserel included
	 * in ph_eval_at.
	 */
	while ((relid = bms_next_member(phinfo->ph_eval_at, relid)) > 0)
	{
		RelOptInfo *rel = root->simple_rel_array[relid];

		/* ignore the RTE_GROUP RTE */
		if (relid == root->group_rtindex)
			continue;

		if (rel == NULL)		/* must be an outer join */
		{
			Assert(bms_is_member(relid, root->outer_join_rels));
			continue;
		}
		result = bms_add_members(result, rel->nulling_relids);
	}

	/* Now remove any OJs already included in ph_eval_at, and we're done. */
	result = bms_del_members(result, phinfo->ph_eval_at);
	return result;
}

/*
 * strip_noop_phvs
 *	  Strip no-op PlaceHolderVar nodes from the given expression tree.
 *
 * A PlaceHolderVar that is not marked as nullable (i.e., its phnullingrels
 * is empty) is effectively a no-op when it appears in a relation-scan-level
 * expression.  This function strips such PlaceHolderVars, which is useful
 * for matching expressions to index keys or partition keys in cases where
 * the expression has been wrapped in PlaceHolderVars during subquery pullup.
 *
 * IMPORTANT: the caller must ensure that the expression is a scan-level
 * expression, so that non-nullable PlaceHolderVars in it are indeed no-ops.
 *
 * The removal is performed recursively because PlaceHolderVars can be nested
 * or interleaved with other node types.  We must peel back all layers to
 * expose the base expression.
 *
 * As a performance optimization, we first use a lightweight walker to check
 * for the presence of strippable PlaceHolderVars.  The expensive mutator is
 * invoked only if a candidate is found, avoiding unnecessary memory allocation
 * and tree copying in the common case where no PlaceHolderVars are present.
 */
/*
 * strip_noop_phvs - (中文)从表达式树中剥掉"无操作"的 PlaceHolderVar
 *
 * 【作用】在扫描层表达式(如索引键、分区键匹配)中,未被标记为可置空
 * (phnullingrels 为空)的 PHV 其实是个空转包装——它不改变计算结果。本
 * 函数把这类 PHV 替换为其内含表达式,使底层表达式"露出真容",便于与
 * 索引键/分区键比对。子查询上拉时会把表达式包进 PHV,故需要此清理。
 *
 * 【设计思想】重要前提:调用者必须保证该表达式确为扫描层表达式,否则
 * 这些 PHV 并非空转,不可剥除。剥离是递归的(PHV 可嵌套或与其他节点交
 * 错),须剥到最底层。性能优化:先跑轻量的 contain_noop_phv_walker 探测
 * 是否存在可剥 PHV,没有则原样返回节点(避免无谓的复制/内存分配);只有
 * 命中才调用耗时的 strip_noop_phvs_mutator。
 *
 * 【参数】node —— 待处理的表达式树。
 * 【返回值】剥除后(或原样)的表达式树。
 */
Node *
strip_noop_phvs(Node *node)
{
	/* Don't mutate/copy if no target PHVs exist */
	if (!contain_noop_phv_walker(node, NULL))
		return node;

	return strip_noop_phvs_mutator(node, NULL);
}

/*
 * contain_noop_phv_walker
 *	  Detect if there are any PlaceHolderVars in the tree that are candidates
 *	  for stripping.
 *
 * We identify a PlaceHolderVar as strippable only if its phnullingrels is
 * empty.
 */
/*
 * contain_noop_phv_walker - (中文)探测树中是否存在可剥离的 PHV
 *
 * 【作用】strip_noop_phvs 的快速预检:只要发现一个 phnullingrels 为空的
 * PHV 就返回 true,让上层决定是否进入代价较高的 mutator。
 *
 * 【设计思想】判定标准与 strip_noop_phvs_mutator 完全一致(空 nullingrels
 * 才可剥),保证预检与执行不会出现偏差。用 expression_tree_walker 遍历,
 * 命中即短路返回。
 *
 * 【参数】
 *   node    —— 当前访问节点;
 *   context —— 未使用,预留。
 * 【返回值】true:存在可剥离的 PHV;false:不存在。
 */
static bool
contain_noop_phv_walker(Node *node, void *context)
{
	if (node == NULL)
		return false;

	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (bms_is_empty(phv->phnullingrels))
			return true;
	}

	return expression_tree_walker(node, contain_noop_phv_walker,
								  context);
}

/*
 * strip_noop_phvs_mutator
 *	  Recursively remove PlaceHolderVars that are not marked nullable.
 *
 * We strip a PlaceHolderVar only if its phnullingrels is empty, replacing it
 * with its contained expression.
 */
/*
 * strip_noop_phvs_mutator - (中文)递归地从树中移除可剥离的 PHV
 *
 * 【作用】strip_noop_phvs 的真正执行者:遍历整棵表达式树,遇到
 * phnullingrels 为空的 PHV 就返回其内含表达式(并继续递归处理之),否则
 * 保留该 PHV 但继续检查其内部;其他节点照常交给 expression_tree_mutator
 * 深拷贝重建。
 *
 * 【设计思想】以"替换为内含表达式"的方式实现"剥离",天然支持 PHV 嵌套
 * 与多层包裹的情形;递归发生在替换位置,保证底层表达式也被清理。
 *
 * 【参数】
 *   node    —— 当前访问节点;
 *   context —— 未使用,预留。
 * 【返回值】处理后的节点(可能为 NULL,若输入为 NULL)。
 */
static Node *
strip_noop_phvs_mutator(Node *node, void *context)
{
	if (node == NULL)
		return NULL;

	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (bms_is_empty(phv->phnullingrels))
		{
			/* Recurse on its contained expression */
			return strip_noop_phvs_mutator((Node *) phv->phexpr,
										   context);
		}

		/* Otherwise, keep this PHV but check its contained expression */
	}

	return expression_tree_mutator(node, strip_noop_phvs_mutator,
								   context);
}
