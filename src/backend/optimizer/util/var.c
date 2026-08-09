/*-------------------------------------------------------------------------
 *
 * var.c
 *	  Var node manipulation routines
 *
 * Note: for most purposes, PlaceHolderVar is considered a Var too,
 * even if its contained expression is variable-free.  Also, CurrentOfExpr
 * is treated as a Var for purposes of determining whether an expression
 * contains variables.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件提供对表达式树中 Var(列引用)节点的查找与操纵例程,是规划器
 * 最基础的表达式分析工具库:找出表达式引用了哪些关系/哪些列、判断是否
 * 含某层引用、把引用 join 别名/分组输出的 Var 展开回底层表达式等。大部分
 * 函数由其它模块(如 pullup、prepjointree、prepunion)在表达式预处理阶段
 * 调用。
 *
 * 【核心概念】
 * - Var 的 varlevelsup 表示它引用的查询层相对深度(0 = 当前层);
 * - 本模块多数"查找"函数把 PlaceHolderVar 视同 Var(它代表一个待求值
 *   子表达式),CurrentOfExpr 在"是否含变量"判断中也视为 Var;
 * - 对"未规划"的表达式,可能见到裸 SubLink,需要递归进子查询;已规划的
 *   SubPlan 则只需看其参数,两种形态在 walker 中区别处理;
 * - nullingrels(outer join 的可空性位图)作为 Var 的一部分被一并收集、
 *   传递,保证外连接语义在展开别名/分组表达式时不丢失。
 *
 * 【按用途分组的函数】
 * - 关系集合收集:pull_varnos / pull_varnos_of_level / pull_varnos_walker
 *   (varno 位图)、pull_varattnos(pull_varattnos_walker,某关系的列号位图,
 *   系统列以 FirstLowInvalidHeapAttributeNumber 偏移)、pull_vars_of_level
 *   (Var 节点列表);
 * - 存在性判断:contain_var_clause、contain_vars_of_level、
 *   contain_vars_returning_old_or_new(均配 walker);
 * - 定位:locate_var_of_level 返回命中 Var 的源码位置(用于报错);
 * - 按 flag 抽取: pull_var_clause 按 PVC_* 标志把 Aggref/WindowFunc/
 *   PlaceHolderVar 分进结果或递归进其参数(不存在的形态直接报错);
 * - 展开替身表达式:flatten_join_alias_vars(把引用 JOIN 输出的 Var 展开成
 *   底层 base + OJ 关系表达式,并传播 varnullingrels)、
 *   flatten_join_alias_for_parser(解析器专用,无 root)、
 *   flatten_group_exprs(展开引用 GROUP 输出的 Var),配套的 mutator 与
 *   mark_nullable_by_grouping / add_nullingrels_if_needed /
 *   is_standard_join_alias_expression / adjust_standard_join_alias_expression /
 *   alias_relid_set 处理 nullingrel 的传播与 PHV 包装。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/var.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/sysattr.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/placeholder.h"
#include "optimizer/prep.h"
#include "parser/parsetree.h"
#include "rewrite/rewriteManip.h"


typedef struct
{
	Relids		varnos;
	PlannerInfo *root;
	int			sublevels_up;
} pull_varnos_context;

typedef struct
{
	Bitmapset  *varattnos;
	Index		varno;
} pull_varattnos_context;

typedef struct
{
	List	   *vars;
	int			sublevels_up;
} pull_vars_context;

typedef struct
{
	int			var_location;
	int			sublevels_up;
} locate_var_of_level_context;

typedef struct
{
	List	   *varlist;
	int			flags;
} pull_var_clause_context;

typedef struct
{
	PlannerInfo *root;			/* could be NULL! */
	Query	   *query;			/* outer Query */
	int			sublevels_up;
	bool		possible_sublink;	/* could aliases include a SubLink? */
	bool		inserted_sublink;	/* have we inserted a SubLink? */
} flatten_join_alias_vars_context;

static bool pull_varnos_walker(Node *node,
							   pull_varnos_context *context);
static bool pull_varattnos_walker(Node *node, pull_varattnos_context *context);
static bool pull_vars_walker(Node *node, pull_vars_context *context);
static bool contain_var_clause_walker(Node *node, void *context);
static bool contain_vars_of_level_walker(Node *node, int *sublevels_up);
static bool contain_vars_returning_old_or_new_walker(Node *node, void *context);
static bool locate_var_of_level_walker(Node *node,
									   locate_var_of_level_context *context);
static bool pull_var_clause_walker(Node *node,
								   pull_var_clause_context *context);
static Node *flatten_join_alias_vars_mutator(Node *node,
											 flatten_join_alias_vars_context *context);
static Node *flatten_group_exprs_mutator(Node *node,
										 flatten_join_alias_vars_context *context);
static Node *mark_nullable_by_grouping(PlannerInfo *root, Node *newnode,
									   Var *oldvar);
static Node *add_nullingrels_if_needed(PlannerInfo *root, Node *newnode,
									   Var *oldvar);
static bool is_standard_join_alias_expression(Node *newnode, Var *oldvar);
static void adjust_standard_join_alias_expression(Node *newnode, Var *oldvar);
static Relids alias_relid_set(Query *query, Relids relids);


/*
 * pull_varnos
 *		Create a set of all the distinct varnos present in a parsetree.
 *		Only varnos that reference level-zero rtable entries are considered.
 *
 * The result includes outer-join relids mentioned in Var.varnullingrels and
 * PlaceHolderVar.phnullingrels fields in the parsetree.
 *
 * "root" can be passed as NULL if it is not necessary to process
 * PlaceHolderVars.
 *
 * NOTE: this is used on not-yet-planned expressions.  It may therefore find
 * bare SubLinks, and if so it needs to recurse into them to look for uplevel
 * references to the desired rtable level!	But when we find a completed
 * SubPlan, we only need to look at the parameters passed to the subplan.
 */
/*
 * pull_varnos - (中文)收集表达式引用的全部 varno 集合
 *
 * 【作用】遍历 node(可为 Query 或裸表达式),收集所有"引用第 0 层 rtable"
 * 的 Var 的 varno,以位图形式返回。还会把 Var.varnullingrels 与
 * PlaceHolderVar.phnullingrels 中的外连接 relid 一并并入结果。root 可传
 * NULL,表示无需处理 PlaceHolderVar。
 *
 * 【设计思想】委托 query_or_expression_tree_walker + pull_varnos_walker。
 * "当前层"为第 0 层;进入子查询(Query 节点)时递增 sublevels_up,使上层
 * 引用仍能被识别。这是规划期最常用的"这组表达式依赖哪些关系"查询,如
 * 计算 RestrictInfo 的 required_relids。
 *
 * 【参数】
 *   root —— 规划上下文(可为 NULL,仅 PHV 处理需要);node —— 待分析的树。
 * 【返回值】varno 位图(NULL 表示空集)。
 */
Relids
pull_varnos(PlannerInfo *root, Node *node)
{
	pull_varnos_context context;

	context.varnos = NULL;
	context.root = root;
	context.sublevels_up = 0;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	query_or_expression_tree_walker(node,
									pull_varnos_walker,
									&context,
									0);

	return context.varnos;
}

/*
 * pull_varnos_of_level
 *		Create a set of all the distinct varnos present in a parsetree.
 *		Only Vars of the specified level are considered.
 */
/*
 * pull_varnos_of_level - (中文)收集指定查询层的 varno 集合
 *
 * 【作用】pull_varnos 的变体:只收集 varlevelsup == levelsup 的 Var 的
 * varno(以及它们的 varnullingrels)。用于在展开别名/分组表达式时,判断
 * 替换后的表达式引用了哪些关系、是否仍是变量无关的。
 *
 * 【设计思想】把 context.sublevels_up 初始化为 levelsup,其余逻辑与
 * pull_varnos 相同。
 *
 * 【参数】
 *   root     —— 规划上下文(可为 NULL);node —— 待分析的树;
 *   levelsup —— 目标查询层深度(0 = 当前层)。
 * 【返回值】varno 位图。
 */
Relids
pull_varnos_of_level(PlannerInfo *root, Node *node, int levelsup)
{
	pull_varnos_context context;

	context.varnos = NULL;
	context.root = root;
	context.sublevels_up = levelsup;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	query_or_expression_tree_walker(node,
									pull_varnos_walker,
									&context,
									0);

	return context.varnos;
}

/*
 * pull_varnos_walker - (中文)pull_varnos 系列的递归遍历器
 *
 * 【作用】递归遍历节点树,把当前层 Var 的 varno、varnullingrels 以及
 * PlaceHolderVar 的求值关系/可空性关系并入 context->varnos;进入子查询
 * 时调整 sublevels_up。返回 true 表示中止遍历(本实现从不中止)。
 *
 * 【设计思想】关键分支:
 * - Var:varlevelsup 等于当前层才收集,否则说明是上层引用,跳过;
 * - CurrentOfExpr:第 0 层时收集 cvarno;
 * - PlaceHolderVar:仅当 phlevelsup == 当前层 且提供了 root 时收集。收集
 *   范围优先取 PlaceHolderInfo.ph_eval_at(求值位置),找不到对应 PHI 时
 *   退化为 phrels(保守);若 PHV 是 appendrel 翻译产物(phrels 与 PHI 的
 *   ph_var->phrels 不一致),需把 ph_eval_at 沿同样的"删减/增补"换算;三种
 *   情况后都要并入 phnullingrels。phlevelsup 不匹配或 root 为 NULL 时,则
 *   继续递归其内部表达式,看是否有当前层的 Var;
 * - Query:进入子查询/未规划 SubLink 子查询,sublevels_up++ 后递归,结束
 *   恢复(注意 varlevelsup 恰是以"进入子查询的深度"计数的)。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 携带 varnos、root、sublevels_up。
 * 【返回值】false(永不中止)。
 */
static bool
pull_varnos_walker(Node *node, pull_varnos_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup == context->sublevels_up)
		{
			context->varnos = bms_add_member(context->varnos, var->varno);
			context->varnos = bms_add_members(context->varnos,
											  var->varnullingrels);
		}
		return false;
	}
	if (IsA(node, CurrentOfExpr))
	{
		CurrentOfExpr *cexpr = (CurrentOfExpr *) node;

		if (context->sublevels_up == 0)
			context->varnos = bms_add_member(context->varnos, cexpr->cvarno);
		return false;
	}
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		/*
		 * If a PlaceHolderVar is not of the target query level, ignore it,
		 * instead recursing into its expression to see if it contains any
		 * vars that are of the target level.  We'll also do that when the
		 * caller doesn't pass a "root" pointer.  (We probably shouldn't see
		 * PlaceHolderVars at all in such cases, but if we do, this is a
		 * reasonable behavior.)
		 */
		if (phv->phlevelsup == context->sublevels_up &&
			context->root != NULL)
		{
			/*
			 * Ideally, the PHV's contribution to context->varnos is its
			 * ph_eval_at set.  However, this code can be invoked before
			 * that's been computed.  If we cannot find a PlaceHolderInfo,
			 * fall back to the conservative assumption that the PHV will be
			 * evaluated at its syntactic level (phv->phrels).
			 *
			 * Another problem is that a PlaceHolderVar can appear in quals or
			 * tlists that have been translated for use in a child appendrel.
			 * Typically such a PHV is a parameter expression sourced by some
			 * other relation, so that the translation from parent appendrel
			 * to child doesn't change its phrels, and we should still take
			 * ph_eval_at at face value.  But in corner cases, the PHV's
			 * original phrels can include the parent appendrel itself, in
			 * which case the translated PHV will have the child appendrel in
			 * phrels, and we must translate ph_eval_at to match.
			 */
			PlaceHolderInfo *phinfo = NULL;

			if (phv->phlevelsup == 0)
			{
				if (phv->phid < context->root->placeholder_array_size)
					phinfo = context->root->placeholder_array[phv->phid];
			}
			if (phinfo == NULL)
			{
				/* No PlaceHolderInfo yet, use phrels */
				context->varnos = bms_add_members(context->varnos,
												  phv->phrels);
			}
			else if (bms_equal(phv->phrels, phinfo->ph_var->phrels))
			{
				/* Normal case: use ph_eval_at */
				context->varnos = bms_add_members(context->varnos,
												  phinfo->ph_eval_at);
			}
			else
			{
				/* Translated PlaceHolderVar: translate ph_eval_at to match */
				Relids		newevalat,
							delta;

				/* remove what was removed from phv->phrels ... */
				delta = bms_difference(phinfo->ph_var->phrels, phv->phrels);
				newevalat = bms_difference(phinfo->ph_eval_at, delta);
				/* ... then if that was in fact part of ph_eval_at ... */
				if (!bms_equal(newevalat, phinfo->ph_eval_at))
				{
					/* ... add what was added */
					delta = bms_difference(phv->phrels, phinfo->ph_var->phrels);
					newevalat = bms_join(newevalat, delta);
				}
				context->varnos = bms_join(context->varnos,
										   newevalat);
			}

			/*
			 * In all three cases, include phnullingrels in the result.  We
			 * don't worry about possibly needing to translate it, because
			 * appendrels only translate varnos of baserels, not outer joins.
			 */
			context->varnos = bms_add_members(context->varnos,
											  phv->phnullingrels);
			return false;		/* don't recurse into expression */
		}
	}
	else if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node, pull_varnos_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, pull_varnos_walker, context);
}


/*
 * pull_varattnos
 *		Find all the distinct attribute numbers present in an expression tree,
 *		and add them to the initial contents of *varattnos.
 *		Only Vars of the given varno and rtable level zero are considered.
 *
 * Attribute numbers are offset by FirstLowInvalidHeapAttributeNumber so that
 * we can include system attributes (e.g., OID) in the bitmap representation.
 *
 * Currently, this does not support unplanned subqueries; that is not needed
 * for current uses.  It will handle already-planned SubPlan nodes, though,
 * looking into only the "testexpr" and the "args" list.  (The subplan cannot
 * contain any other references to Vars of the current level.)
 */
/*
 * pull_varattnos - (中文)收集某关系被表达式引用的全部列号
 *
 * 【作用】在 node 中找出所有"varno 等于 varno 且 varlevelsup == 0"的 Var,
 * 把它们的 varattno 加入 *varattnos 位图(与已有内容合并)。用于判断某个
 * 关系在查询里到底用了哪些列,如收集"UPDATE 需要读哪些列"或生成列依赖。
 *
 * 【设计思想】列号以 FirstLowInvalidHeapAttributeNumber 为偏移存入位图,
 * 使系统列(负 attno)也能表示。列号本身就是位图下标,因此 varattno 直接
 * 减偏移即得。不支持未规划的子查询(断言不会出现 Query),已规划的 SubPlan
 * 会按其 testexpr 与 args 递归(子计划不能再引用当前层 Var,故其它字段
 * 无需检查)。
 *
 * 【参数】
 *   node      —— 待分析的表达式树;
 *   varno     —— 关注的关系 varno;
 *   varattnos —— 输入输出的列号位图(就地累积)。
 * 【返回值】无(结果通过 varattnos 返回)。
 */
void
pull_varattnos(Node *node, Index varno, Bitmapset **varattnos)
{
	pull_varattnos_context context;

	context.varattnos = *varattnos;
	context.varno = varno;

	(void) pull_varattnos_walker(node, &context);

	*varattnos = context.varattnos;
}

/*
 * pull_varattnos_walker - (中文)pull_varattnos 的递归遍历器
 *
 * 【作用】对命中条件的 Var 把 varattno(减 FirstLowInvalidHeapAttributeNumber
 * 偏移)加入 context->varattnos;其余节点继续递归。
 *
 * 【设计思想】仅当 varno 与 varlevelsup 同时匹配才算;遇到 Query 直接断言
 * (本函数不支持未规划子查询)。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 携带 varattnos 与 varno。
 * 【返回值】false(永不中止)。
 */
static bool
pull_varattnos_walker(Node *node, pull_varattnos_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varno == context->varno && var->varlevelsup == 0)
			context->varattnos =
				bms_add_member(context->varattnos,
							   var->varattno - FirstLowInvalidHeapAttributeNumber);
		return false;
	}

	/* Should not find an unplanned subquery */
	Assert(!IsA(node, Query));

	return expression_tree_walker(node, pull_varattnos_walker, context);
}


/*
 * pull_vars_of_level
 *		Create a list of all Vars (and PlaceHolderVars) referencing the
 *		specified query level in the given parsetree.
 *
 * Caution: the Vars are not copied, only linked into the list.
 */
/*
 * pull_vars_of_level - (中文)收集指定查询层的 Var 节点列表
 *
 * 【作用】遍历 node,把所有 varlevelsup == levelsup 的 Var(以及 phlevelsup
 * 相同的 PlaceHolderVar)收进 List 返回。与 pull_varnos 不同,这里返回的是
 * 节点本身而非去重的 varno 位图,适合需要逐个 Var 细节的场合。
 *
 * 【设计思想】PlaceHolderVar 只收集自身、不深入其内部表达式(内含表达式由
 * 别的机制处理);Query 子查询按层递归。节点未拷贝(警告:只链接)。
 *
 * 【参数】
 *   node    —— 待分析的树;levelsup —— 目标查询层深度。
 * 【返回值】Var/PlaceHolderVar 节点列表。
 */
List *
pull_vars_of_level(Node *node, int levelsup)
{
	pull_vars_context context;

	context.vars = NIL;
	context.sublevels_up = levelsup;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	query_or_expression_tree_walker(node,
									pull_vars_walker,
									&context,
									0);

	return context.vars;
}

/*
 * pull_vars_walker - (中文)pull_vars_of_level 的递归遍历器
 *
 * 【作用】命中当前层条件的 Var 或 PlaceHolderVar 加入 context->vars,PHV
 * 不深入其表达式;Query 子查询层数递增后递归。
 *
 * 【设计思想】与 pull_varnos_walker 的分层计数方式一致,只是输出是列表
 * 而非位图。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 携带 vars 与 sublevels_up。
 * 【返回值】false(永不中止)。
 */
static bool
pull_vars_walker(Node *node, pull_vars_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup == context->sublevels_up)
			context->vars = lappend(context->vars, var);
		return false;
	}
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (phv->phlevelsup == context->sublevels_up)
			context->vars = lappend(context->vars, phv);
		/* we don't want to look into the contained expression */
		return false;
	}
	if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node, pull_vars_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, pull_vars_walker, context);
}


/*
 * contain_var_clause
 *	  Recursively scan a clause to discover whether it contains any Var nodes
 *	  (of the current query level).
 *
 *	  Returns true if any varnode found.
 *
 * Does not examine subqueries, therefore must only be used after reduction
 * of sublinks to subplans!
 */
/*
 * contain_var_clause - (中文)判断表达式是否含当前层的 Var
 *
 * 【作用】扫描 node,只要发现任意 varlevelsup == 0 的 Var、任何
 * CurrentOfExpr、或 phlevelsup == 0 的 PlaceHolderVar 即返回 true。用于
 * 判断某子句是否需要关系数据(如判断伪常量、判断子查询是否可下推等)。
 *
 * 【设计思想】利用 walker 的 true 返回值"中止遍历"提前退出。PHV 若 phlevelsup
 * 为 0 直接算命中;为其它层则继续查其内部表达式。注意:本函数不进入子查询,
 * 只能在 sublink 已被改写为 subplan 之后使用。
 *
 * 【参数】node —— 待分析的表达式。
 * 【返回值】含当前层 Var(或等价物)返回 true。
 */
bool
contain_var_clause(Node *node)
{
	return contain_var_clause_walker(node, NULL);
}

/*
 * contain_var_clause_walker - (中文)contain_var_clause 的递归遍历器
 *
 * 【作用】命中当前层 Var / CurrentOfExpr / 当前层 PHV 时返回 true 中止;
 * 否则继续递归。
 *
 * 【设计思想】CurrentOfExpr 无条件算命中(它永远引用某游标关系);PHV
 * 仅 phlevelsup == 0 算命中,否则进入其表达式。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 未使用。
 * 【返回值】true 表示命中并中止遍历,false 继续。
 */
static bool
contain_var_clause_walker(Node *node, void *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		if (((Var *) node)->varlevelsup == 0)
			return true;		/* abort the tree traversal and return true */
		return false;
	}
	if (IsA(node, CurrentOfExpr))
		return true;
	if (IsA(node, PlaceHolderVar))
	{
		if (((PlaceHolderVar *) node)->phlevelsup == 0)
			return true;		/* abort the tree traversal and return true */
		/* else fall through to check the contained expr */
	}
	return expression_tree_walker(node, contain_var_clause_walker, context);
}


/*
 * contain_vars_of_level
 *	  Recursively scan a clause to discover whether it contains any Var nodes
 *	  of the specified query level.
 *
 *	  Returns true if any such Var found.
 *
 * Will recurse into sublinks.  Also, may be invoked directly on a Query.
 */
/*
 * contain_vars_of_level - (中文)判断表达式是否含指定层的 Var
 *
 * 【作用】扫描 node,发现任意 varlevelsup == levelsup 的 Var、第 0 层的
 * CurrentOfExpr、或 phlevelsup 匹配的 PlaceHolderVar 即返回 true。与
 * contain_var_clause 不同,本函数会递归进 sublink(未规划形态),且可直接
 * 作用于 Query。
 *
 * 【设计思想】用 query_or_expression_tree_walker 保证"以 Query 或裸表达式
 * 起始"两种形态下层级计数一致;sublevels_up 以指针方式贯穿遍历,进入
 * Query 时递增、退出恢复。返回 true 即中止。
 *
 * 【参数】
 *   node    —— 待分析的树;levelsup —— 目标查询层深度。
 * 【返回值】含该层 Var 返回 true。
 */
bool
contain_vars_of_level(Node *node, int levelsup)
{
	int			sublevels_up = levelsup;

	return query_or_expression_tree_walker(node,
										   contain_vars_of_level_walker,
										   &sublevels_up,
										   0);
}

/*
 * contain_vars_of_level_walker - (中文)contain_vars_of_level 的递归遍历器
 *
 * 【作用】命中指定层 Var / CurrentOfExpr(第 0 层)/ 指定层 PHV 时返回 true
 * 中止;Query 节点递归进子查询并调整层级计数。
 *
 * 【设计思想】与 pull_varnos_walker 的计数方式一致;CurrentOfExpr 只在
 * 第 0 层算命中(游标引用没有层级概念)。
 *
 * 【参数】
 *   node          —— 当前节点;sublevels_up —— 指向当前层计数的指针。
 * 【返回值】true 表示命中并中止。
 */
static bool
contain_vars_of_level_walker(Node *node, int *sublevels_up)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		if (((Var *) node)->varlevelsup == *sublevels_up)
			return true;		/* abort tree traversal and return true */
		return false;
	}
	if (IsA(node, CurrentOfExpr))
	{
		if (*sublevels_up == 0)
			return true;
		return false;
	}
	if (IsA(node, PlaceHolderVar))
	{
		if (((PlaceHolderVar *) node)->phlevelsup == *sublevels_up)
			return true;		/* abort the tree traversal and return true */
		/* else fall through to check the contained expr */
	}
	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		(*sublevels_up)++;
		result = query_tree_walker((Query *) node,
								   contain_vars_of_level_walker,
								   sublevels_up,
								   0);
		(*sublevels_up)--;
		return result;
	}
	return expression_tree_walker(node,
								  contain_vars_of_level_walker,
								  sublevels_up);
}


/*
 * contain_vars_returning_old_or_new
 *	  Recursively scan a clause to discover whether it contains any Var nodes
 *	  (of the current query level) whose varreturningtype is VAR_RETURNING_OLD
 *	  or VAR_RETURNING_NEW.
 *
 *	  Returns true if any found.
 *
 * Any ReturningExprs are also detected --- if an OLD/NEW Var was rewritten,
 * we still regard this as a clause that returns OLD/NEW values.
 *
 * Does not examine subqueries, therefore must only be used after reduction
 * of sublinks to subplans!
 */
/*
 * contain_vars_returning_old_or_new - (中文)判断表达式是否引用 OLD/NEW 值
 *
 * 【作用】扫描 node,发现任意 varlevelsup == 0 且 varreturningtype 为
 * VAR_RETURNING_OLD / VAR_RETURNING_NEW 的 Var,或 retlevelsup == 0 的
 * ReturningExpr,即返回 true。用于触发器/规则重写后的表达式处理,判断某
 * 表达式是否依赖行的旧值或新值。
 *
 * 【设计思想】OLD/NEW 的 Var 经过改写后可能包在 ReturningExpr 里,因此
 * 两者都要检查;命中即中止。不进入子查询(须在 sublink→subplan 之后用)。
 *
 * 【参数】node —— 待分析的表达式。
 * 【返回值】含 OLD/NEW 引用返回 true。
 */
bool
contain_vars_returning_old_or_new(Node *node)
{
	return contain_vars_returning_old_or_new_walker(node, NULL);
}

/*
 * contain_vars_returning_old_or_new_walker - (中文)其遍历器
 *
 * 【作用】对命中"当前层 OLD/NEW Var"或"当前层 ReturningExpr"的节点返回
 * true 中止,否则递归。
 *
 * 【设计思想】ReturningExpr 的 retlevelsup 语义与 Var.varlevelsup 对应;
 * 二者其一命中即认为表达式含 OLD/NEW 值。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 未使用。
 * 【返回值】true 表示命中并中止。
 */
static bool
contain_vars_returning_old_or_new_walker(Node *node, void *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		if (((Var *) node)->varlevelsup == 0 &&
			((Var *) node)->varreturningtype != VAR_RETURNING_DEFAULT)
			return true;		/* abort the tree traversal and return true */
		return false;
	}
	if (IsA(node, ReturningExpr))
	{
		if (((ReturningExpr *) node)->retlevelsup == 0)
			return true;		/* abort the tree traversal and return true */
		return false;
	}
	return expression_tree_walker(node, contain_vars_returning_old_or_new_walker,
								  context);
}


/*
 * locate_var_of_level
 *	  Find the parse location of any Var of the specified query level.
 *
 * Returns -1 if no such Var is in the querytree, or if they all have
 * unknown parse location.  (The former case is probably caller error,
 * but we don't bother to distinguish it from the latter case.)
 *
 * Will recurse into sublinks.  Also, may be invoked directly on a Query.
 *
 * Note: it might seem appropriate to merge this functionality into
 * contain_vars_of_level, but that would complicate that function's API.
 * Currently, the only uses of this function are for error reporting,
 * and so shaving cycles probably isn't very important.
 */
/*
 * locate_var_of_level - (中文)定位指定层 Var 的源码位置
 *
 * 【作用】返回 node 中第一个"varlevelsup == levelsup 且带合法 location"的
 * Var 的解析位置(用于给用户报错时指出出错列);找不到或全部 location 未知
 * 时返回 -1。
 *
 * 【设计思想】walker 命中即中止并保存 location。CurrentOfExpr 不携带位置
 * 信息,直接跳过;PlaceHolderVar 无需特殊处理,查其内部表达式即可。可递归
 * 进 sublink 与 Query。
 *
 * 【参数】
 *   node    —— 待分析的树;levelsup —— 目标查询层深度。
 * 【返回值】命中的 Var.location,或 -1。
 */
int
locate_var_of_level(Node *node, int levelsup)
{
	locate_var_of_level_context context;

	context.var_location = -1;	/* in case we find nothing */
	context.sublevels_up = levelsup;

	(void) query_or_expression_tree_walker(node,
										   locate_var_of_level_walker,
										   &context,
										   0);

	return context.var_location;
}

/*
 * locate_var_of_level_walker - (中文)locate_var_of_level 的递归遍历器
 *
 * 【作用】命中指定层且 location >= 0 的 Var 时记录位置并返回 true 中止;
 * 否则递归,进入子查询时调整层级计数。
 *
 * 【设计思想】要求 location >= 0(语法树节点多数带有),-1 表示"未知位置",
 * 此时继续找更深的命中,保证优先返回有意义的报错位置。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 携带 var_location 与 sublevels_up。
 * 【返回值】true 表示已找到并中止。
 */
static bool
locate_var_of_level_walker(Node *node,
						   locate_var_of_level_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup == context->sublevels_up &&
			var->location >= 0)
		{
			context->var_location = var->location;
			return true;		/* abort tree traversal and return true */
		}
		return false;
	}
	if (IsA(node, CurrentOfExpr))
	{
		/* since CurrentOfExpr doesn't carry location, nothing we can do */
		return false;
	}
	/* No extra code needed for PlaceHolderVar; just look in contained expr */
	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node,
								   locate_var_of_level_walker,
								   context,
								   0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node,
								  locate_var_of_level_walker,
								  context);
}


/*
 * pull_var_clause
 *	  Recursively pulls all Var nodes from an expression clause.
 *
 *	  Aggrefs are handled according to these bits in 'flags':
 *		PVC_INCLUDE_AGGREGATES		include Aggrefs in output list
 *		PVC_RECURSE_AGGREGATES		recurse into Aggref arguments
 *		neither flag				throw error if Aggref found
 *	  Vars within an Aggref's expression are included in the result only
 *	  when PVC_RECURSE_AGGREGATES is specified.
 *
 *	  WindowFuncs are handled according to these bits in 'flags':
 *		PVC_INCLUDE_WINDOWFUNCS		include WindowFuncs in output list
 *		PVC_RECURSE_WINDOWFUNCS		recurse into WindowFunc arguments
 *		neither flag				throw error if WindowFunc found
 *	  Vars within a WindowFunc's expression are included in the result only
 *	  when PVC_RECURSE_WINDOWFUNCS is specified.
 *
 *	  PlaceHolderVars are handled according to these bits in 'flags':
 *		PVC_INCLUDE_PLACEHOLDERS	include PlaceHolderVars in output list
 *		PVC_RECURSE_PLACEHOLDERS	recurse into PlaceHolderVar arguments
 *		neither flag				throw error if PlaceHolderVar found
 *	  Vars within a PHV's expression are included in the result only
 *	  when PVC_RECURSE_PLACEHOLDERS is specified.
 *
 *	  GroupingFuncs are treated exactly like Aggrefs, and so do not need
 *	  their own flag bits.
 *
 *	  CurrentOfExpr nodes are ignored in all cases.
 *
 *	  Upper-level vars (with varlevelsup > 0) should not be seen here,
 *	  likewise for upper-level Aggrefs and PlaceHolderVars.
 *
 *	  Returns list of nodes found.  Note the nodes themselves are not
 *	  copied, only referenced.
 *
 * Does not examine subqueries, therefore must only be used after reduction
 * of sublinks to subplans!
 */
/*
 * pull_var_clause - (中文)按标志抽取表达式中的 Var / Aggref / WindowFunc / PHV
 *
 * 【作用】遍历 node,把遇到的 Var、Aggref、GroupingFunc、WindowFunc、
 * PlaceHolderVar 按 flags 指定的策略收集成 List 返回。节点未拷贝、仅引用。
 *
 * 【设计思想】flags 对每类节点给出三种互斥策略:
 * - PVC_INCLUDE_*:把该节点原样收进结果,不深入其参数(参数里的 Var 不计);
 * - PVC_RECURSE_*:不收节点本身,但递归进其参数收集参数中的 Var;
 * - 两者皆无:遇到该节点直接报错。
 * 用断言保证 INCLUDE 与 RECURSE 不同时指定(冲突无意义)。组内一致性:
 * GroupingFunc 完全按 Aggref 处理(共用 PVC_*_AGGREGATES 位);CurrentOfExpr
 * 一律忽略;上层引用(levelsup > 0)视为调用方错误而 elog。典型用途:路径
 * 目标/限制条件中的 Var 抽取、判断子句是否含聚合等。
 *
 * 【参数】
 *   node  —— 待分析的表达式;
 *   flags —— PVC_* 位的组合。
 * 【返回值】收集到的节点列表。
 */
List *
pull_var_clause(Node *node, int flags)
{
	pull_var_clause_context context;

	/* Assert that caller has not specified inconsistent flags */
	Assert((flags & (PVC_INCLUDE_AGGREGATES | PVC_RECURSE_AGGREGATES))
		   != (PVC_INCLUDE_AGGREGATES | PVC_RECURSE_AGGREGATES));
	Assert((flags & (PVC_INCLUDE_WINDOWFUNCS | PVC_RECURSE_WINDOWFUNCS))
		   != (PVC_INCLUDE_WINDOWFUNCS | PVC_RECURSE_WINDOWFUNCS));
	Assert((flags & (PVC_INCLUDE_PLACEHOLDERS | PVC_RECURSE_PLACEHOLDERS))
		   != (PVC_INCLUDE_PLACEHOLDERS | PVC_RECURSE_PLACEHOLDERS));

	context.varlist = NIL;
	context.flags = flags;

	pull_var_clause_walker(node, &context);
	return context.varlist;
}

/*
 * pull_var_clause_walker - (中文)pull_var_clause 的递归遍历器
 *
 * 【作用】按 context->flags 处理各类节点:命中当前层 Var 一律收进 varlist;
 * Aggref / GroupingFunc / WindowFunc / PlaceHolderVar 分别按 INCLUDE(收进
 * 并停止深入)/ RECURSE(深入参数)/ 无标志(报错)三分支;其它节点递归。
 *
 * 【设计思想】实现细节:INCLUDE 分支返回 false 避免进入参数,RECURSE 分支
 * 则"穿透"到最后的 expression_tree_walker;上层引用(levelsup != 0)对
 * 各类节点分别 elog。这些特殊节点之外的普通表达式交给通用 walker 递归。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 携带 varlist 与 flags。
 * 【返回值】false(永不中止)。
 */
static bool
pull_var_clause_walker(Node *node, pull_var_clause_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		if (((Var *) node)->varlevelsup != 0)
			elog(ERROR, "Upper-level Var found where not expected");
		context->varlist = lappend(context->varlist, node);
		return false;
	}
	else if (IsA(node, Aggref))
	{
		if (((Aggref *) node)->agglevelsup != 0)
			elog(ERROR, "Upper-level Aggref found where not expected");
		if (context->flags & PVC_INCLUDE_AGGREGATES)
		{
			context->varlist = lappend(context->varlist, node);
			/* we do NOT descend into the contained expression */
			return false;
		}
		else if (context->flags & PVC_RECURSE_AGGREGATES)
		{
			/* fall through to recurse into the aggregate's arguments */
		}
		else
			elog(ERROR, "Aggref found where not expected");
	}
	else if (IsA(node, GroupingFunc))
	{
		if (((GroupingFunc *) node)->agglevelsup != 0)
			elog(ERROR, "Upper-level GROUPING found where not expected");
		if (context->flags & PVC_INCLUDE_AGGREGATES)
		{
			context->varlist = lappend(context->varlist, node);
			/* we do NOT descend into the contained expression */
			return false;
		}
		else if (context->flags & PVC_RECURSE_AGGREGATES)
		{
			/* fall through to recurse into the GroupingFunc's arguments */
		}
		else
			elog(ERROR, "GROUPING found where not expected");
	}
	else if (IsA(node, WindowFunc))
	{
		/* WindowFuncs have no levelsup field to check ... */
		if (context->flags & PVC_INCLUDE_WINDOWFUNCS)
		{
			context->varlist = lappend(context->varlist, node);
			/* we do NOT descend into the contained expressions */
			return false;
		}
		else if (context->flags & PVC_RECURSE_WINDOWFUNCS)
		{
			/* fall through to recurse into the windowfunc's arguments */
		}
		else
			elog(ERROR, "WindowFunc found where not expected");
	}
	else if (IsA(node, PlaceHolderVar))
	{
		if (((PlaceHolderVar *) node)->phlevelsup != 0)
			elog(ERROR, "Upper-level PlaceHolderVar found where not expected");
		if (context->flags & PVC_INCLUDE_PLACEHOLDERS)
		{
			context->varlist = lappend(context->varlist, node);
			/* we do NOT descend into the contained expression */
			return false;
		}
		else if (context->flags & PVC_RECURSE_PLACEHOLDERS)
		{
			/* fall through to recurse into the placeholder's expression */
		}
		else
			elog(ERROR, "PlaceHolderVar found where not expected");
	}
	return expression_tree_walker(node, pull_var_clause_walker, context);
}


/*
 * flatten_join_alias_vars
 *	  Replace Vars that reference JOIN outputs with references to the original
 *	  relation variables instead.  This allows quals involving such vars to be
 *	  pushed down.  Whole-row Vars that reference JOIN relations are expanded
 *	  into RowExpr constructs that name the individual output Vars.  This
 *	  is necessary since we will not scan the JOIN as a base relation, which
 *	  is the only way that the executor can directly handle whole-row Vars.
 *
 * This also adjusts relid sets found in some expression node types to
 * substitute the contained base+OJ rels for any join relid.
 *
 * If a JOIN contains sub-selects that have been flattened, its join alias
 * entries might now be arbitrary expressions, not just Vars.  This affects
 * this function in two important ways.  First, we might find ourselves
 * inserting SubLink expressions into subqueries, and we must make sure that
 * their Query.hasSubLinks fields get set to true if so.  If there are any
 * SubLinks in the join alias lists, the outer Query should already have
 * hasSubLinks = true, so this is only relevant to un-flattened subqueries.
 * Second, we have to preserve any varnullingrels info attached to the
 * alias Vars we're replacing.  If the replacement expression is a Var or
 * PlaceHolderVar or constructed from those, we can just add the
 * varnullingrels bits to the existing nullingrels field(s); otherwise
 * we have to add a PlaceHolderVar wrapper.
 */
/*
 * flatten_join_alias_vars - (中文)把引用 JOIN 输出的 Var 展开为底层表达式
 *
 * 【作用】把 node 中引用 JOIN 关系输出的 Var 替换成它们对应的底层表达式
 * (rtable 中该 JOIN 的 joinaliasvars),使条件可以下推到基础关系。整行 Var
 * 展开为 RowExpr(执行器只能直接处理基础关系的整行 Var)。同时把表达式里的
 * relid 集合从 join relid 改写为"基础关系 + 外连接"relid。
 *
 * 【设计思想】核心复杂性来自两方面:
 * (1) join 别名可能是被展平的子查询的任意表达式,替换后可能把 SubLink
 *     引入当前查询,须维护 inserted_sublink 并把 hasSubLinks 置真;
 * (2) 被替换的别名 Var 携带 varnullingrels(外连接可空性),必须传递给替换
 *     表达式:若替换结果是 Var/PlaceHolderVar(或其经隐式转换/COALESCE 组合),
 *     直接并入其 nullingrels 字段(add_nullingrels_if_needed 的快速路径),
 *     否则包一层 PlaceHolderVar 携带(add_nullingrels_if_needed 的 PHV 分支)。
 * 实现为 mutator:整行引用按 rte->joinaliasvars 与 colnames 逐列展开并递归
 * (join 的输入可能本身是 join),逐列引用则替换为对应别名表达式后继续递归,
 * 同时保留原 Var 的 location。PlaceHolderVar 的 phrels 也要用 alias_relid_set
 * 把其中的 join relid 换成基础集合。
 *
 * 【参数】
 *   root  —— 规划上下文;query —— 当前查询(提供 rtable);
 *   node  —— 待展开的表达式或 LATERAL 子查询(不能是 query 本身)。
 * 【返回值】展开后的表达式拷贝。
 */
Node *
flatten_join_alias_vars(PlannerInfo *root, Query *query, Node *node)
{
	flatten_join_alias_vars_context context;

	/*
	 * We do not expect this to be applied to the whole Query, only to
	 * expressions or LATERAL subqueries.  Hence, if the top node is a Query,
	 * it's okay to immediately increment sublevels_up.
	 */
	Assert(node != (Node *) query);

	context.root = root;
	context.query = query;
	context.sublevels_up = 0;
	/* flag whether join aliases could possibly contain SubLinks */
	context.possible_sublink = query->hasSubLinks;
	/* if hasSubLinks is already true, no need to work hard */
	context.inserted_sublink = query->hasSubLinks;

	return flatten_join_alias_vars_mutator(node, &context);
}

/*
 * flatten_join_alias_for_parser
 *
 * This variant of flatten_join_alias_vars is used by the parser, to expand
 * join alias Vars before checking GROUP BY validity.  In that case we lack
 * a root structure.  Fortunately, we'd only need the root for making
 * PlaceHolderVars.  We can avoid making PlaceHolderVars in the parser's
 * usage because it won't be dealing with arbitrary expressions: so long as
 * adjust_standard_join_alias_expression can handle everything the parser
 * would make as a join alias expression, we're OK.
 *
 * The "node" might be part of a sub-query of the Query whose join alias
 * Vars are to be expanded.  "sublevels_up" indicates how far below the
 * given query we are starting.
 */
/*
 * flatten_join_alias_for_parser - (中文)解析器用的 join 别名展开
 *
 * 【作用】flatten_join_alias_vars 的解析器变体:在检查 GROUP BY 合法性之前
 * 展开 join 别名 Var。与规划器版本的关键差异是没有 root(解析阶段尚无
 * PlannerInfo),因此无法构造 PlaceHolderVar。
 *
 * 【设计思想】由于解析器生成的 join 别名表达式只可能是 Var/PHV/隐式强制
 * 类型转换/COALESCE 的组合,is_standard_join_alias_expression +
 * adjust_standard_join_alias_expression 的"直接并入 nullingrels"路径足以
 * 覆盖,不会走到需要 root 的 PHV 包装分支(add_nullingrels_if_needed 中
 * root 为 NULL 时遇到无法处理的情况会报错)。sublevels_up 允许指定从 query
 * 之下若干层开始展开,配合 node 是 query 子查询内表达式的情形。
 *
 * 【参数】
 *   query         —— 提供 rtable 的查询;
 *   node          —— 待展开的表达式;
 *   sublevels_up  —— 起始的查询层深度。
 * 【返回值】展开后的表达式拷贝。
 */
Node *
flatten_join_alias_for_parser(Query *query, Node *node, int sublevels_up)
{
	flatten_join_alias_vars_context context;

	/*
	 * We do not expect this to be applied to the whole Query, only to
	 * expressions or LATERAL subqueries.  Hence, if the top node is a Query,
	 * it's okay to immediately increment sublevels_up.
	 */
	Assert(node != (Node *) query);

	context.root = NULL;
	context.query = query;
	context.sublevels_up = sublevels_up;
	/* flag whether join aliases could possibly contain SubLinks */
	context.possible_sublink = query->hasSubLinks;
	/* if hasSubLinks is already true, no need to work hard */
	context.inserted_sublink = query->hasSubLinks;

	return flatten_join_alias_vars_mutator(node, &context);
}

/*
 * flatten_join_alias_vars_mutator - (中文)join 别名展开的递归执行体
 *
 * 【作用】对节点树做替换式深拷贝:替换引用 JOIN 输出的 Var(整行→RowExpr,
 * 逐列→别名表达式,均可再递归展开更内层的 join),并维护 varnullingrels 与
 * hasSubLinks 传播;PlaceHolderVar 的 phrels 换成基础集合;Query 子查询递归。
 *
 * 【设计思想】主要分支:
 * - Var:varlevelsup 与当前层不符则原样返回;引用 RTE_JOIN 才处理。整行
 *   (varattno == InvalidAttrNumber)时,把 joinaliasvars 中非删除列逐个拷贝
 *   (从上层下传的别名用 IncrementVarSublevelsUp 校正层级、保留原 location)
 *   后递归展开,拼成 RowExpr(带列名)并补 nullingrels;逐列时取对应别名,
 *   同样校正层级/保留 location/递归展开/检查 sublink/补 nullingrels。
 * - PlaceHolderVar:递归展开内部节点后,若 phlevelsup == 当前层,把 phrels
 *   中的 join relid 用 alias_relid_set 换成基础集合(phnullingrels 不动——
 *   它只涉及外连接,join relid 不会被外连接引用)。
 * - Query:sublevels_up++ 并以 QTW_IGNORE_JOINALIASES 递归子查询,把子查询
 *   hasSubLinks 与该层展开引入的 sublink 合并写回。
 * add_nullingrels_if_needed 收尾补 nullingrels:标准别名表达式直接并入字段,
 * 否则用 PHV 包装;root 为 NULL 且不能直接并入时报错。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 携带 root、query、sublevels_up 与
 *   possible_sublink / inserted_sublink 状态。
 * 【返回值】展开后的节点拷贝。
 */
static Node *
flatten_join_alias_vars_mutator(Node *node,
								flatten_join_alias_vars_context *context)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;
		RangeTblEntry *rte;
		Node	   *newvar;

		/* No change unless Var belongs to a JOIN of the target level */
		if (var->varlevelsup != context->sublevels_up)
			return node;		/* no need to copy, really */
		rte = rt_fetch(var->varno, context->query->rtable);
		if (rte->rtekind != RTE_JOIN)
			return node;
		if (var->varattno == InvalidAttrNumber)
		{
			/* Must expand whole-row reference */
			RowExpr    *rowexpr;
			List	   *fields = NIL;
			List	   *colnames = NIL;
			ListCell   *lv;
			ListCell   *ln;

			Assert(list_length(rte->joinaliasvars) == list_length(rte->eref->colnames));
			forboth(lv, rte->joinaliasvars, ln, rte->eref->colnames)
			{
				newvar = (Node *) lfirst(lv);
				/* Ignore dropped columns */
				if (newvar == NULL)
					continue;
				newvar = copyObject(newvar);

				/*
				 * If we are expanding an alias carried down from an upper
				 * query, must adjust its varlevelsup fields.
				 */
				if (context->sublevels_up != 0)
					IncrementVarSublevelsUp(newvar, context->sublevels_up, 0);
				/* Preserve original Var's location, if possible */
				if (IsA(newvar, Var))
					((Var *) newvar)->location = var->location;
				/* Recurse in case join input is itself a join */
				/* (also takes care of setting inserted_sublink if needed) */
				newvar = flatten_join_alias_vars_mutator(newvar, context);
				fields = lappend(fields, newvar);
				/* We need the names of non-dropped columns, too */
				colnames = lappend(colnames, copyObject((Node *) lfirst(ln)));
			}
			rowexpr = makeNode(RowExpr);
			rowexpr->args = fields;
			rowexpr->row_typeid = var->vartype;
			rowexpr->row_format = COERCE_IMPLICIT_CAST;
			/* vartype will always be RECORDOID, so we always need colnames */
			rowexpr->colnames = colnames;
			rowexpr->location = var->location;

			/* Lastly, add any varnullingrels to the replacement expression */
			return add_nullingrels_if_needed(context->root, (Node *) rowexpr,
											 var);
		}

		/* Expand join alias reference */
		Assert(var->varattno > 0);
		newvar = (Node *) list_nth(rte->joinaliasvars, var->varattno - 1);
		Assert(newvar != NULL);
		newvar = copyObject(newvar);

		/*
		 * If we are expanding an alias carried down from an upper query, must
		 * adjust its varlevelsup fields.
		 */
		if (context->sublevels_up != 0)
			IncrementVarSublevelsUp(newvar, context->sublevels_up, 0);

		/* Preserve original Var's location, if possible */
		if (IsA(newvar, Var))
			((Var *) newvar)->location = var->location;

		/* Recurse in case join input is itself a join */
		newvar = flatten_join_alias_vars_mutator(newvar, context);

		/* Detect if we are adding a sublink to query */
		if (context->possible_sublink && !context->inserted_sublink)
			context->inserted_sublink = checkExprHasSubLink(newvar);

		/* Lastly, add any varnullingrels to the replacement expression */
		return add_nullingrels_if_needed(context->root, newvar, var);
	}
	if (IsA(node, PlaceHolderVar))
	{
		/* Copy the PlaceHolderVar node with correct mutation of subnodes */
		PlaceHolderVar *phv;

		phv = (PlaceHolderVar *) expression_tree_mutator(node,
														 flatten_join_alias_vars_mutator,
														 context);
		/* now fix PlaceHolderVar's relid sets */
		if (phv->phlevelsup == context->sublevels_up)
		{
			phv->phrels = alias_relid_set(context->query,
										  phv->phrels);
			/* we *don't* change phnullingrels */
		}
		return (Node *) phv;
	}

	if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		Query	   *newnode;
		bool		save_inserted_sublink;

		context->sublevels_up++;
		save_inserted_sublink = context->inserted_sublink;
		context->inserted_sublink = ((Query *) node)->hasSubLinks;
		newnode = query_tree_mutator((Query *) node,
									 flatten_join_alias_vars_mutator,
									 context,
									 QTW_IGNORE_JOINALIASES);
		newnode->hasSubLinks |= context->inserted_sublink;
		context->inserted_sublink = save_inserted_sublink;
		context->sublevels_up--;
		return (Node *) newnode;
	}
	/* Already-planned tree not supported */
	Assert(!IsA(node, SubPlan));
	Assert(!IsA(node, AlternativeSubPlan));
	/* Shouldn't need to handle these planner auxiliary nodes here */
	Assert(!IsA(node, SpecialJoinInfo));
	Assert(!IsA(node, PlaceHolderInfo));
	Assert(!IsA(node, MinMaxAggInfo));

	return expression_tree_mutator(node, flatten_join_alias_vars_mutator, context);
}

/*
 * flatten_group_exprs
 *	  Replace Vars that reference GROUP outputs with the underlying grouping
 *	  expressions.
 *
 * We have to preserve any varnullingrels info attached to the group Vars we're
 * replacing.  If the replacement expression is a Var or PlaceHolderVar or
 * constructed from those, we can just add the varnullingrels bits to the
 * existing nullingrels field(s); otherwise we have to add a PlaceHolderVar
 * wrapper.
 *
 * NOTE: root may be passed as NULL, which is why we have to pass the Query
 * separately.  We need the root itself only for preserving varnullingrels.
 * Callers can safely pass NULL if preserving varnullingrels is unnecessary for
 * their specific use case (e.g., deparsing source text, or scanning for
 * volatile functions), or if it is already guaranteed that the query cannot
 * contain grouping sets.
 */
/*
 * flatten_group_exprs - (中文)把引用 GROUP 输出的 Var 展开为分组表达式
 *
 * 【作用】把 node 中引用 GROUP 关系(RTE_GROUP)输出的 Var 替换为其底层
 * 分组表达式(rte->groupexprs),用于 grouping set 场景下把引用"分组结果"
 * 的表达式还原成引用分组依据表达式。与 flatten_join_alias_vars 的结构
 * 完全对应,只是替身来源换成 GROUP 的 groupexprs。
 *
 * 【设计思想】除替换源不同外,与 join 版本的两点差异:
 * (1) 分组引入的可空性用 mark_nullable_by_grouping 传播(varnullingrels
 *     此时只能是 {group_rtindex});
 * (2) 处理 Aggref 时,对当前层的聚合调用不深入其常规参数/ORDER BY/filter
 *     (那里不会有被分组变量),但会展开其 aggdirectargs;更高层的聚合完全
 *     跳过。root 可传 NULL(此时不传播 nullingrels,适合 deparse 或只做
 *     易变性扫描的调用)。
 *
 * 【参数】
 *   root  —— 规划上下文(可为 NULL);query —— 当前查询;
 *   node  —— 待展开的表达式。
 * 【返回值】展开后的表达式拷贝。
 */
Node *
flatten_group_exprs(PlannerInfo *root, Query *query, Node *node)
{
	flatten_join_alias_vars_context context;

	/*
	 * We do not expect this to be applied to the whole Query, only to
	 * expressions or LATERAL subqueries.  Hence, if the top node is a Query,
	 * it's okay to immediately increment sublevels_up.
	 */
	Assert(node != (Node *) query);

	context.root = root;
	context.query = query;
	context.sublevels_up = 0;
	/* flag whether grouping expressions could possibly contain SubLinks */
	context.possible_sublink = query->hasSubLinks;
	/* if hasSubLinks is already true, no need to work hard */
	context.inserted_sublink = query->hasSubLinks;

	return flatten_group_exprs_mutator(node, &context);
}

/*
 * flatten_group_exprs_mutator - (中文)分组表达式展开的递归执行体
 *
 * 【作用】替换引用 RTE_GROUP 输出的 Var 为 groupexprs 对应表达式(校正层级、
 * 保留 location、检测 sublink、经 mark_nullable_by_grouping 传播 nullingrels),
 * 并按上述策略处理 Aggref / GroupingFunc / Query 的递归。
 *
 * 【设计思想】Var 分支与 join 版本类似,最后用 mark_nullable_by_grouping 而
 * 非 add_nullingrels_if_needed。Aggref:仅当前层(agglevelsup == sublevels_up)
 * 的聚合展开其 aggdirectargs 而跳过普通参数;更高层直接不递归(不可能含本
 * 层 Var);更低层继续递归(可能含本层 Var)。GroupingFunc:当前层及以上直接
 * 跳过。Query 递归与 join 版本同构。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 同 flatten_join_alias_vars_mutator。
 * 【返回值】展开后的节点拷贝。
 */
static Node *
flatten_group_exprs_mutator(Node *node,
							flatten_join_alias_vars_context *context)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;
		RangeTblEntry *rte;
		Node	   *newvar;

		/* No change unless Var belongs to the GROUP of the target level */
		if (var->varlevelsup != context->sublevels_up)
			return node;		/* no need to copy, really */
		rte = rt_fetch(var->varno, context->query->rtable);
		if (rte->rtekind != RTE_GROUP)
			return node;

		/* Expand group exprs reference */
		Assert(var->varattno > 0);
		newvar = (Node *) list_nth(rte->groupexprs, var->varattno - 1);
		Assert(newvar != NULL);
		newvar = copyObject(newvar);

		/*
		 * If we are expanding an expr carried down from an upper query, must
		 * adjust its varlevelsup fields.
		 */
		if (context->sublevels_up != 0)
			IncrementVarSublevelsUp(newvar, context->sublevels_up, 0);

		/* Preserve original Var's location, if possible */
		if (IsA(newvar, Var))
			((Var *) newvar)->location = var->location;

		/* Detect if we are adding a sublink to query */
		if (context->possible_sublink && !context->inserted_sublink)
			context->inserted_sublink = checkExprHasSubLink(newvar);

		/* Lastly, add any varnullingrels to the replacement expression */
		return mark_nullable_by_grouping(context->root, newvar, var);
	}

	if (IsA(node, Aggref))
	{
		Aggref	   *agg = (Aggref *) node;

		if ((int) agg->agglevelsup == context->sublevels_up)
		{
			/*
			 * If we find an aggregate call of the original level, do not
			 * recurse into its normal arguments, ORDER BY arguments, or
			 * filter; there are no grouped vars there.  But we should check
			 * direct arguments as though they weren't in an aggregate.
			 */
			agg = copyObject(agg);
			agg->aggdirectargs = (List *)
				flatten_group_exprs_mutator((Node *) agg->aggdirectargs, context);

			return (Node *) agg;
		}

		/*
		 * We can skip recursing into aggregates of higher levels altogether,
		 * since they could not possibly contain Vars of concern to us (see
		 * transformAggregateCall).  We do need to look at aggregates of lower
		 * levels, however.
		 */
		if ((int) agg->agglevelsup > context->sublevels_up)
			return node;
	}

	if (IsA(node, GroupingFunc))
	{
		GroupingFunc *grp = (GroupingFunc *) node;

		/*
		 * If we find a GroupingFunc node of the original or higher level, do
		 * not recurse into its arguments; there are no grouped vars there.
		 */
		if ((int) grp->agglevelsup >= context->sublevels_up)
			return node;
	}

	if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		Query	   *newnode;
		bool		save_inserted_sublink;

		context->sublevels_up++;
		save_inserted_sublink = context->inserted_sublink;
		context->inserted_sublink = ((Query *) node)->hasSubLinks;
		newnode = query_tree_mutator((Query *) node,
									 flatten_group_exprs_mutator,
									 context,
									 QTW_IGNORE_GROUPEXPRS);
		newnode->hasSubLinks |= context->inserted_sublink;
		context->inserted_sublink = save_inserted_sublink;
		context->sublevels_up--;
		return (Node *) newnode;
	}

	return expression_tree_mutator(node, flatten_group_exprs_mutator,
								   context);
}

/*
 * Add oldvar's varnullingrels, if any, to a flattened grouping expression.
 * The newnode has been copied, so we can modify it freely.
 */
/*
 * mark_nullable_by_grouping - (中文)把分组 Var 的可空性传给展开表达式
 *
 * 【作用】flatten_group_exprs 的收尾:把 oldvar 的 varnullingrels(grouping
 * set 引入的可空性,理论上只能是 {group_rtindex})施加到替换后的表达式上。
 * root 为 NULL 或 oldvar 无可空性时原样返回。
 *
 * 【设计思想】分两种情形:
 * - 替换表达式非变量无关(pull_varnos_of_level 非空):把可空性标记加到其
 *   所含 Var / PHV 的 nullingrels 字段(add_nulling_relids)。理论上"整个
 *   表达式因 grouping set 可空"与"逐 Var 标记"并不完全等价,但实践上
 *   只要能让该表达式在等价类(EC)中与未被分组的同名表达式区分开即可;
 * - 替换表达式变量无关且不含易变/集合返回函数:包一层 PlaceHolderVar 来
 *   携带可空性(聚合/窗口函数被断言排除在分组表达式之外);否则保持原样。
 * 两种情况都要断言 oldvar 的可空性与 group_rtindex 一致。
 *
 * 【参数】
 *   root    —— 规划上下文(可为 NULL);newnode —— 已拷贝的替换表达式;
 *   oldvar  —— 被替换的原 Var。
 * 【返回值】施加可空性后的表达式。
 */
static Node *
mark_nullable_by_grouping(PlannerInfo *root, Node *newnode, Var *oldvar)
{
	Relids		relids;

	if (root == NULL)
		return newnode;
	if (oldvar->varnullingrels == NULL)
		return newnode;			/* nothing to do */

	Assert(bms_equal(oldvar->varnullingrels,
					 bms_make_singleton(root->group_rtindex)));

	relids = pull_varnos_of_level(root, newnode, oldvar->varlevelsup);

	if (!bms_is_empty(relids))
	{
		/*
		 * If the newnode is not variable-free, we set the nullingrels of Vars
		 * or PHVs that are contained in the expression.  This is not really
		 * 'correct' in theory, because it is the whole expression that can be
		 * nullable by grouping sets, not its individual vars.  But it works
		 * in practice, because what we need is that the expression can be
		 * somehow distinguished from the same expression in ECs, and marking
		 * its vars is sufficient for this purpose.
		 */
		newnode = add_nulling_relids(newnode,
									 relids,
									 oldvar->varnullingrels);
	}
	else						/* variable-free? */
	{
		/*
		 * If the newnode is variable-free and does not contain volatile
		 * functions or set-returning functions, it can be treated as a member
		 * of EC that is redundant.  So wrap it in a new PlaceHolderVar to
		 * carry the nullingrels.  Otherwise we do not bother to make any
		 * changes.
		 *
		 * Aggregate functions and window functions are not allowed in
		 * grouping expressions.
		 */
		Assert(!contain_agg_clause(newnode));
		Assert(!contain_window_function(newnode));

		if (!contain_volatile_functions(newnode) &&
			!expression_returns_set(newnode))
		{
			PlaceHolderVar *newphv;
			Relids		phrels;

			phrels = get_relids_in_jointree((Node *) root->parse->jointree,
											true, false);
			Assert(!bms_is_empty(phrels));

			newphv = make_placeholder_expr(root, (Expr *) newnode, phrels);
			/* newphv has zero phlevelsup and NULL phnullingrels; fix it */
			newphv->phlevelsup = oldvar->varlevelsup;
			newphv->phnullingrels = bms_copy(oldvar->varnullingrels);
			newnode = (Node *) newphv;
		}
	}

	return newnode;
}

/*
 * Add oldvar's varnullingrels, if any, to a flattened join alias expression.
 * The newnode has been copied, so we can modify it freely.
 */
/*
 * add_nullingrels_if_needed - (中文)把 join 别名 Var 的可空性传给展开表达式
 *
 * 【作用】flatten_join_alias_vars 的收尾:把 oldvar 的 varnullingrels 施加到
 * 替换表达式。oldvar 无可空性则原样返回。
 *
 * 【设计思想】三种路径:
 * - 替换表达式是"标准别名表达式"(is_standard_join_alias_expression 通过:
 *   Var/PHV 或隐式强制转换/COALESCE 组合),直接把可空性并入其 nullingrels
 *   字段,最省事;
 * - 否则若提供了 root,包一层 PlaceHolderVar 携带可空性。PHV 的求值位置
 *   优先取替换表达式的自然语义层(pull_varnos_of_level);表达式变量无关时
 *   退化为该 join 之下(oldvar->varno 所在 join 的关系集合去掉 join 自身,
 *   保证在外连接"下方"求值);
 * - root 为 NULL 且非标准表达式:报错(说明解析器生成了本函数无法处理的
 *   join 别名)。
 *
 * 【参数】
 *   root    —— 规划上下文(可为 NULL,解析器调用时为 NULL);
 *   newnode —— 已拷贝的替换表达式;oldvar —— 被替换的原 Var。
 * 【返回值】施加可空性后的表达式。
 */
static Node *
add_nullingrels_if_needed(PlannerInfo *root, Node *newnode, Var *oldvar)
{
	if (oldvar->varnullingrels == NULL)
		return newnode;			/* nothing to do */
	/* If possible, do it by adding to existing nullingrel fields */
	if (is_standard_join_alias_expression(newnode, oldvar))
		adjust_standard_join_alias_expression(newnode, oldvar);
	else if (root)
	{
		/*
		 * We can insert a PlaceHolderVar to carry the nullingrels.  However,
		 * deciding where to evaluate the PHV is slightly tricky.  We first
		 * try to evaluate it at the natural semantic level of the new
		 * expression; but if that expression is variable-free, fall back to
		 * evaluating it at the join that the oldvar is an alias Var for.
		 */
		PlaceHolderVar *newphv;
		Index		levelsup = oldvar->varlevelsup;
		Relids		phrels = pull_varnos_of_level(root, newnode, levelsup);

		if (bms_is_empty(phrels))	/* variable-free? */
		{
			if (levelsup != 0)	/* this won't work otherwise */
				elog(ERROR, "unsupported join alias expression");
			phrels = get_relids_for_join(root->parse, oldvar->varno);
			/* If it's an outer join, eval below not above the join */
			phrels = bms_del_member(phrels, oldvar->varno);
			Assert(!bms_is_empty(phrels));
		}
		newphv = make_placeholder_expr(root, (Expr *) newnode, phrels);
		/* newphv has zero phlevelsup and NULL phnullingrels; fix it */
		newphv->phlevelsup = levelsup;
		newphv->phnullingrels = bms_copy(oldvar->varnullingrels);
		newnode = (Node *) newphv;
	}
	else
	{
		/* ooops, we're missing support for something the parser can make */
		elog(ERROR, "unsupported join alias expression");
	}
	return newnode;
}

/*
 * Check to see if we can insert nullingrels into this join alias expression
 * without use of a separate PlaceHolderVar.
 *
 * This will handle Vars, PlaceHolderVars, and implicit-coercion and COALESCE
 * expressions built from those.  This coverage needs to handle anything
 * that the parser would put into joinaliasvars.
 */
/*
 * is_standard_join_alias_expression - (中文)替换表达式是否可直接并入可空性
 *
 * 【作用】判断替换表达式能否在"不另包 PlaceHolderVar"的情况下接受
 * oldvar 的 varnullingrels:只接受 Var、PlaceHolderVar 及由它们经隐式
 * 强制类型转换(RelabelType / CoerceViaIO / ArrayCoerceExpr)、单参隐式
 * FuncExpr、COALESCE 组合出的表达式。层级必须与 oldvar 一致。
 *
 * 【设计思想】直接并入的前提是"外层表达式对 NULL 输入保 NULL"(即不会把
 * NULL 变成非 NULL),否则外层表达式在真值上把"因外连接而空的行"变成"非
 * 空值"会破坏可空语义:隐式强制转换、COALESCE 都是保 NULL 的;函数转换
 * 只有 funcformat == COERCE_IMPLICIT_CAST 且至少一个参数时才认为安全
 * (强制转换设计为对 NULL 输入返回 NULL,函数则未必——这就是为什么不用
 * 检查严格性的原因)。COALESCE 需全部参数都保 NULL 才通过;FuncExpr 只查
 * 第一个参数(强制转换可能有额外常量参数)。
 *
 * 【参数】
 *   newnode —— 替换表达式;oldvar —— 原 Var(提供 varlevelsup)。
 * 【返回值】可直接并入返回 true。
 */
static bool
is_standard_join_alias_expression(Node *newnode, Var *oldvar)
{
	if (newnode == NULL)
		return false;
	if (IsA(newnode, Var) &&
		((Var *) newnode)->varlevelsup == oldvar->varlevelsup)
		return true;
	else if (IsA(newnode, PlaceHolderVar) &&
			 ((PlaceHolderVar *) newnode)->phlevelsup == oldvar->varlevelsup)
		return true;
	else if (IsA(newnode, FuncExpr))
	{
		FuncExpr   *fexpr = (FuncExpr *) newnode;

		/*
		 * We need to assume that the function wouldn't produce non-NULL from
		 * NULL, which is reasonable for implicit coercions but otherwise not
		 * so much.  (Looking at its strictness is likely overkill, and anyway
		 * it would cause us to fail if someone forgot to mark an implicit
		 * coercion as strict.)
		 */
		if (fexpr->funcformat != COERCE_IMPLICIT_CAST ||
			fexpr->args == NIL)
			return false;

		/*
		 * Examine only the first argument --- coercions might have additional
		 * arguments that are constants.
		 */
		return is_standard_join_alias_expression(linitial(fexpr->args), oldvar);
	}
	else if (IsA(newnode, RelabelType))
	{
		RelabelType *relabel = (RelabelType *) newnode;

		/* This definitely won't produce non-NULL from NULL */
		return is_standard_join_alias_expression((Node *) relabel->arg, oldvar);
	}
	else if (IsA(newnode, CoerceViaIO))
	{
		CoerceViaIO *iocoerce = (CoerceViaIO *) newnode;

		/* This definitely won't produce non-NULL from NULL */
		return is_standard_join_alias_expression((Node *) iocoerce->arg, oldvar);
	}
	else if (IsA(newnode, ArrayCoerceExpr))
	{
		ArrayCoerceExpr *acoerce = (ArrayCoerceExpr *) newnode;

		/* This definitely won't produce non-NULL from NULL (at array level) */
		return is_standard_join_alias_expression((Node *) acoerce->arg, oldvar);
	}
	else if (IsA(newnode, CoalesceExpr))
	{
		CoalesceExpr *cexpr = (CoalesceExpr *) newnode;
		ListCell   *lc;

		Assert(cexpr->args != NIL);
		foreach(lc, cexpr->args)
		{
			if (!is_standard_join_alias_expression(lfirst(lc), oldvar))
				return false;
		}
		return true;
	}
	else
		return false;
}

/*
 * Insert nullingrels into an expression accepted by
 * is_standard_join_alias_expression.
 */
/*
 * adjust_standard_join_alias_expression - (中文)向标准别名表达式并入可空性
 *
 * 【作用】把 oldvar->varnullingrels 并进被 is_standard_join_alias_expression
 * 接受的替换表达式:顶层是 Var/PHV 时直接并入其 nullingrels 字段,否则
 * 递归进其(唯一的)子表达式继续。递归结构必须与"标准别名表达式"定义一致,
 * 其它形态由断言兜底。
 *
 * 【设计思想】与 is_standard_join_alias_expression 是一对(判定 + 执行);
 * FuncExpr / RelabelType / CoerceViaIO / ArrayCoerceExpr 都只有一条"数据
 * 通道"(首个/唯一的参数),COALESCE 的每条分支都要递归并入。
 *
 * 【参数】
 *   newnode —— 标准别名表达式(可修改);oldvar —— 提供可空性。
 * 【返回值】无(就地修改)。
 */
static void
adjust_standard_join_alias_expression(Node *newnode, Var *oldvar)
{
	if (IsA(newnode, Var) &&
		((Var *) newnode)->varlevelsup == oldvar->varlevelsup)
	{
		Var		   *newvar = (Var *) newnode;

		newvar->varnullingrels = bms_add_members(newvar->varnullingrels,
												 oldvar->varnullingrels);
	}
	else if (IsA(newnode, PlaceHolderVar) &&
			 ((PlaceHolderVar *) newnode)->phlevelsup == oldvar->varlevelsup)
	{
		PlaceHolderVar *newphv = (PlaceHolderVar *) newnode;

		newphv->phnullingrels = bms_add_members(newphv->phnullingrels,
												oldvar->varnullingrels);
	}
	else if (IsA(newnode, FuncExpr))
	{
		FuncExpr   *fexpr = (FuncExpr *) newnode;

		adjust_standard_join_alias_expression(linitial(fexpr->args), oldvar);
	}
	else if (IsA(newnode, RelabelType))
	{
		RelabelType *relabel = (RelabelType *) newnode;

		adjust_standard_join_alias_expression((Node *) relabel->arg, oldvar);
	}
	else if (IsA(newnode, CoerceViaIO))
	{
		CoerceViaIO *iocoerce = (CoerceViaIO *) newnode;

		adjust_standard_join_alias_expression((Node *) iocoerce->arg, oldvar);
	}
	else if (IsA(newnode, ArrayCoerceExpr))
	{
		ArrayCoerceExpr *acoerce = (ArrayCoerceExpr *) newnode;

		adjust_standard_join_alias_expression((Node *) acoerce->arg, oldvar);
	}
	else if (IsA(newnode, CoalesceExpr))
	{
		CoalesceExpr *cexpr = (CoalesceExpr *) newnode;
		ListCell   *lc;

		Assert(cexpr->args != NIL);
		foreach(lc, cexpr->args)
		{
			adjust_standard_join_alias_expression(lfirst(lc), oldvar);
		}
	}
	else
		Assert(false);
}

/*
 * alias_relid_set: in a set of RT indexes, replace joins by their
 * underlying base+OJ relids
 */
/*
 * alias_relid_set - (中文)把 relid 位图中的 join relid 换成底层集合
 *
 * 【作用】遍历 relids,对每个 RTE_JOIN 下标用 get_relids_for_join 展开为其
 * 底层的 base + 外连接(OJ) relid 集合,非 join 下标原样保留,返回新的位图。
 *
 * 【设计思想】规划器一旦把 join 视为"可被拆解的对象",其 relid 就不该再
 * 出现在依赖集合里——所有依赖都必须落在真正提供数据的基础关系与外连接
 * 上。用于 flatten_join_alias_vars 中 PlaceHolderVar.phrels 的改写。
 *
 * 【参数】
 *   query —— 提供 rtable 的查询;relids —— 输入位图。
 * 【返回值】展开后的位图。
 */
static Relids
alias_relid_set(Query *query, Relids relids)
{
	Relids		result = NULL;
	int			rtindex;

	rtindex = -1;
	while ((rtindex = bms_next_member(relids, rtindex)) >= 0)
	{
		RangeTblEntry *rte = rt_fetch(rtindex, query->rtable);

		if (rte->rtekind == RTE_JOIN)
			result = bms_join(result, get_relids_for_join(query, rtindex));
		else
			result = bms_add_member(result, rtindex);
	}
	return result;
}
