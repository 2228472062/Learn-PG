/*-------------------------------------------------------------------------
 *
 * prepqual.c
 *	  Routines for preprocessing qualification expressions
 *
 *
 * While the parser will produce flattened (N-argument) AND/OR trees from
 * simple sequences of AND'ed or OR'ed clauses, there might be an AND clause
 * directly underneath another AND, or OR underneath OR, if the input was
 * oddly parenthesized.  Also, rule expansion and subquery flattening could
 * produce such parsetrees.  The planner wants to flatten all such cases
 * to ensure consistent optimization behavior.
 *
 * Formerly, this module was responsible for doing the initial flattening,
 * but now we leave it to eval_const_expressions to do that since it has to
 * make a complete pass over the expression tree anyway.  Instead, we just
 * have to ensure that our manipulations preserve AND/OR flatness.
 * pull_ands() and pull_ors() are used to maintain flatness of the AND/OR
 * tree after local transformations that might introduce nested AND/ORs.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 优化器"预处理器"(prep 模块)的成员,专门负责对谓词
 * (QUAL,即布尔限定表达式)做规范化与化简,使进入路径/代价计算的限定条件
 * 具有统一、干净的形态。它是"生成计划之前重写查询树"的一部分。
 *
 * 【本模块的职责】
 * - negate_clause():取反一个布尔表达式,并尽量用逻辑等价变换消除 NOT 节点
 *   (如用运算符的负算子把 NOT (a < b) 换成 a >= b、用德摩根律把 NOT 下推到
 *   AND/OR 之下、处理 NOT NOT 抵消、IS NULL/IS TRUE 系列取反等);
 * - canonicalize_qual():QUAL 规范化主入口,对顶层 WHERE / JOIN ON / CHECK
 *   约束做优化(注意必须在 eval_const_expressions 之后调用);
 * - find_duplicate_ors / process_duplicate_ors:应用"逆 OR 分配律",把
 *   ((A AND B) OR (A AND C)) 化简为 A AND (B OR C),同时剔除顶层 AND/OR
 *   结构中的常量 TRUE/FALSE/NULL 项;
 * - pull_ands / pull_ors:递归地把嵌套的 AND/OR 展平为单层列表,维护
 *   "AND/OR 平坦性"这一关键不变量。
 *
 * 【设计思想】
 * - 保持 AND/OR 平坦:解析器与重写器可能产生嵌套的同层 AND/OR,而规划器
 *   的后续阶段(如把 WHERE 拆成隐含 AND 列表、按需分发限定条件)都依赖
 *   "一个 AND/OR 节点的直接子节点里不再出现同种布尔算子"这一性质,因此
 *   任何局部变换后都要用 pull_ands/pull_ors 恢复平坦;
 * - 顶层 NULL 语义利用:WHERE 顶层不需要区分 FALSE 与 NULL(NULL 也被滤掉),
 *   CHECK 约束顶层不需要区分 TRUE 与 NULL(NULL 通过约束),据此可以在
 *   顶层安全删除常量项(这是 eval_const_expressions 出于通用性不能做的);
 * - 逆 OR 分配律只作用于顶层 AND/OR 结构,不深入子表达式,因为收益主要
 *   来自把公共条件提取到顶层,便于连接重排与索引选择。
 *
 * 【函数关系】
 * canonicalize_qual(入口) -> find_duplicate_ors(递归,内部调 pull_ors /
 * pull_ands 保持平坦,并对 OR 节点调 process_duplicate_ors 应用逆分配律);
 * negate_clause 独立使用,主要作为 eval_const_expressions 的辅助工具。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/prep/prepqual.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/optimizer.h"
#include "utils/lsyscache.h"


static List *pull_ands(List *andlist);
static List *pull_ors(List *orlist);
static Expr *find_duplicate_ors(Expr *qual, bool is_check);
static Expr *process_duplicate_ors(List *orlist);


/*
 * negate_clause
 *	  Negate a Boolean expression.
 *
 * Input is a clause to be negated (e.g., the argument of a NOT clause).
 * Returns a new clause equivalent to the negation of the given clause.
 *
 * Although this can be invoked on its own, it's mainly intended as a helper
 * for eval_const_expressions(), and that context drives several design
 * decisions.  In particular, if the input is already AND/OR flat, we must
 * preserve that property.  We also don't bother to recurse in situations
 * where we can assume that lower-level executions of eval_const_expressions
 * would already have simplified sub-clauses of the input.
 *
 * The difference between this and a simple make_notclause() is that this
 * tries to get rid of the NOT node by logical simplification.  It's clearly
 * always a win if the NOT node can be eliminated altogether.  However, our
 * use of DeMorgan's laws could result in having more NOT nodes rather than
 * fewer.  We do that unconditionally anyway, because in WHERE clauses it's
 * important to expose as much top-level AND/OR structure as possible.
 * Also, eliminating an intermediate NOT may allow us to flatten two levels
 * of AND or OR together that we couldn't have otherwise.  Finally, one of
 * the motivations for doing this is to ensure that logically equivalent
 * expressions will be seen as physically equal(), so we should always apply
 * the same transformations.
 */
/*
 * negate_clause - (中文)对布尔表达式取反,并尽可能消除外层 NOT 节点
 *
 * 【作用】返回一个等价于"输入表达式取反"的新表达式。可按需单独调用,但
 * 主要作为 eval_const_expressions() 的辅助函数。能化简的情形:常量(NOT
 * NULL 仍为 NULL,直接返回 FALSE;其他布尔常量取反)、有负算子的 OpExpr
 * 与 ScalarArrayOpExpr(如 x = ANY(...) 取反成 x <> ALL(...))、BoolExpr
 * (AND/OR 用德摩根律互换并逐子项取反,NOT 之下再套 NOT 则抵消)、标量类型
 * 的 NullTest(IS NULL 与 IS NOT NULL 互换)、BooleanTest(IS TRUE 与
 * IS NOT TRUE 等六种情况两两互换)。其余未知情况退化为在外层包一个显式
 * NOT 节点。
 *
 * 【设计思想】
 * - 前提是输入已经过 eval_const_expressions,且 AND/OR 已平坦;变换必须
 *   保持"AND/OR 平坦"与"NOT 不会出现在布尔算子之上"两个性质,这样逻辑
 *   上等价的表达式才能被 equal() 识别为相同,便于去重与复用;
 * - 即使德摩根律可能增加 NOT 节点数量也照做:WHERE 子句中尽量暴露顶层
 *   AND/OR 结构比减少 NOT 更重要;消除中间层 NOT 有时还能让两层 AND/OR
 *   得以合并展平;
 * - 行类型(RowExpr)的 IS NULL 与 IS NOT NULL 并非逻辑互逆,故 NullTest
 *   只在 !argisrow 时才互换;
 * - ScalarArrayOpExpr 取反时把 useOr 翻转(ANY 变 ALL),并把 hashfuncid/
 *   negfuncid 清零,让后续重新解析或重新推导。
 *
 * 【参数】node —— 待取反的表达式。
 * 【返回值】等价于 NOT(node) 的新表达式;输入为 NULL 时报错(空子表达式
 * 无法取反)。
 */
Node *
negate_clause(Node *node)
{
	if (node == NULL)			/* should not happen */
		elog(ERROR, "can't negate an empty subexpression");
	switch (nodeTag(node))
	{
		case T_Const:
			{
				Const	   *c = (Const *) node;

				/* NOT NULL is still NULL */
				if (c->constisnull)
					return makeBoolConst(false, true);
				/* otherwise pretty easy */
				return makeBoolConst(!DatumGetBool(c->constvalue), false);
			}
			break;
		case T_OpExpr:
			{
				/*
				 * Negate operator if possible: (NOT (< A B)) => (>= A B)
				 */
				OpExpr	   *opexpr = (OpExpr *) node;
				Oid			negator = get_negator(opexpr->opno);

				if (negator)
				{
					OpExpr	   *newopexpr = makeNode(OpExpr);

					newopexpr->opno = negator;
					newopexpr->opfuncid = InvalidOid;
					newopexpr->opresulttype = opexpr->opresulttype;
					newopexpr->opretset = opexpr->opretset;
					newopexpr->opcollid = opexpr->opcollid;
					newopexpr->inputcollid = opexpr->inputcollid;
					newopexpr->args = opexpr->args;
					newopexpr->location = opexpr->location;
					return (Node *) newopexpr;
				}
			}
			break;
		case T_ScalarArrayOpExpr:
			{
				/*
				 * Negate a ScalarArrayOpExpr if its operator has a negator;
				 * for example x = ANY (list) becomes x <> ALL (list)
				 */
				ScalarArrayOpExpr *saopexpr = (ScalarArrayOpExpr *) node;
				Oid			negator = get_negator(saopexpr->opno);

				if (negator)
				{
					ScalarArrayOpExpr *newopexpr = makeNode(ScalarArrayOpExpr);

					newopexpr->opno = negator;
					newopexpr->opfuncid = InvalidOid;
					newopexpr->hashfuncid = InvalidOid;
					newopexpr->negfuncid = InvalidOid;
					newopexpr->useOr = !saopexpr->useOr;
					newopexpr->inputcollid = saopexpr->inputcollid;
					newopexpr->args = saopexpr->args;
					newopexpr->location = saopexpr->location;
					return (Node *) newopexpr;
				}
			}
			break;
		case T_BoolExpr:
			{
				BoolExpr   *expr = (BoolExpr *) node;

				switch (expr->boolop)
				{
						/*--------------------
						 * Apply DeMorgan's Laws:
						 *		(NOT (AND A B)) => (OR (NOT A) (NOT B))
						 *		(NOT (OR A B))	=> (AND (NOT A) (NOT B))
						 * i.e., swap AND for OR and negate each subclause.
						 *
						 * If the input is already AND/OR flat and has no NOT
						 * directly above AND or OR, this transformation preserves
						 * those properties.  For example, if no direct child of
						 * the given AND clause is an AND or a NOT-above-OR, then
						 * the recursive calls of negate_clause() can't return any
						 * OR clauses.  So we needn't call pull_ors() before
						 * building a new OR clause.  Similarly for the OR case.
						 *--------------------
						 */
					case AND_EXPR:
						{
							List	   *nargs = NIL;
							ListCell   *lc;

							foreach(lc, expr->args)
							{
								nargs = lappend(nargs,
												negate_clause(lfirst(lc)));
							}
							return (Node *) make_orclause(nargs);
						}
						break;
					case OR_EXPR:
						{
							List	   *nargs = NIL;
							ListCell   *lc;

							foreach(lc, expr->args)
							{
								nargs = lappend(nargs,
												negate_clause(lfirst(lc)));
							}
							return (Node *) make_andclause(nargs);
						}
						break;
					case NOT_EXPR:

						/*
						 * NOT underneath NOT: they cancel.  We assume the
						 * input is already simplified, so no need to recurse.
						 */
						return (Node *) linitial(expr->args);
					default:
						elog(ERROR, "unrecognized boolop: %d",
							 (int) expr->boolop);
						break;
				}
			}
			break;
		case T_NullTest:
			{
				NullTest   *expr = (NullTest *) node;

				/*
				 * In the rowtype case, the two flavors of NullTest are *not*
				 * logical inverses, so we can't simplify.  But it does work
				 * for scalar datatypes.
				 */
				if (!expr->argisrow)
				{
					NullTest   *newexpr = makeNode(NullTest);

					newexpr->arg = expr->arg;
					newexpr->nulltesttype = (expr->nulltesttype == IS_NULL ?
											 IS_NOT_NULL : IS_NULL);
					newexpr->argisrow = expr->argisrow;
					newexpr->location = expr->location;
					return (Node *) newexpr;
				}
			}
			break;
		case T_BooleanTest:
			{
				BooleanTest *expr = (BooleanTest *) node;
				BooleanTest *newexpr = makeNode(BooleanTest);

				newexpr->arg = expr->arg;
				switch (expr->booltesttype)
				{
					case IS_TRUE:
						newexpr->booltesttype = IS_NOT_TRUE;
						break;
					case IS_NOT_TRUE:
						newexpr->booltesttype = IS_TRUE;
						break;
					case IS_FALSE:
						newexpr->booltesttype = IS_NOT_FALSE;
						break;
					case IS_NOT_FALSE:
						newexpr->booltesttype = IS_FALSE;
						break;
					case IS_UNKNOWN:
						newexpr->booltesttype = IS_NOT_UNKNOWN;
						break;
					case IS_NOT_UNKNOWN:
						newexpr->booltesttype = IS_UNKNOWN;
						break;
					default:
						elog(ERROR, "unrecognized booltesttype: %d",
							 (int) expr->booltesttype);
						break;
				}
				newexpr->location = expr->location;
				return (Node *) newexpr;
			}
			break;
		default:
			/* else fall through */
			break;
	}

	/*
	 * Otherwise we don't know how to simplify this, so just tack on an
	 * explicit NOT node.
	 */
	return (Node *) make_notclause((Expr *) node);
}


/*
 * canonicalize_qual
 *	  Convert a qualification expression to the most useful form.
 *
 * This is primarily intended to be used on top-level WHERE (or JOIN/ON)
 * clauses.  It can also be used on top-level CHECK constraints, for which
 * pass is_check = true.  DO NOT call it on any expression that is not known
 * to be one or the other, as it might apply inappropriate simplifications.
 *
 * The name of this routine is a holdover from a time when it would try to
 * force the expression into canonical AND-of-ORs or OR-of-ANDs form.
 * Eventually, we recognized that that had more theoretical purity than
 * actual usefulness, and so now the transformation doesn't involve any
 * notion of reaching a canonical form.
 *
 * NOTE: we assume the input has already been through eval_const_expressions
 * and therefore possesses AND/OR flatness.  Formerly this function included
 * its own flattening logic, but that requires a useless extra pass over the
 * tree.
 *
 * Returns the modified qualification.
 */
/*
 * canonicalize_qual - (中文)把限定表达式规范化为最有用形态
 *
 * 【作用】QUAL 规范化主入口,主要供顶层 WHERE(或 JOIN/ON)子句使用,也可
 * 以(is_check = true)用于顶层 CHECK 约束。当前实现的核心动作是调用
 * find_duplicate_ors 在顶层 AND/OR 结构中提取公共条件(逆 OR 分配律)并
 * 剔除常量项;输入为空(NULL)时直接返回 NULL。
 *
 * 【设计思想】函数名是历史遗留——早期版本试图把表达式压成规范
 * AND-of-ORs/OR-of-ANDs 范式,后来发现纯理论价值大于实际效用,已放弃;
 * 现仅做"有实际收益"的变换。重要前置条件:输入必须先经过
 * eval_const_expressions,因此输入已具备 AND/OR 平坦性且常量已化简,本
 * 函数不再自行展平(否则浪费一次不必要的遍历)。CHECK 约束与 WHERE 的
 * NULL 语义不同(is_check 标志控制),因此不能混用于其他表达式。
 *
 * 【参数】
 *   qual     —— 待规范化的限定表达式(不能是隐含 AND 的 List 形式);
 *   is_check —— true 表示这是顶层 CHECK 约束(顶层 NULL 按 TRUE 处理),
 *               false 表示 WHERE 子句(顶层 NULL 按 FALSE 处理)。
 * 【返回值】规范化后的表达式;输入为 NULL 时返回 NULL。
 */
Expr *
canonicalize_qual(Expr *qual, bool is_check)
{
	Expr	   *newqual;

	/* Quick exit for empty qual */
	if (qual == NULL)
		return NULL;

	/* This should not be invoked on quals in implicit-AND format */
	Assert(!IsA(qual, List));

	/*
	 * Pull up redundant subclauses in OR-of-AND trees.  We do this only
	 * within the top-level AND/OR structure; there's no point in looking
	 * deeper.  Also remove any NULL constants in the top-level structure.
	 */
	newqual = find_duplicate_ors(qual, is_check);

	return newqual;
}


/*
 * pull_ands
 *	  Recursively flatten nested AND clauses into a single and-clause list.
 *
 * Input is the arglist of an AND clause.
 * Returns the rebuilt arglist (note original list structure is not touched).
 */
/*
 * pull_ands - (中文)递归展平嵌套的 AND 子句
 *
 * 【作用】输入是一个 AND 子句的参数列表(隐式 AND 列表或显式 BoolExpr 的
 * args),遍历其成员:遇到 AND 子句则递归取其 args 合并进来,否则原样保留
 * 该成员。返回重建后的单层 AND 参数列表。
 *
 * 【设计思想】用于在局部变换(如把表达式上提)之后恢复"AND 平坦性":
 * 保证任何 AND 节点的直接子节点不再出现 AND。原列表不被修改,新列表
 * 复用旧节点指针,故无节点复制开销。
 *
 * 【参数】andlist —— 某个 AND 子句的参数列表。
 * 【返回值】展平后的新列表(与输入内容等价,结构上只有一层 AND)。
 */
static List *
pull_ands(List *andlist)
{
	List	   *out_list = NIL;
	ListCell   *arg;

	foreach(arg, andlist)
	{
		Node	   *subexpr = (Node *) lfirst(arg);

		if (is_andclause(subexpr))
			out_list = list_concat(out_list,
								   pull_ands(((BoolExpr *) subexpr)->args));
		else
			out_list = lappend(out_list, subexpr);
	}
	return out_list;
}

/*
 * pull_ors
 *	  Recursively flatten nested OR clauses into a single or-clause list.
 *
 * Input is the arglist of an OR clause.
 * Returns the rebuilt arglist (note original list structure is not touched).
 */
/*
 * pull_ors - (中文)递归展平嵌套的 OR 子句
 *
 * 【作用】与 pull_ands 完全对称:输入是 OR 子句的参数列表,遇到 OR 子句
 * 则递归合并其 args,否则原样保留,返回重建后的单层 OR 参数列表。
 *
 * 【设计思想】维护"OR 平坦性":任何 OR 节点的直接子节点不再出现 OR。
 * 对原列表只读,不修改输入结构。
 *
 * 【参数】orlist —— 某个 OR 子句的参数列表。
 * 【返回值】展平后的新列表。
 */
static List *
pull_ors(List *orlist)
{
	List	   *out_list = NIL;
	ListCell   *arg;

	foreach(arg, orlist)
	{
		Node	   *subexpr = (Node *) lfirst(arg);

		if (is_orclause(subexpr))
			out_list = list_concat(out_list,
								   pull_ors(((BoolExpr *) subexpr)->args));
		else
			out_list = lappend(out_list, subexpr);
	}
	return out_list;
}


/*--------------------
 * The following code attempts to apply the inverse OR distributive law:
 *		((A AND B) OR (A AND C))  =>  (A AND (B OR C))
 * That is, locate OR clauses in which every subclause contains an
 * identical term, and pull out the duplicated terms.
 *
 * This may seem like a fairly useless activity, but it turns out to be
 * applicable to many machine-generated queries, and there are also queries
 * in some of the TPC benchmarks that need it.  This was in fact almost the
 * sole useful side-effect of the old prepqual code that tried to force
 * the query into canonical AND-of-ORs form: the canonical equivalent of
 *		((A AND B) OR (A AND C))
 * is
 *		((A OR A) AND (A OR C) AND (B OR A) AND (B OR C))
 * which the code was able to simplify to
 *		(A AND (A OR C) AND (B OR A) AND (B OR C))
 * thus successfully extracting the common condition A --- but at the cost
 * of cluttering the qual with many redundant clauses.
 *--------------------
 */

/*
 * find_duplicate_ors
 *	  Given a qualification tree with the NOTs pushed down, search for
 *	  OR clauses to which the inverse OR distributive law might apply.
 *	  Only the top-level AND/OR structure is searched.
 *
 * While at it, we remove any NULL constants within the top-level AND/OR
 * structure, eg in a WHERE clause, "x OR NULL::boolean" is reduced to "x".
 * In general that would change the result, so eval_const_expressions can't
 * do it; but at top level of WHERE, we don't need to distinguish between
 * FALSE and NULL results, so it's valid to treat NULL::boolean the same
 * as FALSE and then simplify AND/OR accordingly.  Conversely, in a top-level
 * CHECK constraint, we may treat a NULL the same as TRUE.
 *
 * Returns the modified qualification.  AND/OR flatness is preserved.
 */
/*
 * find_duplicate_ors - (中文)在限定树中搜索可应用逆 OR 分配律的 OR 子句,
 * 并顺带剔除顶层常量项
 *
 * 【作用】递归处理限定表达式(假定 NOT 已被压到下层)。对 OR 节点:先递归
 * 处理各参数并剔除常量(FALSE/NULL 在 WHERE 顶层、FALSE 在 CHECK 顶层中
 * 直接删除;TRUE 使整个 OR 化简为 TRUE),再 pull_ors 展平,最后调用
 * process_duplicate_ors 应用逆 OR 分配律;对 AND 节点:类似地递归、剔除
 * 常量(TRUE 在 WHERE 顶层、TRUE/NULL 在 CHECK 顶层中删除;FALSE/NULL 在
 * WHERE 顶层使整个 AND 化简为 FALSE),展平后做单元素/空列表化简;其余节点
 * 原样返回。只有顶层 AND/OR 结构被搜索。
 *
 * 【设计思想】
 * - "逆 OR 分配律"((A AND B) OR (A AND C) => A AND (B OR C))由
 *   process_duplicate_ors 完成,本函数负责定位 OR 子句、准备其展平后的
 *   子句列表,并重建结果时保持 AND/OR 平坦性;
 * - 常量剔除利用了"顶层"语义:WHERE 顶层不区分 FALSE 与 NULL,CHECK 顶层
 *   不区分 TRUE 与 NULL,因此可以比 eval_const_expressions 更大胆地化简。
 *   注意这个安全漏洞只存在于顶层,深入子表达式就必须保留三值逻辑,这正是
 *   本函数只处理顶层结构的原因;
 * - is_check 参数同时影响常量剔除方向与"空/单元素"化简结果:空 AND 在
 *   WHERE 顶层等价 TRUE,在 CHECK 顶层则因为 NULL 也算通过而仍是 TRUE。
 *
 * 【参数】
 *   qual     —— 当前子表达式;
 *   is_check —— true:CHECK 约束语义;false:WHERE 语义(见上)。
 * 【返回值】修改后的表达式。保证 AND/OR 平坦性被保持。
 */
static Expr *
find_duplicate_ors(Expr *qual, bool is_check)
{
	if (is_orclause(qual))
	{
		List	   *orlist = NIL;
		ListCell   *temp;

		/* Recurse */
		foreach(temp, ((BoolExpr *) qual)->args)
		{
			Expr	   *arg = (Expr *) lfirst(temp);

			arg = find_duplicate_ors(arg, is_check);

			/* Get rid of any constant inputs */
			if (arg && IsA(arg, Const))
			{
				Const	   *carg = (Const *) arg;

				if (is_check)
				{
					/* Within OR in CHECK, drop constant FALSE */
					if (!carg->constisnull && !DatumGetBool(carg->constvalue))
						continue;
					/* Constant TRUE or NULL, so OR reduces to TRUE */
					return (Expr *) makeBoolConst(true, false);
				}
				else
				{
					/* Within OR in WHERE, drop constant FALSE or NULL */
					if (carg->constisnull || !DatumGetBool(carg->constvalue))
						continue;
					/* Constant TRUE, so OR reduces to TRUE */
					return arg;
				}
			}

			orlist = lappend(orlist, arg);
		}

		/* Flatten any ORs pulled up to just below here */
		orlist = pull_ors(orlist);

		/* Now we can look for duplicate ORs */
		return process_duplicate_ors(orlist);
	}
	else if (is_andclause(qual))
	{
		List	   *andlist = NIL;
		ListCell   *temp;

		/* Recurse */
		foreach(temp, ((BoolExpr *) qual)->args)
		{
			Expr	   *arg = (Expr *) lfirst(temp);

			arg = find_duplicate_ors(arg, is_check);

			/* Get rid of any constant inputs */
			if (arg && IsA(arg, Const))
			{
				Const	   *carg = (Const *) arg;

				if (is_check)
				{
					/* Within AND in CHECK, drop constant TRUE or NULL */
					if (carg->constisnull || DatumGetBool(carg->constvalue))
						continue;
					/* Constant FALSE, so AND reduces to FALSE */
					return arg;
				}
				else
				{
					/* Within AND in WHERE, drop constant TRUE */
					if (!carg->constisnull && DatumGetBool(carg->constvalue))
						continue;
					/* Constant FALSE or NULL, so AND reduces to FALSE */
					return (Expr *) makeBoolConst(false, false);
				}
			}

			andlist = lappend(andlist, arg);
		}

		/* Flatten any ANDs introduced just below here */
		andlist = pull_ands(andlist);

		/* AND of no inputs reduces to TRUE */
		if (andlist == NIL)
			return (Expr *) makeBoolConst(true, false);

		/* Single-expression AND just reduces to that expression */
		if (list_length(andlist) == 1)
			return (Expr *) linitial(andlist);

		/* Else we still need an AND node */
		return make_andclause(andlist);
	}
	else
		return qual;
}

/*
 * process_duplicate_ors
 *	  Given a list of exprs which are ORed together, try to apply
 *	  the inverse OR distributive law.
 *
 * Returns the resulting expression (could be an AND clause, an OR
 * clause, or maybe even a single subexpression).
 */
/*
 * process_duplicate_ors - (中文)对展平后的 OR 子句列表应用逆 OR 分配律,
 * 提取所有 OR 分支共有的子句
 *
 * 【作用】输入是若干个表达式(它们将用一个 OR 连接)。算法:选出最短的
 * AND 分支作为"参考列表"(非 AND 分支视为单元素 AND,必然最短);对参考
 * 列表中每个子句,检查它是否出现在每个 OR 分支中(AND 分支用 list_member,
 * 非 AND 分支用 equal 比较);把"全部出现"的子句(winners)提取出来作为
 * 公共因子,其余子句重新组成新的 OR;最终返回公共因子与新 OR 的 AND。
 * 边界情况:OR 为空返回 FALSE;单元素 OR 直接返回该元素;若某分支在去掉
 * 公共因子后变空((A AND B) OR A 的情况),整个表达式化简为公共因子 A。
 *
 * 【设计思想】
 * - 公共子句必须出现在所有分支,因此"最短分支"之外的任何子句都不可能是
 *   公共的,选最短分支作参考可减少比较次数;参考列表先去重(list_union)
 *   避免重复处理;
 * - 用 list_difference 去除分支里的公共子句时,某子句的多次出现会被自动
 *   全部移除(同时去重);
 * - 最终结果用 pull_ors/pull_ands 保证 AND/OR 平坦性,因为上提子子句可能
 *   引入嵌套的 OR/AND。
 *
 * 【参数】orlist —— 将被 OR 连接的表达式列表。
 * 【返回值】变换后的表达式:可能是 AND 子句、OR 子句,甚至单个子表达式或
 * 常量(如所有分支相同时)。
 */
static Expr *
process_duplicate_ors(List *orlist)
{
	List	   *reference = NIL;
	int			num_subclauses = 0;
	List	   *winners;
	List	   *neworlist;
	ListCell   *temp;

	/* OR of no inputs reduces to FALSE */
	if (orlist == NIL)
		return (Expr *) makeBoolConst(false, false);

	/* Single-expression OR just reduces to that expression */
	if (list_length(orlist) == 1)
		return (Expr *) linitial(orlist);

	/*
	 * Choose the shortest AND clause as the reference list --- obviously, any
	 * subclause not in this clause isn't in all the clauses. If we find a
	 * clause that's not an AND, we can treat it as a one-element AND clause,
	 * which necessarily wins as shortest.
	 */
	foreach(temp, orlist)
	{
		Expr	   *clause = (Expr *) lfirst(temp);

		if (is_andclause(clause))
		{
			List	   *subclauses = ((BoolExpr *) clause)->args;
			int			nclauses = list_length(subclauses);

			if (reference == NIL || nclauses < num_subclauses)
			{
				reference = subclauses;
				num_subclauses = nclauses;
			}
		}
		else
		{
			reference = list_make1(clause);
			break;
		}
	}

	/*
	 * Just in case, eliminate any duplicates in the reference list.
	 */
	reference = list_union(NIL, reference);

	/*
	 * Check each element of the reference list to see if it's in all the OR
	 * clauses.  Build a new list of winning clauses.
	 */
	winners = NIL;
	foreach(temp, reference)
	{
		Expr	   *refclause = (Expr *) lfirst(temp);
		bool		win = true;
		ListCell   *temp2;

		foreach(temp2, orlist)
		{
			Expr	   *clause = (Expr *) lfirst(temp2);

			if (is_andclause(clause))
			{
				if (!list_member(((BoolExpr *) clause)->args, refclause))
				{
					win = false;
					break;
				}
			}
			else
			{
				if (!equal(refclause, clause))
				{
					win = false;
					break;
				}
			}
		}

		if (win)
			winners = lappend(winners, refclause);
	}

	/*
	 * If no winners, we can't transform the OR
	 */
	if (winners == NIL)
		return make_orclause(orlist);

	/*
	 * Generate new OR list consisting of the remaining sub-clauses.
	 *
	 * If any clause degenerates to empty, then we have a situation like (A
	 * AND B) OR (A), which can be reduced to just A --- that is, the
	 * additional conditions in other arms of the OR are irrelevant.
	 *
	 * Note that because we use list_difference, any multiple occurrences of a
	 * winning clause in an AND sub-clause will be removed automatically.
	 */
	neworlist = NIL;
	foreach(temp, orlist)
	{
		Expr	   *clause = (Expr *) lfirst(temp);

		if (is_andclause(clause))
		{
			List	   *subclauses = ((BoolExpr *) clause)->args;

			subclauses = list_difference(subclauses, winners);
			if (subclauses != NIL)
			{
				if (list_length(subclauses) == 1)
					neworlist = lappend(neworlist, linitial(subclauses));
				else
					neworlist = lappend(neworlist, make_andclause(subclauses));
			}
			else
			{
				neworlist = NIL;	/* degenerate case, see above */
				break;
			}
		}
		else
		{
			if (!list_member(winners, clause))
				neworlist = lappend(neworlist, clause);
			else
			{
				neworlist = NIL;	/* degenerate case, see above */
				break;
			}
		}
	}

	/*
	 * Append reduced OR to the winners list, if it's not degenerate, handling
	 * the special case of one element correctly (can that really happen?).
	 * Also be careful to maintain AND/OR flatness in case we pulled up a
	 * sub-sub-OR-clause.
	 */
	if (neworlist != NIL)
	{
		if (list_length(neworlist) == 1)
			winners = lappend(winners, linitial(neworlist));
		else
			winners = lappend(winners, make_orclause(pull_ors(neworlist)));
	}

	/*
	 * And return the constructed AND clause, again being wary of a single
	 * element and AND/OR flatness.
	 */
	if (list_length(winners) == 1)
		return (Expr *) linitial(winners);
	else
		return make_andclause(pull_ands(winners));
}
