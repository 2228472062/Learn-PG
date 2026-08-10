/*-------------------------------------------------------------------------
 *
 * rewriteSearchCycle.c
 *		Support for rewriting SEARCH and CYCLE clauses.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/rewrite/rewriteSearchCycle.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "catalog/pg_operator_d.h"
#include "catalog/pg_type_d.h"
#include "nodes/makefuncs.h"
#include "nodes/parsenodes.h"
#include "nodes/pg_list.h"
#include "nodes/primnodes.h"
#include "parser/analyze.h"
#include "parser/parsetree.h"
#include "rewrite/rewriteManip.h"
#include "rewrite/rewriteSearchCycle.h"
#include "utils/fmgroids.h"


/*----------
 * Rewrite a CTE with SEARCH or CYCLE clause
 *
 * Consider a CTE like
 *
 * WITH RECURSIVE ctename (col1, col2, col3) AS (
 *     query1
 *   UNION [ALL]
 *     SELECT trosl FROM ctename
 * )
 *
 * With a search clause
 *
 * SEARCH BREADTH FIRST BY col1, col2 SET sqc
 *
 * the CTE is rewritten to
 *
 * WITH RECURSIVE ctename (col1, col2, col3, sqc) AS (
 *     SELECT col1, col2, col3,               -- original WITH column list
 *            ROW(0, col1, col2)              -- initial row of search columns
 *       FROM (query1) "*TLOCRN*" (col1, col2, col3)
 *   UNION [ALL]
 *     SELECT col1, col2, col3,               -- same as above
 *            ROW(sqc.depth + 1, col1, col2)  -- count depth
 *       FROM (SELECT trosl, ctename.sqc FROM ctename) "*TROCRN*" (col1, col2, col3, sqc)
 * )
 *
 * (This isn't quite legal SQL: sqc.depth is meant to refer to the first
 * column of sqc, which has a row type, but the field names are not defined
 * here.  Representing this properly in SQL would be more complicated (and the
 * SQL standard actually does it in that more complicated way), but the
 * internal representation allows us to construct it this way.)
 *
 * With a search clause
 *
 * SEARCH DEPTH FIRST BY col1, col2 SET sqc
 *
 * the CTE is rewritten to
 *
 * WITH RECURSIVE ctename (col1, col2, col3, sqc) AS (
 *     SELECT col1, col2, col3,               -- original WITH column list
 *            ARRAY[ROW(col1, col2)]          -- initial row of search columns
 *       FROM (query1) "*TLOCRN*" (col1, col2, col3)
 *   UNION [ALL]
 *     SELECT col1, col2, col3,               -- same as above
 *            sqc || ARRAY[ROW(col1, col2)]   -- record rows seen
 *       FROM (SELECT trosl, ctename.sqc FROM ctename) "*TROCRN*" (col1, col2, col3, sqc)
 * )
 *
 * With a cycle clause
 *
 * CYCLE col1, col2 SET cmc TO 'Y' DEFAULT 'N' USING cpa
 *
 * (cmc = cycle mark column, cpa = cycle path) the CTE is rewritten to
 *
 * WITH RECURSIVE ctename (col1, col2, col3, cmc, cpa) AS (
 *     SELECT col1, col2, col3,               -- original WITH column list
 *            'N',                            -- cycle mark default
 *            ARRAY[ROW(col1, col2)]          -- initial row of cycle columns
 *       FROM (query1) "*TLOCRN*" (col1, col2, col3)
 *   UNION [ALL]
 *     SELECT col1, col2, col3,               -- same as above
 *            CASE WHEN ROW(col1, col2) = ANY (ARRAY[cpa]) THEN 'Y' ELSE 'N' END,  -- compute cycle mark column
 *            cpa || ARRAY[ROW(col1, col2)]   -- record rows seen
 *       FROM (SELECT trosl, ctename.cmc, ctename.cpa FROM ctename) "*TROCRN*" (col1, col2, col3, cmc, cpa)
 *       WHERE cmc <> 'Y'
 * )
 *
 * The expression to compute the cycle mark column in the right-hand query is
 * written as
 *
 * CASE WHEN ROW(col1, col2) IN (SELECT p.* FROM TABLE(cpa) p) THEN cmv ELSE cmd END
 *
 * in the SQL standard, but in PostgreSQL we can use the scalar-array operator
 * expression shown above.
 *
 * Also, in some of the cases where operators are shown above we actually
 * directly produce the underlying function call.
 *
 * If both a search clause and a cycle clause is specified, then the search
 * clause column is added before the cycle clause columns.
 */

/*
 * ============================================================================
 * 【中文注释】make_path_rowexpr —— 由列名列表构造行值表达式 RowExpr
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   针对 SEARCH / CYCLE 子句中指定的列集合，构造一个 ROW(...) 行值表达式，用于
 *   表示"当前这一行的搜索/环检测列"。生成的 RowExpr 的元素是引用 CTE 输出列的 Var。
 *
 * 参数：
 *   cte      - 正在改写的有 SEARCH/CYCLE 子句的公共表表达式（提供其输出列名、
 *              类型、typmod、collation 等元数据）。
 *   col_list - 列名字符串列表（如 SEARCH ... BY col1, col2 中的 col1、col2）。
 *
 * 返回值：
 *   RowExpr* - 类型为 RECORDOID 的匿名记录行值表达式；每个元素是对应列的 Var，
 *              列名信息保存在 colnames 中。
 *
 * 设计思想：
 *   1. RowExpr 的行类型用 RECORDOID（匿名记录类型），而不是命名复合类型——因为
 *      这些搜索列来自用户任意指定的列，无法预知固定的命名记录类型；匿名记录类型
 *      配合 colnames 字段即可满足后续构造的需要。
 *   2. 通过两层遍历把 col_list 中的每个列名与 cte->ctecolnames 中的输出列名做
 *      字符串匹配，找到对应的输出位置 i，然后用 makeVar(1, i+1, ...) 生成一个
 *      引用"第 1 个范围表、第 i+1 列"的 Var。这里的 varno 固定取 1，因为该 RowExpr
 *      随后会被塞进左右两个 UNION 分支的查询里，而那两个查询都只有 1 个 RTE
 *      （见 rewriteSearchAndCycle 中对 newq1/newq2 的构造）。
 *   3. colnames 里同时记录用户指定的列名，供后续 FIELD 引用（如 sqc.depth）使用。
 *   注意：此处假定列名一定能匹配上（解析阶段已保证），因此未匹配时静默忽略。
 * ============================================================================
 */
static RowExpr *
make_path_rowexpr(const CommonTableExpr *cte, const List *col_list)
{
	RowExpr    *rowexpr;
	ListCell   *lc;

	rowexpr = makeNode(RowExpr);
	rowexpr->row_typeid = RECORDOID;
	rowexpr->row_format = COERCE_IMPLICIT_CAST;
	rowexpr->location = -1;

	foreach(lc, col_list)
	{
		char	   *colname = strVal(lfirst(lc));

		for (int i = 0; i < list_length(cte->ctecolnames); i++)
		{
			char	   *colname2 = strVal(list_nth(cte->ctecolnames, i));

			if (strcmp(colname, colname2) == 0)
			{
				Var		   *var;

				var = makeVar(1, i + 1,
							  list_nth_oid(cte->ctecoltypes, i),
							  list_nth_int(cte->ctecoltypmods, i),
							  list_nth_oid(cte->ctecolcollations, i),
							  0);
				rowexpr->args = lappend(rowexpr->args, var);
				rowexpr->colnames = lappend(rowexpr->colnames, makeString(colname));
				break;
			}
		}
	}

	return rowexpr;
}

/*
 * ============================================================================
 * 【中文注释】make_path_initial_array —— 把行值包装成单元素数组表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   将表示"一条路径中单个元素"的 RowExpr 包装成 ARRAY[ROWElem] 形式的 ArrayExpr，
 *   作为 SEARCH DEPTH FIRST 或 CYCLE 路径数组的初始值。
 *
 * 参数：
 *   rowexpr - 单个路径元素的行值表达式（见 make_path_rowexpr）。
 *
 * 返回值：
 *   Expr* - 一个 element_typeid 为 RECORDOID、整体类型为 RECORDARRAYOID 的
 *           单元素数组表达式。
 *
 * 设计思想：
 *   SEARCH DEPTH FIRST 与 CYCLE 都以"数组形式记录已走过的行"，路径数组是
 *   record[] 类型。初始化时路径里只有起点这一行，所以直接生成一个仅含一个
 *   RowExpr 的数组即可。写成单元素数组而不是裸的行值，是为了让后续的数组
 *   连接操作（||）类型自洽——连接要求两侧都是数组类型。类型统一采用匿名
 *   记录（RECORDOID / RECORDARRAYOID），与 make_path_rowexpr 保持一致。
 * ============================================================================
 */
static Expr *
make_path_initial_array(RowExpr *rowexpr)
{
	ArrayExpr  *arr;

	arr = makeNode(ArrayExpr);
	arr->array_typeid = RECORDARRAYOID;
	arr->element_typeid = RECORDOID;
	arr->location = -1;
	arr->elements = list_make1(rowexpr);

	return (Expr *) arr;
}

/*
 * ============================================================================
 * 【中文注释】make_path_cat_expr —— 构造路径数组拼接表达式 cpa || ARRAY[ROW(cols)]
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   生成"把当前行的元素追加到已有路径数组末尾"的表达式，即
 *      path_var || ARRAY[ROW(col1, col2, ...)]
 *   其中 path_var 是引用已有路径数组（record[] 类型）的 Var，| | 运算符在内部
 *   表示为 array_cat 函数调用。
 *
 * 参数：
 *   rowexpr       - 当前行元素的行值表达式（来自 make_path_rowexpr）。
 *   path_varattno - 已有路径数组列在范围表中的属性号（varno 固定为 1）。
 *
 * 返回值：
 *   Expr* - array_cat(RECORDARRAYOID, ...) 函数调用表达式。
 *
 * 设计思想：
 *   递归求值时需要"记录每一条走过的路径"，而深度优先搜索与环检测的迭代步要把
 *   当前行追加进路径。这里直接构造底层函数调用 array_cat（F_ARRAY_CAT）而非使用
 *   运算符树，是因为 record[] 的 || 运算解析后本来就是 array_cat，绕开运算符解析
 *   可以直接指定输入/输出类型（都是 RECORDARRAYOID），避免再走一遍类型推断。
 *   左侧参数用 makeVar(1, path_varattno, RECORDARRAYOID, -1, 0, 0) 引用已存在
 *   的路径列，右侧是包裹当前元素的单元素数组。
 * ============================================================================
 */
static Expr *
make_path_cat_expr(RowExpr *rowexpr, AttrNumber path_varattno)
{
	ArrayExpr  *arr;
	FuncExpr   *fexpr;

	arr = makeNode(ArrayExpr);
	arr->array_typeid = RECORDARRAYOID;
	arr->element_typeid = RECORDOID;
	arr->location = -1;
	arr->elements = list_make1(rowexpr);

	fexpr = makeFuncExpr(F_ARRAY_CAT, RECORDARRAYOID,
						 list_make2(makeVar(1, path_varattno, RECORDARRAYOID, -1, 0, 0),
									arr),
						 InvalidOid, InvalidOid, COERCE_EXPLICIT_CALL);

	return (Expr *) fexpr;
}

/*
 * ============================================================================
 * 【中文注释】rewriteSearchAndCycle —— SEARCH/CYCLE 子句改写的核心实现
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把带 SEARCH 或 CYCLE 子句的递归 CTE 改写成等价的、只在内部使用 UNION 的
 *   递归 CTE：通过给 CTE 的输出列追加额外列（搜索序列列 / 环标记列 / 环路径列），
 *   并改写左右两个 UNION 分支的查询体，实现在递归过程中记录搜索顺序与检测环路。
 *   具体改写形式见本文件顶部的示意注释。
 *
 * 参数：
 *   cte - 待改写的 CommonTableExpr；其 ctequery 必须是顶层为 UNION 的递归查询，
 *         且至少带 search_clause 或 cycle_clause 之一。
 *
 * 返回值：
 *   CommonTableExpr* - 改写后的新 CTE（输入对象会被复制，不修改原对象）。
 *
 * 设计思想：
 *   整体策略是"把搜索/环检测语义下沉为普通列运算"，让递归执行引擎完全不用感知
 *   SEARCH/CYCLE 的存在。具体分四步：
 *   1. 计算追加列的属性号：先放搜索序列列（sqc），再放环标记列（cmc）与环路径
 *      列（cpa）；若同时有 SEARCH 与 CYCLE，环的两列顺延一位（文件头注释明确：
 *      搜索列在环列之前）。
 *   2. 改写左分支（非递归项，初值）：把原始查询包成子查询（*TLOCRN*），对原
 *      WITH 列做透传，并追加各额外列的初始值——广度优先搜索为 ROW(0, cols)，
 *      深度优先搜索为 ARRAY[ROW(cols)]，CYCLE 为环标记默认值 + ARRAY[ROW(cols)]。
 *   3. 改写右分支（递归项，迭代步）：包成子查询（*TROCRN*），透传原列与上一步
 *      的额外列，再重新计算：搜索列为 sqc.depth+1（广度优先，取 RowExpr 第一字段
 *      自增）或 sqc || ARRAY[ROW(cols)]（深度优先）；环标记列为
 *      CASE WHEN ROW(cols) = ANY(cpa) THEN cmv ELSE cmd END；环路径列为
 *      cpa || ARRAY[ROW(cols)]。若带 CYCLE，还在 FROM 上加 cmc <> cmv 的 WHERE
 *      条件，用于剪枝已访问过的行。
 *   4. 同步更新各结构：SetOperationStmt 的列类型列表（含 DISTINCT 时的分组子句）、
 *      CTE 查询的 targetList、以及 cte 的输出列列表（ctecolnames/types/typmods/
 *      collations），使 CTE 对外暴露的列集合与内部一致。
 *
 * 细节说明：
 *   - 引用递归 CTE 的 Var 使用 ctelevelsup=2（在右分支子查询内部向上两级可见），
 *     且通过 RTE_CTE 类型与名称匹配来定位；找不到（递归引用不在右分支最顶层
 *     范围表）时按"暂未实现"报错。
 *   - 追加列做 VarSublevelsUp 提升时统一 +1，因为右分支的子查询被嵌套进了新的
 *     一层 RTE 子查询中。
 * ============================================================================
 */
CommonTableExpr *
rewriteSearchAndCycle(CommonTableExpr *cte)
{
	Query	   *ctequery;
	SetOperationStmt *sos;
	int			rti1,
				rti2;
	RangeTblEntry *rte1,
			   *rte2,
			   *newrte;
	Query	   *newq1,
			   *newq2;
	Query	   *newsubquery;
	RangeTblRef *rtr;
	Oid			search_seq_type = InvalidOid;
	AttrNumber	sqc_attno = InvalidAttrNumber;
	AttrNumber	cmc_attno = InvalidAttrNumber;
	AttrNumber	cpa_attno = InvalidAttrNumber;
	TargetEntry *tle;
	RowExpr    *cycle_col_rowexpr = NULL;
	RowExpr    *search_col_rowexpr = NULL;
	List	   *ewcl;
	int			cte_rtindex = -1;

	Assert(cte->search_clause || cte->cycle_clause);

	cte = copyObject(cte);

	ctequery = castNode(Query, cte->ctequery);

	/*
	 * The top level of the CTE's query should be a UNION.  Find the two
	 * subqueries.
	 */
	Assert(ctequery->setOperations);
	sos = castNode(SetOperationStmt, ctequery->setOperations);
	Assert(sos->op == SETOP_UNION);

	rti1 = castNode(RangeTblRef, sos->larg)->rtindex;
	rti2 = castNode(RangeTblRef, sos->rarg)->rtindex;

	rte1 = rt_fetch(rti1, ctequery->rtable);
	rte2 = rt_fetch(rti2, ctequery->rtable);

	Assert(rte1->rtekind == RTE_SUBQUERY);
	Assert(rte2->rtekind == RTE_SUBQUERY);

	/*
	 * We'll need this a few times later.
	 */
	if (cte->search_clause)
	{
		if (cte->search_clause->search_breadth_first)
			search_seq_type = RECORDOID;
		else
			search_seq_type = RECORDARRAYOID;
	}

	/*
	 * Attribute numbers of the added columns in the CTE's column list
	 */
	if (cte->search_clause)
		sqc_attno = list_length(cte->ctecolnames) + 1;
	if (cte->cycle_clause)
	{
		cmc_attno = list_length(cte->ctecolnames) + 1;
		cpa_attno = list_length(cte->ctecolnames) + 2;
		if (cte->search_clause)
		{
			cmc_attno++;
			cpa_attno++;
		}
	}

	/*
	 * Make new left subquery
	 */
	newq1 = makeNode(Query);
	newq1->commandType = CMD_SELECT;
	newq1->canSetTag = true;

	newrte = makeNode(RangeTblEntry);
	newrte->rtekind = RTE_SUBQUERY;
	newrte->alias = NULL;
	newrte->eref = makeAlias("*TLOCRN*", cte->ctecolnames);
	newsubquery = copyObject(rte1->subquery);
	IncrementVarSublevelsUp((Node *) newsubquery, 1, 1);
	newrte->subquery = newsubquery;
	newrte->inFromCl = true;
	newq1->rtable = list_make1(newrte);

	rtr = makeNode(RangeTblRef);
	rtr->rtindex = 1;
	newq1->jointree = makeFromExpr(list_make1(rtr), NULL);

	/*
	 * Make target list
	 */
	for (int i = 0; i < list_length(cte->ctecolnames); i++)
	{
		Var		   *var;

		var = makeVar(1, i + 1,
					  list_nth_oid(cte->ctecoltypes, i),
					  list_nth_int(cte->ctecoltypmods, i),
					  list_nth_oid(cte->ctecolcollations, i),
					  0);
		tle = makeTargetEntry((Expr *) var, i + 1, strVal(list_nth(cte->ctecolnames, i)), false);
		tle->resorigtbl = list_nth_node(TargetEntry, rte1->subquery->targetList, i)->resorigtbl;
		tle->resorigcol = list_nth_node(TargetEntry, rte1->subquery->targetList, i)->resorigcol;
		newq1->targetList = lappend(newq1->targetList, tle);
	}

	if (cte->search_clause)
	{
		Expr	   *texpr;

		search_col_rowexpr = make_path_rowexpr(cte, cte->search_clause->search_col_list);
		if (cte->search_clause->search_breadth_first)
		{
			search_col_rowexpr->args = lcons(makeConst(INT8OID, -1, InvalidOid, sizeof(int64),
													   Int64GetDatum(0), false, true),
											 search_col_rowexpr->args);
			search_col_rowexpr->colnames = lcons(makeString("*DEPTH*"), search_col_rowexpr->colnames);
			texpr = (Expr *) search_col_rowexpr;
		}
		else
			texpr = make_path_initial_array(search_col_rowexpr);
		tle = makeTargetEntry(texpr,
							  list_length(newq1->targetList) + 1,
							  cte->search_clause->search_seq_column,
							  false);
		newq1->targetList = lappend(newq1->targetList, tle);
	}
	if (cte->cycle_clause)
	{
		tle = makeTargetEntry((Expr *) cte->cycle_clause->cycle_mark_default,
							  list_length(newq1->targetList) + 1,
							  cte->cycle_clause->cycle_mark_column,
							  false);
		newq1->targetList = lappend(newq1->targetList, tle);
		cycle_col_rowexpr = make_path_rowexpr(cte, cte->cycle_clause->cycle_col_list);
		tle = makeTargetEntry(make_path_initial_array(cycle_col_rowexpr),
							  list_length(newq1->targetList) + 1,
							  cte->cycle_clause->cycle_path_column,
							  false);
		newq1->targetList = lappend(newq1->targetList, tle);
	}

	rte1->subquery = newq1;

	if (cte->search_clause)
	{
		rte1->eref->colnames = lappend(rte1->eref->colnames, makeString(cte->search_clause->search_seq_column));
	}
	if (cte->cycle_clause)
	{
		rte1->eref->colnames = lappend(rte1->eref->colnames, makeString(cte->cycle_clause->cycle_mark_column));
		rte1->eref->colnames = lappend(rte1->eref->colnames, makeString(cte->cycle_clause->cycle_path_column));
	}

	/*
	 * Make new right subquery
	 */
	newq2 = makeNode(Query);
	newq2->commandType = CMD_SELECT;
	newq2->canSetTag = true;

	newrte = makeNode(RangeTblEntry);
	newrte->rtekind = RTE_SUBQUERY;
	ewcl = copyObject(cte->ctecolnames);
	if (cte->search_clause)
	{
		ewcl = lappend(ewcl, makeString(cte->search_clause->search_seq_column));
	}
	if (cte->cycle_clause)
	{
		ewcl = lappend(ewcl, makeString(cte->cycle_clause->cycle_mark_column));
		ewcl = lappend(ewcl, makeString(cte->cycle_clause->cycle_path_column));
	}
	newrte->alias = NULL;
	newrte->eref = makeAlias("*TROCRN*", ewcl);

	/*
	 * Find the reference to the recursive CTE in the right UNION subquery's
	 * range table.  We expect it to be two levels up from the UNION subquery
	 * (and must check that to avoid being fooled by sub-WITHs with the same
	 * CTE name).  There will not be more than one such reference, because the
	 * parser would have rejected that (see checkWellFormedRecursion() in
	 * parse_cte.c).  However, the parser doesn't insist that the reference
	 * appear in the UNION subquery's topmost range table, so we might fail to
	 * find it at all.  That's an unimplemented case for the moment.
	 */
	for (int rti = 1; rti <= list_length(rte2->subquery->rtable); rti++)
	{
		RangeTblEntry *e = rt_fetch(rti, rte2->subquery->rtable);

		if (e->rtekind == RTE_CTE &&
			strcmp(cte->ctename, e->ctename) == 0 &&
			e->ctelevelsup == 2)
		{
			cte_rtindex = rti;
			break;
		}
	}
	if (cte_rtindex <= 0)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("with a SEARCH or CYCLE clause, the recursive reference to WITH query \"%s\" must be at the top level of its right-hand SELECT",
						cte->ctename)));

	newsubquery = copyObject(rte2->subquery);
	IncrementVarSublevelsUp((Node *) newsubquery, 1, 1);

	/*
	 * Add extra columns to target list of subquery of right subquery
	 */
	if (cte->search_clause)
	{
		Var		   *var;

		/* ctename.sqc */
		var = makeVar(cte_rtindex, sqc_attno,
					  search_seq_type, -1, InvalidOid, 0);
		tle = makeTargetEntry((Expr *) var,
							  list_length(newsubquery->targetList) + 1,
							  cte->search_clause->search_seq_column,
							  false);
		newsubquery->targetList = lappend(newsubquery->targetList, tle);
	}
	if (cte->cycle_clause)
	{
		Var		   *var;

		/* ctename.cmc */
		var = makeVar(cte_rtindex, cmc_attno,
					  cte->cycle_clause->cycle_mark_type,
					  cte->cycle_clause->cycle_mark_typmod,
					  cte->cycle_clause->cycle_mark_collation, 0);
		tle = makeTargetEntry((Expr *) var,
							  list_length(newsubquery->targetList) + 1,
							  cte->cycle_clause->cycle_mark_column,
							  false);
		newsubquery->targetList = lappend(newsubquery->targetList, tle);

		/* ctename.cpa */
		var = makeVar(cte_rtindex, cpa_attno,
					  RECORDARRAYOID, -1, InvalidOid, 0);
		tle = makeTargetEntry((Expr *) var,
							  list_length(newsubquery->targetList) + 1,
							  cte->cycle_clause->cycle_path_column,
							  false);
		newsubquery->targetList = lappend(newsubquery->targetList, tle);
	}

	newrte->subquery = newsubquery;
	newrte->inFromCl = true;
	newq2->rtable = list_make1(newrte);

	rtr = makeNode(RangeTblRef);
	rtr->rtindex = 1;

	if (cte->cycle_clause)
	{
		Expr	   *expr;

		/*
		 * Add cmc <> cmv condition
		 */
		expr = make_opclause(cte->cycle_clause->cycle_mark_neop, BOOLOID, false,
							 (Expr *) makeVar(1, cmc_attno,
											  cte->cycle_clause->cycle_mark_type,
											  cte->cycle_clause->cycle_mark_typmod,
											  cte->cycle_clause->cycle_mark_collation, 0),
							 (Expr *) cte->cycle_clause->cycle_mark_value,
							 InvalidOid,
							 cte->cycle_clause->cycle_mark_collation);

		newq2->jointree = makeFromExpr(list_make1(rtr), (Node *) expr);
	}
	else
		newq2->jointree = makeFromExpr(list_make1(rtr), NULL);

	/*
	 * Make target list
	 */
	for (int i = 0; i < list_length(cte->ctecolnames); i++)
	{
		Var		   *var;

		var = makeVar(1, i + 1,
					  list_nth_oid(cte->ctecoltypes, i),
					  list_nth_int(cte->ctecoltypmods, i),
					  list_nth_oid(cte->ctecolcollations, i),
					  0);
		tle = makeTargetEntry((Expr *) var, i + 1, strVal(list_nth(cte->ctecolnames, i)), false);
		tle->resorigtbl = list_nth_node(TargetEntry, rte2->subquery->targetList, i)->resorigtbl;
		tle->resorigcol = list_nth_node(TargetEntry, rte2->subquery->targetList, i)->resorigcol;
		newq2->targetList = lappend(newq2->targetList, tle);
	}

	if (cte->search_clause)
	{
		Expr	   *texpr;

		if (cte->search_clause->search_breadth_first)
		{
			FieldSelect *fs;
			FuncExpr   *fexpr;

			/*
			 * ROW(sqc.depth + 1, cols)
			 */

			search_col_rowexpr = copyObject(search_col_rowexpr);

			fs = makeNode(FieldSelect);
			fs->arg = (Expr *) makeVar(1, sqc_attno, RECORDOID, -1, 0, 0);
			fs->fieldnum = 1;
			fs->resulttype = INT8OID;
			fs->resulttypmod = -1;

			fexpr = makeFuncExpr(F_INT8INC, INT8OID, list_make1(fs), InvalidOid, InvalidOid, COERCE_EXPLICIT_CALL);

			linitial(search_col_rowexpr->args) = fexpr;

			texpr = (Expr *) search_col_rowexpr;
		}
		else
		{
			/*
			 * sqc || ARRAY[ROW(cols)]
			 */
			texpr = make_path_cat_expr(search_col_rowexpr, sqc_attno);
		}
		tle = makeTargetEntry(texpr,
							  list_length(newq2->targetList) + 1,
							  cte->search_clause->search_seq_column,
							  false);
		newq2->targetList = lappend(newq2->targetList, tle);
	}

	if (cte->cycle_clause)
	{
		ScalarArrayOpExpr *saoe;
		CaseExpr   *caseexpr;
		CaseWhen   *casewhen;

		/*
		 * CASE WHEN ROW(cols) = ANY (ARRAY[cpa]) THEN cmv ELSE cmd END
		 */

		saoe = makeNode(ScalarArrayOpExpr);
		saoe->location = -1;
		saoe->opno = RECORD_EQ_OP;
		saoe->useOr = true;
		saoe->args = list_make2(cycle_col_rowexpr,
								makeVar(1, cpa_attno, RECORDARRAYOID, -1, 0, 0));

		caseexpr = makeNode(CaseExpr);
		caseexpr->location = -1;
		caseexpr->casetype = cte->cycle_clause->cycle_mark_type;
		caseexpr->casecollid = cte->cycle_clause->cycle_mark_collation;
		casewhen = makeNode(CaseWhen);
		casewhen->location = -1;
		casewhen->expr = (Expr *) saoe;
		casewhen->result = (Expr *) cte->cycle_clause->cycle_mark_value;
		caseexpr->args = list_make1(casewhen);
		caseexpr->defresult = (Expr *) cte->cycle_clause->cycle_mark_default;

		tle = makeTargetEntry((Expr *) caseexpr,
							  list_length(newq2->targetList) + 1,
							  cte->cycle_clause->cycle_mark_column,
							  false);
		newq2->targetList = lappend(newq2->targetList, tle);

		/*
		 * cpa || ARRAY[ROW(cols)]
		 */
		tle = makeTargetEntry(make_path_cat_expr(cycle_col_rowexpr, cpa_attno),
							  list_length(newq2->targetList) + 1,
							  cte->cycle_clause->cycle_path_column,
							  false);
		newq2->targetList = lappend(newq2->targetList, tle);
	}

	rte2->subquery = newq2;

	if (cte->search_clause)
	{
		rte2->eref->colnames = lappend(rte2->eref->colnames, makeString(cte->search_clause->search_seq_column));
	}
	if (cte->cycle_clause)
	{
		rte2->eref->colnames = lappend(rte2->eref->colnames, makeString(cte->cycle_clause->cycle_mark_column));
		rte2->eref->colnames = lappend(rte2->eref->colnames, makeString(cte->cycle_clause->cycle_path_column));
	}

	/*
	 * Add the additional columns to the SetOperationStmt
	 */
	if (cte->search_clause)
	{
		sos->colTypes = lappend_oid(sos->colTypes, search_seq_type);
		sos->colTypmods = lappend_int(sos->colTypmods, -1);
		sos->colCollations = lappend_oid(sos->colCollations, InvalidOid);
		if (!sos->all)
			sos->groupClauses = lappend(sos->groupClauses,
										makeSortGroupClauseForSetOp(search_seq_type, true));
	}
	if (cte->cycle_clause)
	{
		sos->colTypes = lappend_oid(sos->colTypes, cte->cycle_clause->cycle_mark_type);
		sos->colTypmods = lappend_int(sos->colTypmods, cte->cycle_clause->cycle_mark_typmod);
		sos->colCollations = lappend_oid(sos->colCollations, cte->cycle_clause->cycle_mark_collation);
		if (!sos->all)
			sos->groupClauses = lappend(sos->groupClauses,
										makeSortGroupClauseForSetOp(cte->cycle_clause->cycle_mark_type, true));

		sos->colTypes = lappend_oid(sos->colTypes, RECORDARRAYOID);
		sos->colTypmods = lappend_int(sos->colTypmods, -1);
		sos->colCollations = lappend_oid(sos->colCollations, InvalidOid);
		if (!sos->all)
			sos->groupClauses = lappend(sos->groupClauses,
										makeSortGroupClauseForSetOp(RECORDARRAYOID, true));
	}

	/*
	 * Add the additional columns to the CTE query's target list
	 */
	if (cte->search_clause)
	{
		ctequery->targetList = lappend(ctequery->targetList,
									   makeTargetEntry((Expr *) makeVar(1, sqc_attno,
																		search_seq_type, -1, InvalidOid, 0),
													   list_length(ctequery->targetList) + 1,
													   cte->search_clause->search_seq_column,
													   false));
	}
	if (cte->cycle_clause)
	{
		ctequery->targetList = lappend(ctequery->targetList,
									   makeTargetEntry((Expr *) makeVar(1, cmc_attno,
																		cte->cycle_clause->cycle_mark_type,
																		cte->cycle_clause->cycle_mark_typmod,
																		cte->cycle_clause->cycle_mark_collation, 0),
													   list_length(ctequery->targetList) + 1,
													   cte->cycle_clause->cycle_mark_column,
													   false));
		ctequery->targetList = lappend(ctequery->targetList,
									   makeTargetEntry((Expr *) makeVar(1, cpa_attno,
																		RECORDARRAYOID, -1, InvalidOid, 0),
													   list_length(ctequery->targetList) + 1,
													   cte->cycle_clause->cycle_path_column,
													   false));
	}

	/*
	 * Add the additional columns to the CTE's output columns
	 */
	cte->ctecolnames = ewcl;
	if (cte->search_clause)
	{
		cte->ctecoltypes = lappend_oid(cte->ctecoltypes, search_seq_type);
		cte->ctecoltypmods = lappend_int(cte->ctecoltypmods, -1);
		cte->ctecolcollations = lappend_oid(cte->ctecolcollations, InvalidOid);
	}
	if (cte->cycle_clause)
	{
		cte->ctecoltypes = lappend_oid(cte->ctecoltypes, cte->cycle_clause->cycle_mark_type);
		cte->ctecoltypmods = lappend_int(cte->ctecoltypmods, cte->cycle_clause->cycle_mark_typmod);
		cte->ctecolcollations = lappend_oid(cte->ctecolcollations, cte->cycle_clause->cycle_mark_collation);

		cte->ctecoltypes = lappend_oid(cte->ctecoltypes, RECORDARRAYOID);
		cte->ctecoltypmods = lappend_int(cte->ctecoltypmods, -1);
		cte->ctecolcollations = lappend_oid(cte->ctecolcollations, InvalidOid);
	}

	return cte;
}
