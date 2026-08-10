/*-------------------------------------------------------------------------
 *
 * rewriteGraphTable.c
 *		Support for rewriting GRAPH_TABLE clauses.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/rewrite/rewriteGraphTable.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/genam.h"
#include "access/sysattr.h"
#include "access/table.h"
#include "access/htup_details.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_propgraph_element.h"
#include "catalog/pg_propgraph_element_label.h"
#include "catalog/pg_propgraph_label.h"
#include "catalog/pg_propgraph_label_property.h"
#include "catalog/pg_propgraph_property.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/optimizer.h"
#include "parser/analyze.h"
#include "parser/parse_collate.h"
#include "parser/parse_func.h"
#include "parser/parse_node.h"
#include "parser/parse_oper.h"
#include "parser/parse_relation.h"
#include "parser/parsetree.h"
#include "parser/parse_graphtable.h"
#include "rewrite/rewriteGraphTable.h"
#include "rewrite/rewriteHandler.h"
#include "rewrite/rewriteManip.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/lsyscache.h"
#include "utils/ruleutils.h"
#include "utils/syscache.h"


/*
 * Represents one path factor in a path.
 *
 * In a non-cyclic path, one path factor corresponds to one element pattern.
 *
 * In a cyclic path, one path factor corresponds to all the element patterns with
 * the same variable name.
 */
struct path_factor
{
	GraphElementPatternKind kind;
	const char *variable;
	Node	   *labelexpr;
	Node	   *whereClause;
	int			factorpos;		/* Position of this path factor in the list of
								 * path factors representing a given path
								 * pattern. */
	List	   *labeloids;		/* OIDs of all the labels referenced in
								 * labelexpr. */
	/* Links to adjacent vertex path factors if this is an edge path factor. */
	struct path_factor *src_pf;
	struct path_factor *dest_pf;
};

/*
 * Represents one property graph element (vertex or edge) in the path.
 *
 * Label expression in an element pattern resolves into a set of elements. We
 * create one path_element object for each of those elements.
 */
struct path_element
{
	/* Path factor from which this element is derived. */
	struct path_factor *path_factor;
	Oid			elemoid;
	Oid			reloid;
	/* Source and destination vertex elements for an edge element. */
	Oid			srcvertexid;
	Oid			destvertexid;
	/* Source and destination conditions for an edge element. */
	List	   *src_quals;
	List	   *dest_quals;
};

static Node *replace_property_refs(Oid propgraphid, Node *node, const List *mappings);
static List *build_edge_vertex_link_quals(HeapTuple edgetup, int edgerti, int refrti, Oid refid, AttrNumber catalog_key_attnum, AttrNumber catalog_ref_attnum, AttrNumber catalog_eqop_attnum);
static List *generate_queries_for_path_pattern(RangeTblEntry *rte, List *path_pattern);
static Query *generate_query_for_graph_path(RangeTblEntry *rte, List *graph_path);
static Node *generate_setop_from_pathqueries(List *pathqueries, List **rtable, List **targetlist);
static List *generate_queries_for_path_pattern_recurse(RangeTblEntry *rte, List *pathqueries, List *cur_path, List *path_elem_lists, int elempos);
static Query *generate_query_for_empty_path_pattern(RangeTblEntry *rte);
static Query *generate_union_from_pathqueries(List **pathqueries);
static List *get_path_elements_for_path_factor(Oid propgraphid, struct path_factor *pf);
static bool is_property_associated_with_label(Oid labeloid, Oid propoid);
static Node *get_element_property_expr(Oid elemoid, Oid propoid, int rtindex);

/*
 * ============================================================================
 * 【中文注释】rewriteGraphTable —— 把 GRAPH_TABLE 子句改写为关系算子构成的子查询
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   本函数是 GRAPH_TABLE 改写流程的总入口。它读取语法分析阶段生成、挂在 RTE 上的
 *   graph_pattern（属性图的路径模式），调用后续的生成函数把它改写成一个普通的 SQL
 *   子查询（Query 树），然后把外层 RTE 从图类型改造成 RTE_SUBQUERY，使后续的重写/
 *   规划阶段可以完全按普通子查询来处理，达到"图查询也走标准 SQL 管道"的目的。
 *
 * 参数：
 *   parsetree - 正在被重写（rewrite）的顶层查询树（Query）。
 *   rt_index  - parsetree->rtable 中表示 GRAPH_TABLE 子句的那个 RangeTblEntry 的下标。
 *
 * 返回值：
 *   返回修改后的 parsetree；被改写后的 GRAPH_TABLE 相关字段（graph_pattern、
 *   graph_table_columns）会被清空，替换为 rte->subquery。
 *
 * 设计思想：
 *   1. 流程串起三个子步骤：先由 generate_queries_for_path_pattern() 把路径模式展开
 *      为"每条匹配路径对应一条 SELECT 查询"的 Query 列表；再由
 *      generate_union_from_pathqueries() 把这些路径查询用 UNION ALL 或单条查询合并；
 *      最后对合并结果调用 AcquireRewriteLocks() 统一加锁并装配进外层 RTE。
 *   2. 目前仅支持单个路径模式（path_pattern_list 长度恒为 1，用 Assert 与解析器的
 *      保证相呼应）；多个路径模式是未来的扩展方向。
 *   3. 改写完成后把 RTE 置为 RTE_SUBQUERY 并把 graph_pattern 置空，这是为了配合
 *      WRITE_READ_PARSE_PLAN_TREES（写读检查）时能通过节点相等性校验，也防止后续
 *      阶段再次对 GRAPH_TABLE 语义做处理。
 *   4. rte->lateral = true 表明该子查询可能引用同层其它 FROM 项（如横向引用）。
 * ============================================================================
 */
Query *
rewriteGraphTable(Query *parsetree, int rt_index)
{
	RangeTblEntry *rte;
	Query	   *graph_table_query;
	List	   *path_pattern;
	List	   *pathqueries = NIL;

	rte = rt_fetch(rt_index, parsetree->rtable);

	Assert(list_length(rte->graph_pattern->path_pattern_list) == 1);

	path_pattern = linitial(rte->graph_pattern->path_pattern_list);
	pathqueries = generate_queries_for_path_pattern(rte, path_pattern);
	graph_table_query = generate_union_from_pathqueries(&pathqueries);

	AcquireRewriteLocks(graph_table_query, true, false);

	rte->rtekind = RTE_SUBQUERY;
	rte->subquery = graph_table_query;
	rte->lateral = true;

	/*
	 * Reset no longer applicable fields, to appease
	 * WRITE_READ_PARSE_PLAN_TREES.
	 */
	rte->graph_pattern = NULL;
	rte->graph_table_columns = NIL;

	return parsetree;
}

/*
 * ============================================================================
 * 【中文注释】generate_queries_for_path_pattern —— 为一个路径模式生成所有匹配路径的查询
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把一个路径模式（path pattern，由若干元素模式 element pattern 组成）应用在指定
 *   属性图上，枚举出所有可能满足该模式的路径（path），并为每条路径生成一条 SELECT
 *   查询。返回这些查询组成的列表；若一条路径都匹配不上，则返回一条恒空的哑查询。
 *
 * 参数：
 *   rte          - 表示 GRAPH_TABLE 子句的 RangeTblEntry，其中挂有 graph_pattern。
 *   path_pattern - GraphElementPattern 节点的列表，描述构成路径的元素模式序列。
 *
 * 返回值：
 *   List *（元素为 Query）—— 每条匹配路径对应一条查询；无匹配时返回单元素列表
 *   （该元素由 generate_query_for_empty_path_pattern() 生成）。
 *
 * 设计思想：
 *   1. 第一步做"路径因子（path factor）"的规整：把具有相同变量名的元素模式合并为
 *      同一个 path_factor，并把相邻的顶点/边路径因子两两链接（src_pf/dest_pf），
 *      形成路径因子层面的图结构。同一变量的多个元素模式被解析器约束为同一组图元素。
 *   2. 合并时要检查一致性：同名元素模式必须同类型（都是顶点或都是边），且标签表达式
 *      必须兼容；标签表达式合并成合取（AND），whereClause 也合并成合取。不支持的
 *      情况（如同一变量出现两种标签表达式）直接报错。
 *   3. 边只能连接两个顶点，若同一边路径因子被两个不同顶点因子连接（循环模式），
 *      按标准报错拒绝。方向处理上，边模式向左/向右/任意方向的约定通过 src_pf/dest_pf
 *      体现：RIGHT 或 ANY 的边，前一个因子是 src（源）；LEFT 的边前一个因子是 dest。
 *   4. 第二步对每个路径因子收集其可解析出的全部图元素（get_path_elements_for_path_factor），
 *      得到"每个位置可选的元素集合"列表 path_elem_lists。
 *   5. 第三步调用 generate_queries_for_path_pattern_recurse() 做 DFS 递归枚举：
 *      每个路径因子位置任取一个元素，组合成一条完整路径；"位置数 × 每位置可选元素数"
 *      的笛卡尔积即所有可能的路径。每条完整路径交给 generate_query_for_graph_path()
 *      生成查询。
 *   6. 递归返回空（说明某位置没有可用元素，或边无法连接相邻顶点）时，退化返回
 *      恒空查询，保证外层仍能构造出合法的 UNION 结构。
 * ============================================================================
 */
static List *
generate_queries_for_path_pattern(RangeTblEntry *rte, List *path_pattern)
{
	List	   *pathqueries = NIL;
	List	   *path_elem_lists = NIL;
	int			factorpos = 0;
	List	   *path_factors = NIL;
	struct path_factor *prev_pf = NULL;

	Assert(list_length(path_pattern) > 0);

	/*
	 * Create a list of path factors representing the given path pattern
	 * linking edge path factors to their adjacent vertex path factors.
	 *
	 * While doing that merge element patterns with the same variable name
	 * into a single path_factor.
	 */
	foreach_node(GraphElementPattern, gep, path_pattern)
	{
		struct path_factor *pf = NULL;

		/*
		 * Unsupported conditions should have been caught by the parser
		 * itself. We have corresponding Asserts here to document the
		 * assumptions in this code.
		 */
		Assert(gep->kind == VERTEX_PATTERN || IS_EDGE_PATTERN(gep->kind));
		Assert(!gep->quantifier);

		foreach_ptr(struct path_factor, other, path_factors)
		{
			if (gep->variable && other->variable &&
				strcmp(gep->variable, other->variable) == 0)
			{
				if (other->kind != gep->kind)
					ereport(ERROR,
							(errcode(ERRCODE_WRONG_OBJECT_TYPE),
							 errmsg("element patterns with same variable name \"%s\" but different element pattern types",
									gep->variable)));

				/*
				 * If both the element patterns have label expressions, they
				 * need to be conjuncted, which is not supported right now.
				 *
				 * However, an empty label expression means all labels.
				 * Conjunction of any label expression with all labels is the
				 * expression itself. Hence if only one of the two element
				 * patterns has a label expression use that expression.
				 */
				if (!other->labelexpr)
					other->labelexpr = gep->labelexpr;
				else if (gep->labelexpr && !equal(other->labelexpr, gep->labelexpr))
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("element patterns with same variable name \"%s\" but different label expressions are not supported",
									gep->variable)));

				/*
				 * If two element patterns have the same variable name, they
				 * represent the same set of graph elements and hence are
				 * constrained by conditions from both the element patterns.
				 */
				if (!other->whereClause)
					other->whereClause = gep->whereClause;
				else if (gep->whereClause)
					other->whereClause = (Node *) makeBoolExpr(AND_EXPR,
															   list_make2(other->whereClause, gep->whereClause),
															   -1);
				pf = other;
				break;
			}
		}

		if (!pf)
		{
			pf = palloc0_object(struct path_factor);
			pf->factorpos = factorpos++;
			pf->kind = gep->kind;
			pf->labelexpr = gep->labelexpr;
			pf->variable = gep->variable;
			pf->whereClause = gep->whereClause;

			path_factors = lappend(path_factors, pf);
		}

		/*
		 * Setup links to the previous path factor in the path.
		 *
		 * If the previous path factor represents an edge, this path factor
		 * represents an adjacent vertex; the source vertex for an edge
		 * pointing left or the destination vertex for an edge pointing right.
		 * If this path factor represents an edge, the previous path factor
		 * represents an adjacent vertex; source vertex for an edge pointing
		 * right or the destination vertex for an edge pointing left.
		 *
		 * Edge pointing in any direction is treated similar to that pointing
		 * in right direction here.  When constructing a query in
		 * generate_query_for_graph_path(), we will try links in both the
		 * directions.
		 *
		 * If multiple edge patterns share the same variable name, they
		 * constrain the adjacent vertex patterns since an edge can connect
		 * only one pair of vertices. These adjacent vertex patterns need to
		 * be merged even though they have different variables. Such element
		 * patterns form a walk of graph where vertex and edges are repeated.
		 * For example, in (a)-[b]->(c)<-[b]-(d), (a) and (d) represent the
		 * same vertex element. This is slightly harder to implement and
		 * probably less useful. Hence not supported for now.
		 */
		if (prev_pf)
		{
			if (prev_pf->kind == EDGE_PATTERN_RIGHT || prev_pf->kind == EDGE_PATTERN_ANY)
			{
				Assert(!IS_EDGE_PATTERN(pf->kind));
				if (prev_pf->dest_pf && prev_pf->dest_pf != pf)
					ereport(ERROR,
							errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
							errmsg("an edge cannot connect more than two vertices even in a cyclic pattern"));
				prev_pf->dest_pf = pf;
			}
			else if (prev_pf->kind == EDGE_PATTERN_LEFT)
			{
				Assert(!IS_EDGE_PATTERN(pf->kind));
				if (prev_pf->src_pf && prev_pf->src_pf != pf)
					ereport(ERROR,
							errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
							errmsg("an edge cannot connect more than two vertices even in a cyclic pattern"));
				prev_pf->src_pf = pf;
			}
			else
			{
				Assert(prev_pf->kind == VERTEX_PATTERN);
				Assert(IS_EDGE_PATTERN(pf->kind));
			}

			if (pf->kind == EDGE_PATTERN_RIGHT || pf->kind == EDGE_PATTERN_ANY)
			{
				Assert(!IS_EDGE_PATTERN(prev_pf->kind));
				if (pf->src_pf && pf->src_pf != prev_pf)
					ereport(ERROR,
							errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
							errmsg("an edge cannot connect more than two vertices even in a cyclic pattern"));
				pf->src_pf = prev_pf;
			}
			else if (pf->kind == EDGE_PATTERN_LEFT)
			{
				Assert(!IS_EDGE_PATTERN(prev_pf->kind));
				if (pf->dest_pf && pf->dest_pf != prev_pf)
					ereport(ERROR,
							errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
							errmsg("an edge cannot connect more than two vertices even in a cyclic pattern"));
				pf->dest_pf = prev_pf;
			}
			else
			{
				Assert(pf->kind == VERTEX_PATTERN);
				Assert(IS_EDGE_PATTERN(prev_pf->kind));
			}
		}

		prev_pf = pf;
	}

	/*
	 * Collect list of elements for each path factor. Do this after all the
	 * edge links are setup correctly.
	 */
	foreach_ptr(struct path_factor, pf, path_factors)
		path_elem_lists = lappend(path_elem_lists,
								  get_path_elements_for_path_factor(rte->relid, pf));

	pathqueries = generate_queries_for_path_pattern_recurse(rte, pathqueries,
															NIL, path_elem_lists, 0);
	if (!pathqueries)
		pathqueries = list_make1(generate_query_for_empty_path_pattern(rte));

	return pathqueries;
}

/*
 * ============================================================================
 * 【中文注释】generate_queries_for_path_pattern_recurse —— 递归枚举路径组合的核心
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   generate_queries_for_path_pattern() 的递归工作函数。它在"每个路径因子位置可选
 *   元素集合"（path_elem_lists）上做深度优先遍历：从 elempos 位置开始，逐个尝试该
 *   位置上的每个元素追加到当前路径 cur_path 尾部；一旦路径长度达到全部位置数，即
 *   组合出一条完整路径，交给 generate_query_for_graph_path() 生成查询。
 *
 * 参数：
 *   rte            - 表示 GRAPH_TABLE 子句的 RangeTblEntry。
 *   pathqueries    - 已生成的路径查询列表（累计结果，递归中传递并返回）。
 *   cur_path       - 当前正在构建的路径，元素为 struct path_element * 的列表。
 *   path_elem_lists- 外层按路径因子位置排好的"每个位置的可选元素列表"列表。
 *   elempos        - 本次要处理的位置下标（0 起），即正在追加的元素在路径中的序号。
 *
 * 返回值：
 *   List *（元素为 Query）—— 累加了本分支所有完整路径生成查询后的 pathqueries。
 *
 * 设计思想：
 *   1. 典型的回溯（backtracking）结构：lappend 追加当前元素 → 判断是否完整 →
 *      （完整则生成查询 / 不完整则递归到下一个位置）→ list_delete_last 撤销，为
 *      同一位置尝试下一个元素腾出位置。
 *   2. 递归终止条件用"已追加元素数 == 路径因子位置总数"来判断，并 Assert 此时
 *      elempos 必为最后一个位置，与调用约定一致。
 *   3. check_stack_depth() 防止极端复杂的路径模式导致 C 栈溢出；这也是 PG 所有
 *      递归表达式处理函数的共同防御手段。
 *   4. 与 generate_query_for_graph_path() 的分工：本函数只负责"组合枚举"，真正
 *      把一条路径翻译成 SQL 查询、构造 RTE 与连接条件的是后者。
 * ============================================================================
 */
static List *
generate_queries_for_path_pattern_recurse(RangeTblEntry *rte, List *pathqueries, List *cur_path, List *path_elem_lists, int elempos)
{
	List	   *path_elems = list_nth_node(List, path_elem_lists, elempos);

	/* Guard against stack overflow due to complex path patterns. */
	check_stack_depth();

	foreach_ptr(struct path_element, pe, path_elems)
	{
		/* Update current path being built with current element. */
		cur_path = lappend(cur_path, pe);

		/*
		 * If this is the last element in the path, generate query for the
		 * completed path. Else recurse processing the next element.
		 */
		if (list_length(path_elem_lists) == list_length(cur_path))
		{
			Query	   *pathquery = generate_query_for_graph_path(rte, cur_path);

			Assert(elempos == list_length(path_elem_lists) - 1);
			if (pathquery)
				pathqueries = lappend(pathqueries, pathquery);
		}
		else
			pathqueries = generate_queries_for_path_pattern_recurse(rte, pathqueries,
																	cur_path,
																	path_elem_lists,
																	elempos + 1);
		/* Make way for the next element at the same position. */
		cur_path = list_delete_last(cur_path);
	}

	return pathqueries;
}

/*
 * ============================================================================
 * 【中文注释】generate_query_for_graph_path —— 把一条具体路径翻译成一条 SELECT 查询
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把一条由 path_element 列表描述的具体路径（graph_path）构造为一条 SELECT Query：
 *   为路径中的每个元素（顶点/边）创建对应的 RangeTblEntry 放进 FROM，生成边与相邻
 *   顶点之间的等值连接条件、各元素 WHERE 条件以及 GRAPH_TABLE 级 WHERE 条件放进
 *   JOIN 的 quals，最后按 COLUMNS 子句构造目标列表。若路径的边与相邻顶点无法连接，
 *   返回 NULL 表示该路径无效。
 *
 * 参数：
 *   rte        - 表示 GRAPH_TABLE 子句的 RangeTblEntry。
 *   graph_path - struct path_element * 组成的列表，即一条具体路径的元素序列。
 *
 * 返回值：
 *   Query * —— 路径对应的 SELECT 查询；当路径中的某条边找不到能连接两侧顶点的
 *   连接条件时返回 NULL（表示该路径返回不了任何行，交由上层丢弃）。
 *
 * 设计思想：
 *   1. 逐元素构造：对边元素，先通过其 path_factor 找到 src_pf/dest_pf 相邻顶点
 *      因子，再按 create_pe_for_element() 时预建的 src_quals/dest_quals 拼出
 *      "边 = 源顶点 AND 边 = 目的顶点"的连接条件。
 *   2. 对 EDGE_PATTERN_ANY（任意方向）的边，还要尝试交换源/目的两侧：把连接条件
 *      中的 varno 对调（ChangeVarNodes），构造反方向的连接条件，并与正方向条件做
 *      OR，因为无向边两向都可能满足。若正反都不成立，edge_qual 保持 NULL，直接
 *      返回 NULL 放弃这条路径。
 *   3. 每个元素表以 table_open(..., AccessShareLock) + addRangeTableEntryForRelation
 *      挂进 rtable；后续由 AcquireRewriteLocks() 在改写收尾前统一提升锁等级（此处
 *      先持共享锁，避免在解析阶段持高等级锁）。
 *   4. 关键不变量：元素 RTE 在 rtable 中的顺序与路径因子出现顺序一致，即元素
 *      rtindex == path_factor::factorpos + 1，这样创建元素时预建的连接条件里编码的
 *      varno 才能正确对位（有 Assert 守护）。
 *   5. 元素级 WHERE 与 GRAPH_TABLE 级 WHERE 及 COLUMNS 表达式都要经过
 *      replace_property_refs() 把属性引用替换为实际的表列（Var），mappings 分别传
 *      单元素或整条路径的元素列表。
 *   6. 最后用 pull_vars_of_level 收集目标列表与 quals 用到的 Var，把对应列的
 *      SELECT 权限标记（selectedCols）打进 RTEPermissionInfo，实现列级权限检查；
 *      lateral 列在 ColumnRef 转换时已处理，此处忽略。
 * ============================================================================
 */
static Query *
generate_query_for_graph_path(RangeTblEntry *rte, List *graph_path)
{
	Query	   *path_query = makeNode(Query);
	List	   *fromlist = NIL;
	List	   *qual_exprs = NIL;
	List	   *vars;

	path_query->commandType = CMD_SELECT;

	foreach_ptr(struct path_element, pe, graph_path)
	{
		struct path_factor *pf = pe->path_factor;
		RangeTblRef *rtr;
		Relation	rel;
		ParseNamespaceItem *pni;

		Assert(pf->kind == VERTEX_PATTERN || IS_EDGE_PATTERN(pf->kind));

		/* Add conditions representing edge connections. */
		if (IS_EDGE_PATTERN(pf->kind))
		{
			struct path_element *src_pe;
			struct path_element *dest_pe;
			Expr	   *edge_qual = NULL;

			Assert(pf->src_pf && pf->dest_pf);
			src_pe = list_nth(graph_path, pf->src_pf->factorpos);
			dest_pe = list_nth(graph_path, pf->dest_pf->factorpos);

			/* Make sure that the links of adjacent vertices are correct. */
			Assert(pf->src_pf == src_pe->path_factor &&
				   pf->dest_pf == dest_pe->path_factor);

			if (src_pe->elemoid == pe->srcvertexid &&
				dest_pe->elemoid == pe->destvertexid)
				edge_qual = makeBoolExpr(AND_EXPR,
										 list_concat(copyObject(pe->src_quals),
													 copyObject(pe->dest_quals)),
										 -1);

			/*
			 * An edge pattern in any direction matches edges in both
			 * directions, try swapping source and destination. When the
			 * source and destination is the same vertex table, quals
			 * corresponding to either direction may get satisfied. Hence OR
			 * the quals corresponding to both the directions.
			 */
			if (pf->kind == EDGE_PATTERN_ANY &&
				dest_pe->elemoid == pe->srcvertexid &&
				src_pe->elemoid == pe->destvertexid)
			{
				List	   *src_quals = copyObject(pe->dest_quals);
				List	   *dest_quals = copyObject(pe->src_quals);
				Expr	   *rev_edge_qual;

				/* Swap the source and destination varnos in the quals. */
				ChangeVarNodes((Node *) dest_quals, pe->path_factor->src_pf->factorpos + 1,
							   pe->path_factor->dest_pf->factorpos + 1, 0);
				ChangeVarNodes((Node *) src_quals, pe->path_factor->dest_pf->factorpos + 1,
							   pe->path_factor->src_pf->factorpos + 1, 0);

				rev_edge_qual = makeBoolExpr(AND_EXPR, list_concat(src_quals, dest_quals), -1);
				if (edge_qual)
					edge_qual = makeBoolExpr(OR_EXPR, list_make2(edge_qual, rev_edge_qual), -1);
				else
					edge_qual = rev_edge_qual;
			}

			/*
			 * If the given edge element does not connect the adjacent vertex
			 * elements in this path, the path is broken. Abandon this path as
			 * it won't return any rows.
			 */
			if (edge_qual == NULL)
				return NULL;

			qual_exprs = lappend(qual_exprs, edge_qual);
		}
		else
			Assert(!pe->src_quals && !pe->dest_quals);

		/*
		 * Create RangeTblEntry for this element table.
		 *
		 * SQL/PGQ standard (Ref. Section 11.19, Access rule 2 and General
		 * rule 4) does not specify whose access privileges to use when
		 * accessing the element tables: property graph owner's or current
		 * user's. It is safer to use current user's privileges to avoid
		 * unprivileged data access through a property graph. This is inline
		 * with the views being security_invoker by default.
		 */
		rel = table_open(pe->reloid, AccessShareLock);
		pni = addRangeTableEntryForRelation(make_parsestate(NULL), rel, AccessShareLock,
											NULL, true, false);
		table_close(rel, NoLock);
		path_query->rtable = lappend(path_query->rtable, pni->p_rte);
		path_query->rteperminfos = lappend(path_query->rteperminfos, pni->p_perminfo);
		pni->p_rte->perminfoindex = list_length(path_query->rteperminfos);
		rtr = makeNode(RangeTblRef);
		rtr->rtindex = list_length(path_query->rtable);
		fromlist = lappend(fromlist, rtr);

		/*
		 * Make sure that the assumption mentioned in create_pe_for_element()
		 * holds true; that the elements' RangeTblEntrys are added in the
		 * order in which their respective path factors appear in the list of
		 * path factors representing the path pattern.
		 */
		Assert(pf->factorpos + 1 == rtr->rtindex);

		if (pf->whereClause)
		{
			Node	   *tr;

			tr = replace_property_refs(rte->relid, pf->whereClause, list_make1(pe));

			qual_exprs = lappend(qual_exprs, tr);
		}
	}

	if (rte->graph_pattern->whereClause)
	{
		Node	   *path_quals = replace_property_refs(rte->relid,
													   (Node *) rte->graph_pattern->whereClause,
													   graph_path);

		qual_exprs = lappend(qual_exprs, path_quals);
	}

	path_query->jointree = makeFromExpr(fromlist,
										qual_exprs ? (Node *) makeBoolExpr(AND_EXPR, qual_exprs, -1) : NULL);

	/* Construct query targetlist from COLUMNS specification of GRAPH_TABLE. */
	path_query->targetList = castNode(List,
									  replace_property_refs(rte->relid,
															(Node *) rte->graph_table_columns,
															graph_path));

	/*
	 * Mark the columns being accessed in the path query as requiring SELECT
	 * privilege. Any lateral columns should have been handled when the
	 * corresponding ColumnRefs were transformed. Ignore those here.
	 */
	vars = pull_vars_of_level((Node *) list_make2(qual_exprs, path_query->targetList), 0);
	foreach_node(Var, var, vars)
	{
		RTEPermissionInfo *perminfo = getRTEPermissionInfo(path_query->rteperminfos,
														   rt_fetch(var->varno, path_query->rtable));

		/* Must offset the attnum to fit in a bitmapset */
		perminfo->selectedCols = bms_add_member(perminfo->selectedCols,
												var->varattno - FirstLowInvalidHeapAttributeNumber);
	}

	return path_query;
}

/*
 * ============================================================================
 * 【中文注释】generate_query_for_empty_path_pattern —— 构造不返回任何行的哑查询
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   当路径模式在给定属性图上匹配不到任何路径时，构造一条恒假的 SELECT 查询：FROM
 *   为空、WHERE 为常量 false，但目标列表仍投影出与 GRAPH_TABLE 的 COLUMNS 子句
 *   相同的列（全部为 NULL 常量）。这样外层 UNION 的目标列表结构保持一致，后续
 *   阶段无需区分"空模式"这种特殊情况。
 *
 * 参数：
 *   rte - 表示 GRAPH_TABLE 子句的 RangeTblEntry，其 graph_table_columns 给出列定义。
 *
 * 返回值：
 *   Query * —— 恒空 SELECT 查询。
 *
 * 设计思想：
 *   1. makeBoolConst(false, false) 作为 jointree 的 quals，让执行器恒不产生任何行，
 *      实现"无匹配"的语义。
 *   2. 目标列表复用 rte->graph_table_columns 的每个 TargetEntry，仅把其 expr 替换为
 *      同类型、同 typmod、同 collation 的 NULL 常量（makeNullConst）。这一步很关键：
 *      UNION 各分支的目标列表必须列数、类型一致，否则后续构造 UNION 时无法对齐。
 *   3. rtable/rteperminfos 保持为空，jointree 无 FROM 项；因为没有真实的表访问，
 *      也就不需要产生任何 RangeTblEntry。
 * ============================================================================
 */
static Query *
generate_query_for_empty_path_pattern(RangeTblEntry *rte)
{
	Query	   *query = makeNode(Query);

	query->commandType = CMD_SELECT;
	query->rtable = NIL;
	query->rteperminfos = NIL;
	query->jointree = makeFromExpr(NIL, (Node *) makeBoolConst(false, false));

	/*
	 * Even though no rows are returned, the result still projects the same
	 * columns as projected by GRAPH_TABLE clause. Do this by constructing a
	 * target list full of NULL values.
	 */
	foreach_node(TargetEntry, te, rte->graph_table_columns)
	{
		Node	   *nte = (Node *) te->expr;

		te->expr = (Expr *) makeNullConst(exprType(nte), exprTypmod(nte), exprCollation(nte));
		query->targetList = lappend(query->targetList, te);
	}

	return query;
}

/*
 * ============================================================================
 * 【中文注释】generate_union_from_pathqueries —— 把多条路径查询合并成一条 UNION 查询
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   接收 generate_queries_for_path_pattern() 产出的路径查询列表，把多条查询用
 *   UNION ALL 合并为一条顶层 SELECT：先调用 generate_setop_from_pathqueries() 构造
 *   递归的 SetOperationStmt，再把它封装进一个带外层目标列表的 Query。若列表只有
 *   一条查询，则直接返回该查询本身，省去多余的 UNION 包装。
 *
 * 参数：
 *   pathqueries - List **。指向路径查询列表的指针；函数会**销毁**该列表（递归构造
 *                 SetOperationStmt 时逐条消费），返回时恒置为 NIL。
 *
 * 返回值：
 *   Query * —— 合并后的 UNION 查询；单条输入时直接返回那条查询。
 *
 * 设计思想：
 *   1. 只有一条路径查询时是常见且最有利的路径：避免无谓的 SetOperationStmt 与
 *      外层查询包装，让优化器直接看到平坦的查询树。
 *   2. 多条时，把每条路径查询经 addRangeTableEntryForSubquery 变成 UNION 的 RTE
 *      分支；各分支的目标列表可能类型/排序规则不同，UNION 的结果列类型取合并后的
 *      公共类型（colTypes/colTypmods/colCollations），外层目标列表据此生成 Var，
 *      列名取自样例查询 sampleQuery 的非 junk 列名。
 *   3. 由于路径查询的目标列表已完成 collation 赋值，UNION 结果列的 collation 直接
 *      继承而来，本函数不再需要额外的 collation 处理。
 *   4. 外层目标列表的 varno 固定用 1：rtable 中恒有真实 RTE，避免规则重写
 *      （rule rewriting）时 varno 指向不存在的项。
 * ============================================================================
 */
static Query *
generate_union_from_pathqueries(List **pathqueries)
{
	List	   *rtable = NIL;
	Query	   *sampleQuery = linitial_node(Query, *pathqueries);
	SetOperationStmt *sostmt;
	Query	   *union_query;
	int			resno;
	ListCell   *lctl,
			   *lct,
			   *lcm,
			   *lcc;

	Assert(list_length(*pathqueries) > 0);

	/* If there's only one pathquery, no need to construct a UNION query. */
	if (list_length(*pathqueries) == 1)
	{
		*pathqueries = NIL;
		return sampleQuery;
	}

	sostmt = castNode(SetOperationStmt,
					  generate_setop_from_pathqueries(*pathqueries, &rtable, NULL));

	/* Encapsulate the set operation statement into a Query. */
	union_query = makeNode(Query);
	union_query->commandType = CMD_SELECT;
	union_query->rtable = rtable;
	union_query->setOperations = (Node *) sostmt;
	union_query->rteperminfos = NIL;
	union_query->jointree = makeFromExpr(NIL, NULL);

	/*
	 * Generate dummy targetlist for outer query using column names from one
	 * of the queries and common datatypes/collations of topmost set
	 * operation.  It shouldn't matter which query. Also it shouldn't matter
	 * which RT index is used as varno in the target list entries, as long as
	 * it corresponds to a real RT entry; else funny things may happen when
	 * the tree is mashed by rule rewriting. So we use 1 since there's always
	 * one RT entry at least.
	 */
	Assert(rt_fetch(1, rtable));
	union_query->targetList = NULL;
	resno = 1;
	forfour(lct, sostmt->colTypes,
			lcm, sostmt->colTypmods,
			lcc, sostmt->colCollations,
			lctl, sampleQuery->targetList)
	{
		Oid			colType = lfirst_oid(lct);
		int32		colTypmod = lfirst_int(lcm);
		Oid			colCollation = lfirst_oid(lcc);
		TargetEntry *sample_tle = (TargetEntry *) lfirst(lctl);
		char	   *colName;
		TargetEntry *tle;
		Var		   *var;

		Assert(!sample_tle->resjunk);
		colName = pstrdup(sample_tle->resname);
		var = makeVar(1, sample_tle->resno, colType, colTypmod, colCollation, 0);
		var->location = exprLocation((Node *) sample_tle->expr);
		tle = makeTargetEntry((Expr *) var, (AttrNumber) resno++, colName, false);
		union_query->targetList = lappend(union_query->targetList, tle);
	}

	*pathqueries = NIL;
	return union_query;
}

/*
 * ============================================================================
 * 【中文注释】generate_setop_from_pathqueries —— 递归构建 UNION 的 SetOperationStmt
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把给定的路径查询列表递归地构造成一棵 SetOperationStmt（UNION ALL）树，并同时
 *   把所有子查询登记进 *rtable。每次取出列表头一条查询作为左分支，右分支对剩余列表
 *   递归调用；递归到空列表时，最后一条查询被转成 RangeTblRef 作为最右叶子，并提取
 *   其非 junk 目标列表供上层合并类型。返回 SetOperationStmt 节点；列表为空时返回
 *   NULL。
 *
 * 参数：
 *   pathqueries - 路径查询列表（元素为 Query），本函数递归中逐条消费（list_delete_first）。
 *   rtable      - List **，累加所有作为 UNION 分支子查询的 RangeTblEntry。
 *   targetlist  - List **，用于向上传递"当前 UNION 树的公共目标列表"；外层传 NULL
 *                 表示不需要（见 generate_union_from_pathqueries）。
 *
 * 返回值：
 *   Node * —— SetOperationStmt（或最右叶子的 RangeTblRef）；空列表返回 NULL。
 *
 * 设计思想：
 *   1. 把 UNION ALL 构造成左深树：左分支是当前列表头查询，右分支递归。这种结构与
 *      PG 标准 set operation 树的形态一致，方便后续 planner 处理。
 *   2. 每个子查询要经 IncrementVarSublevelsUp((Node *) lquery, 1, 1) 把其内部引用
 *      外层（如 lateral 横向引用）的 Var 层数加一，因为子查询在 UNION 中下沉了一层。
 *   3. 目标列表合并由 constructSetOpTargetlist() 完成：比较左右两边列的公共类型、
 *      生成该 UNION 层的结果列定义；逐层向上，最终得到整棵树的列定义。
 *   4. check_stack_depth() 防御路径查询数量过大导致的递归栈溢出。
 *   5. 每个子查询通过 addRangeTableEntryForSubquery 创建 RTE（无名称、非 lateral），
 *      其 rtindex 依次递增；最右叶子（最后的 RangeTblRef）不再成为 RTE，直接以引用
 *      形式挂在 SetOperationStmt 上。
 * ============================================================================
 */
static Node *
generate_setop_from_pathqueries(List *pathqueries, List **rtable, List **targetlist)
{
	SetOperationStmt *sostmt;
	Query	   *lquery;
	Node	   *rarg;
	RangeTblRef *lrtr = makeNode(RangeTblRef);
	List	   *rtargetlist;
	ParseNamespaceItem *pni;

	/* Guard against stack overflow due to many path queries. */
	check_stack_depth();

	/* Recursion termination condition. */
	if (list_length(pathqueries) == 0)
	{
		*targetlist = NIL;
		return NULL;
	}

	lquery = linitial_node(Query, pathqueries);

	/*
	 * Each path query will become a subquery of the UNION statement. So any
	 * Vars that already refer outside the path query must be adjusted for
	 * additional query level.
	 */
	IncrementVarSublevelsUp((Node *) lquery, 1, 1);

	pni = addRangeTableEntryForSubquery(make_parsestate(NULL), lquery, NULL,
										false, false);
	*rtable = lappend(*rtable, pni->p_rte);
	lrtr->rtindex = list_length(*rtable);
	rarg = generate_setop_from_pathqueries(list_delete_first(pathqueries), rtable, &rtargetlist);
	if (rarg == NULL)
	{
		/*
		 * No further path queries in the list. Convert the last query into a
		 * RangeTblRef as expected by SetOperationStmt. Extract a list of the
		 * non-junk TLEs for upper-level processing.
		 */
		if (targetlist)
		{
			*targetlist = NIL;
			foreach_node(TargetEntry, tle, lquery->targetList)
			{
				if (!tle->resjunk)
					*targetlist = lappend(*targetlist, tle);
			}
		}
		return (Node *) lrtr;
	}

	sostmt = makeNode(SetOperationStmt);
	sostmt->op = SETOP_UNION;
	sostmt->all = true;
	sostmt->larg = (Node *) lrtr;
	sostmt->rarg = rarg;
	constructSetOpTargetlist(NULL, sostmt, lquery->targetList, rtargetlist, targetlist, "UNION", false);

	return (Node *) sostmt;
}

/*
 * ============================================================================
 * 【中文注释】create_pe_for_element —— 为满足路径因子的某个图元素构造 path_element 对象
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   给定一个路径因子 pf 和一个图元素 OID（elemoid），查系统目录 pg_propgraph_element
 *   获取该元素的信息，构造对应的 struct path_element 对象。若元素的种类（顶点/边）与
 *   路径因子要求的模式类型不符，返回 NULL。对于边元素，还会预先构建其与源/目的顶点
 *   之间的连接条件（src_quals/dest_quals）并记录两端顶点 id。
 *
 * 参数：
 *   pf      - 路径因子，指明期望的元素模式种类（VERTEX_PATTERN / 边模式）。
 *   elemoid - 图元素 OID（pg_propgraph_element 主键）。
 *
 * 返回值：
 *   struct path_element * —— 新构造的元素对象；元素种类不匹配时返回 NULL。
 *
 * 设计思想：
 *   1. 通过 syscache PROPGRAPHELOID 一次性读取元素元组，校验种类后复制所需字段；
 *      查找失败直接 elog(ERROR)，因为调用方传入的 elemoid 必然来自合法的目录扫描。
 *   2. 对边元素预先计算与相邻顶点的连接条件：build_edge_vertex_link_quals() 根据
 *      目录里源/目的 key、ref、eqop 三个数组列构造若干等值 OpExpr。这些 quals 里的
 *      varno 直接编码为 pf->factorpos + 1 与相邻顶点因子的 factorpos + 1。
 *   3. "预构建"是刻意的设计：同一元素可能出现在多条候选路径中（被复用），若推迟到
 *      构造查询时再建 quals，就得反复查目录；而预建时元素 RTE 的 rtindex 与
 *      factorpos + 1 的对应关系由 generate_query_for_graph_path() 保证（有 Assert），
 *      因此 quals 可以在不同路径间安全复用。
 *   4. 访问目录元组后及时 ReleaseSysCache；pe 对象本身由 palloc0 分配，生命周期
 *      覆盖整个改写阶段。
 * ============================================================================
 */
static struct path_element *
create_pe_for_element(struct path_factor *pf, Oid elemoid)
{
	HeapTuple	eletup = SearchSysCache1(PROPGRAPHELOID, ObjectIdGetDatum(elemoid));
	Form_pg_propgraph_element pgeform;
	struct path_element *pe;

	if (!eletup)
		elog(ERROR, "cache lookup failed for property graph element %u", elemoid);
	pgeform = ((Form_pg_propgraph_element) GETSTRUCT(eletup));

	if ((pgeform->pgekind == PGEKIND_VERTEX && pf->kind != VERTEX_PATTERN) ||
		(pgeform->pgekind == PGEKIND_EDGE && !IS_EDGE_PATTERN(pf->kind)))
	{
		ReleaseSysCache(eletup);
		return NULL;
	}

	pe = palloc0_object(struct path_element);
	pe->path_factor = pf;
	pe->elemoid = elemoid;
	pe->reloid = pgeform->pgerelid;

	/*
	 * When a path is converted into a query
	 * (generate_query_for_graph_path()), a RangeTblEntry will be created for
	 * every element in the path.  Fixing rtindexes of RangeTblEntrys here
	 * makes it possible to craft elements' qual expressions only once while
	 * we have access to the catalog entry. Otherwise they need to be crafted
	 * as many times as the number of paths a given element appears in,
	 * fetching catalog entry again each time.  Hence we simply assume
	 * RangeTblEntrys will be created in the same order in which the
	 * corresponding path factors appear in the list of path factors
	 * representing a path pattern. That way their rtindexes will be same as
	 * path_factor::factorpos + 1.
	 */
	if (IS_EDGE_PATTERN(pf->kind))
	{
		pe->srcvertexid = pgeform->pgesrcvertexid;
		pe->destvertexid = pgeform->pgedestvertexid;
		Assert(pf->src_pf && pf->dest_pf);

		pe->src_quals = build_edge_vertex_link_quals(eletup, pf->factorpos + 1, pf->src_pf->factorpos + 1,
													 pe->srcvertexid,
													 Anum_pg_propgraph_element_pgesrckey,
													 Anum_pg_propgraph_element_pgesrcref,
													 Anum_pg_propgraph_element_pgesrceqop);
		pe->dest_quals = build_edge_vertex_link_quals(eletup, pf->factorpos + 1, pf->dest_pf->factorpos + 1,
													  pe->destvertexid,
													  Anum_pg_propgraph_element_pgedestkey,
													  Anum_pg_propgraph_element_pgedestref,
													  Anum_pg_propgraph_element_pgedesteqop);
	}

	ReleaseSysCache(eletup);

	return pe;
}

/*
 * ============================================================================
 * 【中文注释】get_labels_for_expr —— 把标签表达式解析为一组标签 OID
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把元素模式里的标签表达式（labelexpr）解析为它命中的所有图标签 OID 列表。未写
 *   标签表达式等价于"全部标签"；单个 GraphLabelRef 返回单元素列表；BoolExpr 形式
 *   （语法层面产生的标签并列/合取）则展开为其包含的所有 GraphLabelRef 的标签 OID。
 *
 * 参数：
 *   propgraphid - 属性图 OID，用于"全部标签"情形下限定目录扫描范围。
 *   labelexpr   - 标签表达式节点，取值为 NULL、GraphLabelRef 或 BoolExpr。
 *
 * 返回值：
 *   List *（元素为 Oid）—— 标签 OID 列表。
 *
 * 设计思想：
 *   1. NULL（无标签表达式）按 SQL/PGQ 标准第 9.2 节"标签集合的上下文推断"子条款
 *      2.a.ii 处理：等价于 '%|!%'，即属性图中的全部标签。因此需要扫描
 *      pg_propgraph_label 按属性图过滤，把所有标签 OID 收集起来。
 *   2. GraphLabelRef 是语法上直接引用的单个标签；BoolExpr 分支说明 gram.y 允许生成
 *      的标签表达式形态有限（并列/合取），其它节点类型直接 elog(ERROR)，把解析器
 *      保证的"文法约束"显式落在代码上。
 *   3. 返回值被 get_path_elements_for_path_factor() 用于枚举与各标签关联的图元素，
 *      以及后续 replace_property_refs_mutator() 中做"属性是否属于标签"的判断。
 * ============================================================================
 */
static List *
get_labels_for_expr(Oid propgraphid, Node *labelexpr)
{
	List	   *label_oids;

	if (!labelexpr)
	{
		Relation	rel;
		SysScanDesc scan;
		ScanKeyData key[1];
		HeapTuple	tup;

		/*
		 * According to section 9.2 "Contextual inference of a set of labels"
		 * subclause 2.a.ii of SQL/PGQ standard, element pattern which does
		 * not have a label expression is considered to have label expression
		 * equivalent to '%|!%' which is set of all labels.
		 */
		label_oids = NIL;
		rel = table_open(PropgraphLabelRelationId, AccessShareLock);
		ScanKeyInit(&key[0],
					Anum_pg_propgraph_label_pglpgid,
					BTEqualStrategyNumber,
					F_OIDEQ, ObjectIdGetDatum(propgraphid));
		scan = systable_beginscan(rel, PropgraphLabelGraphNameIndexId,
								  true, NULL, 1, key);
		while (HeapTupleIsValid(tup = systable_getnext(scan)))
		{
			Form_pg_propgraph_label label = (Form_pg_propgraph_label) GETSTRUCT(tup);

			label_oids = lappend_oid(label_oids, label->oid);
		}
		systable_endscan(scan);
		table_close(rel, AccessShareLock);
	}
	else if (IsA(labelexpr, GraphLabelRef))
	{
		GraphLabelRef *glr = castNode(GraphLabelRef, labelexpr);

		label_oids = list_make1_oid(glr->labelid);
	}
	else if (IsA(labelexpr, BoolExpr))
	{
		BoolExpr   *be = castNode(BoolExpr, labelexpr);
		List	   *label_exprs = be->args;

		label_oids = NIL;
		foreach_node(GraphLabelRef, glr, label_exprs)
			label_oids = lappend_oid(label_oids, glr->labelid);
	}
	else
	{
		/*
		 * should not reach here since gram.y will not generate a label
		 * expression with other node types.
		 */
		elog(ERROR, "unsupported label expression node: %d", (int) nodeTag(labelexpr));
	}

	return label_oids;
}

/*
 * ============================================================================
 * 【中文注释】get_path_elements_for_path_factor —— 枚举满足某路径因子的全部图元素
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   给定路径因子 pf，找出属性图中所有满足其元素模式的图元素，为每个合格元素构造
 *   struct path_element 并返回列表。逻辑为：先解析标签表达式得到标签集合，再通过
 *   目录 pg_propgraph_element_label 找出与每个标签关联的元素，去重后按元素种类过滤，
 *   最终把合格元素的标签写入 pf->labeloids（用于后续属性引用解析）。
 *
 * 参数：
 *   propgraphid - 属性图 OID。
 *   pf          - 路径因子；函数会回填其 labeloids 字段（与该因子关联的标签 OID）。
 *
 * 返回值：
 *   List *（元素为 struct path_element *）—— 满足该元素模式的图元素对象列表。
 *
 * 设计思想：
 *   1. 三步走：get_labels_for_expr() 得到标签集合 → 逐个标签扫描
 *      pg_propgraph_element_label 得到关联元素 → create_pe_for_element() 按元素种类
 *      过滤。路径因子目前只支持顶点/边两种；嵌套路径模式等其它种类留待未来支持
 *      （Assert 拦下）。
 *   2. 用 elem_oids_seen / pf_elem_oids 两个集合做去重与加速：同一元素被多个标签
 *      共享（标签与元素是多对多），已被处理过的元素不再重复创建 path_element；已
 *      确认合格的元素再次出现时直接标记 found。
 *   3. 错误语义：若显式指定的标签找不到任何合格元素，说明该标签与所需种类的元素
 *      无关，按标准报 UNDEFINED_OBJECT 错误；若是"全部标签"展开来的标签，则不能
 *      报错，只能默默放弃该标签并记入 unresolved_labels。
 *   4. pf->labeloids = 标签全集 − 无合格元素的标签。这保证后续属性引用只会在真实
 *      关联到元素的标签里查找，避免把"标签有属性但无该种类元素"误判为可解析。
 * ============================================================================
 */
static List *
get_path_elements_for_path_factor(Oid propgraphid, struct path_factor *pf)
{
	List	   *label_oids = get_labels_for_expr(propgraphid, pf->labelexpr);
	List	   *elem_oids_seen = NIL;
	List	   *pf_elem_oids = NIL;
	List	   *path_elements = NIL;
	List	   *unresolved_labels = NIL;
	Relation	rel;
	SysScanDesc scan;
	ScanKeyData key[1];
	HeapTuple	tup;

	/*
	 * A property graph element can be either a vertex or an edge. Other types
	 * of path factors like nested path pattern need to be handled separately
	 * when supported.
	 */
	Assert(pf->kind == VERTEX_PATTERN || IS_EDGE_PATTERN(pf->kind));

	rel = table_open(PropgraphElementLabelRelationId, AccessShareLock);
	foreach_oid(labeloid, label_oids)
	{
		bool		found = false;

		ScanKeyInit(&key[0],
					Anum_pg_propgraph_element_label_pgellabelid,
					BTEqualStrategyNumber,
					F_OIDEQ, ObjectIdGetDatum(labeloid));
		scan = systable_beginscan(rel, PropgraphElementLabelLabelIndexId, true,
								  NULL, 1, key);
		while (HeapTupleIsValid(tup = systable_getnext(scan)))
		{
			Form_pg_propgraph_element_label label_elem = (Form_pg_propgraph_element_label) GETSTRUCT(tup);
			Oid			elem_oid = label_elem->pgelelid;

			if (!list_member_oid(elem_oids_seen, elem_oid))
			{
				/*
				 * Create path_element object if the new element qualifies the
				 * element pattern kind.
				 */
				struct path_element *pe = create_pe_for_element(pf, elem_oid);

				if (pe)
				{
					path_elements = lappend(path_elements, pe);

					/* Remember qualified elements. */
					pf_elem_oids = lappend_oid(pf_elem_oids, elem_oid);
					found = true;
				}

				/*
				 * Remember qualified and unqualified elements processed so
				 * far to avoid processing already processed elements again.
				 */
				elem_oids_seen = lappend_oid(elem_oids_seen, label_elem->pgelelid);
			}
			else if (list_member_oid(pf_elem_oids, elem_oid))
			{
				/*
				 * The graph element is known to qualify the given element
				 * pattern. Flag that the current label has at least one
				 * qualified element associated with it.
				 */
				found = true;
			}
		}

		if (!found)
		{
			/*
			 * We did not find any qualified element associated with this
			 * label. The label or its properties can not be associated with
			 * the given element pattern. Throw an error if the label was
			 * explicitly specified in the element pattern. Otherwise remember
			 * it for later use.
			 */
			if (!pf->labelexpr)
				unresolved_labels = lappend_oid(unresolved_labels, labeloid);
			else
				ereport(ERROR,
						(errcode(ERRCODE_UNDEFINED_OBJECT),
						 errmsg("no property graph element of type \"%s\" has label \"%s\" associated with it in property graph \"%s\"",
								pf->kind == VERTEX_PATTERN ? "vertex" : "edge",
								get_propgraph_label_name(labeloid),
								get_rel_name(propgraphid))));
		}

		systable_endscan(scan);
	}
	table_close(rel, AccessShareLock);

	/*
	 * Remove the labels which were not explicitly mentioned in the label
	 * expression but do not have any qualified elements associated with them.
	 * Properties associated with such labels may not be referenced. See
	 * replace_property_refs_mutator() for more details.
	 */
	pf->labeloids = list_difference_oid(label_oids, unresolved_labels);

	return path_elements;
}

/*
 * Mutating property references into table variables
 */

struct replace_property_refs_context
{
	Oid			propgraphid;
	const List *mappings;
};

/*
 * ============================================================================
 * 【中文注释】replace_property_refs_mutator —— 把属性引用替换为实际表列的表达式遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   表达式树遍历器（mutator），把树中的 GraphPropertyRef 节点替换为真正的列访问
 *   表达式（Var 或 NULL 常量），并把 lateral 引用产生的 Var 层数提升一级。这是
 *   replace_property_refs() 的递归实现，供 COLUMNS 与 WHERE 中的属性引用改写使用。
 *
 * 参数：
 *   node    - 待改写的表达式节点；NULL 直接返回 NULL。
 *   context - struct replace_property_refs_context，携带属性图 OID 与"路径元素 → 路径
 *              因子"的映射列表 mappings（用于把属性引用里的元素变量名对位到具体元素）。
 *
 * 返回值：
 *   Node * —— 改写后的表达式；对 GraphPropertyRef 返回解析出的列表达式，
 *   对其它节点递归返回新树。
 *
 * 设计思想：
 *   1. 对 Var 节点：它必是 lateral（横向）引用（语法阶段横向引用在进入本子查询前就
 *      被转成了 Var），由于改写后引用方处于更外层，需要 varlevelsup + 1 指向正确的
 *      查询层。
 *   2. 对 GraphPropertyRef：先在 mappings 里按 elvarname（元素变量名）找到对应
 *      path_element，得到其所属 path_factor；然后遍历该因子的 labeloids，尝试经由
 *      (元素, 标签) → 标签属性 两级 syscache 找到属性定义，命中则把目录里存的
 *      plpexpr 表达式序列化文本 stringToNode 还原，再用 ChangeVarNodes 把其中的
 *      varno = 1 改成该元素的 rtindex（factorpos + 1）。
 *   3. 与元素关联但没挂该属性的标签记录为 unrelated_labels；若全部标签都不挂该属性，
 *      再看属性是否关联到其中任一标签（is_property_associated_with_label）：关联则取
 *      该属性对当前元素的表达式，取不到则按 SQL/PGQ 6.5 节"属性引用"General Rule
 *      2.b 生成 NULL 常量；完全不关联则报"属性不存在"错误。
 *   4. 属性表达式里的 varno 统一约定为 1（目录存的就是"引用自身"的形式），故用
 *      ChangeVarNodes(n, 1, factorpos + 1, 0) 一次性对位。
 *   5. 非特殊节点交给 expression_tree_mutator 递归处理，保持对整棵树结构的忠实复制。
 * ============================================================================
 */
static Node *
replace_property_refs_mutator(Node *node, struct replace_property_refs_context *context)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;
		Var		   *newvar = copyObject(var);

		/*
		 * If it's already a Var, then it was a lateral reference.  Since we
		 * are in a subquery after the rewrite, we have to increase the level
		 * by one.
		 */
		newvar->varlevelsup++;

		return (Node *) newvar;
	}
	else if (IsA(node, GraphPropertyRef))
	{
		GraphPropertyRef *gpr = (GraphPropertyRef *) node;
		Node	   *n = NULL;
		struct path_element *found_mapping = NULL;
		struct path_factor *mapping_factor = NULL;
		List	   *unrelated_labels = NIL;

		foreach_ptr(struct path_element, m, context->mappings)
		{
			if (m->path_factor->variable && strcmp(gpr->elvarname, m->path_factor->variable) == 0)
			{
				found_mapping = m;
				break;
			}
		}

		/*
		 * transformGraphTablePropertyRef() would not create a
		 * GraphPropertyRef for a variable which is not present in the graph
		 * path pattern.
		 */
		Assert(found_mapping);

		mapping_factor = found_mapping->path_factor;

		/*
		 * Find property definition for given element through any of the
		 * associated labels qualifying the given element pattern.
		 */
		foreach_oid(labeloid, mapping_factor->labeloids)
		{
			Oid			elem_labelid = GetSysCacheOid2(PROPGRAPHELEMENTLABELELEMENTLABEL,
													   Anum_pg_propgraph_element_label_oid,
													   ObjectIdGetDatum(found_mapping->elemoid),
													   ObjectIdGetDatum(labeloid));

			if (OidIsValid(elem_labelid))
			{
				HeapTuple	tup = SearchSysCache2(PROPGRAPHLABELPROP, ObjectIdGetDatum(elem_labelid),
												  ObjectIdGetDatum(gpr->propid));

				if (!tup)
				{
					/*
					 * The label is associated with the given element but it
					 * is not associated with the required property. Check
					 * next label.
					 */
					continue;
				}

				n = stringToNode(TextDatumGetCString(SysCacheGetAttrNotNull(PROPGRAPHLABELPROP,
																			tup, Anum_pg_propgraph_label_property_plpexpr)));
				ChangeVarNodes(n, 1, mapping_factor->factorpos + 1, 0);

				ReleaseSysCache(tup);
			}
			else
			{
				/*
				 * Label is not associated with the element but it may be
				 * associated with the property through some other element.
				 * Save it for later use.
				 */
				unrelated_labels = lappend_oid(unrelated_labels, labeloid);
			}
		}

		/* See if we can resolve the property in some other way. */
		if (!n)
		{
			bool		prop_associated = false;

			foreach_oid(loid, unrelated_labels)
			{
				if (is_property_associated_with_label(loid, gpr->propid))
				{
					prop_associated = true;
					break;
				}
			}

			if (prop_associated)
			{
				/*
				 * The property is associated with at least one of the labels
				 * that satisfy given element pattern. If it's associated with
				 * the given element (through some other label), use
				 * corresponding value expression. Otherwise NULL. Ref.
				 * SQL/PGQ standard section 6.5 Property Reference, General
				 * Rule 2.b.
				 */
				n = get_element_property_expr(found_mapping->elemoid, gpr->propid,
											  mapping_factor->factorpos + 1);

				if (!n)
					n = (Node *) makeNullConst(gpr->typeId, gpr->typmod, gpr->collation);
			}

		}

		if (!n)
			ereport(ERROR,
					errcode(ERRCODE_UNDEFINED_OBJECT),
					errmsg("property \"%s\" for element variable \"%s\" not found",
						   get_propgraph_property_name(gpr->propid), mapping_factor->variable));

		return n;
	}

	return expression_tree_mutator(node, replace_property_refs_mutator, context);
}

/*
 * ============================================================================
 * 【中文注释】replace_property_refs —— 属性引用替换的对外封装（入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把给定表达式树中所有 GraphPropertyRef（属性引用）替换为对路径元素表的真实列
 *   访问表达式，供生成路径查询时处理 COLUMNS 目标列表与 WHERE 条件。它只是装配
 *   replace_property_refs_context 上下文并转调 replace_property_refs_mutator() 的
 *   薄封装。
 *
 * 参数：
 *   propgraphid - 属性图 OID，透传给 mutator 供属性/标签解析使用。
 *   node        - 待改写的表达式树（可为 NULL，直接返回 NULL）。
 *   mappings    - struct path_element * 列表；属性引用按元素变量名在其中查找对应
 *                 元素，从而把变量名解析为具体路径元素及其 rtindex。
 *
 * 返回值：
 *   Node * —— 改写后的表达式树。
 *
 * 设计思想：
 *   1. mappings 传入的语义分两种：处理单个元素的 WHERE 时传单元素列表；处理
 *      GRAPH_TABLE 级 WHERE 或 COLUMNS 时传整条路径的元素列表。元素变量名正是通过
 *      path_element->path_factor->variable 与 GraphPropertyRef->elvarname 比对来匹配的。
 *   2. 之所以让调用方传入 mappings 而非内部维护，是因为"某变量对应哪个具体元素"
 *      取决于当前正在构造的这条路径（同一变量在一条路径中唯一），调用方天然拥有
 *      该上下文。
 * ============================================================================
 */
static Node *
replace_property_refs(Oid propgraphid, Node *node, const List *mappings)
{
	struct replace_property_refs_context context;

	context.mappings = mappings;
	context.propgraphid = propgraphid;

	return replace_property_refs_mutator(node, &context);
}

/*
 * ============================================================================
 * 【中文注释】build_edge_vertex_link_quals —— 构造边表与顶点表的连接条件
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   根据目录中存储的"边键列、引用顶点键列、等值操作符"三组并行数组，为一条边与其
 *   一侧的顶点构造一组等值连接条件（OpExpr）。每一组 (key, ref, eqop) 对应一条
 *   "顶点.ref 列 = 边.key 列"的条件。返回该组条件列表，并完成 collation 赋值。
 *
 * 参数：
 *   edgetup            - 边元素的目录元组（pg_propgraph_element）。
 *   edgerti            - 边元素表在查询中的 rtindex（条件右操作数 varno）。
 *   refrti             - 被引用顶点表（src 或 dest）在查询中的 rtindex。
 *   refid              - 被引用顶点元素 OID，用于解析其表 OID。
 *   catalog_key_attnum - 边键列数组（如 pgesrckey/pgedestkey）的 attnum。
 *   catalog_ref_attnum - 顶点键引用数组（pgesrcref/pgedestref）的 attnum。
 *   catalog_eqop_attnum- 等值操作符数组（pgesrceqop/pgedesteqop）的 attnum。
 *
 * 返回值：
 *   List *（元素为 OpExpr）—— 该边与一侧顶点的连接条件；边键/顶点键为空时为空列表。
 *
 * 设计思想：
 *   1. 边可能通过多个键列引用顶点（复合键），目录用三个等长的 int2[]/oid[] 数组
 *      存储；先把三个 Datum 数组解构（deconstruct_array_builtin），并校验三者长度
 *      一致（不一致说明目录损坏，elog(ERROR)）。
 *   2. 对每一组：get_atttypetypmodcoll 取得两端列的类型/排序规则，用 makeVar 构造
 *      keyvar 与 refvar，再从 OPEROID syscache 取等值操作符，校验其为返回 boolean
 *      的二元操作符；参照 PK/FK 连接的惯例，被引用的顶点键作左操作数、边键作右
 *      操作数，make_fn_arguments 处理隐式类型转换。
 *   3. 生成的 OpExpr 不设 collation 相关字段，最后统一用 assign_expr_collations()
 *      一次性赋值——这也是 generate_query_for_graph_path() 说"无需再单独处理
 *      collation"的原因。
 *   4. 本函数不持有任何锁：目录元组的锁与读取由调用方（create_pe_for_element）
 *      负责，这里只做纯计算。
 * ============================================================================
 */
static List *
build_edge_vertex_link_quals(HeapTuple edgetup, int edgerti, int refrti, Oid refid, AttrNumber catalog_key_attnum, AttrNumber catalog_ref_attnum, AttrNumber catalog_eqop_attnum)
{
	List	   *quals = NIL;
	Form_pg_propgraph_element pgeform;
	Datum		datum;
	Datum	   *d1,
			   *d2,
			   *d3;
	int			n1,
				n2,
				n3;
	ParseState *pstate = make_parsestate(NULL);
	Oid			refrelid = GetSysCacheOid1(PROPGRAPHELOID, Anum_pg_propgraph_element_pgerelid, ObjectIdGetDatum(refid));

	pgeform = (Form_pg_propgraph_element) GETSTRUCT(edgetup);

	datum = SysCacheGetAttrNotNull(PROPGRAPHELOID, edgetup, catalog_key_attnum);
	deconstruct_array_builtin(DatumGetArrayTypeP(datum), INT2OID, &d1, NULL, &n1);

	datum = SysCacheGetAttrNotNull(PROPGRAPHELOID, edgetup, catalog_ref_attnum);
	deconstruct_array_builtin(DatumGetArrayTypeP(datum), INT2OID, &d2, NULL, &n2);

	datum = SysCacheGetAttrNotNull(PROPGRAPHELOID, edgetup, catalog_eqop_attnum);
	deconstruct_array_builtin(DatumGetArrayTypeP(datum), OIDOID, &d3, NULL, &n3);

	if (n1 != n2)
		elog(ERROR, "array size key (%d) vs ref (%d) mismatch for element ID %u", catalog_key_attnum, catalog_ref_attnum, pgeform->oid);
	if (n1 != n3)
		elog(ERROR, "array size key (%d) vs operator (%d) mismatch for element ID %u", catalog_key_attnum, catalog_eqop_attnum, pgeform->oid);

	for (int i = 0; i < n1; i++)
	{
		AttrNumber	keyattn = DatumGetInt16(d1[i]);
		AttrNumber	refattn = DatumGetInt16(d2[i]);
		Oid			eqop = DatumGetObjectId(d3[i]);
		Var		   *keyvar;
		Var		   *refvar;
		Oid			atttypid;
		int32		atttypmod;
		Oid			attcoll;
		HeapTuple	tup;
		Form_pg_operator opform;
		List	   *args;
		Oid			actual_arg_types[2];
		Oid			declared_arg_types[2];
		OpExpr	   *linkqual;

		get_atttypetypmodcoll(pgeform->pgerelid, keyattn, &atttypid, &atttypmod, &attcoll);
		keyvar = makeVar(edgerti, keyattn, atttypid, atttypmod, attcoll, 0);
		get_atttypetypmodcoll(refrelid, refattn, &atttypid, &atttypmod, &attcoll);
		refvar = makeVar(refrti, refattn, atttypid, atttypmod, attcoll, 0);

		tup = SearchSysCache1(OPEROID, ObjectIdGetDatum(eqop));
		if (!HeapTupleIsValid(tup))
			elog(ERROR, "cache lookup failed for operator %u", eqop);
		opform = (Form_pg_operator) GETSTRUCT(tup);
		/* An equality operator is a binary operator returning boolean result. */
		Assert(opform->oprkind == 'b'
			   && RegProcedureIsValid(opform->oprcode)
			   && opform->oprresult == BOOLOID
			   && !get_func_retset(opform->oprcode));

		/*
		 * Prepare operands and cast them to the types required by the
		 * equality operator. Similar to PK/FK quals, referenced vertex key is
		 * used as left operand and referencing edge key is used as right
		 * operand.
		 */
		args = list_make2(refvar, keyvar);
		actual_arg_types[0] = exprType((Node *) refvar);
		actual_arg_types[1] = exprType((Node *) keyvar);
		declared_arg_types[0] = opform->oprleft;
		declared_arg_types[1] = opform->oprright;
		make_fn_arguments(pstate, args, actual_arg_types, declared_arg_types);

		linkqual = makeNode(OpExpr);
		linkqual->opno = opform->oid;
		linkqual->opfuncid = opform->oprcode;
		linkqual->opresulttype = opform->oprresult;
		linkqual->opretset = false;
		/* opcollid and inputcollid will be set by parse_collate.c */
		linkqual->args = args;
		linkqual->location = -1;

		ReleaseSysCache(tup);
		quals = lappend(quals, linkqual);
	}

	assign_expr_collations(pstate, (Node *) quals);

	return quals;
}

/*
 * ============================================================================
 * 【中文注释】is_property_associated_with_label —— 判断属性是否关联到某标签
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判断给定属性（propoid）是否与给定标签（labeloid）关联。一个标签通过其所关联的
 *   任意元素投影出相同的属性集合，因此只要该标签的任一关联元素带有该属性即判定为
 *   关联。用于 replace_property_refs_mutator() 中决定"属性引用应解析为具体表达式
 *   还是 NULL"。
 *
 * 参数：
 *   labeloid - 标签 OID（pg_propgraph_label）。
 *   propoid  - 属性 OID（pg_propgraph_property）。
 *
 * 返回值：
 *   bool —— 属性与标签关联返回 true，否则 false。
 *
 * 设计思想：
 *   1. 实现：以 RowShareLock 打开 pg_propgraph_element_label，按标签 OID 取该标签
 *      关联的第一个元素（pg_propgraph_element_label 中"标签 → 元素"唯一），再以
 *      PROPGRAPHLABELPROP 缓存检查该元素是否挂有该属性。取第一个元素即可，因为
 *      同一标签投影的属性集合对每个关联元素一致。
 *   2. 加 RowShareLock 保证并发 DDL（如删除标签关联）不会读到不一致的目录视图；
 *      扫描用索引 pg_propgraph_element_label_label_index，命中即终止扫描。
 *   3. 返回 true 的情形会被上层当作"属性属于该标签"处理，从而允许把属性引用解析为
 *      该元素的实际值表达式（或 NULL 常量），而非报"属性不存在"的错误。
 * ============================================================================
 */
static bool
is_property_associated_with_label(Oid labeloid, Oid propoid)
{
	Relation	rel;
	SysScanDesc scan;
	ScanKeyData key[1];
	HeapTuple	tup;
	bool		associated = false;

	rel = table_open(PropgraphElementLabelRelationId, RowShareLock);
	ScanKeyInit(&key[0],
				Anum_pg_propgraph_element_label_pgellabelid,
				BTEqualStrategyNumber,
				F_OIDEQ, ObjectIdGetDatum(labeloid));
	scan = systable_beginscan(rel, PropgraphElementLabelLabelIndexId,
							  true, NULL, 1, key);

	if (HeapTupleIsValid(tup = systable_getnext(scan)))
	{
		Form_pg_propgraph_element_label ele_label = (Form_pg_propgraph_element_label) GETSTRUCT(tup);

		associated = SearchSysCacheExists2(PROPGRAPHLABELPROP,
										   ObjectIdGetDatum(ele_label->oid), ObjectIdGetDatum(propoid));
	}
	systable_endscan(scan);
	table_close(rel, RowShareLock);

	return associated;
}

/*
 * ============================================================================
 * 【中文注释】get_element_property_expr —— 取元素上某属性的值表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   若给定图元素（elemoid）经由其任意关联标签带有给定属性（propoid），返回该属性
 *   的值表达式（把目录中存储的 plpexpr 还原为节点树，并把其中 varno = 1 改为目标
 *   rtindex）；否则返回 NULL。供 replace_property_refs_mutator() 在"属性可解析但对
 *   当前元素无值"时使用。
 *
 * 参数：
 *   elemoid - 图元素 OID。
 *   propoid - 属性 OID。
 *   rtindex - 该元素表在查询中的 rtindex，用于改写属性表达式中的 Var 引用。
 *
 * 返回值：
 *   Node * —— 属性值表达式；元素上没有该属性时返回 NULL。
 *
 * 设计思想：
 *   1. 以 RowShareLock 扫描 pg_propgraph_element_label 找出该元素关联的全部标签；
 *      对每个 (元素, 标签) 对，用 PROPGRAPHLABELPROP 缓存查 (标签, 属性) 是否定义。
 *      找到第一处定义即返回其 plpexpr，未找到则继续，全部找不到返回 NULL。
 *   2. plpexpr 是目录里以串行化文本存放的属性表达式（stringToNode 还原）；表达式
 *      内部以 varno = 1 表示"该元素自身"，故 ChangeVarNodes(n, 1, rtindex, 0)
 *      统一对位到目标查询的 RTE。
 *   3. 与 is_property_associated_with_label() 的区别：后者只做"是否存在"的布尔判断
 *      （可据此决定返回 NULL 常量），前者要取出可执行的表达式本体；二者的组合覆盖
 *      SQL/PGQ 标准中"属性通过其它标签与元素关联但当前元素未定义"时的默认 NULL
 *      语义。
 * ============================================================================
 */
static Node *
get_element_property_expr(Oid elemoid, Oid propoid, int rtindex)
{
	Relation	rel;
	SysScanDesc scan;
	ScanKeyData key[1];
	HeapTuple	labeltup;
	Node	   *n = NULL;

	rel = table_open(PropgraphElementLabelRelationId, RowShareLock);
	ScanKeyInit(&key[0],
				Anum_pg_propgraph_element_label_pgelelid,
				BTEqualStrategyNumber,
				F_OIDEQ, ObjectIdGetDatum(elemoid));
	scan = systable_beginscan(rel, PropgraphElementLabelElementLabelIndexId,
							  true, NULL, 1, key);

	while (HeapTupleIsValid(labeltup = systable_getnext(scan)))
	{
		Form_pg_propgraph_element_label ele_label = (Form_pg_propgraph_element_label) GETSTRUCT(labeltup);

		HeapTuple	proptup = SearchSysCache2(PROPGRAPHLABELPROP,
											  ObjectIdGetDatum(ele_label->oid), ObjectIdGetDatum(propoid));

		if (!proptup)
			continue;
		n = stringToNode(TextDatumGetCString(SysCacheGetAttrNotNull(PROPGRAPHLABELPROP,
																	proptup, Anum_pg_propgraph_label_property_plpexpr)));
		ChangeVarNodes(n, 1, rtindex, 0);

		ReleaseSysCache(proptup);
		break;
	}
	systable_endscan(scan);
	table_close(rel, RowShareLock);

	return n;
}
