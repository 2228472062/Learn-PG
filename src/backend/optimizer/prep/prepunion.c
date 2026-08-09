/*-------------------------------------------------------------------------
 *
 * prepunion.c
 *	  Routines to plan set-operation queries.  The filename is a leftover
 *	  from a time when only UNIONs were implemented.
 *
 * There are two code paths in the planner for set-operation queries.
 * If a subquery consists entirely of simple UNION ALL operations, it
 * is converted into an "append relation".  Otherwise, it is handled
 * by the general code in this module (plan_set_operations and its
 * subroutines).  There is some support code here for the append-relation
 * case, but most of the heavy lifting for that is done elsewhere,
 * notably in prepjointree.c and allpaths.c.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 优化器"预处理器"(prep 模块)的成员,负责为集合运算
 * 查询(UNION / INTERSECT / EXCEPT 及其 ALL 变体,合称 SetOperation)生成
 * 计划路径。文件名是历史遗留(早期只实现 UNION)。
 *
 * 【两条代码路径】
 * - "纯 UNION ALL"子查询会被转换为"append 关系"(append relation):其各
 *   叶子子查询变成 AppendRelInfo 成员,交由 prepjointree.c 的
 *   pull_up_simple_union_all / flatten_simple_union_all 与 allpaths.c 共同
 *   处理(本文件只有少量辅助代码);
 * - 一般集合运算由本文件主导:plan_set_operations 递归遍历集合运算树,为
 *   每个节点生成 RelOptInfo 与路径(Append / MergeAppend + Unique / Agg /
 *   SetOp 节点),并构造输出目标列表。
 *
 * 【设计思想】
 * - 递归自底向上:对 UNION 节点,先把所有叶子/子节点规划好,收集各自的
 *   cheapest 路径(以及可能的"已排序"路径与并行 partial 路径),再决定用
 *   简单 Append(UNION ALL)、Append+HashAgg/Unique(SETOP_HASHED/SORTED,
 *   UNION 去重)还是 MergeAppend+Unique(充分利用子查询的排序);
 * - INTERSECT/EXCEPT 语义上"分组计数",可用 SetOp 节点(HashSetOp 或
 *   SortSetOp,前者要求可哈希,后者要求可排序)实现,因此生成
 *   generate_nonunion_paths 分支;
 * - 递归 UNION 用 RecursiveUnion 节点,只支持哈希去重(grouping_is_hashable),
 *   非递归分支(larg)同时作为工作表的初始内容;
 * - 目标列表统一约定:输出列的 sortgroupref 等于其 resno,便于上层按列号
 *   描述排序/分组属性;类型不一致的列用 coerce_to_common_type 强制转换;
 * - Append 的目标列表 Vars 统一用 varno == 0(占位),配合
 *   create_setop_pathtarget 用子路径的平均宽度修正宽度估算。
 *
 * 【核心数据结构与函数关系】
 * plan_set_operations(入口) -> recurse_set_operations(递归:叶子子查询由
 * subquery_planner 规划后 build_setop_child_paths 生成 SubqueryScan 路径;
 * 内部节点按类型转 generate_union_paths / generate_nonunion_paths) ;
 * generate_recursion_path 处理递归 UNION;plan_union_children 负责把
 * "同构的 UNION 子树"上提合并成一棵 N 路 UNION;generate_setop_tlist /
 * generate_append_tlist / generate_setop_grouplist / create_setop_pathtarget
 * 是目标列表与分组列表的构造工具;postprocess_setop_rel 做收尾(选最便宜
 * 路径)。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/prep/prepunion.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <math.h>

#include "access/htup_details.h"
#include "catalog/pg_type.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/cost.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/tlist.h"
#include "parser/parse_coerce.h"
#include "port/pg_bitutils.h"
#include "utils/selfuncs.h"


static RelOptInfo *recurse_set_operations(Node *setOp, PlannerInfo *root,
										  SetOperationStmt *parentOp,
										  List *colTypes, List *colCollations,
										  List *refnames_tlist,
										  List **pTargetList,
										  bool *istrivial_tlist);
static RelOptInfo *generate_recursion_path(SetOperationStmt *setOp,
										   PlannerInfo *root,
										   List *refnames_tlist,
										   List **pTargetList);
static void build_setop_child_paths(PlannerInfo *root, RelOptInfo *rel,
									bool trivial_tlist, List *child_tlist,
									List *interesting_pathkeys,
									double *pNumGroups);
static RelOptInfo *generate_union_paths(SetOperationStmt *op, PlannerInfo *root,
										List *refnames_tlist,
										List **pTargetList);
static RelOptInfo *generate_nonunion_paths(SetOperationStmt *op, PlannerInfo *root,
										   List *refnames_tlist,
										   List **pTargetList);
static List *plan_union_children(PlannerInfo *root,
								 SetOperationStmt *top_union,
								 List *refnames_tlist,
								 List **tlist_list,
								 List **istrivial_tlist);
static void postprocess_setop_rel(PlannerInfo *root, RelOptInfo *rel);
static List *generate_setop_tlist(List *colTypes, List *colCollations,
								  Index varno,
								  bool hack_constants,
								  List *input_tlist,
								  List *refnames_tlist,
								  bool *trivial_tlist);
static List *generate_append_tlist(List *colTypes, List *colCollations,
								   List *input_tlists,
								   List *refnames_tlist);
static List *generate_setop_grouplist(SetOperationStmt *op, List *targetlist);
static PathTarget *create_setop_pathtarget(PlannerInfo *root, List *tlist,
										   List *child_pathlist);


/*
 * plan_set_operations
 *
 *	  Plans the queries for a tree of set operations (UNION/INTERSECT/EXCEPT)
 *
 * This routine only deals with the setOperations tree of the given query.
 * Any top-level ORDER BY requested in root->parse->sortClause will be handled
 * when we return to grouping_planner; likewise for LIMIT.
 *
 * What we return is an "upperrel" RelOptInfo containing at least one Path
 * that implements the set-operation tree.  In addition, root->processed_tlist
 * receives a targetlist representing the output of the topmost setop node.
 */
/*
 * plan_set_operations - (中文)为整棵集合运算树规划路径的对外入口
 *
 * 【作用】由 grouping_planner 在查询含 setOperations 时调用,规划给定
 * Query 的 setOperations 树(不含顶层 ORDER BY / LIMIT,那些由
 * grouping_planner 返回后再处理)。返回一个含至少一条可行路径的
 * UPPERREL_SETOP RelOptInfo,并把顶层集合运算节点的输出目标列表写入
 * root->processed_tlist。
 *
 * 【设计思想】
 * - 前置断言:此类查询的 jointree 为空、无 GROUP BY/HAVING/WINDOW/DISTINCT
 *   (解析器/重写器已保证);等价类在这个查询级别只用于"顶层目标与对应子
 *   目标等价",不会有合并,故直接置 ec_merging_done = true 以便生成 pathkey;
 * - 列名统一取自"最左叶子子查询"的目标列表,否则 SELECT INTO 的列名会错;
 * - 递归 UNION(root->hasRecursion)走 generate_recursion_path 特殊路径,
 *   否则走 recurse_set_operations 通用递归;
 * - 在此先 setup_simple_rel_arrays,因为叶子子查询是 RTE_SUBQUERY,后续要
 *   为它们建立 RelOptInfo 与可能的 AppendRelInfo。
 *
 * 【参数】root —— PlannerInfo,其 parse->setOperations 为集合运算树根。
 * 【返回值】实现该集合运算树的 RelOptInfo(上层通过它挑选最终路径)。
 */
RelOptInfo *
plan_set_operations(PlannerInfo *root)
{
	Query	   *parse = root->parse;
	SetOperationStmt *topop = castNode(SetOperationStmt, parse->setOperations);
	Node	   *node;
	RangeTblEntry *leftmostRTE;
	Query	   *leftmostQuery;
	RelOptInfo *setop_rel;
	List	   *top_tlist;

	Assert(topop);

	/* check for unsupported stuff */
	Assert(parse->jointree->fromlist == NIL);
	Assert(parse->jointree->quals == NULL);
	Assert(parse->groupClause == NIL);
	Assert(parse->havingQual == NULL);
	Assert(parse->windowClause == NIL);
	Assert(parse->distinctClause == NIL);

	/*
	 * In the outer query level, equivalence classes are limited to classes
	 * which define that the top-level target entry is equivalent to the
	 * corresponding child target entry.  There won't be any equivalence class
	 * merging.  Mark that merging is complete to allow us to make pathkeys.
	 */
	Assert(root->eq_classes == NIL);
	root->ec_merging_done = true;

	/*
	 * We'll need to build RelOptInfos for each of the leaf subqueries, which
	 * are RTE_SUBQUERY rangetable entries in this Query.  Prepare the index
	 * arrays for those, and for AppendRelInfos in case they're needed.
	 */
	setup_simple_rel_arrays(root);

	/*
	 * Find the leftmost component Query.  We need to use its column names for
	 * all generated tlists (else SELECT INTO won't work right).
	 */
	node = topop->larg;
	while (node && IsA(node, SetOperationStmt))
		node = ((SetOperationStmt *) node)->larg;
	Assert(node && IsA(node, RangeTblRef));
	leftmostRTE = root->simple_rte_array[((RangeTblRef *) node)->rtindex];
	leftmostQuery = leftmostRTE->subquery;
	Assert(leftmostQuery != NULL);

	/*
	 * If the topmost node is a recursive union, it needs special processing.
	 */
	if (root->hasRecursion)
	{
		setop_rel = generate_recursion_path(topop, root,
											leftmostQuery->targetList,
											&top_tlist);
	}
	else
	{
		bool		trivial_tlist;

		/*
		 * Recurse on setOperations tree to generate paths for set ops. The
		 * final output paths should have just the column types shown as the
		 * output from the top-level node.
		 */
		setop_rel = recurse_set_operations((Node *) topop, root,
										   NULL,	/* no parent */
										   topop->colTypes, topop->colCollations,
										   leftmostQuery->targetList,
										   &top_tlist,
										   &trivial_tlist);
	}

	/* Must return the built tlist into root->processed_tlist. */
	root->processed_tlist = top_tlist;

	return setop_rel;
}

/*
 * recurse_set_operations
 *	  Recursively handle one step in a tree of set operations
 *
 * setOp: current step (could be a SetOperationStmt or a leaf RangeTblRef)
 * parentOp: parent step, or NULL if none (but see below)
 * colTypes: OID list of set-op's result column datatypes
 * colCollations: OID list of set-op's result column collations
 * refnames_tlist: targetlist to take column names from
 *
 * parentOp should be passed as NULL unless that step is interested in
 * getting sorted output from this step.  ("Sorted" means "sorted according
 * to the default btree opclasses of the result column datatypes".)
 *
 * Returns a RelOptInfo for the subtree, as well as these output parameters:
 * *pTargetList: receives the fully-fledged tlist for the subtree's top plan
 * *istrivial_tlist: true if, and only if, datatypes between parent and child
 * match.
 *
 * If setOp is a leaf node, this function plans the sub-query but does
 * not populate the pathlist of the returned RelOptInfo.  The caller will
 * generate SubqueryScan paths using useful path(s) of the subquery (see
 * build_setop_child_paths).  But this function does build the paths for
 * set-operation nodes.
 *
 * The pTargetList output parameter is mostly redundant with the pathtarget
 * of the returned RelOptInfo, but for the moment we need it because much of
 * the logic in this file depends on flag columns being marked resjunk.
 * XXX Now that there are no flag columns and hence no resjunk columns, we
 * could probably refactor this file to deal only in pathtargets.
 *
 * We don't have to care about typmods here: the only allowed difference
 * between set-op input and output typmods is input is a specific typmod
 * and output is -1, and that does not require a coercion.
 */
/*
 * recurse_set_operations - (中文)递归处理集合运算树中的一步
 *
 * 【作用】对给定节点 setOp 生成 RelOptInfo。叶子节点(RangeTblRef):用
 * subquery_planner 规划叶子子查询、由 generate_setop_tlist 构造其输出目标
 * 列表并生成 SubqueryScan 路径(路径生成由调用者随后调 build_setop_child_paths
 * 完成);内部节点(SetOperationStmt):按 op 分派给 generate_union_paths
 * 或 generate_nonunion_paths;必要时再加一层 Result 节点做列类型/排序规则
 * 修正投影;最后 postprocess_setop_rel 选最便宜路径。输出参数给出顶层目标
 * 列表与"目标列表是否平凡(类型无需转换)"标志。
 *
 * 【设计思想】
 * - parentOp 非 NULL 时表示父节点需要"按默认 btree 排序"的输入,会传给
 *   subquery_planner 鼓励子查询生成带正确 pathkey 的路径(INTERSECT/EXCEPT
 *   的排序实现与去重 UNION 都需要);
 * - "平凡 tlist"的定义:子查询输出类型与集合运算结果列类型完全一致、无需
 *   强制转换,此时 SubqueryScan 可以省略投影(trivial_subqueryscan);
 * - 类型/排序规则不一致时,用 generate_setop_tlist(varno = 0, hack_constants
 *   = false)生成投影 tlist 并对每条路径(含 partial 路径)应用投影;用
 *   apply_projection_to_path 的原因见函数体注释(必须与 setrefs.c 的
 *   fix_upper_expr 对 Var 的 equal() 要求契合)。
 *
 * 【参数】
 *   setOp           —— 当前节点(SetOperationStmt 或叶子 RangeTblRef);
 *   root            —— 当前 PlannerInfo;
 *   parentOp        —— 需要本节点输出的父集合运算(用于传排序需求),否则 NULL;
 *   colTypes        —— 结果列类型 OID 列表;
 *   colCollations   —— 结果列排序规则 OID 列表;
 *   refnames_tlist  —— 取列名的目标列表(最左叶子子查询的 targetList);
 *   pTargetList     —— 输出:本子树顶层计划的目标列表;
 *   istrivial_tlist —— 输出:父/子类型是否完全一致(平凡 tlist 标志)。
 * 【返回值】本子树的 RelOptInfo(叶子节点不含路径,路径由调用者补建)。
 */
static RelOptInfo *
recurse_set_operations(Node *setOp, PlannerInfo *root,
					   SetOperationStmt *parentOp,
					   List *colTypes, List *colCollations,
					   List *refnames_tlist,
					   List **pTargetList,
					   bool *istrivial_tlist)
{
	RelOptInfo *rel;

	*istrivial_tlist = true;	/* for now */

	/* Guard against stack overflow due to overly complex setop nests */
	check_stack_depth();

	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		RangeTblEntry *rte = root->simple_rte_array[rtr->rtindex];
		Query	   *subquery = rte->subquery;
		PlannerInfo *subroot;
		List	   *tlist;
		bool		trivial_tlist;
		char	   *plan_name;

		Assert(subquery != NULL);

		/* Build a RelOptInfo for this leaf subquery. */
		rel = build_simple_rel(root, rtr->rtindex, NULL);

		/* plan_params should not be in use in current query level */
		Assert(root->plan_params == NIL);

		/*
		 * Generate a subroot and Paths for the subquery.  If we have a
		 * parentOp, pass that down to encourage subquery_planner to consider
		 * suitably-sorted Paths.
		 */
		plan_name = choose_plan_name(root->glob, "setop", true);
		subroot = rel->subroot = subquery_planner(root->glob, subquery,
												  plan_name, root, NULL,
												  false, root->tuple_fraction,
												  parentOp);

		/*
		 * It should not be possible for the primitive query to contain any
		 * cross-references to other primitive queries in the setop tree.
		 */
		if (root->plan_params)
			elog(ERROR, "unexpected outer reference in set operation subquery");

		/* Figure out the appropriate target list for this subquery. */
		tlist = generate_setop_tlist(colTypes, colCollations,
									 rtr->rtindex,
									 true,
									 subroot->processed_tlist,
									 refnames_tlist,
									 &trivial_tlist);
		rel->reltarget = create_pathtarget(root, tlist);

		/* Return the fully-fledged tlist to caller, too */
		*pTargetList = tlist;
		*istrivial_tlist = trivial_tlist;
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		/* UNIONs are much different from INTERSECT/EXCEPT */
		if (op->op == SETOP_UNION)
			rel = generate_union_paths(op, root,
									   refnames_tlist,
									   pTargetList);
		else
			rel = generate_nonunion_paths(op, root,
										  refnames_tlist,
										  pTargetList);

		/*
		 * If necessary, add a Result node to project the caller-requested
		 * output columns.
		 *
		 * XXX you don't really want to know about this: setrefs.c will apply
		 * fix_upper_expr() to the Result node's tlist. This would fail if the
		 * Vars generated by generate_setop_tlist() were not exactly equal()
		 * to the corresponding tlist entries of the subplan. However, since
		 * the subplan was generated by generate_union_paths() or
		 * generate_nonunion_paths(), and hence its tlist was generated by
		 * generate_append_tlist() or generate_setop_tlist(), this will work.
		 * We just tell generate_setop_tlist() to use varno 0.
		 */
		if (!tlist_same_datatypes(*pTargetList, colTypes, false) ||
			!tlist_same_collations(*pTargetList, colCollations, false))
		{
			PathTarget *target;
			bool		trivial_tlist;
			ListCell   *lc;

			*pTargetList = generate_setop_tlist(colTypes, colCollations,
												0,
												false,
												*pTargetList,
												refnames_tlist,
												&trivial_tlist);
			*istrivial_tlist = trivial_tlist;
			target = create_pathtarget(root, *pTargetList);

			/* Apply projection to each path */
			foreach(lc, rel->pathlist)
			{
				Path	   *subpath = (Path *) lfirst(lc);
				Path	   *path;

				Assert(subpath->param_info == NULL);
				path = apply_projection_to_path(root, subpath->parent,
												subpath, target);
				/* If we had to add a Result, path is different from subpath */
				if (path != subpath)
					lfirst(lc) = path;
			}

			/* Apply projection to each partial path */
			foreach(lc, rel->partial_pathlist)
			{
				Path	   *subpath = (Path *) lfirst(lc);
				Path	   *path;

				Assert(subpath->param_info == NULL);

				/* avoid apply_projection_to_path, in case of multiple refs */
				path = (Path *) create_projection_path(root, subpath->parent,
													   subpath, target);
				lfirst(lc) = path;
			}
		}
		postprocess_setop_rel(root, rel);
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
		*pTargetList = NIL;
		rel = NULL;				/* keep compiler quiet */
	}

	return rel;
}

/*
 * Generate paths for a recursive UNION node
 */
/*
 * generate_recursion_path - (中文)为递归 UNION 节点生成 RecursiveUnion 路径
 *
 * 【作用】处理递归 UNION(parser 只允许 UNION 递归,INTERSECT/EXCEPT 报错)。
 * 分别递归规划左(larg,非递归分支)右(rarg,递归分支)两侧:右侧子查询在
 * 规划时会读取 root->non_recursive_path(先设置、用后清空)来引用工作表
 * (工作表的 path 即左侧输出);随后用 generate_append_tlist 生成输出目标
 * 列表,构造 UPPERREL_SETOP 关系并创建 RecursiveUnion 路径。非 ALL 时需
 * 求分组去重,只支持哈希实现(要求列类型可哈希)。
 *
 * 【设计思想】
 * - RecursiveUnion 执行时先输出来自左分支的"基础行",再反复迭代右分支
 *   直至工作表不再增长;右分支里的"递归引用"由 wt_param_id 标识的工作表
 *   提供,规划期通过 root->non_recursive_path 让右分支知道其行数/宽度;
 * - 分组去重时 groupList 由 generate_setop_grouplist 生成;行数估计采用
 *   悲观上界 lpath->rows + rpath->rows * 10(可递归次数未知时的启发式);
 * - 递归 UNION 没有"排序去重"实现,因此可排序但不可哈希的列类型直接报
 *   FEATURE_NOT_SUPPORTED 错误。
 *
 * 【参数】
 *   setOp         —— SETOP_UNION 类型的递归节点;
 *   root          —— PlannerInfo(要求 wt_param_id >= 0);
 *   refnames_tlist —— 取列名的目标列表;
 *   pTargetList   —— 输出:RecursiveUnion 的输出目标列表。
 * 【返回值】承载 RecursiveUnion 路径的 RelOptInfo。
 */
static RelOptInfo *
generate_recursion_path(SetOperationStmt *setOp, PlannerInfo *root,
						List *refnames_tlist,
						List **pTargetList)
{
	RelOptInfo *result_rel;
	Path	   *path;
	RelOptInfo *lrel,
			   *rrel;
	Path	   *lpath;
	Path	   *rpath;
	List	   *lpath_tlist;
	bool		lpath_trivial_tlist;
	List	   *rpath_tlist;
	bool		rpath_trivial_tlist;
	List	   *tlist;
	List	   *groupList;
	double		dNumGroups;

	/* Parser should have rejected other cases */
	if (setOp->op != SETOP_UNION)
		elog(ERROR, "only UNION queries can be recursive");
	/* Worktable ID should be assigned */
	Assert(root->wt_param_id >= 0);

	/*
	 * Unlike a regular UNION node, process the left and right inputs
	 * separately without any intention of combining them into one Append.
	 */
	lrel = recurse_set_operations(setOp->larg, root,
								  NULL, /* no value in sorted results */
								  setOp->colTypes, setOp->colCollations,
								  refnames_tlist,
								  &lpath_tlist,
								  &lpath_trivial_tlist);
	if (lrel->rtekind == RTE_SUBQUERY)
		build_setop_child_paths(root, lrel, lpath_trivial_tlist, lpath_tlist,
								NIL, NULL);
	lpath = lrel->cheapest_total_path;
	/* The right path will want to look at the left one ... */
	root->non_recursive_path = lpath;
	rrel = recurse_set_operations(setOp->rarg, root,
								  NULL, /* no value in sorted results */
								  setOp->colTypes, setOp->colCollations,
								  refnames_tlist,
								  &rpath_tlist,
								  &rpath_trivial_tlist);
	if (rrel->rtekind == RTE_SUBQUERY)
		build_setop_child_paths(root, rrel, rpath_trivial_tlist, rpath_tlist,
								NIL, NULL);
	rpath = rrel->cheapest_total_path;
	root->non_recursive_path = NULL;

	/*
	 * Generate tlist for RecursiveUnion path node --- same as in Append cases
	 */
	tlist = generate_append_tlist(setOp->colTypes, setOp->colCollations,
								  list_make2(lpath_tlist, rpath_tlist),
								  refnames_tlist);

	*pTargetList = tlist;

	/* Build result relation. */
	result_rel = fetch_upper_rel(root, UPPERREL_SETOP,
								 bms_union(lrel->relids, rrel->relids));
	result_rel->reltarget = create_pathtarget(root, tlist);

	/*
	 * If UNION, identify the grouping operators
	 */
	if (setOp->all)
	{
		groupList = NIL;
		dNumGroups = 0;
	}
	else
	{
		/* Identify the grouping semantics */
		groupList = generate_setop_grouplist(setOp, tlist);

		/* We only support hashing here */
		if (!grouping_is_hashable(groupList))
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("could not implement recursive UNION"),
					 errdetail("All column datatypes must be hashable.")));

		/*
		 * For the moment, take the number of distinct groups as equal to the
		 * total input size, ie, the worst case.
		 */
		dNumGroups = lpath->rows + rpath->rows * 10;
	}

	/*
	 * And make the path node.
	 */
	path = (Path *) create_recursiveunion_path(root,
											   result_rel,
											   lpath,
											   rpath,
											   result_rel->reltarget,
											   groupList,
											   root->wt_param_id,
											   dNumGroups);

	add_path(result_rel, path);
	postprocess_setop_rel(root, result_rel);
	return result_rel;
}

/*
 * build_setop_child_paths
 *		Build paths for the set op child relation denoted by 'rel'.
 *
 * 'rel' is an RTE_SUBQUERY relation.  We have already generated paths within
 * the subquery's subroot; the task here is to create SubqueryScan paths for
 * 'rel', representing scans of the useful subquery paths.
 *
 * interesting_pathkeys: if not NIL, also include paths that suit these
 * pathkeys, sorting any unsorted paths as required.
 * *pNumGroups: if not NULL, we estimate the number of distinct groups
 * in the result, and store it there.
 */
/*
 * build_setop_child_paths - (中文)为集合运算的 RTE_SUBQUERY 子关系构建
 * SubqueryScan 路径
 *
 * 【作用】rel 是 RTE_SUBQUERY 关系,其子查询已在 subroot 中规划完成。本函数
 * 遍历子查询 final_rel 的路径,为其中"有用的"路径生成外层 SubqueryScan
 * 路径加入 rel->pathlist:最便宜的输入路径原样纳入(供无需排序的集合运算
 * 实现),若 interesting_pathkeys 非空则额外纳入满足该排序的路径(必要时用
 * Sort / IncrementalSort 排序);若子关系支持并行,再添加一条基于子查询
 * partial 路径的 partial 路径。可选的 *pNumGroups 返回子查询输出的去重组
 * 数估计。
 *
 * 【设计思想】
 * - 排序需求由调用者通过 interesting_pathkeys 传递(如去重 UNION 的
 *   union_pathkeys、INTERSECT/EXCEPT 的 nonunion_pathkeys),排序在子查询
 *   层完成再外包 SubqueryScan,可避免外层再做一次全排序;
 * - pathkey 需用 convert_subquery_pathkeys 从子查询编号空间转换到外层;
 * - 排序取舍:presorted_keys == 0 用 Sort,否则用 IncrementalSort(除非
 *   enable_incremental_sort 关闭);只对 cheapest 路径与已部分排序的路径
 *   考虑,避免生成过多候选;
 * - setop 子关系被标记 dummy(is_dummy_rel)时传播到本层;
 * - 组数估计:子查询若自身有分组/聚合/DISTINCT/HAVING,其输出基本唯一,
 *   直接用 cheapest 路径的行数;否则用 estimate_num_groups 做统计估计
 *   (用 subroot->parse 的原始目标列表,避免 varno 0 的 Var 干扰)。
 *
 * 【参数】
 *   root               —— 外层 PlannerInfo;
 *   rel                —— 待填充路径的 RTE_SUBQUERY 子关系;
 *   trivial_tlist      —— 子 tlist 是否平凡(类型无需转换),影响 SubqueryScan
 *                         是否需要投影;
 *   child_tlist        —— 子查询输出 tlist;
 *   interesting_pathkeys —— 若非 NIL,额外生成符合该排序的路径;
 *   pNumGroups         —— 输出:去重组数估计(可为 NULL 表示不关心)。
 * 【返回值】无。
 */
static void
build_setop_child_paths(PlannerInfo *root, RelOptInfo *rel,
						bool trivial_tlist, List *child_tlist,
						List *interesting_pathkeys, double *pNumGroups)
{
	RelOptInfo *final_rel;
	List	   *setop_pathkeys = rel->subroot->setop_pathkeys;
	ListCell   *lc;

	/* it can't be a set op child rel if it's not a subquery */
	Assert(rel->rtekind == RTE_SUBQUERY);

	/* when sorting is needed, add child rel equivalences */
	if (interesting_pathkeys != NIL)
		add_setop_child_rel_equivalences(root,
										 rel,
										 child_tlist,
										 interesting_pathkeys);

	/*
	 * Mark rel with estimated output rows, width, etc.  Note that we have to
	 * do this before generating outer-query paths, else cost_subqueryscan is
	 * not happy.
	 */
	set_subquery_size_estimates(root, rel);

	/*
	 * Since we may want to add a partial path to this relation, we must set
	 * its consider_parallel flag correctly.
	 */
	final_rel = fetch_upper_rel(rel->subroot, UPPERREL_FINAL, NULL);
	rel->consider_parallel = final_rel->consider_parallel;

	/* Generate subquery scan paths for any interesting path in final_rel */
	foreach(lc, final_rel->pathlist)
	{
		Path	   *subpath = (Path *) lfirst(lc);
		List	   *pathkeys;
		Path	   *cheapest_input_path = final_rel->cheapest_total_path;
		bool		is_sorted;
		int			presorted_keys;

		/* If the input rel is dummy, propagate that to this query level */
		if (is_dummy_rel(final_rel))
		{
			mark_dummy_rel(rel);
			continue;
		}

		/*
		 * Include the cheapest path as-is so that the set operation can be
		 * cheaply implemented using a method which does not require the input
		 * to be sorted.
		 */
		if (subpath == cheapest_input_path)
		{
			/* Convert subpath's pathkeys to outer representation */
			pathkeys = convert_subquery_pathkeys(root, rel, subpath->pathkeys,
												 make_tlist_from_pathtarget(subpath->pathtarget));

			/* Generate outer path using this subpath */
			add_path(rel, (Path *) create_subqueryscan_path(root,
															rel,
															subpath,
															trivial_tlist,
															pathkeys,
															NULL));
		}

		/* skip dealing with sorted paths if the setop doesn't need them */
		if (interesting_pathkeys == NIL)
			continue;

		/*
		 * Create paths to suit final sort order required for setop_pathkeys.
		 * Here we'll sort the cheapest input path (if not sorted already) and
		 * incremental sort any paths which are partially sorted.
		 */
		is_sorted = pathkeys_count_contained_in(setop_pathkeys,
												subpath->pathkeys,
												&presorted_keys);

		if (!is_sorted)
		{
			double		limittuples = rel->subroot->limit_tuples;

			/*
			 * Try at least sorting the cheapest path and also try
			 * incrementally sorting any path which is partially sorted
			 * already (no need to deal with paths which have presorted keys
			 * when incremental sort is disabled unless it's the cheapest
			 * input path).
			 */
			if (subpath != cheapest_input_path &&
				(presorted_keys == 0 || !enable_incremental_sort))
				continue;

			/*
			 * We've no need to consider both a sort and incremental sort.
			 * We'll just do a sort if there are no presorted keys and an
			 * incremental sort when there are presorted keys.
			 */
			if (presorted_keys == 0 || !enable_incremental_sort)
				subpath = (Path *) create_sort_path(rel->subroot,
													final_rel,
													subpath,
													setop_pathkeys,
													limittuples);
			else
				subpath = (Path *) create_incremental_sort_path(rel->subroot,
																final_rel,
																subpath,
																setop_pathkeys,
																presorted_keys,
																limittuples);
		}

		/*
		 * subpath is now sorted, so add it to the pathlist.  We already added
		 * the cheapest_input_path above, so don't add it again unless we just
		 * sorted it.
		 */
		if (subpath != cheapest_input_path)
		{
			/* Convert subpath's pathkeys to outer representation */
			pathkeys = convert_subquery_pathkeys(root, rel, subpath->pathkeys,
												 make_tlist_from_pathtarget(subpath->pathtarget));

			/* Generate outer path using this subpath */
			add_path(rel, (Path *) create_subqueryscan_path(root,
															rel,
															subpath,
															trivial_tlist,
															pathkeys,
															NULL));
		}
	}

	/* if consider_parallel is false, there should be no partial paths */
	Assert(final_rel->consider_parallel ||
		   final_rel->partial_pathlist == NIL);

	/*
	 * If we have a partial path for the child relation, we can use that to
	 * build a partial path for this relation.  But there's no point in
	 * considering any path but the cheapest.
	 */
	if (rel->consider_parallel && bms_is_empty(rel->lateral_relids) &&
		final_rel->partial_pathlist != NIL)
	{
		Path	   *partial_subpath;
		Path	   *partial_path;

		partial_subpath = linitial(final_rel->partial_pathlist);
		partial_path = (Path *)
			create_subqueryscan_path(root, rel, partial_subpath,
									 trivial_tlist,
									 NIL, NULL);
		add_partial_path(rel, partial_path);
	}

	postprocess_setop_rel(root, rel);

	/*
	 * Estimate number of groups if caller wants it.  If the subquery used
	 * grouping or aggregation, its output is probably mostly unique anyway;
	 * otherwise do statistical estimation.
	 *
	 * XXX you don't really want to know about this: we do the estimation
	 * using the subroot->parse's original targetlist expressions, not the
	 * subroot->processed_tlist which might seem more appropriate.  The reason
	 * is that if the subquery is itself a setop, it may return a
	 * processed_tlist containing "varno 0" Vars generated by
	 * generate_append_tlist, and those would confuse estimate_num_groups
	 * mightily.  We ought to get rid of the "varno 0" hack, but that requires
	 * a redesign of the parsetree representation of setops, so that there can
	 * be an RTE corresponding to each setop's output. Note, we use this not
	 * subquery's targetlist but subroot->parse's targetlist, because it was
	 * revised by self-join removal.  subquery's targetlist might contain the
	 * references to the removed relids.
	 */
	if (pNumGroups)
	{
		PlannerInfo *subroot = rel->subroot;
		Query	   *subquery = subroot->parse;

		if (subquery->groupClause || subquery->groupingSets ||
			subquery->distinctClause || subroot->hasHavingQual ||
			subquery->hasAggs)
			*pNumGroups = rel->cheapest_total_path->rows;
		else
			*pNumGroups = estimate_num_groups(subroot,
											  get_tlist_exprs(subroot->parse->targetList, false),
											  rel->cheapest_total_path->rows,
											  NULL,
											  NULL);
	}
}

/*
 * Generate paths for a UNION or UNION ALL node
 */
/*
 * generate_union_paths - (中文)为 UNION / UNION ALL 节点生成路径
 *
 * 【作用】递归合并同构的 UNION 子树(plan_union_children 可把多个 UNION
 * 合并成一棵 N 路),用 generate_append_tlist 生成 Append 的目标列表;若为
 * 去重 UNION(!op->all)且可排序,构造 union_pathkeys 并让各子关系生成
 * 排序路径;随后基于各子关系的最便宜路径生成 Append 路径(以及并行
 * Append + Gather 路径),并在 !op->all 时在其上叠加 HashAgg / Sort+Unique
 * 去重路径,有排序路径时再生成 MergeAppend+Unique 路径;UNION ALL 则直接
 * 采用 Append / Gather 路径。
 *
 * 【设计思想】
 * - 去重行数估计:dNumChildGroups 累加各非 dummy 子关系的组数,利用
 *   distinct(A ∪ B) ≤ distinct(A) + distinct(B) 作为上界;
 * - 排序优先(先制 union_pathkeys)是为了:① 让子查询产出排序路径,从而
 *   可能用 MergeAppend+Unique 免去全局排序;② root->query_pathkeys 同步,
 *   上层 ORDER BY 若恰好匹配即可省去排序;
 * - 并行路径只在所有子关系都 consider_parallel 且有 partial 路径时有效;
 *   parallel_workers 取各子路径的最大值,并按 enable_parallel_append 用
 *   log2(子关系数) 提高下限;
 * - 若某子关系无法产出排序路径(常见于类型转换后 tlist 不再匹配),放弃
 *   try_sorted 整体回退;
 * - 所有 UNION 子关系都是 dummy(空)时,结果关系也标记为 dummy。
 *
 * 【参数】
 *   op            —— SETOP_UNION 节点;
 *   root          —— PlannerInfo;
 *   refnames_tlist —— 取列名的目标列表;
 *   pTargetList   —— 输出:Append 的输出目标列表。
 * 【返回值】承载路径的 UPPERREL_SETOP RelOptInfo。
 */
static RelOptInfo *
generate_union_paths(SetOperationStmt *op, PlannerInfo *root,
					 List *refnames_tlist,
					 List **pTargetList)
{
	Relids		relids = NULL;
	RelOptInfo *result_rel;
	ListCell   *lc;
	ListCell   *lc2;
	ListCell   *lc3;
	AppendPathInput cheapest = {0};
	AppendPathInput ordered = {0};
	AppendPathInput partial = {0};
	bool		partial_paths_valid = true;
	bool		consider_parallel = true;
	List	   *rellist;
	List	   *tlist_list;
	List	   *trivial_tlist_list;
	List	   *tlist;
	List	   *groupList = NIL;
	Path	   *apath;
	Path	   *gpath = NULL;
	bool		try_sorted = false;
	List	   *union_pathkeys = NIL;
	double		dNumChildGroups = 0;

	/*
	 * If any of my children are identical UNION nodes (same op, all-flag, and
	 * colTypes/colCollations) then they can be merged into this node so that
	 * we generate only one Append/MergeAppend and unique-ification for the
	 * lot.  Recurse to find such nodes.
	 */
	rellist = plan_union_children(root,
								  op,
								  refnames_tlist,
								  &tlist_list,
								  &trivial_tlist_list);

	/*
	 * Generate tlist for Append/MergeAppend plan node.
	 *
	 * The tlist for an Append plan isn't important as far as the Append is
	 * concerned, but we must make it look real anyway for the benefit of the
	 * next plan level up.
	 */
	tlist = generate_append_tlist(op->colTypes, op->colCollations,
								  tlist_list, refnames_tlist);
	*pTargetList = tlist;

	/* For UNIONs (not UNION ALL), try sorting, if sorting is possible */
	if (!op->all)
	{
		/* Identify the grouping semantics */
		groupList = generate_setop_grouplist(op, tlist);

		if (grouping_is_sortable(op->groupClauses))
		{
			try_sorted = true;
			/* Determine the pathkeys for sorting by the whole target list */
			union_pathkeys = make_pathkeys_for_sortclauses(root, groupList,
														   tlist);

			root->query_pathkeys = union_pathkeys;
		}
	}

	/*
	 * Now that we've got the append target list, we can build the union child
	 * paths.
	 */
	forthree(lc, rellist, lc2, trivial_tlist_list, lc3, tlist_list)
	{
		RelOptInfo *rel = lfirst(lc);
		bool		trivial_tlist = lfirst_int(lc2);
		List	   *child_tlist = lfirst_node(List, lc3);
		double		childGroups = 0;

		/* only build paths for the union children */
		if (rel->rtekind == RTE_SUBQUERY)
			build_setop_child_paths(root, rel, trivial_tlist, child_tlist,
									union_pathkeys,
									op->all ? NULL : &childGroups);
		else
			childGroups = rel->rows;

		/*
		 * For UNION (not UNION ALL), accumulate the per-child distinct-group
		 * estimates.  This sum is the basis for the UNION's output estimate
		 * below: since distinct(A union B) <= distinct(A) + distinct(B), the
		 * union cannot have more distinct rows than its children do in total.
		 * Children that are known to be empty contribute nothing, so skip
		 * them.
		 */
		if (!op->all && !is_dummy_rel(rel))
			dNumChildGroups += childGroups;
	}

	/* Build path lists and relid set. */
	foreach(lc, rellist)
	{
		RelOptInfo *rel = lfirst(lc);
		Path	   *ordered_path;

		/*
		 * Record the relids so that we can identify the correct
		 * UPPERREL_SETOP RelOptInfo below.
		 */
		relids = bms_add_members(relids, rel->relids);

		/* Skip any UNION children that are proven not to yield any rows */
		if (is_dummy_rel(rel))
			continue;

		cheapest.subpaths = lappend(cheapest.subpaths,
									rel->cheapest_total_path);

		if (try_sorted)
		{
			ordered_path = get_cheapest_path_for_pathkeys(rel->pathlist,
														  union_pathkeys,
														  NULL,
														  TOTAL_COST,
														  false);

			if (ordered_path != NULL)
				ordered.subpaths = lappend(ordered.subpaths, ordered_path);
			else
			{
				/*
				 * If we can't find a sorted path, just give up trying to
				 * generate a list of correctly sorted child paths.  This can
				 * happen when type coercion was added to the targetlist due
				 * to mismatching types from the union children.
				 */
				try_sorted = false;
			}
		}

		if (consider_parallel)
		{
			if (!rel->consider_parallel)
			{
				consider_parallel = false;
				partial_paths_valid = false;
			}
			else if (rel->partial_pathlist == NIL)
				partial_paths_valid = false;
			else
				partial.partial_subpaths = lappend(partial.partial_subpaths,
												   linitial(rel->partial_pathlist));
		}
	}

	/* Build result relation. */
	result_rel = fetch_upper_rel(root, UPPERREL_SETOP, relids);
	result_rel->reltarget = create_setop_pathtarget(root, tlist,
													cheapest.subpaths);
	result_rel->consider_parallel = consider_parallel;
	result_rel->consider_startup = (root->tuple_fraction > 0);

	/* If all UNION children were dummy rels, make the resulting rel dummy */
	if (cheapest.subpaths == NIL)
	{
		mark_dummy_rel(result_rel);

		return result_rel;
	}

	/*
	 * Append the child results together using the cheapest paths from each
	 * union child.
	 */
	apath = (Path *) create_append_path(root, result_rel, cheapest,
										NIL, NULL, 0, false, -1);

	/*
	 * Initialize the result row estimate to the total input size.  This is
	 * correct for UNION ALL; for the UNION case it is overwritten below with
	 * the estimated number of distinct groups.
	 */
	result_rel->rows = apath->rows;

	/*
	 * Now consider doing the same thing using the partial paths plus Append
	 * plus Gather.
	 */
	if (partial_paths_valid)
	{
		Path	   *papath;
		int			parallel_workers = 0;

		/* Find the highest number of workers requested for any subpath. */
		foreach(lc, partial.partial_subpaths)
		{
			Path	   *subpath = lfirst(lc);

			parallel_workers = Max(parallel_workers,
								   subpath->parallel_workers);
		}
		Assert(parallel_workers > 0);

		/*
		 * If the use of parallel append is permitted, always request at least
		 * log2(# of children) paths.  We assume it can be useful to have
		 * extra workers in this case because they will be spread out across
		 * the children.  The precise formula is just a guess; see
		 * add_paths_to_append_rel.
		 */
		if (enable_parallel_append)
		{
			parallel_workers = Max(parallel_workers,
								   pg_leftmost_one_pos32(list_length(partial.partial_subpaths)) + 1);
			parallel_workers = Min(parallel_workers,
								   max_parallel_workers_per_gather);
		}
		Assert(parallel_workers > 0);

		papath = (Path *)
			create_append_path(root, result_rel, partial,
							   NIL, NULL, parallel_workers,
							   enable_parallel_append, -1);
		gpath = (Path *)
			create_gather_path(root, result_rel, papath,
							   result_rel->reltarget, NULL, NULL);
	}

	if (!op->all)
	{
		bool		can_sort = grouping_is_sortable(groupList);
		bool		can_hash = grouping_is_hashable(groupList);

		/*
		 * result_rel->rows was initialized to the total input size above,
		 * which is the correct estimate for UNION ALL.  A UNION removes
		 * duplicates, so override it with the estimated number of distinct
		 * groups.
		 */
		result_rel->rows = dNumChildGroups;

		if (can_hash)
		{
			Path	   *path;

			/*
			 * Try a hash aggregate plan on 'apath'.  This is the cheapest
			 * available path containing each append child.
			 */
			path = (Path *) create_agg_path(root,
											result_rel,
											apath,
											result_rel->reltarget,
											AGG_HASHED,
											AGGSPLIT_SIMPLE,
											groupList,
											NIL,
											NULL,
											dNumChildGroups);
			add_path(result_rel, path);

			/* Try hash aggregate on the Gather path, if valid */
			if (gpath != NULL)
			{
				/* Hashed aggregate plan --- no sort needed */
				path = (Path *) create_agg_path(root,
												result_rel,
												gpath,
												result_rel->reltarget,
												AGG_HASHED,
												AGGSPLIT_SIMPLE,
												groupList,
												NIL,
												NULL,
												dNumChildGroups);
				add_path(result_rel, path);
			}
		}

		if (can_sort)
		{
			Path	   *path = apath;

			/* Try Sort -> Unique on the Append path */
			if (groupList != NIL)
				path = (Path *) create_sort_path(root, result_rel, path,
												 make_pathkeys_for_sortclauses(root, groupList, tlist),
												 -1.0);

			path = (Path *) create_unique_path(root,
											   result_rel,
											   path,
											   list_length(path->pathkeys),
											   dNumChildGroups);

			add_path(result_rel, path);

			/* Try Sort -> Unique on the Gather path, if set */
			if (gpath != NULL)
			{
				path = gpath;

				path = (Path *) create_sort_path(root, result_rel, path,
												 make_pathkeys_for_sortclauses(root, groupList, tlist),
												 -1.0);

				path = (Path *) create_unique_path(root,
												   result_rel,
												   path,
												   list_length(path->pathkeys),
												   dNumChildGroups);
				add_path(result_rel, path);
			}
		}

		/*
		 * Try making a MergeAppend path if we managed to find a path with the
		 * correct pathkeys in each union child query.
		 */
		if (try_sorted && groupList != NIL)
		{
			Path	   *path;

			path = (Path *) create_merge_append_path(root,
													 result_rel,
													 ordered.subpaths,
													 NIL,
													 union_pathkeys,
													 NULL);

			/* and make the MergeAppend unique */
			path = (Path *) create_unique_path(root,
											   result_rel,
											   path,
											   list_length(tlist),
											   dNumChildGroups);

			add_path(result_rel, path);
		}
	}
	else
	{
		/* UNION ALL */
		add_path(result_rel, apath);

		if (gpath != NULL)
			add_path(result_rel, gpath);
	}

	return result_rel;
}

/*
 * Generate paths for an INTERSECT, INTERSECT ALL, EXCEPT, or EXCEPT ALL node
 */
/*
 * generate_nonunion_paths - (中文)为 INTERSECT / EXCEPT 节点生成路径
 *
 * 【作用】递归规划左右两个输入(强制 tuple_fraction = 0 让子查询取全部
 * 行),用 generate_setop_tlist 构造 SetOp 的目标列表与分组列表;判断分组
 * 语义可用哈希/排序;EXCEPT 保持左输入在左,INTERSECT 则把组数较少的一侧
 * 放到左边(利于哈希表大小与空输入快速路径);处理"输入可证明为空"的短路
 * 情形(EXCEPT 左空→结果空、右空→直接扫描左;INTERSECT 任一空→结果空);
 * 然后按可用性生成 HashSetOp 路径与 SortSetOp 路径(SortSetOp 需要两个
 * 输入按相同分组键排序,必要时在子查询层排序)。
 *
 * 【设计思想】
 * - SetOp 分组计数语义:EXCEPT 需要知道左输入的每个组计数、右输入每个组
 *   的计数,ALL 与去重版本输出规则不同,由 SetOpCmd 编码;
 * - 行数估计:哈希表条目数取 EXCEPT 的左组数、INTERSECT 的较小侧组数;
 *   输出行数在 ALL 时取左行数(EXCEPT)或较小行数(INTERSECT),去重时
 *   等于组数(均为保守上界);
 * - 左右输入的交换(INTERSECT)会影响 relids 并集、宽度估计,因此 tlist、
 *   组数、RelOptInfo 都要一起换;
 * - 排序实现:先看 cheapest 路径是否已满足排序,否则从子关系路径中找
 *   nonunion_pathkeys 对应路径,再退化为在最便宜路径上加 Sort。
 *
 * 【参数】
 *   op            —— SETOP_INTERSECT 或 SETOP_EXCEPT 节点;
 *   root          —— PlannerInfo;
 *   refnames_tlist —— 取列名的目标列表;
 *   pTargetList   —— 输出:SetOp 的输出目标列表。
 * 【返回值】承载路径的 UPPERREL_SETOP RelOptInfo。
 */
static RelOptInfo *
generate_nonunion_paths(SetOperationStmt *op, PlannerInfo *root,
						List *refnames_tlist,
						List **pTargetList)
{
	RelOptInfo *result_rel;
	RelOptInfo *lrel,
			   *rrel;
	double		save_fraction = root->tuple_fraction;
	Path	   *lpath,
			   *rpath,
			   *path;
	List	   *lpath_tlist,
			   *rpath_tlist,
			   *tlist,
			   *groupList;
	bool		lpath_trivial_tlist,
				rpath_trivial_tlist,
				result_trivial_tlist;
	List	   *nonunion_pathkeys = NIL;
	double		dLeftGroups,
				dRightGroups,
				dNumGroups,
				dNumOutputRows;
	bool		can_sort;
	bool		can_hash;
	SetOpCmd	cmd;

	/*
	 * Tell children to fetch all tuples.
	 */
	root->tuple_fraction = 0.0;

	/* Recurse on children */
	lrel = recurse_set_operations(op->larg, root,
								  op,
								  op->colTypes, op->colCollations,
								  refnames_tlist,
								  &lpath_tlist,
								  &lpath_trivial_tlist);

	rrel = recurse_set_operations(op->rarg, root,
								  op,
								  op->colTypes, op->colCollations,
								  refnames_tlist,
								  &rpath_tlist,
								  &rpath_trivial_tlist);

	/*
	 * Generate tlist for SetOp plan node.
	 *
	 * The tlist for a SetOp plan isn't important so far as the SetOp is
	 * concerned, but we must make it look real anyway for the benefit of the
	 * next plan level up.
	 */
	tlist = generate_setop_tlist(op->colTypes, op->colCollations,
								 0, false, lpath_tlist, refnames_tlist,
								 &result_trivial_tlist);

	/* We should not have needed any type coercions in the tlist */
	Assert(result_trivial_tlist);

	*pTargetList = tlist;

	/* Identify the grouping semantics */
	groupList = generate_setop_grouplist(op, tlist);

	/* Check whether the operators support sorting or hashing */
	can_sort = grouping_is_sortable(groupList);
	can_hash = grouping_is_hashable(groupList);
	if (!can_sort && !can_hash)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
		/* translator: %s is INTERSECT or EXCEPT */
				 errmsg("could not implement %s",
						(op->op == SETOP_INTERSECT) ? "INTERSECT" : "EXCEPT"),
				 errdetail("Some of the datatypes only support hashing, while others only support sorting.")));

	if (can_sort)
	{
		/* Determine the pathkeys for sorting by the whole target list */
		nonunion_pathkeys = make_pathkeys_for_sortclauses(root, groupList,
														  tlist);

		root->query_pathkeys = nonunion_pathkeys;
	}

	/*
	 * Now that we've got all that info, we can build the child paths.
	 */
	if (lrel->rtekind == RTE_SUBQUERY)
		build_setop_child_paths(root, lrel, lpath_trivial_tlist, lpath_tlist,
								nonunion_pathkeys, &dLeftGroups);
	else
		dLeftGroups = lrel->rows;
	if (rrel->rtekind == RTE_SUBQUERY)
		build_setop_child_paths(root, rrel, rpath_trivial_tlist, rpath_tlist,
								nonunion_pathkeys, &dRightGroups);
	else
		dRightGroups = rrel->rows;

	/* Undo effects of forcing tuple_fraction to 0 */
	root->tuple_fraction = save_fraction;

	/*
	 * For EXCEPT, we must put the left input first.  For INTERSECT, either
	 * order should give the same results, and we prefer to put the smaller
	 * input first in order to (a) minimize the size of the hash table in the
	 * hashing case, and (b) improve our chances of exploiting the executor's
	 * fast path for empty left-hand input.  "Smaller" means the one with the
	 * fewer groups.
	 */
	if (op->op != SETOP_EXCEPT && dLeftGroups > dRightGroups)
	{
		/* need to swap the two inputs */
		RelOptInfo *tmprel;
		List	   *tmplist;
		double		tmpd;

		tmprel = lrel;
		lrel = rrel;
		rrel = tmprel;
		tmplist = lpath_tlist;
		lpath_tlist = rpath_tlist;
		rpath_tlist = tmplist;
		tmpd = dLeftGroups;
		dLeftGroups = dRightGroups;
		dRightGroups = tmpd;
	}

	lpath = lrel->cheapest_total_path;
	rpath = rrel->cheapest_total_path;

	/* Build result relation. */
	result_rel = fetch_upper_rel(root, UPPERREL_SETOP,
								 bms_union(lrel->relids, rrel->relids));

	/*
	 * Create the PathTarget and set the width accordingly.  For EXCEPT, since
	 * the set op result won't contain rows from the rpath, we only account
	 * for the width of the lpath.  For INTERSECT, use both input paths.
	 */
	if (op->op == SETOP_EXCEPT)
		result_rel->reltarget = create_setop_pathtarget(root, tlist,
														list_make1(lpath));
	else
		result_rel->reltarget = create_setop_pathtarget(root, tlist,
														list_make2(lpath, rpath));

	/* Check for provably empty setop inputs and add short-circuit paths. */
	if (op->op == SETOP_EXCEPT)
	{
		/*
		 * For EXCEPTs, if the left side is dummy then there's no need to
		 * inspect the right-hand side as scanning the right to find tuples to
		 * remove won't make the left-hand input any more empty.
		 */
		if (is_dummy_rel(lrel))
		{
			mark_dummy_rel(result_rel);

			return result_rel;
		}

		/* Handle EXCEPTs with dummy right input */
		if (is_dummy_rel(rrel))
		{
			if (op->all)
			{
				Path	   *apath;
				AppendPathInput append = {0};

				append.subpaths = list_make1(lpath);

				/*
				 * EXCEPT ALL: If the right-hand input is dummy then we can
				 * simply scan the left-hand input.  To keep createplan.c
				 * happy, use a single child Append to handle the translation
				 * between the set op targetlist and the targetlist of the
				 * left input.  The Append will be removed in setrefs.c.
				 */
				apath = (Path *) create_append_path(root, result_rel,
													append, NIL, NULL, 0,
													false, -1);

				add_path(result_rel, apath);

				return result_rel;
			}
			else
			{
				/*
				 * To make EXCEPT with a dummy RHS work means having to
				 * deduplicate the left input.  That could be done with
				 * AggPaths, but it doesn't seem worth the effort.  Let the
				 * normal path generation code below handle this one.
				 */
			}
		}
	}
	else
	{
		/*
		 * For INTERSECT, if either input is a dummy rel then we can mark the
		 * result_rel as dummy since intersecting with an empty relation can
		 * never yield any results.  This is true regardless of INTERSECT or
		 * INTERSECT ALL.
		 */
		if (is_dummy_rel(lrel) || is_dummy_rel(rrel))
		{
			mark_dummy_rel(result_rel);

			return result_rel;
		}
	}

	/*
	 * Estimate number of distinct groups that we'll need hashtable entries
	 * for; this is the size of the left-hand input for EXCEPT, or the smaller
	 * input for INTERSECT.  Also estimate the number of eventual output rows.
	 * In non-ALL cases, we estimate each group produces one output row; in
	 * ALL cases use the relevant relation size.  These are worst-case
	 * estimates, of course, but we need to be conservative.
	 */
	if (op->op == SETOP_EXCEPT)
	{
		dNumGroups = dLeftGroups;
		dNumOutputRows = op->all ? lpath->rows : dNumGroups;
	}
	else
	{
		dNumGroups = dLeftGroups;
		dNumOutputRows = op->all ? Min(lpath->rows, rpath->rows) : dNumGroups;
	}
	result_rel->rows = dNumOutputRows;

	/* Select the SetOpCmd type */
	switch (op->op)
	{
		case SETOP_INTERSECT:
			cmd = op->all ? SETOPCMD_INTERSECT_ALL : SETOPCMD_INTERSECT;
			break;
		case SETOP_EXCEPT:
			cmd = op->all ? SETOPCMD_EXCEPT_ALL : SETOPCMD_EXCEPT;
			break;
		default:
			elog(ERROR, "unrecognized set op: %d", (int) op->op);
			cmd = SETOPCMD_INTERSECT;	/* keep compiler quiet */
			break;
	}

	/*
	 * If we can hash, that just requires a SetOp atop the cheapest inputs.
	 */
	if (can_hash)
	{
		path = (Path *) create_setop_path(root,
										  result_rel,
										  lpath,
										  rpath,
										  cmd,
										  SETOP_HASHED,
										  groupList,
										  dNumGroups,
										  dNumOutputRows);
		add_path(result_rel, path);
	}

	/*
	 * If we can sort, generate the cheapest sorted input paths, and add a
	 * SetOp atop those.
	 */
	if (can_sort)
	{
		List	   *pathkeys;
		Path	   *slpath,
				   *srpath;

		/* First the left input ... */
		pathkeys = make_pathkeys_for_sortclauses(root,
												 groupList,
												 lpath_tlist);
		if (pathkeys_contained_in(pathkeys, lpath->pathkeys))
			slpath = lpath;		/* cheapest path is already sorted */
		else
		{
			slpath = get_cheapest_path_for_pathkeys(lrel->pathlist,
													nonunion_pathkeys,
													NULL,
													TOTAL_COST,
													false);
			/* Subquery failed to produce any presorted paths? */
			if (slpath == NULL)
				slpath = (Path *) create_sort_path(root,
												   lpath->parent,
												   lpath,
												   pathkeys,
												   -1.0);
		}

		/* and now the same for the right. */
		pathkeys = make_pathkeys_for_sortclauses(root,
												 groupList,
												 rpath_tlist);
		if (pathkeys_contained_in(pathkeys, rpath->pathkeys))
			srpath = rpath;		/* cheapest path is already sorted */
		else
		{
			srpath = get_cheapest_path_for_pathkeys(rrel->pathlist,
													nonunion_pathkeys,
													NULL,
													TOTAL_COST,
													false);
			/* Subquery failed to produce any presorted paths? */
			if (srpath == NULL)
				srpath = (Path *) create_sort_path(root,
												   rpath->parent,
												   rpath,
												   pathkeys,
												   -1.0);
		}

		path = (Path *) create_setop_path(root,
										  result_rel,
										  slpath,
										  srpath,
										  cmd,
										  SETOP_SORTED,
										  groupList,
										  dNumGroups,
										  dNumOutputRows);
		add_path(result_rel, path);
	}

	return result_rel;
}

/*
 * Pull up children of a UNION node that are identically-propertied UNIONs,
 * and perform planning of the queries underneath the N-way UNION.
 *
 * The result is a list of RelOptInfos containing Paths for sub-nodes, with
 * one entry for each descendant that is a leaf query or non-identical setop.
 * We also return parallel lists of the childrens' targetlists and
 * is-trivial-tlist flags.
 *
 * NOTE: we can also pull a UNION ALL up into a UNION, since the distinct
 * output rows will be lost anyway.
 */
/*
 * plan_union_children - (中文)把同构的 UNION 子树合并上提,并规划 N 路
 * UNION 下的各查询
 *
 * 【作用】用一个 pending 栈对集合运算树做宽度优先展开:凡是与顶层 UNION
 * "同构"(op 相同,且 all 标志相同或子节点为 UNION ALL,且列类型与排序
 * 规则相同)的 UNION 子树,都把自己的两个输入压栈继续展开;非同构的节点
 * 作为独立的子关系,交给 recurse_set_operations 规划。返回所有子关系
 * RelOptInfo 的列表,并平行地返回它们的 tlist 与平凡 tlist 标志。
 *
 * 【设计思想】
 * - 合并同构 UNION 的理由:多个连续 UNION 可以共用一个 Append / MergeAppend
 *   与一次去重,而不是各自生成 Append+Unique 再层层嵌套;
 * - 允许把 UNION ALL 上提到 UNION 中(op->all == true 且 top 为去重 UNION):
 *   去重操作会丢掉重复行,UNION ALL 子树的重复行反正会被滤掉,语义不变;
 * - 非 UNION ALL 的顶层(op->all == false)时,把 top_union 作为 parentOp
 *   传给子节点,鼓励它们生成排序输出,便于后续 MergeAppend 去重。
 *
 * 【参数】
 *   root             —— PlannerInfo;
 *   top_union        —— 顶层 UNION 节点;
 *   refnames_tlist   —— 取列名的目标列表;
 *   tlist_list       —— 输出:各子关系 tlist 的平行列表;
 *   istrivial_tlist  —— 输出:各子关系平凡 tlist 标志的平行列表。
 * 【返回值】子关系 RelOptInfo 列表(每个叶子子查询或非同构 setop 一项)。
 */
static List *
plan_union_children(PlannerInfo *root,
					SetOperationStmt *top_union,
					List *refnames_tlist,
					List **tlist_list,
					List **istrivial_tlist)
{
	List	   *pending_rels = list_make1(top_union);
	List	   *result = NIL;
	List	   *child_tlist;
	bool		trivial_tlist;

	*tlist_list = NIL;
	*istrivial_tlist = NIL;

	while (pending_rels != NIL)
	{
		Node	   *setOp = linitial(pending_rels);

		pending_rels = list_delete_first(pending_rels);

		if (IsA(setOp, SetOperationStmt))
		{
			SetOperationStmt *op = (SetOperationStmt *) setOp;

			if (op->op == top_union->op &&
				(op->all == top_union->all || op->all) &&
				equal(op->colTypes, top_union->colTypes) &&
				equal(op->colCollations, top_union->colCollations))
			{
				/* Same UNION, so fold children into parent */
				pending_rels = lcons(op->rarg, pending_rels);
				pending_rels = lcons(op->larg, pending_rels);
				continue;
			}
		}

		/*
		 * Not same, so plan this child separately.
		 *
		 * If top_union isn't a UNION ALL, then we are interested in sorted
		 * output from the child, so pass top_union as parentOp.  Note that
		 * this isn't necessarily the child node's immediate SetOperationStmt
		 * parent, but that's fine: it's the effective parent.
		 */
		result = lappend(result, recurse_set_operations(setOp, root,
														top_union->all ? NULL : top_union,
														top_union->colTypes,
														top_union->colCollations,
														refnames_tlist,
														&child_tlist,
														&trivial_tlist));
		*tlist_list = lappend(*tlist_list, child_tlist);
		*istrivial_tlist = lappend_int(*istrivial_tlist, trivial_tlist);
	}

	return result;
}

/*
 * postprocess_setop_rel - perform steps required after adding paths
 */
/*
 * postprocess_setop_rel - (中文)集合运算关系添加路径后的收尾处理
 *
 * 【作用】对刚填充完路径的 UPPERREL_SETOP 关系:先调用 create_upper_paths_hook
 * 扩展点(允许扩展/FDW 贡献额外路径),再调用 set_cheapest 选出总代价最小
 * (以及启动代价最小)的路径,供上层引用。
 *
 * 【设计思想】是各集合运算路径生成函数的公共收尾步骤,集中避免重复代码。
 * set_cheapest 会同时设置 cheapest_total_path 与 cheapest_startup_path。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 已生成路径的 UPPERREL_SETOP 关系。
 * 【返回值】无。
 */
static void
postprocess_setop_rel(PlannerInfo *root, RelOptInfo *rel)
{
	/*
	 * We don't currently worry about allowing FDWs to contribute paths to
	 * this relation, but give extensions a chance.
	 */
	if (create_upper_paths_hook)
		(*create_upper_paths_hook) (root, UPPERREL_SETOP,
									NULL, rel, NULL);

	/* Select cheapest path */
	set_cheapest(rel);
}

/*
 * Generate targetlist for a set-operation plan node
 *
 * colTypes: OID list of set-op's result column datatypes
 * colCollations: OID list of set-op's result column collations
 * varno: varno to use in generated Vars
 * hack_constants: true to copy up constants (see comments in code)
 * input_tlist: targetlist of this node's input node
 * refnames_tlist: targetlist to take column names from
 * trivial_tlist: output parameter, set to true if targetlist is trivial
 */
/*
 * generate_setop_tlist - (中文)为集合运算计划节点生成输出目标列表
 *
 * 【作用】对集合运算结果的每一列,生成一个 TLE:通常是一个引用输入列
 * (input_tlist)的 Var(varno 由参数给出);若 hack_constants 且输入是常量,
 * 则直接上提该常量(见设计思想);类型与结果列不一致时用 coerce_to_common_type
 * 强制转换,排序规则不一致时用 RelabelType 修正;列名取自 refnames_tlist;
 * 所有输出列统一设置 ressortgroupref = resno。*trivial_tlist 指示生成的
 * tlist 是否"平凡"(无需转换)。
 *
 * 【设计思想】
 * - hack_constants 上提常量主要是为了 UNKNOWN 常量在强制转换时得到正确
 *   结果,但只在最底层 SubqueryScan 处做,避免上层出现伪造常量;
 * - collation 必须显式正确,因为 plan_set_operations 用一组 SortGroupClause
 *   描述输出排序,而它们不带 collation 只引用 tlist 项,错则上层规划会
 *   出错;用 RelabelType 而非 CollateExpr,保证到达执行器时无需再处理;
 * - ressortgroupref = resno 是贯穿本文件的约定,使上层可直接用列号引用
 *   排序/分组属性。
 *
 * 【参数】
 *   colTypes        —— 结果列类型列表;
 *   colCollations   —— 结果列排序规则列表;
 *   varno           —— 生成 Var 所用的 varno(0 表示占位);
 *   hack_constants  —— true 时把输入常量原样上提;
 *   input_tlist     —— 本节点输入的目标列表;
 *   refnames_tlist  —— 取列名的目标列表;
 *   trivial_tlist   —— 输出:是否平凡(类型与排序规则无需任何转换)。
 * 【返回值】生成的目标列表。
 */
static List *
generate_setop_tlist(List *colTypes, List *colCollations,
					 Index varno,
					 bool hack_constants,
					 List *input_tlist,
					 List *refnames_tlist,
					 bool *trivial_tlist)
{
	List	   *tlist = NIL;
	int			resno = 1;
	ListCell   *ctlc,
			   *cclc,
			   *itlc,
			   *rtlc;
	TargetEntry *tle;
	Node	   *expr;

	*trivial_tlist = true;		/* until proven differently */

	forfour(ctlc, colTypes, cclc, colCollations,
			itlc, input_tlist, rtlc, refnames_tlist)
	{
		Oid			colType = lfirst_oid(ctlc);
		Oid			colColl = lfirst_oid(cclc);
		TargetEntry *inputtle = (TargetEntry *) lfirst(itlc);
		TargetEntry *reftle = (TargetEntry *) lfirst(rtlc);

		Assert(inputtle->resno == resno);
		Assert(reftle->resno == resno);
		Assert(!inputtle->resjunk);
		Assert(!reftle->resjunk);

		/*
		 * Generate columns referencing input columns and having appropriate
		 * data types and column names.  Insert datatype coercions where
		 * necessary.
		 *
		 * HACK: constants in the input's targetlist are copied up as-is
		 * rather than being referenced as subquery outputs.  This is mainly
		 * to ensure that when we try to coerce them to the output column's
		 * datatype, the right things happen for UNKNOWN constants.  But do
		 * this only at the first level of subquery-scan plans; we don't want
		 * phony constants appearing in the output tlists of upper-level
		 * nodes!
		 *
		 * Note that copying a constant doesn't in itself require us to mark
		 * the tlist nontrivial; see trivial_subqueryscan() in setrefs.c.
		 */
		if (hack_constants && inputtle->expr && IsA(inputtle->expr, Const))
			expr = (Node *) inputtle->expr;
		else
			expr = (Node *) makeVar(varno,
									inputtle->resno,
									exprType((Node *) inputtle->expr),
									exprTypmod((Node *) inputtle->expr),
									exprCollation((Node *) inputtle->expr),
									0);

		if (exprType(expr) != colType)
		{
			/*
			 * Note: it's not really cool to be applying coerce_to_common_type
			 * here; one notable point is that assign_expr_collations never
			 * gets run on any generated nodes.  For the moment that's not a
			 * problem because we force the correct exposed collation below.
			 * It would likely be best to make the parser generate the correct
			 * output tlist for every set-op to begin with, though.
			 */
			expr = coerce_to_common_type(NULL,	/* no UNKNOWNs here */
										 expr,
										 colType,
										 "UNION/INTERSECT/EXCEPT");
			*trivial_tlist = false; /* the coercion makes it not trivial */
		}

		/*
		 * Ensure the tlist entry's exposed collation matches the set-op. This
		 * is necessary because plan_set_operations() reports the result
		 * ordering as a list of SortGroupClauses, which don't carry collation
		 * themselves but just refer to tlist entries.  If we don't show the
		 * right collation then planner.c might do the wrong thing in
		 * higher-level queries.
		 *
		 * Note we use RelabelType, not CollateExpr, since this expression
		 * will reach the executor without any further processing.
		 */
		if (exprCollation(expr) != colColl)
		{
			expr = applyRelabelType(expr,
									exprType(expr), exprTypmod(expr), colColl,
									COERCE_IMPLICIT_CAST, -1, false);
			*trivial_tlist = false; /* the relabel makes it not trivial */
		}

		tle = makeTargetEntry((Expr *) expr,
							  (AttrNumber) resno++,
							  pstrdup(reftle->resname),
							  false);

		/*
		 * By convention, all output columns in a setop tree have
		 * ressortgroupref equal to their resno.  In some cases the ref isn't
		 * needed, but this is a cleaner way than modifying the tlist later.
		 */
		tle->ressortgroupref = tle->resno;

		tlist = lappend(tlist, tle);
	}

	return tlist;
}

/*
 * Generate targetlist for a set-operation Append node
 *
 * colTypes: OID list of set-op's result column datatypes
 * colCollations: OID list of set-op's result column collations
 * input_tlists: list of tlists for sub-plans of the Append
 * refnames_tlist: targetlist to take column names from
 *
 * The entries in the Append's targetlist should always be simple Vars;
 * we just have to make sure they have the right datatypes/typmods/collations.
 * The Vars are always generated with varno 0.
 *
 * XXX a problem with the varno-zero approach is that set_pathtarget_cost_width
 * cannot figure out a realistic width for the tlist we make here.  But we
 * ought to refactor this code to produce a PathTarget directly, anyway.
 */
/*
 * generate_append_tlist - (中文)为集合运算的 Append 节点生成目标列表
 *
 * 【作用】为 Append(UNION 的合并器)生成输出目标列表:每列是一个 varno 为
 * 0 的简单 Var,类型为集合运算结果列类型,typmod 取"各输入子 tlist 一致
 * 时该 typmod,否则 -1",排序规则取结果列 collation,列名取自
 * refnames_tlist;同样设置 ressortgroupref = resno。
 *
 * 【设计思想】
 * - Append 本身不消费目标列表(各子计划各自投影),但必须让它"看起来像真
 *   的",供上层计划阶段使用;统一 varno 0 的简单 Var 便于 setrefs.c 处理;
 * - typmod 协商:遍历所有子 tlist,若某列各子类型与 typmod 都一致则沿用
 *   (避免无谓的类型重排),否则用 -1(让类型系统按"通用 typmod"处理);
 * - 注:set_pathtarget_cost_width 无法从 varno 0 的 Var 得到真实宽度,因此
 *   create_setop_pathtarget 事后会手工修正宽度。
 *
 * 【参数】
 *   colTypes        —— 结果列类型列表;
 *   colCollations   —— 结果列排序规则列表;
 *   input_tlists    —— 各子计划的 tlist 列表(Append 的子计划);
 *   refnames_tlist  —— 取列名的目标列表。
 * 【返回值】Append 节点的输出目标列表。
 */
static List *
generate_append_tlist(List *colTypes, List *colCollations,
					  List *input_tlists,
					  List *refnames_tlist)
{
	List	   *tlist = NIL;
	int			resno = 1;
	ListCell   *curColType;
	ListCell   *curColCollation;
	ListCell   *ref_tl_item;
	int			colindex;
	TargetEntry *tle;
	Node	   *expr;
	ListCell   *tlistl;
	int32	   *colTypmods;

	/*
	 * First extract typmods to use.
	 *
	 * If the inputs all agree on type and typmod of a particular column, use
	 * that typmod; else use -1.
	 */
	colTypmods = palloc_array(int32, list_length(colTypes));

	foreach(tlistl, input_tlists)
	{
		List	   *subtlist = (List *) lfirst(tlistl);
		ListCell   *subtlistl;

		curColType = list_head(colTypes);
		colindex = 0;
		foreach(subtlistl, subtlist)
		{
			TargetEntry *subtle = (TargetEntry *) lfirst(subtlistl);

			Assert(!subtle->resjunk);
			Assert(curColType != NULL);
			if (exprType((Node *) subtle->expr) == lfirst_oid(curColType))
			{
				/* If first subplan, copy the typmod; else compare */
				int32		subtypmod = exprTypmod((Node *) subtle->expr);

				if (tlistl == list_head(input_tlists))
					colTypmods[colindex] = subtypmod;
				else if (subtypmod != colTypmods[colindex])
					colTypmods[colindex] = -1;
			}
			else
			{
				/* types disagree, so force typmod to -1 */
				colTypmods[colindex] = -1;
			}
			curColType = lnext(colTypes, curColType);
			colindex++;
		}
		Assert(curColType == NULL);
	}

	/*
	 * Now we can build the tlist for the Append.
	 */
	colindex = 0;
	forthree(curColType, colTypes, curColCollation, colCollations,
			 ref_tl_item, refnames_tlist)
	{
		Oid			colType = lfirst_oid(curColType);
		int32		colTypmod = colTypmods[colindex++];
		Oid			colColl = lfirst_oid(curColCollation);
		TargetEntry *reftle = (TargetEntry *) lfirst(ref_tl_item);

		Assert(reftle->resno == resno);
		Assert(!reftle->resjunk);
		expr = (Node *) makeVar(0,
								resno,
								colType,
								colTypmod,
								colColl,
								0);
		tle = makeTargetEntry((Expr *) expr,
							  (AttrNumber) resno++,
							  pstrdup(reftle->resname),
							  false);

		/*
		 * By convention, all output columns in a setop tree have
		 * ressortgroupref equal to their resno.  In some cases the ref isn't
		 * needed, but this is a cleaner way than modifying the tlist later.
		 */
		tle->ressortgroupref = tle->resno;

		tlist = lappend(tlist, tle);
	}

	pfree(colTypmods);

	return tlist;
}

/*
 * generate_setop_grouplist
 *		Build a SortGroupClause list defining the sort/grouping properties
 *		of the setop's output columns.
 *
 * Parse analysis already determined the properties and built a suitable
 * list, except that the entries do not have sortgrouprefs set because
 * the parser output representation doesn't include a tlist for each
 * setop.  So what we need to do here is copy that list and install
 * proper sortgrouprefs into it (copying those from the targetlist).
 */
/*
 * generate_setop_grouplist - (中文)构建描述集合运算输出列排序/分组性质的
 * SortGroupClause 列表
 *
 * 【作用】解析器已为集合运算确定每列的排序/分组属性并生成 groupClauses,
 * 但其条目的 tleSortGroupRef 为 0(解析器输出表示里每个 setop 没有独立
 * tlist)。本函数复制该列表,并按目标列表中每列的顺序,把 tleSortGroupRef
 * 填成对应列的 ressortgroupref(即其 resno)。
 *
 * 【设计思想】集合运算树输出列的 sortgroupref 统一等于 resno(见
 * generate_setop_tlist),因此这里只需把 SortGroupClause 的引用号与列号
 * 对齐。之后该列表即可用于 make_pathkeys_for_sortclauses 生成排序 pathkey
 * 或供 HashSetOp / SortSetOp / RecursiveUnion 做去重。
 *
 * 【参数】
 *   op        —— 集合运算节点(提供 groupClauses);
 *   targetlist —— 该节点已生成的输出目标列表。
 * 【返回值】填充好 tleSortGroupRef 的 SortGroupClause 列表(新的拷贝)。
 */
static List *
generate_setop_grouplist(SetOperationStmt *op, List *targetlist)
{
	List	   *grouplist = copyObject(op->groupClauses);
	ListCell   *lg;
	ListCell   *lt;

	lg = list_head(grouplist);
	foreach(lt, targetlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(lt);
		SortGroupClause *sgc;

		Assert(!tle->resjunk);

		/* non-resjunk columns should have sortgroupref = resno */
		Assert(tle->ressortgroupref == tle->resno);

		/* non-resjunk columns should have grouping clauses */
		Assert(lg != NULL);
		sgc = (SortGroupClause *) lfirst(lg);
		lg = lnext(grouplist, lg);
		Assert(sgc->tleSortGroupRef == 0);

		sgc->tleSortGroupRef = tle->ressortgroupref;
	}
	Assert(lg == NULL);
	return grouplist;
}

/*
 * create_setop_pathtarget
 *		Do the normal create_pathtarget() work, plus set the resulting
 *		PathTarget's width to the average width of the Paths in	child_pathlist
 *		weighted using the estimated row count of each path.
 *
 * Note: This is required because set op target lists use varno==0, which
 * results in a type default width estimate rather than one that's based on
 * statistics of the columns from the set op children.
 */
/*
 * create_setop_pathtarget - (中文)为集合运算关系创建 PathTarget,并按子
 * 路径的行数加权修正宽度
 *
 * 【作用】先调用 create_pathtarget 做常规转换,然后把 reltarget->width 覆盖
 * 为"各子路径的 reltarget 宽度按各自行数加权平均"。
 *
 * 【设计思想】集合运算 tlist 用 varno == 0 的占位 Var,create_pathtarget
 * 只能给它们类型默认宽度(与真实统计无关);而宽度影响排序/哈希代价估算,
 * 因此这里用子路径的真实宽度加权平均替换,得到更准确的估计。parent_rows
 * 为 0(无子路径)时保持默认宽度。
 *
 * 【参数】
 *   root           —— PlannerInfo;
 *   tlist          —— 集合运算输出目标列表;
 *   child_pathlist —— 参与该集合运算的子路径列表。
 * 【返回值】宽度已修正的 PathTarget。
 */
static PathTarget *
create_setop_pathtarget(PlannerInfo *root, List *tlist, List *child_pathlist)
{
	PathTarget *reltarget;
	ListCell   *lc;
	double		parent_rows = 0;
	double		parent_size = 0;

	reltarget = create_pathtarget(root, tlist);

	/* Calculate the total rows and total size. */
	foreach(lc, child_pathlist)
	{
		Path	   *path = (Path *) lfirst(lc);

		parent_rows += path->rows;
		parent_size += path->parent->reltarget->width * path->rows;
	}

	if (parent_rows > 0)
		reltarget->width = rint(parent_size / parent_rows);

	return reltarget;
}
