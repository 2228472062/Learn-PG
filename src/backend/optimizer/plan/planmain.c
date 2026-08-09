/*-------------------------------------------------------------------------
 *
 * planmain.c
 *	  Routines to plan a single query
 *
 * What's in a name, anyway?  The top-level entry point of the planner/
 * optimizer is over in planner.c, not here as you might think from the
 * file name.  But this is the main code for planning a basic join operation,
 * shorn of features like subselects, inheritance, aggregates, grouping,
 * and so on.  (Those are the things planner.c deals with.)
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件是"单查询计划"的核心编排代码,负责为一条基本查询(只含简单连接,
 * 不含子查询、继承、聚合、分组等复杂特性——那些由 planner.c 的
 * subquery_planner 处理)生成路径(Path,即"简化计划")。注意顶层入口其实
 * 在 planner.c,文件名容易让人误以为这里是规划器入口;这里规划的是"基本
 * 连接操作"的主体。
 *
 * 【本模块在优化器中的职责】
 * query_planner() 是唯一公开入口,它按固定顺序完成一整套预处理:
 *   1. 初始化 PlannerInfo 中的各种列表(join_rel_list、等价类相关、外连接
 *      子句列表等),并建立 simple_rel_array / simple_rte_array 访问数组;
 *   2. 特殊情况优化:FROM 子句只有一个 RTE_RESULT 关系时(如
 *      "SELECT 表达式"、"INSERT ... VALUES()"),直接构造单关系路径返回,
 *      绕过全部常规流程;
 *   3. 常规流程:先收集所有参与查询的 base 关系,再分析目标列表与连接树,
 *      把 Var 引用加入各 baserel 的 targetlist、生成 PlaceHolderInfo、把
 *      限制/连接子句归类、建立等价类(EquivalenceClass)与
 *      SpecialJoinInfo,并调用 qp_callback 在等价类合并完成后计算
 *      query_pathkeys;
 *   4. 做连接消除与简化(去除无用外连接、把内关系唯一确定的半连接降级为
 *      内连接、去除唯一列上的自连接),把占位符分发到 base 关系,扩展
 *      appendrel(分区/UNION ALL 子关系),分发 UPDATE/DELETE/MERGE 的行
 *      标识列;
 *   5. 最后调用 make_one_rel() 生成顶层连接关系的全部候选路径,返回该
 *      关系的 RelOptInfo。
 *
 * 【核心数据结构】
 * - PlannerInfo(root):贯穿整个规划过程的核心上下文,记录 join_rel_list、
 *   等价类(eq_classes)、join_info_list(外连接信息)、placeholder_list、
 *   processed_tlist 等;
 * - RelOptInfo:某个(base/join/upper)关系的路径集合容器;
 * - Path:一种可能的执行方案(顺序扫描、索引扫描、各种连接方式);
 * - joinlist:由 deconstruct_jointree() 得到的待规划连接树(嵌套 List,
 *   叶节点是 RangeTblRef)。
 *
 * 【主要函数关系】
 * query_planner() 内部按固定顺序调用:setup_simple_rel_arrays →
 * add_base_rels_to_query → remove_useless_groupby_columns →
 * build_base_rel_tlists → find_placeholders_in_jointree →
 * find_lateral_references → deconstruct_jointree →
 * reconsider_outer_join_clauses → generate_base_implied_equalities →
 * (*qp_callback) → fix_placeholder_input_needed_levels → remove_useless_joins
 * → reduce_unique_semijoins → remove_useless_self_joins →
 * add_placeholders_to_base_rels → create_lateral_join_info →
 * match_foreign_keys_to_quals → extract_restriction_or_clauses →
 * setup_eager_aggregation → add_other_rels_to_query →
 * distribute_row_identity_vars → make_one_rel。其中 remove_useless_joins /
 * reduce_unique_semijoins / remove_useless_self_joins 均实现在
 * analyzejoins.c 中;generate_implied_equalities 系列在 initsplan.c。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/plan/planmain.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "optimizer/appendinfo.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/orclauses.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/placeholder.h"
#include "optimizer/planmain.h"


/*
 * query_planner
 *	  Generate a path (that is, a simplified plan) for a basic query,
 *	  which may involve joins but not any fancier features.
 *
 * Since query_planner does not handle the toplevel processing (grouping,
 * sorting, etc) it cannot select the best path by itself.  Instead, it
 * returns the RelOptInfo for the top level of joining, and the caller
 * (grouping_planner) can choose among the surviving paths for the rel.
 *
 * root describes the query to plan
 * qp_callback is a function to compute query_pathkeys once it's safe to do so
 * qp_extra is optional extra data to pass to qp_callback
 *
 * Note: the PlannerInfo node also includes a query_pathkeys field, which
 * tells query_planner the sort order that is desired in the final output
 * plan.  This value is *not* available at call time, but is computed by
 * qp_callback once we have completed merging the query's equivalence classes.
 * (We cannot construct canonical pathkeys until that's done.)
 */
/*
 * query_planner - (中文)为一条基本查询生成路径,返回顶层连接关系的 RelOptInfo
 *
 * 【作用】这是"基本查询规划"的主流程。调用者通常是 grouping_planner()(位于
 * planner.c),在本函数返回后由它根据 query_pathkeys 等约束在 final_rel 的
 * 路径集合中挑选最优路径并生成最终计划。本函数只负责把查询分析到
 * make_one_rel() 这一步:返回顶层连接(或单关系)的 RelOptInfo,里面已装好
 * 所有候选路径。
 *
 * 【设计思想】
 * - 阶段划分:本函数按依赖关系分阶段执行,前一个阶段产生的数据结构是后
 *   一阶段的输入。例如等价类(EC)合并必须先完成才能调用 qp_callback 计算
 *   query_pathkeys,因为 canonical pathkeys 依赖 EC 的最终形态;
 * - RTE_RESULT 特例:当 FROM 子句只有一个 RTE_RESULT 关系(如无 FROM 的
 *   SELECT 常量、"INSERT ... VALUES()"),直接构造一个 RelOptInfo 并把查询
 *   限定条件塞进一个 GroupResultPath(借用退化分组语义),然后设置
 *   ec_merging_done = true 假装 EC 合并已完成,再调用一次 qp_callback 以便
 *   正确处理 "SELECT 2+2 ORDER BY 1" 这类情况。这是刻意为之的快速路径;
 * - 并行安全判定:只有 parallelModeOK 且(在子查询层或 debug_parallel_query
 *   打开)时才检查 quals 是否 parallel-restricted,因为顶层纯 Result 计划
 *   通常不值得并行化;
 * - 延迟扩展 appendrel:把 add_other_rels_to_query() 放到最后,使每个
 *   baserel 在扩展子关系前已拥有尽可能完整的信息(全部限制子句),这样可
 *   以裁剪不满足限制子句的分区。
 *
 * 【参数】
 *   root        —— PlannerInfo,描述待规划的查询;内含 parse(Query)、glob
 *                  (PlannerGlobal)等。其中的 query_pathkeys 字段在调用时
 *                  尚不可用,必须由 qp_callback 计算;
 *   qp_callback —— 回调函数,在等价类合并完成后被调用,用于计算
 *                  query_pathkeys、sort_pathkeys 等路径键字段(对常规调用
 *                  者即 grouping_planner 的 grouping_planner_callback);
 *   qp_extra    —— 传给 qp_callback 的可选附加数据,本函数原样透传。
 * 【返回值】顶层连接关系(或唯一的 base 关系)的 RelOptInfo;若无法构造至少
 * 一个可用路径会直接 elog(ERROR)。
 */
RelOptInfo *
query_planner(PlannerInfo *root,
			  query_pathkeys_callback qp_callback, void *qp_extra)
{
	Query	   *parse = root->parse;
	List	   *joinlist;
	RelOptInfo *final_rel;

	/*
	 * Init planner lists to empty.
	 *
	 * NOTE: append_rel_list was set up by subquery_planner, so do not touch
	 * here.
	 */
	root->join_rel_list = NIL;
	root->join_rel_hash = NULL;
	root->join_rel_level = NULL;
	root->join_cur_level = 0;
	root->canon_pathkeys = NIL;
	root->left_join_clauses = NIL;
	root->right_join_clauses = NIL;
	root->full_join_clauses = NIL;
	root->join_info_list = NIL;
	root->placeholder_list = NIL;
	root->placeholder_array = NULL;
	root->placeholder_array_size = 0;
	root->agg_clause_list = NIL;
	root->group_expr_list = NIL;
	root->tlist_vars = NIL;
	root->fkey_list = NIL;
	root->initial_rels = NIL;

	/*
	 * Set up arrays for accessing base relations and AppendRelInfos.
	 */
	setup_simple_rel_arrays(root);

	/*
	 * In the trivial case where the jointree is a single RTE_RESULT relation,
	 * bypass all the rest of this function and just make a RelOptInfo and its
	 * one access path.  This is worth optimizing because it applies for
	 * common cases like "SELECT expression" and "INSERT ... VALUES()".
	 */
	Assert(parse->jointree->fromlist != NIL);
	if (list_length(parse->jointree->fromlist) == 1)
	{
		Node	   *jtnode = (Node *) linitial(parse->jointree->fromlist);

		if (IsA(jtnode, RangeTblRef))
		{
			int			varno = ((RangeTblRef *) jtnode)->rtindex;
			RangeTblEntry *rte = root->simple_rte_array[varno];

			Assert(rte != NULL);
			if (rte->rtekind == RTE_RESULT)
			{
				/* Make the RelOptInfo for it directly */
				final_rel = build_simple_rel(root, varno, NULL);

				/*
				 * If query allows parallelism in general, check whether the
				 * quals are parallel-restricted.  (We need not check
				 * final_rel->reltarget because it's empty at this point.
				 * Anything parallel-restricted in the query tlist will be
				 * dealt with later.)  We should always do this in a subquery,
				 * since it might be useful to use the subquery in parallel
				 * paths in the parent level.  At top level this is normally
				 * not worth the cycles, because a Result-only plan would
				 * never be interesting to parallelize.  However, if
				 * debug_parallel_query is on, then we want to execute the
				 * Result in a parallel worker if possible, so we must check.
				 */
				if (root->glob->parallelModeOK &&
					(root->query_level > 1 ||
					 debug_parallel_query != DEBUG_PARALLEL_OFF))
					final_rel->consider_parallel =
						is_parallel_safe(root, parse->jointree->quals);

				/*
				 * The only path for it is a trivial Result path.  We cheat a
				 * bit here by using a GroupResultPath, because that way we
				 * can just jam the quals into it without preprocessing them.
				 * (But, if you hold your head at the right angle, a FROM-less
				 * SELECT is a kind of degenerate-grouping case, so it's not
				 * that much of a cheat.)
				 */
				add_path(final_rel, (Path *)
						 create_group_result_path(root, final_rel,
												  final_rel->reltarget,
												  (List *) parse->jointree->quals));

				/* Select cheapest path (pretty easy in this case...) */
				set_cheapest(final_rel);

				/*
				 * We don't need to run generate_base_implied_equalities, but
				 * we do need to pretend that EC merging is complete.
				 */
				root->ec_merging_done = true;

				/*
				 * We still are required to call qp_callback, in case it's
				 * something like "SELECT 2+2 ORDER BY 1".
				 */
				(*qp_callback) (root, qp_extra);

				return final_rel;
			}
		}
	}

	/*
	 * Construct RelOptInfo nodes for all base relations used in the query.
	 * Appendrel member relations ("other rels") will be added later.
	 *
	 * Note: the reason we find the baserels by searching the jointree, rather
	 * than scanning the rangetable, is that the rangetable may contain RTEs
	 * for rels not actively part of the query, for example views.  We don't
	 * want to make RelOptInfos for them.
	 */
	add_base_rels_to_query(root, (Node *) parse->jointree);

	/* Remove any redundant GROUP BY columns */
	remove_useless_groupby_columns(root);

	/*
	 * Examine the targetlist and join tree, adding entries to baserel
	 * targetlists for all referenced Vars, and generating PlaceHolderInfo
	 * entries for all referenced PlaceHolderVars.  Restrict and join clauses
	 * are added to appropriate lists belonging to the mentioned relations. We
	 * also build EquivalenceClasses for provably equivalent expressions. The
	 * SpecialJoinInfo list is also built to hold information about join order
	 * restrictions.  Finally, we form a target joinlist for make_one_rel() to
	 * work from.
	 */
	build_base_rel_tlists(root, root->processed_tlist);

	find_placeholders_in_jointree(root);

	find_lateral_references(root);

	joinlist = deconstruct_jointree(root);

	/*
	 * Reconsider any postponed outer-join quals now that we have built up
	 * equivalence classes.  (This could result in further additions or
	 * mergings of classes.)
	 */
	reconsider_outer_join_clauses(root);

	/*
	 * If we formed any equivalence classes, generate additional restriction
	 * clauses as appropriate.  (Implied join clauses are formed on-the-fly
	 * later.)
	 */
	generate_base_implied_equalities(root);

	/*
	 * We have completed merging equivalence sets, so it's now possible to
	 * generate pathkeys in canonical form; so compute query_pathkeys and
	 * other pathkeys fields in PlannerInfo.
	 */
	(*qp_callback) (root, qp_extra);

	/*
	 * Examine any "placeholder" expressions generated during subquery pullup.
	 * Make sure that the Vars they need are marked as needed at the relevant
	 * join level.  This must be done before join removal because it might
	 * cause Vars or placeholders to be needed above a join when they weren't
	 * so marked before.
	 */
	fix_placeholder_input_needed_levels(root);

	/*
	 * Remove any useless outer joins.  Ideally this would be done during
	 * jointree preprocessing, but the necessary information isn't available
	 * until we've built baserel data structures and classified qual clauses.
	 */
	joinlist = remove_useless_joins(root, joinlist);

	/*
	 * Also, reduce any semijoins with unique inner rels to plain inner joins.
	 * Likewise, this can't be done until now for lack of needed info.
	 */
	reduce_unique_semijoins(root);

	/*
	 * Remove self joins on a unique column.
	 */
	joinlist = remove_useless_self_joins(root, joinlist);

	/*
	 * Now distribute "placeholders" to base rels as needed.  This has to be
	 * done after join removal because removal could change whether a
	 * placeholder is evaluable at a base rel.
	 */
	add_placeholders_to_base_rels(root);

	/*
	 * Construct the lateral reference sets now that we have finalized
	 * PlaceHolderVar eval levels.
	 */
	create_lateral_join_info(root);

	/*
	 * Match foreign keys to equivalence classes and join quals.  This must be
	 * done after finalizing equivalence classes, and it's useful to wait till
	 * after join removal so that we can skip processing foreign keys
	 * involving removed relations.
	 */
	match_foreign_keys_to_quals(root);

	/*
	 * Look for join OR clauses that we can extract single-relation
	 * restriction OR clauses from.
	 */
	extract_restriction_or_clauses(root);

	/*
	 * Check if eager aggregation is applicable, and if so, set up
	 * root->agg_clause_list and root->group_expr_list.
	 */
	setup_eager_aggregation(root);

	/*
	 * Now expand appendrels by adding "otherrels" for their children.  We
	 * delay this to the end so that we have as much information as possible
	 * available for each baserel, including all restriction clauses.  That
	 * let us prune away partitions that don't satisfy a restriction clause.
	 * Also note that some information such as lateral_relids is propagated
	 * from baserels to otherrels here, so we must have computed it already.
	 */
	add_other_rels_to_query(root);

	/*
	 * Distribute any UPDATE/DELETE/MERGE row identity variables to the target
	 * relations.  This can't be done till we've finished expansion of
	 * appendrels.
	 */
	distribute_row_identity_vars(root);

	/*
	 * Ready to do the primary planning.
	 */
	final_rel = make_one_rel(root, joinlist);

	/* Check that we got at least one usable path */
	if (!final_rel || !final_rel->cheapest_total_path ||
		final_rel->cheapest_total_path->param_info != NULL)
		elog(ERROR, "failed to construct the join relation");

	return final_rel;
}
