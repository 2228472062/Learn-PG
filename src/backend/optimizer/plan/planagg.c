/*-------------------------------------------------------------------------
 *
 * planagg.c
 *	  Special planning for aggregate queries.
 *
 * This module tries to replace MIN/MAX aggregate functions by subqueries
 * of the form
 *		(SELECT col FROM tab
 *		 WHERE col IS NOT NULL AND existing-quals
 *		 ORDER BY col ASC/DESC
 *		 LIMIT 1)
 * Given a suitable index on tab.col, this can be much faster than the
 * generic scan-all-the-rows aggregation plan.  We can handle multiple
 * MIN/MAX aggregates by generating multiple subqueries, and their
 * orderings can be different.  However, if the query contains any
 * non-optimizable aggregates, there's no point since we'll have to
 * scan all the rows anyway.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件实现聚合查询的特殊规划:把 MIN/MAX 聚合改写为子查询
 *		(SELECT col FROM tab
 *		 WHERE col IS NOT NULL AND existing-quals
 *		 ORDER BY col ASC/DESC
 *		 LIMIT 1)
 * 当 tab.col 上有合适的索引时,这种改写可用索引扫描代替"扫全表再聚合"的
 * 通用方案,代价可降低一个数量级。多个 MIN/MAX 聚合可以生成多个子查询,
 * 各自的排序方向可以不同。
 *
 * 【适用前提】
 * - 查询必须只含可优化的 MIN/MAX 聚合:一旦混入任何"不可优化"聚合(如
 *   COUNT、SUM、AVG),反正必须扫描全部行,做这种改写没有意义,直接放弃;
 * - 不接受 GROUP BY、多组 grouping sets、窗口函数、CTE、行锁,且 FROM 中
 *   必须恰好引用一张表(可以是普通关系,也可以是已扁平化为 appendrel 的
 *   UNION ALL 子查询);对每一聚合,其参数必须能对应到索引列(表达式
 *   不可含易变函数,且不能是行类型)。
 *
 * 【核心数据结构】
 * - MinMaxAggInfo:每个待优化的 MIN/MAX 聚合对应一个节点,记录聚合函数
 *   OID(aggfnoid)、排序算子(aggsortop)、目标表达式(target)、克隆出来的
 *   "子查询"的 PlannerInfo(subroot)、挑选出的最佳路径(path)与代价
 *   (pathcost),以及用于代替该聚合输出值的 PARAM_EXEC 参数(param);
 * - MinMaxAggPath:代表"用 initplan 求出一批 Param 值、外层用 Result 节点
 *   替换聚合"的优化路径,被塞进 UPPERREL_GROUP_AGG 上层关系,与标准
 *   聚合实现竞争。
 *
 * 【主要函数关系】
 * preprocess_minmax_aggregates() 是唯一公开入口,由 grouping_planner() 在
 * 调用 query_planner() 之前调用(此时 preprocess_aggrefs() 已填好
 * root->agginfos)。它先用 can_minmax_aggs() 检查所有聚合是否都是 MIN/MAX,
 * 再对每个聚合调用 build_minmax_path() 尝试构造索引扫描路径(它克隆当前
 * 查询层状态、改写 parsetree 后递归调用 query_planner());全部成功后才为
 * 每个聚合创建 PARAM_EXEC 输出参数,并创建 MinMaxAggPath 加入
 * UPPERREL_GROUP_AGG。minmax_qp_callback() 是克隆子查询的 pathkeys 回调,
 * fetch_agg_sort_op() 从 pg_aggregate 读取聚合的排序算子。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/plan/planagg.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "catalog/pg_aggregate.h"
#include "catalog/pg_type.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/planmain.h"
#include "optimizer/planner.h"
#include "optimizer/subselect.h"
#include "optimizer/tlist.h"
#include "parser/parse_clause.h"
#include "parser/parsetree.h"
#include "rewrite/rewriteManip.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"

static bool can_minmax_aggs(PlannerInfo *root, List **context);
static bool build_minmax_path(PlannerInfo *root, MinMaxAggInfo *mminfo,
							  Oid eqop, Oid sortop, bool reverse_sort,
							  bool nulls_first);
static void minmax_qp_callback(PlannerInfo *root, void *extra);
static Oid	fetch_agg_sort_op(Oid aggfnoid);


/*
 * preprocess_minmax_aggregates - preprocess MIN/MAX aggregates
 *
 * Check to see whether the query contains MIN/MAX aggregate functions that
 * might be optimizable via indexscans.  If it does, and all the aggregates
 * are potentially optimizable, then create a MinMaxAggPath and add it to
 * the (UPPERREL_GROUP_AGG, NULL) upperrel.
 *
 * This should be called by grouping_planner() just before it's ready to call
 * query_planner(), because we generate indexscan paths by cloning the
 * planner's state and invoking query_planner() on a modified version of
 * the query parsetree.  Thus, all preprocessing needed before query_planner()
 * must already be done.  This relies on the list of aggregates in
 * root->agginfos, so preprocess_aggrefs() must have been called already, too.
 */
/*
 * preprocess_minmax_aggregates - (中文)预处理 MIN/MAX 聚合,尝试用索引扫描改写
 *
 * 【作用】检查查询中是否含有可能用索引扫描优化的 MIN/MAX 聚合函数。若含、
 * 且所有聚合都潜在可优化,则为每个聚合构造访问路径,并创建 MinMaxAggPath
 * 加入 (UPPERREL_GROUP_AGG, NULL) 上层关系,与标准聚合实现竞争。该函数由
 * grouping_planner()(planner.c)在即将调用 query_planner() 之前调用。
 *
 * 【设计思想】
 * - 必须在此处(而不是更早)调用,因为要生成索引扫描路径需要克隆规划器
 *   当前状态并基于改写后的 parsetree 再跑一次 query_planner(),这要求所有
 *   query_planner 之前的预处理已完成;同时依赖 root->agginfos(由
 *   preprocess_aggrefs() 填好)定位聚合;
 * - 一系列"拒绝"检查(precheck)把不可优化的情形尽早排除:有 GROUP BY/
 *   多组 grouping sets/窗口函数、有 CTE、FROM 不恰好一张表、某聚合不是
 *   MIN/MAX 等——一旦命中即整体放弃,避免半吊子优化;
 * - "要么全部要么全不"原则:foreach 逐个为聚合构造路径,若任何一个
 *   无法构造索引路径则立即 return,因为只优化其中一部分没意义;
 * - 排序方向策略:对每个聚合先按"reverse ? NULLS FIRST : NULLS LAST"
 *   尝试(NULLS FIRST 更可能与反向排序算子配套的索引匹配),失败再试另一
 *   种,两种方向代价差别通常很小,不值得都估算后再比较;
 * - 创建 PARAM_EXEC 输出参数的工作不能拖到 create_plan 阶段,因为外层
 *   MinMaxAggPath 需要先有这些 Param 占位。
 *
 * 【参数】
 *   root —— PlannerInfo,描述待规划查询;函数会修改 root->minmax_aggs、
 *           并向 UPPERREL_GROUP_AGG 添加路径。
 * 【返回值】void(成功与否通过是否在 grouped_rel 中新增路径体现)。
 */
void
preprocess_minmax_aggregates(PlannerInfo *root)
{
	Query	   *parse = root->parse;
	FromExpr   *jtnode;
	RangeTblRef *rtr;
	RangeTblEntry *rte;
	List	   *aggs_list;
	RelOptInfo *grouped_rel;
	ListCell   *lc;

	/* minmax_aggs list should be empty at this point */
	Assert(root->minmax_aggs == NIL);

	/* Nothing to do if query has no aggregates */
	if (!parse->hasAggs)
		return;

	Assert(!parse->setOperations);	/* shouldn't get here if a setop */
	Assert(parse->rowMarks == NIL); /* nor if FOR UPDATE */

	/*
	 * Reject unoptimizable cases.
	 *
	 * We don't handle GROUP BY or windowing, because our current
	 * implementations of grouping require looking at all the rows anyway, and
	 * so there's not much point in optimizing MIN/MAX.
	 */
	if (parse->groupClause || list_length(parse->groupingSets) > 1 ||
		parse->hasWindowFuncs)
		return;

	/*
	 * Reject if query contains any CTEs; there's no way to build an indexscan
	 * on one so we couldn't succeed here.  (If the CTEs are unreferenced,
	 * that's not true, but it doesn't seem worth expending cycles to check.)
	 */
	if (parse->cteList)
		return;

	/*
	 * We also restrict the query to reference exactly one table, since join
	 * conditions can't be handled reasonably.  (We could perhaps handle a
	 * query containing cartesian-product joins, but it hardly seems worth the
	 * trouble.)  However, the single table could be buried in several levels
	 * of FromExpr due to subqueries.  Note the "single" table could be an
	 * inheritance parent, too, including the case of a UNION ALL subquery
	 * that's been flattened to an appendrel.
	 */
	jtnode = parse->jointree;
	while (IsA(jtnode, FromExpr))
	{
		if (list_length(jtnode->fromlist) != 1)
			return;
		jtnode = linitial(jtnode->fromlist);
	}
	if (!IsA(jtnode, RangeTblRef))
		return;
	rtr = (RangeTblRef *) jtnode;
	rte = planner_rt_fetch(rtr->rtindex, root);
	if (rte->rtekind == RTE_RELATION)
		 /* ordinary relation, ok */ ;
	else if (rte->rtekind == RTE_SUBQUERY && rte->inh)
		 /* flattened UNION ALL subquery, ok */ ;
	else
		return;

	/*
	 * Examine all the aggregates and verify all are MIN/MAX aggregates.  Stop
	 * as soon as we find one that isn't.
	 */
	aggs_list = NIL;
	if (!can_minmax_aggs(root, &aggs_list))
		return;

	/*
	 * OK, there is at least the possibility of performing the optimization.
	 * Build an access path for each aggregate.  If any of the aggregates
	 * prove to be non-indexable, give up; there is no point in optimizing
	 * just some of them.
	 */
	foreach(lc, aggs_list)
	{
		MinMaxAggInfo *mminfo = (MinMaxAggInfo *) lfirst(lc);
		Oid			eqop;
		bool		reverse;

		/*
		 * We'll need the equality operator that goes with the aggregate's
		 * ordering operator.
		 */
		eqop = get_equality_op_for_ordering_op(mminfo->aggsortop, &reverse);
		if (!OidIsValid(eqop))	/* shouldn't happen */
			elog(ERROR, "could not find equality operator for ordering operator %u",
				 mminfo->aggsortop);

		/*
		 * We can use either an ordering that gives NULLS FIRST or one that
		 * gives NULLS LAST; furthermore there's unlikely to be much
		 * performance difference between them, so it doesn't seem worth
		 * costing out both ways if we get a hit on the first one.  NULLS
		 * FIRST is more likely to be available if the operator is a
		 * reverse-sort operator, so try that first if reverse.
		 */
		if (build_minmax_path(root, mminfo, eqop, mminfo->aggsortop, reverse, reverse))
			continue;
		if (build_minmax_path(root, mminfo, eqop, mminfo->aggsortop, reverse, !reverse))
			continue;

		/* No indexable path for this aggregate, so fail */
		return;
	}

	/*
	 * OK, we can do the query this way.  Prepare to create a MinMaxAggPath
	 * node.
	 *
	 * First, create an output Param node for each agg.  (If we end up not
	 * using the MinMaxAggPath, we'll waste a PARAM_EXEC slot for each agg,
	 * which is not worth worrying about.  We can't wait till create_plan time
	 * to decide whether to make the Param, unfortunately.)
	 */
	foreach(lc, aggs_list)
	{
		MinMaxAggInfo *mminfo = (MinMaxAggInfo *) lfirst(lc);

		mminfo->param =
			SS_make_initplan_output_param(root,
										  exprType((Node *) mminfo->target),
										  -1,
										  exprCollation((Node *) mminfo->target));
	}

	/*
	 * Create a MinMaxAggPath node with the appropriate estimated costs and
	 * other needed data, and add it to the UPPERREL_GROUP_AGG upperrel, where
	 * it will compete against the standard aggregate implementation.  (It
	 * will likely always win, but we need not assume that here.)
	 *
	 * Note: grouping_planner won't have created this upperrel yet, but it's
	 * fine for us to create it first.  We will not have inserted the correct
	 * consider_parallel value in it, but MinMaxAggPath paths are currently
	 * never parallel-safe anyway, so that doesn't matter.  Likewise, it
	 * doesn't matter that we haven't filled FDW-related fields in the rel.
	 * Also, because there are no rowmarks, we know that the processed_tlist
	 * doesn't need to change anymore, so making the pathtarget now is safe.
	 */
	grouped_rel = fetch_upper_rel(root, UPPERREL_GROUP_AGG, NULL);
	add_path(grouped_rel, (Path *)
			 create_minmaxagg_path(root, grouped_rel,
								   create_pathtarget(root,
													 root->processed_tlist),
								   aggs_list,
								   (List *) parse->havingQual));
}

/*
 * can_minmax_aggs
 *		Examine all the aggregates in the query, and check if they are
 *		all MIN/MAX aggregates.  If so, build a list of MinMaxAggInfo
 *		nodes for them.
 *
 * Returns false if a non-MIN/MAX aggregate is found, true otherwise.
 */
/*
 * can_minmax_aggs - (中文)检查查询中所有聚合是否都是可优化的 MIN/MAX 聚合
 *
 * 【作用】遍历 root->agginfos(由 preprocess_aggrefs() 生成,每个 AggInfo
 * 对应一个聚合;被拉平的顶层聚合的 agglevelsup 均为 0),逐一检查是否满足
 * 可索引化条件;若全部满足,则把为每个聚合建立的 MinMaxAggInfo 节点追加到
 * *context 列表中并返回 true;一旦发现不满足的聚合立即返回 false。
 * 由 preprocess_minmax_aggregates() 调用。
 *
 * 【设计思想】本函数是"可行性预筛",逐个聚合检查如下条件:
 * - 参数个数必须为 1(否则不可能是 MIN/MAX);
 * - 不能带 ORDER BY(即聚合自身的排序):虽然 MIN/MAX 的 ORDER BY 通常无关
 *   紧要,但当排序算子对应的操作符类把"不相同但相等"的值视为相等时(如
 *   numeric_ops 下 4.0 与 4.00),ORDER BY 会改变 MIN 从若干相等值中挑选
 *   哪个;本优化用子查询路径不实现该语义,同时这个检查也能快速排除
 *   ordered-set 聚合;
 * - 不能带 FILTER(理想情况下可把 filter 加入子查询的 quals,当前暂不支持);
 * - 聚合必须有关联排序算子(fetch_agg_sort_op 返回非 InvalidOid),否则不是
 *   MIN/MAX 类;
 * - 目标表达式不能含易变函数(否则无法依赖索引,值在两次求值间可能变化),
 *   不能是行类型(否则 "IS NOT NULL" 语义怪异)。
 * 注意:参数若带 DISTINCT 不影响判断(注释明说不在意)。
 *
 * 【参数】
 *   root    —— PlannerInfo,取 root->agginfos 遍历;
 *   context —— 输出参数,成功时为全部 MinMaxAggInfo 组成的 List 追加位置
 *               (调用者传入的是 NIL)。
 * 【返回值】true:所有聚合均可优化,MinMaxAggInfo 列表已填入 *context;
 * false:存在不可优化的聚合,调用方应放弃本优化。
 */
static bool
can_minmax_aggs(PlannerInfo *root, List **context)
{
	ListCell   *lc;

	/*
	 * This function used to have to scan the query for itself, but now we can
	 * just thumb through the AggInfo list made by preprocess_aggrefs.
	 */
	foreach(lc, root->agginfos)
	{
		AggInfo    *agginfo = lfirst_node(AggInfo, lc);
		Aggref	   *aggref = linitial_node(Aggref, agginfo->aggrefs);
		Oid			aggsortop;
		TargetEntry *curTarget;
		MinMaxAggInfo *mminfo;

		Assert(aggref->agglevelsup == 0);
		if (list_length(aggref->args) != 1)
			return false;		/* it couldn't be MIN/MAX */

		/*
		 * ORDER BY is usually irrelevant for MIN/MAX, but it can change the
		 * outcome if the aggsortop's operator class recognizes non-identical
		 * values as equal.  For example, 4.0 and 4.00 are equal according to
		 * numeric_ops, yet distinguishable.  If MIN() receives more than one
		 * value equal to 4.0 and no value less than 4.0, it is unspecified
		 * which of those equal values MIN() returns.  An ORDER BY expression
		 * that differs for each of those equal values of the argument
		 * expression makes the result predictable once again.  This is a
		 * niche requirement, and we do not implement it with subquery paths.
		 * In any case, this test lets us reject ordered-set aggregates
		 * quickly.
		 */
		if (aggref->aggorder != NIL)
			return false;
		/* note: we do not care if DISTINCT is mentioned ... */

		/*
		 * We might implement the optimization when a FILTER clause is present
		 * by adding the filter to the quals of the generated subquery.  For
		 * now, just punt.
		 */
		if (aggref->aggfilter != NULL)
			return false;

		aggsortop = fetch_agg_sort_op(aggref->aggfnoid);
		if (!OidIsValid(aggsortop))
			return false;		/* not a MIN/MAX aggregate */

		curTarget = (TargetEntry *) linitial(aggref->args);

		if (contain_mutable_functions((Node *) curTarget->expr))
			return false;		/* not potentially indexable */

		if (type_is_rowtype(exprType((Node *) curTarget->expr)))
			return false;		/* IS NOT NULL would have weird semantics */

		mminfo = makeNode(MinMaxAggInfo);
		mminfo->aggfnoid = aggref->aggfnoid;
		mminfo->aggsortop = aggsortop;
		mminfo->target = curTarget->expr;
		mminfo->subroot = NULL; /* don't compute path yet */
		mminfo->path = NULL;
		mminfo->pathcost = 0;
		mminfo->param = NULL;

		*context = lappend(*context, mminfo);
	}
	return true;
}

/*
 * build_minmax_path
 *		Given a MIN/MAX aggregate, try to build an indexscan Path it can be
 *		optimized with.
 *
 * If successful, stash the best path in *mminfo and return true.
 * Otherwise, return false.
 */
/*
 * build_minmax_path - (中文)为单个 MIN/MAX 聚合构造可优化的索引扫描路径
 *
 * 【作用】给定一个 MIN/MAX 聚合,尝试构造它能利用的索引扫描路径:克隆当前
 * 查询层状态构造出形如
 *		(SELECT col FROM tab
 *		 WHERE col IS NOT NULL AND existing-quals
 *		 ORDER BY col ASC/DESC
 *		 LIMIT 1)
 * 的"子查询",递归调用 query_planner() 生成路径,再挑选按 query_pathkeys
 * 预排序且取首行最便宜(分数代价)的路径。成功则把最佳路径存入
 * *mminfo(subroot/path/pathcost)并返回 true,否则返回 false。
 * 由 preprocess_minmax_aggregates() 对每个聚合调用两次(两种 NULLS
 * 顺序)。
 *
 * 【设计思想】
 * - 子查询构造方式:直接 memcpy 一份 PlannerInfo,query_level 加一、
 *   parent_root 指向原 root、把 parse 复制并 IncrementVarSublevelsUp 使
 *   外层的 Var 变成上一级引用——这样最终子查询内不再有 level 1 的 Var,
 *   从而可以被当作 initplan 执行。同时清空 plan_params/outer_params/
 *   init_plans/agginfos 等子计划相关状态;
 * - 目标列表只有一个条目:聚合目标表达式(别名为 agg_target);HAVING、
 *   DISTINCT、hasAggs 全部清空;在 jointree->quals 前追加 "target IS
 *   NOT NULL"(若用户 WHERE 里已有同形表达式则通过 list_member 去重);
 *   构造 SortGroupClause 表达排序方向(reverse_sort/nulls_first),设置
 *   LIMIT 1(limitCount 为常量 1);
 * - 用 tuple_fraction = 1.0 和 limit_tuples = 1.0 告知 query_planner 只要
 *   取第一行,从而在代价估算时偏向索引扫描;
 * - 由于绕过了 subquery_planner,需手工补做其收尾工作:
 *   SS_identify_outer_params() 识别外层参数、SS_charge_for_initplans() 为
 *   子查询内的 initplan 计费;
 * - 分数代价计算方式(首行代价 = startup + fraction*(total - startup),
 *   fraction 取 1/rows)与 compare_fractional_path_costs() 保持一致,
 *   保证挑选路径的标准统一;
 * - apply_projection_to_path() 可能对挑选出的路径再加投影以对齐目标列,
 *   并假定这不改变"哪个路径最便宜"的结论。
 *
 * 【参数】
 *   root         —— 当前查询层的 PlannerInfo;
 *   mminfo       —— 待处理的聚合信息,函数会填充其 subroot/path/pathcost;
 *   eqop         —— 与排序算子配套的等值算子 OID;
 *   sortop       —— 聚合的排序算子 OID;
 *   reverse_sort —— true 表示按逆序排列(对应 MAX);
 *   nulls_first  —— true 表示 NULL 排在最前。
 * 【返回值】true:找到并缓存了最佳索引路径;false:该方向构造不出
 * 有序索引路径。
 */
static bool
build_minmax_path(PlannerInfo *root, MinMaxAggInfo *mminfo,
				  Oid eqop, Oid sortop, bool reverse_sort, bool nulls_first)
{
	PlannerInfo *subroot;
	Query	   *parse;
	TargetEntry *tle;
	List	   *tlist;
	NullTest   *ntest;
	SortGroupClause *sortcl;
	RelOptInfo *final_rel;
	Path	   *sorted_path;
	Cost		path_cost;
	double		path_fraction;

	/*
	 * We are going to construct what is effectively a sub-SELECT query, so
	 * clone the current query level's state and adjust it to make it look
	 * like a subquery.  Any outer references will now be one level higher
	 * than before.  (This means that when we are done, there will be no Vars
	 * of level 1, which is why the subquery can become an initplan.)
	 */
	subroot = palloc_object(PlannerInfo);
	memcpy(subroot, root, sizeof(PlannerInfo));
	subroot->query_level++;
	subroot->parent_root = root;
	subroot->plan_name = choose_plan_name(root->glob, "minmax", true);
	subroot->alternative_plan_name = root->plan_name;

	/* reset subplan-related stuff */
	subroot->plan_params = NIL;
	subroot->outer_params = NULL;
	subroot->init_plans = NIL;
	subroot->agginfos = NIL;
	subroot->aggtransinfos = NIL;

	subroot->parse = parse = copyObject(root->parse);
	IncrementVarSublevelsUp((Node *) parse, 1, 1);

	/* append_rel_list might contain outer Vars? */
	subroot->append_rel_list = copyObject(root->append_rel_list);
	IncrementVarSublevelsUp((Node *) subroot->append_rel_list, 1, 1);
	/* There shouldn't be any OJ info to translate, as yet */
	Assert(subroot->join_info_list == NIL);
	/* and we haven't made equivalence classes, either */
	Assert(subroot->eq_classes == NIL);
	/* and we haven't created PlaceHolderInfos, either */
	Assert(subroot->placeholder_list == NIL);

	/*----------
	 * Generate modified query of the form
	 *		(SELECT col FROM tab
	 *		 WHERE col IS NOT NULL AND existing-quals
	 *		 ORDER BY col ASC/DESC
	 *		 LIMIT 1)
	 *----------
	 */
	/* single tlist entry that is the aggregate target */
	tle = makeTargetEntry(copyObject(mminfo->target),
						  (AttrNumber) 1,
						  pstrdup("agg_target"),
						  false);
	tlist = list_make1(tle);
	subroot->processed_tlist = parse->targetList = tlist;

	/* No HAVING, no DISTINCT, no aggregates anymore */
	parse->havingQual = NULL;
	subroot->hasHavingQual = false;
	parse->distinctClause = NIL;
	parse->hasDistinctOn = false;
	parse->hasAggs = false;

	/* Build "target IS NOT NULL" expression */
	ntest = makeNode(NullTest);
	ntest->nulltesttype = IS_NOT_NULL;
	ntest->arg = copyObject(mminfo->target);
	/* we checked it wasn't a rowtype in can_minmax_aggs */
	ntest->argisrow = false;
	ntest->location = -1;

	/* User might have had that in WHERE already */
	if (!list_member((List *) parse->jointree->quals, ntest))
		parse->jointree->quals = (Node *)
			lcons(ntest, (List *) parse->jointree->quals);

	/* Build suitable ORDER BY clause */
	sortcl = makeNode(SortGroupClause);
	sortcl->tleSortGroupRef = assignSortGroupRef(tle, subroot->processed_tlist);
	sortcl->eqop = eqop;
	sortcl->sortop = sortop;
	sortcl->reverse_sort = reverse_sort;
	sortcl->nulls_first = nulls_first;
	sortcl->hashable = false;	/* no need to make this accurate */
	parse->sortClause = list_make1(sortcl);

	/* set up expressions for LIMIT 1 */
	parse->limitOffset = NULL;
	parse->limitCount = (Node *) makeConst(INT8OID, -1, InvalidOid,
										   sizeof(int64),
										   Int64GetDatum(1), false,
										   true);

	/*
	 * Generate the best paths for this query, telling query_planner that we
	 * have LIMIT 1.
	 */
	subroot->tuple_fraction = 1.0;
	subroot->limit_tuples = 1.0;

	final_rel = query_planner(subroot, minmax_qp_callback, NULL);

	/*
	 * Since we didn't go through subquery_planner() to handle the subquery,
	 * we have to do some of the same cleanup it would do, in particular cope
	 * with params and initplans used within this subquery.  (This won't
	 * matter if we end up not using the subplan.)
	 */
	SS_identify_outer_params(subroot);
	SS_charge_for_initplans(subroot, final_rel);

	/*
	 * Get the best presorted path, that being the one that's cheapest for
	 * fetching just one row.  If there's no such path, fail.
	 */
	if (final_rel->rows > 1.0)
		path_fraction = 1.0 / final_rel->rows;
	else
		path_fraction = 1.0;

	sorted_path =
		get_cheapest_fractional_path_for_pathkeys(final_rel->pathlist,
												  subroot->query_pathkeys,
												  NULL,
												  path_fraction);
	if (!sorted_path)
		return false;

	/*
	 * The path might not return exactly what we want, so fix that.  (We
	 * assume that this won't change any conclusions about which was the
	 * cheapest path.)
	 */
	sorted_path = apply_projection_to_path(subroot, final_rel, sorted_path,
										   create_pathtarget(subroot,
															 subroot->processed_tlist));

	/*
	 * Determine cost to get just the first row of the presorted path.
	 *
	 * Note: cost calculation here should match
	 * compare_fractional_path_costs().
	 */
	path_cost = sorted_path->startup_cost +
		path_fraction * (sorted_path->total_cost - sorted_path->startup_cost);

	/* Save state for further processing */
	mminfo->subroot = subroot;
	mminfo->path = sorted_path;
	mminfo->pathcost = path_cost;

	return true;
}

/*
 * Compute query_pathkeys and other pathkeys during query_planner()
 */
/*
 * minmax_qp_callback - (中文)克隆子查询在 query_planner 期间计算 pathkeys 的回调
 *
 * 【作用】作为 build_minmax_path() 中 query_planner() 调用的 qp_callback,
 * 在等价类合并完成后被回调,负责计算该克隆"子查询"的 sort_pathkeys 与
 * query_pathkeys。
 *
 * 【设计思想】被改写的子查询没有分组、窗口、DISTINCT,因此 group_pathkeys /
 * window_pathkeys / distinct_pathkeys 一律置为 NIL;唯一的排序来源就是
 * parse->sortClause(即 build_minmax_path 构造的 ORDER BY col ASC/DESC),故
 * sort_pathkeys 由 make_pathkeys_for_sortclauses() 生成并直接赋给
 * query_pathkeys。这样 query_planner 就会把按此顺序排序的路径(即索引扫描
 * 路径)作为目标。
 *
 * 【参数】
 *   root  —— 克隆子查询的 PlannerInfo,其 parse->sortClause/targetList 已被
 *             build_minmax_path() 改写;
 *   extra —— 未使用(NULL)。
 * 【返回值】void。
 */
static void
minmax_qp_callback(PlannerInfo *root, void *extra)
{
	root->group_pathkeys = NIL;
	root->window_pathkeys = NIL;
	root->distinct_pathkeys = NIL;

	root->sort_pathkeys =
		make_pathkeys_for_sortclauses(root,
									  root->parse->sortClause,
									  root->parse->targetList);

	root->query_pathkeys = root->sort_pathkeys;
}

/*
 * Get the OID of the sort operator, if any, associated with an aggregate.
 * Returns InvalidOid if there is no such operator.
 */
/*
 * fetch_agg_sort_op - (中文)获取聚合函数关联的排序算子 OID
 *
 * 【作用】根据聚合函数 OID 在系统目录 pg_aggregate 中查找其 aggsortop
 * (聚合的排序算子)。MIN/MAX 等聚合在定义时注册了排序算子(用于其排序
 * 语义);没有注册的(如 COUNT、SUM、AVG)说明不是 MIN/MAX 类,返回
 * InvalidOid。
 *
 * 【设计思想】简单的系统缓存查询:用 SearchSysCache1(AGGFNOID,...) 按
 * 聚合函数 OID 取元组,读到 Form_pg_aggregate 后取 aggsortop 字段,然后
 * ReleaseSysCache 释放缓存引用(返回值是拷贝的 OID,与缓存无关)。
 *
 * 【参数】
 *   aggfnoid —— 聚合函数的 OID。
 * 【返回值】关联的排序算子 OID;若该聚合没有排序算子(不是 MIN/MAX 类)
 * 则返回 InvalidOid。
 */
static Oid
fetch_agg_sort_op(Oid aggfnoid)
{
	HeapTuple	aggTuple;
	Form_pg_aggregate aggform;
	Oid			aggsortop;

	/* fetch aggregate entry from pg_aggregate */
	aggTuple = SearchSysCache1(AGGFNOID, ObjectIdGetDatum(aggfnoid));
	if (!HeapTupleIsValid(aggTuple))
		return InvalidOid;
	aggform = (Form_pg_aggregate) GETSTRUCT(aggTuple);
	aggsortop = aggform->aggsortop;
	ReleaseSysCache(aggTuple);

	return aggsortop;
}
