/*-------------------------------------------------------------------------
 *
 * joinpath.c
 *	  Routines to find all possible paths for processing a set of joins
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本模块(joinpath.c)负责为"给定的两个输入关系(outer/inner)"生成各种
 * 连接路径(JoinPath),是规划器自底向上构建连接计划的关键一环。它被
 * joinrels.c 的 populate_joinrel_with_paths() 调用,把生成好的路径加入
 * joinrel 的 pathlist / partial_pathlist(经由 add_path /
 * add_partial_path 的去劣后筛选)。
 *
 * 【职责】
 * - 对一对输入关系尝试四种主要连接方法:嵌套循环(NestLoop)、归并连接
 *   (MergeJoin)、哈希连接(HashJoin),以及(通过 FDW / hook)外部连接;
 * - 每种方法内再细分变体:普通/带物化(Materialize)/带 Memoize 的嵌套
 *   循环,需要显式排序的双边归并、外层已有序/内层已预排序的单边归并,
 *   以及并行(partial)版本;
 * - 评估参数化路径(parameterized path):决定哪些外层关系可以作为内层
 *   路径的参数来源(param_source_rels 启发式,以及星型模式
 *   allow_star_schema_join 特例);
 * - 为 semi/anti 连接计算代价修正因子(semifactors);
 * - 对外部表连接调用 FDW 的 GetForeignJoinPaths,并对扩展开放两个钩子
 *   (join_path_setup_hook、set_join_pathlist_hook)。
 *
 * 【设计思想】
 * 入口 add_paths_to_joinrel() 在收集齐"连接子句候选列表
 * (mergeclause_list)"后,依次调用:
 *   1. sort_inner_and_outer():双侧都显式排序的归并连接;
 *   2. match_unsorted_outer():外层免排序的嵌套循环 + 单边归并(外层
 *      已有序),并尝试物化/Memoize 内层;
 *   3. hash_inner_and_outer():哈希连接;
 *   4. FDW 连接下推与扩展钩子。
 * 每种路径在创建前先用 initial_cost_* 求代价下界,再经 add_path_precheck
 * 快速淘汰明显劣势者,最后才构造完整 Path 结构交给 add_path 做精确去劣。
 * 归并连接还利用 EquivalenceClass 机制(p 外部文件 pathkeys.c)把连接子句
 * 换算成规范排序键,从而枚举多种有意义的排序顺序。
 *
 * 【核心数据结构】JoinPathExtraData:在一次 add_paths_to_joinrel() 调用
 * 内传递 restrictlist、mergeclause_list、sjinfo、param_source_rels、
 * semifactors、inner_unique、pgs_mask 等上下文信息。
 *
 * 本文件与 joinrels.c(连接关系构建)、pathkeys.c(路径键)、costsize.c
 * (代价估算)以及 pathnode.c(Path 节点构造)紧密配合。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/path/joinpath.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "executor/executor.h"
#include "foreign/fdwapi.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/placeholder.h"
#include "optimizer/planmain.h"
#include "optimizer/restrictinfo.h"
#include "utils/lsyscache.h"
#include "utils/typcache.h"

/* Hooks for plugins to get control in add_paths_to_joinrel() */
set_join_pathlist_hook_type set_join_pathlist_hook = NULL;
join_path_setup_hook_type join_path_setup_hook = NULL;

/*
 * Paths parameterized by a parent rel can be considered to be parameterized
 * by any of its children, when we are performing partitionwise joins.  These
 * macros simplify checking for such cases.  Beware multiple eval of args.
 */
#define PATH_PARAM_BY_PARENT(path, rel)	\
	((path)->param_info && bms_overlap(PATH_REQ_OUTER(path),	\
									   (rel)->top_parent_relids))
#define PATH_PARAM_BY_REL_SELF(path, rel)  \
	((path)->param_info && bms_overlap(PATH_REQ_OUTER(path), (rel)->relids))

#define PATH_PARAM_BY_REL(path, rel)	\
	(PATH_PARAM_BY_REL_SELF(path, rel) || PATH_PARAM_BY_PARENT(path, rel))

static void try_partial_mergejoin_path(PlannerInfo *root,
									   RelOptInfo *joinrel,
									   Path *outer_path,
									   Path *inner_path,
									   List *pathkeys,
									   List *mergeclauses,
									   List *outersortkeys,
									   List *innersortkeys,
									   JoinType jointype,
									   JoinPathExtraData *extra);
static void sort_inner_and_outer(PlannerInfo *root, RelOptInfo *joinrel,
								 RelOptInfo *outerrel, RelOptInfo *innerrel,
								 JoinType jointype, JoinPathExtraData *extra);
static void match_unsorted_outer(PlannerInfo *root, RelOptInfo *joinrel,
								 RelOptInfo *outerrel, RelOptInfo *innerrel,
								 JoinType jointype, JoinPathExtraData *extra);
static void consider_parallel_nestloop(PlannerInfo *root,
									   RelOptInfo *joinrel,
									   RelOptInfo *outerrel,
									   RelOptInfo *innerrel,
									   JoinType jointype,
									   JoinPathExtraData *extra);
static void consider_parallel_mergejoin(PlannerInfo *root,
										RelOptInfo *joinrel,
										RelOptInfo *outerrel,
										RelOptInfo *innerrel,
										JoinType jointype,
										JoinPathExtraData *extra,
										Path *inner_cheapest_total);
static void hash_inner_and_outer(PlannerInfo *root, RelOptInfo *joinrel,
								 RelOptInfo *outerrel, RelOptInfo *innerrel,
								 JoinType jointype, JoinPathExtraData *extra);
static List *select_mergejoin_clauses(PlannerInfo *root,
									  RelOptInfo *joinrel,
									  RelOptInfo *outerrel,
									  RelOptInfo *innerrel,
									  List *restrictlist,
									  JoinType jointype,
									  bool *mergejoin_allowed);
static void generate_mergejoin_paths(PlannerInfo *root,
									 RelOptInfo *joinrel,
									 RelOptInfo *innerrel,
									 Path *outerpath,
									 JoinType jointype,
									 JoinPathExtraData *extra,
									 bool useallclauses,
									 Path *inner_cheapest_total,
									 List *merge_pathkeys,
									 bool is_partial);


/*
 * add_paths_to_joinrel
 *	  Given a join relation and two component rels from which it can be made,
 *	  consider all possible paths that use the two component rels as outer
 *	  and inner rel respectively.  Add these paths to the join rel's pathlist
 *	  if they survive comparison with other paths (and remove any existing
 *	  paths that are dominated by these paths).
 *
 * Modifies the pathlist field of the joinrel node to contain the best
 * paths found so far.
 *
 * jointype is not necessarily the same as sjinfo->jointype; it might be
 * "flipped around" if we are considering joining the rels in the opposite
 * direction from what's indicated in sjinfo.
 *
 * Also, this routine accepts the special JoinTypes JOIN_UNIQUE_OUTER and
 * JOIN_UNIQUE_INNER to indicate that the outer or inner relation has been
 * unique-ified and a regular inner join should then be applied.  These values
 * are not allowed to propagate outside this routine, however.  Path cost
 * estimation code, as well as match_unsorted_outer, may need to recognize that
 * it's dealing with such a case --- the combination of nominal jointype INNER
 * with sjinfo->jointype == JOIN_SEMI indicates that.
 */
/*
 * add_paths_to_joinrel - (中文)为给定一对输入关系生成并加入所有可行的连接路径
 *
 * 【作用】给定一个连接关系 joinrel 及其两个组成部分 outerrel、innerrel,
 * 考虑所有把二者分别作为外/内关系使用的连接路径,把存活下来的路径加入
 * joinrel 的 pathlist(同时剔除被支配的旧路径)。这是 joinpath.c 的顶层
 * 入口,由 joinrels.c 的 populate_joinrel_with_paths() 为每个可行的
 * (rel1, rel2) 顺序调用一次。它修改 joinrel->pathlist。
 *
 * 【设计思想】
 * - 先把上下文打包进 JoinPathExtraData extra,随后各生成子过程都读它;
 * - 调 join_path_setup_hook 让扩展可改 pgs_mask/其它字段(此后一律用
 *   extra.pgs_mask 而非 rel->pgs_mask);
 * - 用 innerrel_is_unique() 证明内层对当前外层的唯一性(JOIN_SEMI/
 *   UNIQUE_* 有专门分支),结果放入 extra.inner_unique,供 Memoize 及
 *   半连接代价修正使用;
 * - JOIN_UNIQUE_OUTER/INNER 会被规约为普通内连接(jointype 改 JOIN_INNER),
 *   但其语义通过 sjinfo->jointype == JOIN_SEMI 传达给代价估算;
 * - 若启用归并连接(或 FULL 连接——归并连接是 FULL 的唯一实现),调用
 *   select_mergejoin_clauses() 收集可归并子句;
 * - semi/anti/inner_unique 时计算半连接代价修正因子;
 * - 按"外层连接约束"推导 param_source_rels:与某个 SpecialJoinInfo 的
 *   RHS 部分重叠、但尚未并入其 LHS 时,该 SJ 之外的所有基表都可能成为
 *   参数来源,据此过滤参数化路径的数量;随后并入 LATERAL 剩余依赖
 *   (joinrel->lateral_relids);
 * - 依序调用 sort_inner_and_outer()、match_unsorted_outer()、
 *   hash_inner_and_outer(),最后是 FDW 的 GetForeignJoinPaths 与
 *   set_join_pathlist_hook。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   joinrel     —— 目标连接关系(路径加入其 pathlist);
 *   outerrel    —— 外部输入关系;
 *   innerrel    —— 内部输入关系;
 *   jointype    —— 本次连接类型(可能与 sjinfo->jointype 不同,例如把
 *                  输入翻转后的变体);
 *   sjinfo      —— 连接上下文(SpecialJoinInfo);
 *   restrictlist —— 应用于本次连接的限制/连接子句列表。
 * 【返回值】无。
 */
void
add_paths_to_joinrel(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 SpecialJoinInfo *sjinfo,
					 List *restrictlist)
{
	JoinType	save_jointype = jointype;
	JoinPathExtraData extra;
	bool		mergejoin_allowed = true;
	ListCell   *lc;
	Relids		joinrelids;

	/*
	 * PlannerInfo doesn't contain the SpecialJoinInfos created for joins
	 * between child relations, even if there is a SpecialJoinInfo node for
	 * the join between the topmost parents. So, while calculating Relids set
	 * representing the restriction, consider relids of topmost parent of
	 * partitions.
	 */
	if (joinrel->reloptkind == RELOPT_OTHER_JOINREL)
		joinrelids = joinrel->top_parent_relids;
	else
		joinrelids = joinrel->relids;

	extra.restrictlist = restrictlist;
	extra.mergeclause_list = NIL;
	extra.sjinfo = sjinfo;
	extra.param_source_rels = NULL;
	extra.pgs_mask = joinrel->pgs_mask;

	/*
	 * Give extensions a chance to take control. In particular, an extension
	 * might want to modify extra.pgs_mask. It's possible to override pgs_mask
	 * on a query-wide basis using join_search_hook, or for a particular
	 * relation using joinrel_setup_hook, but extensions that want to provide
	 * different advice for the same joinrel based on the choice of innerrel
	 * and outerrel will need to use this hook.
	 *
	 * A very simple way for an extension to use this hook is to set
	 * extra.pgs_mask &= ~PGS_JOIN_ANY, if it simply doesn't want any of the
	 * paths generated by this call to add_paths_to_joinrel() to be selected.
	 * An extension could use this technique to constrain the join order,
	 * since it could thereby arrange to reject all paths from join orders
	 * that it does not like. An extension can also selectively clear bits
	 * from extra.pgs_mask to rule out specific techniques for specific joins,
	 * or could even set additional bits to re-allow methods disabled at some
	 * higher level.
	 *
	 * NB: Below this point, this function should be careful to reference
	 * extra.pgs_mask rather than rel->pgs_mask to avoid disregarding any
	 * changes made by the hook we're about to call.
	 */
	if (join_path_setup_hook)
		join_path_setup_hook(root, joinrel, outerrel, innerrel,
							 jointype, &extra);

	/*
	 * See if the inner relation is provably unique for this outer rel.
	 *
	 * We have some special cases: for JOIN_SEMI, it doesn't matter since the
	 * executor can make the equivalent optimization anyway.  It also doesn't
	 * help enable use of Memoize, since a semijoin with a provably unique
	 * inner side should have been reduced to an inner join in that case.
	 * Therefore, we need not expend planner cycles on proofs.  (For
	 * JOIN_ANTI, although it doesn't help the executor for the same reason,
	 * it can benefit Memoize paths.)  For JOIN_UNIQUE_INNER, we must be
	 * considering a semijoin whose inner side is not provably unique (else
	 * reduce_unique_semijoins would've simplified it), so there's no point in
	 * calling innerrel_is_unique.  However, if the LHS covers all of the
	 * semijoin's min_lefthand, then it's appropriate to set inner_unique
	 * because the unique relation produced by create_unique_paths will be
	 * unique relative to the LHS.  (If we have an LHS that's only part of the
	 * min_lefthand, that is *not* true.)  For JOIN_UNIQUE_OUTER, pass
	 * JOIN_INNER to avoid letting that value escape this module.
	 */
	switch (jointype)
	{
		case JOIN_SEMI:
			extra.inner_unique = false; /* well, unproven */
			break;
		case JOIN_UNIQUE_INNER:
			extra.inner_unique = bms_is_subset(sjinfo->min_lefthand,
											   outerrel->relids);
			break;
		case JOIN_UNIQUE_OUTER:
			extra.inner_unique = innerrel_is_unique(root,
													joinrel->relids,
													outerrel->relids,
													innerrel,
													JOIN_INNER,
													restrictlist,
													false);
			break;
		default:
			extra.inner_unique = innerrel_is_unique(root,
													joinrel->relids,
													outerrel->relids,
													innerrel,
													jointype,
													restrictlist,
													false);
			break;
	}

	/*
	 * If the outer or inner relation has been unique-ified, handle as a plain
	 * inner join.
	 */
	if (jointype == JOIN_UNIQUE_OUTER || jointype == JOIN_UNIQUE_INNER)
		jointype = JOIN_INNER;

	/*
	 * Find potential mergejoin clauses.  We can skip this if we are not
	 * interested in doing a mergejoin.  However, mergejoin may be our only
	 * way of implementing a full outer join, so in that case we don't care
	 * whether mergejoins are disabled.
	 */
	if ((extra.pgs_mask & PGS_MERGEJOIN_ANY) != 0 || jointype == JOIN_FULL)
		extra.mergeclause_list = select_mergejoin_clauses(root,
														  joinrel,
														  outerrel,
														  innerrel,
														  restrictlist,
														  jointype,
														  &mergejoin_allowed);

	/*
	 * If it's SEMI, ANTI, or inner_unique join, compute correction factors
	 * for cost estimation.  These will be the same for all paths.
	 */
	if (jointype == JOIN_SEMI || jointype == JOIN_ANTI || extra.inner_unique)
		compute_semi_anti_join_factors(root, joinrel, outerrel, innerrel,
									   jointype, sjinfo, restrictlist,
									   &extra.semifactors);

	/*
	 * Decide whether it's sensible to generate parameterized paths for this
	 * joinrel, and if so, which relations such paths should require.  There
	 * is usually no need to create a parameterized result path unless there
	 * is a join order restriction that prevents joining one of our input rels
	 * directly to the parameter source rel instead of joining to the other
	 * input rel.  (But see allow_star_schema_join().)	This restriction
	 * reduces the number of parameterized paths we have to deal with at
	 * higher join levels, without compromising the quality of the resulting
	 * plan.  We express the restriction as a Relids set that must overlap the
	 * parameterization of any proposed join path.  Note: param_source_rels
	 * should contain only baserels, not OJ relids, so starting from
	 * all_baserels not all_query_rels is correct.
	 */
	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo2 = (SpecialJoinInfo *) lfirst(lc);

		/*
		 * SJ is relevant to this join if we have some part of its RHS
		 * (possibly not all of it), and haven't yet joined to its LHS.  (This
		 * test is pretty simplistic, but should be sufficient considering the
		 * join has already been proven legal.)  If the SJ is relevant, it
		 * presents constraints for joining to anything not in its RHS.
		 */
		if (bms_overlap(joinrelids, sjinfo2->min_righthand) &&
			!bms_overlap(joinrelids, sjinfo2->min_lefthand))
			extra.param_source_rels = bms_join(extra.param_source_rels,
											   bms_difference(root->all_baserels,
															  sjinfo2->min_righthand));

		/* full joins constrain both sides symmetrically */
		if (sjinfo2->jointype == JOIN_FULL &&
			bms_overlap(joinrelids, sjinfo2->min_lefthand) &&
			!bms_overlap(joinrelids, sjinfo2->min_righthand))
			extra.param_source_rels = bms_join(extra.param_source_rels,
											   bms_difference(root->all_baserels,
															  sjinfo2->min_lefthand));
	}

	/*
	 * However, when a LATERAL subquery is involved, there will simply not be
	 * any paths for the joinrel that aren't parameterized by whatever the
	 * subquery is parameterized by, unless its parameterization is resolved
	 * within the joinrel.  So we might as well allow additional dependencies
	 * on whatever residual lateral dependencies the joinrel will have.
	 */
	extra.param_source_rels = bms_add_members(extra.param_source_rels,
											  joinrel->lateral_relids);

	/*
	 * 1. Consider mergejoin paths where both relations must be explicitly
	 * sorted.  Skip this if we can't mergejoin.
	 */
	if (mergejoin_allowed)
		sort_inner_and_outer(root, joinrel, outerrel, innerrel,
							 jointype, &extra);

	/*
	 * 2. Consider paths where the outer relation need not be explicitly
	 * sorted. This includes both nestloops and mergejoins where the outer
	 * path is already ordered.  Again, skip this if we can't mergejoin.
	 * (That's okay because we know that nestloop can't handle
	 * right/right-anti/right-semi/full joins at all, so it wouldn't work in
	 * the prohibited cases either.)
	 */
	if (mergejoin_allowed)
		match_unsorted_outer(root, joinrel, outerrel, innerrel,
							 jointype, &extra);

#ifdef NOT_USED

	/*
	 * 3. Consider paths where the inner relation need not be explicitly
	 * sorted.  This includes mergejoins only (nestloops were already built in
	 * match_unsorted_outer).
	 *
	 * Diked out as redundant 2/13/2000 -- tgl.  There isn't any really
	 * significant difference between the inner and outer side of a mergejoin,
	 * so match_unsorted_inner creates no paths that aren't equivalent to
	 * those made by match_unsorted_outer when add_paths_to_joinrel() is
	 * invoked with the two rels given in the other order.
	 */
	if (mergejoin_allowed)
		match_unsorted_inner(root, joinrel, outerrel, innerrel,
							 jointype, &extra);
#endif

	/*
	 * 4. Consider paths where both outer and inner relations must be hashed
	 * before being joined.  As above, when it's a full join, we must try this
	 * even when the path type is disabled, because it may be our only option.
	 */
	if ((extra.pgs_mask & PGS_HASHJOIN) != 0 || jointype == JOIN_FULL)
		hash_inner_and_outer(root, joinrel, outerrel, innerrel,
							 jointype, &extra);

	/*
	 * 5. If inner and outer relations are foreign tables (or joins) belonging
	 * to the same server and assigned to the same user to check access
	 * permissions as, give the FDW a chance to push down joins.
	 */
	if ((extra.pgs_mask & PGS_FOREIGNJOIN) != 0 && joinrel->fdwroutine &&
		joinrel->fdwroutine->GetForeignJoinPaths)
		joinrel->fdwroutine->GetForeignJoinPaths(root, joinrel,
												 outerrel, innerrel,
												 save_jointype, &extra);

	/*
	 * 6. Finally, give extensions a chance to manipulate the path list.  They
	 * could add new paths (such as CustomPaths) by calling add_path(), or
	 * add_partial_path() if parallel aware.
	 *
	 * In theory, extensions could also use this hook to delete or modify
	 * paths added by the core code, but in practice this is difficult to make
	 * work, since it's too late to get back any paths that have already been
	 * discarded by add_path() or add_partial_path(). If you're trying to
	 * suppress paths, consider using join_path_setup_hook instead.
	 */
	if (set_join_pathlist_hook)
		set_join_pathlist_hook(root, joinrel, outerrel, innerrel,
							   save_jointype, &extra);
}

/*
 * We override the param_source_rels heuristic to accept nestloop paths in
 * which the outer rel satisfies some but not all of the inner path's
 * parameterization.  This is necessary to get good plans for star-schema
 * scenarios, in which a parameterized path for a large table may require
 * parameters from multiple small tables that will not get joined directly to
 * each other.  We can handle that by stacking nestloops that have the small
 * tables on the outside; but this breaks the rule the param_source_rels
 * heuristic is based on, namely that parameters should not be passed down
 * across joins unless there's a join-order-constraint-based reason to do so.
 * So we ignore the param_source_rels restriction when this case applies.
 *
 * allow_star_schema_join() returns true if the param_source_rels restriction
 * should be overridden, ie, it's okay to perform this join.
 */
/*
 * allow_star_schema_join - (中文)判断是否允许"星型模式"连接,从而放宽
 * param_source_rels 的启发式限制
 *
 * 【作用】try_nestloop_path() 在发现连接路径仍带参数化、且该参数来源不在
 * param_source_rels 中时调用本函数,判断是否放行该连接。返回 true 表示
 * 可以忽略 param_source_rels 的限制,继续构造该嵌套循环路径。
 *
 * 【设计思想】星型模式场景:大表(事实表)的参数化路径可能同时依赖多个小表
 * (维表),而这些小表彼此之间并不直接连接。此时可以把小表叠放在外层,通过
 * 嵌套循环逐层向内提供参数。这打破了 param_source_rels 启发式所依据的规则
 * ("除非有连接顺序约束,否则不应跨连接下传参数")。判断条件是:外层关系
 * 提供了内层参数化的一部分(inner_paramrels 与 outerrelids 有交集),但又
 * 不是全部(bms_nonempty_difference 要求存在未被满足的部分)——即"部分满足
 * 参数化"。全部满足时不需要 override,完全未满足时叠放无意义。
 *
 * 【参数】
 *   root           —— PlannerInfo;
 *   outerrelids    —— 外层关系的 relids;
 *   inner_paramrels —— 内层路径所要求的外层参数来源集合。
 * 【返回值】true:允许执行本次连接(忽略 param_source_rels 限制);
 * false:参数化不合理,应拒绝该路径。
 */
static inline bool
allow_star_schema_join(PlannerInfo *root,
					   Relids outerrelids,
					   Relids inner_paramrels)
{
	/*
	 * It's a star-schema case if the outer rel provides some but not all of
	 * the inner rel's parameterization.
	 */
	return (bms_overlap(inner_paramrels, outerrelids) &&
			bms_nonempty_difference(inner_paramrels, outerrelids));
}

/*
 * If the parameterization is only partly satisfied by the outer rel,
 * the unsatisfied part can't include any outer-join relids that could
 * null rels of the satisfied part.  That would imply that we're trying
 * to use a clause involving a Var with nonempty varnullingrels at
 * a join level where that value isn't yet computable.
 *
 * In practice, this test never finds a problem because earlier join order
 * restrictions prevent us from attempting a join that would cause a problem.
 * (That's unsurprising, because the code worked before we ever added
 * outer-join relids to expression relids.)  It still seems worth checking
 * as a backstop, but we only do so in assert-enabled builds.
 */
#ifdef USE_ASSERT_CHECKING
/*
 * have_unsafe_outer_join_ref - (中文)检查被外层关系部分满足的参数化中,
 * 未满足部分是否包含会对已满足部分产生 NULL 化的外层连接
 *
 * 【作用】仅用于 assert 构建(USE_ASSERT_CHECKING)的安全兜底检查:
 * 当星型模式连接中,内层路径的参数化只被外层关系部分满足时,未满足的部分
 * 不能包含"会把已满足部分的关系置 NULL 的外层连接 relid"。因为那意味着在
 * 某个连接层,某个 Var 带非空 varnullingrels,但其对应的值此刻还无法计算。
 *
 * 【设计思想】把 inner_paramrels 拆成"已满足(satisfied)"与"未满足
 * (unsatisfied)"两部分;若 unsatisfied 中确实含外层连接 relid
 * (root->outer_join_rels),则逐条扫描 join_info_list,凡该外层连接的 RHS
 * (或 FULL 连接的 LHS)与 satisfied 有交集,就说明已满足部分会被它 NULL 化,
 * 判断为不安全。源码注释说明:实际中由于更早的连接顺序限制,此检查通常
 * 不会发现任何问题,只是作为最后一道防线,所以仅放在 assert 构建里。
 *
 * 【参数】
 *   root           —— PlannerInfo;
 *   outerrelids    —— 外层关系的 relids;
 *   inner_paramrels —— 内层路径要求的参数来源集合。
 * 【返回值】true:存在不安全的引用,该路径不能采用;false:安全。
 * 注意本函数内部会释放临时构建的 bms 集合,失败路径不泄漏内存。
 */
static inline bool
have_unsafe_outer_join_ref(PlannerInfo *root,
						   Relids outerrelids,
						   Relids inner_paramrels)
{
	bool		result = false;
	Relids		unsatisfied = bms_difference(inner_paramrels, outerrelids);
	Relids		satisfied = bms_intersect(inner_paramrels, outerrelids);

	if (bms_overlap(unsatisfied, root->outer_join_rels))
	{
		ListCell   *lc;

		foreach(lc, root->join_info_list)
		{
			SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(lc);

			if (!bms_is_member(sjinfo->ojrelid, unsatisfied))
				continue;		/* not relevant */
			if (bms_overlap(satisfied, sjinfo->min_righthand) ||
				(sjinfo->jointype == JOIN_FULL &&
				 bms_overlap(satisfied, sjinfo->min_lefthand)))
			{
				result = true;	/* doesn't work */
				break;
			}
		}
	}

	/* Waste no memory when we reject a path here */
	bms_free(unsatisfied);
	bms_free(satisfied);

	return result;
}
#endif							/* USE_ASSERT_CHECKING */

/*
 * paraminfo_get_equal_hashops
 *		Determine if the clauses in param_info and innerrel's lateral vars
 *		can be hashed.
 *		Returns true if hashing is possible, otherwise false.
 *
 * Additionally, on success we collect the outer expressions and the
 * appropriate equality operators for each hashable parameter to innerrel.
 * These are returned in parallel lists in *param_exprs and *operators.
 * We also set *binary_mode to indicate whether strict binary matching is
 * required.
 */
/*
 * paraminfo_get_equal_hashops - (中文)判断内层路径的参数化子句与 LATERAL
 * 变量能否作为 Memoize 缓存键,并收集哈希运算符
 *
 * 【作用】get_memoize_path() 的辅助函数:检查 param_info 中的参数化连接子句
 * (ppi_clauses)以及 innerrel 的 LATERAL 变量,是否都能用哈希等值算子来
 * 构造缓存键。成功时把各"外层表达式 + 对应哈希等值算子"分别填入
 * *param_exprs 与 *operators(并行列表),并用 *binary_mode 表示是否需要
 * 按二进制严格比较。失败返回 false。
 *
 * 【设计思想】
 * - 每个 ppi_clauses 中的 RestrictInfo 必须是"outer op inner"或反之的
 *   两目 OpExpr(clause_sides_match_join),否则无法确定哪一侧是外层表达式;
 * - 取对应当前外层一侧(left_hasheqoperator / right_hasheqoperator)的哈希
 *   等值算子;若无效则不能哈希,失败;
 * - 若该连接算子本身不可哈希(rinfo->hashjoinoperator 无效),说明哈希等值
 *   算子可能把两个不同的值判为相等(例如浮点的 +0.0 与 -0.0),必须置
 *   *binary_mode = true,让 Memoize 做逐位比较而不是"逻辑"比较;
 * - LATERAL 变量一律加入缓存键:含 volatile 函数则失败;类型必须同时有
 *   哈希过程与等值算子;由于不了解这些 Var 的用途,一律要求二进制模式;
 * - 用 list_member() 去重:同一表达式已在 ppi_clauses 中出现时不重复加入,
 *   但若属上述需要二进制模式的情形,仍会切换模式。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   param_info    —— 内层路径的参数化信息(可能为 NULL);
 *   outerrel      —— 外层关系(可能用到其 top_parent 以便匹配 relids);
 *   innerrel      —— 内层关系(取 innerrel->lateral_vars);
 *   ph_lateral_vars —— 由 extract_lateral_vars_from_PHVs() 提取的、需在内层
 *                      求值的 PlaceHolderVar 中的横向引用列表;
 *   param_exprs   —— 出参:外层表达式列表;
 *   operators     —— 出参:与 param_exprs 一一对应的哈希等值算子;
 *   binary_mode   —— 出参:true 表示 Memoize 需二进制严格比较。
 * 【返回值】true:所有参数都可哈希,出参有效;false:存在不可哈希的参数,
 * 此时已释放部分累积的列表,出参不可用。
 */
static bool
paraminfo_get_equal_hashops(PlannerInfo *root, ParamPathInfo *param_info,
							RelOptInfo *outerrel, RelOptInfo *innerrel,
							List *ph_lateral_vars, List **param_exprs,
							List **operators, bool *binary_mode)

{
	List	   *lateral_vars;
	ListCell   *lc;

	*param_exprs = NIL;
	*operators = NIL;
	*binary_mode = false;

	/* Add join clauses from param_info to the hash key */
	if (param_info != NULL)
	{
		List	   *clauses = param_info->ppi_clauses;

		foreach(lc, clauses)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
			OpExpr	   *opexpr;
			Node	   *expr;
			Oid			hasheqoperator;

			opexpr = (OpExpr *) rinfo->clause;

			/*
			 * Bail if the rinfo is not compatible.  We need a join OpExpr
			 * with 2 args.
			 */
			if (!IsA(opexpr, OpExpr) || list_length(opexpr->args) != 2 ||
				!clause_sides_match_join(rinfo, outerrel->relids,
										 innerrel->relids))
			{
				list_free(*operators);
				list_free(*param_exprs);
				return false;
			}

			if (rinfo->outer_is_left)
			{
				expr = (Node *) linitial(opexpr->args);
				hasheqoperator = rinfo->left_hasheqoperator;
			}
			else
			{
				expr = (Node *) lsecond(opexpr->args);
				hasheqoperator = rinfo->right_hasheqoperator;
			}

			/* can't do memoize if we can't hash the outer type */
			if (!OidIsValid(hasheqoperator))
			{
				list_free(*operators);
				list_free(*param_exprs);
				return false;
			}

			/*
			 * 'expr' may already exist as a parameter from a previous item in
			 * ppi_clauses.  No need to include it again, however we'd better
			 * ensure we do switch into binary mode if required.  See below.
			 */
			if (!list_member(*param_exprs, expr))
			{
				*operators = lappend_oid(*operators, hasheqoperator);
				*param_exprs = lappend(*param_exprs, expr);
			}

			/*
			 * When the join operator is not hashable then it's possible that
			 * the operator will be able to distinguish something that the
			 * hash equality operator could not. For example with floating
			 * point types -0.0 and +0.0 are classed as equal by the hash
			 * function and equality function, but some other operator may be
			 * able to tell those values apart.  This means that we must put
			 * memoize into binary comparison mode so that it does bit-by-bit
			 * comparisons rather than a "logical" comparison as it would
			 * using the hash equality operator.
			 */
			if (!OidIsValid(rinfo->hashjoinoperator))
				*binary_mode = true;
		}
	}

	/* Now add any lateral vars to the cache key too */
	lateral_vars = list_concat(ph_lateral_vars, innerrel->lateral_vars);
	foreach(lc, lateral_vars)
	{
		Node	   *expr = (Node *) lfirst(lc);
		TypeCacheEntry *typentry;

		/* Reject if there are any volatile functions in lateral vars */
		if (contain_volatile_functions(expr))
		{
			list_free(*operators);
			list_free(*param_exprs);
			return false;
		}

		typentry = lookup_type_cache(exprType(expr),
									 TYPECACHE_HASH_PROC | TYPECACHE_EQ_OPR);

		/* can't use memoize without a valid hash proc and equals operator */
		if (!OidIsValid(typentry->hash_proc) || !OidIsValid(typentry->eq_opr))
		{
			list_free(*operators);
			list_free(*param_exprs);
			return false;
		}

		/*
		 * 'expr' may already exist as a parameter from the ppi_clauses.  No
		 * need to include it again, however we'd better ensure we do switch
		 * into binary mode.
		 */
		if (!list_member(*param_exprs, expr))
		{
			*operators = lappend_oid(*operators, typentry->eq_opr);
			*param_exprs = lappend(*param_exprs, expr);
		}

		/*
		 * We must go into binary mode as we don't have too much of an idea of
		 * how these lateral Vars are being used.  See comment above when we
		 * set *binary_mode for the non-lateral Var case. This could be
		 * relaxed a bit if we had the RestrictInfos and knew the operators
		 * being used, however for cases like Vars that are arguments to
		 * functions we must operate in binary mode as we don't have
		 * visibility into what the function is doing with the Vars.
		 */
		*binary_mode = true;
	}

	/* We're okay to use memoize */
	return true;
}

/*
 * extract_lateral_vars_from_PHVs
 *	  Extract lateral references within PlaceHolderVars that are due to be
 *	  evaluated at 'innerrelids'.
 */
/*
 * extract_lateral_vars_from_PHVs - (中文)提取计划在内层关系处求值的
 * PlaceHolderVar 中所含的横向引用,作为 Memoize 的候选缓存键
 *
 * 【作用】get_memoize_path() 的辅助函数:遍历 root->placeholder_list,找出
 * 所有"应在本连接的内层关系(innerrelids)处求值"且含横向引用(ph_lateral
 * 非空)的 PlaceHolderVar,把其中引用的 Var / PlaceHolderVar 提取出来返回,
 * 供 get_memoize_path() 用作缓存键的一部分。
 *
 * 【设计思想】
 * - 快速路径:查询无 LATERAL RTE 或 innerrelids 是多个关系(BMS_MULTIPLE,
 *   即内层是 joinrel)时直接返回 NIL——因为 Memoize 不会加在 joinrel 路径
 *   之上,joinrel 也维护不了缓存键;
 * - 对每个满足条件的 PHInfo:若其表达式根本不引用 innerrelids 中的关系
 *   (只由外层关系构成),则直接把这个表达式整体作为键,好处是某些场景下
 *   表达式的不同值更少、缓存命中率更高;否则把 phexpr 中 level 0 的 Var
 *   和 PlaceHolderVar 逐一提出来(pull_vars_of_level),仅保留确实属于
 *   ph_lateral(横向引用集)的部分;
 * - 提取嵌套 PHV 时要求其求值点 ph_eval_at 是 ph_lateral 的子集,保证它
 *   在横向上下文中可计算。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   innerrelids —— 期望求值位置(通常为内层关系的 relids)。
 * 【返回值】横向引用(Var/PlaceHolderVar/表达式)的列表;无相关内容时返回
 * NIL。列表元素由调用者负责按需使用。
 */
static List *
extract_lateral_vars_from_PHVs(PlannerInfo *root, Relids innerrelids)
{
	List	   *ph_lateral_vars = NIL;
	ListCell   *lc;

	/* Nothing would be found if the query contains no LATERAL RTEs */
	if (!root->hasLateralRTEs)
		return NIL;

	/*
	 * No need to consider PHVs that are due to be evaluated at joinrels,
	 * since we do not add Memoize nodes on top of joinrel paths.
	 */
	if (bms_membership(innerrelids) == BMS_MULTIPLE)
		return NIL;

	foreach(lc, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(lc);
		List	   *vars;
		ListCell   *cell;

		/* PHV is uninteresting if no lateral refs */
		if (phinfo->ph_lateral == NULL)
			continue;

		/* PHV is uninteresting if not due to be evaluated at innerrelids */
		if (!bms_equal(phinfo->ph_eval_at, innerrelids))
			continue;

		/*
		 * If the PHV does not reference any rels in innerrelids, use its
		 * contained expression as a cache key rather than extracting the
		 * Vars/PHVs from it and using those.  This can be beneficial in cases
		 * where the expression results in fewer distinct values to cache
		 * tuples for.
		 */
		if (!bms_overlap(pull_varnos(root, (Node *) phinfo->ph_var->phexpr),
						 innerrelids))
		{
			ph_lateral_vars = lappend(ph_lateral_vars, phinfo->ph_var->phexpr);
			continue;
		}

		/* Fetch Vars and PHVs of lateral references within PlaceHolderVars */
		vars = pull_vars_of_level((Node *) phinfo->ph_var->phexpr, 0);
		foreach(cell, vars)
		{
			Node	   *node = (Node *) lfirst(cell);

			if (IsA(node, Var))
			{
				Var		   *var = (Var *) node;

				Assert(var->varlevelsup == 0);

				if (bms_is_member(var->varno, phinfo->ph_lateral))
					ph_lateral_vars = lappend(ph_lateral_vars, node);
			}
			else if (IsA(node, PlaceHolderVar))
			{
				PlaceHolderVar *phv = (PlaceHolderVar *) node;

				Assert(phv->phlevelsup == 0);

				if (bms_is_subset(find_placeholder_info(root, phv)->ph_eval_at,
								  phinfo->ph_lateral))
					ph_lateral_vars = lappend(ph_lateral_vars, node);
			}
			else
				Assert(false);
		}

		list_free(vars);
	}

	return ph_lateral_vars;
}

/*
 * get_memoize_path
 *		If possible, make and return a Memoize path atop of 'inner_path'.
 *		Otherwise return NULL.
 *
 * Note that currently we do not add Memoize nodes on top of join relation
 * paths.  This is because the ParamPathInfos for join relation paths do not
 * maintain ppi_clauses, as the set of relevant clauses varies depending on how
 * the join is formed.  In addition, joinrels do not maintain lateral_vars.  So
 * we do not have a way to extract cache keys from joinrels.
 */
/*
 * get_memoize_path - (中文)尽可能在内层路径之上构造 Memoize 路径并返回,
 * 否则返回 NULL
 *
 * 【作用】match_unsorted_outer() / consider_parallel_nestloop() 在尝试普通
 * 嵌套循环路径的同时,调用本函数尝试把内层路径包一层 Memoize(缓存内层按
 * 参数取值扫描的结果),若可行则返回新路径,再交给 try_nestloop_path /
 * try_partial_nestloop_path 与普通版本比较代价。
 *
 * 【设计思想】Memoize 能避免"同一个内层参数值被重复扫描",但有多项前提:
 * - pgs_mask 必须允许 Memoize(PGS_NESTLOOP_MEMOIZE);通常还要求外层至少
 *   有 2 行(否则第一次扫描必是 cache miss,白费功夫),除非纯嵌套循环被
 *   禁用时才冒险交给代价比较;
 * - 必须存在缓存键:内层路径的参数化子句(ppi_clauses)、innerrel 的
 *   LATERAL 变量、或从 PHV 提取的横向引用,三者至少其一;
 * - SEMI/ANTI 连接中,嵌套循环可能不会把内层扫完(命中即跳),Memoize 无法
 *   把缓存项标记为"完整",所以一般禁止;例外是内层已证明唯一
 *   (extra->inner_unique)且整个连接条件都被参数化覆盖时,可在取到第一行后
 *   标记完整;
 * - 内层目标表、baserestrictinfo、参数化子句中都不能有 volatile 函数
 *   (缓存命中会减少这些函数的调用次数,改变语义);
 * - 所有参数都须可哈希(paraminfo_get_equal_hashops),并据此决定是否进入
 *   二进制比较模式。
 * 构造时用 create_memoize_path(),并传入 outer_path->rows 作为预估的单组
 * 行数,用于代价估算。
 *
 * 【参数】
 *   root       —— PlannerInfo;
 *   innerrel   —— 内层关系;
 *   outerrel   —— 外层关系;
 *   inner_path —— 内层路径(将被包装);
 *   outer_path —— 外层路径;
 *   jointype   —— 连接类型;
 *   extra      —— JoinPathExtraData 上下文。
 * 【返回值】新的 Memoize 路径;任何条件不满足时返回 NULL。
 */
static Path *
get_memoize_path(PlannerInfo *root, RelOptInfo *innerrel,
				 RelOptInfo *outerrel, Path *inner_path,
				 Path *outer_path, JoinType jointype,
				 JoinPathExtraData *extra)
{
	List	   *param_exprs;
	List	   *hash_operators;
	ListCell   *lc;
	bool		binary_mode;
	List	   *ph_lateral_vars;

	/* Obviously not if it's disabled */
	if ((extra->pgs_mask & PGS_NESTLOOP_MEMOIZE) == 0)
		return NULL;

	/*
	 * We can safely not bother with all this unless we expect to perform more
	 * than one inner scan.  The first scan is always going to be a cache
	 * miss.  This would likely fail later anyway based on costs, so this is
	 * really just to save some wasted effort.
	 *
	 * However, if the "plain nested loop" strategy is disabled, then it is no
	 * longer certain that any path we'd construct here would lose on cost.
	 * So, in that case, continue and let cost comparison sort things out.
	 */
	if (outer_path->parent->rows < 2 &&
		(extra->pgs_mask & PGS_NESTLOOP_PLAIN) != 0)
		return NULL;

	/*
	 * Extract lateral Vars/PHVs within PlaceHolderVars that are due to be
	 * evaluated at innerrel.  These lateral Vars/PHVs could be used as
	 * memoize cache keys.
	 */
	ph_lateral_vars = extract_lateral_vars_from_PHVs(root, innerrel->relids);

	/*
	 * We can only have a memoize node when there's some kind of cache key,
	 * either parameterized path clauses or lateral Vars.  No cache key sounds
	 * more like something a Materialize node might be more useful for.
	 */
	if ((inner_path->param_info == NULL ||
		 inner_path->param_info->ppi_clauses == NIL) &&
		innerrel->lateral_vars == NIL &&
		ph_lateral_vars == NIL)
		return NULL;

	/*
	 * Currently we don't do this for SEMI and ANTI joins, because nested loop
	 * SEMI/ANTI joins don't scan the inner node to completion, which means
	 * memoize cannot mark the cache entry as complete.  Nor can we mark the
	 * cache entry as complete after fetching the first inner tuple, because
	 * if that tuple and the current outer tuple don't satisfy the join
	 * clauses, a second inner tuple that satisfies the parameters would find
	 * the cache entry already marked as complete.  The only exception is when
	 * the inner relation is provably unique, as in that case, there won't be
	 * a second matching tuple and we can safely mark the cache entry as
	 * complete after fetching the first inner tuple.  Note that in such
	 * cases, the SEMI join should have been reduced to an inner join by
	 * reduce_unique_semijoins.
	 */
	if ((jointype == JOIN_SEMI || jointype == JOIN_ANTI) &&
		!extra->inner_unique)
		return NULL;

	/*
	 * Memoize normally marks cache entries as complete when it runs out of
	 * tuples to read from its subplan.  However, with unique joins, Nested
	 * Loop will skip to the next outer tuple after finding the first matching
	 * inner tuple.  This means that we may not read the inner side of the
	 * join to completion which leaves no opportunity to mark the cache entry
	 * as complete.  To work around that, when the join is unique we
	 * automatically mark cache entries as complete after fetching the first
	 * tuple.  This works when the entire join condition is parameterized.
	 * Otherwise, when the parameterization is only a subset of the join
	 * condition, we can't be sure which part of it causes the join to be
	 * unique.  This means there are no guarantees that only 1 tuple will be
	 * read.  We cannot mark the cache entry as complete after reading the
	 * first tuple without that guarantee.  This means the scope of Memoize
	 * node's usefulness is limited to only outer rows that have no join
	 * partner as this is the only case where Nested Loop would exhaust the
	 * inner scan of a unique join.  Since the scope is limited to that, we
	 * just don't bother making a memoize path in this case.
	 *
	 * Lateral vars needn't be considered here as they're not considered when
	 * determining if the join is unique.
	 */
	if (extra->inner_unique)
	{
		Bitmapset  *ppi_serials;

		if (inner_path->param_info == NULL)
			return NULL;

		ppi_serials = inner_path->param_info->ppi_serials;

		foreach_node(RestrictInfo, rinfo, extra->restrictlist)
		{
			if (!bms_is_member(rinfo->rinfo_serial, ppi_serials))
				return NULL;
		}
	}

	/*
	 * We can't use a memoize node if there are volatile functions in the
	 * inner rel's target list or restrict list.  A cache hit could reduce the
	 * number of calls to these functions.
	 */
	if (contain_volatile_functions((Node *) innerrel->reltarget))
		return NULL;

	foreach(lc, innerrel->baserestrictinfo)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		if (contain_volatile_functions((Node *) rinfo))
			return NULL;
	}

	/*
	 * Also check the parameterized path restrictinfos for volatile functions.
	 * Indexed functions must be immutable so shouldn't have any volatile
	 * functions, however, with a lateral join the inner scan may not be an
	 * index scan.
	 */
	if (inner_path->param_info != NULL)
	{
		foreach(lc, inner_path->param_info->ppi_clauses)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			if (contain_volatile_functions((Node *) rinfo))
				return NULL;
		}
	}

	/* Check if we have hash ops for each parameter to the path */
	if (paraminfo_get_equal_hashops(root,
									inner_path->param_info,
									outerrel->top_parent ?
									outerrel->top_parent : outerrel,
									innerrel,
									ph_lateral_vars,
									&param_exprs,
									&hash_operators,
									&binary_mode))
	{
		return (Path *) create_memoize_path(root,
											innerrel,
											inner_path,
											param_exprs,
											hash_operators,
											extra->inner_unique,
											binary_mode,
											outer_path->rows);
	}

	return NULL;
}

/*
 * try_nestloop_path
 *	  Consider a nestloop join path; if it appears useful, push it into
 *	  the joinrel's pathlist via add_path().
 */
/*
 * try_nestloop_path - (中文)考虑一条嵌套循环连接路径,若看似有用则加入
 * joinrel 的 pathlist
 *
 * 【作用】match_unsorted_outer() 针对每条外层路径与每条内层候选路径,调用
 * 本函数尝试生成嵌套循环路径。先做一系列合法性/代价预检,通过后调用
 * create_nestloop_path() 构造完整路径并交给 add_path() 精确去劣。
 *
 * 【设计思想】
 * - 合法性检查:若本层正在形成一个外层连接(extra->sjinfo->ojrelid != 0),
 *   输入路径的参数化中绝不能包含该外层连接的 relid(否则意味着要依赖
 *   尚未算出的 NULL 化结果);随后用 calc_nestloop_required_outer() 计算
 *   结果路径真正需要的参数来源 required_outer,若它既与 param_source_rels
 *   无交集、又不满足 allow_star_schema_join() 的星型例外,则拒绝该路径;
 * - 分区裁剪相关:参数化一律针对 top_parent(顶层父表),因此必须用
 *   top_parent_relids 参与判定;若内层路径被顶层父表参数化,还要确认
 *   path_is_reparameterizable_by_child() 能在 create_plan() 阶段把参数化
 *   翻译到子表上,否则直接放弃;
 * - 两阶段代价方法:先用 initial_cost_nestloop() 算出廉价的下界
 *   (startup_cost/total_cost),配合 add_path_precheck() 快速淘汰明显被
 *   现有路径支配者;只有通过预检才构造完整路径走 add_path(),节省昂贵的
 *   完整路径构造时间;
 * - nestloop_subtype 区分 PGS_NESTLOOP_PLAIN / MATERIALIZE / MEMOIZE,
 *   try_nestloop_path 阶段统一加 PGS_CONSIDER_NONPARTIAL(部分路径由
 *   try_partial_nestloop_path 处理)。
 *
 * 【参数】
 *   root             —— PlannerInfo;
 *   joinrel          —— 目标连接关系;
 *   outer_path       —— 外层路径;
 *   inner_path       —— 内层路径;
 *   pathkeys         —— 结果路径的输出排序(通常来自外层);
 *   jointype         —— 连接类型;
 *   nestloop_subtype —— 嵌套循环子类型(PGS_NESTLOOP_* 位);
 *   extra            —— JoinPathExtraData 上下文。
 * 【返回值】无(可能把路径加入 joinrel->pathlist)。
 */
static void
try_nestloop_path(PlannerInfo *root,
				  RelOptInfo *joinrel,
				  Path *outer_path,
				  Path *inner_path,
				  List *pathkeys,
				  JoinType jointype,
				  uint64 nestloop_subtype,
				  JoinPathExtraData *extra)
{
	Relids		required_outer;
	JoinCostWorkspace workspace;
	RelOptInfo *innerrel = inner_path->parent;
	RelOptInfo *outerrel = outer_path->parent;
	Relids		innerrelids;
	Relids		outerrelids;
	Relids		inner_paramrels = PATH_REQ_OUTER(inner_path);
	Relids		outer_paramrels = PATH_REQ_OUTER(outer_path);

	/*
	 * If we are forming an outer join at this join, it's nonsensical to use
	 * an input path that uses the outer join as part of its parameterization.
	 * (This can happen despite our join order restrictions, since those apply
	 * to what is in an input relation not what its parameters are.)
	 */
	if (extra->sjinfo->ojrelid != 0 &&
		(bms_is_member(extra->sjinfo->ojrelid, inner_paramrels) ||
		 bms_is_member(extra->sjinfo->ojrelid, outer_paramrels)))
		return;

	/*
	 * Any parameterization of the input paths refers to topmost parents of
	 * the relevant relations, because reparameterize_path_by_child() hasn't
	 * been called yet.  So we must consider topmost parents of the relations
	 * being joined, too, while determining parameterization of the result and
	 * checking for disallowed parameterization cases.
	 */
	if (innerrel->top_parent_relids)
		innerrelids = innerrel->top_parent_relids;
	else
		innerrelids = innerrel->relids;

	if (outerrel->top_parent_relids)
		outerrelids = outerrel->top_parent_relids;
	else
		outerrelids = outerrel->relids;

	/*
	 * Check to see if proposed path is still parameterized, and reject if the
	 * parameterization wouldn't be sensible --- unless allow_star_schema_join
	 * says to allow it anyway.
	 */
	required_outer = calc_nestloop_required_outer(outerrelids, outer_paramrels,
												  innerrelids, inner_paramrels);
	if (required_outer &&
		!bms_overlap(required_outer, extra->param_source_rels) &&
		!allow_star_schema_join(root, outerrelids, inner_paramrels))
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
		return;
	}

	/* If we got past that, we shouldn't have any unsafe outer-join refs */
	Assert(!have_unsafe_outer_join_ref(root, outerrelids, inner_paramrels));

	/*
	 * If the inner path is parameterized, it is parameterized by the topmost
	 * parent of the outer rel, not the outer rel itself.  We will need to
	 * translate the parameterization, if this path is chosen, during
	 * create_plan().  Here we just check whether we will be able to perform
	 * the translation, and if not avoid creating a nestloop path.
	 */
	if (PATH_PARAM_BY_PARENT(inner_path, outer_path->parent) &&
		!path_is_reparameterizable_by_child(inner_path, outer_path->parent))
	{
		bms_free(required_outer);
		return;
	}

	/*
	 * Do a precheck to quickly eliminate obviously-inferior paths.  We
	 * calculate a cheap lower bound on the path's cost and then use
	 * add_path_precheck() to see if the path is clearly going to be dominated
	 * by some existing path for the joinrel.  If not, do the full pushup with
	 * creating a fully valid path structure and submitting it to add_path().
	 * The latter two steps are expensive enough to make this two-phase
	 * methodology worthwhile.
	 */
	initial_cost_nestloop(root, &workspace, jointype,
						  nestloop_subtype | PGS_CONSIDER_NONPARTIAL,
						  outer_path, inner_path, extra);

	if (add_path_precheck(joinrel, workspace.disabled_nodes,
						  workspace.startup_cost, workspace.total_cost,
						  pathkeys, required_outer))
	{
		add_path(joinrel, (Path *)
				 create_nestloop_path(root,
									  joinrel,
									  jointype,
									  &workspace,
									  extra,
									  outer_path,
									  inner_path,
									  extra->restrictlist,
									  pathkeys,
									  required_outer));
	}
	else
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
	}
}

/*
 * try_partial_nestloop_path
 *	  Consider a partial nestloop join path; if it appears useful, push it into
 *	  the joinrel's partial_pathlist via add_partial_path().
 */
/*
 * try_partial_nestloop_path - (中文)考虑一条并行(partial)嵌套循环路径,若
 * 看似有用则加入 joinrel 的 partial_pathlist
 *
 * 【作用】consider_parallel_nestloop() 为每条并行外层路径与并行安全的内层
 * 路径调用本函数,尝试生成 partial 嵌套循环路径。与 try_nestloop_path 的
 * 区别:结果加入 partial_pathlist(通过 add_partial_path),且路径不能有任何
 * 剩余参数化(并行路径不支持参数化)。
 *
 * 【设计思想】
 * - 前置断言:joinrel 无横向依赖、外层路径无参数化(调用方已保证);
 * - 内层参数化必须被外层关系完全满足(bms_is_subset),否则放弃——并行
 *   路径的参数化必须是完整的、可由外层提供的;
 * - 同样要考虑顶层父表的参数化翻译问题,不可翻译则放弃;
 * - 代价预检用 add_partial_path_precheck(),通过后再构造路径。
 * 创建时向 create_nestloop_path() 传 required_outer = NULL,保证产物无
 * 参数化。
 *
 * 【参数】
 *   root             —— PlannerInfo;
 *   joinrel          —— 目标连接关系;
 *   outer_path       —— 并行外层路径;
 *   inner_path       —— 内层路径;
 *   pathkeys         —— 结果路径的输出排序;
 *   jointype         —— 连接类型;
 *   nestloop_subtype —— 嵌套循环子类型;
 *   extra            —— JoinPathExtraData 上下文。
 * 【返回值】无(可能把路径加入 joinrel->partial_pathlist)。
 */
static void
try_partial_nestloop_path(PlannerInfo *root,
						  RelOptInfo *joinrel,
						  Path *outer_path,
						  Path *inner_path,
						  List *pathkeys,
						  JoinType jointype,
						  uint64 nestloop_subtype,
						  JoinPathExtraData *extra)
{
	JoinCostWorkspace workspace;

	/*
	 * If the inner path is parameterized, the parameterization must be fully
	 * satisfied by the proposed outer path.  Parameterized partial paths are
	 * not supported.  The caller should already have verified that no lateral
	 * rels are required here.
	 */
	Assert(bms_is_empty(joinrel->lateral_relids));
	Assert(bms_is_empty(PATH_REQ_OUTER(outer_path)));
	if (inner_path->param_info != NULL)
	{
		Relids		inner_paramrels = inner_path->param_info->ppi_req_outer;
		RelOptInfo *outerrel = outer_path->parent;
		Relids		outerrelids;

		/*
		 * The inner and outer paths are parameterized, if at all, by the top
		 * level parents, not the child relations, so we must use those relids
		 * for our parameterization tests.
		 */
		if (outerrel->top_parent_relids)
			outerrelids = outerrel->top_parent_relids;
		else
			outerrelids = outerrel->relids;

		if (!bms_is_subset(inner_paramrels, outerrelids))
			return;
	}

	/*
	 * If the inner path is parameterized, it is parameterized by the topmost
	 * parent of the outer rel, not the outer rel itself.  We will need to
	 * translate the parameterization, if this path is chosen, during
	 * create_plan().  Here we just check whether we will be able to perform
	 * the translation, and if not avoid creating a nestloop path.
	 */
	if (PATH_PARAM_BY_PARENT(inner_path, outer_path->parent) &&
		!path_is_reparameterizable_by_child(inner_path, outer_path->parent))
		return;

	/*
	 * Before creating a path, get a quick lower bound on what it is likely to
	 * cost.  Bail out right away if it looks terrible.
	 */
	initial_cost_nestloop(root, &workspace, jointype, nestloop_subtype,
						  outer_path, inner_path, extra);
	if (!add_partial_path_precheck(joinrel, workspace.disabled_nodes,
								   workspace.startup_cost,
								   workspace.total_cost, pathkeys))
		return;

	/* Might be good enough to be worth trying, so let's try it. */
	add_partial_path(joinrel, (Path *)
					 create_nestloop_path(root,
										  joinrel,
										  jointype,
										  &workspace,
										  extra,
										  outer_path,
										  inner_path,
										  extra->restrictlist,
										  pathkeys,
										  NULL));
}

/*
 * try_mergejoin_path
 *	  Consider a merge join path; if it appears useful, push it into
 *	  the joinrel's pathlist via add_path().
 */
/*
 * try_mergejoin_path - (中文)考虑一条归并连接路径,若看似有用则加入
 * joinrel 的 pathlist(或 partial_pathlist)
 *
 * 【作用】sort_inner_and_outer() / generate_mergejoin_paths() 为每条候选
 * (外层路径, 内层路径)组合调用本函数。is_partial 为 true 时转交
 * try_partial_mergejoin_path() 处理;否则走与 try_nestloop_path 类似的两
 * 阶段预检流程,构造 MergeJoin 路径加入 pathlist。
 *
 * 【设计思想】
 * - is_partial 分支直接把工作交给 try_partial_mergejoin_path()(partial
 *   路径无参数化、加 partial_pathlist);
 * - 非 partial 时:拒绝参数化中包含本层外层连接 relid 的输入路径;用
 *   calc_non_nestloop_required_outer() 计算必需参数,若与 param_source_rels
 *   无交集则拒绝;
 * - 排序优化:若外层路径已经满足 outersortkeys 的前缀
 *   (pathkeys_count_contained_in 同时给出前缀长度 outer_presorted_keys,
 *   用于判断是否可应用增量排序 Incremental Sort),或内层路径已满足
 *   innersortkeys,则把相应的显式排序需求置 NIL,省去排序步骤;
 * - initial_cost_mergejoin() + add_path_precheck() 两阶段过滤,通过后
 *   create_mergejoin_path() 构造完整路径。
 *
 * 【参数】
 *   root             —— PlannerInfo;
 *   joinrel          —— 目标连接关系;
 *   outer_path       —— 外层路径;
 *   inner_path       —— 内层路径;
 *   pathkeys         —— 结果路径的输出排序;
 *   mergeclauses     —— 本次归并使用的连接子句;
 *   outersortkeys    —— 需要加在外层上的显式排序键(可为 NIL);
 *   innersortkeys    —— 需要加在内层上的显式排序键(可为 NIL);
 *   jointype         —— 连接类型;
 *   extra            —— JoinPathExtraData 上下文;
 *   is_partial       —— true 表示生成并行(partial)归并路径。
 * 【返回值】无(可能把路径加入 joinrel->pathlist 或 partial_pathlist)。
 */
static void
try_mergejoin_path(PlannerInfo *root,
				   RelOptInfo *joinrel,
				   Path *outer_path,
				   Path *inner_path,
				   List *pathkeys,
				   List *mergeclauses,
				   List *outersortkeys,
				   List *innersortkeys,
				   JoinType jointype,
				   JoinPathExtraData *extra,
				   bool is_partial)
{
	Relids		required_outer;
	int			outer_presorted_keys = 0;
	JoinCostWorkspace workspace;

	if (is_partial)
	{
		try_partial_mergejoin_path(root,
								   joinrel,
								   outer_path,
								   inner_path,
								   pathkeys,
								   mergeclauses,
								   outersortkeys,
								   innersortkeys,
								   jointype,
								   extra);
		return;
	}

	/*
	 * If we are forming an outer join at this join, it's nonsensical to use
	 * an input path that uses the outer join as part of its parameterization.
	 * (This can happen despite our join order restrictions, since those apply
	 * to what is in an input relation not what its parameters are.)
	 */
	if (extra->sjinfo->ojrelid != 0 &&
		(bms_is_member(extra->sjinfo->ojrelid, PATH_REQ_OUTER(inner_path)) ||
		 bms_is_member(extra->sjinfo->ojrelid, PATH_REQ_OUTER(outer_path))))
		return;

	/*
	 * Check to see if proposed path is still parameterized, and reject if the
	 * parameterization wouldn't be sensible.
	 */
	required_outer = calc_non_nestloop_required_outer(outer_path,
													  inner_path);
	if (required_outer &&
		!bms_overlap(required_outer, extra->param_source_rels))
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
		return;
	}

	/*
	 * If the given paths are already well enough ordered, we can skip doing
	 * an explicit sort.
	 *
	 * We need to determine the number of presorted keys of the outer path to
	 * decide whether explicit incremental sort can be applied when
	 * outersortkeys is not NIL.  We do not need to do the same for the inner
	 * path though, as incremental sort currently does not support
	 * mark/restore.
	 */
	if (outersortkeys &&
		pathkeys_count_contained_in(outersortkeys, outer_path->pathkeys,
									&outer_presorted_keys))
		outersortkeys = NIL;
	if (innersortkeys &&
		pathkeys_contained_in(innersortkeys, inner_path->pathkeys))
		innersortkeys = NIL;

	/*
	 * See comments in try_nestloop_path().
	 */
	initial_cost_mergejoin(root, &workspace, jointype, mergeclauses,
						   outer_path, inner_path,
						   outersortkeys, innersortkeys,
						   outer_presorted_keys,
						   extra);

	if (add_path_precheck(joinrel, workspace.disabled_nodes,
						  workspace.startup_cost, workspace.total_cost,
						  pathkeys, required_outer))
	{
		add_path(joinrel, (Path *)
				 create_mergejoin_path(root,
									   joinrel,
									   jointype,
									   &workspace,
									   extra,
									   outer_path,
									   inner_path,
									   extra->restrictlist,
									   pathkeys,
									   required_outer,
									   mergeclauses,
									   outersortkeys,
									   innersortkeys,
									   outer_presorted_keys));
	}
	else
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
	}
}

/*
 * try_partial_mergejoin_path
 *	  Consider a partial merge join path; if it appears useful, push it into
 *	  the joinrel's pathlist via add_partial_path().
 */
/*
 * try_partial_mergejoin_path - (中文)考虑一条并行(partial)归并连接路径,若
 * 看似有用则加入 joinrel 的 partial_pathlist
 *
 * 【作用】try_mergejoin_path() 在 is_partial 为 true 时转入本函数,或由
 * sort_inner_and_outer() 直接调用。尝试用并行外层 + 并行安全内层生成
 * partial 归并路径。
 *
 * 【设计思想】
 * - 并行归并要求无横向依赖、外层无参数化、内层也无参数化
 *   (bms_is_empty(PATH_REQ_OUTER(inner_path))),否则放弃;
 * - 与 try_mergejoin_path 相同的外层/内层排序需求检测
 *   (pathkeys_count_contained_in 计算外层已预排序键数,决定是否可用增量
 *   排序;内层用 pathkeys_contained_in 判定);
 * - initial_cost_mergejoin() + add_partial_path_precheck() 两阶段过滤;
 * - 构造时 create_mergejoin_path() 的 required_outer 传 NULL(无参数化)。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   joinrel       —— 目标连接关系;
 *   outer_path    —— 并行外层路径;
 *   inner_path    —— 内层路径;
 *   pathkeys      —— 结果路径的输出排序;
 *   mergeclauses  —— 归并连接子句;
 *   outersortkeys —— 外层显式排序键(可为 NIL);
 *   innersortkeys —— 内层显式排序键(可为 NIL);
 *   jointype      —— 连接类型;
 *   extra         —— JoinPathExtraData 上下文。
 * 【返回值】无(可能把路径加入 joinrel->partial_pathlist)。
 */
static void
try_partial_mergejoin_path(PlannerInfo *root,
						   RelOptInfo *joinrel,
						   Path *outer_path,
						   Path *inner_path,
						   List *pathkeys,
						   List *mergeclauses,
						   List *outersortkeys,
						   List *innersortkeys,
						   JoinType jointype,
						   JoinPathExtraData *extra)
{
	int			outer_presorted_keys = 0;
	JoinCostWorkspace workspace;

	/*
	 * See comments in try_partial_hashjoin_path().
	 */
	Assert(bms_is_empty(joinrel->lateral_relids));
	Assert(bms_is_empty(PATH_REQ_OUTER(outer_path)));
	if (!bms_is_empty(PATH_REQ_OUTER(inner_path)))
		return;

	/*
	 * If the given paths are already well enough ordered, we can skip doing
	 * an explicit sort.
	 *
	 * We need to determine the number of presorted keys of the outer path to
	 * decide whether explicit incremental sort can be applied when
	 * outersortkeys is not NIL.  We do not need to do the same for the inner
	 * path though, as incremental sort currently does not support
	 * mark/restore.
	 */
	if (outersortkeys &&
		pathkeys_count_contained_in(outersortkeys, outer_path->pathkeys,
									&outer_presorted_keys))
		outersortkeys = NIL;
	if (innersortkeys &&
		pathkeys_contained_in(innersortkeys, inner_path->pathkeys))
		innersortkeys = NIL;

	/*
	 * See comments in try_partial_nestloop_path().
	 */
	initial_cost_mergejoin(root, &workspace, jointype, mergeclauses,
						   outer_path, inner_path,
						   outersortkeys, innersortkeys,
						   outer_presorted_keys,
						   extra);

	if (!add_partial_path_precheck(joinrel, workspace.disabled_nodes,
								   workspace.startup_cost,
								   workspace.total_cost, pathkeys))
		return;

	/* Might be good enough to be worth trying, so let's try it. */
	add_partial_path(joinrel, (Path *)
					 create_mergejoin_path(root,
										   joinrel,
										   jointype,
										   &workspace,
										   extra,
										   outer_path,
										   inner_path,
										   extra->restrictlist,
										   pathkeys,
										   NULL,
										   mergeclauses,
										   outersortkeys,
										   innersortkeys,
										   outer_presorted_keys));
}

/*
 * try_hashjoin_path
 *	  Consider a hash join path; if it appears useful, push it into
 *	  the joinrel's pathlist via add_path().
 */
/*
 * try_hashjoin_path - (中文)考虑一条哈希连接路径,若看似有用则加入
 * joinrel 的 pathlist
 *
 * 【作用】hash_inner_and_outer() 为每条 (外层, 内层) 候选组合调用本函数
 * 生成哈希连接路径。哈希连接按定义不产生有序输出,因此 pathkeys 恒为 NIL。
 *
 * 【设计思想】与 try_nestloop_path 相似:
 * - 拒绝参数化中包含本层外层连接 relid 的输入路径;
 * - 用 calc_non_nestloop_required_outer() 计算必需参数,与 param_source_rels
 *   无交集则拒绝;
 * - initial_cost_hashjoin()(parallel_hash 传 false)计算代价下界,经
 *   add_path_precheck()(pathkeys 传 NIL)快速淘汰后,再
 *   create_hashjoin_path() 构造完整路径(parallel_hash 传 false)。
 *
 * 【参数】
 *   root       —— PlannerInfo;
 *   joinrel    —— 目标连接关系;
 *   outer_path —— 外层路径;
 *   inner_path —— 内层路径;
 *   hashclauses —— 哈希连接子句;
 *   jointype   —— 连接类型;
 *   extra      —— JoinPathExtraData 上下文。
 * 【返回值】无(可能把路径加入 joinrel->pathlist)。
 */
static void
try_hashjoin_path(PlannerInfo *root,
				  RelOptInfo *joinrel,
				  Path *outer_path,
				  Path *inner_path,
				  List *hashclauses,
				  JoinType jointype,
				  JoinPathExtraData *extra)
{
	Relids		required_outer;
	JoinCostWorkspace workspace;

	/*
	 * If we are forming an outer join at this join, it's nonsensical to use
	 * an input path that uses the outer join as part of its parameterization.
	 * (This can happen despite our join order restrictions, since those apply
	 * to what is in an input relation not what its parameters are.)
	 */
	if (extra->sjinfo->ojrelid != 0 &&
		(bms_is_member(extra->sjinfo->ojrelid, PATH_REQ_OUTER(inner_path)) ||
		 bms_is_member(extra->sjinfo->ojrelid, PATH_REQ_OUTER(outer_path))))
		return;

	/*
	 * Check to see if proposed path is still parameterized, and reject if the
	 * parameterization wouldn't be sensible.
	 */
	required_outer = calc_non_nestloop_required_outer(outer_path,
													  inner_path);
	if (required_outer &&
		!bms_overlap(required_outer, extra->param_source_rels))
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
		return;
	}

	/*
	 * See comments in try_nestloop_path().  Also note that hashjoin paths
	 * never have any output pathkeys, per comments in create_hashjoin_path.
	 */
	initial_cost_hashjoin(root, &workspace, jointype, hashclauses,
						  outer_path, inner_path, extra, false);

	if (add_path_precheck(joinrel, workspace.disabled_nodes,
						  workspace.startup_cost, workspace.total_cost,
						  NIL, required_outer))
	{
		add_path(joinrel, (Path *)
				 create_hashjoin_path(root,
									  joinrel,
									  jointype,
									  &workspace,
									  extra,
									  outer_path,
									  inner_path,
									  false,	/* parallel_hash */
									  extra->restrictlist,
									  required_outer,
									  hashclauses));
	}
	else
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
	}
}

/*
 * try_partial_hashjoin_path
 *	  Consider a partial hashjoin join path; if it appears useful, push it into
 *	  the joinrel's partial_pathlist via add_partial_path().
 *	  The outer side is partial.  If parallel_hash is true, then the inner path
 *	  must be partial and will be run in parallel to create one or more shared
 *	  hash tables; otherwise the inner path must be complete and a copy of it
 *	  is run in every process to create separate identical private hash tables.
 */
/*
 * try_partial_hashjoin_path - (中文)考虑一条并行(partial)哈希连接路径,若
 * 看似有用则加入 joinrel 的 partial_pathlist
 *
 * 【作用】hash_inner_and_outer() 在 joinrel 并行安全时调用本函数,尝试构建
 * partial 哈希连接:外层必须是 partial 路径。根据 parallel_hash 决定内层
 * 策略——true 时内层也用 partial 路径并行构造一个或多个共享哈希表;false
 * 时内层是完整(非 partial)路径,每个 worker 各自复制执行构造一份私有
 * 哈希表。
 *
 * 【设计思想】
 * - 前置断言:无横向依赖、外层无参数化;内层若有参数化则放弃(并行路径
 *   不支持参数化);
 * - initial_cost_hashjoin()(parallel_hash 按实参传入)计算代价下界,经
 *   add_partial_path_precheck() 快速过滤后,create_hashjoin_path() 构造
 *   路径(required_outer 为 NULL,parallel_hash 按实参传入)并加入
 *   partial_pathlist。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   joinrel       —— 目标连接关系;
 *   outer_path    —— 并行外层路径;
 *   inner_path    —— 内层路径;
 *   hashclauses   —— 哈希连接子句;
 *   jointype      —— 连接类型;
 *   extra         —— JoinPathExtraData 上下文;
 *   parallel_hash —— true:内层也是 partial,构建共享哈希表;false:内层完整,
 *                    每个进程各自建私有哈希表。
 * 【返回值】无(可能把路径加入 joinrel->partial_pathlist)。
 */
static void
try_partial_hashjoin_path(PlannerInfo *root,
						  RelOptInfo *joinrel,
						  Path *outer_path,
						  Path *inner_path,
						  List *hashclauses,
						  JoinType jointype,
						  JoinPathExtraData *extra,
						  bool parallel_hash)
{
	JoinCostWorkspace workspace;

	/*
	 * If the inner path is parameterized, we can't use a partial hashjoin.
	 * Parameterized partial paths are not supported.  The caller should
	 * already have verified that no lateral rels are required here.
	 */
	Assert(bms_is_empty(joinrel->lateral_relids));
	Assert(bms_is_empty(PATH_REQ_OUTER(outer_path)));
	if (!bms_is_empty(PATH_REQ_OUTER(inner_path)))
		return;

	/*
	 * Before creating a path, get a quick lower bound on what it is likely to
	 * cost.  Bail out right away if it looks terrible.
	 */
	initial_cost_hashjoin(root, &workspace, jointype, hashclauses,
						  outer_path, inner_path, extra, parallel_hash);
	if (!add_partial_path_precheck(joinrel, workspace.disabled_nodes,
								   workspace.startup_cost,
								   workspace.total_cost, NIL))
		return;

	/* Might be good enough to be worth trying, so let's try it. */
	add_partial_path(joinrel, (Path *)
					 create_hashjoin_path(root,
										  joinrel,
										  jointype,
										  &workspace,
										  extra,
										  outer_path,
										  inner_path,
										  parallel_hash,
										  extra->restrictlist,
										  NULL,
										  hashclauses));
}

/*
 * sort_inner_and_outer
 *	  Create mergejoin join paths by explicitly sorting both the outer and
 *	  inner join relations on each available merge ordering.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 */
/*
 * sort_inner_and_outer - (中文)对每种子句排序顺序,显式排序外/内两侧以生成
 * 归并连接路径
 *
 * 【作用】add_paths_to_joinrel() 的第 1 步:两侧都需要显式排序的归并连接。
 * 若存在可用的归并连接子句,就枚举多种排序顺序,分别调用
 * try_mergejoin_path() 生成路径。
 *
 * 【设计思想】
 * - 只用最便宜总代价的输入路径(outerrel->cheapest_total_path、
 *   innerrel->cheapest_total_path):既然假设需要排序,就无需考虑最便宜启动
 *   路径(那是 match_unsorted_outer 的职责);也刻意不考虑参数化输入路径,
 *   以免归并路径组合爆炸;
 * - 若某个 cheapest-total 路径被另一个关系参数化,则无法归并,直接返回;
 * - joinrel 并行安全且连接类型不是 FULL/RIGHT/RIGHT_ANTI 时,尝试 partial
 *   归并:取外层 partial 路径与并行安全的内层 cheapest-total 路径;
 * - 关键技巧:不同归并子句排列会产生不同输出排序,但对高层归并可能各有
 *   价值,因此把 mergeclause 列表换算成"规范路径键"列表
 *   (select_outer_pathkeys_for_merge),再让每个 pathkey 依次"打头"、其余
 *   按原序跟在后面,得到多种排序;对每种排序用
 *   find_mergeclauses_for_outer_pathkeys() 重新排列子句、用
 *   make_inner_pathkeys_for_merge() 求内层排序、用 build_join_pathkeys()
 *   求输出排序,然后调用 try_mergejoin_path()(以及有并行输入时
 *   try_partial_mergejoin_path());
 * - try_mergejoin_path() 会检测"路径已有序"的情况,自动省略显式排序。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   joinrel —— 连接关系;
 *   outerrel —— 外层输入关系;
 *   innerrel —— 内层输入关系;
 *   jointype —— 连接类型;
 *   extra   —— JoinPathExtraData 上下文(含 mergeclause_list)。
 * 【返回值】无。
 */
static void
sort_inner_and_outer(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 JoinPathExtraData *extra)
{
	Path	   *outer_path;
	Path	   *inner_path;
	Path	   *cheapest_partial_outer = NULL;
	Path	   *cheapest_safe_inner = NULL;
	List	   *all_pathkeys;
	ListCell   *l;

	/* Nothing to do if there are no available mergejoin clauses */
	if (extra->mergeclause_list == NIL)
		return;

	/*
	 * We only consider the cheapest-total-cost input paths, since we are
	 * assuming here that a sort is required.  We will consider
	 * cheapest-startup-cost input paths later, and only if they don't need a
	 * sort.
	 *
	 * This function intentionally does not consider parameterized input
	 * paths, except when the cheapest-total is parameterized.  If we did so,
	 * we'd have a combinatorial explosion of mergejoin paths of dubious
	 * value.  This interacts with decisions elsewhere that also discriminate
	 * against mergejoins with parameterized inputs; see comments in
	 * src/backend/optimizer/README.
	 */
	outer_path = outerrel->cheapest_total_path;
	inner_path = innerrel->cheapest_total_path;

	/*
	 * If either cheapest-total path is parameterized by the other rel, we
	 * can't use a mergejoin.  (There's no use looking for alternative input
	 * paths, since these should already be the least-parameterized available
	 * paths.)
	 */
	if (PATH_PARAM_BY_REL(outer_path, innerrel) ||
		PATH_PARAM_BY_REL(inner_path, outerrel))
		return;

	/*
	 * If the joinrel is parallel-safe, we may be able to consider a partial
	 * merge join.  However, we can't handle JOIN_FULL, JOIN_RIGHT and
	 * JOIN_RIGHT_ANTI, because they can produce false null extended rows.
	 * Also, the resulting path must not be parameterized.
	 */
	if (joinrel->consider_parallel &&
		jointype != JOIN_FULL &&
		jointype != JOIN_RIGHT &&
		jointype != JOIN_RIGHT_ANTI &&
		outerrel->partial_pathlist != NIL &&
		bms_is_empty(joinrel->lateral_relids))
	{
		cheapest_partial_outer = (Path *) linitial(outerrel->partial_pathlist);

		if (inner_path->parallel_safe)
			cheapest_safe_inner = inner_path;
		else
			cheapest_safe_inner =
				get_cheapest_parallel_safe_total_inner(innerrel->pathlist);
	}

	/*
	 * Each possible ordering of the available mergejoin clauses will generate
	 * a differently-sorted result path at essentially the same cost.  We have
	 * no basis for choosing one over another at this level of joining, but
	 * some sort orders may be more useful than others for higher-level
	 * mergejoins, so it's worth considering multiple orderings.
	 *
	 * Actually, it's not quite true that every mergeclause ordering will
	 * generate a different path order, because some of the clauses may be
	 * partially redundant (refer to the same EquivalenceClasses).  Therefore,
	 * what we do is convert the mergeclause list to a list of canonical
	 * pathkeys, and then consider different orderings of the pathkeys.
	 *
	 * Generating a path for *every* permutation of the pathkeys doesn't seem
	 * like a winning strategy; the cost in planning time is too high. For
	 * now, we generate one path for each pathkey, listing that pathkey first
	 * and the rest in random order.  This should allow at least a one-clause
	 * mergejoin without re-sorting against any other possible mergejoin
	 * partner path.  But if we've not guessed the right ordering of secondary
	 * keys, we may end up evaluating clauses as qpquals when they could have
	 * been done as mergeclauses.  (In practice, it's rare that there's more
	 * than two or three mergeclauses, so expending a huge amount of thought
	 * on that is probably not worth it.)
	 *
	 * The pathkey order returned by select_outer_pathkeys_for_merge() has
	 * some heuristics behind it (see that function), so be sure to try it
	 * exactly as-is as well as making variants.
	 */
	all_pathkeys = select_outer_pathkeys_for_merge(root,
												   extra->mergeclause_list,
												   joinrel);

	foreach(l, all_pathkeys)
	{
		PathKey    *front_pathkey = (PathKey *) lfirst(l);
		List	   *cur_mergeclauses;
		List	   *outerkeys;
		List	   *innerkeys;
		List	   *merge_pathkeys;

		/* Make a pathkey list with this guy first */
		if (l != list_head(all_pathkeys))
			outerkeys = lcons(front_pathkey,
							  list_delete_nth_cell(list_copy(all_pathkeys),
												   foreach_current_index(l)));
		else
			outerkeys = all_pathkeys;	/* no work at first one... */

		/* Sort the mergeclauses into the corresponding ordering */
		cur_mergeclauses =
			find_mergeclauses_for_outer_pathkeys(root,
												 outerkeys,
												 extra->mergeclause_list);

		/* Should have used them all... */
		Assert(list_length(cur_mergeclauses) == list_length(extra->mergeclause_list));

		/* Build sort pathkeys for the inner side */
		innerkeys = make_inner_pathkeys_for_merge(root,
												  cur_mergeclauses,
												  outerkeys);

		/* Build pathkeys representing output sort order */
		merge_pathkeys = build_join_pathkeys(root, joinrel, jointype,
											 outerkeys);

		/*
		 * And now we can make the path.
		 *
		 * Note: it's possible that the cheapest paths will already be sorted
		 * properly.  try_mergejoin_path will detect that case and suppress an
		 * explicit sort step, so we needn't do so here.
		 */
		try_mergejoin_path(root,
						   joinrel,
						   outer_path,
						   inner_path,
						   merge_pathkeys,
						   cur_mergeclauses,
						   outerkeys,
						   innerkeys,
						   jointype,
						   extra,
						   false);

		/*
		 * If we have partial outer and parallel safe inner path then try
		 * partial mergejoin path.
		 */
		if (cheapest_partial_outer && cheapest_safe_inner)
			try_partial_mergejoin_path(root,
									   joinrel,
									   cheapest_partial_outer,
									   cheapest_safe_inner,
									   merge_pathkeys,
									   cur_mergeclauses,
									   outerkeys,
									   innerkeys,
									   jointype,
									   extra);
	}
}

/*
 * generate_mergejoin_paths
 *	Creates possible mergejoin paths for input outerpath.
 *
 * We generate mergejoins if mergejoin clauses are available.  We have
 * two ways to generate the inner path for a mergejoin: sort the cheapest
 * inner path, or use an inner path that is already suitably ordered for the
 * merge.  If we have several mergeclauses, it could be that there is no inner
 * path (or only a very expensive one) for the full list of mergeclauses, but
 * better paths exist if we truncate the mergeclause list (thereby discarding
 * some sort key requirements).  So, we consider truncations of the
 * mergeclause list as well as the full list.  (Ideally we'd consider all
 * subsets of the mergeclause list, but that seems way too expensive.)
 */
/*
 * generate_mergejoin_paths - (中文)为给定的外层路径生成各种归并连接路径
 *
 * 【作用】match_unsorted_outer() 与 consider_parallel_mergejoin() 对外层
 * 的每条(已充分排序的)路径调用本函数。它先找与该外层排序匹配的归并子句,
 * 再分别按"对内层最便宜总代价路径加显式排序"与"复用已预排序的内层路径"
 * 两种方式构造归并路径。
 *
 * 【设计思想】
 * - 用 find_mergeclauses_for_outer_pathkeys() 得到可用于当前外层排序的子
 *   句序列;若无(且非 FULL JOIN 的空子句特例)则放弃;
 * - useallclauses 为 true(右/右反/全连接)时,要求子句必须全部用上,否则
 *   不能生成合法计划;
 * - 方案 A:对内层最便宜总代价路径 inner_cheapest_total 加 innersortkeys
 *   显式排序(若已有序, try_mergejoin_path 会自动省略);
 * - 方案 B:从完整 innersortkeys 开始,逐轮截短(每轮去掉最后一个排序键),
 *   用 get_cheapest_path_for_pathkeys 找满足该前缀排序的内层路径,并只保留
 *   严格更便宜的路径(否则就是故意少用归并键,不是好主意);必要时用
 *   trim_mergeclauses_for_inner_pathkeys() 截取匹配的子句前缀;
 * - 分别按 TOTAL_COST 与 STARTUP_COST 两种准则各找一次内层路径;
 * - is_partial 为 true 时,所有 try_mergejoin_path 调用都会转交给 partial
 *   版本,且 get_cheapest_path_for_pathkeys 也限定在 partial_pathlist 中找。
 *
 * 【参数】
 *   root               —— PlannerInfo;
 *   joinrel            —— 连接关系;
 *   innerrel           —— 内层关系;
 *   outerpath          —— 外层路径;
 *   jointype           —— 连接类型;
 *   extra              —— JoinPathExtraData 上下文;
 *   useallclauses      —— true 时必须用上全部归并子句;
 *   inner_cheapest_total —— 内层最便宜总代价路径(排序基准);
 *   merge_pathkeys     —— 结果路径的输出排序键;
 *   is_partial         —— true 表示生成并行路径。
 * 【返回值】无。
 */
static void
generate_mergejoin_paths(PlannerInfo *root,
						 RelOptInfo *joinrel,
						 RelOptInfo *innerrel,
						 Path *outerpath,
						 JoinType jointype,
						 JoinPathExtraData *extra,
						 bool useallclauses,
						 Path *inner_cheapest_total,
						 List *merge_pathkeys,
						 bool is_partial)
{
	List	   *mergeclauses;
	List	   *innersortkeys;
	List	   *trialsortkeys;
	Path	   *cheapest_startup_inner;
	Path	   *cheapest_total_inner;
	int			num_sortkeys;
	int			sortkeycnt;

	/* Look for useful mergeclauses (if any) */
	mergeclauses =
		find_mergeclauses_for_outer_pathkeys(root,
											 outerpath->pathkeys,
											 extra->mergeclause_list);

	/*
	 * Done with this outer path if no chance for a mergejoin.
	 *
	 * Special corner case: for "x FULL JOIN y ON true", there will be no join
	 * clauses at all.  Ordinarily we'd generate a clauseless nestloop path,
	 * but since mergejoin is our only join type that supports FULL JOIN
	 * without any join clauses, it's necessary to generate a clauseless
	 * mergejoin path instead.
	 */
	if (mergeclauses == NIL)
	{
		if (jointype == JOIN_FULL)
			 /* okay to try for mergejoin */ ;
		else
			return;
	}
	if (useallclauses &&
		list_length(mergeclauses) != list_length(extra->mergeclause_list))
		return;

	/* Compute the required ordering of the inner path */
	innersortkeys = make_inner_pathkeys_for_merge(root,
												  mergeclauses,
												  outerpath->pathkeys);

	/*
	 * Generate a mergejoin on the basis of sorting the cheapest inner. Since
	 * a sort will be needed, only cheapest total cost matters. (But
	 * try_mergejoin_path will do the right thing if inner_cheapest_total is
	 * already correctly sorted.)
	 */
	try_mergejoin_path(root,
					   joinrel,
					   outerpath,
					   inner_cheapest_total,
					   merge_pathkeys,
					   mergeclauses,
					   NIL,
					   innersortkeys,
					   jointype,
					   extra,
					   is_partial);

	/*
	 * Look for presorted inner paths that satisfy the innersortkey list ---
	 * or any truncation thereof, if we are allowed to build a mergejoin using
	 * a subset of the merge clauses.  Here, we consider both cheap startup
	 * cost and cheap total cost.
	 *
	 * Currently we do not consider parameterized inner paths here. This
	 * interacts with decisions elsewhere that also discriminate against
	 * mergejoins with parameterized inputs; see comments in
	 * src/backend/optimizer/README.
	 *
	 * As we shorten the sortkey list, we should consider only paths that are
	 * strictly cheaper than (in particular, not the same as) any path found
	 * in an earlier iteration.  Otherwise we'd be intentionally using fewer
	 * merge keys than a given path allows (treating the rest as plain
	 * joinquals), which is unlikely to be a good idea.  Also, eliminating
	 * paths here on the basis of compare_path_costs is a lot cheaper than
	 * building the mergejoin path only to throw it away.
	 *
	 * If inner_cheapest_total is well enough sorted to have not required a
	 * sort in the path made above, we shouldn't make a duplicate path with
	 * it, either.  We handle that case with the same logic that handles the
	 * previous consideration, by initializing the variables that track
	 * cheapest-so-far properly.  Note that we do NOT reject
	 * inner_cheapest_total if we find it matches some shorter set of
	 * pathkeys.  That case corresponds to using fewer mergekeys to avoid
	 * sorting inner_cheapest_total, whereas we did sort it above, so the
	 * plans being considered are different.
	 */
	if (pathkeys_contained_in(innersortkeys,
							  inner_cheapest_total->pathkeys))
	{
		/* inner_cheapest_total didn't require a sort */
		cheapest_startup_inner = inner_cheapest_total;
		cheapest_total_inner = inner_cheapest_total;
	}
	else
	{
		/* it did require a sort, at least for the full set of keys */
		cheapest_startup_inner = NULL;
		cheapest_total_inner = NULL;
	}
	num_sortkeys = list_length(innersortkeys);
	if (num_sortkeys > 1 && !useallclauses)
		trialsortkeys = list_copy(innersortkeys);	/* need modifiable copy */
	else
		trialsortkeys = innersortkeys;	/* won't really truncate */

	for (sortkeycnt = num_sortkeys; sortkeycnt > 0; sortkeycnt--)
	{
		Path	   *innerpath;
		List	   *newclauses = NIL;

		/*
		 * Look for an inner path ordered well enough for the first
		 * 'sortkeycnt' innersortkeys.  NB: trialsortkeys list is modified
		 * destructively, which is why we made a copy...
		 */
		trialsortkeys = list_truncate(trialsortkeys, sortkeycnt);
		innerpath = get_cheapest_path_for_pathkeys(innerrel->pathlist,
												   trialsortkeys,
												   NULL,
												   TOTAL_COST,
												   is_partial);
		if (innerpath != NULL &&
			(cheapest_total_inner == NULL ||
			 compare_path_costs(innerpath, cheapest_total_inner,
								TOTAL_COST) < 0))
		{
			/* Found a cheap (or even-cheaper) sorted path */
			/* Select the right mergeclauses, if we didn't already */
			if (sortkeycnt < num_sortkeys)
			{
				newclauses =
					trim_mergeclauses_for_inner_pathkeys(root,
														 mergeclauses,
														 trialsortkeys);
				Assert(newclauses != NIL);
			}
			else
				newclauses = mergeclauses;
			try_mergejoin_path(root,
							   joinrel,
							   outerpath,
							   innerpath,
							   merge_pathkeys,
							   newclauses,
							   NIL,
							   NIL,
							   jointype,
							   extra,
							   is_partial);
			cheapest_total_inner = innerpath;
		}
		/* Same on the basis of cheapest startup cost ... */
		innerpath = get_cheapest_path_for_pathkeys(innerrel->pathlist,
												   trialsortkeys,
												   NULL,
												   STARTUP_COST,
												   is_partial);
		if (innerpath != NULL &&
			(cheapest_startup_inner == NULL ||
			 compare_path_costs(innerpath, cheapest_startup_inner,
								STARTUP_COST) < 0))
		{
			/* Found a cheap (or even-cheaper) sorted path */
			if (innerpath != cheapest_total_inner)
			{
				/*
				 * Avoid rebuilding clause list if we already made one; saves
				 * memory in big join trees...
				 */
				if (newclauses == NIL)
				{
					if (sortkeycnt < num_sortkeys)
					{
						newclauses =
							trim_mergeclauses_for_inner_pathkeys(root,
																 mergeclauses,
																 trialsortkeys);
						Assert(newclauses != NIL);
					}
					else
						newclauses = mergeclauses;
				}
				try_mergejoin_path(root,
								   joinrel,
								   outerpath,
								   innerpath,
								   merge_pathkeys,
								   newclauses,
								   NIL,
								   NIL,
								   jointype,
								   extra,
								   is_partial);
			}
			cheapest_startup_inner = innerpath;
		}

		/*
		 * Don't consider truncated sortkeys if we need all clauses.
		 */
		if (useallclauses)
			break;
	}
}

/*
 * match_unsorted_outer
 *	  Creates possible join paths for processing a single join relation
 *	  'joinrel' by employing either iterative substitution or
 *	  mergejoining on each of its possible outer paths (considering
 *	  only outer paths that are already ordered well enough for merging).
 *
 * We always generate a nestloop path for each available outer path.
 * In fact we may generate as many as five: one on the cheapest-total-cost
 * inner path, one on the same with materialization, one on the
 * cheapest-startup-cost inner path (if different), one on the
 * cheapest-total inner-indexscan path (if any), and one on the
 * cheapest-startup inner-indexscan path (if different).
 *
 * We also consider mergejoins if mergejoin clauses are available.  See
 * detailed comments in generate_mergejoin_paths.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 */
/*
 * match_unsorted_outer - (中文)为每条"已有序的外层路径"生成嵌套循环与单边
 * 归并连接路径
 *
 * 【作用】add_paths_to_joinrel() 的第 2 步:考虑"外层不必显式排序"的连接,
 * 包括普通嵌套循环,以及外层已有序的单边归并连接。对每条外层路径,先生成
 * 嵌套循环变体(普通 / Memoize / 物化),再交给 generate_mergejoin_paths()
 * 生成归并变体。此外在 joinrel 并行安全时还尝试 partial 嵌套循环与 partial
 * 归并(consider_parallel_nestloop / consider_parallel_mergejoin)。
 *
 * 【设计思想】
 * - 连接类型分流:嵌套循环只支持 INNER/LEFT/SEMI/ANTI(nestjoinOK);
 *   RIGHT/RIGHT_ANTI/FULL 只能走归并,且必须 useallclauses;
 * - 若内层最便宜总代价路径被外层参数化,则置 inner_cheapest_total = NULL
 *   (它稍后会在 cheapest_parameterized_paths 中被考虑),且若内层是"已唯一化
 *   的关系"则完全无法在此生成合法路径,直接返回;
 * - 允许物化时,若内层 cheapest-total 未物化且类型允许,先创建 matpath;
 * - 外层主循环:跳过被内层参数化的外层路径;用 build_join_pathkeys() 计算
 *   结果排序;对每条内层 cheapest_parameterized_paths(含无参数化情形)尝试
 *   普通嵌套循环,再尝试 Memoize 包装;最后尝试物化内层;
 * - 并行收尾:joinrel 并行安全、无横向依赖、非 FULL/RIGHT/RIGHT_ANTI 时,
 *   对每条外层 partial 路径尝试 partial 嵌套循环与 partial 归并。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   joinrel —— 连接关系;
 *   outerrel —— 外层关系;
 *   innerrel —— 内层关系;
 *   jointype —— 连接类型;
 *   extra   —— JoinPathExtraData 上下文。
 * 【返回值】无。
 */
static void
match_unsorted_outer(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 JoinPathExtraData *extra)
{
	bool		nestjoinOK;
	bool		useallclauses;
	Path	   *inner_cheapest_total = innerrel->cheapest_total_path;
	Path	   *matpath = NULL;
	ListCell   *lc1;

	/*
	 * For now we do not support RIGHT_SEMI join in mergejoin or nestloop
	 * join.
	 */
	if (jointype == JOIN_RIGHT_SEMI)
		return;

	/*
	 * Nestloop only supports inner, left, semi, and anti joins.  Also, if we
	 * are doing a right, right-anti or full mergejoin, we must use *all* the
	 * mergeclauses as join clauses, else we will not have a valid plan.
	 * (Although these two flags are currently inverses, keep them separate
	 * for clarity and possible future changes.)
	 */
	switch (jointype)
	{
		case JOIN_INNER:
		case JOIN_LEFT:
		case JOIN_SEMI:
		case JOIN_ANTI:
			nestjoinOK = true;
			useallclauses = false;
			break;
		case JOIN_RIGHT:
		case JOIN_RIGHT_ANTI:
		case JOIN_FULL:
			nestjoinOK = false;
			useallclauses = true;
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) jointype);
			nestjoinOK = false; /* keep compiler quiet */
			useallclauses = false;
			break;
	}

	/*
	 * If inner_cheapest_total is parameterized by the outer rel, ignore it;
	 * we will consider it below as a member of cheapest_parameterized_paths,
	 * but the other possibilities considered in this routine aren't usable.
	 *
	 * Furthermore, if the inner side is a unique-ified relation, we cannot
	 * generate any valid paths here, because the inner rel's dependency on
	 * the outer rel makes unique-ification meaningless.
	 */
	if (PATH_PARAM_BY_REL(inner_cheapest_total, outerrel))
	{
		inner_cheapest_total = NULL;

		if (RELATION_WAS_MADE_UNIQUE(innerrel, extra->sjinfo, jointype))
			return;
	}

	if (nestjoinOK)
	{
		/*
		 * Consider materializing the cheapest inner path, unless that is
		 * disabled or the path in question materializes its output anyway.
		 *
		 * At present, we only consider materialization for non-partial outer
		 * paths, so it's correct to test PGS_CONSIDER_NONPARTIAL here. If we
		 * ever want to consider materialization for partial paths, we'll need
		 * to create matpath whenever PGS_NESTLOOP_MATERIALIZE is set, use it
		 * for partial paths either way, and use it for non-partial paths only
		 * when PGS_CONSIDER_NONPARTIAL is also set.
		 */
		if ((extra->pgs_mask &
			 (PGS_NESTLOOP_MATERIALIZE | PGS_CONSIDER_NONPARTIAL)) ==
			(PGS_NESTLOOP_MATERIALIZE | PGS_CONSIDER_NONPARTIAL) &&
			inner_cheapest_total != NULL &&
			!ExecMaterializesOutput(inner_cheapest_total->pathtype))
			matpath = (Path *)
				create_material_path(innerrel, inner_cheapest_total, true);
	}

	foreach(lc1, outerrel->pathlist)
	{
		Path	   *outerpath = (Path *) lfirst(lc1);
		List	   *merge_pathkeys;

		/*
		 * We cannot use an outer path that is parameterized by the inner rel.
		 */
		if (PATH_PARAM_BY_REL(outerpath, innerrel))
			continue;

		/*
		 * The result will have this sort order (even if it is implemented as
		 * a nestloop, and even if some of the mergeclauses are implemented by
		 * qpquals rather than as true mergeclauses):
		 */
		merge_pathkeys = build_join_pathkeys(root, joinrel, jointype,
											 outerpath->pathkeys);

		if (nestjoinOK)
		{
			/*
			 * Consider nestloop joins using this outer path and various
			 * available paths for the inner relation.  We consider the
			 * cheapest-total paths for each available parameterization of the
			 * inner relation, including the unparameterized case.
			 */
			ListCell   *lc2;

			foreach(lc2, innerrel->cheapest_parameterized_paths)
			{
				Path	   *innerpath = (Path *) lfirst(lc2);
				Path	   *mpath;

				try_nestloop_path(root,
								  joinrel,
								  outerpath,
								  innerpath,
								  merge_pathkeys,
								  jointype,
								  PGS_NESTLOOP_PLAIN,
								  extra);

				/*
				 * Try generating a memoize path and see if that makes the
				 * nested loop any cheaper.
				 */
				mpath = get_memoize_path(root, innerrel, outerrel,
										 innerpath, outerpath, jointype,
										 extra);
				if (mpath != NULL)
					try_nestloop_path(root,
									  joinrel,
									  outerpath,
									  mpath,
									  merge_pathkeys,
									  jointype,
									  PGS_NESTLOOP_MEMOIZE,
									  extra);
			}

			/* Also consider materialized form of the cheapest inner path */
			if (matpath != NULL)
				try_nestloop_path(root,
								  joinrel,
								  outerpath,
								  matpath,
								  merge_pathkeys,
								  jointype,
								  PGS_NESTLOOP_MATERIALIZE,
								  extra);
		}

		/* Can't do anything else if inner rel is parameterized by outer */
		if (inner_cheapest_total == NULL)
			continue;

		/* Generate merge join paths */
		generate_mergejoin_paths(root, joinrel, innerrel, outerpath,
								 jointype, extra, useallclauses,
								 inner_cheapest_total, merge_pathkeys,
								 false);
	}

	/*
	 * Consider partial nestloop and mergejoin plan if outerrel has any
	 * partial path and the joinrel is parallel-safe.  However, we can't
	 * handle joins needing lateral rels, since partial paths must not be
	 * parameterized.  Similarly, we can't handle JOIN_FULL, JOIN_RIGHT and
	 * JOIN_RIGHT_ANTI, because they can produce false null extended rows.
	 */
	if (joinrel->consider_parallel &&
		jointype != JOIN_FULL &&
		jointype != JOIN_RIGHT &&
		jointype != JOIN_RIGHT_ANTI &&
		outerrel->partial_pathlist != NIL &&
		bms_is_empty(joinrel->lateral_relids))
	{
		if (nestjoinOK)
			consider_parallel_nestloop(root, joinrel, outerrel, innerrel,
									   jointype, extra);

		/*
		 * If inner_cheapest_total is NULL or non parallel-safe then find the
		 * cheapest total parallel safe path.
		 */
		if (inner_cheapest_total == NULL ||
			!inner_cheapest_total->parallel_safe)
		{
			inner_cheapest_total =
				get_cheapest_parallel_safe_total_inner(innerrel->pathlist);
		}

		if (inner_cheapest_total)
			consider_parallel_mergejoin(root, joinrel, outerrel, innerrel,
										jointype, extra,
										inner_cheapest_total);
	}
}

/*
 * consider_parallel_mergejoin
 *	  Try to build partial paths for a joinrel by joining a partial path
 *	  for the outer relation to a complete path for the inner relation.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 * 'inner_cheapest_total' cheapest total path for innerrel
 */
/*
 * consider_parallel_mergejoin - (中文)尝试用并行外层 + 完整内层构建
 * partial 归并连接路径
 *
 * 【作用】match_unsorted_outer() 在 joinrel 并行安全时调用本函数:对外层
 * 关系的每条 partial 路径,调用 generate_mergejoin_paths()(is_partial 为
 * true)尝试构建并行归并路径。
 *
 * 【设计思想】并行归并的实现方式:外层用 partial 路径(各 worker 并行扫描
 * 各自的数据分片),内层用一条完整(非 partial)路径(每个 worker 各自执行
 * 同样的完整内层扫描),二者按归并键归并。每条外层 partial 路径都先计算其
 * 输出排序 merge_pathkeys,再交给 generate_mergejoin_paths() 用同一内层
 * 最便宜总代价路径 inner_cheapest_total 生成候选。
 *
 * 【参数】
 *   root               —— PlannerInfo;
 *   joinrel            —— 连接关系;
 *   outerrel           —— 外层关系;
 *   innerrel           —— 内层关系;
 *   jointype           —— 连接类型;
 *   extra              —— JoinPathExtraData 上下文;
 *   inner_cheapest_total —— 内层最便宜总代价路径(并行归并的内层基准)。
 * 【返回值】无。
 */
static void
consider_parallel_mergejoin(PlannerInfo *root,
							RelOptInfo *joinrel,
							RelOptInfo *outerrel,
							RelOptInfo *innerrel,
							JoinType jointype,
							JoinPathExtraData *extra,
							Path *inner_cheapest_total)
{
	ListCell   *lc1;

	/* generate merge join path for each partial outer path */
	foreach(lc1, outerrel->partial_pathlist)
	{
		Path	   *outerpath = (Path *) lfirst(lc1);
		List	   *merge_pathkeys;

		/*
		 * Figure out what useful ordering any paths we create will have.
		 */
		merge_pathkeys = build_join_pathkeys(root, joinrel, jointype,
											 outerpath->pathkeys);

		generate_mergejoin_paths(root, joinrel, innerrel, outerpath, jointype,
								 extra, false, inner_cheapest_total,
								 merge_pathkeys, true);
	}
}

/*
 * consider_parallel_nestloop
 *	  Try to build partial paths for a joinrel by joining a partial path for the
 *	  outer relation to a complete path for the inner relation.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 */
/*
 * consider_parallel_nestloop - (中文)尝试用并行外层 + 完整内层构建
 * partial 嵌套循环连接路径
 *
 * 【作用】match_unsorted_outer() 在 joinrel 并行安全时调用本函数:对外层
 * 关系的每条 partial 路径,遍历内层 cheapest_parameterized_paths 中并行
 * 安全的内层路径,尝试生成普通与 Memoize 两种 partial 嵌套循环路径,再尝试
 * 物化内层变体。
 *
 * 【设计思想】
 * - 内层 cheapest-total 路径满足"允许物化、并行安全、未被外层参数化、且
 *   输出未物化"时,预先创建 matpath(物化路径并行安全);
 * - 每条外层 partial 路径先用 build_join_pathkeys() 求输出排序;然后对每个
 *   并行安全的内层候选依次:跳过不合条件者交给 try_partial_nestloop_path()
 *   生成普通版本;再尝试 get_memoize_path() 生成 Memoize 版本交给
 *   try_partial_nestloop_path();最后尝试物化版本。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   joinrel —— 连接关系;
 *   outerrel —— 外层关系;
 *   innerrel —— 内层关系;
 *   jointype —— 连接类型;
 *   extra   —— JoinPathExtraData 上下文。
 * 【返回值】无。
 */
static void
consider_parallel_nestloop(PlannerInfo *root,
						   RelOptInfo *joinrel,
						   RelOptInfo *outerrel,
						   RelOptInfo *innerrel,
						   JoinType jointype,
						   JoinPathExtraData *extra)
{
	Path	   *inner_cheapest_total = innerrel->cheapest_total_path;
	Path	   *matpath = NULL;
	ListCell   *lc1;

	/*
	 * Consider materializing the cheapest inner path, unless: 1)
	 * materialization is disabled here, 2) the cheapest inner path is not
	 * parallel-safe, 3) the cheapest inner path is parameterized by the outer
	 * rel, or 4) the cheapest inner path materializes its output anyway.
	 */
	if ((extra->pgs_mask & PGS_NESTLOOP_MATERIALIZE) != 0 &&
		inner_cheapest_total->parallel_safe &&
		!PATH_PARAM_BY_REL(inner_cheapest_total, outerrel) &&
		!ExecMaterializesOutput(inner_cheapest_total->pathtype))
	{
		matpath = (Path *)
			create_material_path(innerrel, inner_cheapest_total, true);
		Assert(matpath->parallel_safe);
	}

	foreach(lc1, outerrel->partial_pathlist)
	{
		Path	   *outerpath = (Path *) lfirst(lc1);
		List	   *pathkeys;
		ListCell   *lc2;

		/* Figure out what useful ordering any paths we create will have. */
		pathkeys = build_join_pathkeys(root, joinrel, jointype,
									   outerpath->pathkeys);

		/*
		 * Try the cheapest parameterized paths; only those which will produce
		 * an unparameterized path when joined to this outerrel will survive
		 * try_partial_nestloop_path.  The cheapest unparameterized path is
		 * also in this list.
		 */
		foreach(lc2, innerrel->cheapest_parameterized_paths)
		{
			Path	   *innerpath = (Path *) lfirst(lc2);
			Path	   *mpath;

			/* Can't join to an inner path that is not parallel-safe */
			if (!innerpath->parallel_safe)
				continue;

			try_partial_nestloop_path(root, joinrel, outerpath, innerpath,
									  pathkeys, jointype,
									  PGS_NESTLOOP_PLAIN, extra);

			/*
			 * Try generating a memoize path and see if that makes the nested
			 * loop any cheaper.
			 */
			mpath = get_memoize_path(root, innerrel, outerrel,
									 innerpath, outerpath, jointype,
									 extra);
			if (mpath != NULL)
				try_partial_nestloop_path(root, joinrel, outerpath, mpath,
										  pathkeys, jointype,
										  PGS_NESTLOOP_MEMOIZE, extra);
		}

		/* Also consider materialized form of the cheapest inner path */
		if (matpath != NULL)
			try_partial_nestloop_path(root, joinrel, outerpath, matpath,
									  pathkeys, jointype,
									  PGS_NESTLOOP_MATERIALIZE, extra);
	}
}

/*
 * hash_inner_and_outer
 *	  Create hashjoin join paths by explicitly hashing both the outer and
 *	  inner keys of each available hash clause.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 */
/*
 * hash_inner_and_outer - (中文)用可哈希的连接子句生成哈希连接路径
 *
 * 【作用】add_paths_to_joinrel() 的第 4 步:扫描 restrictlist,找出对当前
 * (outer, inner) 关系组合可用的哈希连接子句,并据此构造哈希连接路径(含
 * 并行变体)。
 *
 * 【设计思想】
 * - 收集子句:外层连接时只取"自身专有、未下推"的子句(RINFO_IS_PUSHED_DOWN);
 *   子句必须 can_join 且 hashjoinoperator 有效;必须是 outer/inner 两侧
 *   恰好落在当前两个关系上(clause_sides_match_join);若子句是
 *   "inner op outer" 形式,其算子必须有可交换算子(createplan 的
 *   get_switched_clauses 会把它换成 outer 在左);
 * - 若无任何可用子句则什么都不做;
 * - 路径枚举:内层只用 cheapest_total;外层考虑 cheapest_startup 与所有
 *   cheapest_parameterized_paths(组合时跳过被另一侧参数化的路径,以及已经
 *   试过的 startup×total 组合);
 * - 并行变体:joinrel 并行安全、非 RIGHT_SEMI(共享/私有哈希表的 match 标志
 *   并发不安全)、有外层 partial 路径且无横向依赖时,尝试(1)并行构建共享
 *   哈希表(内层 partial,enable_parallel_hash);(2)每个进程复制完整内层
 *   建私有哈希表(FULL/RIGHT/RIGHT_ANTI 时禁止,因无人持有全部 match 位)。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   joinrel —— 连接关系;
 *   outerrel —— 外层关系;
 *   innerrel —— 内层关系;
 *   jointype —— 连接类型;
 *   extra   —— JoinPathExtraData 上下文(含 restrictlist)。
 * 【返回值】无。
 */
static void
hash_inner_and_outer(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 JoinPathExtraData *extra)
{
	bool		isouterjoin = IS_OUTER_JOIN(jointype);
	List	   *hashclauses;
	ListCell   *l;

	/*
	 * We need to build only one hashclauses list for any given pair of outer
	 * and inner relations; all of the hashable clauses will be used as keys.
	 *
	 * Scan the join's restrictinfo list to find hashjoinable clauses that are
	 * usable with this pair of sub-relations.
	 */
	hashclauses = NIL;
	foreach(l, extra->restrictlist)
	{
		RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(l);

		/*
		 * If processing an outer join, only use its own join clauses for
		 * hashing.  For inner joins we need not be so picky.
		 */
		if (isouterjoin && RINFO_IS_PUSHED_DOWN(restrictinfo, joinrel->relids))
			continue;

		if (!restrictinfo->can_join ||
			restrictinfo->hashjoinoperator == InvalidOid)
			continue;			/* not hashjoinable */

		/*
		 * Check if clause has the form "outer op inner" or "inner op outer".
		 */
		if (!clause_sides_match_join(restrictinfo, outerrel->relids,
									 innerrel->relids))
			continue;			/* no good for these input relations */

		/*
		 * If clause has the form "inner op outer", check if its operator has
		 * valid commutator.  This is necessary because hashclauses in this
		 * form will get commuted in createplan.c to put the outer var on the
		 * left (see get_switched_clauses).  This probably shouldn't ever
		 * fail, since hashable operators ought to have commutators, but be
		 * paranoid.
		 *
		 * The clause being hashjoinable indicates that it's an OpExpr.
		 */
		if (!restrictinfo->outer_is_left &&
			!OidIsValid(get_commutator(castNode(OpExpr, restrictinfo->clause)->opno)))
			continue;

		hashclauses = lappend(hashclauses, restrictinfo);
	}

	/* If we found any usable hashclauses, make paths */
	if (hashclauses)
	{
		/*
		 * We consider both the cheapest-total-cost and cheapest-startup-cost
		 * outer paths.  There's no need to consider any but the
		 * cheapest-total-cost inner path, however.
		 */
		Path	   *cheapest_startup_outer = outerrel->cheapest_startup_path;
		Path	   *cheapest_total_outer = outerrel->cheapest_total_path;
		Path	   *cheapest_total_inner = innerrel->cheapest_total_path;
		ListCell   *lc1;
		ListCell   *lc2;

		/*
		 * If either cheapest-total path is parameterized by the other rel, we
		 * can't use a hashjoin.  (There's no use looking for alternative
		 * input paths, since these should already be the least-parameterized
		 * available paths.)
		 */
		if (PATH_PARAM_BY_REL(cheapest_total_outer, innerrel) ||
			PATH_PARAM_BY_REL(cheapest_total_inner, outerrel))
			return;

		/*
		 * Consider the cheapest startup outer together with the cheapest
		 * total inner, and then consider pairings of cheapest-total paths
		 * including parameterized ones.  There is no use in generating
		 * parameterized paths on the basis of possibly cheap startup cost, so
		 * this is sufficient.
		 */
		if (cheapest_startup_outer != NULL)
			try_hashjoin_path(root,
							  joinrel,
							  cheapest_startup_outer,
							  cheapest_total_inner,
							  hashclauses,
							  jointype,
							  extra);

		foreach(lc1, outerrel->cheapest_parameterized_paths)
		{
			Path	   *outerpath = (Path *) lfirst(lc1);

			/*
			 * We cannot use an outer path that is parameterized by the inner
			 * rel.
			 */
			if (PATH_PARAM_BY_REL(outerpath, innerrel))
				continue;

			foreach(lc2, innerrel->cheapest_parameterized_paths)
			{
				Path	   *innerpath = (Path *) lfirst(lc2);

				/*
				 * We cannot use an inner path that is parameterized by the
				 * outer rel, either.
				 */
				if (PATH_PARAM_BY_REL(innerpath, outerrel))
					continue;

				if (outerpath == cheapest_startup_outer &&
					innerpath == cheapest_total_inner)
					continue;	/* already tried it */

				try_hashjoin_path(root,
								  joinrel,
								  outerpath,
								  innerpath,
								  hashclauses,
								  jointype,
								  extra);
			}
		}

		/*
		 * If the joinrel is parallel-safe, we may be able to consider a
		 * partial hash join.
		 *
		 * However, we can't handle JOIN_RIGHT_SEMI, because the hash table is
		 * either a shared hash table or a private hash table per backend.  In
		 * the shared case, there is no concurrency protection for the match
		 * flags, so multiple workers could inspect and set the flags
		 * concurrently, potentially producing incorrect results.  In the
		 * private case, each worker has its own copy of the hash table, so no
		 * single process has all the match flags.
		 *
		 * Also, the resulting path must not be parameterized.
		 */
		if (joinrel->consider_parallel &&
			jointype != JOIN_RIGHT_SEMI &&
			outerrel->partial_pathlist != NIL &&
			bms_is_empty(joinrel->lateral_relids))
		{
			Path	   *cheapest_partial_outer;
			Path	   *cheapest_partial_inner = NULL;
			Path	   *cheapest_safe_inner = NULL;

			cheapest_partial_outer =
				(Path *) linitial(outerrel->partial_pathlist);

			/*
			 * Can we use a partial inner plan too, so that we can build a
			 * shared hash table in parallel?
			 */
			if (innerrel->partial_pathlist != NIL &&
				enable_parallel_hash)
			{
				cheapest_partial_inner =
					(Path *) linitial(innerrel->partial_pathlist);
				try_partial_hashjoin_path(root, joinrel,
										  cheapest_partial_outer,
										  cheapest_partial_inner,
										  hashclauses, jointype, extra,
										  true /* parallel_hash */ );
			}

			/*
			 * Normally, given that the joinrel is parallel-safe, the cheapest
			 * total inner path will also be parallel-safe, but if not, we'll
			 * have to search for the cheapest safe, unparameterized inner
			 * path.  If full, right, or right-anti join, we can't use
			 * parallelism (building the hash table in each backend) because
			 * no one process has all the match bits.
			 */
			if (jointype == JOIN_FULL ||
				jointype == JOIN_RIGHT ||
				jointype == JOIN_RIGHT_ANTI)
				cheapest_safe_inner = NULL;
			else if (cheapest_total_inner->parallel_safe)
				cheapest_safe_inner = cheapest_total_inner;
			else
				cheapest_safe_inner =
					get_cheapest_parallel_safe_total_inner(innerrel->pathlist);

			if (cheapest_safe_inner != NULL)
				try_partial_hashjoin_path(root, joinrel,
										  cheapest_partial_outer,
										  cheapest_safe_inner,
										  hashclauses, jointype, extra,
										  false /* parallel_hash */ );
		}
	}
}

/*
 * select_mergejoin_clauses
 *	  Select mergejoin clauses that are usable for a particular join.
 *	  Returns a list of RestrictInfo nodes for those clauses.
 *
 * *mergejoin_allowed is normally set to true, but it is set to false if
 * this is a right-semi join, or this is a right/right-anti/full join and
 * there are nonmergejoinable join clauses.  The executor's mergejoin
 * machinery cannot handle such cases, so we have to avoid generating a
 * mergejoin plan.  (Note that this flag does NOT consider whether there are
 * actually any mergejoinable clauses.  This is correct because in some
 * cases we need to build a clauseless mergejoin.  Simply returning NIL is
 * therefore not enough to distinguish safe from unsafe cases.)
 *
 * We also mark each selected RestrictInfo to show which side is currently
 * being considered as outer.  These are transient markings that are only
 * good for the duration of the current add_paths_to_joinrel() call!
 *
 * We examine each restrictinfo clause known for the join to see
 * if it is mergejoinable and involves vars from the two sub-relations
 * currently of interest.
 */
/*
 * select_mergejoin_clauses - (中文)挑选可用于本次连接的归并连接子句
 *
 * 【作用】add_paths_to_joinrel() 在需要归并时调用本函数,从 restrictlist
 * 中挑出对当前 (outer, inner) 组合可用、且可归并的子句,返回 RestrictInfo
 * 列表。同时通过 *mergejoin_allowed 报告"本次连接整体上是否允许使用归并
 * 连接"。
 *
 * 【设计思想】
 * - RIGHT_SEMI 暂不支持归并,直接置 *mergejoin_allowed = false;
 * - 外层连接时只用自身专有(未下推)的子句,下推子句将来作为 otherquals;
 * - 逐条检查:必须 can_join 且有 mergeopfamilies;两侧 relids 必须恰好对应
 *   outer/inner(clause_sides_match_join);"inner op outer" 形式算子必须有
 *   可交换算子;两侧等价类都不得是"必冗余"的 EC(EC_MUST_BE_REDUNDANT,
 *   冗余 EC 不能出现在规范路径键中);
 * - 关键副作用:对每条合格子句调用 update_mergeclause_eclasses(),使
 *   left_ec / right_ec 指向规范 EC,并把 outer_is_left 标记为当前外层一侧
 *   ——这些是本次 add_paths_to_joinrel() 调用期间的临时标记;
 * - 归并可用性:*mergejoin_allowed 只在 RIGHT/RIGHT_ANTI/FULL 时才可能为
 *   false(当存在"非常量且不可归并"的连接子句时),因为执行器对这类连接
 *   要求所有非归并子句必须是常量(FULL JOIN ON FALSE 的情形);注意该标志
 *   与"是否存在归并子句"无关——某些情况(如 x FULL JOIN y ON true)需要
 *   构建无子句的归并连接,返回 NIL 并不等于"不安全"。
 *
 * 【参数】
 *   root              —— PlannerInfo;
 *   joinrel           —— 连接关系;
 *   outerrel          —— 外层关系;
 *   innerrel          —— 内层关系;
 *   restrictlist      —— 本次连接的子句列表;
 *   jointype          —— 连接类型;
 *   mergejoin_allowed —— 出参:本次连接是否允许生成归并连接计划。
 * 【返回值】可归并子句的 RestrictInfo 列表(可能为空)。
 */
static List *
select_mergejoin_clauses(PlannerInfo *root,
						 RelOptInfo *joinrel,
						 RelOptInfo *outerrel,
						 RelOptInfo *innerrel,
						 List *restrictlist,
						 JoinType jointype,
						 bool *mergejoin_allowed)
{
	List	   *result_list = NIL;
	bool		isouterjoin = IS_OUTER_JOIN(jointype);
	bool		have_nonmergeable_joinclause = false;
	ListCell   *l;

	/*
	 * For now we do not support RIGHT_SEMI join in mergejoin: the benefit of
	 * swapping inputs tends to be small here.
	 */
	if (jointype == JOIN_RIGHT_SEMI)
	{
		*mergejoin_allowed = false;
		return NIL;
	}

	foreach(l, restrictlist)
	{
		RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(l);

		/*
		 * If processing an outer join, only use its own join clauses in the
		 * merge.  For inner joins we can use pushed-down clauses too. (Note:
		 * we don't set have_nonmergeable_joinclause here because pushed-down
		 * clauses will become otherquals not joinquals.)
		 */
		if (isouterjoin && RINFO_IS_PUSHED_DOWN(restrictinfo, joinrel->relids))
			continue;

		/* Check that clause is a mergeable operator clause */
		if (!restrictinfo->can_join ||
			restrictinfo->mergeopfamilies == NIL)
		{
			/*
			 * The executor can handle extra joinquals that are constants, but
			 * not anything else, when doing right/right-anti/full merge join.
			 * (The reason to support constants is so we can do FULL JOIN ON
			 * FALSE.)
			 */
			if (!restrictinfo->clause || !IsA(restrictinfo->clause, Const))
				have_nonmergeable_joinclause = true;
			continue;			/* not mergejoinable */
		}

		/*
		 * Check if clause has the form "outer op inner" or "inner op outer".
		 */
		if (!clause_sides_match_join(restrictinfo, outerrel->relids,
									 innerrel->relids))
		{
			have_nonmergeable_joinclause = true;
			continue;			/* no good for these input relations */
		}

		/*
		 * If clause has the form "inner op outer", check if its operator has
		 * valid commutator.  This is necessary because mergejoin clauses in
		 * this form will get commuted in createplan.c to put the outer var on
		 * the left (see get_switched_clauses).  This probably shouldn't ever
		 * fail, since mergejoinable operators ought to have commutators, but
		 * be paranoid.
		 *
		 * The clause being mergejoinable indicates that it's an OpExpr.
		 */
		if (!restrictinfo->outer_is_left &&
			!OidIsValid(get_commutator(castNode(OpExpr, restrictinfo->clause)->opno)))
		{
			have_nonmergeable_joinclause = true;
			continue;
		}

		/*
		 * Insist that each side have a non-redundant eclass.  This
		 * restriction is needed because various bits of the planner expect
		 * that each clause in a merge be associable with some pathkey in a
		 * canonical pathkey list, but redundant eclasses can't appear in
		 * canonical sort orderings.  (XXX it might be worth relaxing this,
		 * but not enough time to address it for 8.3.)
		 */
		update_mergeclause_eclasses(root, restrictinfo);

		if (EC_MUST_BE_REDUNDANT(restrictinfo->left_ec) ||
			EC_MUST_BE_REDUNDANT(restrictinfo->right_ec))
		{
			have_nonmergeable_joinclause = true;
			continue;			/* can't handle redundant eclasses */
		}

		result_list = lappend(result_list, restrictinfo);
	}

	/*
	 * Report whether mergejoin is allowed (see comment at top of function).
	 */
	switch (jointype)
	{
		case JOIN_RIGHT:
		case JOIN_RIGHT_ANTI:
		case JOIN_FULL:
			*mergejoin_allowed = !have_nonmergeable_joinclause;
			break;
		default:
			*mergejoin_allowed = true;
			break;
	}

	return result_list;
}
