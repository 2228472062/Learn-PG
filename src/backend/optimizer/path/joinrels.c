/*-------------------------------------------------------------------------
 *
 * joinrels.c
 *	  Routines to determine which relations should be joined
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本模块(joinrels.c)负责决定"哪些关系应该被连接",即连接关系(joinrel)
 * 的发现与构建。它是规划器动态规划搜索(standard_join_search)中"自底向上
 * 枚举连接组合"的一层:给定当前级别 level,把较低级别的 RelOptInfo 两两
 * 组合出恰好包含 level 个基表的新 RelOptInfo,并为每个新 joinrel 填充路径。
 *
 * 【职责】
 * - join_search_one_level():每一层连接搜索的顶层入口,先做左/右线性连接
 *   (level-1 关系的连接),再做 2 <= k <= level/2 的 bushy 连接,最后兜底
 *   强制生成笛卡尔积;
 * - 通过 make_join_rel() 先验证连接是否合法(join_is_legal 依据
 *   SpecialJoinInfo 判断外层连接语义、LATERAL 引用等约束),再构建/复用
 *   joinrel,计算 restrictlist,并依次调用 make_grouped_join_rel() 与
 *   populate_joinrel_with_paths();
 * - populate_joinrel_with_paths():按连接类型(INNER/LEFT/FULL/SEMI/ANTI)
 *   处理 dummy 关系与"常量 FALSE"限制的剪枝,再以两个方向调用 joinpath.c
 *   的 add_paths_to_joinrel() 生成路径;最后尝试分区剪枝下的
 *   partitionwise join(try_partitionwise_join());
 * - 提供 join 顺序约束检测:have_join_order_restriction()、
 *   has_join_restriction()、has_legal_joinclause();
 * - 提供"关系已证明为空"的判定与标记:is_dummy_rel() / mark_dummy_rel();
 * - 支持 eager aggregation(make_grouped_join_rel)与分区连接
 *   (try_partitionwise_join 及其子函数)。
 *
 * 【设计思想】
 * - 动态规划记忆化:同一组基表可能被多种顺序组合出来,但 joinrel 是唯一
 *   的(以 join_rel_level[level] 列表去重),后续组合只会在已存在的 joinrel
 *   上追加路径;
 * - 连接合法性检查是正确性关键:外层连接不可任意交换输入,半连接可通过对
 *   RHS 做 unique 化放宽顺序(join_is_legal 的 unique_ified 分支);
 * - 用 join_cur_level 记录当前层,使新 joinrel 自动加入正确的层列表。
 *
 * 【核心数据结构】RelOptInfo(连接关系)、SpecialJoinInfo(连接语义)、
 * join_rel_level(每层的关系列表)。
 *
 * 本文件与 joinpath.c(为 joinrel 生成路径)、pathnode.c(build_join_rel /
 * create_*_path)、joininfo.c、equivclass.c(等价类)、appendinfo.c
 * (分区子表映射)紧密配合。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/path/joinrels.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "miscadmin.h"
#include "optimizer/appendinfo.h"
#include "optimizer/cost.h"
#include "optimizer/joininfo.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/planner.h"
#include "partitioning/partbounds.h"
#include "utils/memutils.h"


static void make_rels_by_clause_joins(PlannerInfo *root,
									  RelOptInfo *old_rel,
									  List *other_rels,
									  int first_rel_idx);
static void make_rels_by_clauseless_joins(PlannerInfo *root,
										  RelOptInfo *old_rel,
										  List *other_rels);
static bool has_join_restriction(PlannerInfo *root, RelOptInfo *rel);
static bool has_legal_joinclause(PlannerInfo *root, RelOptInfo *rel);
static bool restriction_is_constant_false(List *restrictlist,
										  RelOptInfo *joinrel,
										  bool only_pushed_down);
static void make_grouped_join_rel(PlannerInfo *root, RelOptInfo *rel1,
								  RelOptInfo *rel2, RelOptInfo *joinrel,
								  SpecialJoinInfo *sjinfo, List *restrictlist);
static void populate_joinrel_with_paths(PlannerInfo *root, RelOptInfo *rel1,
										RelOptInfo *rel2, RelOptInfo *joinrel,
										SpecialJoinInfo *sjinfo, List *restrictlist);
static void try_partitionwise_join(PlannerInfo *root, RelOptInfo *rel1,
								   RelOptInfo *rel2, RelOptInfo *joinrel,
								   SpecialJoinInfo *parent_sjinfo,
								   List *parent_restrictlist);
static SpecialJoinInfo *build_child_join_sjinfo(PlannerInfo *root,
												SpecialJoinInfo *parent_sjinfo,
												Relids left_relids, Relids right_relids);
static void free_child_join_sjinfo(SpecialJoinInfo *child_sjinfo,
								   SpecialJoinInfo *parent_sjinfo);
static void compute_partition_bounds(PlannerInfo *root, RelOptInfo *rel1,
									 RelOptInfo *rel2, RelOptInfo *joinrel,
									 SpecialJoinInfo *parent_sjinfo,
									 List **parts1, List **parts2);
static void get_matching_part_pairs(PlannerInfo *root, RelOptInfo *joinrel,
									RelOptInfo *rel1, RelOptInfo *rel2,
									List **parts1, List **parts2);


/*
 * join_search_one_level
 *	  Consider ways to produce join relations containing exactly 'level'
 *	  jointree items.  (This is one step of the dynamic-programming method
 *	  embodied in standard_join_search.)  Join rel nodes for each feasible
 *	  combination of lower-level rels are created and returned in a list.
 *	  Implementation paths are created for each such joinrel, too.
 *
 * level: level of rels we want to make this time
 * root->join_rel_level[j], 1 <= j < level, is a list of rels containing j items
 *
 * The result is returned in root->join_rel_level[level].
 */
/*
 * join_search_one_level - (中文)搜索并构建恰好包含 level 个 jointree 项的
 * 所有连接关系(动态规划的一步)
 *
 * 【作用】standard_join_search() 对 level = 2, 3, ... 逐层调用本函数,考虑
 * 所有产生"含 level 个基表"连接关系的方式,创建相应 joinrel 及其实现路径,
 * 结果放入 root->join_rel_level[level]。这是 joinrels.c 的顶层入口,也是
 * GEQO 之外的标准连接搜索的核心。
 *
 * 【设计思想】三个阶段:
 * 1. 左/右线性连接:把 level-1 层的每个关系与初始关系(joinrels[1])连接;
 *    若该关系有连接子句、等价类连接或连接顺序限制,只与存在子句/限制的
 *    初始关系连接(make_rels_by_clause_joins);否则生成笛卡尔积
 *    (make_rels_by_clauseless_joins)。level 2 时对称性使只用"当前项之后"
 *    的初始关系即可(first_rel = foreach_current_index(r) + 1),因为镜像
 *    组合由 make_join_rel 自动处理;
 * 2. bushy 连接:对 2 <= k <= level-2,把 k 个与 level-k 个基表的关系两两
 *    连接,只处理到中点(k > other_level 时 break,利用对称性);只有存在
 *    相关连接子句或连接顺序限制时才组合,避免规划时间爆炸;
 * 3. 兜底笛卡尔积:若上述两步未生成任何 level 层关系(例如某个子问题里
 *    所有子句都指向子问题之外),强制对 level-1 层每个关系做笛卡尔积;
 *    若仍失败且无特殊连接、无 LATERAL,则报错(理论上不应发生)。
 * 每步都维护 root->join_cur_level = level,使 build_join_rel 创建的新
 * joinrel 自动落入正确的层列表。
 *
 * 【参数】
 *   root  —— PlannerInfo(其 join_rel_level 数组按层存放关系列表);
 *   level —— 本层要构建的关系大小(含基表个数)。
 * 【返回值】无(结果写入 root->join_rel_level[level])。
 */
void
join_search_one_level(PlannerInfo *root, int level)
{
	List	  **joinrels = root->join_rel_level;
	ListCell   *r;
	int			k;

	Assert(joinrels[level] == NIL);

	/* Set join_cur_level so that new joinrels are added to proper list */
	root->join_cur_level = level;

	/*
	 * First, consider left-sided and right-sided plans, in which rels of
	 * exactly level-1 member relations are joined against initial relations.
	 * We prefer to join using join clauses, but if we find a rel of level-1
	 * members that has no join clauses, we will generate Cartesian-product
	 * joins against all initial rels not already contained in it.
	 */
	foreach(r, joinrels[level - 1])
	{
		RelOptInfo *old_rel = (RelOptInfo *) lfirst(r);

		if (old_rel->joininfo != NIL || old_rel->has_eclass_joins ||
			has_join_restriction(root, old_rel))
		{
			int			first_rel;

			/*
			 * There are join clauses or join order restrictions relevant to
			 * this rel, so consider joins between this rel and (only) those
			 * initial rels it is linked to by a clause or restriction.
			 *
			 * At level 2 this condition is symmetric, so there is no need to
			 * look at initial rels before this one in the list; we already
			 * considered such joins when we were at the earlier rel.  (The
			 * mirror-image joins are handled automatically by make_join_rel.)
			 * In later passes (level > 2), we join rels of the previous level
			 * to each initial rel they don't already include but have a join
			 * clause or restriction with.
			 */
			if (level == 2)		/* consider remaining initial rels */
				first_rel = foreach_current_index(r) + 1;
			else
				first_rel = 0;

			make_rels_by_clause_joins(root, old_rel, joinrels[1], first_rel);
		}
		else
		{
			/*
			 * Oops, we have a relation that is not joined to any other
			 * relation, either directly or by join-order restrictions.
			 * Cartesian product time.
			 *
			 * We consider a cartesian product with each not-already-included
			 * initial rel, whether it has other join clauses or not.  At
			 * level 2, if there are two or more clauseless initial rels, we
			 * will redundantly consider joining them in both directions; but
			 * such cases aren't common enough to justify adding complexity to
			 * avoid the duplicated effort.
			 */
			make_rels_by_clauseless_joins(root,
										  old_rel,
										  joinrels[1]);
		}
	}

	/*
	 * Now, consider "bushy plans" in which relations of k initial rels are
	 * joined to relations of level-k initial rels, for 2 <= k <= level-2.
	 *
	 * We only consider bushy-plan joins for pairs of rels where there is a
	 * suitable join clause (or join order restriction), in order to avoid
	 * unreasonable growth of planning time.
	 */
	for (k = 2;; k++)
	{
		int			other_level = level - k;

		/*
		 * Since make_join_rel(x, y) handles both x,y and y,x cases, we only
		 * need to go as far as the halfway point.
		 */
		if (k > other_level)
			break;

		foreach(r, joinrels[k])
		{
			RelOptInfo *old_rel = (RelOptInfo *) lfirst(r);
			int			first_rel;
			ListCell   *r2;

			/*
			 * We can ignore relations without join clauses here, unless they
			 * participate in join-order restrictions --- then we might have
			 * to force a bushy join plan.
			 */
			if (old_rel->joininfo == NIL && !old_rel->has_eclass_joins &&
				!has_join_restriction(root, old_rel))
				continue;

			if (k == other_level)	/* only consider remaining rels */
				first_rel = foreach_current_index(r) + 1;
			else
				first_rel = 0;

			for_each_from(r2, joinrels[other_level], first_rel)
			{
				RelOptInfo *new_rel = (RelOptInfo *) lfirst(r2);

				if (!bms_overlap(old_rel->relids, new_rel->relids))
				{
					/*
					 * OK, we can build a rel of the right level from this
					 * pair of rels.  Do so if there is at least one relevant
					 * join clause or join order restriction.
					 */
					if (have_relevant_joinclause(root, old_rel, new_rel) ||
						have_join_order_restriction(root, old_rel, new_rel))
					{
						(void) make_join_rel(root, old_rel, new_rel);
					}
				}
			}
		}
	}

	/*----------
	 * Last-ditch effort: if we failed to find any usable joins so far, force
	 * a set of cartesian-product joins to be generated.  This handles the
	 * special case where all the available rels have join clauses but we
	 * cannot use any of those clauses yet.  This can only happen when we are
	 * considering a join sub-problem (a sub-joinlist) and all the rels in the
	 * sub-problem have only join clauses with rels outside the sub-problem.
	 * An example is
	 *
	 *		SELECT ... FROM a INNER JOIN b ON TRUE, c, d, ...
	 *		WHERE a.w = c.x and b.y = d.z;
	 *
	 * If the "a INNER JOIN b" sub-problem does not get flattened into the
	 * upper level, we must be willing to make a cartesian join of a and b;
	 * but the code above will not have done so, because it thought that both
	 * a and b have joinclauses.  We consider only left-sided and right-sided
	 * cartesian joins in this case (no bushy).
	 *----------
	 */
	if (joinrels[level] == NIL)
	{
		/*
		 * This loop is just like the first one, except we always call
		 * make_rels_by_clauseless_joins().
		 */
		foreach(r, joinrels[level - 1])
		{
			RelOptInfo *old_rel = (RelOptInfo *) lfirst(r);

			make_rels_by_clauseless_joins(root,
										  old_rel,
										  joinrels[1]);
		}

		/*----------
		 * When special joins are involved, there may be no legal way
		 * to make an N-way join for some values of N.  For example consider
		 *
		 * SELECT ... FROM t1 WHERE
		 *	 x IN (SELECT ... FROM t2,t3 WHERE ...) AND
		 *	 y IN (SELECT ... FROM t4,t5 WHERE ...)
		 *
		 * We will flatten this query to a 5-way join problem, but there are
		 * no 4-way joins that join_is_legal() will consider legal.  We have
		 * to accept failure at level 4 and go on to discover a workable
		 * bushy plan at level 5.
		 *
		 * However, if there are no special joins and no lateral references
		 * then join_is_legal() should never fail, and so the following sanity
		 * check is useful.
		 *----------
		 */
		if (joinrels[level] == NIL &&
			root->join_info_list == NIL &&
			!root->hasLateralRTEs)
			elog(ERROR, "failed to build any %d-way joins", level);
	}
}

/*
 * make_rels_by_clause_joins
 *	  Build joins between the given relation 'old_rel' and other relations
 *	  that participate in join clauses that 'old_rel' also participates in
 *	  (or participate in join-order restrictions with it).
 *	  The join rels are returned in root->join_rel_level[join_cur_level].
 *
 * Note: at levels above 2 we will generate the same joined relation in
 * multiple ways --- for example (a join b) join c is the same RelOptInfo as
 * (b join c) join a, though the second case will add a different set of Paths
 * to it.  This is the reason for using the join_rel_level mechanism, which
 * automatically ensures that each new joinrel is only added to the list once.
 *
 * 'old_rel' is the relation entry for the relation to be joined
 * 'other_rels': a list containing the other rels to be considered for joining
 * 'first_rel_idx': the first rel to be considered in 'other_rels'
 *
 * Currently, this is only used with initial rels in other_rels, but it
 * will work for joining to joinrels too.
 */
/*
 * make_rels_by_clause_joins - (中文)把给定关系与"有连接子句/顺序限制的
 * 其他关系"逐个构建连接关系
 *
 * 【作用】join_search_one_level() 在线性连接阶段,对每个带连接子句或
 * 顺序限制的 old_rel 调用本函数:从 other_rels 中(从 first_rel_idx 起)
 * 找出与 old_rel 无重叠、且存在相关连接子句或有连接顺序限制的其他关系,
 * 逐个调用 make_join_rel() 构建连接关系。
 *
 * 【设计思想】
 * - 过滤条件:relids 不重叠(不能自连接),且
 *   have_relevant_joinclause() 或 have_join_order_restriction() 至少其一
 *   为真——没有子句/限制时本就不该走这条路径;
 * - first_rel_idx 用于 level 2 的对称剪枝:跳过列表前面的关系,因为反向
 *   组合已经处理过;
 * - 生成的新 joinrel 会经由 make_join_rel → build_join_rel 自动加入
 *   root->join_rel_level[join_cur_level]。
 *
 * 【参数】
 *   root         —— PlannerInfo;
 *   old_rel      —— 待连接的关系;
 *   other_rels   —— 候选其他关系列表;
 *   first_rel_idx —— 从 other_rels 中开始考虑的下标(跳过已处理者)。
 * 【返回值】无。
 */
static void
make_rels_by_clause_joins(PlannerInfo *root,
						  RelOptInfo *old_rel,
						  List *other_rels,
						  int first_rel_idx)
{
	ListCell   *l;

	for_each_from(l, other_rels, first_rel_idx)
	{
		RelOptInfo *other_rel = (RelOptInfo *) lfirst(l);

		if (!bms_overlap(old_rel->relids, other_rel->relids) &&
			(have_relevant_joinclause(root, old_rel, other_rel) ||
			 have_join_order_restriction(root, old_rel, other_rel)))
		{
			(void) make_join_rel(root, old_rel, other_rel);
		}
	}
}

/*
 * make_rels_by_clauseless_joins
 *	  Given a relation 'old_rel' and a list of other relations
 *	  'other_rels', create a join relation between 'old_rel' and each
 *	  member of 'other_rels' that isn't already included in 'old_rel'.
 *	  The join rels are returned in root->join_rel_level[join_cur_level].
 *
 * 'old_rel' is the relation entry for the relation to be joined
 * 'other_rels': a list containing the other rels to be considered for joining
 *
 * Currently, this is only used with initial rels in other_rels, but it would
 * work for joining to joinrels too.
 */
/*
 * make_rels_by_clauseless_joins - (中文)把给定关系与所有未包含的其他关系
 * 构建笛卡尔积连接关系
 *
 * 【作用】join_search_one_level() 对"无任何连接子句/顺序限制"的关系,以及
 * 兜底阶段的全部关系调用本函数:把 old_rel 与 other_rels 中每个 relids 不
 * 重叠的关系都做一次 make_join_rel()(即笛卡尔积连接),尽力避免遗漏任何
 * 可行计划。
 *
 * 【设计思想】这是最宽松的搜索:不做任何子句过滤,只要 relids 不重叠就
 * 尝试连接。level 2 时若存在多个无子句的初始关系,可能在两个方向上重复
 * 尝试(不过这类情形不常见,不值得为此增加复杂度去去重)。生成的 joinrel
 * 仍由 make_join_rel 负责合法性检查与路径填充。
 *
 * 【参数】
 *   root       —— PlannerInfo;
 *   old_rel    —— 待连接的关系;
 *   other_rels —— 候选其他关系列表。
 * 【返回值】无。
 */
static void
make_rels_by_clauseless_joins(PlannerInfo *root,
							  RelOptInfo *old_rel,
							  List *other_rels)
{
	ListCell   *l;

	foreach(l, other_rels)
	{
		RelOptInfo *other_rel = (RelOptInfo *) lfirst(l);

		if (!bms_overlap(other_rel->relids, old_rel->relids))
		{
			(void) make_join_rel(root, old_rel, other_rel);
		}
	}
}


/*
 * join_is_legal
 *	   Determine whether a proposed join is legal given the query's
 *	   join order constraints; and if it is, determine the join type.
 *
 * Caller must supply not only the two rels, but the union of their relids.
 * (We could simplify the API by computing joinrelids locally, but this
 * would be redundant work in the normal path through make_join_rel.
 * Note that this value does NOT include the RT index of any outer join that
 * might need to be performed here, so it's not the canonical identifier
 * of the join relation.)
 *
 * On success, *sjinfo_p is set to NULL if this is to be a plain inner join,
 * else it's set to point to the associated SpecialJoinInfo node.  Also,
 * *reversed_p is set true if the given relations need to be swapped to
 * match the SpecialJoinInfo node.
 */
/*
 * join_is_legal - (中文)判断一个候选连接是否合法,并确定其连接类型
 *
 * 【作用】make_join_rel() 在构建 joinrel 之前调用本函数:根据查询的连接
 * 顺序约束(尤其是外层连接 SpecialJoinInfo 与 LATERAL 引用)判断 rel1 与
 * rel2 的连接是否允许。合法时返回 true,并通过 *sjinfo_p 给出对应的
 * SpecialJoinInfo(纯内连接时为 NULL)、通过 *reversed_p 说明是否需要交换
 * rel1/rel2 以匹配该 SJ 的左右手侧。
 *
 * 【设计思想】逐条扫描 root->join_info_list,对每个与候选连接有关的 SJ
 * (其 RHS 与 joinrelids 有交集、候选连接未被 RHS 完全包含、SJ 也未在任一
 * 输入内完成)分情形判定:
 * - rel1 含其 min_lefthand 且 rel2 含其 min_righthand(或反序):可以在本
 *   连接实现该 SJ,记下 match_sjinfo 与 reversed;若匹配到两个 SJ 则非法;
 * - SEMI 且某输入恰好等于 syn_righthand 且可 unique 化:通过对 RHS 做
 *   unique 化把半连接降级为内连接,放宽连接顺序(如 C 较小可先与 A 连、
 *   再与 B 连),记 unique_ified;
 * - 其余情形:SJ 的 RHS 已被部分违反。若两个输入都与 RHS 有交集,视为
 *   此前已被允许的违规,继续;否则只有该 SJ 是 LEFT 且候选连接不触及 LHS
 *   时才可能"并入其 RHS",并置 must_be_leftjoin 要求随后匹配的 SJ 必须是
 *   LEFT 且 lhs_strict(本质对应外层连接恒等式 3);
 * - LATERAL 检查:两个输入互相横向引用则非法;单向引用必须用嵌套循环实现
 *   (匹配的 SJ 不得是 FULL / reversed / unique_ified 情形)且必须是直接
 *   引用(间接引用拒绝);最后用 min_join_parameterization() 计算连接最小
 *   参数化,若其中某个关系会落到某个外层连接的 RHS 内侧(不可连接),非法。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   rel1, rel2  —— 候选连接的两个输入关系;
 *   joinrelids  —— 两者的 relids 并集(不含可能需在此执行的外层连接 RT 索引);
 *   sjinfo_p    —— 出参:关联的 SpecialJoinInfo(纯内连接为 NULL);
 *   reversed_p  —— 出参:是否需要交换 rel1/rel2 以匹配 SJ。
 * 【返回值】true:连接合法;false:非法(调用方应放弃该连接路径)。
 */
static bool
join_is_legal(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2,
			  Relids joinrelids,
			  SpecialJoinInfo **sjinfo_p, bool *reversed_p)
{
	SpecialJoinInfo *match_sjinfo;
	bool		reversed;
	bool		unique_ified;
	bool		must_be_leftjoin;
	ListCell   *l;

	/*
	 * Ensure output params are set on failure return.  This is just to
	 * suppress uninitialized-variable warnings from overly anal compilers.
	 */
	*sjinfo_p = NULL;
	*reversed_p = false;

	/*
	 * If we have any special joins, the proposed join might be illegal; and
	 * in any case we have to determine its join type.  Scan the join info
	 * list for matches and conflicts.
	 */
	match_sjinfo = NULL;
	reversed = false;
	unique_ified = false;
	must_be_leftjoin = false;

	foreach(l, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(l);

		/*
		 * This special join is not relevant unless its RHS overlaps the
		 * proposed join.  (Check this first as a fast path for dismissing
		 * most irrelevant SJs quickly.)
		 */
		if (!bms_overlap(sjinfo->min_righthand, joinrelids))
			continue;

		/*
		 * Also, not relevant if proposed join is fully contained within RHS
		 * (ie, we're still building up the RHS).
		 */
		if (bms_is_subset(joinrelids, sjinfo->min_righthand))
			continue;

		/*
		 * Also, not relevant if SJ is already done within either input.
		 */
		if (bms_is_subset(sjinfo->min_lefthand, rel1->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel1->relids))
			continue;
		if (bms_is_subset(sjinfo->min_lefthand, rel2->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel2->relids))
			continue;

		/*
		 * If it's a semijoin and we already joined the RHS to any other rels
		 * within either input, then we must have unique-ified the RHS at that
		 * point (see below).  Therefore the semijoin is no longer relevant in
		 * this join path.
		 */
		if (sjinfo->jointype == JOIN_SEMI)
		{
			if (bms_is_subset(sjinfo->syn_righthand, rel1->relids) &&
				!bms_equal(sjinfo->syn_righthand, rel1->relids))
				continue;
			if (bms_is_subset(sjinfo->syn_righthand, rel2->relids) &&
				!bms_equal(sjinfo->syn_righthand, rel2->relids))
				continue;
		}

		/*
		 * If one input contains min_lefthand and the other contains
		 * min_righthand, then we can perform the SJ at this join.
		 *
		 * Reject if we get matches to more than one SJ; that implies we're
		 * considering something that's not really valid.
		 */
		if (bms_is_subset(sjinfo->min_lefthand, rel1->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel2->relids))
		{
			if (match_sjinfo)
				return false;	/* invalid join path */
			match_sjinfo = sjinfo;
			reversed = false;
		}
		else if (bms_is_subset(sjinfo->min_lefthand, rel2->relids) &&
				 bms_is_subset(sjinfo->min_righthand, rel1->relids))
		{
			if (match_sjinfo)
				return false;	/* invalid join path */
			match_sjinfo = sjinfo;
			reversed = true;
		}
		else if (sjinfo->jointype == JOIN_SEMI &&
				 bms_equal(sjinfo->syn_righthand, rel2->relids) &&
				 create_unique_paths(root, rel2, sjinfo) != NULL)
		{
			/*----------
			 * For a semijoin, we can join the RHS to anything else by
			 * unique-ifying the RHS (if the RHS can be unique-ified).
			 * We will only get here if we have the full RHS but less
			 * than min_lefthand on the LHS.
			 *
			 * The reason to consider such a join path is exemplified by
			 *	SELECT ... FROM a,b WHERE (a.x,b.y) IN (SELECT c1,c2 FROM c)
			 * If we insist on doing this as a semijoin we will first have
			 * to form the cartesian product of A*B.  But if we unique-ify
			 * C then the semijoin becomes a plain innerjoin and we can join
			 * in any order, eg C to A and then to B.  When C is much smaller
			 * than A and B this can be a huge win.  So we allow C to be
			 * joined to just A or just B here, and then make_join_rel has
			 * to handle the case properly.
			 *
			 * Note that actually we'll allow unique-ified C to be joined to
			 * some other relation D here, too.  That is legal, if usually not
			 * very sane, and this routine is only concerned with legality not
			 * with whether the join is good strategy.
			 *----------
			 */
			if (match_sjinfo)
				return false;	/* invalid join path */
			match_sjinfo = sjinfo;
			reversed = false;
			unique_ified = true;
		}
		else if (sjinfo->jointype == JOIN_SEMI &&
				 bms_equal(sjinfo->syn_righthand, rel1->relids) &&
				 create_unique_paths(root, rel1, sjinfo) != NULL)
		{
			/* Reversed semijoin case */
			if (match_sjinfo)
				return false;	/* invalid join path */
			match_sjinfo = sjinfo;
			reversed = true;
			unique_ified = true;
		}
		else
		{
			/*
			 * Otherwise, the proposed join overlaps the RHS but isn't a valid
			 * implementation of this SJ.  But don't panic quite yet: the RHS
			 * violation might have occurred previously, in one or both input
			 * relations, in which case we must have previously decided that
			 * it was OK to commute some other SJ with this one.  If we need
			 * to perform this join to finish building up the RHS, rejecting
			 * it could lead to not finding any plan at all.  (This can occur
			 * because of the heuristics elsewhere in this file that postpone
			 * clauseless joins: we might not consider doing a clauseless join
			 * within the RHS until after we've performed other, validly
			 * commutable SJs with one or both sides of the clauseless join.)
			 * This consideration boils down to the rule that if both inputs
			 * overlap the RHS, we can allow the join --- they are either
			 * fully within the RHS, or represent previously-allowed joins to
			 * rels outside it.
			 */
			if (bms_overlap(rel1->relids, sjinfo->min_righthand) &&
				bms_overlap(rel2->relids, sjinfo->min_righthand))
				continue;		/* assume valid previous violation of RHS */

			/*
			 * The proposed join could still be legal, but only if we're
			 * allowed to associate it into the RHS of this SJ.  That means
			 * this SJ must be a LEFT join (not SEMI or ANTI, and certainly
			 * not FULL) and the proposed join must not overlap the LHS.
			 */
			if (sjinfo->jointype != JOIN_LEFT ||
				bms_overlap(joinrelids, sjinfo->min_lefthand))
				return false;	/* invalid join path */

			/*
			 * To be valid, the proposed join must be a LEFT join; otherwise
			 * it can't associate into this SJ's RHS.  But we may not yet have
			 * found the SpecialJoinInfo matching the proposed join, so we
			 * can't test that yet.  Remember the requirement for later.
			 */
			must_be_leftjoin = true;
		}
	}

	/*
	 * Fail if violated any SJ's RHS and didn't match to a LEFT SJ: the
	 * proposed join can't associate into an SJ's RHS.
	 *
	 * Also, fail if the proposed join's predicate isn't strict; we're
	 * essentially checking to see if we can apply outer-join identity 3, and
	 * that's a requirement.  (This check may be redundant with checks in
	 * make_outerjoininfo, but I'm not quite sure, and it's cheap to test.)
	 */
	if (must_be_leftjoin &&
		(match_sjinfo == NULL ||
		 match_sjinfo->jointype != JOIN_LEFT ||
		 !match_sjinfo->lhs_strict))
		return false;			/* invalid join path */

	/*
	 * We also have to check for constraints imposed by LATERAL references.
	 */
	if (root->hasLateralRTEs)
	{
		bool		lateral_fwd;
		bool		lateral_rev;
		Relids		join_lateral_rels;

		/*
		 * The proposed rels could each contain lateral references to the
		 * other, in which case the join is impossible.  If there are lateral
		 * references in just one direction, then the join has to be done with
		 * a nestloop with the lateral referencer on the inside.  If the join
		 * matches an SJ that cannot be implemented by such a nestloop, the
		 * join is impossible.
		 *
		 * Also, if the lateral reference is only indirect, we should reject
		 * the join; whatever rel(s) the reference chain goes through must be
		 * joined to first.
		 */
		lateral_fwd = bms_overlap(rel1->relids, rel2->lateral_relids);
		lateral_rev = bms_overlap(rel2->relids, rel1->lateral_relids);
		if (lateral_fwd && lateral_rev)
			return false;		/* have lateral refs in both directions */
		if (lateral_fwd)
		{
			/* has to be implemented as nestloop with rel1 on left */
			if (match_sjinfo &&
				(reversed ||
				 unique_ified ||
				 match_sjinfo->jointype == JOIN_FULL))
				return false;	/* not implementable as nestloop */
			/* check there is a direct reference from rel2 to rel1 */
			if (!bms_overlap(rel1->relids, rel2->direct_lateral_relids))
				return false;	/* only indirect refs, so reject */
		}
		else if (lateral_rev)
		{
			/* has to be implemented as nestloop with rel2 on left */
			if (match_sjinfo &&
				(!reversed ||
				 unique_ified ||
				 match_sjinfo->jointype == JOIN_FULL))
				return false;	/* not implementable as nestloop */
			/* check there is a direct reference from rel1 to rel2 */
			if (!bms_overlap(rel2->relids, rel1->direct_lateral_relids))
				return false;	/* only indirect refs, so reject */
		}

		/*
		 * LATERAL references could also cause problems later on if we accept
		 * this join: if the join's minimum parameterization includes any rels
		 * that would have to be on the inside of an outer join with this join
		 * rel, then it's never going to be possible to build the complete
		 * query using this join.  We should reject this join not only because
		 * it'll save work, but because if we don't, the clauseless-join
		 * heuristics might think that legality of this join means that some
		 * other join rel need not be formed, and that could lead to failure
		 * to find any plan at all.  We have to consider not only rels that
		 * are directly on the inner side of an OJ with the joinrel, but also
		 * ones that are indirectly so, so search to find all such rels.
		 */
		join_lateral_rels = min_join_parameterization(root, joinrelids,
													  rel1, rel2);
		if (join_lateral_rels)
		{
			Relids		join_plus_rhs = bms_copy(joinrelids);
			bool		more;

			do
			{
				more = false;
				foreach(l, root->join_info_list)
				{
					SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(l);

					/* ignore full joins --- their ordering is predetermined */
					if (sjinfo->jointype == JOIN_FULL)
						continue;

					if (bms_overlap(sjinfo->min_lefthand, join_plus_rhs) &&
						!bms_is_subset(sjinfo->min_righthand, join_plus_rhs))
					{
						join_plus_rhs = bms_add_members(join_plus_rhs,
														sjinfo->min_righthand);
						more = true;
					}
				}
			} while (more);
			if (bms_overlap(join_plus_rhs, join_lateral_rels))
				return false;	/* will not be able to join to some RHS rel */
		}
	}

	/* Otherwise, it's a valid join */
	*sjinfo_p = match_sjinfo;
	*reversed_p = reversed;
	return true;
}

/*
 * init_dummy_sjinfo
 *    Populate the given SpecialJoinInfo for a plain inner join between the
 *    left and right relations specified by left_relids and right_relids
 *    respectively.
 *
 * Normally, an inner join does not have a SpecialJoinInfo node associated with
 * it. But some functions involved in join planning require one containing at
 * least the information of which relations are being joined.  So we initialize
 * that information here.
 */
/*
 * init_dummy_sjinfo - (中文)为一次纯内连接初始化一个"哑" SpecialJoinInfo
 *
 * 【作用】普通内连接在 join_info_list 中没有对应的 SpecialJoinInfo,但若干
 * 连接规划函数(如 make_join_rel 内为选择率估算准备的 sjinfo_data)需要一
 * 个至少能说明"连接了哪些关系"的 SpecialJoinInfo。本函数就把给定结构按
 * 左/右关系填充成最简内连接语义。
 *
 * 【设计思想】除了把两侧 relids 同时填进 min_/syn_lefthand/righthand 并把
 * jointype 置为 JOIN_INNER、ojrelid 置 0(表示无外层连接)之外,其余字段
 * (lhs_strict、semi_* 等)不做有效处理——因为它们只对真正的特殊连接有意义,
 * 哑节点用不到。commute_* 指针置 NULL 表示没有可交换的外层连接。
 *
 * 【参数】
 *   sjinfo      —— 待填充的 SpecialJoinInfo(通常位于调用者栈上);
 *   left_relids —— 左侧关系的 relids;
 *   right_relids —— 右侧关系的 relids。
 * 【返回值】无。
 */
void
init_dummy_sjinfo(SpecialJoinInfo *sjinfo, Relids left_relids,
				  Relids right_relids)
{
	sjinfo->type = T_SpecialJoinInfo;
	sjinfo->min_lefthand = left_relids;
	sjinfo->min_righthand = right_relids;
	sjinfo->syn_lefthand = left_relids;
	sjinfo->syn_righthand = right_relids;
	sjinfo->jointype = JOIN_INNER;
	sjinfo->ojrelid = 0;
	sjinfo->commute_above_l = NULL;
	sjinfo->commute_above_r = NULL;
	sjinfo->commute_below_l = NULL;
	sjinfo->commute_below_r = NULL;
	/* we don't bother trying to make the remaining fields valid */
	sjinfo->lhs_strict = false;
	sjinfo->semi_can_btree = false;
	sjinfo->semi_can_hash = false;
	sjinfo->semi_operators = NIL;
	sjinfo->semi_rhs_exprs = NIL;
}

/*
 * make_join_rel
 *	   Find or create a join RelOptInfo that represents the join of
 *	   the two given rels, and add to it path information for paths
 *	   created with the two rels as outer and inner rel.
 *	   (The join rel may already contain paths generated from other
 *	   pairs of rels that add up to the same set of base rels.)
 *
 * NB: will return NULL if attempted join is not valid.  This can happen
 * when working with outer joins, or with IN or EXISTS clauses that have been
 * turned into joins.
 */
/*
 * make_join_rel - (中文)查找或创建两个关系连接的 RelOptInfo,并为其添加
 * 路径信息
 *
 * 【作用】join_search_one_level() 及其辅助函数在确定"值得尝试某对关系"后
 * 调用本函数:构建/复用 joinrel,计算 restrictlist,并在其上填充以该两关系
 * 为外/内输入生成的路径。若连接非法(如违反外层连接语义),返回 NULL。
 *
 * 【设计思想】核心流程:
 * 1. 计算 joinrelids = rel1 ∪ rel2,调 join_is_legal() 判定合法性并取
 *    sjinfo / reversed;
 * 2. 用 add_outer_joins_to_relids() 把需要在本次连接中结算的外层连接 relid
 *    加进 joinrelids,形成规范标识,并把被"下推"进 RHS 的 SJ 追加到
 *    pushed_down_joins;
 * 3. 若需要则交换 rel1/rel2 以匹配 SJ;纯内连接时构造哑 sjinfo;
 * 4. build_join_rel() 查找或构建 joinrel 并计算 restrictlist;
 * 5. 若该 joinrel 已被证明为空(is_dummy_rel),无需再考虑路径;
 * 6. 否则依次 make_grouped_join_rel()(eager aggregation)与
 *    populate_joinrel_with_paths()(为 rel1×rel2 与 rel2×rel1 生成路径)。
 * 注意 joinrel 可能已被其他 (rel1', rel2') 组合创建过,本函数只负责追加
 * 路径。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel1, rel2 —— 两个待连接的输入关系(relids 不得重叠,有断言)。
 * 【返回值】构建出的连接关系 RelOptInfo;连接非法时返回 NULL。
 */
RelOptInfo *
make_join_rel(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	Relids		joinrelids;
	SpecialJoinInfo *sjinfo;
	bool		reversed;
	List	   *pushed_down_joins = NIL;
	SpecialJoinInfo sjinfo_data;
	RelOptInfo *joinrel;
	List	   *restrictlist;

	/* We should never try to join two overlapping sets of rels. */
	Assert(!bms_overlap(rel1->relids, rel2->relids));

	/* Construct Relids set that identifies the joinrel (without OJ as yet). */
	joinrelids = bms_union(rel1->relids, rel2->relids);

	/* Check validity and determine join type. */
	if (!join_is_legal(root, rel1, rel2, joinrelids,
					   &sjinfo, &reversed))
	{
		/* invalid join path */
		bms_free(joinrelids);
		return NULL;
	}

	/*
	 * Add outer join relid(s) to form the canonical relids.  Any added outer
	 * joins besides sjinfo itself are appended to pushed_down_joins.
	 */
	joinrelids = add_outer_joins_to_relids(root, joinrelids, sjinfo,
										   &pushed_down_joins);

	/* Swap rels if needed to match the join info. */
	if (reversed)
	{
		RelOptInfo *trel = rel1;

		rel1 = rel2;
		rel2 = trel;
	}

	/*
	 * If it's a plain inner join, then we won't have found anything in
	 * join_info_list.  Make up a SpecialJoinInfo so that selectivity
	 * estimation functions will know what's being joined.
	 */
	if (sjinfo == NULL)
	{
		sjinfo = &sjinfo_data;
		init_dummy_sjinfo(sjinfo, rel1->relids, rel2->relids);
	}

	/*
	 * Find or build the join RelOptInfo, and compute the restrictlist that
	 * goes with this particular joining.
	 */
	joinrel = build_join_rel(root, joinrelids, rel1, rel2,
							 sjinfo, pushed_down_joins,
							 &restrictlist);

	/*
	 * If we've already proven this join is empty, we needn't consider any
	 * more paths for it.
	 */
	if (is_dummy_rel(joinrel))
	{
		bms_free(joinrelids);
		return joinrel;
	}

	/* Build a grouped join relation for 'joinrel' if possible. */
	make_grouped_join_rel(root, rel1, rel2, joinrel, sjinfo,
						  restrictlist);

	/* Add paths to the join relation. */
	populate_joinrel_with_paths(root, rel1, rel2, joinrel, sjinfo,
								restrictlist);

	bms_free(joinrelids);

	return joinrel;
}

/*
 * add_outer_joins_to_relids
 *	  Add relids to input_relids to represent any outer joins that will be
 *	  calculated at this join.
 *
 * input_relids is the union of the relid sets of the two input relations.
 * Note that we modify this in-place and return it; caller must bms_copy()
 * it first, if a separate value is desired.
 *
 * sjinfo represents the join being performed.
 *
 * If the current join completes the calculation of any outer joins that
 * have been pushed down per outer-join identity 3, those relids will be
 * added to the result along with sjinfo's own relid.  If pushed_down_joins
 * is not NULL, then also the SpecialJoinInfos for such added outer joins will
 * be appended to *pushed_down_joins (so caller must initialize it to NIL).
 */
/*
 * add_outer_joins_to_relids - (中文)把本次连接将结算的外层连接 relid 加入
 * relids 集合,构成连接的规范标识
 *
 * 【作用】make_join_rel() 调用本函数:在输入 relids 并集(input_relids)的
 * 基础上,加入"将在本次连接中被计算出来"的外层连接的 relid(含按外层连接
 * 恒等式 3 被下推、现在该补算的连接),形成连接的规范 relids。可选地把这些
 * 被补算 SJ 的 SpecialJoinInfo 追加到 *pushed_down_joins。
 *
 * 【设计思想】
 * - 若非外层连接(无 ojrelid),直接返回原集合;
 * - 非 LEFT 连接没有交换执行规则,只需加上自身 ojrelid 后返回(此时其
 *   commute_below_l / commute_above_l 必为空);
 * - LEFT 连接:仅当"下交换"条件满足(commute_below_l ⊆ input_relids)才能
 *   加上自身 relid;否则该 OJ 是被推进更低层 LEFT 连接的 RHS,不能声称其
 *   输出已完成;
 * - 若该 OJ 曾允许"上交换"(commute_above_l 非空),则遍历 join_info_list,
 *   把同样满足结算条件(ojrelid ∈ commute_above_rels、min_lefthand/
 *   min_righthand/commute_below_l 都已就绪)的被下推 LEFT 连接一并加入;
 *   由于 join_info_list 自底向上构建,一遍遍历即可(本次加入的 ojrelid 不会
 *   影响更早迭代的判断),并递归扩展 commute_above_rels。
 *
 * 【参数】
 *   root             —— PlannerInfo;
 *   input_relids     —— 两个输入关系的 relids 并集(会被原地修改并返回,
 *                       调用方如需保留须先 bms_copy);
 *   sjinfo           —— 本次进行的连接对应的 SpecialJoinInfo;
 *   pushed_down_joins —— 可为 NULL;非 NULL 时把被补算的 SJ 追加进来。
 * 【返回值】扩展后的 relids 集合(与传入 input_relids 是同一对象,可能被
 * 原地扩展)。
 */
Relids
add_outer_joins_to_relids(PlannerInfo *root, Relids input_relids,
						  SpecialJoinInfo *sjinfo,
						  List **pushed_down_joins)
{
	/* Nothing to do if this isn't an outer join with an assigned relid. */
	if (sjinfo == NULL || sjinfo->ojrelid == 0)
		return input_relids;

	/*
	 * If it's not a left join, we have no rules that would permit executing
	 * it in non-syntactic order, so just form the syntactic relid set.  (This
	 * is just a quick-exit test; we'd come to the same conclusion anyway,
	 * since its commute_below_l and commute_above_l sets must be empty.)
	 */
	if (sjinfo->jointype != JOIN_LEFT)
		return bms_add_member(input_relids, sjinfo->ojrelid);

	/*
	 * We cannot add the OJ relid if this join has been pushed into the RHS of
	 * a syntactically-lower left join per OJ identity 3.  (If it has, then we
	 * cannot claim that its outputs represent the final state of its RHS.)
	 * There will not be any other OJs that can be added either, so we're
	 * done.
	 */
	if (!bms_is_subset(sjinfo->commute_below_l, input_relids))
		return input_relids;

	/* OK to add OJ's own relid */
	input_relids = bms_add_member(input_relids, sjinfo->ojrelid);

	/*
	 * Contrariwise, if we are now forming the final result of such a commuted
	 * pair of OJs, it's time to add the relid(s) of the pushed-down join(s).
	 * We can skip this if this join was never a candidate to be pushed up.
	 */
	if (sjinfo->commute_above_l)
	{
		Relids		commute_above_rels = bms_copy(sjinfo->commute_above_l);
		ListCell   *lc;

		/*
		 * The current join could complete the nulling of more than one
		 * pushed-down join, so we have to examine all the SpecialJoinInfos.
		 * Because join_info_list was built in bottom-up order, it's
		 * sufficient to traverse it once: an ojrelid we add in one loop
		 * iteration would not have affected decisions of earlier iterations.
		 */
		foreach(lc, root->join_info_list)
		{
			SpecialJoinInfo *othersj = (SpecialJoinInfo *) lfirst(lc);

			if (othersj == sjinfo ||
				othersj->ojrelid == 0 || othersj->jointype != JOIN_LEFT)
				continue;		/* definitely not interesting */

			if (!bms_is_member(othersj->ojrelid, commute_above_rels))
				continue;

			/* Add it if not already present but conditions now satisfied */
			if (!bms_is_member(othersj->ojrelid, input_relids) &&
				bms_is_subset(othersj->min_lefthand, input_relids) &&
				bms_is_subset(othersj->min_righthand, input_relids) &&
				bms_is_subset(othersj->commute_below_l, input_relids))
			{
				input_relids = bms_add_member(input_relids, othersj->ojrelid);
				/* report such pushed down outer joins, if asked */
				if (pushed_down_joins != NULL)
					*pushed_down_joins = lappend(*pushed_down_joins, othersj);

				/*
				 * We must also check any joins that othersj potentially
				 * commutes with.  They likewise must appear later in
				 * join_info_list than othersj itself, so we can visit them
				 * later in this loop.
				 */
				commute_above_rels = bms_add_members(commute_above_rels,
													 othersj->commute_above_l);
			}
		}
	}

	return input_relids;
}

/*
 * make_grouped_join_rel
 *	  Build a grouped join relation for the given "joinrel" if eager
 *	  aggregation is applicable and the resulting grouped paths are considered
 *	  useful.
 *
 * There are two strategies for generating grouped paths for a join relation:
 *
 * 1. Join a grouped (partially aggregated) input relation with a non-grouped
 * input (e.g., AGG(B) JOIN A).
 *
 * 2. Apply partial aggregation (sorted or hashed) on top of existing
 * non-grouped join paths (e.g., AGG(A JOIN B)).
 *
 * To limit planning effort and avoid an explosion of alternatives, we adopt a
 * strategy where partial aggregation is only pushed to the lowest possible
 * level in the join tree that is deemed useful.  That is, if grouped paths can
 * be built using the first strategy, we skip consideration of the second
 * strategy for the same join level.
 *
 * Additionally, if there are multiple lowest useful levels where partial
 * aggregation could be applied, such as in a join tree with relations A, B,
 * and C where both "AGG(A JOIN B) JOIN C" and "A JOIN AGG(B JOIN C)" are valid
 * placements, we choose only the first one encountered during join search.
 * This avoids generating multiple versions of the same grouped relation based
 * on different aggregation placements.
 *
 * These heuristics also ensure that all grouped paths for the same grouped
 * relation produce the same set of rows, which is a basic assumption in the
 * planner.
 */
/*
 * make_grouped_join_rel - (中文)若"急切聚合"(eager aggregation)适用,为
 * 给定的 joinrel 构建分组连接关系(grouped join rel)并生成分组路径
 *
 * 【作用】make_join_rel() 在 populate_joinrel_with_paths() 之前调用本函数:
 * 若查询含聚合/分组表达式,且分组路径被认为有用,则构建与 joinrel 对应的
 * grouped_rel,并调用 populate_joinrel_with_paths() 为其填充路径。
 *
 * 【设计思想】两种生成分组路径的策略:
 * 1. 一个分组输入 + 一个非分组输入连接(如 AGG(B) JOIN A);
 * 2. 在既有非分组连接路径之上做部分聚合(如 AGG(A JOIN B))。
 * 为避免规划组合爆炸,限制部分聚合只下推到"最低的有用层":若能走策略 1
 * 就跳过同一层的策略 2;多个候选最低层(如 AGG(A JOIN B) JOIN C 与
 * A JOIN AGG(B JOIN C) 都合法)时只采用搜索中先遇到的那个
 * (joinrel->agg_info->apply_agg_at 记录"应用聚合的关系集合"作为唯一指定层)。
 * 这些启发式也保证同一个 grouped_rel 的所有分组路径产生相同的行集。
 * 细节:create_rel_agg_info() 评估聚合是否有用(agg_useful);rel1_empty /
 * rel2_empty 表示某输入没有分组关系或为空;若指定层 apply_agg_at 与已记录
 * 的不同:是其子集则更新记录并重算大小估计,否则跳过。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   rel1, rel2  —— joinrel 的两个输入关系;
 *   joinrel     —— 连接关系(其 grouped_rel 字段保存分组关系);
 *   sjinfo      —— 连接上下文;
 *   restrictlist —— 本次连接的子句列表。
 * 【返回值】无。
 */
static void
make_grouped_join_rel(PlannerInfo *root, RelOptInfo *rel1,
					  RelOptInfo *rel2, RelOptInfo *joinrel,
					  SpecialJoinInfo *sjinfo, List *restrictlist)
{
	RelOptInfo *grouped_rel;
	RelOptInfo *grouped_rel1;
	RelOptInfo *grouped_rel2;
	bool		rel1_empty;
	bool		rel2_empty;
	Relids		apply_agg_at;

	/*
	 * If there are no aggregate expressions or grouping expressions, eager
	 * aggregation is not possible.
	 */
	if (root->agg_clause_list == NIL ||
		root->group_expr_list == NIL)
		return;

	/* Retrieve the grouped relations for the two input rels */
	grouped_rel1 = rel1->grouped_rel;
	grouped_rel2 = rel2->grouped_rel;

	rel1_empty = (grouped_rel1 == NULL || IS_DUMMY_REL(grouped_rel1));
	rel2_empty = (grouped_rel2 == NULL || IS_DUMMY_REL(grouped_rel2));

	/* Find or construct a grouped joinrel for this joinrel */
	grouped_rel = joinrel->grouped_rel;
	if (grouped_rel == NULL)
	{
		RelAggInfo *agg_info = NULL;

		/*
		 * Prepare the information needed to create grouped paths for this
		 * join relation.
		 */
		agg_info = create_rel_agg_info(root, joinrel, rel1_empty == rel2_empty);
		if (agg_info == NULL)
			return;

		/*
		 * If grouped paths for the given join relation are not considered
		 * useful, and no grouped paths can be built by joining grouped input
		 * relations, skip building the grouped join relation.
		 */
		if (!agg_info->agg_useful &&
			(rel1_empty == rel2_empty))
			return;

		/* build the grouped relation */
		grouped_rel = build_grouped_rel(root, joinrel);
		grouped_rel->reltarget = agg_info->target;

		if (rel1_empty != rel2_empty)
		{
			/*
			 * If there is exactly one grouped input relation, then we can
			 * build grouped paths by joining the input relations.  Set size
			 * estimates for the grouped join relation based on the input
			 * relations, and update the set of relids where partial
			 * aggregation is applied to that of the grouped input relation.
			 */
			set_joinrel_size_estimates(root, grouped_rel,
									   rel1_empty ? rel1 : grouped_rel1,
									   rel2_empty ? rel2 : grouped_rel2,
									   sjinfo, restrictlist);
			agg_info->apply_agg_at = rel1_empty ?
				grouped_rel2->agg_info->apply_agg_at :
				grouped_rel1->agg_info->apply_agg_at;
		}
		else
		{
			/*
			 * Otherwise, grouped paths can be built by applying partial
			 * aggregation on top of existing non-grouped join paths.  Set
			 * size estimates for the grouped join relation based on the
			 * estimated number of groups, and track the set of relids where
			 * partial aggregation is applied.  Note that these values may be
			 * updated later if it is determined that grouped paths can be
			 * constructed by joining other input relations.
			 */
			grouped_rel->rows = agg_info->grouped_rows;
			agg_info->apply_agg_at = bms_copy(joinrel->relids);
		}

		grouped_rel->agg_info = agg_info;
		joinrel->grouped_rel = grouped_rel;
	}

	Assert(IS_GROUPED_REL(grouped_rel));

	/* We may have already proven this grouped join relation to be dummy. */
	if (IS_DUMMY_REL(grouped_rel))
		return;

	/*
	 * Nothing to do if there's no grouped input relation.  Also, joining two
	 * grouped relations is not currently supported.
	 */
	if (rel1_empty == rel2_empty)
		return;

	/*
	 * Get the set of relids where partial aggregation is applied among the
	 * given input relations.
	 */
	apply_agg_at = rel1_empty ?
		grouped_rel2->agg_info->apply_agg_at :
		grouped_rel1->agg_info->apply_agg_at;

	/*
	 * If it's not the designated level, skip building grouped paths.
	 *
	 * One exception is when it is a subset of the previously recorded level.
	 * In that case, we need to update the designated level to this one, and
	 * adjust the size estimates for the grouped join relation accordingly.
	 * For example, suppose partial aggregation can be applied on top of (B
	 * JOIN C).  If we first construct the join as ((A JOIN B) JOIN C), we'd
	 * record the designated level as including all three relations (A B C).
	 * Later, when we consider (A JOIN (B JOIN C)), we encounter the smaller
	 * (B C) join level directly.  Since this is a subset of the previous
	 * level and still valid for partial aggregation, we update the designated
	 * level to (B C), and adjust the size estimates accordingly.
	 */
	if (!bms_equal(apply_agg_at, grouped_rel->agg_info->apply_agg_at))
	{
		if (bms_is_subset(apply_agg_at, grouped_rel->agg_info->apply_agg_at))
		{
			/* Adjust the size estimates for the grouped join relation. */
			set_joinrel_size_estimates(root, grouped_rel,
									   rel1_empty ? rel1 : grouped_rel1,
									   rel2_empty ? rel2 : grouped_rel2,
									   sjinfo, restrictlist);
			grouped_rel->agg_info->apply_agg_at = apply_agg_at;
		}
		else
			return;
	}

	/* Make paths for the grouped join relation. */
	populate_joinrel_with_paths(root,
								rel1_empty ? rel1 : grouped_rel1,
								rel2_empty ? rel2 : grouped_rel2,
								grouped_rel,
								sjinfo,
								restrictlist);
}

/*
 * populate_joinrel_with_paths
 *	  Add paths to the given joinrel for given pair of joining relations. The
 *	  SpecialJoinInfo provides details about the join and the restrictlist
 *	  contains the join clauses and the other clauses applicable for given pair
 *	  of the joining relations.
 */
/*
 * populate_joinrel_with_paths - (中文)为给定的 joinrel 及一对连接关系添加
 * 路径
 *
 * 【作用】make_join_rel() 与 make_grouped_join_rel()(以及分区连接的
 * try_partitionwise_join)调用本函数:根据 sjinfo 的连接类型,以两个方向
 * 调用 joinpath.c 的 add_paths_to_joinrel() 生成路径,并处理"可证明为空"
 * 的剪枝。
 *
 * 【设计思想】按 sjinfo->jointype 分派:
 * - INNER/SEMI:任一侧为 dummy 或限制恒为 FALSE 则整个 joinrel 标为 dummy;
 * - LEFT/ANTI:外层(rel1)为 dummy 或恒 FALSE(推下)则 joinrel 为 dummy;
 *   恒 FALSE(未推下)且 rel2 属于 syn_righthand 时只把内层标记 dummy;
 * - FULL:两侧都 dummy 或恒 FALSE 才标 dummy;若最终一条路径都没生成,
 *   报错(FULL JOIN 只支持可归并/可哈希的连接条件);
 * - SEMI 特殊处理:若 rel1/rel2 恰好满足 min_lefthand/min_righthand,按
 *   JOIN_SEMI 与 JOIN_RIGHT_SEMI 两个方向生成;若某输入恰好等于
 *   syn_righthand 且可 unique 化,则用 unique 化后的关系以
 *   JOIN_UNIQUE_INNER / JOIN_UNIQUE_OUTER 生成路径;
 * 最后若连接双方是分区关系,调用 try_partitionwise_join() 尝试分区剪枝。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   rel1, rel2  —— 一对连接关系(可能其一为 grouped 关系);
 *   joinrel     —— 目标连接关系;
 *   sjinfo      —— 连接上下文;
 *   restrictlist —— 本次连接的子句列表。
 * 【返回值】无。
 */
static void
populate_joinrel_with_paths(PlannerInfo *root, RelOptInfo *rel1,
							RelOptInfo *rel2, RelOptInfo *joinrel,
							SpecialJoinInfo *sjinfo, List *restrictlist)
{
	RelOptInfo *unique_rel2;

	/*
	 * Consider paths using each rel as both outer and inner.  Depending on
	 * the join type, a provably empty outer or inner rel might mean the join
	 * is provably empty too; in which case throw away any previously computed
	 * paths and mark the join as dummy.  (We do it this way since it's
	 * conceivable that dummy-ness of a multi-element join might only be
	 * noticeable for certain construction paths.)
	 *
	 * Also, a provably constant-false join restriction typically means that
	 * we can skip evaluating one or both sides of the join.  We do this by
	 * marking the appropriate rel as dummy.  For outer joins, a
	 * constant-false restriction that is pushed down still means the whole
	 * join is dummy, while a non-pushed-down one means that no inner rows
	 * will join so we can treat the inner rel as dummy.
	 *
	 * We need only consider the jointypes that appear in join_info_list, plus
	 * JOIN_INNER.
	 */
	switch (sjinfo->jointype)
	{
		case JOIN_INNER:
			if (is_dummy_rel(rel1) || is_dummy_rel(rel2) ||
				restriction_is_constant_false(restrictlist, joinrel, false))
			{
				mark_dummy_rel(joinrel);
				break;
			}
			add_paths_to_joinrel(root, joinrel, rel1, rel2,
								 JOIN_INNER, sjinfo,
								 restrictlist);
			add_paths_to_joinrel(root, joinrel, rel2, rel1,
								 JOIN_INNER, sjinfo,
								 restrictlist);
			break;
		case JOIN_LEFT:
			if (is_dummy_rel(rel1) ||
				restriction_is_constant_false(restrictlist, joinrel, true))
			{
				mark_dummy_rel(joinrel);
				break;
			}
			if (restriction_is_constant_false(restrictlist, joinrel, false) &&
				bms_is_subset(rel2->relids, sjinfo->syn_righthand))
				mark_dummy_rel(rel2);
			add_paths_to_joinrel(root, joinrel, rel1, rel2,
								 JOIN_LEFT, sjinfo,
								 restrictlist);
			add_paths_to_joinrel(root, joinrel, rel2, rel1,
								 JOIN_RIGHT, sjinfo,
								 restrictlist);
			break;
		case JOIN_FULL:
			if ((is_dummy_rel(rel1) && is_dummy_rel(rel2)) ||
				restriction_is_constant_false(restrictlist, joinrel, true))
			{
				mark_dummy_rel(joinrel);
				break;
			}
			add_paths_to_joinrel(root, joinrel, rel1, rel2,
								 JOIN_FULL, sjinfo,
								 restrictlist);
			add_paths_to_joinrel(root, joinrel, rel2, rel1,
								 JOIN_FULL, sjinfo,
								 restrictlist);

			/*
			 * If there are join quals that aren't mergeable or hashable, we
			 * may not be able to build any valid plan.  Complain here so that
			 * we can give a somewhat-useful error message.  (Since we have no
			 * flexibility of planning for a full join, there's no chance of
			 * succeeding later with another pair of input rels.)
			 */
			if (joinrel->pathlist == NIL)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("FULL JOIN is only supported with merge-joinable or hash-joinable join conditions")));
			break;
		case JOIN_SEMI:

			/*
			 * We might have a normal semijoin, or a case where we don't have
			 * enough rels to do the semijoin but can unique-ify the RHS and
			 * then do an innerjoin (see comments in join_is_legal).  In the
			 * latter case we can't apply JOIN_SEMI joining.
			 */
			if (bms_is_subset(sjinfo->min_lefthand, rel1->relids) &&
				bms_is_subset(sjinfo->min_righthand, rel2->relids))
			{
				if (is_dummy_rel(rel1) || is_dummy_rel(rel2) ||
					restriction_is_constant_false(restrictlist, joinrel, false))
				{
					mark_dummy_rel(joinrel);
					break;
				}
				add_paths_to_joinrel(root, joinrel, rel1, rel2,
									 JOIN_SEMI, sjinfo,
									 restrictlist);
				add_paths_to_joinrel(root, joinrel, rel2, rel1,
									 JOIN_RIGHT_SEMI, sjinfo,
									 restrictlist);
			}

			/*
			 * If we know how to unique-ify the RHS and one input rel is
			 * exactly the RHS (not a superset) we can consider unique-ifying
			 * it and then doing a regular join.  (The create_unique_paths
			 * check here is probably redundant with what join_is_legal did,
			 * but if so the check is cheap because it's cached.  So test
			 * anyway to be sure.)
			 */
			if (bms_equal(sjinfo->syn_righthand, rel2->relids) &&
				(unique_rel2 = create_unique_paths(root, rel2, sjinfo)) != NULL)
			{
				if (is_dummy_rel(rel1) || is_dummy_rel(rel2) ||
					restriction_is_constant_false(restrictlist, joinrel, false))
				{
					mark_dummy_rel(joinrel);
					break;
				}
				add_paths_to_joinrel(root, joinrel, rel1, unique_rel2,
									 JOIN_UNIQUE_INNER, sjinfo,
									 restrictlist);
				add_paths_to_joinrel(root, joinrel, unique_rel2, rel1,
									 JOIN_UNIQUE_OUTER, sjinfo,
									 restrictlist);
			}
			break;
		case JOIN_ANTI:
			if (is_dummy_rel(rel1) ||
				restriction_is_constant_false(restrictlist, joinrel, true))
			{
				mark_dummy_rel(joinrel);
				break;
			}
			if (restriction_is_constant_false(restrictlist, joinrel, false) &&
				bms_is_subset(rel2->relids, sjinfo->syn_righthand))
				mark_dummy_rel(rel2);
			add_paths_to_joinrel(root, joinrel, rel1, rel2,
								 JOIN_ANTI, sjinfo,
								 restrictlist);
			add_paths_to_joinrel(root, joinrel, rel2, rel1,
								 JOIN_RIGHT_ANTI, sjinfo,
								 restrictlist);
			break;
		default:
			/* other values not expected here */
			elog(ERROR, "unrecognized join type: %d", (int) sjinfo->jointype);
			break;
	}

	/* Apply partitionwise join technique, if possible. */
	try_partitionwise_join(root, rel1, rel2, joinrel, sjinfo, restrictlist);
}


/*
 * have_join_order_restriction
 *		Detect whether the two relations should be joined to satisfy
 *		a join-order restriction arising from special or lateral joins.
 *
 * In practice this is always used with have_relevant_joinclause(), and so
 * could be merged with that function, but it seems clearer to separate the
 * two concerns.  We need this test because there are degenerate cases where
 * a clauseless join must be performed to satisfy join-order restrictions.
 * Also, if one rel has a lateral reference to the other, or both are needed
 * to compute some PHV, we should consider joining them even if the join would
 * be clauseless.
 *
 * Note: this is only a problem if one side of a degenerate outer join
 * contains multiple rels, or a clauseless join is required within an
 * IN/EXISTS RHS; else we will find a join path via the "last ditch" case in
 * join_search_one_level().  We could dispense with this test if we were
 * willing to try bushy plans in the "last ditch" case, but that seems much
 * less efficient.
 */
/*
 * have_join_order_restriction - (中文)检测两个关系是否因特殊连接或横向连接
 * 产生的连接顺序限制而必须被连接
 *
 * 【作用】make_rels_by_clause_joins() / join_search_one_level() 用来判断
 * "即使没有连接子句,这两个关系是否也必须连接",以满足外层连接、IN/EXISTS
 * 子查询或 LATERAL 引用强加的顺序约束。实践中总与 have_relevant_joinclause()
 * 一起使用。
 *
 * 【设计思想】四种需要强制连接的情形:
 * 1. 一方对另一方有直接横向引用(direct_lateral_relids);
 * 2. 双方同时是某个 PlaceHolderVar 求值点(ph_eval_at)的子集——需要它们
 *    一起才能算出该 PHV;
 * 3. 双方恰好构成某个非 FULL 外层连接的 LHS/RHS(正序或反序);
 * 4. 双方都重叠某个外层连接的 RHS(或 LHS)——说明需要它们共同补全该侧。
 * 最后的关键启发式:若任一输入可以用连接子句合法地连到别的关系,就不强制
 * 本次连接(result 置回 false)——即"无子句的 bushy 连接尽量推迟",以免在
 * 高层顺序限制内部浪费大量规划时间。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel1, rel2 —— 待检测的两个关系。
 * 【返回值】true:应强制连接;false:无此必要。
 */
bool
have_join_order_restriction(PlannerInfo *root,
							RelOptInfo *rel1, RelOptInfo *rel2)
{
	bool		result = false;
	ListCell   *l;

	/*
	 * If either side has a direct lateral reference to the other, attempt the
	 * join regardless of outer-join considerations.
	 */
	if (bms_overlap(rel1->relids, rel2->direct_lateral_relids) ||
		bms_overlap(rel2->relids, rel1->direct_lateral_relids))
		return true;

	/*
	 * Likewise, if both rels are needed to compute some PlaceHolderVar,
	 * attempt the join regardless of outer-join considerations.  (This is not
	 * very desirable, because a PHV with a large eval_at set will cause a lot
	 * of probably-useless joins to be considered, but failing to do this can
	 * cause us to fail to construct a plan at all.)
	 */
	foreach(l, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(l);

		if (bms_is_subset(rel1->relids, phinfo->ph_eval_at) &&
			bms_is_subset(rel2->relids, phinfo->ph_eval_at))
			return true;
	}

	/*
	 * It's possible that the rels correspond to the left and right sides of a
	 * degenerate outer join, that is, one with no joinclause mentioning the
	 * non-nullable side; in which case we should force the join to occur.
	 *
	 * Also, the two rels could represent a clauseless join that has to be
	 * completed to build up the LHS or RHS of an outer join.
	 */
	foreach(l, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(l);

		/* ignore full joins --- other mechanisms handle them */
		if (sjinfo->jointype == JOIN_FULL)
			continue;

		/* Can we perform the SJ with these rels? */
		if (bms_is_subset(sjinfo->min_lefthand, rel1->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel2->relids))
		{
			result = true;
			break;
		}
		if (bms_is_subset(sjinfo->min_lefthand, rel2->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel1->relids))
		{
			result = true;
			break;
		}

		/*
		 * Might we need to join these rels to complete the RHS?  We have to
		 * use "overlap" tests since either rel might include a lower SJ that
		 * has been proven to commute with this one.
		 */
		if (bms_overlap(sjinfo->min_righthand, rel1->relids) &&
			bms_overlap(sjinfo->min_righthand, rel2->relids))
		{
			result = true;
			break;
		}

		/* Likewise for the LHS. */
		if (bms_overlap(sjinfo->min_lefthand, rel1->relids) &&
			bms_overlap(sjinfo->min_lefthand, rel2->relids))
		{
			result = true;
			break;
		}
	}

	/*
	 * We do not force the join to occur if either input rel can legally be
	 * joined to anything else using joinclauses.  This essentially means that
	 * clauseless bushy joins are put off as long as possible. The reason is
	 * that when there is a join order restriction high up in the join tree
	 * (that is, with many rels inside the LHS or RHS), we would otherwise
	 * expend lots of effort considering very stupid join combinations within
	 * its LHS or RHS.
	 */
	if (result)
	{
		if (has_legal_joinclause(root, rel1) ||
			has_legal_joinclause(root, rel2))
			result = false;
	}

	return result;
}


/*
 * has_join_restriction
 *		Detect whether the specified relation has join-order restrictions,
 *		due to being inside an outer join or an IN (sub-SELECT),
 *		or participating in any LATERAL references or multi-rel PHVs.
 *
 * Essentially, this tests whether have_join_order_restriction() could
 * succeed with this rel and some other one.  It's OK if we sometimes
 * say "true" incorrectly.  (Therefore, we don't bother with the relatively
 * expensive has_legal_joinclause test.)
 */
/*
 * has_join_restriction - (中文)检测指定关系是否带有连接顺序限制
 *
 * 【作用】join_search_one_level() 判断一个关系是否可能受到顺序约束,以便
 * 决定走 make_rels_by_clause_joins()(有子句/限制)还是
 * make_rels_by_clauseless_joins()(纯笛卡尔积)。本质上是
 * have_join_order_restriction() 对该关系"与其他某个关系"成立的可能性的
 * 廉价近似。
 *
 * 【设计思想】三种情况返回 true:
 * - rel 有横向依赖或被其他关系横向引用(lateral_relids / lateral_referencers);
 * - rel 是某个多关系 PlaceHolderVar 求值点的真子集(ph_eval_at 严格包含
 *   rel->relids)——需要 rel 与别的关系一起求值;
 * - rel 与某个非 FULL 外层连接的 LHS 或 RHS 有交集,但尚未完整包含该 SJ。
 * 允许偶发误报("true" 但实际没有限制),因为多花一点规划时间代价很小,且
 * 因此刻意省略较昂贵的 has_legal_joinclause() 检测。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 待检测的关系。
 * 【返回值】true:该关系可能有连接顺序限制;false:没有。
 */
static bool
has_join_restriction(PlannerInfo *root, RelOptInfo *rel)
{
	ListCell   *l;

	if (rel->lateral_relids != NULL || rel->lateral_referencers != NULL)
		return true;

	foreach(l, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(l);

		if (bms_is_subset(rel->relids, phinfo->ph_eval_at) &&
			!bms_equal(rel->relids, phinfo->ph_eval_at))
			return true;
	}

	foreach(l, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(l);

		/* ignore full joins --- other mechanisms preserve their ordering */
		if (sjinfo->jointype == JOIN_FULL)
			continue;

		/* ignore if SJ is already contained in rel */
		if (bms_is_subset(sjinfo->min_lefthand, rel->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel->relids))
			continue;

		/* restricted if it overlaps LHS or RHS, but doesn't contain SJ */
		if (bms_overlap(sjinfo->min_lefthand, rel->relids) ||
			bms_overlap(sjinfo->min_righthand, rel->relids))
			return true;
	}

	return false;
}


/*
 * has_legal_joinclause
 *		Detect whether the specified relation can legally be joined
 *		to any other rels using join clauses.
 *
 * We consider only joins to single other relations in the current
 * initial_rels list.  This is sufficient to get a "true" result in most real
 * queries, and an occasional erroneous "false" will only cost a bit more
 * planning time.  The reason for this limitation is that considering joins to
 * other joins would require proving that the other join rel can legally be
 * formed, which seems like too much trouble for something that's only a
 * heuristic to save planning time.  (Note: we must look at initial_rels
 * and not all of the query, since when we are planning a sub-joinlist we
 * may be forced to make clauseless joins within initial_rels even though
 * there are join clauses linking to other parts of the query.)
 */
/*
 * has_legal_joinclause - (中文)检测指定关系能否用连接子句合法地连到其他
 * 关系
 *
 * 【作用】have_join_order_restriction() 的辅助判断:当存在顺序限制时,若
 * rel 还能用连接子句连到别的某个关系,则不强制无子句连接(推迟 bushy)。
 * 本函数在 root->initial_rels 中寻找 rel 的合法连接对象。
 *
 * 【设计思想】只考虑"与单个初始关系"的连接,就足以在绝大多数真实查询中
 * 得到正确结果;偶尔的误判"false"只多花一点规划时间。限制到初始关系是因为
 * 若要去证明"与某个连接关系"连接合法,成本过高;而且规划子问题时,即使
 * 查询其他部分存在连接子句,initial_rels 内部也可能被迫做无子句连接。对每
 * 个 relids 不重叠的候选,若 have_relevant_joinclause() 成立,则用
 * join_is_legal() 验证合法性,合法即返回 true。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 待检测的关系。
 * 【返回值】true:rel 能用连接子句连到某个初始关系;false:不能。
 */
static bool
has_legal_joinclause(PlannerInfo *root, RelOptInfo *rel)
{
	ListCell   *lc;

	foreach(lc, root->initial_rels)
	{
		RelOptInfo *rel2 = (RelOptInfo *) lfirst(lc);

		/* ignore rels that are already in "rel" */
		if (bms_overlap(rel->relids, rel2->relids))
			continue;

		if (have_relevant_joinclause(root, rel, rel2))
		{
			Relids		joinrelids;
			SpecialJoinInfo *sjinfo;
			bool		reversed;

			/* join_is_legal needs relids of the union */
			joinrelids = bms_union(rel->relids, rel2->relids);

			if (join_is_legal(root, rel, rel2, joinrelids,
							  &sjinfo, &reversed))
			{
				/* Yes, this will work */
				bms_free(joinrelids);
				return true;
			}

			bms_free(joinrelids);
		}
	}

	return false;
}


/*
 * is_dummy_rel --- has relation been proven empty?
 */
/*
 * is_dummy_rel - (中文)判断关系是否已被证明为空(dummy)
 *
 * 【作用】各处规划代码(如 populate_joinrel_with_paths、joinpath 的路径
 * 生成、partitionwise join)调用本函数判断某关系是否可被证明为空,以便
 * 提前剪枝。
 *
 * 【设计思想】被证明为空的关系,其 pathlist 的第一个路径是一条"无子节点的
 * Append"(成本为零,必然排在最前)。此后规划阶段可能在其上叠加 ProjectSet /
 * Projection 路径(因为 Append 不能投影),所以需要循环下钻,直到发现
 * IS_DUMMY_APPEND 路径为止。若 pathlist 为空(尚无路径)则不算 dummy。
 *
 * 【参数】rel —— 待检测的关系。
 * 【返回值】true:关系已被证明为空;false:否则。
 */
bool
is_dummy_rel(RelOptInfo *rel)
{
	Path	   *path;

	/*
	 * A rel that is known dummy will have just one path that is a childless
	 * Append.  (Even if somehow it has more paths, a childless Append will
	 * have cost zero and hence should be at the front of the pathlist.)
	 */
	if (rel->pathlist == NIL)
		return false;
	path = (Path *) linitial(rel->pathlist);

	/*
	 * Initially, a dummy path will just be a childless Append.  But in later
	 * planning stages we might stick a ProjectSetPath and/or ProjectionPath
	 * on top, since Append can't project.  Rather than make assumptions about
	 * which combinations can occur, just descend through whatever we find.
	 */
	for (;;)
	{
		if (IsA(path, ProjectionPath))
			path = ((ProjectionPath *) path)->subpath;
		else if (IsA(path, ProjectSetPath))
			path = ((ProjectSetPath *) path)->subpath;
		else
			break;
	}
	if (IS_DUMMY_APPEND(path))
		return true;
	return false;
}

/*
 * Mark a relation as proven empty.
 *
 * During GEQO planning, this can get invoked more than once on the same
 * baserel struct, so it's worth checking to see if the rel is already marked
 * dummy.
 *
 * Also, when called during GEQO join planning, we are in a short-lived
 * memory context.  We must make sure that the dummy path attached to a
 * baserel survives the GEQO cycle, else the baserel is trashed for future
 * GEQO cycles.  On the other hand, when we are marking a joinrel during GEQO,
 * we don't want the dummy path to clutter the main planning context.  Upshot
 * is that the best solution is to explicitly make the dummy path in the same
 * context the given RelOptInfo is in.
 */
/*
 * mark_dummy_rel - (中文)把一个关系标记为"已证明为空"
 *
 * 【作用】当规划器证明某关系不会产生任何行时(如限制恒为 FALSE、输入关系
 * 为空),调用本函数:清空既有路径、把行数估计置 0、放入一条无子节点的
 * Append 路径作为 dummy 标记。
 *
 * 【设计思想】
 * - 已标记时直接返回(GEQO 规划中同一个基表可能被重复调用本函数);
 * - 内存上下文:GEQO 连接规划运行在短生命周期的上下文里,而基表结构要跨
 *   GEQO 循环存活,因此 dummy 路径必须创建在 rel 所在的上下文
 *   (GetMemoryChunkContext(rel))中;反之标记 joinrel 时又不希望它污染主
 *   规划上下文——统一在 rel 所在上下文创建正好两全;
 * - 行数置 0、pathlist / partial_pathlist 清空,再通过 add_path() 加入
 *   无子节点 Append(dummy 路径成本为零),最后 set_cheapest() 刷新最便宜
 *   路径字段。
 *
 * 【参数】rel —— 待标记为空的关系。
 * 【返回值】无。
 */
void
mark_dummy_rel(RelOptInfo *rel)
{
	MemoryContext oldcontext;
	AppendPathInput in = {0};

	/* Already marked? */
	if (is_dummy_rel(rel))
		return;

	/* No, so choose correct context to make the dummy path in */
	oldcontext = MemoryContextSwitchTo(GetMemoryChunkContext(rel));

	/* Set dummy size estimate */
	rel->rows = 0;

	/* Evict any previously chosen paths */
	rel->pathlist = NIL;
	rel->partial_pathlist = NIL;

	/* Set up the dummy path */
	add_path(rel, (Path *) create_append_path(NULL, rel, in,
											  NIL, rel->lateral_relids,
											  0, false, -1));

	/* Set or update cheapest_total_path and related fields */
	set_cheapest(rel);

	MemoryContextSwitchTo(oldcontext);
}


/*
 * restriction_is_constant_false --- is a restrictlist just FALSE?
 *
 * In cases where a qual is provably constant FALSE, eval_const_expressions
 * will generally have thrown away anything that's ANDed with it.  In outer
 * join situations this will leave us computing cartesian products only to
 * decide there's no match for an outer row, which is pretty stupid.  So,
 * we need to detect the case.
 *
 * If only_pushed_down is true, then consider only quals that are pushed-down
 * from the point of view of the joinrel.
 */
/*
 * restriction_is_constant_false - (中文)判断 restrictlist 中是否存在"恒为
 * FALSE"的限制子句
 *
 * 【作用】populate_joinrel_with_paths() 调用本函数,检测限制列表里是否有
 * 可证明恒为 FALSE 的子句,以便把整个连接或某侧输入标记为 dummy,避免只
 * 为验证"外层行没有匹配"而计算笛卡尔积。
 *
 * 【设计思想】正常情况下 eval_const_expressions() 会把与常量 FALSE 相与的
 * 子句全部折叠掉;但在外层连接场景,其他 qual 可能被下推到外层连接层,所以
 * 列表里可能还残留其他成员,必须逐条检查。常量 NULL 与常量 FALSE 在本用途
 * 上等价(都不能产生匹配行)。only_pushed_down 为 true 时只检查从本 joinrel
 * 视角"已下推"(RINFO_IS_PUSHED_DOWN)的子句。
 *
 * 【参数】
 *   restrictlist     —— 限制子句列表;
 *   joinrel          —— 相关连接关系(用于判断下推);
 *   only_pushed_down —— true:只看已下推的子句;false:全部子句。
 * 【返回值】true:存在恒为 FALSE(或 NULL)的常量子句;false:否则。
 */
static bool
restriction_is_constant_false(List *restrictlist,
							  RelOptInfo *joinrel,
							  bool only_pushed_down)
{
	ListCell   *lc;

	/*
	 * Despite the above comment, the restriction list we see here might
	 * possibly have other members besides the FALSE constant, since other
	 * quals could get "pushed down" to the outer join level.  So we check
	 * each member of the list.
	 */
	foreach(lc, restrictlist)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc);

		if (only_pushed_down && !RINFO_IS_PUSHED_DOWN(rinfo, joinrel->relids))
			continue;

		if (rinfo->clause && IsA(rinfo->clause, Const))
		{
			Const	   *con = (Const *) rinfo->clause;

			/* constant NULL is as good as constant FALSE for our purposes */
			if (con->constisnull)
				return true;
			if (!DatumGetBool(con->constvalue))
				return true;
		}
	}
	return false;
}

/*
 * Assess whether join between given two partitioned relations can be broken
 * down into joins between matching partitions; a technique called
 * "partitionwise join"
 *
 * Partitionwise join is possible when a. Joining relations have same
 * partitioning scheme b. There exists an equi-join between the partition keys
 * of the two relations.
 *
 * Partitionwise join is planned as follows (details: optimizer/README.)
 *
 * 1. Create the RelOptInfos for joins between matching partitions i.e
 * child-joins and add paths to them.
 *
 * 2. Construct Append or MergeAppend paths across the set of child joins.
 * This second phase is implemented by generate_partitionwise_join_paths().
 *
 * The RelOptInfo, SpecialJoinInfo and restrictlist for each child join are
 * obtained by translating the respective parent join structures.
 */
/*
 * try_partitionwise_join - (中文)评估并实施"分区连接"(partitionwise join)
 *
 * 【作用】populate_joinrel_with_paths() 在生成完父级连接路径后调用本函数:
 * 若两个输入关系共享同一分区方案且分区键之间存在等值连接,则把父连接分解
 * 为"匹配分区对之间的子连接",为每个子连接构建子 joinrel 并填充路径,上层
 * 再通过 generate_partitionwise_join_paths() 汇总成 Append/MergeAppend。
 *
 * 【设计思想】
 * - 前置条件:joinrel 已分区(part_scheme 非空、nparts > 0),双方都是分区
 *   关系,且考虑分区连接(consider_partitionwise_join);任一不满足则返回;
 * - compute_partition_bounds() 计算连接关系的分区边界与匹配的分区对
 *   (parts1 / parts2):边界相同则同位配对,否则调用 partition_bounds_merge
 *   合并边界;
 * - 主循环:对每个分区段,取出子关系对,依据父连接类型跳过可证明为空的段
 *   (规则与 populate_joinrel_with_paths 对 dummy 输入的处理等价);子关系
 *   被整体剪除(NULL)或是不完整(consider_partitionwise_join=false)则放弃
 *   整个分区连接(joinrel->nparts = 0);
 * - 用 build_child_join_sjinfo() 翻译父 SJ,用 adjust_appendrel_attrs()
 *   翻译 restrictlist 与 relids,再 build_child_join_rel() 构建/复用子
 *   joinrel,最后 make_grouped_join_rel() + populate_joinrel_with_paths()
 *   生成子连接路径;
 * - 每轮迭代末 eager 释放局部对象(appinfos、child_relids、子 SJ),避免
 *   成千上万分区时内存膨胀;
 * - check_stack_depth() 防止过深分区层级导致栈溢出。
 *
 * 【参数】
 *   root              —— PlannerInfo;
 *   rel1, rel2        —— 两个输入(分区)关系;
 *   joinrel           —— 父连接关系;
 *   parent_sjinfo     —— 父连接的 SpecialJoinInfo;
 *   parent_restrictlist —— 父连接的子句列表。
 * 【返回值】无。
 */
static void
try_partitionwise_join(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2,
					   RelOptInfo *joinrel, SpecialJoinInfo *parent_sjinfo,
					   List *parent_restrictlist)
{
	bool		rel1_is_simple = IS_SIMPLE_REL(rel1);
	bool		rel2_is_simple = IS_SIMPLE_REL(rel2);
	List	   *parts1 = NIL;
	List	   *parts2 = NIL;
	ListCell   *lcr1 = NULL;
	ListCell   *lcr2 = NULL;
	int			cnt_parts;

	/* Guard against stack overflow due to overly deep partition hierarchy. */
	check_stack_depth();

	/* Nothing to do, if the join relation is not partitioned. */
	if (joinrel->part_scheme == NULL || joinrel->nparts == 0)
		return;

	/* The join relation should have consider_partitionwise_join set. */
	Assert(joinrel->consider_partitionwise_join);

	/*
	 * We can not perform partitionwise join if either of the joining
	 * relations is not partitioned.
	 */
	if (!IS_PARTITIONED_REL(rel1) || !IS_PARTITIONED_REL(rel2))
		return;

	Assert(REL_HAS_ALL_PART_PROPS(rel1) && REL_HAS_ALL_PART_PROPS(rel2));

	/* The joining relations should have consider_partitionwise_join set. */
	Assert(rel1->consider_partitionwise_join &&
		   rel2->consider_partitionwise_join);

	/*
	 * The partition scheme of the join relation should match that of the
	 * joining relations.
	 */
	Assert(joinrel->part_scheme == rel1->part_scheme &&
		   joinrel->part_scheme == rel2->part_scheme);

	Assert(!(joinrel->partbounds_merged && (joinrel->nparts <= 0)));

	compute_partition_bounds(root, rel1, rel2, joinrel, parent_sjinfo,
							 &parts1, &parts2);

	if (joinrel->partbounds_merged)
	{
		lcr1 = list_head(parts1);
		lcr2 = list_head(parts2);
	}

	/*
	 * Create child-join relations for this partitioned join, if those don't
	 * exist. Add paths to child-joins for a pair of child relations
	 * corresponding to the given pair of parent relations.
	 */
	for (cnt_parts = 0; cnt_parts < joinrel->nparts; cnt_parts++)
	{
		RelOptInfo *child_rel1;
		RelOptInfo *child_rel2;
		bool		rel1_empty;
		bool		rel2_empty;
		SpecialJoinInfo *child_sjinfo;
		List	   *child_restrictlist;
		RelOptInfo *child_joinrel;
		AppendRelInfo **appinfos;
		int			nappinfos;
		Relids		child_relids;

		if (joinrel->partbounds_merged)
		{
			child_rel1 = lfirst_node(RelOptInfo, lcr1);
			child_rel2 = lfirst_node(RelOptInfo, lcr2);
			lcr1 = lnext(parts1, lcr1);
			lcr2 = lnext(parts2, lcr2);
		}
		else
		{
			child_rel1 = rel1->part_rels[cnt_parts];
			child_rel2 = rel2->part_rels[cnt_parts];
		}

		rel1_empty = (child_rel1 == NULL || IS_DUMMY_REL(child_rel1));
		rel2_empty = (child_rel2 == NULL || IS_DUMMY_REL(child_rel2));

		/*
		 * Check for cases where we can prove that this segment of the join
		 * returns no rows, due to one or both inputs being empty (including
		 * inputs that have been pruned away entirely).  If so just ignore it.
		 * These rules are equivalent to populate_joinrel_with_paths's rules
		 * for dummy input relations.
		 */
		switch (parent_sjinfo->jointype)
		{
			case JOIN_INNER:
			case JOIN_SEMI:
				if (rel1_empty || rel2_empty)
					continue;	/* ignore this join segment */
				break;
			case JOIN_LEFT:
			case JOIN_ANTI:
				if (rel1_empty)
					continue;	/* ignore this join segment */
				break;
			case JOIN_FULL:
				if (rel1_empty && rel2_empty)
					continue;	/* ignore this join segment */
				break;
			default:
				/* other values not expected here */
				elog(ERROR, "unrecognized join type: %d",
					 (int) parent_sjinfo->jointype);
				break;
		}

		/*
		 * If a child has been pruned entirely then we can't generate paths
		 * for it, so we have to reject partitionwise joining unless we were
		 * able to eliminate this partition above.
		 */
		if (child_rel1 == NULL || child_rel2 == NULL)
		{
			/*
			 * Mark the joinrel as unpartitioned so that later functions treat
			 * it correctly.
			 */
			joinrel->nparts = 0;
			return;
		}

		/*
		 * If a leaf relation has consider_partitionwise_join=false, it means
		 * that it's a dummy relation for which we skipped setting up tlist
		 * expressions and adding EC members in set_append_rel_size(), so
		 * again we have to fail here.
		 */
		if (rel1_is_simple && !child_rel1->consider_partitionwise_join)
		{
			Assert(child_rel1->reloptkind == RELOPT_OTHER_MEMBER_REL);
			Assert(IS_DUMMY_REL(child_rel1));
			joinrel->nparts = 0;
			return;
		}
		if (rel2_is_simple && !child_rel2->consider_partitionwise_join)
		{
			Assert(child_rel2->reloptkind == RELOPT_OTHER_MEMBER_REL);
			Assert(IS_DUMMY_REL(child_rel2));
			joinrel->nparts = 0;
			return;
		}

		/* We should never try to join two overlapping sets of rels. */
		Assert(!bms_overlap(child_rel1->relids, child_rel2->relids));

		/*
		 * Construct SpecialJoinInfo from parent join relations's
		 * SpecialJoinInfo.
		 */
		child_sjinfo = build_child_join_sjinfo(root, parent_sjinfo,
											   child_rel1->relids,
											   child_rel2->relids);

		/* Find the AppendRelInfo structures */
		child_relids = bms_union(child_rel1->relids, child_rel2->relids);
		appinfos = find_appinfos_by_relids(root, child_relids,
										   &nappinfos);

		/*
		 * Construct restrictions applicable to the child join from those
		 * applicable to the parent join.
		 */
		child_restrictlist =
			(List *) adjust_appendrel_attrs(root,
											(Node *) parent_restrictlist,
											nappinfos, appinfos);

		/* Find or construct the child join's RelOptInfo */
		child_joinrel = joinrel->part_rels[cnt_parts];
		if (!child_joinrel)
		{
			child_joinrel = build_child_join_rel(root, child_rel1, child_rel2,
												 joinrel, child_restrictlist,
												 child_sjinfo, nappinfos, appinfos);
			joinrel->part_rels[cnt_parts] = child_joinrel;
			joinrel->live_parts = bms_add_member(joinrel->live_parts, cnt_parts);
			joinrel->all_partrels = bms_add_members(joinrel->all_partrels,
													child_joinrel->relids);
		}

		/* Assert we got the right one */
		Assert(bms_equal(child_joinrel->relids,
						 adjust_child_relids(joinrel->relids,
											 nappinfos, appinfos)));

		/* Build a grouped join relation for 'child_joinrel' if possible */
		make_grouped_join_rel(root, child_rel1, child_rel2,
							  child_joinrel, child_sjinfo,
							  child_restrictlist);

		/* And make paths for the child join */
		populate_joinrel_with_paths(root, child_rel1, child_rel2,
									child_joinrel, child_sjinfo,
									child_restrictlist);

		/*
		 * When there are thousands of partitions involved, this loop will
		 * accumulate a significant amount of memory usage from objects that
		 * are only needed within the loop.  Free these local objects eagerly
		 * at the end of each iteration.
		 */
		pfree(appinfos);
		bms_free(child_relids);
		free_child_join_sjinfo(child_sjinfo, parent_sjinfo);
	}
}

/*
 * Construct the SpecialJoinInfo for a child-join by translating
 * SpecialJoinInfo for the join between parents. left_relids and right_relids
 * are the relids of left and right side of the join respectively.
 *
 * If translations are added to or removed from this function, consider
 * updating free_child_join_sjinfo() accordingly.
 */
/*
 * build_child_join_sjinfo - (中文)由父连接的 SpecialJoinInfo 构造子连接的
 * SpecialJoinInfo
 *
 * 【作用】try_partitionwise_join() 为每个子连接调用本函数:把父级 SJ 的
 * min_/syn_lefthand 与 min_/syn_righthand 从父 relids 翻译成子 relids,并
 * 翻译 semi_rhs_exprs,得到子连接的 SJ。
 *
 * 【设计思想】
 * - 父连接是纯内连接(JOIN_INNER,ojrelid == 0)时,直接构造哑 SJ,无需
 *   翻译;
 * - 否则整体 memcpy 父 SJ,再分别用 adjust_child_relids() 把左/右 relids
 *   翻译到子关系(左/右各自用对应侧的 AppendRelInfo),用
 *   adjust_appendrel_attrs() 翻译 semi_rhs_exprs;ojrelid 等外层连接标识
 *   不需要调整(子连接共享同一 OJ 节点);
 * - 注意:翻译出的字段是指向新分配结构的,因此配对函数
 *   free_child_join_sjinfo() 需要知道哪些字段是翻译副本、哪些与父共享。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   parent_sjinfo —— 父连接的 SpecialJoinInfo;
 *   left_relids   —— 子连接左侧(rel1 侧)的子 relids;
 *   right_relids  —— 子连接右侧(rel2 侧)的子 relids。
 * 【返回值】新建的、字段已翻译的子连接 SpecialJoinInfo(调用方负责释放)。
 */
static SpecialJoinInfo *
build_child_join_sjinfo(PlannerInfo *root, SpecialJoinInfo *parent_sjinfo,
						Relids left_relids, Relids right_relids)
{
	SpecialJoinInfo *sjinfo = makeNode(SpecialJoinInfo);
	AppendRelInfo **left_appinfos;
	int			left_nappinfos;
	AppendRelInfo **right_appinfos;
	int			right_nappinfos;

	/* Dummy SpecialJoinInfos can be created without any translation. */
	if (parent_sjinfo->jointype == JOIN_INNER)
	{
		Assert(parent_sjinfo->ojrelid == 0);
		init_dummy_sjinfo(sjinfo, left_relids, right_relids);
		return sjinfo;
	}

	memcpy(sjinfo, parent_sjinfo, sizeof(SpecialJoinInfo));
	left_appinfos = find_appinfos_by_relids(root, left_relids,
											&left_nappinfos);
	right_appinfos = find_appinfos_by_relids(root, right_relids,
											 &right_nappinfos);

	sjinfo->min_lefthand = adjust_child_relids(sjinfo->min_lefthand,
											   left_nappinfos, left_appinfos);
	sjinfo->min_righthand = adjust_child_relids(sjinfo->min_righthand,
												right_nappinfos,
												right_appinfos);
	sjinfo->syn_lefthand = adjust_child_relids(sjinfo->syn_lefthand,
											   left_nappinfos, left_appinfos);
	sjinfo->syn_righthand = adjust_child_relids(sjinfo->syn_righthand,
												right_nappinfos,
												right_appinfos);
	/* outer-join relids need no adjustment */
	sjinfo->semi_rhs_exprs = (List *) adjust_appendrel_attrs(root,
															 (Node *) sjinfo->semi_rhs_exprs,
															 right_nappinfos,
															 right_appinfos);

	pfree(left_appinfos);
	pfree(right_appinfos);

	return sjinfo;
}

/*
 * free_child_join_sjinfo
 *		Free memory consumed by a SpecialJoinInfo created by
 *		build_child_join_sjinfo()
 *
 * Only members that are translated copies of their counterpart in the parent
 * SpecialJoinInfo are freed here.
 */
/*
 * free_child_join_sjinfo - (中文)释放 build_child_join_sjinfo() 创建的子
 * 连接 SpecialJoinInfo
 *
 * 【作用】try_partitionwise_join() 每轮迭代结束调用本函数回收子 SJ 占用的
 * 内存,防止大量分区时内存膨胀。
 *
 * 【设计思想】只有"翻译副本"(即 build_child_join_sjinfo 中新分配、与父
 * 节点不同的字段)才需要释放:min_/syn_lefthand/righthand 若与父 SJ 对应
 * 字段不是同一对象,则 bms_free。commute_above_l/r 与 commute_below_l/r、
 * semi_operators 断言与父一致(共享,不释放);semi_rhs_exprs 理论上也是
 * 翻译副本,但简单 pfree 不够,所以不动它。内连接的哑 SJ 没有任何翻译字段,
 * 直接释放结构本身即可。
 *
 * 【参数】
 *   child_sjinfo  —— 子连接 SJ(由 build_child_join_sjinfo 创建);
 *   parent_sjinfo —— 父连接 SJ(用于对照判断字段是否共享)。
 * 【返回值】无。
 */
static void
free_child_join_sjinfo(SpecialJoinInfo *child_sjinfo,
					   SpecialJoinInfo *parent_sjinfo)
{
	/*
	 * Dummy SpecialJoinInfos of inner joins do not have any translated fields
	 * and hence no fields that to be freed.
	 */
	if (child_sjinfo->jointype != JOIN_INNER)
	{
		if (child_sjinfo->min_lefthand != parent_sjinfo->min_lefthand)
			bms_free(child_sjinfo->min_lefthand);

		if (child_sjinfo->min_righthand != parent_sjinfo->min_righthand)
			bms_free(child_sjinfo->min_righthand);

		if (child_sjinfo->syn_lefthand != parent_sjinfo->syn_lefthand)
			bms_free(child_sjinfo->syn_lefthand);

		if (child_sjinfo->syn_righthand != parent_sjinfo->syn_righthand)
			bms_free(child_sjinfo->syn_righthand);

		Assert(child_sjinfo->commute_above_l == parent_sjinfo->commute_above_l);
		Assert(child_sjinfo->commute_above_r == parent_sjinfo->commute_above_r);
		Assert(child_sjinfo->commute_below_l == parent_sjinfo->commute_below_l);
		Assert(child_sjinfo->commute_below_r == parent_sjinfo->commute_below_r);

		Assert(child_sjinfo->semi_operators == parent_sjinfo->semi_operators);

		/*
		 * semi_rhs_exprs may in principle be freed, but a simple pfree() does
		 * not suffice, so we leave it alone.
		 */
	}

	pfree(child_sjinfo);
}

/*
 * compute_partition_bounds
 *		Compute the partition bounds for a join rel from those for inputs
 */
/*
 * compute_partition_bounds - (中文)根据输入关系的分区边界计算连接关系的
 * 分区边界与匹配的分区对
 *
 * 【作用】try_partitionwise_join() 调用本函数:为 joinrel 计算分区边界
 * (boundinfo / nparts / part_rels),并产生与每个分区段对应的匹配分区对
 * (parts1 / parts2)。
 *
 * 【设计思想】分两种情况:
 * - joinrel->nparts == -1(边界尚未计算):若两个输入都未合并边界、分区数
 *   相同且边界逐点相等(partition_bounds_equal),则直接复用 rel1 的
 *   boundinfo,同位分区即配对(不劳合并);否则调用 partition_bounds_merge()
 *   合并边界,产出 parts1/parts2,并置 partbounds_merged 标志;合并失败
 *   (boundinfo == NULL)则 nparts = 0,放弃分区连接;
 * - nparts > 0(之前已计算):若 partbounds_merged 为真,输入边界不保证
 *   一致,须调用 get_matching_part_pairs() 从已构建的子 joinrel 反推匹配
 *   分区对;否则(边界一致)同位配对,无需额外处理。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   rel1, rel2    —— 两个输入(分区)关系;
 *   joinrel       —— 连接关系(就地填充 boundinfo/nparts/part_rels);
 *   parent_sjinfo —— 父连接 SJ(合并边界时需知道连接类型);
 *   parts1, parts2 —— 出参:与 joinrel 各分区段对应的两个输入分区列表。
 * 【返回值】无。
 */
static void
compute_partition_bounds(PlannerInfo *root, RelOptInfo *rel1,
						 RelOptInfo *rel2, RelOptInfo *joinrel,
						 SpecialJoinInfo *parent_sjinfo,
						 List **parts1, List **parts2)
{
	/*
	 * If we don't have the partition bounds for the join rel yet, try to
	 * compute those along with pairs of partitions to be joined.
	 */
	if (joinrel->nparts == -1)
	{
		PartitionScheme part_scheme = joinrel->part_scheme;
		PartitionBoundInfo boundinfo = NULL;
		int			nparts = 0;

		Assert(joinrel->boundinfo == NULL);
		Assert(joinrel->part_rels == NULL);

		/*
		 * See if the partition bounds for inputs are exactly the same, in
		 * which case we don't need to work hard: the join rel will have the
		 * same partition bounds as inputs, and the partitions with the same
		 * cardinal positions will form the pairs.
		 *
		 * Note: even in cases where one or both inputs have merged bounds, it
		 * would be possible for both the bounds to be exactly the same, but
		 * it seems unlikely to be worth the cycles to check.
		 */
		if (!rel1->partbounds_merged &&
			!rel2->partbounds_merged &&
			rel1->nparts == rel2->nparts &&
			partition_bounds_equal(part_scheme->partnatts,
								   part_scheme->parttyplen,
								   part_scheme->parttypbyval,
								   rel1->boundinfo, rel2->boundinfo))
		{
			boundinfo = rel1->boundinfo;
			nparts = rel1->nparts;
		}
		else
		{
			/* Try merging the partition bounds for inputs. */
			boundinfo = partition_bounds_merge(part_scheme->partnatts,
											   part_scheme->partsupfunc,
											   part_scheme->partcollation,
											   rel1, rel2,
											   parent_sjinfo->jointype,
											   parts1, parts2);
			if (boundinfo == NULL)
			{
				joinrel->nparts = 0;
				return;
			}
			nparts = list_length(*parts1);
			joinrel->partbounds_merged = true;
		}

		Assert(nparts > 0);
		joinrel->boundinfo = boundinfo;
		joinrel->nparts = nparts;
		joinrel->part_rels = palloc0_array(RelOptInfo *, nparts);
	}
	else
	{
		Assert(joinrel->nparts > 0);
		Assert(joinrel->boundinfo);
		Assert(joinrel->part_rels);

		/*
		 * If the join rel's partbounds_merged flag is true, it means inputs
		 * are not guaranteed to have the same partition bounds, therefore we
		 * can't assume that the partitions at the same cardinal positions
		 * form the pairs; let get_matching_part_pairs() generate the pairs.
		 * Otherwise, nothing to do since we can assume that.
		 */
		if (joinrel->partbounds_merged)
		{
			get_matching_part_pairs(root, joinrel, rel1, rel2,
									parts1, parts2);
			Assert(list_length(*parts1) == joinrel->nparts);
			Assert(list_length(*parts2) == joinrel->nparts);
		}
	}
}

/*
 * get_matching_part_pairs
 *		Generate pairs of partitions to be joined from inputs
 */
/*
 * get_matching_part_pairs - (中文)根据已构建的子连接关系生成输入侧的分区
 * 匹配对
 *
 * 【作用】compute_partition_bounds() 在 joinrel 的 partbounds_merged 为真
 * (输入边界不一致)时调用本函数:遍历 joinrel->part_rels(各分区段的子
 * joinrel),为每段从 rel1 侧与 rel2 侧各解析出一个子关系,填进 parts1 /
 * parts2,与 joinrel 各分区段一一对应。
 *
 * 【设计思想】
 * - 某段子 joinrel 为空(NULL):说明此前 try_partitionwise_join() 已因输入
 *   为空而跳过该段,这里也对应地放入两个 NULL,让后续逻辑再次跳过;
 * - 对每段,用 bms_intersect 把子 joinrel 的 relids 分别与 rel1->all_partrels
 *   (或 rel2)求交,得到属于 rel1 侧(或 rel2 侧)的分区 relids;断言其成员
 *   数与该侧父关系基表数一致;
 * - 简单关系(IS_SIMPLE_REL)按唯一 varno 用 find_base_rel 取子表,否则用
 *   find_join_rel 取子连接关系;断言非空——因为该段子 joinrel 存在,意味着
 *   输入侧相应的子关系此前必然已被构建(边界匹配/重叠的指定分区会被视为
 *   待连接对象)。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   joinrel —— 分区连接关系(其 part_rels 保存各段子 joinrel);
 *   rel1    —— 输入侧 1(其 all_partrels 列出该侧全部子关系 relids);
 *   rel2    —— 输入侧 2;
 *   parts1, parts2 —— 出参:与 joinrel 各分区段对应的两侧子关系列表。
 * 【返回值】无。
 */
static void
get_matching_part_pairs(PlannerInfo *root, RelOptInfo *joinrel,
						RelOptInfo *rel1, RelOptInfo *rel2,
						List **parts1, List **parts2)
{
	bool		rel1_is_simple = IS_SIMPLE_REL(rel1);
	bool		rel2_is_simple = IS_SIMPLE_REL(rel2);
	int			cnt_parts;

	*parts1 = NIL;
	*parts2 = NIL;

	for (cnt_parts = 0; cnt_parts < joinrel->nparts; cnt_parts++)
	{
		RelOptInfo *child_joinrel = joinrel->part_rels[cnt_parts];
		RelOptInfo *child_rel1;
		RelOptInfo *child_rel2;
		Relids		child_relids1;
		Relids		child_relids2;

		/*
		 * If this segment of the join is empty, it means that this segment
		 * was ignored when previously creating child-join paths for it in
		 * try_partitionwise_join() as it would not contribute to the join
		 * result, due to one or both inputs being empty; add NULL to each of
		 * the given lists so that this segment will be ignored again in that
		 * function.
		 */
		if (!child_joinrel)
		{
			*parts1 = lappend(*parts1, NULL);
			*parts2 = lappend(*parts2, NULL);
			continue;
		}

		/*
		 * Get a relids set of partition(s) involved in this join segment that
		 * are from the rel1 side.
		 */
		child_relids1 = bms_intersect(child_joinrel->relids,
									  rel1->all_partrels);
		Assert(bms_num_members(child_relids1) == bms_num_members(rel1->relids));

		/*
		 * Get a child rel for rel1 with the relids.  Note that we should have
		 * the child rel even if rel1 is a join rel, because in that case the
		 * partitions specified in the relids would have matching/overlapping
		 * boundaries, so the specified partitions should be considered as
		 * ones to be joined when planning partitionwise joins of rel1,
		 * meaning that the child rel would have been built by the time we get
		 * here.
		 */
		if (rel1_is_simple)
		{
			int			varno = bms_singleton_member(child_relids1);

			child_rel1 = find_base_rel(root, varno);
		}
		else
			child_rel1 = find_join_rel(root, child_relids1);
		Assert(child_rel1);

		/*
		 * Get a relids set of partition(s) involved in this join segment that
		 * are from the rel2 side.
		 */
		child_relids2 = bms_intersect(child_joinrel->relids,
									  rel2->all_partrels);
		Assert(bms_num_members(child_relids2) == bms_num_members(rel2->relids));

		/*
		 * Get a child rel for rel2 with the relids.  See above comments.
		 */
		if (rel2_is_simple)
		{
			int			varno = bms_singleton_member(child_relids2);

			child_rel2 = find_base_rel(root, varno);
		}
		else
			child_rel2 = find_join_rel(root, child_relids2);
		Assert(child_rel2);

		/*
		 * The join of rel1 and rel2 is legal, so is the join of the child
		 * rels obtained above; add them to the given lists as a join pair
		 * producing this join segment.
		 */
		*parts1 = lappend(*parts1, child_rel1);
		*parts2 = lappend(*parts2, child_rel2);
	}
}
