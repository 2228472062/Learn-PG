/*-------------------------------------------------------------------------
 *
 * joininfo.c
 *	  joininfo list manipulation routines
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件提供对"连接信息(joininfo)列表"的增删查操作。joininfo 是挂在
 * 每个基表 RelOptInfo 上的一个列表,记录所有"语义上需要该基表参与的
 * 连接条件"(join clause)。规划器在 deconstruct_jointree 阶段把每个连接
 * 条件登记到相关基表的 joininfo 列表;在连接路径生成阶段则通过
 * have_relevant_joinclause 判断两个关系之间是否确实存在连接线索,从而
 * 决定是否值得为这两个关系生成连接路径。
 *
 * 【核心数据结构】
 * - RelOptInfo.joininfo:List<RestrictInfo>,每个元素是一个连接条件;
 * - required_relids:RestrictInfo 中表示"计算该条件至少需要哪些关系"的
 *   位图集合。注意同一连接条件会出现在所有参与关系的 joininfo 列表里,
 *   且共享同一个 RestrictInfo 节点(通过指针链接),以便复用缓存信息。
 *
 * 【主要函数关系】
 * add_join_clause_to_rels 把一个连接条件追加到所有相关基表的 joininfo
 * 列表(同时处理"恒真/恒假"裁剪);remove_join_clause_from_rels 是它的
 * 逆操作(当发现某关系根本无需参与连接时删除);have_relevant_joinclause
 * 则被 joinpath.c 等模块用于探测两个关系间是否存在可用的连接线索,它
 * 除了扫描 joininfo 列表,还会检查等价类(EquivalenceClass)中隐含的
 * 连接关系(通过 have_relevant_eclass_joinclause)。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/joininfo.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "nodes/makefuncs.h"
#include "optimizer/joininfo.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/planmain.h"
#include "optimizer/restrictinfo.h"


/*
 * have_relevant_joinclause
 *		Detect whether there is a joinclause that involves
 *		the two given relations.
 *
 * Note: the joinclause does not have to be evaluable with only these two
 * relations.  This is intentional.  For example consider
 *		SELECT * FROM a, b, c WHERE a.x = (b.y + c.z)
 * If a is much larger than the other tables, it may be worthwhile to
 * cross-join b and c and then use an inner indexscan on a.x.  Therefore
 * we should consider this joinclause as reason to join b to c, even though
 * it can't be applied at that join step.
 */
/*
 * have_relevant_joinclause - (中文)判断两个关系之间是否存在相关的连接条件
 *
 * 【作用】规划器在 joinpath.c 等模块中调用本函数,判断给定的两个关系
 * (rel1、rel2)之间是否存在"可以推动二者做连接"的线索。若有,才值得为
 * 这两个关系生成连接路径;否则生成连接路径只会徒增开销。这是动态规划
 * 连接路径生成阶段"剪枝"的关键依据之一。
 *
 * 【设计思想】"相关连接条件"的定义很宽泛:只要某个连接条件的
 * required_relids 与另一个关系的 relids 有交集,就算相关——即使该条件
 * 无法仅用这两个关系求值(例如 a.x = (b.y + c.z) 这样的条件,虽然不能在
 * b⋈c 这一步应用,但仍可作为推动 b 与 c 连接的线索)。为了效率,优先扫描
 * 较短的 joininfo 列表;此外还必须检查等价类(EquivalenceClass)中可能
 * 隐含的连接关系——它们不会出现在 joininfo 列表里,因此当两个关系都
 * 标记了 has_eclass_joins 时,还要调用 have_relevant_eclass_joinclause。
 *
 * 【参数】
 *   root —— 规划上下文(PlannerInfo),用于等价类查询;
 *   rel1 —— 参与判断的第一个关系;
 *   rel2 —— 参与判断的第二个关系。
 * 【返回值】true:两个关系之间存在相关连接条件,值得生成连接路径;
 *          false:不存在。
 */
bool
have_relevant_joinclause(PlannerInfo *root,
						 RelOptInfo *rel1, RelOptInfo *rel2)
{
	bool		result = false;
	List	   *joininfo;
	Relids		other_relids;
	ListCell   *l;

	/*
	 * We could scan either relation's joininfo list; may as well use the
	 * shorter one.
	 */
	if (list_length(rel1->joininfo) <= list_length(rel2->joininfo))
	{
		joininfo = rel1->joininfo;
		other_relids = rel2->relids;
	}
	else
	{
		joininfo = rel2->joininfo;
		other_relids = rel1->relids;
	}

	foreach(l, joininfo)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(l);

		if (bms_overlap(other_relids, rinfo->required_relids))
		{
			result = true;
			break;
		}
	}

	/*
	 * We also need to check the EquivalenceClass data structure, which might
	 * contain relationships not emitted into the joininfo lists.
	 */
	if (!result && rel1->has_eclass_joins && rel2->has_eclass_joins)
		result = have_relevant_eclass_joinclause(root, rel1, rel2);

	return result;
}


/*
 * add_join_clause_to_rels
 *	  Add 'restrictinfo' to the joininfo list of each relation it requires.
 *
 * Note that the same copy of the restrictinfo node is linked to by all the
 * lists it is in.  This allows us to exploit caching of information about
 * the restriction clause (but we must be careful that the information does
 * not depend on context).
 *
 * 'restrictinfo' describes the join clause
 * 'join_relids' is the set of relations participating in the join clause
 *				 (some of these could be outer joins)
 */
/*
 * add_join_clause_to_rels - (中文)把一个连接条件登记到所有相关基表的
 * joininfo 列表
 *
 * 【作用】在 deconstruct_jointree 阶段,当分析出一个连接条件
 * (restrictinfo)需要 join_relids 中的关系参与时,把它追加到其中每个
 * "基表"的 joininfo 列表里。后续连接路径生成阶段就是靠这些列表判断
 * 关系之间是否存在连接线索的。
 *
 * 【设计思想】同一个 RestrictInfo 节点通过指针被链入多个基表的 joininfo
 * 列表(而不是复制),以复用其中缓存的代价/选择性等信息;这也要求缓存的
 * 信息不能依赖具体上下文。两个特例:
 * - 恒真条件(restriction_is_always_true)没有登记价值,直接丢弃;
 * - 恒假条件(restriction_is_always_false)则替换为一个常量 FALSE 的新
 *   RestrictInfo 再加入,以便在路径生成阶段直接把该关系裁剪为空。替换时
 *   保留原 rinfo_serial,并恢复 root->last_rinfo_serial 计数器,确保
 *   "同一语义"的条件在各处拿到相同的序列号(参见
 *   deconstruct_distribute_oj_quals 的注释)。
 *
 * 注意:join_relids 中可能含有外层连接(outer join)引入的伪 relid,它们
 * 在 simple_rel_array 中没有对应的基表,find_base_rel_ignore_join 会返回
 * NULL,此时跳过即可——joininfo 只登记在真正的基表上。
 *
 * 【参数】
 *   root         —— 规划上下文;
 *   restrictinfo —— 待登记(或被替换后)的连接条件;
 *   join_relids  —— 该连接条件涉及的所有关系(位图集合)。
 * 【返回值】无。
 */
void
add_join_clause_to_rels(PlannerInfo *root,
						RestrictInfo *restrictinfo,
						Relids join_relids)
{
	int			cur_relid;

	/* Don't add the clause if it is always true */
	if (restriction_is_always_true(root, restrictinfo))
		return;

	/*
	 * Substitute the origin qual with constant-FALSE if it is provably always
	 * false.
	 *
	 * Note that we need to keep the same rinfo_serial, since it is in
	 * practice the same condition.  We also need to reset the
	 * last_rinfo_serial counter, which is essential to ensure that the
	 * RestrictInfos for the "same" qual condition get identical serial
	 * numbers (see deconstruct_distribute_oj_quals).
	 */
	if (restriction_is_always_false(root, restrictinfo))
	{
		int			save_rinfo_serial = restrictinfo->rinfo_serial;
		int			save_last_rinfo_serial = root->last_rinfo_serial;

		restrictinfo = make_restrictinfo(root,
										 (Expr *) makeBoolConst(false, false),
										 restrictinfo->is_pushed_down,
										 restrictinfo->has_clone,
										 restrictinfo->is_clone,
										 restrictinfo->pseudoconstant,
										 0, /* security_level */
										 restrictinfo->required_relids,
										 restrictinfo->incompatible_relids,
										 restrictinfo->outer_relids);
		restrictinfo->rinfo_serial = save_rinfo_serial;
		root->last_rinfo_serial = save_last_rinfo_serial;
	}

	cur_relid = -1;
	while ((cur_relid = bms_next_member(join_relids, cur_relid)) >= 0)
	{
		RelOptInfo *rel = find_base_rel_ignore_join(root, cur_relid);

		/* We only need to add the clause to baserels */
		if (rel == NULL)
			continue;
		rel->joininfo = lappend(rel->joininfo, restrictinfo);
	}
}

/*
 * remove_join_clause_from_rels
 *	  Delete 'restrictinfo' from all the joininfo lists it is in
 *
 * This reverses the effect of add_join_clause_to_rels.  It's used when we
 * discover that a relation need not be joined at all.
 *
 * 'restrictinfo' describes the join clause
 * 'join_relids' is the set of relations participating in the join clause
 *				 (some of these could be outer joins)
 */
/*
 * remove_join_clause_from_rels - (中文)从所有相关基表的 joininfo 列表中
 * 删除一个连接条件
 *
 * 【作用】add_join_clause_to_rels 的逆操作:当规划过程发现某个关系根本
 * 无需参与连接(比如该关系被证明为空或已从连接树中移除)时,把先前登记的
 * 连接条件从各基表的 joininfo 列表里删除,以免后续生成无用的连接路径。
 *
 * 【设计思想】同样遍历 join_relids 中的每个基表(跳过伪 relid),用指针
 * 比较(list_member_ptr / list_delete_ptr)定位并删除该 RestrictInfo 节点。
 * 之所以可以用指针比较,是因为 add_join_clause_to_rels 登记的就是同一个
 * 节点指针。删除前用 Assert 校验节点确实在列表中,若断言失败说明逻辑上
 * 出现了"先删后加"或"重复添加"这类顺序错误。
 *
 * 【参数】
 *   root         —— 规划上下文;
 *   restrictinfo —— 要删除的连接条件节点;
 *   join_relids  —— 该连接条件涉及的所有关系(位图集合)。
 * 【返回值】无。
 */
void
remove_join_clause_from_rels(PlannerInfo *root,
							 RestrictInfo *restrictinfo,
							 Relids join_relids)
{
	int			cur_relid;

	cur_relid = -1;
	while ((cur_relid = bms_next_member(join_relids, cur_relid)) >= 0)
	{
		RelOptInfo *rel = find_base_rel_ignore_join(root, cur_relid);

		/* We would only have added the clause to baserels */
		if (rel == NULL)
			continue;

		/*
		 * Remove the restrictinfo from the list.  Pointer comparison is
		 * sufficient.
		 */
		Assert(list_member_ptr(rel->joininfo, restrictinfo));
		rel->joininfo = list_delete_ptr(rel->joininfo, restrictinfo);
	}
}
