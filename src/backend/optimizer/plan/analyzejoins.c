/*-------------------------------------------------------------------------
 *
 * analyzejoins.c
 *	  Routines for simplifying joins after initial query analysis
 *
 * While we do a great deal of join simplification in prep/prepjointree.c,
 * certain optimizations cannot be performed at that stage for lack of
 * detailed information about the query.  The routines here are invoked
 * after initsplan.c has done its work, and can do additional join removal
 * and simplification steps based on the information extracted.  The penalty
 * is that we have to work harder to clean up after ourselves when we modify
 * the query, since the derived data structures have to be updated too.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件实现"初步查询分析完成后的连接简化":在 prepjointree.c 已经做过大量
 * 连接简化(基于语法层面即可判断的信息)之后,本文件利用 initsplan.c 提取
 * 出的更详细信息(等价类、外连接子句、占位符、属性使用位图等),进一步做
 * 三类优化:
 *
 * 1. 去除无用外连接(remove_useless_joins 系列):当左连接的右端恰好是单个
 *    基础关系、且该内关系对连接子句而言可证明唯一(每行至多匹配一行)时,
 *    该外连接只是"复制左输入",可整段摘除。要求内关系的属性不被连接上层的
 *    任何结构引用。摘除后要把 PlannerInfo 中所有引用该关系/该连接的派生
 *    结构(SpecialJoinInfo、PlaceHolderInfo、等价类、RestrictInfo 的 relid
 *    位图等)一并清理;
 * 2. 半连接降级(reduce_unique_semijoins):当半连接的内关系对连接子句可证明
 *    唯一时,半连接等价于普通内连接,只需从 join_info_list 删掉对应
 *    SpecialJoinInfo 即可(连接树里的类型标注不再被使用,无需修改);
 * 3. 自连接消除(remove_useless_self_joins 系列):对同一张表出现多次(相同
 *    OID 的基础关系)的自连接,若连接子句是 X = X 形式、且每侧一行要么匹配
 *    同一物理行要么都不匹配,则可把其中一个关系当作"死关系"摘掉,并把所有
 *    引用改写指向保留的那个(改写 Var、RestrictInfo、等价类成员、行标记等)。
 *
 * 【设计思想】
 * - 唯一性证明(rel_is_distinct_for / innerrel_is_unique / query_is_distinct_for)
 *   是本模块的数学核心:基础关系靠唯一索引证明;子查询靠其自身的
 *   DISTINCT / GROUP BY / GROUPING SETS / 聚合 / HAVING / 集合运算(去重
 *   版)证明;证明依据"上层等值算子的操作符族兼容 + 排序规则一致";
 * - 结果缓存:innerrel_is_unique_ext 把已证唯一/已证不唯一的结果缓存到
 *   innerrel->unique_for_rels / non_unique_for_rels,避免重复计算;连接搜索
 *   自底向上进行,通常能先看到"最小充分"的外关系集合;
 * - 数据清理需"自食其果":本模块修改查询的同时必须同步更新已派生的数据
 *   结构,故大量辅助函数(remove_rel_from_restrictinfo /
 *   remove_rel_from_eclass / remove_rel_from_phvs 等)专门负责从各种结构中
 *   摘除/改写对已删关系的引用;attr_needed / ph_needed 位图还会通过
 *   rebuild_placeholder_attr_needed 等重建;
 * - 自连接消除按"关系 OID 排序分组"处理,把同 OID 的关系聚成一组,避免
 *   两两比较带来的二次方复杂度。
 *
 * 【核心数据结构】
 * - SpecialJoinInfo:外连接/半连接/反连接的"连接顺序约束"信息,含
 *   min_lefthand/min_righthand、ojrelid、commute_xxx(可与本外连接交换的
 *   外连接 relid 集合)等;
 * - RestrictInfo:一条限制/连接子句的规划信息(required_relids、
 *   clause_relids、can_join、mergeopfamilies、is_clone、rinfo_serial 等);
 * - PlaceHolderInfo:占位变量(子查询拉平产物)的求值位置/使用位图信息;
 * - EquivalenceClass:表达式等价类,由等值子句推导;
 * - UniqueRelInfo:唯一性证明的缓存条目(outerrelids、self_join、
 *   extra_clauses);
 * - SelfJoinCandidate:(relid, reloid) 对,用于自连接候选按 OID 排序。
 *
 * 【主要函数关系】
 * 顶层入口三个:remove_useless_joins(左连接消除)、reduce_unique_semijoins
 * (半连接降级)、remove_useless_self_joins(自连接消除),均由 planmain.c 的
 * query_planner() 按顺序调用。左连接消除由 join_is_removable 判定、
 * remove_leftjoinrel_from_query 执行;两者共用 remove_rel_from_query 及其
 * 辅助清理函数。唯一性证明链为 rel_supports_distinctness →
 * rel_is_distinct_for → (子查询)query_is_distinct_for;半连接/自连接场景
 * 走 innerrel_is_unique(_ext) → is_innerrel_unique_for → rel_is_distinct_for。
 * 自连接消除执行链为 remove_self_joins_recurse → remove_self_joins_one_group
 * → remove_self_join_rel(+update_eclasses / add_non_redundant_clauses /
 * replace_relid_callback 等)。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/plan/analyzejoins.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "catalog/pg_class.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/joininfo.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/placeholder.h"
#include "optimizer/planmain.h"
#include "optimizer/restrictinfo.h"
#include "parser/parse_agg.h"
#include "rewrite/rewriteManip.h"
#include "utils/lsyscache.h"

/*
 * Utility structure.  A sorting procedure is needed to simplify the search
 * of SJE-candidate baserels referencing the same database relation.  Having
 * collected all baserels from the query jointree, the planner sorts them
 * according to the reloid value, groups them with the next pass and attempts
 * to remove self-joins.
 *
 * Preliminary sorting prevents quadratic behavior that can be harmful in the
 * case of numerous joins.
 */
typedef struct
{
	int			relid;
	Oid			reloid;
} SelfJoinCandidate;

bool		enable_self_join_elimination;

/* local functions */
static bool join_is_removable(PlannerInfo *root, SpecialJoinInfo *sjinfo);
static void remove_leftjoinrel_from_query(PlannerInfo *root, int relid,
										  SpecialJoinInfo *sjinfo);
static void remove_rel_from_query(PlannerInfo *root, int relid,
								  int subst, SpecialJoinInfo *sjinfo,
								  Relids joinrelids);
static void remove_rel_from_restrictinfo(RestrictInfo *rinfo,
										 int relid, int ojrelid);
static void remove_rel_from_eclass(PlannerInfo *root, EquivalenceClass *ec,
								   int relid, int ojrelid);
static void remove_rel_from_restrictinfo_phvs(RestrictInfo *rinfo,
											  int relid, int ojrelid);
static Node *remove_rel_from_phvs(Node *node, int relid, int ojrelid);
static Node *remove_rel_from_phvs_mutator(Node *node, Relids removable);
static List *remove_rel_from_joinlist(List *joinlist, int relid, int *nremoved);
static bool rel_supports_distinctness(PlannerInfo *root, RelOptInfo *rel);
static bool rel_is_distinct_for(PlannerInfo *root, RelOptInfo *rel,
								List *clause_list, List **extra_clauses);
static DistinctColInfo *distinct_col_search(int colno, List *distinct_cols);
static bool is_innerrel_unique_for(PlannerInfo *root,
								   Relids joinrelids,
								   Relids outerrelids,
								   RelOptInfo *innerrel,
								   JoinType jointype,
								   List *restrictlist,
								   List **extra_clauses);
static int	self_join_candidates_cmp(const void *a, const void *b);
static bool replace_relid_callback(Node *node,
								   ChangeVarNodes_context *context);


/*
 * remove_useless_joins
 *		Check for relations that don't actually need to be joined at all,
 *		and remove them from the query.
 *
 * We are passed the current joinlist and return the updated list.  Other
 * data structures that have to be updated are accessible via "root".
 */
/*
 * remove_useless_joins - (中文)从查询中摘除无用的连接
 *
 * 【作用】检查哪些关系其实根本不需要参与连接,并把它们从查询中移除。输入
 * 是当前 joinlist,返回更新后的 joinlist;其它需要同步更新的数据结构都通过
 * root 访问。由 planmain.c 的 query_planner() 在等价类合并完成后、调用
 * make_one_rel() 之前调用。
 *
 * 【设计思想】
 * - 只关心"被左连接的对象":左连接的右端(内关系)在满足条件时可以被整
 *   个摘掉,因此只需扫描 root->join_info_list 里的 SpecialJoinInfo;
 * - 逐个检查 join_is_removable(),若可移除,取其 righthand 唯一的成员
 *   (已保证是单个 baserel)作为 innerrelid,调用
 *   remove_leftjoinrel_from_query() 把该关系连同对目标连接的引用从规划器
 *   数据结构中抹掉,再用 remove_rel_from_joinlist() 从 joinlist 中删除恰好
 *   一个引用(必须是 1 个,否则 elog 报错),并把这条 SpecialJoinInfo 从
 *   join_info_list 中删除;
 * - 用 goto restart 重新开始整个扫描:因为删除一个连接后,某属性的
 *   attr_needed 位图变化可能使之前"不可移除"的连接变为可移除,重扫可保证
 *   结果与 join_info_list 的遍历顺序无关。
 *
 * 【参数】
 *   root     —— PlannerInfo,其 join_info_list 会被修改(删除已消除连接的
 *               SpecialJoinInfo);
 *   joinlist —— 待处理的连接树列表,被删除关系的 RangeTblRef 会被移除。
 * 【返回值】更新后的 joinlist(结构可能与输入不同,是新建的 List)。
 */
List *
remove_useless_joins(PlannerInfo *root, List *joinlist)
{
	ListCell   *lc;

	/*
	 * We are only interested in relations that are left-joined to, so we can
	 * scan the join_info_list to find them easily.
	 */
restart:
	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(lc);
		int			innerrelid;
		int			nremoved;

		/* Skip if not removable */
		if (!join_is_removable(root, sjinfo))
			continue;

		/*
		 * Currently, join_is_removable can only succeed when the sjinfo's
		 * righthand is a single baserel.  Remove that rel from the query and
		 * joinlist.
		 */
		innerrelid = bms_singleton_member(sjinfo->min_righthand);

		remove_leftjoinrel_from_query(root, innerrelid, sjinfo);

		/* We verify that exactly one reference gets removed from joinlist */
		nremoved = 0;
		joinlist = remove_rel_from_joinlist(joinlist, innerrelid, &nremoved);
		if (nremoved != 1)
			elog(ERROR, "failed to find relation %d in joinlist", innerrelid);

		/*
		 * We can delete this SpecialJoinInfo from the list too, since it's no
		 * longer of interest.  (Since we'll restart the foreach loop
		 * immediately, we don't bother with foreach_delete_current.)
		 */
		root->join_info_list = list_delete_cell(root->join_info_list, lc);

		/*
		 * Restart the scan.  This is necessary to ensure we find all
		 * removable joins independently of ordering of the join_info_list
		 * (note that removal of attr_needed bits may make a join appear
		 * removable that did not before).
		 */
		goto restart;
	}

	return joinlist;
}

/*
 * join_is_removable
 *	  Check whether we need not perform this special join at all, because
 *	  it will just duplicate its left input.
 *
 * This is true for a left join for which the join condition cannot match
 * more than one inner-side row.  (There are other possibly interesting
 * cases, but we don't have the infrastructure to prove them.)  We also
 * have to check that the inner side doesn't generate any variables needed
 * above the join.
 */
/*
 * join_is_removable - (中文)判断某个特殊连接是否可以被移除
 *
 * 【作用】判断能否完全不需要执行该特殊连接(这里特指左连接),因为它只会
 * "复制"其左输入:当左连接的连接条件对内关系的每一行至多匹配一行时,外连接
 * 与直接取左输入在语义上等价。还需确认内关系没有任何被连接上层用到的变量。
 * 由 remove_useless_joins() 调用。
 *
 * 【设计思想】判定条件(全部满足才返回 true):
 * - 必须是 JOIN_LEFT,且 min_righthand 恰好是单个 baserel(否则无从下手);
 * - 不能是查询的结果关系(resultRelation,如 MERGE 构造出的合成连接树);
 * - 内关系必须"支持唯一性证明"(rel_supports_distinctness 预筛,即基础关系
 *   有唯一索引或子查询自身可证唯一);
 * - 内关系所有属性的 attr_needed 必须是 inputrelids 的子集:任何属性若被
 *   连接上层使用,移除后即"无家可归"。注意比较对象是 inputrelids 而非
 *   joinrelids,因为被下推的限定条件会把属性的需要标记到 OJ 自身的 relid 上;
 * - PlaceHolderInfo 检查:PHV 不能侧向引用内关系;若 PHV 在连接层求值且被
 *   上层使用,必须保证删除连接后仍存在求值位置(即 min_lefthand 与
 *   ph_eval_at 有交集),且 PHV 内表达式不引用内关系;
 * - 在 innerrel->joininfo 中收集"可合并连接的等值子句":子句必须是连接子句
 *   (非 pushed-down)、非 is_clone(避免与可交换外连接的克隆子句混淆)、
 *   can_join 且 mergeopfamilies 非空(mergejoinable 算子行为类似某个 btree
 *   操作符类下的等值,且能排除含易变函数的子句)、且两侧分别属于外/内
 *   关系(clause_sides_match_join);
 * - 最后用 rel_is_distinct_for() 证明内关系对这些子句唯一。
 *
 * 【参数】
 *   root   —— PlannerInfo,用于访问 base rel、placeholder_list 等;
 *   sjinfo —— 待检查的 SpecialJoinInfo(当前仅处理 JOIN_LEFT)。
 * 【返回值】true:该左连接可移除;false:不可移除。
 */
static bool
join_is_removable(PlannerInfo *root, SpecialJoinInfo *sjinfo)
{
	int			innerrelid;
	RelOptInfo *innerrel;
	Relids		inputrelids;
	Relids		joinrelids;
	List	   *clause_list = NIL;
	ListCell   *l;
	int			attroff;

	/*
	 * Must be a left join to a single baserel, else we aren't going to be
	 * able to do anything with it.
	 */
	if (sjinfo->jointype != JOIN_LEFT)
		return false;

	if (!bms_get_singleton_member(sjinfo->min_righthand, &innerrelid))
		return false;

	/*
	 * Never try to eliminate a left join to the query result rel.  Although
	 * the case is syntactically impossible in standard SQL, MERGE will build
	 * a join tree that looks exactly like that.
	 */
	if (innerrelid == root->parse->resultRelation)
		return false;

	innerrel = find_base_rel(root, innerrelid);

	/*
	 * Before we go to the effort of checking whether any innerrel variables
	 * are needed above the join, make a quick check to eliminate cases in
	 * which we will surely be unable to prove uniqueness of the innerrel.
	 */
	if (!rel_supports_distinctness(root, innerrel))
		return false;

	/* Compute the relid set for the join we are considering */
	inputrelids = bms_union(sjinfo->min_lefthand, sjinfo->min_righthand);
	Assert(sjinfo->ojrelid != 0);
	joinrelids = bms_copy(inputrelids);
	joinrelids = bms_add_member(joinrelids, sjinfo->ojrelid);

	/*
	 * We can't remove the join if any inner-rel attributes are used above the
	 * join.  Here, "above" the join includes pushed-down conditions, so we
	 * should reject if attr_needed includes the OJ's own relid; therefore,
	 * compare to inputrelids not joinrelids.
	 *
	 * As a micro-optimization, it seems better to start with max_attr and
	 * count down rather than starting with min_attr and counting up, on the
	 * theory that the system attributes are somewhat less likely to be wanted
	 * and should be tested last.
	 */
	for (attroff = innerrel->max_attr - innerrel->min_attr;
		 attroff >= 0;
		 attroff--)
	{
		if (!bms_is_subset(innerrel->attr_needed[attroff], inputrelids))
			return false;
	}

	/*
	 * Similarly check that the inner rel isn't needed by any PlaceHolderVars
	 * that will be used above the join.  The PHV case is a little bit more
	 * complicated, because PHVs may have been assigned a ph_eval_at location
	 * that includes the innerrel, yet their contained expression might not
	 * actually reference the innerrel (it could be just a constant, for
	 * instance).  If such a PHV is due to be evaluated above the join then it
	 * needn't prevent join removal.
	 */
	foreach(l, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(l);

		if (bms_overlap(phinfo->ph_lateral, innerrel->relids))
			return false;		/* it references innerrel laterally */
		if (!bms_overlap(phinfo->ph_eval_at, innerrel->relids))
			continue;			/* it definitely doesn't reference innerrel */
		if (bms_is_subset(phinfo->ph_needed, inputrelids))
			continue;			/* PHV is not used above the join */
		if (!bms_is_member(sjinfo->ojrelid, phinfo->ph_eval_at))
			return false;		/* it has to be evaluated below the join */

		/*
		 * We need to be sure there will still be a place to evaluate the PHV
		 * if we remove the join, ie that ph_eval_at wouldn't become empty.
		 */
		if (!bms_overlap(sjinfo->min_lefthand, phinfo->ph_eval_at))
			return false;		/* there isn't any other place to eval PHV */
		/* Check contained expression last, since this is a bit expensive */
		if (bms_overlap(pull_varnos(root, (Node *) phinfo->ph_var->phexpr),
						innerrel->relids))
			return false;		/* contained expression references innerrel */
	}

	/*
	 * Search for mergejoinable clauses that constrain the inner rel against
	 * either the outer rel or a pseudoconstant.  If an operator is
	 * mergejoinable then it behaves like equality for some btree opclass, so
	 * it's what we want.  The mergejoinability test also eliminates clauses
	 * containing volatile functions, which we couldn't depend on.
	 */
	foreach(l, innerrel->joininfo)
	{
		RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(l);

		/*
		 * If the current join commutes with some other outer join(s) via
		 * outer join identity 3, there will be multiple clones of its join
		 * clauses in the joininfo list.  We want to consider only the
		 * has_clone form of such clauses.  Processing more than one form
		 * would be wasteful, and also some of the others would confuse the
		 * RINFO_IS_PUSHED_DOWN test below.
		 */
		if (restrictinfo->is_clone)
			continue;			/* ignore it */

		/*
		 * If it's not a join clause for this outer join, we can't use it.
		 * Note that if the clause is pushed-down, then it is logically from
		 * above the outer join, even if it references no other rels (it might
		 * be from WHERE, for example).
		 */
		if (RINFO_IS_PUSHED_DOWN(restrictinfo, joinrelids))
			continue;			/* ignore; not useful here */

		/* Ignore if it's not a mergejoinable clause */
		if (!restrictinfo->can_join ||
			restrictinfo->mergeopfamilies == NIL)
			continue;			/* not mergejoinable */

		/*
		 * Check if the clause has the form "outer op inner" or "inner op
		 * outer", and if so mark which side is inner.
		 */
		if (!clause_sides_match_join(restrictinfo, sjinfo->min_lefthand,
									 innerrel->relids))
			continue;			/* no good for these input relations */

		/* OK, add to list */
		clause_list = lappend(clause_list, restrictinfo);
	}

	/*
	 * Now that we have the relevant equality join clauses, try to prove the
	 * innerrel distinct.
	 */
	if (rel_is_distinct_for(root, innerrel, clause_list, NULL))
		return true;

	/*
	 * Some day it would be nice to check for other methods of establishing
	 * distinctness.
	 */
	return false;
}

/*
 * Remove the target relid and references to the target join from the
 * planner's data structures, having determined that there is no need
 * to include them in the query.
 *
 * We are not terribly thorough here.  We only bother to update parts of
 * the planner's data structures that will actually be consulted later.
 */
/*
 * remove_leftjoinrel_from_query - (中文)把目标左连接及其内关系从规划器结构中摘除
 *
 * 【作用】在确认某左连接无需保留后,把内关系 relid 与对目标连接的引用从
 * 规划器的数据结构中清理掉。由 remove_useless_joins() 调用(对应左连接移除
 * 场景);自连接消除场景另有 remove_self_join_rel() 走更复杂的流程。
 *
 * 【设计思想】本函数是左连接移除的"收尾总务":
 * - 先调用共享清理函数 remove_rel_from_query()(传入 sjinfo 表示外连接
 *   移除,subst=-1 表示"删除而非替换")处理大部分共享结构;
 * - 再把引用该关系的连接子句从各 joininfo 列表移除:必须先用 list_copy
 *   复制 rel->joininfo,因为 remove_join_clause_from_rels() 会边扫描边销毁
 *   原列表;若子句相对 join_plus_commute(本连接 relid 集合并上所有可与本
 *   外连接交换的外连接 relid)而言属于 pushed-down,说明它逻辑上来自连接
 *   上层,不能丢,需清理其 relid 位图中对本关系的引用后重新分发回去
 *   (distribute_restrictinfo_to_rels)。注意 join_plus_commute 把 commute_*
 *   集合并入,是为了连"带外连接 relid 的克隆子句"一起清掉;
 * - 对伪常量/外连接延迟求值等子句,它们可能因"被强制在本连接层求值"而
 *   把本关系标记进 required_relids——这些必须"放回去"而不是丢弃;
 * - 把 simple_rel_array[relid] / simple_rte_array[relid] 置 NULL 并 pfree
 *   RelOptInfo,防止后续再被引用(不能更早,因为 remove_join_clause_from_rels
 *   还会碰它);
 * - 最后重建所有来源的 attr_needed 位图(占位符、连接子句、等价类、侧向
 *   引用),因为删除连接子句后原本需要的属性可能不再需要,这能帮助发现
 *   其它"现在可移除"的连接。
 *
 * 【参数】
 *   root   —— PlannerInfo;
 *   relid  —— 被移除的内关系 RT index;
 *   sjinfo —— 被移除的左连接的 SpecialJoinInfo(提供 ojrelid、min_lefthand
 *              /min_righthand、commute_xxx 等信息)。
 * 【返回值】void。
 */
static void
remove_leftjoinrel_from_query(PlannerInfo *root, int relid,
							  SpecialJoinInfo *sjinfo)
{
	RelOptInfo *rel = find_base_rel(root, relid);
	int			ojrelid = sjinfo->ojrelid;
	Relids		joinrelids;
	Relids		join_plus_commute;
	List	   *joininfos;
	ListCell   *l;

	/* Compute the relid set for the join we are considering */
	joinrelids = bms_union(sjinfo->min_lefthand, sjinfo->min_righthand);
	Assert(ojrelid != 0);
	joinrelids = bms_add_member(joinrelids, ojrelid);

	remove_rel_from_query(root, relid, -1, sjinfo, joinrelids);

	/*
	 * Remove any joinquals referencing the rel from the joininfo lists.
	 *
	 * In some cases, a joinqual has to be put back after deleting its
	 * reference to the target rel.  This can occur for pseudoconstant and
	 * outerjoin-delayed quals, which can get marked as requiring the rel in
	 * order to force them to be evaluated at or above the join.  We can't
	 * just discard them, though.  Only quals that logically belonged to the
	 * outer join being discarded should be removed from the query.
	 *
	 * We might encounter a qual that is a clone of a deletable qual with some
	 * outer-join relids added (see deconstruct_distribute_oj_quals).  To
	 * ensure we get rid of such clones as well, add the relids of all OJs
	 * commutable with this one to the set we test against for
	 * pushed-down-ness.
	 */
	join_plus_commute = bms_union(joinrelids,
								  sjinfo->commute_above_r);
	join_plus_commute = bms_add_members(join_plus_commute,
										sjinfo->commute_below_l);

	/*
	 * We must make a copy of the rel's old joininfo list before starting the
	 * loop, because otherwise remove_join_clause_from_rels would destroy the
	 * list while we're scanning it.
	 */
	joininfos = list_copy(rel->joininfo);
	foreach(l, joininfos)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(l);

		remove_join_clause_from_rels(root, rinfo, rinfo->required_relids);

		if (RINFO_IS_PUSHED_DOWN(rinfo, join_plus_commute))
		{
			/*
			 * There might be references to relid or ojrelid in the
			 * RestrictInfo's relid sets, as a consequence of PHVs having had
			 * ph_eval_at sets that include those.  We already checked above
			 * that any such PHV is safe (and updated its ph_eval_at), so we
			 * can just drop those references.
			 */
			remove_rel_from_restrictinfo(rinfo, relid, ojrelid);

			/*
			 * Cross-check that the clause itself does not reference the
			 * target rel or join.
			 */
#ifdef USE_ASSERT_CHECKING
			{
				Relids		clause_varnos = pull_varnos(root,
														(Node *) rinfo->clause);

				Assert(!bms_is_member(relid, clause_varnos));
				Assert(!bms_is_member(ojrelid, clause_varnos));
			}
#endif
			/* Now throw it back into the joininfo lists */
			distribute_restrictinfo_to_rels(root, rinfo);
		}
	}

	/*
	 * There may be references to the rel in root->fkey_list, but if so,
	 * match_foreign_keys_to_quals() will get rid of them.
	 */

	/*
	 * Now remove the rel from the baserel array to prevent it from being
	 * referenced again.  (We can't do this earlier because
	 * remove_join_clause_from_rels will touch it.)
	 */
	root->simple_rel_array[relid] = NULL;
	root->simple_rte_array[relid] = NULL;

	/* And nuke the RelOptInfo, just in case there's another access path */
	pfree(rel);

	/*
	 * Now repeat construction of attr_needed bits coming from all other
	 * sources.
	 */
	rebuild_placeholder_attr_needed(root);
	rebuild_joinclause_attr_needed(root);
	rebuild_eclass_attr_needed(root);
	rebuild_lateral_attr_needed(root);
}

/*
 * Remove the target relid and references to the target join from the
 * planner's data structures, having determined that there is no need
 * to include them in the query.  Optionally replace references to the
 * removed relid with subst if this is a self-join removal.
 *
 * This function serves as the common infrastructure for left-join removal
 * and self-join elimination.  It is intentionally scoped to update only the
 * shared planner data structures that are universally affected by relation
 * removal.  Each specific caller remains responsible for updating any
 * remaining data structures required by its unique removal logic.
 *
 * The specific type of removal being performed is dictated by the combination
 * of the sjinfo and subst parameters.  A non-NULL sjinfo indicates left-join
 * removal.  When sjinfo is NULL, a positive subst value indicates self-join
 * elimination (where references are replaced with subst).
 */
/*
 * remove_rel_from_query - (中文)从规划器共享数据结构中删除/改写对某关系的引用
 *
 * 【作用】把对 relid 的引用从 PlannerInfo 的各类共享数据结构中删除(左连接
 * 移除场景)或改写为 subst(自连接消除场景)。本函数是"关系移除"的公共
 * 基础设施,只负责更新所有移除操作都会波及的共享结构;各特定调用者仍须
 * 自行更新其特有数据结构。
 *
 * 【设计思想】本函数按数据结构逐一清理:
 * - 全局 relid 位图:all_baserels / all_query_rels 用 adjust_relid_set 调整
 *   (relid 改为 subst,或删除);外连接移除时还要把 ojrelid 从
 *   outer_join_rels / all_query_rels 中删除;
 * - SpecialJoinInfo:对 join_info_list 中每个 sjinf,先 bms_copy 四组
 *   lefthand/righthand 集合(initsplan.c 允许这些位图被多个结构共享,绝不能
 *   直接改原对象),再逐一 adjust;外连接移除时删除 ojrelid 位并清理
 *   commute_xxx 集合;自连接移除时用 ChangeVarNodesExtended + 回调改写
 *   semi_rhs_exprs;
 * - PlaceHolderInfo:左连接移除时,若 PHV 只在目标连接内被需要、求值位置含
 *   relid 且不含 ojrelid,则整个删除(在 placeholder_array 里也置 NULL);
 *   否则只改写 ph_eval_at / ph_needed("关系 0"位保留的技巧:目标列表与
 *   HAVING 引用的属性永远不删)/ phv->phrels;自连接移除时还改写 phexpr 内
 *   Var、ph_lateral(去掉与 ph_eval_at 重叠的部分)。注意 phnullingrels 无需
 *   调整;
 * - 等价类:仅左连接移除时逐 EC 调用 remove_rel_from_eclass();自连接场景
 *   调用者已处理过 EC(update_eclasses),这里跳过;
 * - attr_needed 重建准备:对 simple_rel_array 中每个关系,把每个属性的
 *   attr_needed 缩减为仅保留"关系 0"位(表示目标列表/HAVING 的引用),
 *   其余交给调用者随后用 rebuild_* 重建;自连接移除时改写各关系的
 *   lateral_vars;左连接移除且存在 PHV 时,对各 baserestrictinfo 与
 *   joininfo 中的 RestrictInfo 调用 remove_rel_from_restrictinfo_phvs
 *   (joininfo 用 seen_serials 位图按 rinfo_serial 去重,避免重复处理同一
 *   子句;is_clone 子句 serial 不唯一,只能任其重复处理)。
 *
 * 【参数】
 *   root       —— PlannerInfo;
 *   relid      —— 被移除关系的 RT index;
 *   subst      —— 自连接移除时要替换成的 RT index(>0);左连接移除传 -1;
 *   sjinfo     —— 左连接移除时给出被删连接的 SpecialJoinInfo(非 NULL);自
 *                 连接移除传 NULL;
 *   joinrelids —— 左连接移除时为目标连接的全部 relid(含 ojrelid);自连接
 *                 移除传 NULL。
 * 【返回值】void。
 */
static void
remove_rel_from_query(PlannerInfo *root, int relid,
					  int subst, SpecialJoinInfo *sjinfo,
					  Relids joinrelids)
{
	int			ojrelid = sjinfo ? sjinfo->ojrelid : 0;
	Index		rti;
	ListCell   *l;
	bool		is_outer_join = (sjinfo != NULL);
	bool		is_self_join = (!is_outer_join && subst > 0);
	Bitmapset  *seen_serials = NULL;

	Assert(is_outer_join || is_self_join);
	Assert(!is_outer_join || ojrelid > 0);
	Assert(!is_outer_join || joinrelids != NULL);

	/*
	 * Update all_baserels and related relid sets.
	 */
	root->all_baserels = adjust_relid_set(root->all_baserels, relid, subst);
	root->all_query_rels = adjust_relid_set(root->all_query_rels, relid, subst);

	if (is_outer_join)
	{
		root->outer_join_rels = bms_del_member(root->outer_join_rels, ojrelid);
		root->all_query_rels = bms_del_member(root->all_query_rels, ojrelid);
	}

	/*
	 * Likewise remove references from SpecialJoinInfo data structures.
	 *
	 * This is relevant in case the relation we're deleting is part of the
	 * relid sets of special joins: those sets have to be adjusted.  If we are
	 * removing an outer join, the RHS of the target outer join will be made
	 * empty here, but that's OK since the caller will delete that
	 * SpecialJoinInfo entirely.
	 */
	foreach(l, root->join_info_list)
	{
		SpecialJoinInfo *sjinf = (SpecialJoinInfo *) lfirst(l);

		/*
		 * initsplan.c is fairly cavalier about allowing SpecialJoinInfos'
		 * lefthand/righthand relid sets to be shared with other data
		 * structures.  Ensure that we don't modify the original relid sets.
		 * (The commute_xxx sets are always per-SpecialJoinInfo though.)
		 */
		sjinf->min_lefthand = bms_copy(sjinf->min_lefthand);
		sjinf->min_righthand = bms_copy(sjinf->min_righthand);
		sjinf->syn_lefthand = bms_copy(sjinf->syn_lefthand);
		sjinf->syn_righthand = bms_copy(sjinf->syn_righthand);

		/* Now adjust relid bit in the sets: */
		sjinf->min_lefthand = adjust_relid_set(sjinf->min_lefthand, relid, subst);
		sjinf->min_righthand = adjust_relid_set(sjinf->min_righthand, relid, subst);
		sjinf->syn_lefthand = adjust_relid_set(sjinf->syn_lefthand, relid, subst);
		sjinf->syn_righthand = adjust_relid_set(sjinf->syn_righthand, relid, subst);

		if (is_outer_join)
		{
			/* Remove ojrelid bit from the sets: */
			sjinf->min_lefthand = bms_del_member(sjinf->min_lefthand, ojrelid);
			sjinf->min_righthand = bms_del_member(sjinf->min_righthand, ojrelid);
			sjinf->syn_lefthand = bms_del_member(sjinf->syn_lefthand, ojrelid);
			sjinf->syn_righthand = bms_del_member(sjinf->syn_righthand, ojrelid);
			/* relid cannot appear in these fields, but ojrelid can: */
			sjinf->commute_above_l = bms_del_member(sjinf->commute_above_l, ojrelid);
			sjinf->commute_above_r = bms_del_member(sjinf->commute_above_r, ojrelid);
			sjinf->commute_below_l = bms_del_member(sjinf->commute_below_l, ojrelid);
			sjinf->commute_below_r = bms_del_member(sjinf->commute_below_r, ojrelid);
		}
		else
		{
			/*
			 * For self-join removal, replace relid references in
			 * semi_rhs_exprs.
			 */
			ChangeVarNodesExtended((Node *) sjinf->semi_rhs_exprs, relid, subst,
								   0, replace_relid_callback);
		}
	}

	/*
	 * Likewise remove references from PlaceHolderVar data structures,
	 * removing any no-longer-needed placeholders entirely.  We only remove
	 * PHVs for left-join removal.  With self-join elimination, PHVs already
	 * get moved to the remaining relation, where they might still be needed.
	 * It might also happen that we skip the removal of some PHVs that could
	 * be removed.  However, the overhead of extra PHVs is small compared to
	 * the complexity of analysis needed to remove them.
	 *
	 * Removal is a bit trickier than it might seem: we can remove PHVs that
	 * are used at the target rel and/or in the join qual, but not those that
	 * are used at join partner rels or above the join.  It's not that easy to
	 * distinguish PHVs used at partner rels from those used in the join qual,
	 * since they will both have ph_needed sets that are subsets of
	 * joinrelids.  However, a PHV used at a partner rel could not have the
	 * target rel in ph_eval_at, so we check that while deciding whether to
	 * remove or just update the PHV.  There is no corresponding test in
	 * join_is_removable because it doesn't need to distinguish those cases.
	 */
	foreach(l, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(l);

		Assert(!is_outer_join || !bms_is_member(relid, phinfo->ph_lateral));

		if (is_outer_join &&
			bms_is_subset(phinfo->ph_needed, joinrelids) &&
			bms_is_member(relid, phinfo->ph_eval_at) &&
			!bms_is_member(ojrelid, phinfo->ph_eval_at))
		{
			root->placeholder_list = foreach_delete_current(root->placeholder_list,
															l);
			root->placeholder_array[phinfo->phid] = NULL;
		}
		else
		{
			PlaceHolderVar *phv = phinfo->ph_var;

			phinfo->ph_eval_at = adjust_relid_set(phinfo->ph_eval_at, relid, subst);
			if (is_outer_join)
				phinfo->ph_eval_at = bms_del_member(phinfo->ph_eval_at, ojrelid);
			Assert(!bms_is_empty(phinfo->ph_eval_at));	/* checked previously */

			/* Reduce ph_needed to contain only "relation 0"; see below */
			if (bms_is_member(0, phinfo->ph_needed))
				phinfo->ph_needed = bms_make_singleton(0);
			else
				phinfo->ph_needed = NULL;

			phv->phrels = adjust_relid_set(phv->phrels, relid, subst);
			if (is_outer_join)
				phv->phrels = bms_del_member(phv->phrels, ojrelid);
			Assert(!bms_is_empty(phv->phrels));

			/*
			 * For self-join removal, update Var nodes within the PHV's
			 * expression to reference the replacement relid, and adjust
			 * ph_lateral for the relid substitution.  (For left-join removal,
			 * we're removing rather than replacing, and any surviving PHV
			 * shouldn't reference the removed rel in its expression.  Also,
			 * relid can't appear in ph_lateral for outer joins.)
			 */
			if (is_self_join)
			{
				ChangeVarNodesExtended((Node *) phv->phexpr, relid, subst, 0,
									   replace_relid_callback);
				phinfo->ph_lateral = adjust_relid_set(phinfo->ph_lateral, relid, subst);

				/*
				 * ph_lateral might contain rels mentioned in ph_eval_at after
				 * the replacement, remove them.
				 */
				phinfo->ph_lateral = bms_difference(phinfo->ph_lateral, phinfo->ph_eval_at);
				/* ph_lateral might or might not be empty */
			}

			Assert(phv->phnullingrels == NULL); /* no need to adjust */
		}
	}

	/*
	 * Likewise remove references from EquivalenceClasses.
	 *
	 * For self-join removal, the caller has already updated the
	 * EquivalenceClasses, so we can skip this step.
	 */
	if (is_outer_join)
	{
		foreach(l, root->eq_classes)
		{
			EquivalenceClass *ec = (EquivalenceClass *) lfirst(l);

			remove_rel_from_eclass(root, ec, relid, ojrelid);
		}
	}

	/*
	 * Finally, we must prepare for the caller to recompute per-Var
	 * attr_needed and per-PlaceHolderVar ph_needed relid sets.  These have to
	 * be known accurately, else we may fail to remove other now-removable
	 * joins.  Because the caller removes the join clause(s) associated with
	 * the removed join, Vars that were formerly needed may no longer be.
	 *
	 * The actual reconstruction of these relid sets is performed by the
	 * specific caller.  Here, we simply clear out the existing attr_needed
	 * sets (we already did this above for ph_needed) to ensure they are
	 * rebuilt from scratch.  We can cheat to one small extent: we can avoid
	 * re-examining the targetlist and HAVING qual by preserving "relation 0"
	 * bits from the existing relid sets.  This is safe because we'd never
	 * remove such references.
	 *
	 * Additionally, if we are performing self-join elimination, we must
	 * replace references to the removed relid with subst within the
	 * lateral_vars lists.
	 *
	 * Also, for left-join removal, we strip the removed rel and join from any
	 * PlaceHolderVar embedded in the surviving rels' restriction clauses and
	 * join clauses; we needn't bother with the rel being removed, nor when
	 * the query has no PlaceHolderVars.
	 */
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *otherrel = root->simple_rel_array[rti];
		int			attroff;

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (otherrel == NULL)
			continue;

		Assert(otherrel->relid == rti); /* sanity check on array */

		for (attroff = otherrel->max_attr - otherrel->min_attr;
			 attroff >= 0;
			 attroff--)
		{
			if (bms_is_member(0, otherrel->attr_needed[attroff]))
				otherrel->attr_needed[attroff] = bms_make_singleton(0);
			else
				otherrel->attr_needed[attroff] = NULL;
		}

		if (is_self_join)
			ChangeVarNodesExtended((Node *) otherrel->lateral_vars, relid,
								   subst, 0, replace_relid_callback);

		if (is_outer_join && rti != relid && root->glob->lastPHId != 0)
		{
			foreach_node(RestrictInfo, rinfo, otherrel->baserestrictinfo)
				remove_rel_from_restrictinfo_phvs(rinfo, relid, ojrelid);

			/*
			 * Join clauses need the same treatment, but there's no value in
			 * processing any join clause more than once.  So it's slightly
			 * annoying that we have to find them via the per-base-relation
			 * joininfo lists.  Avoid duplicate processing by tracking the
			 * rinfo_serial numbers of join clauses we've already seen.  (This
			 * doesn't work for is_clone clauses, so we must waste effort on
			 * them.)
			 */
			foreach_node(RestrictInfo, rinfo, otherrel->joininfo)
			{
				if (!rinfo->is_clone)	/* else serial number is not unique */
				{
					if (bms_is_member(rinfo->rinfo_serial, seen_serials))
						continue;	/* saw it already */
					seen_serials = bms_add_member(seen_serials,
												  rinfo->rinfo_serial);
				}
				remove_rel_from_restrictinfo_phvs(rinfo, relid, ojrelid);
			}
		}
	}
}

/*
 * Remove any references to relid or ojrelid from the RestrictInfo.
 *
 * We only bother to clean out bits in the RestrictInfo's various relid sets,
 * not nullingrel bits in contained Vars and PHVs.  (This might have to be
 * improved sometime.)  However, if the RestrictInfo contains an OR clause
 * we have to also clean up the sub-clauses.
 */
/*
 * remove_rel_from_restrictinfo - (中文)从 RestrictInfo 的 relid 位图中删除关系引用
 *
 * 【作用】把对 relid 和 ojrelid 的引用从 RestrictInfo 的各个 relid 位图
 * (clause_relids / required_relids / incompatible_relids / outer_relids /
 * left_relids / right_relids)中全部删除;若子句是 OR 子句,递归清理其子
 * 句。由 remove_rel_from_query() 及 remove_rel_from_eclass() 调用。
 *
 * 【设计思想】
 * - 只清理 RestrictInfo 自身各字段的位图,不动内含 Var/PHV 里的
 *   phnullingrels 位(注释注明这是"或许有待改进"的简化);
 * - 因为 initsplan.c 允许 RestrictInfo 之间、以及与 SpecialJoinInfo 共享
 *   relid 位图,修改前必须对每个字段先 bms_copy 出独立副本,避免破坏共享
 *   对象;
 * - OR 子句有"并行表示"问题:rinfo->clause 可能是 BoolExpr(OR),而
 *   rinfo->orclause 是等价的子 RestrictInfo 列表,递归时对二者都要处理
 *   (调用点如 remove_rel_from_restrictinfo 直接递归子句;PHV 版本见
 *   remove_rel_from_restrictinfo_phvs)。
 *
 * 【参数】
 *   rinfo  —— 待清理的 RestrictInfo;
 *   relid  —— 被移除关系的 RT index;
 *   ojrelid —— 被移除连接的 RT index(可能为 0,表示无需清理)。
 * 【返回值】void。
 */
static void
remove_rel_from_restrictinfo(RestrictInfo *rinfo, int relid, int ojrelid)
{
	/*
	 * initsplan.c is fairly cavalier about allowing RestrictInfos to share
	 * relid sets with other RestrictInfos, and SpecialJoinInfos too.  Make
	 * sure this RestrictInfo has its own relid sets before we modify them.
	 * (In present usage, clause_relids is probably not shared, but
	 * required_relids could be; let's not assume anything.)
	 */
	rinfo->clause_relids = bms_copy(rinfo->clause_relids);
	rinfo->clause_relids = bms_del_member(rinfo->clause_relids, relid);
	rinfo->clause_relids = bms_del_member(rinfo->clause_relids, ojrelid);
	/* Likewise for required_relids */
	rinfo->required_relids = bms_copy(rinfo->required_relids);
	rinfo->required_relids = bms_del_member(rinfo->required_relids, relid);
	rinfo->required_relids = bms_del_member(rinfo->required_relids, ojrelid);
	/* Likewise for incompatible_relids */
	rinfo->incompatible_relids = bms_copy(rinfo->incompatible_relids);
	rinfo->incompatible_relids = bms_del_member(rinfo->incompatible_relids, relid);
	rinfo->incompatible_relids = bms_del_member(rinfo->incompatible_relids, ojrelid);
	/* Likewise for outer_relids */
	rinfo->outer_relids = bms_copy(rinfo->outer_relids);
	rinfo->outer_relids = bms_del_member(rinfo->outer_relids, relid);
	rinfo->outer_relids = bms_del_member(rinfo->outer_relids, ojrelid);
	/* Likewise for left_relids */
	rinfo->left_relids = bms_copy(rinfo->left_relids);
	rinfo->left_relids = bms_del_member(rinfo->left_relids, relid);
	rinfo->left_relids = bms_del_member(rinfo->left_relids, ojrelid);
	/* Likewise for right_relids */
	rinfo->right_relids = bms_copy(rinfo->right_relids);
	rinfo->right_relids = bms_del_member(rinfo->right_relids, relid);
	rinfo->right_relids = bms_del_member(rinfo->right_relids, ojrelid);

	/* If it's an OR, recurse to clean up sub-clauses */
	if (restriction_is_or_clause(rinfo))
	{
		ListCell   *lc;

		Assert(is_orclause(rinfo->orclause));
		foreach(lc, ((BoolExpr *) rinfo->orclause)->args)
		{
			Node	   *orarg = (Node *) lfirst(lc);

			/* OR arguments should be ANDs or sub-RestrictInfos */
			if (is_andclause(orarg))
			{
				List	   *andargs = ((BoolExpr *) orarg)->args;
				ListCell   *lc2;

				foreach(lc2, andargs)
				{
					RestrictInfo *rinfo2 = lfirst_node(RestrictInfo, lc2);

					remove_rel_from_restrictinfo(rinfo2, relid, ojrelid);
				}
			}
			else
			{
				RestrictInfo *rinfo2 = castNode(RestrictInfo, orarg);

				remove_rel_from_restrictinfo(rinfo2, relid, ojrelid);
			}
		}
	}
}

/*
 * Remove any references to relid or ojrelid from the EquivalenceClass.
 *
 * We fix the EC and EM relid sets to ensure that implied join equalities will
 * be generated at the appropriate join level(s).  We also strip the removed
 * rel from PlaceHolderVars embedded in member expressions; a member's
 * em_relids reflects ph_eval_at rather than the PHV's phrels, so the latter
 * can still mention the removed rel even when em_relids does not.  Like
 * remove_rel_from_restrictinfo, we don't bother with nullingrel bits in
 * contained plain Vars.
 */
/*
 * remove_rel_from_eclass - (中文)从等价类及其成员中删除对某关系的引用
 *
 * 【作用】把对 relid / ojrelid 的引用从 EquivalenceClass 中清理掉:修正 EC
 * 与各成员(EquivalenceMember)的 relid 位图,从成员表达式中剥离被删除关系
 * 的 PlaceHolderVar,丢弃不再需要的成员与已派生子句。仅在左连接移除时由
 * remove_rel_from_query() 调用(自连接场景用 update_eclasses 改写而非删除)。
 *
 * 【设计思想】
 * - 修正 EC/EM 位图是为了让"由等价类推导出的连接等值子句"能在正确的连接
 *   层级生成;EM 的 em_relids 反映的是 ph_eval_at 而非 PHV 的 phrels,因此
 *   即使 em_relids 已不含被删关系,成员表达式里的 PHV 仍可能引用它,故先
 *   对每个非 Var/Const 成员表达式调用 remove_rel_from_phvs 剥离;
 * - 若 EC 的 ec_relids 根本不涉及被删关系/连接,则直接返回;
 * - 修正成员时,某个非 const 成员若删除 relid 位后 em_relids 变空,说明它
 *   就是被删关系的 Var/PHV,不再需要,从 ec_members 中删除(操作前先
 *   bms_copy,因 em_relids 可能与其他 RestrictInfo 共享);
 * - 源子句(ec_sources)逐个调 remove_rel_from_restrictinfo 修正位图;
 * - 已派生的子句(ec_derives 等)直接丢弃(ec_clear_derived_clauses),不必
 *   花代码修——此时它们至多是基础限制子句,反正不再需要;
 * - 断言 ec_childmembers 为空:本阶段不可能存在分区/继承子成员的 EC。
 *
 * 【参数】
 *   root   —— PlannerInfo(用于访问 glob->lastPHId 判断是否存在 PHV);
 *   ec     —— 待清理的等价类;
 *   relid  —— 被移除关系的 RT index;
 *   ojrelid —— 被移除连接的 RT index。
 * 【返回值】void。
 */
static void
remove_rel_from_eclass(PlannerInfo *root, EquivalenceClass *ec,
					   int relid, int ojrelid)
{
	ListCell   *lc;

	/*
	 * Strip the removed rel/join from PlaceHolderVars in member expressions.
	 * This is needed even when the EC's relids don't mention the removed rel.
	 * Plain Vars and Consts can't contain a PlaceHolderVar, so skip them.
	 */
	if (root->glob->lastPHId != 0)
	{
		foreach_node(EquivalenceMember, em, ec->ec_members)
		{
			if (!IsA(em->em_expr, Var) && !IsA(em->em_expr, Const))
				em->em_expr = (Expr *)
					remove_rel_from_phvs((Node *) em->em_expr, relid, ojrelid);
		}
	}

	if (!bms_is_member(relid, ec->ec_relids) &&
		!bms_is_member(ojrelid, ec->ec_relids))
		return;

	/* Fix up the EC's overall relids */
	ec->ec_relids = bms_del_member(ec->ec_relids, relid);
	ec->ec_relids = bms_del_member(ec->ec_relids, ojrelid);

	/*
	 * We don't expect any EC child members to exist at this point.  Ensure
	 * that's the case, otherwise, we might be getting asked to do something
	 * this function hasn't been coded for.
	 */
	Assert(ec->ec_childmembers == NULL);

	/*
	 * Fix up the member expressions.  Any non-const member that ends with
	 * empty em_relids must be a Var or PHV of the removed relation.  We don't
	 * need it anymore, so we can drop it.
	 */
	foreach(lc, ec->ec_members)
	{
		EquivalenceMember *cur_em = (EquivalenceMember *) lfirst(lc);

		if (bms_is_member(relid, cur_em->em_relids) ||
			bms_is_member(ojrelid, cur_em->em_relids))
		{
			Assert(!cur_em->em_is_const);
			/* em_relids is likely to be shared with some RestrictInfo */
			cur_em->em_relids = bms_copy(cur_em->em_relids);
			cur_em->em_relids = bms_del_member(cur_em->em_relids, relid);
			cur_em->em_relids = bms_del_member(cur_em->em_relids, ojrelid);
			if (bms_is_empty(cur_em->em_relids))
				ec->ec_members = foreach_delete_current(ec->ec_members, lc);
		}
	}

	/* Fix up the source clauses, in case we can re-use them later */
	foreach(lc, ec->ec_sources)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		remove_rel_from_restrictinfo(rinfo, relid, ojrelid);
	}

	/*
	 * Rather than expend code on fixing up any already-derived clauses, just
	 * drop them.  (At this point, any such clauses would be base restriction
	 * clauses, which we'd not need anymore anyway.)
	 */
	ec_clear_derived_clauses(ec);
}

/*
 * Remove any references to relid or ojrelid from the PlaceHolderVars embedded
 * in a RestrictInfo's clause.
 *
 * If it's an OR clause, we must also fix up the orclause, which is a parallel
 * representation built from its own sub-RestrictInfos.  We recurse into the
 * sub-clauses for that, mirroring remove_rel_from_restrictinfo.
 */
/*
 * remove_rel_from_restrictinfo_phvs - (中文)剥离 RestrictInfo 子句中 PHV 对已删关系的引用
 *
 * 【作用】对 RestrictInfo 的 clause 调用 remove_rel_from_phvs(),把其中所有
 * PlaceHolderVar 的 phrels / phnullingrels 中涉及 relid / ojrelid 的位删掉;
 * 若子句是 OR,还要递归处理 orclause 的各个子 RestrictInfo(与
 * remove_rel_from_restrictinfo 的处理方式平行)。由 remove_rel_from_query()
 * 在左连接移除时对幸存关系的 baserestrictinfo / joininfo 逐条调用。
 *
 * 【设计思想】remove_rel_from_query() 只修正了 RestrictInfo 和
 * EquivalenceMember 自身的 relid 位图,但没处理嵌在表达式里的 PHV。平时没
 * 问题,可一旦表达式要为 appendrel 子关系做翻译(translate),其 relids 会
 * 被 pull_varnos() 重算,残留的被删 relid 就会引用一个不存在的关系,所以
 * 必须在这里剥干净,使它与"canonical"的 PlaceHolderVar 一致。
 *
 * 【参数】
 *   rinfo  —— 待处理的 RestrictInfo;
 *   relid  —— 被移除关系的 RT index;
 *   ojrelid —— 被移除连接的 RT index。
 * 【返回值】void。
 */
static void
remove_rel_from_restrictinfo_phvs(RestrictInfo *rinfo, int relid, int ojrelid)
{
	rinfo->clause = (Expr *)
		remove_rel_from_phvs((Node *) rinfo->clause, relid, ojrelid);

	/* If it's an OR, recurse to clean up sub-clauses */
	if (restriction_is_or_clause(rinfo))
	{
		ListCell   *lc;

		Assert(is_orclause(rinfo->orclause));
		foreach(lc, ((BoolExpr *) rinfo->orclause)->args)
		{
			Node	   *orarg = (Node *) lfirst(lc);

			/* OR arguments should be ANDs or sub-RestrictInfos */
			if (is_andclause(orarg))
			{
				List	   *andargs = ((BoolExpr *) orarg)->args;
				ListCell   *lc2;

				foreach(lc2, andargs)
				{
					RestrictInfo *rinfo2 = lfirst_node(RestrictInfo, lc2);

					remove_rel_from_restrictinfo_phvs(rinfo2, relid, ojrelid);
				}
			}
			else
			{
				RestrictInfo *rinfo2 = castNode(RestrictInfo, orarg);

				remove_rel_from_restrictinfo_phvs(rinfo2, relid, ojrelid);
			}
		}
	}
}

/*
 * Remove any references to the specified RT index(es) from the phrels (and
 * phnullingrels) of every PlaceHolderVar in the given expression.
 *
 * remove_rel_from_query() fixes up the relid sets of RestrictInfos and
 * EquivalenceMembers, but not the PlaceHolderVars embedded in their
 * expressions.  That's normally fine, but such an expression may later be
 * translated for an appendrel child and have its relids recomputed by
 * pull_varnos().  A leftover removed relid in phrels would then make
 * pull_varnos() reference a nonexistent rel, so we strip it here to match the
 * canonical PlaceHolderVar.
 */
/*
 * remove_rel_from_phvs - (中文)从表达式内所有 PHV 的 phrels 中删除指定关系
 *
 * 【作用】构造一个"可删除位集合"(relid 与 ojrelid),然后委托
 * remove_rel_from_phvs_mutator() 遍历整棵表达式树,把每个 PlaceHolderVar 的
 * phrels 与 phnullingrels 中这些位删掉。由 remove_rel_from_eclass() 和
 * remove_rel_from_restrictinfo_phvs() 调用。
 *
 * 【设计思想】这只是个薄封装:把要删除的 relid 集合组装成 Bitmapset,再交给
 * 递归的 mutator;递归/位图操作的正确性都在 mutator 中处理。
 *
 * 【参数】
 *   node   —— 待遍历的表达式树;
 *   relid  —— 被移除关系的 RT index;
 *   ojrelid —— 被移除连接的 RT index。
 * 【返回值】处理后的新表达式树(未命中任何修改时可能返回原树或深拷贝)。
 */
static Node *
remove_rel_from_phvs(Node *node, int relid, int ojrelid)
{
	Relids		removable = bms_add_member(bms_make_singleton(relid), ojrelid);

	return remove_rel_from_phvs_mutator(node, removable);
}

/*
 * remove_rel_from_phvs_mutator - (中文)递归遍历表达式树剥离 PHV 中被删关系的 relid
 *
 * 【作用】remove_rel_from_phvs() 的递归实现:深度优先遍历表达式树,对每个
 * PlaceHolderVar 复制节点、递归处理其子表达式,然后把 removable 集合中的位
 * 从 phv->phrels 与 phv->phnullingrels 中删除。
 *
 * 【设计思想】
 * - 递归用 expression_tree_mutator 完成:它对已知节点类型逐一展开子节点,
 *   对未知节点深拷贝(见 nodeFuncs.c);对 PHV 特判是因为它携带 relid 位图
 *   (phrels/phnullingrels),而普通节点没有;
 * - 上层 PHV 早已被处理完毕,故断言 phlevelsup == 0;
 * - 关键边界情况:若剥离后 phrels 变空,说明该 PHV 只在被删关系(连接)处求
 *   值,它属于"即将被调用者丢弃的 EquivalenceMember",此时故意保持原样
 *   而不生成一个 phrels 为空的新 PHV——planner 全局假设"空 phrels 的 PHV
 *   从不出现",违反该假设会引发后续断言失败。
 *
 * 【参数】
 *   node     —— 当前遍历到的节点;
 *   removable —— 需要从 phrels / phnullingrels 中删除的 relid 集合。
 * 【返回值】处理后的节点(可能是原节点、深拷贝节点或新构造的 PHV)。
 */
static Node *
remove_rel_from_phvs_mutator(Node *node, Relids removable)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;
		Relids		newphrels;

		/* Upper-level PlaceHolderVars should be long gone at this point */
		Assert(phv->phlevelsup == 0);

		/* Copy the PlaceHolderVar and mutate what's below ... */
		phv = (PlaceHolderVar *)
			expression_tree_mutator(node,
									remove_rel_from_phvs_mutator,
									removable);

		/*
		 * ... then strip the removed rels from its relid sets.
		 *
		 * If stripping would empty phrels, the PHV is evaluated only at the
		 * removed relation(s); it then belongs to an EquivalenceMember that
		 * the caller drops immediately afterwards.  Leave such a PHV
		 * untouched rather than build one with empty phrels, which the rest
		 * of the planner assumes never occurs.
		 */
		newphrels = bms_difference(phv->phrels, removable);
		if (!bms_is_empty(newphrels))
		{
			phv->phrels = newphrels;
			phv->phnullingrels = bms_difference(phv->phnullingrels,
												removable);
		}

		return (Node *) phv;
	}
	return expression_tree_mutator(node,
								   remove_rel_from_phvs_mutator,
								   removable);
}

/*
 * Remove any occurrences of the target relid from a joinlist structure.
 *
 * It's easiest to build a whole new list structure, so we handle it that
 * way.  Efficiency is not a big deal here.
 *
 * *nremoved is incremented by the number of occurrences removed (there
 * should be exactly one, but the caller checks that).
 */
/*
 * remove_rel_from_joinlist - (中文)从连接树列表中删除目标关系的所有出现
 *
 * 【作用】递归遍历 joinlist(嵌套 List 结构,叶节点是 RangeTblRef),把
 * rtindex 等于 relid 的叶子摘除,返回新建的列表;通过 *nremoved 累计删除的
 * 次数(调用方期望恰好 1 次并自行校验)。由 remove_useless_joins() 与
 * remove_useless_self_joins() 调用。
 *
 * 【设计思想】
 * - 直接新建整棵列表而非原地修改,代码简单、效率在规划期无足轻重;
 * - 递归时若某个子列表删除后变空则整体丢弃(避免留下空 List);
 * - 遇到未知节点类型直接 elog(ERROR)——joinlist 只应包含 RangeTblRef 与
 *   嵌套 List 两种节点。
 *
 * 【参数】
 *   joinlist —— 待处理的连接树列表;
 *   relid    —— 要删除的目标关系 RT index;
 *   nremoved —— 输出参数,累加被删除的叶子个数(调用者初始化为 0)。
 * 【返回值】新建的、不含目标关系的连接树列表。
 */
static List *
remove_rel_from_joinlist(List *joinlist, int relid, int *nremoved)
{
	List	   *result = NIL;
	ListCell   *jl;

	foreach(jl, joinlist)
	{
		Node	   *jlnode = (Node *) lfirst(jl);

		if (IsA(jlnode, RangeTblRef))
		{
			int			varno = ((RangeTblRef *) jlnode)->rtindex;

			if (varno == relid)
				(*nremoved)++;
			else
				result = lappend(result, jlnode);
		}
		else if (IsA(jlnode, List))
		{
			/* Recurse to handle subproblem */
			List	   *sublist;

			sublist = remove_rel_from_joinlist((List *) jlnode,
											   relid, nremoved);
			/* Avoid including empty sub-lists in the result */
			if (sublist)
				result = lappend(result, sublist);
		}
		else
		{
			elog(ERROR, "unrecognized joinlist node type: %d",
				 (int) nodeTag(jlnode));
		}
	}

	return result;
}


/*
 * reduce_unique_semijoins
 *		Check for semijoins that can be simplified to plain inner joins
 *		because the inner relation is provably unique for the join clauses.
 *
 * Ideally this would happen during reduce_outer_joins, but we don't have
 * enough information at that point.
 *
 * To perform the strength reduction when applicable, we need only delete
 * the semijoin's SpecialJoinInfo from root->join_info_list.  (We don't
 * bother fixing the join type attributed to it in the query jointree,
 * since that won't be consulted again.)
 */
/*
 * reduce_unique_semijoins - (中文)把可证明唯一内关系的半连接降级为普通内连接
 *
 * 【作用】检查哪些半连接由于内关系对连接子句可证明唯一而可以简化为普通
 * 内连接:此时只需把对应 SpecialJoinInfo 从 root->join_info_list 中删除即可
 * (连接树里标记的 join 类型已无人再查,不必改)。由 query_planner() 调用。
 *
 * 【设计思想】
 * - 理想情况下这种化简应在 reduce_outer_joins 阶段做,但那时信息不足;现在
 *   initsplan.c 已完成分析、等价类已生成,才有足够依据;
 * - 遍历 join_info_list,只处理 JOIN_SEMI 且 min_righthand 为单个 baserel
 *   的条目;先做 rel_supports_distinctness 快速预筛;
 * - 半连接没有 ojrelid(断言为 0);连接子句集合用 generate_join_implied_
 *   equalities(考虑由等价类推导出的子句,即 WHERE/ON 中只写了一侧等于另一
 *   侧时由等价类补全的连接子句)连接内关系的 joininfo;
 * - 用 innerrel_is_unique() 证明唯一性,force_cache = true:本调用发生在常规
 *   连接搜索开始之前,缓存"不唯一"结论对后续自底向上的连接搜索有用。
 *
 * 【参数】
 *   root —— PlannerInfo,其 join_info_list 中可化简的半连接条目会被删除。
 * 【返回值】void。
 */
void
reduce_unique_semijoins(PlannerInfo *root)
{
	ListCell   *lc;

	/*
	 * Scan the join_info_list to find semijoins.
	 */
	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(lc);
		int			innerrelid;
		RelOptInfo *innerrel;
		Relids		joinrelids;
		List	   *restrictlist;

		/*
		 * Must be a semijoin to a single baserel, else we aren't going to be
		 * able to do anything with it.
		 */
		if (sjinfo->jointype != JOIN_SEMI)
			continue;

		if (!bms_get_singleton_member(sjinfo->min_righthand, &innerrelid))
			continue;

		innerrel = find_base_rel(root, innerrelid);

		/*
		 * Before we trouble to run generate_join_implied_equalities, make a
		 * quick check to eliminate cases in which we will surely be unable to
		 * prove uniqueness of the innerrel.
		 */
		if (!rel_supports_distinctness(root, innerrel))
			continue;

		/* Compute the relid set for the join we are considering */
		joinrelids = bms_union(sjinfo->min_lefthand, sjinfo->min_righthand);
		Assert(sjinfo->ojrelid == 0);	/* SEMI joins don't have RT indexes */

		/*
		 * Since we're only considering a single-rel RHS, any join clauses it
		 * has must be clauses linking it to the semijoin's min_lefthand.  We
		 * can also consider EC-derived join clauses.
		 */
		restrictlist =
			list_concat(generate_join_implied_equalities(root,
														 joinrelids,
														 sjinfo->min_lefthand,
														 innerrel,
														 NULL),
						innerrel->joininfo);

		/* Test whether the innerrel is unique for those clauses. */
		if (!innerrel_is_unique(root,
								joinrelids, sjinfo->min_lefthand, innerrel,
								JOIN_SEMI, restrictlist, true))
			continue;

		/* OK, remove the SpecialJoinInfo from the list. */
		root->join_info_list = foreach_delete_current(root->join_info_list, lc);
	}
}


/*
 * rel_supports_distinctness
 *		Could the relation possibly be proven distinct on some set of columns?
 *
 * This is effectively a pre-checking function for rel_is_distinct_for().
 * It must return true if rel_is_distinct_for() could possibly return true
 * with this rel, but it should not expend a lot of cycles.  The idea is
 * that callers can avoid doing possibly-expensive processing to compute
 * rel_is_distinct_for()'s argument lists if the call could not possibly
 * succeed.
 */
/*
 * rel_supports_distinctness - (中文)预筛:该关系能否在某个列集合上被证明唯一
 *
 * 【作用】rel_is_distinct_for() 的"廉价预检":若返回 true,则 rel_is_distinct_for()
 * 仍有可能成功;若返回 false,则绝无可能。调用方据此避免花费昂贵代价去构
 * 造 rel_is_distinct_for() 的参数列表。由 join_is_removable() 和
 * reduce_unique_semijoins()、innerrel_is_unique_ext() 等调用。
 *
 * 【设计思想】
 * - 只认识 RELOPT_BASEREL 基础关系;
 * - 普通关系(RTE_RELATION):只能通过"唯一索引"证明唯一,故检查 indexlist
 *   中是否存在 unique 且 immediate 且非部分索引(无 indpred)的索引;条件
 *   必须与 relation_has_unique_index_for() 保持同步;
 * - 子查询(RTE_SUBQUERY):其唯一性靠查询自身性质(DISTINCT/GROUP BY/
 *   聚合/集合运算等)证明,故委托 query_supports_distinctness();
 * - 其它 rtekind 一律返回 false(没有可用的证明规则)。
 *
 * 【参数】
 *   root —— PlannerInfo(用于经 simple_rte_array 访问子查询的 Query);
 *   rel  —— 待检查的关系。
 * 【返回值】true:有可能证明唯一;false:不可能。
 */
static bool
rel_supports_distinctness(PlannerInfo *root, RelOptInfo *rel)
{
	/* We only know about baserels ... */
	if (rel->reloptkind != RELOPT_BASEREL)
		return false;
	if (rel->rtekind == RTE_RELATION)
	{
		/*
		 * For a plain relation, we only know how to prove uniqueness by
		 * reference to unique indexes.  Make sure there's at least one
		 * suitable unique index.  It must be immediately enforced, and not a
		 * partial index. (Keep these conditions in sync with
		 * relation_has_unique_index_for!)
		 */
		ListCell   *lc;

		foreach(lc, rel->indexlist)
		{
			IndexOptInfo *ind = (IndexOptInfo *) lfirst(lc);

			if (ind->unique && ind->immediate && ind->indpred == NIL)
				return true;
		}
	}
	else if (rel->rtekind == RTE_SUBQUERY)
	{
		Query	   *subquery = root->simple_rte_array[rel->relid]->subquery;

		/* Check if the subquery has any qualities that support distinctness */
		if (query_supports_distinctness(subquery))
			return true;
	}
	/* We have no proof rules for any other rtekinds. */
	return false;
}

/*
 * rel_is_distinct_for
 *		Does the relation return only distinct rows according to clause_list?
 *
 * clause_list is a list of join restriction clauses involving this rel and
 * some other one.  Return true if no two rows emitted by this rel could
 * possibly join to the same row of the other rel.
 *
 * The caller must have already determined that each condition is a
 * mergejoinable equality with an expression in this relation on one side, and
 * an expression not involving this relation on the other.  The transient
 * outer_is_left flag is used to identify which side references this relation:
 * left side if outer_is_left is false, right side if it is true.
 *
 * Note that the passed-in clause_list may be destructively modified!  This
 * is OK for current uses, because the clause_list is built by the caller for
 * the sole purpose of passing to this function.
 *
 * (*extra_clauses) to be set to the right sides of baserestrictinfo clauses,
 * looking like "x = const" if distinctness is derived from such clauses, not
 * joininfo clauses.  Pass NULL to the extra_clauses if this value is not
 * needed.
 */
/*
 * rel_is_distinct_for - (中文)判断关系是否根据给定子句集合只产生互不相同的行
 *
 * 【作用】clause_list 是涉及本关系与另一关系的连接子句列表;若本关系输出的
 * 任意两行都不可能连接到另一关系的同一行,返回 true。可选的 extra_clauses
 * 输出参数用于回传"形如 x = const 的基础限制子句"(当唯一性是由这类子句而
 * 非 joininfo 子句证明时)。由 join_is_removable() 与 is_innerrel_unique_for()
 * 调用。
 *
 * 【设计思想】
 * - 调用方必须已确认:每个条件是 mergejoinable 的等值子句,一侧是引用本关
 *   系的表达式,另一侧不引用本关系;用 RestrictInfo 的 outer_is_left 标志辨
 *   认哪一侧属于本关系(false = 左侧,true = 右侧);
 * - 普通关系:委托 relation_has_unique_index_for(),它会自动把本关系的可
 *   用限制子句一并纳入(故这里不需要额外处理 baserestrictinfo);
 * - 子查询:对每个子句取内侧操作数(剥掉可能的 RelabelType),要求它必须是
 *   引用子查询输出列(var->varno == relid、varlevelsup == 0)的 Var,否则该
 *   子句对唯一性无用;然后组装 DistinctColInfo 列表(列号、等值算子 OID 与
 *   其输入排序规则),交给 query_is_distinct_for() 证明。排序规则必须一起给,
 *   因为子查询自己的 DISTINCT/GROUP BY/集合运算是在"自己的排序规则"下证明
 *   唯一的,未必与上层算子一致;
 * - 传入的 clause_list 可能会被破坏性修改!当前调用方构造该列表的目的就是
 *   一次性传给本函数,所以可以接受。
 *
 * 【参数】
 *   root         —— PlannerInfo;
 *   rel          —— 待检查的关系;
 *   clause_list  —— 连接子句(RestrictInfo)列表,可能被本函数破坏性修改;
 *   extra_clauses —— 可选输出参数,填上用于证明唯一性的 "x = const" 基础
 *                     限制子句(不需要时传 NULL)。
 * 【返回值】true:该关系对这些子句唯一。
 */
static bool
rel_is_distinct_for(PlannerInfo *root, RelOptInfo *rel, List *clause_list,
					List **extra_clauses)
{
	/*
	 * We could skip a couple of tests here if we assume all callers checked
	 * rel_supports_distinctness first, but it doesn't seem worth taking any
	 * risk for.
	 */
	if (rel->reloptkind != RELOPT_BASEREL)
		return false;
	if (rel->rtekind == RTE_RELATION)
	{
		/*
		 * Examine the indexes to see if we have a matching unique index.
		 * relation_has_unique_index_for automatically adds any usable
		 * restriction clauses for the rel, so we needn't do that here.
		 */
		if (relation_has_unique_index_for(root, rel, clause_list, extra_clauses))
			return true;
	}
	else if (rel->rtekind == RTE_SUBQUERY)
	{
		Index		relid = rel->relid;
		Query	   *subquery = root->simple_rte_array[relid]->subquery;
		List	   *distinct_cols = NIL;
		ListCell   *l;

		/*
		 * Build the argument list for query_is_distinct_for: a list of
		 * DistinctColInfo entries, each holding an output column number that
		 * the query needs to be distinct over, the equality operator that the
		 * column needs to be distinct according to, and that operator's input
		 * collation.  The collation matters because the subquery's own
		 * DISTINCT / GROUP BY / set-op proves uniqueness under its own
		 * collation, which need not agree with the operator's.
		 *
		 * (XXX we are not considering restriction clauses attached to the
		 * subquery; is that worth doing?)
		 */
		foreach(l, clause_list)
		{
			RestrictInfo *rinfo = lfirst_node(RestrictInfo, l);
			OpExpr	   *opexpr;
			Var		   *var;
			DistinctColInfo *dcinfo;

			/*
			 * The caller's mergejoinability test should have selected only
			 * OpExprs.  The operator might be a cross-type operator and thus
			 * not exactly the same operator the subquery would consider;
			 * that's all right since query_is_distinct_for can resolve such
			 * cases.
			 */
			opexpr = castNode(OpExpr, rinfo->clause);

			/* caller identified the inner side for us */
			if (rinfo->outer_is_left)
				var = (Var *) get_rightop(rinfo->clause);
			else
				var = (Var *) get_leftop(rinfo->clause);

			/*
			 * We may ignore any RelabelType node above the operand.  (There
			 * won't be more than one, since eval_const_expressions() has been
			 * applied already.)
			 */
			if (var && IsA(var, RelabelType))
				var = (Var *) ((RelabelType *) var)->arg;

			/*
			 * If inner side isn't a Var referencing a subquery output column,
			 * this clause doesn't help us.
			 */
			if (!var || !IsA(var, Var) ||
				var->varno != relid || var->varlevelsup != 0)
				continue;

			dcinfo = palloc(sizeof(DistinctColInfo));
			dcinfo->colno = var->varattno;
			dcinfo->opid = opexpr->opno;
			dcinfo->collid = opexpr->inputcollid;
			distinct_cols = lappend(distinct_cols, dcinfo);
		}

		if (query_is_distinct_for(subquery, distinct_cols))
			return true;
	}
	return false;
}


/*
 * query_supports_distinctness - could the query possibly be proven distinct
 *		on some set of output columns?
 *
 * This is effectively a pre-checking function for query_is_distinct_for().
 * It must return true if query_is_distinct_for() could possibly return true
 * with this query, but it should not expend a lot of cycles.  The idea is
 * that callers can avoid doing possibly-expensive processing to compute
 * query_is_distinct_for()'s argument lists if the call could not possibly
 * succeed.
 */
/*
 * query_supports_distinctness - (中文)预筛:子查询能否在某个输出列集合上被证明唯一
 *
 * 【作用】query_is_distinct_for() 的廉价预检:若返回 false 则证明绝无可能,
 * 调用方(rel_supports_distinctness)不必再构造参数;若返回 true 仍可能最终
 * 失败。两函数必须保持同步(见 query_is_distinct_for 末尾注释)。
 *
 * 【设计思想】按"哪些特性可以证明唯一"枚举:
 * - 目标列表中的 SRF(集合返回函数)会破坏唯一性,除非有 DISTINCT(此时
 *   DISTINCT 在展开 SRF 后仍可去重),故 hasTargetSRFs 且无 distinctClause
 *   时直接返回 false;
 * - 其余只要存在 DISTINCT、GROUP BY、GROUPING SETS、聚合、HAVING、集合运
 *   算(setOperations)任一,就"可能"证明唯一,返回 true。
 *
 * 【参数】
 *   query —— 待检查的(尚未规划)子查询。
 * 【返回值】true:存在证明唯一的可能性。
 */
bool
query_supports_distinctness(Query *query)
{
	/* SRFs break distinctness except with DISTINCT, see below */
	if (query->hasTargetSRFs && query->distinctClause == NIL)
		return false;

	/* check for features we can prove distinctness with */
	if (query->distinctClause != NIL ||
		query->groupClause != NIL ||
		query->groupingSets != NIL ||
		query->hasAggs ||
		query->havingQual ||
		query->setOperations)
		return true;

	return false;
}

/*
 * query_is_distinct_for - does query never return duplicates of the
 *		specified columns?
 *
 * query is a not-yet-planned subquery (in current usage, it's always from
 * a subquery RTE, which the planner avoids scribbling on).
 *
 * distinct_cols is a list of DistinctColInfo, one per requested output column.
 * Each entry names the subquery output column number we want distinct, the
 * upper-level equality operator we'll compare values with, and that operator's
 * input collation.  We are interested in whether rows consisting of just these
 * columns are certain to be distinct.
 *
 * "Distinctness" is defined according to whether the corresponding upper-level
 * equality operators would think the values are distinct.  (Note: each opid
 * could be a cross-type operator, and thus not exactly the equality operator
 * that the subquery would use itself.  We use equality_ops_are_compatible() to
 * check compatibility.  That looks at opfamily membership for index AMs that
 * have declared that they support consistent equality semantics within an
 * opfamily, and so should give trustworthy answers for all operators that we
 * might need to deal with here.)
 *
 * The collid must also agree on equality with the collation the subquery's own
 * DISTINCT/GROUP BY/set-op uses to deduplicate the column, else the subquery's
 * distinctness does not carry over to the caller's equality semantics.  Two
 * collations agree on equality if they match or if both are deterministic (in
 * which case both reduce equality to byte-equality; see CREATE COLLATION).
 */
/*
 * query_is_distinct_for - (中文)判断子查询在指定输出列上是否保证不产生重复行
 *
 * 【作用】判断子查询 query 的行在"仅由 distinct_cols 这些列构成的元组"层面
 * 是否确定互不相同。distinct_cols 中每个 DistinctColInfo 指定:要保证唯一的
 * 输出列号、上层用来比较该列的等值算子 OID、该算子的输入排序规则。
 * 由 rel_is_distinct_for()(子查询分支)调用。
 *
 * 【设计思想】按可证明唯一的特性逐个分支处理:
 * - DISTINCT(含 DISTINCT ON):只要 distinctClause 中每个分组列的 TargetEntry
 *   都能在 colnos 中找到、且算子兼容、排序规则一致,即唯一。注意即使目标
 *   列表里有 SRF 也成立,因为 DISTINCT 在展开 SRF 之后仍去重;
 * - 目标列表 SRF:无 DISTINCT 的情况下,SRF 可能制造重复行(分组展开之后再
 *   求值),返回 false;
 * - GROUP BY(无 GROUPING SETS):分组列全在 colnos 且兼容即唯一;
 * - GROUPING SETS:若还带 groupClause 表达式则放弃;若 groupDistinct(DISTINCT
 *   作用于 GROUP BY 之后)则唯一;否则展开分组集,只有恰好一个分组集时(等
 *   价于单组聚合/整体聚合)才唯一;
 * - 无 GROUP BY 但有聚合或 HAVING:结果至多一行,必然唯一(与算子无关);
 * - 集合运算(UNION/INTERSECT/EXCEPT,非 ALL):整行去重,只要所有非 resjunk
 *   输出列都在 colnos 且兼容即唯一;
 * - "唯一性"按上层等值算子语义定义:opid 可能是跨类型算子,与子查询自己
 *   用的等值算子不同,故用 equality_ops_are_compatible() 检查操作符族兼容
 *   (只信任声明过"族内等值语义一致"的索引 AM);排序规则必须一致(完全相同,
 *   或两者都是确定性排序规则——此时等值退化为字节等值)。
 *
 * 【参数】
 *   query         —— 尚未规划的查询(当前用法总是来自子查询 RTE,planner
 *                     不会改写它);
 *   distinct_cols —— DistinctColInfo 列表,每项对应一个需要唯一的输出列。
 * 【返回值】true:该查询在这些列上确定唯一。
 */
bool
query_is_distinct_for(Query *query, List *distinct_cols)
{
	ListCell   *l;
	DistinctColInfo *dcinfo;

	/*
	 * DISTINCT (including DISTINCT ON) guarantees uniqueness if all the
	 * columns in the DISTINCT clause appear in colnos and operator semantics
	 * match.  This is true even if there are SRFs in the DISTINCT columns or
	 * elsewhere in the tlist.
	 */
	if (query->distinctClause)
	{
		foreach(l, query->distinctClause)
		{
			SortGroupClause *sgc = (SortGroupClause *) lfirst(l);
			TargetEntry *tle = get_sortgroupclause_tle(sgc,
													   query->targetList);

			dcinfo = distinct_col_search(tle->resno, distinct_cols);
			if (dcinfo == NULL ||
				!equality_ops_are_compatible(dcinfo->opid, sgc->eqop) ||
				!collations_agree_on_equality(dcinfo->collid,
											  exprCollation((Node *) tle->expr)))
				break;			/* exit early if no match */
		}
		if (l == NULL)			/* had matches for all? */
			return true;
	}

	/*
	 * Otherwise, a set-returning function in the query's targetlist can
	 * result in returning duplicate rows, despite any grouping that might
	 * occur before tlist evaluation.  (If all tlist SRFs are within GROUP BY
	 * columns, it would be safe because they'd be expanded before grouping.
	 * But it doesn't currently seem worth the effort to check for that.)
	 */
	if (query->hasTargetSRFs)
		return false;

	/*
	 * Similarly, GROUP BY without GROUPING SETS guarantees uniqueness if all
	 * the grouped columns appear in colnos and operator semantics match.
	 */
	if (query->groupClause && !query->groupingSets)
	{
		foreach(l, query->groupClause)
		{
			SortGroupClause *sgc = (SortGroupClause *) lfirst(l);
			TargetEntry *tle = get_sortgroupclause_tle(sgc,
													   query->targetList);

			dcinfo = distinct_col_search(tle->resno, distinct_cols);
			if (dcinfo == NULL ||
				!equality_ops_are_compatible(dcinfo->opid, sgc->eqop) ||
				!collations_agree_on_equality(dcinfo->collid,
											  exprCollation((Node *) tle->expr)))
				break;			/* exit early if no match */
		}
		if (l == NULL)			/* had matches for all? */
			return true;
	}
	else if (query->groupingSets)
	{
		List	   *gsets;

		/*
		 * If we have grouping sets with expressions, we probably don't have
		 * uniqueness and analysis would be hard. Punt.
		 */
		if (query->groupClause)
			return false;

		/*
		 * If we have no groupClause (therefore no grouping expressions), we
		 * might have one or many empty grouping sets.  If there's just one,
		 * or if the DISTINCT clause is used on the GROUP BY, then we're
		 * returning only one row and are certainly unique.  But otherwise, we
		 * know we're certainly not unique.
		 */
		if (query->groupDistinct)
			return true;

		gsets = expand_grouping_sets(query->groupingSets, false, -1);

		return (list_length(gsets) == 1);
	}
	else
	{
		/*
		 * If we have no GROUP BY, but do have aggregates or HAVING, then the
		 * result is at most one row so it's surely unique, for any operators.
		 */
		if (query->hasAggs || query->havingQual)
			return true;
	}

	/*
	 * UNION, INTERSECT, EXCEPT guarantee uniqueness of the whole output row,
	 * except with ALL.
	 */
	if (query->setOperations)
	{
		SetOperationStmt *topop = castNode(SetOperationStmt, query->setOperations);

		Assert(topop->op != SETOP_NONE);

		if (!topop->all)
		{
			ListCell   *lg;

			/* We're good if all the nonjunk output columns are in colnos */
			lg = list_head(topop->groupClauses);
			foreach(l, query->targetList)
			{
				TargetEntry *tle = (TargetEntry *) lfirst(l);
				SortGroupClause *sgc;

				if (tle->resjunk)
					continue;	/* ignore resjunk columns */

				/* non-resjunk columns should have grouping clauses */
				Assert(lg != NULL);
				sgc = (SortGroupClause *) lfirst(lg);
				lg = lnext(topop->groupClauses, lg);

				dcinfo = distinct_col_search(tle->resno, distinct_cols);
				if (dcinfo == NULL ||
					!equality_ops_are_compatible(dcinfo->opid, sgc->eqop) ||
					!collations_agree_on_equality(dcinfo->collid,
												  exprCollation((Node *) tle->expr)))
					break;		/* exit early if no match */
			}
			if (l == NULL)		/* had matches for all? */
				return true;
		}
	}

	/*
	 * XXX Are there any other cases in which we can easily see the result
	 * must be distinct?
	 *
	 * If you do add more smarts to this function, be sure to update
	 * query_supports_distinctness() to match.
	 */

	return false;
}

/*
 * distinct_col_search - subroutine for query_is_distinct_for
 *
 * If colno matches the colno field of an entry in distinct_cols, return a
 * pointer to that entry; else return NULL.  (Ordinarily distinct_cols would
 * not contain duplicate colnos, but if it does, we arbitrarily select the
 * first match.)
 */
/*
 * distinct_col_search - (中文)在 distinct_cols 列表中按列号查找条目
 *
 * 【作用】query_is_distinct_for() 的子程序:在 distinct_cols 中线性查找
 * colno 与给定列号匹配的 DistinctColInfo,找到即返回该条目指针,否则返回
 * NULL。
 *
 * 【设计思想】distinct_cols 通常不含重复列号,但若含重复则"任意选择第一个
 * 匹配项"也可接受——反正要比较的内容相同。
 *
 * 【参数】
 *   colno         —— 要查找的目标输出列号;
 *   distinct_cols —— DistinctColInfo 列表。
 * 【返回值】匹配条目的指针;无匹配则返回 NULL。
 */
static DistinctColInfo *
distinct_col_search(int colno, List *distinct_cols)
{
	foreach_ptr(DistinctColInfo, dcinfo, distinct_cols)
	{
		if (dcinfo->colno == colno)
			return dcinfo;
	}

	return NULL;
}


/*
 * innerrel_is_unique
 *	  Check if the innerrel provably contains at most one tuple matching any
 *	  tuple from the outerrel, based on join clauses in the 'restrictlist'.
 *
 * We need an actual RelOptInfo for the innerrel, but it's sufficient to
 * identify the outerrel by its Relids.  This asymmetry supports use of this
 * function before joinrels have been built.  (The caller is expected to
 * also supply the joinrelids, just to save recalculating that.)
 *
 * The proof must be made based only on clauses that will be "joinquals"
 * rather than "otherquals" at execution.  For an inner join there's no
 * difference; but if the join is outer, we must ignore pushed-down quals,
 * as those will become "otherquals".  Note that this means the answer might
 * vary depending on whether IS_OUTER_JOIN(jointype); since we cache the
 * answer without regard to that, callers must take care not to call this
 * with jointypes that would be classified differently by IS_OUTER_JOIN().
 *
 * The actual proof is undertaken by is_innerrel_unique_for(); this function
 * is a frontend that is mainly concerned with caching the answers.
 * In particular, the force_cache argument allows overriding the internal
 * heuristic about whether to cache negative answers; it should be "true"
 * if making an inquiry that is not part of the normal bottom-up join search
 * sequence.
 */
/*
 * innerrel_is_unique - (中文)判断内关系对给定外关系是否可证明唯一(带缓存入口)
 *
 * 【作用】基于 restrictlist 中的连接子句,判断内关系 innerrel 对来自外关系
 * (仅用 Relids 标识)的任意一行,是否至多匹配一行。这是带缓存的前端函数,
 * 实际证明由 is_innerrel_unique_for() 完成;它主要负责任何缓存与判定。由
 * reduce_unique_semijoins() 等调用。
 *
 * 【设计思想】本函数只是 innerrel_is_unique_ext() 的薄封装:force_cache 传
 * true,extra_clauses 传 NULL(普通使用场景不关心额外子句)。详细说明见
 * innerrel_is_unique_ext()。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   joinrelids  —— 该连接的全部关系 relid 集(含内关系),调用方预计算传入;
 *   outerrelids —— 外关系的 relid 集;
 *   innerrel    —— 内关系 RelOptInfo;
 *   jointype    —— 连接类型(IS_OUTER_JOIN 的取值会影响能用的子句集合);
 *   restrictlist —— 候选连接子句(RestrictInfo)列表;
 *   force_cache —— 是否强制缓存"不唯一"的负面结论。
 * 【返回值】true:证明唯一;false:无法证明。
 */
bool
innerrel_is_unique(PlannerInfo *root,
				   Relids joinrelids,
				   Relids outerrelids,
				   RelOptInfo *innerrel,
				   JoinType jointype,
				   List *restrictlist,
				   bool force_cache)
{
	return innerrel_is_unique_ext(root, joinrelids, outerrelids, innerrel,
								  jointype, restrictlist, force_cache, NULL);
}

/*
 * innerrel_is_unique_ext
 *	  Do the same as innerrel_is_unique(), but also set to (*extra_clauses)
 *	  additional clauses from a baserestrictinfo list used to prove the
 *	  uniqueness.
 *
 * A non-NULL extra_clauses indicates that we're checking for self-join and
 * correspondingly dealing with filtered clauses.
 */
/*
 * innerrel_is_unique_ext - (中文)判断内关系对给定外关系是否可证明唯一(带缓存与额外子句)
 *
 * 【作用】innerrel_is_unique() 的完整版本:同样判断唯一性,但额外允许通过
 * extra_clauses 回传"用于证明唯一性的基础限制子句"(形如 x = const)。
 * extra_clauses 非 NULL 表示正处于自连接消除场景,要处理被过滤的子句。
 *
 * 【设计思想】这是"唯一性证明"的缓存中枢:
 * - 前置快速失败:restrictlist 为空(无连接子句无从证明)或
 *   rel_supports_distinctness 预筛不过,直接 false;
 * - 查"唯一"缓存(innerrel->unique_for_rels):对非自连接场景,只要缓存条目
 *   的 outerrelids 是当前 outerrelids 的子集即可命中——多出来的外关系不会
 *   让内关系"更不唯一"(外层关系的超集对应的 restrictlist 必然包含成功用过
 *   的子句);自连接场景则要求 outerrelids 完全相等且条目也是自连接类型的,
 *   因为 extra_clauses 必须对当前场景严格有效;
 * - 查"不唯一"缓存(innerrel->non_unique_for_rels):若当前 outerrelids 是某
 *   个已证不唯一条目 outerrelids 的子集,则直接失败(超集都证不出来,子集
 *   更不可能);
 * - 以上都未命中则真正调用 is_innerrel_unique_for() 做证明;成功则在
 *   planner_cxt(而非 GEQO 的临时上下文)缓存 UniqueRelInfo;失败且
 *   force_cache 或 assumeReplanning 时也缓存"不唯一"结论——常规模式下不
 *   缓存负面结论是因为连接搜索自底向上、不会再被问到;force_cache 用于
 *   reduce_unique_semijoins 这类在连接搜索开始前的调用,assumeReplanning
 *   用于 GEQO 等多次规划的扩展。
 * - 注释提醒:本想尝试隔离"证明唯一所需的最小 outerrel 子集",但没必要——
 *   连接搜索增量构造 joinrel,必先看到最小充分集合。
 *
 * 【参数】
 *   root          —— PlannerInfo(用 planner_cxt 保存缓存);
 *   joinrelids    —— 连接的全部 relid(含内关系);
 *   outerrelids   —— 外关系 relid 集;
 *   innerrel      —— 内关系;
 *   jointype      —— 连接类型;
 *   restrictlist  —— 候选连接子句列表;
 *   force_cache   —— 是否强制缓存负面(不唯一)结论;
 *   extra_clauses —— 可选输出参数,回传证明唯一所用的基础限制子句;非 NULL
 *                     即表示自连接场景。
 * 【返回值】true:证明唯一;false:无法证明。
 */
bool
innerrel_is_unique_ext(PlannerInfo *root,
					   Relids joinrelids,
					   Relids outerrelids,
					   RelOptInfo *innerrel,
					   JoinType jointype,
					   List *restrictlist,
					   bool force_cache,
					   List **extra_clauses)
{
	MemoryContext old_context;
	ListCell   *lc;
	UniqueRelInfo *uniqueRelInfo;
	List	   *outer_exprs = NIL;
	bool		self_join = (extra_clauses != NULL);

	/* Certainly can't prove uniqueness when there are no joinclauses */
	if (restrictlist == NIL)
		return false;

	/*
	 * Make a quick check to eliminate cases in which we will surely be unable
	 * to prove uniqueness of the innerrel.
	 */
	if (!rel_supports_distinctness(root, innerrel))
		return false;

	/*
	 * Query the cache to see if we've managed to prove that innerrel is
	 * unique for any subset of this outerrel.  For non-self-join search, we
	 * don't need an exact match, as extra outerrels can't make the innerrel
	 * any less unique (or more formally, the restrictlist for a join to a
	 * superset outerrel must be a superset of the conditions we successfully
	 * used before). For self-join search, we require an exact match of
	 * outerrels because we need extra clauses to be valid for our case. Also,
	 * for self-join checking we've filtered the clauses list.  Thus, we can
	 * match only the result cached for a self-join search for another
	 * self-join check.
	 */
	foreach(lc, innerrel->unique_for_rels)
	{
		uniqueRelInfo = (UniqueRelInfo *) lfirst(lc);

		if ((!self_join && bms_is_subset(uniqueRelInfo->outerrelids, outerrelids)) ||
			(self_join && bms_equal(uniqueRelInfo->outerrelids, outerrelids) &&
			 uniqueRelInfo->self_join))
		{
			if (extra_clauses)
				*extra_clauses = uniqueRelInfo->extra_clauses;
			return true;		/* Success! */
		}
	}

	/*
	 * Conversely, we may have already determined that this outerrel, or some
	 * superset thereof, cannot prove this innerrel to be unique.
	 */
	foreach(lc, innerrel->non_unique_for_rels)
	{
		Relids		unique_for_rels = (Relids) lfirst(lc);

		if (bms_is_subset(outerrelids, unique_for_rels))
			return false;
	}

	/* No cached information, so try to make the proof. */
	if (is_innerrel_unique_for(root, joinrelids, outerrelids, innerrel,
							   jointype, restrictlist,
							   self_join ? &outer_exprs : NULL))
	{
		/*
		 * Cache the positive result for future probes, being sure to keep it
		 * in the planner_cxt even if we are working in GEQO.
		 *
		 * Note: one might consider trying to isolate the minimal subset of
		 * the outerrels that proved the innerrel unique.  But it's not worth
		 * the trouble, because the planner builds up joinrels incrementally
		 * and so we'll see the minimally sufficient outerrels before any
		 * supersets of them anyway.
		 */
		old_context = MemoryContextSwitchTo(root->planner_cxt);
		uniqueRelInfo = makeNode(UniqueRelInfo);
		uniqueRelInfo->outerrelids = bms_copy(outerrelids);
		uniqueRelInfo->self_join = self_join;
		uniqueRelInfo->extra_clauses = outer_exprs;
		innerrel->unique_for_rels = lappend(innerrel->unique_for_rels,
											uniqueRelInfo);
		MemoryContextSwitchTo(old_context);

		if (extra_clauses)
			*extra_clauses = outer_exprs;
		return true;			/* Success! */
	}
	else
	{
		/*
		 * None of the join conditions for outerrel proved innerrel unique, so
		 * we can safely reject this outerrel or any subset of it in future
		 * checks.
		 *
		 * However, in normal planning mode, caching this knowledge is totally
		 * pointless; it won't be queried again, because we build up joinrels
		 * from smaller to larger.  It's only useful when using GEQO or
		 * another planner extension that attempts planning multiple times.
		 *
		 * Also, allow callers to override that heuristic and force caching;
		 * that's useful for reduce_unique_semijoins, which calls here before
		 * the normal join search starts.
		 */
		if (force_cache || root->assumeReplanning)
		{
			old_context = MemoryContextSwitchTo(root->planner_cxt);
			innerrel->non_unique_for_rels =
				lappend(innerrel->non_unique_for_rels,
						bms_copy(outerrelids));
			MemoryContextSwitchTo(old_context);
		}

		return false;
	}
}

/*
 * is_innerrel_unique_for
 *	  Check if the innerrel provably contains at most one tuple matching any
 *	  tuple from the outerrel, based on join clauses in the 'restrictlist'.
 */
/*
 * is_innerrel_unique_for - (中文)真正执行唯一性证明的底层函数
 *
 * 【作用】基于 restrictlist 中的连接子句判断内关系 innerrel 对外关系的任意
 * 一行至多匹配一行。这是不带缓存的实际证明者,由 innerrel_is_unique_ext()
 * 在缓存未命中时调用。另注:unique_rel 缓存与 self-join 检查经由本函数也可
 * 收集 extra_clauses。
 *
 * 【设计思想】
 * - 遍历 restrictlist,收集可用的等值连接子句到 clause_list:
 *   - 外连接(jointype 满足 IS_OUTER_JOIN)时跳过 pushed-down 子句——它们
 *     执行时会变成 otherqual,不能依赖(内连接两者等价,无需区分);
 *   - 必须是 mergejoinable(can_join 且 mergeopfamilies 非空):mergejoinable
 *     算子行为类似某 btree 操作符族下的等值,且测试能排除含易变函数的子句;
 *   - 子句两侧必须分别是外关系与内关系(clause_sides_match_join);
 * - 把筛选结果交给 rel_is_distinct_for() 做真正的唯一性证明(它按
 *   RTE_RELATION 的唯一索引 / RTE_SUBQUERY 的查询性质两个分支处理)。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   joinrelids    —— 连接的全部 relid(用于外连接时判断 pushed-down);
 *   outerrelids   —— 外关系 relid 集;
 *   innerrel      —— 内关系;
 *   jointype      —— 连接类型;
 *   restrictlist  —— 候选连接子句列表;
 *   extra_clauses —— 可选输出,透传给 rel_is_distinct_for()。
 * 【返回值】true:证明唯一;false:无法证明。
 */
static bool
is_innerrel_unique_for(PlannerInfo *root,
					   Relids joinrelids,
					   Relids outerrelids,
					   RelOptInfo *innerrel,
					   JoinType jointype,
					   List *restrictlist,
					   List **extra_clauses)
{
	List	   *clause_list = NIL;
	ListCell   *lc;

	/*
	 * Search for mergejoinable clauses that constrain the inner rel against
	 * the outer rel.  If an operator is mergejoinable then it behaves like
	 * equality for some btree opclass, so it's what we want.  The
	 * mergejoinability test also eliminates clauses containing volatile
	 * functions, which we couldn't depend on.
	 */
	foreach(lc, restrictlist)
	{
		RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(lc);

		/*
		 * As noted above, if it's a pushed-down clause and we're at an outer
		 * join, we can't use it.
		 */
		if (IS_OUTER_JOIN(jointype) &&
			RINFO_IS_PUSHED_DOWN(restrictinfo, joinrelids))
			continue;

		/* Ignore if it's not a mergejoinable clause */
		if (!restrictinfo->can_join ||
			restrictinfo->mergeopfamilies == NIL)
			continue;			/* not mergejoinable */

		/*
		 * Check if the clause has the form "outer op inner" or "inner op
		 * outer", and if so mark which side is inner.
		 */
		if (!clause_sides_match_join(restrictinfo, outerrelids,
									 innerrel->relids))
			continue;			/* no good for these input relations */

		/* OK, add to the list */
		clause_list = lappend(clause_list, restrictinfo);
	}

	/* Let rel_is_distinct_for() do the hard work */
	return rel_is_distinct_for(root, innerrel, clause_list, extra_clauses);
}

/*
 * Update EC members to point to the remaining relation instead of the removed
 * one, removing duplicates.
 *
 * Restriction clauses for base relations are already distributed to
 * the respective baserestrictinfo lists (see
 * generate_implied_equalities_for_column). The above code has already processed
 * this list and updated these clauses to reference the remaining
 * relation, so that we can skip them here based on their relids.
 *
 * Likewise, we have already processed the join clauses that join the
 * removed relation to the remaining one.
 *
 * Finally, there might be join clauses tying the removed relation to
 * some third relation.  We can't just delete the source clauses and
 * regenerate them from the EC because the corresponding equality
 * operators might be missing (see the handling of ec_broken).
 * Therefore, we will update the references in the source clauses.
 *
 * Derived clauses can be generated again, so it is simpler just to
 * delete them.
 */
/*
 * update_eclasses - (中文)自连接消除时把等价类成员从被删关系改写为保留关系
 *
 * 【作用】把等价类 ec 中所有引用"被删关系 from"的成员(EquivalenceMember)与
 * 源子句(ec_sources)改写为指向"保留关系 to",并去除改写造成的重复项。由
 * remove_self_join_rel() 对被删关系涉及的每个 EC 调用。
 *
 * 【设计思想】
 * - 基础关系的限制子句早已分布到各自的 baserestrictinfo(见
 *   generate_implied_equalities_for_column),且调用链中的 replace_relid_callback
 *   已把这些子句改写到保留关系,所以这里可以依据 relids 直接跳过它们;
 * - 连接被删关系与保留关系的连接子句也已在调用链中处理过;
 * - 把被删关系与第三方关系相连的连接子句不能简单删除再重建:对应等值算子
 *   可能缺失(即 ec_broken 情形),因此必须原地改写源子句里的 Var 引用;
 * - 对成员:改写 em_relids、em_jdomain->jd_relids,并用 ChangeVarNodesExtended
 *   改写 em_expr 中 Var 的 varno;然后与已处理过的成员比较,若 em_relids 与
 *   em_expr 都相同则判定为冗余并丢弃;
 * - 对源子句:同样改写 rinfo,比较 clause_relids 与 clause 判重;
 * - 已派生子句(ec_derives)一律删除,反正可以重新生成;
 * - 断言 ec_childmembers 为空(本阶段没有子 EC)。
 *
 * 【参数】
 *   ec   —— 待更新的等价类;
 *   from —— 被删除(改写)的关系 RT index;
 *   to   —— 保留(替换目标)的关系 RT index。
 * 【返回值】void。
 */
static void
update_eclasses(EquivalenceClass *ec, int from, int to)
{
	List	   *new_members = NIL;
	List	   *new_sources = NIL;

	/*
	 * We don't expect any EC child members to exist at this point.  Ensure
	 * that's the case, otherwise, we might be getting asked to do something
	 * this function hasn't been coded for.
	 */
	Assert(ec->ec_childmembers == NULL);

	foreach_node(EquivalenceMember, em, ec->ec_members)
	{
		bool		is_redundant = false;

		if (!bms_is_member(from, em->em_relids))
		{
			new_members = lappend(new_members, em);
			continue;
		}

		em->em_relids = adjust_relid_set(em->em_relids, from, to);
		em->em_jdomain->jd_relids = adjust_relid_set(em->em_jdomain->jd_relids, from, to);

		/* We only process inner joins */
		ChangeVarNodesExtended((Node *) em->em_expr, from, to, 0,
							   replace_relid_callback);

		foreach_node(EquivalenceMember, other, new_members)
		{
			if (!equal(em->em_relids, other->em_relids))
				continue;

			if (equal(em->em_expr, other->em_expr))
			{
				is_redundant = true;
				break;
			}
		}

		if (!is_redundant)
			new_members = lappend(new_members, em);
	}

	list_free(ec->ec_members);
	ec->ec_members = new_members;

	ec_clear_derived_clauses(ec);

	/* Update EC source expressions */
	foreach_node(RestrictInfo, rinfo, ec->ec_sources)
	{
		bool		is_redundant = false;

		if (!bms_is_member(from, rinfo->required_relids))
		{
			new_sources = lappend(new_sources, rinfo);
			continue;
		}

		ChangeVarNodesExtended((Node *) rinfo, from, to, 0,
							   replace_relid_callback);

		/*
		 * After switching the clause to the remaining relation, check it for
		 * redundancy with existing ones. We don't have to check for
		 * redundancy with derived clauses, because we've just deleted them.
		 */
		foreach_node(RestrictInfo, other, new_sources)
		{
			if (!equal(rinfo->clause_relids, other->clause_relids))
				continue;

			if (equal(rinfo->clause, other->clause))
			{
				is_redundant = true;
				break;
			}
		}

		if (!is_redundant)
			new_sources = lappend(new_sources, rinfo);
	}

	list_free(ec->ec_sources);
	ec->ec_sources = new_sources;
	ec->ec_relids = adjust_relid_set(ec->ec_relids, from, to);
}

/*
 * "Logically" compares two RestrictInfo's ignoring the 'rinfo_serial' field,
 * which makes almost every RestrictInfo unique.  This type of comparison is
 * useful when removing duplicates while moving RestrictInfo's from removed
 * relation to remaining relation during self-join elimination.
 *
 * XXX: In the future, we might remove the 'rinfo_serial' field completely and
 * get rid of this function.
 */
/*
 * restrict_infos_logically_equal - (中文)忽略 rinfo_serial 字段比较两个 RestrictInfo
 *
 * 【作用】在"逻辑上"比较两个 RestrictInfo 是否相等:临时把 a->rinfo_serial 设
 * 成与 b 相同再调用 equal(),用完恢复。用于自连接消除时把子句从被删关系搬
 * 到保留关系的过程中去重。
 *
 * 【设计思想】rinfo_serial 是每个 RestrictInfo 唯一的序号,直接 equal() 几乎
 * 总返回 false;而去重时我们关心的是"子句逻辑内容是否相同",所以临时对齐该
 * 字段再比较。注释提到未来可能彻底删除 rinfo_serial 字段从而去掉本函数。
 *
 * 【参数】
 *   a —— 待比较的 RestrictInfo(其 rinfo_serial 会被临时改写并恢复);
 *   b —— 待比较的 RestrictInfo。
 * 【返回值】忽略 rinfo_serial 后两者逻辑相等返回 true。
 */
static bool
restrict_infos_logically_equal(RestrictInfo *a, RestrictInfo *b)
{
	int			saved_rinfo_serial = a->rinfo_serial;
	bool		result;

	a->rinfo_serial = b->rinfo_serial;
	result = equal(a, b);
	a->rinfo_serial = saved_rinfo_serial;

	return result;
}

/*
 * This function adds all non-redundant clauses to the keeping relation
 * during self-join elimination.  That is a contradictory operation. On the
 * one hand, we reduce the length of the `restrict` lists, which can
 * impact planning or executing time.  Additionally, we improve the
 * accuracy of cardinality estimation.  On the other hand, it is one more
 * place that can make planning time much longer in specific cases.  It
 * would have been better to avoid calling the equal() function here, but
 * it's the only way to detect duplicated inequality expressions.
 *
 * (*keep_rinfo_list) is given by pointer because it might be altered by
 * distribute_restrictinfo_to_rels().
 */
/*
 * add_non_redundant_clauses - (中文)把候选子句中非冗余的部分分发给保留关系
 *
 * 【作用】自连接消除时,把 rinfo_candidates 里不重复的子句通过
 * distribute_restrictinfo_to_rels() 分发给保留关系(*keep_rinfo_list 所指的
 * baserestrictinfo 或 joininfo);重复的丢弃。由 remove_self_join_rel() 分别对
 * 限制子句候选和连接子句候选调用。
 *
 * 【设计思想】这是一个"矛盾"的操作:一方面缩短 restrict 列表可提升规划/执行
 * 速度并提高基数估计精度;另一方面这是又一处可能使规划时间显著变长的点
 * (调用 equal() 是检测重复不等值表达式的唯一途径,但代价昂贵)。判重逻辑:
 * - 若 clause_relids 不同,无需比较(显然不同);
 * - 与已有条目相同指针、或同属一个 parent_ec、或 restrict_infos_logically_equal
 *   则视为冗余;
 * - 断言候选子句的 required_relids 不含被删关系。
 * 注意 *keep_rinfo_list 用指针传递,因为 distribute_restrictinfo_to_rels() 可能
 * 原地修改它。
 *
 * 【参数】
 *   root            —— PlannerInfo;
 *   rinfo_candidates —— 候选 RestrictInfo 列表;
 *   keep_rinfo_list  —— 输出,保留关系的 baserestrictinfo / joininfo 列表指针;
 *   removed_relid    —— 被删关系 RT index(用于断言)。
 * 【返回值】void。
 */
static void
add_non_redundant_clauses(PlannerInfo *root,
						  List *rinfo_candidates,
						  List **keep_rinfo_list,
						  Index removed_relid)
{
	foreach_node(RestrictInfo, rinfo, rinfo_candidates)
	{
		bool		is_redundant = false;

		Assert(!bms_is_member(removed_relid, rinfo->required_relids));

		foreach_node(RestrictInfo, src, (*keep_rinfo_list))
		{
			if (!bms_equal(src->clause_relids, rinfo->clause_relids))
				/* Can't compare trivially different clauses */
				continue;

			if (src == rinfo ||
				(rinfo->parent_ec != NULL &&
				 src->parent_ec == rinfo->parent_ec) ||
				restrict_infos_logically_equal(rinfo, src))
			{
				is_redundant = true;
				break;
			}
		}
		if (!is_redundant)
			distribute_restrictinfo_to_rels(root, rinfo);
	}
}

/*
 * A custom callback for ChangeVarNodesExtended() providing Self-join
 * elimination (SJE) related functionality
 *
 * SJE needs to skip the RangeTblRef node type.  During SJE's last
 * step, remove_rel_from_joinlist() removes remaining RangeTblRefs
 * with target relid.  If ChangeVarNodes() replaces the target relid
 * before, remove_rel_from_joinlist() would fail to identify the nodes
 * to delete.
 *
 * SJE also needs to change the relids within RestrictInfo's.
 */
/*
 * replace_relid_callback - (中文)ChangeVarNodesExtended 的 SJE 专用回调
 *
 * 【作用】为 ChangeVarNodesExtended() 提供自连接消除(SJE)专用的节点处理回调:
 * 跳过 RangeTblRef,并对 RestrictInfo 做特殊处理(改写其各 relid 位图、递归下
 * 探到 clause/orclause,必要时把 "t1.a = t1.a" 改写为 IS NOT NULL)。返回 true
 * 表示"已处理完该节点,不要再走默认的 varno 替换逻辑"。
 *
 * 【设计思想】
 * - 必须跳过 RangeTblRef:SJE 最后一步 remove_rel_from_joinlist() 要按 relid
 *   删除残留的 RangeTblRef;若 ChangeVarNodes 先把 varno 换掉,后面的删除就
 *   认不出这些节点了;
 * - RestrictInfo 分支:先把 relid 是否出现在 clause_relids / required_relids
 *   记下来;若出现,递归改写 clause 与 orclause 内的表达式,并用
 *   adjust_relid_set 改写 clause_relids / left_relids / right_relids,同时增量
 *   修正 num_base_rels(减掉替换减少的成员数);required_relids 若原本与
 *   clause_relids 是同一对象则跟随新值,否则单独 adjust;outer_relids /
 *   incompatible_relids 也 adjust;
 * - 特殊情况:改写后 clause_relids 变成单例且恰好是保留关系、且原
 *   clause_relids 是多成员、且子句是 OpExpr——这对应 "t1.a = t2.a" 变成
 *   "t1.a = t1.a"。此时左边等于右边恒成立(只要非 NULL),故把子句改写为
 *   IS NOT NULL 检查(NullTest),并清掉 mergeopfamilies / left_em / right_em
 *   使其不再被当作等值连接子句。
 *
 * 【参数】
 *   node    —— 当前访问的节点;
 *   context —— ChangeVarNodes_context,含 rt_index(被替换的旧 relid)与
 *              new_index(新 relid)。
 * 【返回值】true:节点已按 SJE 语义处理(对 RangeTblRef / RestrictInfo 而言);
 * false:应交给默认 varno 替换逻辑。
 */
static bool
replace_relid_callback(Node *node, ChangeVarNodes_context *context)
{
	if (IsA(node, RangeTblRef))
	{
		return true;
	}
	else if (IsA(node, RestrictInfo))
	{
		RestrictInfo *rinfo = (RestrictInfo *) node;
		int			relid = -1;
		bool		is_req_equal =
			(rinfo->required_relids == rinfo->clause_relids);
		bool		clause_relids_is_multiple =
			(bms_membership(rinfo->clause_relids) == BMS_MULTIPLE);

		/*
		 * Recurse down into clauses if the target relation is present in
		 * clause_relids or required_relids.  We must check required_relids
		 * because the relation not present in clause_relids might still be
		 * present somewhere in orclause.
		 */
		if (bms_is_member(context->rt_index, rinfo->clause_relids) ||
			bms_is_member(context->rt_index, rinfo->required_relids))
		{
			Relids		new_clause_relids;

			ChangeVarNodesWalkExpression((Node *) rinfo->clause, context);
			ChangeVarNodesWalkExpression((Node *) rinfo->orclause, context);

			new_clause_relids = adjust_relid_set(rinfo->clause_relids,
												 context->rt_index,
												 context->new_index);

			/*
			 * Incrementally adjust num_base_rels based on the change of
			 * clause_relids, which could contain both base relids and
			 * outer-join relids.  This operation is legal until we remove
			 * only baserels.
			 */
			rinfo->num_base_rels -= bms_num_members(rinfo->clause_relids) -
				bms_num_members(new_clause_relids);

			rinfo->clause_relids = new_clause_relids;
			rinfo->left_relids =
				adjust_relid_set(rinfo->left_relids, context->rt_index, context->new_index);
			rinfo->right_relids =
				adjust_relid_set(rinfo->right_relids, context->rt_index, context->new_index);
		}

		if (is_req_equal)
			rinfo->required_relids = rinfo->clause_relids;
		else
			rinfo->required_relids =
				adjust_relid_set(rinfo->required_relids, context->rt_index, context->new_index);

		rinfo->outer_relids =
			adjust_relid_set(rinfo->outer_relids, context->rt_index, context->new_index);
		rinfo->incompatible_relids =
			adjust_relid_set(rinfo->incompatible_relids, context->rt_index, context->new_index);

		if (rinfo->mergeopfamilies &&
			bms_get_singleton_member(rinfo->clause_relids, &relid) &&
			clause_relids_is_multiple &&
			relid == context->new_index && IsA(rinfo->clause, OpExpr))
		{
			Expr	   *leftOp;
			Expr	   *rightOp;

			leftOp = (Expr *) get_leftop(rinfo->clause);
			rightOp = (Expr *) get_rightop(rinfo->clause);

			/*
			 * For self-join elimination, changing varnos could transform
			 * "t1.a = t2.a" into "t1.a = t1.a".  That is always true as long
			 * as "t1.a" is not null.  We use equal() to check for such a
			 * case, and then we replace the qual with a check for not null
			 * (NullTest).
			 */
			if (leftOp != NULL && equal(leftOp, rightOp))
			{
				NullTest   *ntest = makeNode(NullTest);

				ntest->arg = leftOp;
				ntest->nulltesttype = IS_NOT_NULL;
				ntest->argisrow = false;
				ntest->location = -1;
				rinfo->clause = (Expr *) ntest;
				rinfo->mergeopfamilies = NIL;
				rinfo->left_em = NULL;
				rinfo->right_em = NULL;
			}
			Assert(rinfo->orclause == NULL);
		}
		return true;
	}

	return false;
}

/*
 * Remove a relation after we have proven that it participates only in an
 * unneeded unique self-join.
 *
 * Replace any links in planner info structures.
 *
 * Transfer join and restriction clauses from the removed relation to the
 * remaining one. We change the Vars of the clause to point to the
 * remaining relation instead of the removed one. The clauses that require
 * a subset of joinrelids become restriction clauses of the remaining
 * relation, and others remain join clauses. We append them to
 * baserestrictinfo and joininfo, respectively, trying not to introduce
 * duplicates.
 *
 * We also have to process the 'joinclauses' list here, because it
 * contains EC-derived join clauses which must become filter clauses. It
 * is not enough to just correct the ECs because the EC-derived
 * restrictions are generated before join removal (see
 * generate_base_implied_equalities).
 *
 * NOTE: Remember to keep the code in sync with PlannerInfo to be sure all
 * cached relids and relid bitmapsets can be correctly cleaned during the
 * self-join elimination procedure.
 */
/*
 * remove_self_join_rel - (中文)自连接消除:摘除被证明无用的关系并改写所有引用
 *
 * 【作用】在证明某关系只参与无用的唯一自连接之后,把它从查询中移除:把
 * 规划器各结构中指向被删关系(toRemove)的引用全部改写为保留关系(toKeep),
 * 转移/去重连接与限制子句、等价类、目标列表、attr_needed、行标记等。
 * 由 remove_self_joins_one_group() 调用。
 *
 * 【设计思想】执行顺序(顺序很关键):
 * - 先把 toRemove->joininfo 复制后逐一 remove_join_clause_from_rels(从其它
 *   关系的 joininfo 里摘掉),再用 replace_relid_callback 改写子句,并按
 *   required_relids 是否多成员分入 jinfo_candidates / binfo_candidates;
 * - 把 restrictlist(调用者传入的连接子句)并入 toRemove->baserestrictinfo,
 *   同样改写并归类;
 * - add_non_redundant_clauses() 把两批候选去重后加入保留关系的 joininfo /
 *   baserestrictinfo;
 * - 对 toRemove->eclass_indexes 中的每个 EC 调 update_eclasses() 改写成员,
 *   并把 EC 序号加入 toKeep->eclass_indexes;
 * - 转移 reltarget 表达式(去重)与 attr_needed 位图(把被删关系的属性需要
 *   并入保留关系);
 * - 行标记处理:若两者都有行标记则保留保留关系的并删掉被删关系的(强度
 *   已断言相等);仅被删关系有则改写其 rti/prti 指向保留关系;
 * - 对 root->parse 与 root->processed_tlist 用 ChangeVarNodesExtended + 回调
 *   改写 Var(注意不能动 RangeTblRef,否则 remove_rel_from_joinlist 会找不到
 *   待删节点);
 * - 调 remove_rel_from_query()(sjinfo=NULL、subst=toKeep->relid)清理共享结构;
 * - 断言 toRemove->relid 不在 all_result_relids / leaf_result_relids(此时结果
 *   关系集合里只有 parse->resultRelation,而 SJE 已拒绝把结果关系当候选,以
 *   保护 EPQ 机制);
 * - 清空 simple_rel_array / simple_rte_array 槽位并 pfree RelOptInfo;最后重建
 *   各来源的 attr_needed 位图。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   kmark       —— 保留关系的行标记(可能为 NULL);
 *   rmark       —— 被删关系的行标记(可能为 NULL);
 *   toKeep      —— 保留的关系;
 *   toRemove    —— 被删的关系;
 *   restrictlist —— 该自连接的连接子句列表。
 * 【返回值】void。
 */
static void
remove_self_join_rel(PlannerInfo *root, PlanRowMark *kmark, PlanRowMark *rmark,
					 RelOptInfo *toKeep, RelOptInfo *toRemove,
					 List *restrictlist)
{
	List	   *joininfos;
	ListCell   *lc;
	int			i;
	List	   *jinfo_candidates = NIL;
	List	   *binfo_candidates = NIL;

	Assert(toKeep->relid > 0);
	Assert(toRemove->relid > 0);

	/*
	 * Replace the index of the removing table with the keeping one. The
	 * technique of removing/distributing restrictinfo is used here to attach
	 * just appeared (for keeping relation) join clauses and avoid adding
	 * duplicates of those that already exist in the joininfo list.
	 */
	joininfos = list_copy(toRemove->joininfo);
	foreach_node(RestrictInfo, rinfo, joininfos)
	{
		remove_join_clause_from_rels(root, rinfo, rinfo->required_relids);
		ChangeVarNodesExtended((Node *) rinfo, toRemove->relid, toKeep->relid,
							   0, replace_relid_callback);

		if (bms_membership(rinfo->required_relids) == BMS_MULTIPLE)
			jinfo_candidates = lappend(jinfo_candidates, rinfo);
		else
			binfo_candidates = lappend(binfo_candidates, rinfo);
	}

	/*
	 * Concatenate restrictlist to the list of base restrictions of the
	 * removing table just to simplify the replacement procedure: all of them
	 * weren't connected to any keeping relations and need to be added to some
	 * rels.
	 */
	toRemove->baserestrictinfo = list_concat(toRemove->baserestrictinfo,
											 restrictlist);
	foreach_node(RestrictInfo, rinfo, toRemove->baserestrictinfo)
	{
		ChangeVarNodesExtended((Node *) rinfo, toRemove->relid, toKeep->relid,
							   0, replace_relid_callback);

		if (bms_membership(rinfo->required_relids) == BMS_MULTIPLE)
			jinfo_candidates = lappend(jinfo_candidates, rinfo);
		else
			binfo_candidates = lappend(binfo_candidates, rinfo);
	}

	/*
	 * Now, add all non-redundant clauses to the keeping relation.
	 */
	add_non_redundant_clauses(root, binfo_candidates,
							  &toKeep->baserestrictinfo, toRemove->relid);
	add_non_redundant_clauses(root, jinfo_candidates,
							  &toKeep->joininfo, toRemove->relid);

	list_free(binfo_candidates);
	list_free(jinfo_candidates);

	/*
	 * Arrange equivalence classes, mentioned removing a table, with the
	 * keeping one: varno of removing table should be replaced in members and
	 * sources lists. Also, remove duplicated elements if this replacement
	 * procedure created them.
	 */
	i = -1;
	while ((i = bms_next_member(toRemove->eclass_indexes, i)) >= 0)
	{
		EquivalenceClass *ec = (EquivalenceClass *) list_nth(root->eq_classes, i);

		update_eclasses(ec, toRemove->relid, toKeep->relid);
		toKeep->eclass_indexes = bms_add_member(toKeep->eclass_indexes, i);
	}

	/*
	 * Transfer the targetlist and attr_needed flags.
	 */

	foreach(lc, toRemove->reltarget->exprs)
	{
		Node	   *node = lfirst(lc);

		ChangeVarNodesExtended(node, toRemove->relid, toKeep->relid, 0,
							   replace_relid_callback);
		if (!list_member(toKeep->reltarget->exprs, node))
			toKeep->reltarget->exprs = lappend(toKeep->reltarget->exprs, node);
	}

	for (i = toKeep->min_attr; i <= toKeep->max_attr; i++)
	{
		int			attno = i - toKeep->min_attr;

		toRemove->attr_needed[attno] = adjust_relid_set(toRemove->attr_needed[attno],
														toRemove->relid, toKeep->relid);
		toKeep->attr_needed[attno] = bms_add_members(toKeep->attr_needed[attno],
													 toRemove->attr_needed[attno]);
	}

	/*
	 * If the removed relation has a row mark, transfer it to the remaining
	 * one.
	 *
	 * If both rels have row marks, just keep the one corresponding to the
	 * remaining relation because we verified earlier that they have the same
	 * strength.
	 */
	if (rmark)
	{
		if (kmark)
		{
			Assert(kmark->markType == rmark->markType);

			root->rowMarks = list_delete_ptr(root->rowMarks, rmark);
		}
		else
		{
			/* Shouldn't have inheritance children here. */
			Assert(rmark->rti == rmark->prti);

			rmark->rti = rmark->prti = toKeep->relid;
		}
	}

	/*
	 * Replace varno in all the query structures, except nodes RangeTblRef
	 * otherwise later remove_rel_from_joinlist will yield errors.
	 */
	ChangeVarNodesExtended((Node *) root->parse, toRemove->relid, toKeep->relid,
						   0, replace_relid_callback);

	/* Replace links in the planner info */
	remove_rel_from_query(root, toRemove->relid, toKeep->relid, NULL, NULL);

	/* Replace varno in the fully-processed targetlist */
	ChangeVarNodesExtended((Node *) root->processed_tlist, toRemove->relid,
						   toKeep->relid, 0, replace_relid_callback);

	/*
	 * No need to touch all_result_relids or leaf_result_relids: at this point
	 * those sets contain only parse->resultRelation; inheritance children
	 * have not been added yet; that happens later in add_other_rels_to_query.
	 * And remove_self_joins_recurse rejects parse->resultRelation as an SJE
	 * candidate to preserve the EPQ mechanism.  So toRemove->relid cannot be
	 * a member.
	 */
	Assert(!bms_is_member(toRemove->relid, root->all_result_relids));
	Assert(!bms_is_member(toRemove->relid, root->leaf_result_relids));

	/*
	 * There may be references to the rel in root->fkey_list, but if so,
	 * match_foreign_keys_to_quals() will get rid of them.
	 */

	/*
	 * Finally, remove the rel from the baserel array to prevent it from being
	 * referenced again.  (We can't do this earlier because
	 * remove_join_clause_from_rels will touch it.)
	 */
	root->simple_rel_array[toRemove->relid] = NULL;
	root->simple_rte_array[toRemove->relid] = NULL;

	/* And nuke the RelOptInfo, just in case there's another access path. */
	pfree(toRemove);


	/*
	 * Now repeat construction of attr_needed bits coming from all other
	 * sources.
	 */
	rebuild_placeholder_attr_needed(root);
	rebuild_joinclause_attr_needed(root);
	rebuild_eclass_attr_needed(root);
	rebuild_lateral_attr_needed(root);
}

/*
 * split_selfjoin_quals
 *		Processes 'joinquals' by building two lists: one containing the quals
 *		where the columns/exprs are on either side of the join match and
 *		another one containing the remaining quals.
 *
 * 'joinquals' must only contain quals for a RTE_RELATION being joined to
 * itself.
 */
/*
 * split_selfjoin_quals - (中文)把自连接的连接子句分为"自连接子句"与"其它子句"
 *
 * 【作用】处理 joinquals,构建两个列表:*selfjoinquals 存放"两侧表达式在把右
 * 侧 relid 换成左侧后完全相等"的子句(如 "t1.x = t2.x",改写后为 "x = x",
 * 即自连接子句);*otherjoinquals 存放其余子句(如 "t1.a = t2.b" 或非等值
 * 形式)。由 remove_self_joins_one_group() 调用。
 *
 * 【设计思想】
 * - joinquals 只能包含"同一张 RTE_RELATION 自连接"产生的子句;
 * - 一般子句形如 F(arg1) = G(arg2)。只有满足:mergejoinable(mergeopfamilies
 *   非空)、clause_relids 恰好两个成员、left_relids 与 right_relids 各为单
 *   例、clause 是二目 OpExpr,才值得尝试判断是否"自连接子句";
 * - 判断方法:取左操作数(剥 RelabelType),再取右操作数的拷贝并把其中引用的
 *   右侧关系 relid 用 ChangeVarNodesExtended 改写为左侧 relid,最后 equal()
 *   比较左右两侧;相等 → 自连接子句(执行时同一行内恒真,可换成 NOT NULL 检
 *   查),否则 → 其它子句。注释提示这是相当昂贵的操作,故适用面被刻意收窄
 *   (例如同一 Var 到不同但兼容类型的 cast 就无法识别)。
 *
 * 【参数】
 *   root           —— PlannerInfo;
 *   joinquals      —— 自连接的连接子句列表;
 *   selfjoinquals  —— 输出:自连接子句(X = X 形);
 *   otherjoinquals —— 输出:其余子句;
 *   from           —— 一侧(右)关系 relid;
 *   to             —— 另一侧(左)关系 relid。
 * 【返回值】void。
 */
static void
split_selfjoin_quals(PlannerInfo *root, List *joinquals, List **selfjoinquals,
					 List **otherjoinquals, int from, int to)
{
	List	   *sjoinquals = NIL;
	List	   *ojoinquals = NIL;

	foreach_node(RestrictInfo, rinfo, joinquals)
	{
		OpExpr	   *expr;
		Node	   *leftexpr;
		Node	   *rightexpr;

		/* In general, clause looks like F(arg1) = G(arg2) */
		if (!rinfo->mergeopfamilies ||
			bms_num_members(rinfo->clause_relids) != 2 ||
			bms_membership(rinfo->left_relids) != BMS_SINGLETON ||
			bms_membership(rinfo->right_relids) != BMS_SINGLETON)
		{
			ojoinquals = lappend(ojoinquals, rinfo);
			continue;
		}

		expr = (OpExpr *) rinfo->clause;

		if (!IsA(expr, OpExpr) || list_length(expr->args) != 2)
		{
			ojoinquals = lappend(ojoinquals, rinfo);
			continue;
		}

		leftexpr = get_leftop(rinfo->clause);
		rightexpr = copyObject(get_rightop(rinfo->clause));

		if (leftexpr && IsA(leftexpr, RelabelType))
			leftexpr = (Node *) ((RelabelType *) leftexpr)->arg;
		if (rightexpr && IsA(rightexpr, RelabelType))
			rightexpr = (Node *) ((RelabelType *) rightexpr)->arg;

		/*
		 * Quite an expensive operation, narrowing the use case. For example,
		 * when we have cast of the same var to different (but compatible)
		 * types.
		 */
		ChangeVarNodesExtended(rightexpr,
							   bms_singleton_member(rinfo->right_relids),
							   bms_singleton_member(rinfo->left_relids), 0,
							   replace_relid_callback);

		if (equal(leftexpr, rightexpr))
			sjoinquals = lappend(sjoinquals, rinfo);
		else
			ojoinquals = lappend(ojoinquals, rinfo);
	}

	*selfjoinquals = sjoinquals;
	*otherjoinquals = ojoinquals;
}

/*
 * Check for a case when uniqueness is at least partly derived from a
 * baserestrictinfo clause. In this case, we have a chance to return only
 * one row (if such clauses on both sides of SJ are equal) or nothing (if they
 * are different).
 */
/*
 * match_unique_clauses - (中文)校验两侧基础限制子句是否一致,保证唯一性结论成立
 *
 * 【作用】当唯一性至少部分来自基础限制子句(baserestrictinfo)时,校验:把被
 * 删关系 relid 侧的"唯一性来源子句"uclauses 改写为引用外关系后,外关系的
 * baserestrictinfo 中必须存在"两侧都完全一致"的对应子句;否则两侧可能匹配
 * 不同行,唯一性结论不成立,返回 false。由 remove_self_joins_one_group() 调用。
 *
 * 【设计思想】
 * - uclauses 是 innerrel_is_unique_ext 通过 extra_clauses 回传的、与唯一索引
 *   关联的 "f(R.x1,...,R.xn) = expr" 形基础子句;仅用这些子句配合唯一索引
 *   只能证明"内关系侧对每个外行至多匹配一行",而自连接要求两侧选到的是
 *   "同一物理行"。例:"WHERE s1.b = s2.b AND s1.a = 1 AND s2.a = 2" 且唯一索
 *   引是 (a,b):若右侧唯一性子句没在外侧找到相同表达式,两侧过滤条件不同,
 *   匹配到的行可能不是同一行;
 * - 对每条 uclauses:拷贝后把 relid 改写为 outer->relid;子句一侧是"限定值
 *   侧"(iclause,通常是常量/表达式),另一侧是"列侧"(c1);再遍历外关系的
 *   baserestrictinfo,要求存在同样形态(合并可连接的 F(X)=G(Y))的子句,且其
 *   "值侧"与"列侧"分别与 iclause、c1 相等(注意两侧方向的对称处理);
 * - 任一 uclauses 未匹配到即返回 false。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   outer   —— 保留(外)关系;
 *   uclauses —— 被删侧的唯一性来源基础子句列表;
 *   relid   —— 被删关系的 relid(用于改写)。
 * 【返回值】true:两侧限制子句一致,可以继续消除自连接。
 */
static bool
match_unique_clauses(PlannerInfo *root, RelOptInfo *outer, List *uclauses,
					 Index relid)
{
	foreach_node(RestrictInfo, rinfo, uclauses)
	{
		Expr	   *clause;
		Node	   *iclause;
		Node	   *c1;
		bool		matched = false;

		Assert(outer->relid > 0 && relid > 0);

		/* Only filters like f(R.x1,...,R.xN) == expr we should consider. */
		Assert(bms_is_empty(rinfo->left_relids) ^
			   bms_is_empty(rinfo->right_relids));

		clause = (Expr *) copyObject(rinfo->clause);
		ChangeVarNodesExtended((Node *) clause, relid, outer->relid, 0,
							   replace_relid_callback);

		iclause = bms_is_empty(rinfo->left_relids) ? get_rightop(clause) :
			get_leftop(clause);
		c1 = bms_is_empty(rinfo->left_relids) ? get_leftop(clause) :
			get_rightop(clause);

		/*
		 * Compare these left and right sides with the corresponding sides of
		 * the outer's filters. If no one is detected - return immediately.
		 */
		foreach_node(RestrictInfo, orinfo, outer->baserestrictinfo)
		{
			Node	   *oclause;
			Node	   *c2;

			if (orinfo->mergeopfamilies == NIL)
				/* Don't consider clauses that aren't similar to 'F(X)=G(Y)' */
				continue;

			Assert(is_opclause(orinfo->clause));

			oclause = bms_is_empty(orinfo->left_relids) ?
				get_rightop(orinfo->clause) : get_leftop(orinfo->clause);
			c2 = (bms_is_empty(orinfo->left_relids) ?
				  get_leftop(orinfo->clause) : get_rightop(orinfo->clause));

			if (equal(iclause, oclause) && equal(c1, c2))
			{
				matched = true;
				break;
			}
		}

		if (!matched)
			return false;
	}

	return true;
}

/*
 * Find and remove unique self-joins in a group of base relations that have
 * the same Oid.
 *
 * Returns a set of relids that were removed.
 */
/*
 * remove_self_joins_one_group - (中文)在一组同 OID 的基础关系中查找并移除唯一自连接
 *
 * 【作用】对"相同 OID 的基础关系集合"(同一张表出现多次)两两尝试消除自连
 * 接:满足全部前置条件时调用 remove_self_join_rel() 摘除其中一个关系并改写
 * 引用。返回被摘除的 relid 集合。由 remove_self_joins_recurse() 调用。
 *
 * 【设计思想】外层双重循环(r 为被删候选、k 为保留候选),对每对关系依次
 * 检查:
 * - 同属一个连接顺序约束组:若二者在任一 SpecialJoinInfo 的 syn_lefthand /
 *   syn_righthand 中归属不同,则不能消除(否则规划器无法找到正确的计划变体);
 * - 行标记强度一致:若两者都有行标记且 markType 不同(如一个 FOR UPDATE、
 *   另一个只是 EPQ 的 ROW_MARK_REFERENCE),不能消除;
 * - 构造 joinrelids({r,k}),生成 implied 连接子句
 *   (generate_join_implied_equalities);此时 joininfo 里只可能有"为更上层外
 *   连接服务"的子句,不影响本优化,故不必调 build_joinrel_restrictlist;
 * - split_selfjoin_quals() 分出"自连接子句"与"其它子句";把保留侧
 *   baserestrictinfo 并入自连接子句,以支持"完全没有自连接子句的退化情形"
 *   (前提是两侧子句相同);
 * - 用 innerrel_is_unique_ext() 证明唯一:由于这里用的是"子集"的连接子句,
 *   必须绕过常规的唯一缓存,故传 uclauses 收集;仅当所有连接子句都是自连接
 *   子句时(其它子句为空)才能 force_cache=true,否则会把假阴性结论塞进缓存;
 * - 有 uclauses 时再经 match_unique_clauses() 校验两侧基础子句一致;
 * - 全部通过则 remove_self_join_rel() 摘除 r,把 r 记入 result,break 到外层
 *   试下一个被删候选。
 *
 * 【参数】
 *   root   —— PlannerInfo;
 *   relids —— 同 OID 的基础关系 relid 集合(至少两个成员)。
 * 【返回值】实际被移除的关系 relid 集合(可能为空)。
 */
static Relids
remove_self_joins_one_group(PlannerInfo *root, Relids relids)
{
	Relids		result = NULL;
	int			k;				/* Index of kept relation */
	int			r = -1;			/* Index of removed relation */

	while ((r = bms_next_member(relids, r)) > 0)
	{
		RelOptInfo *rrel = root->simple_rel_array[r];

		k = r;

		while ((k = bms_next_member(relids, k)) > 0)
		{
			Relids		joinrelids = NULL;
			RelOptInfo *krel = root->simple_rel_array[k];
			List	   *restrictlist;
			List	   *selfjoinquals;
			List	   *otherjoinquals;
			ListCell   *lc;
			bool		jinfo_check = true;
			PlanRowMark *kmark = NULL;
			PlanRowMark *rmark = NULL;
			List	   *uclauses = NIL;

			/* A sanity check: the relations have the same Oid. */
			Assert(root->simple_rte_array[k]->relid ==
				   root->simple_rte_array[r]->relid);

			/*
			 * It is impossible to eliminate the join of two relations if they
			 * belong to different rules of order. Otherwise, the planner
			 * can't find any variants of the correct query plan.
			 */
			foreach(lc, root->join_info_list)
			{
				SpecialJoinInfo *info = (SpecialJoinInfo *) lfirst(lc);

				if ((bms_is_member(k, info->syn_lefthand) ^
					 bms_is_member(r, info->syn_lefthand)) ||
					(bms_is_member(k, info->syn_righthand) ^
					 bms_is_member(r, info->syn_righthand)))
				{
					jinfo_check = false;
					break;
				}
			}
			if (!jinfo_check)
				continue;

			/*
			 * Check Row Marks equivalence. We can't remove the join if the
			 * relations have row marks of different strength (e.g., one is
			 * locked FOR UPDATE, and another just has ROW_MARK_REFERENCE for
			 * EvalPlanQual rechecking).
			 */
			foreach(lc, root->rowMarks)
			{
				PlanRowMark *rowMark = (PlanRowMark *) lfirst(lc);

				if (rowMark->rti == r)
				{
					Assert(rmark == NULL);
					rmark = rowMark;
				}
				else if (rowMark->rti == k)
				{
					Assert(kmark == NULL);
					kmark = rowMark;
				}

				if (kmark && rmark)
					break;
			}
			if (kmark && rmark && kmark->markType != rmark->markType)
				continue;

			/*
			 * We only deal with base rels here, so their relids bitset
			 * contains only one member -- their relid.
			 */
			joinrelids = bms_add_member(joinrelids, r);
			joinrelids = bms_add_member(joinrelids, k);

			/*
			 * PHVs should not impose any constraints on removing self-joins.
			 */

			/*
			 * At this stage, joininfo lists of inner and outer can contain
			 * only clauses required for a superior outer join that can't
			 * influence this optimization. So, we can avoid to call the
			 * build_joinrel_restrictlist() routine.
			 */
			restrictlist = generate_join_implied_equalities(root, joinrelids,
															rrel->relids,
															krel, NULL);
			if (restrictlist == NIL)
				continue;

			/*
			 * Process restrictlist to separate the self-join quals from the
			 * other quals. e.g., "x = x" goes to selfjoinquals and "a = b" to
			 * otherjoinquals.
			 */
			split_selfjoin_quals(root, restrictlist, &selfjoinquals,
								 &otherjoinquals, rrel->relid, krel->relid);

			Assert(list_length(restrictlist) ==
				   (list_length(selfjoinquals) + list_length(otherjoinquals)));

			/*
			 * To enable SJE for the only degenerate case without any self
			 * join clauses at all, add baserestrictinfo to this list. The
			 * degenerate case works only if both sides have the same clause.
			 * So doesn't matter which side to add.
			 */
			selfjoinquals = list_concat(selfjoinquals, krel->baserestrictinfo);

			/*
			 * Determine if the rrel can duplicate outer rows. We must bypass
			 * the unique rel cache here since we're possibly using a subset
			 * of join quals. We can use 'force_cache' == true when all join
			 * quals are self-join quals.  Otherwise, we could end up putting
			 * false negatives in the cache.
			 */
			if (!innerrel_is_unique_ext(root, joinrelids, rrel->relids,
										krel, JOIN_INNER, selfjoinquals,
										list_length(otherjoinquals) == 0,
										&uclauses))
				continue;

			/*
			 * 'uclauses' is the copy of outer->baserestrictinfo that are
			 * associated with an index.  We proved by matching selfjoinquals
			 * to a unique index that the outer relation has at most one
			 * matching row for each inner row.  Sometimes that is not enough.
			 * e.g. "WHERE s1.b = s2.b AND s1.a = 1 AND s2.a = 2" when the
			 * unique index is (a,b).  Having non-empty uclauses, we must
			 * validate that the inner baserestrictinfo contains the same
			 * expressions, or we won't match the same row on each side of the
			 * join.
			 */
			if (!match_unique_clauses(root, rrel, uclauses, krel->relid))
				continue;

			/*
			 * Remove rrel RelOptInfo from the planner structures and the
			 * corresponding row mark.
			 */
			remove_self_join_rel(root, kmark, rmark, krel, rrel, restrictlist);

			result = bms_add_member(result, r);

			/* We have removed the outer relation, try the next one. */
			break;
		}
	}

	return result;
}

/*
 * Gather indexes of base relations from the joinlist and try to eliminate self
 * joins.
 */
/*
 * remove_self_joins_recurse - (中文)遍历连接树收集基础关系并按 OID 分组尝试消除自连接
 *
 * 【作用】递归遍历 joinlist,收集其中的基础关系(RTE_RELATION)索引,按 OID
 * 排序分组后,对每组同 OID 的关系反复调用 remove_self_joins_one_group() 消除
 * 自连接,并汇总被移除的 relid 到 toRemove。由 remove_useless_self_joins()
 * 调用。
 *
 * 【设计思想】
 * - 递归收集:RangeTblRef 叶子若满足"普通关系、relkind 是 RELKIND_RELATION、
 *   无 TABLESAMPLE、不是结果关系(resultRelation / mergeTargetRelation,受
 *   UPDATE/DELETE 的 EPQ 机制限制不可删)"则加入 relids;子列表递归处理;
 * - 为避免两两比较的二次方复杂度,把候选按 reloid 排序(self_join_candidates_cmp)
 *   再线性扫描聚组;每组至少 2 个成员才尝试消除;
 * - 对同一组用 do-while 反复尝试:删除一个关系后子句与等价类发生变化,可能
 *   让该组出现新的可删候选,直到一次调用没有删除任何关系、或组内只剩单
 *   个成员为止;
 * - 已处理完的组从 relids 中删除,保证外层迭代规模递减。
 *
 * 【参数】
 *   root     —— PlannerInfo(经 simple_rte_array 访问 RangeTblEntry);
 *   joinlist —— 待处理的连接树列表;
 *   toRemove —— 累计被移除关系的 relid 集合(递归累积)。
 * 【返回值】合并后的 toRemove 集合。
 */
static Relids
remove_self_joins_recurse(PlannerInfo *root, List *joinlist, Relids toRemove)
{
	ListCell   *jl;
	Relids		relids = NULL;
	SelfJoinCandidate *candidates = NULL;
	int			i;
	int			j;
	int			numRels;

	/* Collect indexes of base relations of the join tree */
	foreach(jl, joinlist)
	{
		Node	   *jlnode = (Node *) lfirst(jl);

		if (IsA(jlnode, RangeTblRef))
		{
			int			varno = ((RangeTblRef *) jlnode)->rtindex;
			RangeTblEntry *rte = root->simple_rte_array[varno];

			/*
			 * We only consider ordinary relations as candidates to be
			 * removed, and these relations should not have TABLESAMPLE
			 * clauses specified.  Removing a relation with TABLESAMPLE clause
			 * could potentially change the syntax of the query. Because of
			 * UPDATE/DELETE EPQ mechanism, currently Query->resultRelation or
			 * Query->mergeTargetRelation associated rel cannot be eliminated.
			 */
			if (rte->rtekind == RTE_RELATION &&
				rte->relkind == RELKIND_RELATION &&
				rte->tablesample == NULL &&
				varno != root->parse->resultRelation &&
				varno != root->parse->mergeTargetRelation)
			{
				Assert(!bms_is_member(varno, relids));
				relids = bms_add_member(relids, varno);
			}
		}
		else if (IsA(jlnode, List))
		{
			/* Recursively go inside the sub-joinlist */
			toRemove = remove_self_joins_recurse(root, (List *) jlnode,
												 toRemove);
		}
		else
			elog(ERROR, "unrecognized joinlist node type: %d",
				 (int) nodeTag(jlnode));
	}

	numRels = bms_num_members(relids);

	/* Need at least two relations for the join */
	if (numRels < 2)
		return toRemove;

	/*
	 * In order to find relations with the same oid we first build an array of
	 * candidates and then sort it by oid.
	 */
	candidates = palloc_array(SelfJoinCandidate, numRels);
	i = -1;
	j = 0;
	while ((i = bms_next_member(relids, i)) >= 0)
	{
		candidates[j].relid = i;
		candidates[j].reloid = root->simple_rte_array[i]->relid;
		j++;
	}

	qsort(candidates, numRels, sizeof(SelfJoinCandidate),
		  self_join_candidates_cmp);

	/*
	 * Iteratively form a group of relation indexes with the same oid and
	 * launch the routine that detects self-joins in this group and removes
	 * excessive range table entries.
	 *
	 * At the end of the iteration, exclude the group from the overall relids
	 * list. So each next iteration of the cycle will involve less and less
	 * value of relids.
	 */
	i = 0;
	for (j = 1; j < numRels + 1; j++)
	{
		if (j == numRels || candidates[j].reloid != candidates[i].reloid)
		{
			if (j - i >= 2)
			{
				/* Create a group of relation indexes with the same oid */
				Relids		group = NULL;
				Relids		removed;

				while (i < j)
				{
					group = bms_add_member(group, candidates[i].relid);
					i++;
				}
				relids = bms_del_members(relids, group);

				/*
				 * Try to remove self-joins from a group of identical entries.
				 * Make the next attempt iteratively - if something is deleted
				 * from a group, changes in clauses and equivalence classes
				 * can give us a chance to find more candidates.
				 */
				do
				{
					Assert(!bms_overlap(group, toRemove));
					removed = remove_self_joins_one_group(root, group);
					toRemove = bms_add_members(toRemove, removed);
					group = bms_del_members(group, removed);
				} while (!bms_is_empty(removed) &&
						 bms_membership(group) == BMS_MULTIPLE);
				bms_free(removed);
				bms_free(group);
			}
			else
			{
				/* Single relation, just remove it from the set */
				relids = bms_del_member(relids, candidates[i].relid);
				i = j;
			}
		}
	}

	Assert(bms_is_empty(relids));

	return toRemove;
}

/*
 * Compare self-join candidates by their oids.
 */
/*
 * self_join_candidates_cmp - (中文)自连接候选按 OID 排序的比较函数
 *
 * 【作用】qsort() 的比较回调:按 SelfJoinCandidate 的 reloid(对应关系的 OID)
 * 排序,使同 OID 的候选相邻。由 remove_self_joins_recurse() 调用。
 *
 * 【设计思想】排序的目的见 remove_self_joins_recurse:把同 OID 关系聚在一起,
 * 便于线性扫描分组,避免 O(N^2) 的两两比较。同一 OID 内相对顺序无关紧要,
 * 故相等时返回 0。
 *
 * 【参数】
 *   a —— 左侧比较元素;
 *   b —— 右侧比较元素。
 * 【返回值】ca->reloid < cb->reloid 返回 -1;大于返回 1;相等返回 0。
 */
static int
self_join_candidates_cmp(const void *a, const void *b)
{
	const SelfJoinCandidate *ca = (const SelfJoinCandidate *) a;
	const SelfJoinCandidate *cb = (const SelfJoinCandidate *) b;

	if (ca->reloid != cb->reloid)
		return (ca->reloid < cb->reloid ? -1 : 1);
	else
		return 0;
}

/*
 * Find and remove useless self joins.
 *
 * Search for joins where a relation is joined to itself. If the join clause
 * for each tuple from one side of the join is proven to match the same
 * physical row (or nothing) on the other side, that self-join can be
 * eliminated from the query.  Suitable join clauses are assumed to be in the
 * form of X = X, and can be replaced with NOT NULL clauses.
 *
 * For the sake of simplicity, we don't apply this optimization to special
 * joins. Here is a list of what we could do in some particular cases:
 * 'a a1 semi join a a2': is reduced to inner by reduce_unique_semijoins,
 * and then removed normally.
 * 'a a1 anti join a a2': could simplify to a scan with 'outer quals AND
 * (IS NULL on join columns OR NOT inner quals)'.
 * 'a a1 left join a a2': could simplify to a scan like inner but without
 * NOT NULL conditions on join columns.
 * 'a a1 left join (a a2 join b)': can't simplify this, because join to b
 * can both remove rows and introduce duplicates.
 *
 * To search for removable joins, we order all the relations on their Oid,
 * go over each set with the same Oid, and consider each pair of relations
 * in this set.
 *
 * To remove the join, we mark one of the participating relations as dead
 * and rewrite all references to it to point to the remaining relation.
 * This includes modifying RestrictInfos, EquivalenceClasses, and
 * EquivalenceMembers. We also have to modify the row marks. The join clauses
 * of the removed relation become either restriction or join clauses, based on
 * whether they reference any relations not participating in the removed join.
 *
 * 'joinlist' is the top-level joinlist of the query. If it has any
 * references to the removed relations, we update them to point to the
 * remaining ones.
 */
/*
 * remove_useless_self_joins - (中文)查找并移除无用的自连接
 *
 * 【作用】查找"关系与自身连接"的无用场景:若连接子句能证明每侧一行要么匹
 * 配同一物理行、要么都不匹配,则该自连接可从查询中删除。删除时把参与关系
 * 之一标记为"死关系",并把所有对它的引用改写为指向保留关系(包括
 * RestrictInfo、等价类、等价类成员、行标记等)。入口由 query_planner() 调用。
 *
 * 【设计思想】
 * - 适用形态:合适的连接子句形如 X = X,可替换为 NOT NULL 检查;为简单起见
 *   不对特殊连接应用本优化(半连接先被 reduce_unique_semijoins 降级为内连接
 *   再正常处理;反连接/左连接/带第三方关系的组合各有简化可能性但未实现);
 * - 搜索策略:按关系 OID 排序,对每组同 OID 的关系两两检查(见
 *   remove_self_joins_recurse / remove_self_joins_one_group);
 * - 被删关系的连接子句根据是否引用连接外关系,变成保留关系的限制子句或
 *   连接子句;
 * - 开头的快速放弃条件:未启用 enable_self_join_elimination、连接树为空、
 *   或只有单个 RangeTblRef(不存在连接)时直接原样返回;
 * - 末尾清理:对每个被移除的 relid,从 joinlist 中删除恰好一个 RangeTblRef
 *   引用(必须是 1 个,否则报错)。
 *
 * 【参数】
 *   root     —— PlannerInfo;
 *   joinlist —— 查询的顶层 joinlist;若含被删关系的引用会被改写。
 * 【返回值】更新后的 joinlist。
 */
List *
remove_useless_self_joins(PlannerInfo *root, List *joinlist)
{
	Relids		toRemove = NULL;
	int			relid = -1;

	if (!enable_self_join_elimination || joinlist == NIL ||
		(list_length(joinlist) == 1 && !IsA(linitial(joinlist), List)))
		return joinlist;

	/*
	 * Merge pairs of relations participated in self-join. Remove unnecessary
	 * range table entries.
	 */
	toRemove = remove_self_joins_recurse(root, joinlist, toRemove);

	if (unlikely(toRemove != NULL))
	{
		/* At the end, remove orphaned relation links */
		while ((relid = bms_next_member(toRemove, relid)) >= 0)
		{
			int			nremoved = 0;

			joinlist = remove_rel_from_joinlist(joinlist, relid, &nremoved);
			if (nremoved != 1)
				elog(ERROR, "failed to find relation %d in joinlist", relid);
		}
	}

	return joinlist;
}
