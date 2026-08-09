/*-------------------------------------------------------------------------
 *
 * pathkeys.c
 *	  Utilities for matching and building path keys
 *
 * See src/backend/optimizer/README for a great deal of information about
 * the nature and use of path keys.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本模块(pathkeys.c)负责路径键(PathKey)的构造、比较与匹配。路径键描述
 * 一个路径(Path)输出的元组排序顺序,是规划器决定"哪些路径值得保留"的
 * 重要依据:它服务于排序(Sort/增量排序)、归并连接(Merge Join,要求两侧
 * 都按归并键有序)、以及索引扫描顺序与查询 ORDER BY/GROUP BY/DISTINCT 的
 * 匹配。
 *
 * 【职责】
 * - 构造:由等价类(EquivalenceClass)加算符族/比较方向构造规范路径键
 *   (make_canonical_pathkey),并识别冗余键(pathkey_is_redundant);
 * - 比较:compare_pathkeys() 按"规范键指针相等"比较两个键列表,
 *   pathkeys_contained_in() / pathkeys_count_contained_in() 判断子集关系
 *   与公共前缀长度,并据此提供 get_cheapest_path_for_pathkeys() 等查找
 *   最便宜已排序路径的接口;
 * - 新路径键生成:build_index_pathkeys()(索引扫描排序)、
 *   build_partition_pathkeys()(分区扫描排序)、build_expression_pathkey()
 *   (单表达式排序)、convert_subquery_pathkeys()(子查询排序向外部转换);
 * - 归并连接配套:initialize_mergeclause_eclasses() /
 *   update_mergeclause_eclasses() 维护归并子句两侧的等价类缓存;
 *   find_mergeclauses_for_outer_pathkeys() / select_outer_pathkeys_for_merge()
 *   / make_inner_pathkeys_for_merge() / trim_mergeclauses_for_inner_pathkeys()
 *   负责归并子句与排序键的相互换算;
 * - 有用性判定:truncate_useless_pathkeys() 只保留对高层合并或最终输出
 *   有用的键,避免 add_path() 认为两个路径"排序不同"其实毫无差别;
 * - 额外支持:GROUP BY 键按输入排序重排(get_useful_group_keys_orderings /
 *   group_keys_reorder_by_pathkeys,为增量排序服务)。
 *
 * 【设计思想】
 * - 规范唯一性:每个等价类经过合并后,同一条目全查询唯一,因此规范路径键
 *   可以用指针相等直接比较(O(1)),键列表比较退化为前缀逐元素比较;
 * - 冗余消除:某键的等价类含常量(绑定单一值)或与列表前项同一等价类时
 *   (如 ORDER BY x, x)即冗余,不应保留;
 * - "有用性"启发式:排序方向采用 right_merge_direction() 在 ASC/DESC 间
 *   选择其一,避免归并路径数量翻倍;排序需求则按 sort/window/setop/group/
 *   distinct/merge 六类逐一匹配,取最长有用前缀。
 *
 * 【核心数据结构】PathKey:由 pk_eclass(等价类)、pk_opfamily(排序算符族)、
 * pk_cmptype(COMPARE_LT/COMPARE_GT 表示升/降序)与 pk_nulls_first
 * (NULL 排序位置)四元组唯一确定。
 *
 * 本文件与 equivclass.c(等价类构造)、joinpath.c(归并连接使用本模块换算
 * 排序)、pathnode.c(路径排序字段)以及 cost(排序代价)紧密配合。详细设计
 * 见 src/backend/optimizer/README。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/path/pathkeys.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/stratnum.h"
#include "catalog/pg_opfamily.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "partitioning/partbounds.h"
#include "rewrite/rewriteManip.h"
#include "utils/lsyscache.h"

/* Consider reordering of GROUP BY keys? */
bool		enable_group_by_reordering = true;

static bool pathkey_is_redundant(PathKey *new_pathkey, List *pathkeys);
static bool matches_boolean_partition_clause(RestrictInfo *rinfo,
											 RelOptInfo *partrel,
											 int partkeycol);
static Var *find_var_for_subquery_tle(RelOptInfo *rel, TargetEntry *tle);
static bool right_merge_direction(PlannerInfo *root, PathKey *pathkey);


/****************************************************************************
 *		PATHKEY CONSTRUCTION AND REDUNDANCY TESTING
 ****************************************************************************/

/*
 * make_canonical_pathkey
 *	  Given the parameters for a PathKey, find any pre-existing matching
 *	  pathkey in the query's list of "canonical" pathkeys.  Make a new
 *	  entry if there's not one already.
 *
 * Note that this function must not be used until after we have completed
 * merging EquivalenceClasses.
 */
/*
 * make_canonical_pathkey - (中文)按给定参数查找或创建规范路径键
 *
 * 【作用】各处构造排序键时调用本函数:在 root->canon_pathkeys 中查找与
 * (eclass, opfamily, cmptype, nulls_first) 四元组完全一致的既有规范路径键,
 * 有则复用,无则新建并追加。等价类必须已完成合并,否则报错。
 *
 * 【设计思想】规范路径键的"唯一性"是 pathkeys 快速比较的基石:同一 EC
 * 全查询只有一份,因此后续可直接用指针相等判断键相等。eclass 参数可能是
 * 已被合并的非顶层等价类,先沿 ec_merged 链上溯到顶层;新建键时切换到
 * 主规划上下文(root->planner_cxt)分配,保证 GEQO 场景下跨代存活。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   eclass      —— 该键所属的等价类(可能非规范,会被上溯);
 *   opfamily    —— 排序用算符族 OID;
 *   cmptype     —— COMPARE_LT(升序)或 COMPARE_GT(降序);
 *   nulls_first —— NULL 是否排在最前。
 * 【返回值】规范 PathKey 指针(既有或新建)。
 */
PathKey *
make_canonical_pathkey(PlannerInfo *root,
					   EquivalenceClass *eclass, Oid opfamily,
					   CompareType cmptype, bool nulls_first)
{
	PathKey    *pk;
	ListCell   *lc;
	MemoryContext oldcontext;

	/* Can't make canonical pathkeys if the set of ECs might still change */
	if (!root->ec_merging_done)
		elog(ERROR, "too soon to build canonical pathkeys");

	/* The passed eclass might be non-canonical, so chase up to the top */
	while (eclass->ec_merged)
		eclass = eclass->ec_merged;

	foreach(lc, root->canon_pathkeys)
	{
		pk = (PathKey *) lfirst(lc);
		if (eclass == pk->pk_eclass &&
			opfamily == pk->pk_opfamily &&
			cmptype == pk->pk_cmptype &&
			nulls_first == pk->pk_nulls_first)
			return pk;
	}

	/*
	 * Be sure canonical pathkeys are allocated in the main planning context.
	 * Not an issue in normal planning, but it is for GEQO.
	 */
	oldcontext = MemoryContextSwitchTo(root->planner_cxt);

	pk = makeNode(PathKey);
	pk->pk_eclass = eclass;
	pk->pk_opfamily = opfamily;
	pk->pk_cmptype = cmptype;
	pk->pk_nulls_first = nulls_first;

	root->canon_pathkeys = lappend(root->canon_pathkeys, pk);

	MemoryContextSwitchTo(oldcontext);

	return pk;
}

/*
 * append_pathkeys
 *		Append all non-redundant PathKeys in 'source' onto 'target' and
 *		returns the updated 'target' list.
 */
/*
 * append_pathkeys - (中文)把 source 中所有不冗余的路径键追加到 target 并
 * 返回更新后的列表
 *
 * 【作用】需要合并两个排序键列表时(如把索引已满足的部分与仍需排序的部分
 * 拼接)调用本函数。逐个检查 source 中的键,若与 target 已有内容不冗余则
 * 追加。
 *
 * 【设计思想】依赖 pathkey_is_redundant() 判定:等价类含常量或与 target
 * 中既有键同等价类者跳过。要求 target 非空(有断言),因为通常调用方已
 * 有基础的排序键。
 *
 * 【参数】
 *   target —— 目标键列表(非空,会被就地追加);
 *   source —— 待追加的键列表。
 * 【返回值】更新后的 target 列表(可能返回新列表头)。
 */
List *
append_pathkeys(List *target, List *source)
{
	ListCell   *lc;

	Assert(target != NIL);

	foreach(lc, source)
	{
		PathKey    *pk = lfirst_node(PathKey, lc);

		if (!pathkey_is_redundant(pk, target))
			target = lappend(target, pk);
	}
	return target;
}

/*
 * pathkey_is_redundant
 *	   Is a pathkey redundant with one already in the given list?
 *
 * We detect two cases:
 *
 * 1. If the new pathkey's equivalence class contains a constant, and isn't
 * below an outer join, then we can disregard it as a sort key.  An example:
 *			SELECT ... WHERE x = 42 ORDER BY x, y;
 * We may as well just sort by y.  Note that because of opfamily matching,
 * this is semantically correct: we know that the equality constraint is one
 * that actually binds the variable to a single value in the terms of any
 * ordering operator that might go with the eclass.  This rule not only lets
 * us simplify (or even skip) explicit sorts, but also allows matching index
 * sort orders to a query when there are don't-care index columns.
 *
 * 2. If the new pathkey's equivalence class is the same as that of any
 * existing member of the pathkey list, then it is redundant.  Some examples:
 *			SELECT ... ORDER BY x, x;
 *			SELECT ... ORDER BY x, x DESC;
 *			SELECT ... WHERE x = y ORDER BY x, y;
 * In all these cases the second sort key cannot distinguish values that are
 * considered equal by the first, and so there's no point in using it.
 * Note in particular that we need not compare opfamily (all the opfamilies
 * of the EC have the same notion of equality) nor sort direction.
 *
 * Both the given pathkey and the list members must be canonical for this
 * to work properly, but that's okay since we no longer ever construct any
 * non-canonical pathkeys.  (Note: the notion of a pathkey *list* being
 * canonical includes the additional requirement of no redundant entries,
 * which is exactly what we are checking for here.)
 *
 * Because the equivclass.c machinery forms only one copy of any EC per query,
 * pointer comparison is enough to decide whether canonical ECs are the same.
 */
/*
 * pathkey_is_redundant - (中文)判断一个新路径键与列表中既有键是否冗余
 *
 * 【作用】构造/合并路径键列表时,用来剔除"不增加任何区分能力"的排序键,
 * 保证列表保持规范(无冗余项)。
 *
 * 【设计思想】两种冗余情形:
 * 1. 新键的等价类含常量(EC_MUST_BE_REDUNDANT)且不在外层连接之下:该列被
 *   等值约束绑定为单值,按任何排序算符看都只有一种取值,故完全可忽略
 *   (如 WHERE x=42 ORDER BY x, y 只按 y 排序即可;该规则还能让索引排序与
 *    查询匹配时容忍 don't-care 索引列);
 * 2. 新键与列表中某键属于同一等价类:第二个排序键无法区分第一个键认为
 *   相等的值(如 ORDER BY x, x 或 WHERE x=y ORDER BY x, y),无需比较算符族
 *   (同一 EC 的所有算符族对"相等"的看法一致)或排序方向。
 * 因为等价类全查询唯一,等价类判定用指针相等即可。新键与列表成员都必须是
 * 规范键(现在代码已不再构造非规范键)。
 *
 * 【参数】
 *   new_pathkey —— 待检查的新键;
 *   pathkeys    —— 既有键列表。
 * 【返回值】true:冗余,应丢弃;false:保留。
 */
static bool
pathkey_is_redundant(PathKey *new_pathkey, List *pathkeys)
{
	EquivalenceClass *new_ec = new_pathkey->pk_eclass;
	ListCell   *lc;

	/* Check for EC containing a constant --- unconditionally redundant */
	if (EC_MUST_BE_REDUNDANT(new_ec))
		return true;

	/* If same EC already used in list, then redundant */
	foreach(lc, pathkeys)
	{
		PathKey    *old_pathkey = (PathKey *) lfirst(lc);

		if (new_ec == old_pathkey->pk_eclass)
			return true;
	}

	return false;
}

/*
 * make_pathkey_from_sortinfo
 *	  Given an expression and sort-order information, create a PathKey.
 *	  The result is always a "canonical" PathKey, but it might be redundant.
 *
 * If the PathKey is being generated from a SortGroupClause, sortref should be
 * the SortGroupClause's SortGroupRef; otherwise zero.
 *
 * If rel is not NULL, it identifies a specific relation we're considering
 * a path for, and indicates that child EC members for that relation can be
 * considered.  Otherwise child members are ignored.  (See the comments for
 * get_eclass_for_sort_expr.)
 *
 * create_it is true if we should create any missing EquivalenceClass
 * needed to represent the sort key.  If it's false, we return NULL if the
 * sort key isn't already present in any EquivalenceClass.
 */
/*
 * make_pathkey_from_sortinfo - (中文)由表达式与排序信息构造路径键
 *
 * 【作用】各类"已知排序算符/算符族"的路径键构造器(如
 * make_pathkey_from_sortop、build_index_pathkeys、build_partition_pathkeys、
 * build_expression_pathkey)的核心底层:给定表达式与排序细节,找到(必要时
 * 创建)等价类,再调用 make_canonical_pathkey() 返回规范路径键。结果可能
 * 是冗余键(由调用方决定是否剔除)。
 *
 * 【设计思想】
 * - reverse_sort 决定 cmptype(COMPARE_GT=降序 / COMPARE_LT=升序);
 * - 等价类需要"归并等值算子所属的全部算符族"作为成员依据,因此先从排序
 *   算符族中取等值算子(get_opfamily_member_for_cmptype),再用
 *   get_mergejoin_opfamilies() 求其所属全部算符族;
 * - 用 get_eclass_for_sort_expr() 查找/创建等价类:create_it 为 false 时
 *   表达式不在任何 EC 中就返回 NULL(表示该排序对查询不相关);rel 非空时
 *   允许该关系的子 EC 成员参与匹配(分区/子表相关);
 * - 最后 make_canonical_pathkey() 完成规范键的查建。
 *
 * 【参数】
 *   root         —— PlannerInfo;
 *   expr         —— 待排序的表达式;
 *   opfamily     —— 排序算符族;
 *   opcintype    —— 排序输入类型;
 *   collation    —— 排序规则;
 *   reverse_sort —— true 表示降序;
 *   nulls_first  —— true 表示 NULL 排最前;
 *   sortref      —— 来自 SortGroupClause 时为其 SortGroupRef,否则 0;
 *   rel          —— 非空时只考虑该关系相关的 EC 成员,否则忽略子成员;
 *   create_it    —— true:允许创建缺失的 EC;false:缺失即返回 NULL。
 * 【返回值】规范路径键;create_it 为 false 且无匹配 EC 时返回 NULL。
 */
static PathKey *
make_pathkey_from_sortinfo(PlannerInfo *root,
						   Expr *expr,
						   Oid opfamily,
						   Oid opcintype,
						   Oid collation,
						   bool reverse_sort,
						   bool nulls_first,
						   Index sortref,
						   Relids rel,
						   bool create_it)
{
	CompareType cmptype;
	Oid			equality_op;
	List	   *opfamilies;
	EquivalenceClass *eclass;

	cmptype = reverse_sort ? COMPARE_GT : COMPARE_LT;

	/*
	 * EquivalenceClasses need to contain opfamily lists based on the family
	 * membership of mergejoinable equality operators, which could belong to
	 * more than one opfamily.  So we have to look up the opfamily's equality
	 * operator and get its membership.
	 */
	equality_op = get_opfamily_member_for_cmptype(opfamily,
												  opcintype,
												  opcintype,
												  COMPARE_EQ);
	if (!OidIsValid(equality_op))	/* shouldn't happen */
		elog(ERROR, "missing operator %d(%u,%u) in opfamily %u",
			 COMPARE_EQ, opcintype, opcintype, opfamily);
	opfamilies = get_mergejoin_opfamilies(equality_op);
	if (!opfamilies)			/* certainly should find some */
		elog(ERROR, "could not find opfamilies for equality operator %u",
			 equality_op);

	/* Now find or (optionally) create a matching EquivalenceClass */
	eclass = get_eclass_for_sort_expr(root, expr,
									  opfamilies, opcintype, collation,
									  sortref, rel, create_it);

	/* Fail if no EC and !create_it */
	if (!eclass)
		return NULL;

	/* And finally we can find or create a PathKey node */
	return make_canonical_pathkey(root, eclass, opfamily,
								  cmptype, nulls_first);
}

/*
 * make_pathkey_from_sortop
 *	  Like make_pathkey_from_sortinfo, but work from a sort operator.
 *
 * This should eventually go away, but we need to restructure SortGroupClause
 * first.
 */
/*
 * make_pathkey_from_sortop - (中文)由排序运算符构造路径键
 *
 * 【作用】make_pathkeys_for_sortclauses_extended() 逐个处理 SortGroupClause
 * 时调用本函数:给定排序运算符 ordering_op,反查出其算符族、输入类型与比较
 * 方向,再转交 make_pathkey_from_sortinfo() 完成路径键构造。
 *
 * 【设计思想】SortGroupClause 不携带排序规则,因此排序规则需从表达式本身
 * 推导(exprCollation);反向信息通过 get_ordering_op_properties() 从
 * pg_amop 获取。源码注明:此函数是过渡性接口,待 SortGroupClause 重构后
 * 应移除。rel 传 NULL(不针对特定关系)。
 *
 * 【参数】
 *   root         —— PlannerInfo;
 *   expr         —— 待排序表达式;
 *   ordering_op  —— 排序运算符 OID;
 *   reverse_sort —— true 表示降序;
 *   nulls_first  —— true 表示 NULL 排最前;
 *   sortref      —— SortGroupClause 的 SortGroupRef;
 *   create_it    —— true:允许创建缺失的 EC。
 * 【返回值】规范路径键;create_it 为 false 且无匹配 EC 时返回 NULL。
 */
static PathKey *
make_pathkey_from_sortop(PlannerInfo *root,
						 Expr *expr,
						 Oid ordering_op,
						 bool reverse_sort,
						 bool nulls_first,
						 Index sortref,
						 bool create_it)
{
	Oid			opfamily,
				opcintype,
				collation;
	CompareType cmptype;

	/* Find the operator in pg_amop --- failure shouldn't happen */
	if (!get_ordering_op_properties(ordering_op,
									&opfamily, &opcintype, &cmptype))
		elog(ERROR, "operator %u is not a valid ordering operator",
			 ordering_op);

	/* Because SortGroupClause doesn't carry collation, consult the expr */
	collation = exprCollation((Node *) expr);

	return make_pathkey_from_sortinfo(root,
									  expr,
									  opfamily,
									  opcintype,
									  collation,
									  reverse_sort,
									  nulls_first,
									  sortref,
									  NULL,
									  create_it);
}


/****************************************************************************
 *		PATHKEY COMPARISONS
 ****************************************************************************/

/*
 * compare_pathkeys
 *	  Compare two pathkeys to see if they are equivalent, and if not whether
 *	  one is "better" than the other.
 *
 *	  We assume the pathkeys are canonical, and so they can be checked for
 *	  equality by simple pointer comparison.
 */
/*
 * compare_pathkeys - (中文)比较两个路径键列表,判断等价或优劣
 *
 * 【作用】规划器判定"某路径的排序是否满足某种需求"时的核心比较工具,被
 * pathkeys_contained_in() 等大量函数复用。
 *
 * 【设计思想】假设两个列表都是规范键列表,则键相等等价于指针相等:
 * - 同一列表(含两个都为空)直接返回 PATHKEYS_EQUAL;
 * - 逐位比较,任一位置指针不同即返回 PATHKEYS_DIFFERENT(后面无需再看);
 * - 若一方先遍历完:较短者是较长者的前缀,较长者排序"更好"
 *   (PATHKEYS_BETTER1 表示 keys1 更长更精细)。
 * 返回类型 PathKeysComparison 语义:BETTER1 = keys1 排序更严格(多出若干
 * 键),BETTER2 = keys2 更严格,EQUAL = 完全一致,DIFFERENT = 互不满足。
 *
 * 【参数】
 *   keys1 —— 第一个键列表;
 *   keys2 —— 第二个键列表。
 * 【返回值】PATHKEYS_EQUAL / PATHKEYS_BETTER1 / PATHKEYS_BETTER2 /
 * PATHKEYS_DIFFERENT。
 */
PathKeysComparison
compare_pathkeys(List *keys1, List *keys2)
{
	ListCell   *key1,
			   *key2;

	/*
	 * Fall out quickly if we are passed two identical lists.  This mostly
	 * catches the case where both are NIL, but that's common enough to
	 * warrant the test.
	 */
	if (keys1 == keys2)
		return PATHKEYS_EQUAL;

	forboth(key1, keys1, key2, keys2)
	{
		PathKey    *pathkey1 = (PathKey *) lfirst(key1);
		PathKey    *pathkey2 = (PathKey *) lfirst(key2);

		if (pathkey1 != pathkey2)
			return PATHKEYS_DIFFERENT;	/* no need to keep looking */
	}

	/*
	 * If we reached the end of only one list, the other is longer and
	 * therefore not a subset.
	 */
	if (key1 != NULL)
		return PATHKEYS_BETTER1;	/* key1 is longer */
	if (key2 != NULL)
		return PATHKEYS_BETTER2;	/* key2 is longer */
	return PATHKEYS_EQUAL;
}

/*
 * pathkeys_contained_in
 *	  Common special case of compare_pathkeys: we just want to know
 *	  if keys2 are at least as well sorted as keys1.
 */
/*
 * pathkeys_contained_in - (中文)判断 keys2 的排序是否至少与 keys1 一样好
 * (即 keys1 是否被 keys2 包含)
 *
 * 【作用】最常用的路径键子集判断:例如"该路径的排序是否满足所需的排序键"
 * (get_cheapest_path_for_pathkeys)、"归并键是否已由某路径排序覆盖"
 * (try_mergejoin_path 判断可省略显式排序)等。
 *
 * 【设计思想】直接复用 compare_pathkeys():keys2 与 keys1 相等或比 keys1
 * 更严格(前缀一致且 keys2 更长)即为满足。也就是说 keys1 必须是 keys2 的
 * 前缀(按指针比较),允许 keys2 比 keys1 多出额外排序键。
 *
 * 【参数】
 *   keys1 —— 被包含方(需求侧);
 *   keys2 —— 包含方(路径的实际排序)。
 * 【返回值】true:keys2 的排序覆盖 keys1;false:否则。
 */
bool
pathkeys_contained_in(List *keys1, List *keys2)
{
	switch (compare_pathkeys(keys1, keys2))
	{
		case PATHKEYS_EQUAL:
		case PATHKEYS_BETTER2:
			return true;
		default:
			break;
	}
	return false;
}

/*
 * group_keys_reorder_by_pathkeys
 *		Reorder GROUP BY pathkeys and clauses to match the input pathkeys.
 *
 * 'pathkeys' is an input list of pathkeys
 * '*group_pathkeys' and '*group_clauses' are pathkeys and clauses lists to
 *		reorder.  The pointers are redirected to new lists, original lists
 *		stay untouched.
 * 'num_groupby_pathkeys' is the number of first '*group_pathkeys' items to
 *		search matching pathkeys.
 *
 * Returns the number of GROUP BY keys with a matching pathkey.
 */
/*
 * group_keys_reorder_by_pathkeys - (中文)按输入路径的排序重排 GROUP BY
 * 路径键与子句,返回成功匹配的键数
 *
 * 【作用】get_useful_group_keys_orderings() 的辅助函数:把 (group_pathkeys,
 * group_clauses) 按 pathkeys(输入路径的实际排序)重新排列——凡能在路径排序
 * 前缀中找到匹配的 GROUP BY 键,就提前放到新列表前面,为增量排序降低代价。
 *
 * 【设计思想】
 * - 只在前 num_groupby_pathkeys 个 group_pathkeys 中搜索:因为
 *   root->group_pathkeys 同时包含"聚合键"(其 ec_sortref 不指向目标表,
 *   get_sortgroupref_clause_noerr() 会失败),先 list_copy_head 出一份纯
 *   GROUP BY 键的拷贝用于查找;
 * - 逐 pathkey 匹配:一旦遇到第一个在 grouping_pathkeys 中找不到匹配指针
 *   (或 ec_sortref == 0,或 group_clauses 中无对应 SortGroupClause)的键,
 *   说明后续 pathkeys 对分组不再有用,立即停止;
 * - 匹配的键与子句(经 get_sortgroupref_clause_noerr 取回,断言有排序算子)
 *   依次放入新列表;最后把未匹配的剩余键用 list_concat_unique_ptr 接在
 *   后面,保证全部键不丢失;
 * - 返回值 n 供调用方判断是否真正产生了新的排序(以及是否可配合增量排序)。
 *
 * 【参数】
 *   pathkeys          —— 输入路径的排序键列表;
 *   group_pathkeys    —— 入/出参:GROUP BY 路径键列表指针(被重排);
 *   group_clauses     —— 入/出参:分组子句列表指针(与 pathkeys 同步重排);
 *   num_groupby_pathkeys —— group_pathkeys 前多少个是真正的 GROUP BY 键。
 * 【返回值】在 pathkeys 前缀中找到匹配的 GROUP BY 键个数。
 */
static int
group_keys_reorder_by_pathkeys(List *pathkeys, List **group_pathkeys,
							   List **group_clauses,
							   int num_groupby_pathkeys)
{
	List	   *new_group_pathkeys = NIL,
			   *new_group_clauses = NIL;
	List	   *grouping_pathkeys;
	ListCell   *lc;
	int			n;

	if (pathkeys == NIL || *group_pathkeys == NIL)
		return 0;

	/*
	 * We're going to search within just the first num_groupby_pathkeys of
	 * *group_pathkeys.  The thing is that root->group_pathkeys is passed as
	 * *group_pathkeys containing grouping pathkeys altogether with aggregate
	 * pathkeys.  If we process aggregate pathkeys we could get an invalid
	 * result of get_sortgroupref_clause_noerr(), because their
	 * pathkey->pk_eclass->ec_sortref doesn't reference query targetlist.  So,
	 * we allocate a separate list of pathkeys for lookups.
	 */
	grouping_pathkeys = list_copy_head(*group_pathkeys, num_groupby_pathkeys);

	/*
	 * Walk the pathkeys (determining ordering of the input path) and see if
	 * there's a matching GROUP BY key. If we find one, we append it to the
	 * list, and do the same for the clauses.
	 *
	 * Once we find the first pathkey without a matching GROUP BY key, the
	 * rest of the pathkeys are useless and can't be used to evaluate the
	 * grouping, so we abort the loop and ignore the remaining pathkeys.
	 */
	foreach(lc, pathkeys)
	{
		PathKey    *pathkey = (PathKey *) lfirst(lc);
		SortGroupClause *sgc;

		/*
		 * Pathkeys are built in a way that allows simply comparing pointers.
		 * Give up if we can't find the matching pointer.  Also give up if
		 * there is no sortclause reference for some reason.
		 */
		if (foreach_current_index(lc) >= num_groupby_pathkeys ||
			!list_member_ptr(grouping_pathkeys, pathkey) ||
			pathkey->pk_eclass->ec_sortref == 0)
			break;

		/*
		 * Since 1349d27 pathkey coming from underlying node can be in the
		 * root->group_pathkeys but not in the processed_groupClause. So, we
		 * should be careful here.
		 */
		sgc = get_sortgroupref_clause_noerr(pathkey->pk_eclass->ec_sortref,
											*group_clauses);
		if (!sgc)
			/* The grouping clause does not cover this pathkey */
			break;

		/*
		 * Sort group clause should have an ordering operator as long as there
		 * is an associated pathkey.
		 */
		Assert(OidIsValid(sgc->sortop));

		new_group_pathkeys = lappend(new_group_pathkeys, pathkey);
		new_group_clauses = lappend(new_group_clauses, sgc);
	}

	/* remember the number of pathkeys with a matching GROUP BY key */
	n = list_length(new_group_pathkeys);

	/* append the remaining group pathkeys (will be treated as not sorted) */
	*group_pathkeys = list_concat_unique_ptr(new_group_pathkeys,
											 *group_pathkeys);
	*group_clauses = list_concat_unique_ptr(new_group_clauses,
											*group_clauses);

	list_free(grouping_pathkeys);
	return n;
}

/*
 * get_useful_group_keys_orderings
 *		Determine which orderings of GROUP BY keys are potentially interesting.
 *
 * Returns a list of GroupByOrdering items, each representing an interesting
 * ordering of GROUP BY keys.  Each item stores pathkeys and clauses in the
 * matching order.
 *
 * The function considers (and keeps) following GROUP BY orderings:
 *
 * - GROUP BY keys as ordered by preprocess_groupclause() to match target
 *   ORDER BY clause (as much as possible),
 * - GROUP BY keys reordered to match 'path' ordering (as much as possible).
 */
/*
 * get_useful_group_keys_orderings - (中文)计算 GROUP BY 键有哪些"可能有用
 * 的排序",返回 GroupByOrdering 列表
 *
 * 【作用】规划器在选择分组路径(GroupAggregate/HashAggregate)前调用本函数,
 * 收集一组合适的 GROUP BY 键排序方案。至少返回原始排序(按查询中的顺序),
 * 若开启 enable_group_by_reordering 且输入路径有一定排序,还会附加"按路径
 * 排序重排后"的方案,供后续以增量排序廉价获得分组有序输入。
 *
 * 【设计思想】
 * - 恒定返回原始方案(查询书写顺序,已尽量贴合 ORDER BY);
 * - 优化开关:enable_group_by_reordering 关闭、有 groupingSets(分组集有
 *   自己更复杂的排序逻辑)时直接返回单方案;
 * - 若 path 有排序且不与原始分组排序相同,用 group_keys_reorder_by_pathkeys()
 *   尝试重排,得到匹配数 n;只有 n > 0 且(允许增量排序或 n 覆盖全部 GROUP
 *   BY 键)且重排结果确实不同时,才追加第二个方案;
 * - assert 构建下逐一校验各方案与原始方案元素相同、子句与键的 sortref
 *   一一对应,保证一致性。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   path —— 正在考虑的路径(其 pathkeys 用于重排尝试)。
 * 【返回值】GroupByOrdering 节点列表(每个含 pathkeys 与 clauses),至少
 * 包含原始顺序。
 */
List *
get_useful_group_keys_orderings(PlannerInfo *root, Path *path)
{
	Query	   *parse = root->parse;
	List	   *infos = NIL;
	GroupByOrdering *info;

	List	   *pathkeys = root->group_pathkeys;
	List	   *clauses = root->processed_groupClause;

	/* always return at least the original pathkeys/clauses */
	info = makeNode(GroupByOrdering);
	info->pathkeys = pathkeys;
	info->clauses = clauses;
	infos = lappend(infos, info);

	/*
	 * Should we try generating alternative orderings of the group keys? If
	 * not, we produce only the order specified in the query, i.e. the
	 * optimization is effectively disabled.
	 */
	if (!enable_group_by_reordering)
		return infos;

	/*
	 * Grouping sets have own and more complex logic to decide the ordering.
	 */
	if (parse->groupingSets)
		return infos;

	/*
	 * If the path is sorted in some way, try reordering the group keys to
	 * match the path as much of the ordering as possible.  Then thanks to
	 * incremental sort we would get this sort as cheap as possible.
	 */
	if (path->pathkeys &&
		!pathkeys_contained_in(path->pathkeys, root->group_pathkeys))
	{
		int			n;

		n = group_keys_reorder_by_pathkeys(path->pathkeys, &pathkeys, &clauses,
										   root->num_groupby_pathkeys);

		if (n > 0 &&
			(enable_incremental_sort || n == root->num_groupby_pathkeys) &&
			compare_pathkeys(pathkeys, root->group_pathkeys) != PATHKEYS_EQUAL)
		{
			info = makeNode(GroupByOrdering);
			info->pathkeys = pathkeys;
			info->clauses = clauses;

			infos = lappend(infos, info);
		}
	}

#ifdef USE_ASSERT_CHECKING
	{
		GroupByOrdering *pinfo = linitial_node(GroupByOrdering, infos);
		ListCell   *lc;

		/* Test consistency of info structures */
		for_each_from(lc, infos, 1)
		{
			ListCell   *lc1,
					   *lc2;

			info = lfirst_node(GroupByOrdering, lc);

			Assert(list_length(info->clauses) == list_length(pinfo->clauses));
			Assert(list_length(info->pathkeys) == list_length(pinfo->pathkeys));
			Assert(list_difference(info->clauses, pinfo->clauses) == NIL);
			Assert(list_difference_ptr(info->pathkeys, pinfo->pathkeys) == NIL);

			forboth(lc1, info->clauses, lc2, info->pathkeys)
			{
				SortGroupClause *sgc = lfirst_node(SortGroupClause, lc1);
				PathKey    *pk = lfirst_node(PathKey, lc2);

				Assert(pk->pk_eclass->ec_sortref == sgc->tleSortGroupRef);
			}
		}
	}
#endif
	return infos;
}

/*
 * pathkeys_count_contained_in
 *    Same as pathkeys_contained_in, but also sets length of longest
 *    common prefix of keys1 and keys2.
 */
/*
 * pathkeys_count_contained_in - (中文)同 pathkeys_contained_in,并额外
 * 输出 keys1 与 keys2 最长公共前缀的长度
 *
 * 【作用】在需要"不仅知道是否覆盖、还知道覆盖了多少键"时使用:例如
 * try_mergejoin_path 用 outer_presorted_keys(前缀长度)判断是否可应用增量
 * 排序;count_common_leading_pathkeys_ordered() 直接委托本函数。
 *
 * 【设计思想】快速路径:同一列表(前缀长 = 列表长度,包含)或 keys1 为空
 * (前缀长 0,包含)或 keys2 为空(前缀长 0,不包含)。否则两列表逐位比较,
 * 记录公共前缀数 n;一旦发现不同元素即返回 false 并输出 n;全部比较完
 * 后,仅当 keys1 也遍历完(key1 == NULL)才算 keys2 覆盖 keys1。
 *
 * 【参数】
 *   keys1   —— 需求侧键列表;
 *   keys2   —— 路径实际排序键列表;
 *   n_common —— 出参:最长公共前缀的键个数。
 * 【返回值】true:keys2 的排序覆盖 keys1;false:否则。
 */
bool
pathkeys_count_contained_in(List *keys1, List *keys2, int *n_common)
{
	int			n = 0;
	ListCell   *key1,
			   *key2;

	/*
	 * See if we can avoiding looping through both lists. This optimization
	 * gains us several percent in planning time in a worst-case test.
	 */
	if (keys1 == keys2)
	{
		*n_common = list_length(keys1);
		return true;
	}
	else if (keys1 == NIL)
	{
		*n_common = 0;
		return true;
	}
	else if (keys2 == NIL)
	{
		*n_common = 0;
		return false;
	}

	/*
	 * If both lists are non-empty, iterate through both to find out how many
	 * items are shared.
	 */
	forboth(key1, keys1, key2, keys2)
	{
		PathKey    *pathkey1 = (PathKey *) lfirst(key1);
		PathKey    *pathkey2 = (PathKey *) lfirst(key2);

		if (pathkey1 != pathkey2)
		{
			*n_common = n;
			return false;
		}
		n++;
	}

	/* If we ended with a null value, then we've processed the whole list. */
	*n_common = n;
	return (key1 == NULL);
}

/*
 * get_cheapest_path_for_pathkeys
 *	  Find the cheapest path (according to the specified criterion) that
 *	  satisfies the given pathkeys and parameterization, and is parallel-safe
 *	  if required.
 *	  Return NULL if no such path.
 *
 * 'paths' is a list of possible paths that all generate the same relation
 * 'pathkeys' represents a required ordering (in canonical form!)
 * 'required_outer' denotes allowable outer relations for parameterized paths
 * 'cost_criterion' is STARTUP_COST or TOTAL_COST
 * 'require_parallel_safe' causes us to consider only parallel-safe paths
 */
/*
 * get_cheapest_path_for_pathkeys - (中文)在给定路径列表中找出满足指定排序
 * 与参数化约束的最便宜路径
 *
 * 【作用】规划器在多种场合使用:如 generate_mergejoin_paths() 找已预排序
 * 的内层路径、路径选择时找满足输出排序的路径等。遍历 paths,筛选出"排序
 * 覆盖 pathkeys、参数来源是 required_outer 子集、按需并行安全"的路径,返回
 * 按指定代价准则最便宜者。
 *
 * 【设计思想】因为代价比较比路径键比较便宜,先做代价比较快速排除
 * (matched_path 已更便宜则跳过),再做 pathkeys_contained_in() 与
 * bms_is_subset(PATH_REQ_OUTER(path), required_outer) 判定;注意只比较
 * 当前最优,未通过者不会成为候选;最终返回 NULL 表示没有满足条件的路径。
 *
 * 【参数】
 *   paths                —— 产生同一关系的候选路径列表;
 *   pathkeys             —— 要求的排序(规范形式);
 *   required_outer       —— 允许的参数来源关系集合;
 *   cost_criterion       —— STARTUP_COST 或 TOTAL_COST;
 *   require_parallel_safe —— true 时只考虑并行安全路径。
 * 【返回值】满足条件的最便宜路径;无匹配时返回 NULL。
 */
Path *
get_cheapest_path_for_pathkeys(List *paths, List *pathkeys,
							   Relids required_outer,
							   CostSelector cost_criterion,
							   bool require_parallel_safe)
{
	Path	   *matched_path = NULL;
	ListCell   *l;

	foreach(l, paths)
	{
		Path	   *path = (Path *) lfirst(l);

		/* If required, reject paths that are not parallel-safe */
		if (require_parallel_safe && !path->parallel_safe)
			continue;

		/*
		 * Since cost comparison is a lot cheaper than pathkey comparison, do
		 * that first.  (XXX is that still true?)
		 */
		if (matched_path != NULL &&
			compare_path_costs(matched_path, path, cost_criterion) <= 0)
			continue;

		if (pathkeys_contained_in(pathkeys, path->pathkeys) &&
			bms_is_subset(PATH_REQ_OUTER(path), required_outer))
			matched_path = path;
	}
	return matched_path;
}

/*
 * get_cheapest_fractional_path_for_pathkeys
 *	  Find the cheapest path (for retrieving a specified fraction of all
 *	  the tuples) that satisfies the given pathkeys and parameterization.
 *	  Return NULL if no such path.
 *
 * See compare_fractional_path_costs() for the interpretation of the fraction
 * parameter.
 *
 * 'paths' is a list of possible paths that all generate the same relation
 * 'pathkeys' represents a required ordering (in canonical form!)
 * 'required_outer' denotes allowable outer relations for parameterized paths
 * 'fraction' is the fraction of the total tuples expected to be retrieved
 */
/*
 * get_cheapest_fractional_path_for_pathkeys - (中文)找出"检索全部元组的指定
 * 比例"时最便宜的、满足排序与参数化约束的路径
 *
 * 【作用】与 get_cheapest_path_for_pathkeys 类似,但代价准则换成"取前
 * fraction 比例的元组"(如 LIMIT 场景下提前停止的排序),供上层在处理部分
 * 结果检索时使用。
 *
 * 【设计思想】结构与普通版本完全一致,只是用 compare_fractional_path_costs()
 * 比较"获取 fraction 比例"所需的代价;排序与参数化过滤逻辑不变
 * (pathkeys_contained_in + bms_is_subset)。
 *
 * 【参数】
 *   paths         —— 候选路径列表;
 *   pathkeys      —— 要求的排序(规范形式);
 *   required_outer —— 允许的参数来源集合;
 *   fraction      —— 期望检索的元组比例(语义见
 *                    compare_fractional_path_costs())。
 * 【返回值】满足条件的按分数代价最便宜的路径;无匹配时返回 NULL。
 */
Path *
get_cheapest_fractional_path_for_pathkeys(List *paths,
										  List *pathkeys,
										  Relids required_outer,
										  double fraction)
{
	Path	   *matched_path = NULL;
	ListCell   *l;

	foreach(l, paths)
	{
		Path	   *path = (Path *) lfirst(l);

		/*
		 * Since cost comparison is a lot cheaper than pathkey comparison, do
		 * that first.  (XXX is that still true?)
		 */
		if (matched_path != NULL &&
			compare_fractional_path_costs(matched_path, path, fraction) <= 0)
			continue;

		if (pathkeys_contained_in(pathkeys, path->pathkeys) &&
			bms_is_subset(PATH_REQ_OUTER(path), required_outer))
			matched_path = path;
	}
	return matched_path;
}


/*
 * get_cheapest_parallel_safe_total_inner
 *	  Find the unparameterized parallel-safe path with the least total cost.
 */
/*
 * get_cheapest_parallel_safe_total_inner - (中文)找出总代价最便宜、无参数化
 * 且并行安全的内层路径
 *
 * 【作用】并行归并/哈希连接的输入选择辅助函数:当 joinrel 并行安全而内层
 * cheapest_total_path 不并行安全时,在 pathlist 中找出可用的替代——要求
 * 并行安全且无参数化(parallel 路径不能带参数)。供 sort_inner_and_outer()、
 * match_unsorted_outer()、hash_inner_and_outer() 使用。
 *
 * 【设计思想】pathlist 按 add_path() 的保留顺序大致有序(总代价递增排列,
 * 同类路径按某种顺序),因此首个同时满足 parallel_safe 且无参数化的路径
 * 通常就是最便宜者,直接返回即可,无需显式代价比较。
 *
 * 【参数】paths —— 内层关系的路径列表。
 * 【返回值】满足条件的路径;无则返回 NULL。
 */
Path *
get_cheapest_parallel_safe_total_inner(List *paths)
{
	ListCell   *l;

	foreach(l, paths)
	{
		Path	   *innerpath = (Path *) lfirst(l);

		if (innerpath->parallel_safe &&
			bms_is_empty(PATH_REQ_OUTER(innerpath)))
			return innerpath;
	}

	return NULL;
}

/****************************************************************************
 *		NEW PATHKEY FORMATION
 ****************************************************************************/

/*
 * build_index_pathkeys
 *	  Build a pathkeys list that describes the ordering induced by an index
 *	  scan using the given index.  (Note that an unordered index doesn't
 *	  induce any ordering, so we return NIL.)
 *
 * If 'scandir' is BackwardScanDirection, build pathkeys representing a
 * backwards scan of the index.
 *
 * We iterate only key columns of covering indexes, since non-key columns
 * don't influence index ordering.  The result is canonical, meaning that
 * redundant pathkeys are removed; it may therefore have fewer entries than
 * there are key columns in the index.
 *
 * Another reason for stopping early is that we may be able to tell that
 * an index column's sort order is uninteresting for this query.  However,
 * that test is just based on the existence of an EquivalenceClass and not
 * on position in pathkey lists, so it's not complete.  Caller should call
 * truncate_useless_pathkeys() to possibly remove more pathkeys.
 */
/*
 * build_index_pathkeys - (中文)构建描述"用给定索引扫描"产生的排序的路径键
 * 列表
 *
 * 【作用】planmain.c / plannodes 生成索引扫描路径前调用本函数:把索引各键
 * 列的排序信息(算符族、方向、NULL 位置)转成规范路径键列表,作为索引扫描
 * 路径的输出排序。无序索引(无 sortopfamily)返回 NIL。
 *
 * 【设计思想】
 * - 只遍历 nkeycolumns 个键列,INCLUDE 列不参与排序;
 * - 反向扫描时,把每个键列的 reverse_sort 与 nulls_first 取反;
 * - 对每列调 make_pathkey_from_sortinfo(create_it = false):只有该列存在于
 *   某个等价类(即对本次查询"有意义")时才加入列表,并剔除冗余键
 *   (pathkey_is_redundant);
 * - 若某键列不在任何 EC 中:若是"布尔常量绑定"(indexcol_is_bool_constant_
 *   for_query 命中,如 WHERE bool_col),仍可继续处理更低的列;否则该排序
 *   对查询无意义,低阶键更无意义,立即停止;
 * - 结果规范且去冗余,故条目数可能少于索引键列数;调用方还应再用
 *   truncate_useless_pathkeys() 进一步裁剪。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   index   —— 索引(IndexOptInfo);
 *   scandir —— 扫描方向(ForwardScanDirection / BackwardScanDirection)。
 * 【返回值】描述索引排序的路径键列表;无序索引返回 NIL。
 */
List *
build_index_pathkeys(PlannerInfo *root,
					 IndexOptInfo *index,
					 ScanDirection scandir)
{
	List	   *retval = NIL;
	ListCell   *lc;
	int			i;

	if (index->sortopfamily == NULL)
		return NIL;				/* non-orderable index */

	i = 0;
	foreach(lc, index->indextlist)
	{
		TargetEntry *indextle = (TargetEntry *) lfirst(lc);
		Expr	   *indexkey;
		bool		reverse_sort;
		bool		nulls_first;
		PathKey    *cpathkey;

		/*
		 * INCLUDE columns are stored in index unordered, so they don't
		 * support ordered index scan.
		 */
		if (i >= index->nkeycolumns)
			break;

		/* We assume we don't need to make a copy of the tlist item */
		indexkey = indextle->expr;

		if (ScanDirectionIsBackward(scandir))
		{
			reverse_sort = !index->reverse_sort[i];
			nulls_first = !index->nulls_first[i];
		}
		else
		{
			reverse_sort = index->reverse_sort[i];
			nulls_first = index->nulls_first[i];
		}

		/*
		 * OK, try to make a canonical pathkey for this sort key.
		 */
		cpathkey = make_pathkey_from_sortinfo(root,
											  indexkey,
											  index->sortopfamily[i],
											  index->opcintype[i],
											  index->indexcollations[i],
											  reverse_sort,
											  nulls_first,
											  0,
											  index->rel->relids,
											  false);

		if (cpathkey)
		{
			/*
			 * We found the sort key in an EquivalenceClass, so it's relevant
			 * for this query.  Add it to list, unless it's redundant.
			 */
			if (!pathkey_is_redundant(cpathkey, retval))
				retval = lappend(retval, cpathkey);
		}
		else
		{
			/*
			 * Boolean index keys might be redundant even if they do not
			 * appear in an EquivalenceClass, because of our special treatment
			 * of boolean equality conditions --- see the comment for
			 * indexcol_is_bool_constant_for_query().  If that applies, we can
			 * continue to examine lower-order index columns.  Otherwise, the
			 * sort key is not an interesting sort order for this query, so we
			 * should stop considering index columns; any lower-order sort
			 * keys won't be useful either.
			 */
			if (!indexcol_is_bool_constant_for_query(root, index, i))
				break;
		}

		i++;
	}

	return retval;
}

/*
 * partkey_is_bool_constant_for_query
 *
 * If a partition key column is constrained to have a constant value by the
 * query's WHERE conditions, then it's irrelevant for sort-order
 * considerations.  Usually that means we have a restriction clause
 * WHERE partkeycol = constant, which gets turned into an EquivalenceClass
 * containing a constant, which is recognized as redundant by
 * build_partition_pathkeys().  But if the partition key column is a
 * boolean variable (or expression), then we are not going to see such a
 * WHERE clause, because expression preprocessing will have simplified it
 * to "WHERE partkeycol" or "WHERE NOT partkeycol".  So we are not going
 * to have a matching EquivalenceClass (unless the query also contains
 * "ORDER BY partkeycol").  To allow such cases to work the same as they would
 * for non-boolean values, this function is provided to detect whether the
 * specified partition key column matches a boolean restriction clause.
 */
/*
 * partkey_is_bool_constant_for_query - (中文)判断分区键列是否被查询条件
 * 约束为布尔常量
 *
 * 【作用】build_partition_pathkeys() 的辅助函数:当某个布尔型分区键列被
 * "WHERE partkey" 或 "WHERE NOT partkey" 约束为常量时,它对本查询的排序
 * 无关紧要,可跳过该列继续处理更低的列。
 *
 * 【设计思想】普通类型的分区键约束会进入等价类并被识别为冗余;但布尔类型
 * 的 "= TRUE"/"= FALSE" 会被表达式预处理折叠成裸 Var 或 NOT Var,不会产生
 * 等价类,故需要专门检测:列必须使用内建布尔算符族(分区目前只允许内建
 * AM),且 baserestrictinfo 中存在一条与之精确匹配(或 NOT 匹配)的子句。
 *
 * 【参数】
 *   partrel    —— 分区关系;
 *   partkeycol —— 分区键列下标(0 基)。
 * 【返回值】true:该列被布尔限制子句绑定为常量;false:否则。
 */
static bool
partkey_is_bool_constant_for_query(RelOptInfo *partrel, int partkeycol)
{
	PartitionScheme partscheme = partrel->part_scheme;
	ListCell   *lc;

	/*
	 * If the partkey isn't boolean, we can't possibly get a match.
	 *
	 * Partitioning currently can only use built-in AMs, so checking for
	 * built-in boolean opfamilies is good enough.
	 */
	if (!IsBuiltinBooleanOpfamily(partscheme->partopfamily[partkeycol]))
		return false;

	/* Check each restriction clause for the partitioned rel */
	foreach(lc, partrel->baserestrictinfo)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		/* Ignore pseudoconstant quals, they won't match */
		if (rinfo->pseudoconstant)
			continue;

		/* See if we can match the clause's expression to the partkey column */
		if (matches_boolean_partition_clause(rinfo, partrel, partkeycol))
			return true;
	}

	return false;
}

/*
 * matches_boolean_partition_clause
 *		Determine if the boolean clause described by rinfo matches
 *		partrel's partkeycol-th partition key column.
 *
 * "Matches" can be either an exact match (equivalent to partkey = true),
 * or a NOT above an exact match (equivalent to partkey = false).
 */
/*
 * matches_boolean_partition_clause - (中文)判断 rinfo 描述的布尔子句是否
 * 匹配 partrel 的第 partkeycol 个分区键列
 *
 * 【作用】partkey_is_bool_constant_for_query() 的底层判定:检查一条限制
 * 子句是否等价于"分区键 = TRUE"(直接匹配)或"分区键 = FALSE"(NOT 包裹
 * 的匹配)。
 *
 * 【设计思想】用 equal() 做结构等值比较:子句表达式与该分区键列表达式
 * (partexprs[partkeycol] 的首个元素)完全相等,或子句是 NOT 且其参数与
 * 分区键相等,即为匹配。partexprs 里含多个表达式时取第一个(常规情形)。
 *
 * 【参数】
 *   rinfo     —— 限制子句节点;
 *   partrel   —— 分区关系;
 *   partkeycol —— 分区键列下标。
 * 【返回值】true:子句把该分区键列绑定为 TRUE 或 FALSE;false:否则。
 */
static bool
matches_boolean_partition_clause(RestrictInfo *rinfo,
								 RelOptInfo *partrel, int partkeycol)
{
	Node	   *clause = (Node *) rinfo->clause;
	Node	   *partexpr = (Node *) linitial(partrel->partexprs[partkeycol]);

	/* Direct match? */
	if (equal(partexpr, clause))
		return true;
	/* NOT clause? */
	else if (is_notclause(clause))
	{
		Node	   *arg = (Node *) get_notclausearg((Expr *) clause);

		if (equal(partexpr, arg))
			return true;
	}

	return false;
}

/*
 * build_partition_pathkeys
 *	  Build a pathkeys list that describes the ordering induced by the
 *	  partitions of partrel, under either forward or backward scan
 *	  as per scandir.
 *
 * Caller must have checked that the partitions are properly ordered,
 * as detected by partitions_are_ordered().
 *
 * Sets *partialkeys to true if pathkeys were only built for a prefix of the
 * partition key, or false if the pathkeys include all columns of the
 * partition key.
 */
/*
 * build_partition_pathkeys - (中文)构建描述分区扫描(按分区边界顺序)排序的
 * 路径键列表
 *
 * 【作用】分区表扫描路径的排序信息构造器:当分区被证明是按分区键有序排列
 * (partitions_are_ordered)时,顺序扫描各分区即产生一种排序;本函数把分区
 * 键各列换算成规范路径键。通过 *partialkeys 告知调用方是否只覆盖了分区键
 * 的前缀。
 *
 * 【设计思想】
 * - 调用前必须已验证分区有序,且当前只支持基表(IS_SIMPLE_REL);
 * - 每列分区键用 make_pathkey_from_sortinfo(create_it = false)构造键:
 *   NULL 分区约定排最后,因此 nulls_first 只在反向扫描时取 true
 *   (与 NULLS LAST 索引一致);
 * - 键存在于等价类(对查询有意义)且不冗余则加入;否则若布尔列被常量绑定
 *   (partkey_is_bool_constant_for_query)可继续低列,不然置 *partialkeys =
 *   true 并返回已收集前缀;全部处理完则 *partialkeys = false。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   partrel     —— 分区关系;
 *   scandir     —— 前向/后向扫描;
 *   partialkeys —— 出参:true 表示只构建了分区键前缀的路径键。
 * 【返回值】分区扫描排序的路径键列表。
 */
List *
build_partition_pathkeys(PlannerInfo *root, RelOptInfo *partrel,
						 ScanDirection scandir, bool *partialkeys)
{
	List	   *retval = NIL;
	PartitionScheme partscheme = partrel->part_scheme;
	int			i;

	Assert(partscheme != NULL);
	Assert(partitions_are_ordered(partrel->boundinfo, partrel->live_parts));
	/* For now, we can only cope with baserels */
	Assert(IS_SIMPLE_REL(partrel));

	for (i = 0; i < partscheme->partnatts; i++)
	{
		PathKey    *cpathkey;
		Expr	   *keyCol = (Expr *) linitial(partrel->partexprs[i]);

		/*
		 * Try to make a canonical pathkey for this partkey.
		 *
		 * We assume the PartitionDesc lists any NULL partition last, so we
		 * treat the scan like a NULLS LAST index: we have nulls_first for
		 * backwards scan only.
		 */
		cpathkey = make_pathkey_from_sortinfo(root,
											  keyCol,
											  partscheme->partopfamily[i],
											  partscheme->partopcintype[i],
											  partscheme->partcollation[i],
											  ScanDirectionIsBackward(scandir),
											  ScanDirectionIsBackward(scandir),
											  0,
											  partrel->relids,
											  false);


		if (cpathkey)
		{
			/*
			 * We found the sort key in an EquivalenceClass, so it's relevant
			 * for this query.  Add it to list, unless it's redundant.
			 */
			if (!pathkey_is_redundant(cpathkey, retval))
				retval = lappend(retval, cpathkey);
		}
		else
		{
			/*
			 * Boolean partition keys might be redundant even if they do not
			 * appear in an EquivalenceClass, because of our special treatment
			 * of boolean equality conditions --- see the comment for
			 * partkey_is_bool_constant_for_query().  If that applies, we can
			 * continue to examine lower-order partition keys.  Otherwise, the
			 * sort key is not an interesting sort order for this query, so we
			 * should stop considering partition columns; any lower-order sort
			 * keys won't be useful either.
			 */
			if (!partkey_is_bool_constant_for_query(partrel, i))
			{
				*partialkeys = true;
				return retval;
			}
		}
	}

	*partialkeys = false;
	return retval;
}

/*
 * build_expression_pathkey
 *	  Build a pathkeys list that describes an ordering by a single expression
 *	  using the given sort operator.
 *
 * expr and rel are as for make_pathkey_from_sortinfo.
 * We induce the other arguments assuming default sort order for the operator.
 *
 * Similarly to make_pathkey_from_sortinfo, the result is NIL if create_it
 * is false and the expression isn't already in some EquivalenceClass.
 */
/*
 * build_expression_pathkey - (中文)用给定排序运算符构造"按单个表达式排序"
 * 的路径键列表
 *
 * 【作用】由表达式 + 排序运算符直接构造一个(或零个)路径键的便利接口,
 * 供 planagg.c(如 MIN/MAX 聚合利用索引)等场景使用。
 *
 * 【设计思想】先从 pg_amop 反查运算符的算符族/类型/比较方向
 * (get_ordering_op_properties),排序规则取表达式的 collation,然后转交
 * make_pathkey_from_sortinfo()。排序方向按 cmptype 决定(reverse_sort 与
 * nulls_first 均取"是否 COMPARE_GT",即降序时两者都为 true——按默认排序
 * 语义,降序等价于反转且 NULL 位置也反转)。
 *
 * 【参数】
 *   root      —— PlannerInfo;
 *   expr      —— 待排序表达式;
 *   opno      —— 排序运算符 OID;
 *   rel       —— 相关关系 relids(允许其子 EC 成员匹配,可为空);
 *   create_it —— true:允许创建缺失的等价类。
 * 【返回值】含单元素的路径键列表;create_it 为 false 且表达式不在任何
 * 等价类时返回 NIL。
 */
List *
build_expression_pathkey(PlannerInfo *root,
						 Expr *expr,
						 Oid opno,
						 Relids rel,
						 bool create_it)
{
	List	   *pathkeys;
	Oid			opfamily,
				opcintype;
	CompareType cmptype;
	PathKey    *cpathkey;

	/* Find the operator in pg_amop --- failure shouldn't happen */
	if (!get_ordering_op_properties(opno,
									&opfamily, &opcintype, &cmptype))
		elog(ERROR, "operator %u is not a valid ordering operator",
			 opno);

	cpathkey = make_pathkey_from_sortinfo(root,
										  expr,
										  opfamily,
										  opcintype,
										  exprCollation((Node *) expr),
										  (cmptype == COMPARE_GT),
										  (cmptype == COMPARE_GT),
										  0,
										  rel,
										  create_it);

	if (cpathkey)
		pathkeys = list_make1(cpathkey);
	else
		pathkeys = NIL;

	return pathkeys;
}

/*
 * convert_subquery_pathkeys
 *	  Build a pathkeys list that describes the ordering of a subquery's
 *	  result, in the terms of the outer query.  This is essentially a
 *	  task of conversion.
 *
 * 'rel': outer query's RelOptInfo for the subquery relation.
 * 'subquery_pathkeys': the subquery's output pathkeys, in its terms.
 * 'subquery_tlist': the subquery's output targetlist, in its terms.
 *
 * We intentionally don't do truncate_useless_pathkeys() here, because there
 * are situations where seeing the raw ordering of the subquery is helpful.
 * For example, if it returns ORDER BY x DESC, that may prompt us to
 * construct a mergejoin using DESC order rather than ASC order; but the
 * right_merge_direction heuristic would have us throw the knowledge away.
 */
/*
 * convert_subquery_pathkeys - (中文)把子查询的输出排序翻译成外层查询术语
 * 下的路径键
 *
 * 【作用】处理"子查询作为范围表被拉起"时调用(如 pull_up_subquery / 子查询
 * 扫描):把子查询的排序键(subquery_pathkeys,用子查询自己的表达式)映射到
 * 外层查询可见的 Var,构建外层查询的路径键列表。
 *
 * 【设计思想】
 * - 对子查询的每个路径键,把其等价类的成员逐一与子查询 targetlist 条目
 *   匹配,条目若被外层可见(非 resjunk 且出现在 rel 的 reltarget 中,
 *   find_var_for_subquery_tle),则用外层 Var 找外层等价类并构造外层规范键;
 * - volatile 等价类(必来自 ORDER BY)只能精确匹配到原 targetlist 条目;
 * - 非 volatile 等价类可能有多个候选表示,取"评分"最高者:等价类成员数-1
 *   (对等同伴数) + 若恰好匹配外层 query_pathkeys 当前项再加 1;无法把外层
 *   等价类全部生成出来是因为调用时机外层 EC 已冻结;
 * - 刻意不做 truncate_useless_pathkeys():某些场景需要看到子查询原始排序
 *   (例如 DESC 排序也许能引导外层用 DESC 归并,而 right_merge_direction
 *    启发式会把这条信息丢掉);
 * - 剔除冗余键;任一步骤找不到表示就停止(后面的键更用不上)。
 *
 * 【参数】
 *   root             —— PlannerInfo;
 *   rel              —— 外层查询中代表该子查询的关系;
 *   subquery_pathkeys —— 子查询的输出排序键;
 *   subquery_tlist    —— 子查询的输出目标表。
 * 【返回值】外层查询术语下的路径键列表(可能短于输入)。
 */
List *
convert_subquery_pathkeys(PlannerInfo *root, RelOptInfo *rel,
						  List *subquery_pathkeys,
						  List *subquery_tlist)
{
	List	   *retval = NIL;
	int			retvallen = 0;
	int			outer_query_keys = list_length(root->query_pathkeys);
	ListCell   *i;

	foreach(i, subquery_pathkeys)
	{
		PathKey    *sub_pathkey = (PathKey *) lfirst(i);
		EquivalenceClass *sub_eclass = sub_pathkey->pk_eclass;
		PathKey    *best_pathkey = NULL;

		if (sub_eclass->ec_has_volatile)
		{
			/*
			 * If the sub_pathkey's EquivalenceClass is volatile, then it must
			 * have come from an ORDER BY clause, and we have to match it to
			 * that same targetlist entry.
			 */
			TargetEntry *tle;
			Var		   *outer_var;

			if (sub_eclass->ec_sortref == 0)	/* can't happen */
				elog(ERROR, "volatile EquivalenceClass has no sortref");
			tle = get_sortgroupref_tle(sub_eclass->ec_sortref, subquery_tlist);
			Assert(tle);
			/* Is TLE actually available to the outer query? */
			outer_var = find_var_for_subquery_tle(rel, tle);
			if (outer_var)
			{
				/* We can represent this sub_pathkey */
				EquivalenceMember *sub_member;
				EquivalenceClass *outer_ec;

				Assert(list_length(sub_eclass->ec_members) == 1);
				sub_member = (EquivalenceMember *) linitial(sub_eclass->ec_members);

				/*
				 * Note: it might look funny to be setting sortref = 0 for a
				 * reference to a volatile sub_eclass.  However, the
				 * expression is *not* volatile in the outer query: it's just
				 * a Var referencing whatever the subquery emitted. (IOW, the
				 * outer query isn't going to re-execute the volatile
				 * expression itself.)	So this is okay.
				 */
				outer_ec =
					get_eclass_for_sort_expr(root,
											 (Expr *) outer_var,
											 sub_eclass->ec_opfamilies,
											 sub_member->em_datatype,
											 sub_eclass->ec_collation,
											 0,
											 rel->relids,
											 false);

				/*
				 * If we don't find a matching EC, sub-pathkey isn't
				 * interesting to the outer query
				 */
				if (outer_ec)
					best_pathkey =
						make_canonical_pathkey(root,
											   outer_ec,
											   sub_pathkey->pk_opfamily,
											   sub_pathkey->pk_cmptype,
											   sub_pathkey->pk_nulls_first);
			}
		}
		else
		{
			/*
			 * Otherwise, the sub_pathkey's EquivalenceClass could contain
			 * multiple elements (representing knowledge that multiple items
			 * are effectively equal).  Each element might match none, one, or
			 * more of the output columns that are visible to the outer query.
			 * This means we may have multiple possible representations of the
			 * sub_pathkey in the context of the outer query.  Ideally we
			 * would generate them all and put them all into an EC of the
			 * outer query, thereby propagating equality knowledge up to the
			 * outer query.  Right now we cannot do so, because the outer
			 * query's EquivalenceClasses are already frozen when this is
			 * called. Instead we prefer the one that has the highest "score"
			 * (number of EC peers, plus one if it matches the outer
			 * query_pathkeys). This is the most likely to be useful in the
			 * outer query.
			 */
			int			best_score = -1;
			ListCell   *j;

			/* Ignore children here */
			foreach(j, sub_eclass->ec_members)
			{
				EquivalenceMember *sub_member = (EquivalenceMember *) lfirst(j);
				Expr	   *sub_expr = sub_member->em_expr;
				Oid			sub_expr_type = sub_member->em_datatype;
				Oid			sub_expr_coll = sub_eclass->ec_collation;
				ListCell   *k;

				/* Child members should not exist in ec_members */
				Assert(!sub_member->em_is_child);

				foreach(k, subquery_tlist)
				{
					TargetEntry *tle = (TargetEntry *) lfirst(k);
					Var		   *outer_var;
					Expr	   *tle_expr;
					EquivalenceClass *outer_ec;
					PathKey    *outer_pk;
					int			score;

					/* Is TLE actually available to the outer query? */
					outer_var = find_var_for_subquery_tle(rel, tle);
					if (!outer_var)
						continue;

					/*
					 * The targetlist entry is considered to match if it
					 * matches after sort-key canonicalization.  That is
					 * needed since the sub_expr has been through the same
					 * process.
					 */
					tle_expr = canonicalize_ec_expression(tle->expr,
														  sub_expr_type,
														  sub_expr_coll);
					if (!equal(tle_expr, sub_expr))
						continue;

					/* See if we have a matching EC for the TLE */
					outer_ec = get_eclass_for_sort_expr(root,
														(Expr *) outer_var,
														sub_eclass->ec_opfamilies,
														sub_expr_type,
														sub_expr_coll,
														0,
														rel->relids,
														false);

					/*
					 * If we don't find a matching EC, this sub-pathkey isn't
					 * interesting to the outer query
					 */
					if (!outer_ec)
						continue;

					outer_pk = make_canonical_pathkey(root,
													  outer_ec,
													  sub_pathkey->pk_opfamily,
													  sub_pathkey->pk_cmptype,
													  sub_pathkey->pk_nulls_first);
					/* score = # of equivalence peers */
					score = list_length(outer_ec->ec_members) - 1;
					/* +1 if it matches the proper query_pathkeys item */
					if (retvallen < outer_query_keys &&
						list_nth(root->query_pathkeys, retvallen) == outer_pk)
						score++;
					if (score > best_score)
					{
						best_pathkey = outer_pk;
						best_score = score;
					}
				}
			}
		}

		/*
		 * If we couldn't find a representation of this sub_pathkey, we're
		 * done (we can't use the ones to its right, either).
		 */
		if (!best_pathkey)
			break;

		/*
		 * Eliminate redundant ordering info; could happen if outer query
		 * equivalences subquery keys...
		 */
		if (!pathkey_is_redundant(best_pathkey, retval))
		{
			retval = lappend(retval, best_pathkey);
			retvallen++;
		}
	}

	return retval;
}

/*
 * find_var_for_subquery_tle
 *
 * If the given subquery tlist entry is due to be emitted by the subquery's
 * scan node, return a Var for it, else return NULL.
 *
 * We need this to ensure that we don't return pathkeys describing values
 * that are unavailable above the level of the subquery scan.
 */
/*
 * find_var_for_subquery_tle - (中文)若给定子查询目标表条目将由子查询扫描
 * 节点输出,则返回对应的 Var,否则返回 NULL
 *
 * 【作用】convert_subquery_pathkeys() 的辅助函数:确认子查询的某个 TLE 对外
 * 层可见,并生成引用它的 Var。
 *
 * 【设计思想】resjunk 条目不对外可见,直接拒绝;然后在 rel->reltarget->exprs
 * 中寻找 varno == rel->relid 且 varattno == tle->resno 的 Var。找到即返回
 * 其副本(copyObject,保证安全);找不到返回 NULL(说明该值不会被子查询扫描
 * 输出)。
 *
 * 【参数】
 *   rel —— 外层查询中该子查询的 RelOptInfo;
 *   tle —— 子查询目标表条目。
 * 【返回值】引用该条目的 Var 副本;不可见时返回 NULL。
 */
static Var *
find_var_for_subquery_tle(RelOptInfo *rel, TargetEntry *tle)
{
	ListCell   *lc;

	/* If the TLE is resjunk, it's certainly not visible to the outer query */
	if (tle->resjunk)
		return NULL;

	/* Search the rel's targetlist to see what it will return */
	foreach(lc, rel->reltarget->exprs)
	{
		Var		   *var = (Var *) lfirst(lc);

		/* Ignore placeholders */
		if (!IsA(var, Var))
			continue;
		Assert(var->varno == rel->relid);

		/* If we find a Var referencing this TLE, we're good */
		if (var->varattno == tle->resno)
			return copyObject(var); /* Make a copy for safety */
	}
	return NULL;
}

/*
 * build_join_pathkeys
 *	  Build the path keys for a join relation constructed by mergejoin or
 *	  nestloop join.  This is normally the same as the outer path's keys.
 *
 *	  EXCEPTION: in a FULL, RIGHT or RIGHT_ANTI join, we cannot treat the
 *	  result as having the outer path's path keys, because null lefthand rows
 *	  may be inserted at random points.  It must be treated as unsorted.
 *
 *	  We truncate away any pathkeys that are uninteresting for higher joins.
 *
 * 'joinrel' is the join relation that paths are being formed for
 * 'jointype' is the join type (inner, left, full, etc)
 * 'outer_pathkeys' is the list of the current outer path's path keys
 *
 * Returns the list of new path keys.
 */
/*
 * build_join_pathkeys - (中文)构建连接关系(归并/嵌套循环)的输出排序键
 *
 * 【作用】joinpath.c(如 match_unsorted_outer、sort_inner_and_outer)为每条
 * 候选连接路径计算输出排序时调用本函数。通常与输入外层路径的排序相同,但
 * FULL/RIGHT/RIGHT_ANTI 连接因可能随机插入 NULL 扩展行而视为无序。
 *
 * 【设计思想】RIGHT_SEMI 不允许到达这里(断言)。FULL/RIGHT/RIGHT_ANTI
 * 直接返回 NIL(无排序);其余类型直接把外层路径键交给
 * truncate_useless_pathkeys() 裁剪后返回——源码注释说明历史上这里曾是很
 * 复杂的代码,但自从所有路径键子列表都规范化后,只需做裁剪(去掉对更高层
 * 无用、但对形成本连接曾有用的键)。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   joinrel       —— 正在形成路径的连接关系;
 *   jointype      —— 连接类型;
 *   outer_pathkeys —— 当前外层路径的排序键。
 * 【返回值】新的路径键列表(FULL/RIGHT/RIGHT_ANTI 时为 NIL)。
 */
List *
build_join_pathkeys(PlannerInfo *root,
					RelOptInfo *joinrel,
					JoinType jointype,
					List *outer_pathkeys)
{
	/* RIGHT_SEMI should not come here */
	Assert(jointype != JOIN_RIGHT_SEMI);

	if (jointype == JOIN_FULL ||
		jointype == JOIN_RIGHT ||
		jointype == JOIN_RIGHT_ANTI)
		return NIL;

	/*
	 * This used to be quite a complex bit of code, but now that all pathkey
	 * sublists start out life canonicalized, we don't have to do a darn thing
	 * here!
	 *
	 * We do, however, need to truncate the pathkeys list, since it may
	 * contain pathkeys that were useful for forming this joinrel but are
	 * uninteresting to higher levels.
	 */
	return truncate_useless_pathkeys(root, joinrel, outer_pathkeys);
}

/****************************************************************************
 *		PATHKEYS AND SORT CLAUSES
 ****************************************************************************/

/*
 * make_pathkeys_for_sortclauses
 *		Generate a pathkeys list that represents the sort order specified
 *		by a list of SortGroupClauses
 *
 * The resulting PathKeys are always in canonical form.  (Actually, there
 * is no longer any code anywhere that creates non-canonical PathKeys.)
 *
 * 'sortclauses' is a list of SortGroupClause nodes
 * 'tlist' is the targetlist to find the referenced tlist entries in
 */
/*
 * make_pathkeys_for_sortclauses - (中文)为 SortGroupClause 列表生成路径键
 *
 * 【作用】ORDER BY / GROUP BY / DISTINCT 等处理中,把排序子句列表换算成
 * 路径键列表的便捷封装。结果是规范形式(现代代码已不存在非规范键)。
 *
 * 【设计思想】只是 make_pathkeys_for_sortclauses_extended() 的薄封装:
 * remove_redundant = false(不修改 sortclauses)、sortable 出参直接断言为
 * true——调用方有责任保证所有子句都可排序。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   sortclauses —— SortGroupClause 列表;
 *   tlist       —— 用于解析被引用 TLE 的目标表。
 * 【返回值】对应排序顺序的路径键列表。
 */
List *
make_pathkeys_for_sortclauses(PlannerInfo *root,
							  List *sortclauses,
							  List *tlist)
{
	List	   *result;
	bool		sortable;

	result = make_pathkeys_for_sortclauses_extended(root,
													&sortclauses,
													tlist,
													false,
													false,
													&sortable,
													false);
	/* It's caller error if not all clauses were sortable */
	Assert(sortable);
	return result;
}

/*
 * make_pathkeys_for_sortclauses_extended
 *		Generate a pathkeys list that represents the sort order specified
 *		by a list of SortGroupClauses
 *
 * The comments for make_pathkeys_for_sortclauses apply here too. In addition:
 *
 * If remove_redundant is true, then any sort clauses that are found to
 * give rise to redundant pathkeys are removed from the sortclauses list
 * (which therefore must be pass-by-reference in this version).
 *
 * If remove_group_rtindex is true, then we need to remove the RT index of the
 * grouping step from the sort expressions before we make PathKeys for them.
 *
 * *sortable is set to true if all the sort clauses are in fact sortable.
 * If any are not, they are ignored except for setting *sortable false.
 * (In that case, the output pathkey list isn't really useful.  However,
 * we process the whole sortclauses list anyway, because it's still valid
 * to remove any clauses that can be proven redundant via the eclass logic.
 * Even though we'll have to hash in that case, we might as well not hash
 * redundant columns.)
 *
 * If set_ec_sortref is true then sets the value of the pathkey's
 * EquivalenceClass unless it's already initialized.
 */
/*
 * make_pathkeys_for_sortclauses_extended - (中文)为 SortGroupClause 列表
 * 生成路径键的扩展版
 *
 * 【作用】make_pathkeys_for_sortclauses() 的实现本体,以及其它需要更多控制
 * 的调用方(如分组处理)直接使用的接口:逐个 SortGroupClause 构造路径键,
 * 可移除冗余子句、移除分组步骤的 RT 索引、报告可排序性并回填 ec_sortref。
 *
 * 【设计思想】
 * - 通过 get_sortgroupclause_expr() 从 tlist 取排序表达式;sortop 无效则该
 *   子句不可排序,置 *sortable = false 但继续处理(仍可借 eclass 逻辑剔除
 *   冗余列,因为反正要哈希分组);
 * - remove_group_rtindex 为 true 时,先用 remove_nulling_relids() 去掉表达
 *   式中分组步骤(group_rtindex)的 NULL 化 relid(分组被简化后需要);
 * - make_pathkey_from_sortop() 构造键;若 EC 的 ec_sortref 尚未设置且要求
 *   set_ec_sortref,则回填 SortGroupRef(来自 WHERE 构造的 EC 没有目标引用);
 * - 冗余键不加入列表;remove_redundant 为 true 时,同步把产生冗余键的
 *   sortclause 从原列表删除(故此模式下列表必须按引用传入)。
 *
 * 【参数】
 *   root                —— PlannerInfo;
 *   sortclauses         —— 入/出参:SortGroupClause 列表指针(remove_redundant
 *                          时会被就地删除冗余项);
 *   tlist               —— 目标表;
 *   remove_redundant    —— true:把产生冗余键的子句从 sortclauses 删除;
 *   remove_group_rtindex —— true:构造键前从排序表达式中移除分组步骤的 RT 索引;
 *   sortable            —— 出参:所有子句是否都可排序;
 *   set_ec_sortref      —— true:必要时把 EC 的 ec_sortref 设为 SortGroupRef。
 * 【返回值】规范路径键列表(去冗余)。
 */
List *
make_pathkeys_for_sortclauses_extended(PlannerInfo *root,
									   List **sortclauses,
									   List *tlist,
									   bool remove_redundant,
									   bool remove_group_rtindex,
									   bool *sortable,
									   bool set_ec_sortref)
{
	List	   *pathkeys = NIL;
	ListCell   *l;

	*sortable = true;
	foreach(l, *sortclauses)
	{
		SortGroupClause *sortcl = (SortGroupClause *) lfirst(l);
		Expr	   *sortkey;
		PathKey    *pathkey;

		sortkey = (Expr *) get_sortgroupclause_expr(sortcl, tlist);
		if (!OidIsValid(sortcl->sortop))
		{
			*sortable = false;
			continue;
		}
		if (remove_group_rtindex)
		{
			Assert(root->group_rtindex > 0);
			sortkey = (Expr *)
				remove_nulling_relids((Node *) sortkey,
									  bms_make_singleton(root->group_rtindex),
									  NULL);
		}
		pathkey = make_pathkey_from_sortop(root,
										   sortkey,
										   sortcl->sortop,
										   sortcl->reverse_sort,
										   sortcl->nulls_first,
										   sortcl->tleSortGroupRef,
										   true);
		if (pathkey->pk_eclass->ec_sortref == 0 && set_ec_sortref)
		{
			/*
			 * Copy the sortref if it hasn't been set yet.  That may happen if
			 * the EquivalenceClass was constructed from a WHERE clause, i.e.
			 * it doesn't have a target reference at all.
			 */
			pathkey->pk_eclass->ec_sortref = sortcl->tleSortGroupRef;
		}

		/* Canonical form eliminates redundant ordering keys */
		if (!pathkey_is_redundant(pathkey, pathkeys))
			pathkeys = lappend(pathkeys, pathkey);
		else if (remove_redundant)
			*sortclauses = foreach_delete_current(*sortclauses, l);
	}
	return pathkeys;
}

/****************************************************************************
 *		PATHKEYS AND MERGECLAUSES
 ****************************************************************************/

/*
 * initialize_mergeclause_eclasses
 *		Set the EquivalenceClass links in a mergeclause restrictinfo.
 *
 * RestrictInfo contains fields in which we may cache pointers to
 * EquivalenceClasses for the left and right inputs of the mergeclause.
 * (If the mergeclause is a true equivalence clause these will be the
 * same EquivalenceClass, otherwise not.)  If the mergeclause is either
 * used to generate an EquivalenceClass, or derived from an EquivalenceClass,
 * then it's easy to set up the left_ec and right_ec members --- otherwise,
 * this function should be called to set them up.  We will generate new
 * EquivalenceClauses if necessary to represent the mergeclause's left and
 * right sides.
 *
 * Note this is called before EC merging is complete, so the links won't
 * necessarily point to canonical ECs.  Before they are actually used for
 * anything, update_mergeclause_eclasses must be called to ensure that
 * they've been updated to point to canonical ECs.
 */
/*
 * initialize_mergeclause_eclasses - (中文)在归并子句的 RestrictInfo 中设置
 * 左右两侧的等价类链接
 *
 * 【作用】process_equivalence() 之外的路径上(如尚未产生等价类的归并子句),
 * 由调用方调用本函数初始化 rinfo->left_ec / right_ec:为子句左右表达式各
 * 找(必要时创建)一个等价类并缓存。
 *
 * 【设计思想】归并子句两侧若本就是等价类成员,则指向同一 EC;否则需要为
 * 两侧各建一个 EC。类型用算子声明输入类型(op_input_types),算符族列表用
 * rinfo->mergeopfamilies,排序规则用子句 inputcollid。注意此时 EC 合并尚未
 * 完成,缓存的可能不是规范 EC,真正使用前必须先调
 * update_mergeclause_eclasses() 上溯。
 *
 * 【参数】
 *   root         —— PlannerInfo;
 *   restrictinfo —— 归并子句(须 mergeopfamilies 非空,且 left_ec/right_ec
 *                   尚未设置,有断言)。
 * 【返回值】无(副作用:设置 restrictinfo->left_ec / right_ec)。
 */
void
initialize_mergeclause_eclasses(PlannerInfo *root, RestrictInfo *restrictinfo)
{
	Expr	   *clause = restrictinfo->clause;
	Oid			lefttype,
				righttype;

	/* Should be a mergeclause ... */
	Assert(restrictinfo->mergeopfamilies != NIL);
	/* ... with links not yet set */
	Assert(restrictinfo->left_ec == NULL);
	Assert(restrictinfo->right_ec == NULL);

	/* Need the declared input types of the operator */
	op_input_types(((OpExpr *) clause)->opno, &lefttype, &righttype);

	/* Find or create a matching EquivalenceClass for each side */
	restrictinfo->left_ec =
		get_eclass_for_sort_expr(root,
								 (Expr *) get_leftop(clause),
								 restrictinfo->mergeopfamilies,
								 lefttype,
								 ((OpExpr *) clause)->inputcollid,
								 0,
								 NULL,
								 true);
	restrictinfo->right_ec =
		get_eclass_for_sort_expr(root,
								 (Expr *) get_rightop(clause),
								 restrictinfo->mergeopfamilies,
								 righttype,
								 ((OpExpr *) clause)->inputcollid,
								 0,
								 NULL,
								 true);
}

/*
 * update_mergeclause_eclasses
 *		Make the cached EquivalenceClass links valid in a mergeclause
 *		restrictinfo.
 *
 * These pointers should have been set by process_equivalence or
 * initialize_mergeclause_eclasses, but they might have been set to
 * non-canonical ECs that got merged later.  Chase up to the canonical
 * merged parent if so.
 */
/*
 * update_mergeclause_eclasses - (中文)把归并子句缓存的等价类链接更新为规范
 * 等价类
 *
 * 【作用】EC 合并完成之后、任何需要按规范 EC 匹配归并子句的代码(如
 * select_mergejoin_clauses、find_mergeclauses_for_outer_pathkeys、
 * pathkeys_useful_for_merging)在使用前调用:沿 ec_merged 链把 left_ec /
 * right_ec 上溯到合并后的顶层规范 EC。
 *
 * 【设计思想】指针缓存在 process_equivalence() 或
 * initialize_mergeclause_eclasses() 中设置时可能指向后续被合并进其他 EC 的
 * 非规范节点;本函数简单地把两个指针各自沿 ec_merged 提升到不再被合并的
 * 节点。前提:mergeopfamilies 非空、指针已设置(断言)。
 *
 * 【参数】
 *   root         —— PlannerInfo;
 *   restrictinfo —— 归并子句。
 * 【返回值】无(副作用:原地更新 left_ec / right_ec 指针)。
 */
void
update_mergeclause_eclasses(PlannerInfo *root, RestrictInfo *restrictinfo)
{
	/* Should be a merge clause ... */
	Assert(restrictinfo->mergeopfamilies != NIL);
	/* ... with pointers already set */
	Assert(restrictinfo->left_ec != NULL);
	Assert(restrictinfo->right_ec != NULL);

	/* Chase up to the top as needed */
	while (restrictinfo->left_ec->ec_merged)
		restrictinfo->left_ec = restrictinfo->left_ec->ec_merged;
	while (restrictinfo->right_ec->ec_merged)
		restrictinfo->right_ec = restrictinfo->right_ec->ec_merged;
}

/*
 * find_mergeclauses_for_outer_pathkeys
 *	  This routine attempts to find a list of mergeclauses that can be
 *	  used with a specified ordering for the join's outer relation.
 *	  If successful, it returns a list of mergeclauses.
 *
 * 'pathkeys' is a pathkeys list showing the ordering of an outer-rel path.
 * 'restrictinfos' is a list of mergejoinable restriction clauses for the
 *			join relation being formed, in no particular order.
 *
 * The restrictinfos must be marked (via outer_is_left) to show which side
 * of each clause is associated with the current outer path.  (See
 * select_mergejoin_clauses())
 *
 * The result is NIL if no merge can be done, else a maximal list of
 * usable mergeclauses (represented as a list of their restrictinfo nodes).
 * The list is ordered to match the pathkeys, as required for execution.
 */
/*
 * find_mergeclauses_for_outer_pathkeys - (中文)为外层路径的排序找到可用的
 * 归并连接子句
 *
 * 【作用】sort_inner_and_outer() 与 generate_mergejoin_paths() 调用本函数:
 * 给定外层路径的排序键列表,从 restrictinfos(已用 outer_is_left 标记外层
 * 侧)中找出与该排序匹配、可用于归并的子句,按路径键顺序返回最大可用集合。
 *
 * 【设计思想】一条归并子句匹配某路径键当且仅当其对应外层侧的等价类与该键
 * 的等价类相同(update_mergeclause_eclasses 先保证规范)。对外层连接可能有多
 * 条子句匹配同一个键(如 a.v1=b.v1 与 a.v1=b.v2 共享外层 EC),此时必须全
 * 部收下,否则可能无法形成合法计划(示例见源码);纯内连接场景一般只有一条。
 * 若某路径键无任何匹配子句,后面更低位键也不可能用得上,立即停止。结果可能
 * 产生内层侧的非规范键序,由 make_inner_pathkeys_for_merge() 与
 * create_mergejoin_plan() 处理。
 *
 * 【参数】
 *   root         —— PlannerInfo;
 *   pathkeys     —— 外层路径的排序键列表;
 *   restrictinfos —— 连接关系的可归并限制子句列表(无序)。
 * 【返回值】NIL(无法归并)或按路径键顺序排列的可用归并子句列表。
 */
List *
find_mergeclauses_for_outer_pathkeys(PlannerInfo *root,
									 List *pathkeys,
									 List *restrictinfos)
{
	List	   *mergeclauses = NIL;
	ListCell   *i;

	/* make sure we have eclasses cached in the clauses */
	foreach(i, restrictinfos)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(i);

		update_mergeclause_eclasses(root, rinfo);
	}

	foreach(i, pathkeys)
	{
		PathKey    *pathkey = (PathKey *) lfirst(i);
		EquivalenceClass *pathkey_ec = pathkey->pk_eclass;
		List	   *matched_restrictinfos = NIL;
		ListCell   *j;

		/*----------
		 * A mergejoin clause matches a pathkey if it has the same EC.
		 * If there are multiple matching clauses, take them all.  In plain
		 * inner-join scenarios we expect only one match, because
		 * equivalence-class processing will have removed any redundant
		 * mergeclauses.  However, in outer-join scenarios there might be
		 * multiple matches.  An example is
		 *
		 *	select * from a full join b
		 *		on a.v1 = b.v1 and a.v2 = b.v2 and a.v1 = b.v2;
		 *
		 * Given the pathkeys ({a.v1}, {a.v2}) it is okay to return all three
		 * clauses (in the order a.v1=b.v1, a.v1=b.v2, a.v2=b.v2) and indeed
		 * we *must* do so or we will be unable to form a valid plan.
		 *
		 * We expect that the given pathkeys list is canonical, which means
		 * no two members have the same EC, so it's not possible for this
		 * code to enter the same mergeclause into the result list twice.
		 *
		 * It's possible that multiple matching clauses might have different
		 * ECs on the other side, in which case the order we put them into our
		 * result makes a difference in the pathkeys required for the inner
		 * input rel.  However this routine hasn't got any info about which
		 * order would be best, so we don't worry about that.
		 *
		 * It's also possible that the selected mergejoin clauses produce
		 * a noncanonical ordering of pathkeys for the inner side, ie, we
		 * might select clauses that reference b.v1, b.v2, b.v1 in that
		 * order.  This is not harmful in itself, though it suggests that
		 * the clauses are partially redundant.  Since the alternative is
		 * to omit mergejoin clauses and thereby possibly fail to generate a
		 * plan altogether, we live with it.  make_inner_pathkeys_for_merge()
		 * has to delete duplicates when it constructs the inner pathkeys
		 * list, and we also have to deal with such cases specially in
		 * create_mergejoin_plan().
		 *----------
		 */
		foreach(j, restrictinfos)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(j);
			EquivalenceClass *clause_ec;

			clause_ec = rinfo->outer_is_left ?
				rinfo->left_ec : rinfo->right_ec;
			if (clause_ec == pathkey_ec)
				matched_restrictinfos = lappend(matched_restrictinfos, rinfo);
		}

		/*
		 * If we didn't find a mergeclause, we're done --- any additional
		 * sort-key positions in the pathkeys are useless.  (But we can still
		 * mergejoin if we found at least one mergeclause.)
		 */
		if (matched_restrictinfos == NIL)
			break;

		/*
		 * If we did find usable mergeclause(s) for this sort-key position,
		 * add them to result list.
		 */
		mergeclauses = list_concat(mergeclauses, matched_restrictinfos);
	}

	return mergeclauses;
}

/*
 * select_outer_pathkeys_for_merge
 *	  Builds a pathkey list representing a possible sort ordering
 *	  that can be used with the given mergeclauses.
 *
 * 'mergeclauses' is a list of RestrictInfos for mergejoin clauses
 *			that will be used in a merge join.
 * 'joinrel' is the join relation we are trying to construct.
 *
 * The restrictinfos must be marked (via outer_is_left) to show which side
 * of each clause is associated with the current outer path.  (See
 * select_mergejoin_clauses())
 *
 * Returns a pathkeys list that can be applied to the outer relation.
 *
 * Since we assume here that a sort is required, there is no particular use
 * in matching any available ordering of the outerrel.  (joinpath.c has an
 * entirely separate code path for considering sort-free mergejoins.)  Rather,
 * it's interesting to try to match, or match a prefix of the requested
 * query_pathkeys so that a second output sort may be avoided or an
 * incremental sort may be done instead.  We can get away with just a prefix
 * of the query_pathkeys when that prefix covers the entire join condition.
 * Failing that, we try to list "more popular" keys  (those with the most
 * unmatched EquivalenceClass peers) earlier, in hopes of making the resulting
 * ordering useful for as many higher-level mergejoins as possible.
 */
/*
 * select_outer_pathkeys_for_merge - (中文)为给定归并子句集构建一个可用的
 * 外层排序键列表
 *
 * 【作用】sort_inner_and_outer() 调用本函数,得到可用于这些归并子句的候选
 * 外层排序(之后每个键分别"打头"生成多种变体)。由于此处假设必须排序,
 * 重点不是匹配外层现有排序,而是尽量契合 query_pathkeys 以免二次排序。
 *
 * 【设计思想】
 * - 收集子句外层侧涉及的等价类(去重),并计算每个 EC 的"人气"得分:其
 *   成员中"非常量且尚未被 joinrel 连接"的个数,即未来仍可能与之归并的
 *   潜在伙伴数;
 * - 若 query_pathkeys 全部由这些 EC 构成:直接以 query_pathkeys 为起点
 *   (输出排序还能满足最终 ORDER BY),已用的 EC 标记为已发射(scores = -1);
 *   若只匹配了前缀且前缀恰好覆盖全部子句:直接返回该前缀(便于上层用增量
 *   排序);
 * - 否则把剩余 EC 按得分降序逐个补上,使用默认排序(COMPARE_LT, 非 NULLS
 *   FIRST),每补一个断言不冗余;
 * - 总复杂度很小,用线性选择而非 qsort。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   mergeclauses —— 将用于归并的子句列表;
 *   joinrel     —— 正在构造的连接关系。
 * 【返回值】可应用于外层关系的路径键列表(可为空)。
 */
List *
select_outer_pathkeys_for_merge(PlannerInfo *root,
								List *mergeclauses,
								RelOptInfo *joinrel)
{
	List	   *pathkeys = NIL;
	int			nClauses = list_length(mergeclauses);
	EquivalenceClass **ecs;
	int		   *scores;
	int			necs;
	ListCell   *lc;
	int			j;

	/* Might have no mergeclauses */
	if (nClauses == 0)
		return NIL;

	/*
	 * Make arrays of the ECs used by the mergeclauses (dropping any
	 * duplicates) and their "popularity" scores.
	 */
	ecs = (EquivalenceClass **) palloc(nClauses * sizeof(EquivalenceClass *));
	scores = (int *) palloc(nClauses * sizeof(int));
	necs = 0;

	foreach(lc, mergeclauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
		EquivalenceClass *oeclass;
		int			score;
		ListCell   *lc2;

		/* get the outer eclass */
		update_mergeclause_eclasses(root, rinfo);

		if (rinfo->outer_is_left)
			oeclass = rinfo->left_ec;
		else
			oeclass = rinfo->right_ec;

		/* reject duplicates */
		for (j = 0; j < necs; j++)
		{
			if (ecs[j] == oeclass)
				break;
		}
		if (j < necs)
			continue;

		/* compute score */
		score = 0;
		foreach(lc2, oeclass->ec_members)
		{
			EquivalenceMember *em = (EquivalenceMember *) lfirst(lc2);

			/* Child members should not exist in ec_members */
			Assert(!em->em_is_child);

			/* Potential future join partner? */
			if (!em->em_is_const &&
				!bms_overlap(em->em_relids, joinrel->relids))
				score++;
		}

		ecs[necs] = oeclass;
		scores[necs] = score;
		necs++;
	}

	/*
	 * Find out if we have all the ECs mentioned in query_pathkeys; if so we
	 * can generate a sort order that's also useful for final output. If we
	 * only have a prefix of the query_pathkeys, and that prefix is the entire
	 * join condition, then it's useful to use the prefix as the pathkeys as
	 * this increases the chances that an incremental sort will be able to be
	 * used by the upper planner.
	 */
	if (root->query_pathkeys)
	{
		int			matches = 0;

		foreach(lc, root->query_pathkeys)
		{
			PathKey    *query_pathkey = (PathKey *) lfirst(lc);
			EquivalenceClass *query_ec = query_pathkey->pk_eclass;

			for (j = 0; j < necs; j++)
			{
				if (ecs[j] == query_ec)
					break;		/* found match */
			}
			if (j >= necs)
				break;			/* didn't find match */

			matches++;
		}
		/* if we got to the end of the list, we have them all */
		if (lc == NULL)
		{
			/* copy query_pathkeys as starting point for our output */
			pathkeys = list_copy(root->query_pathkeys);
			/* mark their ECs as already-emitted */
			foreach(lc, root->query_pathkeys)
			{
				PathKey    *query_pathkey = (PathKey *) lfirst(lc);
				EquivalenceClass *query_ec = query_pathkey->pk_eclass;

				for (j = 0; j < necs; j++)
				{
					if (ecs[j] == query_ec)
					{
						scores[j] = -1;
						break;
					}
				}
			}
		}

		/*
		 * If we didn't match to all of the query_pathkeys, but did match to
		 * all of the join clauses then we'll make use of these as partially
		 * sorted input is better than nothing for the upper planner as it may
		 * lead to incremental sorts instead of full sorts.
		 */
		else if (matches == nClauses)
		{
			pathkeys = list_copy_head(root->query_pathkeys, matches);

			/* we have all of the join pathkeys, so nothing more to do */
			pfree(ecs);
			pfree(scores);

			return pathkeys;
		}
	}

	/*
	 * Add remaining ECs to the list in popularity order, using a default sort
	 * ordering.  (We could use qsort() here, but the list length is usually
	 * so small it's not worth it.)
	 */
	for (;;)
	{
		int			best_j;
		int			best_score;
		EquivalenceClass *ec;
		PathKey    *pathkey;

		best_j = 0;
		best_score = scores[0];
		for (j = 1; j < necs; j++)
		{
			if (scores[j] > best_score)
			{
				best_j = j;
				best_score = scores[j];
			}
		}
		if (best_score < 0)
			break;				/* all done */
		ec = ecs[best_j];
		scores[best_j] = -1;
		pathkey = make_canonical_pathkey(root,
										 ec,
										 linitial_oid(ec->ec_opfamilies),
										 COMPARE_LT,
										 false);
		/* can't be redundant because no duplicate ECs */
		Assert(!pathkey_is_redundant(pathkey, pathkeys));
		pathkeys = lappend(pathkeys, pathkey);
	}

	pfree(ecs);
	pfree(scores);

	return pathkeys;
}

/*
 * make_inner_pathkeys_for_merge
 *	  Builds a pathkey list representing the explicit sort order that
 *	  must be applied to an inner path to make it usable with the
 *	  given mergeclauses.
 *
 * 'mergeclauses' is a list of RestrictInfos for the mergejoin clauses
 *			that will be used in a merge join, in order.
 * 'outer_pathkeys' are the already-known canonical pathkeys for the outer
 *			side of the join.
 *
 * The restrictinfos must be marked (via outer_is_left) to show which side
 * of each clause is associated with the current outer path.  (See
 * select_mergejoin_clauses())
 *
 * Returns a pathkeys list that can be applied to the inner relation.
 *
 * Note that it is not this routine's job to decide whether sorting is
 * actually needed for a particular input path.  Assume a sort is necessary;
 * just make the keys, eh?
 */
/*
 * make_inner_pathkeys_for_merge - (中文)为归并连接计算内层路径所需的显式
 * 排序键
 *
 * 【作用】sort_inner_and_outer() 与 generate_mergejoin_paths() 在确定归并
 * 子句与内层排序需求后调用本函数:把归并子句序列换算成施加于内层路径的
 * 排序键列表。
 *
 * 【设计思想】外层排序键(lop,从 outer_pathkeys 依次取)与归并子句一一
 * 对应:每条子句的外层侧 EC 必须与当前/下一个外层路径键的 EC 一致(违反
 * 报错,用于调试);内层侧 EC 若与外层相同(等值子句,两侧同 EC),直接复用
 * 外层键;否则用同一算符族/方向/NULL 位置为内层 EC 构造规范键。多个子句
 * 引用同一内层 EC 时会产生冗余键,必须剔除——代价是输出键序可能与子句序
 * 不一致,给 create_mergejoin_plan() 增加一点复杂度,但换来规范键列表
 * (可与既有排序匹配)。
 *
 * 【参数】
 *   root           —— PlannerInfo;
 *   mergeclauses   —— 有序的归并子句列表;
 *   outer_pathkeys —— 外层已确定的规范路径键。
 * 【返回值】可施加于内层关系的路径键列表。
 */
List *
make_inner_pathkeys_for_merge(PlannerInfo *root,
							  List *mergeclauses,
							  List *outer_pathkeys)
{
	List	   *pathkeys = NIL;
	EquivalenceClass *lastoeclass;
	PathKey    *opathkey;
	ListCell   *lc;
	ListCell   *lop;

	lastoeclass = NULL;
	opathkey = NULL;
	lop = list_head(outer_pathkeys);

	foreach(lc, mergeclauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
		EquivalenceClass *oeclass;
		EquivalenceClass *ieclass;
		PathKey    *pathkey;

		update_mergeclause_eclasses(root, rinfo);

		if (rinfo->outer_is_left)
		{
			oeclass = rinfo->left_ec;
			ieclass = rinfo->right_ec;
		}
		else
		{
			oeclass = rinfo->right_ec;
			ieclass = rinfo->left_ec;
		}

		/* outer eclass should match current or next pathkeys */
		/* we check this carefully for debugging reasons */
		if (oeclass != lastoeclass)
		{
			if (!lop)
				elog(ERROR, "too few pathkeys for mergeclauses");
			opathkey = (PathKey *) lfirst(lop);
			lop = lnext(outer_pathkeys, lop);
			lastoeclass = opathkey->pk_eclass;
			if (oeclass != lastoeclass)
				elog(ERROR, "outer pathkeys do not match mergeclause");
		}

		/*
		 * Often, we'll have same EC on both sides, in which case the outer
		 * pathkey is also canonical for the inner side, and we can skip a
		 * useless search.
		 */
		if (ieclass == oeclass)
			pathkey = opathkey;
		else
			pathkey = make_canonical_pathkey(root,
											 ieclass,
											 opathkey->pk_opfamily,
											 opathkey->pk_cmptype,
											 opathkey->pk_nulls_first);

		/*
		 * Don't generate redundant pathkeys (which can happen if multiple
		 * mergeclauses refer to the same EC).  Because we do this, the output
		 * pathkey list isn't necessarily ordered like the mergeclauses, which
		 * complicates life for create_mergejoin_plan().  But if we didn't,
		 * we'd have a noncanonical sort key list, which would be bad; for one
		 * reason, it certainly wouldn't match any available sort order for
		 * the input relation.
		 */
		if (!pathkey_is_redundant(pathkey, pathkeys))
			pathkeys = lappend(pathkeys, pathkey);
	}

	return pathkeys;
}

/*
 * trim_mergeclauses_for_inner_pathkeys
 *	  This routine trims a list of mergeclauses to include just those that
 *	  work with a specified ordering for the join's inner relation.
 *
 * 'mergeclauses' is a list of RestrictInfos for mergejoin clauses for the
 *			join relation being formed, in an order known to work for the
 *			currently-considered sort ordering of the join's outer rel.
 * 'pathkeys' is a pathkeys list showing the ordering of an inner-rel path;
 *			it should be equal to, or a truncation of, the result of
 *			make_inner_pathkeys_for_merge for these mergeclauses.
 *
 * What we return will be a prefix of the given mergeclauses list.
 *
 * We need this logic because make_inner_pathkeys_for_merge's result isn't
 * necessarily in the same order as the mergeclauses.  That means that if we
 * consider an inner-rel pathkey list that is a truncation of that result,
 * we might need to drop mergeclauses even though they match a surviving inner
 * pathkey.  This happens when they are to the right of a mergeclause that
 * matches a removed inner pathkey.
 *
 * The mergeclauses must be marked (via outer_is_left) to show which side
 * of each clause is associated with the current outer path.  (See
 * select_mergejoin_clauses())
 */
/*
 * trim_mergeclauses_for_inner_pathkeys - (中文)把归并子句列表裁剪为与内层
 * 排序键匹配的前缀
 *
 * 【作用】generate_mergejoin_paths() 在考虑"只用一部分内层排序键"的截断
 * 方案时调用本函数:给定归并子句(按外层排序顺序)与内层路径键(应是
 * make_inner_pathkeys_for_merge 结果的截断),返回仍能使用的子句前缀。
 *
 * 【设计思想】由于 make_inner_pathkeys_for_merge 的输出键序不一定与子句
 * 顺序一致,当内层键列表被截断后,某些"匹配幸存内层键"的子句可能夹在
 * "匹配被删除键"的子句右侧,若不丢弃就会破坏归并的一致性。算法:同时遍历
 * 子句与内层键,子句的内层侧 EC 必须与当前内层键匹配;不匹配则前进到下一
 * 内层键,但若当前键尚无任何子句匹配则停止;匹配则收下并继续。返回的必为
 * 原子句列表的前缀。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   mergeclauses —— 有序归并子句列表;
 *   pathkeys    —— 内层路径的排序键(等于或截断自完整结果)。
 * 【返回值】可用子句列表(原列表前缀,可能为空)。
 */
List *
trim_mergeclauses_for_inner_pathkeys(PlannerInfo *root,
									 List *mergeclauses,
									 List *pathkeys)
{
	List	   *new_mergeclauses = NIL;
	PathKey    *pathkey;
	EquivalenceClass *pathkey_ec;
	bool		matched_pathkey;
	ListCell   *lip;
	ListCell   *i;

	/* No pathkeys => no mergeclauses (though we don't expect this case) */
	if (pathkeys == NIL)
		return NIL;
	/* Initialize to consider first pathkey */
	lip = list_head(pathkeys);
	pathkey = (PathKey *) lfirst(lip);
	pathkey_ec = pathkey->pk_eclass;
	lip = lnext(pathkeys, lip);
	matched_pathkey = false;

	/* Scan mergeclauses to see how many we can use */
	foreach(i, mergeclauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(i);
		EquivalenceClass *clause_ec;

		/* Assume we needn't do update_mergeclause_eclasses again here */

		/* Check clause's inner-rel EC against current pathkey */
		clause_ec = rinfo->outer_is_left ?
			rinfo->right_ec : rinfo->left_ec;

		/* If we don't have a match, attempt to advance to next pathkey */
		if (clause_ec != pathkey_ec)
		{
			/* If we had no clauses matching this inner pathkey, must stop */
			if (!matched_pathkey)
				break;

			/* Advance to next inner pathkey, if any */
			if (lip == NULL)
				break;
			pathkey = (PathKey *) lfirst(lip);
			pathkey_ec = pathkey->pk_eclass;
			lip = lnext(pathkeys, lip);
			matched_pathkey = false;
		}

		/* If mergeclause matches current inner pathkey, we can use it */
		if (clause_ec == pathkey_ec)
		{
			new_mergeclauses = lappend(new_mergeclauses, rinfo);
			matched_pathkey = true;
		}
		else
		{
			/* Else, no hope of adding any more mergeclauses */
			break;
		}
	}

	return new_mergeclauses;
}


/****************************************************************************
 *		PATHKEY USEFULNESS CHECKS
 *
 * We only want to remember as many of the pathkeys of a path as have some
 * potential use, either for subsequent mergejoins or for meeting the query's
 * requested output ordering.  This ensures that add_path() won't consider
 * a path to have a usefully different ordering unless it really is useful.
 * These routines check for usefulness of given pathkeys.
 ****************************************************************************/

/*
 * pathkeys_useful_for_merging
 *		Count the number of pathkeys that may be useful for mergejoins
 *		above the given relation.
 *
 * We consider a pathkey potentially useful if it corresponds to the merge
 * ordering of either side of any joinclause for the rel.  This might be
 * overoptimistic, since joinclauses that require different other relations
 * might never be usable at the same time, but trying to be exact is likely
 * to be more trouble than it's worth.
 *
 * To avoid doubling the number of mergejoin paths considered, we would like
 * to consider only one of the two scan directions (ASC or DESC) as useful
 * for merging for any given target column.  The choice is arbitrary unless
 * one of the directions happens to match an ORDER BY key, in which case
 * that direction should be preferred, in hopes of avoiding a final sort step.
 * right_merge_direction() implements this heuristic.
 */
/*
 * pathkeys_useful_for_merging - (中文)统计路径键中"对当前关系之上的归并
 * 连接可能有用"的个数
 *
 * 【作用】truncate_useless_pathkeys() 的最后一步判定:一个路径键若可用于
 * 本关系与更高层关系的归并连接,则值得保留。
 *
 * 【设计思想】逐键检查:
 * - 方向启发式:非首选方向(right_merge_direction 为 false)的键对归并无用,
 *   直接停止(其后键更无用);
 * - 匹配来源有二:一是键的等价类中存在尚未与 rel 连接的成员(rel 有
 *   eclass 连接,用 eclass_useful_for_merging);二是 rel 的 joininfo 中有
 *   mergejoinable 子句的左右 EC 之一与该键 EC 相同;
 * - 某键无任何匹配即停止并返回计数。允许乐观(可能高估),但精确判定过于
 *   复杂不划算。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   rel     —— 相关关系;
 *   pathkeys —— 待统计的路径键列表。
 * 【返回值】可用于归并的键个数(前缀计数)。
 */
static int
pathkeys_useful_for_merging(PlannerInfo *root, RelOptInfo *rel, List *pathkeys)
{
	int			useful = 0;
	ListCell   *i;

	foreach(i, pathkeys)
	{
		PathKey    *pathkey = (PathKey *) lfirst(i);
		bool		matched = false;
		ListCell   *j;

		/* If "wrong" direction, not useful for merging */
		if (!right_merge_direction(root, pathkey))
			break;

		/*
		 * First look into the EquivalenceClass of the pathkey, to see if
		 * there are any members not yet joined to the rel.  If so, it's
		 * surely possible to generate a mergejoin clause using them.
		 */
		if (rel->has_eclass_joins &&
			eclass_useful_for_merging(root, pathkey->pk_eclass, rel))
			matched = true;
		else
		{
			/*
			 * Otherwise search the rel's joininfo list, which contains
			 * non-EquivalenceClass-derivable join clauses that might
			 * nonetheless be mergejoinable.
			 */
			foreach(j, rel->joininfo)
			{
				RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(j);

				if (restrictinfo->mergeopfamilies == NIL)
					continue;
				update_mergeclause_eclasses(root, restrictinfo);

				if (pathkey->pk_eclass == restrictinfo->left_ec ||
					pathkey->pk_eclass == restrictinfo->right_ec)
				{
					matched = true;
					break;
				}
			}
		}

		/*
		 * If we didn't find a mergeclause, we're done --- any additional
		 * sort-key positions in the pathkeys are useless.  (But we can still
		 * mergejoin if we found at least one mergeclause.)
		 */
		if (matched)
			useful++;
		else
			break;
	}

	return useful;
}

/*
 * right_merge_direction
 *		Check whether the pathkey embodies the preferred sort direction
 *		for merging its target column.
 */
/*
 * right_merge_direction - (中文)判断路径键是否采用"目标列的归并首选排序
 * 方向"
 *
 * 【作用】pathkeys_useful_for_merging() 的方向过滤:为避免归并路径数量
 * 翻倍,对同一列只保留一个方向的键作为"可归并";方向的选择除了默认偏好,
 * 还优先迎合查询的 ORDER BY,以便省去最终排序。
 *
 * 【设计思想】在 root->query_pathkeys 中找与 pathkey 同等价类、同算符族
 * 的键:找到了则返回本键方向是否与之相同(忽略 nulls_first,排序仍可能要,
 * 但方向偏好二选一而已);没找到则偏好升序(COMPARE_LT)。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   pathkey —— 待判断的路径键。
 * 【返回值】true:该键方向是首选;false:非首选(对归并无用)。
 */
static bool
right_merge_direction(PlannerInfo *root, PathKey *pathkey)
{
	ListCell   *l;

	foreach(l, root->query_pathkeys)
	{
		PathKey    *query_pathkey = (PathKey *) lfirst(l);

		if (pathkey->pk_eclass == query_pathkey->pk_eclass &&
			pathkey->pk_opfamily == query_pathkey->pk_opfamily)
		{
			/*
			 * Found a matching query sort column.  Prefer this pathkey's
			 * direction iff it matches.  Note that we ignore pk_nulls_first,
			 * which means that a sort might be needed anyway ... but we still
			 * want to prefer only one of the two possible directions, and we
			 * might as well use this one.
			 */
			return (pathkey->pk_cmptype == query_pathkey->pk_cmptype);
		}
	}

	/* If no matching ORDER BY request, prefer the ASC direction */
	return (pathkey->pk_cmptype == COMPARE_LT);
}

/*
 * count_common_leading_pathkeys_ordered
 *		Returns the number of leading pathkeys which both lists have in common
 */
/*
 * count_common_leading_pathkeys_ordered - (中文)返回两个键列表共有的前缀键
 * 个数(有序匹配)
 *
 * 【作用】truncate_useless_pathkeys() 对 ORDER BY / WINDOW / SETOP 这类
 * "要求键顺序完全一致"的需求,统计路径排序与该需求键的公共前缀长度。
 *
 * 【设计思想】直接委托 pathkeys_count_contained_in() 得到前缀长度,并把
 * "包含关系是否成立"这一返回值忽略(调用方只关心前缀长度)。
 *
 * 【参数】
 *   keys1 —— 需求侧键列表;
 *   keys2 —— 路径排序键列表。
 * 【返回值】二者共有的前导键个数。
 */
static int
count_common_leading_pathkeys_ordered(List *keys1, List *keys2)
{
	int			ncommon;

	(void) pathkeys_count_contained_in(keys1, keys2, &ncommon);

	return ncommon;
}

/*
 * count_common_leading_pathkeys_unordered
 *		Returns the number of leading PathKeys in 'keys2' which exist in
 *		'keys1'.
 */
/*
 * count_common_leading_pathkeys_unordered - (中文)返回 keys2 的前缀中、
 * 存在于 keys1(顺序无关)的键个数
 *
 * 【作用】truncate_useless_pathkeys() 对 GROUP BY / DISTINCT 这类"只要键
 * 集合满足、不要求顺序一致"的需求,统计路径排序中能被分组/去重直接利用的
 * 键数。
 *
 * 【设计思想】keys1 为空时直接返回 0(无意义);否则逐元素遍历 keys2,若某
 * 键不在 keys1 中(list_member_ptr 指针查找)立即停止,否则计数加一——即
 * 返回 keys2 中"连续位于 keys1 集合内"的前缀长度。
 *
 * 【参数】
 *   keys1 —— 需求键集合(顺序无关);
 *   keys2 —— 路径排序键列表。
 * 【返回值】keys2 前导中属于 keys1 的键个数。
 */
static int
count_common_leading_pathkeys_unordered(List *keys1, List *keys2)
{
	int			ncommon = 0;

	/* No point in searching keys2 when keys1 is empty */
	if (keys1 == NIL)
		return 0;

	/* walk keys2 and search for matching PathKeys in keys1 */
	foreach_node(PathKey, pathkey, keys2)
	{
		/*
		 * return the number of matches so far as soon as keys1 doesn't
		 * contain the given keys2 key.
		 */
		if (!list_member_ptr(keys1, pathkey))
			break;

		ncommon++;
	}

	return ncommon;
}

/*
 * truncate_useless_pathkeys
 *		Shorten the given PathKey List to just the useful PathKeys.  If all
 *		PathKeys are useful, return the input List, otherwise return a new
 *		List containing only the useful PathKeys.
 */
/*
 * truncate_useless_pathkeys - (中文)把路径键列表裁剪到只保留"有用"的部分
 *
 * 【作用】路径创建(如 build_join_pathkeys、索引扫描路径)后调用本函数,去掉
 * 对任何需求(排序、窗口、集合运算、分组、去重、高层归并)都用不上的尾部键。
 * 它保证 add_path() 不会因为两条路径"排序不同但差异毫无用处"而把两条都
 * 保留。
 *
 * 【设计思想】计算有用键数 nuseful,按需求分三类累加取最大:
 * - 顺序敏感需求(sort/window/setop):用 count_common_leading_pathkeys_
 *   ordered() 与 root->sort_pathkeys / window_pathkeys / setop_pathkeys
 *   求公共前缀长;
 * - 顺序不敏感需求(group/distinct):用 unordered 版本与 root->group_pathkeys
 *   / distinct_pathkeys 求"集合内前导键数";
 * - 归并需求:pathkeys_useful_for_merging()(最贵,最后做)。
 * 任一步发现 nuseful 已等于总长即短路返回原列表。最后若全部有用返回原
 * 列表,否则 list_copy_head() 返回前 nuseful 个(不原地破坏输入)。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   rel     —— 相关关系(供归并有用性判断);
 *   pathkeys —— 待裁剪的路径键列表。
 * 【返回值】裁剪后的路径键列表(可能仍是原列表)。
 */
List *
truncate_useless_pathkeys(PlannerInfo *root,
						  RelOptInfo *rel,
						  List *pathkeys)
{
	int			nuseful;
	int			nuseful2;
	int			ntotal = list_length(pathkeys);

	/*
	 * Here we determine how many items in 'pathkeys' might be useful for
	 * various Path sort ordering requirements the planner has.  Operations
	 * such as ORDER BY require a Path's pathkeys to match the PathKeys of the
	 * ORDER BY in the same order, however operations such as GROUP BY and
	 * DISTINCT are less critical as a Unique or GroupAggregate only need to
	 * care that all PathKeys exist in their subpath, and don't need to care
	 * if they're in the same order as the clause in the query.
	 */
	nuseful = count_common_leading_pathkeys_ordered(root->sort_pathkeys,
													pathkeys);

	/* Short-circuit at any point we discover *all* pathkeys are useful */
	if (nuseful == ntotal)
		return pathkeys;

	nuseful2 = count_common_leading_pathkeys_ordered(root->window_pathkeys,
													 pathkeys);
	if (nuseful2 == ntotal)
		return pathkeys;

	nuseful = Max(nuseful, nuseful2);
	nuseful2 = count_common_leading_pathkeys_ordered(root->setop_pathkeys,
													 pathkeys);
	if (nuseful2 == ntotal)
		return pathkeys;

	nuseful = Max(nuseful, nuseful2);

	/*
	 * Check if these pathkeys are useful for GROUP BY or DISTINCT.  The order
	 * of the pathkeys does not matter here as Unique and GroupAggregate for
	 * these operations can take advantage of Paths presorted by any of the
	 * GROUP BY/DISTINCT pathkeys.
	 */
	nuseful2 = count_common_leading_pathkeys_unordered(root->group_pathkeys,
													   pathkeys);
	if (nuseful2 == ntotal)
		return pathkeys;

	nuseful = Max(nuseful, nuseful2);
	nuseful2 = count_common_leading_pathkeys_unordered(root->distinct_pathkeys,
													   pathkeys);

	if (nuseful2 == ntotal)
		return pathkeys;

	nuseful = Max(nuseful, nuseful2);

	/*
	 * Finally, check how many PathKeys might be useful for Merge Joins.  This
	 * is a bit more expensive, so do it last and only if we've not figured
	 * out that all the pathkeys are useful already.
	 */
	nuseful2 = pathkeys_useful_for_merging(root, rel, pathkeys);
	nuseful = Max(nuseful, nuseful2);

	/*
	 * Note: not safe to modify input list destructively, but we can avoid
	 * copying the list if we're not actually going to change it
	 */
	if (nuseful == ntotal)
		return pathkeys;
	else
		return list_copy_head(pathkeys, nuseful);
}

/*
 * has_useful_pathkeys
 *		Detect whether the specified rel could have any pathkeys that are
 *		useful according to truncate_useless_pathkeys().
 *
 * This is a cheap test that lets us skip building pathkeys at all in very
 * simple queries.  It's OK to err in the direction of returning "true" when
 * there really aren't any usable pathkeys, but erring in the other direction
 * is bad --- so keep this in sync with the routines above!
 *
 * We could make the test more complex, for example checking to see if any of
 * the joinclauses are really mergejoinable, but that likely wouldn't win
 * often enough to repay the extra cycles.  Queries with neither a join nor
 * a sort are reasonably common, though, so this much work seems worthwhile.
 */
/*
 * has_useful_pathkeys - (中文)快速检测指定关系是否可能拥有任何有用的路径键
 *
 * 【作用】make_one_rel() 等处的廉价预检:若返回 false,则完全不必为该关系
 * 构造路径键,省去在极简单查询中的开销。
 *
 * 【设计思想】两个判断即可:关系有 joininfo 或等价类连接(可能用排序做归并),
 * 或 root->query_pathkeys 非空(上层可能要求排序)。允许"误报 true"(多花点
 * 时间),但绝不能"误报 false";因此该测试必须与 truncate_useless_pathkeys
 * 的逻辑保持同步。不做更精细的归并子句可归并性检查——大多数查询既无连接
 * 也无排序,这份简单检查已值得。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 待检测关系。
 * 【返回值】true:可能有有用路径键,值得构造;false:确定无用。
 */
bool
has_useful_pathkeys(PlannerInfo *root, RelOptInfo *rel)
{
	if (rel->joininfo != NIL || rel->has_eclass_joins)
		return true;			/* might be able to use pathkeys for merging */
	if (root->query_pathkeys != NIL)
		return true;			/* the upper planner might need them */

	return false;				/* definitely useless */
}
