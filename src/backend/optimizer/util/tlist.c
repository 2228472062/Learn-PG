/*-------------------------------------------------------------------------
 *
 * tlist.c
 *	  Target list manipulation routines
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件提供目标列表(TargetList / TargetEntry)与 PathTarget 的全部操纵
 * 例程:在 tlist 中按表达式查找成员、合并去重、按 SortGroupRef 索引定位
 * 表达式、从 SortGroupClause 列表提取分组所需的算子/排序规则/列号,以及
 * 在 PathTarget 与 tlist 之间互相转换、维护 PathTarget 的表达式与
 * sortgrouprefs 标注,并把含集合返回函数(SRF)的 PathTarget 安全地切分到
 * 多层计划节点。
 *
 * 【核心数据结构】
 * - TargetEntry:tlist 的一个元素,包含 expr(表达式)、resno(输出列号)、
 *   resname(列名)、ressortgroupref(ORDER/GROUP BY 引用的索引)、resjunk
 *   (是否"垃圾"列,不影响最终输出)、resorigtbl/resorigcol(来源表列)。
 * - PathTarget:规划阶段比 tlist 更轻量的"目标"——只有 exprs 列表与可选的
 *   sortgrouprefs 数组,外加代价与输出宽度缓存、易变性标记。
 * - SortGroupClause:一条 ORDER/GROUP BY 子句,含 tleSortGroupRef(指向
 *   tlist 表达式)、sortop / eqop、hashable 等分组/排序元数据。
 * - split_pathtarget_item / split_pathtarget_context:SRF 切分时的辅助结构,
 *   用"表达式 + sortgroupref"配对保存,以保留表达式的身份。
 *
 * 【主要函数关系】
 * 前半部分是 tlist 通用工具:tlist_member / tlist_member_match_var 查找、
 * add_to_flat_tlist 去重追加、get_tlist_exprs / count_nonjunk_tlist_entries
 * 提取、tlist_same_exprs / tlist_same_datatypes / tlist_same_collations 比较、
 * apply_tlist_labeling 复贴标签、get_sortgroupref_tle 一族按 SortGroupRef
 * 定位;get_sortgroupref_clause 与 extract_grouping_ops/collations/cols 支撑
 * 分组计划;grouping_is_sortable / grouping_is_hashable 决定分组实现方式。
 * 后半部分围绕 PathTarget:make_pathtarget_from_tlist /
 * make_tlist_from_pathtarget / copy_pathtarget / create_empty_pathtarget /
 * add_column_to_pathtarget / add_new_column(s)_to_pathtarget /
 * apply_pathtarget_labeling_to_tlist 负责创建与修改;split_pathtarget_at_srfs
 * (及其 Grouping 变体)调用 split_pathtarget_at_srfs_extended,把含嵌套 SRF
 * 的 PathTarget 拆成"底层无 SRF + 逐层 ProjectSet"的多个 PathTarget,
 * 保证执行器每个 ProjectSet 节点只在顶层出现 SRF。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/tlist.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/tlist.h"
#include "rewrite/rewriteManip.h"


/*
 * Test if an expression node represents a SRF call.  Beware multiple eval!
 *
 * Please note that this is only meant for use in split_pathtarget_at_srfs();
 * if you use it anywhere else, your code is almost certainly wrong for SRFs
 * nested within expressions.  Use expression_returns_set() instead.
 */
#define IS_SRF_CALL(node) \
	((IsA(node, FuncExpr) && ((FuncExpr *) (node))->funcretset) || \
	 (IsA(node, OpExpr) && ((OpExpr *) (node))->opretset))

/*
 * Data structures for split_pathtarget_at_srfs().  To preserve the identity
 * of sortgroupref items even if they are textually equal(), what we track is
 * not just bare expressions but expressions plus their sortgroupref indexes.
 */
typedef struct
{
	Node	   *expr;			/* some subexpression of a PathTarget */
	Index		sortgroupref;	/* its sortgroupref, or 0 if none */
} split_pathtarget_item;

typedef struct
{
	PlannerInfo *root;
	bool		is_grouping_target; /* true if processing grouping target */
	/* This is a List of bare expressions: */
	List	   *input_target_exprs; /* exprs available from input */
	/* These are Lists of Lists of split_pathtarget_items: */
	List	   *level_srfs;		/* SRF exprs to evaluate at each level */
	List	   *level_input_vars;	/* input vars needed at each level */
	List	   *level_input_srfs;	/* input SRFs needed at each level */
	/* These are Lists of split_pathtarget_items: */
	List	   *current_input_vars; /* vars needed in current subexpr */
	List	   *current_input_srfs; /* SRFs needed in current subexpr */
	/* Auxiliary data for current split_pathtarget_walker traversal: */
	int			current_depth;	/* max SRF depth in current subexpr */
	Index		current_sgref;	/* current subexpr's sortgroupref, or 0 */
} split_pathtarget_context;

static void split_pathtarget_at_srfs_extended(PlannerInfo *root,
											  PathTarget *target,
											  PathTarget *input_target,
											  List **targets,
											  List **targets_contain_srfs,
											  bool is_grouping_target);
static bool split_pathtarget_walker(Node *node,
									split_pathtarget_context *context);
static void add_sp_item_to_pathtarget(PathTarget *target,
									  split_pathtarget_item *item);
static void add_sp_items_to_pathtarget(PathTarget *target, List *items);


/*****************************************************************************
 *		Target list creation and searching utilities
 *****************************************************************************/

/*
 * tlist_member
 *	  Finds the (first) member of the given tlist whose expression is
 *	  equal() to the given expression.  Result is NULL if no such member.
 */
/*
 * tlist_member - (中文)在目标列表中查找与给定表达式 equal() 的成员
 *
 * 【作用】线性扫描 targetlist,返回第一个 expr 与 node 结构相等
 * (equal(),即深度比较全部字段)的 TargetEntry;找不到返回 NULL。这是
 * tlist 最常见的查找原语,被 add_to_flat_tlist、apply_pathtarget_labeling_to_tlist
 * 等大量函数使用。
 *
 * 【设计思想】equal() 是全结构比较,所以"同一个逻辑列的不同位置 Var"
 * (例如来自不同 reltarget 的同一列)不会被认为是同一个成员;需要更宽松
 * 匹配的场合应改用 tlist_member_match_var。忽略 resname、resjunk 等标注。
 *
 * 【参数】
 *   node       —— 待匹配的表达式;
 *   targetlist —— 待扫描的目标列表。
 * 【返回值】命中的 TargetEntry,或 NULL。
 */
TargetEntry *
tlist_member(Expr *node, List *targetlist)
{
	ListCell   *temp;

	foreach(temp, targetlist)
	{
		TargetEntry *tlentry = (TargetEntry *) lfirst(temp);

		if (equal(node, tlentry->expr))
			return tlentry;
	}
	return NULL;
}

/*
 * tlist_member_match_var
 *	  Same as above, except that we match the provided Var on the basis
 *	  of varno/varattno/varlevelsup/vartype only, rather than full equal().
 *
 * This is needed in some cases where we can't be sure of an exact typmod
 * match.  For safety, though, we insist on vartype match.
 */
/*
 * tlist_member_match_var - (中文)按 Var 关键字段宽松匹配目标列表成员
 *
 * 【作用】tlist_member 的变体:只比较 varno、varattno、varlevelsup、
 * vartype 四项,忽略 typmod、collation 及其它标注,使匹配比 equal() 更宽松。
 * 返回第一个命中(表达式本身必须是 Var)的 TargetEntry,否则 NULL。
 *
 * 【设计思想】某些场景(SRF 内联展开后,对新返回类型的 Var 重新贴 sortgroupref
 * 标签)无法保证 typmod 完全一致,此时仍要求按 vartype 匹配以保证安全。
 * 非 Var 的 TLE 直接跳过。
 *
 * 【参数】
 *   var        —— 待匹配的 Var;
 *   targetlist —— 待扫描的目标列表。
 * 【返回值】命中的 TargetEntry,或 NULL。
 */
static TargetEntry *
tlist_member_match_var(Var *var, List *targetlist)
{
	ListCell   *temp;

	foreach(temp, targetlist)
	{
		TargetEntry *tlentry = (TargetEntry *) lfirst(temp);
		Var		   *tlvar = (Var *) tlentry->expr;

		if (!tlvar || !IsA(tlvar, Var))
			continue;
		if (var->varno == tlvar->varno &&
			var->varattno == tlvar->varattno &&
			var->varlevelsup == tlvar->varlevelsup &&
			var->vartype == tlvar->vartype)
			return tlentry;
	}
	return NULL;
}

/*
 * add_to_flat_tlist
 *		Add more items to a flattened tlist (if they're not already in it)
 *
 * 'tlist' is the flattened tlist
 * 'exprs' is a list of expressions (usually, but not necessarily, Vars)
 *
 * Returns the extended tlist.
 */
/*
 * add_to_flat_tlist - (中文)把一组表达式去重后追加到扁平目标列表
 *
 * 【作用】对 exprs 中每个表达式,若 tlist 中尚无 equal() 的成员,就复制后
 * 作为新的非 junk TargetEntry 追加(resno 顺延),返回扩展后的列表。用于
 * 维护"扁平化"的目标列表,如 pathkey 所需 Vars 的收集。
 *
 * 【设计思想】去重采用 tlist_member(equal() 全结构比较),保证同一列只出现
 * 一次;新条目 resname 为 NULL、resjunk 为 false。注意这里"扁平"指 tlist
 * 中每一项都是基本表达式(通常为 Var),与"让计划节点直接输出该表达式"
 * 的含义一致。
 *
 * 【参数】
 *   tlist —— 已有目标列表(会被就地扩展,返回新表头);
 *   exprs —— 待加入的表达式列表。
 * 【返回值】扩展后的目标列表。
 */
List *
add_to_flat_tlist(List *tlist, List *exprs)
{
	int			next_resno = list_length(tlist) + 1;
	ListCell   *lc;

	foreach(lc, exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);

		if (!tlist_member(expr, tlist))
		{
			TargetEntry *tle;

			tle = makeTargetEntry(copyObject(expr), /* copy needed?? */
								  next_resno++,
								  NULL,
								  false);
			tlist = lappend(tlist, tle);
		}
	}
	return tlist;
}


/*
 * get_tlist_exprs
 *		Get just the expression subtrees of a tlist
 *
 * Resjunk columns are ignored unless includeJunk is true
 */
/*
 * get_tlist_exprs - (中文)取目标列表的全部表达式
 *
 * 【作用】把 tlist 中各 TargetEntry 的 expr 收集成普通 List 返回。默认跳过
 * resjunk 列;includeJunk 为 true 时全部包含。常用于把 tlist 表达式交给
 * 通用表达式处理例程(如 pull_var_clause)。
 *
 * 【设计思想】纯投影操作:丢弃 TargetEntry 外壳,只保留表达式本身,方便
 * 用 List 工具直接操作。返回的新 List 与原 tlist 共享表达式节点,不做拷贝。
 *
 * 【参数】
 *   tlist       —— 目标列表;
 *   includeJunk —— 是否包含 resjunk 列。
 * 【返回值】表达式列表。
 */
List *
get_tlist_exprs(List *tlist, bool includeJunk)
{
	List	   *result = NIL;
	ListCell   *l;

	foreach(l, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (tle->resjunk && !includeJunk)
			continue;

		result = lappend(result, tle->expr);
	}
	return result;
}


/*
 * count_nonjunk_tlist_entries
 *		What it says ...
 */
/*
 * count_nonjunk_tlist_entries - (中文)统计非 junk 目标列表条目数
 *
 * 【作用】遍历 tlist,统计 resjunk 为 false 的条目个数,即"真正输出给用户
 * 的列数"。用于计算查询的可见列数(如检查聚合结果列数、生成 resno 等)。
 *
 * 【设计思想】junk 列(TID、tableoid、wholerow 等执行辅助列)不计入可见列。
 *
 * 【参数】tlist —— 目标列表。
 * 【返回值】非 junk 条目个数。
 */
int
count_nonjunk_tlist_entries(List *tlist)
{
	int			len = 0;
	ListCell   *l;

	foreach(l, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (!tle->resjunk)
			len++;
	}
	return len;
}


/*
 * tlist_same_exprs
 *		Check whether two target lists contain the same expressions
 *
 * Note: this function is used to decide whether it's safe to jam a new tlist
 * into a non-projection-capable plan node.  Obviously we can't do that unless
 * the node's tlist shows it already returns the column values we want.
 * However, we can ignore the TargetEntry attributes resname, ressortgroupref,
 * resorigtbl, resorigcol, and resjunk, because those are only labelings that
 * don't affect the row values computed by the node.  (Moreover, if we didn't
 * ignore them, we'd frequently fail to make the desired optimization, since
 * the planner tends to not bother to make resname etc. valid in intermediate
 * plan nodes.)  Note that on success, the caller must still jam the desired
 * tlist into the plan node, else it won't have the desired labeling fields.
 */
/*
 * tlist_same_exprs - (中文)判断两个目标列表是否含相同表达式序列
 *
 * 【作用】逐位置比较两个 tlist 的 expr 是否 equal(),且要求长度相等。用于
 * 判断"某个无投影能力的计划节点(如 Sort、Agg 之外的大多数执行器节点)
 * 是否已经计算出我们想要的那些列值",据此决定能否把新 tlist 直接塞给它。
 *
 * 【设计思想】只比较 expr,忽略 resname、ressortgroupref、resorigtbl、
 * resorigcol、resjunk 等"标注字段"——这些不影响节点计算出的行值,而且
 * 规划器在中间节点上通常不维护它们。命中后调用方仍须自行把想要的 tlist
 * 真正写入计划节点,以补上标注。
 *
 * 【参数】tlist1、tlist2 —— 两个目标列表。
 * 【返回值】表达式序列逐项相等返回 true。
 */
bool
tlist_same_exprs(List *tlist1, List *tlist2)
{
	ListCell   *lc1,
			   *lc2;

	if (list_length(tlist1) != list_length(tlist2))
		return false;			/* not same length, so can't match */

	forboth(lc1, tlist1, lc2, tlist2)
	{
		TargetEntry *tle1 = (TargetEntry *) lfirst(lc1);
		TargetEntry *tle2 = (TargetEntry *) lfirst(lc2);

		if (!equal(tle1->expr, tle2->expr))
			return false;
	}

	return true;
}


/*
 * Does tlist have same output datatypes as listed in colTypes?
 *
 * Resjunk columns are ignored if junkOK is true; otherwise presence of
 * a resjunk column will always cause a 'false' result.
 *
 * Note: currently no callers care about comparing typmods.
 */
/*
 * tlist_same_datatypes - (中文)判断 tlist 输出类型与给定类型列表一致
 *
 * 【作用】把 tlist 的可见(非 junk)列按顺序与 colTypes 中列出的 OID 逐一
 * 比较(exprType),并校验两者长度一致;junkOK 为 false 时遇到任何 junk 列
 * 直接判 false。用于判断 UNION/INSERT 等场景下输出列类型是否匹配声明。
 *
 * 【设计思想】跳过 junk 列(其类型与输出无关),仅对可见列推进 colTypes
 * 游标;末尾两者长度不同(任一方向)均判 false。不比较 typmod(调用者
 * 目前不关心)。
 *
 * 【参数】
 *   tlist   —— 目标列表;
 *   colTypes —— 期望的类型 OID 列表;
 *   junkOK  —— 是否容忍 junk 列。
 * 【返回值】类型序列一致返回 true。
 */
bool
tlist_same_datatypes(List *tlist, List *colTypes, bool junkOK)
{
	ListCell   *l;
	ListCell   *curColType = list_head(colTypes);

	foreach(l, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (tle->resjunk)
		{
			if (!junkOK)
				return false;
		}
		else
		{
			if (curColType == NULL)
				return false;	/* tlist longer than colTypes */
			if (exprType((Node *) tle->expr) != lfirst_oid(curColType))
				return false;
			curColType = lnext(colTypes, curColType);
		}
	}
	if (curColType != NULL)
		return false;			/* tlist shorter than colTypes */
	return true;
}

/*
 * Does tlist have same exposed collations as listed in colCollations?
 *
 * Identical logic to the above, but for collations.
 */
/*
 * tlist_same_collations - (中文)判断 tlist 输出排序规则与给定列表一致
 *
 * 【作用】tlist_same_datatypes 的排序规则版本:逐列比较可见列的
 * exprCollation 与 colCollations。用于 UNION 等场景校验输出列的排序规则
 * 兼容性。
 *
 * 【设计思想】逻辑与 tlist_same_datatypes 完全一致,只是比较对象换成
 * 排序规则 OID。
 *
 * 【参数】
 *   tlist         —— 目标列表;
 *   colCollations —— 期望的排序规则 OID 列表;
 *   junkOK        —— 是否容忍 junk 列。
 * 【返回值】排序规则序列一致返回 true。
 */
bool
tlist_same_collations(List *tlist, List *colCollations, bool junkOK)
{
	ListCell   *l;
	ListCell   *curColColl = list_head(colCollations);

	foreach(l, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (tle->resjunk)
		{
			if (!junkOK)
				return false;
		}
		else
		{
			if (curColColl == NULL)
				return false;	/* tlist longer than colCollations */
			if (exprCollation((Node *) tle->expr) != lfirst_oid(curColColl))
				return false;
			curColColl = lnext(colCollations, curColColl);
		}
	}
	if (curColColl != NULL)
		return false;			/* tlist shorter than colCollations */
	return true;
}

/*
 * apply_tlist_labeling
 *		Apply the TargetEntry labeling attributes of src_tlist to dest_tlist
 *
 * This is useful for reattaching column names etc to a plan's final output
 * targetlist.
 */
/*
 * apply_tlist_labeling - (中文)把源目标列表的标注字段贴到目标列表
 *
 * 【作用】逐位置把 src_tlist 中每个 TargetEntry 的 resname、ressortgroupref、
 * resorigtbl、resorigcol、resjunk 五个标注字段复制到 dest_tlist 对应条目。
 * 典型用途:createplan 阶段计划节点计算出了正确列值,但中间 tlist 没维护
 * 标注,最后用解析得到的 tlist 把列名等补回顶层输出。
 *
 * 【设计思想】只复制"标注",不碰 expr 与 resno(两者必须已经一致,用断言
 * 保证)。两个列表必须等长且 resno 逐项相等。
 *
 * 【参数】dest_tlist —— 接收标注的列表;src_tlist —— 标注来源列表。
 * 【返回值】无。
 */
void
apply_tlist_labeling(List *dest_tlist, List *src_tlist)
{
	ListCell   *ld,
			   *ls;

	Assert(list_length(dest_tlist) == list_length(src_tlist));
	forboth(ld, dest_tlist, ls, src_tlist)
	{
		TargetEntry *dest_tle = (TargetEntry *) lfirst(ld);
		TargetEntry *src_tle = (TargetEntry *) lfirst(ls);

		Assert(dest_tle->resno == src_tle->resno);
		dest_tle->resname = src_tle->resname;
		dest_tle->ressortgroupref = src_tle->ressortgroupref;
		dest_tle->resorigtbl = src_tle->resorigtbl;
		dest_tle->resorigcol = src_tle->resorigcol;
		dest_tle->resjunk = src_tle->resjunk;
	}
}


/*
 * get_sortgroupref_tle
 *		Find the targetlist entry matching the given SortGroupRef index,
 *		and return it.
 */
/*
 * get_sortgroupref_tle - (中文)按 SortGroupRef 索引查找目标列表条目
 *
 * 【作用】在 targetList 中查找 ressortgroupref 等于 sortref 的 TargetEntry
 * 并返回。SortGroupRef 是 ORDER/GROUP BY 子句通过 SortGroupClause 引用
 * tlist 表达式的"句柄"。找不到时抛错。
 *
 * 【设计思想】ressortgroupref 在同一查询的目标列表中唯一(规划器保证),
 * 线性扫描即可。这是 get_sortgroupclause_tle 等函数的基础。
 *
 * 【参数】
 *   sortref    —— 要查找的 SortGroupRef 索引;
 *   targetList —— 目标列表。
 * 【返回值】命中的 TargetEntry。
 */
TargetEntry *
get_sortgroupref_tle(Index sortref, List *targetList)
{
	ListCell   *l;

	foreach(l, targetList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (tle->ressortgroupref == sortref)
			return tle;
	}

	elog(ERROR, "ORDER/GROUP BY expression not found in targetlist");
	return NULL;				/* keep compiler quiet */
}

/*
 * get_sortgroupclause_tle
 *		Find the targetlist entry matching the given SortGroupClause
 *		by ressortgroupref, and return it.
 */
/*
 * get_sortgroupclause_tle - (中文)按 SortGroupClause 查找目标列表条目
 *
 * 【作用】取 sgClause->tleSortGroupRef 作为索引,调用
 * get_sortgroupref_tle 返回对应 TargetEntry。是"分组/排序子句 → 表达式"
 * 的标准桥梁。
 *
 * 【设计思想】仅做字段转发,封装"SortGroupClause 里哪个字段是 SortGroupRef"
 * 这一细节,避免调用方散落硬编码。
 *
 * 【参数】
 *   sgClause   —— 排序/分组子句;targetList —— 目标列表。
 * 【返回值】对应的 TargetEntry。
 */
TargetEntry *
get_sortgroupclause_tle(SortGroupClause *sgClause,
						List *targetList)
{
	return get_sortgroupref_tle(sgClause->tleSortGroupRef, targetList);
}

/*
 * get_sortgroupclause_expr
 *		Find the targetlist entry matching the given SortGroupClause
 *		by ressortgroupref, and return its expression.
 */
/*
 * get_sortgroupclause_expr - (中文)取 SortGroupClause 引用的表达式
 *
 * 【作用】由 SortGroupClause 定位其 TargetEntry,返回该条目的 expr。
 *
 * 【设计思想】get_sortgroupclause_tle 再剥一层壳,直接给出表达式节点,
 * 供 get_sortgrouplist_exprs 等批量处理使用。
 *
 * 【参数】
 *   sgClause   —— 排序/分组子句;targetList —— 目标列表。
 * 【返回值】对应的表达式节点(未拷贝)。
 */
Node *
get_sortgroupclause_expr(SortGroupClause *sgClause, List *targetList)
{
	TargetEntry *tle = get_sortgroupclause_tle(sgClause, targetList);

	return (Node *) tle->expr;
}

/*
 * get_sortgrouplist_exprs
 *		Given a list of SortGroupClauses, build a list
 *		of the referenced targetlist expressions.
 */
/*
 * get_sortgrouplist_exprs - (中文)把 SortGroupClause 列表映射为表达式列表
 *
 * 【作用】对 sgClauses 中每条 SortGroupClause 取其在 targetList 中引用的
 * 表达式,收集成列表返回。用于批量取出 ORDER/GROUP BY 涉及的表达式。
 *
 * 【设计思想】纯批量转发,顺序与 sgClauses 一致;表达式未拷贝。
 *
 * 【参数】
 *   sgClauses  —— 排序/分组子句列表;targetList —— 目标列表。
 * 【返回值】表达式列表。
 */
List *
get_sortgrouplist_exprs(List *sgClauses, List *targetList)
{
	List	   *result = NIL;
	ListCell   *l;

	foreach(l, sgClauses)
	{
		SortGroupClause *sortcl = (SortGroupClause *) lfirst(l);
		Node	   *sortexpr;

		sortexpr = get_sortgroupclause_expr(sortcl, targetList);
		result = lappend(result, sortexpr);
	}
	return result;
}


/*****************************************************************************
 *		Functions to extract data from a list of SortGroupClauses
 *
 * These don't really belong in tlist.c, but they are sort of related to the
 * functions just above, and they don't seem to deserve their own file.
 *****************************************************************************/

/*
 * get_sortgroupref_clause
 *		Find the SortGroupClause matching the given SortGroupRef index,
 *		and return it.
 */
/*
 * get_sortgroupref_clause - (中文)按 SortGroupRef 索引查找 SortGroupClause
 *
 * 【作用】在 clauses(一般为 parse->sortClause / groupClause)中查找
 * tleSortGroupRef 等于 sortref 的 SortGroupClause 并返回;找不到抛错。
 *
 * 【设计思想】与 get_sortgroupref_tle 对称:后者按 SortGroupRef 查 tlist,
 * 前者查 SortGroupClause 列表。SortGroupRef 是两个集合共享的键。
 *
 * 【参数】
 *   sortref —— 要查找的 SortGroupRef 索引;
 *   clauses —— SortGroupClause 列表。
 * 【返回值】命中的 SortGroupClause。
 */
SortGroupClause *
get_sortgroupref_clause(Index sortref, List *clauses)
{
	ListCell   *l;

	foreach(l, clauses)
	{
		SortGroupClause *cl = (SortGroupClause *) lfirst(l);

		if (cl->tleSortGroupRef == sortref)
			return cl;
	}

	elog(ERROR, "ORDER/GROUP BY expression not found in list");
	return NULL;				/* keep compiler quiet */
}

/*
 * get_sortgroupref_clause_noerr
 *		As above, but return NULL rather than throwing an error if not found.
 */
/*
 * get_sortgroupref_clause_noerr - (中文)按 SortGroupRef 查找子句(不抛错)
 *
 * 【作用】get_sortgroupref_clause 的无错误版本:找不到时返回 NULL 而非抛
 * 错,供"该引用可能不存在"的可选查找场景使用(如判断某表达式是否在分组
 * 子句里)。
 *
 * 【设计思想】唯一区别是省略 elog,其余逻辑相同。
 *
 * 【参数】
 *   sortref —— SortGroupRef 索引;clauses —— SortGroupClause 列表。
 * 【返回值】命中的 SortGroupClause,或 NULL。
 */
SortGroupClause *
get_sortgroupref_clause_noerr(Index sortref, List *clauses)
{
	ListCell   *l;

	foreach(l, clauses)
	{
		SortGroupClause *cl = (SortGroupClause *) lfirst(l);

		if (cl->tleSortGroupRef == sortref)
			return cl;
	}

	return NULL;
}

/*
 * extract_grouping_ops - make an array of the equality operator OIDs
 *		for a SortGroupClause list
 */
/*
 * extract_grouping_ops - (中文)提取分组等值算子 OID 数组
 *
 * 【作用】把 groupClause 中每条 SortGroupClause 的 eqop(等值算子 OID)
 * 收集成与列表顺序一致的 Oid 数组。供 hash 分组、去重等按等值语义实现
 * 的分组计划使用。
 *
 * 【设计思想】解析器保证每条 SortGroupClause 的 eqop 有效;数组长度等于
 * 列表长度。
 *
 * 【参数】groupClause —— SortGroupClause 列表。
 * 【返回值】palloc 分配的 Oid 数组,调用方负责 pfree。
 */
Oid *
extract_grouping_ops(List *groupClause)
{
	int			numCols = list_length(groupClause);
	int			colno = 0;
	Oid		   *groupOperators;
	ListCell   *glitem;

	groupOperators = palloc_array(Oid, numCols);

	foreach(glitem, groupClause)
	{
		SortGroupClause *groupcl = (SortGroupClause *) lfirst(glitem);

		groupOperators[colno] = groupcl->eqop;
		Assert(OidIsValid(groupOperators[colno]));
		colno++;
	}

	return groupOperators;
}

/*
 * extract_grouping_collations - make an array of the grouping column collations
 *		for a SortGroupClause list
 */
/*
 * extract_grouping_collations - (中文)提取分组列的排序规则数组
 *
 * 【作用】对 groupClause 的每条子句,找到其 tlist 表达式并取 exprCollation,
 * 组成 Oid 数组。用于 hash 分组时按列排序规则计算 hash。
 *
 * 【设计思想】通过 get_sortgroupclause_tle 把 SortGroupRef 解析成表达式,
 * 再求其排序规则;分组列必须具有确定排序规则才有意义。
 *
 * 【参数】
 *   groupClause —— SortGroupClause 列表;tlist —— 目标列表。
 * 【返回值】palloc 分配的排序规则 OID 数组。
 */
Oid *
extract_grouping_collations(List *groupClause, List *tlist)
{
	int			numCols = list_length(groupClause);
	int			colno = 0;
	Oid		   *grpCollations;
	ListCell   *glitem;

	grpCollations = palloc_array(Oid, numCols);

	foreach(glitem, groupClause)
	{
		SortGroupClause *groupcl = (SortGroupClause *) lfirst(glitem);
		TargetEntry *tle = get_sortgroupclause_tle(groupcl, tlist);

		grpCollations[colno++] = exprCollation((Node *) tle->expr);
	}

	return grpCollations;
}

/*
 * extract_grouping_cols - make an array of the grouping column resnos
 *		for a SortGroupClause list
 */
/*
 * extract_grouping_cols - (中文)提取分组列在输出中的 resno 数组
 *
 * 【作用】对 groupClause 的每条子句,返回其 tlist 条目的 resno(目标列表
 * 输出列号),组成 AttrNumber 数组。用于排序分组时告知执行器"按第几列
 * 分组/排序"。
 *
 * 【设计思想】resno 是分组列在计划节点输出中的位置,执行器的 sort/agg
 * 用这个数组定位按键列。
 *
 * 【参数】
 *   groupClause —— SortGroupClause 列表;tlist —— 目标列表。
 * 【返回值】palloc 分配的 resno 数组。
 */
AttrNumber *
extract_grouping_cols(List *groupClause, List *tlist)
{
	AttrNumber *grpColIdx;
	int			numCols = list_length(groupClause);
	int			colno = 0;
	ListCell   *glitem;

	grpColIdx = palloc_array(AttrNumber, numCols);

	foreach(glitem, groupClause)
	{
		SortGroupClause *groupcl = (SortGroupClause *) lfirst(glitem);
		TargetEntry *tle = get_sortgroupclause_tle(groupcl, tlist);

		grpColIdx[colno++] = tle->resno;
	}

	return grpColIdx;
}

/*
 * grouping_is_sortable - is it possible to implement grouping list by sorting?
 *
 * This is easy since the parser will have included a sortop if one exists.
 */
/*
 * grouping_is_sortable - (中文)分组列表是否可排序实现
 *
 * 【作用】判断给定 groupClause 是否可用"排序 + 相邻相等判定"实现分组:
 * 每条 SortGroupClause 的 sortop 都必须有效。
 *
 * 【设计思想】解析器在存在可排序类型时已填好 sortop,这里只做全员检查。
 * 与 grouping_is_hashable 一起,由分组路径生成者选择实现方式(可排序优先
 * 于可哈希的决策在别处完成)。
 *
 * 【参数】groupClause —— SortGroupClause 列表。
 * 【返回值】全部可排序返回 true。
 */
bool
grouping_is_sortable(List *groupClause)
{
	ListCell   *glitem;

	foreach(glitem, groupClause)
	{
		SortGroupClause *groupcl = (SortGroupClause *) lfirst(glitem);

		if (!OidIsValid(groupcl->sortop))
			return false;
	}
	return true;
}

/*
 * grouping_is_hashable - is it possible to implement grouping list by hashing?
 *
 * We rely on the parser to have set the hashable flag correctly.
 */
/*
 * grouping_is_hashable - (中文)分组列表是否可哈希实现
 *
 * 【作用】判断给定 groupClause 是否可用哈希分组实现:每条 SortGroupClause
 * 的 hashable 标志都必须为 true。
 *
 * 【设计思想】直接依赖解析器设置的 hashable 标志(对分组列存在哈希算子
 * 的类型为 true)。
 *
 * 【参数】groupClause —— SortGroupClause 列表。
 * 【返回值】全部可哈希返回 true。
 */
bool
grouping_is_hashable(List *groupClause)
{
	ListCell   *glitem;

	foreach(glitem, groupClause)
	{
		SortGroupClause *groupcl = (SortGroupClause *) lfirst(glitem);

		if (!groupcl->hashable)
			return false;
	}
	return true;
}


/*****************************************************************************
 *		PathTarget manipulation functions
 *
 * PathTarget is a somewhat stripped-down version of a full targetlist; it
 * omits all the TargetEntry decoration except (optionally) sortgroupref data,
 * and it adds evaluation cost and output data width info.
 *****************************************************************************/

/*
 * make_pathtarget_from_tlist
 *	  Construct a PathTarget equivalent to the given targetlist.
 *
 * This leaves the cost and width fields as zeroes.  Most callers will want
 * to use create_pathtarget(), so as to get those set.
 */
/*
 * make_pathtarget_from_tlist - (中文)由目标列表构造 PathTarget
 *
 * 【作用】把 tlist 中每个 TargetEntry 的 expr 与其 ressortgroupref 分别
 * 填入新建 PathTarget 的 exprs 与 sortgrouprefs,并置 has_volatile_expr 为
 * 未知(惰性求值)。代价/宽度字段保留为 0,通常由调用方随后用
 * create_pathtarget(经 set_pathtarget_cost_width)补全。
 *
 * 【设计思想】PathTarget 是 tlist 的"轻量版",丢弃 resname 等标注,只保留
 * 表达式与 SortGroupRef;sortgrouprefs 是与 exprs 平行的 Index 数组,没有
 * SortGroupRef 的列记为 0。易变性标志初始为 VOLATILITY_UNKNOWN,首次
 * contain_volatile_functions 查询时再确定。
 *
 * 【参数】tlist —— 输入目标列表。
 * 【返回值】新建的 PathTarget(尚未计算代价/宽度)。
 */
PathTarget *
make_pathtarget_from_tlist(List *tlist)
{
	PathTarget *target = makeNode(PathTarget);
	int			i;
	ListCell   *lc;

	target->sortgrouprefs = (Index *) palloc(list_length(tlist) * sizeof(Index));

	i = 0;
	foreach(lc, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(lc);

		target->exprs = lappend(target->exprs, tle->expr);
		target->sortgrouprefs[i] = tle->ressortgroupref;
		i++;
	}

	/*
	 * Mark volatility as unknown.  The contain_volatile_functions function
	 * will determine if there are any volatile functions when called for the
	 * first time with this PathTarget.
	 */
	target->has_volatile_expr = VOLATILITY_UNKNOWN;

	return target;
}

/*
 * make_tlist_from_pathtarget
 *	  Construct a targetlist from a PathTarget.
 */
/*
 * make_tlist_from_pathtarget - (中文)由 PathTarget 构造目标列表
 *
 * 【作用】把 PathTarget 的 exprs 逐个包成 TargetEntry(依次 resno、resname
 * 为空、非 junk),并把 sortgrouprefs 中的标注写回 ressortgroupref,返回新
 * tlist。是 make_pathtarget_from_tlist 的逆操作,常用于计划节点创建阶段把
 * PathTarget 还原成执行器可用的 tlist。
 *
 * 【设计思想】PathTarget 省略的字段(resname、resorigtbl 等)在构造的
 * TargetEntry 中取默认值;只有 SortGroupRef 这一标注被保留,因为它影响
 * 执行器对排序/分组输出的识别。
 *
 * 【参数】target —— 输入 PathTarget。
 * 【返回值】新建的目标列表。
 */
List *
make_tlist_from_pathtarget(PathTarget *target)
{
	List	   *tlist = NIL;
	int			i;
	ListCell   *lc;

	i = 0;
	foreach(lc, target->exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);
		TargetEntry *tle;

		tle = makeTargetEntry(expr,
							  i + 1,
							  NULL,
							  false);
		if (target->sortgrouprefs)
			tle->ressortgroupref = target->sortgrouprefs[i];
		tlist = lappend(tlist, tle);
		i++;
	}

	return tlist;
}

/*
 * copy_pathtarget
 *	  Copy a PathTarget.
 *
 * The new PathTarget has its own exprs List, but shares the underlying
 * target expression trees with the old one.
 */
/*
 * copy_pathtarget - (中文)浅拷贝 PathTarget
 *
 * 【作用】复制一个 PathTarget:标量字段整体拷贝,exprs 列表为新的 List 但
 * 共享底层表达式节点,sortgrouprefs 数组按需复制。
 *
 * 【设计思想】路径生成中常需要一份"内容相同但可独立修改 List 结构"的
 * PathTarget;表达式树本身不被修改,故可共享以省内存。
 *
 * 【参数】src —— 源 PathTarget。
 * 【返回值】拷贝后的 PathTarget。
 */
PathTarget *
copy_pathtarget(PathTarget *src)
{
	PathTarget *dst = makeNode(PathTarget);

	/* Copy scalar fields */
	memcpy(dst, src, sizeof(PathTarget));
	/* Shallow-copy the expression list */
	dst->exprs = list_copy(src->exprs);
	/* Duplicate sortgrouprefs if any (if not, the memcpy handled this) */
	if (src->sortgrouprefs)
	{
		Size		nbytes = list_length(src->exprs) * sizeof(Index);

		dst->sortgrouprefs = (Index *) palloc(nbytes);
		memcpy(dst->sortgrouprefs, src->sortgrouprefs, nbytes);
	}
	return dst;
}

/*
 * create_empty_pathtarget
 *	  Create an empty (zero columns, zero cost) PathTarget.
 */
/*
 * create_empty_pathtarget - (中文)创建空 PathTarget
 *
 * 【作用】返回一个零列、零代价的 PathTarget(makeNode 的默认字段)。供
 * "逐步加列"的构造场景及 SRF 切分产生中间目标时使用。
 *
 * 【设计思想】封装 makeNode,避免调用方硬编码节点类型并给语义命名。
 *
 * 【参数】无。
 * 【返回值】新建的空 PathTarget。
 */
PathTarget *
create_empty_pathtarget(void)
{
	/* This is easy, but we don't want callers to hard-wire this ... */
	return makeNode(PathTarget);
}

/*
 * add_column_to_pathtarget
 *		Append a target column to the PathTarget.
 *
 * As with make_pathtarget_from_tlist, we leave it to the caller to update
 * the cost and width fields.
 */
/*
 * add_column_to_pathtarget - (中文)向 PathTarget 追加一列
 *
 * 【作用】把 expr 追加到 target 的 exprs 末尾,并按 sortgroupref 同步维护
 * sortgrouprefs 数组(原来没有该数组时惰性创建)。代价/宽度由调用方负责
 * 后续更新。
 *
 * 【设计思想】sortgrouprefs 数组保持"与 exprs 平行"的不变量:数组可能尚未
 * 分配(全 0 语义),此时若新增列的 sortgroupref 为 0 则不必分配;非 0 则用
 * palloc0 补齐历史列(历史列标 0)。追加后若易变性标记曾为 NOVOLATILE,需
 * 复位为 UNKNOWN——新增表达式可能含易变函数,统一交给
 * contain_volatile_functions 重新判定,避免逻辑分散。
 *
 * 【参数】
 *   target       —— 目标 PathTarget;
 *   expr         —— 要追加的表达式;
 *   sortgroupref —— 该列的 SortGroupRef(无则 0)。
 * 【返回值】无。
 */
void
add_column_to_pathtarget(PathTarget *target, Expr *expr, Index sortgroupref)
{
	/* Updating the exprs list is easy ... */
	target->exprs = lappend(target->exprs, expr);
	/* ... the sortgroupref data, a bit less so */
	if (target->sortgrouprefs)
	{
		int			nexprs = list_length(target->exprs);

		/* This might look inefficient, but actually it's usually cheap */
		target->sortgrouprefs = (Index *)
			repalloc(target->sortgrouprefs, nexprs * sizeof(Index));
		target->sortgrouprefs[nexprs - 1] = sortgroupref;
	}
	else if (sortgroupref)
	{
		/* Adding sortgroupref labeling to a previously unlabeled target */
		int			nexprs = list_length(target->exprs);

		target->sortgrouprefs = (Index *) palloc0(nexprs * sizeof(Index));
		target->sortgrouprefs[nexprs - 1] = sortgroupref;
	}

	/*
	 * Reset has_volatile_expr to UNKNOWN.  We just leave it up to
	 * contain_volatile_functions to set this properly again.  Technically we
	 * could save some effort here and just check the new Expr, but it seems
	 * better to keep the logic for setting this flag in one location rather
	 * than duplicating the logic here.
	 */
	if (target->has_volatile_expr == VOLATILITY_NOVOLATILE)
		target->has_volatile_expr = VOLATILITY_UNKNOWN;
}

/*
 * add_new_column_to_pathtarget
 *		Append a target column to the PathTarget, but only if it's not
 *		equal() to any pre-existing target expression.
 *
 * The caller cannot specify a sortgroupref, since it would be unclear how
 * to merge that with a pre-existing column.
 *
 * As with make_pathtarget_from_tlist, we leave it to the caller to update
 * the cost and width fields.
 */
/*
 * add_new_column_to_pathtarget - (中文)去重后追加一列到 PathTarget
 *
 * 【作用】若 target 中尚无与 expr equal() 的列,则调用 add_column_to_pathtarget
 * 追加(sortgroupref 固定为 0)。用于避免重复列。
 *
 * 【设计思想】与 add_column_to_pathtarget 相比只多一次 list_member 去重;
 * 因为可能合并进已有列,调用方无法指定 sortgroupref(冲突语义不明),故
 * 该参数被省略。
 *
 * 【参数】
 *   target —— 目标 PathTarget;expr —— 待加入的表达式。
 * 【返回值】无。
 */
void
add_new_column_to_pathtarget(PathTarget *target, Expr *expr)
{
	if (!list_member(target->exprs, expr))
		add_column_to_pathtarget(target, expr, 0);
}

/*
 * add_new_columns_to_pathtarget
 *		Apply add_new_column_to_pathtarget() for each element of the list.
 */
/*
 * add_new_columns_to_pathtarget - (中文)批量去重追加列到 PathTarget
 *
 * 【作用】对 exprs 中每个表达式逐一调用 add_new_column_to_pathtarget。
 *
 * 【设计思想】纯批量转发;逐个去重,与"整体去重"结果一致。
 *
 * 【参数】
 *   target —— 目标 PathTarget;exprs —— 待加入的表达式列表。
 * 【返回值】无。
 */
void
add_new_columns_to_pathtarget(PathTarget *target, List *exprs)
{
	ListCell   *lc;

	foreach(lc, exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);

		add_new_column_to_pathtarget(target, expr);
	}
}

/*
 * apply_pathtarget_labeling_to_tlist
 *		Apply any sortgrouprefs in the PathTarget to matching tlist entries
 *
 * Here, we do not assume that the tlist entries are one-for-one with the
 * PathTarget.  The intended use of this function is to deal with cases
 * where createplan.c has decided to use some other tlist and we have
 * to identify what matches exist.
 */
/*
 * apply_pathtarget_labeling_to_tlist - (中文)把 PathTarget 的 SortGroupRef 标注贴到 tlist
 *
 * 【作用】把 PathTarget 中每列的 sortgroupref 按表达式匹配写回到 tlist 的
 * 对应 TargetEntry.ressortgroupref。不要求两者一一对应:在 tlist 里逐个
 * 表达式查找命中。用于 createplan 决定采用其它 tlist、需重新贴标签的场景。
 *
 * 【设计思想】与 apply_tlist_labeling(按位置)不同,这里按 equal() 匹配
 * (Var 用 tlist_member_match_var 的宽松规则——允许因 SRF 内联导致 typmod
 * 变化)。命中后若该 TLE 已带不同标签则报错(一个输出列不能有两个分组
 * 语义);已带相同标签则幂等允许。
 *
 * 【参数】
 *   tlist  —— 待贴标签的目标列表;target —— SortGroupRef 来源的 PathTarget。
 * 【返回值】无。
 */
void
apply_pathtarget_labeling_to_tlist(List *tlist, PathTarget *target)
{
	int			i;
	ListCell   *lc;

	/* Nothing to do if PathTarget has no sortgrouprefs data */
	if (target->sortgrouprefs == NULL)
		return;

	i = 0;
	foreach(lc, target->exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);
		TargetEntry *tle;

		if (target->sortgrouprefs[i])
		{
			/*
			 * For Vars, use tlist_member_match_var's weakened matching rule;
			 * this allows us to deal with some cases where a set-returning
			 * function has been inlined, so that we now have more knowledge
			 * about what it returns than we did when the original Var was
			 * created.  Otherwise, use regular equal() to find the matching
			 * TLE.  (In current usage, only the Var case is actually needed;
			 * but it seems best to have sane behavior here for non-Vars too.)
			 */
			if (expr && IsA(expr, Var))
				tle = tlist_member_match_var((Var *) expr, tlist);
			else
				tle = tlist_member(expr, tlist);

			/*
			 * Complain if noplace for the sortgrouprefs label, or if we'd
			 * have to label a column twice.  (The case where it already has
			 * the desired label probably can't happen, but we may as well
			 * allow for it.)
			 */
			if (!tle)
				elog(ERROR, "ORDER/GROUP BY expression not found in targetlist");
			if (tle->ressortgroupref != 0 &&
				tle->ressortgroupref != target->sortgrouprefs[i])
				elog(ERROR, "targetlist item has multiple sortgroupref labels");

			tle->ressortgroupref = target->sortgrouprefs[i];
		}
		i++;
	}
}

/*
 * split_pathtarget_at_srfs
 *		Split given PathTarget into multiple levels to position SRFs safely,
 *		performing exact matching against input_target.
 *
 * This is a wrapper for split_pathtarget_at_srfs_extended() that is used when
 * both targets are on the same side of the grouping boundary (i.e., both are
 * pre-grouping or both are post-grouping).  In this case, no special handling
 * for the grouping nulling bit is required.
 *
 * See split_pathtarget_at_srfs_extended() for more details.
 */
/*
 * split_pathtarget_at_srfs - (中文)切分含 SRF 的 PathTarget 到多层计划
 *
 * 【作用】split_pathtarget_at_srfs_extended 的包装:用于"target 与
 * input_target 在分组边界同一侧"(同属分组前或同属分组后)的情形,此时
 * 无需处理分组引入的 nullingrel 位,is_grouping_target 传 false。
 *
 * 【设计思想】见 split_pathtarget_at_srfs_extended 的详细说明;本函数把
 * "是否跨分组边界"这一复杂开关固定为否。
 *
 * 【参数】
 *   root       —— 规划上下文;
 *   target     —— 需切分的 PathTarget;
 *   input_target —— 下层已可得的表达式(可为 NULL);
 *   targets   —— 输出:按求值顺序的 PathTarget 列表(最后一个是原 target);
 *   targets_contain_srfs —— 输出:与 targets 平行的"是否含可求值 SRF"标志。
 * 【返回值】无。
 */
void
split_pathtarget_at_srfs(PlannerInfo *root,
						 PathTarget *target, PathTarget *input_target,
						 List **targets, List **targets_contain_srfs)
{
	split_pathtarget_at_srfs_extended(root, target, input_target,
									  targets, targets_contain_srfs,
									  false);
}

/*
 * split_pathtarget_at_srfs_grouping
 *		Split given PathTarget into multiple levels to position SRFs safely,
 *		ignoring the grouping nulling bit when matching against input_target.
 *
 * This variant is used when the targets cross the grouping boundary (i.e.,
 * target is post-grouping while input_target is pre-grouping).  In this case,
 * we need to ignore the grouping nulling bit when checking for expression
 * availability to avoid incorrectly re-evaluating SRFs that have already been
 * computed in input_target.
 *
 * See split_pathtarget_at_srfs_extended() for more details.
 */
/*
 * split_pathtarget_at_srfs_grouping - (中文)跨分组边界切分含 SRF 的 PathTarget
 *
 * 【作用】split_pathtarget_at_srfs_extended 的包装:用于"target 在分组后、
 * input_target 在分组前"(跨分组边界)的情形。此时 target 中的表达式可能
 * 带分组引入的 nullingrel 位,而 input_target 中没有,直接匹配会误判为
 * "不可得"而重复求值 SRF,因此必须忽略这些位(is_grouping_target = true)。
 *
 * 【设计思想】见 split_pathtarget_at_srfs_extended 与 split_pathtarget_walker
 * 中 remove_nulling_relids 的处理。
 *
 * 【参数】
 *   root       —— 规划上下文;
 *   target     —— 分组后的 PathTarget;input_target —— 分组前的下层表达式;
 *   targets   —— 输出 PathTarget 列表;targets_contain_srfs —— 平行标志列表。
 * 【返回值】无。
 */
void
split_pathtarget_at_srfs_grouping(PlannerInfo *root,
								  PathTarget *target, PathTarget *input_target,
								  List **targets, List **targets_contain_srfs)
{
	split_pathtarget_at_srfs_extended(root, target, input_target,
									  targets, targets_contain_srfs,
									  true);
}

/*
 * split_pathtarget_at_srfs_extended
 *		Split given PathTarget into multiple levels to position SRFs safely
 *
 * The executor can only handle set-returning functions that appear at the
 * top level of the targetlist of a ProjectSet plan node.  If we have any SRFs
 * that are not at top level, we need to split up the evaluation into multiple
 * plan levels in which each level satisfies this constraint.  This function
 * creates appropriate PathTarget(s) for each level.
 *
 * As an example, consider the tlist expression
 *		x + srf1(srf2(y + z))
 * This expression should appear as-is in the top PathTarget, but below that
 * we must have a PathTarget containing
 *		x, srf1(srf2(y + z))
 * and below that, another PathTarget containing
 *		x, srf2(y + z)
 * and below that, another PathTarget containing
 *		x, y, z
 * When these tlists are processed by setrefs.c, subexpressions that match
 * output expressions of the next lower tlist will be replaced by Vars,
 * so that what the executor gets are tlists looking like
 *		Var1 + Var2
 *		Var1, srf1(Var2)
 *		Var1, srf2(Var2 + Var3)
 *		x, y, z
 * which satisfy the desired property.
 *
 * Another example is
 *		srf1(x), srf2(srf3(y))
 * That must appear as-is in the top PathTarget, but below that we need
 *		srf1(x), srf3(y)
 * That is, each SRF must be computed at a level corresponding to the nesting
 * depth of SRFs within its arguments.
 *
 * In some cases, a SRF has already been evaluated in some previous plan level
 * and we shouldn't expand it again (that is, what we see in the target is
 * already meant as a reference to a lower subexpression).  So, don't expand
 * any tlist expressions that appear in input_target, if that's not NULL.
 *
 * This check requires extra care when processing the grouping target
 * (indicated by the is_grouping_target flag).  In this case input_target is
 * pre-grouping while target is post-grouping, so the latter may carry
 * nullingrels bits from the grouping step that are absent in the former.  We
 * must ignore those bits to correctly recognize that the tlist expressions are
 * available in input_target.
 *
 * It's also important that we preserve any sortgroupref annotation appearing
 * in the given target, especially on expressions matching input_target items.
 *
 * The outputs of this function are two parallel lists, one a list of
 * PathTargets and the other an integer list of bool flags indicating
 * whether the corresponding PathTarget contains any evaluable SRFs.
 * The lists are given in the order they'd need to be evaluated in, with
 * the "lowest" PathTarget first.  So the last list entry is always the
 * originally given PathTarget, and any entries before it indicate evaluation
 * levels that must be inserted below it.  The first list entry must not
 * contain any SRFs (other than ones duplicating input_target entries), since
 * it will typically be attached to a plan node that cannot evaluate SRFs.
 *
 * Note: using a list for the flags may seem like overkill, since there
 * are only a few possible patterns for which levels contain SRFs.
 * But this representation decouples callers from that knowledge.
 */
/*
 * split_pathtarget_at_srfs_extended - (中文)把含 SRF 的 PathTarget 拆成多层
 *
 * 【作用】实现"SRF 安全切分":执行器要求每个 ProjectSet 节点只能在其目标
 * 列表"顶层"求值 SRF。若 target 中含嵌套于标量表达式内部的 SRF,就把它
 * 拆成若干层 PathTarget——最底层不含 SRF(挂到普通计划节点,如 Result/
 * Scan),其上每层用 ProjectSet 求值一层 SRF,最顶层即原始 target。输出
 * targets 按求值顺序排列、与 targets_contain_srfs 平行。
 *
 * 【设计思想】核心思想:对每个表达式,先递归找出其中 SRF 的嵌套深度
 * (split_pathtarget_walker),一个"深度为 d 的 SRF 调用"必须在恰好第 d 层
 * 被求值,它的输入(普通 Var 或更浅的 SRF)必须在本层可用。实现上维护三
 * 个"按深度索引"的并行列表 level_srfs / level_input_vars / level_input_srfs,
 * 深度 0 恒为空(表示"底层计划节点不能求值 SRF");walker 每发现一个 SRF
 * 就把它按深度归档,并把其输入按深度记录。若干关键处理:
 * - 与 input_target 中已算过的表达式 equal() 的节点视为"输入 Var"而不再
 *   展开(避免重复求值,也保留其在 input_target 中的 sortgroupref 身份);
 * - 跨分组边界(is_grouping_target)时,匹配前用 remove_nulling_relids 去掉
 *   分组引入的 nullingrel 位,与 set_upper_references 的匹配逻辑对齐;
 * - 若最大深度 SRF 不在表达式顶层(表达式形如 x + srf(...)),还需要一个
 *   额外 Result 节点先算出该顶层标量(need_extra_projection),对应的第 0 层
 *   之后再加一层空 SRF 层;
 * - 构造各层 PathTarget 时,每一层要"传播"所有更深层需要的 Var 与已算
 *   SRF,底层(输入节点输出)用 set_pathtarget_cost_width 补代价与宽度。
 * 最后 target == input_target 或未发现 SRF 时快速返回单层。
 *
 * 【参数】
 *   root          —— 规划上下文;
 *   target        —— 需切分的 PathTarget;
 *   input_target  —— 下层已算表达式(可为 NULL);
 *   targets       —— 输出:求值顺序的 PathTarget 列表;
 *   targets_contain_srfs —— 输出:平行 bool 标志;
 *   is_grouping_target —— 是否跨分组边界(需要忽略分组 nullingrel 位)。
 * 【返回值】无。
 */
static void
split_pathtarget_at_srfs_extended(PlannerInfo *root,
								  PathTarget *target, PathTarget *input_target,
								  List **targets, List **targets_contain_srfs,
								  bool is_grouping_target)
{
	split_pathtarget_context context;
	int			max_depth;
	bool		need_extra_projection;
	List	   *prev_level_tlist;
	int			lci;
	ListCell   *lc,
			   *lc1,
			   *lc2,
			   *lc3;

	/*
	 * It's not unusual for planner.c to pass us two physically identical
	 * targets, in which case we can conclude without further ado that all
	 * expressions are available from the input.  (The logic below would
	 * arrive at the same conclusion, but much more tediously.)
	 */
	if (target == input_target)
	{
		*targets = list_make1(target);
		*targets_contain_srfs = list_make1_int(false);
		return;
	}

	/*
	 * Pass 'root', the is_grouping_target flag, and any input_target exprs
	 * down to split_pathtarget_walker().
	 */
	context.root = root;
	context.is_grouping_target = is_grouping_target;
	context.input_target_exprs = input_target ? input_target->exprs : NIL;

	/*
	 * Initialize with empty level-zero lists, and no levels after that.
	 * (Note: we could dispense with representing level zero explicitly, since
	 * it will never receive any SRFs, but then we'd have to special-case that
	 * level when we get to building result PathTargets.  Level zero describes
	 * the SRF-free PathTarget that will be given to the input plan node.)
	 */
	context.level_srfs = list_make1(NIL);
	context.level_input_vars = list_make1(NIL);
	context.level_input_srfs = list_make1(NIL);

	/* Initialize data we'll accumulate across all the target expressions */
	context.current_input_vars = NIL;
	context.current_input_srfs = NIL;
	max_depth = 0;
	need_extra_projection = false;

	/* Scan each expression in the PathTarget looking for SRFs */
	lci = 0;
	foreach(lc, target->exprs)
	{
		Node	   *node = (Node *) lfirst(lc);

		/* Tell split_pathtarget_walker about this expr's sortgroupref */
		context.current_sgref = get_pathtarget_sortgroupref(target, lci);
		lci++;

		/*
		 * Find all SRFs and Vars (and Var-like nodes) in this expression, and
		 * enter them into appropriate lists within the context struct.
		 */
		context.current_depth = 0;
		split_pathtarget_walker(node, &context);

		/* An expression containing no SRFs is of no further interest */
		if (context.current_depth == 0)
			continue;

		/*
		 * Track max SRF nesting depth over the whole PathTarget.  Also, if
		 * this expression establishes a new max depth, we no longer care
		 * whether previous expressions contained nested SRFs; we can handle
		 * any required projection for them in the final ProjectSet node.
		 */
		if (max_depth < context.current_depth)
		{
			max_depth = context.current_depth;
			need_extra_projection = false;
		}

		/*
		 * If any maximum-depth SRF is not at the top level of its expression,
		 * we'll need an extra Result node to compute the top-level scalar
		 * expression.
		 */
		if (max_depth == context.current_depth && !IS_SRF_CALL(node))
			need_extra_projection = true;
	}

	/*
	 * If we found no SRFs needing evaluation (maybe they were all present in
	 * input_target, or maybe they were all removed by const-simplification),
	 * then no ProjectSet is needed; fall out.
	 */
	if (max_depth == 0)
	{
		*targets = list_make1(target);
		*targets_contain_srfs = list_make1_int(false);
		return;
	}

	/*
	 * The Vars and SRF outputs needed at top level can be added to the last
	 * level_input lists if we don't need an extra projection step.  If we do
	 * need one, add a SRF-free level to the lists.
	 */
	if (need_extra_projection)
	{
		context.level_srfs = lappend(context.level_srfs, NIL);
		context.level_input_vars = lappend(context.level_input_vars,
										   context.current_input_vars);
		context.level_input_srfs = lappend(context.level_input_srfs,
										   context.current_input_srfs);
	}
	else
	{
		lc = list_nth_cell(context.level_input_vars, max_depth);
		lfirst(lc) = list_concat(lfirst(lc), context.current_input_vars);
		lc = list_nth_cell(context.level_input_srfs, max_depth);
		lfirst(lc) = list_concat(lfirst(lc), context.current_input_srfs);
	}

	/*
	 * Now construct the output PathTargets.  The original target can be used
	 * as-is for the last one, but we need to construct a new SRF-free target
	 * representing what the preceding plan node has to emit, as well as a
	 * target for each intermediate ProjectSet node.
	 */
	*targets = *targets_contain_srfs = NIL;
	prev_level_tlist = NIL;

	forthree(lc1, context.level_srfs,
			 lc2, context.level_input_vars,
			 lc3, context.level_input_srfs)
	{
		List	   *level_srfs = (List *) lfirst(lc1);
		PathTarget *ntarget;

		if (lnext(context.level_srfs, lc1) == NULL)
		{
			ntarget = target;
		}
		else
		{
			ntarget = create_empty_pathtarget();

			/*
			 * This target should actually evaluate any SRFs of the current
			 * level, and it needs to propagate forward any Vars needed by
			 * later levels, as well as SRFs computed earlier and needed by
			 * later levels.
			 */
			add_sp_items_to_pathtarget(ntarget, level_srfs);
			for_each_cell(lc, context.level_input_vars,
						  lnext(context.level_input_vars, lc2))
			{
				List	   *input_vars = (List *) lfirst(lc);

				add_sp_items_to_pathtarget(ntarget, input_vars);
			}
			for_each_cell(lc, context.level_input_srfs,
						  lnext(context.level_input_srfs, lc3))
			{
				List	   *input_srfs = (List *) lfirst(lc);
				ListCell   *lcx;

				foreach(lcx, input_srfs)
				{
					split_pathtarget_item *item = lfirst(lcx);

					if (list_member(prev_level_tlist, item->expr))
						add_sp_item_to_pathtarget(ntarget, item);
				}
			}
			set_pathtarget_cost_width(root, ntarget);
		}

		/*
		 * Add current target and does-it-compute-SRFs flag to output lists.
		 */
		*targets = lappend(*targets, ntarget);
		*targets_contain_srfs = lappend_int(*targets_contain_srfs,
											(level_srfs != NIL));

		/* Remember this level's output for next pass */
		prev_level_tlist = ntarget->exprs;
	}
}

/*
 * Recursively examine expressions for split_pathtarget_at_srfs.
 *
 * Note we make no effort here to prevent duplicate entries in the output
 * lists.  Duplicates will be gotten rid of later.
 */
/*
 * split_pathtarget_walker - (中文)递归分析表达式并归档 SRF 与输入 Var
 *
 * 【作用】split_pathtarget_at_srfs_extended 的表达式遍历器:递归扫描单个
 * 目标表达式,把其中出现的 SRF 调用按嵌套深度写入 context 的 level_srfs,
 * 把普通输入(Var/PHV/Aggref/GroupingFunc/WindowFunc 以及"input_target 中
 * 已有"的表达式)记入 current_input_vars / current_input_srfs。返回 true
 * 表示应中止遍历(本实现从不中止)。
 *
 * 【设计思想】按节点类别分流:
 * - 与 input_target 已算表达式匹配的节点:视为"输入",记录当前 subexpr 的
 *   sortgroupref(current_sgref)后不再深入——它已由下层算好(可能本身是
 *   SRF,但引用语义等同于 Var);
 * - Var / PlaceHolderVar / Aggref / GroupingFunc / WindowFunc:假定这些
 *   叶子状构造不含 SRF,记录为输入;
 * - IS_SRF_CALL(FuncExpr/OpExpr 且 funcretset/opretset):先递归分析其参数
 *   (把参数里的 SRF 与输入分别累计),本 SRF 的深度 = 参数最大深度 + 1;
 *   若深度超过已记录层数则补一层;把本 SRF 记入第 srf_depth 层的 level_srfs,
 *   把参数输入并入同层 input 列表;恢复并更新调用者上下文的输入与深度
 *   (本 SRF 对其外围表达式而言是"输入");
 * - 其余标量表达式:置 current_sgref = 0(子表达式不参与分组标注)后递归。
 * 跨分组边界时,先用 remove_nulling_relids 去掉分组 nullingrel 位再做匹配。
 *
 * 【参数】
 *   node    —— 当前节点;context —— 携带 level_srfs 等全部切分状态的上下文。
 * 【返回值】false(永不请求中止)。
 */
static bool
split_pathtarget_walker(Node *node, split_pathtarget_context *context)
{
	Node	   *sanitized_node = node;

	if (node == NULL)
		return false;

	/*
	 * If we are crossing the grouping boundary (post-grouping target vs
	 * pre-grouping input_target), we must ignore the grouping nulling bit to
	 * correctly check if the subexpression is available in input_target. This
	 * aligns with the matching logic in set_upper_references().
	 */
	if (context->is_grouping_target &&
		context->root->parse->hasGroupRTE &&
		context->root->parse->groupingSets != NIL)
	{
		sanitized_node =
			remove_nulling_relids(node,
								  bms_make_singleton(context->root->group_rtindex),
								  NULL);
	}

	/*
	 * A subexpression that matches an expression already computed in
	 * input_target can be treated like a Var (which indeed it will be after
	 * setrefs.c gets done with it), even if it's actually a SRF.  Record it
	 * as being needed for the current expression, and ignore any
	 * substructure.  (Note in particular that this preserves the identity of
	 * any expressions that appear as sortgrouprefs in input_target.)
	 */
	if (list_member(context->input_target_exprs, sanitized_node))
	{
		split_pathtarget_item *item = palloc_object(split_pathtarget_item);

		item->expr = node;
		item->sortgroupref = context->current_sgref;
		context->current_input_vars = lappend(context->current_input_vars,
											  item);
		return false;
	}

	/*
	 * Vars and Var-like constructs are expected to be gotten from the input,
	 * too.  We assume that these constructs cannot contain any SRFs (if one
	 * does, there will be an executor failure from a misplaced SRF).
	 */
	if (IsA(node, Var) ||
		IsA(node, PlaceHolderVar) ||
		IsA(node, Aggref) ||
		IsA(node, GroupingFunc) ||
		IsA(node, WindowFunc))
	{
		split_pathtarget_item *item = palloc_object(split_pathtarget_item);

		item->expr = node;
		item->sortgroupref = context->current_sgref;
		context->current_input_vars = lappend(context->current_input_vars,
											  item);
		return false;
	}

	/*
	 * If it's a SRF, recursively examine its inputs, determine its level, and
	 * make appropriate entries in the output lists.
	 */
	if (IS_SRF_CALL(node))
	{
		split_pathtarget_item *item = palloc_object(split_pathtarget_item);
		List	   *save_input_vars = context->current_input_vars;
		List	   *save_input_srfs = context->current_input_srfs;
		int			save_current_depth = context->current_depth;
		int			srf_depth;
		ListCell   *lc;

		item->expr = node;
		item->sortgroupref = context->current_sgref;

		context->current_input_vars = NIL;
		context->current_input_srfs = NIL;
		context->current_depth = 0;
		context->current_sgref = 0; /* subexpressions are not sortgroup items */

		(void) expression_tree_walker(node, split_pathtarget_walker, context);

		/* Depth is one more than any SRF below it */
		srf_depth = context->current_depth + 1;

		/* If new record depth, initialize another level of output lists */
		if (srf_depth >= list_length(context->level_srfs))
		{
			context->level_srfs = lappend(context->level_srfs, NIL);
			context->level_input_vars = lappend(context->level_input_vars, NIL);
			context->level_input_srfs = lappend(context->level_input_srfs, NIL);
		}

		/* Record this SRF as needing to be evaluated at appropriate level */
		lc = list_nth_cell(context->level_srfs, srf_depth);
		lfirst(lc) = lappend(lfirst(lc), item);

		/* Record its inputs as being needed at the same level */
		lc = list_nth_cell(context->level_input_vars, srf_depth);
		lfirst(lc) = list_concat(lfirst(lc), context->current_input_vars);
		lc = list_nth_cell(context->level_input_srfs, srf_depth);
		lfirst(lc) = list_concat(lfirst(lc), context->current_input_srfs);

		/*
		 * Restore caller-level state and update it for presence of this SRF.
		 * Notice we report the SRF itself as being needed for evaluation of
		 * surrounding expression.
		 */
		context->current_input_vars = save_input_vars;
		context->current_input_srfs = lappend(save_input_srfs, item);
		context->current_depth = Max(save_current_depth, srf_depth);

		/* We're done here */
		return false;
	}

	/*
	 * Otherwise, the node is a scalar (non-set) expression, so recurse to
	 * examine its inputs.
	 */
	context->current_sgref = 0; /* subexpressions are not sortgroup items */
	return expression_tree_walker(node, split_pathtarget_walker, context);
}

/*
 * Add a split_pathtarget_item to the PathTarget, unless a matching item is
 * already present.  This is like add_new_column_to_pathtarget, but allows
 * for sortgrouprefs to be handled.  An item having zero sortgroupref can
 * be merged with one that has a sortgroupref, acquiring the latter's
 * sortgroupref.
 *
 * Note that we don't worry about possibly adding duplicate sortgrouprefs
 * to the PathTarget.  That would be bad, but it should be impossible unless
 * the target passed to split_pathtarget_at_srfs already had duplicates.
 * As long as it didn't, we can have at most one split_pathtarget_item with
 * any particular nonzero sortgroupref.
 */
/*
 * add_sp_item_to_pathtarget - (中文)把切分项并入 PathTarget(带 SortGroupRef 去重)
 *
 * 【作用】把 split_pathtarget_item 代表的表达式加入 target,类似
 * add_new_column_to_pathtarget,但额外处理 sortgroupref:已存在的 equal()
 * 列会被合并(零 SortGroupRef 的项可吸收已有/被已有吸收),新列则追加。
 *
 * 【设计思想】遍历 target->exprs 找 equal() 且 sortgroupref 不冲突
 * (一方为 0 即不冲突)的项:命中时若 item 带非 0 sortgroupref,把它写进
 * 对应槽位(必要时惰性创建 sortgrouprefs 数组);未命中则复制表达式后调用
 * add_column_to_pathtarget 追加。这样既保留 SRF 层的求值身份,又不产生
 * 重复列。
 *
 * 【参数】
 *   target —— 目标 PathTarget;item —— 待并入的切分项。
 * 【返回值】无。
 */
static void
add_sp_item_to_pathtarget(PathTarget *target, split_pathtarget_item *item)
{
	int			lci;
	ListCell   *lc;

	/*
	 * Look for a pre-existing entry that is equal() and does not have a
	 * conflicting sortgroupref already.
	 */
	lci = 0;
	foreach(lc, target->exprs)
	{
		Node	   *node = (Node *) lfirst(lc);
		Index		sgref = get_pathtarget_sortgroupref(target, lci);

		if ((item->sortgroupref == sgref ||
			 item->sortgroupref == 0 ||
			 sgref == 0) &&
			equal(item->expr, node))
		{
			/* Found a match.  Assign item's sortgroupref if it has one. */
			if (item->sortgroupref)
			{
				if (target->sortgrouprefs == NULL)
				{
					target->sortgrouprefs = (Index *)
						palloc0(list_length(target->exprs) * sizeof(Index));
				}
				target->sortgrouprefs[lci] = item->sortgroupref;
			}
			return;
		}
		lci++;
	}

	/*
	 * No match, so add item to PathTarget.  Copy the expr for safety.
	 */
	add_column_to_pathtarget(target, (Expr *) copyObject(item->expr),
							 item->sortgroupref);
}

/*
 * Apply add_sp_item_to_pathtarget to each element of list.
 */
/*
 * add_sp_items_to_pathtarget - (中文)批量并入切分项
 *
 * 【作用】对 items 中每个 split_pathtarget_item 调用 add_sp_item_to_pathtarget。
 *
 * 【设计思想】纯批量转发。
 *
 * 【参数】
 *   target —— 目标 PathTarget;items —— 切分项列表。
 * 【返回值】无。
 */
static void
add_sp_items_to_pathtarget(PathTarget *target, List *items)
{
	ListCell   *lc;

	foreach(lc, items)
	{
		split_pathtarget_item *item = lfirst(lc);

		add_sp_item_to_pathtarget(target, item);
	}
}
