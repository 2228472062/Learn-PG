/*-------------------------------------------------------------------------
 *
 * rewriteManip.c
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/rewrite/rewriteManip.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/attmap.h"
#include "catalog/pg_type.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/pathnodes.h"
#include "nodes/plannodes.h"
#include "parser/parse_coerce.h"
#include "parser/parse_relation.h"
#include "parser/parsetree.h"
#include "rewrite/rewriteManip.h"
#include "utils/lsyscache.h"


typedef struct
{
	int			sublevels_up;
} contain_aggs_of_level_context;

typedef struct
{
	int			agg_location;
	int			sublevels_up;
} locate_agg_of_level_context;

typedef struct
{
	int			win_location;
} locate_windowfunc_context;

typedef struct
{
	const Bitmapset *target_relids;
	const Bitmapset *added_relids;
	int			sublevels_up;
} add_nulling_relids_context;

typedef struct
{
	const Bitmapset *removable_relids;
	const Bitmapset *except_relids;
	int			sublevels_up;
} remove_nulling_relids_context;

static bool contain_aggs_of_level_walker(Node *node,
										 contain_aggs_of_level_context *context);
static bool locate_agg_of_level_walker(Node *node,
									   locate_agg_of_level_context *context);
static bool contain_windowfuncs_walker(Node *node, void *context);
static bool locate_windowfunc_walker(Node *node,
									 locate_windowfunc_context *context);
static bool checkExprHasSubLink_walker(Node *node, void *context);
static Node *add_nulling_relids_mutator(Node *node,
										add_nulling_relids_context *context);
static Node *remove_nulling_relids_mutator(Node *node,
										   remove_nulling_relids_context *context);


/*
 * ============================================================================
 * 【中文注释】contain_aggs_of_level —— 判断表达式是否包含指定查询层的聚合函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历一棵查询/表达式树，检查其中是否存在 agglevelsup 恰好等于 levelsup 的
 *   聚合调用（Aggref 或 GroupingFunc）。用于判断"某个查询层上是否使用了聚合"。
 *
 * 参数：
 *   node    - 待检查的树根，可以是 Query 或普通表达式树。
 *   levelsup- 目标查询层：0 表示当前查询层，1 表示外层，依此类推。
 *
 * 返回值：
 *   bool - 存在属于该查询层的聚合则返回 true，否则 false。
 *
 * 设计思想：
 *   1. 一个关键点：不仅要检查"当前树里直接可见"的聚合，还要**递归进入子查询**
 *      去找"子查询引用了外层查询的聚合"这种情形——这种聚合（agglevelsup 指向
 *      外层）逻辑上仍属于外层查询层，所以必须递归下去才能准确判定。
 *   2. 属于子查询自己或更外层的聚合（agglevelsup 不等于 levelsup）不会导致返回
 *      true，此时继续向下检查其参数。
 *   3. 用 query_or_expression_tree_walker 启动遍历，并传 0 作为起始
 *      sublevels_up：若从 Query 开始，不会先自增层数（见 walker 中进入子查询才
 *      自增的设计）。
 * ============================================================================
 */
bool
contain_aggs_of_level(Node *node, int levelsup)
{
	contain_aggs_of_level_context context;

	context.sublevels_up = levelsup;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	return query_or_expression_tree_walker(node,
										   contain_aggs_of_level_walker,
										   &context,
										   0);
}

/*
 * ============================================================================
 * 【中文注释】contain_aggs_of_level_walker —— 聚合存在性检查的遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   contain_aggs_of_level 的实际递归实现。返回 true 表示"找到匹配聚合"，立即
 *   中止整个遍历。
 *
 * 参数：
 *   node    - 当前遍历节点。
 *   context- 携带当前 sublevels_up（已深入多少层子查询）。
 *
 * 返回值：
 *   bool - true 表示命中并终止遍历；false 表示继续遍历。
 *
 * 设计思想：
 *   1. 对 Aggref/GroupingFunc：比较 agglevelsup 与当前 sublevels_up，相等即命中；
 *      不等则继续检查其参数（聚合的参数里可能嵌套了更深层的聚合或子查询）。
 *   2. 对 Query：表示进入一个子查询，sublevels_up 加一后递归（query_tree_walker），
 *      返回后减一恢复现场——这是把"层"计数与递归深度同步的标准做法。
 *   3. 其他节点用 expression_tree_walker 通用遍历。
 * ============================================================================
 */
static bool
contain_aggs_of_level_walker(Node *node,
							 contain_aggs_of_level_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Aggref))
	{
		if (((Aggref *) node)->agglevelsup == context->sublevels_up)
			return true;		/* abort the tree traversal and return true */
		/* else fall through to examine argument */
	}
	if (IsA(node, GroupingFunc))
	{
		if (((GroupingFunc *) node)->agglevelsup == context->sublevels_up)
			return true;
		/* else fall through to examine argument */
	}
	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node,
								   contain_aggs_of_level_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, contain_aggs_of_level_walker,
								  context);
}

/*
 * ============================================================================
 * 【中文注释】locate_agg_of_level —— 定位指定查询层中聚合的源码位置
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历查询树，找到第一个"属于指定查询层、且解析位置已知"的聚合调用，返回其
 *   location（源码中的位置，用于错误报告定位）。找不到则返回 -1。
 *
 * 参数：
 *   node    - 树根（Query 或表达式）。
 *   levelsup- 目标查询层。
 *
 * 返回值：
 *   int - 聚合的源码 location；找不到或位置未知返回 -1。
 *
 * 设计思想：
 *   1. 与 contain_aggs_of_level 功能相近，但目标是"报错时给用户指出聚合在哪"，
 *      因此保存的是 location 而非布尔值。两者故意分开实现：合并会让
 *      contain_aggs_of_level 的 API 变复杂，而本函数仅用于错误报告，性能无关紧要。
 *   2. 返回 -1 有两种情况：根本找不到该层聚合（多半是调用方搞错了层数），或
 *      找到了但 location 为 -1（源码位置未知）。这两种情况难以区分也无须区分，
 *      调用方只需在 >=0 时用于报错定位。
 * ============================================================================
 */
int
locate_agg_of_level(Node *node, int levelsup)
{
	locate_agg_of_level_context context;

	context.agg_location = -1;	/* in case we find nothing */
	context.sublevels_up = levelsup;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	(void) query_or_expression_tree_walker(node,
										   locate_agg_of_level_walker,
										   &context,
										   0);

	return context.agg_location;
}

/*
 * ============================================================================
 * 【中文注释】locate_agg_of_level_walker —— 聚合定位遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   locate_agg_of_level 的递归实现：遇到"层数匹配且 location>=0"的聚合即把位置
 *   写入 context 并返回 true 终止遍历。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - 记录聚合位置（agg_location）与当前查询层（sublevels_up）。
 *
 * 返回值：
 *   bool - true 表示已找到并终止遍历。
 *
 * 设计思想：
 *   与 contain_aggs_of_level_walker 的遍历骨架完全一致（进入子查询时层数自增、
 *   GroupingFunc 同样处理），差别仅在命中条件多了 location>=0，且命中时保存位置
 *   而非返回简单 true。
 * ============================================================================
 */
static bool
locate_agg_of_level_walker(Node *node,
						   locate_agg_of_level_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Aggref))
	{
		if (((Aggref *) node)->agglevelsup == context->sublevels_up &&
			((Aggref *) node)->location >= 0)
		{
			context->agg_location = ((Aggref *) node)->location;
			return true;		/* abort the tree traversal and return true */
		}
		/* else fall through to examine argument */
	}
	if (IsA(node, GroupingFunc))
	{
		if (((GroupingFunc *) node)->agglevelsup == context->sublevels_up &&
			((GroupingFunc *) node)->location >= 0)
		{
			context->agg_location = ((GroupingFunc *) node)->location;
			return true;		/* abort the tree traversal and return true */
		}
	}
	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node,
								   locate_agg_of_level_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, locate_agg_of_level_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】contain_windowfuncs —— 判断表达式是否包含当前查询层的窗口函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历查询/表达式树，检查是否存在窗口函数调用（WindowFunc）。注意只关心
 *   **当前查询层**的窗口函数，且**不递归进入子查询**。
 *
 * 参数：
 *   node - 树根（Query 或表达式）。
 *
 * 返回值：
 *   bool - 找到窗口函数返回 true，否则 false。
 *
 * 设计思想：
 *   与 contain_aggs_of_level 最大的不同：窗口函数在 PostgreSQL 中只允许出现在
 *   最外层的查询中（窗口不能在子查询里直接使用外层窗口），因此遍历时明确"不能
 *   递归进入子查询"，否则会把子查询里的引用误判。这个差别由
 *   contain_windowfuncs_walker 中"不做 Query 特殊处理"来体现——expression_tree_
 *   walker 默认不会钻入 RTE 子查询。
 * ============================================================================
 */
bool
contain_windowfuncs(Node *node)
{
	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	return query_or_expression_tree_walker(node,
										   contain_windowfuncs_walker,
										   NULL,
										   0);
}

/*
 * ============================================================================
 * 【中文注释】contain_windowfuncs_walker —— 窗口函数存在性遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   contain_windowfuncs 的递归实现：遇到 WindowFunc 立即返回 true 终止遍历。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - 未使用（保持 walker 签名兼容）。
 *
 * 返回值：
 *   bool - true 表示命中并终止遍历。
 *
 * 设计思想：
 *   只有一条命中规则（IsA WindowFunc），其余交给 expression_tree_walker。注释里
 *   明确写着"不得递归进入子查询"：因为 expression_tree_walker 不会进入 RTE 的
 *   子查询，天然符合"只看当前层"的要求，无需像聚合检查那样处理 Query。
 * ============================================================================
 */
static bool
contain_windowfuncs_walker(Node *node, void *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, WindowFunc))
		return true;			/* abort the tree traversal and return true */
	/* Mustn't recurse into subselects */
	return expression_tree_walker(node, contain_windowfuncs_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】locate_windowfunc —— 定位当前查询层中窗口函数的源码位置
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历查询树，找到第一个"解析位置已知"的窗口函数并返回其 location，用于错误
 *   报告定位；找不到或位置未知返回 -1。
 *
 * 参数：
 *   node - 树根（Query 或表达式）。
 *
 * 返回值：
 *   int - 窗口函数的源码 location；找不到返回 -1。
 *
 * 设计思想：
 *   与 locate_agg_of_level 同模式：为错误报告服务而单独实现，不合并进
 *   contain_windowfuncs。同样只关心当前查询层、不递归进子查询。
 * ============================================================================
 */
int
locate_windowfunc(Node *node)
{
	locate_windowfunc_context context;

	context.win_location = -1;	/* in case we find nothing */

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	(void) query_or_expression_tree_walker(node,
										   locate_windowfunc_walker,
										   &context,
										   0);

	return context.win_location;
}

/*
 * ============================================================================
 * 【中文注释】locate_windowfunc_walker —— 窗口函数定位遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   locate_windowfunc 的递归实现：遇到 location>=0 的 WindowFunc 即保存位置并
 *   返回 true 终止遍历。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - 记录窗口函数位置（win_location）。
 *
 * 返回值：
 *   bool - true 表示已找到并终止遍历。
 *
 * 设计思想：
 *   与 contain_windowfuncs_walker 骨架一致（不递归子查询），差别在于命中时记录
 *   位置，且只接受 location>=0 的窗口函数（-1 表示来源未知，不适合报错定位）。
 * ============================================================================
 */
static bool
locate_windowfunc_walker(Node *node, locate_windowfunc_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, WindowFunc))
	{
		if (((WindowFunc *) node)->location >= 0)
		{
			context->win_location = ((WindowFunc *) node)->location;
			return true;		/* abort the tree traversal and return true */
		}
		/* else fall through to examine argument */
	}
	/* Mustn't recurse into subselects */
	return expression_tree_walker(node, locate_windowfunc_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】checkExprHasSubLink —— 判断表达式是否包含子链接（SubLink）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历查询/表达式树，检查其中是否存在 SubLink 节点（IN/EXISTS/ANY/标量子查询
 *   等尚未改写为 SubPlan 的子查询引用形式）。
 *
 * 参数：
 *   node - 树根（Query 或表达式）。
 *
 * 返回值：
 *   bool - 存在 SubLink 返回 true，否则 false。
 *
 * 设计思想：
 *   1. 子链接检测通常用于维护查询的 hasSubLinks 标志，或者用于判断改写是否会
 *      引入新的子链接。
 *   2. 与前面几个"检查函数"的区别：对传入的 Query，**不递归进入其 rtable/CTE
 *      中的子查询**（QTW_IGNORE_RC_SUBQUERIES）——因为那些子查询已经在自己的
 *      hasSubLinks 字段里记录了自己的子链接情况，此处只需检测本查询表达式树
 *      中实际出现的 SubLink 节点即可，避免重复与误报。
 * ============================================================================
 */
bool
checkExprHasSubLink(Node *node)
{
	/*
	 * If a Query is passed, examine it --- but we should not recurse into
	 * sub-Queries that are in its rangetable or CTE list.
	 */
	return query_or_expression_tree_walker(node,
										   checkExprHasSubLink_walker,
										   NULL,
										   QTW_IGNORE_RC_SUBQUERIES);
}

/*
 * ============================================================================
 * 【中文注释】checkExprHasSubLink_walker —— 子链接存在性遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   checkExprHasSubLink 的递归实现：遇到 SubLink 立即返回 true 终止遍历。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - 未使用。
 *
 * 返回值：
 *   bool - true 表示命中并终止遍历。
 *
 * 设计思想：
 *   单一命中规则（IsA SubLink），其余交给通用遍历器。注意 SubLink 自身的
 *   subselect 字段里是一个 Query，expression_tree_walker 不会自动进入它；但对
 *   本函数来说这是正确的——一旦在外层发现 SubLink 就已经命中返回了。
 * ============================================================================
 */
static bool
checkExprHasSubLink_walker(Node *node, void *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, SubLink))
		return true;			/* abort the tree traversal and return true */
	return expression_tree_walker(node, checkExprHasSubLink_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】contains_multiexpr_param —— 检查表达式树中是否含 MULTIEXPR 参数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历表达式树，检查是否存在 paramkind == PARAM_MULTIEXPR 的 Param 节点。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - 未使用。
 *
 * 返回值：
 *   bool - 命中 MULTIEXPR 参数返回 true。
 *
 * 设计思想：
 *   1. PARAM_MULTIEXPR 是 PostgreSQL 为"多个目标列在一次赋值（如 UPDATE 的
 *      (a,b) = (SELECT ...) 行式赋值）"生成的内部参数。在规则展开（尤其是 ON
 *      UPDATE 规则的 NEW 变量替换）时遇到它无法安全处理——因为那样会需要把
 *      该行式赋值的子查询求值多次，产生语义怪异的结果，因此调用方会直接报
 *      "not implemented" 错误。
 *   2. 遍历时**故意不进入 SubLink**：只有当前查询层的 Params 才值得关心，子查询
 *      里的 MULTIEXPR 参数属于内层，不会影响外层替换的正确性。
 * ============================================================================
 */
static bool
contains_multiexpr_param(Node *node, void *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Param))
	{
		if (((Param *) node)->paramkind == PARAM_MULTIEXPR)
			return true;		/* abort the tree traversal and return true */
		return false;
	}
	return expression_tree_walker(node, contains_multiexpr_param, context);
}

/*
 * ============================================================================
 * 【中文注释】CombineRangeTables —— 把源范围表（及权限信息）合并进目标范围表
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   将 src_rtable 中的所有 RangeTblEntry 追加到 dst_rtable 末尾，同时把
 *   src_perminfos 中的 RTEPermissionInfo 追加到 dst_perminfos 末尾，并修正被
 *   移动的 RTE 中 perminfoindex 字段，使它们指向新列表中的正确下标。
 *
 * 参数：
 *   dst_rtable   - 目标范围表（List* 的指针，会被就地修改并在末尾追加）。
 *   dst_perminfos- 目标权限信息列表（同上）。
 *   src_rtable   - 待合并的源范围表。
 *   src_perminfos- 与 src_rtable 对应顺序的权限信息列表。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 背景：从 PG 13 起，RTE 的权限信息独立存放在 Query 的 rteperminfos 列表里，
 *      RTE.perminfoindex 指向其在 perminfos 中的下标（1 基）。合并两个查询（如把
 *      规则动作查询的范围表并入主查询）时，必须保证每个 RTE 的 perminfoindex
 *      在合并后仍指向正确的权限项。
 *   2. 因此先算出 offset = 原 dst_perminfos 的长度，把所有 src_rtable 中
 *      perminfoindex>0 的 RTE 的下标统一加上 offset，再 concat 两个列表即可。
 *   3. 该函数会破坏性修改 dst_rtable 与 dst_perminfos（以及 src_rtable 里 RTE 的
 *      perminfoindex 字段），所以调用方应当传入可安全修改的拷贝。
 * ============================================================================
 */
void
CombineRangeTables(List **dst_rtable, List **dst_perminfos,
				   List *src_rtable, List *src_perminfos)
{
	ListCell   *l;
	int			offset = list_length(*dst_perminfos);

	if (offset > 0)
	{
		foreach(l, src_rtable)
		{
			RangeTblEntry *rte = lfirst_node(RangeTblEntry, l);

			if (rte->perminfoindex > 0)
				rte->perminfoindex += offset;
		}
	}

	*dst_perminfos = list_concat(*dst_perminfos, src_perminfos);
	*dst_rtable = list_concat(*dst_rtable, src_rtable);
}

/*
 * ============================================================================
 * 【中文注释】OffsetVarNodes_walker —— 对树中所有 Var 的 varno 做统一位移的遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   OffsetVarNodes 的递归实现：找出所有 varlevelsup == sublevels_up 的 Var，把其
 *   varno、varnosyn 以及 varnullingrels 里的成员统一加上 offset；同时处理含范围
 *   表下标的其他节点（RangeTblRef、JoinExpr、CurrentOfExpr、PlaceHolderVar、
 *   AppendRelInfo）。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - 携带 offset（位移量）与 sublevels_up（当前查询层）。
 *
 * 返回值：
 *   bool - false（本函数不终止遍历，采用就地修改）。
 *
 * 设计思想：
 *   1. 用途：当把一个查询的范围表拼接到另一个查询后面时（如规则动作合并、子查询
 *      上提），原查询里所有引用范围表的编号都要整体平移 offset，否则会指向错误
 *      的 RTE。
 *   2. 只有 varlevelsup 与当前层相同的 Var 才需要调整——内层子查询里引用外层
 *      的 Var（varlevelsup 更小）或引用更深层的 Var 都不在本层调整范围内。
 *   3. "外层（sublevels_up==0）才调整范围表节点"：RangeTblRef/JoinExpr 等只存在于
 *      当前查询的 jointree 里，递归进入子查询时 sublevels_up 已自增，不再满足条件。
 *   4. 实现上名为 walker 实为 mutator-in-place：直接改写节点字段而非复制，因此
 *      调用方必须保证传入的是拷贝后的树，避免产生副作用。
 *   5. varnullingrels/phrels/phnullingrels 等 Relid 集合也要平移（bms_offset_members），
 *      否则 nulling 信息里的 relid 会与实际 varno 不一致。
 * ============================================================================
 */

typedef struct
{
	int			offset;
	int			sublevels_up;
} OffsetVarNodes_context;

static bool
OffsetVarNodes_walker(Node *node, OffsetVarNodes_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup == context->sublevels_up)
		{
			var->varno += context->offset;
			var->varnullingrels = bms_offset_members(var->varnullingrels,
													 context->offset);
			if (var->varnosyn > 0)
				var->varnosyn += context->offset;
		}
		return false;
	}
	if (IsA(node, CurrentOfExpr))
	{
		CurrentOfExpr *cexpr = (CurrentOfExpr *) node;

		if (context->sublevels_up == 0)
			cexpr->cvarno += context->offset;
		return false;
	}
	if (IsA(node, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) node;

		if (context->sublevels_up == 0)
			rtr->rtindex += context->offset;
		/* the subquery itself is visited separately */
		return false;
	}
	if (IsA(node, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) node;

		if (j->rtindex && context->sublevels_up == 0)
			j->rtindex += context->offset;
		/* fall through to examine children */
	}
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (phv->phlevelsup == context->sublevels_up)
		{
			phv->phrels = bms_offset_members(phv->phrels,
											 context->offset);
			phv->phnullingrels = bms_offset_members(phv->phnullingrels,
													context->offset);
		}
		/* fall through to examine children */
	}
	if (IsA(node, AppendRelInfo))
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) node;

		if (context->sublevels_up == 0)
		{
			appinfo->parent_relid += context->offset;
			appinfo->child_relid += context->offset;
		}
		/* fall through to examine children */
	}
	/* Shouldn't need to handle other planner auxiliary nodes here */
	Assert(!IsA(node, PlanRowMark));
	Assert(!IsA(node, SpecialJoinInfo));
	Assert(!IsA(node, PlaceHolderInfo));
	Assert(!IsA(node, MinMaxAggInfo));

	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node, OffsetVarNodes_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, OffsetVarNodes_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】OffsetVarNodes —— 将一个查询中引用范围表的编号整体平移（对外入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对外入口。把整棵树（Query 或表达式）中 varlevelsup == sublevels_up 的所有
 *   Var 的 varno、varnosyn 加上 offset，同时平移 RangeTblRef/JoinExpr/rowMarks/
 *   resultRelation 等所有含范围表下标的字段。用于把一个查询的范围表拼接到另一个
 *   查询之后。
 *
 * 参数：
 *   node         - 待处理的树根（Query 或表达式）。
 *   offset       - 要加的位移量。
 *   sublevels_up - 要处理的查询层。
 *
 * 返回值：
 *   无（就地修改）。
 *
 * 设计思想：
 *   1. 若树根是 Query 且 sublevels_up == 0，还要额外处理 Query 自身的顶层字段：
 *      resultRelation、mergeTargetRelation、onConflict->exclRelIndex、以及
 *      rowMarks 列表里每个 RowMarkClause 的 rti。这些字段也存范围表下标，而它们
 *      只会出现在顶层 Query 上（递归进子查询时 sublevels_up 必不为 0），所以放
 *      在入口函数而非 walker 里处理。
 *   2. 用 query_tree_walker 而非通用 walker 启动，避免 Query 被当作"子查询"
 *      先自增 sublevels_up（否则最外层就会被当成第 1 层而漏调）。
 * ============================================================================
 */
void
OffsetVarNodes(Node *node, int offset, int sublevels_up)
{
	OffsetVarNodes_context context;

	context.offset = offset;
	context.sublevels_up = sublevels_up;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, go straight to query_tree_walker to make sure that
	 * sublevels_up doesn't get incremented prematurely.
	 */
	if (node && IsA(node, Query))
	{
		Query	   *qry = (Query *) node;

		/*
		 * If we are starting at a Query, and sublevels_up is zero, then we
		 * must also fix rangetable indexes in the Query itself --- namely
		 * resultRelation, mergeTargetRelation, exclRelIndex and rowMarks
		 * entries.  sublevels_up cannot be zero when recursing into a
		 * subquery, so there's no need to have the same logic inside
		 * OffsetVarNodes_walker.
		 */
		if (sublevels_up == 0)
		{
			ListCell   *l;

			if (qry->resultRelation)
				qry->resultRelation += offset;

			if (qry->mergeTargetRelation)
				qry->mergeTargetRelation += offset;

			if (qry->onConflict && qry->onConflict->exclRelIndex)
				qry->onConflict->exclRelIndex += offset;

			foreach(l, qry->rowMarks)
			{
				RowMarkClause *rc = (RowMarkClause *) lfirst(l);

				rc->rti += offset;
			}
		}
		query_tree_walker(qry, OffsetVarNodes_walker, &context, 0);
	}
	else
		OffsetVarNodes_walker(node, &context);
}

/*
 * ============================================================================
 * 【中文注释】ChangeVarNodes_walker —— 把特定关系编号改为新编号的遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   ChangeVarNodesExtended 的递归实现：把树中"属于指定关系（varno == rt_index 且
 *   varlevelsup == sublevels_up）"的 Var 的 varno/varnosyn 改为 new_index，同时
 *   更新 varnullingrels；并对 RangeTblRef、JoinExpr、CurrentOfExpr、PlanRowMark、
 *   PlaceHolderVar、AppendRelInfo 等含范围表下标的节点做同样的替换。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - ChangeVarNodes_context：rt_index（旧编号）、new_index（新编号）、
 *             sublevels_up（当前层）、callback（可选的前处理回调）。
 *
 * 返回值：
 *   bool - false（不终止遍历，就地修改）。
 *
 * 设计思想：
 *   1. 与 OffsetVarNodes_walker 结构非常相似，但语义是"指定编号的替换"而非"整体
 *      平移"。典型用途：视图/规则展开时，把对视图的引用替换为对其内部 RTE 的
 *      引用（编号变了），或把 OLD/NEW 伪行对应的 varno 改写。
 *   2. 先调用 context->callback（若存在）做前处理：若回调返回 true 则跳过本节点
 *      的默认处理，供调用方自定义某些节点的处理逻辑。
 *   3. 对 var->varnullingrels 这类 Relid 集合用 adjust_relid_set 替换成员；对
 *      varnosyn（记录源语法引用的编号，用于 deparse）同样处理，保证改写后
 *      语义与语法引用都指向正确。
 *   4. 注意 PlanRowMark（rti/prti）在这里被处理，而 Offset 版本没有——因为行锁
 *      标记的编号替换在视图展开场景更需要。
 *   5. 同样"名为 walker 实为就地修改"，调用方需保证传入拷贝后的树。
 * ============================================================================
 */

static bool
ChangeVarNodes_walker(Node *node, ChangeVarNodes_context *context)
{
	if (node == NULL)
		return false;

	if (context->callback && context->callback(node, context))
		return false;

	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup == context->sublevels_up)
		{
			if (var->varno == context->rt_index)
				var->varno = context->new_index;
			var->varnullingrels = adjust_relid_set(var->varnullingrels,
												   context->rt_index,
												   context->new_index);
			if (var->varnosyn == context->rt_index)
				var->varnosyn = context->new_index;
		}
		return false;
	}
	if (IsA(node, CurrentOfExpr))
	{
		CurrentOfExpr *cexpr = (CurrentOfExpr *) node;

		if (context->sublevels_up == 0 &&
			cexpr->cvarno == context->rt_index)
			cexpr->cvarno = context->new_index;
		return false;
	}
	if (IsA(node, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) node;

		if (context->sublevels_up == 0 &&
			rtr->rtindex == context->rt_index)
			rtr->rtindex = context->new_index;
		/* the subquery itself is visited separately */
		return false;
	}
	if (IsA(node, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) node;

		if (context->sublevels_up == 0 &&
			j->rtindex == context->rt_index)
			j->rtindex = context->new_index;
		/* fall through to examine children */
	}
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (phv->phlevelsup == context->sublevels_up)
		{
			phv->phrels = adjust_relid_set(phv->phrels,
										   context->rt_index,
										   context->new_index);
			phv->phnullingrels = adjust_relid_set(phv->phnullingrels,
												  context->rt_index,
												  context->new_index);
		}
		/* fall through to examine children */
	}
	if (IsA(node, PlanRowMark))
	{
		PlanRowMark *rowmark = (PlanRowMark *) node;

		if (context->sublevels_up == 0)
		{
			if (rowmark->rti == context->rt_index)
				rowmark->rti = context->new_index;
			if (rowmark->prti == context->rt_index)
				rowmark->prti = context->new_index;
		}
		return false;
	}
	if (IsA(node, AppendRelInfo))
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) node;

		if (context->sublevels_up == 0)
		{
			if (appinfo->parent_relid == context->rt_index)
				appinfo->parent_relid = context->new_index;
			if (appinfo->child_relid == context->rt_index)
				appinfo->child_relid = context->new_index;
		}
		/* fall through to examine children */
	}
	/* Shouldn't need to handle other planner auxiliary nodes here */
	Assert(!IsA(node, SpecialJoinInfo));
	Assert(!IsA(node, PlaceHolderInfo));
	Assert(!IsA(node, MinMaxAggInfo));

	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node, ChangeVarNodes_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, ChangeVarNodes_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】ChangeVarNodesExtended —— 带回调的"替换范围表编号"入口
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   ChangeVarNodes 的扩展版本：除按 ChangeVarNodes 规则把指定旧编号替换为新编号
 *   外，还接受一个回调，在 walker 处理每个节点之前先交给回调，回调可返回 true
 *   指示"跳过该节点的默认处理"。
 *
 * 参数：
 *   node         - 树根（Query 或表达式）。
 *   rt_index     - 要被替换的旧范围表编号。
 *   new_index    - 新编号。
 *   sublevels_up - 要处理的查询层。
 *   callback     - 可选回调（可 NULL），在 ChangeVarNodes_walker 处理每个节点前
 *                  调用；返回 true 表示跳过该节点的默认处理。
 *
 * 返回值：
 *   无（就地修改）。
 *
 * 设计思想：
 *   1. 回调机制用于"自定义特殊节点的处理"：例如某些节点希望整体跳过，或需要先
 *      做自己的递归再参与默认替换。注意回调只在 walker 遍历到的表达式/子节点上
 *      触发，根 Query 节点本身不会触发回调。
 *   2. 若树根是 Query 且 sublevels_up == 0，同样处理顶层字段：resultRelation、
 *      mergeTargetRelation、exclRelIndex、rowMarks。
 *   3. 普通场景直接传 NULL 回调，退化为 ChangeVarNodes 的语义。
 * ============================================================================
 */
void
ChangeVarNodesExtended(Node *node, int rt_index, int new_index,
					   int sublevels_up, ChangeVarNodes_callback callback)
{
	ChangeVarNodes_context context;

	context.rt_index = rt_index;
	context.new_index = new_index;
	context.sublevels_up = sublevels_up;
	context.callback = callback;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, go straight to query_tree_walker to make sure that
	 * sublevels_up doesn't get incremented prematurely.
	 */
	if (node && IsA(node, Query))
	{
		Query	   *qry = (Query *) node;

		/*
		 * If we are starting at a Query, and sublevels_up is zero, then we
		 * must also fix rangetable indexes in the Query itself --- namely
		 * resultRelation, mergeTargetRelation, exclRelIndex  and rowMarks
		 * entries.  sublevels_up cannot be zero when recursing into a
		 * subquery, so there's no need to have the same logic inside
		 * ChangeVarNodes_walker.
		 */
		if (sublevels_up == 0)
		{
			ListCell   *l;

			if (qry->resultRelation == rt_index)
				qry->resultRelation = new_index;

			if (qry->mergeTargetRelation == rt_index)
				qry->mergeTargetRelation = new_index;

			/* this is unlikely to ever be used, but ... */
			if (qry->onConflict && qry->onConflict->exclRelIndex == rt_index)
				qry->onConflict->exclRelIndex = new_index;

			foreach(l, qry->rowMarks)
			{
				RowMarkClause *rc = (RowMarkClause *) lfirst(l);

				if (rc->rti == rt_index)
					rc->rti = new_index;
			}
		}
		query_tree_walker(qry, ChangeVarNodes_walker, &context, 0);
	}
	else
		ChangeVarNodes_walker(node, &context);
}

/*
 * ============================================================================
 * 【中文注释】ChangeVarNodes —— 无回调版"替换范围表编号"（对外常用入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   简单包装 ChangeVarNodesExtended：把指定查询层中引用旧编号 rt_index 的所有
 *   Var 及相关节点改为引用新编号 new_index。
 *
 * 参数：
 *   node         - 树根（Query 或表达式）。
 *   rt_index     - 旧编号。
 *   new_index    - 新编号。
 *   sublevels_up - 目标查询层。
 *
 * 返回值：
 *   无（就地修改）。
 *
 * 设计思想：
 *   纯粹是便捷封装，传 NULL 回调；具体逻辑与注意事项见 ChangeVarNodesExtended。
 * ============================================================================
 */
void
ChangeVarNodes(Node *node, int rt_index, int new_index, int sublevels_up)
{
	ChangeVarNodesExtended(node, rt_index, new_index, sublevels_up, NULL);
}

/*
 * ============================================================================
 * 【中文注释】ChangeVarNodesWalkExpression —— 在回调内递归处理子表达式的工具
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   供 ChangeVarNodesExtended 的回调函数使用：直接对传入的单个表达式/节点调用
 *   ChangeVarNodes_walker，使其（连同其子节点）都被 ChangeVarNodes 规则处理。
 *
 * 参数：
 *   node    - 需要处理的表达式节点（单个节点，如一个裸 Var）。
 *   context - 外层 ChangeVarNodesExtended 的上下文。
 *
 * 返回值：
 *   bool - ChangeVarNodes_walker 的返回值（本函数透传）。
 *
 * 设计思想：
 *   1. 为什么需要它？回调若想对某个节点做自己的递归处理，又希望该节点也能享受
 *      ChangeVarNodes 的默认编号替换，不能直接用 expression_tree_walker——
 *      它只访问子节点，会漏掉节点本身（例如一个裸 Var 就不会被改 varno）。
 *      直接调用 walker 才能"连节点带子树"一起处理。
 *   2. 重要限制：此处传入的 Query 会被当作"子查询"处理——walker 会先自增
 *      sublevels_up 再递归，也不会调整 Query 顶层字段（resultRelation 等）。
 *      因此**不要**用它处理顶层 Query；顶层 Query 请直接用
 *      ChangeVarNodesExtended。
 * ============================================================================
 */
bool
ChangeVarNodesWalkExpression(Node *node, ChangeVarNodes_context *context)
{
	return ChangeVarNodes_walker(node, context);
}

/*
 * ============================================================================
 * 【中文注释】adjust_relid_set —— 在 Relid 集合中用新编号替换旧编号
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从 relids 位图中移除 oldrelid（若存在），并把 newrelid 加入（若非特殊编号）。
 *   返回修改后的新位图。
 *
 * 参数：
 *   relids   - 待修改的 Relid 集合（位图）。
 *   oldrelid - 要移除的编号。
 *   newrelid - 要加入的编号。
 *
 * 返回值：
 *   Relids - 修改后的位图。可能返回与原位图相同的指针（未发生修改时）或新分配
 *            的拷贝。
 *
 * 设计思想：
 *   1. 特殊编号（IS_SPECIAL_VARNO，如 0 表示整行 Var、-1 及以下表示 OLD/NEW
 *      伪变量等）不能作为位图成员参与替换：因此 oldrelid 为特殊编号时函数不做
 *      任何事（返回原集合），newrelid 为特殊编号时等价于"仅删除"。
 *   2. 仅当 oldrelid 确实在集合中时才需要修改；修改前 bms_copy 一份，避免破坏
 *      调用方持有的位图（位图是可共享引用的不可变对象）。
 *   3. 本函数是 ChangeVarNodes_walker 更新 varnullingrels/phrels/phnullingrels
 *      等 Relid 集合的公共工具。
 * ============================================================================
 */
Relids
adjust_relid_set(Relids relids, int oldrelid, int newrelid)
{
	if (!IS_SPECIAL_VARNO(oldrelid) && bms_is_member(oldrelid, relids))
	{
		/* Ensure we have a modifiable copy */
		relids = bms_copy(relids);
		/* Remove old, add new */
		relids = bms_del_member(relids, oldrelid);
		if (!IS_SPECIAL_VARNO(newrelid))
			relids = bms_add_member(relids, newrelid);
	}
	return relids;
}

/*
 * ============================================================================
 * 【中文注释】IncrementVarSublevelsUp_walker —— 提升 Var 嵌套层数的遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   IncrementVarSublevelsUp 的递归实现：把树中 varlevelsup >= min_sublevels_up
 *   的所有 Var 的 varlevelsup 统一加上 delta_sublevels_up；Aggref、GroupingFunc、
 *   PlaceHolderVar、ReturningExpr 的 levelsup 字段、RTE_CTE 的 ctelevelsup 也
 *   同样处理。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - delta_sublevels_up（层数增量）与 min_sublevels_up（最小受影响层）。
 *
 * 返回值：
 *   bool - false（就地修改，不终止遍历）。
 *
 * 设计思想：
 *   1. 用途：当把一个本属于某层查询的表达式下推/嵌入到更深一层的子查询中时，
 *      其中引用原层的 Var 必须把 varlevelsup 相应加大，否则它会被误解释为引用
 *      子查询自身的列。例如把 WHERE 条件整体搬进一个子查询。
 *   2. min_sublevels_up 的意义：递归进入子查询（subplan/sublink）时把它加一，
 *      这样子查询**内部自己**的 Var（varlevelsup 相对更深）不受影响，只有引用
 *      原表达式层的"外层引用"被提升。
 *   3. 对 RangeTblEntry（RTE_CTE）需要特殊处理其 ctelevelsup，并使用
 *      QTW_EXAMINE_RTES_BEFORE 标志让 range_table_walker 在进入 RTE 子查询前先
 *      看到 RTE 本身；对 RTE 只改 ctelevelsup 后返回 false 让遍历继续。
 *   4. CurrentOfExpr 不支持下推（会直接报错）。
 * ============================================================================
 */

typedef struct
{
	int			delta_sublevels_up;
	int			min_sublevels_up;
} IncrementVarSublevelsUp_context;

static bool
IncrementVarSublevelsUp_walker(Node *node,
							   IncrementVarSublevelsUp_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup >= context->min_sublevels_up)
			var->varlevelsup += context->delta_sublevels_up;
		return false;			/* done here */
	}
	if (IsA(node, CurrentOfExpr))
	{
		/* this should not happen */
		if (context->min_sublevels_up == 0)
			elog(ERROR, "cannot push down CurrentOfExpr");
		return false;
	}
	if (IsA(node, Aggref))
	{
		Aggref	   *agg = (Aggref *) node;

		if (agg->agglevelsup >= context->min_sublevels_up)
			agg->agglevelsup += context->delta_sublevels_up;
		/* fall through to recurse into argument */
	}
	if (IsA(node, GroupingFunc))
	{
		GroupingFunc *grp = (GroupingFunc *) node;

		if (grp->agglevelsup >= context->min_sublevels_up)
			grp->agglevelsup += context->delta_sublevels_up;
		/* fall through to recurse into argument */
	}
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (phv->phlevelsup >= context->min_sublevels_up)
			phv->phlevelsup += context->delta_sublevels_up;
		/* fall through to recurse into argument */
	}
	if (IsA(node, ReturningExpr))
	{
		ReturningExpr *rexpr = (ReturningExpr *) node;

		if (rexpr->retlevelsup >= context->min_sublevels_up)
			rexpr->retlevelsup += context->delta_sublevels_up;
		/* fall through to recurse into argument */
	}
	if (IsA(node, RangeTblEntry))
	{
		RangeTblEntry *rte = (RangeTblEntry *) node;

		if (rte->rtekind == RTE_CTE)
		{
			if (rte->ctelevelsup >= context->min_sublevels_up)
				rte->ctelevelsup += context->delta_sublevels_up;
		}
		return false;			/* allow range_table_walker to continue */
	}
	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->min_sublevels_up++;
		result = query_tree_walker((Query *) node,
								   IncrementVarSublevelsUp_walker,
								   context,
								   QTW_EXAMINE_RTES_BEFORE);
		context->min_sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, IncrementVarSublevelsUp_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】IncrementVarSublevelsUp —— 提升整棵树的 Var 嵌套层数（对外入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对外入口。把树中所有 varlevelsup >= min_sublevels_up 的 Var 的 varlevelsup
 *   加上 delta_sublevels_up，用于"把表达式嵌入更深层子查询"前的调整。
 *
 * 参数：
 *   node              - 树根（Query 或表达式）。
 *   delta_sublevels_up- 层数增量（通常为 1）。
 *   min_sublevels_up  - 最小受影响层（初始调用通常为 0，表示所有 Var 都受影响）。
 *
 * 返回值：
 *   无（就地修改）。
 *
 * 设计思想：
 *   1. 使用 query_or_expression_tree_walker：若从 Query 开始，不会把最外层当作
 *      子查询而多自增一次层数。
 *   2. 传入 QTW_EXAMINE_RTES_BEFORE，让遍历在进入每个 RTE 的 subquery 前先处理
 *      RTE 节点本身（RTE_CTE 的 ctelevelsup 需要被调整）。
 *   3. 其余细节见 IncrementVarSublevelsUp_walker。
 * ============================================================================
 */
void
IncrementVarSublevelsUp(Node *node, int delta_sublevels_up,
						int min_sublevels_up)
{
	IncrementVarSublevelsUp_context context;

	context.delta_sublevels_up = delta_sublevels_up;
	context.min_sublevels_up = min_sublevels_up;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	query_or_expression_tree_walker(node,
									IncrementVarSublevelsUp_walker,
									&context,
									QTW_EXAMINE_RTES_BEFORE);
}

/*
 * ============================================================================
 * 【中文注释】IncrementVarSublevelsUp_rtable —— 对范围表执行层数提升
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   IncrementVarSublevelsUp 的范围表版本：对 rtable 列表（及其中的子查询）执行
 *   相同的 varlevelsup 提升。
 *
 * 参数：
 *   rtable            - 范围表（List<RangeTblEntry>）。
 *   delta_sublevels_up- 层数增量。
 *   min_sublevels_up  - 最小受影响层。
 *
 * 返回值：
 *   无（就地修改）。
 *
 * 设计思想：
 *   某些场景（如 CTE 的引用提升）需要直接对 rtable 而非整棵查询树调用该变换。
 *   用 range_table_walker 遍历范围表，同样用 QTW_EXAMINE_RTES_BEFORE 以便处理
 *   RTE 自身的 ctelevelsup 字段；其余逻辑与 IncrementVarSublevelsUp 一致。
 * ============================================================================
 */
void
IncrementVarSublevelsUp_rtable(List *rtable, int delta_sublevels_up,
							   int min_sublevels_up)
{
	IncrementVarSublevelsUp_context context;

	context.delta_sublevels_up = delta_sublevels_up;
	context.min_sublevels_up = min_sublevels_up;

	range_table_walker(rtable,
					   IncrementVarSublevelsUp_walker,
					   &context,
					   QTW_EXAMINE_RTES_BEFORE);
}

/*
 * ============================================================================
 * 【中文注释】SetVarReturningType_walker —— 设置 Var 的 RETURNING 语义标记遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   SetVarReturningType 的递归实现：把指定查询层中引用 result_relation 的所有
 *   Var 的 varreturningtype 改为指定值。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - result_relation（结果关系编号）、sublevels_up（当前层）、
 *             returning_type（要设置的值）。
 *
 * 返回值：
 *   bool - false（就地修改）。
 *
 * 设计思想：
 *   varreturningtype 标记 Var 在 RETURNING 列表中的语义（默认 / OLD / NEW）：
 *   规则展开时（如把 ON UPDATE 规则的 NEW 引用替换成实际表达式），需要把这个
 *   标记传播到展开产物里的各个 Var 上，executor 才能正确判断"该返回原行还是
 *   新行、若该行不存在则返回 NULL"。遍历骨架与其他 walker 一致（进入子查询自增
 *   层数），命中条件为 varno==result_relation 且层数匹配。
 * ============================================================================
 */

typedef struct
{
	int			result_relation;
	int			sublevels_up;
	VarReturningType returning_type;
} SetVarReturningType_context;

static bool
SetVarReturningType_walker(Node *node, SetVarReturningType_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varno == context->result_relation &&
			var->varlevelsup == context->sublevels_up)
			var->varreturningtype = context->returning_type;

		return false;
	}

	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node, SetVarReturningType_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, SetVarReturningType_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】SetVarReturningType —— 设置表达式树中 Var 的 RETURNING 语义标记
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对外入口（静态工具，供本文件内部调用）。把表达式中引用 result_relation 的
 *   Var 的 varreturningtype 设为 returning_type。
 *
 * 参数：
 *   node           - 表达式树根。
 *   result_relation- 结果关系编号（只有引用它的 Var 才被修改）。
 *   sublevels_up   - 目标查询层。
 *   returning_type - 要设置的 VarReturningType 值。
 *
 * 返回值：
 *   无（就地修改）。
 *
 * 设计思想：
 *   薄封装，初始化上下文后直接调 walker。与其它"树根可能是 Query"的入口不同，
 *   本函数约定从纯表达式开始（调用方通常是 ReplaceVarFromTargetList 对某个
 *   tlist 表达式做传播），故直接调用 walker 即可。
 * ============================================================================
 */
static void
SetVarReturningType(Node *node, int result_relation, int sublevels_up,
					VarReturningType returning_type)
{
	SetVarReturningType_context context;

	context.result_relation = result_relation;
	context.sublevels_up = sublevels_up;
	context.returning_type = returning_type;

	/* Expect to start with an expression */
	SetVarReturningType_walker(node, &context);
}

/*
 * ============================================================================
 * 【中文注释】rangeTableEntry_used_walker —— 判断 RTE 是否被引用的遍历器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   rangeTableEntry_used 的递归实现：检查树中是否存在对指定范围表的引用——包括
 *   Var（varno 或 varnullingrels 命中）、CurrentOfExpr、RangeTblRef（FROM 里的
 *   直接引用）以及 JoinExpr 的 rtindex。命中即返回 true 终止遍历。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - rt_index（待查范围表编号）与 sublevels_up（当前层）。
 *
 * 返回值：
 *   bool - true 表示发现引用并终止遍历。
 *
 * 设计思想：
 *   1. 用途：规则展开等场景需要判断"某个范围表是否还被树的某处使用"，例如视图
 *      展开后判断某 RTE 是否已无引用、能否安全移除。
 *   2. Var 的匹配包括两种情况：varno 直接等于 rt_index，或该 Var 的
 *      varnullingrels 集合中包含 rt_index（被 nulling 标记，也算对该表的引用）。
 *   3. RangeTblRef/JoinExpr 只存在于当前查询（sublevels_up==0）的 jointree 中，
 *      递归进子查询时层数自增后自然不匹配。
 *   4. 对 planner 辅助节点（PlaceHolderVar、PlanRowMark 等）用 Assert 断言不会
 *      出现——本函数通常用于未进入 planner 的查询树。
 * ============================================================================
 */

typedef struct
{
	int			rt_index;
	int			sublevels_up;
} rangeTableEntry_used_context;

static bool
rangeTableEntry_used_walker(Node *node,
							rangeTableEntry_used_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup == context->sublevels_up &&
			(var->varno == context->rt_index ||
			 bms_is_member(context->rt_index, var->varnullingrels)))
			return true;
		return false;
	}
	if (IsA(node, CurrentOfExpr))
	{
		CurrentOfExpr *cexpr = (CurrentOfExpr *) node;

		if (context->sublevels_up == 0 &&
			cexpr->cvarno == context->rt_index)
			return true;
		return false;
	}
	if (IsA(node, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) node;

		if (rtr->rtindex == context->rt_index &&
			context->sublevels_up == 0)
			return true;
		/* the subquery itself is visited separately */
		return false;
	}
	if (IsA(node, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) node;

		if (j->rtindex == context->rt_index &&
			context->sublevels_up == 0)
			return true;
		/* fall through to examine children */
	}
	/* Shouldn't need to handle planner auxiliary nodes here */
	Assert(!IsA(node, PlaceHolderVar));
	Assert(!IsA(node, PlanRowMark));
	Assert(!IsA(node, SpecialJoinInfo));
	Assert(!IsA(node, AppendRelInfo));
	Assert(!IsA(node, PlaceHolderInfo));
	Assert(!IsA(node, MinMaxAggInfo));

	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node, rangeTableEntry_used_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	return expression_tree_walker(node, rangeTableEntry_used_walker, context);
}

/*
 * ============================================================================
 * 【中文注释】rangeTableEntry_used —— 判断指定 RTE 是否被树中某处引用（对外入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对外入口。遍历查询/表达式树，判断是否存在对范围表编号 rt_index 的引用
 *   （Var、RangeTblRef、JoinExpr 等）。
 *
 * 参数：
 *   node         - 树根（Query 或表达式）。
 *   rt_index     - 待查的范围表编号。
 *   sublevels_up - 目标查询层。
 *
 * 返回值：
 *   bool - 被引用返回 true，否则 false。
 *
 * 设计思想：
 *   薄封装，用 query_or_expression_tree_walker 启动遍历并保持最外层层数语义
 *   （从 Query 开始不会多自增）；具体匹配逻辑见 walker。
 * ============================================================================
 */
bool
rangeTableEntry_used(Node *node, int rt_index, int sublevels_up)
{
	rangeTableEntry_used_context context;

	context.rt_index = rt_index;
	context.sublevels_up = sublevels_up;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	return query_or_expression_tree_walker(node,
										   rangeTableEntry_used_walker,
										   &context,
										   0);
}


/*
 * ============================================================================
 * 【中文注释】getInsertSelectQuery —— 取出 INSERT ... SELECT 中的 SELECT 子查询
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   若给定的 Query 是 INSERT ... SELECT 形式，则提取并返回其中表示 SELECT 部分
 *   的 Query；否则原样返回该 Query。可选地通过 subquery_ptr 返回指向 SELECT
 *   子查询链接位置的指针（以便调用方就地替换）。
 *
 * 参数：
 *   parsetree    - 待检查的查询。
 *   subquery_ptr - 可选输出参数：非空时被设置为指向 SELECT 子查询字段的指针
 *                  （即 &rte->subquery），以便调用方改写；非 INSERT ... SELECT
 *                  时置为 NULL。
 *
 * 返回值：
 *   Query* - SELECT 子查询，或原 Query。
 *
 * 设计思想：
 *   1. 为什么需要这个"hack"？规则动作里的 INSERT ... SELECT 在做变换（比如
 *      AdjustVarSublevelsUp、视图展开）时，应该作用在**数据来源的 SELECT**上，
 *      而不是 INSERT 外壳上——例如 OLD/NEW 伪行占位 RTE 可能被下推到了 SELECT
 *      的 rtable 里。直接把变换应用到 INSERT 部分会漏改或改错。
 *   2. 判定过程：
 *      - 非 INSERT 命令直接返回原查询。
 *      - 若 INSERT 的 rtable 前两个位置仍是规则占位符 "old"/"new"
 *        （PRS2_OLD_VARNO/PRS2_NEW_VARNO），说明还没有被下推，直接返回原查询。
 *      - 否则，期望其 jointree 是单元素 FROM，且该 RTE 是类型为 SELECT 的
 *        RTE_SUBQUERY；取出它的 subquery。再检查该 SELECT 的 rtable 前两个位置
 *        是否为 old/new 占位符——是则说明占位符已下推至此，返回该 SELECT 并通过
 *        subquery_ptr 暴露其链接位置。
 *   3. 任何结构不符都会 elog 报错（期望一定找得到占位符）。
 * ============================================================================
 */
Query *
getInsertSelectQuery(Query *parsetree, Query ***subquery_ptr)
{
	Query	   *selectquery;
	RangeTblEntry *selectrte;
	RangeTblRef *rtr;

	if (subquery_ptr)
		*subquery_ptr = NULL;

	if (parsetree == NULL)
		return parsetree;
	if (parsetree->commandType != CMD_INSERT)
		return parsetree;

	/*
	 * Currently, this is ONLY applied to rule-action queries, and so we
	 * expect to find the OLD and NEW placeholder entries in the given query.
	 * If they're not there, it must be an INSERT/SELECT in which they've been
	 * pushed down to the SELECT.
	 */
	if (list_length(parsetree->rtable) >= 2 &&
		strcmp(rt_fetch(PRS2_OLD_VARNO, parsetree->rtable)->eref->aliasname,
			   "old") == 0 &&
		strcmp(rt_fetch(PRS2_NEW_VARNO, parsetree->rtable)->eref->aliasname,
			   "new") == 0)
		return parsetree;
	Assert(parsetree->jointree && IsA(parsetree->jointree, FromExpr));
	if (list_length(parsetree->jointree->fromlist) != 1)
		elog(ERROR, "expected to find SELECT subquery");
	rtr = (RangeTblRef *) linitial(parsetree->jointree->fromlist);
	if (!IsA(rtr, RangeTblRef))
		elog(ERROR, "expected to find SELECT subquery");
	selectrte = rt_fetch(rtr->rtindex, parsetree->rtable);
	if (!(selectrte->rtekind == RTE_SUBQUERY &&
		  selectrte->subquery &&
		  IsA(selectrte->subquery, Query) &&
		  selectrte->subquery->commandType == CMD_SELECT))
		elog(ERROR, "expected to find SELECT subquery");
	selectquery = selectrte->subquery;
	if (list_length(selectquery->rtable) >= 2 &&
		strcmp(rt_fetch(PRS2_OLD_VARNO, selectquery->rtable)->eref->aliasname,
			   "old") == 0 &&
		strcmp(rt_fetch(PRS2_NEW_VARNO, selectquery->rtable)->eref->aliasname,
			   "new") == 0)
	{
		if (subquery_ptr)
			*subquery_ptr = &(selectrte->subquery);
		return selectquery;
	}
	elog(ERROR, "could not find rule placeholders");
	return NULL;				/* not reached */
}


/*
 * ============================================================================
 * 【中文注释】AddQual —— 把给定条件并入查询的 WHERE 子句
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把条件表达式 qual 与查询原有的 WHERE 条件做 AND 合并后写回。是规则/视图
 *   展开时为查询追加过滤条件的主要工具（如规则的事件条件、安全策略等）。
 *
 * 参数：
 *   parsetree - 目标查询（必须是普通 DML/SELECT，不能是 UTILITY 或 SETOP）。
 *   qual      - 要追加的条件（可为 NULL，此时不做任何事）。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 特殊情况处理：
 *      - UTILITY 语句没有位置放条件：NOTIFY 被**静默忽略**条件（因为多发一次
 *        NOTIFY 无害，比拒绝执行整个规则有用），其他 utility 语句直接报错
 *        （目前也不允许这种情况出现，保留检查只是以防万一）。
 *      - SETOP（UNION/INTERSECT/EXCEPT）查询同样没有合适的条件位置，直接报错
 *        （planner 会忽略其 WHERE，为避免静默错误而拒绝）。
 *   2. 用 copyObject 复制 qual 再用 make_and_qual 与原条件 AND 合并，避免共享
 *      引用导致的问题。
 *   3. 合并后断言条件中不含聚合（把聚合塞进 WHERE 是非法的），并维护
 *      hasSubLinks 标志：若查询原本没有子链接而新条件引入了，则更新标志。
 * ============================================================================
 */
void
AddQual(Query *parsetree, Node *qual)
{
	Node	   *copy;

	if (qual == NULL)
		return;

	if (parsetree->commandType == CMD_UTILITY)
	{
		/*
		 * There's noplace to put the qual on a utility statement.
		 *
		 * If it's a NOTIFY, silently ignore the qual; this means that the
		 * NOTIFY will execute, whether or not there are any qualifying rows.
		 * While clearly wrong, this is much more useful than refusing to
		 * execute the rule at all, and extra NOTIFY events are harmless for
		 * typical uses of NOTIFY.
		 *
		 * If it isn't a NOTIFY, error out, since unconditional execution of
		 * other utility stmts is unlikely to be wanted.  (This case is not
		 * currently allowed anyway, but keep the test for safety.)
		 */
		if (parsetree->utilityStmt && IsA(parsetree->utilityStmt, NotifyStmt))
			return;
		else
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("conditional utility statements are not implemented")));
	}

	if (parsetree->setOperations != NULL)
	{
		/*
		 * There's noplace to put the qual on a setop statement, either. (This
		 * could be fixed, but right now the planner simply ignores any qual
		 * condition on a setop query.)
		 */
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("conditional UNION/INTERSECT/EXCEPT statements are not implemented")));
	}

	/* INTERSECT wants the original, but we need to copy - Jan */
	copy = copyObject(qual);

	parsetree->jointree->quals = make_and_qual(parsetree->jointree->quals,
											   copy);

	/*
	 * We had better not have stuck an aggregate into the WHERE clause.
	 */
	Assert(!contain_aggs_of_level(copy, 0));

	/*
	 * Make sure query is marked correctly if added qual has sublinks. Need
	 * not search qual when query is already marked.
	 */
	if (!parsetree->hasSubLinks)
		parsetree->hasSubLinks = checkExprHasSubLink(copy);
}


/*
 * ============================================================================
 * 【中文注释】AddInvertedQual —— 把给定条件的"反条件"并入 WHERE
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对条件 qual 做"反转"后追加到查询的 WHERE 子句。这里的反转是
 *   "x IS NOT TRUE"，而不是简单的 "NOT x"。
 *
 * 参数：
 *   parsetree - 目标查询。
 *   qual      - 要被反转并追加的条件。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   为什么用 IS NOT TRUE 而不是 NOT？三值逻辑下，x 为 NULL 时 NOT x 也是 NULL，
 *   而 WHERE 条件在 NULL 时**不匹配**（语义上等于 false），所以 NOT x 在 x=NULL
 *   时反而会匹配——这常常不是我们想要的。而 x IS NOT TRUE 在 x 为 false 或 NULL
 *   时都为真，保证"不满足 x 的行全部被保留"，与"排除满足 x 的行"的直觉一致。
 *   典型用法：规则条件取反后加到动作查询的 WHERE，实现"否则"分支。
 *   实现上构造一个 BooleanTest（IS_NOT_TRUE）节点包住 qual，再交给 AddQual。
 * ============================================================================
 */
void
AddInvertedQual(Query *parsetree, Node *qual)
{
	BooleanTest *invqual;

	if (qual == NULL)
		return;

	/* Need not copy input qual, because AddQual will... */
	invqual = makeNode(BooleanTest);
	invqual->arg = (Expr *) qual;
	invqual->booltesttype = IS_NOT_TRUE;
	invqual->location = -1;

	AddQual(parsetree, (Node *) invqual);
}


/*
 * ============================================================================
 * 【中文注释】add_nulling_relids —— 给指定 Vars/PHVs 追加 nulling 关系集合
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历（并拷贝）查询/表达式树，找出引用 target_relids 中任一关系的 Var 和
 *   PlaceHolderVar，把 added_relids 并入它们的 varnullingrels / phnullingrels。
 *   target_relids 为 NULL 时，修改所有第 0 层的 Var 与 PHV。
 *
 * 参数：
 *   node         - 树根（Query 或表达式）。
 *   target_relids- 目标关系集合：引用这些关系的 Var 才被修改；NULL 表示全部。
 *   added_relids - 要并入 nulling 集合的关系集合。
 *
 * 返回值：
 *   Node* - 修改后的新树（本函数是真正的 mutator，会复制节点）。
 *
 * 设计思想：
 *   1. 背景：varnullingrels 记录"该 Var 在向外冒泡时经过哪些被 nulling 的关系"。
 *      当规则/视图展开导致某些 RTE 被标记为 nullable（例如通过外连接/反连接
 *      求值后置空）时，需要把这些关系记录进相关 Var，以便 executor 在行缺失时
 *      正确置空。add_nulling_relids 用于"新增"这类标记。
 *   2. 用 query_or_expression_tree_mutator 启动，sublevels_up 初始为 0；mutator
 *      对命中的 Var 做 copyObject 后修改字段，对命中的 PHV 只浅拷贝（memcpy）
 *      并改 phnullingrels——注释强调假设 PHV 仍会在原层求值、只是在上升途中被
 *      nulling，因此不深入其内部表达式。
 *   3. PHV 的匹配条件用 bms_overlap(phrels, target_relids)，因为 PHV 可同时挂靠
 *      多个关系。
 * ============================================================================
 */
Node *
add_nulling_relids(Node *node,
				   const Bitmapset *target_relids,
				   const Bitmapset *added_relids)
{
	add_nulling_relids_context context;

	context.target_relids = target_relids;
	context.added_relids = added_relids;
	context.sublevels_up = 0;
	return query_or_expression_tree_mutator(node,
											add_nulling_relids_mutator,
											&context,
											0);
}

/*
 * ============================================================================
 * 【中文注释】add_nulling_relids_mutator —— 追加 nulling 关系的具体递归实现
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   add_nulling_relids 的 mutator 实现：逐节点复制树，对命中条件的 Var/PHV
 *   修改其 nulling 关系集合后返回拷贝，其余节点按通用 mutator 复制。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - target_relids、added_relids 与当前 sublevels_up。
 *
 * 返回值：
 *   Node* - 处理后的新节点。
 *
 * 设计思想：
 *   1. Var：命中（层数匹配且 varno 属于 target_relids，或 target 为 NULL）时，
 *      用 bms_union 合并 varnullingrels 与 added_relids，copyObject 出拷贝后替换
 *      字段返回。不命中则 fall through 让通用 mutator 正常复制。
 *   2. PlaceHolderVar：命中条件为 phlevelsup 匹配且 phrels 与 target_relids 有
 *      交集；修改时**只**浅拷贝节点（makeNode+memcpy）改 phnullingrels，不深入
 *      其内部表达式——注释解释这是假定 PHV 求值层级不变。
 *   3. Query：进入子查询时 sublevels_up 自增，用 query_tree_mutator 递归。
 * ============================================================================
 */
static Node *
add_nulling_relids_mutator(Node *node,
						   add_nulling_relids_context *context)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup == context->sublevels_up &&
			(context->target_relids == NULL ||
			 bms_is_member(var->varno, context->target_relids)))
		{
			Relids		newnullingrels = bms_union(var->varnullingrels,
												   context->added_relids);

			/* Copy the Var ... */
			var = copyObject(var);
			/* ... and replace the copy's varnullingrels field */
			var->varnullingrels = newnullingrels;
			return (Node *) var;
		}
		/* Otherwise fall through to copy the Var normally */
	}
	else if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (phv->phlevelsup == context->sublevels_up &&
			(context->target_relids == NULL ||
			 bms_overlap(phv->phrels, context->target_relids)))
		{
			Relids		newnullingrels = bms_union(phv->phnullingrels,
												   context->added_relids);

			/*
			 * We don't modify the contents of the PHV's expression, only add
			 * to phnullingrels.  This corresponds to assuming that the PHV
			 * will be evaluated at the same level as before, then perhaps be
			 * nulled as it bubbles up.  Hence, just flat-copy the node ...
			 */
			phv = makeNode(PlaceHolderVar);
			memcpy(phv, node, sizeof(PlaceHolderVar));
			/* ... and replace the copy's phnullingrels field */
			phv->phnullingrels = newnullingrels;
			return (Node *) phv;
		}
		/* Otherwise fall through to copy the PlaceHolderVar normally */
	}
	else if (IsA(node, Query))
	{
		/* Recurse into RTE or sublink subquery */
		Query	   *newnode;

		context->sublevels_up++;
		newnode = query_tree_mutator((Query *) node,
									 add_nulling_relids_mutator,
									 context,
									 0);
		context->sublevels_up--;
		return (Node *) newnode;
	}
	return expression_tree_mutator(node, add_nulling_relids_mutator, context);
}

/*
 * ============================================================================
 * 【中文注释】remove_nulling_relids —— 从 Vars/PHVs 移除指定的 nulling 关系
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历（并拷贝）查询/表达式树，从 Var 的 varnullingrels 与 PlaceHolderVar 的
 *   phnullingrels（及 phrels）中移除 removable_relids 里的关系，但属于
 *   except_relids 中关系的节点除外。
 *
 * 参数：
 *   node            - 树根（Query 或表达式）。
 *   removable_relids- 要从 nulling 集合中移除的关系集合。
 *   except_relids   - 例外：引用这些关系的 Var/PHV 不做修改。
 *
 * 返回值：
 *   Node* - 修改后的新树。
 *
 * 设计思想：
 *   1. 与 add_nulling_relids 相反：当某些关系不再会被 nulling（如相应的外连接
 *      被消除、规则改写去掉了 nullable 语义）时，清除对应的记录，避免 executor
 *      做出错误的置空。
 *   2. Var 命中条件：层数匹配、varno 不在 except_relids 中、且其 varnullingrels
 *      与 removable_relids 有交集。PHV 命中条件为 phlevelsup 匹配且 phrels 与
 *      except_relids 无交集——对 PHV 额外要从 phrels 中一并移除可移除的关系。
 *   3. 对 PHV 的一个谨慎点：即使 phnullingrels 清空也不删除 PHV 节点本身，因为
 *      PHV 有时被用来强制子表达式的身份唯一（见 prepjointree.c 的 wrap_option），
 *      删除会破坏语义。
 * ============================================================================
 */
Node *
remove_nulling_relids(Node *node,
					  const Bitmapset *removable_relids,
					  const Bitmapset *except_relids)
{
	remove_nulling_relids_context context;

	context.removable_relids = removable_relids;
	context.except_relids = except_relids;
	context.sublevels_up = 0;
	return query_or_expression_tree_mutator(node,
											remove_nulling_relids_mutator,
											&context,
											0);
}

/*
 * ============================================================================
 * 【中文注释】remove_nulling_relids_mutator —— 移除 nulling 关系的递归实现
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   remove_nulling_relids 的 mutator 实现：复制节点树，对命中的 Var/PHV 移除
 *   指定关系后返回新节点。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - removable_relids、except_relids 与当前 sublevels_up。
 *
 * 返回值：
 *   Node* - 处理后的新节点。
 *
 * 设计思想：
 *   1. Var：命中时用 bms_difference 从 varnullingrels 中扣除 removable_relids，
 *      再 copyObject 替换字段返回。
 *   2. PlaceHolderVar：用 expression_tree_mutator 先深度复制其内部表达式，再修改
 *      phnullingrels（bms_difference）与 phrels（同样扣减，因为 phrels 中若含可
 *      移除的关系也应同步清理）；随后用 Assert 确保 phrels 非空。
 *   3. Query：层数自增后用 query_tree_mutator 递归。
 * ============================================================================
 */
static Node *
remove_nulling_relids_mutator(Node *node,
							  remove_nulling_relids_context *context)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varlevelsup == context->sublevels_up &&
			!bms_is_member(var->varno, context->except_relids) &&
			bms_overlap(var->varnullingrels, context->removable_relids))
		{
			/* Copy the Var ... */
			var = copyObject(var);
			/* ... and replace the copy's varnullingrels field */
			var->varnullingrels = bms_difference(var->varnullingrels,
												 context->removable_relids);
			return (Node *) var;
		}
		/* Otherwise fall through to copy the Var normally */
	}
	else if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (phv->phlevelsup == context->sublevels_up &&
			!bms_overlap(phv->phrels, context->except_relids))
		{
			/*
			 * Note: it might seem desirable to remove the PHV altogether if
			 * phnullingrels goes to empty.  Currently we dare not do that
			 * because we use PHVs in some cases to enforce separate identity
			 * of subexpressions; see wrap_option usages in prepjointree.c.
			 */
			/* Copy the PlaceHolderVar and mutate what's below ... */
			phv = (PlaceHolderVar *)
				expression_tree_mutator(node,
										remove_nulling_relids_mutator,
										context);
			/* ... and replace the copy's phnullingrels field */
			phv->phnullingrels = bms_difference(phv->phnullingrels,
												context->removable_relids);
			/* We must also update phrels, if it contains a removable RTI */
			phv->phrels = bms_difference(phv->phrels,
										 context->removable_relids);
			Assert(!bms_is_empty(phv->phrels));
			return (Node *) phv;
		}
		/* Otherwise fall through to copy the PlaceHolderVar normally */
	}
	else if (IsA(node, Query))
	{
		/* Recurse into RTE or sublink subquery */
		Query	   *newnode;

		context->sublevels_up++;
		newnode = query_tree_mutator((Query *) node,
									 remove_nulling_relids_mutator,
									 context,
									 0);
		context->sublevels_up--;
		return (Node *) newnode;
	}
	return expression_tree_mutator(node, remove_nulling_relids_mutator, context);
}


/*
 * ============================================================================
 * 【中文注释】replace_rte_variables —— 用回调替换引用指定 RTE 的所有 Var
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历（并拷贝）查询/表达式树，把其中引用 target_varno 且处于指定查询层的
 *   所有 Var 替换为"调用方回调返回的替代表达式"。这是视图展开、规则动作替换
 *   （如把 NEW/OLD 引用换成具体表达式）的核心基础设施。
 *
 * 参数：
 *   node             - 树根（Query 或表达式）。
 *   target_varno     - 要被替换的 RTE 编号。
 *   sublevels_up     - 目标查询层。
 *   callback         - 用户回调：对每个命中的 Var 调用，返回替代表达式。
 *   callback_arg     - 透传给回调的上下文指针。
 *   outer_hasSubLinks- 可选：若 node 是某查询的一部分，传该查询 hasSubLinks 字段
 *                      的地址；若为 NULL，往非 Query 表达式里插入 SubLink 会报错。
 *
 * 返回值：
 *   Node* - 替换后的新树。
 *
 * 设计思想：
 *   1. 回调机制把"替换成什么"与"在哪替换"解耦，本函数只负责精准地找到目标 Var。
 *   2. inserted_sublink 追踪：替换产物可能引入新的 SubLink（例如把视图列替换成
 *      一个子查询表达式）。替换完成后需要把对应查询的 hasSubLinks 置为 true。
 *      初始化策略：若根是 Query 且其已有子链接，直接视为"无需再检测"；否则从
 *      outer_hasSubLinks 读取。
 *   3. 遍历过程在 mutator 里维护 inserted_sublink：进入子查询前保存现场、把
 *      该子查询自己的 hasSubLinks 作为初始值，返回后 OR 回去——这样即使替换在
 *      深层子查询里引入了 SubLink，也能准确回填。
 *   4. 为什么不处理 hasAggs/hasWindowFuncs 的类似回填？因为该变换不可能向子查询
 *      插入"属于子查询自身的第 0 层聚合/窗口函数"，最多插入外层引用，那些标志
 *      无需更新。
 *   5. 特意暴露 mutator 与 context 结构：回调常希望对返回表达式的子部分直接递归
 *      调用 mutator，简化实现。
 * ============================================================================
 */
Node *
replace_rte_variables(Node *node, int target_varno, int sublevels_up,
					  replace_rte_variables_callback callback,
					  void *callback_arg,
					  bool *outer_hasSubLinks)
{
	Node	   *result;
	replace_rte_variables_context context;

	context.callback = callback;
	context.callback_arg = callback_arg;
	context.target_varno = target_varno;
	context.sublevels_up = sublevels_up;

	/*
	 * We try to initialize inserted_sublink to true if there is no need to
	 * detect new sublinks because the query already has some.
	 */
	if (node && IsA(node, Query))
		context.inserted_sublink = ((Query *) node)->hasSubLinks;
	else if (outer_hasSubLinks)
		context.inserted_sublink = *outer_hasSubLinks;
	else
		context.inserted_sublink = false;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	result = query_or_expression_tree_mutator(node,
											  replace_rte_variables_mutator,
											  &context,
											  0);

	if (context.inserted_sublink)
	{
		if (result && IsA(result, Query))
			((Query *) result)->hasSubLinks = true;
		else if (outer_hasSubLinks)
			*outer_hasSubLinks = true;
		else
			elog(ERROR, "replace_rte_variables inserted a SubLink, but has noplace to record it");
	}

	return result;
}

/*
 * ============================================================================
 * 【中文注释】replace_rte_variables_mutator —— 变量替换的具体递归实现
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   replace_rte_variables 的 mutator 实现：复制节点树，遇到命中目标 RTE 与层的
 *   Var 时调用回调生成替换表达式；进入子查询时维护 inserted_sublink 追踪。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - 回调、target_varno、当前层与 inserted_sublink 追踪标志。
 *
 * 返回值：
 *   Node* - 处理后的新节点。
 *
 * 设计思想：
 *   1. Var 命中时调用回调获得 newnode；若尚未标记 inserted_sublink，用
 *      checkExprHasSubLink 检查替换产物是否引入了 SubLink，有则标记——这保证最终
 *      返回后外层能把 hasSubLinks 置位。
 *   2. Query：进入前保存 inserted_sublink 现场，用该子查询自身的 hasSubLinks
 *      作为本层初始值，递归后把结果 OR 进新节点的 hasSubLinks，再恢复现场并
 *      层数减一。这套"存取现场"的写法保证深层替换产生的子链接信息能正确汇聚。
 *   3. 其他节点交给 expression_tree_mutator 复制。
 * ============================================================================
 */
Node *
replace_rte_variables_mutator(Node *node,
							  replace_rte_variables_context *context)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varno == context->target_varno &&
			var->varlevelsup == context->sublevels_up)
		{
			/* Found a matching variable, make the substitution */
			Node	   *newnode;

			newnode = context->callback(var, context);
			/* Detect if we are adding a sublink to query */
			if (!context->inserted_sublink)
				context->inserted_sublink = checkExprHasSubLink(newnode);
			return newnode;
		}
		/* otherwise fall through to copy the var normally */
	}
	else if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		Query	   *newnode;
		bool		save_inserted_sublink;

		context->sublevels_up++;
		save_inserted_sublink = context->inserted_sublink;
		context->inserted_sublink = ((Query *) node)->hasSubLinks;
		newnode = query_tree_mutator((Query *) node,
									 replace_rte_variables_mutator,
									 context,
									 0);
		newnode->hasSubLinks |= context->inserted_sublink;
		context->inserted_sublink = save_inserted_sublink;
		context->sublevels_up--;
		return (Node *) newnode;
	}
	return expression_tree_mutator(node, replace_rte_variables_mutator, context);
}


/*
 * ============================================================================
 * 【中文注释】map_variable_attnos_mutator —— 重映射 Var 列号的具体递归实现
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   map_variable_attnos 的 mutator 实现：复制节点树，对引用目标 RTE 的 Var 按
 *   attno_map 重新映射 varattno（系统列不动、整行 Var 特殊处理），并在必要时
 *   处理 ConvertRowtypeExpr 的化简。
 *
 * 参数：
 *   node    - 当前节点。
 *   context - target_varno、当前层、attno_map、to_rowtype、found_whole_row。
 *
 * 返回值：
 *   Node* - 处理后的新节点。
 *
 * 设计思想：
 *   1. 普通列（varattno>0）：查表得到新列号；映射数组中的 0 表示被丢弃的列，若
 *      表达式里引用了它则报错（丢弃列不应出现在表达式中）。同时若 varnosyn 仍
 *      指向目标 RTE，同步修正 varattnosyn 以保持语法引用一致。
 *   2. 整行 Var（varattno==0）：置 found_whole_row=true 提醒调用方；若调用方
 *      提供了 to_rowtype 且与当前类型不同，把 Var 的 vartype 改为 to_rowtype
 *      （要求是目标 RTE 行类型的子类型），再在顶层包一个 ConvertRowtypeExpr 转回
 *      原类型，保证表达式其余部分期望的类型不变。RECORD 变量不支持此转换。
 *   3. ConvertRowtypeExpr 的化简：若某个 CRE 的参数正好是"需要转换的整行 Var"，
 *      直接把 Var 换成 to_rowtype 并让 CRE 的结果类型仍为外层所需——等价于把
 *      var::parenttype::grandparenttype 化简成 var::grandparenttype，避免重复
 *      应用本函数时堆积大量 CRE 节点。
 *   4. 不用 replace_rte_variables 实现的原因：本函数从不插入 SubLink，用那个
 *      更复杂的基础设施是杀鸡用牛刀。
 * ============================================================================
 */

typedef struct
{
	int			target_varno;	/* RTE index to search for */
	int			sublevels_up;	/* (current) nesting depth */
	const AttrMap *attno_map;	/* map array for user attnos */
	Oid			to_rowtype;		/* change whole-row Vars to this type */
	bool	   *found_whole_row;	/* output flag */
} map_variable_attnos_context;

static Node *
map_variable_attnos_mutator(Node *node,
							map_variable_attnos_context *context)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		if (var->varno == context->target_varno &&
			var->varlevelsup == context->sublevels_up)
		{
			/* Found a matching variable, make the substitution */
			Var		   *newvar = palloc_object(Var);
			int			attno = var->varattno;

			*newvar = *var;		/* initially copy all fields of the Var */

			if (attno > 0)
			{
				/* user-defined column, replace attno */
				if (attno > context->attno_map->maplen ||
					context->attno_map->attnums[attno - 1] == 0)
					elog(ERROR, "unexpected varattno %d in expression to be mapped",
						 attno);
				newvar->varattno = context->attno_map->attnums[attno - 1];
				/* If the syntactic referent is same RTE, fix it too */
				if (newvar->varnosyn == context->target_varno)
					newvar->varattnosyn = newvar->varattno;
			}
			else if (attno == 0)
			{
				/* whole-row variable, warn caller */
				*(context->found_whole_row) = true;

				/* If the caller expects us to convert the Var, do so. */
				if (OidIsValid(context->to_rowtype) &&
					context->to_rowtype != var->vartype)
				{
					ConvertRowtypeExpr *r;

					/* This certainly won't work for a RECORD variable. */
					Assert(var->vartype != RECORDOID);

					/* Var itself is changed to the requested type. */
					newvar->vartype = context->to_rowtype;

					/*
					 * Add a conversion node on top to convert back to the
					 * original type expected by the expression.
					 */
					r = makeNode(ConvertRowtypeExpr);
					r->arg = (Expr *) newvar;
					r->resulttype = var->vartype;
					r->convertformat = COERCE_IMPLICIT_CAST;
					r->location = -1;

					return (Node *) r;
				}
			}
			return (Node *) newvar;
		}
		/* otherwise fall through to copy the var normally */
	}
	else if (IsA(node, ConvertRowtypeExpr))
	{
		ConvertRowtypeExpr *r = (ConvertRowtypeExpr *) node;
		Var		   *var = (Var *) r->arg;

		/*
		 * If this is coercing a whole-row Var that we need to convert, then
		 * just convert the Var without adding an extra ConvertRowtypeExpr.
		 * Effectively we're simplifying var::parenttype::grandparenttype into
		 * just var::grandparenttype.  This avoids building stacks of CREs if
		 * this function is applied repeatedly.
		 */
		if (IsA(var, Var) &&
			var->varno == context->target_varno &&
			var->varlevelsup == context->sublevels_up &&
			var->varattno == 0 &&
			OidIsValid(context->to_rowtype) &&
			context->to_rowtype != var->vartype)
		{
			ConvertRowtypeExpr *newnode;
			Var		   *newvar = palloc_object(Var);

			/* whole-row variable, warn caller */
			*(context->found_whole_row) = true;

			*newvar = *var;		/* initially copy all fields of the Var */

			/* This certainly won't work for a RECORD variable. */
			Assert(var->vartype != RECORDOID);

			/* Var itself is changed to the requested type. */
			newvar->vartype = context->to_rowtype;

			newnode = palloc_object(ConvertRowtypeExpr);
			*newnode = *r;		/* initially copy all fields of the CRE */
			newnode->arg = (Expr *) newvar;

			return (Node *) newnode;
		}
		/* otherwise fall through to process the expression normally */
	}
	else if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		Query	   *newnode;

		context->sublevels_up++;
		newnode = query_tree_mutator((Query *) node,
									 map_variable_attnos_mutator,
									 context,
									 0);
		context->sublevels_up--;
		return (Node *) newnode;
	}
	return expression_tree_mutator(node, map_variable_attnos_mutator, context);
}

/*
 * ============================================================================
 * 【中文注释】map_variable_attnos —— 按映射数组重映射引用指定 RTE 的列号
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对外入口。遍历（并拷贝）查询/表达式树，把引用 target_varno 的 Var 的
 *   varattno 按 attno_map 重映射（varattno n -> attno_map[n-1]）。系统列不变。
 *   若遇到整行 Var，置 found_whole_row 并通过 to_rowtype 可选地转换类型。
 *
 * 参数：
 *   node           - 树根（Query 或表达式）。
 *   target_varno   - 目标 RTE 编号。
 *   sublevels_up   - 目标查询层。
 *   attno_map      - 用户列映射数组（0 表示丢弃列，不应出现在表达式中）。
 *   to_rowtype     - 整行 Var 要转换成的行类型；InvalidOid 表示不转换。
 *   found_whole_row- 输出：若树中存在整行 Var 则置为 true。
 *
 * 返回值：
 *   Node* - 重映射后的新树。
 *
 * 设计思想：
 *   1. 典型用途：把引用视图 RTE 的 Var 改写为引用底表 RTE 的 Var 时，视图列与
 *      底表列的序号往往不同，需要按视图定义时的映射关系重排。
 *   2. 未提供 to_rowtype 且 found_whole_row 为 true 的调用方应自行报错——本函数
 *      不知道最合适的错误文案，由调用方根据上下文决定。
 *   3. 初始把 *found_whole_row 清 false，再以 query_or_expression_tree_mutator
 *      启动遍历（保持最外层层数语义）。
 * ============================================================================
 */
Node *
map_variable_attnos(Node *node,
					int target_varno, int sublevels_up,
					const AttrMap *attno_map,
					Oid to_rowtype, bool *found_whole_row)
{
	map_variable_attnos_context context;

	context.target_varno = target_varno;
	context.sublevels_up = sublevels_up;
	context.attno_map = attno_map;
	context.to_rowtype = to_rowtype;
	context.found_whole_row = found_whole_row;

	*found_whole_row = false;

	/*
	 * Must be prepared to start with a Query or a bare expression tree; if
	 * it's a Query, we don't want to increment sublevels_up.
	 */
	return query_or_expression_tree_mutator(node,
											map_variable_attnos_mutator,
											&context,
											0);
}


/*
 * ============================================================================
 * 【中文注释】ReplaceVarsFromTargetList —— 用目标列表中的项替换 Var（对外入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历（并拷贝）查询/表达式树，把引用 target_varno 且处于指定层的 Var 替换为
 *   targetlist 中 resno 匹配的项；整行 Var 展开为 RowExpr；处理 OLD/NEW RETURNING
 *   语义与未命中选项。这是视图展开与规则动作（尤其 UPDATE/DELETE 的 NEW/OLD
 *   替换）的重要基础工具。
 *
 * 参数：
 *   node             - 树根（Query 或表达式）。
 *   target_varno     - 要被替换的 RTE 编号。
 *   sublevels_up     - 目标查询层。
 *   target_rte       - 目标 RTE（用于展开整行 Var 的列清单）。
 *   targetlist       - 提供替换项的 SELECT 目标列表。
 *   result_relation  - 改写后查询中结果关系的编号（处理 OLD/NEW RETURNING Var 用；
 *                      非 DML 场景可传 0）。
 *   nomatch_option   - 未命中时的策略（见下）。
 *   nomatch_varno    - REPLACEVARS_CHANGE_VARNO 时要改成的编号。
 *   outer_hasSubLinks- 同 replace_rte_variables。
 *
 * 返回值：
 *   Node* - 替换后的新树。
 *
 * 设计思想：
 *   1. 未命中策略（nomatch_option）：
 *      - REPORT_ERROR：直接报错（默认最严格）。
 *      - CHANGE_VARNO：把 Var 的 varno 改为 nomatch_varno（用于把对 OLD 的引用
 *        改到 OLD 对应 RTE、对 NEW 改到结果关系等）。
 *      - SUBSTITUTE_NULL：用同类型 NULL 常量替换（含域类型需包 CoerceToDomain，
 *        防止违反 NOT NULL 域约束）。
 *   2. 整行 Var：通过 expandRTE 展开成各列 Var 的 RowExpr；命名行类型（普通表）
 *      要补丢弃列的哑元项，RECORD 类型（JOIN 结果）则省略并附列名。生成结果
 *      统一用 varlevelsup=0，调用方按需再提升——便于缓存替换表达式。
 *   3. OLD/NEW RETURNING 语义：若被替换 Var 的 varreturningtype 非默认，把该标记
 *      传播到引用 result_relation 的替换 Vars；若替换表达式不是"直接引用结果关系
 *      的 Var"，包一层 ReturningExpr，使 executor 在 OLD/NEW 行不存在时返回 NULL。
 *   4. 特殊检查：替换项里若含 PARAM_MULTIEXPR 则报错——ON UPDATE 规则里 NEW 引用
 *      的列若属于原 UPDATE 的多值赋值（行式赋值），无法安全展开，按未实现处理。
 * ============================================================================
 */

typedef struct
{
	RangeTblEntry *target_rte;
	List	   *targetlist;
	int			result_relation;
	ReplaceVarsNoMatchOption nomatch_option;
	int			nomatch_varno;
} ReplaceVarsFromTargetList_context;

/*
 * ============================================================================
 * 【中文注释】ReplaceVarsFromTargetList_callback —— 适配 replace_rte_variables 的回调
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 ReplaceVarFromTargetList 包装成 replace_rte_variables 需要的回调：对每个
 *   命中的 Var 生成替换表达式，并修正 varlevelsup。
 *
 * 参数：
 *   var     - 命中的 Var。
 *   context - replace_rte_variables 的上下文，其 callback_arg 指向
 *             ReplaceVarsFromTargetList_context。
 *
 * 返回值：
 *   Node* - 替代表达式。
 *
 * 设计思想：
 *   1. 从 context->callback_arg 解出 ReplaceVarsFromTargetList_context，然后委托
 *      ReplaceVarFromTargetList 完成真正的替换逻辑。
 *   2. 关键一步：ReplaceVarFromTargetList 生成的表达式 varlevelsup 固定为 0；若被
 *      替换的 Var 位于子查询里（var->varlevelsup > 0），这里用
 *      IncrementVarSublevelsUp 把替换表达式整体提升到对应层数，保证引用层级正确。
 * ============================================================================
 */
static Node *
ReplaceVarsFromTargetList_callback(const Var *var,
								   replace_rte_variables_context *context)
{
	ReplaceVarsFromTargetList_context *rcon = (ReplaceVarsFromTargetList_context *) context->callback_arg;
	Node	   *newnode;

	newnode = ReplaceVarFromTargetList(var,
									   rcon->target_rte,
									   rcon->targetlist,
									   rcon->result_relation,
									   rcon->nomatch_option,
									   rcon->nomatch_varno);

	/* Must adjust varlevelsup if replaced Var is within a subquery */
	if (var->varlevelsup > 0)
		IncrementVarSublevelsUp(newnode, var->varlevelsup, 0);

	return newnode;
}

/*
 * ============================================================================
 * 【中文注释】ReplaceVarFromTargetList —— 单个 Var 的目标列表替换（核心）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为一个 Var 生成其替换表达式：普通列去 targetlist 中按 resno 找对应项；整行
 *   Var 展开为 RowExpr 并逐字段递归替换；同时处理未命中策略与 OLD/NEW RETURNING
 *   语义。生成的表达式 varlevelsup 恒为 0（由调用方负责提升）。
 *
 * 参数：
 *   var            - 待替换的 Var。
 *   target_rte     - 目标 RTE（展开整行 Var 需要其列定义）。
 *   targetlist     - 提供替换项的列表。
 *   result_relation- 结果关系编号（RETURNING 语义用）。
 *   nomatch_option - 未命中策略。
 *   nomatch_varno  - CHANGE_VARNO 时的目标编号。
 *
 * 返回值：
 *   Node* - 替换表达式。
 *
 * 设计思想：
 *   1. 整行 Var（varattno == InvalidAttrNumber）：调用 expandRTE 展开成逐列 Var
 *      列表。命名行类型（普通表 RTE）须含丢弃列哑元项；RECORD 类型（JOIN）省略
 *      并附带列名。展开出的每个字段 Var 再递归调用本函数处理（这样字段级也可能
 *      命中/未命中），最后组装成 RowExpr。展开时把 varreturningtype 复制到每个
 *      字段 Var 上保证后续递归语义正确；需要时再包 ReturningExpr。
 *   2. 普通列：get_tle_by_resno 找 resno 匹配的 TargetEntry；找不到或该项是
 *      resjunk（内部条目）时按 nomatch_option 处理。找到时复制 tle->expr 返回，
 *      并检查其中的 MULTIEXPR 参数（见上）。
 *   3. 缓存友好设计：所有输出 varlevelsup=0，调用方可放心缓存（如视图展开中
 *      对每个列的替换结果）。
 *   4. 域类型注意：SUBSTITUTE_NULL 时若 Var 是域类型，用 coerce_null_to_domain
 *      保证 NULL 满足域的 NOT NULL 约束检查结构。
 * ============================================================================
 */
Node *
ReplaceVarFromTargetList(const Var *var,
						 RangeTblEntry *target_rte,
						 List *targetlist,
						 int result_relation,
						 ReplaceVarsNoMatchOption nomatch_option,
						 int nomatch_varno)
{
	TargetEntry *tle;

	if (var->varattno == InvalidAttrNumber)
	{
		/* Must expand whole-tuple reference into RowExpr */
		RowExpr    *rowexpr;
		List	   *colnames;
		List	   *fields;
		ListCell   *lc;

		/*
		 * If generating an expansion for a var of a named rowtype (ie, this
		 * is a plain relation RTE), then we must include dummy items for
		 * dropped columns.  If the var is RECORD (ie, this is a JOIN), then
		 * omit dropped columns.  In the latter case, attach column names to
		 * the RowExpr for use of the executor and ruleutils.c.
		 *
		 * In order to be able to cache the results, we always generate the
		 * expansion with varlevelsup = 0.  The caller is responsible for
		 * adjusting it if needed.
		 *
		 * The varreturningtype is copied onto each individual field Var, so
		 * that it is handled correctly when we recurse.
		 */
		expandRTE(target_rte,
				  var->varno, 0 /* not varlevelsup */ ,
				  var->varreturningtype, var->location,
				  (var->vartype != RECORDOID),
				  &colnames, &fields);
		rowexpr = makeNode(RowExpr);
		/* the fields will be set below */
		rowexpr->args = NIL;
		rowexpr->row_typeid = var->vartype;
		rowexpr->row_format = COERCE_IMPLICIT_CAST;
		rowexpr->colnames = (var->vartype == RECORDOID) ? colnames : NIL;
		rowexpr->location = var->location;
		/* Adjust the generated per-field Vars... */
		foreach(lc, fields)
		{
			Node	   *field = lfirst(lc);

			if (field && IsA(field, Var))
				field = ReplaceVarFromTargetList((Var *) field,
												 target_rte,
												 targetlist,
												 result_relation,
												 nomatch_option,
												 nomatch_varno);
			rowexpr->args = lappend(rowexpr->args, field);
		}

		/* Wrap it in a ReturningExpr, if needed, per comments above */
		if (var->varreturningtype != VAR_RETURNING_DEFAULT)
		{
			ReturningExpr *rexpr = makeNode(ReturningExpr);

			rexpr->retlevelsup = 0;
			rexpr->retold = (var->varreturningtype == VAR_RETURNING_OLD);
			rexpr->retexpr = (Expr *) rowexpr;

			return (Node *) rexpr;
		}

		return (Node *) rowexpr;
	}

	/* Normal case referencing one targetlist element */
	tle = get_tle_by_resno(targetlist, var->varattno);

	if (tle == NULL || tle->resjunk)
	{
		/* Failed to find column in targetlist */
		switch (nomatch_option)
		{
			case REPLACEVARS_REPORT_ERROR:
				/* fall through, throw error below */
				break;

			case REPLACEVARS_CHANGE_VARNO:
				{
					Var		   *newvar = copyObject(var);

					newvar->varno = nomatch_varno;
					newvar->varlevelsup = 0;
					/* we leave the syntactic referent alone */
					return (Node *) newvar;
				}

			case REPLACEVARS_SUBSTITUTE_NULL:
				{
					/*
					 * If Var is of domain type, we must add a CoerceToDomain
					 * node, in case there is a NOT NULL domain constraint.
					 */
					int16		vartyplen;
					bool		vartypbyval;

					get_typlenbyval(var->vartype, &vartyplen, &vartypbyval);
					return coerce_null_to_domain(var->vartype,
												 var->vartypmod,
												 var->varcollid,
												 vartyplen,
												 vartypbyval);
				}
		}
		elog(ERROR, "could not find replacement targetlist entry for attno %d",
			 var->varattno);
		return NULL;			/* keep compiler quiet */
	}
	else
	{
		/* Make a copy of the tlist item to return */
		Expr	   *newnode = copyObject(tle->expr);

		/*
		 * Check to see if the tlist item contains a PARAM_MULTIEXPR Param,
		 * and throw error if so.  This case could only happen when expanding
		 * an ON UPDATE rule's NEW variable and the referenced tlist item in
		 * the original UPDATE command is part of a multiple assignment. There
		 * seems no practical way to handle such cases without multiple
		 * evaluation of the multiple assignment's sub-select, which would
		 * create semantic oddities that users of rules would probably prefer
		 * not to cope with.  So treat it as an unimplemented feature.
		 */
		if (contains_multiexpr_param((Node *) newnode, NULL))
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("NEW variables in ON UPDATE rules cannot reference columns that are part of a multiple assignment in the subject UPDATE command")));

		/* Handle any OLD/NEW RETURNING list Vars */
		if (var->varreturningtype != VAR_RETURNING_DEFAULT)
		{
			/*
			 * Copy varreturningtype onto any Vars in the tlist item that
			 * refer to result_relation (which had better be non-zero).
			 */
			if (result_relation == 0)
				elog(ERROR, "variable returning old/new found outside RETURNING list");

			SetVarReturningType((Node *) newnode, result_relation,
								0, var->varreturningtype);

			/* Wrap it in a ReturningExpr, if needed, per comments above */
			if (!IsA(newnode, Var) ||
				((Var *) newnode)->varno != result_relation ||
				((Var *) newnode)->varlevelsup != 0)
			{
				ReturningExpr *rexpr = makeNode(ReturningExpr);

				rexpr->retlevelsup = 0;
				rexpr->retold = (var->varreturningtype == VAR_RETURNING_OLD);
				rexpr->retexpr = newnode;

				newnode = (Expr *) rexpr;
			}
		}

		return (Node *) newnode;
	}
}

/*
 * ============================================================================
 * 【中文注释】ReplaceVarsFromTargetList —— 对整棵树执行目标列表替换（入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对外入口：把整个查询/表达式树中引用 target_varno 的 Var 替换为 targetlist
 *   中对应项，具体策略见 ReplaceVarFromTargetList 与 ReplaceVarsFromTargetList
 *   上方的注释。本质上就是把 replace_rte_variables 与上述回调组合起来。
 *
 * 参数：
 *   node             - 树根。
 *   target_varno     - 目标 RTE 编号。
 *   sublevels_up     - 目标查询层。
 *   target_rte       - 目标 RTE。
 *   targetlist       - 替换项列表。
 *   result_relation  - 结果关系编号。
 *   nomatch_option   - 未命中策略。
 *   nomatch_varno    - CHANGE_VARNO 目标编号。
 *   outer_hasSubLinks- 同 replace_rte_variables。
 *
 * 返回值：
 *   Node* - 替换后的新树。
 *
 * 设计思想：
 *   薄封装：初始化 context 后直接调用 replace_rte_variables，把
 *   ReplaceVarsFromTargetList_callback 与 context 一起传入。所有复杂的遍历、
 *   层数维护、hasSubLinks 回填逻辑都复用 replace_rte_variables。
 * ============================================================================
 */
Node *
ReplaceVarsFromTargetList(Node *node,
						  int target_varno, int sublevels_up,
						  RangeTblEntry *target_rte,
						  List *targetlist,
						  int result_relation,
						  ReplaceVarsNoMatchOption nomatch_option,
						  int nomatch_varno,
						  bool *outer_hasSubLinks)
{
	ReplaceVarsFromTargetList_context context;

	context.target_rte = target_rte;
	context.targetlist = targetlist;
	context.result_relation = result_relation;
	context.nomatch_option = nomatch_option;
	context.nomatch_varno = nomatch_varno;

	return replace_rte_variables(node, target_varno, sublevels_up,
								 ReplaceVarsFromTargetList_callback,
								 &context,
								 outer_hasSubLinks);
}
