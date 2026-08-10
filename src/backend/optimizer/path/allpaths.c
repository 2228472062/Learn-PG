/*-------------------------------------------------------------------------
 *
 * allpaths.c
 *	  Routines to find possible search paths for processing a query
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 优化器路径生成的"顶层入口",负责为一个查询找出
 * 所有可能的执行路径(Path)。路径生成大体分两层,本文件驱动的是"扫描/连接"
 * 这一层:
 *
 * - 入口函数 make_one_rel() 按固定的四个阶段推进:
 *   1) set_base_rel_consider_startup():标记哪些基础关系值得考虑"快速启动"
 *      (fast-start)参数化路径(主要是 SEMI/ANTI 连接的内侧);
 *   2) set_base_rel_sizes():为每个基础关系估算行数/宽度,并决定是否考虑
 *      并行扫描(consider_parallel);
 *   3) setup_simple_grouped_rels():对简单关系构建"分组的简单关系"
 *      (grouped rel),为急切聚合(eager aggregation,即先做部分聚合)做准备;
 *   4) set_base_rel_pathlists() + make_rel_from_joinlist():先为每个基础关系
 *      生成扫描路径,再按 joinlist(连接树)用动态规划自底向上生成连接路径,
 *      最终返回代表"所有基础关系连接结果"的一个 RelOptInfo。
 *
 * 【设计思想】
 * - 基础关系按 RTE 类型分发:普通表(set_plain_rel_*)、继承/分区表
 *   (set_append_rel_*,把每个子表当作成员逐个子计划后再合成 Append 路径)、
 *   外表(set_foreign_*,委托 FDW)、子查询(set_subquery_*,递归调用
 *   subquery_planner)、函数 / VALUES / CTE / 工作表 / Result 等。大小估算
 *   (set_*_size)与路径生成(set_*_pathlist)分两遍完成:先全部估算完大小,
 *   路径生成时才能利用统一的行数估计。
 * - 继承/分区(Append 关系)是重点:子关系可能与父表有不同的大小;若某个子表
 *   能被约束排除(constraint exclusion)则标记为 dummy 并跳过;所有存活子表
 *   的路径被聚合成 Append 路径(无序),或当子表自带排序时聚合成 MergeAppend
 *   路径,或当分区键天然有序时直接合成有序的 Append 路径;还支持并行 Append
 *   (部分子路径用 worker 扫描、部分由 leader 扫描)。
 * - 并行:create_plain_partial_paths() 等函数生成 partial 路径,
 *   generate_gather_paths() / generate_useful_gather_paths() 在其上套一层
 *   Gather / Gather Merge 变成完整路径;compute_parallel_worker() 按表大小
 *   的对数估算 worker 数量。
 * - 连接顺序搜索:make_rel_from_joinlist() 对 joinlist 中的每个节点递归,
 *   单节点直接返回;多节点则按 levels_needed 走 standard_join_search() 的
 *   动态规划(逐层生成 2 路、3 路……连接),也可以被 GEQO 或用户插件替换。
 * - 本文件末尾还实现了两套"下推"支持:把上层限制条件下推进子查询
 *   (subquery_is_pushdown_safe / qual_is_pushdown_safe / subquery_push_qual
 *   等,逐条判断安全性、按 setop 树递归、最后改写子查询的 WHERE/HAVING),
 *   以及删除子查询未使用的输出列(remove_unused_subquery_outputs)。
 * - 急切聚合:eager aggregation 允许在连接之前就按 group 子句做部分聚合,
 *   grouped rel(RelOptInfo->grouped_rel,配 RelAggInfo)承载这一信息,
 *   generate_grouped_paths() 为它生成 AGG_SORTED / AGG_HASHED 的部分聚合路径。
 *
 * 【与其它模块的关系】
 * - 所有路径的"构造"(把 Path 结构填好、加入 rel 的 pathlist)由 pathnode.c
 *   完成,本文件只是调用它们;
 * - 路径的成本由 costsize.c 估算、索引路径的细节由 indxpath.c 处理、
 *   等价类/排序键信息由 equivclass.c 维护;
 * - set_cheapest()(pathnode.c)在每个关系路径生成完毕后挑选最便宜路径,
 *   供上层(planagg.c/planner.c)决定最终执行计划。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/path/allpaths.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <limits.h>
#include <math.h>

#include "access/sysattr.h"
#include "access/tsmapi.h"
#include "catalog/pg_class.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "foreign/fdwapi.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/supportnodes.h"
#ifdef OPTIMIZER_DEBUG
#include "nodes/print.h"
#endif
#include "optimizer/appendinfo.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/geqo.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/plancat.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/tlist.h"
#include "parser/parse_clause.h"
#include "parser/parsetree.h"
#include "partitioning/partbounds.h"
#include "port/pg_bitutils.h"
#include "rewrite/rewriteManip.h"
#include "utils/lsyscache.h"
#include "utils/selfuncs.h"


/* Bitmask flags for pushdown_safety_info.unsafeFlags */
#define UNSAFE_HAS_VOLATILE_FUNC		(1 << 0)
#define UNSAFE_HAS_SET_FUNC				(1 << 1)
#define UNSAFE_NOTIN_DISTINCTON_CLAUSE	(1 << 2)
#define UNSAFE_NOTIN_PARTITIONBY_CLAUSE	(1 << 3)
#define UNSAFE_TYPE_MISMATCH			(1 << 4)

/* results of subquery_is_pushdown_safe */
typedef struct pushdown_safety_info
{
	unsigned char *unsafeFlags; /* bitmask of reasons why this target list
								 * column is unsafe for qual pushdown, or 0 if
								 * no reason. */
	bool		unsafeVolatile; /* don't push down volatile quals */
	bool		unsafeLeaky;	/* don't push down leaky quals */
} pushdown_safety_info;

/* Return type for qual_is_pushdown_safe */
typedef enum pushdown_safe_type
{
	PUSHDOWN_UNSAFE,			/* unsafe to push qual into subquery */
	PUSHDOWN_SAFE,				/* safe to push qual into subquery */
	PUSHDOWN_WINDOWCLAUSE_RUNCOND,	/* unsafe, but may work as WindowClause
									 * run condition */
} pushdown_safe_type;

/* These parameters are set by GUC */
bool		enable_geqo = false;	/* just in case GUC doesn't set it */
bool		enable_eager_aggregate = true;
int			geqo_threshold;
double		min_eager_agg_group_size;
int			min_parallel_table_scan_size;
int			min_parallel_index_scan_size;

/* Hook for plugins to get control in set_rel_pathlist() */
set_rel_pathlist_hook_type set_rel_pathlist_hook = NULL;

/* Hook for plugins to replace standard_join_search() */
join_search_hook_type join_search_hook = NULL;


static void set_base_rel_consider_startup(PlannerInfo *root);
static void set_base_rel_sizes(PlannerInfo *root);
static void setup_simple_grouped_rels(PlannerInfo *root);
static void set_base_rel_pathlists(PlannerInfo *root);
static void set_rel_size(PlannerInfo *root, RelOptInfo *rel,
						 Index rti, RangeTblEntry *rte);
static void set_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
							 Index rti, RangeTblEntry *rte);
static void set_plain_rel_size(PlannerInfo *root, RelOptInfo *rel,
							   RangeTblEntry *rte);
static void create_plain_partial_paths(PlannerInfo *root, RelOptInfo *rel);
static void set_rel_consider_parallel(PlannerInfo *root, RelOptInfo *rel,
									  RangeTblEntry *rte);
static void set_plain_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
								   RangeTblEntry *rte);
static void set_tablesample_rel_size(PlannerInfo *root, RelOptInfo *rel,
									 RangeTblEntry *rte);
static void set_tablesample_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
										 RangeTblEntry *rte);
static void set_foreign_size(PlannerInfo *root, RelOptInfo *rel,
							 RangeTblEntry *rte);
static void set_foreign_pathlist(PlannerInfo *root, RelOptInfo *rel,
								 RangeTblEntry *rte);
static void set_append_rel_size(PlannerInfo *root, RelOptInfo *rel,
								Index rti, RangeTblEntry *rte);
static void set_append_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
									Index rti, RangeTblEntry *rte);
static void set_grouped_rel_pathlist(PlannerInfo *root, RelOptInfo *rel);
static void generate_orderedappend_paths(PlannerInfo *root, RelOptInfo *rel,
										 List *live_childrels,
										 List *all_child_pathkeys);
static Path *get_cheapest_parameterized_child_path(PlannerInfo *root,
												   RelOptInfo *rel,
												   Relids required_outer);
static void accumulate_append_subpath(Path *path,
									  List **subpaths,
									  List **special_subpaths,
									  List **child_append_relid_sets);
static Path *get_singleton_append_subpath(Path *path,
										  List **child_append_relid_sets);
static void set_dummy_rel_pathlist(RelOptInfo *rel);
static void set_subquery_pathlist(PlannerInfo *root, RelOptInfo *rel,
								  Index rti, RangeTblEntry *rte);
static void set_function_pathlist(PlannerInfo *root, RelOptInfo *rel,
								  RangeTblEntry *rte);
static void set_values_pathlist(PlannerInfo *root, RelOptInfo *rel,
								RangeTblEntry *rte);
static void set_tablefunc_pathlist(PlannerInfo *root, RelOptInfo *rel,
								   RangeTblEntry *rte);
static void set_cte_pathlist(PlannerInfo *root, RelOptInfo *rel,
							 RangeTblEntry *rte);
static void set_namedtuplestore_pathlist(PlannerInfo *root, RelOptInfo *rel,
										 RangeTblEntry *rte);
static void set_result_pathlist(PlannerInfo *root, RelOptInfo *rel,
								RangeTblEntry *rte);
static void set_worktable_pathlist(PlannerInfo *root, RelOptInfo *rel,
								   RangeTblEntry *rte);
static RelOptInfo *make_rel_from_joinlist(PlannerInfo *root, List *joinlist);
static bool subquery_is_pushdown_safe(Query *subquery, Query *topquery,
									  pushdown_safety_info *safetyInfo);
static bool recurse_pushdown_safe(Node *setOp, Query *topquery,
								  pushdown_safety_info *safetyInfo);
static void check_output_expressions(Query *subquery,
									 pushdown_safety_info *safetyInfo);
static void compare_tlist_datatypes(List *tlist, List *colTypes,
									pushdown_safety_info *safetyInfo);
static bool targetIsInAllPartitionLists(TargetEntry *tle, Query *query);
static pushdown_safe_type qual_is_pushdown_safe(Query *subquery, Index rti,
												RestrictInfo *rinfo,
												pushdown_safety_info *safetyInfo);
static Oid	pushdown_var_grouping_eqop(Var *var, void *context);
static Oid	subquery_column_grouping_eqop(Query *subquery, AttrNumber attno);
static Oid	setop_column_grouping_eqop(Node *setop, AttrNumber attno);
static bool setop_has_grouping(Node *setop);
static void subquery_push_qual(Query *subquery,
							   RangeTblEntry *rte, Index rti, Node *qual);
static void recurse_push_qual(Node *setOp, Query *topquery,
							  RangeTblEntry *rte, Index rti, Node *qual);
static void remove_unused_subquery_outputs(Query *subquery, RelOptInfo *rel,
										   Bitmapset *extra_used_attrs);


/*
 * make_one_rel
 *	  Finds all possible access paths for executing a query, returning a
 *	  single rel that represents the join of all base rels in the query.
 */
/*
 * make_one_rel - (中文)查询路径生成的顶层入口:为整个查询找出所有访问路径
 *
 * 【作用】由 planner.c 的 query_planner() 调用,负责生成整棵查询的路径集合。
 * 它按顺序完成四件事:决定哪些基础关系要考虑快速启动路径;为所有基础关系
 * 估算大小并决定是否允许并行;构建"分组的简单关系"(为急切聚合做准备);
 * 为每个基础关系生成扫描路径、再按 joinlist 动态规划生成连接路径。最终返回
 * 代表"所有基础关系(含被 SEMI/ANTI 连接特殊处理的外连接关系)连接结果"的
 * 单一 RelOptInfo,它是本查询扫描/连接阶段路径搜索的终点。
 *
 * 【设计思想】这是整个"扫描+连接"路径生成阶段的分层骨架:
 * - 大小估算(set_base_rel_sizes)必须先于路径生成(set_base_rel_pathlists),
 *   因为参数化路径、并行判定、连接大小估计都需要行数;而
 *   consider_parallel 又必须先于 set_rel_size,因为继承/分区父关系会复用并
 *   修改子关系的该标志;
 * - total_table_pages 在这里汇总:只统计"简单关系"(继承/分区父关系的
 *   pages 保持为 0,避免重复计数),它用于后续 seq_page_cost 等整体成本计算;
 * - 自连接的表会被重复计数一次(代码注释承认这是已知的不精确点);
 * - 路径搜索在 make_rel_from_joinlist() 内部选择:只有一个 joinlist 节点时
 *   直接返回;否则用 standard_join_search(动态规划)、GEQO 或插件钩子。
 *
 * 【参数】
 *   root     —— 正在规划的查询级 PlannerInfo(含解析树、关系数组、
 *               joininfo 等全部规划上下文);
 *   joinlist —— 由 deconstruct_jointree() 生成的连接树扁平化表示,是嵌套
 *               列表:RangeTblRef 代表单个基础关系,List 代表一个连接子问题。
 * 【返回值】一个 RelOptInfo,其 relids 恰好等于 root->all_query_rels
 *           (即全部基础关系 + 外连接关系)。其 pathlist 中包含到达最终
 *           连接结果的全部候选路径;调用者从中挑选(通过 set_cheapest)
 *           生成最终执行计划。
 */
RelOptInfo *
make_one_rel(PlannerInfo *root, List *joinlist)
{
	RelOptInfo *rel;
	Index		rti;
	double		total_pages;

	/* Mark base rels as to whether we care about fast-start plans */
	set_base_rel_consider_startup(root);

	/*
	 * Compute size estimates and consider_parallel flags for each base rel.
	 */
	set_base_rel_sizes(root);

	/*
	 * Build grouped relations for simple rels (i.e., base or "other" member
	 * relations) where possible.
	 */
	setup_simple_grouped_rels(root);

	/*
	 * We should now have size estimates for every actual table involved in
	 * the query, and we also know which if any have been deleted from the
	 * query by join removal, pruned by partition pruning, or eliminated by
	 * constraint exclusion.  So we can now compute total_table_pages.
	 *
	 * Note that appendrels are not double-counted here, even though we don't
	 * bother to distinguish RelOptInfos for appendrel parents, because the
	 * parents will have pages = 0.
	 *
	 * XXX if a table is self-joined, we will count it once per appearance,
	 * which perhaps is the wrong thing ... but that's not completely clear,
	 * and detecting self-joins here is difficult, so ignore it for now.
	 */
	total_pages = 0;
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (brel == NULL)
			continue;

		Assert(brel->relid == rti); /* sanity check on array */

		if (IS_DUMMY_REL(brel))
			continue;

		if (IS_SIMPLE_REL(brel))
			total_pages += (double) brel->pages;
	}
	root->total_table_pages = total_pages;

	/*
	 * Generate access paths for each base rel.
	 */
	set_base_rel_pathlists(root);

	/*
	 * Generate access paths for the entire join tree.
	 */
	rel = make_rel_from_joinlist(root, joinlist);

	/*
	 * The result should join all and only the query's base + outer-join rels.
	 */
	Assert(bms_equal(rel->relids, root->all_query_rels));

	return rel;
}

/*
 * set_base_rel_consider_startup
 *	  Set the consider_[param_]startup flags for each base-relation entry.
 *
 * For the moment, we only deal with consider_param_startup here; because the
 * logic for consider_startup is pretty trivial and is the same for every base
 * relation, we just let build_simple_rel() initialize that flag correctly to
 * start with.  If that logic ever gets more complicated it would probably
 * be better to move it here.
 */
/*
 * set_base_rel_consider_startup - (中文)标记需要"快速启动"参数化路径的基础关系
 *
 * 【作用】在路径生成的第一个阶段(make_one_rel 中第一个调用)扫描
 * root->join_info_list,对每个"右侧恰好只有一个基础关系"的 SEMI/ANTI 连接,
 * 把该内侧重置为 rel->consider_param_startup = true。它不处理
 * consider_startup(普通启动成本),因为 build_simple_rel() 已按简单规则初始化
 * 好了那个标志。
 *
 * 【设计思想】参数化路径只能用作嵌套循环连接的内侧;对普通连接而言考虑
 * "快速启动"方案价值不大。但 SEMI/ANTI 连接只要找到(或证明不存在)一个
 * 匹配元组就停止,快速启动可以显著减少无谓扫描,因此对这类内侧重置该标志。
 * 出于规划开销考虑,只限定"内侧是单个基础关系"(连接关系、appendrel 一律
 * 不处理),且 costsize.c 的 nestloop semi/anti 成本公式也只覆盖这种情况。
 *
 * 【参数】
 *   root —— PlannerInfo,其 join_info_list 保存所有 SpecialJoinInfo。
 * 【返回值】无。
 */
static void
set_base_rel_consider_startup(PlannerInfo *root)
{
	/*
	 * Since parameterized paths can only be used on the inside of a nestloop
	 * join plan, there is usually little value in considering fast-start
	 * plans for them.  However, for relations that are on the RHS of a SEMI
	 * or ANTI join, a fast-start plan can be useful because we're only going
	 * to care about fetching one tuple anyway.
	 *
	 * To minimize growth of planning time, we currently restrict this to
	 * cases where the RHS is a single base relation, not a join; there is no
	 * provision for consider_param_startup to get set at all on joinrels.
	 * Also we don't worry about appendrels.  costsize.c's costing rules for
	 * nestloop semi/antijoins don't consider such cases either.
	 */
	ListCell   *lc;

	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(lc);
		int			varno;

		if ((sjinfo->jointype == JOIN_SEMI || sjinfo->jointype == JOIN_ANTI) &&
			bms_get_singleton_member(sjinfo->syn_righthand, &varno))
		{
			RelOptInfo *rel = find_base_rel(root, varno);

			rel->consider_param_startup = true;
		}
	}
}

/*
 * set_base_rel_sizes
 *	  Set the size estimates (rows and widths) for each base-relation entry.
 *	  Also determine whether to consider parallel paths for base relations.
 *
 * We do this in a separate pass over the base rels so that rowcount
 * estimates are available for parameterized path generation, and also so
 * that each rel's consider_parallel flag is set correctly before we begin to
 * generate paths.
 */
/*
 * set_base_rel_sizes - (中文)为所有基础关系设置大小估算与并行标志
 *
 * 【作用】遍历 root->simple_rel_array 中每个 RELOPT_BASEREL 基础关系,依次
 * 调用 set_rel_consider_parallel(决定能否并行扫描该关系)与 set_rel_size
 * (估算行数、宽度等)。由 make_one_rel() 在路径生成之前调用。
 *
 * 【设计思想】分两件事、按固定先后做:先确定 consider_parallel,再估大小。
 * 理由:继承/分区父关系在 set_append_rel_size() 中会读取(并可能改坏)子
 * 关系的 consider_parallel,若大小先算则可能拿到过时值;另外某些 RTE 类型
 * (如子查询、CTE)在 set_rel_size 内就立即生成路径了。大小估算集中先做完,
 * 好处是所有关系的行数在生成参数化路径之前都已可用。数组里的空槽位
 * (对应非基础 RTE)与"other rel"(继承子关系等)被跳过。
 *
 * 【参数】
 *   root —— PlannerInfo,simple_rel_array 是其基础关系数组。
 * 【返回值】无(通过修改各 RelOptInfo 返回结果)。
 */
static void
set_base_rel_sizes(PlannerInfo *root)
{
	Index		rti;

	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *rel = root->simple_rel_array[rti];
		RangeTblEntry *rte;

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (rel == NULL)
			continue;

		Assert(rel->relid == rti);	/* sanity check on array */

		/* ignore RTEs that are "other rels" */
		if (rel->reloptkind != RELOPT_BASEREL)
			continue;

		rte = root->simple_rte_array[rti];

		/*
		 * If parallelism is allowable for this query in general, see whether
		 * it's allowable for this rel in particular.  We have to do this
		 * before set_rel_size(), because (a) if this rel is an inheritance
		 * parent, set_append_rel_size() will use and perhaps change the rel's
		 * consider_parallel flag, and (b) for some RTE types, set_rel_size()
		 * goes ahead and makes paths immediately.
		 */
		if (root->glob->parallelModeOK)
			set_rel_consider_parallel(root, rel, rte);

		set_rel_size(root, rel, rti, rte);
	}
}

/*
 * setup_simple_grouped_rels
 *	  For each simple relation, build a grouped simple relation if eager
 *	  aggregation is possible and if this relation can produce grouped paths.
 */
/*
 * setup_simple_grouped_rels - (中文)为简单关系构建"分组的简单关系"
 *
 * 【作用】在 set_base_rel_sizes() 之后、set_base_rel_pathlists() 之前调用,
 * 遍历所有简单关系(基础关系或继承子关系),对每个调用
 * build_simple_grouped_rel(root, rel) 尝试构造 grouped rel。这是急切聚合
 * (eager aggregation)的准备工作:把 group by / 聚合信息挂在关系上,后续
 * generate_grouped_paths() 就能在连接之前先生成部分聚合路径。
 *
 * 【设计思想】只有当查询确实含有聚合表达式和分组表达式(即
 * root->agg_clause_list 与 group_expr_list 均非空)时,急切聚合才有意义,
 * 否则直接返回。build_simple_grouped_rel() 内部会判断该关系能否产生分组
 * 路径(例如必须能排序或哈希分组),不能则留空。注意这里处理的是"简单"
 * 关系;连接关系(joinrel)的 grouped rel 是在 standard_join_search() 里按层
 * 生成的。
 *
 * 【参数】
 *   root —— PlannerInfo,其中 agg_clause_list / group_expr_list 由
 *           preprocess_agg_aggregates 等预处理阶段填充。
 * 【返回值】无。
 */
static void
setup_simple_grouped_rels(PlannerInfo *root)
{
	Index		rti;

	/*
	 * If there are no aggregate expressions or grouping expressions, eager
	 * aggregation is not possible.
	 */
	if (root->agg_clause_list == NIL ||
		root->group_expr_list == NIL)
		return;

	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *rel = root->simple_rel_array[rti];

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (rel == NULL)
			continue;

		Assert(rel->relid == rti);	/* sanity check on array */
		Assert(IS_SIMPLE_REL(rel)); /* sanity check on rel */

		(void) build_simple_grouped_rel(root, rel);
	}
}

/*
 * set_base_rel_pathlists
 *	  Finds all paths available for scanning each base-relation entry.
 *	  Sequential scan and any available indices are considered.
 *	  Each useful path is attached to its relation's 'pathlist' field.
 */
/*
 * set_base_rel_pathlists - (中文)为所有基础关系生成扫描路径
 *
 * 【作用】遍历 simple_rel_array 中每个 RELOPT_BASEREL 基础关系,逐个调用
 * set_rel_pathlist() 为该关系生成所有可用的扫描路径(顺序扫描、索引扫描、
 * 并行扫描、FDW 路径等),并挂到 rel->pathlist。由 make_one_rel() 在大小
 * 估算与 grouped rel 准备之后调用。
 *
 * 【设计思想】大小与路径分两步走的核心原因:路径生成(尤其是参数化路径、
 * 并行路径)依赖已经就绪的行数与 consider_parallel 标志。这里只处理
 * RELOPT_BASEREL,继承子关系(RELOPT_OTHER_MEMBER_REL)等 "other rel" 由
 * set_append_rel_pathlist() 递归处理,不会再在本函数重复。
 *
 * 【参数】
 *   root —— PlannerInfo,simple_rel_array 是基础关系数组。
 * 【返回值】无(路径写入各 rel->pathlist)。
 */
static void
set_base_rel_pathlists(PlannerInfo *root)
{
	Index		rti;

	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *rel = root->simple_rel_array[rti];

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (rel == NULL)
			continue;

		Assert(rel->relid == rti);	/* sanity check on array */

		/* ignore RTEs that are "other rels" */
		if (rel->reloptkind != RELOPT_BASEREL)
			continue;

		set_rel_pathlist(root, rel, rti, root->simple_rte_array[rti]);
	}
}

/*
 * set_rel_size
 *	  Set size estimates for a base relation
 */
/*
 * set_rel_size - (中文)设置单个基础关系的大小估算
 *
 * 【作用】根据关系的类型为单个基础关系估算行数/宽度。被 set_base_rel_sizes()
 * 对每个基础关系调用;也被 set_append_rel_size() 递归地对每个继承子关系调用。
 * 内部先尝试约束排除(constraint exclusion):能证明关系为空则立即置为 dummy
 * 关系;否则按 RTE 类型分发到具体的估算函数。
 *
 * 【设计思想】
 * - 约束排除只对普通基础关系做(继承子关系的约束排除已在
 *   set_append_rel_size() 里做过),证明为空时通过 set_dummy_rel_pathlist()
 *   立刻生成 dummy 路径,这是"把关系标记为空"的唯一约定机制;
 * - rte->inh 表示继承/分区:走 set_append_rel_size() 汇总所有子表大小;
 * - 非继承时按 rtekind 分发:RTE_RELATION 再细分为外表(FDW 估算)、
 *   分区表(带 ONLY 时不允许扫描分区,置 dummy)、采样表(TABLESAMPLE,
 *   调用采样方法的估算例程)、普通表;子查询、CTE 等类型因不支持"参数化/
 *   非参数化路径的选择",直接在估算阶段就生成路径(即不遵循"先估大小再
 *   生成路径"的两阶段约定)。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 待估算的关系;
 *   rti  —— rel 在 rtable 中的索引(用于约束排除等);
 *   rte  —— 对应的 RangeTblEntry。
 * 【返回值】无。结束时满足不变量:非 dummy 关系的 rel->rows > 0。
 */
static void
set_rel_size(PlannerInfo *root, RelOptInfo *rel,
			 Index rti, RangeTblEntry *rte)
{
	if (rel->reloptkind == RELOPT_BASEREL &&
		relation_excluded_by_constraints(root, rel, rte))
	{
		/*
		 * We proved we don't need to scan the rel via constraint exclusion,
		 * so set up a single dummy path for it.  Here we only check this for
		 * regular baserels; if it's an otherrel, CE was already checked in
		 * set_append_rel_size().
		 *
		 * In this case, we go ahead and set up the relation's path right away
		 * instead of leaving it for set_rel_pathlist to do.  This is because
		 * we don't have a convention for marking a rel as dummy except by
		 * assigning a dummy path to it.
		 */
		set_dummy_rel_pathlist(rel);
	}
	else if (rte->inh)
	{
		/* It's an "append relation", process accordingly */
		set_append_rel_size(root, rel, rti, rte);
	}
	else
	{
		switch (rel->rtekind)
		{
			case RTE_RELATION:
				if (rte->relkind == RELKIND_FOREIGN_TABLE)
				{
					/* Foreign table */
					set_foreign_size(root, rel, rte);
				}
				else if (rte->relkind == RELKIND_PARTITIONED_TABLE)
				{
					/*
					 * We could get here if asked to scan a partitioned table
					 * with ONLY.  In that case we shouldn't scan any of the
					 * partitions, so mark it as a dummy rel.
					 */
					set_dummy_rel_pathlist(rel);
				}
				else if (rte->tablesample != NULL)
				{
					/* Sampled relation */
					set_tablesample_rel_size(root, rel, rte);
				}
				else
				{
					/* Plain relation */
					set_plain_rel_size(root, rel, rte);
				}
				break;
			case RTE_SUBQUERY:

				/*
				 * Subqueries don't support making a choice between
				 * parameterized and unparameterized paths, so just go ahead
				 * and build their paths immediately.
				 */
				set_subquery_pathlist(root, rel, rti, rte);
				break;
			case RTE_FUNCTION:
				set_function_size_estimates(root, rel);
				break;
			case RTE_TABLEFUNC:
				set_tablefunc_size_estimates(root, rel);
				break;
			case RTE_VALUES:
				set_values_size_estimates(root, rel);
				break;
			case RTE_CTE:

				/*
				 * CTEs don't support making a choice between parameterized
				 * and unparameterized paths, so just go ahead and build their
				 * paths immediately.
				 */
				if (rte->self_reference)
					set_worktable_pathlist(root, rel, rte);
				else
					set_cte_pathlist(root, rel, rte);
				break;
			case RTE_NAMEDTUPLESTORE:
				/* Might as well just build the path immediately */
				set_namedtuplestore_pathlist(root, rel, rte);
				break;
			case RTE_RESULT:
				/* Might as well just build the path immediately */
				set_result_pathlist(root, rel, rte);
				break;
			default:
				elog(ERROR, "unexpected rtekind: %d", (int) rel->rtekind);
				break;
		}
	}

	/*
	 * We insist that all non-dummy rels have a nonzero rowcount estimate.
	 */
	Assert(rel->rows > 0 || IS_DUMMY_REL(rel));
}

/*
 * set_rel_pathlist
 *	  Build access paths for a base relation
 */
/*
 * set_rel_pathlist - (中文)为单个基础关系生成访问路径
 *
 * 【作用】为单个基础关系生成并注册所有访问路径。被 set_base_rel_pathlists()
 * 对每个基础关系调用,也被 set_append_rel_pathlist() 对每个继承子关系调用。
 * 完成后执行:调用 set_rel_pathlist_hook 让插件增删路径、对非顶层基础关系
 * 生成 Gather 路径(把 partial 路径变成完整路径)、用 set_cheapest() 找出
 * 最便宜路径、并为该关系的 grouped rel 生成部分聚合路径。
 *
 * 【设计思想】
 * - 已证明为空(dummy)的关系直接跳过;
 * - 继承关系走 set_append_rel_pathlist() 递归处理子表;
 * - 其余按 rtekind 分发,子查询/CTE/工作表和 Result 等在估算阶段已经生成
 *   过路径,这里无事可做;
 * - set_rel_pathlist_hook 被设计成可以在核心代码之后增删路径(尤其可以添加
 *   CustomPath),因此 Gather 生成必须放在 hook 调用之后,否则插件加入的
 *   partial 路径不会被汇总;
 * - 继承子关系本身不生成 Gather(否则每个子表都要抢一批 worker),统一留给
 *   父 appendrel;顶层连接关系(relids == all_query_rels)也推迟到拿到最终
 *   扫描/连接目标列表后再做(见 grouping_planner 的 apply_scanjoin_target_to_paths);
 * - set_cheapest() 必须先于 generate_grouped_paths(),后者需要关系的最便宜路径。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 待生成路径的关系;
 *   rti  —— rel 在 rtable 中的索引;
 *   rte  —— 对应的 RangeTblEntry。
 * 【返回值】无(路径写入 rel->pathlist / partial_pathlist)。
 */
static void
set_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
				 Index rti, RangeTblEntry *rte)
{
	if (IS_DUMMY_REL(rel))
	{
		/* We already proved the relation empty, so nothing more to do */
	}
	else if (rte->inh)
	{
		/* It's an "append relation", process accordingly */
		set_append_rel_pathlist(root, rel, rti, rte);
	}
	else
	{
		switch (rel->rtekind)
		{
			case RTE_RELATION:
				if (rte->relkind == RELKIND_FOREIGN_TABLE)
				{
					/* Foreign table */
					set_foreign_pathlist(root, rel, rte);
				}
				else if (rte->tablesample != NULL)
				{
					/* Sampled relation */
					set_tablesample_rel_pathlist(root, rel, rte);
				}
				else
				{
					/* Plain relation */
					set_plain_rel_pathlist(root, rel, rte);
				}
				break;
			case RTE_SUBQUERY:
				/* Subquery --- fully handled during set_rel_size */
				break;
			case RTE_FUNCTION:
				/* RangeFunction */
				set_function_pathlist(root, rel, rte);
				break;
			case RTE_TABLEFUNC:
				/* Table Function */
				set_tablefunc_pathlist(root, rel, rte);
				break;
			case RTE_VALUES:
				/* Values list */
				set_values_pathlist(root, rel, rte);
				break;
			case RTE_CTE:
				/* CTE reference --- fully handled during set_rel_size */
				break;
			case RTE_NAMEDTUPLESTORE:
				/* tuplestore reference --- fully handled during set_rel_size */
				break;
			case RTE_RESULT:
				/* simple Result --- fully handled during set_rel_size */
				break;
			default:
				elog(ERROR, "unexpected rtekind: %d", (int) rel->rtekind);
				break;
		}
	}

	/*
	 * Allow a plugin to editorialize on the set of Paths for this base
	 * relation.  It could add new paths (such as CustomPaths) by calling
	 * add_path(), or add_partial_path() if parallel aware.  It could also
	 * delete or modify paths added by the core code.
	 */
	if (set_rel_pathlist_hook)
		(*set_rel_pathlist_hook) (root, rel, rti, rte);

	/*
	 * If this is a baserel, we should normally consider gathering any partial
	 * paths we may have created for it.  We have to do this after calling the
	 * set_rel_pathlist_hook, else it cannot add partial paths to be included
	 * here.
	 *
	 * However, if this is an inheritance child, skip it.  Otherwise, we could
	 * end up with a very large number of gather nodes, each trying to grab
	 * its own pool of workers.  Instead, we'll consider gathering partial
	 * paths for the parent appendrel.
	 *
	 * Also, if this is the topmost scan/join rel, we postpone gathering until
	 * the final scan/join targetlist is available (see grouping_planner).
	 */
	if (rel->reloptkind == RELOPT_BASEREL &&
		!bms_equal(rel->relids, root->all_query_rels))
		generate_useful_gather_paths(root, rel, false);

	/* Now find the cheapest of the paths for this rel */
	set_cheapest(rel);

	/*
	 * If a grouped relation for this rel exists, build partial aggregation
	 * paths for it.
	 *
	 * Note that this can only happen after we've called set_cheapest() for
	 * this base rel, because we need its cheapest paths.
	 */
	set_grouped_rel_pathlist(root, rel);

#ifdef OPTIMIZER_DEBUG
	pprint(rel);
#endif
}

/*
 * set_plain_rel_size
 *	  Set size estimates for a plain relation (no subquery, no inheritance)
 */
/*
 * set_plain_rel_size - (中文)估算普通表关系的大小
 *
 * 【作用】对普通表(无子查询、无继承)设置行数与宽度估算。先调用
 * check_index_predicates() 检验部分索引(partial index)是否适用于该查询,
 * 再调用 set_baserel_size_estimates()(costsize.c)完成最终估算。
 *
 * 【设计思想】部分唯一索引会影响大小估计(例如部分索引暗示某些行一定唯一,
 * 影响行数下界),因此必须最先检查。set_baserel_size_estimates 会根据
 * pg_class 的统计信息、限制条件的选择性估算 rel->rows、rel->tuples、
 * rel->reltarget->width 等。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 普通表关系(RELOPT_BASEREL);
 *   rte  —— 对应的 RangeTblEntry。
 * 【返回值】无。
 */
static void
set_plain_rel_size(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	/*
	 * Test any partial indexes of rel for applicability.  We must do this
	 * first since partial unique indexes can affect size estimates.
	 */
	check_index_predicates(root, rel);

	/* Mark rel with estimated output rows, width, etc */
	set_baserel_size_estimates(root, rel);
}

/*
 * If this relation could possibly be scanned from within a worker, then set
 * its consider_parallel flag.
 */
/*
 * set_rel_consider_parallel - (中文)判定一个关系能否被并行扫描并置标志
 *
 * 【作用】如果该关系理论上可以在并行 worker 中被扫描,则把
 * rel->consider_parallel 置为 true。被 set_base_rel_sizes() 对每个基础关系
 * 调用,也被 set_append_rel_size() 对继承子关系调用。调用前要求整个查询
 * parallelModeOK 且 rel->consider_parallel 尚未被设置。
 *
 * 【设计思想】并行限制按 RTE 类型逐条检查:
 * - RTE_RELATION:worker 不能访问 leader 的临时表(临时表直接拒绝);TABLESAMPLE
 *   要求采样函数与其参数都并行安全;外表要求 FDW 声明 IsForeignScanParallelSafe;
 * - RTE_SUBQUERY:子查询含 LIMIT/OFFSET 时行顺序不可保证,拒绝;
 * - RTE_FUNCTION / RTE_VALUES:要求其中的函数并行安全;
 * - RTE_TABLEFUNC、RTE_CTE(CTE tuplestore 无法共享)、RTE_NAMEDTUPLESTORE:
 *   一律不并行;
 * - RTE_JOIN、RTE_GROUP 等不该出现在这里(断言);
 * 最后还要检查关系自身的 baserestrictinfo(限制条件)与 reltarget 表达式都
 * 不含并行受限(parallel-restricted)元素。整体思路是"只要有一处不放心就
 * 整体放弃",因为把受限条件上提再并行执行在多数场景下不是净收益,还可能
 * 破坏等价类。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 基础关系或继承子关系(IS_SIMPLE_REL);
 *   rte  —— 对应 RangeTblEntry。
 * 【返回值】无(结果写入 rel->consider_parallel)。
 */
static void
set_rel_consider_parallel(PlannerInfo *root, RelOptInfo *rel,
						  RangeTblEntry *rte)
{
	/*
	 * The flag has previously been initialized to false, so we can just
	 * return if it becomes clear that we can't safely set it.
	 */
	Assert(!rel->consider_parallel);

	/* Don't call this if parallelism is disallowed for the entire query. */
	Assert(root->glob->parallelModeOK);

	/* This should only be called for baserels and appendrel children. */
	Assert(IS_SIMPLE_REL(rel));

	/* Assorted checks based on rtekind. */
	switch (rte->rtekind)
	{
		case RTE_RELATION:

			/*
			 * Currently, parallel workers can't access the leader's temporary
			 * tables.  We could possibly relax this if we wrote all of its
			 * local buffers at the start of the query and made no changes
			 * thereafter (maybe we could allow hint bit changes), and if we
			 * taught the workers to read them.  Writing a large number of
			 * temporary buffers could be expensive, though, and we don't have
			 * the rest of the necessary infrastructure right now anyway.  So
			 * for now, bail out if we see a temporary table.
			 */
			if (get_rel_persistence(rte->relid) == RELPERSISTENCE_TEMP)
				return;

			/*
			 * Table sampling can be pushed down to workers if the sample
			 * function and its arguments are safe.
			 */
			if (rte->tablesample != NULL)
			{
				char		proparallel = func_parallel(rte->tablesample->tsmhandler);

				if (proparallel != PROPARALLEL_SAFE)
					return;
				if (!is_parallel_safe(root, (Node *) rte->tablesample->args))
					return;
			}

			/*
			 * Ask FDWs whether they can support performing a ForeignScan
			 * within a worker.  Most often, the answer will be no.  For
			 * example, if the nature of the FDW is such that it opens a TCP
			 * connection with a remote server, each parallel worker would end
			 * up with a separate connection, and these connections might not
			 * be appropriately coordinated between workers and the leader.
			 */
			if (rte->relkind == RELKIND_FOREIGN_TABLE)
			{
				Assert(rel->fdwroutine);
				if (!rel->fdwroutine->IsForeignScanParallelSafe)
					return;
				if (!rel->fdwroutine->IsForeignScanParallelSafe(root, rel, rte))
					return;
			}

			/*
			 * There are additional considerations for appendrels, which we'll
			 * deal with in set_append_rel_size and set_append_rel_pathlist.
			 * For now, just set consider_parallel based on the rel's own
			 * quals and targetlist.
			 */
			break;

		case RTE_SUBQUERY:

			/*
			 * There's no intrinsic problem with scanning a subquery-in-FROM
			 * (as distinct from a SubPlan or InitPlan) in a parallel worker.
			 * If the subquery doesn't happen to have any parallel-safe paths,
			 * then flagging it as consider_parallel won't change anything,
			 * but that's true for plain tables, too.  We must set
			 * consider_parallel based on the rel's own quals and targetlist,
			 * so that if a subquery path is parallel-safe but the quals and
			 * projection we're sticking onto it are not, we correctly mark
			 * the SubqueryScanPath as not parallel-safe.  (Note that
			 * set_subquery_pathlist() might push some of these quals down
			 * into the subquery itself, but that doesn't change anything.)
			 *
			 * We can't push sub-select containing LIMIT/OFFSET to workers as
			 * there is no guarantee that the row order will be fully
			 * deterministic, and applying LIMIT/OFFSET will lead to
			 * inconsistent results at the top-level.  (In some cases, where
			 * the result is ordered, we could relax this restriction.  But it
			 * doesn't currently seem worth expending extra effort to do so.)
			 */
			{
				Query	   *subquery = castNode(Query, rte->subquery);

				if (limit_needed(subquery))
					return;
			}
			break;

		case RTE_JOIN:
			/* Shouldn't happen; we're only considering baserels here. */
			Assert(false);
			return;

		case RTE_FUNCTION:
			/* Check for parallel-restricted functions. */
			if (!is_parallel_safe(root, (Node *) rte->functions))
				return;
			break;

		case RTE_TABLEFUNC:
			/* not parallel safe */
			return;

		case RTE_VALUES:
			/* Check for parallel-restricted functions. */
			if (!is_parallel_safe(root, (Node *) rte->values_lists))
				return;
			break;

		case RTE_CTE:

			/*
			 * CTE tuplestores aren't shared among parallel workers, so we
			 * force all CTE scans to happen in the leader.  Also, populating
			 * the CTE would require executing a subplan that's not available
			 * in the worker, might be parallel-restricted, and must get
			 * executed only once.
			 */
			return;

		case RTE_NAMEDTUPLESTORE:

			/*
			 * tuplestore cannot be shared, at least without more
			 * infrastructure to support that.
			 */
			return;

		case RTE_RESULT:
			/* RESULT RTEs, in themselves, are no problem. */
			break;

		case RTE_GRAPH_TABLE:

			/*
			 * Shouldn't happen since these are replaced by subquery RTEs when
			 * rewriting queries.
			 */
			Assert(false);
			return;

		case RTE_GROUP:
			/* Shouldn't happen; we're only considering baserels here. */
			Assert(false);
			return;
	}

	/*
	 * If there's anything in baserestrictinfo that's parallel-restricted, we
	 * give up on parallelizing access to this relation.  We could consider
	 * instead postponing application of the restricted quals until we're
	 * above all the parallelism in the plan tree, but it's not clear that
	 * that would be a win in very many cases, and it might be tricky to make
	 * outer join clauses work correctly.  It would likely break equivalence
	 * classes, too.
	 */
	if (!is_parallel_safe(root, (Node *) rel->baserestrictinfo))
		return;

	/*
	 * Likewise, if the relation's outputs are not parallel-safe, give up.
	 * (Usually, they're just Vars, but sometimes they're not.)
	 */
	if (!is_parallel_safe(root, (Node *) rel->reltarget->exprs))
		return;

	/* We have a winner. */
	rel->consider_parallel = true;
}

/*
 * set_plain_rel_pathlist
 *	  Build access paths for a plain relation (no subquery, no inheritance)
 */
/*
 * set_plain_rel_pathlist - (中文)为普通表生成扫描路径
 *
 * 【作用】为普通表生成并注册候选扫描路径:按顺序考虑 TID 扫描、顺序扫描、
 * 并行顺序扫描、索引扫描。被 set_rel_pathlist() 对 RTE_RELATION 的普通表
 * 调用。
 *
 * 【设计思想】
 * - required_outer 取 rel->lateral_relids:连接条件不会下推到顺序扫描的
 *   quals 里,但 LATERAL 引用造成的参数化仍需保留;
 * - create_tidscan_paths() 返回 true 表示"必须使用 TID 扫描"(因为限制条件
 *   里有 CurrentOfExpr,执行器无法处理其它路径),此时直接返回,不再加别的
 *   路径;
 * - 并行顺序扫描要求 rel->consider_parallel 且无参数化;
 * - 索引扫描交给 create_index_paths()(indxpath.c)负责。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 普通表关系;
 *   rte  —— 对应 RangeTblEntry。
 * 【返回值】无(路径写入 rel->pathlist / partial_pathlist)。
 */
static void
set_plain_rel_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Relids		required_outer;

	/*
	 * We don't support pushing join clauses into the quals of a seqscan, but
	 * it could still have required parameterization due to LATERAL refs in
	 * its tlist.
	 */
	required_outer = rel->lateral_relids;

	/*
	 * Consider TID scans.
	 *
	 * If create_tidscan_paths returns true, then a TID scan path is forced.
	 * This happens when rel->baserestrictinfo contains CurrentOfExpr, because
	 * the executor can't handle any other type of path for such queries.
	 * Hence, we return without adding any other paths.
	 */
	if (create_tidscan_paths(root, rel))
		return;

	/* Consider sequential scan */
	add_path(rel, create_seqscan_path(root, rel, required_outer, 0));

	/* If appropriate, consider parallel sequential scan */
	if (rel->consider_parallel && required_outer == NULL)
		create_plain_partial_paths(root, rel);

	/* Consider index scans */
	create_index_paths(root, rel);
}

/*
 * create_plain_partial_paths
 *	  Build partial access paths for parallel scan of a plain relation
 */
/*
 * create_plain_partial_paths - (中文)为普通表生成并行顺序扫描的 partial 路径
 *
 * 【作用】为普通表创建一个基于并行顺序扫描的无序 partial 路径,加入
 * rel->partial_pathlist。由 set_plain_rel_pathlist() 在关系允许并行且无参数
 * 化时调用。之后这些 partial 路径会被 generate_gather_paths() 等套上
 * Gather 变成完整路径。
 *
 * 【设计思想】worker 数量由 compute_parallel_worker() 按表页数估算;若算出的
 * worker 数 <= 0(表太小或 GUC 限制为 0),说明用户不想要并行扫描,直接返回。
 * 本函数只生成最简单的无序 partial 顺序扫描;带排序的并行扫描由上层
 * generate_useful_gather_paths() 用 Gather Merge 处理。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 普通表关系(已确定 consider_parallel 为真)。
 * 【返回值】无。
 */
static void
create_plain_partial_paths(PlannerInfo *root, RelOptInfo *rel)
{
	int			parallel_workers;

	parallel_workers = compute_parallel_worker(rel, rel->pages, -1,
											   max_parallel_workers_per_gather);

	/* If any limit was set to zero, the user doesn't want a parallel scan. */
	if (parallel_workers <= 0)
		return;

	/* Add an unordered partial path based on a parallel sequential scan. */
	add_partial_path(rel, create_seqscan_path(root, rel, NULL, parallel_workers));
}

/*
 * set_tablesample_rel_size
 *	  Set size estimates for a sampled relation
 */
/*
 * set_tablesample_rel_size - (中文)估算采样表(TABLESAMPLE)关系的大小
 *
 * 【作用】对使用 TABLESAMPLE 子句的表设置大小估算:先检查部分索引适用性,
 * 然后调用采样方法的 SampleScanGetSampleSize 回调来估计将要读取的页数与
 * 返回的元组数,最后用 set_baserel_size_estimates() 完成行数/宽度计算。
 *
 * 【设计思想】因为目前只为采样关系考虑 SampleScan 这一种路径,所以直接把
 * 采样方法算出的 pages/tuples 覆盖写入 rel->pages/rel->tuples 是安全的
 * (若将来支持多种路径类型就需要更精细的处理)。set_baserel_size_estimates
 * 会在此基础上应用 baserestrictinfo 的选择性算出最终 rel->rows。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 采样表关系;
 *   rte  —— 对应 RangeTblEntry,其 tablesample 字段给出采样子句。
 * 【返回值】无。
 */
static void
set_tablesample_rel_size(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	TableSampleClause *tsc = rte->tablesample;
	TsmRoutine *tsm;
	BlockNumber pages;
	double		tuples;

	/*
	 * Test any partial indexes of rel for applicability.  We must do this
	 * first since partial unique indexes can affect size estimates.
	 */
	check_index_predicates(root, rel);

	/*
	 * Call the sampling method's estimation function to estimate the number
	 * of pages it will read and the number of tuples it will return.  (Note:
	 * we assume the function returns sane values.)
	 */
	tsm = GetTsmRoutine(tsc->tsmhandler);
	tsm->SampleScanGetSampleSize(root, rel, tsc->args,
								 &pages, &tuples);

	/*
	 * For the moment, because we will only consider a SampleScan path for the
	 * rel, it's okay to just overwrite the pages and tuples estimates for the
	 * whole relation.  If we ever consider multiple path types for sampled
	 * rels, we'll need more complication.
	 */
	rel->pages = pages;
	rel->tuples = tuples;

	/* Mark rel with estimated output rows, width, etc */
	set_baserel_size_estimates(root, rel);
}

/*
 * set_tablesample_rel_pathlist
 *	  Build access paths for a sampled relation
 */
/*
 * set_tablesample_rel_pathlist - (中文)为采样表生成访问路径
 *
 * 【作用】为采样表生成唯一的 SampleScan 路径并加入 rel->pathlist。由
 * set_rel_pathlist() 对带 TABLESAMPLE 的关系调用。
 *
 * 【设计思想】
 * - required_outer 取 rel->lateral_relids:采样扫描不支持下推连接条件,但
 *   LATERAL 引用(在 tlist 或采样参数中)造成的参数化要保留;
 * - 采样方法若不支持"可重复扫描"(repeatable_across_scans),同一关系被
 *   多次扫描时会得到不一致的采样结果,因此只要查询可能做连接
 *   (顶层有多个基础关系,或本函数位于子查询中无法确认外层),就用
 *   Materialize 节点包一层,保证采样结果只计算一次;
 * - 目前只为采样关系生成这一种路径。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 采样表关系;
 *   rte  —— 对应 RangeTblEntry。
 * 【返回值】无。
 */
static void
set_tablesample_rel_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Relids		required_outer;
	Path	   *path;

	/*
	 * We don't support pushing join clauses into the quals of a samplescan,
	 * but it could still have required parameterization due to LATERAL refs
	 * in its tlist or TABLESAMPLE arguments.
	 */
	required_outer = rel->lateral_relids;

	/* Consider sampled scan */
	path = create_samplescan_path(root, rel, required_outer);

	/*
	 * If the sampling method does not support repeatable scans, we must avoid
	 * plans that would scan the rel multiple times.  Ideally, we'd simply
	 * avoid putting the rel on the inside of a nestloop join; but adding such
	 * a consideration to the planner seems like a great deal of complication
	 * to support an uncommon usage of second-rate sampling methods.  Instead,
	 * if there is a risk that the query might perform an unsafe join, just
	 * wrap the SampleScan in a Materialize node.  We can check for joins by
	 * counting the membership of all_query_rels (note that this correctly
	 * counts inheritance trees as single rels).  If we're inside a subquery,
	 * we can't easily check whether a join might occur in the outer query, so
	 * just assume one is possible.
	 *
	 * GetTsmRoutine is relatively expensive compared to the other tests here,
	 * so check repeatable_across_scans last, even though that's a bit odd.
	 */
	if ((root->query_level > 1 ||
		 bms_membership(root->all_query_rels) != BMS_SINGLETON) &&
		!(GetTsmRoutine(rte->tablesample->tsmhandler)->repeatable_across_scans))
	{
		path = (Path *) create_material_path(rel, path, true);
	}

	add_path(rel, path);

	/* For the moment, at least, there are no other paths to consider */
}

/*
 * set_foreign_size
 *		Set size estimates for a foreign table RTE
 */
/*
 * set_foreign_size - (中文)估算外表关系的大小
 *
 * 【作用】为外表设置大小估算:先用 set_foreign_size_estimates()(costsize.c)
 * 做基本估算,再调用 FDW 的 GetForeignRelSize 回调让 FDW 根据远程统计信息
 * 调整估算,最后做两处保护性修正。
 *
 * 【设计思想】
 * - FDW 的估算结果可能不规范:行数(rel->rows)不允许为 0(用
 *   clamp_row_est() 夹到最小合理值),否则后续成本公式会出错;
 * - rel->tuples(表中总元组数)不能小于 rel->rows:防止 pg_class.reltuples
 *   为 -1 且 FDW 没替换它时产生自相矛盾的估算。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 外表关系;
 *   rte  —— 对应 RangeTblEntry(relkind == RELKIND_FOREIGN_TABLE)。
 * 【返回值】无。
 */
static void
set_foreign_size(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	/* Mark rel with estimated output rows, width, etc */
	set_foreign_size_estimates(root, rel);

	/* Let FDW adjust the size estimates, if it can */
	rel->fdwroutine->GetForeignRelSize(root, rel, rte->relid);

	/* ... but do not let it set the rows estimate to zero */
	rel->rows = clamp_row_est(rel->rows);

	/*
	 * Also, make sure rel->tuples is not insane relative to rel->rows.
	 * Notably, this ensures sanity if pg_class.reltuples contains -1 and the
	 * FDW doesn't do anything to replace that.
	 */
	rel->tuples = Max(rel->tuples, rel->rows);
}

/*
 * set_foreign_pathlist
 *		Build access paths for a foreign table RTE
 */
/*
 * set_foreign_pathlist - (中文)为外表生成访问路径
 *
 * 【作用】委托 FDW 的 GetForeignPaths 回调为外表生成一条或多条 ForeignPath,
 * 加入 rel->pathlist。由 set_rel_pathlist() 对外表调用。
 *
 * 【设计思想】外表的路径生成完全交给 FDW 定制:FDW 可能返回多种路径
 * (如远程扫描 vs 本地扫描、并行与否),并自行调用 add_path()/add_partial_path()
 * 注册。本函数只是薄薄的转发层。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 外表关系(rel->fdwroutine 已绑定);
 *   rte  —— 对应 RangeTblEntry。
 * 【返回值】无。
 */
static void
set_foreign_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	/* Call the FDW's GetForeignPaths function to generate path(s) */
	rel->fdwroutine->GetForeignPaths(root, rel, rte->relid);
}

/*
 * set_append_rel_size
 *	  Set size estimates for a simple "append relation"
 *
 * The passed-in rel and RTE represent the entire append relation.  The
 * relation's contents are computed by appending together the output of the
 * individual member relations.  Note that in the non-partitioned inheritance
 * case, the first member relation is actually the same table as is mentioned
 * in the parent RTE ... but it has a different RTE and RelOptInfo.  This is
 * a good thing because their outputs are not the same size.
 */
/*
 * set_append_rel_size - (中文)估算继承/分区(append)关系的总大小
 *
 * 【作用】把整个 append 关系(父关系,可能对应一张分区表或继承表)的大小
 * 估算为其所有"存活"子关系的大小之和:依次对每个子关系做约束排除、把父的
 * 连接条件与目标列表改写并复制给子关系、建立子关系的等价类条目、估算子
 * 关系大小,最后把各子关系的 tuples/rows/宽度按行数加权汇总到父关系。
 * 由 set_rel_size() 对 rte->inh 的关系调用。
 *
 * 【设计思想】
 * - 循环遍历 root->append_rel_list,只处理 parent_relid == 本关系的条目;
 *   子关系 RelOptInfo 在 add_other_rels_to_query 阶段已创建;
 * - 对每个子关系:先用 relation_excluded_by_constraints() 做约束排除,命中
 *   则 set_dummy_rel_pathlist() 并跳过;否则把父的连接条件(childrinfos,
 *   跳过会置空本关系的、来自外层外连接的连接条件,因为 nullingrels 无法套用)
 *   和目标列表通过 adjust_appendrel_attrs() 变量替换后复制给子关系;若父
 *   参与等价类连接或有用的排序键,还要 add_child_rel_equivalences() 建立子
 *   关系在等价类中的成员;
 * - tuples 累加的是各子关系"物理元组数",rows 累加的是"过滤后行数",两者
 *   分开统计是为了让基于 appendrel 的 distinct 估计等能正确应用选择性;
 *   宽度按"子关系行数"加权平均(宽度用于估算排序/哈希的整体占用);
 * - 并行标志:任一存活子关系不并行则父整体不并行(将来可能部分子关系并行,
 *   但现在不支持,所以全部或不);
 * - 大小汇总完成后 rel->pages 保持为 0,避免在 total_table_pages 里把
 *   append 树重复计数;
 * - 全部子关系都被排除时把父标记为 dummy(set_dummy_rel_pathlist),这样
 *   本阶段其它关系就能看到父为空。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— append 父关系(RELOPT_BASEREL 或继承子关系);
 *   rti  —— rel 的 rtable 索引;
 *   rte  —— 对应 RangeTblEntry(rte->inh 为真)。
 * 【返回值】无。
 */
static void
set_append_rel_size(PlannerInfo *root, RelOptInfo *rel,
					Index rti, RangeTblEntry *rte)
{
	int			parentRTindex = rti;
	bool		has_live_children;
	double		parent_tuples;
	double		parent_rows;
	double		parent_size;
	double	   *parent_attrsizes;
	int			nattrs;
	ListCell   *l;

	/* Guard against stack overflow due to overly deep inheritance tree. */
	check_stack_depth();

	Assert(IS_SIMPLE_REL(rel));

	/*
	 * If this is a partitioned baserel, set the consider_partitionwise_join
	 * flag; currently, we only consider partitionwise joins with the baserel
	 * if its targetlist doesn't contain a whole-row Var.
	 */
	if (enable_partitionwise_join &&
		rel->reloptkind == RELOPT_BASEREL &&
		rte->relkind == RELKIND_PARTITIONED_TABLE &&
		bms_is_empty(rel->attr_needed[InvalidAttrNumber - rel->min_attr]))
		rel->consider_partitionwise_join = true;

	/*
	 * Initialize to compute size estimates for whole append relation.
	 *
	 * We handle tuples estimates by setting "tuples" to the total number of
	 * tuples accumulated from each live child, rather than using "rows".
	 * Although an appendrel itself doesn't directly enforce any quals, its
	 * child relations may.  Therefore, setting "tuples" equal to "rows" for
	 * an appendrel isn't always appropriate, and can lead to inaccurate cost
	 * estimates.  For example, when estimating the number of distinct values
	 * from an appendrel, we would be unable to adjust the estimate based on
	 * the restriction selectivity (see estimate_num_groups).
	 *
	 * We handle width estimates by weighting the widths of different child
	 * rels proportionally to their number of rows.  This is sensible because
	 * the use of width estimates is mainly to compute the total relation
	 * "footprint" if we have to sort or hash it.  To do this, we sum the
	 * total equivalent size (in "double" arithmetic) and then divide by the
	 * total rowcount estimate.  This is done separately for the total rel
	 * width and each attribute.
	 *
	 * Note: if you consider changing this logic, beware that child rels could
	 * have zero rows and/or width, if they were excluded by constraints.
	 */
	has_live_children = false;
	parent_tuples = 0;
	parent_rows = 0;
	parent_size = 0;
	nattrs = rel->max_attr - rel->min_attr + 1;
	parent_attrsizes = (double *) palloc0(nattrs * sizeof(double));

	foreach(l, root->append_rel_list)
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) lfirst(l);
		int			childRTindex;
		RangeTblEntry *childRTE;
		RelOptInfo *childrel;
		List	   *childrinfos;
		ListCell   *parentvars;
		ListCell   *childvars;
		ListCell   *lc;

		/* append_rel_list contains all append rels; ignore others */
		if (appinfo->parent_relid != parentRTindex)
			continue;

		childRTindex = appinfo->child_relid;
		childRTE = root->simple_rte_array[childRTindex];

		/*
		 * The child rel's RelOptInfo was already created during
		 * add_other_rels_to_query.
		 */
		childrel = find_base_rel(root, childRTindex);
		Assert(childrel->reloptkind == RELOPT_OTHER_MEMBER_REL);

		/* We may have already proven the child to be dummy. */
		if (IS_DUMMY_REL(childrel))
			continue;

		/*
		 * We have to copy the parent's targetlist and quals to the child,
		 * with appropriate substitution of variables.  However, the
		 * baserestrictinfo quals were already copied/substituted when the
		 * child RelOptInfo was built.  So we don't need any additional setup
		 * before applying constraint exclusion.
		 */
		if (relation_excluded_by_constraints(root, childrel, childRTE))
		{
			/*
			 * This child need not be scanned, so we can omit it from the
			 * appendrel.
			 */
			set_dummy_rel_pathlist(childrel);
			continue;
		}

		/*
		 * Constraint exclusion failed, so copy the parent's join quals and
		 * targetlist to the child, with appropriate variable substitutions.
		 *
		 * We skip join quals that came from above outer joins that can null
		 * this rel, since they would be of no value while generating paths
		 * for the child.  This saves some effort while processing the child
		 * rel, and it also avoids an implementation restriction in
		 * adjust_appendrel_attrs (it can't apply nullingrels to a non-Var).
		 */
		childrinfos = NIL;
		foreach(lc, rel->joininfo)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			if (!bms_overlap(rinfo->clause_relids, rel->nulling_relids))
				childrinfos = lappend(childrinfos,
									  adjust_appendrel_attrs(root,
															 (Node *) rinfo,
															 1, &appinfo));
		}
		childrel->joininfo = childrinfos;

		/*
		 * Now for the child's targetlist.
		 *
		 * NB: the resulting childrel->reltarget->exprs may contain arbitrary
		 * expressions, which otherwise would not occur in a rel's targetlist.
		 * Code that might be looking at an appendrel child must cope with
		 * such.  (Normally, a rel's targetlist would only include Vars and
		 * PlaceHolderVars.)  XXX we do not bother to update the cost or width
		 * fields of childrel->reltarget; not clear if that would be useful.
		 */
		childrel->reltarget->exprs = (List *)
			adjust_appendrel_attrs(root,
								   (Node *) rel->reltarget->exprs,
								   1, &appinfo);

		/*
		 * We have to make child entries in the EquivalenceClass data
		 * structures as well.  This is needed either if the parent
		 * participates in some eclass joins (because we will want to consider
		 * inner-indexscan joins on the individual children) or if the parent
		 * has useful pathkeys (because we should try to build MergeAppend
		 * paths that produce those sort orderings).
		 */
		if (rel->has_eclass_joins || has_useful_pathkeys(root, rel))
			add_child_rel_equivalences(root, appinfo, rel, childrel);
		childrel->has_eclass_joins = rel->has_eclass_joins;

		/*
		 * Note: we could compute appropriate attr_needed data for the child's
		 * variables, by transforming the parent's attr_needed through the
		 * translated_vars mapping.  However, currently there's no need
		 * because attr_needed is only examined for base relations not
		 * otherrels.  So we just leave the child's attr_needed empty.
		 */

		/*
		 * If we consider partitionwise joins with the parent rel, do the same
		 * for partitioned child rels.
		 *
		 * Note: here we abuse the consider_partitionwise_join flag by setting
		 * it for child rels that are not themselves partitioned.  We do so to
		 * tell try_partitionwise_join() that the child rel is sufficiently
		 * valid to be used as a per-partition input, even if it later gets
		 * proven to be dummy.  (It's not usable until we've set up the
		 * reltarget and EC entries, which we just did.)
		 */
		if (rel->consider_partitionwise_join)
			childrel->consider_partitionwise_join = true;

		/*
		 * If parallelism is allowable for this query in general, see whether
		 * it's allowable for this childrel in particular.  But if we've
		 * already decided the appendrel is not parallel-safe as a whole,
		 * there's no point in considering parallelism for this child.  For
		 * consistency, do this before calling set_rel_size() for the child.
		 */
		if (root->glob->parallelModeOK && rel->consider_parallel)
			set_rel_consider_parallel(root, childrel, childRTE);

		/*
		 * Compute the child's size.
		 */
		set_rel_size(root, childrel, childRTindex, childRTE);

		/*
		 * It is possible that constraint exclusion detected a contradiction
		 * within a child subquery, even though we didn't prove one above. If
		 * so, we can skip this child.
		 */
		if (IS_DUMMY_REL(childrel))
			continue;

		/* We have at least one live child. */
		has_live_children = true;

		/*
		 * If any live child is not parallel-safe, treat the whole appendrel
		 * as not parallel-safe.  In future we might be able to generate plans
		 * in which some children are farmed out to workers while others are
		 * not; but we don't have that today, so it's a waste to consider
		 * partial paths anywhere in the appendrel unless it's all safe.
		 * (Child rels visited before this one will be unmarked in
		 * set_append_rel_pathlist().)
		 */
		if (!childrel->consider_parallel)
			rel->consider_parallel = false;

		/*
		 * Accumulate size information from each live child.
		 */
		Assert(childrel->rows > 0);

		parent_tuples += childrel->tuples;
		parent_rows += childrel->rows;
		parent_size += childrel->reltarget->width * childrel->rows;

		/*
		 * Accumulate per-column estimates too.  We need not do anything for
		 * PlaceHolderVars in the parent list.  If child expression isn't a
		 * Var, or we didn't record a width estimate for it, we have to fall
		 * back on a datatype-based estimate.
		 *
		 * By construction, child's targetlist is 1-to-1 with parent's.
		 */
		forboth(parentvars, rel->reltarget->exprs,
				childvars, childrel->reltarget->exprs)
		{
			Var		   *parentvar = (Var *) lfirst(parentvars);
			Node	   *childvar = (Node *) lfirst(childvars);

			if (IsA(parentvar, Var) && parentvar->varno == parentRTindex)
			{
				int			pndx = parentvar->varattno - rel->min_attr;
				int32		child_width = 0;

				if (IsA(childvar, Var) &&
					((Var *) childvar)->varno == childrel->relid)
				{
					int			cndx = ((Var *) childvar)->varattno - childrel->min_attr;

					child_width = childrel->attr_widths[cndx];
				}
				if (child_width <= 0)
					child_width = get_typavgwidth(exprType(childvar),
												  exprTypmod(childvar));
				Assert(child_width > 0);
				parent_attrsizes[pndx] += child_width * childrel->rows;
			}
		}
	}

	if (has_live_children)
	{
		/*
		 * Save the finished size estimates.
		 */
		int			i;

		Assert(parent_rows > 0);
		rel->tuples = parent_tuples;
		rel->rows = parent_rows;
		rel->reltarget->width = rint(parent_size / parent_rows);
		for (i = 0; i < nattrs; i++)
			rel->attr_widths[i] = rint(parent_attrsizes[i] / parent_rows);

		/*
		 * Note that we leave rel->pages as zero; this is important to avoid
		 * double-counting the appendrel tree in total_table_pages.
		 */
	}
	else
	{
		/*
		 * All children were excluded by constraints, so mark the whole
		 * appendrel dummy.  We must do this in this phase so that the rel's
		 * dummy-ness is visible when we generate paths for other rels.
		 */
		set_dummy_rel_pathlist(rel);
	}

	pfree(parent_attrsizes);
}

/*
 * set_append_rel_pathlist
 *	  Build access paths for an "append relation"
 */
/*
 * set_append_rel_pathlist - (中文)为继承/分区(append)关系生成访问路径
 *
 * 【作用】为 append 父关系生成路径:先递归为每个存活子关系生成各自的扫描
 * 路径,然后把所有非 dummy 子关系收集进 live_childrels 列表,最后交给
 * add_paths_to_append_rel() 合成各种 Append/MergeAppend/并行 Append 路径。
 * 由 set_rel_pathlist() 对 rte->inh 的关系调用。
 *
 * 【设计思想】
 * - 循环 append_rel_list 定位子关系后直接递归调用 set_rel_pathlist() 为子
 *   生成路径;若父因 set_append_rel_size 已判定不并行,要把该标志向下传播到
 *   子关系,避免为子生成无用 partial 路径;
 * - dummy 子关系被忽略,不进入 live_childrels;
 * - 具体的 Append 路径形态(无序 Append、并行 Append、有序 MergeAppend、
 *   参数化 Append 等)都在 add_paths_to_append_rel() / generate_orderedappend_paths()
 *   中根据子关系暴露的 pathkeys 与参数化集合决定。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— append 父关系;
 *   rti  —— rel 的 rtable 索引;
 *   rte  —— 对应 RangeTblEntry。
 * 【返回值】无。
 */
static void
set_append_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
						Index rti, RangeTblEntry *rte)
{
	int			parentRTindex = rti;
	List	   *live_childrels = NIL;
	ListCell   *l;

	/*
	 * Generate access paths for each member relation, and remember the
	 * non-dummy children.
	 */
	foreach(l, root->append_rel_list)
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) lfirst(l);
		int			childRTindex;
		RangeTblEntry *childRTE;
		RelOptInfo *childrel;

		/* append_rel_list contains all append rels; ignore others */
		if (appinfo->parent_relid != parentRTindex)
			continue;

		/* Re-locate the child RTE and RelOptInfo */
		childRTindex = appinfo->child_relid;
		childRTE = root->simple_rte_array[childRTindex];
		childrel = root->simple_rel_array[childRTindex];

		/*
		 * If set_append_rel_size() decided the parent appendrel was
		 * parallel-unsafe at some point after visiting this child rel, we
		 * need to propagate the unsafety marking down to the child, so that
		 * we don't generate useless partial paths for it.
		 */
		if (!rel->consider_parallel)
			childrel->consider_parallel = false;

		/*
		 * Compute the child's access paths.
		 */
		set_rel_pathlist(root, childrel, childRTindex, childRTE);

		/*
		 * If child is dummy, ignore it.
		 */
		if (IS_DUMMY_REL(childrel))
			continue;

		/*
		 * Child is live, so add it to the live_childrels list for use below.
		 */
		live_childrels = lappend(live_childrels, childrel);
	}

	/* Add paths to the append relation. */
	add_paths_to_append_rel(root, rel, live_childrels);
}

/*
 * set_grouped_rel_pathlist
 *	  If a grouped relation for the given 'rel' exists, build partial
 *	  aggregation paths for it.
 */
/*
 * set_grouped_rel_pathlist - (中文)为基础关系的 grouped rel 生成部分聚合路径
 *
 * 【作用】若给定关系存在对应的 grouped rel(急切聚合信息),则调用
 * generate_grouped_paths() 在其上生成部分聚合路径,并调用 set_cheapest()
 * 选出最便宜路径。由 set_rel_pathlist() 在每个基础关系的路径生成完毕之后
 * 调用。
 *
 * 【设计思想】急切聚合要求查询确实含聚合与分组表达式,否则直接返回。
 * set_cheapest() 必须先于本函数调用(见 set_rel_pathlist 顺序),因为
 * generate_grouped_paths() 需要用到关系的最便宜路径。连接关系(joinrel)的
 * grouped rel 不在此处理,而在 standard_join_search() 里逐层处理。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 基础关系,rel->grouped_rel 可能是其 grouped rel。
 * 【返回值】无。
 */
static void
set_grouped_rel_pathlist(PlannerInfo *root, RelOptInfo *rel)
{
	RelOptInfo *grouped_rel;

	/*
	 * If there are no aggregate expressions or grouping expressions, eager
	 * aggregation is not possible.
	 */
	if (root->agg_clause_list == NIL ||
		root->group_expr_list == NIL)
		return;

	/* Add paths to the grouped base relation if one exists. */
	grouped_rel = rel->grouped_rel;
	if (grouped_rel)
	{
		Assert(IS_GROUPED_REL(grouped_rel));

		generate_grouped_paths(root, grouped_rel, rel);
		set_cheapest(grouped_rel);
	}
}


/*
 * add_paths_to_append_rel
 *		Generate paths for the given append relation given the set of non-dummy
 *		child rels.
 *
 * The function collects all parameterizations and orderings supported by the
 * non-dummy children. For every such parameterization or ordering, it creates
 * an append path collecting one path from each non-dummy child with given
 * parameterization or ordering. Similarly it collects partial paths from
 * non-dummy children to create partial append paths.
 */
/*
 * add_paths_to_append_rel - (中文)为 append 关系合成各种 Append 路径
 *
 * 【作用】给定 append 父关系与非 dummy 子关系列表,收集各子关系支持的
 * 参数化集合与排序键,据此生成:无序非参数化 Append 路径、快速启动
 * (cheapest_startup) Append 路径、纯 partial 路径的并行 Append、混合
 * partial 与非 partial 子路径的并行 Append、按每种排序键的 MergeAppend/
 * 有序 Append(见 generate_orderedappend_paths())、以及每种参数化集合的
 * 参数化 Append 路径。本函数同时是 partitionwise join 中
 * generate_partitionwise_join_paths() 复用"把子连接合成父连接路径"的入口。
 *
 * 【设计思想】
 * - 对每个 child:取 unparameterized cheapest-total 路径填进
 *   unparameterized 输入;若父关系考虑快速启动,再取 cheapest-startup(或
 *   按 tuple_fraction 取 cheapest-fractional)路径填进 startup 输入;取
 *   partial_pathlist 的第一条(最便宜的)partial 路径填进 partial_only 输入;
 *   并行 Append 的输入在"partial 路径更便宜"时用 partial 路径,否则用
 *   parallel-safe 的非 partial 路径(两者都缺则放弃并行 Append);
 * - 并行 Append 的 worker 数取各 partial 子路径的最大值,且至少要
 *   log2(#children)+1 个(猜测公式,目的是分区表与同数据量的整表在并行度
 *   上不至于差太多),并受 max_parallel_workers_per_gather 限制;
 * - 参数化 Append 要求每个子路径参数化集合完全一致(Append 自身不检查
 *   quals),不足的通过 get_cheapest_parameterized_child_path() 提升;因此
 *   同一个参数化集合在所有子关系都凑齐时才生成路径;
 * - 单子关系时 append 路径可继承子路径的排序,因此还会为带 pathkeys 的
 *   有序 partial 路径(跳过已用过的第一条)各生成一个并行 Append。
 *
 * 【参数】
 *   root           —— PlannerInfo;
 *   rel            —— append 父关系(也可能是分区连接关系的父);
 *   live_childrels —— 所有非 dummy 子关系的列表。
 * 【返回值】无(路径通过 add_path/add_partial_path 注册到 rel)。
 */
void
add_paths_to_append_rel(PlannerInfo *root, RelOptInfo *rel,
						List *live_childrels)
{
	AppendPathInput unparameterized = {0};
	AppendPathInput startup = {0};
	AppendPathInput partial_only = {0};
	AppendPathInput parallel_append = {0};
	bool		unparameterized_valid = true;
	bool		startup_valid = true;
	bool		partial_only_valid = true;
	bool		parallel_append_valid = true;
	List	   *all_child_pathkeys = NIL;
	List	   *all_child_outers = NIL;
	ListCell   *l;
	double		partial_rows = -1;

	/* If appropriate, consider parallel append */
	parallel_append_valid = enable_parallel_append && rel->consider_parallel;

	/*
	 * For every non-dummy child, remember the cheapest path.  Also, identify
	 * all pathkeys (orderings) and parameterizations (required_outer sets)
	 * available for the non-dummy member relations.
	 */
	foreach(l, live_childrels)
	{
		RelOptInfo *childrel = lfirst(l);
		ListCell   *lcp;
		Path	   *cheapest_partial_path = NULL;

		/*
		 * If child has an unparameterized cheapest-total path, add that to
		 * the unparameterized Append path we are constructing for the parent.
		 * If not, there's no workable unparameterized path.
		 *
		 * With partitionwise aggregates, the child rel's pathlist may be
		 * empty, so don't assume that a path exists here.
		 */
		if (childrel->pathlist != NIL &&
			childrel->cheapest_total_path->param_info == NULL)
			accumulate_append_subpath(childrel->cheapest_total_path,
									  &unparameterized.subpaths, NULL, &unparameterized.child_append_relid_sets);
		else
			unparameterized_valid = false;

		/*
		 * When the planner is considering cheap startup plans, we'll also
		 * collect all the cheapest_startup_paths (if set) and build an
		 * AppendPath containing those as subpaths.
		 */
		if (rel->consider_startup && childrel->cheapest_startup_path != NULL)
		{
			Path	   *cheapest_path;

			/*
			 * With an indication of how many tuples the query should provide,
			 * the optimizer tries to choose the path optimal for that
			 * specific number of tuples.
			 */
			if (root->tuple_fraction > 0.0)
				cheapest_path =
					get_cheapest_fractional_path(childrel,
												 root->tuple_fraction);
			else
				cheapest_path = childrel->cheapest_startup_path;

			/* cheapest_startup_path must not be a parameterized path. */
			Assert(cheapest_path->param_info == NULL);
			accumulate_append_subpath(cheapest_path,
									  &startup.subpaths,
									  NULL,
									  &startup.child_append_relid_sets);
		}
		else
			startup_valid = false;


		/* Same idea, but for a partial plan. */
		if (childrel->partial_pathlist != NIL)
		{
			cheapest_partial_path = linitial(childrel->partial_pathlist);
			accumulate_append_subpath(cheapest_partial_path,
									  &partial_only.partial_subpaths, NULL,
									  &partial_only.child_append_relid_sets);
		}
		else
			partial_only_valid = false;

		/*
		 * Same idea, but for a parallel append mixing partial and non-partial
		 * paths.
		 */
		if (parallel_append_valid)
		{
			Path	   *nppath = NULL;

			nppath =
				get_cheapest_parallel_safe_total_inner(childrel->pathlist);

			if (cheapest_partial_path == NULL && nppath == NULL)
			{
				/* Neither a partial nor a parallel-safe path?  Forget it. */
				parallel_append_valid = false;
			}
			else if (nppath == NULL ||
					 (cheapest_partial_path != NULL &&
					  cheapest_partial_path->total_cost < nppath->total_cost))
			{
				/* Partial path is cheaper or the only option. */
				Assert(cheapest_partial_path != NULL);
				accumulate_append_subpath(cheapest_partial_path,
										  &parallel_append.partial_subpaths,
										  &parallel_append.subpaths,
										  &parallel_append.child_append_relid_sets);
			}
			else
			{
				/*
				 * Either we've got only a non-partial path, or we think that
				 * a single backend can execute the best non-partial path
				 * faster than all the parallel backends working together can
				 * execute the best partial path.
				 *
				 * It might make sense to be more aggressive here.  Even if
				 * the best non-partial path is more expensive than the best
				 * partial path, it could still be better to choose the
				 * non-partial path if there are several such paths that can
				 * be given to different workers.  For now, we don't try to
				 * figure that out.
				 */
				accumulate_append_subpath(nppath,
										  &parallel_append.subpaths,
										  NULL,
										  &parallel_append.child_append_relid_sets);
			}
		}

		/*
		 * Collect lists of all the available path orderings and
		 * parameterizations for all the children.  We use these as a
		 * heuristic to indicate which sort orderings and parameterizations we
		 * should build Append and MergeAppend paths for.
		 */
		foreach(lcp, childrel->pathlist)
		{
			Path	   *childpath = (Path *) lfirst(lcp);
			List	   *childkeys = childpath->pathkeys;
			Relids		childouter = PATH_REQ_OUTER(childpath);

			/* Unsorted paths don't contribute to pathkey list */
			if (childkeys != NIL)
			{
				ListCell   *lpk;
				bool		found = false;

				/* Have we already seen this ordering? */
				foreach(lpk, all_child_pathkeys)
				{
					List	   *existing_pathkeys = (List *) lfirst(lpk);

					if (compare_pathkeys(existing_pathkeys,
										 childkeys) == PATHKEYS_EQUAL)
					{
						found = true;
						break;
					}
				}
				if (!found)
				{
					/* No, so add it to all_child_pathkeys */
					all_child_pathkeys = lappend(all_child_pathkeys,
												 childkeys);
				}
			}

			/* Unparameterized paths don't contribute to param-set list */
			if (childouter)
			{
				ListCell   *lco;
				bool		found = false;

				/* Have we already seen this param set? */
				foreach(lco, all_child_outers)
				{
					Relids		existing_outers = (Relids) lfirst(lco);

					if (bms_equal(existing_outers, childouter))
					{
						found = true;
						break;
					}
				}
				if (!found)
				{
					/* No, so add it to all_child_outers */
					all_child_outers = lappend(all_child_outers,
											   childouter);
				}
			}
		}
	}

	/*
	 * If we found unparameterized paths for all children, build an unordered,
	 * unparameterized Append path for the rel.  (Note: this is correct even
	 * if we have zero or one live subpath due to constraint exclusion.)
	 */
	if (unparameterized_valid)
		add_path(rel, (Path *) create_append_path(root, rel, unparameterized,
												  NIL, NULL, 0, false,
												  -1));

	/* build an AppendPath for the cheap startup paths, if valid */
	if (startup_valid)
		add_path(rel, (Path *) create_append_path(root, rel, startup,
												  NIL, NULL, 0, false, -1));

	/*
	 * Consider an append of unordered, unparameterized partial paths.  Make
	 * it parallel-aware if possible.
	 */
	if (partial_only_valid && partial_only.partial_subpaths != NIL)
	{
		AppendPath *appendpath;
		ListCell   *lc;
		int			parallel_workers = 0;

		/* Find the highest number of workers requested for any subpath. */
		foreach(lc, partial_only.partial_subpaths)
		{
			Path	   *path = lfirst(lc);

			parallel_workers = Max(parallel_workers, path->parallel_workers);
		}
		Assert(parallel_workers > 0);

		/*
		 * If the use of parallel append is permitted, always request at least
		 * log2(# of children) workers.  We assume it can be useful to have
		 * extra workers in this case because they will be spread out across
		 * the children.  The precise formula is just a guess, but we don't
		 * want to end up with a radically different answer for a table with N
		 * partitions vs. an unpartitioned table with the same data, so the
		 * use of some kind of log-scaling here seems to make some sense.
		 */
		if (enable_parallel_append)
		{
			parallel_workers = Max(parallel_workers,
								   pg_leftmost_one_pos32(list_length(live_childrels)) + 1);
			parallel_workers = Min(parallel_workers,
								   max_parallel_workers_per_gather);
		}
		Assert(parallel_workers > 0);

		/* Generate a partial append path. */
		appendpath = create_append_path(root, rel, partial_only,
										NIL, NULL, parallel_workers,
										enable_parallel_append,
										-1);

		/*
		 * Make sure any subsequent partial paths use the same row count
		 * estimate.
		 */
		partial_rows = appendpath->path.rows;

		/* Add the path. */
		add_partial_path(rel, (Path *) appendpath);
	}

	/*
	 * Consider a parallel-aware append using a mix of partial and non-partial
	 * paths.  (This only makes sense if there's at least one child which has
	 * a non-partial path that is substantially cheaper than any partial path;
	 * otherwise, we should use the append path added in the previous step.)
	 */
	if (parallel_append_valid && parallel_append.subpaths != NIL)
	{
		AppendPath *appendpath;
		ListCell   *lc;
		int			parallel_workers = 0;

		/*
		 * Find the highest number of workers requested for any partial
		 * subpath.
		 */
		foreach(lc, parallel_append.partial_subpaths)
		{
			Path	   *path = lfirst(lc);

			parallel_workers = Max(parallel_workers, path->parallel_workers);
		}

		/*
		 * Same formula here as above.  It's even more important in this
		 * instance because the non-partial paths won't contribute anything to
		 * the planned number of parallel workers.
		 */
		parallel_workers = Max(parallel_workers,
							   pg_leftmost_one_pos32(list_length(live_childrels)) + 1);
		parallel_workers = Min(parallel_workers,
							   max_parallel_workers_per_gather);
		Assert(parallel_workers > 0);

		appendpath = create_append_path(root, rel, parallel_append,
										NIL, NULL, parallel_workers, true,
										partial_rows);
		add_partial_path(rel, (Path *) appendpath);
	}

	/*
	 * Also build unparameterized ordered append paths based on the collected
	 * list of child pathkeys.
	 */
	if (unparameterized_valid)
		generate_orderedappend_paths(root, rel, live_childrels,
									 all_child_pathkeys);

	/*
	 * Build Append paths for each parameterization seen among the child rels.
	 * (This may look pretty expensive, but in most cases of practical
	 * interest, the child rels will expose mostly the same parameterizations,
	 * so that not that many cases actually get considered here.)
	 *
	 * The Append node itself cannot enforce quals, so all qual checking must
	 * be done in the child paths.  This means that to have a parameterized
	 * Append path, we must have the exact same parameterization for each
	 * child path; otherwise some children might be failing to check the
	 * moved-down quals.  To make them match up, we can try to increase the
	 * parameterization of lesser-parameterized paths.
	 */
	foreach(l, all_child_outers)
	{
		Relids		required_outer = (Relids) lfirst(l);
		ListCell   *lcr;
		AppendPathInput parameterized = {0};
		bool		parameterized_valid = true;

		/* Select the child paths for an Append with this parameterization */
		foreach(lcr, live_childrels)
		{
			RelOptInfo *childrel = (RelOptInfo *) lfirst(lcr);
			Path	   *subpath;

			if (childrel->pathlist == NIL)
			{
				/* failed to make a suitable path for this child */
				parameterized_valid = false;
				break;
			}

			subpath = get_cheapest_parameterized_child_path(root,
															childrel,
															required_outer);
			if (subpath == NULL)
			{
				/* failed to make a suitable path for this child */
				parameterized_valid = false;
				break;
			}
			accumulate_append_subpath(subpath, &parameterized.subpaths, NULL,
									  &parameterized.child_append_relid_sets);
		}

		if (parameterized_valid)
			add_path(rel, (Path *)
					 create_append_path(root, rel, parameterized,
										NIL, required_outer, 0, false,
										-1));
	}

	/*
	 * When there is only a single child relation, the Append path can inherit
	 * any ordering available for the child rel's path, so that it's useful to
	 * consider ordered partial paths.  Above we only considered the cheapest
	 * partial path for each child, but let's also make paths using any
	 * partial paths that have pathkeys.
	 */
	if (list_length(live_childrels) == 1)
	{
		RelOptInfo *childrel = (RelOptInfo *) linitial(live_childrels);

		/* skip the cheapest partial path, since we already used that above */
		for_each_from(l, childrel->partial_pathlist, 1)
		{
			Path	   *path = (Path *) lfirst(l);
			AppendPath *appendpath;
			AppendPathInput append = {0};

			/* skip paths with no pathkeys. */
			if (path->pathkeys == NIL)
				continue;

			append.partial_subpaths = list_make1(path);
			appendpath = create_append_path(root, rel, append, NIL, NULL,
											path->parallel_workers, true,
											partial_rows);
			add_partial_path(rel, (Path *) appendpath);
		}
	}
}

/*
 * generate_orderedappend_paths
 *		Generate ordered append paths for an append relation
 *
 * Usually we generate MergeAppend paths here, but there are some special
 * cases where we can generate simple Append paths, because the subpaths
 * can provide tuples in the required order already.
 *
 * We generate a path for each ordering (pathkey list) appearing in
 * all_child_pathkeys.
 *
 * We consider the cheapest-startup and cheapest-total cases, and also the
 * cheapest-fractional case when not all tuples need to be retrieved.  For each
 * interesting ordering, we collect all the cheapest startup subpaths, all the
 * cheapest total paths, and, if applicable, all the cheapest fractional paths,
 * and build a suitable path for each case.
 *
 * We don't currently generate any parameterized ordered paths here.  While
 * it would not take much more code here to do so, it's very unclear that it
 * is worth the planning cycles to investigate such paths: there's little
 * use for an ordered path on the inside of a nestloop.  In fact, it's likely
 * that the current coding of add_path would reject such paths out of hand,
 * because add_path gives no credit for sort ordering of parameterized paths,
 * and a parameterized MergeAppend is going to be more expensive than the
 * corresponding parameterized Append path.  If we ever try harder to support
 * parameterized mergejoin plans, it might be worth adding support for
 * parameterized paths here to feed such joins.  (See notes in
 * optimizer/README for why that might not ever happen, though.)
 */
/*
 * generate_orderedappend_paths - (中文)为 append 关系生成有序路径(MergeAppend/有序 Append)
 *
 * 【作用】对 all_child_pathkeys 里收集到的每种排序键,分别以 cheapest-startup、
 * cheapest-total、cheapest-fractional(仅当 tuple_fraction > 0)三种口径收集
 * 每个子关系的子路径,合成 MergeAppend 路径(或当分区键天然有序时合成直接
 * 有序的 Append 路径),加入父关系的 pathlist。
 *
 * 【设计思想】
 * - RANGE 分区表存在"分区排列顺序与排序键一致"的可能:先调用
 *   build_partition_pathkeys() 构造正反两个方向的分区排序键,若查询的排序键
 *   完全包含分区键(或分区键完整且包含于查询键),则按分区顺序直接 Append
 *   即可得到有序结果,无需 MergeAppend 的归并排序。反方向时通过反向遍历
 *   子关系实现;
 * - 对每个子关系,用 get_cheapest_path_for_pathkeys() 找恰好满足该排序键的
 *   路径;找不到就退化为 cheapest-total 路径并靠上层再排序(创建 MergeAppend
 *   时每个子路径要单独 Sort,或让父级后续处理);
 * - startup 与 total 若指向同一路径则不重复生成两条几乎相同的 MergeAppend
 *   (用 startup_neq_total / fraction_neq_total 标记);
 * - 这里不生成参数化有序路径:有序路径主要用于最外层或 merge join 的外侧,
 *   放在 nestloop 内测价值不大,而且 add_path 对参数化路径的排序也不给加分。
 *
 * 【参数】
 *   root               —— PlannerInfo;
 *   rel                —— append 父关系;
 *   live_childrels     —— 非 dummy 子关系列表;
 *   all_child_pathkeys —— add_paths_to_append_rel 收集到的全部候选排序键列表
 *                         (每个元素是一个 pathkey 列表)。
 * 【返回值】无。
 */
static void
generate_orderedappend_paths(PlannerInfo *root, RelOptInfo *rel,
							 List *live_childrels,
							 List *all_child_pathkeys)
{
	ListCell   *lcp;
	List	   *partition_pathkeys = NIL;
	List	   *partition_pathkeys_desc = NIL;
	bool		partition_pathkeys_partial = true;
	bool		partition_pathkeys_desc_partial = true;

	/*
	 * Some partitioned table setups may allow us to use an Append node
	 * instead of a MergeAppend.  This is possible in cases such as RANGE
	 * partitioned tables where it's guaranteed that an earlier partition must
	 * contain rows which come earlier in the sort order.  To detect whether
	 * this is relevant, build pathkey descriptions of the partition ordering,
	 * for both forward and reverse scans.
	 */
	if (rel->part_scheme != NULL && IS_SIMPLE_REL(rel) &&
		partitions_are_ordered(rel->boundinfo, rel->live_parts))
	{
		partition_pathkeys = build_partition_pathkeys(root, rel,
													  ForwardScanDirection,
													  &partition_pathkeys_partial);

		partition_pathkeys_desc = build_partition_pathkeys(root, rel,
														   BackwardScanDirection,
														   &partition_pathkeys_desc_partial);

		/*
		 * You might think we should truncate_useless_pathkeys here, but
		 * allowing partition keys which are a subset of the query's pathkeys
		 * can often be useful.  For example, consider a table partitioned by
		 * RANGE (a, b), and a query with ORDER BY a, b, c.  If we have child
		 * paths that can produce the a, b, c ordering (perhaps via indexes on
		 * (a, b, c)) then it works to consider the appendrel output as
		 * ordered by a, b, c.
		 */
	}

	/* Now consider each interesting sort ordering */
	foreach(lcp, all_child_pathkeys)
	{
		List	   *pathkeys = (List *) lfirst(lcp);
		AppendPathInput startup = {0};
		AppendPathInput total = {0};
		AppendPathInput fractional = {0};
		bool		startup_neq_total = false;
		bool		fraction_neq_total = false;
		bool		match_partition_order;
		bool		match_partition_order_desc;
		int			end_index;
		int			first_index;
		int			direction;

		/*
		 * Determine if this sort ordering matches any partition pathkeys we
		 * have, for both ascending and descending partition order.  If the
		 * partition pathkeys happen to be contained in pathkeys then it still
		 * works, as described above, providing that the partition pathkeys
		 * are complete and not just a prefix of the partition keys.  (In such
		 * cases we'll be relying on the child paths to have sorted the
		 * lower-order columns of the required pathkeys.)
		 */
		match_partition_order =
			pathkeys_contained_in(pathkeys, partition_pathkeys) ||
			(!partition_pathkeys_partial &&
			 pathkeys_contained_in(partition_pathkeys, pathkeys));

		match_partition_order_desc = !match_partition_order &&
			(pathkeys_contained_in(pathkeys, partition_pathkeys_desc) ||
			 (!partition_pathkeys_desc_partial &&
			  pathkeys_contained_in(partition_pathkeys_desc, pathkeys)));

		/*
		 * When the required pathkeys match the reverse of the partition
		 * order, we must build the list of paths in reverse starting with the
		 * last matching partition first.  We can get away without making any
		 * special cases for this in the loop below by just looping backward
		 * over the child relations in this case.
		 */
		if (match_partition_order_desc)
		{
			/* loop backward */
			first_index = list_length(live_childrels) - 1;
			end_index = -1;
			direction = -1;

			/*
			 * Set this to true to save us having to check for
			 * match_partition_order_desc in the loop below.
			 */
			match_partition_order = true;
		}
		else
		{
			/* for all other case, loop forward */
			first_index = 0;
			end_index = list_length(live_childrels);
			direction = 1;
		}

		/* Select the child paths for this ordering... */
		for (int i = first_index; i != end_index; i += direction)
		{
			RelOptInfo *childrel = list_nth_node(RelOptInfo, live_childrels, i);
			Path	   *cheapest_startup,
					   *cheapest_total,
					   *cheapest_fractional = NULL;

			/* Locate the right paths, if they are available. */
			cheapest_startup =
				get_cheapest_path_for_pathkeys(childrel->pathlist,
											   pathkeys,
											   NULL,
											   STARTUP_COST,
											   false);
			cheapest_total =
				get_cheapest_path_for_pathkeys(childrel->pathlist,
											   pathkeys,
											   NULL,
											   TOTAL_COST,
											   false);

			/*
			 * If we can't find any paths with the right order just use the
			 * cheapest-total path; we'll have to sort it later.
			 */
			if (cheapest_startup == NULL || cheapest_total == NULL)
			{
				cheapest_startup = cheapest_total =
					childrel->cheapest_total_path;
				/* Assert we do have an unparameterized path for this child */
				Assert(cheapest_total->param_info == NULL);
			}

			/*
			 * When building a fractional path, determine a cheapest
			 * fractional path for each child relation too. Looking at startup
			 * and total costs is not enough, because the cheapest fractional
			 * path may be dominated by two separate paths (one for startup,
			 * one for total).
			 *
			 * When needed (building fractional path), determine the cheapest
			 * fractional path too.
			 */
			if (root->tuple_fraction > 0)
			{
				double		path_fraction = root->tuple_fraction;

				/*
				 * We should not have a dummy child relation here.  However,
				 * we cannot use childrel->rows to compute the tuple fraction,
				 * as childrel can be an upper relation with an unset row
				 * estimate.  Instead, we use the row estimate from the
				 * cheapest_total path, which should already have been forced
				 * to a sane value.
				 */
				Assert(cheapest_total->rows > 0);

				/* Convert absolute limit to a path fraction */
				if (path_fraction >= 1.0)
					path_fraction /= cheapest_total->rows;

				cheapest_fractional =
					get_cheapest_fractional_path_for_pathkeys(childrel->pathlist,
															  pathkeys,
															  NULL,
															  path_fraction);

				/*
				 * If we found no path with matching pathkeys, use the
				 * cheapest total path instead.
				 *
				 * XXX We might consider partially sorted paths too (with an
				 * incremental sort on top). But we'd have to build all the
				 * incremental paths, do the costing etc.
				 *
				 * Also, notice whether we actually have different paths for
				 * the "fractional" and "total" cases.  This helps avoid
				 * generating two identical ordered append paths.
				 */
				if (cheapest_fractional == NULL)
					cheapest_fractional = cheapest_total;
				else if (cheapest_fractional != cheapest_total)
					fraction_neq_total = true;
			}

			/*
			 * Notice whether we actually have different paths for the
			 * "cheapest" and "total" cases.  This helps avoid generating two
			 * identical ordered append paths.
			 */
			if (cheapest_startup != cheapest_total)
				startup_neq_total = true;

			/*
			 * Collect the appropriate child paths.  The required logic varies
			 * for the Append and MergeAppend cases.
			 */
			if (match_partition_order)
			{
				/*
				 * We're going to make a plain Append path.  We don't need
				 * most of what accumulate_append_subpath would do, but we do
				 * want to cut out child Appends or MergeAppends if they have
				 * just a single subpath (and hence aren't doing anything
				 * useful).
				 */
				cheapest_startup =
					get_singleton_append_subpath(cheapest_startup,
												 &startup.child_append_relid_sets);
				cheapest_total =
					get_singleton_append_subpath(cheapest_total,
												 &total.child_append_relid_sets);

				startup.subpaths = lappend(startup.subpaths, cheapest_startup);
				total.subpaths = lappend(total.subpaths, cheapest_total);

				if (cheapest_fractional)
				{
					cheapest_fractional =
						get_singleton_append_subpath(cheapest_fractional,
													 &fractional.child_append_relid_sets);
					fractional.subpaths =
						lappend(fractional.subpaths, cheapest_fractional);
				}
			}
			else
			{
				/*
				 * Otherwise, rely on accumulate_append_subpath to collect the
				 * child paths for the MergeAppend.
				 */
				accumulate_append_subpath(cheapest_startup,
										  &startup.subpaths, NULL,
										  &startup.child_append_relid_sets);
				accumulate_append_subpath(cheapest_total,
										  &total.subpaths, NULL,
										  &total.child_append_relid_sets);

				if (cheapest_fractional)
					accumulate_append_subpath(cheapest_fractional,
											  &fractional.subpaths, NULL,
											  &fractional.child_append_relid_sets);
			}
		}

		/* ... and build the Append or MergeAppend paths */
		if (match_partition_order)
		{
			/* We only need Append */
			add_path(rel, (Path *) create_append_path(root,
													  rel,
													  startup,
													  pathkeys,
													  NULL,
													  0,
													  false,
													  -1));
			if (startup_neq_total)
				add_path(rel, (Path *) create_append_path(root,
														  rel,
														  total,
														  pathkeys,
														  NULL,
														  0,
														  false,
														  -1));

			if (fractional.subpaths && fraction_neq_total)
				add_path(rel, (Path *) create_append_path(root,
														  rel,
														  fractional,
														  pathkeys,
														  NULL,
														  0,
														  false,
														  -1));
		}
		else
		{
			/* We need MergeAppend */
			add_path(rel, (Path *) create_merge_append_path(root,
															rel,
															startup.subpaths,
															startup.child_append_relid_sets,
															pathkeys,
															NULL));
			if (startup_neq_total)
				add_path(rel, (Path *) create_merge_append_path(root,
																rel,
																total.subpaths,
																total.child_append_relid_sets,
																pathkeys,
																NULL));

			if (fractional.subpaths && fraction_neq_total)
				add_path(rel, (Path *) create_merge_append_path(root,
																rel,
																fractional.subpaths,
																fractional.child_append_relid_sets,
																pathkeys,
																NULL));
		}
	}
}

/*
 * get_cheapest_parameterized_child_path
 *		Get cheapest path for this relation that has exactly the requested
 *		parameterization.
 *
 * Returns NULL if unable to create such a path.
 */
/*
 * get_cheapest_parameterized_child_path - (中文)取恰好具有指定参数化的最便宜子路径
 *
 * 【作用】在 append 子关系的 pathlist 中寻找"参数化集合恰好等于
 * required_outer"的最便宜路径;找不到精确匹配时,尝试把已有的"参数化集合
 * 是 required_outer 子集"的路径"重参数化"(reparameterize_path)提升到所需
 * 参数化后再比较成本。用于 add_paths_to_append_rel() 组装参数化 Append 路径。
 *
 * 【设计思想】
 * - 第一步直接查询:get_cheapest_path_for_pathkeys() 找"不超过所需参数化"
 *   的最便宜路径;若其参数化恰好匹配则直接返回;
 * - 否则逐个扫描 pathlist:跳过"所需参数化超集"(参数化只增不减,超集路径
 *   无法满足;用 bms_is_subset 判断);
 * - 重参数化只会增加成本,所以可以提前用当前 cheapest 剪枝;调用
 *   reparameterize_path(root, path, required_outer, 1.0) 时 loop_count 传 1.0,
 *   表示按 nestloop 内层循环一次来估新增 quals 的成本;失败(返回 NULL)则跳过;
 * - 返回值可能为 NULL,调用方(add_paths_to_append_rel)据此判定该参数化
 *   集合下无法凑齐所有子路径。
 *
 * 【参数】
 *   root           —— PlannerInfo;
 *   rel            —— append 子关系;
 *   required_outer —— 期望的参数化集合(必含关系的 lateral_relids)。
 * 【返回值】满足参数化的最便宜路径,或 NULL。
 */
static Path *
get_cheapest_parameterized_child_path(PlannerInfo *root, RelOptInfo *rel,
									  Relids required_outer)
{
	Path	   *cheapest;
	ListCell   *lc;

	/*
	 * Look up the cheapest existing path with no more than the needed
	 * parameterization.  If it has exactly the needed parameterization, we're
	 * done.
	 */
	cheapest = get_cheapest_path_for_pathkeys(rel->pathlist,
											  NIL,
											  required_outer,
											  TOTAL_COST,
											  false);
	Assert(cheapest != NULL);
	if (bms_equal(PATH_REQ_OUTER(cheapest), required_outer))
		return cheapest;

	/*
	 * Otherwise, we can "reparameterize" an existing path to match the given
	 * parameterization, which effectively means pushing down additional
	 * joinquals to be checked within the path's scan.  However, some existing
	 * paths might check the available joinquals already while others don't;
	 * therefore, it's not clear which existing path will be cheapest after
	 * reparameterization.  We have to go through them all and find out.
	 */
	cheapest = NULL;
	foreach(lc, rel->pathlist)
	{
		Path	   *path = (Path *) lfirst(lc);

		/* Can't use it if it needs more than requested parameterization */
		if (!bms_is_subset(PATH_REQ_OUTER(path), required_outer))
			continue;

		/*
		 * Reparameterization can only increase the path's cost, so if it's
		 * already more expensive than the current cheapest, forget it.
		 */
		if (cheapest != NULL &&
			compare_path_costs(cheapest, path, TOTAL_COST) <= 0)
			continue;

		/* Reparameterize if needed, then recheck cost */
		if (!bms_equal(PATH_REQ_OUTER(path), required_outer))
		{
			path = reparameterize_path(root, path, required_outer, 1.0);
			if (path == NULL)
				continue;		/* failed to reparameterize this one */
			Assert(bms_equal(PATH_REQ_OUTER(path), required_outer));

			if (cheapest != NULL &&
				compare_path_costs(cheapest, path, TOTAL_COST) <= 0)
				continue;
		}

		/* We have a new best path */
		cheapest = path;
	}

	/* Return the best path, or NULL if we found no suitable candidate */
	return cheapest;
}

/*
 * accumulate_append_subpath
 *		Add a subpath to the list being built for an Append or MergeAppend.
 *
 * It's possible that the child is itself an Append or MergeAppend path, in
 * which case we can "cut out the middleman" and just add its child paths to
 * our own list.  (We don't try to do this earlier because we need to apply
 * both levels of transformation to the quals.)
 *
 * Note that if we omit a child MergeAppend in this way, we are effectively
 * omitting a sort step, which seems fine: if the parent is to be an Append,
 * its result would be unsorted anyway, while if the parent is to be a
 * MergeAppend, there's no point in a separate sort on a child.
 *
 * Normally, either path is a partial path and subpaths is a list of partial
 * paths, or else path is a non-partial plan and subpaths is a list of those.
 * However, if path is a parallel-aware Append, then we add its partial path
 * children to subpaths and the rest to special_subpaths.  If the latter is
 * NULL, we don't flatten the path at all (unless it contains only partial
 * paths).
 */
/*
 * accumulate_append_subpath - (中文)把一个子路径累加进 Append/MergeAppend 的子路径表
 *
 * 【作用】把 path 加入正在构造的 Append/MergeAppend 的子路径列表,同时维护
 * child_append_relid_sets。若 path 本身是 Append/MergeAppend 且可以"展平",
 * 则把它的子路径直接并入,而不是嵌套一层。被 add_paths_to_append_rel() 与
 * generate_orderedappend_paths() 广泛调用。
 *
 * 【设计思想】
 * - 展平的意义:省略中间层。若父是 MergeAppend,子合并 Append 的多余嵌套
 *   排序无意义;若父是无序 Append,子 MergeAppend 的输出反正会被打乱。
 *   不提前展平是因为两层变量替换(adjust_appendrel_attrs)要分别作用于
 *   父子路径;
 * - 非并行感知的 Append 或首部分路径下标为 0(全 partial)的并行 Append:
 *   整个子路径列表并入 subpaths;带 partial 的并行 Append:把 partial 段
 *   (subpaths[first_partial_path..])并入 subpaths,非 partial 段并入
 *   special_subpaths(父并行 Append 的非 partial 段由 leader 执行);
 * - MergeAppendPath 无条件并入其子路径;
 * - 无论展平与否,都把 path 所属关系(parent->relids)登记进
 *   child_append_relid_sets,以免该关系 id 从最终计划的 relid 集合中消失
 *   (上层用它对 join/unique 判定)。
 *
 * 【参数】
 *   path                     —— 待累加的子路径;
 *   subpaths                 —— 输出/输入:partial(或普通)子路径累积列表;
 *   special_subpaths         —— 输出/输入:并行 Append 的非 partial 段;NULL
 *                              表示不展平并行 Append;
 *   child_append_relid_sets  —— 输出/输入:子 append 关系的 relid 集合列表。
 * 【返回值】无。
 */
static void
accumulate_append_subpath(Path *path, List **subpaths, List **special_subpaths,
						  List **child_append_relid_sets)
{
	if (IsA(path, AppendPath))
	{
		AppendPath *apath = (AppendPath *) path;

		if (!apath->path.parallel_aware || apath->first_partial_path == 0)
		{
			*subpaths = list_concat(*subpaths, apath->subpaths);
			*child_append_relid_sets =
				lappend(*child_append_relid_sets, path->parent->relids);
			*child_append_relid_sets =
				list_concat(*child_append_relid_sets,
							apath->child_append_relid_sets);
			return;
		}
		else if (special_subpaths != NULL)
		{
			List	   *new_special_subpaths;

			/* Split Parallel Append into partial and non-partial subpaths */
			*subpaths = list_concat(*subpaths,
									list_copy_tail(apath->subpaths,
												   apath->first_partial_path));
			new_special_subpaths = list_copy_head(apath->subpaths,
												  apath->first_partial_path);
			*special_subpaths = list_concat(*special_subpaths,
											new_special_subpaths);
			*child_append_relid_sets =
				lappend(*child_append_relid_sets, path->parent->relids);
			*child_append_relid_sets =
				list_concat(*child_append_relid_sets,
							apath->child_append_relid_sets);
			return;
		}
	}
	else if (IsA(path, MergeAppendPath))
	{
		MergeAppendPath *mpath = (MergeAppendPath *) path;

		*subpaths = list_concat(*subpaths, mpath->subpaths);
		*child_append_relid_sets =
			lappend(*child_append_relid_sets, path->parent->relids);
		*child_append_relid_sets =
			list_concat(*child_append_relid_sets,
						mpath->child_append_relid_sets);
		return;
	}

	*subpaths = lappend(*subpaths, path);
}

/*
 * get_singleton_append_subpath
 *		Returns the single subpath of an Append/MergeAppend, or just
 *		return 'path' if it's not a single sub-path Append/MergeAppend.
 *
 * As a side effect, whenever we return a single subpath rather than the
 * original path, add the relid sets for the original path to
 * child_append_relid_sets, so that those relids don't entirely disappear
 * from the final plan.
 *
 * Note: 'path' must not be a parallel-aware path.
 */
/*
 * get_singleton_append_subpath - (中文)若 Append/MergeAppend 只有一个子路径则返回该子路径
 *
 * 【作用】用于有序 Append 的路径组装:如果传入的 path 是"只有一个子路径"的
 * Append/MergeAppend(即它本身没在干实事),就把它"脱壳",返回那唯一的子路径;
 * 否则原样返回 path。副作用:每当脱壳返回子路径时,把原路径所属关系的
 * relid 集合记入 child_append_relid_sets,保证这些 relid 不会从最终计划消失。
 *
 * 【设计思想】子表本身可能是分区(子 append 关系),其路径又包了一层
 * Append/MergeAppend;当该层只有一个子路径时纯属冗余,展开后父路径直接使用
 * 这个子路径即可。要求 path 非并行感知(并行 Append 的语义不能这样简化)。
 *
 * 【参数】
 *   path                     —— 待检查的路径;
 *   child_append_relid_sets  —— 输出/输入:子 append 关系的 relid 集合列表。
 * 【返回值】脱壳后的单子路径,或原 path。
 */
static Path *
get_singleton_append_subpath(Path *path, List **child_append_relid_sets)
{
	Assert(!path->parallel_aware);

	if (IsA(path, AppendPath))
	{
		AppendPath *apath = (AppendPath *) path;

		if (list_length(apath->subpaths) == 1)
		{
			*child_append_relid_sets =
				lappend(*child_append_relid_sets, path->parent->relids);
			*child_append_relid_sets =
				list_concat(*child_append_relid_sets,
							apath->child_append_relid_sets);
			return (Path *) linitial(apath->subpaths);
		}
	}
	else if (IsA(path, MergeAppendPath))
	{
		MergeAppendPath *mpath = (MergeAppendPath *) path;

		if (list_length(mpath->subpaths) == 1)
		{
			*child_append_relid_sets =
				lappend(*child_append_relid_sets, path->parent->relids);
			*child_append_relid_sets =
				list_concat(*child_append_relid_sets,
							mpath->child_append_relid_sets);
			return (Path *) linitial(mpath->subpaths);
		}
	}

	return path;
}

/*
 * set_dummy_rel_pathlist
 *	  Build a dummy path for a relation that's been excluded by constraints
 *
 * Rather than inventing a special "dummy" path type, we represent this as an
 * AppendPath with no members (see also IS_DUMMY_APPEND/IS_DUMMY_REL macros).
 *
 * (See also mark_dummy_rel, which does basically the same thing, but is
 * typically used to change a rel into dummy state after we already made
 * paths for it.)
 */
/*
 * set_dummy_rel_pathlist - (中文)把被约束排除的关系标记为 dummy 并给出空路径
 *
 * 【作用】把关系的大小估算清零、丢弃已有路径,并添加一个"无任何子路径"的
 * AppendPath 作为 dummy 路径。被 set_rel_size()/set_append_rel_size() 在约束
 * 排除证明关系为空时调用;也是整个规划器标记"关系为空"的约定方式。
 *
 * 【设计思想】不发明专门的 dummy 路径类型,而是用空 AppendPath 表示
 * (IS_DUMMY_APPEND/IS_DUMMY_REL 宏据此判断)。dummy 关系虽然零行,仍要保留
 * lateral_relids 作为参数化,以免上层误判可无条件扫描。结尾调用 set_cheapest()
 * 立即填充 cheapest-path 字段(与 mark_dummy_rel 行为一致),虽然当前调用点
 * 稍后也会做,但这是廉价的安全措施。
 *
 * 【参数】
 *   rel —— 待标记为 dummy 的关系。
 * 【返回值】无。
 */
static void
set_dummy_rel_pathlist(RelOptInfo *rel)
{
	AppendPathInput in = {0};

	/* Set dummy size estimates --- we leave attr_widths[] as zeroes */
	rel->rows = 0;
	rel->reltarget->width = 0;

	/* Discard any pre-existing paths; no further need for them */
	rel->pathlist = NIL;
	rel->partial_pathlist = NIL;

	/* Set up the dummy path */
	add_path(rel, (Path *) create_append_path(NULL, rel, in,
											  NIL, rel->lateral_relids,
											  0, false, -1));

	/*
	 * We set the cheapest-path fields immediately, just in case they were
	 * pointing at some discarded path.  This is redundant in current usage
	 * because set_rel_pathlist will do it later, but it's cheap so we keep it
	 * for safety and consistency with mark_dummy_rel.
	 */
	set_cheapest(rel);
}

/*
 * find_window_run_conditions
 *		Determine if 'wfunc' is really a WindowFunc and call its prosupport
 *		function to determine the function's monotonic properties.  We then
 *		see if 'opexpr' can be used to short-circuit execution.
 *
 * For example row_number() over (order by ...) always produces a value one
 * higher than the previous.  If someone has a window function in a subquery
 * and has a WHERE clause in the outer query to filter rows <= 10, then we may
 * as well stop processing the windowagg once the row number reaches 11.  Here
 * we check if 'opexpr' might help us to stop doing needless extra processing
 * in WindowAgg nodes.
 *
 * '*keep_original' is set to true if the caller should also use 'opexpr' for
 * its original purpose.  This is set to false if the caller can assume that
 * the run condition will handle all of the required filtering.
 *
 * Returns true if 'opexpr' was found to be useful and was added to the
 * WindowFunc's runCondition.  We also set *keep_original accordingly and add
 * 'attno' to *run_cond_attrs offset by FirstLowInvalidHeapAttributeNumber.
 * If the 'opexpr' cannot be used then we set *keep_original to true and
 * return false.
 */
/*
 * find_window_run_conditions - (中文)为窗口函数寻找可作 runCondition 的比较条件
 *
 * 【作用】判断子查询输出列上的比较表达式 opexpr 能否改造成窗口函数
 * WindowAgg 的 runCondition,从而在执行时提前终止窗口计算(例如
 * row_number() <= 10 时行号一到 11 就不再处理)。能用时把条件写入
 * wfunc->runCondition、登记 run_cond_attrs,并按需设置 *keep_original。
 * 被 check_and_push_window_quals() 调用。
 *
 * 【设计思想】
 * - 前提:窗口函数的支持函数(prosupport)报告其单调性(monotonic),且被比较
 *   的另一侧是伪常量(pseudo-constant,整个分区内不变);若含子查询则放弃;
 * - 按比较类型转换 runCondition:单调递增函数配合 < / <= 过滤上界
 *   (wfunc 在左)或 > / >= 过滤下界(常数在左);单调递减相反;= 时则改写为
 *   <= / >= 形式过滤掉超过/低于目标值的行(此时原始相等条件必须保留,
 *   keep_original = true);同时支持单调递增又递减(常量函数)时直接用原条件;
 * - 改写用的运算符通过 get_opfamily_member_for_cmptype() 从原运算符所属
 *   opfamily 推导;
 * - 找到可用条件后把 runopexpr 复制进 WindowFuncRunCondition(拷贝的是对侧
 *   表达式),登记"第 attno 列被 runCondition 使用"(偏移
 *   FirstLowInvalidHeapAttributeNumber),供 remove_unused_subquery_outputs()
 *   保留该列不被删除。
 *
 * 【参数】
 *   subquery       —— 被分析的子查询;
 *   attno          —— opexpr 引用的子查询输出列号;
 *   wfunc          —— 对应的窗口函数(调用方已确认其来自该列);
 *   opexpr         —— 候选比较表达式(<、<=、>、>=、=);
 *   wfunc_left     —— wfunc 是否位于 opexpr 左操作数;
 *   keep_original  —— 输出:调用方是否仍需保留原始 qual(置 false 表示
 *                     runCondition 已完全接管过滤);
 *   run_cond_attrs —— 输出:被 runCondition 用到的列号位图(累加)。
 * 【返回值】true:成功把条件加入 wfunc->runCondition;false:不可用。
 */
static bool
find_window_run_conditions(Query *subquery, AttrNumber attno,
						   WindowFunc *wfunc, OpExpr *opexpr, bool wfunc_left,
						   bool *keep_original, Bitmapset **run_cond_attrs)
{
	Oid			prosupport;
	Expr	   *otherexpr;
	SupportRequestWFuncMonotonic req;
	SupportRequestWFuncMonotonic *res;
	WindowClause *wclause;
	List	   *opinfos;
	OpExpr	   *runopexpr;
	Oid			runoperator;
	ListCell   *lc;

	*keep_original = true;

	while (IsA(wfunc, RelabelType))
		wfunc = (WindowFunc *) ((RelabelType *) wfunc)->arg;

	/* we can only work with window functions */
	if (!IsA(wfunc, WindowFunc))
		return false;

	/* can't use it if there are subplans in the WindowFunc */
	if (contain_subplans((Node *) wfunc))
		return false;

	prosupport = get_func_support(wfunc->winfnoid);

	/* Check if there's a support function for 'wfunc' */
	if (!OidIsValid(prosupport))
		return false;

	/* get the Expr from the other side of the OpExpr */
	if (wfunc_left)
		otherexpr = lsecond(opexpr->args);
	else
		otherexpr = linitial(opexpr->args);

	/*
	 * The value being compared must not change during the evaluation of the
	 * window partition.
	 */
	if (!is_pseudo_constant_clause((Node *) otherexpr))
		return false;

	/* find the window clause belonging to the window function */
	wclause = (WindowClause *) list_nth(subquery->windowClause,
										wfunc->winref - 1);

	req.type = T_SupportRequestWFuncMonotonic;
	req.window_func = wfunc;
	req.window_clause = wclause;

	/* call the support function */
	res = (SupportRequestWFuncMonotonic *)
		DatumGetPointer(OidFunctionCall1(prosupport,
										 PointerGetDatum(&req)));

	/*
	 * Nothing to do if the function is neither monotonically increasing nor
	 * monotonically decreasing.
	 */
	if (res == NULL || res->monotonic == MONOTONICFUNC_NONE)
		return false;

	runopexpr = NULL;
	runoperator = InvalidOid;
	opinfos = get_op_index_interpretation(opexpr->opno);

	foreach(lc, opinfos)
	{
		OpIndexInterpretation *opinfo = (OpIndexInterpretation *) lfirst(lc);
		CompareType cmptype = opinfo->cmptype;

		/* handle < / <= */
		if (cmptype == COMPARE_LT || cmptype == COMPARE_LE)
		{
			/*
			 * < / <= is supported for monotonically increasing functions in
			 * the form <wfunc> op <pseudoconst> and <pseudoconst> op <wfunc>
			 * for monotonically decreasing functions.
			 */
			if ((wfunc_left && (res->monotonic & MONOTONICFUNC_INCREASING)) ||
				(!wfunc_left && (res->monotonic & MONOTONICFUNC_DECREASING)))
			{
				*keep_original = false;
				runopexpr = opexpr;
				runoperator = opexpr->opno;
			}
			break;
		}
		/* handle > / >= */
		else if (cmptype == COMPARE_GT || cmptype == COMPARE_GE)
		{
			/*
			 * > / >= is supported for monotonically decreasing functions in
			 * the form <wfunc> op <pseudoconst> and <pseudoconst> op <wfunc>
			 * for monotonically increasing functions.
			 */
			if ((wfunc_left && (res->monotonic & MONOTONICFUNC_DECREASING)) ||
				(!wfunc_left && (res->monotonic & MONOTONICFUNC_INCREASING)))
			{
				*keep_original = false;
				runopexpr = opexpr;
				runoperator = opexpr->opno;
			}
			break;
		}
		/* handle = */
		else if (cmptype == COMPARE_EQ)
		{
			CompareType newcmptype;

			/*
			 * When both monotonically increasing and decreasing then the
			 * return value of the window function will be the same each time.
			 * We can simply use 'opexpr' as the run condition without
			 * modifying it.
			 */
			if ((res->monotonic & MONOTONICFUNC_BOTH) == MONOTONICFUNC_BOTH)
			{
				*keep_original = false;
				runopexpr = opexpr;
				runoperator = opexpr->opno;
				break;
			}

			/*
			 * When monotonically increasing we make a qual with <wfunc> <=
			 * <value> or <value> >= <wfunc> in order to filter out values
			 * which are above the value in the equality condition.  For
			 * monotonically decreasing functions we want to filter values
			 * below the value in the equality condition.
			 */
			if (res->monotonic & MONOTONICFUNC_INCREASING)
				newcmptype = wfunc_left ? COMPARE_LE : COMPARE_GE;
			else
				newcmptype = wfunc_left ? COMPARE_GE : COMPARE_LE;

			/* We must keep the original equality qual */
			*keep_original = true;
			runopexpr = opexpr;

			/* determine the operator to use for the WindowFuncRunCondition */
			runoperator = get_opfamily_member_for_cmptype(opinfo->opfamily_id,
														  opinfo->oplefttype,
														  opinfo->oprighttype,
														  newcmptype);
			break;
		}
	}

	if (runopexpr != NULL)
	{
		WindowFuncRunCondition *wfuncrc;

		wfuncrc = makeNode(WindowFuncRunCondition);
		wfuncrc->opno = runoperator;
		wfuncrc->inputcollid = runopexpr->inputcollid;
		wfuncrc->wfunc_left = wfunc_left;
		wfuncrc->arg = copyObject(otherexpr);

		wfunc->runCondition = lappend(wfunc->runCondition, wfuncrc);

		/* record that this attno was used in a run condition */
		*run_cond_attrs = bms_add_member(*run_cond_attrs,
										 attno - FirstLowInvalidHeapAttributeNumber);
		return true;
	}

	/* unsupported OpExpr */
	return false;
}

/*
 * check_and_push_window_quals
 *		Check if 'clause' is a qual that can be pushed into a WindowFunc
 *		as a 'runCondition' qual.  These, when present, allow some unnecessary
 *		work to be skipped during execution.
 *
 * 'run_cond_attrs' will be populated with all targetlist resnos of subquery
 * targets (offset by FirstLowInvalidHeapAttributeNumber) that we pushed
 * window quals for.
 *
 * Returns true if the caller still must keep the original qual or false if
 * the caller can safely ignore the original qual because the WindowAgg node
 * will use the runCondition to stop returning tuples.
 */
/*
 * check_and_push_window_quals - (中文)检查子查询外层 qual 能否推进为窗口 runCondition
 *
 * 【作用】给定子查询外层的一个限制条件 clause(取自 baserestrictinfo,由
 * qual_is_pushdown_safe 判定为 PUSHDOWN_WINDOWCLAUSE_RUNCOND),检查它是否
 * 是"窗口函数 <=/>= 常数"形式的二元比较;是则进一步调用
 * find_window_run_conditions() 尝试把它改造成 WindowAgg 的 runCondition。
 * 由 set_subquery_pathlist() 调用。
 *
 * 【设计思想】
 * - 只接受二元 OpExpr,且要求操作符严格(strict):一旦 runCondition 变 false
 *   执行器就停止计算 WindowFunc 并把剩余值置 NULL,只有严格函数才能保证
 *   顶层 WindowAgg 正确过滤含 NULL 的行;
 * - 分别在左、右操作数里找引用子查询输出列(targetlist 元素)的 Var,且该列
 *   表达式是 WindowFunc 时才有戏;找到后询问 find_window_run_conditions(),
 *   按其返回值决定调用方是否还需保留原始 qual。
 *
 * 【参数】
 *   subquery       —— 被分析的子查询;
 *   clause         —— 候选限制条件(通常来自上层 baserestrictinfo);
 *   run_cond_attrs —— 输出:被 runCondition 用到的子查询输出列位图(累加)。
 * 【返回值】true:调用方必须保留原始 qual;false:runCondition 已接管过滤,
 *           调用方可丢弃原始 qual。
 */
static bool
check_and_push_window_quals(Query *subquery, Node *clause,
							Bitmapset **run_cond_attrs)
{
	OpExpr	   *opexpr = (OpExpr *) clause;
	bool		keep_original = true;
	Var		   *var1;
	Var		   *var2;

	/* We're only able to use OpExprs with 2 operands */
	if (!IsA(opexpr, OpExpr))
		return true;

	if (list_length(opexpr->args) != 2)
		return true;

	/*
	 * Currently, we restrict this optimization to strict OpExprs.  The reason
	 * for this is that during execution, once the runcondition becomes false,
	 * we stop evaluating WindowFuncs.  To avoid leaving around stale window
	 * function result values, we set them to NULL.  Having only strict
	 * OpExprs here ensures that we properly filter out the tuples with NULLs
	 * in the top-level WindowAgg.
	 */
	set_opfuncid(opexpr);
	if (!func_strict(opexpr->opfuncid))
		return true;

	/*
	 * Check for plain Vars that reference window functions in the subquery.
	 * If we find any, we'll ask find_window_run_conditions() if 'opexpr' can
	 * be used as part of the run condition.
	 */

	/* Check the left side of the OpExpr */
	var1 = linitial(opexpr->args);
	if (IsA(var1, Var) && var1->varattno > 0)
	{
		TargetEntry *tle = list_nth(subquery->targetList, var1->varattno - 1);
		WindowFunc *wfunc = (WindowFunc *) tle->expr;

		if (find_window_run_conditions(subquery, tle->resno, wfunc, opexpr,
									   true, &keep_original, run_cond_attrs))
			return keep_original;
	}

	/* and check the right side */
	var2 = lsecond(opexpr->args);
	if (IsA(var2, Var) && var2->varattno > 0)
	{
		TargetEntry *tle = list_nth(subquery->targetList, var2->varattno - 1);
		WindowFunc *wfunc = (WindowFunc *) tle->expr;

		if (find_window_run_conditions(subquery, tle->resno, wfunc, opexpr,
									   false, &keep_original, run_cond_attrs))
			return keep_original;
	}

	return true;
}

/*
 * set_subquery_pathlist
 *		Generate SubqueryScan access paths for a subquery RTE
 *
 * We don't currently support generating parameterized paths for subqueries
 * by pushing join clauses down into them; it seems too expensive to re-plan
 * the subquery multiple times to consider different alternatives.
 * (XXX that could stand to be reconsidered, now that we use Paths.)
 * So the paths made here will be parameterized if the subquery contains
 * LATERAL references, otherwise not.  As long as that's true, there's no need
 * for a separate set_subquery_size phase: just make the paths right away.
 */
/*
 * set_subquery_pathlist - (中文)为子查询 RTE 生成 SubqueryScan 访问路径
 *
 * 【作用】处理 FROM 中的子查询:拷贝 Query 以免规划过程破坏原 RTE;尝试把
 * 上层限制条件推入子查询(WHERE/HAVING 或窗口 runCondition);删除子查询不
 * 需要的输出列;递归调用 subquery_planner() 为子查询生成子计划;然后把子
 * 计划的每条路径包装成 SubqueryScanPath 加入本关系。由 set_rel_size() 对
 * RTE_SUBQUERY 调用(在估算阶段就完成路径生成)。
 *
 * 【设计思想】
 * - 推入条件的正确性分三层把关:subquery_is_pushdown_safe() 检查子查询整体
 *   结构是否安全(LIMIT/EXCEPT/DISTINCT/窗口/集合函数/分组集等),
 *   qual_is_pushdown_safe() 检查单条 qual(伪常量除外,留给上层做 gating),
 *   推入时再用 setop 树递归 + ReplaceVarsFromTargetList 完成变量替换;
 *   推入到 HAVING 而不是 WHERE 的判定依据是子查询是否分组/聚合;
 * - 未能推入的条件留在 SubqueryScan 的 qpqual;推入窗口 runCondition 的条件
 *   仍可能要在上层保留(见 check_and_push_window_quals 返回值);
 * - tuple_fraction 只有在当前查询无连接/聚合/排序时才可下传,否则子查询要
 *   按"取全部行"来规划,否则外层过滤会破坏语义;
 * - 子查询规划结果(subroot、plan_params)保存在 rel->subroot /
 *   rel->subplan_params,供执行期初始化 SubPlan 参数;若子查询被约束排除证明
 *   为空则整个关系置 dummy;
 * - reltarget 的 trivial 性(按序逐列取子计划输出)预先算出并传给
 *   cost_subqueryscan(),避免它重复推导;
 * - 子查询路径同样支持并行:若 rel->consider_parallel 且无参数化,把子计划
 *   的 partial 路径逐个包装为 SubqueryScanPath 加入 partial_pathlist。
 *
 * 【参数】
 *   root —— 外层查询的 PlannerInfo;
 *   rel  —— 子查询关系(RELOPT_BASEREL);
 *   rti  —— rel 在 rtable 中的索引;
 *   rte  —— 对应 RangeTblEntry(RTE_SUBQUERY)。
 * 【返回值】无。
 */
static void
set_subquery_pathlist(PlannerInfo *root, RelOptInfo *rel,
					  Index rti, RangeTblEntry *rte)
{
	Query	   *parse = root->parse;
	Query	   *subquery = rte->subquery;
	bool		trivial_pathtarget;
	Relids		required_outer;
	pushdown_safety_info safetyInfo;
	double		tuple_fraction;
	RelOptInfo *sub_final_rel;
	Bitmapset  *run_cond_attrs = NULL;
	ListCell   *lc;
	char	   *plan_name;

	/*
	 * Must copy the Query so that planning doesn't mess up the RTE contents
	 * (really really need to fix the planner to not scribble on its input,
	 * someday ... but see remove_unused_subquery_outputs to start with).
	 */
	subquery = copyObject(subquery);

	/*
	 * If it's a LATERAL subquery, it might contain some Vars of the current
	 * query level, requiring it to be treated as parameterized, even though
	 * we don't support pushing down join quals into subqueries.
	 */
	required_outer = rel->lateral_relids;

	/*
	 * Zero out result area for subquery_is_pushdown_safe, so that it can set
	 * flags as needed while recursing.  In particular, we need a workspace
	 * for keeping track of the reasons why columns are unsafe to reference.
	 * These reasons are stored in the bits inside unsafeFlags[i] when we
	 * discover reasons that column i of the subquery is unsafe to be used in
	 * a pushed-down qual.
	 */
	memset(&safetyInfo, 0, sizeof(safetyInfo));
	safetyInfo.unsafeFlags = (unsigned char *)
		palloc0((list_length(subquery->targetList) + 1) * sizeof(unsigned char));

	/*
	 * If the subquery has the "security_barrier" flag, it means the subquery
	 * originated from a view that must enforce row-level security.  Then we
	 * must not push down quals that contain leaky functions.  (Ideally this
	 * would be checked inside subquery_is_pushdown_safe, but since we don't
	 * currently pass the RTE to that function, we must do it here.)
	 */
	safetyInfo.unsafeLeaky = rte->security_barrier;

	/*
	 * If there are any restriction clauses that have been attached to the
	 * subquery relation, consider pushing them down to become WHERE or HAVING
	 * quals of the subquery itself.  This transformation is useful because it
	 * may allow us to generate a better plan for the subquery than evaluating
	 * all the subquery output rows and then filtering them.
	 *
	 * There are several cases where we cannot push down clauses. Restrictions
	 * involving the subquery are checked by subquery_is_pushdown_safe().
	 * Restrictions on individual clauses are checked by
	 * qual_is_pushdown_safe().  Also, we don't want to push down
	 * pseudoconstant clauses; better to have the gating node above the
	 * subquery.
	 *
	 * Non-pushed-down clauses will get evaluated as qpquals of the
	 * SubqueryScan node.
	 *
	 * XXX Are there any cases where we want to make a policy decision not to
	 * push down a pushable qual, because it'd result in a worse plan?
	 */
	if (rel->baserestrictinfo != NIL &&
		subquery_is_pushdown_safe(subquery, subquery, &safetyInfo))
	{
		/* OK to consider pushing down individual quals */
		List	   *upperrestrictlist = NIL;
		ListCell   *l;

		foreach(l, rel->baserestrictinfo)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(l);
			Node	   *clause = (Node *) rinfo->clause;

			if (rinfo->pseudoconstant)
			{
				upperrestrictlist = lappend(upperrestrictlist, rinfo);
				continue;
			}

			switch (qual_is_pushdown_safe(subquery, rti, rinfo, &safetyInfo))
			{
				case PUSHDOWN_SAFE:
					/* Push it down */
					subquery_push_qual(subquery, rte, rti, clause);
					break;

				case PUSHDOWN_WINDOWCLAUSE_RUNCOND:

					/*
					 * Since we can't push the qual down into the subquery,
					 * check if it happens to reference a window function.  If
					 * so then it might be useful to use for the WindowAgg's
					 * runCondition.
					 */
					if (!subquery->hasWindowFuncs ||
						check_and_push_window_quals(subquery, clause,
													&run_cond_attrs))
					{
						/*
						 * subquery has no window funcs or the clause is not a
						 * suitable window run condition qual or it is, but
						 * the original must also be kept in the upper query.
						 */
						upperrestrictlist = lappend(upperrestrictlist, rinfo);
					}
					break;

				case PUSHDOWN_UNSAFE:
					upperrestrictlist = lappend(upperrestrictlist, rinfo);
					break;
			}
		}
		rel->baserestrictinfo = upperrestrictlist;
		/* We don't bother recomputing baserestrict_min_security */
	}

	pfree(safetyInfo.unsafeFlags);

	/*
	 * The upper query might not use all the subquery's output columns; if
	 * not, we can simplify.  Pass the attributes that were pushed down into
	 * WindowAgg run conditions to ensure we don't accidentally think those
	 * are unused.
	 */
	remove_unused_subquery_outputs(subquery, rel, run_cond_attrs);

	/*
	 * We can safely pass the outer tuple_fraction down to the subquery if the
	 * outer level has no joining, aggregation, or sorting to do. Otherwise
	 * we'd better tell the subquery to plan for full retrieval. (XXX This
	 * could probably be made more intelligent ...)
	 */
	if (parse->hasAggs ||
		parse->groupClause ||
		parse->groupingSets ||
		root->hasHavingQual ||
		parse->distinctClause ||
		parse->sortClause ||
		bms_membership(root->all_baserels) == BMS_MULTIPLE)
		tuple_fraction = 0.0;	/* default case */
	else
		tuple_fraction = root->tuple_fraction;

	/* plan_params should not be in use in current query level */
	Assert(root->plan_params == NIL);

	/* Generate a subroot and Paths for the subquery */
	plan_name = choose_plan_name(root->glob, rte->eref->aliasname, false);
	rel->subroot = subquery_planner(root->glob, subquery, plan_name,
									root, NULL, false, tuple_fraction, NULL);

	/* Isolate the params needed by this specific subplan */
	rel->subplan_params = root->plan_params;
	root->plan_params = NIL;

	/*
	 * It's possible that constraint exclusion proved the subquery empty. If
	 * so, it's desirable to produce an unadorned dummy path so that we will
	 * recognize appropriate optimizations at this query level.
	 */
	sub_final_rel = fetch_upper_rel(rel->subroot, UPPERREL_FINAL, NULL);

	if (IS_DUMMY_REL(sub_final_rel))
	{
		set_dummy_rel_pathlist(rel);
		return;
	}

	/*
	 * Mark rel with estimated output rows, width, etc.  Note that we have to
	 * do this before generating outer-query paths, else cost_subqueryscan is
	 * not happy.
	 */
	set_subquery_size_estimates(root, rel);

	/*
	 * Also detect whether the reltarget is trivial, so that we can pass that
	 * info to cost_subqueryscan (rather than re-deriving it multiple times).
	 * It's trivial if it fetches all the subplan output columns in order.
	 */
	if (list_length(rel->reltarget->exprs) != list_length(subquery->targetList))
		trivial_pathtarget = false;
	else
	{
		trivial_pathtarget = true;
		foreach(lc, rel->reltarget->exprs)
		{
			Node	   *node = (Node *) lfirst(lc);
			Var		   *var;

			if (!IsA(node, Var))
			{
				trivial_pathtarget = false;
				break;
			}
			var = (Var *) node;
			if (var->varno != rti ||
				var->varattno != foreach_current_index(lc) + 1)
			{
				trivial_pathtarget = false;
				break;
			}
		}
	}

	/*
	 * For each Path that subquery_planner produced, make a SubqueryScanPath
	 * in the outer query.
	 */
	foreach(lc, sub_final_rel->pathlist)
	{
		Path	   *subpath = (Path *) lfirst(lc);
		List	   *pathkeys;

		/* Convert subpath's pathkeys to outer representation */
		pathkeys = convert_subquery_pathkeys(root,
											 rel,
											 subpath->pathkeys,
											 make_tlist_from_pathtarget(subpath->pathtarget));

		/* Generate outer path using this subpath */
		add_path(rel, (Path *)
				 create_subqueryscan_path(root, rel, subpath,
										  trivial_pathtarget,
										  pathkeys, required_outer));
	}

	/* If outer rel allows parallelism, do same for partial paths. */
	if (rel->consider_parallel && bms_is_empty(required_outer))
	{
		/* If consider_parallel is false, there should be no partial paths. */
		Assert(sub_final_rel->consider_parallel ||
			   sub_final_rel->partial_pathlist == NIL);

		/* Same for partial paths. */
		foreach(lc, sub_final_rel->partial_pathlist)
		{
			Path	   *subpath = (Path *) lfirst(lc);
			List	   *pathkeys;

			/* Convert subpath's pathkeys to outer representation */
			pathkeys = convert_subquery_pathkeys(root,
												 rel,
												 subpath->pathkeys,
												 make_tlist_from_pathtarget(subpath->pathtarget));

			/* Generate outer path using this subpath */
			add_partial_path(rel, (Path *)
							 create_subqueryscan_path(root, rel, subpath,
													  trivial_pathtarget,
													  pathkeys,
													  required_outer));
		}
	}
}

/*
 * set_function_pathlist
 *		Build the (single) access path for a function RTE
 */
/*
 * set_function_pathlist - (中文)为函数 RTE(FROM 中的函数)生成访问路径
 *
 * 【作用】为 RTE_FUNCTION 生成唯一的 FunctionScan 路径加入 rel->pathlist。
 * 由 set_rel_pathlist() 调用。函数扫描不下推连接条件,但 LATERAL 引用造成的
 * 参数化需要保留。
 *
 * 【设计思想】函数结果默认无序;若函数带 WITH ORDINALITY,则输出按序数列
 * (最后一列)有序。此时若该列出现在关系 tlist 中,尝试用
 * build_expression_pathkey() 构造排序键——注意传 allow_no_new_eclass = false,
 * 表示如果该列尚不属于任何等价类(即没有人在意排序),就不要新建等价类,
 * 路径保持无序。构造成功后 FunctionScan 路径带 pathkeys,上层可据此做
 * 免排序合并等。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 函数关系;
 *   rte  —— 对应 RangeTblEntry(RTE_FUNCTION)。
 * 【返回值】无。
 */
static void
set_function_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Relids		required_outer;
	List	   *pathkeys = NIL;

	/*
	 * We don't support pushing join clauses into the quals of a function
	 * scan, but it could still have required parameterization due to LATERAL
	 * refs in the function expression.
	 */
	required_outer = rel->lateral_relids;

	/*
	 * The result is considered unordered unless ORDINALITY was used, in which
	 * case it is ordered by the ordinal column (the last one).  See if we
	 * care, by checking for uses of that Var in equivalence classes.
	 */
	if (rte->funcordinality)
	{
		AttrNumber	ordattno = rel->max_attr;
		Var		   *var = NULL;
		ListCell   *lc;

		/*
		 * Is there a Var for it in rel's targetlist?  If not, the query did
		 * not reference the ordinality column, or at least not in any way
		 * that would be interesting for sorting.
		 */
		foreach(lc, rel->reltarget->exprs)
		{
			Var		   *node = (Var *) lfirst(lc);

			/* checking varno/varlevelsup is just paranoia */
			if (IsA(node, Var) &&
				node->varattno == ordattno &&
				node->varno == rel->relid &&
				node->varlevelsup == 0)
			{
				var = node;
				break;
			}
		}

		/*
		 * Try to build pathkeys for this Var with int8 sorting.  We tell
		 * build_expression_pathkey not to build any new equivalence class; if
		 * the Var isn't already mentioned in some EC, it means that nothing
		 * cares about the ordering.
		 */
		if (var)
			pathkeys = build_expression_pathkey(root,
												(Expr *) var,
												Int8LessOperator,
												rel->relids,
												false);
	}

	/* Generate appropriate path */
	add_path(rel, create_functionscan_path(root, rel,
										   pathkeys, required_outer));
}

/*
 * set_values_pathlist
 *		Build the (single) access path for a VALUES RTE
 */
/*
 * set_values_pathlist - (中文)为 VALUES 列表 RTE 生成访问路径
 *
 * 【作用】为 RTE_VALUES 生成唯一的 ValuesScan 路径加入 rel->pathlist。
 * 由 set_rel_pathlist() 调用。VALUES 扫描不下推连接条件,但 LATERAL 引用
 * (出现在 values 表达式中)造成的参数化需要保留。
 *
 * 【设计思想】VALUES 列表本质上是一组常量行,执行器逐行返回,没有索引等
 * 其它访问方式,所以只有一条路径。行数估算已在 set_values_size_estimates()
 * 完成(见 set_rel_size)。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— VALUES 关系;
 *   rte  —— 对应 RangeTblEntry(RTE_VALUES)。
 * 【返回值】无。
 */
static void
set_values_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Relids		required_outer;

	/*
	 * We don't support pushing join clauses into the quals of a values scan,
	 * but it could still have required parameterization due to LATERAL refs
	 * in the values expressions.
	 */
	required_outer = rel->lateral_relids;

	/* Generate appropriate path */
	add_path(rel, create_valuesscan_path(root, rel, required_outer));
}

/*
 * set_tablefunc_pathlist
 *		Build the (single) access path for a table func RTE
 */
/*
 * set_tablefunc_pathlist - (中文)为 XMLTABLE 等表函数 RTE 生成访问路径
 *
 * 【作用】为 RTE_TABLEFUNC 生成唯一的 TableFuncScan 路径加入 rel->pathlist。
 * 由 set_rel_pathlist() 调用。表函数扫描不下推连接条件,但 LATERAL 引用造成
 * 的参数化需要保留。
 *
 * 【设计思想】表函数(XMLTABLE 等)由执行器直接展开成行,没有其它访问方式,
 * 所以只有一条路径。大小估算在 set_tablefunc_size_estimates() 完成(见
 * set_rel_size)。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 表函数关系;
 *   rte  —— 对应 RangeTblEntry(RTE_TABLEFUNC)。
 * 【返回值】无。
 */
static void
set_tablefunc_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Relids		required_outer;

	/*
	 * We don't support pushing join clauses into the quals of a tablefunc
	 * scan, but it could still have required parameterization due to LATERAL
	 * refs in the function expression.
	 */
	required_outer = rel->lateral_relids;

	/* Generate appropriate path */
	add_path(rel, create_tablefuncscan_path(root, rel,
											required_outer));
}

/*
 * set_cte_pathlist
 *		Build the (single) access path for a non-self-reference CTE RTE
 *
 * There's no need for a separate set_cte_size phase, since we don't
 * support join-qual-parameterized paths for CTEs.
 */
/*
 * set_cte_pathlist - (中文)为非递归 CTE 引用 RTE 生成访问路径
 *
 * 【作用】为 RTE_CTE(非 self-reference)生成唯一的 CteScan 路径:根据
 * ctelevelsup 找到规划该 CTE 的那一层(cteroot),在其 cteList 中按名字定位
 * CTE 并取得已生成好的路径(glob->subpaths[plan_id-1])与计划,据此设置大小
 * 估算、转换排序键,最后创建 CteScan 路径。由 set_rel_size() 对非递归 CTE
 * 调用。
 *
 * 【设计思想】CTE 先于引用处整体规划好(见 planner.c 的 WITH 处理),本函数
 * 只负责"引用"它,因此同样不存在参数化选择问题,大小与路径在同一阶段完成。
 * cte_plan_ids 可能比 cteList 短(规划过程中某个 CTE 引用另一个正在规划的
 * CTE),所以要按名字线性查找并校验 plan_id 合法。路径排序键用
 * convert_subquery_pathkeys() 从 CTE 内部表示转换为外层表示。
 *
 * 【参数】
 *   root —— 引用 CTE 那一层的 PlannerInfo;
 *   rel  —— CTE 引用关系;
 *   rte  —— 对应 RangeTblEntry(RTE_CTE)。
 * 【返回值】无。
 */
static void
set_cte_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Path	   *ctepath;
	Plan	   *cteplan;
	PlannerInfo *cteroot;
	Index		levelsup;
	List	   *pathkeys;
	int			ndx;
	ListCell   *lc;
	int			plan_id;
	Relids		required_outer;

	/*
	 * Find the referenced CTE, and locate the path and plan previously made
	 * for it.
	 */
	levelsup = rte->ctelevelsup;
	cteroot = root;
	while (levelsup-- > 0)
	{
		cteroot = cteroot->parent_root;
		if (!cteroot)			/* shouldn't happen */
			elog(ERROR, "bad levelsup for CTE \"%s\"", rte->ctename);
	}

	/*
	 * Note: cte_plan_ids can be shorter than cteList, if we are still working
	 * on planning the CTEs (ie, this is a side-reference from another CTE).
	 * So we mustn't use forboth here.
	 */
	ndx = 0;
	foreach(lc, cteroot->parse->cteList)
	{
		CommonTableExpr *cte = (CommonTableExpr *) lfirst(lc);

		if (strcmp(cte->ctename, rte->ctename) == 0)
			break;
		ndx++;
	}
	if (lc == NULL)				/* shouldn't happen */
		elog(ERROR, "could not find CTE \"%s\"", rte->ctename);
	if (ndx >= list_length(cteroot->cte_plan_ids))
		elog(ERROR, "could not find plan for CTE \"%s\"", rte->ctename);
	plan_id = list_nth_int(cteroot->cte_plan_ids, ndx);
	if (plan_id <= 0)
		elog(ERROR, "no plan was made for CTE \"%s\"", rte->ctename);

	Assert(list_length(root->glob->subpaths) == list_length(root->glob->subplans));
	ctepath = (Path *) list_nth(root->glob->subpaths, plan_id - 1);
	cteplan = (Plan *) list_nth(root->glob->subplans, plan_id - 1);

	/* Mark rel with estimated output rows, width, etc */
	set_cte_size_estimates(root, rel, cteplan->plan_rows);

	/* Convert the ctepath's pathkeys to outer query's representation */
	pathkeys = convert_subquery_pathkeys(root,
										 rel,
										 ctepath->pathkeys,
										 cteplan->targetlist);

	/*
	 * We don't support pushing join clauses into the quals of a CTE scan, but
	 * it could still have required parameterization due to LATERAL refs in
	 * its tlist.
	 */
	required_outer = rel->lateral_relids;

	/* Generate appropriate path */
	add_path(rel, create_ctescan_path(root, rel, pathkeys, required_outer));
}

/*
 * set_namedtuplestore_pathlist
 *		Build the (single) access path for a named tuplestore RTE
 *
 * There's no need for a separate set_namedtuplestore_size phase, since we
 * don't support join-qual-parameterized paths for tuplestores.
 */
/*
 * set_namedtuplestore_pathlist - (中文)为具名 tuplestore RTE 生成访问路径
 *
 * 【作用】为 RTE_NAMEDTUPLESTORE(spi 之类机制传入的具名 tuplestore)设置
 * 大小估算并生成唯一的 NamedTuplestoreScan 路径。由 set_rel_size() 调用。
 *
 * 【设计思想】tuplestore 内容已在进入查询前物化,没有其它访问方式,也不支持
 * 参数化路径选择,所以大小与路径在同一阶段完成。LATERAL 引用造成的参数化
 * 仍需保留。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— tuplestore 引用关系;
 *   rte  —— 对应 RangeTblEntry(RTE_NAMEDTUPLESTORE)。
 * 【返回值】无。
 */
static void
set_namedtuplestore_pathlist(PlannerInfo *root, RelOptInfo *rel,
							 RangeTblEntry *rte)
{
	Relids		required_outer;

	/* Mark rel with estimated output rows, width, etc */
	set_namedtuplestore_size_estimates(root, rel);

	/*
	 * We don't support pushing join clauses into the quals of a tuplestore
	 * scan, but it could still have required parameterization due to LATERAL
	 * refs in its tlist.
	 */
	required_outer = rel->lateral_relids;

	/* Generate appropriate path */
	add_path(rel, create_namedtuplestorescan_path(root, rel, required_outer));
}

/*
 * set_result_pathlist
 *		Build the (single) access path for an RTE_RESULT RTE
 *
 * There's no need for a separate set_result_size phase, since we
 * don't support join-qual-parameterized paths for these RTEs.
 */
/*
 * set_result_pathlist - (中文)为 RTE_RESULT 关系生成访问路径
 *
 * 【作用】为 RTE_RESULT(表示"无实际数据源"的 Result 关系,例如仅含常量列的
 * SELECT)设置大小估算并生成唯一的 ResultScan 路径。由 set_rel_size() 调用。
 *
 * 【设计思想】RTE_RESULT 只产生一行(或不产生),没有扫描语义,也没有其它访问
 * 方式;大小与路径在同一阶段完成。LATERAL 引用造成的参数化仍需保留。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— Result 关系;
 *   rte  —— 对应 RangeTblEntry(RTE_RESULT)。
 * 【返回值】无。
 */
static void
set_result_pathlist(PlannerInfo *root, RelOptInfo *rel,
					RangeTblEntry *rte)
{
	Relids		required_outer;

	/* Mark rel with estimated output rows, width, etc */
	set_result_size_estimates(root, rel);

	/*
	 * We don't support pushing join clauses into the quals of a Result scan,
	 * but it could still have required parameterization due to LATERAL refs
	 * in its tlist.
	 */
	required_outer = rel->lateral_relids;

	/* Generate appropriate path */
	add_path(rel, create_resultscan_path(root, rel, required_outer));
}

/*
 * set_worktable_pathlist
 *		Build the (single) access path for a self-reference CTE RTE
 *
 * There's no need for a separate set_worktable_size phase, since we don't
 * support join-qual-parameterized paths for CTEs.
 */
/*
 * set_worktable_pathlist - (中文)为递归 CTE 的工作表引用 RTE 生成访问路径
 *
 * 【作用】为递归 CTE 中"引用工作表(worktable)"的 RTE 生成唯一的
 * WorkTableScan 路径:沿 ctelevelsup 向上找到递归 UNION 所在层,取其
 * non_recursive_path(非递归项的路径,代表工作表的初始内容)来估算大小。
 * 由 set_rel_size() 对 self-reference 的 CTE 引用调用。
 *
 * 【设计思想】递归 CTE 的工作表在每次迭代后更新,其扫描由执行器的
 * WorkTableScan 节点完成。这里需要注意 ctelevelsup 指向的层"下面"才是处理
 * 递归 UNION 的层(levelsup 要减 1),因为工作表由递归查询本身维护。
 * non_recursive_path 决定初始内容的大小,递归扩展的增量没有单独估计。
 *
 * 【参数】
 *   root —— 引用工作表的查询层 PlannerInfo;
 *   rel  —— 工作表引用关系;
 *   rte  —— 对应 RangeTblEntry(RTE_CTE,self_reference 为真)。
 * 【返回值】无。
 */
static void
set_worktable_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Path	   *ctepath;
	PlannerInfo *cteroot;
	Index		levelsup;
	Relids		required_outer;

	/*
	 * We need to find the non-recursive term's path, which is in the plan
	 * level that's processing the recursive UNION, which is one level *below*
	 * where the CTE comes from.
	 */
	levelsup = rte->ctelevelsup;
	if (levelsup == 0)			/* shouldn't happen */
		elog(ERROR, "bad levelsup for CTE \"%s\"", rte->ctename);
	levelsup--;
	cteroot = root;
	while (levelsup-- > 0)
	{
		cteroot = cteroot->parent_root;
		if (!cteroot)			/* shouldn't happen */
			elog(ERROR, "bad levelsup for CTE \"%s\"", rte->ctename);
	}
	ctepath = cteroot->non_recursive_path;
	if (!ctepath)				/* shouldn't happen */
		elog(ERROR, "could not find path for CTE \"%s\"", rte->ctename);

	/* Mark rel with estimated output rows, width, etc */
	set_cte_size_estimates(root, rel, ctepath->rows);

	/*
	 * We don't support pushing join clauses into the quals of a worktable
	 * scan, but it could still have required parameterization due to LATERAL
	 * refs in its tlist.  (I'm not sure this is actually possible given the
	 * restrictions on recursive references, but it's easy enough to support.)
	 */
	required_outer = rel->lateral_relids;

	/* Generate appropriate path */
	add_path(rel, create_worktablescan_path(root, rel, required_outer));
}

/*
 * generate_gather_paths
 *		Generate parallel access paths for a relation by pushing a Gather or
 *		Gather Merge on top of a partial path.
 *
 * This must not be called until after we're done creating all partial paths
 * for the specified relation.  (Otherwise, add_partial_path might delete a
 * path that some GatherPath or GatherMergePath has a reference to.)
 *
 * If we're generating paths for a scan or join relation, override_rows will
 * be false, and we'll just use the relation's size estimate.  When we're
 * being called for a partially-grouped or partially-distinct path, though, we
 * need to override the rowcount estimate.  (It's not clear that the
 * particular value we're using here is actually best, but the underlying rel
 * has no estimate so we must do something.)
 */
/*
 * generate_gather_paths - (中文)在 partial 路径之上生成 Gather / Gather Merge 路径
 *
 * 【作用】把关系的 partial 路径集合转化为完整的并行路径:对最便宜的(无序)
 * partial 路径包一层 Gather;对每条带排序键的 partial 路径包一层保序的
 * Gather Merge。生成结果加入 rel->pathlist。被 generate_useful_gather_paths()、
 * planner.c 以及扫描/连接关系路径生成完毕时调用。
 *
 * 【设计思想】
 * - 前提:调用时该关系的所有 partial 路径都已创建完毕,否则 add_partial_path
 *   可能删除已被本函数引用的路径;
 * - Gather 输出无序,因此只需考虑最便宜的 partial 路径(partial_pathlist 头部,
 *   add_partial_path 保证最便宜的在前);
 * - Gather Merge 保序:对每个带 pathkeys 的 partial 路径生成一条,输出行数
 *   用 compute_gather_rows() 折算(考虑 worker 间的重复计数);
 * - override_rows 为 true 时(用于部分聚合/部分 distinct 的上层关系)覆盖关系
 *   自带的行数估计,因为这类关系没有合理估计。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   rel           —— 拥有 partial_pathlist 的关系;
 *   override_rows —— true 时用 compute_gather_rows 覆盖 rel->rows 用于成本计算。
 * 【返回值】无。
 */
void
generate_gather_paths(PlannerInfo *root, RelOptInfo *rel, bool override_rows)
{
	Path	   *cheapest_partial_path;
	Path	   *simple_gather_path;
	ListCell   *lc;
	double		rows;
	double	   *rowsp = NULL;

	/* If there are no partial paths, there's nothing to do here. */
	if (rel->partial_pathlist == NIL)
		return;

	/* Should we override the rel's rowcount estimate? */
	if (override_rows)
		rowsp = &rows;

	/*
	 * The output of Gather is always unsorted, so there's only one partial
	 * path of interest: the cheapest one.  That will be the one at the front
	 * of partial_pathlist because of the way add_partial_path works.
	 */
	cheapest_partial_path = linitial(rel->partial_pathlist);
	rows = compute_gather_rows(cheapest_partial_path);
	simple_gather_path = (Path *)
		create_gather_path(root, rel, cheapest_partial_path, rel->reltarget,
						   NULL, rowsp);
	add_path(rel, simple_gather_path);

	/*
	 * For each useful ordering, we can consider an order-preserving Gather
	 * Merge.
	 */
	foreach(lc, rel->partial_pathlist)
	{
		Path	   *subpath = (Path *) lfirst(lc);
		GatherMergePath *path;

		if (subpath->pathkeys == NIL)
			continue;

		rows = compute_gather_rows(subpath);
		path = create_gather_merge_path(root, rel, subpath, rel->reltarget,
										subpath->pathkeys, NULL, rowsp);
		add_path(rel, &path->path);
	}
}

/*
 * get_useful_pathkeys_for_relation
 *		Determine which orderings of a relation might be useful.
 *
 * Getting data in sorted order can be useful either because the requested
 * order matches the final output ordering for the overall query we're
 * planning, or because it enables an efficient merge join.  Here, we try
 * to figure out which pathkeys to consider.
 *
 * This allows us to do incremental sort on top of an index scan under a gather
 * merge node, i.e. parallelized.
 *
 * If the require_parallel_safe is true, we also require the expressions to
 * be parallel safe (which allows pushing the sort below Gather Merge).
 *
 * XXX At the moment this can only ever return a list with a single element,
 * because it looks at query_pathkeys only. So we might return the pathkeys
 * directly, but it seems plausible we'll want to consider other orderings
 * in the future. For example, we might want to consider pathkeys useful for
 * merge joins.
 */
/*
 * get_useful_pathkeys_for_relation - (中文)判断关系哪些排序键值得考虑
 *
 * 【作用】返回对指定关系"有用"的排序键列表,供 generate_useful_gather_paths()
 * 在 Gather Merge 之下考虑加增量排序/全排序。目前只考察根查询的
 * query_pathkeys:只要该关系能提前(在 gather 之前)按其中某前缀排序,这段
 * 前缀就是有用的。
 *
 * 【设计思想】数据有序可能因为两点:匹配最终输出排序(省去顶层全排序),或
 * 支持 merge join。这里的启发式是扫描 query_pathkeys 的前缀,逐键调用
 * relation_can_be_sorted_early() 确认关系的 reltarget 里有安全(且可并行安全)
 * 的等价类成员可提前计算;一旦某个键不满足就停止,但已满足的前缀仍返回
 * (因为可以做增量排序)。require_parallel_safe 为 true 时额外要求排序表达式
 * 并行安全,这样排序可被推入 Gather Merge 之下的并行部分。
 * 若能匹配整个 query_pathkeys 则直接返回原列表指针(便于后续用指针比较),
 * 否则拷贝前缀。
 *
 * 【参数】
 *   root                  —— PlannerInfo;
 *   rel                   —— 待生成 gather 路径的关系;
 *   require_parallel_safe —— true 时要求排序表达式并行安全。
 * 【返回值】有用排序键的列表(每个元素是一个 pathkey 列表);当前实现最多
 *           一个元素。
 */
static List *
get_useful_pathkeys_for_relation(PlannerInfo *root, RelOptInfo *rel,
								 bool require_parallel_safe)
{
	List	   *useful_pathkeys_list = NIL;

	/*
	 * Considering query_pathkeys is always worth it, because it might allow
	 * us to avoid a total sort when we have a partially presorted path
	 * available or to push the total sort into the parallel portion of the
	 * query.
	 */
	if (root->query_pathkeys)
	{
		ListCell   *lc;
		int			npathkeys = 0;	/* useful pathkeys */

		foreach(lc, root->query_pathkeys)
		{
			PathKey    *pathkey = (PathKey *) lfirst(lc);
			EquivalenceClass *pathkey_ec = pathkey->pk_eclass;

			/*
			 * We can only build a sort for pathkeys that contain a
			 * safe-to-compute-early EC member computable from the current
			 * relation's reltarget, so ignore the remainder of the list as
			 * soon as we find a pathkey without such a member.
			 *
			 * It's still worthwhile to return any prefix of the pathkeys list
			 * that meets this requirement, as we may be able to do an
			 * incremental sort.
			 *
			 * If requested, ensure the sort expression is parallel-safe too.
			 */
			if (!relation_can_be_sorted_early(root, rel, pathkey_ec,
											  require_parallel_safe))
				break;

			npathkeys++;
		}

		/*
		 * The whole query_pathkeys list matches, so append it directly, to
		 * allow comparing pathkeys easily by comparing list pointer. If we
		 * have to truncate the pathkeys, we gotta do a copy though.
		 */
		if (npathkeys == list_length(root->query_pathkeys))
			useful_pathkeys_list = lappend(useful_pathkeys_list,
										   root->query_pathkeys);
		else if (npathkeys > 0)
			useful_pathkeys_list = lappend(useful_pathkeys_list,
										   list_copy_head(root->query_pathkeys,
														  npathkeys));
	}

	return useful_pathkeys_list;
}

/*
 * generate_useful_gather_paths
 *		Generate parallel access paths for a relation by pushing a Gather or
 *		Gather Merge on top of a partial path.
 *
 * Unlike plain generate_gather_paths, this looks both at pathkeys of input
 * paths (aiming to preserve the ordering), but also considers ordering that
 * might be useful for nodes above the gather merge node, and tries to add
 * a sort (regular or incremental) to provide that.
 */
/*
 * generate_useful_gather_paths - (中文)生成带"有用排序"的 Gather / Gather Merge 路径
 *
 * 【作用】generate_gather_paths() 的增强版:除了为带排序键的 partial 路径直接
 * 生成保序 Gather Merge 外,还会根据 get_useful_pathkeys_for_relation() 找出的
 * "有用排序",为部分已排序的 partial 路径加增量排序、为最便宜的 partial 路径
 * 加全排序,再包上 Gather Merge,从而把顶层排序尽量下推进并行部分。被
 * set_rel_pathlist()/standard_join_search() 等在处理完一个关系的 partial 路径
 * 之后调用。
 *
 * 【设计思想】
 * - 先调用 generate_gather_paths() 处理"已完全有序"的 subpath(它对每个带
 *   pathkeys 的 subpath 都会建 Gather Merge),所以这里只需考虑"尚未达到所需
 *   顺序"的路径;
 * - 对每个有用排序:遍历 partial_pathlist,用 pathkeys_count_contained_in()
 *   计算已有排序前缀长度 presorted_keys;完全有序则跳过;为了控制规划时间,
 *   只对"最便宜的 partial 路径"做全排序,对"已有部分有序前缀"的路径做增量
 *   排序(增量排序被禁用时则只排序最便宜的路径);
 * - 排序后 subpath 的排序键成为 Gather Merge 的排序键,最后行数用
 *   compute_gather_rows() 折算;
 * - override_rows 语义同 generate_gather_paths()。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   rel           —— 拥有 partial_pathlist 的关系;
 *   override_rows —— true 时用 compute_gather_rows 覆盖 rel->rows。
 * 【返回值】无。
 */
void
generate_useful_gather_paths(PlannerInfo *root, RelOptInfo *rel, bool override_rows)
{
	ListCell   *lc;
	double		rows;
	double	   *rowsp = NULL;
	List	   *useful_pathkeys_list = NIL;
	Path	   *cheapest_partial_path = NULL;

	/* If there are no partial paths, there's nothing to do here. */
	if (rel->partial_pathlist == NIL)
		return;

	/* Should we override the rel's rowcount estimate? */
	if (override_rows)
		rowsp = &rows;

	/* generate the regular gather (merge) paths */
	generate_gather_paths(root, rel, override_rows);

	/* consider incremental sort for interesting orderings */
	useful_pathkeys_list = get_useful_pathkeys_for_relation(root, rel, true);

	/* used for explicit (full) sort paths */
	cheapest_partial_path = linitial(rel->partial_pathlist);

	/*
	 * Consider sorted paths for each interesting ordering. We generate both
	 * incremental and full sort.
	 */
	foreach(lc, useful_pathkeys_list)
	{
		List	   *useful_pathkeys = lfirst(lc);
		ListCell   *lc2;
		bool		is_sorted;
		int			presorted_keys;

		foreach(lc2, rel->partial_pathlist)
		{
			Path	   *subpath = (Path *) lfirst(lc2);
			GatherMergePath *path;

			is_sorted = pathkeys_count_contained_in(useful_pathkeys,
													subpath->pathkeys,
													&presorted_keys);

			/*
			 * We don't need to consider the case where a subpath is already
			 * fully sorted because generate_gather_paths already creates a
			 * gather merge path for every subpath that has pathkeys present.
			 *
			 * But since the subpath is already sorted, we know we don't need
			 * to consider adding a sort (full or incremental) on top of it,
			 * so we can continue here.
			 */
			if (is_sorted)
				continue;

			/*
			 * Try at least sorting the cheapest path and also try
			 * incrementally sorting any path which is partially sorted
			 * already (no need to deal with paths which have presorted keys
			 * when incremental sort is disabled unless it's the cheapest
			 * input path).
			 */
			if (subpath != cheapest_partial_path &&
				(presorted_keys == 0 || !enable_incremental_sort))
				continue;

			/*
			 * Consider regular sort for any path that's not presorted or if
			 * incremental sort is disabled.  We've no need to consider both
			 * sort and incremental sort on the same path.  We assume that
			 * incremental sort is always faster when there are presorted
			 * keys.
			 *
			 * This is not redundant with the gather paths created in
			 * generate_gather_paths, because that doesn't generate ordered
			 * output. Here we add an explicit sort to match the useful
			 * ordering.
			 */
			if (presorted_keys == 0 || !enable_incremental_sort)
			{
				subpath = (Path *) create_sort_path(root,
													rel,
													subpath,
													useful_pathkeys,
													-1.0);
			}
			else
				subpath = (Path *) create_incremental_sort_path(root,
																rel,
																subpath,
																useful_pathkeys,
																presorted_keys,
																-1);
			rows = compute_gather_rows(subpath);
			path = create_gather_merge_path(root, rel,
											subpath,
											rel->reltarget,
											subpath->pathkeys,
											NULL,
											rowsp);

			add_path(rel, &path->path);
		}
	}
}

/*
 * generate_grouped_paths
 *		Generate paths for a grouped relation by adding sorted and hashed
 *		partial aggregation paths on top of paths of the ungrouped relation.
 *
 * The information needed is provided by the RelAggInfo structure stored in
 * "grouped_rel".
 */
/*
 * generate_grouped_paths - (中文)为 grouped rel 生成排序/哈希的部分聚合路径
 *
 * 【作用】在"未分组关系"的路径之上,为对应的 grouped rel 生成各种"部分聚合"
 * 路径:AGG_SORTED(排序分组)与 AGG_HASHED(哈希分组)、非并行与并行
 * (partial)四种组合。被 set_grouped_rel_pathlist()(基础关系)与
 * standard_join_search() / generate_partitionwise_join_paths()(连接关系)调用。
 * 这些部分聚合路径随后由上层 FinalizeAggregate 路径再聚合成完整聚合。
 *
 * 【设计思想】
 * - 急切聚合的适用位置与收益已由 RelAggInfo 记录(agg_info->apply_agg_at
 *   表明聚合应推到的连接层,agg_useful 表明是否值得),不符合则直接返回;
 *   rel 为空则标记 grouped_rel 为 dummy;
 * - AGGSPLIT_INITIAL_SERIAL 表示"先做部分聚合,序列化中间结果"的拆分方式,
 *   聚合开销由 get_agg_clause_costs() 统计;
 * - can_sort 由 grouping_is_sortable() 判定,并构造 group_pathkeys(分组子句的
 *   排序键);can_hash 由 grouping_is_hashable() 判定,要求有分组子句且可哈希
 *   分组(有序聚合时禁止哈希——断言 numOrderedAggs == 0);
 * - 排序路径生成:遍历 rel 的完整/partial 路径,优先用已部分有序的路径(增量
 *   排序),否则对最便宜路径做全排序;非最便宜的参数化路径被忽略以省规划时间;
 * - 哈希路径生成:直接基于 cheapest_total / cheapest_partial 路径;
 * - 所有路径之上都先加 Projection(把未分组关系的输出投影成聚合所需输入
 *   agg_info->agg_input),因为未分组关系不懂急切聚合;
 * - 分组数估计用 estimate_num_groups()(按完整路径行数与 partial 路径行数
 *   分别估计 dNumGroups / dNumPartialGroups),用于成本模型;
 * - HAVING 条件不能下放(qual = NIL),因为最终聚合值未求出前无法评估。
 *
 * 【参数】
 *   root        —— PlannerInfo;
 *   grouped_rel —— 目标 grouped rel(IS_GROUPED_REL),其 agg_info 是 RelAggInfo;
 *   rel         —— 提供输入路径的未分组关系(与 grouped_rel 同 relids)。
 * 【返回值】无。
 */
void
generate_grouped_paths(PlannerInfo *root, RelOptInfo *grouped_rel,
					   RelOptInfo *rel)
{
	RelAggInfo *agg_info = grouped_rel->agg_info;
	AggClauseCosts agg_costs;
	bool		can_hash;
	bool		can_sort;
	Path	   *cheapest_total_path = NULL;
	Path	   *cheapest_partial_path = NULL;
	double		dNumGroups = 0;
	double		dNumPartialGroups = 0;
	List	   *group_pathkeys = NIL;

	if (IS_DUMMY_REL(rel))
	{
		mark_dummy_rel(grouped_rel);
		return;
	}

	/*
	 * We push partial aggregation only to the lowest possible level in the
	 * join tree that is deemed useful.
	 */
	if (!bms_equal(agg_info->apply_agg_at, rel->relids) ||
		!agg_info->agg_useful)
		return;

	MemSet(&agg_costs, 0, sizeof(AggClauseCosts));
	get_agg_clause_costs(root, AGGSPLIT_INITIAL_SERIAL, &agg_costs);

	/*
	 * Determine whether it's possible to perform sort-based implementations
	 * of grouping, and generate the pathkeys that represent the grouping
	 * requirements in that case.
	 */
	can_sort = grouping_is_sortable(agg_info->group_clauses);
	if (can_sort)
	{
		RelOptInfo *top_grouped_rel;
		List	   *top_group_tlist;

		top_grouped_rel = IS_OTHER_REL(rel) ?
			rel->top_parent->grouped_rel : grouped_rel;
		top_group_tlist =
			make_tlist_from_pathtarget(top_grouped_rel->agg_info->target);

		group_pathkeys =
			make_pathkeys_for_sortclauses(root, agg_info->group_clauses,
										  top_group_tlist);
	}

	/*
	 * Determine whether we should consider hash-based implementations of
	 * grouping.
	 */
	Assert(root->numOrderedAggs == 0);
	can_hash = (agg_info->group_clauses != NIL &&
				grouping_is_hashable(agg_info->group_clauses));

	/*
	 * Consider whether we should generate partially aggregated non-partial
	 * paths.  We can only do this if we have a non-partial path.
	 */
	if (rel->pathlist != NIL)
	{
		cheapest_total_path = rel->cheapest_total_path;
		Assert(cheapest_total_path != NULL);
	}

	/*
	 * If parallelism is possible for grouped_rel, then we should consider
	 * generating partially-grouped partial paths.  However, if the ungrouped
	 * rel has no partial paths, then we can't.
	 */
	if (grouped_rel->consider_parallel && rel->partial_pathlist != NIL)
	{
		cheapest_partial_path = linitial(rel->partial_pathlist);
		Assert(cheapest_partial_path != NULL);
	}

	/* Estimate number of partial groups. */
	if (cheapest_total_path != NULL)
		dNumGroups = estimate_num_groups(root,
										 agg_info->group_exprs,
										 cheapest_total_path->rows,
										 NULL, NULL);
	if (cheapest_partial_path != NULL)
		dNumPartialGroups = estimate_num_groups(root,
												agg_info->group_exprs,
												cheapest_partial_path->rows,
												NULL, NULL);

	if (can_sort && cheapest_total_path != NULL)
	{
		ListCell   *lc;

		/*
		 * Use any available suitably-sorted path as input, and also consider
		 * sorting the cheapest-total path and incremental sort on any paths
		 * with presorted keys.
		 *
		 * To save planning time, we ignore parameterized input paths unless
		 * they are the cheapest-total path.
		 */
		foreach(lc, rel->pathlist)
		{
			Path	   *input_path = (Path *) lfirst(lc);
			Path	   *path;
			bool		is_sorted;
			int			presorted_keys;

			/*
			 * Ignore parameterized paths that are not the cheapest-total
			 * path.
			 */
			if (input_path->param_info &&
				input_path != cheapest_total_path)
				continue;

			is_sorted = pathkeys_count_contained_in(group_pathkeys,
													input_path->pathkeys,
													&presorted_keys);

			/*
			 * Ignore paths that are not suitably or partially sorted, unless
			 * they are the cheapest total path (no need to deal with paths
			 * which have presorted keys when incremental sort is disabled).
			 */
			if (!is_sorted && input_path != cheapest_total_path &&
				(presorted_keys == 0 || !enable_incremental_sort))
				continue;

			/*
			 * Since the path originates from a non-grouped relation that is
			 * not aware of eager aggregation, we must ensure that it provides
			 * the correct input for partial aggregation.
			 */
			path = (Path *) create_projection_path(root,
												   grouped_rel,
												   input_path,
												   agg_info->agg_input);

			if (!is_sorted)
			{
				/*
				 * We've no need to consider both a sort and incremental sort.
				 * We'll just do a sort if there are no presorted keys and an
				 * incremental sort when there are presorted keys.
				 */
				if (presorted_keys == 0 || !enable_incremental_sort)
					path = (Path *) create_sort_path(root,
													 grouped_rel,
													 path,
													 group_pathkeys,
													 -1.0);
				else
					path = (Path *) create_incremental_sort_path(root,
																 grouped_rel,
																 path,
																 group_pathkeys,
																 presorted_keys,
																 -1.0);
			}

			/*
			 * qual is NIL because the HAVING clause cannot be evaluated until
			 * the final value of the aggregate is known.
			 */
			path = (Path *) create_agg_path(root,
											grouped_rel,
											path,
											agg_info->target,
											AGG_SORTED,
											AGGSPLIT_INITIAL_SERIAL,
											agg_info->group_clauses,
											NIL,
											&agg_costs,
											dNumGroups);

			add_path(grouped_rel, path);
		}
	}

	if (can_sort && cheapest_partial_path != NULL)
	{
		ListCell   *lc;

		/* Similar to above logic, but for partial paths. */
		foreach(lc, rel->partial_pathlist)
		{
			Path	   *input_path = (Path *) lfirst(lc);
			Path	   *path;
			bool		is_sorted;
			int			presorted_keys;

			is_sorted = pathkeys_count_contained_in(group_pathkeys,
													input_path->pathkeys,
													&presorted_keys);

			/*
			 * Ignore paths that are not suitably or partially sorted, unless
			 * they are the cheapest partial path (no need to deal with paths
			 * which have presorted keys when incremental sort is disabled).
			 */
			if (!is_sorted && input_path != cheapest_partial_path &&
				(presorted_keys == 0 || !enable_incremental_sort))
				continue;

			/*
			 * Since the path originates from a non-grouped relation that is
			 * not aware of eager aggregation, we must ensure that it provides
			 * the correct input for partial aggregation.
			 */
			path = (Path *) create_projection_path(root,
												   grouped_rel,
												   input_path,
												   agg_info->agg_input);

			if (!is_sorted)
			{
				/*
				 * We've no need to consider both a sort and incremental sort.
				 * We'll just do a sort if there are no presorted keys and an
				 * incremental sort when there are presorted keys.
				 */
				if (presorted_keys == 0 || !enable_incremental_sort)
					path = (Path *) create_sort_path(root,
													 grouped_rel,
													 path,
													 group_pathkeys,
													 -1.0);
				else
					path = (Path *) create_incremental_sort_path(root,
																 grouped_rel,
																 path,
																 group_pathkeys,
																 presorted_keys,
																 -1.0);
			}

			/*
			 * qual is NIL because the HAVING clause cannot be evaluated until
			 * the final value of the aggregate is known.
			 */
			path = (Path *) create_agg_path(root,
											grouped_rel,
											path,
											agg_info->target,
											AGG_SORTED,
											AGGSPLIT_INITIAL_SERIAL,
											agg_info->group_clauses,
											NIL,
											&agg_costs,
											dNumPartialGroups);

			add_partial_path(grouped_rel, path);
		}
	}

	/*
	 * Add a partially-grouped HashAgg Path where possible
	 */
	if (can_hash && cheapest_total_path != NULL)
	{
		Path	   *path;

		/*
		 * Since the path originates from a non-grouped relation that is not
		 * aware of eager aggregation, we must ensure that it provides the
		 * correct input for partial aggregation.
		 */
		path = (Path *) create_projection_path(root,
											   grouped_rel,
											   cheapest_total_path,
											   agg_info->agg_input);

		/*
		 * qual is NIL because the HAVING clause cannot be evaluated until the
		 * final value of the aggregate is known.
		 */
		path = (Path *) create_agg_path(root,
										grouped_rel,
										path,
										agg_info->target,
										AGG_HASHED,
										AGGSPLIT_INITIAL_SERIAL,
										agg_info->group_clauses,
										NIL,
										&agg_costs,
										dNumGroups);

		add_path(grouped_rel, path);
	}

	/*
	 * Now add a partially-grouped HashAgg partial Path where possible
	 */
	if (can_hash && cheapest_partial_path != NULL)
	{
		Path	   *path;

		/*
		 * Since the path originates from a non-grouped relation that is not
		 * aware of eager aggregation, we must ensure that it provides the
		 * correct input for partial aggregation.
		 */
		path = (Path *) create_projection_path(root,
											   grouped_rel,
											   cheapest_partial_path,
											   agg_info->agg_input);

		/*
		 * qual is NIL because the HAVING clause cannot be evaluated until the
		 * final value of the aggregate is known.
		 */
		path = (Path *) create_agg_path(root,
										grouped_rel,
										path,
										agg_info->target,
										AGG_HASHED,
										AGGSPLIT_INITIAL_SERIAL,
										agg_info->group_clauses,
										NIL,
										&agg_costs,
										dNumPartialGroups);

		add_partial_path(grouped_rel, path);
	}
}

/*
 * make_rel_from_joinlist
 *	  Build access paths using a "joinlist" to guide the join path search.
 *
 * See comments for deconstruct_jointree() for definition of the joinlist
 * data structure.
 */
/*
 * make_rel_from_joinlist - (中文)按 joinlist 引导连接路径搜索
 *
 * 【作用】根据 deconstruct_jointree() 生成的 joinlist(连接树的一种扁平化
 * 嵌套列表表示)构建最终的连接关系:对列表里每个节点递归——RangeTblRef 直接
 * 取对应基础关系,List 则递归本函数先求出该子问题的连接关系;然后按层数选择
 * 搜索策略:单节点直接返回;多节点则交给插件钩子(join_search_hook)、GEQO
 * (enable_geqo 且层数达标)或 standard_join_search()。由 make_one_rel() 调用。
 *
 * 【设计思想】joinlist 的深度就是动态规划需要的"层数"(levels_needed,即独立
 * 连接树项的数量)。把 initial_rels 暂存到 root->initial_rels 是因为
 * has_legal_joinclause() 需要读取它。这样设计让 join 顺序搜索算法可以替换:
 * 插件/GEQO 与标准算法共享同一份输入与输出契约。
 *
 * 【参数】
 *   root     —— PlannerInfo;
 *   joinlist —— 嵌套列表:RangeTblRef 或子 List。
 * 【返回值】代表全部基础关系连接结果的 RelOptInfo(level 为 0 时返回 NULL)。
 */
static RelOptInfo *
make_rel_from_joinlist(PlannerInfo *root, List *joinlist)
{
	int			levels_needed;
	List	   *initial_rels;
	ListCell   *jl;

	/*
	 * Count the number of child joinlist nodes.  This is the depth of the
	 * dynamic-programming algorithm we must employ to consider all ways of
	 * joining the child nodes.
	 */
	levels_needed = list_length(joinlist);

	if (levels_needed <= 0)
		return NULL;			/* nothing to do? */

	/*
	 * Construct a list of rels corresponding to the child joinlist nodes.
	 * This may contain both base rels and rels constructed according to
	 * sub-joinlists.
	 */
	initial_rels = NIL;
	foreach(jl, joinlist)
	{
		Node	   *jlnode = (Node *) lfirst(jl);
		RelOptInfo *thisrel;

		if (IsA(jlnode, RangeTblRef))
		{
			int			varno = ((RangeTblRef *) jlnode)->rtindex;

			thisrel = find_base_rel(root, varno);
		}
		else if (IsA(jlnode, List))
		{
			/* Recurse to handle subproblem */
			thisrel = make_rel_from_joinlist(root, (List *) jlnode);
		}
		else
		{
			elog(ERROR, "unrecognized joinlist node type: %d",
				 (int) nodeTag(jlnode));
			thisrel = NULL;		/* keep compiler quiet */
		}

		initial_rels = lappend(initial_rels, thisrel);
	}

	if (levels_needed == 1)
	{
		/*
		 * Single joinlist node, so we're done.
		 */
		return (RelOptInfo *) linitial(initial_rels);
	}
	else
	{
		/*
		 * Consider the different orders in which we could join the rels,
		 * using a plugin, GEQO, or the regular join search code.
		 *
		 * We put the initial_rels list into a PlannerInfo field because
		 * has_legal_joinclause() needs to look at it (ugly :-().
		 */
		root->initial_rels = initial_rels;

		if (join_search_hook)
			return (*join_search_hook) (root, levels_needed, initial_rels);
		else if (enable_geqo && levels_needed >= geqo_threshold)
			return geqo(root, levels_needed, initial_rels);
		else
			return standard_join_search(root, levels_needed, initial_rels);
	}
}

/*
 * standard_join_search
 *	  Find possible joinpaths for a query by successively finding ways
 *	  to join component relations into join relations.
 *
 * 'levels_needed' is the number of iterations needed, ie, the number of
 *		independent jointree items in the query.  This is > 1.
 *
 * 'initial_rels' is a list of RelOptInfo nodes for each independent
 *		jointree item.  These are the components to be joined together.
 *		Note that levels_needed == list_length(initial_rels).
 *
 * Returns the final level of join relations, i.e., the relation that is
 * the result of joining all the original relations together.
 * At least one implementation path must be provided for this relation and
 * all required sub-relations.
 *
 * To support loadable plugins that modify planner behavior by changing the
 * join searching algorithm, we provide a hook variable that lets a plugin
 * replace or supplement this function.  Any such hook must return the same
 * final join relation as the standard code would, but it might have a
 * different set of implementation paths attached, and only the sub-joinrels
 * needed for these paths need have been instantiated.
 *
 * Note to plugin authors: the functions invoked during standard_join_search()
 * modify root->join_rel_list and root->join_rel_hash.  If you want to do more
 * than one join-order search, you'll probably need to save and restore the
 * original states of those data structures.  See geqo_eval() for an example.
 */
/*
 * standard_join_search - (中文)标准动态规划连接顺序搜索
 *
 * 【作用】用自底向上的动态规划找出全部连接顺序:第 lev 层生成所有"连接
 * lev 个 joinlist 项"的连接关系(joinrel),每个 joinrel 由任意一对低层
 * (合计 lev 项)关系通过 join_search_one_level() 构造。逐层推进直到顶层,
 * 返回最终的全体连接关系。由 make_rel_from_joinlist() 在未启用 GEQO 时调用;
 * 也可由插件替换。
 *
 * 【设计思想】
 * - root->join_rel_level[lev] 存放第 lev 层的全部 joinrel 列表;
 *   join_rel_level[1] 就是 initial_rels。每层生成后立刻做三件事:
 *   generate_partitionwise_join_paths()(分区连接关系先各自处理子分区连接)、
 *   generate_useful_gather_paths()(非顶层关系汇聚 partial 路径)、
 *   set_cheapest()(挑最便宜路径);有 grouped rel 的连接关系还要生成部分聚合
 *   路径。必须等 join_search_one_level 对该层全部 joinrel 处理完再做,因为
 *   一个 joinrel 的路径可能在过程中多次追加;
 * - 最顶层(relids == all_query_rels)的 Gather 推迟到拿到最终 targetlist
 *   之后(见 grouping_planner 的 apply_scanjoin_target_to_paths),所以这里
 *   用 is_top_rel 跳过;
 * - 结束时要求第 levels_needed 层恰好一个关系;join_rel_level 被置回 NULL
 *   以释放临时数组(元素本身属于 join_rel_list,仍保留)。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   levels_needed —— 独立 jointree 项个数(> 1),即动态规划层数;
 *   initial_rels  —— 各独立 jointree 项的 RelOptInfo 列表(长度 == levels_needed)。
 * 【返回值】最终层(全部关系连接结果)的 RelOptInfo。
 */
RelOptInfo *
standard_join_search(PlannerInfo *root, int levels_needed, List *initial_rels)
{
	int			lev;
	RelOptInfo *rel;

	/*
	 * This function cannot be invoked recursively within any one planning
	 * problem, so join_rel_level[] can't be in use already.
	 */
	Assert(root->join_rel_level == NULL);

	/*
	 * We employ a simple "dynamic programming" algorithm: we first find all
	 * ways to build joins of two jointree items, then all ways to build joins
	 * of three items (from two-item joins and single items), then four-item
	 * joins, and so on until we have considered all ways to join all the
	 * items into one rel.
	 *
	 * root->join_rel_level[j] is a list of all the j-item rels.  Initially we
	 * set root->join_rel_level[1] to represent all the single-jointree-item
	 * relations.
	 */
	root->join_rel_level = (List **) palloc0((levels_needed + 1) * sizeof(List *));

	root->join_rel_level[1] = initial_rels;

	for (lev = 2; lev <= levels_needed; lev++)
	{
		ListCell   *lc;

		/*
		 * Determine all possible pairs of relations to be joined at this
		 * level, and build paths for making each one from every available
		 * pair of lower-level relations.
		 */
		join_search_one_level(root, lev);

		/*
		 * Run generate_partitionwise_join_paths() and
		 * generate_useful_gather_paths() for each just-processed joinrel.  We
		 * could not do this earlier because both regular and partial paths
		 * can get added to a particular joinrel at multiple times within
		 * join_search_one_level.
		 *
		 * After that, we're done creating paths for the joinrel, so run
		 * set_cheapest().
		 *
		 * In addition, we also run generate_grouped_paths() for the grouped
		 * relation of each just-processed joinrel, and run set_cheapest() for
		 * the grouped relation afterwards.
		 */
		foreach(lc, root->join_rel_level[lev])
		{
			bool		is_top_rel;

			rel = (RelOptInfo *) lfirst(lc);

			is_top_rel = bms_equal(rel->relids, root->all_query_rels);

			/* Create paths for partitionwise joins. */
			generate_partitionwise_join_paths(root, rel);

			/*
			 * Except for the topmost scan/join rel, consider gathering
			 * partial paths.  We'll do the same for the topmost scan/join rel
			 * once we know the final targetlist (see grouping_planner's and
			 * its call to apply_scanjoin_target_to_paths).
			 */
			if (!is_top_rel)
				generate_useful_gather_paths(root, rel, false);

			/* Find and save the cheapest paths for this rel */
			set_cheapest(rel);

			/*
			 * Except for the topmost scan/join rel, consider generating
			 * partial aggregation paths for the grouped relation on top of
			 * the paths of this rel.  After that, we're done creating paths
			 * for the grouped relation, so run set_cheapest().
			 */
			if (rel->grouped_rel != NULL && !is_top_rel)
			{
				RelOptInfo *grouped_rel = rel->grouped_rel;

				Assert(IS_GROUPED_REL(grouped_rel));

				generate_grouped_paths(root, grouped_rel, rel);
				set_cheapest(grouped_rel);
			}

#ifdef OPTIMIZER_DEBUG
			pprint(rel);
#endif
		}
	}

	/*
	 * We should have a single rel at the final level.
	 */
	if (root->join_rel_level[levels_needed] == NIL)
		elog(ERROR, "failed to build any %d-way joins", levels_needed);
	Assert(list_length(root->join_rel_level[levels_needed]) == 1);

	rel = (RelOptInfo *) linitial(root->join_rel_level[levels_needed]);

	root->join_rel_level = NULL;

	return rel;
}

/*****************************************************************************
 *			PUSHING QUALS DOWN INTO SUBQUERIES
 *****************************************************************************/

/*
 * subquery_is_pushdown_safe - is a subquery safe for pushing down quals?
 *
 * subquery is the particular component query being checked.  topquery
 * is the top component of a set-operations tree (the same Query if no
 * set-op is involved).
 *
 * Conditions checked here:
 *
 * 1. If the subquery has a LIMIT clause, we must not push down any quals,
 * since that could change the set of rows returned.
 *
 * 2. If the subquery contains EXCEPT or EXCEPT ALL set ops we cannot push
 * quals into it, because that could change the results.
 *
 * 3. If the subquery uses DISTINCT, we cannot push volatile quals into it.
 * This is because upper-level quals should semantically be evaluated only
 * once per distinct row, not once per original row, and if the qual is
 * volatile then extra evaluations could change the results.  (This issue
 * does not apply to other forms of aggregation such as GROUP BY, because
 * when those are present we push into HAVING not WHERE, so that the quals
 * are still applied after aggregation.)
 *
 * 4. If the subquery contains window functions, we cannot push volatile quals
 * into it.  The issue here is a bit different from DISTINCT: a volatile qual
 * might succeed for some rows of a window partition and fail for others,
 * thereby changing the partition contents and thus the window functions'
 * results for rows that remain.
 *
 * 5. If the subquery contains any set-returning functions in its targetlist,
 * we cannot push volatile quals into it.  That would push them below the SRFs
 * and thereby change the number of times they are evaluated.  Also, a
 * volatile qual could succeed for some SRF output rows and fail for others,
 * a behavior that cannot occur if it's evaluated before SRF expansion.
 *
 * 6. If the subquery has nonempty grouping sets, we cannot push down any
 * quals.  The concern here is that a qual referencing a "constant" grouping
 * column could get constant-folded, which would be improper because the value
 * is potentially nullable by grouping-set expansion.  This restriction could
 * be removed if we had a parsetree representation that shows that such
 * grouping columns are not really constant.  (There are other ideas that
 * could be used to relax this restriction, but that's the approach most
 * likely to get taken in the future.  Note that there's not much to be gained
 * so long as subquery_planner can't move HAVING clauses to WHERE within such
 * a subquery.)
 *
 * In addition, we make several checks on the subquery's output columns to see
 * if it is safe to reference them in pushed-down quals.  If output column k
 * is found to be unsafe to reference, we set the reason for that inside
 * safetyInfo->unsafeFlags[k], but we don't reject the subquery overall since
 * column k might not be referenced by some/all quals.  The unsafeFlags[]
 * array will be consulted later by qual_is_pushdown_safe().  It's better to
 * do it this way than to make the checks directly in qual_is_pushdown_safe(),
 * because when the subquery involves set operations we have to check the
 * output expressions in each arm of the set op.
 *
 * Note: pushing quals into a DISTINCT subquery is theoretically dubious:
 * we're effectively assuming that the quals cannot distinguish values that
 * the DISTINCT's equality operator sees as equal, yet there are many
 * counterexamples to that assumption.  However use of such a qual with a
 * DISTINCT subquery would be unsafe anyway, since there's no guarantee which
 * "equal" value will be chosen as the output value by the DISTINCT operation.
 * So we don't worry too much about that.  Another objection is that if the
 * qual is expensive to evaluate, running it for each original row might cost
 * more than we save by eliminating rows before the DISTINCT step.  But it
 * would be very hard to estimate that at this stage, and in practice pushdown
 * seldom seems to make things worse, so we ignore that problem too.
 *
 * Note: likewise, pushing quals into a subquery with window functions is a
 * bit dubious: the quals might remove some rows of a window partition while
 * leaving others, causing changes in the window functions' results for the
 * surviving rows.  We insist that such a qual reference only partitioning
 * columns, but again that only protects us if the qual does not distinguish
 * values that the partitioning equality operator sees as equal.  The risks
 * here are perhaps larger than for DISTINCT, since no de-duplication of rows
 * occurs and thus there is no theoretical problem with such a qual.  But
 * we'll do this anyway because the potential performance benefits are very
 * large, and we've seen no field complaints about the longstanding comparable
 * behavior with DISTINCT.
 */
/*
 * subquery_is_pushdown_safe - (中文)判定子查询整体是否允许下推条件
 *
 * 【作用】检查一个子查询(或 setop 树的某个组件查询)是否具备把上层限制条件
 * 推入其内部的安全性。同时扫描子查询的输出列,把"哪些列不适合被下推条件
 * 引用"的原因逐列记入 safetyInfo->unsafeFlags[]。由 set_subquery_pathlist()
 * 调用。
 *
 * 【设计思想】整体层面拒绝的情况:
 * 1) 子查询含 LIMIT(改变返回行集);6) 含非空 grouping sets(常量折叠隐患);
 * 2) EXCEPT / EXCEPT ALL(setop 递归检查);3) DISTINCT 时拒绝易变(volatile)
 * 条件;4) 窗口函数时拒绝易变条件;5) targetlist 含 SRF 时拒绝易变条件。
 * 列层面:叶子查询(无 setop)调用 check_output_expressions() 逐列标记不安全
 * 原因(集合函数、易变函数、DISTINCT ON 之外的列、未全部分区列等);
 * setop 组件则调用 compare_tlist_datatypes() 标记类型不一致的列。
 * 关键点:列的不安全只"记录"不"整体拒绝",因为具体的 qual 可能根本不用这些
 * 列——真正的逐条件判断在 qual_is_pushdown_safe() 里做。
 *
 * 【参数】
 *   subquery   —— 当前检查的组件查询;
 *   topquery   —— setop 树的最顶层查询(无 setop 时即 subquery 本身);
 *   safetyInfo —— 共享的推入安全性工作区,unsafeFlags[] 按列号记录原因。
 * 【返回值】true 表示可以继续考虑下推(还需逐条 qual 检查);false 表示整体
 *           禁止下推。
 */
static bool
subquery_is_pushdown_safe(Query *subquery, Query *topquery,
						  pushdown_safety_info *safetyInfo)
{
	SetOperationStmt *topop;

	/* Check point 1 */
	if (subquery->limitOffset != NULL || subquery->limitCount != NULL)
		return false;

	/* Check point 6 */
	if (subquery->groupClause && subquery->groupingSets)
		return false;

	/* Check points 3, 4, and 5 */
	if (subquery->distinctClause ||
		subquery->hasWindowFuncs ||
		subquery->hasTargetSRFs)
		safetyInfo->unsafeVolatile = true;

	/*
	 * If we're at a leaf query, check for unsafe expressions in its target
	 * list, and mark any reasons why they're unsafe in unsafeFlags[].
	 * (Non-leaf nodes in setop trees have only simple Vars in their tlists,
	 * so no need to check them.)
	 */
	if (subquery->setOperations == NULL)
		check_output_expressions(subquery, safetyInfo);

	/* Are we at top level, or looking at a setop component? */
	if (subquery == topquery)
	{
		/* Top level, so check any component queries */
		if (subquery->setOperations != NULL)
			if (!recurse_pushdown_safe(subquery->setOperations, topquery,
									   safetyInfo))
				return false;
	}
	else
	{
		/* Setop component must not have more components (too weird) */
		if (subquery->setOperations != NULL)
			return false;
		/* Check whether setop component output types match top level */
		topop = castNode(SetOperationStmt, topquery->setOperations);
		Assert(topop);
		compare_tlist_datatypes(subquery->targetList,
								topop->colTypes,
								safetyInfo);
	}
	return true;
}

/*
 * Helper routine to recurse through setOperations tree
 */
/*
 * recurse_pushdown_safe - (中文)递归检查 setop 树的下推安全性
 *
 * 【作用】沿 SetOperationStmt 树递归,逐个组件查询调用
 * subquery_is_pushdown_safe() 做安全检查;遇到 EXCEPT/EXCEPT ALL 立即返回
 * false(下推会改变结果语义)。被 subquery_is_pushdown_safe() 在顶层调用。
 *
 * 【设计思想】UNION / INTERSECT 对组内行做去重或合并,只要 qual 不区分
 * "分组认为相等"的行,下推就安全;EXCEPT 的下推语义难以保证,故直接拒绝。
 *
 * 【参数】
 *   setOp      —— setop 树的当前节点(RangeTblRef 或 SetOperationStmt);
 *   topquery   —— 顶层查询(供 rt_fetch 定位组件 RTE);
 *   safetyInfo —— 共享的安全性工作区。
 * 【返回值】true 表示该子树可安全下推;false 表示发现 EXCEPT 或不安全。
 */
static bool
recurse_pushdown_safe(Node *setOp, Query *topquery,
					  pushdown_safety_info *safetyInfo)
{
	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		RangeTblEntry *rte = rt_fetch(rtr->rtindex, topquery->rtable);
		Query	   *subquery = rte->subquery;

		Assert(subquery != NULL);
		return subquery_is_pushdown_safe(subquery, topquery, safetyInfo);
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		/* EXCEPT is no good (point 2 for subquery_is_pushdown_safe) */
		if (op->op == SETOP_EXCEPT)
			return false;
		/* Else recurse */
		if (!recurse_pushdown_safe(op->larg, topquery, safetyInfo))
			return false;
		if (!recurse_pushdown_safe(op->rarg, topquery, safetyInfo))
			return false;
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
	}
	return true;
}

/*
 * check_output_expressions - check subquery's output expressions for safety
 *
 * There are several cases in which it's unsafe to push down an upper-level
 * qual if it references a particular output column of a subquery.  We check
 * each output column of the subquery and set flags in unsafeFlags[k] when we
 * see that column is unsafe for a pushed-down qual to reference.  The
 * conditions checked here are:
 *
 * 1. We must not push down any quals that refer to subselect outputs that
 * return sets, else we'd introduce functions-returning-sets into the
 * subquery's WHERE/HAVING quals.
 *
 * 2. We must not push down any quals that refer to subselect outputs that
 * contain volatile functions, for fear of introducing strange results due
 * to multiple evaluation of a volatile function.
 *
 * 3. If the subquery uses DISTINCT ON, we must not push down any quals that
 * refer to non-DISTINCT output columns, because that could change the set
 * of rows returned.  (This condition is vacuous for DISTINCT, because then
 * there are no non-DISTINCT output columns, so we needn't check.  Note that
 * subquery_is_pushdown_safe already reported that we can't use volatile
 * quals if there's DISTINCT or DISTINCT ON.)
 *
 * 4. If the subquery has any window functions, we must not push down quals
 * that reference any output columns that are not listed in all the subquery's
 * window PARTITION BY clauses.  We can push down quals that use only
 * partitioning columns because they should succeed or fail identically for
 * every row of any one window partition, and totally excluding some
 * partitions will not change a window function's results for remaining
 * partitions.  (Again, this also requires nonvolatile quals, but
 * subquery_is_pushdown_safe handles that.).  Subquery columns marked as
 * unsafe for this reason can still have WindowClause run conditions pushed
 * down.
 */
/*
 * check_output_expressions - (中文)检查子查询输出表达式,逐列标记下推不安全的列
 *
 * 【作用】对叶子子查询的每个非 resjunk 输出列,检查四种不安全情形并在
 * safetyInfo->unsafeFlags[resno] 里置对应位:含集合返回函数(SRF)、含易变
 * (volatile)函数、DISTINCT ON 中未出现的列、未出现在所有窗口 PARTITION BY
 * 中的列。被 subquery_is_pushdown_safe() 对无 setop 的查询调用。
 *
 * 【设计思想】
 * - SRF 列:下推会把"函数返回集合"塞进 WHERE,改变求值次数/结果;
 * - 易变函数列:多重求值会产生不一致结果;
 * - DISTINCT ON 未选中的列:被下推 qual 过滤会改变返回行的集合(普通 DISTINCT
 *   时所有列都出现在 distinctClause,该检查自然为空);
 * - 窗口列:只有全部出现在每个窗口的 PARTITION BY 里,qual 才会对同一分区内
 *   所有行一致地通过/失败,不改变窗口函数结果;这种列仍可作为 WindowClause
 *   的 runCondition 被下推,故只是"不能当普通 qual 引用";
 * - 对 GROUP RTE 的查询,先把 targetlist 展开(group 变量展开成底层分组表达式)
 *   再检查,因为分组表达式本身可能易变/返回集合;join alias 变量无需展开。
 *
 * 【参数】
 *   subquery   —— 叶子子查询;
 *   safetyInfo —— 安全性工作区(unsafeFlags 已按列数分配)。
 * 【返回值】无。
 */
static void
check_output_expressions(Query *subquery, pushdown_safety_info *safetyInfo)
{
	List	   *flattened_targetList = subquery->targetList;
	ListCell   *lc;

	/*
	 * We must be careful with grouping Vars and join alias Vars in the
	 * subquery's outputs, as they hide the underlying expressions.
	 *
	 * We need to expand grouping Vars to their underlying expressions (the
	 * grouping clauses) because the grouping expressions themselves might be
	 * volatile or set-returning.  However, we do not need to expand join
	 * alias Vars, as their underlying structure does not introduce volatile
	 * or set-returning functions at the current level.
	 *
	 * In neither case do we need to recursively examine the Vars contained in
	 * these underlying expressions.  Even if they reference outputs from
	 * lower-level subqueries (at any depth), those references are guaranteed
	 * not to expand to volatile or set-returning functions, because
	 * subqueries containing such functions in their targetlists are never
	 * pulled up.
	 */
	if (subquery->hasGroupRTE)
	{
		/*
		 * We can safely pass NULL for the root here.  This function uses the
		 * expanded expressions solely to check for volatile or set-returning
		 * functions, which is independent of the Vars' nullingrels.
		 */
		flattened_targetList = (List *)
			flatten_group_exprs(NULL, subquery, (Node *) subquery->targetList);
	}

	foreach(lc, flattened_targetList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(lc);

		if (tle->resjunk)
			continue;			/* ignore resjunk columns */

		/* Functions returning sets are unsafe (point 1) */
		if (subquery->hasTargetSRFs &&
			(safetyInfo->unsafeFlags[tle->resno] &
			 UNSAFE_HAS_SET_FUNC) == 0 &&
			expression_returns_set((Node *) tle->expr))
		{
			safetyInfo->unsafeFlags[tle->resno] |= UNSAFE_HAS_SET_FUNC;
			continue;
		}

		/* Volatile functions are unsafe (point 2) */
		if ((safetyInfo->unsafeFlags[tle->resno] &
			 UNSAFE_HAS_VOLATILE_FUNC) == 0 &&
			contain_volatile_functions((Node *) tle->expr))
		{
			safetyInfo->unsafeFlags[tle->resno] |= UNSAFE_HAS_VOLATILE_FUNC;
			continue;
		}

		/* If subquery uses DISTINCT ON, check point 3 */
		if (subquery->hasDistinctOn &&
			(safetyInfo->unsafeFlags[tle->resno] &
			 UNSAFE_NOTIN_DISTINCTON_CLAUSE) == 0 &&
			!targetIsInSortList(tle, InvalidOid, subquery->distinctClause))
		{
			/* non-DISTINCT column, so mark it unsafe */
			safetyInfo->unsafeFlags[tle->resno] |= UNSAFE_NOTIN_DISTINCTON_CLAUSE;
			continue;
		}

		/* If subquery uses window functions, check point 4 */
		if (subquery->hasWindowFuncs &&
			(safetyInfo->unsafeFlags[tle->resno] &
			 UNSAFE_NOTIN_PARTITIONBY_CLAUSE) == 0 &&
			!targetIsInAllPartitionLists(tle, subquery))
		{
			/* not present in all PARTITION BY clauses, so mark it unsafe */
			safetyInfo->unsafeFlags[tle->resno] |= UNSAFE_NOTIN_PARTITIONBY_CLAUSE;
			continue;
		}
	}
}

/*
 * For subqueries using UNION/UNION ALL/INTERSECT/INTERSECT ALL, we can
 * push quals into each component query, but the quals can only reference
 * subquery columns that suffer no type coercions in the set operation.
 * Otherwise there are possible semantic gotchas.  So, we check the
 * component queries to see if any of them have output types different from
 * the top-level setop outputs.  We set the UNSAFE_TYPE_MISMATCH bit in
 * unsafeFlags[k] if column k has different type in any component.
 *
 * We don't have to care about typmods here: the only allowed difference
 * between set-op input and output typmods is input is a specific typmod
 * and output is -1, and that does not require a coercion.
 *
 * tlist is a subquery tlist.
 * colTypes is an OID list of the top-level setop's output column types.
 * safetyInfo is the pushdown_safety_info to set unsafeFlags[] for.
 */
/*
 * compare_tlist_datatypes - (中文)比对 setop 组件输出与顶层输出的类型
 *
 * 【作用】把某个 setop 组件查询的 targetlist 与顶层 setop 的输出类型列表逐列
 * 比较,若某列类型不一致,在 safetyInfo->unsafeFlags[resno] 置
 * UNSAFE_TYPE_MISMATCH。由 subquery_is_pushdown_safe() 对 setop 组件调用。
 *
 * 【设计思想】UNION/INTERSECT 系列允许把 qual 推入各组件,但被引用列必须在
 * setop 过程中"未经历类型强制转换",否则语义有坑;因此只要任一组件该列类型
 * 与顶层不同就标记为不安全。typmod 的差异无需关心:setop 允许的唯一 typmod
 * 差异是"输入为具体 typmod、输出为 -1",而这不产生强制转换。resjunk 列跳过,
 * 列数不匹配时报错(内部一致性错误)。
 *
 * 【参数】
 *   tlist      —— 组件查询的 targetlist;
 *   colTypes   —— 顶层 setop 输出列类型的 OID 列表;
 *   safetyInfo —— 安全性工作区。
 * 【返回值】无。
 */
static void
compare_tlist_datatypes(List *tlist, List *colTypes,
						pushdown_safety_info *safetyInfo)
{
	ListCell   *l;
	ListCell   *colType = list_head(colTypes);

	foreach(l, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (tle->resjunk)
			continue;			/* ignore resjunk columns */
		if (colType == NULL)
			elog(ERROR, "wrong number of tlist entries");
		if (exprType((Node *) tle->expr) != lfirst_oid(colType))
			safetyInfo->unsafeFlags[tle->resno] |= UNSAFE_TYPE_MISMATCH;
		colType = lnext(colTypes, colType);
	}
	if (colType != NULL)
		elog(ERROR, "wrong number of tlist entries");
}

/*
 * targetIsInAllPartitionLists
 *		True if the TargetEntry is listed in the PARTITION BY clause
 *		of every window defined in the query.
 *
 * It would be safe to ignore windows not actually used by any window
 * function, but it's not easy to get that info at this stage; and it's
 * unlikely to be useful to spend any extra cycles getting it, since
 * unreferenced window definitions are probably infrequent in practice.
 */
/*
 * targetIsInAllPartitionLists - (中文)判断目标列是否出现在所有窗口的 PARTITION BY 中
 *
 * 【作用】返回 true 当且仅当 targetlist 项 tle 出现在查询定义的所有窗口的
 * PARTITION BY 子句里。被 check_output_expressions() 用于标记窗口列是否可被
 * 下推 qual 引用。
 *
 * 【设计思想】只要任一窗口未把该列作为分区列,该列就不满足"同一分区内全部
 * 行一致"的保证,标记为不安全。此处不试图排除"没有被任何窗口函数实际使用"
 * 的窗口定义,因为此阶段获取该信息成本高而收益低。
 *
 * 【参数】
 *   tle   —— 待检查的 targetlist 项;
 *   query —— 子查询。
 * 【返回值】true:出现在所有窗口的 PARTITION BY;false:至少一个窗口没有。
 */
static bool
targetIsInAllPartitionLists(TargetEntry *tle, Query *query)
{
	ListCell   *lc;

	foreach(lc, query->windowClause)
	{
		WindowClause *wc = (WindowClause *) lfirst(lc);

		if (!targetIsInSortList(tle, InvalidOid, wc->partitionClause))
			return false;
	}
	return true;
}

/*
 * qual_is_pushdown_safe - is a particular rinfo safe to push down?
 *
 * rinfo is a restriction clause applying to the given subquery (whose RTE
 * has index rti in the parent query).
 *
 * Conditions checked here:
 *
 * 1. rinfo's clause must not contain any SubPlans (mainly because it's
 * unclear that it will work correctly: SubLinks will already have been
 * transformed into SubPlans in the qual, but not in the subquery).  Note that
 * SubLinks that transform to initplans are safe, and will be accepted here
 * because what we'll see in the qual is just a Param referencing the initplan
 * output.
 *
 * 2. If unsafeVolatile is set, rinfo's clause must not contain any volatile
 * functions.
 *
 * 3. If unsafeLeaky is set, rinfo's clause must not contain any leaky
 * functions that are passed Var nodes, and therefore might reveal values from
 * the subquery as side effects.
 *
 * 4. rinfo's clause must not refer to the whole-row output of the subquery
 * (since there is no easy way to name that within the subquery itself).
 *
 * 5. rinfo's clause must not refer to any subquery output columns that were
 * found to be unsafe to reference by subquery_is_pushdown_safe().
 *
 * 6. If the subquery has a grouping layer (DISTINCT, DISTINCT ON, window
 * PARTITION BY, or a set operation that groups rows by equality), rinfo's
 * clause must not apply a different equivalence relation to a grouping column
 * than the grouping uses; otherwise it would distinguish rows the grouping
 * considers equal, and pushing such a clause past the grouping would drop
 * members of a group and change which row becomes the group's representative
 * (or, for window functions, change per-partition values such as ranks and
 * counts).  See expression_has_grouping_conflict for the kinds of conflict
 * detected.
 */
/*
 * qual_is_pushdown_safe - (中文)判定单条限制条件是否可下推进子查询
 *
 * 【作用】在子查询整体可下推(见 subquery_is_pushdown_safe)的前提下,逐条
 * 检查上层限制条件 rinfo,返回 PUSHDOWN_SAFE(可推入 WHERE/HAVING)、
 * PUSHDOWN_UNSAFE(不可推)或 PUSHDOWN_WINDOWCLAUSE_RUNCOND(不能当普通条件,
 * 但可作为窗口 runCondition 下推)。由 set_subquery_pathlist() 对每个
 * baserestrictinfo 项调用。
 *
 * 【设计思想】六类检查:
 * 1) 含子计划(SubPlan)拒绝——子查询里对应的 SubLink 尚未转换,推入会不一致
 *    (initplan 转换成的 Param 是安全的);
 * 2) 子查询有 DISTINCT/窗口/SRF 且条件易变时拒绝(语义变化);
 * 3) 子查询是安全屏障(security_barrier)且条件含"泄密"函数(带 Var 参数、
 *    可能通过副作用泄露数据)时拒绝;
 * 4) 条件引用子查询整行(varattno == 0)拒绝(子查询内部无法命名该输出);
 * 5) 条件引用的列被标记为不安全:视具体原因——易变/SRF/DISTINCT ON/类型不
 *    匹配则拒绝;仅"未全部分区列"(UNSAFE_NOTIN_PARTITIONBY_CLAUSE)时可降级
 *    为 PUSHDOWN_WINDOWCLAUSE_RUNCOND(注意即使已降级仍继续扫描其它 Var,
 *    可能进一步退化为不安全);
 * 6) 分组冲突检查:子查询有窗口/DISTINCT/setop 分组时,若条件对"分组视为
 *    相等"的行应用了不同等价关系(expression_has_grouping_conflict),推入
 *    会改变组的代表行,拒绝。
 * 另外 LATERAL 引用与 PlaceHolderVar 也被拒绝(基础设施不支持)。
 *
 * 【参数】
 *   subquery   —— 子查询;
 *   rti        —— 子查询在父查询 rtable 中的索引;
 *   rinfo      —— 待检查的上层限制条件;
 *   safetyInfo —— 安全性工作区(含 unsafeFlags 与 volatile/leaky 开关)。
 * 【返回值】PUSHDOWN_SAFE / PUSHDOWN_UNSAFE / PUSHDOWN_WINDOWCLAUSE_RUNCOND。
 */
static pushdown_safe_type
qual_is_pushdown_safe(Query *subquery, Index rti, RestrictInfo *rinfo,
					  pushdown_safety_info *safetyInfo)
{
	pushdown_safe_type safe = PUSHDOWN_SAFE;
	Node	   *qual = (Node *) rinfo->clause;
	List	   *vars;
	ListCell   *vl;

	/* Refuse subselects (point 1) */
	if (contain_subplans(qual))
		return PUSHDOWN_UNSAFE;

	/* Refuse volatile quals if we found they'd be unsafe (point 2) */
	if (safetyInfo->unsafeVolatile &&
		contain_volatile_functions((Node *) rinfo))
		return PUSHDOWN_UNSAFE;

	/* Refuse leaky quals if told to (point 3) */
	if (safetyInfo->unsafeLeaky &&
		contain_leaked_vars(qual))
		return PUSHDOWN_UNSAFE;

	/*
	 * Examine all Vars used in clause.  Since it's a restriction clause, all
	 * such Vars must refer to subselect output columns ... unless this is
	 * part of a LATERAL subquery, in which case there could be lateral
	 * references.
	 *
	 * By omitting the relevant flags, this also gives us a cheap sanity check
	 * that no aggregates or window functions appear in the qual.  Those would
	 * be unsafe to push down, but at least for the moment we could never see
	 * any in a qual anyhow.
	 */
	vars = pull_var_clause(qual, PVC_INCLUDE_PLACEHOLDERS);
	foreach(vl, vars)
	{
		Var		   *var = (Var *) lfirst(vl);

		/*
		 * XXX Punt if we find any PlaceHolderVars in the restriction clause.
		 * It's not clear whether a PHV could safely be pushed down, and even
		 * less clear whether such a situation could arise in any cases of
		 * practical interest anyway.  So for the moment, just refuse to push
		 * down.
		 */
		if (!IsA(var, Var))
		{
			safe = PUSHDOWN_UNSAFE;
			break;
		}

		/*
		 * Punt if we find any lateral references.  It would be safe to push
		 * these down, but we'd have to convert them into outer references,
		 * which subquery_push_qual lacks the infrastructure to do.  The case
		 * arises so seldom that it doesn't seem worth working hard on.
		 */
		if (var->varno != rti)
		{
			safe = PUSHDOWN_UNSAFE;
			break;
		}

		/* Subqueries have no system columns */
		Assert(var->varattno >= 0);

		/* Check point 4 */
		if (var->varattno == 0)
		{
			safe = PUSHDOWN_UNSAFE;
			break;
		}

		/* Check point 5 */
		if (safetyInfo->unsafeFlags[var->varattno] != 0)
		{
			if (safetyInfo->unsafeFlags[var->varattno] &
				(UNSAFE_HAS_VOLATILE_FUNC | UNSAFE_HAS_SET_FUNC |
				 UNSAFE_NOTIN_DISTINCTON_CLAUSE | UNSAFE_TYPE_MISMATCH))
			{
				safe = PUSHDOWN_UNSAFE;
				break;
			}
			else
			{
				/* UNSAFE_NOTIN_PARTITIONBY_CLAUSE is ok for run conditions */
				safe = PUSHDOWN_WINDOWCLAUSE_RUNCOND;
				/* don't break, we might find another Var that's unsafe */
			}
		}
	}

	list_free(vars);

	/* Check point 6 */
	if (safe == PUSHDOWN_SAFE &&
		(subquery->hasWindowFuncs ||
		 subquery->distinctClause != NIL ||
		 (subquery->setOperations != NULL &&
		  setop_has_grouping(subquery->setOperations))))
	{
		if (expression_has_grouping_conflict(qual, pushdown_var_grouping_eqop,
											 subquery))
			safe = PUSHDOWN_UNSAFE;
	}

	return safe;
}

/*
 * pushdown_var_grouping_eqop
 *		grouping_eqop_callback for qual_is_pushdown_safe.
 *
 * Returns the grouping equality operator for 'var' if it references a subquery
 * output column that participates in the subquery's grouping layer; InvalidOid
 * otherwise.
 *
 * 'context' is the subquery Query whose pushdown safety we're checking.
 */
/*
 * pushdown_var_grouping_eqop - (中文)分组冲突检查回调:取变量的分组等号运算符
 *
 * 【作用】作为 expression_has_grouping_conflict() 的 grouping_eqop_callback
 * 回调:对 qual 中引用的 Var,返回子查询在其上做行分组所用的等号运算符
 * (eqop);若 Var 不参与任何分组机制则返回 InvalidOid。由 qual_is_pushdown_safe()
 * 传入使用。
 *
 * 【设计思想】qual_is_pushdown_safe() 已保证到达这里的 level-0 Var 必然引用
 * 子查询的某个分组列(否则走不到点 6),因此断言 eqop 必然有效。上层 Var
 * (varlevelsup != 0)一律返回 InvalidOid(不在本层分组)。
 *
 * 【参数】
 *   var     —— qual 中引用的 Var;
 *   context —— 子查询 Query。
 * 【返回值】子查询对该列使用的分组等号运算符 OID,无则 InvalidOid。
 */
static Oid
pushdown_var_grouping_eqop(Var *var, void *context)
{
	Query	   *subquery = (Query *) context;
	Oid			eqop;

	if (var->varlevelsup != 0)
		return InvalidOid;

	eqop = subquery_column_grouping_eqop(subquery, var->varattno);

	/*
	 * qual_is_pushdown_safe ensures any level-0 subquery Var that reaches us
	 * references a grouping column.
	 */
	Assert(OidIsValid(eqop));

	return eqop;
}

/*
 * subquery_column_grouping_eqop
 *		Return the equality operator that the subquery uses to group rows on
 *		the given output column, or InvalidOid if the column doesn't
 *		participate in any grouping mechanism.
 *
 * A subquery output column is grouping-relevant if it appears in
 * subquery->distinctClause (covering both DISTINCT and DISTINCT ON), in every
 * window's PARTITION BY clause, or is grouped by some node in a set-operation
 * tree.  In all of these cases the parser builds the SortGroupClause with the
 * column's type-default equality operator via get_sort_group_operators, so any
 * matching SortGroupClause carries the correct eqop.
 */
/*
 * subquery_column_grouping_eqop - (中文)取子查询某输出列的分组等号运算符
 *
 * 【作用】给定子查询与输出列号,返回子查询对该列做行分组所用的等号运算符;
 * 若该列不参与任何分组机制(DISTINCT/DISTINCT ON、窗口 PARTITION BY、
 * setop 分组)则返回 InvalidOid。被 pushdown_var_grouping_eqop() 调用。
 *
 * 【设计思想】分组机制分三种按序检查:
 * 1) distinctClause(DISTINCT 与 DISTINCT ON 共用):找到 tleSortGroupRef 匹配
 *    的 SortGroupClause 即返回其 eqop;
 * 2) 窗口 PARTITION BY:必须出现在每个窗口的 partitionClause 里才返回等号
 *    运算符(取最后一个匹配窗口的 eqop,解析器用 get_sort_group_operators
 *    生成的都是类型默认等号,所以一致);
 * 3) setop:递归 setop_column_grouping_eqop() 检查是否被某个节点按等号分组。
 * 全部未命中返回 InvalidOid。attno 越界直接返回 InvalidOid。
 *
 * 【参数】
 *   subquery —— 子查询;
 *   attno    —— 输出列号(1 起)。
 * 【返回值】该列的分组等号运算符 OID;不参与分组则 InvalidOid。
 */
static Oid
subquery_column_grouping_eqop(Query *subquery, AttrNumber attno)
{
	TargetEntry *tle;
	ListCell   *lc;

	if (attno <= 0 || attno > list_length(subquery->targetList))
		return InvalidOid;

	tle = list_nth_node(TargetEntry, subquery->targetList, attno - 1);

	/* DISTINCT or DISTINCT ON */
	foreach(lc, subquery->distinctClause)
	{
		SortGroupClause *sgc = lfirst_node(SortGroupClause, lc);

		if (sgc->tleSortGroupRef == tle->ressortgroupref)
			return sgc->eqop;
	}

	/* Window function PARTITION BY: must appear in every window's list. */
	if (subquery->hasWindowFuncs && subquery->windowClause != NIL)
	{
		Oid			eqop = InvalidOid;

		foreach(lc, subquery->windowClause)
		{
			WindowClause *wc = (WindowClause *) lfirst(lc);
			ListCell   *lc2;

			foreach(lc2, wc->partitionClause)
			{
				SortGroupClause *sgc = lfirst_node(SortGroupClause, lc2);

				if (sgc->tleSortGroupRef == tle->ressortgroupref)
					break;
			}
			if (lc2 == NULL)
				break;			/* not present in this window's list */
			eqop = lfirst_node(SortGroupClause, lc2)->eqop;
		}
		if (lc == NULL)
			return eqop;		/* matched in every window */
	}

	/* Set operation */
	if (subquery->setOperations != NULL)
		return setop_column_grouping_eqop(subquery->setOperations, attno);

	return InvalidOid;
}

/*
 * setop_column_grouping_eqop
 *		Recursively search a SetOperationStmt tree for any node that groups
 *		rows by equality, and return the equality operator used for the given
 *		output column.  Returns InvalidOid if no node in the tree groups (i.e.,
 *		an entirely-UNION-ALL tree).
 *
 * For any set operation other than UNION ALL, groupClauses is a positional
 * list of SortGroupClauses, with element N-1 corresponding to output column N
 * (see makeSortGroupClauseForSetOp).
 */
/*
 * setop_column_grouping_eqop - (中文)递归查找 setop 树中某列的分组等号运算符
 *
 * 【作用】沿 SetOperationStmt 树递归,查找第一个按等号分组行并且覆盖指定输出
 * 列的节点,返回其分组等号运算符;整棵树都不分组(纯 UNION ALL)时返回
 * InvalidOid。被 subquery_column_grouping_eqop() 调用。
 *
 * 【设计思想】对任何非 UNION ALL 的 setop 节点,groupClauses 是按位置排列的
 * SortGroupClause 列表(第 N 个元素对应输出列 N),直接按 attno-1 取即可;若
 * 当前节点不分组(UNION ALL)则向左右子树递归。注意递归只找"第一个"命中的
 * 等号运算符即可,因为解析器构造的各类节点运算符一致。
 *
 * 【参数】
 *   setop —— setop 树节点(NULL 或非 SetOperationStmt 返回 InvalidOid);
 *   attno —— 输出列号(1 起)。
 * 【返回值】该列的分组等号运算符 OID;无则 InvalidOid。
 */
static Oid
setop_column_grouping_eqop(Node *setop, AttrNumber attno)
{
	SetOperationStmt *op;
	Oid			eqop;

	if (setop == NULL || !IsA(setop, SetOperationStmt))
		return InvalidOid;

	op = (SetOperationStmt *) setop;

	if (op->groupClauses != NIL &&
		attno >= 1 && attno <= list_length(op->groupClauses))
	{
		SortGroupClause *sgc = list_nth_node(SortGroupClause,
											 op->groupClauses, attno - 1);

		return sgc->eqop;
	}

	/* Recurse into children to find any inner grouping */
	eqop = setop_column_grouping_eqop(op->larg, attno);
	if (OidIsValid(eqop))
		return eqop;
	return setop_column_grouping_eqop(op->rarg, attno);
}

/*
 * setop_has_grouping
 *		Return true if any node in the SetOperationStmt tree groups rows by
 *		equality (i.e., has non-NIL groupClauses).
 */
/*
 * setop_has_grouping - (中文)判断 setop 树中是否存在按等号分组的节点
 *
 * 【作用】返回 true 当且仅当 SetOperationStmt 树的某个节点带非空 groupClauses
 * (即非 UNION ALL,按等号分组)。被 qual_is_pushdown_safe() 用于判定是否要做
 * 分组冲突检查。
 *
 * 【设计思想】简单的递归:当前节点有 groupClauses 即为 true,否则递归左右
 * 子树取或。
 *
 * 【参数】
 *   setop —— setop 树节点(可为 NULL)。
 * 【返回值】true:存在分组节点;false:纯 UNION ALL 树或空节点。
 */
static bool
setop_has_grouping(Node *setop)
{
	SetOperationStmt *op;

	if (setop == NULL || !IsA(setop, SetOperationStmt))
		return false;

	op = (SetOperationStmt *) setop;
	if (op->groupClauses != NIL)
		return true;

	return setop_has_grouping(op->larg) || setop_has_grouping(op->rarg);
}

/*
 * subquery_push_qual - push down a qual that we have determined is safe
 */
/*
 * subquery_push_qual - (中文)把已确认安全的 qual 推入子查询
 *
 * 【作用】把一条上层限制条件真正下推进子查询:若子查询是 setop 树则按组件
 * 递归(每个组件得到自己的副本);否则把 qual 中引用子查询输出列的 Var 替换
 * 为子查询 targetlist 的对应表达式,再挂到子查询的 WHERE(无分组时)或 HAVING
 * (有聚合/分组时)。由 set_subquery_pathlist() 调用。
 *
 * 【设计思想】
 * - 用 ReplaceVarsFromTargetList() 完成变量替换:qual 里的 Var 在父查询中
 *   以 (rti, attno) 标识子查询输出,替换后变成子查询内部实际表达式;上层
 *   变量此时已被改成 Param,无需处理;
 * - 归属地选择:若子查询有聚合/分组,条件语义针对"组结果行",必须进 HAVING;
 * - 不改 hasAggs/hasSubLinks 标志:推入的不会有新聚合,也不下推子查询。
 *
 * 【参数】
 *   subquery —— 目标子查询;
 *   rte      —— 子查询在父查询中的 RTE;
 *   rti      —— 子查询 RTE 的索引;
 *   qual     —— 待推入的条件。
 * 【返回值】无。
 */
static void
subquery_push_qual(Query *subquery, RangeTblEntry *rte, Index rti, Node *qual)
{
	if (subquery->setOperations != NULL)
	{
		/* Recurse to push it separately to each component query */
		recurse_push_qual(subquery->setOperations, subquery,
						  rte, rti, qual);
	}
	else
	{
		/*
		 * We need to replace Vars in the qual (which must refer to outputs of
		 * the subquery) with copies of the subquery's targetlist expressions.
		 * Note that at this point, any uplevel Vars in the qual should have
		 * been replaced with Params, so they need no work.
		 *
		 * This step also ensures that when we are pushing into a setop tree,
		 * each component query gets its own copy of the qual.
		 */
		qual = ReplaceVarsFromTargetList(qual, rti, 0, rte,
										 subquery->targetList,
										 subquery->resultRelation,
										 REPLACEVARS_REPORT_ERROR, 0,
										 &subquery->hasSubLinks);

		/*
		 * Now attach the qual to the proper place: normally WHERE, but if the
		 * subquery uses grouping or aggregation, put it in HAVING (since the
		 * qual really refers to the group-result rows).
		 */
		if (subquery->hasAggs || subquery->groupClause || subquery->groupingSets || subquery->havingQual)
			subquery->havingQual = make_and_qual(subquery->havingQual, qual);
		else
			subquery->jointree->quals =
				make_and_qual(subquery->jointree->quals, qual);

		/*
		 * We need not change the subquery's hasAggs or hasSubLinks flags,
		 * since we can't be pushing down any aggregates that weren't there
		 * before, and we don't push down subselects at all.
		 */
	}
}

/*
 * Helper routine to recurse through setOperations tree
 */
/*
 * recurse_push_qual - (中文)把 qual 递归推入 setop 树的每个组件查询
 *
 * 【作用】沿 SetOperationStmt 树递归,对每个叶子组件查询(RangeTblRef)调用
 * subquery_push_qual() 把同一条 qual 推入。由 subquery_push_qual() 在子查询
 * 含 setop 时调用。
 *
 * 【设计思想】同一 qual 会被推入所有组件(每个组件自行做变量替换),这是
 * UNION/INTERSECT 语义要求的"每臂都过滤"。EXCEPT 已在安全性检查阶段被排除。
 *
 * 【参数】
 *   setOp    —— setop 树节点;
 *   topquery —— 顶层查询(供 rt_fetch 定位组件 RTE);
 *   rte      —— 子查询在父查询中的 RTE;
 *   rti      —— 子查询 RTE 的索引;
 *   qual     —— 待推入的条件。
 * 【返回值】无。
 */
static void
recurse_push_qual(Node *setOp, Query *topquery,
				  RangeTblEntry *rte, Index rti, Node *qual)
{
	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		RangeTblEntry *subrte = rt_fetch(rtr->rtindex, topquery->rtable);
		Query	   *subquery = subrte->subquery;

		Assert(subquery != NULL);
		subquery_push_qual(subquery, rte, rti, qual);
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		recurse_push_qual(op->larg, topquery, rte, rti, qual);
		recurse_push_qual(op->rarg, topquery, rte, rti, qual);
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
	}
}

/*****************************************************************************
 *			SIMPLIFYING SUBQUERY TARGETLISTS
 *****************************************************************************/

/*
 * remove_unused_subquery_outputs
 *		Remove subquery targetlist items we don't need
 *
 * It's possible, even likely, that the upper query does not read all the
 * output columns of the subquery.  We can remove any such outputs that are
 * not needed by the subquery itself (e.g., as sort/group columns) and do not
 * affect semantics otherwise (e.g., volatile functions can't be removed).
 * This is useful not only because we might be able to remove expensive-to-
 * compute expressions, but because deletion of output columns might allow
 * optimizations such as join removal to occur within the subquery.
 *
 * extra_used_attrs can be passed as non-NULL to mark any columns (offset by
 * FirstLowInvalidHeapAttributeNumber) that we should not remove.  This
 * parameter is modified by the function, so callers must make a copy if they
 * need to use the passed in Bitmapset after calling this function.
 *
 * To avoid affecting column numbering in the targetlist, we don't physically
 * remove unused tlist entries, but rather replace their expressions with NULL
 * constants.  This is implemented by modifying subquery->targetList.
 */
/*
 * remove_unused_subquery_outputs - (中文)删除子查询中未被使用的输出列
 *
 * 【作用】把子查询 targetlist 中"上层查询不需要、且子查询自身也不依赖"的
 * 输出表达式替换成 NULL 常量,从而减少计算量并可能让子查询内部(如 join
 * removal)受益。由 set_subquery_pathlist() 在推入 quals 之后调用。
 *
 * 【设计思想】
 * - 收集"被使用"的输出列号位图:关系 reltarget(注意不能看 attr_needed,
 *   继承子关系没有它)、未推下的限制条件,以及调用方传入的
 *   extra_used_attrs(窗口 runCondition 用到的列);
 * - 存在整行引用时不可删除任何列;
 * - 逐列跳过:有 sortgroupref(参与某 sort/group 子句)、resjunk、被上层使用、
 *   含 SRF(删了改变行数)、含易变函数(可能产生用户期待的副作用)的列都保留;
 * - 删除的实现是"把表达式替换为保持类型/typmod/排序规则的 NULL 常量",而
 *   非物理删除,以保证列编号稳定;
 * - 有 setop 或普通 DISTINCT 时不处理(前者改全部子 SELECT 麻烦,后者所有
 *   输出列本来就在 distinctClause 中)。
 *
 * 【参数】
 *   subquery         —— 子查询(其 targetList 被就地修改);
 *   rel              —— 子查询关系(供收集使用列);
 *   extra_used_attrs —— 额外的必须保留列位图(偏移
 *                       FirstLowInvalidHeapAttributeNumber),会被就地修改。
 * 【返回值】无。
 */
static void
remove_unused_subquery_outputs(Query *subquery, RelOptInfo *rel,
							   Bitmapset *extra_used_attrs)
{
	Bitmapset  *attrs_used;
	ListCell   *lc;

	/*
	 * Just point directly to extra_used_attrs. No need to bms_copy as none of
	 * the current callers use the Bitmapset after calling this function.
	 */
	attrs_used = extra_used_attrs;

	/*
	 * Do nothing if subquery has UNION/INTERSECT/EXCEPT: in principle we
	 * could update all the child SELECTs' tlists, but it seems not worth the
	 * trouble presently.
	 */
	if (subquery->setOperations)
		return;

	/*
	 * If subquery has regular DISTINCT (not DISTINCT ON), we're wasting our
	 * time: all its output columns must be used in the distinctClause.
	 */
	if (subquery->distinctClause && !subquery->hasDistinctOn)
		return;

	/*
	 * Collect a bitmap of all the output column numbers used by the upper
	 * query.
	 *
	 * Add all the attributes needed for joins or final output.  Note: we must
	 * look at rel's targetlist, not the attr_needed data, because attr_needed
	 * isn't computed for inheritance child rels, cf set_append_rel_size().
	 * (XXX might be worth changing that sometime.)
	 */
	pull_varattnos((Node *) rel->reltarget->exprs, rel->relid, &attrs_used);

	/* Add all the attributes used by un-pushed-down restriction clauses. */
	foreach(lc, rel->baserestrictinfo)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		pull_varattnos((Node *) rinfo->clause, rel->relid, &attrs_used);
	}

	/*
	 * If there's a whole-row reference to the subquery, we can't remove
	 * anything.
	 */
	if (bms_is_member(0 - FirstLowInvalidHeapAttributeNumber, attrs_used))
		return;

	/*
	 * Run through the tlist and zap entries we don't need.  It's okay to
	 * modify the tlist items in-place because set_subquery_pathlist made a
	 * copy of the subquery.
	 */
	foreach(lc, subquery->targetList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(lc);
		Node	   *texpr = (Node *) tle->expr;

		/*
		 * If it has a sortgroupref number, it's used in some sort/group
		 * clause so we'd better not remove it.  Also, don't remove any
		 * resjunk columns, since their reason for being has nothing to do
		 * with anybody reading the subquery's output.  (It's likely that
		 * resjunk columns in a sub-SELECT would always have ressortgroupref
		 * set, but even if they don't, it seems imprudent to remove them.)
		 */
		if (tle->ressortgroupref || tle->resjunk)
			continue;

		/*
		 * If it's used by the upper query, we can't remove it.
		 */
		if (bms_is_member(tle->resno - FirstLowInvalidHeapAttributeNumber,
						  attrs_used))
			continue;

		/*
		 * If it contains a set-returning function, we can't remove it since
		 * that could change the number of rows returned by the subquery.
		 */
		if (subquery->hasTargetSRFs &&
			expression_returns_set(texpr))
			continue;

		/*
		 * If it contains volatile functions, we daren't remove it for fear
		 * that the user is expecting their side-effects to happen.
		 */
		if (contain_volatile_functions(texpr))
			continue;

		/*
		 * OK, we don't need it.  Replace the expression with a NULL constant.
		 * Preserve the exposed type of the expression, in case something
		 * looks at the rowtype of the subquery's result.
		 */
		tle->expr = (Expr *) makeNullConst(exprType(texpr),
										   exprTypmod(texpr),
										   exprCollation(texpr));
	}
}

/*
 * create_partial_bitmap_paths
 *	  Build partial bitmap heap path for the relation
 */
/*
 * create_partial_bitmap_paths - (中文)为位图堆扫描生成 partial 路径
 *
 * 【作用】在给定位图路径(bitmapqual)之上,为关系生成一个并行感知的
 * BitmapHeapScan partial 路径:先用 compute_bitmap_pages() 估算需要读取的堆
 * 页数,据此计算并行 worker 数,然后创建路径加入 rel->partial_pathlist。
 * 被 indxpath.c 在生成位图路径时调用。
 *
 * 【设计思想】位图扫描的并行度按"位图访问到的堆页数"而非全表页数估算
 * (compute_bitmap_pages 应用了位图选择性与随机访问比例)。worker 数不够
 * (<=0,例如表太小)则放弃生成。
 *
 * 【参数】
 *   root       —— PlannerInfo;
 *   rel        —— 被扫描的关系;
 *   bitmapqual —— 位图路径(任意叶子为 BitmapIndexScan 的树)。
 * 【返回值】无。
 */
void
create_partial_bitmap_paths(PlannerInfo *root, RelOptInfo *rel,
							Path *bitmapqual)
{
	int			parallel_workers;
	double		pages_fetched;

	/* Compute heap pages for bitmap heap scan */
	pages_fetched = compute_bitmap_pages(root, rel, bitmapqual, 1.0,
										 NULL, NULL);

	parallel_workers = compute_parallel_worker(rel, pages_fetched, -1,
											   max_parallel_workers_per_gather);

	if (parallel_workers <= 0)
		return;

	add_partial_path(rel, (Path *) create_bitmap_heap_path(root, rel,
														   bitmapqual, rel->lateral_relids, 1.0, parallel_workers));
}

/*
 * Compute the number of parallel workers that should be used to scan a
 * relation.  We compute the parallel workers based on the size of the heap to
 * be scanned and the size of the index to be scanned, then choose a minimum
 * of those.
 *
 * "heap_pages" is the number of pages from the table that we expect to scan, or
 * -1 if we don't expect to scan any.
 *
 * "index_pages" is the number of pages from the index that we expect to scan, or
 * -1 if we don't expect to scan any.
 *
 * "max_workers" is caller's limit on the number of workers.  This typically
 * comes from a GUC.
 */
/*
 * compute_parallel_worker - (中文)计算扫描关系应使用的并行 worker 数
 *
 * 【作用】根据将被扫描的堆页数与索引页数估算并行 worker 数,返回给调用方
 * 用于创建 parallel 路径。被 create_plain_partial_paths()、create_partial_bitmap_paths()
 * 等调用。
 *
 * 【设计思想】
 * - 优先使用表的 parallel_workers reloption(用户显式指定);
 * - 否则按"页数每增长 3 倍就多一个 worker"的对数公式估算(以
 *   min_parallel_table_scan_size / min_parallel_index_scan_size 为基数,即
 *   小于该阈值时表太小不值得并行,返回 0;但继承子关系例外——单独可能不值,
 *   合起来却值,所以子关系不因大小被拒);堆、索引两个估算取小者;
 * - 最终结果受调用方 max_workers(通常来自 max_parallel_workers_per_gather
 *   等 GUC)封顶;循环里有溢出保护(阈值超过 INT_MAX/3 即停)。
 *
 * 【参数】
 *   rel         —— 被扫描的关系;
 *   heap_pages  —— 预计扫描的堆页数,-1 表示不扫堆(如纯索引场景);
 *   index_pages —— 预计扫描的索引页数,-1 表示不扫索引;
 *   max_workers —— 调用方允许的最大 worker 数。
 * 【返回值】并行 worker 数(0 表示不值得/不允许并行)。
 */
int
compute_parallel_worker(RelOptInfo *rel, double heap_pages, double index_pages,
						int max_workers)
{
	int			parallel_workers = 0;

	/*
	 * If the user has set the parallel_workers reloption, use that; otherwise
	 * select a default number of workers.
	 */
	if (rel->rel_parallel_workers != -1)
		parallel_workers = rel->rel_parallel_workers;
	else
	{
		/*
		 * If the number of pages being scanned is insufficient to justify a
		 * parallel scan, just return zero ... unless it's an inheritance
		 * child. In that case, we want to generate a parallel path here
		 * anyway.  It might not be worthwhile just for this relation, but
		 * when combined with all of its inheritance siblings it may well pay
		 * off.
		 */
		if (rel->reloptkind == RELOPT_BASEREL &&
			((heap_pages >= 0 && heap_pages < min_parallel_table_scan_size) ||
			 (index_pages >= 0 && index_pages < min_parallel_index_scan_size)))
			return 0;

		if (heap_pages >= 0)
		{
			int			heap_parallel_threshold;
			int			heap_parallel_workers = 1;

			/*
			 * Select the number of workers based on the log of the size of
			 * the relation.  This probably needs to be a good deal more
			 * sophisticated, but we need something here for now.  Note that
			 * the upper limit of the min_parallel_table_scan_size GUC is
			 * chosen to prevent overflow here.
			 */
			heap_parallel_threshold = Max(min_parallel_table_scan_size, 1);
			while (heap_pages >= (BlockNumber) (heap_parallel_threshold * 3))
			{
				heap_parallel_workers++;
				heap_parallel_threshold *= 3;
				if (heap_parallel_threshold > INT_MAX / 3)
					break;		/* avoid overflow */
			}

			parallel_workers = heap_parallel_workers;
		}

		if (index_pages >= 0)
		{
			int			index_parallel_workers = 1;
			int			index_parallel_threshold;

			/* same calculation as for heap_pages above */
			index_parallel_threshold = Max(min_parallel_index_scan_size, 1);
			while (index_pages >= (BlockNumber) (index_parallel_threshold * 3))
			{
				index_parallel_workers++;
				index_parallel_threshold *= 3;
				if (index_parallel_threshold > INT_MAX / 3)
					break;		/* avoid overflow */
			}

			if (parallel_workers > 0)
				parallel_workers = Min(parallel_workers, index_parallel_workers);
			else
				parallel_workers = index_parallel_workers;
		}
	}

	/* In no case use more than caller supplied maximum number of workers */
	parallel_workers = Min(parallel_workers, max_workers);

	return parallel_workers;
}

/*
 * generate_partitionwise_join_paths
 * 		Create paths representing partitionwise join for given partitioned
 * 		join relation.
 *
 * This must not be called until after we are done adding paths for all
 * child-joins. Otherwise, add_path might delete a path to which some path
 * generated here has a reference.
 */
/*
 * generate_partitionwise_join_paths - (中文)为分区连接关系生成分区连接路径
 *
 * 【作用】对分区连接关系(joinrel),递归地为其每个子分区连接(part_rels)
 * 生成路径,然后把所有非 dummy 子连接的路径聚合成父连接的 Append 路径。
 * 被 standard_join_search() 在每层连接关系路径生成完毕后调用;也递归调用
 * 自身处理更深的分区层级。
 *
 * 【设计思想】
 * - 前提:rel 是 joinrel 且带分区(IS_PARTITIONED_REL),且
 *   consider_partitionwise_join 已置位(由 set_append_rel_size 或更上层保证);
 * - 每个子分区连接递归处理:若某个子分区因约束排除而无法生成任何路径,
 *   则父连接"放弃分区连接"——把 rel->nparts 清零、直接返回(让普通连接路径
 *   继续存在);
 * - 子连接路径生成后立即 set_cheapest() 挑最便宜路径,并同样处理其 grouped
 *   rel(急切聚合);dummy 子连接跳过;
 * - 全部子连接都为 dummy 时父连接也标记 dummy;否则用 add_paths_to_append_rel()
 *   把子连接路径合成父连接的 Append/并行 Append 路径;
 * - 注意调用时机:必须在所有子连接路径都添加完之后,否则 add_path 可能删除
 *   本函数引用的路径。
 *
 * 【参数】
 *   root —— PlannerInfo;
 *   rel  —— 分区连接关系(若非 joinrel 或非分区则立即返回)。
 * 【返回值】无。
 */
void
generate_partitionwise_join_paths(PlannerInfo *root, RelOptInfo *rel)
{
	List	   *live_children = NIL;
	int			cnt_parts;
	int			num_parts;
	RelOptInfo **part_rels;

	/* Handle only join relations here. */
	if (!IS_JOIN_REL(rel))
		return;

	/* We've nothing to do if the relation is not partitioned. */
	if (!IS_PARTITIONED_REL(rel))
		return;

	/* The relation should have consider_partitionwise_join set. */
	Assert(rel->consider_partitionwise_join);

	/* Guard against stack overflow due to overly deep partition hierarchy. */
	check_stack_depth();

	num_parts = rel->nparts;
	part_rels = rel->part_rels;

	/* Collect non-dummy child-joins. */
	for (cnt_parts = 0; cnt_parts < num_parts; cnt_parts++)
	{
		RelOptInfo *child_rel = part_rels[cnt_parts];

		/* If it's been pruned entirely, it's certainly dummy. */
		if (child_rel == NULL)
			continue;

		/* Make partitionwise join paths for this partitioned child-join. */
		generate_partitionwise_join_paths(root, child_rel);

		/* If we failed to make any path for this child, we must give up. */
		if (child_rel->pathlist == NIL)
		{
			/*
			 * Mark the parent joinrel as unpartitioned so that later
			 * functions treat it correctly.
			 */
			rel->nparts = 0;
			return;
		}

		/* Else, identify the cheapest path for it. */
		set_cheapest(child_rel);

		/* Dummy children need not be scanned, so ignore those. */
		if (IS_DUMMY_REL(child_rel))
			continue;

		/*
		 * Except for the topmost scan/join rel, consider generating partial
		 * aggregation paths for the grouped relation on top of the paths of
		 * this partitioned child-join.  After that, we're done creating paths
		 * for the grouped relation, so run set_cheapest().
		 */
		if (child_rel->grouped_rel != NULL &&
			!bms_equal(IS_OTHER_REL(rel) ?
					   rel->top_parent_relids : rel->relids,
					   root->all_query_rels))
		{
			RelOptInfo *grouped_rel = child_rel->grouped_rel;

			Assert(IS_GROUPED_REL(grouped_rel));

			generate_grouped_paths(root, grouped_rel, child_rel);
			set_cheapest(grouped_rel);
		}

#ifdef OPTIMIZER_DEBUG
		pprint(child_rel);
#endif

		live_children = lappend(live_children, child_rel);
	}

	/* If all child-joins are dummy, parent join is also dummy. */
	if (!live_children)
	{
		mark_dummy_rel(rel);
		return;
	}

	/* Build additional paths for this rel from child-join paths. */
	add_paths_to_append_rel(root, rel, live_children);
	list_free(live_children);
}
