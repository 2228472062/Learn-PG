/*-------------------------------------------------------------------------
 *
 * initsplan.c
 *	  Target list, group by, qualification, joininfo initialization routines
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 查询优化器的"初始化计划"阶段,它是把分析器/重写器
 * 产出的原始查询树(Query + jointree)加工成后续路径生成阶段所需的各种
 * 规划器内部数据结构的关键模块。其核心目标可以概括为三件事:建立所有基础
 * 关系(基表)的信息、把连接树(Jointree)拆解为连接关系与限制条件(qual),
 * 以及为 GROUP BY、LATERAL、外连接等构造必要的辅助结构。
 *
 * 【职责与主要阶段】
 * 1. 建立基础关系:add_base_rels_to_query() 递归扫描 jointree,为每个出现在
 *    FROM 中的基表/子查询/函数 RTE 调用 build_simple_rel() 创建 RelOptInfo;
 *    add_other_rels_to_query() 随后为继承/分区父表扩展出子关系(otherrel)。
 * 2. 目标列收集:build_base_rel_tlists() 从最终目标列与 HAVING 子句中提取
 *    需要的 Var 与 PlaceHolderVar,并通过 add_vars_to_targetlist() 把每个
 *    Var 登记进其所属基础关系的 reltarget 与 attr_needed,保证后续计划树
 *    每一层都能拿到该列(顶层用"关系 0"标记表示必须一直向上传递)。
 * 3. 连接树拆解:deconstruct_jointree() 是本模块的中枢。它先调用
 *    deconstruct_recurse() 深度优先遍历 jointree,为每个节点建立 JoinTreeItem
 *    (记录 qualscope、inner_join_rels、左右 Relids 等),同时给外连接分配
 *    JoinDomain 并标记被外连接置空的 rel;随后 deconstruct_distribute() 对
 *    每个节点把 WHERE/JOIN ON 条件分发(distribute_qual_to_rels)到相应关系
 *    的 baserestrictinfo / joininfo,并为每个外连接构造 SpecialJoinInfo 加入
 *    root->join_info_list。带 LATERAL 引用而需推迟的条件会挂在父节点的
 *    lateral_clauses 中,可交换的左连接条件则推迟到第三遍
 *    deconstruct_distribute_oj_quals() 处理。
 * 4. 限制条件的等价类(EquivalenceClass)加工:distribute_qual_to_rels() 对
 *    可 mergejoin 的等式条件调用 process_equivalence() 把左右表达式送入 EC
 *    机制;外连接等式则登记到 left/right/full_join_clauses 列表供后续使用。
 * 5. GROUP BY 化简:remove_useless_groupby_columns() 利用唯一索引的函数依赖
 *    关系删掉冗余的 GROUP BY 列;setup_eager_aggregation() 及相关辅助函数
 *    尝试把聚合下推(eager aggregation)到连接之下。
 * 6. LATERAL 引用处理:find_lateral_references() 提取子查询对外层 Var 的
 *    引用并登记 where_needed,create_lateral_join_info() 计算每个基表的
 *    direct_lateral_relids / lateral_relids / lateral_referencers。
 * 7. 外键匹配:match_foreign_keys_to_quals() 把查询中的连接条件与 pg_constraint
 *    中的外键约束匹配,用于更可靠的选择率估算。
 *
 * 【核心数据结构】
 * - RelOptInfo:每个关系(基表或连接结果)的规划信息,含 targetlist、
 *   baserestrictinfo、joininfo、attr_needed 等;
 * - RestrictInfo:一个限制条件,记录所需关系集合 required_relids、安全级别、
 *   is_pushed_down、以及 merge/hash join 能力;
 * - SpecialJoinInfo:一个外连接的语义约束,记录 syn_lefthand/syn_righthand、
 *   min_lefthand/min_righthand、lhs_strict、以及可交换性信息
 *   (commute_above_l/r、commute_below_l/r);
 * - JoinDomain:一组其条件可以自由重排的连接的"域",用于约束等价类与
 *   伪常量条件的求值位置;
 * - EquivalenceClass:若干被等号相连的表达式集合,是生成 join 路径、传递
 *   相等性推导的核心;
 * - JoinTreeItem:deconstruct_jointree 遍历过程中为每个 jointree 节点建立的
 *   临时记录(本模块私有)。
 *
 * 【调用关系】
 * 本模块各函数主要由 planner() 在规划一个查询的初期调用:先建关系,再建
 * 目标列,然后 deconstruct_jointree() 分发所有条件,之后路径生成阶段
 * (paths.c / joinpath.c)使用 RestrictInfo 与 SpecialJoinInfo 决定连接顺序;
 * 在 join 被删除时 analyzejoins.c 会调用 rebuild_lateral_attr_needed()、
 * rebuild_joinclause_attr_needed() 等重建 attr_needed 信息。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/plan/initsplan.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/nbtree.h"
#include "access/sysattr.h"
#include "catalog/pg_constraint.h"
#include "catalog/pg_type.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/inherit.h"
#include "optimizer/joininfo.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/placeholder.h"
#include "optimizer/planmain.h"
#include "optimizer/planner.h"
#include "optimizer/restrictinfo.h"
#include "parser/analyze.h"
#include "rewrite/rewriteManip.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/typcache.h"

/* These parameters are set by GUC */
int			from_collapse_limit;
int			join_collapse_limit;


/*
 * deconstruct_jointree requires multiple passes over the join tree, because we
 * need to finish computing JoinDomains before we start distributing quals.
 * As long as we have to do that, other information such as the relevant
 * qualscopes might as well be computed in the first pass too.
 *
 * deconstruct_recurse recursively examines the join tree and builds a List
 * (in depth-first traversal order) of JoinTreeItem structs, which are then
 * processed iteratively by deconstruct_distribute.  If there are outer
 * joins, non-degenerate outer join clauses are processed in a third pass
 * deconstruct_distribute_oj_quals.
 *
 * The JoinTreeItem structs themselves can be freed at the end of
 * deconstruct_jointree, but do not modify or free their substructure,
 * as the relid sets may also be pointed to by RestrictInfo and
 * SpecialJoinInfo nodes.
 */
typedef struct JoinTreeItem
{
	/* Fields filled during deconstruct_recurse: */
	Node	   *jtnode;			/* jointree node to examine */
	JoinDomain *jdomain;		/* join domain for its ON/WHERE clauses */
	struct JoinTreeItem *jti_parent;	/* JoinTreeItem for this node's
										 * parent, or NULL if it's the top */
	Relids		qualscope;		/* base+OJ Relids syntactically included in
								 * this jointree node */
	Relids		inner_join_rels;	/* base+OJ Relids syntactically included
									 * in inner joins appearing at or below
									 * this jointree node */
	Relids		left_rels;		/* if join node, Relids of the left side */
	Relids		right_rels;		/* if join node, Relids of the right side */
	Relids		nonnullable_rels;	/* if outer join, Relids of the
									 * non-nullable side */
	/* Fields filled during deconstruct_distribute: */
	SpecialJoinInfo *sjinfo;	/* if outer join, its SpecialJoinInfo */
	List	   *oj_joinclauses; /* outer join quals not yet distributed */
	List	   *lateral_clauses;	/* quals postponed from children due to
									 * lateral references */
} JoinTreeItem;

/*
 * Compatibility info for one GROUP BY item, precomputed for use by
 * remove_useless_groupby_columns() when matching unique-index columns against
 * GROUP BY items.
 */
typedef struct GroupByColInfo
{
	AttrNumber	attno;			/* var->varattno */
	List	   *eq_opfamilies;	/* mergejoin opfamilies of sgc->eqop */
	Oid			coll;			/* var->varcollid */
} GroupByColInfo;


static bool is_partial_agg_memory_risky(PlannerInfo *root);
static void create_agg_clause_infos(PlannerInfo *root);
static void create_grouping_expr_infos(PlannerInfo *root);
static EquivalenceClass *get_eclass_for_sortgroupclause(PlannerInfo *root,
														SortGroupClause *sgc,
														Expr *expr);
static void extract_lateral_references(PlannerInfo *root, RelOptInfo *brel,
									   Index rtindex);
static List *deconstruct_recurse(PlannerInfo *root, Node *jtnode,
								 JoinDomain *parent_domain,
								 JoinTreeItem *parent_jtitem,
								 List **item_list);
static void deconstruct_distribute(PlannerInfo *root, JoinTreeItem *jtitem);
static void process_security_barrier_quals(PlannerInfo *root,
										   int rti, JoinTreeItem *jtitem);
static void mark_rels_nulled_by_join(PlannerInfo *root, Index ojrelid,
									 Relids lower_rels);
static SpecialJoinInfo *make_outerjoininfo(PlannerInfo *root,
										   Relids left_rels, Relids right_rels,
										   Relids inner_join_rels,
										   JoinType jointype, Index ojrelid,
										   List *clause);
static void compute_semijoin_info(PlannerInfo *root, SpecialJoinInfo *sjinfo,
								  List *clause);
static void deconstruct_distribute_oj_quals(PlannerInfo *root,
											List *jtitems,
											JoinTreeItem *jtitem);
static void distribute_quals_to_rels(PlannerInfo *root, List *clauses,
									 JoinTreeItem *jtitem,
									 SpecialJoinInfo *sjinfo,
									 Index security_level,
									 Relids qualscope,
									 Relids ojscope,
									 Relids outerjoin_nonnullable,
									 Relids incompatible_relids,
									 bool allow_equivalence,
									 bool has_clone,
									 bool is_clone,
									 List **postponed_oj_qual_list);
static void distribute_qual_to_rels(PlannerInfo *root, Node *clause,
									JoinTreeItem *jtitem,
									SpecialJoinInfo *sjinfo,
									Index security_level,
									Relids qualscope,
									Relids ojscope,
									Relids outerjoin_nonnullable,
									Relids incompatible_relids,
									bool allow_equivalence,
									bool has_clone,
									bool is_clone,
									List **postponed_oj_qual_list);
static bool check_redundant_nullability_qual(PlannerInfo *root, Node *clause);
static Relids get_join_domain_min_rels(PlannerInfo *root, Relids domain_relids);
static void check_mergejoinable(RestrictInfo *restrictinfo);
static void check_hashjoinable(RestrictInfo *restrictinfo);
static void check_memoizable(RestrictInfo *restrictinfo);


/*****************************************************************************
 *
 *	 JOIN TREES
 *
 *****************************************************************************/

/*
 * add_base_rels_to_query
 *
 *	  Scan the query's jointree and create baserel RelOptInfos for all
 *	  the base relations (e.g., table, subquery, and function RTEs)
 *	  appearing in the jointree.
 *
 * The initial invocation must pass root->parse->jointree as the value of
 * jtnode.  Internally, the function recurses through the jointree.
 *
 * At the end of this process, there should be one baserel RelOptInfo for
 * every non-join RTE that is used in the query.  Some of the baserels
 * may be appendrel parents, which will require additional "otherrel"
 * RelOptInfos for their member rels, but those are added later.
 */
/*
 * add_base_rels_to_query - (中文)递归扫描连接树,为所有基础关系创建 RelOptInfo
 *
 * 【作用】查询规划的第一步:遍历整个 jointree(由 RangeTblRef / FromExpr /
 * JoinExpr 三种节点组成的树),对每个 RangeTblRef 指向的非连接 RTE 调用
 * build_simple_rel() 创建对应的 RelOptInfo,并把其指针存入
 * root->simple_rel_array。由 planner() 在预处理器之后、构造目标列之前调用。
 *
 * 【设计思想】jointree 是 FROM 子句的结构化表示:RangeTblRef 是叶子(一个
 * RTE),FromExpr 表示"多个项的内连接"(f->fromlist),JoinExpr 表示一个显式
 * JOIN 节点。本函数只是按节点类型分类递归,对叶子节点建立关系信息。
 * 处理结束后,查询中"每个被使用的非 join RTE"都应有一个 baserel
 * RelOptInfo。注意:appendrel 父表(继承/分区)的子表 otherrel 此时还不建立,
 * 留待 add_other_rels_to_query() 处理。
 *
 * 【参数】
 *   root   —— 当前查询级的 PlannerInfo;
 *   jtnode —— 当前待处理的 jointree 节点,初始调用时必须是
 *             root->parse->jointree。
 * 【返回值】无。
 */
void
add_base_rels_to_query(PlannerInfo *root, Node *jtnode)
{
	if (jtnode == NULL)
		return;
	if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		(void) build_simple_rel(root, varno, NULL);
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		foreach(l, f->fromlist)
			add_base_rels_to_query(root, lfirst(l));
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		add_base_rels_to_query(root, j->larg);
		add_base_rels_to_query(root, j->rarg);
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
}

/*
 * add_other_rels_to_query
 *	  create "otherrel" RelOptInfos for the children of appendrel baserels
 *
 * At the end of this process, there should be RelOptInfos for all relations
 * that will be scanned by the query.
 */
/*
 * add_other_rels_to_query - (中文)为 appendrel(继承/分区)父表的子关系
 * 创建 "otherrel" RelOptInfo
 *
 * 【作用】在 add_base_rels_to_query() 之后调用:扫描 simple_rel_array,
 * 对每个标记了 rte->inh(可继承)的基础关系调用 expand_inherited_rtentry(),
 * 为其所有子表/分区建立 reloptkind 为 RELOPT_OTHER_MEMBER_REL 的 otherrel
 * RelOptInfo。处理完毕后,查询中所有可能被扫描的关系都具备了 RelOptInfo。
 *
 * 【设计思想】继承/分区表的每个子表虽然在执行时会作为独立扫描目标,但路径
 * 生成时要以父表为入口、在 Append/MergeAppend 下枚举子表,因此必须为子表
 * 单独建立 RelOptInfo 才能计算各自路径。本函数只关心 reloptkind ==
 * RELOPT_BASEREL 的父关系,跳过空洞槽位(非 baserel RTE)与已生成的
 * otherrel,避免重复展开。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无。
 */
void
add_other_rels_to_query(PlannerInfo *root)
{
	int			rti;

	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *rel = root->simple_rel_array[rti];
		RangeTblEntry *rte = root->simple_rte_array[rti];

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (rel == NULL)
			continue;

		/* Ignore any "otherrels" that were already added. */
		if (rel->reloptkind != RELOPT_BASEREL)
			continue;

		/* If it's marked as inheritable, look for children. */
		if (rte->inh)
			expand_inherited_rtentry(root, rel, rte, rti);
	}
}


/*****************************************************************************
 *
 *	 TARGET LISTS
 *
 *****************************************************************************/

/*
 * build_base_rel_tlists
 *	  Add targetlist entries for each var needed in the query's final tlist
 *	  (and HAVING clause, if any) to the appropriate base relations.
 *
 * We mark such vars as needed by "relation 0" to ensure that they will
 * propagate up through all join plan steps.
 */
/*
 * build_base_rel_tlists - (中文)把最终目标列与 HAVING 子句需要的 Var 加入
 * 各基础关系的 targetlist
 *
 * 【作用】扫描查询的最终目标列 final_tlist(以及存在时的 HAVING 子句),
 * 用 pull_var_clause() 抽出其中所有 Var 与 PlaceHolderVar,然后调用
 * add_vars_to_targetlist() 把每个 Var 登记到其所属基础关系
 * (rel->reltarget->exprs 与 rel->attr_needed)。由 planner() 在
 * deconstruct_jointree() 之前调用。
 *
 * 【设计思想】顶层目标列与 HAVING 中的列是最晚才被消费的,必须保证它们能
 * 一路从扫描节点向上传递到顶层计划节点。为此用 where_needed =
 * bms_make_singleton(0),即"关系 0"(伪关系)来标记这些 Var,只要
 * attr_needed 中包含了关系 0,计划树中每一层 join 都会继续带上该列。
 * 对 HAVING 用 PVC_RECURSE_AGGREGATES | PVC_INCLUDE_PLACEHOLDERS 递归聚合
 * 参数与占位符(HAVING 不会含 WindowFunc,故不递归 WindowFuncs)。
 *
 * 【参数】
 *   root       —— 当前查询级的 PlannerInfo;
 *   final_tlist —— 查询最终的目标列列表(processed_tlist)。
 * 【返回值】无。
 */
void
build_base_rel_tlists(PlannerInfo *root, List *final_tlist)
{
	List	   *tlist_vars = pull_var_clause((Node *) final_tlist,
											 PVC_RECURSE_AGGREGATES |
											 PVC_RECURSE_WINDOWFUNCS |
											 PVC_INCLUDE_PLACEHOLDERS);

	if (tlist_vars != NIL)
	{
		add_vars_to_targetlist(root, tlist_vars, bms_make_singleton(0));
		list_free(tlist_vars);
	}

	/*
	 * If there's a HAVING clause, we'll need the Vars it uses, too.  Note
	 * that HAVING can contain Aggrefs but not WindowFuncs.
	 */
	if (root->parse->havingQual)
	{
		List	   *having_vars = pull_var_clause(root->parse->havingQual,
												  PVC_RECURSE_AGGREGATES |
												  PVC_INCLUDE_PLACEHOLDERS);

		if (having_vars != NIL)
		{
			add_vars_to_targetlist(root, having_vars,
								   bms_make_singleton(0));
			list_free(having_vars);
		}
	}
}

/*
 * add_vars_to_targetlist
 *	  For each variable appearing in the list, add it to the owning
 *	  relation's targetlist if not already present, and mark the variable
 *	  as being needed for the indicated join (or for final output if
 *	  where_needed includes "relation 0").
 *
 *	  The list may also contain PlaceHolderVars.  These don't necessarily
 *	  have a single owning relation; we keep their attr_needed info in
 *	  root->placeholder_list instead.  Find or create the associated
 *	  PlaceHolderInfo entry, and update its ph_needed.
 *
 *	  See also add_vars_to_attr_needed.
 */
/*
 * add_vars_to_targetlist - (中文)把一组 Var/PlaceHolderVar 加入其所属关系
 * 的目标列,并标记需要它们的位置
 *
 * 【作用】对列表中的每个 Var:若其所属基础关系的 targetlist 里还没有这一列,
 * 则加入 rel->reltarget->exprs(此时去掉 varnullingrels,因为扫描层取值尚未
 * 被任何外连接置空),并把 where_needed 并入 rel->attr_needed[attno]。
 * 对 PlaceHolderVar:查找/创建对应的 PlaceHolderInfo,把 where_needed 并入其
 * ph_needed。由 build_base_rel_tlists()、extract_lateral_references()、
 * distribute_qual_to_rels()、process_implied_equality() 等多处调用。
 *
 * 【设计思想】"某个 Var 在何处被需要"信息存放在 attr_needed 中:它是按
 * 关系编号索引的 Bitmapset 数组,位 i 表示在编号 i 的连接(或最终输出)处
 * 需要该列。连接顺序搜索时据此判断列的向上传递路径。PlaceHolderVar 没有
 * 单一归属关系,故其需求单独存于 PlaceHolderInfo.ph_needed。若 where_needed
 * 已是该关系自身的 relids 子集(即仅关系内部使用),则无需任何标记。
 *
 * 【参数】
 *   root         —— 当前查询级的 PlannerInfo;
 *   vars         —— 待处理的 Var / PlaceHolderVar 节点列表;
 *   where_needed —— 一个非空 Relids 集合,指明这些值在哪些连接处被需要
 *                   (包含关系 0 表示顶层输出需要)。
 * 【返回值】无。
 */
void
add_vars_to_targetlist(PlannerInfo *root, List *vars,
					   Relids where_needed)
{
	ListCell   *temp;

	Assert(!bms_is_empty(where_needed));

	foreach(temp, vars)
	{
		Node	   *node = (Node *) lfirst(temp);

		if (IsA(node, Var))
		{
			Var		   *var = (Var *) node;
			RelOptInfo *rel = find_base_rel(root, var->varno);
			int			attno = var->varattno;

			if (bms_is_subset(where_needed, rel->relids))
				continue;
			Assert(attno >= rel->min_attr && attno <= rel->max_attr);
			attno -= rel->min_attr;
			if (rel->attr_needed[attno] == NULL)
			{
				/*
				 * Variable not yet requested, so add to rel's targetlist.
				 *
				 * The value available at the rel's scan level has not been
				 * nulled by any outer join, so drop its varnullingrels.
				 * (We'll put those back as we climb up the join tree.)
				 */
				var = copyObject(var);
				var->varnullingrels = NULL;
				rel->reltarget->exprs = lappend(rel->reltarget->exprs, var);
				/* reltarget cost and width will be computed later */
			}
			rel->attr_needed[attno] = bms_add_members(rel->attr_needed[attno],
													  where_needed);
		}
		else if (IsA(node, PlaceHolderVar))
		{
			PlaceHolderVar *phv = (PlaceHolderVar *) node;
			PlaceHolderInfo *phinfo = find_placeholder_info(root, phv);

			phinfo->ph_needed = bms_add_members(phinfo->ph_needed,
												where_needed);
		}
		else
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
	}
}

/*
 * add_vars_to_attr_needed
 *	  This does a subset of what add_vars_to_targetlist does: it just
 *	  updates attr_needed for Vars and ph_needed for PlaceHolderVars.
 *	  We assume the Vars are already in their relations' targetlists.
 *
 *	  This is used to rebuild attr_needed/ph_needed sets after removal
 *	  of a useless outer join.  The removed join clause might have been
 *	  the only upper-level use of some other relation's Var, in which
 *	  case we can reduce that Var's attr_needed and thereby possibly
 *	  open the door to further join removals.  But we can't tell that
 *	  without tedious reconstruction of the attr_needed data.
 *
 *	  Note that if a Var's attr_needed is successfully reduced to empty,
 *	  it will still be in the relation's targetlist even though we do
 *	  not really need the scan plan node to emit it.  The extra plan
 *	  inefficiency seems tiny enough to not be worth spending planner
 *	  cycles to get rid of it.
 */
/*
 * add_vars_to_attr_needed - (中文)只更新 Var/PlaceHolderVar 的需求集合
 * (attr_needed / ph_needed),不向 targetlist 添加新列
 *
 * 【作用】add_vars_to_targetlist() 的子集操作:假定列表中所有 Var 已经在
 * 其所属关系的 targetlist 中(由先前调用保证),此处仅把 where_needed 并入
 * 各 Var 的 rel->attr_needed 与各 PHV 的 phinfo->ph_needed。
 *
 * 【设计思想】当 analyzejoins.c 移除了一个无用外连接后,被移除的连接条件
 * 可能是某个 Var 的唯一上层使用点,因而需要重建 attr_needed/ph_needed 以便
 * 缩小需求、为后续进一步的连接移除创造条件。与 add_vars_to_targetlist
 * 不同的是本函数不复制节点也不改 targetlist——因为列已存在。若某 Var 的
 * attr_needed 被缩成空,它仍会留在 targetlist 中,只是多输出一列、开销极小,
 * 不值得为此消耗规划周期。
 *
 * 【参数】
 *   root         —— 当前查询级的 PlannerInfo;
 *   vars         —— 待处理节点列表(须已登记在 targetlist);
 *   where_needed —— 非空 Relids,指明这些值在哪些连接处被需要。
 * 【返回值】无。
 */
void
add_vars_to_attr_needed(PlannerInfo *root, List *vars,
						Relids where_needed)
{
	ListCell   *temp;

	Assert(!bms_is_empty(where_needed));

	foreach(temp, vars)
	{
		Node	   *node = (Node *) lfirst(temp);

		if (IsA(node, Var))
		{
			Var		   *var = (Var *) node;
			RelOptInfo *rel = find_base_rel(root, var->varno);
			int			attno = var->varattno;

			if (bms_is_subset(where_needed, rel->relids))
				continue;
			Assert(attno >= rel->min_attr && attno <= rel->max_attr);
			attno -= rel->min_attr;
			rel->attr_needed[attno] = bms_add_members(rel->attr_needed[attno],
													  where_needed);
		}
		else if (IsA(node, PlaceHolderVar))
		{
			PlaceHolderVar *phv = (PlaceHolderVar *) node;
			PlaceHolderInfo *phinfo = find_placeholder_info(root, phv);

			phinfo->ph_needed = bms_add_members(phinfo->ph_needed,
												where_needed);
		}
		else
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
	}
}

/*****************************************************************************
 *
 *	  GROUP BY
 *
 *****************************************************************************/

/*
 * remove_useless_groupby_columns
 *		Remove any columns in the GROUP BY clause that are redundant due to
 *		being functionally dependent on other GROUP BY columns.
 *
 * Since some other DBMSes do not allow references to ungrouped columns, it's
 * not unusual to find all columns listed in GROUP BY even though listing the
 * primary-key columns, or columns of a unique constraint would be sufficient.
 * Deleting such excess columns avoids redundant sorting or hashing work, so
 * it's worth doing.
 *
 * Relcache invalidations will ensure that cached plans become invalidated
 * when the underlying supporting indexes are dropped or if a column's NOT
 * NULL attribute is removed.
 */
/*
 * remove_useless_groupby_columns - (中文)删除因函数依赖而冗余的 GROUP BY 列
 *
 * 【作用】若 GROUP BY 中有多个列,且某关系存在一个"列集是这些分组列的
 * 真子集"的唯一索引,则由索引列即可唯一确定分组,其余列是函数依赖冗余,
 * 应把它们从 root->processed_groupClause 中移除,从而避免多余的排序/哈希。
 * 由 planner() 在目标列处理阶段调用。
 *
 * 【设计思想】
 * - 先扫 GROUP BY 收集各关系的分组列号(groupbyattnos)与分组列兼容信息
 *   (groupbycols,记录 attno、合并操作符族、排序规则);
 * - 再对每个普通基表扫描其索引:要求索引唯一、立即(非 deferrable)、无
 *   谓词、无表达式列,且各索引列均 NOT NULL(或索引声明 NULLS NOT
 *   DISTINCT),并且每个索引列的等值操作符与排序规则能在某个 GROUP BY
 *   项上找到一致匹配;
 * - 选取"列数最少"的满足条件的索引,用它覆盖的列作为保留集合,其余
 *   GROUP BY 项列为冗余(surplusvars);
 * - 重建 GROUP BY 列表,保留非 Var、外层 Var 与非冗余项。被剔除项的
 *   ressortgroupref 标记残留无害。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无。
 */
void
remove_useless_groupby_columns(PlannerInfo *root)
{
	Query	   *parse = root->parse;
	Bitmapset **groupbyattnos;
	List	  **groupbycols;
	Bitmapset **surplusvars;
	bool		tryremove = false;
	ListCell   *lc;
	int			relid;

	/* No chance to do anything if there are less than two GROUP BY items */
	if (list_length(root->processed_groupClause) < 2)
		return;

	/* Don't fiddle with the GROUP BY clause if the query has grouping sets */
	if (parse->groupingSets)
		return;

	/*
	 * Scan the GROUP BY clause to find GROUP BY items that are simple Vars.
	 * Fill groupbyattnos[k] with a bitmapset of the column attnos of RTE k
	 * that are GROUP BY items, and groupbycols[k] with a parallel list of
	 * GroupByColInfo records.  We need the latter so that, when checking a
	 * unique index against this rel's GROUP BY items, we can verify that the
	 * index's notion of equality agrees with at least one GROUP BY item per
	 * index column.
	 */
	groupbyattnos = palloc0_array(Bitmapset *, list_length(parse->rtable) + 1);
	groupbycols = palloc0_array(List *, list_length(parse->rtable) + 1);
	foreach(lc, root->processed_groupClause)
	{
		SortGroupClause *sgc = lfirst_node(SortGroupClause, lc);
		TargetEntry *tle = get_sortgroupclause_tle(sgc, parse->targetList);
		Var		   *var = (Var *) tle->expr;
		GroupByColInfo *info;

		/*
		 * Ignore non-Vars and Vars from other query levels.
		 *
		 * XXX in principle, stable expressions containing Vars could also be
		 * removed, if all the Vars are functionally dependent on other GROUP
		 * BY items.  But it's not clear that such cases occur often enough to
		 * be worth troubling over.
		 */
		if (!IsA(var, Var) ||
			var->varlevelsup > 0)
			continue;

		/* OK, remember we have this Var */
		relid = var->varno;
		Assert(relid <= list_length(parse->rtable));

		/*
		 * If this isn't the first column for this relation then we now have
		 * multiple columns.  That means there might be some that can be
		 * removed.
		 */
		tryremove |= !bms_is_empty(groupbyattnos[relid]);
		groupbyattnos[relid] = bms_add_member(groupbyattnos[relid],
											  var->varattno - FirstLowInvalidHeapAttributeNumber);

		info = palloc(sizeof(GroupByColInfo));
		info->attno = var->varattno;
		info->eq_opfamilies = get_mergejoin_opfamilies(sgc->eqop);
		info->coll = var->varcollid;
		groupbycols[relid] = lappend(groupbycols[relid], info);
	}

	/*
	 * No Vars or didn't find multiple Vars for any relation in the GROUP BY?
	 * If so, nothing can be removed, so don't waste more effort trying.
	 */
	if (!tryremove)
		return;

	/*
	 * Consider each relation and see if it is possible to remove some of its
	 * Vars from GROUP BY.  For simplicity and speed, we do the actual removal
	 * in a separate pass.  Here, we just fill surplusvars[k] with a bitmapset
	 * of the column attnos of RTE k that are removable GROUP BY items.
	 */
	surplusvars = NULL;			/* don't allocate array unless required */
	relid = 0;
	foreach(lc, parse->rtable)
	{
		RangeTblEntry *rte = lfirst_node(RangeTblEntry, lc);
		RelOptInfo *rel;
		Bitmapset  *relattnos;
		Bitmapset  *best_keycolumns = NULL;
		int32		best_nkeycolumns = PG_INT32_MAX;

		relid++;

		/* Only plain relations could have primary-key constraints */
		if (rte->rtekind != RTE_RELATION)
			continue;

		/*
		 * We must skip inheritance parent tables as some of the child rels
		 * may cause duplicate rows.  This cannot happen with partitioned
		 * tables, however.
		 */
		if (rte->inh && rte->relkind != RELKIND_PARTITIONED_TABLE)
			continue;

		/* Nothing to do unless this rel has multiple Vars in GROUP BY */
		relattnos = groupbyattnos[relid];
		if (bms_membership(relattnos) != BMS_MULTIPLE)
			continue;

		rel = root->simple_rel_array[relid];

		/*
		 * Now check each index for this relation to see if there are any with
		 * columns which are a proper subset of the grouping columns for this
		 * relation.
		 */
		foreach_node(IndexOptInfo, index, rel->indexlist)
		{
			Bitmapset  *ind_attnos;
			bool		index_check_ok;

			/*
			 * Skip any non-unique and deferrable indexes.  Predicate indexes
			 * have not been checked yet, so we must skip those too as the
			 * predOK check that's done later might fail.
			 */
			if (!index->unique || !index->immediate || index->indpred != NIL)
				continue;

			/* For simplicity, we currently don't support expression indexes */
			if (index->indexprs != NIL)
				continue;

			ind_attnos = NULL;
			index_check_ok = true;
			for (int i = 0; i < index->nkeycolumns; i++)
			{
				AttrNumber	indkey_attno = index->indexkeys[i];
				Oid			indkey_opfamily = index->opfamily[i];
				Oid			indkey_coll = index->indexcollations[i];
				ListCell   *lc2;

				/*
				 * We must insist that the index columns are all defined NOT
				 * NULL otherwise duplicate NULLs could exist.  However, we
				 * can relax this check when the index is defined with NULLS
				 * NOT DISTINCT as there can only be 1 NULL row, therefore
				 * functional dependency on the unique columns is maintained,
				 * despite the NULL.
				 */
				if (!index->nullsnotdistinct &&
					!bms_is_member(indkey_attno, rel->notnullattnums))
				{
					index_check_ok = false;
					break;
				}

				/*
				 * The index proves uniqueness only under its own opfamily and
				 * collation.  Require some GROUP BY item on this column to
				 * use a compatible eqop and collation, the same check
				 * relation_has_unique_index_for() applies to join clauses.
				 */
				foreach(lc2, groupbycols[relid])
				{
					GroupByColInfo *info = (GroupByColInfo *) lfirst(lc2);

					if (info->attno != indkey_attno)
						continue;
					if (list_member_oid(info->eq_opfamilies, indkey_opfamily) &&
						collations_agree_on_equality(indkey_coll, info->coll))
						break;
				}
				if (lc2 == NULL)
				{
					index_check_ok = false;
					break;
				}

				ind_attnos =
					bms_add_member(ind_attnos,
								   indkey_attno -
								   FirstLowInvalidHeapAttributeNumber);
			}

			if (!index_check_ok)
				continue;

			/*
			 * Skip any indexes where the indexed columns aren't a proper
			 * subset of the GROUP BY.
			 */
			if (bms_subset_compare(ind_attnos, relattnos) != BMS_SUBSET1)
				continue;

			/*
			 * Record the attribute numbers from the index with the fewest
			 * columns.  This allows the largest number of columns to be
			 * removed from the GROUP BY clause.  In the future, we may wish
			 * to consider using the narrowest set of columns and looking at
			 * pg_statistic.stawidth as it might be better to use an index
			 * with, say two INT4s, rather than, say, one long varlena column.
			 */
			if (index->nkeycolumns < best_nkeycolumns)
			{
				best_keycolumns = ind_attnos;
				best_nkeycolumns = index->nkeycolumns;
			}
		}

		/* Did we find a suitable index? */
		if (!bms_is_empty(best_keycolumns))
		{
			/*
			 * To easily remember whether we've found anything to do, we don't
			 * allocate the surplusvars[] array until we find something.
			 */
			if (surplusvars == NULL)
				surplusvars = palloc0_array(Bitmapset *, list_length(parse->rtable) + 1);

			/* Remember the attnos of the removable columns */
			surplusvars[relid] = bms_difference(relattnos, best_keycolumns);
		}
	}

	/*
	 * If we found any surplus Vars, build a new GROUP BY clause without them.
	 * (Note: this may leave some TLEs with unreferenced ressortgroupref
	 * markings, but that's harmless.)
	 */
	if (surplusvars != NULL)
	{
		List	   *new_groupby = NIL;

		foreach(lc, root->processed_groupClause)
		{
			SortGroupClause *sgc = lfirst_node(SortGroupClause, lc);
			TargetEntry *tle = get_sortgroupclause_tle(sgc, parse->targetList);
			Var		   *var = (Var *) tle->expr;

			/*
			 * New list must include non-Vars, outer Vars, and anything not
			 * marked as surplus.
			 */
			if (!IsA(var, Var) ||
				var->varlevelsup > 0 ||
				!bms_is_member(var->varattno - FirstLowInvalidHeapAttributeNumber,
							   surplusvars[var->varno]))
				new_groupby = lappend(new_groupby, sgc);
		}

		root->processed_groupClause = new_groupby;
	}
}

/*
 * setup_eager_aggregation
 *	  Check if eager aggregation is applicable, and if so collect suitable
 *	  aggregate expressions and grouping expressions in the query.
 */
/*
 * setup_eager_aggregation - (中文)检查"急切聚合"(把聚合下推到连接之下)
 * 是否可用,若可用则收集合适的聚合表达式与分组表达式
 *
 * 【作用】由 planner() 在 deconstruct_jointree() 之前调用。先用一连串快速
 * 检查排除不适用急切聚合的情况(如用户关闭开关、无 GROUP BY、分组集、
 * 有序/去重聚合、非 partial 聚合、SRF 目标列、单基表查询、聚合状态内存
 * 可能无界等),随后用 create_agg_clause_infos() 从 targetlist 与 havingQual
 * 收集 Aggref 与普通 Var,再用 create_grouping_expr_infos() 收集分组表达式,
 * 结果分别存于 root->agg_clause_list / root->tlist_vars / root->group_expr_list。
 *
 * 【设计思想】急切聚合是在 GROUP BY 列经过外连接侧保持"非空"时,把聚合放到
 * 连接之前(对连接输入先做部分聚合),大幅缩小连接输入规模。判断聚合能否下推、
 * 是否安全(等价于"相等必同像",防止丢失精度)由被收集的信息支撑;后续
 * setup_eager_agg_path() 才真正生成路径。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无。
 */
void
setup_eager_aggregation(PlannerInfo *root)
{
	/*
	 * Don't apply eager aggregation if disabled by user.
	 */
	if (!enable_eager_aggregate)
		return;

	/*
	 * Don't apply eager aggregation if there are no available GROUP BY
	 * clauses.
	 */
	if (!root->processed_groupClause)
		return;

	/*
	 * For now we don't try to support grouping sets.
	 */
	if (root->parse->groupingSets)
		return;

	/*
	 * For now we don't try to support DISTINCT or ORDER BY aggregates.
	 */
	if (root->numOrderedAggs > 0)
		return;

	/*
	 * If there are any aggregates that do not support partial mode, or any
	 * partial aggregates that are non-serializable, do not apply eager
	 * aggregation.
	 */
	if (root->hasNonPartialAggs || root->hasNonSerialAggs)
		return;

	/*
	 * We don't try to apply eager aggregation if there are set-returning
	 * functions in targetlist.
	 */
	if (root->parse->hasTargetSRFs)
		return;

	/*
	 * Eager aggregation only makes sense if there are multiple base rels in
	 * the query.
	 */
	if (bms_membership(root->all_baserels) != BMS_MULTIPLE)
		return;

	/*
	 * Don't apply eager aggregation if any aggregate poses a risk of
	 * excessive memory usage during partial aggregation.
	 */
	if (is_partial_agg_memory_risky(root))
		return;

	/*
	 * Collect aggregate expressions and plain Vars that appear in the
	 * targetlist and havingQual.
	 */
	create_agg_clause_infos(root);

	/*
	 * If there are no suitable aggregate expressions, we cannot apply eager
	 * aggregation.
	 */
	if (root->agg_clause_list == NIL)
		return;

	/*
	 * Collect grouping expressions that appear in grouping clauses.
	 */
	create_grouping_expr_infos(root);
}

/*
 * is_partial_agg_memory_risky
 *	  Check if any aggregate poses a risk of excessive memory usage during
 *	  partial aggregation.
 *
 * We check if any aggregate has a negative aggtransspace value, which
 * indicates that its transition state data can grow unboundedly in size.
 * Applying eager aggregation in such cases risks high memory usage since
 * partial aggregation results might be stored in join hash tables or
 * materialized nodes.
 */
/*
 * is_partial_agg_memory_risky - (中文)检查是否存在使部分聚合内存占用无界的聚合
 *
 * 【作用】遍历 root->aggtransinfos,只要发现某个聚合的 aggtransspace 为负
 * (表示其转移状态大小不可估量、可无限增长),即返回 true。
 *
 * 【设计思想】急切聚合会把部分聚合结果保存在 join 哈希表或物化节点中,
 * 若某个聚合的转移状态可无界增长(aggtransspace < 0),内存风险过高,应禁止
 * 急切聚合。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】任一聚合有内存风险则返回 true,否则 false。
 */
static bool
is_partial_agg_memory_risky(PlannerInfo *root)
{
	ListCell   *lc;

	foreach(lc, root->aggtransinfos)
	{
		AggTransInfo *transinfo = lfirst_node(AggTransInfo, lc);

		if (transinfo->aggtransspace < 0)
			return true;
	}

	return false;
}

/*
 * create_agg_clause_infos
 *	  Search the targetlist and havingQual for Aggrefs and plain Vars, and
 *	  create an AggClauseInfo for each Aggref node.
 */
/*
 * create_agg_clause_infos - (中文)在目标列与 HAVING 中搜索 Aggref 与普通 Var,
 * 为每个可下推的 Aggref 创建 AggClauseInfo
 *
 * 【作用】用 pull_var_clause() 抽出 targetlist(含 window func 递归)与
 * havingQual 中的聚合/Var/占位符,遍历处理:遇到 GroupingFunc、含 volatile
 * 函数的聚合、非 leakproof 聚合(存在 securityQuals 时)、或聚合引用了全部
 * 基表(无处可下推)等情况时,整体放弃急切聚合;否则为该聚合创建
 * AggClauseInfo(记录 aggref 与 agg_eval_at 涉及的关系集合)。结果存入
 * root->agg_clause_list 与 root->tlist_vars。
 *
 * 【设计思想】急切聚合要保证语义不变:volatile 函数在部分聚合时会减少求值
 * 次数、可能改变结果;安全级别下推要求聚合函数 leakproof,否则会绕过行级
 * 安全过滤把不该透露的中间结果暴露到 join 中。agg_eval_at 用于判断聚合涉及
 * 哪些关系,以便在正确的连接层次进行部分聚合。若中途失败则清空列表
 * (deep free)。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无,结果写入 root。
 */
static void
create_agg_clause_infos(PlannerInfo *root)
{
	List	   *tlist_exprs;
	List	   *agg_clause_list = NIL;
	List	   *tlist_vars = NIL;
	Relids		aggregate_relids = NULL;
	bool		eager_agg_applicable = true;
	ListCell   *lc;

	Assert(root->agg_clause_list == NIL);
	Assert(root->tlist_vars == NIL);

	tlist_exprs = pull_var_clause((Node *) root->processed_tlist,
								  PVC_INCLUDE_AGGREGATES |
								  PVC_RECURSE_WINDOWFUNCS |
								  PVC_RECURSE_PLACEHOLDERS);

	/*
	 * Aggregates within the HAVING clause need to be processed in the same
	 * way as those in the targetlist.  Note that HAVING can contain Aggrefs
	 * but not WindowFuncs.
	 */
	if (root->parse->havingQual != NULL)
	{
		List	   *having_exprs;

		having_exprs = pull_var_clause((Node *) root->parse->havingQual,
									   PVC_INCLUDE_AGGREGATES |
									   PVC_RECURSE_PLACEHOLDERS);
		if (having_exprs != NIL)
		{
			tlist_exprs = list_concat(tlist_exprs, having_exprs);
			list_free(having_exprs);
		}
	}

	foreach(lc, tlist_exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);
		Aggref	   *aggref;
		Relids		agg_eval_at;
		AggClauseInfo *ac_info;

		/* For now we don't try to support GROUPING() expressions */
		if (IsA(expr, GroupingFunc))
		{
			eager_agg_applicable = false;
			break;
		}

		/* Collect plain Vars for future reference */
		if (IsA(expr, Var))
		{
			tlist_vars = list_append_unique(tlist_vars, expr);
			continue;
		}

		aggref = castNode(Aggref, expr);

		Assert(aggref->aggorder == NIL);
		Assert(aggref->aggdistinct == NIL);

		/*
		 * We cannot push down aggregates that contain volatile functions.
		 * Doing so would change the number of times the function is
		 * evaluated.
		 */
		if (contain_volatile_functions((Node *) aggref))
		{
			eager_agg_applicable = false;
			break;
		}

		/*
		 * If there are any securityQuals, do not try to apply eager
		 * aggregation if any non-leakproof aggregate functions are present.
		 * This is overly strict, but for now...
		 */
		if (root->qual_security_level > 0 &&
			!get_func_leakproof(aggref->aggfnoid))
		{
			eager_agg_applicable = false;
			break;
		}

		agg_eval_at = pull_varnos(root, (Node *) aggref);

		/*
		 * If all base relations in the query are referenced by aggregate
		 * functions, then eager aggregation is not applicable.
		 */
		aggregate_relids = bms_add_members(aggregate_relids, agg_eval_at);
		if (bms_is_subset(root->all_baserels, aggregate_relids))
		{
			eager_agg_applicable = false;
			break;
		}

		/* OK, create the AggClauseInfo node */
		ac_info = makeNode(AggClauseInfo);
		ac_info->aggref = aggref;
		ac_info->agg_eval_at = agg_eval_at;

		/* ... and add it to the list */
		agg_clause_list = list_append_unique(agg_clause_list, ac_info);
	}

	list_free(tlist_exprs);

	if (eager_agg_applicable)
	{
		root->agg_clause_list = agg_clause_list;
		root->tlist_vars = tlist_vars;
	}
	else
	{
		list_free_deep(agg_clause_list);
		list_free(tlist_vars);
	}
}

/*
 * create_grouping_expr_infos
 *	  Create a GroupingExprInfo for each expression usable as grouping key.
 *
 * If any grouping expression is not suitable, we will just return with
 * root->group_expr_list being NIL.
 */
/*
 * create_grouping_expr_infos - (中文)为每个可作分组键的表达式创建
 * GroupingExprInfo
 *
 * 【作用】遍历 root->processed_groupClause,对每个分组项取出其 targetlist
 * 表达式。仅当表达式是普通 Var、类型有 btree 操作族、且其
 * BTEQUALIMAGE_PROC(等值即同像)过程返回真(以保证"等值分组"不丢失对上层
 * 条件必要的字节级信息)时,才把它收入候选;否则函数直接返回、使
 * group_expr_list 保持 NIL(表示急切聚合不可用)。最终为每个候选表达式构造
 * GroupingExprInfo(记录 expr 副本、sortgroupref 及所属等价类 ec)。
 *
 * 【设计思想】急切聚合的关键约束是"相等⇒同像":如 NUMERIC 的 0 与 0.0
 * 等值但字节不同,若被放入同一组,上层 quals 可能依赖被丢弃的精度。
 * BTEQUALIMAGE_PROC 正是检测该属性的标准接口,调用时须传递表达式实际
 * 排序规则,正确处理非确定性 collation。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无,候选结果写入 root->group_expr_list。
 */
static void
create_grouping_expr_infos(PlannerInfo *root)
{
	List	   *exprs = NIL;
	List	   *sortgrouprefs = NIL;
	List	   *ecs = NIL;
	ListCell   *lc,
			   *lc1,
			   *lc2,
			   *lc3;

	Assert(root->group_expr_list == NIL);

	foreach(lc, root->processed_groupClause)
	{
		SortGroupClause *sgc = lfirst_node(SortGroupClause, lc);
		TargetEntry *tle = get_sortgroupclause_tle(sgc, root->processed_tlist);
		TypeCacheEntry *tce;
		Oid			equalimageproc;

		Assert(tle->ressortgroupref > 0);

		/*
		 * For now we only support plain Vars as grouping expressions.
		 */
		if (!IsA(tle->expr, Var))
			return;

		/*
		 * Eager aggregation is only possible if equality implies image
		 * equality for each grouping key.  Otherwise, placing keys with
		 * different byte images into the same group may result in the loss of
		 * information that could be necessary to evaluate upper qual clauses.
		 *
		 * For instance, the NUMERIC data type is not supported, as values
		 * that are considered equal by the equality operator (e.g., 0 and
		 * 0.0) can have different scales.
		 */
		tce = lookup_type_cache(exprType((Node *) tle->expr),
								TYPECACHE_BTREE_OPFAMILY);
		if (!OidIsValid(tce->btree_opf) ||
			!OidIsValid(tce->btree_opintype))
			return;

		equalimageproc = get_opfamily_proc(tce->btree_opf,
										   tce->btree_opintype,
										   tce->btree_opintype,
										   BTEQUALIMAGE_PROC);

		/*
		 * If there is no BTEQUALIMAGE_PROC, eager aggregation is assumed to
		 * be unsafe.  Otherwise, we call the procedure to check.  We must be
		 * careful to pass the expression's actual collation, rather than the
		 * data type's default collation, to ensure that non-deterministic
		 * collations are correctly handled.
		 */
		if (!OidIsValid(equalimageproc) ||
			!DatumGetBool(OidFunctionCall1Coll(equalimageproc,
											   exprCollation((Node *) tle->expr),
											   ObjectIdGetDatum(tce->btree_opintype))))
			return;

		exprs = lappend(exprs, tle->expr);
		sortgrouprefs = lappend_int(sortgrouprefs, tle->ressortgroupref);
		ecs = lappend(ecs, get_eclass_for_sortgroupclause(root, sgc, tle->expr));
	}

	/*
	 * Construct a GroupingExprInfo for each expression.
	 */
	forthree(lc1, exprs, lc2, sortgrouprefs, lc3, ecs)
	{
		Expr	   *expr = (Expr *) lfirst(lc1);
		int			sortgroupref = lfirst_int(lc2);
		EquivalenceClass *ec = (EquivalenceClass *) lfirst(lc3);
		GroupingExprInfo *ge_info;

		ge_info = makeNode(GroupingExprInfo);
		ge_info->expr = (Expr *) copyObject(expr);
		ge_info->sortgroupref = sortgroupref;
		ge_info->ec = ec;

		root->group_expr_list = lappend(root->group_expr_list, ge_info);
	}
}

/*
 * get_eclass_for_sortgroupclause
 *	  Given a group clause and an expression, find an existing equivalence
 *	  class that the expression is a member of; return NULL if none.
 */
/*
 * get_eclass_for_sortgroupclause - (中文)根据分组子句与表达式查找其所属的
 * 现有等价类;无则返回 NULL
 *
 * 【作用】create_grouping_expr_infos() 的辅助函数:由分组子句的排序操作符
 * 得到操作族(opfamily)与输入类型,再取该操作族的等值操作符、由其得到完整
 * 的 mergejoin 操作族集合,最后委托 get_eclass_for_sort_expr() 查找/创建
 * 等价类。
 *
 * 【设计思想】SortGroupClause 只携带 sortop 而不携带 collation,排序规则须
 * 从表达式本身获取。等价类的操作族列表必须基于等值操作符所属的全部操作族
 * (一个等值操作符可同时属于多个 opfamily),故不能直接用 sortop 所在操作族。
 *
 * 【参数】
 *   root —— 当前查询级的 PlannerInfo;
 *   sgc  —— 分组/排序子句;
 *   expr —— 对应的分组表达式。
 * 【返回值】匹配的 EquivalenceClass;若分组子句不可排序则返回 NULL。
 */
static EquivalenceClass *
get_eclass_for_sortgroupclause(PlannerInfo *root, SortGroupClause *sgc,
							   Expr *expr)
{
	Oid			opfamily,
				opcintype,
				collation;
	CompareType cmptype;
	Oid			equality_op;
	List	   *opfamilies;

	/* Punt if the group clause is not sortable */
	if (!OidIsValid(sgc->sortop))
		return NULL;

	/* Find the operator in pg_amop --- failure shouldn't happen */
	if (!get_ordering_op_properties(sgc->sortop,
									&opfamily, &opcintype, &cmptype))
		elog(ERROR, "operator %u is not a valid ordering operator",
			 sgc->sortop);

	/* Because SortGroupClause doesn't carry collation, consult the expr */
	collation = exprCollation((Node *) expr);

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

	/* Now find a matching EquivalenceClass */
	return get_eclass_for_sort_expr(root, expr, opfamilies, opcintype,
									collation, sgc->tleSortGroupRef,
									NULL, false);
}

/*****************************************************************************
 *
 *	  LATERAL REFERENCES
 *
 *****************************************************************************/

/*
 * find_lateral_references
 *	  For each LATERAL subquery, extract all its references to Vars and
 *	  PlaceHolderVars of the current query level, and make sure those values
 *	  will be available for evaluation of the subquery.
 *
 * While later planning steps ensure that the Var/PHV source rels are on the
 * outside of nestloops relative to the LATERAL subquery, we also need to
 * ensure that the Vars/PHVs propagate up to the nestloop join level; this
 * means setting suitable where_needed values for them.
 *
 * Note that this only deals with lateral references in unflattened LATERAL
 * subqueries.  When we flatten a LATERAL subquery, its lateral references
 * become plain Vars in the parent query, but they may have to be wrapped in
 * PlaceHolderVars if they need to be forced NULL by outer joins that don't
 * also null the LATERAL subquery.  That's all handled elsewhere.
 *
 * This has to run before deconstruct_jointree, since it might result in
 * creation of PlaceHolderInfos.
 */
/*
 * find_lateral_references - (中文)为每个 LATERAL 子查询提取其对当前查询级
 * Var/PlaceHolderVar 的引用,并确保这些值在求值时可用
 *
 * 【作用】在 deconstruct_jointree() 之前运行:若查询含 LATERAL RTE,遍历所有
 * baserel(仅 RELOPT_BASEREL,忽略 otherrel),对每个 LATERAL 关系调用
 * extract_lateral_references() 提取其引用并把 where_needed 设为该 LATERAL
 * 关系本身,保证被引用的 Var/PHV 能传播到嵌套循环的连接层。
 *
 * 【设计思想】后续规划步骤会确保 Var/PHV 的源关系位于 LATERAL 子查询的外层
 * (nestloop 外侧),这里则需为它们设置合适的 where_needed 使其一路传到
 * nestloop join 层。仅处理未被扁平化的 LATERAL 子查询;被拉平后其引用成为
 * 普通 Var,必要时包进 PlaceHolderVar 的置空处理在别处完成。忽略 otherrel
 * 是因为继承/UNION ALL 拉平场景下规划以父表 relid 为准,父表 RTE 已含全部
 * 所需引用信息。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无。
 */
void
find_lateral_references(PlannerInfo *root)
{
	Index		rti;

	/* We need do nothing if the query contains no LATERAL RTEs */
	if (!root->hasLateralRTEs)
		return;

	/*
	 * Examine all baserels (the rel array has been set up by now).
	 */
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (brel == NULL)
			continue;

		Assert(brel->relid == rti); /* sanity check on array */

		/*
		 * This bit is less obvious than it might look.  We ignore appendrel
		 * otherrels and consider only their parent baserels.  In a case where
		 * a LATERAL-containing UNION ALL subquery was pulled up, it is the
		 * otherrel that is actually going to be in the plan.  However, we
		 * want to mark all its lateral references as needed by the parent,
		 * because it is the parent's relid that will be used for join
		 * planning purposes.  And the parent's RTE will contain all the
		 * lateral references we need to know, since the pulled-up member is
		 * nothing but a copy of parts of the original RTE's subquery.  We
		 * could visit the parent's children instead and transform their
		 * references back to the parent's relid, but it would be much more
		 * complicated for no real gain.  (Important here is that the child
		 * members have not yet received any processing beyond being pulled
		 * up.)  Similarly, in appendrels created by inheritance expansion,
		 * it's sufficient to look at the parent relation.
		 */

		/* ignore RTEs that are "other rels" */
		if (brel->reloptkind != RELOPT_BASEREL)
			continue;

		extract_lateral_references(root, brel, rti);
	}
}

/*
 * extract_lateral_references - (中文)提取单个 LATERAL 关系对外层 Var/PHV 的
 * 引用,调整层级并登记到源关系的 targetlist
 *
 * 【作用】find_lateral_references() 的辅助函数。根据 RTE 类型(RTE_RELATION
 * 的 tablesample、RTE_SUBQUERY 的 subquery、RTE_FUNCTION、RTE_TABLEFUNC、
 * RTE_VALUES)用 pull_vars_of_level() 抽出指定 levelsup(子查询为 1,其余
 * 为 0)的 Var/PHV;对每个引用做副本:Var 直接把 varlevelsup 清零,PHV 则用
 * IncrementVarSublevelsUp() 降级并(若来自子查询)对其 phexpr 执行
 * preprocess_phv_expression()。最后把 where_needed 设为 LATERAL RTE 自身的
 * relids,调用 add_vars_to_targetlist() 登记,并把结果保存到
 * brel->lateral_vars 供后续重建与连接信息计算使用。
 *
 * 【设计思想】"needed at LATERAL RTE"是一种取巧但正确的标记:形式化地应标记
 * 在 LATERAL RTE 与其源 RTE 的连接处,但统一标在 LATERAL RTE 上能保证在
 * 到达该连接时列必然已向上传递,且实现简单。PHV 调整比 Var 复杂,因其内部
 * 表达式也可能含子层引用。
 *
 * 【参数】
 *   root    —— 当前查询级的 PlannerInfo;
 *   brel    —— LATERAL 关系对应的 RelOptInfo;
 *   rtindex —— 该关系在 simple_rte_array 中的索引。
 * 【返回值】无。
 */
static void
extract_lateral_references(PlannerInfo *root, RelOptInfo *brel, Index rtindex)
{
	RangeTblEntry *rte = root->simple_rte_array[rtindex];
	List	   *vars;
	List	   *newvars;
	Relids		where_needed;
	ListCell   *lc;

	/* No cross-references are possible if it's not LATERAL */
	if (!rte->lateral)
		return;

	/* Fetch the appropriate variables */
	if (rte->rtekind == RTE_RELATION)
		vars = pull_vars_of_level((Node *) rte->tablesample, 0);
	else if (rte->rtekind == RTE_SUBQUERY)
		vars = pull_vars_of_level((Node *) rte->subquery, 1);
	else if (rte->rtekind == RTE_FUNCTION)
		vars = pull_vars_of_level((Node *) rte->functions, 0);
	else if (rte->rtekind == RTE_TABLEFUNC)
		vars = pull_vars_of_level((Node *) rte->tablefunc, 0);
	else if (rte->rtekind == RTE_VALUES)
		vars = pull_vars_of_level((Node *) rte->values_lists, 0);
	else
	{
		Assert(false);
		return;					/* keep compiler quiet */
	}

	if (vars == NIL)
		return;					/* nothing to do */

	/* Copy each Var (or PlaceHolderVar) and adjust it to match our level */
	newvars = NIL;
	foreach(lc, vars)
	{
		Node	   *node = (Node *) lfirst(lc);

		node = copyObject(node);
		if (IsA(node, Var))
		{
			Var		   *var = (Var *) node;

			/* Adjustment is easy since it's just one node */
			var->varlevelsup = 0;
		}
		else if (IsA(node, PlaceHolderVar))
		{
			PlaceHolderVar *phv = (PlaceHolderVar *) node;
			int			levelsup = phv->phlevelsup;

			/* Have to work harder to adjust the contained expression too */
			if (levelsup != 0)
				IncrementVarSublevelsUp(node, -levelsup, 0);

			/*
			 * If we pulled the PHV out of a subquery RTE, its expression
			 * needs to be preprocessed.  subquery_planner() already did this
			 * for level-zero PHVs in function and values RTEs, though.
			 */
			if (levelsup > 0)
				phv->phexpr = preprocess_phv_expression(root, phv->phexpr);
		}
		else
			Assert(false);
		newvars = lappend(newvars, node);
	}

	list_free(vars);

	/*
	 * We mark the Vars as being "needed" at the LATERAL RTE.  This is a bit
	 * of a cheat: a more formal approach would be to mark each one as needed
	 * at the join of the LATERAL RTE with its source RTE.  But it will work,
	 * and it's much less tedious than computing a separate where_needed for
	 * each Var.
	 */
	where_needed = bms_make_singleton(rtindex);

	/*
	 * Push Vars into their source relations' targetlists, and PHVs into
	 * root->placeholder_list.
	 */
	add_vars_to_targetlist(root, newvars, where_needed);

	/*
	 * Remember the lateral references for rebuild_lateral_attr_needed and
	 * create_lateral_join_info.
	 */
	brel->lateral_vars = newvars;
}

/*
 * rebuild_lateral_attr_needed
 *	  Put back attr_needed bits for Vars/PHVs needed for lateral references.
 *
 * This is used to rebuild attr_needed/ph_needed sets after removal of a
 * useless outer join.  It should match what find_lateral_references did,
 * except that we call add_vars_to_attr_needed not add_vars_to_targetlist.
 */
/*
 * rebuild_lateral_attr_needed - (中文)在删除无用外连接后,为 LATERAL 引用
 * 涉及的 Var/PHV 重建 attr_needed/ph_needed 位
 *
 * 【作用】效果与 find_lateral_references() 一致,但调用的是
 * add_vars_to_attr_needed() 而非 add_vars_to_targetlist():直接复用各 baserel
 * 已保存的 lateral_vars,把 where_needed(bms_make_singleton(rti))并入其
 * attr_needed / ph_needed。由 analyzejoins.c 在移除无用外连接后调用。
 *
 * 【设计思想】连接被移除后,某个 Var 原本由被删条件提供的上层需求消失,其
 * attr_needed 需要收缩,才可能让后续更激进的连接消除继续进行;而 LATERAL
 * 引用的需求始终存在,必须原样补回。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无。
 */
void
rebuild_lateral_attr_needed(PlannerInfo *root)
{
	Index		rti;

	/* We need do nothing if the query contains no LATERAL RTEs */
	if (!root->hasLateralRTEs)
		return;

	/* Examine the same baserels that find_lateral_references did */
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];
		Relids		where_needed;

		if (brel == NULL)
			continue;
		if (brel->reloptkind != RELOPT_BASEREL)
			continue;

		/*
		 * We don't need to repeat all of extract_lateral_references, since it
		 * kindly saved the extracted Vars/PHVs in lateral_vars.
		 */
		if (brel->lateral_vars == NIL)
			continue;

		where_needed = bms_make_singleton(rti);

		add_vars_to_attr_needed(root, brel->lateral_vars, where_needed);
	}
}

/*
 * create_lateral_join_info
 *	  Fill in the per-base-relation direct_lateral_relids, lateral_relids
 *	  and lateral_referencers sets.
 */
/*
 * create_lateral_join_info - (中文)计算每个基表的 direct_lateral_relids、
 * lateral_relids 与 lateral_referencers 集合
 *
 * 【作用】在 placeholdersFrozen 之后、连接规划之前调用。第一步:遍历所有
 * baserel,从其 lateral_vars 中直接收集被引用的 Var 的 varno 与 PHV 的
 * ph_eval_at,填入 direct_lateral_relids 与 lateral_relids。第二步:检查每个
 * 含横向引用(ph_lateral)的 PlaceHolderVar:求值点在单基表时,把其源关系
 * 并入该基表的 direct+lateral 集合;求值点是连接时,则仅并入各基表的
 * lateral_relids(间接依赖)。第三步:用 Warshall 算法求 lateral_relids 的
 * 传递闭包;第四步:构造反向映射,把"谁引用了我"写入各基表的
 * lateral_referencers。若无任何实际横向引用,把 hasLateralRTEs 复位以免
 * 后续做无用功。
 *
 * 【设计思想】direct vs indirect 区分:若 X 被置于 Y 的 nestloop 内侧,则 X
 * 的所有间接依赖(Z)也必须在外侧,故传递闭包必须存在;而 indirect(经由
 * join 求值点)不能直接把两表单独相接,只能靠连接顺序约束满足。外连接
 * (eval_at 中的 OJ 伪 relid)不进入求值点集合,避免连接顺序重排后失效。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无,各 RelOptInfo 的字段被填充。
 */
void
create_lateral_join_info(PlannerInfo *root)
{
	bool		found_laterals = false;
	Index		rti;
	ListCell   *lc;

	/* We need do nothing if the query contains no LATERAL RTEs */
	if (!root->hasLateralRTEs)
		return;

	/* We'll need to have the ph_eval_at values for PlaceHolderVars */
	Assert(root->placeholdersFrozen);

	/*
	 * Examine all baserels (the rel array has been set up by now).
	 */
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];
		Relids		lateral_relids;

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (brel == NULL)
			continue;

		Assert(brel->relid == rti); /* sanity check on array */

		/* ignore RTEs that are "other rels" */
		if (brel->reloptkind != RELOPT_BASEREL)
			continue;

		lateral_relids = NULL;

		/* consider each laterally-referenced Var or PHV */
		foreach(lc, brel->lateral_vars)
		{
			Node	   *node = (Node *) lfirst(lc);

			if (IsA(node, Var))
			{
				Var		   *var = (Var *) node;

				found_laterals = true;
				lateral_relids = bms_add_member(lateral_relids,
												var->varno);
			}
			else if (IsA(node, PlaceHolderVar))
			{
				PlaceHolderVar *phv = (PlaceHolderVar *) node;
				PlaceHolderInfo *phinfo = find_placeholder_info(root, phv);

				found_laterals = true;
				lateral_relids = bms_add_members(lateral_relids,
												 phinfo->ph_eval_at);
			}
			else
				Assert(false);
		}

		/* We now have all the simple lateral refs from this rel */
		brel->direct_lateral_relids = lateral_relids;
		brel->lateral_relids = bms_copy(lateral_relids);
	}

	/*
	 * Now check for lateral references within PlaceHolderVars, and mark their
	 * eval_at rels as having lateral references to the source rels.
	 *
	 * For a PHV that is due to be evaluated at a baserel, mark its source(s)
	 * as direct lateral dependencies of the baserel (adding onto the ones
	 * recorded above).  If it's due to be evaluated at a join, mark its
	 * source(s) as indirect lateral dependencies of each baserel in the join,
	 * ie put them into lateral_relids but not direct_lateral_relids.  This is
	 * appropriate because we can't put any such baserel on the outside of a
	 * join to one of the PHV's lateral dependencies, but on the other hand we
	 * also can't yet join it directly to the dependency.
	 */
	foreach(lc, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(lc);
		Relids		eval_at = phinfo->ph_eval_at;
		Relids		lateral_refs;
		int			varno;

		if (phinfo->ph_lateral == NULL)
			continue;			/* PHV is uninteresting if no lateral refs */

		found_laterals = true;

		/*
		 * Include only baserels not outer joins in the evaluation sites'
		 * lateral relids.  This avoids problems when outer join order gets
		 * rearranged, and it should still ensure that the lateral values are
		 * available when needed.
		 */
		lateral_refs = bms_intersect(phinfo->ph_lateral, root->all_baserels);
		Assert(!bms_is_empty(lateral_refs));

		if (bms_get_singleton_member(eval_at, &varno))
		{
			/* Evaluation site is a baserel */
			RelOptInfo *brel = find_base_rel(root, varno);

			brel->direct_lateral_relids =
				bms_add_members(brel->direct_lateral_relids,
								lateral_refs);
			brel->lateral_relids =
				bms_add_members(brel->lateral_relids,
								lateral_refs);
		}
		else
		{
			/* Evaluation site is a join */
			varno = -1;
			while ((varno = bms_next_member(eval_at, varno)) >= 0)
			{
				RelOptInfo *brel = find_base_rel_ignore_join(root, varno);

				if (brel == NULL)
					continue;	/* ignore outer joins in eval_at */
				brel->lateral_relids = bms_add_members(brel->lateral_relids,
													   lateral_refs);
			}
		}
	}

	/*
	 * If we found no actual lateral references, we're done; but reset the
	 * hasLateralRTEs flag to avoid useless work later.
	 */
	if (!found_laterals)
	{
		root->hasLateralRTEs = false;
		return;
	}

	/*
	 * Calculate the transitive closure of the lateral_relids sets, so that
	 * they describe both direct and indirect lateral references.  If relation
	 * X references Y laterally, and Y references Z laterally, then we will
	 * have to scan X on the inside of a nestloop with Z, so for all intents
	 * and purposes X is laterally dependent on Z too.
	 *
	 * This code is essentially Warshall's algorithm for transitive closure.
	 * The outer loop considers each baserel, and propagates its lateral
	 * dependencies to those baserels that have a lateral dependency on it.
	 */
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];
		Relids		outer_lateral_relids;
		Index		rti2;

		if (brel == NULL || brel->reloptkind != RELOPT_BASEREL)
			continue;

		/* need not consider baserel further if it has no lateral refs */
		outer_lateral_relids = brel->lateral_relids;
		if (outer_lateral_relids == NULL)
			continue;

		/* else scan all baserels */
		for (rti2 = 1; rti2 < root->simple_rel_array_size; rti2++)
		{
			RelOptInfo *brel2 = root->simple_rel_array[rti2];

			if (brel2 == NULL || brel2->reloptkind != RELOPT_BASEREL)
				continue;

			/* if brel2 has lateral ref to brel, propagate brel's refs */
			if (bms_is_member(rti, brel2->lateral_relids))
				brel2->lateral_relids = bms_add_members(brel2->lateral_relids,
														outer_lateral_relids);
		}
	}

	/*
	 * Now that we've identified all lateral references, mark each baserel
	 * with the set of relids of rels that reference it laterally (possibly
	 * indirectly) --- that is, the inverse mapping of lateral_relids.
	 */
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];
		Relids		lateral_relids;
		int			rti2;

		if (brel == NULL || brel->reloptkind != RELOPT_BASEREL)
			continue;

		/* Nothing to do at rels with no lateral refs */
		lateral_relids = brel->lateral_relids;
		if (bms_is_empty(lateral_relids))
			continue;

		/* No rel should have a lateral dependency on itself */
		Assert(!bms_is_member(rti, lateral_relids));

		/* Mark this rel's referencees */
		rti2 = -1;
		while ((rti2 = bms_next_member(lateral_relids, rti2)) >= 0)
		{
			RelOptInfo *brel2 = root->simple_rel_array[rti2];

			if (brel2 == NULL)
				continue;		/* must be an OJ */

			Assert(brel2->reloptkind == RELOPT_BASEREL);
			brel2->lateral_referencers =
				bms_add_member(brel2->lateral_referencers, rti);
		}
	}
}


/*****************************************************************************
 *
 *	  JOIN TREE PROCESSING
 *
 *****************************************************************************/

/*
 * deconstruct_jointree
 *	  Recursively scan the query's join tree for WHERE and JOIN/ON qual
 *	  clauses, and add these to the appropriate restrictinfo and joininfo
 *	  lists belonging to base RelOptInfos.  Also, add SpecialJoinInfo nodes
 *	  to root->join_info_list for any outer joins appearing in the query tree.
 *	  Return a "joinlist" data structure showing the join order decisions
 *	  that need to be made by make_one_rel().
 *
 * The "joinlist" result is a list of items that are either RangeTblRef
 * jointree nodes or sub-joinlists.  All the items at the same level of
 * joinlist must be joined in an order to be determined by make_one_rel()
 * (note that legal orders may be constrained by SpecialJoinInfo nodes).
 * A sub-joinlist represents a subproblem to be planned separately. Currently
 * sub-joinlists arise only from FULL OUTER JOIN or when collapsing of
 * subproblems is stopped by join_collapse_limit or from_collapse_limit.
 */
/*
 * deconstruct_jointree - (中文)递归扫描查询连接树,分发 WHERE 与 JOIN/ON
 * 条件到限制/连接列表,并为外连接建立 SpecialJoinInfo,返回连接顺序决策表
 *
 * 【作用】由 planner() 在目标列建立之后调用,是连接条件加工的中枢。整体分
 * 三遍完成:
 *   1) 置 placeholdersFrozen(此后不得再创建 PlaceHolderInfo),取顶层
 *      JoinDomain,调用 deconstruct_recurse() 深度优先遍历 jointree,为每个
 *      节点建立 JoinTreeItem 加入 item_list(深搜顺序),同时累积
 *      all_baserels、outer_join_rels、为外连接分配 JoinDomain;
 *   2) 对每个 JoinTreeItem 调用 deconstruct_distribute() 把条件分发到
 *      baserestrictinfo / joininfo,并生成/注册各外连接的 SpecialJoinInfo;
 *   3) 若存在被推迟的可交换左连接条件(oj_joinclauses),调用
 *      deconstruct_distribute_oj_quals() 做第三遍处理。
 * 最后释放 item_list 并返回 root->joinlist。
 *
 * 【返回值语义】返回的 "joinlist" 是嵌套列表:元素要么是 RangeTblRef
 * jointree 节点,要么是子 joinlist。同一层级的项必须由 make_one_rel() 决定
 * 连接顺序(合法顺序受 SpecialJoinInfo 约束);子 joinlist 代表需单独规划
 * 的子问题(目前仅 FULL OUTER JOIN 或超过 join_collapse_limit /
 * from_collapse_limit 时产生)。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】joinlist,见上述语义。
 */
List *
deconstruct_jointree(PlannerInfo *root)
{
	List	   *result;
	JoinDomain *top_jdomain;
	List	   *item_list = NIL;
	ListCell   *lc;

	/*
	 * After this point, no more PlaceHolderInfos may be made, because
	 * make_outerjoininfo requires all active placeholders to be present in
	 * root->placeholder_list while we crawl up the join tree.
	 */
	root->placeholdersFrozen = true;

	/* Fetch the already-created top-level join domain for the query */
	top_jdomain = linitial_node(JoinDomain, root->join_domains);
	top_jdomain->jd_relids = NULL;	/* filled during deconstruct_recurse */

	/* Start recursion at top of jointree */
	Assert(root->parse->jointree != NULL &&
		   IsA(root->parse->jointree, FromExpr));

	/* These are filled as we scan the jointree */
	root->all_baserels = NULL;
	root->outer_join_rels = NULL;

	/* Perform the initial scan of the jointree */
	result = deconstruct_recurse(root, (Node *) root->parse->jointree,
								 top_jdomain, NULL,
								 &item_list);

	/* Now we can form the value of all_query_rels, too */
	root->all_query_rels = bms_union(root->all_baserels, root->outer_join_rels);

	/* ... which should match what we computed for the top join domain */
	Assert(bms_equal(root->all_query_rels, top_jdomain->jd_relids));

	/* Now scan all the jointree nodes again, and distribute quals */
	foreach(lc, item_list)
	{
		JoinTreeItem *jtitem = (JoinTreeItem *) lfirst(lc);

		deconstruct_distribute(root, jtitem);
	}

	/*
	 * If there were any special joins then we may have some postponed LEFT
	 * JOIN clauses to deal with.
	 */
	if (root->join_info_list)
	{
		foreach(lc, item_list)
		{
			JoinTreeItem *jtitem = (JoinTreeItem *) lfirst(lc);

			if (jtitem->oj_joinclauses != NIL)
				deconstruct_distribute_oj_quals(root, item_list, jtitem);
		}
	}

	/* Don't need the JoinTreeItems any more */
	list_free_deep(item_list);

	return result;
}

/*
 * deconstruct_recurse
 *	  One recursion level of deconstruct_jointree's initial jointree scan.
 *
 * jtnode is the jointree node to examine, and parent_domain is the
 * enclosing join domain.  (We must add all base+OJ relids appearing
 * here or below to parent_domain.)  parent_jtitem is the JoinTreeItem
 * for the parent jointree node, or NULL at the top of the recursion.
 *
 * item_list is an in/out parameter: we add a JoinTreeItem struct to
 * that list for each jointree node, in depth-first traversal order.
 * (Hence, after each call, the last list item corresponds to its jtnode.)
 *
 * Return value is the appropriate joinlist for this jointree node.
 */
/*
 * deconstruct_recurse - (中文)deconstruct_jointree 初始扫描的每一层递归
 *
 * 【作用】按节点类型递归处理 jointree,同时完成:
 * - 为当前节点创建 JoinTreeItem(palloc0_object,先不入 item_list,结束时
 *   按深度优先顺序追加),记录 jti_parent;
 * - RangeTblRef(叶子):把 varno 加入 root->all_baserels 与 parent_domain 的
 *   jd_relids,设置 qualscope 为单元素集合,inner_join_rels 为空;
 * - FromExpr:所有子节点属于 parent_domain,递归处理子节点并拼接 joinlist
 *   (不超过 from_collapse_limit 时折叠子问题,单元素子问题总是折叠);
 * - JoinExpr:按连接类型处理——INNER/SEMI 属于 parent_domain;LEFT/ANTI
 *   为 RHS 新建 JoinDomain(child_domain)并把自身 relids(含 rtindex)并入
 *   parent_domain;FULL 为自身 ON 条件新建专属 fj_domain 且左右各建独立
 *   child_domain,自身 relids 同时并入父域。同时更新 outer_join_rels、
 *   调用 mark_rels_nulled_by_join() 记录被置空的关系,计算每个域的
 *   jd_relids 以及 left_rels / right_rels / nonnullable_rels。
 * - 依 join_collapse_limit 折叠/分隔输出 joinlist(FULL 强制精确顺序)。
 *
 * 【设计思想】JoinDomain 把"条件可自由重排的连接"划为一个域:域内条件可
 * 下推重排,跨域不可。LEFT/ANTI 的 RHS 条件与 JOIN ON 必须留在 RHS 域内
 * (防止条件错误地下推到外连接外侧),故为 RHS 单独建域;FULL 的 ON 条件
 * 则更需要完全独立的域。这些域约束将在 deconstruct_distribute() 及后续
 * 等价类/伪常量处理中被遵守。
 *
 * 【参数】
 *   root          —— 当前查询级的 PlannerInfo;
 *   jtnode        —— 当前待处理的 jointree 节点;
 *   parent_domain —— 本节点所属的外层 JoinDomain;
 *   parent_jtitem —— 父节点的 JoinTreeItem(顶层为 NULL);
 *   item_list     —— 入/出参数,按深度优先顺序累积 JoinTreeItem。
 * 【返回值】本节点的 joinlist(见 deconstruct_jointree 的语义)。
 */
static List *
deconstruct_recurse(PlannerInfo *root, Node *jtnode,
					JoinDomain *parent_domain,
					JoinTreeItem *parent_jtitem,
					List **item_list)
{
	List	   *joinlist;
	JoinTreeItem *jtitem;

	Assert(jtnode != NULL);

	/* Make the new JoinTreeItem, but don't add it to item_list yet */
	jtitem = palloc0_object(JoinTreeItem);
	jtitem->jtnode = jtnode;
	jtitem->jti_parent = parent_jtitem;

	if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		/* Fill all_baserels as we encounter baserel jointree nodes */
		root->all_baserels = bms_add_member(root->all_baserels, varno);
		/* This node belongs to parent_domain */
		jtitem->jdomain = parent_domain;
		parent_domain->jd_relids = bms_add_member(parent_domain->jd_relids,
												  varno);
		/* qualscope is just the one RTE */
		jtitem->qualscope = bms_make_singleton(varno);
		/* A single baserel does not create an inner join */
		jtitem->inner_join_rels = NULL;
		joinlist = list_make1(jtnode);
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		int			remaining;
		ListCell   *l;

		/* This node belongs to parent_domain, as do its children */
		jtitem->jdomain = parent_domain;

		/*
		 * Recurse to handle child nodes, and compute output joinlist.  We
		 * collapse subproblems into a single joinlist whenever the resulting
		 * joinlist wouldn't exceed from_collapse_limit members.  Also, always
		 * collapse one-element subproblems, since that won't lengthen the
		 * joinlist anyway.
		 */
		jtitem->qualscope = NULL;
		jtitem->inner_join_rels = NULL;
		joinlist = NIL;
		remaining = list_length(f->fromlist);
		foreach(l, f->fromlist)
		{
			JoinTreeItem *sub_item;
			List	   *sub_joinlist;
			int			sub_members;

			sub_joinlist = deconstruct_recurse(root, lfirst(l),
											   parent_domain,
											   jtitem,
											   item_list);
			sub_item = (JoinTreeItem *) llast(*item_list);
			jtitem->qualscope = bms_add_members(jtitem->qualscope,
												sub_item->qualscope);
			jtitem->inner_join_rels = sub_item->inner_join_rels;
			sub_members = list_length(sub_joinlist);
			remaining--;
			if (sub_members <= 1 ||
				list_length(joinlist) + sub_members + remaining <= from_collapse_limit)
				joinlist = list_concat(joinlist, sub_joinlist);
			else
				joinlist = lappend(joinlist, sub_joinlist);
		}

		/*
		 * A FROM with more than one list element is an inner join subsuming
		 * all below it, so we should report inner_join_rels = qualscope. If
		 * there was exactly one element, we should (and already did) report
		 * whatever its inner_join_rels were.  If there were no elements (is
		 * that still possible?) the initialization before the loop fixed it.
		 */
		if (list_length(f->fromlist) > 1)
			jtitem->inner_join_rels = jtitem->qualscope;
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;
		JoinDomain *child_domain,
				   *fj_domain;
		JoinTreeItem *left_item,
				   *right_item;
		List	   *leftjoinlist,
				   *rightjoinlist;

		switch (j->jointype)
		{
			case JOIN_INNER:
				/* This node belongs to parent_domain, as do its children */
				jtitem->jdomain = parent_domain;
				/* Recurse */
				leftjoinlist = deconstruct_recurse(root, j->larg,
												   parent_domain,
												   jtitem,
												   item_list);
				left_item = (JoinTreeItem *) llast(*item_list);
				rightjoinlist = deconstruct_recurse(root, j->rarg,
													parent_domain,
													jtitem,
													item_list);
				right_item = (JoinTreeItem *) llast(*item_list);
				/* Compute qualscope etc */
				jtitem->qualscope = bms_union(left_item->qualscope,
											  right_item->qualscope);
				jtitem->inner_join_rels = jtitem->qualscope;
				jtitem->left_rels = left_item->qualscope;
				jtitem->right_rels = right_item->qualscope;
				/* Inner join adds no restrictions for quals */
				jtitem->nonnullable_rels = NULL;
				break;
			case JOIN_LEFT:
			case JOIN_ANTI:
				/* Make new join domain for my quals and the RHS */
				child_domain = makeNode(JoinDomain);
				child_domain->jd_relids = NULL; /* filled by recursion */
				root->join_domains = lappend(root->join_domains, child_domain);
				jtitem->jdomain = child_domain;
				/* Recurse */
				leftjoinlist = deconstruct_recurse(root, j->larg,
												   parent_domain,
												   jtitem,
												   item_list);
				left_item = (JoinTreeItem *) llast(*item_list);
				rightjoinlist = deconstruct_recurse(root, j->rarg,
													child_domain,
													jtitem,
													item_list);
				right_item = (JoinTreeItem *) llast(*item_list);
				/* Compute join domain contents, qualscope etc */
				parent_domain->jd_relids =
					bms_add_members(parent_domain->jd_relids,
									child_domain->jd_relids);
				jtitem->qualscope = bms_union(left_item->qualscope,
											  right_item->qualscope);
				/* caution: ANTI join derived from SEMI will lack rtindex */
				if (j->rtindex != 0)
				{
					parent_domain->jd_relids =
						bms_add_member(parent_domain->jd_relids,
									   j->rtindex);
					jtitem->qualscope = bms_add_member(jtitem->qualscope,
													   j->rtindex);
					root->outer_join_rels = bms_add_member(root->outer_join_rels,
														   j->rtindex);
					mark_rels_nulled_by_join(root, j->rtindex,
											 right_item->qualscope);
				}
				jtitem->inner_join_rels = bms_union(left_item->inner_join_rels,
													right_item->inner_join_rels);
				jtitem->left_rels = left_item->qualscope;
				jtitem->right_rels = right_item->qualscope;
				jtitem->nonnullable_rels = left_item->qualscope;
				break;
			case JOIN_SEMI:
				/* This node belongs to parent_domain, as do its children */
				jtitem->jdomain = parent_domain;
				/* Recurse */
				leftjoinlist = deconstruct_recurse(root, j->larg,
												   parent_domain,
												   jtitem,
												   item_list);
				left_item = (JoinTreeItem *) llast(*item_list);
				rightjoinlist = deconstruct_recurse(root, j->rarg,
													parent_domain,
													jtitem,
													item_list);
				right_item = (JoinTreeItem *) llast(*item_list);
				/* Compute qualscope etc */
				jtitem->qualscope = bms_union(left_item->qualscope,
											  right_item->qualscope);
				/* SEMI join never has rtindex, so don't add to anything */
				Assert(j->rtindex == 0);
				jtitem->inner_join_rels = bms_union(left_item->inner_join_rels,
													right_item->inner_join_rels);
				jtitem->left_rels = left_item->qualscope;
				jtitem->right_rels = right_item->qualscope;
				/* Semi join adds no restrictions for quals */
				jtitem->nonnullable_rels = NULL;
				break;
			case JOIN_FULL:
				/* The FULL JOIN's quals need their very own domain */
				fj_domain = makeNode(JoinDomain);
				root->join_domains = lappend(root->join_domains, fj_domain);
				jtitem->jdomain = fj_domain;
				/* Recurse, giving each side its own join domain */
				child_domain = makeNode(JoinDomain);
				child_domain->jd_relids = NULL; /* filled by recursion */
				root->join_domains = lappend(root->join_domains, child_domain);
				leftjoinlist = deconstruct_recurse(root, j->larg,
												   child_domain,
												   jtitem,
												   item_list);
				left_item = (JoinTreeItem *) llast(*item_list);
				fj_domain->jd_relids = bms_copy(child_domain->jd_relids);
				child_domain = makeNode(JoinDomain);
				child_domain->jd_relids = NULL; /* filled by recursion */
				root->join_domains = lappend(root->join_domains, child_domain);
				rightjoinlist = deconstruct_recurse(root, j->rarg,
													child_domain,
													jtitem,
													item_list);
				right_item = (JoinTreeItem *) llast(*item_list);
				/* Compute qualscope etc */
				fj_domain->jd_relids = bms_add_members(fj_domain->jd_relids,
													   child_domain->jd_relids);
				parent_domain->jd_relids = bms_add_members(parent_domain->jd_relids,
														   fj_domain->jd_relids);
				jtitem->qualscope = bms_union(left_item->qualscope,
											  right_item->qualscope);
				Assert(j->rtindex != 0);
				parent_domain->jd_relids = bms_add_member(parent_domain->jd_relids,
														  j->rtindex);
				jtitem->qualscope = bms_add_member(jtitem->qualscope,
												   j->rtindex);
				root->outer_join_rels = bms_add_member(root->outer_join_rels,
													   j->rtindex);
				mark_rels_nulled_by_join(root, j->rtindex,
										 left_item->qualscope);
				mark_rels_nulled_by_join(root, j->rtindex,
										 right_item->qualscope);
				jtitem->inner_join_rels = bms_union(left_item->inner_join_rels,
													right_item->inner_join_rels);
				jtitem->left_rels = left_item->qualscope;
				jtitem->right_rels = right_item->qualscope;
				/* each side is both outer and inner */
				jtitem->nonnullable_rels = jtitem->qualscope;
				break;
			default:
				/* JOIN_RIGHT was eliminated during reduce_outer_joins() */
				elog(ERROR, "unrecognized join type: %d",
					 (int) j->jointype);
				leftjoinlist = rightjoinlist = NIL; /* keep compiler quiet */
				break;
		}

		/*
		 * Compute the output joinlist.  We fold subproblems together except
		 * at a FULL JOIN or where join_collapse_limit would be exceeded.
		 */
		if (j->jointype == JOIN_FULL)
		{
			/* force the join order exactly at this node */
			joinlist = list_make1(list_make2(leftjoinlist, rightjoinlist));
		}
		else if (list_length(leftjoinlist) + list_length(rightjoinlist) <=
				 join_collapse_limit)
		{
			/* OK to combine subproblems */
			joinlist = list_concat(leftjoinlist, rightjoinlist);
		}
		else
		{
			/* can't combine, but needn't force join order above here */
			Node	   *leftpart,
					   *rightpart;

			/* avoid creating useless 1-element sublists */
			if (list_length(leftjoinlist) == 1)
				leftpart = (Node *) linitial(leftjoinlist);
			else
				leftpart = (Node *) leftjoinlist;
			if (list_length(rightjoinlist) == 1)
				rightpart = (Node *) linitial(rightjoinlist);
			else
				rightpart = (Node *) rightjoinlist;
			joinlist = list_make2(leftpart, rightpart);
		}
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
		joinlist = NIL;			/* keep compiler quiet */
	}

	/* Finally, we can add the new JoinTreeItem to item_list */
	*item_list = lappend(*item_list, jtitem);

	return joinlist;
}

/*
 * deconstruct_distribute
 *	  Process one jointree node in phase 2 of deconstruct_jointree processing.
 *
 * Distribute quals of the node to appropriate restriction and join lists.
 * In addition, entries will be added to root->join_info_list for outer joins.
 */
/*
 * deconstruct_distribute - (中文)deconstruct_jointree 第二遍:处理一个
 * jointree 节点,分发其条件并登记外连接
 *
 * 【作用】对每个 JoinTreeItem:
 * - RangeTblRef:若存在安全隔离条件(qual_security_level > 0),调用
 *   process_security_barrier_quals() 处理 RTE 上的 securityQuals;
 * - FromExpr:先把子节点推迟上来的 lateral_clauses、再处理本层 top-level
 *   quals,均委托 distribute_quals_to_rels() 分发;
 * - JoinExpr:合并本层推迟的 lateral_clauses 与 j->quals 作为 my_quals;对
 *   非内连接先用 make_outerjoininfo() 构造 SpecialJoinInfo(存于
 *   jtitem->sjinfo),并计算 ojscope(SEMI 特例为 NULL);对 lhs_strict 的
 *   LEFT JOIN 把非退化连接条件推迟到 oj_joinclauses(补回被移除的
 *   commute_below relids 以通过 ojscope 交叉检查);最后用
 *   distribute_quals_to_rels() 分发 my_quals,并把 SpecialJoinInfo 加入
 *   root->join_info_list。
 *
 * 【设计思想】条件推迟(oj_joinclauses)服务于连接恒等式 3 的交换:当左连接
 * 的 ON 条件对 LHS 严格(lhs_strict)时,该左连接可能与另一个左连接交换,
 * 故其非退化条件应推迟到第三遍重新决策放置位置;退化条件(只依赖左侧)会
 * 自然下坠无需推迟。
 *
 * 【参数】
 *   root    —— 当前查询级的 PlannerInfo;
 *   jtitem  —— 本遍要处理的 JoinTreeItem。
 * 【返回值】无。
 */
static void
deconstruct_distribute(PlannerInfo *root, JoinTreeItem *jtitem)
{
	Node	   *jtnode = jtitem->jtnode;

	if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		/* Deal with any securityQuals attached to the RTE */
		if (root->qual_security_level > 0)
			process_security_barrier_quals(root,
										   varno,
										   jtitem);
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;

		/*
		 * Process any lateral-referencing quals that were postponed to this
		 * level by children.
		 */
		distribute_quals_to_rels(root, jtitem->lateral_clauses,
								 jtitem,
								 NULL,
								 root->qual_security_level,
								 jtitem->qualscope,
								 NULL, NULL, NULL,
								 true, false, false,
								 NULL);

		/*
		 * Now process the top-level quals.
		 */
		distribute_quals_to_rels(root, (List *) f->quals,
								 jtitem,
								 NULL,
								 root->qual_security_level,
								 jtitem->qualscope,
								 NULL, NULL, NULL,
								 true, false, false,
								 NULL);
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;
		Relids		ojscope;
		List	   *my_quals;
		SpecialJoinInfo *sjinfo;
		List	  **postponed_oj_qual_list;

		/*
		 * Include lateral-referencing quals postponed from children in
		 * my_quals, so that they'll be handled properly in
		 * make_outerjoininfo.  (This is destructive to
		 * jtitem->lateral_clauses, but we won't use that again.)
		 */
		my_quals = list_concat(jtitem->lateral_clauses,
							   (List *) j->quals);

		/*
		 * For an OJ, form the SpecialJoinInfo now, so that we can pass it to
		 * distribute_qual_to_rels.  We must compute its ojscope too.
		 *
		 * Semijoins are a bit of a hybrid: we build a SpecialJoinInfo, but we
		 * want ojscope = NULL for distribute_qual_to_rels.
		 */
		if (j->jointype != JOIN_INNER)
		{
			sjinfo = make_outerjoininfo(root,
										jtitem->left_rels,
										jtitem->right_rels,
										jtitem->inner_join_rels,
										j->jointype,
										j->rtindex,
										my_quals);
			jtitem->sjinfo = sjinfo;
			if (j->jointype == JOIN_SEMI)
				ojscope = NULL;
			else
				ojscope = bms_union(sjinfo->min_lefthand,
									sjinfo->min_righthand);
		}
		else
		{
			sjinfo = NULL;
			ojscope = NULL;
		}

		/*
		 * If it's a left join with a join clause that is strict for the LHS,
		 * then we need to postpone handling of any non-degenerate join
		 * clauses, in case the join is able to commute with another left join
		 * per identity 3.  (Degenerate clauses need not be postponed, since
		 * they will drop down below this join anyway.)
		 */
		if (j->jointype == JOIN_LEFT && sjinfo->lhs_strict)
		{
			postponed_oj_qual_list = &jtitem->oj_joinclauses;

			/*
			 * Add back any commutable lower OJ relids that were removed from
			 * min_lefthand or min_righthand, else the ojscope cross-check in
			 * distribute_qual_to_rels will complain.  Since we are postponing
			 * processing of non-degenerate clauses, this addition doesn't
			 * affect anything except that cross-check.  Real clause
			 * positioning decisions will be made later, when we revisit the
			 * postponed clauses.
			 */
			ojscope = bms_add_members(ojscope, sjinfo->commute_below_l);
			ojscope = bms_add_members(ojscope, sjinfo->commute_below_r);
		}
		else
			postponed_oj_qual_list = NULL;

		/* Process the JOIN's qual clauses */
		distribute_quals_to_rels(root, my_quals,
								 jtitem,
								 sjinfo,
								 root->qual_security_level,
								 jtitem->qualscope,
								 ojscope, jtitem->nonnullable_rels,
								 NULL,	/* incompatible_relids */
								 true,	/* allow_equivalence */
								 false, false,	/* not clones */
								 postponed_oj_qual_list);

		/* And add the SpecialJoinInfo to join_info_list */
		if (sjinfo)
			root->join_info_list = lappend(root->join_info_list, sjinfo);
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
	}
}

/*
 * process_security_barrier_quals
 *	  Transfer security-barrier quals into relation's baserestrictinfo list.
 *
 * The rewriter put any relevant security-barrier conditions into the RTE's
 * securityQuals field, but it's now time to copy them into the rel's
 * baserestrictinfo.
 *
 * In inheritance cases, we only consider quals attached to the parent rel
 * here; they will be valid for all children too, so it's okay to consider
 * them for purposes like equivalence class creation.  Quals attached to
 * individual child rels will be dealt with during path creation.
 */
/*
 * process_security_barrier_quals - (中文)把安全屏障条件(securityQuals)转移
 * 到关系的 baserestrictinfo
 *
 * 【作用】重写器已把相关安全屏障条件放入 RTE 的 securityQuals 字段,现在把它们
 * 复制进该关系(以 rti 标识)的 baserestrictinfo。securityQuals 是隐式 AND
 * 的子列表列表:同一子列表内所有条件同一安全级别,后续子列表级别递增
 * (security_level 从 0 起逐次加一)。
 *
 * 【设计思想】ojscope 取qualscope 而非更合理的 NULL 是一种"作弊":其唯一效果
 * 是强制"无 Var 条件"在该关系处求值而非上推到树顶,这正是安全屏障需要的
 * (不能把 RLS 条件提到可被绕过的位置)。继承场景只考虑挂在父表上的条件,
 * 它们对所有子表同样有效,可用于等价类等;子表自身的条件在路径生成期处理。
 *
 * 【参数】
 *   root   —— 当前查询级的 PlannerInfo;
 *   rti    —— 基础关系的 RTE 索引;
 *   jtitem —— 该关系所属的 JoinTreeItem(提供 qualscope)。
 * 【返回值】无。
 */
static void
process_security_barrier_quals(PlannerInfo *root,
							   int rti, JoinTreeItem *jtitem)
{
	RangeTblEntry *rte = root->simple_rte_array[rti];
	Index		security_level = 0;
	ListCell   *lc;

	/*
	 * Each element of the securityQuals list has been preprocessed into an
	 * implicitly-ANDed list of clauses.  All the clauses in a given sublist
	 * should get the same security level, but successive sublists get higher
	 * levels.
	 */
	foreach(lc, rte->securityQuals)
	{
		List	   *qualset = (List *) lfirst(lc);

		/*
		 * We cheat to the extent of passing ojscope = qualscope rather than
		 * its more logical value of NULL.  The only effect this has is to
		 * force a Var-free qual to be evaluated at the rel rather than being
		 * pushed up to top of tree, which we don't want.
		 */
		distribute_quals_to_rels(root, qualset,
								 jtitem,
								 NULL,
								 security_level,
								 jtitem->qualscope,
								 jtitem->qualscope,
								 NULL,
								 NULL,
								 true,
								 false, false,	/* not clones */
								 NULL);
		security_level++;
	}

	/* Assert that qual_security_level is higher than anything we just used */
	Assert(security_level <= root->qual_security_level);
}

/*
 * mark_rels_nulled_by_join
 *	  Fill RelOptInfo.nulling_relids of baserels nulled by this outer join
 *
 * Inputs:
 *	ojrelid: RT index of the join RTE (must not be 0)
 *	lower_rels: the base+OJ Relids syntactically below nullable side of join
 */
/*
 * mark_rels_nulled_by_join - (中文)为被本外连接置空(放到 nullable 侧)的
 * 基础关系填充 RelOptInfo.nulling_relids
 *
 * 【作用】遍历 lower_rels(该外连接 nullable 侧语法下属的所有 base+OJ relids),
 * 对每个基础关系在其 nulling_relids 中加入 ojrelid,表示"当这个外连接丢弃
 * 一行时,该关系会被置空"。由 deconstruct_recurse() 在遍历 LEFT/FULL join
 * 时调用(LEFT 只标记 RHS,FULL 两侧都标记)。
 *
 * 【设计思想】nulling_relids 是现代 PostgreSQL(14+ 引入,替代老式
 * nullable_relids 语义)用于执行期 varnullingrels 与 PlaceHolderVar 置空计算
 * 的基础:上层在引用被置空关系的列时,需据此在 Var 上标注
 * varnullingrels,以便 EvalPlanQual / 外连接下推等场景正确判断空值。忽略
 * RTE_GROUP 特殊 RTE;遇到 OJ 伪 relid 时跳过(外连接本身不在此列)。
 *
 * 【参数】
 *   root       —— 当前查询级的 PlannerInfo;
 *   ojrelid    —— 外连接 RTE 的 RT 索引(不能为 0);
 *   lower_rels —— nullable 侧语法下属的 base+OJ Relids。
 * 【返回值】无。
 */
static void
mark_rels_nulled_by_join(PlannerInfo *root, Index ojrelid,
						 Relids lower_rels)
{
	int			relid = -1;

	while ((relid = bms_next_member(lower_rels, relid)) > 0)
	{
		RelOptInfo *rel = root->simple_rel_array[relid];

		/* ignore the RTE_GROUP RTE */
		if (relid == root->group_rtindex)
			continue;

		if (rel == NULL)		/* must be an outer join */
		{
			Assert(bms_is_member(relid, root->outer_join_rels));
			continue;
		}
		rel->nulling_relids = bms_add_member(rel->nulling_relids, ojrelid);
	}
}

/*
 * make_outerjoininfo
 *	  Build a SpecialJoinInfo for the current outer join
 *
 * Inputs:
 *	left_rels: the base+OJ Relids syntactically on outer side of join
 *	right_rels: the base+OJ Relids syntactically on inner side of join
 *	inner_join_rels: base+OJ Relids participating in inner joins below this one
 *	jointype: what it says (must always be LEFT, FULL, SEMI, or ANTI)
 *	ojrelid: RT index of the join RTE (0 for SEMI, which isn't in the RT list)
 *	clause: the outer join's join condition (in implicit-AND format)
 *
 * The node should eventually be appended to root->join_info_list, but we
 * do not do that here.
 *
 * Note: we assume that this function is invoked bottom-up, so that
 * root->join_info_list already contains entries for all outer joins that are
 * syntactically below this one.
 */
/*
 * make_outerjoininfo - (中文)为当前外连接构建 SpecialJoinInfo,计算其最小
 * 左右侧集合、严格性与可交换性约束
 *
 * 【作用】由 deconstruct_distribute() 对每个非内连接(LEFT/FULL/SEMI/ANTI)
 * 自底向上调用。核心步骤:
 * 1) 检查 FOR [KEY] UPDATE/SHARE 是否落到外连接 nullable 侧,若是则报错
 *    (执行器不支持在 nullable 侧做行锁定;解析器信息不足,只能在此发现);
 * 2) 填入 syn_lefthand/syn_righthand/jointype/ojrelid,初始化可交换字段;
 * 3) 调用 compute_semijoin_info() 分析半/反连接内部连接信息;FULL JOIN
 *    特例直接取左右语法的完整集合、lhs_strict 置 false;
 * 4) 计算 clause_relids 与 strict_relids(find_nonnullable_rels),
 *    lhs_strict 表示条件对任一 LHS 关系严格;
 * 5) min_lefthand = 条件涉及 ∩ 语法 LHS;min_righthand = (条件涉及 ∪
 *    下层 inner_join_rels) ∩ 语法 RHS(把下层内连接并入以禁止与它们交换);
 * 6) 遍历已存在的下层外连接,维护连接顺序约束:遇到 FULL JOIN 作为屏障把
 *    整个 FULL join 扩展进 min_lefthand/min_righthand;遇到含不安全 PHV、
 *    SEMI/ANTI 或条件不严格的 LHS 下层 OJ 时保留顺序(把其语法集合并入
 *    min_lefthand);满足外连接恒等式 3 时把下层 ojrelid 从 min_lefthand
 *    移除以允许交换;RHS 侧遇到外连接时同样并入 min_righthand。
 *
 * 【设计思想】SpecialJoinInfo 决定连接顺序搜索的合法性。min_lefthand/
 * min_righthand 分别表示"本外连接之前必须已完成的集合";commute_below_l/r
 * 记录允许交换的下层外连接;恒等式 3(A LEFT JOIN B LEFT JOIN C,当 ON 对 B
 * 严格且不涉及 A 时,A 可与 B 交换)是连接树重排的重要理论依据。PHV 的不
 * 安全性:若条件引用了必须在某下层外连接之上求值的 PlaceHolderVar,则不得
 * 与它交换。
 *
 * 【参数】
 *   root            —— 当前查询级的 PlannerInfo;
 *   left_rels       —— 连接外侧语法上的 base+OJ Relids;
 *   right_rels      —— 连接内侧语法上的 base+OJ Relids;
 *   inner_join_rels —— 本连接之下参与内连接的 base+OJ Relids;
 *   jointype        —— JOIN_LEFT/FULL/SEMI/ANTI 之一;
 *   ojrelid         —— 外连接 RTE 的 RT 索引(SEMI 为 0);
 *   clause          —— 外连接的连接条件(隐式 AND 格式)。
 * 【返回值】新建的 SpecialJoinInfo(不加入 join_info_list,由调用者加入)。
 */
static SpecialJoinInfo *
make_outerjoininfo(PlannerInfo *root,
				   Relids left_rels, Relids right_rels,
				   Relids inner_join_rels,
				   JoinType jointype, Index ojrelid,
				   List *clause)
{
	SpecialJoinInfo *sjinfo = makeNode(SpecialJoinInfo);
	Relids		clause_relids;
	Relids		strict_relids;
	Relids		min_lefthand;
	Relids		min_righthand;
	Relids		commute_below_l;
	Relids		commute_below_r;
	ListCell   *l;

	/*
	 * We should not see RIGHT JOIN here because left/right were switched
	 * earlier
	 */
	Assert(jointype != JOIN_INNER);
	Assert(jointype != JOIN_RIGHT);

	/*
	 * Presently the executor cannot support FOR [KEY] UPDATE/SHARE marking of
	 * rels appearing on the nullable side of an outer join. (It's somewhat
	 * unclear what that would mean, anyway: what should we mark when a result
	 * row is generated from no element of the nullable relation?)	So,
	 * complain if any nullable rel is FOR [KEY] UPDATE/SHARE.
	 *
	 * You might be wondering why this test isn't made far upstream in the
	 * parser.  It's because the parser hasn't got enough info --- consider
	 * FOR UPDATE applied to a view.  Only after rewriting and flattening do
	 * we know whether the view contains an outer join.
	 *
	 * We use the original RowMarkClause list here; the PlanRowMark list would
	 * list everything.
	 */
	foreach(l, root->parse->rowMarks)
	{
		RowMarkClause *rc = (RowMarkClause *) lfirst(l);

		if (bms_is_member(rc->rti, right_rels) ||
			(jointype == JOIN_FULL && bms_is_member(rc->rti, left_rels)))
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			/*------
			 translator: %s is a SQL row locking clause such as FOR UPDATE */
					 errmsg("%s cannot be applied to the nullable side of an outer join",
							LCS_asString(rc->strength))));
	}

	sjinfo->syn_lefthand = left_rels;
	sjinfo->syn_righthand = right_rels;
	sjinfo->jointype = jointype;
	sjinfo->ojrelid = ojrelid;
	/* these fields may get added to later: */
	sjinfo->commute_above_l = NULL;
	sjinfo->commute_above_r = NULL;
	sjinfo->commute_below_l = NULL;
	sjinfo->commute_below_r = NULL;

	compute_semijoin_info(root, sjinfo, clause);

	/* If it's a full join, no need to be very smart */
	if (jointype == JOIN_FULL)
	{
		sjinfo->min_lefthand = bms_copy(left_rels);
		sjinfo->min_righthand = bms_copy(right_rels);
		sjinfo->lhs_strict = false; /* don't care about this */
		return sjinfo;
	}

	/*
	 * Retrieve all relids mentioned within the join clause.
	 */
	clause_relids = pull_varnos(root, (Node *) clause);

	/*
	 * For which relids is the clause strict, ie, it cannot succeed if the
	 * rel's columns are all NULL?
	 */
	strict_relids = find_nonnullable_rels((Node *) clause);

	/* Remember whether the clause is strict for any LHS relations */
	sjinfo->lhs_strict = bms_overlap(strict_relids, left_rels);

	/*
	 * Required LHS always includes the LHS rels mentioned in the clause. We
	 * may have to add more rels based on lower outer joins; see below.
	 */
	min_lefthand = bms_intersect(clause_relids, left_rels);

	/*
	 * Similarly for required RHS.  But here, we must also include any lower
	 * inner joins, to ensure we don't try to commute with any of them.
	 */
	min_righthand = bms_int_members(bms_union(clause_relids, inner_join_rels),
									right_rels);

	/*
	 * Now check previous outer joins for ordering restrictions.
	 *
	 * commute_below_l and commute_below_r accumulate the relids of lower
	 * outer joins that we think this one can commute with.  These decisions
	 * are just tentative within this loop, since we might find an
	 * intermediate outer join that prevents commutation.  Surviving relids
	 * will get merged into the SpecialJoinInfo structs afterwards.
	 */
	commute_below_l = commute_below_r = NULL;
	foreach(l, root->join_info_list)
	{
		SpecialJoinInfo *otherinfo = (SpecialJoinInfo *) lfirst(l);
		bool		have_unsafe_phvs;

		/*
		 * A full join is an optimization barrier: we can't associate into or
		 * out of it.  Hence, if it overlaps either LHS or RHS of the current
		 * rel, expand that side's min relset to cover the whole full join.
		 */
		if (otherinfo->jointype == JOIN_FULL)
		{
			Assert(otherinfo->ojrelid != 0);
			if (bms_overlap(left_rels, otherinfo->syn_lefthand) ||
				bms_overlap(left_rels, otherinfo->syn_righthand))
			{
				min_lefthand = bms_add_members(min_lefthand,
											   otherinfo->syn_lefthand);
				min_lefthand = bms_add_members(min_lefthand,
											   otherinfo->syn_righthand);
				min_lefthand = bms_add_member(min_lefthand,
											  otherinfo->ojrelid);
			}
			if (bms_overlap(right_rels, otherinfo->syn_lefthand) ||
				bms_overlap(right_rels, otherinfo->syn_righthand))
			{
				min_righthand = bms_add_members(min_righthand,
												otherinfo->syn_lefthand);
				min_righthand = bms_add_members(min_righthand,
												otherinfo->syn_righthand);
				min_righthand = bms_add_member(min_righthand,
											   otherinfo->ojrelid);
			}
			/* Needn't do anything else with the full join */
			continue;
		}

		/*
		 * If our join condition contains any PlaceHolderVars that need to be
		 * evaluated above the lower OJ, then we can't commute with it.
		 */
		if (otherinfo->ojrelid != 0)
			have_unsafe_phvs =
				contain_placeholder_references_to(root,
												  (Node *) clause,
												  otherinfo->ojrelid);
		else
			have_unsafe_phvs = false;

		/*
		 * For a lower OJ in our LHS, if our join condition uses the lower
		 * join's RHS and is not strict for that rel, we must preserve the
		 * ordering of the two OJs, so add lower OJ's full syntactic relset to
		 * min_lefthand.  (We must use its full syntactic relset, not just its
		 * min_lefthand + min_righthand.  This is because there might be other
		 * OJs below this one that this one can commute with, but we cannot
		 * commute with them if we don't with this one.)  Also, if we have
		 * unsafe PHVs or the current join is a semijoin or antijoin, we must
		 * preserve ordering regardless of strictness.
		 *
		 * Note: I believe we have to insist on being strict for at least one
		 * rel in the lower OJ's min_righthand, not its whole syn_righthand.
		 *
		 * When we don't need to preserve ordering, check to see if outer join
		 * identity 3 applies, and if so, remove the lower OJ's ojrelid from
		 * our min_lefthand so that commutation is allowed.
		 */
		if (bms_overlap(left_rels, otherinfo->syn_righthand))
		{
			if (bms_overlap(clause_relids, otherinfo->syn_righthand) &&
				(have_unsafe_phvs ||
				 jointype == JOIN_SEMI || jointype == JOIN_ANTI ||
				 !bms_overlap(strict_relids, otherinfo->min_righthand)))
			{
				/* Preserve ordering */
				min_lefthand = bms_add_members(min_lefthand,
											   otherinfo->syn_lefthand);
				min_lefthand = bms_add_members(min_lefthand,
											   otherinfo->syn_righthand);
				if (otherinfo->ojrelid != 0)
					min_lefthand = bms_add_member(min_lefthand,
												  otherinfo->ojrelid);
			}
			else if (jointype == JOIN_LEFT &&
					 otherinfo->jointype == JOIN_LEFT &&
					 bms_overlap(strict_relids, otherinfo->min_righthand) &&
					 !bms_overlap(clause_relids, otherinfo->syn_lefthand))
			{
				/* Identity 3 applies, so remove the ordering restriction */
				min_lefthand = bms_del_member(min_lefthand, otherinfo->ojrelid);
				/* Record the (still tentative) commutability relationship */
				commute_below_l =
					bms_add_member(commute_below_l, otherinfo->ojrelid);
			}
		}

		/*
		 * For a lower OJ in our RHS, if our join condition does not use the
		 * lower join's RHS and the lower OJ's join condition is strict, we
		 * can interchange the ordering of the two OJs; otherwise we must add
		 * the lower OJ's full syntactic relset to min_righthand.
		 *
		 * Also, if our join condition does not use the lower join's LHS
		 * either, force the ordering to be preserved.  Otherwise we can end
		 * up with SpecialJoinInfos with identical min_righthands, which can
		 * confuse join_is_legal (see discussion in backend/optimizer/README).
		 *
		 * Also, we must preserve ordering anyway if we have unsafe PHVs, or
		 * if either this join or the lower OJ is a semijoin or antijoin.
		 *
		 * When we don't need to preserve ordering, check to see if outer join
		 * identity 3 applies, and if so, remove the lower OJ's ojrelid from
		 * our min_righthand so that commutation is allowed.
		 */
		if (bms_overlap(right_rels, otherinfo->syn_righthand))
		{
			if (bms_overlap(clause_relids, otherinfo->syn_righthand) ||
				!bms_overlap(clause_relids, otherinfo->min_lefthand) ||
				have_unsafe_phvs ||
				jointype == JOIN_SEMI ||
				jointype == JOIN_ANTI ||
				otherinfo->jointype == JOIN_SEMI ||
				otherinfo->jointype == JOIN_ANTI ||
				!otherinfo->lhs_strict)
			{
				/* Preserve ordering */
				min_righthand = bms_add_members(min_righthand,
												otherinfo->syn_lefthand);
				min_righthand = bms_add_members(min_righthand,
												otherinfo->syn_righthand);
				if (otherinfo->ojrelid != 0)
					min_righthand = bms_add_member(min_righthand,
												   otherinfo->ojrelid);
			}
			else if (jointype == JOIN_LEFT &&
					 otherinfo->jointype == JOIN_LEFT &&
					 otherinfo->lhs_strict)
			{
				/* Identity 3 applies, so remove the ordering restriction */
				min_righthand = bms_del_member(min_righthand,
											   otherinfo->ojrelid);
				/* Record the (still tentative) commutability relationship */
				commute_below_r =
					bms_add_member(commute_below_r, otherinfo->ojrelid);
			}
		}
	}

	/*
	 * Examine PlaceHolderVars.  If a PHV is supposed to be evaluated within
	 * this join's nullable side, then ensure that min_righthand contains the
	 * full eval_at set of the PHV.  This ensures that the PHV actually can be
	 * evaluated within the RHS.  Note that this works only because we should
	 * already have determined the final eval_at level for any PHV
	 * syntactically within this join.
	 */
	foreach(l, root->placeholder_list)
	{
		PlaceHolderInfo *phinfo = (PlaceHolderInfo *) lfirst(l);
		Relids		ph_syn_level = phinfo->ph_var->phrels;

		/* Ignore placeholder if it didn't syntactically come from RHS */
		if (!bms_is_subset(ph_syn_level, right_rels))
			continue;

		/* Else, prevent join from being formed before we eval the PHV */
		min_righthand = bms_add_members(min_righthand, phinfo->ph_eval_at);
	}

	/*
	 * If we found nothing to put in min_lefthand, punt and make it the full
	 * LHS, to avoid having an empty min_lefthand which will confuse later
	 * processing. (We don't try to be smart about such cases, just correct.)
	 * Likewise for min_righthand.
	 */
	if (bms_is_empty(min_lefthand))
		min_lefthand = bms_copy(left_rels);
	if (bms_is_empty(min_righthand))
		min_righthand = bms_copy(right_rels);

	/* Now they'd better be nonempty */
	Assert(!bms_is_empty(min_lefthand));
	Assert(!bms_is_empty(min_righthand));
	/* Shouldn't overlap either */
	Assert(!bms_overlap(min_lefthand, min_righthand));

	sjinfo->min_lefthand = min_lefthand;
	sjinfo->min_righthand = min_righthand;

	/*
	 * Now that we've identified the correct min_lefthand and min_righthand,
	 * any commute_below_l or commute_below_r relids that have not gotten
	 * added back into those sets (due to intervening outer joins) are indeed
	 * commutable with this one.
	 *
	 * First, delete any subsequently-added-back relids (this is easier than
	 * maintaining commute_below_l/r precisely through all the above).
	 */
	commute_below_l = bms_del_members(commute_below_l, min_lefthand);
	commute_below_r = bms_del_members(commute_below_r, min_righthand);

	/* Anything left? */
	if (commute_below_l || commute_below_r)
	{
		/* Yup, so we must update the derived data in the SpecialJoinInfos */
		sjinfo->commute_below_l = commute_below_l;
		sjinfo->commute_below_r = commute_below_r;
		foreach(l, root->join_info_list)
		{
			SpecialJoinInfo *otherinfo = (SpecialJoinInfo *) lfirst(l);

			if (bms_is_member(otherinfo->ojrelid, commute_below_l))
				otherinfo->commute_above_l =
					bms_add_member(otherinfo->commute_above_l, ojrelid);
			else if (bms_is_member(otherinfo->ojrelid, commute_below_r))
				otherinfo->commute_above_r =
					bms_add_member(otherinfo->commute_above_r, ojrelid);
		}
	}

	return sjinfo;
}

/*
 * compute_semijoin_info
 *	  Fill semijoin-related fields of a new SpecialJoinInfo
 *
 * Note: this relies on only the jointype and syn_righthand fields of the
 * SpecialJoinInfo; the rest may not be set yet.
 */
/*
 * compute_semijoin_info - (中文)填充新 SpecialJoinInfo 的半连接相关字段
 *
 * 【作用】由 make_outerjoininfo() 调用。对非 SEMI 连接,初始化
 * semi_can_btree=false、semi_can_hash=false、semi_operators=NIL、
 * semi_rhs_exprs=NIL 后即返回。对 SEMI 连接,扫描其语法关联的(IN 的合成
 * 比较列表或 EXISTS 的 WHERE)条件列表,逐个检查:
 * - 条件只涉及一侧(单边引用):忽略之,但若含 volatile 函数则整体放弃
 *   (不能安全地用于去重推导);
 * - 非二元操作符但涉及两侧:放弃;
 * - 二元等值操作符:若 RHS 变量恰在某一边(必要时取交换算子把 RHS 换到
 *   右侧),记录该操作符与 RHS 表达式;要求所有条件均为 btree 兼容(检查
 *   排序操作族)和/或 hash 兼容(enable_hashagg 才考虑哈希),据此置
 *   all_btree / all_hash,最终把结果写入 sjinfo。
 *
 * 【设计思想】半连接的 RHS 若能"去重(unique-ify)",执行时可把 SEMI 变成
 * 内连接+去重,显著提升性能。判断依据:连接条件全为等值、且每个等值条件
 * 一侧只含 RHS 变量,即可用该 RHS 表达式集合做 btree/hash 去重。
 * semi_operators 存的是连接算子本身(必要时已交换),交叉类型算子可能没有
 * 对应的单类型去重算子——这里假设届时 btree/hash 操作类能提供,否则
 * create_unique_plan() 会失败报错。语法关联条件可能含语义上不相关(单侧)
 * 的子句,它们会自然下坠到单侧处理,故只需考虑语法关联条件即可。
 *
 * 【参数】
 *   root   —— 当前查询级的 PlannerInfo;
 *   sjinfo —— 待填充的 SpecialJoinInfo(须已设置 jointype 与 syn_righthand);
 *   clause —— 与半连接语法关联的条件列表。
 * 【返回值】无。
 */
static void
compute_semijoin_info(PlannerInfo *root, SpecialJoinInfo *sjinfo, List *clause)
{
	List	   *semi_operators;
	List	   *semi_rhs_exprs;
	bool		all_btree;
	bool		all_hash;
	ListCell   *lc;

	/* Initialize semijoin-related fields in case we can't unique-ify */
	sjinfo->semi_can_btree = false;
	sjinfo->semi_can_hash = false;
	sjinfo->semi_operators = NIL;
	sjinfo->semi_rhs_exprs = NIL;

	/* Nothing more to do if it's not a semijoin */
	if (sjinfo->jointype != JOIN_SEMI)
		return;

	/*
	 * Look to see whether the semijoin's join quals consist of AND'ed
	 * equality operators, with (only) RHS variables on only one side of each
	 * one.  If so, we can figure out how to enforce uniqueness for the RHS.
	 *
	 * Note that the input clause list is the list of quals that are
	 * *syntactically* associated with the semijoin, which in practice means
	 * the synthesized comparison list for an IN or the WHERE of an EXISTS.
	 * Particularly in the latter case, it might contain clauses that aren't
	 * *semantically* associated with the join, but refer to just one side or
	 * the other.  We can ignore such clauses here, as they will just drop
	 * down to be processed within one side or the other.  (It is okay to
	 * consider only the syntactically-associated clauses here because for a
	 * semijoin, no higher-level quals could refer to the RHS, and so there
	 * can be no other quals that are semantically associated with this join.
	 * We do things this way because it is useful to have the set of potential
	 * unique-ification expressions before we can extract the list of quals
	 * that are actually semantically associated with the particular join.)
	 *
	 * Note that the semi_operators list consists of the joinqual operators
	 * themselves (but commuted if needed to put the RHS value on the right).
	 * These could be cross-type operators, in which case the operator
	 * actually needed for uniqueness is a related single-type operator. We
	 * assume here that that operator will be available from the btree or hash
	 * opclass when the time comes ... if not, create_unique_plan() will fail.
	 */
	semi_operators = NIL;
	semi_rhs_exprs = NIL;
	all_btree = true;
	all_hash = enable_hashagg;	/* don't consider hash if not enabled */
	foreach(lc, clause)
	{
		OpExpr	   *op = (OpExpr *) lfirst(lc);
		Oid			opno;
		Node	   *left_expr;
		Node	   *right_expr;
		Relids		left_varnos;
		Relids		right_varnos;
		Relids		all_varnos;
		Oid			opinputtype;

		/* Is it a binary opclause? */
		if (!IsA(op, OpExpr) ||
			list_length(op->args) != 2)
		{
			/* No, but does it reference both sides? */
			all_varnos = pull_varnos(root, (Node *) op);
			if (!bms_overlap(all_varnos, sjinfo->syn_righthand) ||
				bms_is_subset(all_varnos, sjinfo->syn_righthand))
			{
				/*
				 * Clause refers to only one rel, so ignore it --- unless it
				 * contains volatile functions, in which case we'd better
				 * punt.
				 */
				if (contain_volatile_functions((Node *) op))
					return;
				continue;
			}
			/* Non-operator clause referencing both sides, must punt */
			return;
		}

		/* Extract data from binary opclause */
		opno = op->opno;
		left_expr = linitial(op->args);
		right_expr = lsecond(op->args);
		left_varnos = pull_varnos(root, left_expr);
		right_varnos = pull_varnos(root, right_expr);
		all_varnos = bms_union(left_varnos, right_varnos);
		opinputtype = exprType(left_expr);

		/* Does it reference both sides? */
		if (!bms_overlap(all_varnos, sjinfo->syn_righthand) ||
			bms_is_subset(all_varnos, sjinfo->syn_righthand))
		{
			/*
			 * Clause refers to only one rel, so ignore it --- unless it
			 * contains volatile functions, in which case we'd better punt.
			 */
			if (contain_volatile_functions((Node *) op))
				return;
			continue;
		}

		/* check rel membership of arguments */
		if (!bms_is_empty(right_varnos) &&
			bms_is_subset(right_varnos, sjinfo->syn_righthand) &&
			!bms_overlap(left_varnos, sjinfo->syn_righthand))
		{
			/* typical case, right_expr is RHS variable */
		}
		else if (!bms_is_empty(left_varnos) &&
				 bms_is_subset(left_varnos, sjinfo->syn_righthand) &&
				 !bms_overlap(right_varnos, sjinfo->syn_righthand))
		{
			/* flipped case, left_expr is RHS variable */
			opno = get_commutator(opno);
			if (!OidIsValid(opno))
				return;
			right_expr = left_expr;
		}
		else
		{
			/* mixed membership of args, punt */
			return;
		}

		/* all operators must be btree equality or hash equality */
		if (all_btree)
		{
			/* oprcanmerge is considered a hint... */
			if (!op_mergejoinable(opno, opinputtype) ||
				get_mergejoin_opfamilies(opno) == NIL)
				all_btree = false;
		}
		if (all_hash)
		{
			/* ... but oprcanhash had better be correct */
			if (!op_hashjoinable(opno, opinputtype))
				all_hash = false;
		}
		if (!(all_btree || all_hash))
			return;

		/* so far so good, keep building lists */
		semi_operators = lappend_oid(semi_operators, opno);
		semi_rhs_exprs = lappend(semi_rhs_exprs, copyObject(right_expr));
	}

	/* Punt if we didn't find at least one column to unique-ify */
	if (semi_rhs_exprs == NIL)
		return;

	/*
	 * The expressions we'd need to unique-ify mustn't be volatile.
	 */
	if (contain_volatile_functions((Node *) semi_rhs_exprs))
		return;

	/*
	 * If we get here, we can unique-ify the semijoin's RHS using at least one
	 * of sorting and hashing.  Save the information about how to do that.
	 */
	sjinfo->semi_can_btree = all_btree;
	sjinfo->semi_can_hash = all_hash;
	sjinfo->semi_operators = semi_operators;
	sjinfo->semi_rhs_exprs = semi_rhs_exprs;
}

/*
 * deconstruct_distribute_oj_quals
 *	  Adjust LEFT JOIN quals to be suitable for commuted-left-join cases,
 *	  then push them into the joinqual lists and EquivalenceClass structures.
 *
 * This runs immediately after we've completed the deconstruct_distribute scan.
 * jtitems contains all the JoinTreeItems (in depth-first order), and jtitem
 * is one that has postponed oj_joinclauses to deal with.
 */
/*
 * deconstruct_distribute_oj_quals - (中文)第三遍处理被推迟的可交换左连接
 * 条件:调整 nullingrels 标记后推入连接条件列表与等价类
 *
 * 【作用】在 deconstruct_distribute() 完成后运行,对每个含 oj_joinclauses
 * 的节点处理其被推迟的条件。先由 SpecialJoinInfo 重新计算语法与语义作用域
 * (qualscope/ojscope/nonnullable_rels)。若该连接可按恒等式 3 与其他连接
 * 交换(commute_above_r 或 commute_below_l 非空),则须生成同一连接条件的
 * 多种 nullingrels 变体:先剥掉 commute_below 连接的置空位,然后沿
 * jtitems(深度优先=语法嵌套顺序)逐个处理参与交换的连接,在"下方/上方"
 * 判定后按当前栈把对应的置空位逐层加回,每生成一批 RestrictInfo 就重置
 * root->last_rinfo_serial,使同一条件派生的 RestrictInfo 共享相同 serial
 * (用于后续去重检测)。同时用 incompatible_joins 标记不能把克隆条件应用
 * 到其上的连接,防止错误层次求值;否则直接把推迟的条件原样分发。
 *
 * 【设计思想】恒等式 3 交换后,同一连接条件可能在若干不同连接层次被
 * 求值,而 Var/PHV 上的 varnullingrels 必须与该层次一致,否则外连接空值
 * 语义错误。为每种"交换组合"生成带不同置空标记的条件变体(clone),
 * 并让不同变体共享 serial 号,既覆盖了所有合法放置,又便于检测重复使用。
 *
 * 【参数】
 *   root    —— 当前查询级的 PlannerInfo;
 *   jtitems —— 全部 JoinTreeItem 列表(深度优先顺序);
 *   jtitem  —— 有待处理 oj_joinclauses 的节点。
 * 【返回值】无。
 */
static void
deconstruct_distribute_oj_quals(PlannerInfo *root,
								List *jtitems,
								JoinTreeItem *jtitem)
{
	SpecialJoinInfo *sjinfo = jtitem->sjinfo;
	Relids		qualscope,
				ojscope,
				nonnullable_rels;

	/* Recompute syntactic and semantic scopes of this left join */
	qualscope = bms_union(sjinfo->syn_lefthand, sjinfo->syn_righthand);
	qualscope = bms_add_member(qualscope, sjinfo->ojrelid);
	ojscope = bms_union(sjinfo->min_lefthand, sjinfo->min_righthand);
	nonnullable_rels = sjinfo->syn_lefthand;

	/*
	 * If this join can commute with any other ones per outer-join identity 3,
	 * and it is the one providing the join clause with flexible semantics,
	 * then we have to generate variants of the join clause with different
	 * nullingrels labeling.  Otherwise, just push out the postponed clause
	 * as-is.
	 */
	Assert(sjinfo->lhs_strict); /* else we shouldn't be here */
	if (sjinfo->commute_above_r || sjinfo->commute_below_l)
	{
		Relids		joins_above;
		Relids		joins_below;
		Relids		incompatible_joins;
		Relids		joins_so_far;
		List	   *quals;
		int			save_last_rinfo_serial;
		ListCell   *lc;

		/* Identify the outer joins this one commutes with */
		joins_above = sjinfo->commute_above_r;
		joins_below = sjinfo->commute_below_l;

		/*
		 * Generate qual variants with different sets of nullingrels bits.
		 *
		 * We only need bit-sets that correspond to the successively less
		 * deeply syntactically-nested subsets of this join and its
		 * commutators.  That's true first because obviously only those forms
		 * of the Vars and PHVs could appear elsewhere in the query, and
		 * second because the outer join identities do not provide a way to
		 * re-order such joins in a way that would require different marking.
		 * (That is, while the current join may commute with several others,
		 * none of those others can commute with each other.)  To visit the
		 * interesting joins in syntactic nesting order, we rely on the
		 * jtitems list to be ordered that way.
		 *
		 * We first strip out all the nullingrels bits corresponding to
		 * commuting joins below this one, and then successively put them back
		 * as we crawl up the join stack.
		 */
		quals = jtitem->oj_joinclauses;
		if (!bms_is_empty(joins_below))
			quals = (List *) remove_nulling_relids((Node *) quals,
												   joins_below,
												   NULL);

		/*
		 * We'll need to mark the lower versions of the quals as not safe to
		 * apply above not-yet-processed joins of the stack.  This prevents
		 * possibly applying a cloned qual at the wrong join level.
		 */
		incompatible_joins = bms_union(joins_below, joins_above);
		incompatible_joins = bms_add_member(incompatible_joins,
											sjinfo->ojrelid);

		/*
		 * Each time we produce RestrictInfo(s) from these quals, reset the
		 * last_rinfo_serial counter, so that the RestrictInfos for the "same"
		 * qual condition get identical serial numbers.  (This relies on the
		 * fact that we're not changing the qual list in any way that'd affect
		 * the number of RestrictInfos built from it.) This'll allow us to
		 * detect duplicative qual usage later.
		 */
		save_last_rinfo_serial = root->last_rinfo_serial;

		joins_so_far = NULL;
		foreach(lc, jtitems)
		{
			JoinTreeItem *otherjtitem = (JoinTreeItem *) lfirst(lc);
			SpecialJoinInfo *othersj = otherjtitem->sjinfo;
			bool		below_sjinfo = false;
			bool		above_sjinfo = false;
			Relids		this_qualscope;
			Relids		this_ojscope;
			bool		allow_equivalence,
						has_clone,
						is_clone;

			if (othersj == NULL)
				continue;		/* not an outer-join item, ignore */

			if (bms_is_member(othersj->ojrelid, joins_below))
			{
				/* othersj commutes with sjinfo from below left */
				below_sjinfo = true;
			}
			else if (othersj == sjinfo)
			{
				/* found our join in syntactic order */
				Assert(bms_equal(joins_so_far, joins_below));
			}
			else if (bms_is_member(othersj->ojrelid, joins_above))
			{
				/* othersj commutes with sjinfo from above */
				above_sjinfo = true;
			}
			else
			{
				/* othersj is not relevant, ignore */
				continue;
			}

			/* Reset serial counter for this version of the quals */
			root->last_rinfo_serial = save_last_rinfo_serial;

			/*
			 * When we are looking at joins above sjinfo, we are envisioning
			 * pushing sjinfo to above othersj, so add othersj's nulling bit
			 * before distributing the quals.  We should add it to Vars coming
			 * from the current join's LHS: we want to transform the second
			 * form of OJ identity 3 to the first form, in which Vars of
			 * relation B will appear nulled by the syntactically-upper OJ
			 * within the Pbc clause, but those of relation C will not.  (In
			 * the notation used by optimizer/README, we're converting a qual
			 * of the form Pbc to Pb*c.)  Of course, we must also remove that
			 * bit from the incompatible_joins value, else we'll make a qual
			 * that can't be placed anywhere.
			 */
			if (above_sjinfo)
			{
				quals = (List *)
					add_nulling_relids((Node *) quals,
									   sjinfo->syn_lefthand,
									   bms_make_singleton(othersj->ojrelid));
				incompatible_joins = bms_del_member(incompatible_joins,
													othersj->ojrelid);
			}

			/* Compute qualscope and ojscope for this join level */
			this_qualscope = bms_union(qualscope, joins_so_far);
			this_ojscope = bms_union(ojscope, joins_so_far);
			if (above_sjinfo)
			{
				/* othersj is not yet in joins_so_far, but we need it */
				this_qualscope = bms_add_member(this_qualscope,
												othersj->ojrelid);
				this_ojscope = bms_add_member(this_ojscope,
											  othersj->ojrelid);
				/* sjinfo is in joins_so_far, and we don't want it */
				this_ojscope = bms_del_member(this_ojscope,
											  sjinfo->ojrelid);
			}

			/*
			 * We generate EquivalenceClasses only from the first form of the
			 * quals, with the fewest nullingrels bits set.  An EC made from
			 * this version of the quals can be useful below the outer-join
			 * nest, whereas versions with some nullingrels bits set would not
			 * be.  We cannot generate ECs from more than one version, or
			 * we'll make nonsensical conclusions that Vars with nullingrels
			 * bits set are equal to their versions without.  Fortunately,
			 * such ECs wouldn't be very useful anyway, because they'd equate
			 * values not observable outside the join nest.  (See
			 * optimizer/README.)
			 *
			 * The first form of the quals is also the only one marked as
			 * has_clone rather than is_clone.
			 */
			allow_equivalence = (joins_so_far == NULL);
			has_clone = allow_equivalence;
			is_clone = !has_clone;

			distribute_quals_to_rels(root, quals,
									 otherjtitem,
									 sjinfo,
									 root->qual_security_level,
									 this_qualscope,
									 this_ojscope, nonnullable_rels,
									 bms_copy(incompatible_joins),
									 allow_equivalence,
									 has_clone,
									 is_clone,
									 NULL); /* no more postponement */

			/*
			 * Adjust qual nulling bits for next level up, if needed.  We
			 * don't want to put sjinfo's own bit in at all, and if we're
			 * above sjinfo then we did it already.  Here, we should mark all
			 * Vars coming from the lower join's RHS.  (Again, we are
			 * converting a qual of the form Pbc to Pb*c, but now we are
			 * putting back bits that were there in the parser output and were
			 * temporarily stripped above.)  Update incompatible_joins too.
			 */
			if (below_sjinfo)
			{
				quals = (List *)
					add_nulling_relids((Node *) quals,
									   othersj->syn_righthand,
									   bms_make_singleton(othersj->ojrelid));
				incompatible_joins = bms_del_member(incompatible_joins,
													othersj->ojrelid);
			}

			/* ... and track joins processed so far */
			joins_so_far = bms_add_member(joins_so_far, othersj->ojrelid);
		}
	}
	else
	{
		/* No commutation possible, just process the postponed clauses */
		distribute_quals_to_rels(root, jtitem->oj_joinclauses,
								 jtitem,
								 sjinfo,
								 root->qual_security_level,
								 qualscope,
								 ojscope, nonnullable_rels,
								 NULL,	/* incompatible_relids */
								 true,	/* allow_equivalence */
								 false, false,	/* not clones */
								 NULL); /* no more postponement */
	}
}


/*****************************************************************************
 *
 *	  QUALIFICATIONS
 *
 *****************************************************************************/

/*
 * distribute_quals_to_rels
 *	  Convenience routine to apply distribute_qual_to_rels to each element
 *	  of an AND'ed list of clauses.
 */
/*
 * distribute_quals_to_rels - (中文)便捷封装:把一条 AND 连接的条件列表逐项
 * 交给 distribute_qual_to_rels() 处理
 *
 * 【作用】distribute_qual_to_rels() 的参数集被多处(deconstruct_distribute、
 * deconstruct_distribute_oj_quals、process_security_barrier_quals)使用,
 * 本函数仅循环调用,避免重复展开这些参数。
 *
 * 【参数】与 distribute_qual_to_rels() 完全一致,仅把单个 clause 换成
 * clauses 列表。
 * 【返回值】无。
 */
static void
distribute_quals_to_rels(PlannerInfo *root, List *clauses,
						 JoinTreeItem *jtitem,
						 SpecialJoinInfo *sjinfo,
						 Index security_level,
						 Relids qualscope,
						 Relids ojscope,
						 Relids outerjoin_nonnullable,
						 Relids incompatible_relids,
						 bool allow_equivalence,
						 bool has_clone,
						 bool is_clone,
						 List **postponed_oj_qual_list)
{
	ListCell   *lc;

	foreach(lc, clauses)
	{
		Node	   *clause = (Node *) lfirst(lc);

		distribute_qual_to_rels(root, clause,
								jtitem,
								sjinfo,
								security_level,
								qualscope,
								ojscope,
								outerjoin_nonnullable,
								incompatible_relids,
								allow_equivalence,
								has_clone,
								is_clone,
								postponed_oj_qual_list);
	}
}

/*
 * distribute_qual_to_rels
 *	  Add clause information to either the baserestrictinfo or joininfo list
 *	  (depending on whether the clause is a join) of each base relation
 *	  mentioned in the clause.  A RestrictInfo node is created and added to
 *	  the appropriate list for each rel.  Alternatively, if the clause uses a
 *	  mergejoinable operator, enter its left- and right-side expressions into
 *	  the query's EquivalenceClasses.
 *
 * In some cases, quals will be added to parent jtitems' lateral_clauses
 * or to postponed_oj_qual_list instead of being processed right away.
 * These will be dealt with in later calls of deconstruct_distribute.
 *
 * 'clause': the qual clause to be distributed
 * 'jtitem': the JoinTreeItem for the containing jointree node
 * 'sjinfo': join's SpecialJoinInfo (NULL for an inner join or WHERE clause)
 * 'security_level': security_level to assign to the qual
 * 'qualscope': set of base+OJ rels the qual's syntactic scope covers
 * 'ojscope': NULL if not an outer-join qual, else the minimum set of base+OJ
 *		rels needed to form this join
 * 'outerjoin_nonnullable': NULL if not an outer-join qual, else the set of
 *		base+OJ rels appearing on the outer (nonnullable) side of the join
 *		(for FULL JOIN this includes both sides of the join, and must in fact
 *		equal qualscope)
 * 'incompatible_relids': the set of outer-join relid(s) that must not be
 *		computed below this qual.  We only bother to compute this for
 *		"clone" quals, otherwise it can be left NULL.
 * 'allow_equivalence': true if it's okay to convert clause into an
 *		EquivalenceClass
 * 'has_clone': has_clone property to assign to the qual
 * 'is_clone': is_clone property to assign to the qual
 * 'postponed_oj_qual_list': if not NULL, non-degenerate outer join clauses
 *		should be added to this list instead of being processed (list entries
 *		are just the bare clauses)
 *
 * 'qualscope' identifies what level of JOIN the qual came from syntactically.
 * 'ojscope' is needed if we decide to force the qual up to the outer-join
 * level, which will be ojscope not necessarily qualscope.
 *
 * At the time this is called, root->join_info_list must contain entries for
 * at least those special joins that are syntactically below this qual.
 * (We now need that only for detection of redundant IS NULL quals.)
 */
/*
 * distribute_qual_to_rels - (中文)把单个连接/过滤条件分发到各基础关系的
 * baserestrictinfo 或 joininfo(必要时送入等价类/推迟列表)
 *
 * 【作用】分发单个条件的核心例程,流程如下:
 * 1. pull_varnos() 取出条件涉及的关系集合 relids;
 * 2. 若 relids 超出本节点语法作用域(拉平的 LATERAL 情形),沿父链寻找能
 *    覆盖全部 relids 的最近祖先,把条件挂到其 lateral_clauses 推迟处理;
 * 3. 外连接条件须满足 relids ⊆ ojscope,否则报错;
 * 4. 无 Var 条件:外连接条件强制在 ojscope 求值;含 volatile 的条件留在
 *    原语法层次;否则按是否位于顶层 JoinDomain 决定推到树顶(标记
 *    pseudoconstant 与 hasPseudoConstantQuals,供 createplan 生成 gating
 *    Result)还是留在原层次;
 * 5. 依据是否提及非空侧判断外连接条件是否退化(degenerate):
 *    - 非退化且调用者要求推迟:加入 postponed_oj_qual_list 返回;
 *    - 非退化:is_pushed_down=false,可能进入"预留的外连接条件"列表;
 *    - 退化:当作普通过滤条件,is_pushed_down=true;
 *    - WHERE/内连接条件:is_pushed_down=true;
 * 6. 对合并可连接(mergejoinable)的等值条件,依 may_equivalence 等标志
 *    调用 process_equivalence() 进入等价类机制,或 process_implied_equality();
 *    其余条件用 make_restrictinfo() 构造 RestrictInfo,并按 relids 中基表
 *    数量决定放入单个关系的 baserestrictinfo 还是多个关系的 joininfo,
 *    且为"等值可下推的惰性条件"复制到每个含相关列的 rel(惰性复制);
 * 7. 处理安全级别 security_level、克隆标记(has_clone/is_clone)、以及
 *    incompatible_relids(克隆条件不得应用到其下的外连接)。
 *
 * 【设计思想】is_pushed_down 标志区分外连接 ON 条件与下推的普通条件:
 * WHERE/内连接=true、非退化外连接=false、退化外连接=true。退化条件
 * (不提非空侧)可在 nullable 侧内求值而不改变结果。外连接等值条件的
 * 上下两侧在外连接之后可能不等,故不能直接进入等价类,只登记到
 * left_join_clauses / right_join_clauses / full_join_clauses 供 joinpath
 * 使用(若满足 hashable/mergejoinable 再尝试推导)。
 *
 * 【参数】见函数定义处的英文注释;关键者:
 *   clause               —— 待分发条件;
 *   jtitem               —— 所属 jointree 节点的 JoinTreeItem;
 *   sjinfo               —— 所属外连接的 SpecialJoinInfo(内连接/WHERE 为 NULL);
 *   qualscope/ojscope    —— 语法/语义作用域;
 *   outerjoin_nonnullable—— 非空侧集合;
 *   postponed_oj_qual_list—— 非 NULL 时把非退化外连接条件加入其中推迟。
 * 【返回值】无。
 */
static void
distribute_qual_to_rels(PlannerInfo *root, Node *clause,
						JoinTreeItem *jtitem,
						SpecialJoinInfo *sjinfo,
						Index security_level,
						Relids qualscope,
						Relids ojscope,
						Relids outerjoin_nonnullable,
						Relids incompatible_relids,
						bool allow_equivalence,
						bool has_clone,
						bool is_clone,
						List **postponed_oj_qual_list)
{
	Relids		relids;
	bool		is_pushed_down;
	bool		pseudoconstant = false;
	bool		maybe_equivalence;
	bool		maybe_outer_join;
	RestrictInfo *restrictinfo;

	/*
	 * Retrieve all relids mentioned within the clause.
	 */
	relids = pull_varnos(root, clause);

	/*
	 * In ordinary SQL, a WHERE or JOIN/ON clause can't reference any rels
	 * that aren't within its syntactic scope; however, if we pulled up a
	 * LATERAL subquery then we might find such references in quals that have
	 * been pulled up.  We need to treat such quals as belonging to the join
	 * level that includes every rel they reference.  Although we could make
	 * pull_up_subqueries() place such quals correctly to begin with, it's
	 * easier to handle it here.  When we find a clause that contains Vars
	 * outside its syntactic scope, locate the nearest parent join level that
	 * includes all the required rels and add the clause to that level's
	 * lateral_clauses list.  We'll process it when we reach that join level.
	 */
	if (!bms_is_subset(relids, qualscope))
	{
		JoinTreeItem *pitem;

		Assert(root->hasLateralRTEs);	/* shouldn't happen otherwise */
		Assert(sjinfo == NULL); /* mustn't postpone past outer join */
		for (pitem = jtitem->jti_parent; pitem; pitem = pitem->jti_parent)
		{
			if (bms_is_subset(relids, pitem->qualscope))
			{
				pitem->lateral_clauses = lappend(pitem->lateral_clauses,
												 clause);
				return;
			}

			/*
			 * We should not be postponing any quals past an outer join.  If
			 * this Assert fires, pull_up_subqueries() messed up.
			 */
			Assert(pitem->sjinfo == NULL);
		}
		elog(ERROR, "failed to postpone qual containing lateral reference");
	}

	/*
	 * If it's an outer-join clause, also check that relids is a subset of
	 * ojscope.  (This should not fail if the syntactic scope check passed.)
	 */
	if (ojscope && !bms_is_subset(relids, ojscope))
		elog(ERROR, "JOIN qualification cannot refer to other relations");

	/*
	 * If the clause is variable-free, our normal heuristic for pushing it
	 * down to just the mentioned rels doesn't work, because there are none.
	 *
	 * If the clause is an outer-join clause, we must force it to the OJ's
	 * semantic level to preserve semantics.
	 *
	 * Otherwise, when the clause contains volatile functions, we force it to
	 * be evaluated at its original syntactic level.  This preserves the
	 * expected semantics.
	 *
	 * When the clause contains no volatile functions either, it is actually a
	 * pseudoconstant clause that will not change value during any one
	 * execution of the plan, and hence can be used as a one-time qual in a
	 * gating Result plan node.  We put such a clause into the regular
	 * RestrictInfo lists for the moment, but eventually createplan.c will
	 * pull it out and make a gating Result node immediately above whatever
	 * plan node the pseudoconstant clause is assigned to.  It's usually best
	 * to put a gating node as high in the plan tree as possible.
	 */
	if (bms_is_empty(relids))
	{
		if (ojscope)
		{
			/* clause is attached to outer join, eval it there */
			relids = bms_copy(ojscope);
			/* mustn't use as gating qual, so don't mark pseudoconstant */
		}
		else if (contain_volatile_functions(clause))
		{
			/* eval at original syntactic level */
			relids = bms_copy(qualscope);
			/* again, can't mark pseudoconstant */
		}
		else
		{
			/*
			 * If we are in the top-level join domain, we can push the qual to
			 * the top of the plan tree.  Otherwise, be conservative and eval
			 * it at original syntactic level.  (Ideally we'd push it to the
			 * top of the current join domain in all cases, but that causes
			 * problems if we later rearrange outer-join evaluation order.
			 * Pseudoconstant quals below the top level are a pretty odd case,
			 * so it's not clear that it's worth working hard on.)
			 */
			if (jtitem->jdomain == (JoinDomain *) linitial(root->join_domains))
				relids = bms_copy(jtitem->jdomain->jd_relids);
			else
				relids = bms_copy(qualscope);
			/* mark as gating qual */
			pseudoconstant = true;
			/* tell createplan.c to check for gating quals */
			root->hasPseudoConstantQuals = true;
		}
	}

	/*----------
	 * Check to see if clause application must be delayed by outer-join
	 * considerations.
	 *
	 * A word about is_pushed_down: we mark the qual as "pushed down" if
	 * it is (potentially) applicable at a level different from its original
	 * syntactic level.  This flag is used to distinguish OUTER JOIN ON quals
	 * from other quals pushed down to the same joinrel.  The rules are:
	 *		WHERE quals and INNER JOIN quals: is_pushed_down = true.
	 *		Non-degenerate OUTER JOIN quals: is_pushed_down = false.
	 *		Degenerate OUTER JOIN quals: is_pushed_down = true.
	 * A "degenerate" OUTER JOIN qual is one that doesn't mention the
	 * non-nullable side, and hence can be pushed down into the nullable side
	 * without changing the join result.  It is correct to treat it as a
	 * regular filter condition at the level where it is evaluated.
	 *
	 * Note: it is not immediately obvious that a simple boolean is enough
	 * for this: if for some reason we were to attach a degenerate qual to
	 * its original join level, it would need to be treated as an outer join
	 * qual there.  However, this cannot happen, because all the rels the
	 * clause mentions must be in the outer join's min_righthand, therefore
	 * the join it needs must be formed before the outer join; and we always
	 * attach quals to the lowest level where they can be evaluated.  But
	 * if we were ever to re-introduce a mechanism for delaying evaluation
	 * of "expensive" quals, this area would need work.
	 *
	 * Note: generally, use of is_pushed_down has to go through the macro
	 * RINFO_IS_PUSHED_DOWN, because that flag alone is not always sufficient
	 * to tell whether a clause must be treated as pushed-down in context.
	 * This seems like another reason why it should perhaps be rethought.
	 *----------
	 */
	if (bms_overlap(relids, outerjoin_nonnullable))
	{
		/*
		 * The qual is attached to an outer join and mentions (some of the)
		 * rels on the nonnullable side, so it's not degenerate.  If the
		 * caller wants to postpone handling such clauses, just add it to
		 * postponed_oj_qual_list and return.  (The work we've done up to here
		 * will have to be redone later, but there's not much of it.)
		 */
		if (postponed_oj_qual_list != NULL)
		{
			*postponed_oj_qual_list = lappend(*postponed_oj_qual_list, clause);
			return;
		}

		/*
		 * We can't use such a clause to deduce equivalence (the left and
		 * right sides might be unequal above the join because one of them has
		 * gone to NULL) ... but we might be able to use it for more limited
		 * deductions, if it is mergejoinable.  So consider adding it to the
		 * lists of set-aside outer-join clauses.
		 */
		is_pushed_down = false;
		maybe_equivalence = false;
		maybe_outer_join = true;

		/*
		 * Now force the qual to be evaluated exactly at the level of joining
		 * corresponding to the outer join.  We cannot let it get pushed down
		 * into the nonnullable side, since then we'd produce no output rows,
		 * rather than the intended single null-extended row, for any
		 * nonnullable-side rows failing the qual.
		 */
		Assert(ojscope);
		relids = ojscope;
		Assert(!pseudoconstant);
	}
	else
	{
		/*
		 * Normal qual clause or degenerate outer-join clause.  Either way, we
		 * can mark it as pushed-down.
		 */
		is_pushed_down = true;

		/*
		 * It's possible that this is an IS NULL clause that's redundant with
		 * a lower antijoin; if so we can just discard it.  We need not test
		 * in any of the other cases, because this will only be possible for
		 * pushed-down clauses.
		 */
		if (check_redundant_nullability_qual(root, clause))
			return;

		/* Feed qual to the equivalence machinery, if allowed by caller */
		maybe_equivalence = allow_equivalence;

		/*
		 * Since it doesn't mention the LHS, it's certainly not useful as a
		 * set-aside OJ clause, even if it's in an OJ.
		 */
		maybe_outer_join = false;
	}

	/*
	 * Build the RestrictInfo node itself.
	 */
	restrictinfo = make_restrictinfo(root,
									 (Expr *) clause,
									 is_pushed_down,
									 has_clone,
									 is_clone,
									 pseudoconstant,
									 security_level,
									 relids,
									 incompatible_relids,
									 outerjoin_nonnullable);

	/*
	 * If it's a join clause, add vars used in the clause to targetlists of
	 * their relations, so that they will be emitted by the plan nodes that
	 * scan those relations (else they won't be available at the join node!).
	 *
	 * Normally we mark the vars as needed at the join identified by "relids".
	 * However, if this is a clone clause then ignore the outer-join relids in
	 * that set.  Otherwise, vars appearing in a cloned clause would end up
	 * marked as having to propagate to the highest one of the commuting
	 * joins, which would often be an overestimate.  For such clauses, correct
	 * var propagation is ensured by making ojscope include input rels from
	 * both sides of the join.
	 *
	 * See also rebuild_joinclause_attr_needed, which has to partially repeat
	 * this work after removal of an outer join.
	 *
	 * Note: if the clause gets absorbed into an EquivalenceClass then this
	 * may be unnecessary, but for now we have to do it to cover the case
	 * where the EC becomes ec_broken and we end up reinserting the original
	 * clauses into the plan.
	 */
	if (bms_membership(relids) == BMS_MULTIPLE)
	{
		List	   *vars = pull_var_clause(clause,
										   PVC_RECURSE_AGGREGATES |
										   PVC_RECURSE_WINDOWFUNCS |
										   PVC_INCLUDE_PLACEHOLDERS);
		Relids		where_needed;

		if (is_clone)
			where_needed = bms_intersect(relids, root->all_baserels);
		else
			where_needed = relids;
		add_vars_to_targetlist(root, vars, where_needed);
		list_free(vars);
	}

	/*
	 * We check "mergejoinability" of every clause, not only join clauses,
	 * because we want to know about equivalences between vars of the same
	 * relation, or between vars and consts.
	 */
	check_mergejoinable(restrictinfo);

	/*
	 * If it is a true equivalence clause, send it to the EquivalenceClass
	 * machinery.  We do *not* attach it directly to any restriction or join
	 * lists.  The EC code will propagate it to the appropriate places later.
	 *
	 * If the clause has a mergejoinable operator, yet isn't an equivalence
	 * because it is an outer-join clause, the EC code may still be able to do
	 * something with it.  We add it to appropriate lists for further
	 * consideration later.  Specifically:
	 *
	 * If it is a left or right outer-join qualification that relates the two
	 * sides of the outer join (no funny business like leftvar1 = leftvar2 +
	 * rightvar), we add it to root->left_join_clauses or
	 * root->right_join_clauses according to which side the nonnullable
	 * variable appears on.
	 *
	 * If it is a full outer-join qualification, we add it to
	 * root->full_join_clauses.  (Ideally we'd discard cases that aren't
	 * leftvar = rightvar, as we do for left/right joins, but this routine
	 * doesn't have the info needed to do that; and the current usage of the
	 * full_join_clauses list doesn't require that, so it's not currently
	 * worth complicating this routine's API to make it possible.)
	 *
	 * If none of the above hold, pass it off to
	 * distribute_restrictinfo_to_rels().
	 *
	 * In all cases, it's important to initialize the left_ec and right_ec
	 * fields of a mergejoinable clause, so that all possibly mergejoinable
	 * expressions have representations in EquivalenceClasses.  If
	 * process_equivalence is successful, it will take care of that;
	 * otherwise, we have to call initialize_mergeclause_eclasses to do it.
	 */
	if (restrictinfo->mergeopfamilies)
	{
		if (maybe_equivalence)
		{
			if (process_equivalence(root, &restrictinfo, jtitem->jdomain))
				return;
			/* EC rejected it, so set left_ec/right_ec the hard way ... */
			if (restrictinfo->mergeopfamilies)	/* EC might have changed this */
				initialize_mergeclause_eclasses(root, restrictinfo);
			/* ... and fall through to distribute_restrictinfo_to_rels */
		}
		else if (maybe_outer_join && restrictinfo->can_join)
		{
			/* we need to set up left_ec/right_ec the hard way */
			initialize_mergeclause_eclasses(root, restrictinfo);
			/* now see if it should go to any outer-join lists */
			Assert(sjinfo != NULL);
			if (bms_is_subset(restrictinfo->left_relids,
							  outerjoin_nonnullable) &&
				!bms_overlap(restrictinfo->right_relids,
							 outerjoin_nonnullable))
			{
				/* we have outervar = innervar */
				OuterJoinClauseInfo *ojcinfo = makeNode(OuterJoinClauseInfo);

				ojcinfo->rinfo = restrictinfo;
				ojcinfo->sjinfo = sjinfo;
				root->left_join_clauses = lappend(root->left_join_clauses,
												  ojcinfo);
				return;
			}
			if (bms_is_subset(restrictinfo->right_relids,
							  outerjoin_nonnullable) &&
				!bms_overlap(restrictinfo->left_relids,
							 outerjoin_nonnullable))
			{
				/* we have innervar = outervar */
				OuterJoinClauseInfo *ojcinfo = makeNode(OuterJoinClauseInfo);

				ojcinfo->rinfo = restrictinfo;
				ojcinfo->sjinfo = sjinfo;
				root->right_join_clauses = lappend(root->right_join_clauses,
												   ojcinfo);
				return;
			}
			if (sjinfo->jointype == JOIN_FULL)
			{
				/* FULL JOIN (above tests cannot match in this case) */
				OuterJoinClauseInfo *ojcinfo = makeNode(OuterJoinClauseInfo);

				ojcinfo->rinfo = restrictinfo;
				ojcinfo->sjinfo = sjinfo;
				root->full_join_clauses = lappend(root->full_join_clauses,
												  ojcinfo);
				return;
			}
			/* nope, so fall through to distribute_restrictinfo_to_rels */
		}
		else
		{
			/* we still need to set up left_ec/right_ec */
			initialize_mergeclause_eclasses(root, restrictinfo);
		}
	}

	/* No EC special case applies, so push it into the clause lists */
	distribute_restrictinfo_to_rels(root, restrictinfo);
}

/*
 * check_redundant_nullability_qual
 *	  Check to see if the qual is an IS NULL qual that is redundant with
 *	  a lower JOIN_ANTI join.
 *
 * We want to suppress redundant IS NULL quals, not so much to save cycles
 * as to avoid generating bogus selectivity estimates for them.  So if
 * redundancy is detected here, distribute_qual_to_rels() just throws away
 * the qual.
 */
/*
 * check_redundant_nullability_qual - (中文)检查 IS NULL 条件是否与下层
 * ANTI JOIN 冗余
 *
 * 【作用】对下推条件,先 find_forced_null_var() 找到被强制为 NULL 的 Var;
 * 若其 varnullingrels 非空,则扫描 root->join_info_list,若某 JOIN_ANTI 且
 * 其 ojrelid(非 0)正好出现在该 Var 的置空集合中,则返回 true——该
 * IS NULL 条件必然成立,可整体丢弃。
 *
 * 【设计思想】抑制冗余 IS NULL 条件的动机主要是避免为它生成虚高的选择率
 * 估计(而非省计算量):被反连接置空的列再做 IS NULL 是恒真条件,保留它
 * 会让后续估算错误。由 SEMI 转换而来的 ANTI 可能 ojrelid 为 0,但此时
 * Var 不可能来自其 nullable 侧,故需先排除。
 *
 * 【参数】
 *   root   —— 当前查询级的 PlannerInfo;
 *   clause —— 待检查的 IS NULL 条件。
 * 【返回值】冗余时返回 true。
 */
static bool
check_redundant_nullability_qual(PlannerInfo *root, Node *clause)
{
	Var		   *forced_null_var;
	ListCell   *lc;

	/* Check for IS NULL, and identify the Var forced to NULL */
	forced_null_var = find_forced_null_var(clause);
	if (forced_null_var == NULL)
		return false;

	/*
	 * If the Var comes from the nullable side of a lower antijoin, the IS
	 * NULL condition is necessarily true.  If it's not nulled by anything,
	 * there is no point in searching the join_info_list.  Otherwise, we need
	 * to find out whether the nulling rel is an antijoin.
	 */
	if (forced_null_var->varnullingrels == NULL)
		return false;

	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(lc);

		/*
		 * This test will not succeed if sjinfo->ojrelid is zero, which is
		 * possible for an antijoin that was converted from a semijoin; but in
		 * such a case the Var couldn't have come from its nullable side.
		 */
		if (sjinfo->jointype == JOIN_ANTI && sjinfo->ojrelid != 0 &&
			bms_is_member(sjinfo->ojrelid, forced_null_var->varnullingrels))
			return true;
	}

	return false;
}

/*
 * add_base_clause_to_rel
 *		Add 'restrictinfo' as a baserestrictinfo to the base relation denoted
 *		by 'relid'.  We offer some simple prechecks to try to determine if the
 *		qual is always true, in which case we ignore it rather than add it.
 *		If we detect the qual is always false, we replace it with
 *		constant-FALSE.
 */
/*
 * add_base_clause_to_rel - (中文)把 RestrictInfo 加入基础关系的
 * baserestrictinfo,并做恒真/恒假的常量化简
 *
 * 【作用】distribute_restrictinfo_to_rels() 的辅助:把单关系条件加入
 * rel->baserestrictinfo,同时更新 baserestrict_min_security。加入前做检查:
 * - 恒真条件(restriction_is_always_true)直接忽略不加入;
 * - 恒假条件(restriction_is_always_false)用常量 FALSE 替换后再加入。
 * 特例:对继承父表(rte->inh 且非分区表)必须原样记录条件,因为
 * apply_child_basequals() 需要原始条件推给子表,不能变换或跳过。
 *
 * 【设计思想】恒假→FALSE 替换可让上层把查询判定为空结果;替换时保持
 * rinfo_serial 不变(同一条件应序列号相同,供克隆去重检测使用),并复位
 * root->last_rinfo_serial。对分区表恒真/恒假变换总是安全:子分区同列集
 * 必继承同样的真值。继承父表有 inh=true/false 两个 RTE,inh=false 那个
 * 用于最终扫描节点,仍可享受化简。
 *
 * 【参数】
 *   root         —— 当前查询级的 PlannerInfo;
 *   relid        —— 目标基础关系的 RTE 索引;
 *   restrictinfo —— 待加入的 RestrictInfo(required_relids 须为单元素)。
 * 【返回值】无。
 */
static void
add_base_clause_to_rel(PlannerInfo *root, Index relid,
					   RestrictInfo *restrictinfo)
{
	RelOptInfo *rel = find_base_rel(root, relid);
	RangeTblEntry *rte = root->simple_rte_array[relid];

	Assert(bms_membership(restrictinfo->required_relids) == BMS_SINGLETON);

	/*
	 * For inheritance parent tables, we must always record the RestrictInfo
	 * in baserestrictinfo as is.  If we were to transform or skip adding it,
	 * then the original wouldn't be available in apply_child_basequals. Since
	 * there are two RangeTblEntries for inheritance parents, one with
	 * inh==true and the other with inh==false, we're still able to apply this
	 * optimization to the inh==false one.  The inh==true one is what
	 * apply_child_basequals() sees, whereas the inh==false one is what's used
	 * for the scan node in the final plan.
	 *
	 * We make an exception to this for partitioned tables.  For these, we
	 * always apply the constant-TRUE and constant-FALSE transformations.  A
	 * qual which is either of these for a partitioned table must also be that
	 * for all of its child partitions.
	 */
	if (!rte->inh || rte->relkind == RELKIND_PARTITIONED_TABLE)
	{
		/* Don't add the clause if it is always true */
		if (restriction_is_always_true(root, restrictinfo))
			return;

		/*
		 * Substitute the origin qual with constant-FALSE if it is provably
		 * always false.
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
	}

	/* Add clause to rel's restriction list */
	rel->baserestrictinfo = lappend(rel->baserestrictinfo, restrictinfo);

	/* Update security level info */
	rel->baserestrict_min_security = Min(rel->baserestrict_min_security,
										 restrictinfo->security_level);
}

/*
 * restriction_is_always_true
 *	  Check to see if the RestrictInfo is always true.
 *
 * Currently we only check for NullTest quals and OR clauses that include
 * NullTest quals.  We may extend it in the future.
 */
/*
 * restriction_is_always_true - (中文)检查 RestrictInfo 是否恒真
 *
 * 【作用】add_base_clause_to_rel() 的辅助。克隆条件(has_clone/is_clone)一律
 * 返回 false——其置空位可能不代表真实情况,不能据其判断非空。对
 * IS_NOT_NULL 的 NullTest(排除行表达式 argisrow),若其参数表达式可证明
 * 非空(expr_is_nonnullable)则恒真;对 OR 条件,任一分支可证明恒真则整个
 * OR 恒真。
 *
 * 【设计思想】简化目标是避免在计划里保留必然成立的过滤条件,省执行与估算
 * 成本。当前仅覆盖 NullTest 与含 NullTest 的 OR,未来可扩展。
 *
 * 【参数】
 *   root         —— 当前查询级的 PlannerInfo;
 *   restrictinfo —— 待检查的条件。
 * 【返回值】恒真返回 true。
 */
bool
restriction_is_always_true(PlannerInfo *root,
						   RestrictInfo *restrictinfo)
{
	/*
	 * For a clone clause, we don't have a reliable way to determine if the
	 * input expression of a NullTest is non-nullable: nullingrel bits in
	 * clone clauses may not reflect reality, so we dare not draw conclusions
	 * from clones about whether Vars are guaranteed not-null.
	 */
	if (restrictinfo->has_clone || restrictinfo->is_clone)
		return false;

	/* Check for NullTest qual */
	if (IsA(restrictinfo->clause, NullTest))
	{
		NullTest   *nulltest = (NullTest *) restrictinfo->clause;

		/* is this NullTest an IS_NOT_NULL qual? */
		if (nulltest->nulltesttype != IS_NOT_NULL)
			return false;

		/*
		 * Empty rows can appear NULL in some contexts and NOT NULL in others,
		 * so avoid this optimization for row expressions.
		 */
		if (nulltest->argisrow)
			return false;

		return expr_is_nonnullable(root, nulltest->arg, NOTNULL_SOURCE_RELOPT);
	}

	/* If it's an OR, check its sub-clauses */
	if (restriction_is_or_clause(restrictinfo))
	{
		ListCell   *lc;

		Assert(is_orclause(restrictinfo->orclause));

		/*
		 * if any of the given OR branches is provably always true then the
		 * entire condition is true.
		 */
		foreach(lc, ((BoolExpr *) restrictinfo->orclause)->args)
		{
			Node	   *orarg = (Node *) lfirst(lc);

			if (!IsA(orarg, RestrictInfo))
				continue;

			if (restriction_is_always_true(root, (RestrictInfo *) orarg))
				return true;
		}
	}

	return false;
}

/*
 * restriction_is_always_false
 *	  Check to see if the RestrictInfo is always false.
 *
 * Currently we only check for NullTest quals and OR clauses that include
 * NullTest quals.  We may extend it in the future.
 */
/*
 * restriction_is_always_false - (中文)检查 RestrictInfo 是否恒假
 *
 * 【作用】add_base_clause_to_rel() 的辅助。克隆条件一律返回 false。对
 * IS_NULL 的 NullTest(排除行表达式),若参数可证明非空则恒假;对 OR 条件,
 * 仅当所有分支都恒假时才返回 true。
 *
 * 【设计思想】与恒真检查互为补充。OR 情形目前只做"全部恒假"判定,未来
 * 可扩展为剔除恒假分支(这可能把 OR 化简成单参数甚至允许用索引)。
 *
 * 【参数】
 *   root         —— 当前查询级的 PlannerInfo;
 *   restrictinfo —— 待检查的条件。
 * 【返回值】恒假返回 true。
 */
bool
restriction_is_always_false(PlannerInfo *root,
							RestrictInfo *restrictinfo)
{
	/*
	 * For a clone clause, we don't have a reliable way to determine if the
	 * input expression of a NullTest is non-nullable: nullingrel bits in
	 * clone clauses may not reflect reality, so we dare not draw conclusions
	 * from clones about whether Vars are guaranteed not-null.
	 */
	if (restrictinfo->has_clone || restrictinfo->is_clone)
		return false;

	/* Check for NullTest qual */
	if (IsA(restrictinfo->clause, NullTest))
	{
		NullTest   *nulltest = (NullTest *) restrictinfo->clause;

		/* is this NullTest an IS_NULL qual? */
		if (nulltest->nulltesttype != IS_NULL)
			return false;

		/*
		 * Empty rows can appear NULL in some contexts and NOT NULL in others,
		 * so avoid this optimization for row expressions.
		 */
		if (nulltest->argisrow)
			return false;

		return expr_is_nonnullable(root, nulltest->arg, NOTNULL_SOURCE_RELOPT);
	}

	/* If it's an OR, check its sub-clauses */
	if (restriction_is_or_clause(restrictinfo))
	{
		ListCell   *lc;

		Assert(is_orclause(restrictinfo->orclause));

		/*
		 * Currently, when processing OR expressions, we only return true when
		 * all of the OR branches are always false.  This could perhaps be
		 * expanded to remove OR branches that are provably false.  This may
		 * be a useful thing to do as it could result in the OR being left
		 * with a single arg.  That's useful as it would allow the OR
		 * condition to be replaced with its single argument which may allow
		 * use of an index for faster filtering on the remaining condition.
		 */
		foreach(lc, ((BoolExpr *) restrictinfo->orclause)->args)
		{
			Node	   *orarg = (Node *) lfirst(lc);

			if (!IsA(orarg, RestrictInfo) ||
				!restriction_is_always_false(root, (RestrictInfo *) orarg))
				return false;
		}
		return true;
	}

	return false;
}

/*
 * distribute_restrictinfo_to_rels
 *	  Push a completed RestrictInfo into the proper restriction or join
 *	  clause list(s).
 *
 * This is the last step of distribute_qual_to_rels() for ordinary qual
 * clauses.  Clauses that are interesting for equivalence-class processing
 * are diverted to the EC machinery, but may ultimately get fed back here.
 */
/*
 * distribute_restrictinfo_to_rels - (中文)把已完成的 RestrictInfo 推入
 * 恰当的限制/连接条件列表
 *
 * 【作用】distribute_qual_to_rels() 的收尾步骤:
 * - required_relids 为单元素:该条件是某关系的限制条件,调用
 *   add_base_clause_to_rel() 加入其 baserestrictinfo;
 * - 多元素:是连接条件,先 check_hashjoinable()(仅真连接条件设置哈希信息)、
 *   check_memoizable()(检查是否可用 Memoize 缓存参数化 nestloop 的内侧
 *   元组),再 add_join_clause_to_rels() 把它加入所有相关关系的 joininfo;
 * - 空集合:无关系可挂,报错(正常调用者不应出现)。
 *
 * 【参数】
 *   root         —— 当前查询级的 PlannerInfo;
 *   restrictinfo —— 待分发的条件。
 * 【返回值】无。
 */
void
distribute_restrictinfo_to_rels(PlannerInfo *root,
								RestrictInfo *restrictinfo)
{
	Relids		relids = restrictinfo->required_relids;

	if (!bms_is_empty(relids))
	{
		int			relid;

		if (bms_get_singleton_member(relids, &relid))
		{
			/*
			 * There is only one relation participating in the clause, so it
			 * is a restriction clause for that relation.
			 */
			add_base_clause_to_rel(root, relid, restrictinfo);
		}
		else
		{
			/*
			 * The clause is a join clause, since there is more than one rel
			 * in its relid set.
			 */

			/*
			 * Check for hashjoinable operators.  (We don't bother setting the
			 * hashjoin info except in true join clauses.)
			 */
			check_hashjoinable(restrictinfo);

			/*
			 * Likewise, check if the clause is suitable to be used with a
			 * Memoize node to cache inner tuples during a parameterized
			 * nested loop.
			 */
			check_memoizable(restrictinfo);

			/*
			 * Add clause to the join lists of all the relevant relations.
			 */
			add_join_clause_to_rels(root, restrictinfo, relids);
		}
	}
	else
	{
		/*
		 * clause references no rels, and therefore we have no place to attach
		 * it.  Shouldn't get here if callers are working properly.
		 */
		elog(ERROR, "cannot cope with variable-free clause");
	}
}

/*
 * process_implied_equality
 *	  Create a restrictinfo item that says "item1 op item2", and push it
 *	  into the appropriate lists.  (In practice opno is always a btree
 *	  equality operator.)
 *
 * "qualscope" is the nominal syntactic level to impute to the restrictinfo.
 * This must contain at least all the rels used in the expressions, but it
 * is used only to set the qual application level when both exprs are
 * variable-free.  (Hence, it should usually match the join domain in which
 * the clause applies.)  Otherwise the qual is applied at the lowest join
 * level that provides all its variables.
 *
 * "security_level" is the security level to assign to the new restrictinfo.
 *
 * "both_const" indicates whether both items are known pseudo-constant;
 * in this case it is worth applying eval_const_expressions() in case we
 * can produce constant TRUE or constant FALSE.  (Otherwise it's not,
 * because the expressions went through eval_const_expressions already.)
 *
 * Returns the generated RestrictInfo, if any.  The result will be NULL
 * if both_const is true and we successfully reduced the clause to
 * constant TRUE.
 *
 * Note: this function will copy item1 and item2, but it is caller's
 * responsibility to make sure that the Relids parameters are fresh copies
 * not shared with other uses.
 *
 * Note: we do not do initialize_mergeclause_eclasses() here.  It is
 * caller's responsibility that left_ec/right_ec be set as necessary.
 */
/*
 * process_implied_equality - (中文)创建表达"item1 op item2"的 RestrictInfo
 * 并推入相应列表(实践中 opno 总是 btree 等值操作符)
 *
 * 【作用】由等价类机制生成"由传递性推导出的新等式"时调用:复制 item1/item2
 * (避免与原始结构共享子结构,特别是有子查询时),构建 OpExpr 条件;若
 * both_const 为真先对常量做 eval_const_expressions()——能约成恒真则返回
 * NULL,恒假则直接返回 constant FALSE 条件;否则计算 relids,伪常量标记,
 * 用 make_restrictinfo() 生成 RestrictInfo 交给
 * distribute_restrictinfo_to_rels() 分发。
 *
 * 【设计思想】等价类在合并两个类、发现"某表达式在另一上下文中等值"时,
 * 需要把隐含等式物化为真实条件供连接使用;both_const 时由于两常量可能
 * 相等或不等,先化简可避免留下无意义的连接条件。
 *
 * 【参数】
 *   root           —— 当前查询级的 PlannerInfo;
 *   opno           —— 等值操作符 OID;
 *   collation      —— 排序规则;
 *   item1, item2   —— 等式两侧表达式;
 *   qualscope      —— 应赋予新条件的名义语法层级(两个表达式都无 Var 时
 *                     用它决定求值位置,否则取能覆盖全部变量的最低连接层);
 *   security_level —— 安全级别;
 *   both_const     —— 两个 item 是否都是已知伪常量。
 * 【返回值】生成的 RestrictInfo;both_const 且成功化简为恒真时返回 NULL。
 */
RestrictInfo *
process_implied_equality(PlannerInfo *root,
						 Oid opno,
						 Oid collation,
						 Expr *item1,
						 Expr *item2,
						 Relids qualscope,
						 Index security_level,
						 bool both_const)
{
	RestrictInfo *restrictinfo;
	Node	   *clause;
	Relids		relids;
	bool		pseudoconstant = false;

	/*
	 * Build the new clause.  Copy to ensure it shares no substructure with
	 * original (this is necessary in case there are subselects in there...)
	 */
	clause = (Node *) make_opclause(opno,
									BOOLOID,	/* opresulttype */
									false,	/* opretset */
									copyObject(item1),
									copyObject(item2),
									InvalidOid,
									collation);

	/* If both constant, try to reduce to a boolean constant. */
	if (both_const)
	{
		clause = eval_const_expressions(root, clause);

		/* If we produced const TRUE, just drop the clause */
		if (clause && IsA(clause, Const))
		{
			Const	   *cclause = (Const *) clause;

			Assert(cclause->consttype == BOOLOID);
			if (!cclause->constisnull && DatumGetBool(cclause->constvalue))
				return NULL;
		}
	}

	/*
	 * The rest of this is a very cut-down version of distribute_qual_to_rels.
	 * We can skip most of the work therein, but there are a couple of special
	 * cases we still have to handle.
	 *
	 * Retrieve all relids mentioned within the possibly-simplified clause.
	 */
	relids = pull_varnos(root, clause);
	Assert(bms_is_subset(relids, qualscope));

	/*
	 * If the clause is variable-free, our normal heuristic for pushing it
	 * down to just the mentioned rels doesn't work, because there are none.
	 * Apply it as a gating qual at the appropriate level (see comments for
	 * get_join_domain_min_rels).
	 */
	if (bms_is_empty(relids))
	{
		/* eval at join domain's safe level */
		relids = get_join_domain_min_rels(root, qualscope);
		/* mark as gating qual */
		pseudoconstant = true;
		/* tell createplan.c to check for gating quals */
		root->hasPseudoConstantQuals = true;
	}

	/*
	 * Build the RestrictInfo node itself.
	 */
	restrictinfo = make_restrictinfo(root,
									 (Expr *) clause,
									 true,	/* is_pushed_down */
									 false, /* !has_clone */
									 false, /* !is_clone */
									 pseudoconstant,
									 security_level,
									 relids,
									 NULL,	/* incompatible_relids */
									 NULL); /* outer_relids */

	/*
	 * If it's a join clause, add vars used in the clause to targetlists of
	 * their relations, so that they will be emitted by the plan nodes that
	 * scan those relations (else they won't be available at the join node!).
	 *
	 * Typically, we'd have already done this when the component expressions
	 * were first seen by distribute_qual_to_rels; but it is possible that
	 * some of the Vars could have missed having that done because they only
	 * appeared in single-relation clauses originally.  So do it here for
	 * safety.
	 *
	 * See also rebuild_joinclause_attr_needed, which has to partially repeat
	 * this work after removal of an outer join.  (Since we will put this
	 * clause into the joininfo lists, that function needn't do any extra work
	 * to find it.)
	 */
	if (bms_membership(relids) == BMS_MULTIPLE)
	{
		List	   *vars = pull_var_clause(clause,
										   PVC_RECURSE_AGGREGATES |
										   PVC_RECURSE_WINDOWFUNCS |
										   PVC_INCLUDE_PLACEHOLDERS);

		add_vars_to_targetlist(root, vars, relids);
		list_free(vars);
	}

	/*
	 * Check mergejoinability.  This will usually succeed, since the op came
	 * from an EquivalenceClass; but we could have reduced the original clause
	 * to a constant.
	 */
	check_mergejoinable(restrictinfo);

	/*
	 * Note we don't do initialize_mergeclause_eclasses(); the caller can
	 * handle that much more cheaply than we can.  It's okay to call
	 * distribute_restrictinfo_to_rels() before that happens.
	 */

	/*
	 * Push the new clause into all the appropriate restrictinfo lists.
	 */
	distribute_restrictinfo_to_rels(root, restrictinfo);

	return restrictinfo;
}

/*
 * build_implied_join_equality --- build a RestrictInfo for a derived equality
 *
 * This overlaps the functionality of process_implied_equality(), but we
 * must not push the RestrictInfo into the joininfo tree.
 *
 * Note: this function will copy item1 and item2, but it is caller's
 * responsibility to make sure that the Relids parameters are fresh copies
 * not shared with other uses.
 *
 * Note: we do not do initialize_mergeclause_eclasses() here.  It is
 * caller's responsibility that left_ec/right_ec be set as necessary.
 */
/*
 * build_implied_join_equality - (中文)为推导出的等式构建 RestrictInfo
 *
 * 【作用】与 process_implied_equality() 功能重叠,但本函数只构建
 * RestrictInfo 并把 mergejoinable/hashjoinable/memoizable 标志设置好,
 * 不把条件推入 joininfo 树。复制 item1/item2 保证无共享子结构,用
 * make_restrictinfo() 生成 is_pushed_down=true、非伪常量、安全级别为
 * security_level 的条件。
 *
 * 【设计思想】某些场合(如 lateral 引用处理)只需要"物化一个推导等式的
 * 条件节点",而分发与放置由调用者另行完成,故不调用
 * distribute_restrictinfo_to_rels()。init 左/右等价类(initialize_merge
 * clause_eclasses)同样由调用者负责,此处成本更低。
 *
 * 【参数】
 *   root           —— 当前查询级的 PlannerInfo;
 *   opno           —— 等值操作符 OID;
 *   collation      —— 排序规则;
 *   item1, item2   —— 等式两侧表达式;
 *   qualscope      —— 条件的名义作用域;
 *   security_level —— 安全级别。
 * 【返回值】新建的 RestrictInfo。
 */
RestrictInfo *
build_implied_join_equality(PlannerInfo *root,
							Oid opno,
							Oid collation,
							Expr *item1,
							Expr *item2,
							Relids qualscope,
							Index security_level)
{
	RestrictInfo *restrictinfo;
	Expr	   *clause;

	/*
	 * Build the new clause.  Copy to ensure it shares no substructure with
	 * original (this is necessary in case there are subselects in there...)
	 */
	clause = make_opclause(opno,
						   BOOLOID, /* opresulttype */
						   false,	/* opretset */
						   copyObject(item1),
						   copyObject(item2),
						   InvalidOid,
						   collation);

	/*
	 * Build the RestrictInfo node itself.
	 */
	restrictinfo = make_restrictinfo(root,
									 clause,
									 true,	/* is_pushed_down */
									 false, /* !has_clone */
									 false, /* !is_clone */
									 false, /* pseudoconstant */
									 security_level,	/* security_level */
									 qualscope, /* required_relids */
									 NULL,	/* incompatible_relids */
									 NULL); /* outer_relids */

	/* Set mergejoinability/hashjoinability flags */
	check_mergejoinable(restrictinfo);
	check_hashjoinable(restrictinfo);
	check_memoizable(restrictinfo);

	return restrictinfo;
}

/*
 * get_join_domain_min_rels
 *	  Identify the appropriate join level for derived quals belonging
 *	  to the join domain with the given relids.
 *
 * When we derive a pseudoconstant (Var-free) clause from an EquivalenceClass,
 * we'd ideally apply the clause at the top level of the EC's join domain.
 * However, if there are any outer joins inside that domain that get commuted
 * with joins outside it, that leads to not finding a correct place to apply
 * the clause.  Instead, remove any lower outer joins from the relid set,
 * and apply the clause to just the remaining rels.  This still results in a
 * correct answer, since if the clause produces FALSE then the LHS of these
 * joins will be empty leading to an empty join result.
 *
 * However, there's no need to remove outer joins if this is the top-level
 * join domain of the query, since then there's nothing else to commute with.
 *
 * Note: it's tempting to use this in distribute_qual_to_rels where it's
 * dealing with pseudoconstant quals; but we can't because the necessary
 * SpecialJoinInfos aren't all formed at that point.
 *
 * The result is always freshly palloc'd; we do not modify domain_relids.
 */
/*
 * get_join_domain_min_rels - (中文)为属于给定 JoinDomain 的推导条件确定
 * 恰当的连接层次(用于无 Var 的伪常量条件)
 *
 * 【作用】当从等价类推导出无 Var(伪常量)条件时,理想上应把它放在该
 * 等价类所属 JoinDomain 的顶层求值;但若域内存在可被交换出去的下层左连接,
 * 顶层可能没有合适位置。故这里把域内可交换的左连接(及其右侧)从 relid
 * 集合中剔除,把条件应用到剩余关系上——由于条件为假时这些左连接的 LHS
 * 为空、整个连接结果为空,结果仍然正确。若本身是查询顶层 JoinDomain
 * (结果集等于 all_query_rels),则无需剔除(没有可交换的对象),直接返回。
 *
 * 【设计思想】这个"min rels"层级兼顾了正确性与尽量高位求值的愿望;不能
 * 在 distribute_qual_to_rels() 中使用它,因为那时 SpecialJoinInfo 尚未
 * 全部建立。返回的集合总是新分配的,不修改入参。
 *
 * 【参数】
 *   root          —— 当前查询级的 PlannerInfo;
 *   domain_relids —— JoinDomain 的关系集合。
 * 【返回值】应用条件的层级集合。
 */
static Relids
get_join_domain_min_rels(PlannerInfo *root, Relids domain_relids)
{
	Relids		result = bms_copy(domain_relids);
	ListCell   *lc;

	/* Top-level join domain? */
	if (bms_equal(result, root->all_query_rels))
		return result;

	/* Nope, look for lower outer joins that could potentially commute out */
	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(lc);

		if (sjinfo->jointype == JOIN_LEFT &&
			bms_is_member(sjinfo->ojrelid, result))
		{
			result = bms_del_member(result, sjinfo->ojrelid);
			result = bms_del_members(result, sjinfo->syn_righthand);
		}
	}
	return result;
}


/*
 * rebuild_joinclause_attr_needed
 *	  Put back attr_needed bits for Vars/PHVs needed for join clauses.
 *
 * This is used to rebuild attr_needed/ph_needed sets after removal of a
 * useless outer join.  It should match what distribute_qual_to_rels did,
 * except that we call add_vars_to_attr_needed not add_vars_to_targetlist.
 */
/*
 * rebuild_joinclause_attr_needed - (中文)在删除无用外连接后,为连接条件涉及
 * 的 Var/PHV 重建 attr_needed/ph_needed 位
 *
 * 【作用】与 distribute_qual_to_rels() 中"连接条件登记 Var 需求"的逻辑对应,
 * 但调用 add_vars_to_attr_needed()(列已在 targetlist)。扫描所有 baserel
 * 的 joininfo 列表,用 rinfo_serial 去重(克隆条件 serial 不唯一,须重复
 * 处理),对 required_relids 为多元素的条件抽取 Var/PHV 并登记;克隆条件
 * 的 where_needed 只取全部基表部分。由 analyzejoins.c 移除无用外连接后
 * 调用。
 *
 * 【设计思想】连接被删除后,原本只被被删连接需要的列可能不再需要向上传递,
 * 收缩 attr_needed 是后续进一步连接消除的前提。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无。
 */
void
rebuild_joinclause_attr_needed(PlannerInfo *root)
{
	/*
	 * We must examine all join clauses, but there's no value in processing
	 * any join clause more than once.  So it's slightly annoying that we have
	 * to find them via the per-base-relation joininfo lists.  Avoid duplicate
	 * processing by tracking the rinfo_serial numbers of join clauses we've
	 * already seen.  (This doesn't work for is_clone clauses, so we must
	 * waste effort on them.)
	 */
	Bitmapset  *seen_serials = NULL;
	Index		rti;

	/* Scan all baserels for join clauses */
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];
		ListCell   *lc;

		if (brel == NULL)
			continue;
		if (brel->reloptkind != RELOPT_BASEREL)
			continue;

		foreach(lc, brel->joininfo)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
			Relids		relids = rinfo->required_relids;

			if (!rinfo->is_clone)	/* else serial number is not unique */
			{
				if (bms_is_member(rinfo->rinfo_serial, seen_serials))
					continue;	/* saw it already */
				seen_serials = bms_add_member(seen_serials,
											  rinfo->rinfo_serial);
			}

			if (bms_membership(relids) == BMS_MULTIPLE)
			{
				List	   *vars = pull_var_clause((Node *) rinfo->clause,
												   PVC_RECURSE_AGGREGATES |
												   PVC_RECURSE_WINDOWFUNCS |
												   PVC_INCLUDE_PLACEHOLDERS);
				Relids		where_needed;

				if (rinfo->is_clone)
					where_needed = bms_intersect(relids, root->all_baserels);
				else
					where_needed = relids;
				add_vars_to_attr_needed(root, vars, where_needed);
				list_free(vars);
			}
		}
	}
}


/*
 * match_foreign_keys_to_quals
 *		Match foreign-key constraints to equivalence classes and join quals
 *
 * The idea here is to see which query join conditions match equality
 * constraints of a foreign-key relationship.  For such join conditions,
 * we can use the FK semantics to make selectivity estimates that are more
 * reliable than estimating from statistics, especially for multiple-column
 * FKs, where the normal assumption of independent conditions tends to fail.
 *
 * In this function we annotate the ForeignKeyOptInfos in root->fkey_list
 * with info about which eclasses and join qual clauses they match, and
 * discard any ForeignKeyOptInfos that are irrelevant for the query.
 */
/*
 * match_foreign_keys_to_quals - (中文)把外键约束与等价类/连接条件匹配,
 * 供更可靠的选择率估算使用
 *
 * 【作用】对 root->fkey_list 中每个 ForeignKeyOptInfo:
 * - 跳过无 RelOptInfo(不在 jointree、被连接消除移除)或非 BASEREL 的关系;
 * - 逐列尝试两路匹配:①用 match_eclasses_to_foreign_key_col() 在等价类中
 *   找匹配列(简单内连接通常走这条,统计 nmatched_ec、nconst_ec);②否则
 *   扫描 con_rel 的 joininfo,找形如 ref_var = con_var(或反向,须检查交换
 *   算子)且算子为外键等值算子的条件,记录到 fkinfo->rinfos[colno] 并累计
 *   nmatched_ri / nmatched_rcols;
 * - 仅保留完全匹配(nmatched_ec + nmatched_rcols == nkeys)的外键,其余丢弃,
 *   以此替换 root->fkey_list。
 *
 * 【设计思想】外键匹配能让多列 FK 的选择率估计摆脱"各列独立"的强假设
 * (对多列外键尤其失效),从而显著提升估算可靠性。匹配来源为等价类或
 * "松散"条件(被外连接等拒绝进入 EC 的语法匹配条件)。
 *
 * 【参数】root —— 当前查询级的 PlannerInfo。
 * 【返回值】无,更新 root->fkey_list 与各 fkinfo 字段。
 */
void
match_foreign_keys_to_quals(PlannerInfo *root)
{
	List	   *newlist = NIL;
	ListCell   *lc;

	foreach(lc, root->fkey_list)
	{
		ForeignKeyOptInfo *fkinfo = (ForeignKeyOptInfo *) lfirst(lc);
		RelOptInfo *con_rel;
		RelOptInfo *ref_rel;
		int			colno;

		/*
		 * Either relid might identify a rel that is in the query's rtable but
		 * isn't referenced by the jointree, or has been removed by join
		 * removal, so that it won't have a RelOptInfo.  Hence don't use
		 * find_base_rel() here.  We can ignore such FKs.
		 */
		if (fkinfo->con_relid >= root->simple_rel_array_size ||
			fkinfo->ref_relid >= root->simple_rel_array_size)
			continue;			/* just paranoia */
		con_rel = root->simple_rel_array[fkinfo->con_relid];
		if (con_rel == NULL)
			continue;
		ref_rel = root->simple_rel_array[fkinfo->ref_relid];
		if (ref_rel == NULL)
			continue;

		/*
		 * Ignore FK unless both rels are baserels.  This gets rid of FKs that
		 * link to inheritance child rels (otherrels).
		 */
		if (con_rel->reloptkind != RELOPT_BASEREL ||
			ref_rel->reloptkind != RELOPT_BASEREL)
			continue;

		/*
		 * Scan the columns and try to match them to eclasses and quals.
		 *
		 * Note: for simple inner joins, any match should be in an eclass.
		 * "Loose" quals that syntactically match an FK equality must have
		 * been rejected for EC status because they are outer-join quals or
		 * similar.  We can still consider them to match the FK.
		 */
		for (colno = 0; colno < fkinfo->nkeys; colno++)
		{
			EquivalenceClass *ec;
			AttrNumber	con_attno,
						ref_attno;
			Oid			fpeqop;
			ListCell   *lc2;

			ec = match_eclasses_to_foreign_key_col(root, fkinfo, colno);
			/* Don't bother looking for loose quals if we got an EC match */
			if (ec != NULL)
			{
				fkinfo->nmatched_ec++;
				if (ec->ec_has_const)
					fkinfo->nconst_ec++;
				continue;
			}

			/*
			 * Scan joininfo list for relevant clauses.  Either rel's joininfo
			 * list would do equally well; we use con_rel's.
			 */
			con_attno = fkinfo->conkey[colno];
			ref_attno = fkinfo->confkey[colno];
			fpeqop = InvalidOid;	/* we'll look this up only if needed */

			foreach(lc2, con_rel->joininfo)
			{
				RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc2);
				OpExpr	   *clause = (OpExpr *) rinfo->clause;
				Var		   *leftvar;
				Var		   *rightvar;

				/* Only binary OpExprs are useful for consideration */
				if (!IsA(clause, OpExpr) ||
					list_length(clause->args) != 2)
					continue;
				leftvar = (Var *) get_leftop((Expr *) clause);
				rightvar = (Var *) get_rightop((Expr *) clause);

				/* Operands must be Vars, possibly with RelabelType */
				while (leftvar && IsA(leftvar, RelabelType))
					leftvar = (Var *) ((RelabelType *) leftvar)->arg;
				if (!(leftvar && IsA(leftvar, Var)))
					continue;
				while (rightvar && IsA(rightvar, RelabelType))
					rightvar = (Var *) ((RelabelType *) rightvar)->arg;
				if (!(rightvar && IsA(rightvar, Var)))
					continue;

				/* Now try to match the vars to the current foreign key cols */
				if (fkinfo->ref_relid == leftvar->varno &&
					ref_attno == leftvar->varattno &&
					fkinfo->con_relid == rightvar->varno &&
					con_attno == rightvar->varattno)
				{
					/* Vars match, but is it the right operator? */
					if (clause->opno == fkinfo->conpfeqop[colno])
					{
						fkinfo->rinfos[colno] = lappend(fkinfo->rinfos[colno],
														rinfo);
						fkinfo->nmatched_ri++;
					}
				}
				else if (fkinfo->ref_relid == rightvar->varno &&
						 ref_attno == rightvar->varattno &&
						 fkinfo->con_relid == leftvar->varno &&
						 con_attno == leftvar->varattno)
				{
					/*
					 * Reverse match, must check commutator operator.  Look it
					 * up if we didn't already.  (In the worst case we might
					 * do multiple lookups here, but that would require an FK
					 * equality operator without commutator, which is
					 * unlikely.)
					 */
					if (!OidIsValid(fpeqop))
						fpeqop = get_commutator(fkinfo->conpfeqop[colno]);
					if (clause->opno == fpeqop)
					{
						fkinfo->rinfos[colno] = lappend(fkinfo->rinfos[colno],
														rinfo);
						fkinfo->nmatched_ri++;
					}
				}
			}
			/* If we found any matching loose quals, count col as matched */
			if (fkinfo->rinfos[colno])
				fkinfo->nmatched_rcols++;
		}

		/*
		 * Currently, we drop multicolumn FKs that aren't fully matched to the
		 * query.  Later we might figure out how to derive some sort of
		 * estimate from them, in which case this test should be weakened to
		 * "if ((fkinfo->nmatched_ec + fkinfo->nmatched_rcols) > 0)".
		 */
		if ((fkinfo->nmatched_ec + fkinfo->nmatched_rcols) == fkinfo->nkeys)
			newlist = lappend(newlist, fkinfo);
	}
	/* Replace fkey_list, thereby discarding any useless entries */
	root->fkey_list = newlist;
}


/*****************************************************************************
 *
 *	 CHECKS FOR MERGEJOINABLE AND HASHJOINABLE CLAUSES
 *
 *****************************************************************************/

/*
 * check_mergejoinable
 *	  If the restrictinfo's clause is mergejoinable, set the mergejoin
 *	  info fields in the restrictinfo.
 *
 *	  Currently, we support mergejoin for binary opclauses where
 *	 the operator is a mergejoinable operator.  The arguments can be
 *	 anything --- as long as there are no volatile functions in them.
 */
/*
 * check_mergejoinable - (中文)若条件可 mergejoin,设置 RestrictInfo 的
 * mergejoin 相关字段
 *
 * 【作用】对非伪常量、二元 OpExpr 条件,检查操作符是否 mergejoinable
 * (op_mergejoinable 且两侧无 volatile 函数);若是,用
 * get_mergejoin_opfamilies() 取得操作族列表存入 mergeopfamilies。
 *
 * 【设计思想】mergejoin 只需要"等值且可比序";op_mergejoinable 只是提示,
 * 若操作符最终不在任何 btree 操作族中,mergeopfamilies 保持 NIL,条件仍
 * 视为不可 mergejoin。对每个条件(不限于连接条件)都检查,是为了发现同一
 * 关系内 Var 之间、Var 与常量之间的等值关系。
 *
 * 【参数】restrictinfo —— 待检查的条件。
 * 【返回值】无。
 */
static void
check_mergejoinable(RestrictInfo *restrictinfo)
{
	Expr	   *clause = restrictinfo->clause;
	Oid			opno;
	Node	   *leftarg;

	if (restrictinfo->pseudoconstant)
		return;
	if (!is_opclause(clause))
		return;
	if (list_length(((OpExpr *) clause)->args) != 2)
		return;

	opno = ((OpExpr *) clause)->opno;
	leftarg = linitial(((OpExpr *) clause)->args);

	if (op_mergejoinable(opno, exprType(leftarg)) &&
		!contain_volatile_functions((Node *) restrictinfo))
		restrictinfo->mergeopfamilies = get_mergejoin_opfamilies(opno);

	/*
	 * Note: op_mergejoinable is just a hint; if we fail to find the operator
	 * in any btree opfamilies, mergeopfamilies remains NIL and so the clause
	 * is not treated as mergejoinable.
	 */
}

/*
 * check_hashjoinable
 *	  If the restrictinfo's clause is hashjoinable, set the hashjoin
 *	  info fields in the restrictinfo.
 *
 *	  Currently, we support hashjoin for binary opclauses where
 *	 the operator is a hashjoinable operator.  The arguments can be
 *	 anything --- as long as there are no volatile functions in them.
 */
/*
 * check_hashjoinable - (中文)若条件可 hashjoin,设置 RestrictInfo 的
 * hashjoin 相关字段
 *
 * 【作用】对非伪常量、二元 OpExpr 条件,检查操作符是否 hashjoinable
 * (op_hashjoinable 且无 volatile 函数);若是,把操作符 OID 存入
 * restrictinfo->hashjoinoperator。与 check_mergejoinable 类似,仅在真
 * 连接条件上调用(distribute_restrictinfo_to_rels 中)。
 *
 * 【参数】restrictinfo —— 待检查的条件。
 * 【返回值】无。
 */
static void
check_hashjoinable(RestrictInfo *restrictinfo)
{
	Expr	   *clause = restrictinfo->clause;
	Oid			opno;
	Node	   *leftarg;

	if (restrictinfo->pseudoconstant)
		return;
	if (!is_opclause(clause))
		return;
	if (list_length(((OpExpr *) clause)->args) != 2)
		return;

	opno = ((OpExpr *) clause)->opno;
	leftarg = linitial(((OpExpr *) clause)->args);

	if (op_hashjoinable(opno, exprType(leftarg)) &&
		!contain_volatile_functions((Node *) restrictinfo))
		restrictinfo->hashjoinoperator = opno;
}

/*
 * check_memoizable
 *	  If the restrictinfo's clause is suitable to be used for a Memoize node,
 *	  set the left_hasheqoperator and right_hasheqoperator to the hash equality
 *	  operator that will be needed during caching.
 */
/*
 * check_memoizable - (中文)若条件适合用于 Memoize 节点缓存,设置左右侧的
 * 哈希等值操作符
 *
 * 【作用】对非伪常量、二元 OpExpr 条件,分别查左右操作数类型的类型缓存:
 * 若该类型既有哈希过程(hash_proc)又有等值操作符(eq_opr),就把等值操作符
 * 记入 left_hasheqoperator / right_hasheqoperator;两侧类型相同时复用同一
 * TypeCacheEntry,否则为右类型单独查询。
 *
 * 【设计思想】Memoize 在参数化嵌套循环中缓存内侧元组,须按参数值哈希;
 * 左右两侧的操作数类型都可能作为参数键,故各存一个等值操作符。
 *
 * 【参数】restrictinfo —— 待检查的条件。
 * 【返回值】无。
 */
static void
check_memoizable(RestrictInfo *restrictinfo)
{
	TypeCacheEntry *typentry;
	Expr	   *clause = restrictinfo->clause;
	Oid			lefttype;
	Oid			righttype;

	if (restrictinfo->pseudoconstant)
		return;
	if (!is_opclause(clause))
		return;
	if (list_length(((OpExpr *) clause)->args) != 2)
		return;

	lefttype = exprType(linitial(((OpExpr *) clause)->args));

	typentry = lookup_type_cache(lefttype, TYPECACHE_HASH_PROC |
								 TYPECACHE_EQ_OPR);

	if (OidIsValid(typentry->hash_proc) && OidIsValid(typentry->eq_opr))
		restrictinfo->left_hasheqoperator = typentry->eq_opr;

	righttype = exprType(lsecond(((OpExpr *) clause)->args));

	/*
	 * Lookup the right type, unless it's the same as the left type, in which
	 * case typentry is already pointing to the required TypeCacheEntry.
	 */
	if (lefttype != righttype)
		typentry = lookup_type_cache(righttype, TYPECACHE_HASH_PROC |
									 TYPECACHE_EQ_OPR);

	if (OidIsValid(typentry->hash_proc) && OidIsValid(typentry->eq_opr))
		restrictinfo->right_hasheqoperator = typentry->eq_opr;
}
