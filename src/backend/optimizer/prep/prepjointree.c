/*-------------------------------------------------------------------------
 *
 * prepjointree.c
 *	  Planner preprocessing for subqueries and join tree manipulation.
 *
 * NOTE: the intended sequence for invoking these operations is
 *		preprocess_relation_rtes
 *		replace_empty_jointree
 *		pull_up_sublinks
 *		preprocess_function_rtes
 *		pull_up_subqueries
 *		flatten_simple_union_all
 *		do expression preprocessing (including flattening JOIN alias vars)
 *		reduce_outer_joins
 *		remove_useless_result_rtes
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 优化器"预处理器"(prep 模块)中最核心、最庞大的成员,
 * 负责子查询处理与连接树(join tree)的改写。目标是把 SQL 语义层面复杂的
 * 查询树变换成适合路径枚举的、扁平的、语义被显式化的形态,是一切后续
 * 优化(等价类合并、外连接简化、路径生成)的前提。
 *
 * 【本模块的职责(按推荐的调用顺序)】
 * 1. preprocess_relation_rtes:扫描关系 RTE,清理无子表的 inh 标志、收集
 *    NOT NULL 约束、展开虚拟生成列;
 * 2. replace_empty_jointree:为空的 FROM 子句插入 RTE_RESULT 占位关系;
 * 3. pull_up_sublinks:把顶层 WHERE / JOIN ON 中的 ANY/EXISTS SubLink 上提
 *    为半连接(SEMI)/反连接(ANTI);
 * 4. preprocess_function_rtes:对 FROM 中的函数 RTE 做常量化简与内联;
 * 5. pull_up_subqueries:把"简单"的子查询、纯 UNION ALL、简单 VALUES、常量
 *    函数上提到父查询(本文件的重头戏);
 * 6. flatten_simple_union_all:把顶层纯 UNION ALL 展平成 append 关系;
 * 7. reduce_outer_joins:把可化简的外连接降级为内连接 / 反连接;
 * 8. remove_useless_result_rtes:删除无用的 RTE_RESULT 并裁剪单子 FromExpr。
 *
 * 【设计思想】
 * - 子查询上提(pull up)是把子查询的叶子关系、表达式并入父查询,把子查询
 *   的 RTE 用其 jointree 替换;难点在于"被上提子查询的输出 Var"必须遍及
 *   全树替换为对应表达式(pullup_replace_vars 及其回调),并妥善处理
 *   LATERAL 引用、外连接可空性(nullingrels)、PlaceHolderVar 包裹与
 *   varlevelsup 调整;因此本文件大量使用"可修改副本 + 递归后重新校验"的
 *   策略(先试、失败则放弃并保留原样);
 * - 半/反连接识别:WHERE x IN (sub)/EXISTS(sub) 在限定条件允许的形态下
 *   等价于半连接,NOT IN / NOT EXISTS 等价于反连接,但仅限顶层 AND 结构,
 *   因为 NULL 的三值语义不允许任意嵌套处做这种变换;
 * - 外连接简化(reduce_outer_joins)利用"严格谓词 + 非空列"的推理:某列被
 *   上层强制非空,而它来自可空侧,则外连接行必然被滤掉,外连接可降级;
 *   "强制为 NULL"则可把 LEFT JOIN 变 ANTI JOIN;RIGHT 统一翻转为 LEFT;
 * - RTE_RESULT 只返回一行且无输出列,内连接时可直接删除,配合
 *   remove_nulling_relids 清理可空性标记,并可据此裁剪冗余的 FromExpr。
 *
 * 【核心数据结构】
 * - pullup_replace_vars_context:上提替换的上下文(目标 tlist、varno、
 *   nullinfo、wrap_option、缓存数组 rv_cache 等);
 * - nullingrel_info:记录每个叶子 RTE 被哪些外连接潜在置空(per-RTE 的
 *   nullingrels 位图数组);
 * - reduce_outer_joins_pass1_state / pass2_state / partial_state:外连接
 *   简化的两遍扫描状态(可空侧集合、强制非空/强制 NULL 集合、已降级连接);
 * - PlannerInfo 的 append_rel_list / join_info_list / placeholder_list /
 *   root->parse 等在整个过程中被持续维护。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/prep/prepjointree.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/table.h"
#include "catalog/pg_type.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/multibitmapset.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/placeholder.h"
#include "optimizer/plancat.h"
#include "optimizer/prep.h"
#include "optimizer/subselect.h"
#include "optimizer/tlist.h"
#include "parser/parse_relation.h"
#include "parser/parsetree.h"
#include "rewrite/rewriteHandler.h"
#include "rewrite/rewriteManip.h"
#include "utils/rel.h"


typedef struct nullingrel_info
{
	/*
	 * For each leaf RTE, nullingrels[rti] is the set of relids of outer joins
	 * that potentially null that RTE.
	 */
	Relids	   *nullingrels;
	/* Length of range table (maximum index in nullingrels[]) */
	int			rtlength;		/* used only for assertion checks */
} nullingrel_info;

/* Options for wrapping an expression for identification purposes */
typedef enum ReplaceWrapOption
{
	REPLACE_WRAP_NONE,			/* no expressions need to be wrapped */
	REPLACE_WRAP_ALL,			/* all expressions need to be wrapped */
	REPLACE_WRAP_VARFREE,		/* variable-free expressions need to be
								 * wrapped */
} ReplaceWrapOption;

typedef struct pullup_replace_vars_context
{
	PlannerInfo *root;
	List	   *targetlist;		/* tlist of subquery being pulled up */
	RangeTblEntry *target_rte;	/* RTE of subquery */
	int			result_relation;	/* the index of the result relation in the
									 * rewritten query */
	Relids		relids;			/* relids within subquery, as numbered after
								 * pullup (set only if target_rte->lateral) */
	nullingrel_info *nullinfo;	/* per-RTE nullingrel info (set only if
								 * target_rte->lateral) */
	bool	   *outer_hasSubLinks;	/* -> outer query's hasSubLinks */
	int			varno;			/* varno of subquery */
	ReplaceWrapOption wrap_option;	/* do we need certain outputs to be PHVs? */
	Node	  **rv_cache;		/* cache for results with PHVs */
} pullup_replace_vars_context;

typedef struct reduce_outer_joins_pass1_state
{
	Relids		relids;			/* base relids within this subtree */
	bool		contains_outer; /* does subtree contain outer join(s)? */
	Relids		nullable_rels;	/* base relids that are nullable within this
								 * subtree */
	List	   *sub_states;		/* List of states for subtree components */
} reduce_outer_joins_pass1_state;

typedef struct reduce_outer_joins_pass2_state
{
	Relids		inner_reduced;	/* OJ relids reduced to plain inner joins */
	List	   *partial_reduced;	/* List of partially reduced FULL joins */
} reduce_outer_joins_pass2_state;

typedef struct reduce_outer_joins_partial_state
{
	int			full_join_rti;	/* RT index of a formerly-FULL join */
	Relids		unreduced_side; /* relids in its still-nullable side */
} reduce_outer_joins_partial_state;

static Query *expand_virtual_generated_columns(PlannerInfo *root, Query *parse,
											   RangeTblEntry *rte, int rt_index,
											   Relation relation);
static Node *pull_up_sublinks_jointree_recurse(PlannerInfo *root, Node *jtnode,
											   Relids *relids);
static Node *pull_up_sublinks_qual_recurse(PlannerInfo *root, Node *node,
										   Node **jtlink1, Relids available_rels1,
										   Node **jtlink2, Relids available_rels2);
static Node *pull_up_subqueries_recurse(PlannerInfo *root, Node *jtnode,
										JoinExpr *lowest_outer_join,
										AppendRelInfo *containing_appendrel);
static Node *pull_up_simple_subquery(PlannerInfo *root, Node *jtnode,
									 RangeTblEntry *rte,
									 JoinExpr *lowest_outer_join,
									 AppendRelInfo *containing_appendrel);
static Node *pull_up_simple_union_all(PlannerInfo *root, Node *jtnode,
									  RangeTblEntry *rte);
static void pull_up_union_leaf_queries(Node *setOp, PlannerInfo *root,
									   int parentRTindex, Query *setOpQuery,
									   int childRToffset);
static void make_setop_translation_list(Query *query, int newvarno,
										AppendRelInfo *appinfo);
static bool is_simple_subquery(PlannerInfo *root, Query *subquery,
							   RangeTblEntry *rte,
							   JoinExpr *lowest_outer_join);
static Node *pull_up_simple_values(PlannerInfo *root, Node *jtnode,
								   RangeTblEntry *rte);
static bool is_simple_values(PlannerInfo *root, RangeTblEntry *rte);
static Node *pull_up_constant_function(PlannerInfo *root, Node *jtnode,
									   RangeTblEntry *rte,
									   AppendRelInfo *containing_appendrel);
static bool is_simple_union_all(Query *subquery);
static bool is_simple_union_all_recurse(Node *setOp, Query *setOpQuery,
										List *colTypes);
static bool is_safe_append_member(Query *subquery);
static bool jointree_contains_lateral_outer_refs(PlannerInfo *root,
												 Node *jtnode, bool restricted,
												 Relids safe_upper_varnos);
static void perform_pullup_replace_vars(PlannerInfo *root,
										pullup_replace_vars_context *rvcontext,
										AppendRelInfo *containing_appendrel);
static void replace_vars_in_jointree(Node *jtnode,
									 pullup_replace_vars_context *context);
static Node *pullup_replace_vars(Node *expr,
								 pullup_replace_vars_context *context);
static Node *pullup_replace_vars_callback(const Var *var,
										  replace_rte_variables_context *context);
static Query *pullup_replace_vars_subquery(Query *query,
										   pullup_replace_vars_context *context);
static reduce_outer_joins_pass1_state *reduce_outer_joins_pass1(Node *jtnode);
static void reduce_outer_joins_pass2(Node *jtnode,
									 reduce_outer_joins_pass1_state *state1,
									 reduce_outer_joins_pass2_state *state2,
									 PlannerInfo *root,
									 Relids nonnullable_rels,
									 List *forced_null_vars);
static void report_reduced_full_join(reduce_outer_joins_pass2_state *state2,
									 int rtindex, Relids relids);
static bool has_notnull_forced_var(PlannerInfo *root, List *forced_null_vars,
								   reduce_outer_joins_pass1_state *right_state);
static Node *remove_useless_results_recurse(PlannerInfo *root, Node *jtnode,
											Relids baserels,
											Node **parent_quals,
											Relids *dropped_outer_joins);
static int	get_result_relid(PlannerInfo *root, Node *jtnode);
static void remove_result_refs(PlannerInfo *root, int varno, Node *newjtloc);
static bool find_dependent_phvs(PlannerInfo *root, int varno, Relids baserels);
static bool find_dependent_phvs_in_jointree(PlannerInfo *root,
											Node *node, int varno,
											Relids baserels);
static void substitute_phv_relids(Node *node,
								  int varno, Relids subrelids);
static void fix_append_rel_relids(PlannerInfo *root, int varno,
								  Relids subrelids);
static Node *find_jointree_node_for_rel(Node *jtnode, int relid);
static nullingrel_info *get_nullingrels(Query *parse);
static void get_nullingrels_recurse(Node *jtnode, Relids upper_nullingrels,
									nullingrel_info *info);


/*
 * transform_MERGE_to_join
 *		Replace a MERGE's jointree to also include the target relation.
 */
/*
 * transform_MERGE_to_join - (中文)把 MERGE 查询的连接树改写为包含目标表的
 * 连接,使 MERGE 可复用普通连接/过滤的执行框架
 *
 * 【作用】对 CMD_MERGE 查询:根据各 WHEN 动作类型决定所需连接类型(有
 * NOT MATCHED BY SOURCE 与 BY TARGET 动作用 FULL,只有 BY SOURCE 用
 * LEFT,只有 BY TARGET 用 RIGHT,否则 INNER),构造一个 RTE_JOIN(把目标表
 * 与源表连接,连接条件为 parse->mergeJoinCondition),把源表的 jointree
 * 换成这个 JoinExpr;并为可空侧 Var 添加 nullingrels 标记、给合并连接条件
 * 补充"源表 IS NOT NULL"守卫(见设计思想)。非 MERGE 查询直接返回。
 *
 * 【设计思想】
 * - 执行器用"连接子计划的输出"区分 MATCHED / NOT MATCHED BY SOURCE 等
 *   情况:因此源侧 Var 在被可空化时必须带 nullingrels,这样 ModifyTable
 *   之上(ExecMergeMatched 判 MATCHED 与否)才分辨得清;
 * - join 条件本身在连接内部使用时是"内部版本",同时给上层留一份加过
 *   nullingrels 的副本:上层需要靠它区分 MATCHED 与 NOT MATCHED BY SOURCE;
 * - 若 join 条件非严格(如 src.col IS NOT DISTINCT FROM tgt.col),执行器
 *   用连接输出重检时可能误判,故在其前 AND 上"src 整行 IS NOT NULL",
 *   保证按连接子计划输出重算时行为正确;
 * - 目标表是触发器可更新视图时其 RTE 是展开后的视图子查询,由
 *   parse->mergeTargetRelation 定位;源表(通常一个)取 jointree->fromlist
 *   的唯一成员。
 *
 * 【参数】parse —— 待改写的 MERGE 查询(就地修改其 jointree / rtable /
 * mergeJoinCondition / targetList 等)。
 * 【返回值】无。
 */
void
transform_MERGE_to_join(Query *parse)
{
	RangeTblEntry *joinrte;
	JoinExpr   *joinexpr;
	bool		have_action[NUM_MERGE_MATCH_KINDS];
	JoinType	jointype;
	int			joinrti;
	List	   *vars;
	RangeTblRef *rtr;
	FromExpr   *target;
	Node	   *source;
	int			sourcerti;

	if (parse->commandType != CMD_MERGE)
		return;

	/* XXX probably bogus */
	vars = NIL;

	/*
	 * Work out what kind of join is required.  If there any WHEN NOT MATCHED
	 * BY SOURCE/TARGET actions, an outer join is required so that we process
	 * all unmatched tuples from the source and/or target relations.
	 * Otherwise, we can use an inner join.
	 */
	have_action[MERGE_WHEN_MATCHED] = false;
	have_action[MERGE_WHEN_NOT_MATCHED_BY_SOURCE] = false;
	have_action[MERGE_WHEN_NOT_MATCHED_BY_TARGET] = false;

	foreach_node(MergeAction, action, parse->mergeActionList)
	{
		if (action->commandType != CMD_NOTHING)
			have_action[action->matchKind] = true;
	}

	if (have_action[MERGE_WHEN_NOT_MATCHED_BY_SOURCE] &&
		have_action[MERGE_WHEN_NOT_MATCHED_BY_TARGET])
		jointype = JOIN_FULL;
	else if (have_action[MERGE_WHEN_NOT_MATCHED_BY_SOURCE])
		jointype = JOIN_LEFT;
	else if (have_action[MERGE_WHEN_NOT_MATCHED_BY_TARGET])
		jointype = JOIN_RIGHT;
	else
		jointype = JOIN_INNER;

	/* Manufacture a join RTE to use. */
	joinrte = makeNode(RangeTblEntry);
	joinrte->rtekind = RTE_JOIN;
	joinrte->jointype = jointype;
	joinrte->joinmergedcols = 0;
	joinrte->joinaliasvars = vars;
	joinrte->joinleftcols = NIL;	/* MERGE does not allow JOIN USING */
	joinrte->joinrightcols = NIL;	/* ditto */
	joinrte->join_using_alias = NULL;

	joinrte->alias = NULL;
	joinrte->eref = makeAlias("*MERGE*", NIL);
	joinrte->lateral = false;
	joinrte->inh = false;
	joinrte->inFromCl = true;

	/*
	 * Add completed RTE to pstate's range table list, so that we know its
	 * index.
	 */
	parse->rtable = lappend(parse->rtable, joinrte);
	joinrti = list_length(parse->rtable);

	/*
	 * Create a JOIN between the target and the source relation.
	 *
	 * Here the target is identified by parse->mergeTargetRelation.  For a
	 * regular table, this will equal parse->resultRelation, but for a
	 * trigger-updatable view, it will be the expanded view subquery that we
	 * need to pull data from.
	 *
	 * The source relation is in parse->jointree->fromlist, but any quals in
	 * parse->jointree->quals are restrictions on the target relation (if the
	 * target relation is an auto-updatable view).
	 */
	/* target rel, with any quals */
	rtr = makeNode(RangeTblRef);
	rtr->rtindex = parse->mergeTargetRelation;
	target = makeFromExpr(list_make1(rtr), parse->jointree->quals);

	/* source rel (expect exactly one -- see transformMergeStmt()) */
	Assert(list_length(parse->jointree->fromlist) == 1);
	source = linitial(parse->jointree->fromlist);

	/*
	 * index of source rel (expect either a RangeTblRef or a JoinExpr -- see
	 * transformFromClauseItem()).
	 */
	if (IsA(source, RangeTblRef))
		sourcerti = ((RangeTblRef *) source)->rtindex;
	else if (IsA(source, JoinExpr))
		sourcerti = ((JoinExpr *) source)->rtindex;
	else
	{
		elog(ERROR, "unrecognized source node type: %d",
			 (int) nodeTag(source));
		sourcerti = 0;			/* keep compiler quiet */
	}

	/* Join the source and target */
	joinexpr = makeNode(JoinExpr);
	joinexpr->jointype = jointype;
	joinexpr->isNatural = false;
	joinexpr->larg = (Node *) target;
	joinexpr->rarg = source;
	joinexpr->usingClause = NIL;
	joinexpr->join_using_alias = NULL;
	joinexpr->quals = parse->mergeJoinCondition;
	joinexpr->alias = NULL;
	joinexpr->rtindex = joinrti;

	/* Make the new join be the sole entry in the query's jointree */
	parse->jointree->fromlist = list_make1(joinexpr);
	parse->jointree->quals = NULL;

	/*
	 * If necessary, mark parse->targetlist entries that refer to the target
	 * as nullable by the join.  Normally the targetlist will be empty for a
	 * MERGE, but if the target is a trigger-updatable view, it will contain a
	 * whole-row Var referring to the expanded view query.
	 */
	if (parse->targetList != NIL &&
		(jointype == JOIN_RIGHT || jointype == JOIN_FULL))
		parse->targetList = (List *)
			add_nulling_relids((Node *) parse->targetList,
							   bms_make_singleton(parse->mergeTargetRelation),
							   bms_make_singleton(joinrti));

	/*
	 * If the source relation is on the outer side of the join, mark any
	 * source relation Vars in the join condition, actions, and RETURNING list
	 * as nullable by the join.  These Vars will be added to the targetlist by
	 * preprocess_targetlist(), so it's important to mark them correctly here.
	 *
	 * It might seem that this is not necessary for Vars in the join
	 * condition, since it is inside the join, but it is also needed above the
	 * join (in the ModifyTable node) to distinguish between the MATCHED and
	 * NOT MATCHED BY SOURCE cases -- see ExecMergeMatched().  Note that this
	 * creates a modified copy of the join condition, for use above the join,
	 * without modifying the original join condition, inside the join.
	 */
	if (jointype == JOIN_LEFT || jointype == JOIN_FULL)
	{
		parse->mergeJoinCondition =
			add_nulling_relids(parse->mergeJoinCondition,
							   bms_make_singleton(sourcerti),
							   bms_make_singleton(joinrti));

		foreach_node(MergeAction, action, parse->mergeActionList)
		{
			action->qual =
				add_nulling_relids(action->qual,
								   bms_make_singleton(sourcerti),
								   bms_make_singleton(joinrti));

			action->targetList = (List *)
				add_nulling_relids((Node *) action->targetList,
								   bms_make_singleton(sourcerti),
								   bms_make_singleton(joinrti));
		}

		parse->returningList = (List *)
			add_nulling_relids((Node *) parse->returningList,
							   bms_make_singleton(sourcerti),
							   bms_make_singleton(joinrti));
	}

	/*
	 * If there are any WHEN NOT MATCHED BY SOURCE actions, the executor will
	 * use the join condition to distinguish between MATCHED and NOT MATCHED
	 * BY SOURCE cases.  Otherwise, it's no longer needed, and we set it to
	 * NULL, saving cycles during planning and execution.
	 *
	 * We need to be careful though: the executor evaluates this condition
	 * using the output of the join subplan node, which nulls the output from
	 * the source relation when the join condition doesn't match.  That risks
	 * producing incorrect results when rechecking using a "non-strict" join
	 * condition, such as "src.col IS NOT DISTINCT FROM tgt.col".  To guard
	 * against that, we add an additional "src IS NOT NULL" check to the join
	 * condition, so that it does the right thing when performing a recheck
	 * based on the output of the join subplan.
	 */
	if (have_action[MERGE_WHEN_NOT_MATCHED_BY_SOURCE])
	{
		Var		   *var;
		NullTest   *ntest;

		/* source wholerow Var (nullable by the new join) */
		var = makeWholeRowVar(rt_fetch(sourcerti, parse->rtable),
							  sourcerti, 0, false);
		var->varnullingrels = bms_make_singleton(joinrti);

		/* "src IS NOT NULL" check */
		ntest = makeNode(NullTest);
		ntest->arg = (Expr *) var;
		ntest->nulltesttype = IS_NOT_NULL;
		ntest->argisrow = false;
		ntest->location = -1;

		/* combine it with the original join condition */
		parse->mergeJoinCondition =
			(Node *) make_and_qual((Node *) ntest, parse->mergeJoinCondition);
	}
	else
		parse->mergeJoinCondition = NULL;	/* join condition not needed */
}

/*
 * preprocess_relation_rtes
 *		Do the preprocessing work for any relation RTEs in the FROM clause.
 *
 * This scans the rangetable for relation RTEs and retrieves the necessary
 * catalog information for each relation.  Using this information, it clears
 * the inh flag for any relation that has no children, collects not-null
 * attribute numbers for any relation that has column not-null constraints, and
 * expands virtual generated columns for any relation that contains them.
 *
 * Note that expanding virtual generated columns may cause the query tree to
 * have new copies of rangetable entries.  Therefore, we have to use list_nth
 * instead of foreach when iterating over the query's rangetable.
 *
 * Returns a modified copy of the query tree, if any relations with virtual
 * generated columns are present.
 */
/*
 * preprocess_relation_rtes - (中文)对 FROM 子句中的关系 RTE 做预处理
 *
 * 【作用】遍历当前查询级别的 rangetable:对每个 RTE_RELATION,打开关系并
 * 做三件事——(1) 若声明了继承(inherit)但实际没有子表(relhassubclass
 * 为假),清除 inh 标志使其按普通基表处理;(2) 收集列的 NOT NULL 约束信息
 * 存入以关系 OID 为键的哈希表(get_relation_notnullatts,供外连接简化等
 * 使用);(3) 若含虚拟生成列,调用 expand_virtual_generated_columns 在整棵
 * 查询树中把对它们的引用替换为生成表达式。返回(可能更新后的)查询树。
 *
 * 【设计思想】
 * - 关系此前已被重写器加锁,这里用 NoLock 打开 relcache 即可,省去重复
 *   获取锁;
 * - inh 清除是有益的简化:让规划器把"曾经有子表但现在没有"的关系当普通
 *   基表,减少继承处理开销;但因为可能产生假阳性,此判定之后不再复核;
 * - 展开虚拟生成列会使 rangetable 复制出新的副本,故循环必须用 list_nth
 *   按快照长度索引,不能用 foreach 遍历实时列表。
 *
 * 【参数】root —— PlannerInfo,其 parse->rtable 被扫描。
 * 【返回值】处理后的查询树(关系含虚拟生成列时是新副本,否则为原 parse)。
 */
Query *
preprocess_relation_rtes(PlannerInfo *root)
{
	Query	   *parse = root->parse;
	int			rtable_size;
	int			rt_index;

	rtable_size = list_length(parse->rtable);

	for (rt_index = 0; rt_index < rtable_size; rt_index++)
	{
		RangeTblEntry *rte = rt_fetch(rt_index + 1, parse->rtable);
		Relation	relation;

		/* We only care about relation RTEs. */
		if (rte->rtekind != RTE_RELATION)
			continue;

		/*
		 * We need not lock the relation since it was already locked by the
		 * rewriter.
		 */
		relation = table_open(rte->relid, NoLock);

		/*
		 * Check to see if the relation actually has any children; if not,
		 * clear the inh flag so we can treat it as a plain base relation.
		 *
		 * Note: this could give a false-positive result, if the rel once had
		 * children but no longer does.  We used to be able to clear rte->inh
		 * later on when we discovered that, but no more; we have to handle
		 * such cases as full-fledged inheritance.
		 */
		if (rte->inh)
			rte->inh = relation->rd_rel->relhassubclass;

		/*
		 * Check to see if the relation has any column not-null constraints;
		 * if so, retrieve the constraint information and store it in a
		 * relation OID based hash table.
		 */
		get_relation_notnullatts(root, relation);

		/*
		 * Check to see if the relation has any virtual generated columns; if
		 * so, replace all Var nodes in the query that reference these columns
		 * with the generation expressions.
		 */
		parse = expand_virtual_generated_columns(root, parse,
												 rte, rt_index + 1,
												 relation);

		table_close(relation, NoLock);
	}

	return parse;
}

/*
 * expand_virtual_generated_columns
 *		Expand virtual generated columns for the given relation.
 *
 * This checks whether the given relation has any virtual generated columns,
 * and if so, replaces all Var nodes in the query that reference those columns
 * with their generation expressions.
 *
 * Returns a modified copy of the query tree if the relation contains virtual
 * generated columns.
 */
/*
 * expand_virtual_generated_columns - (中文)把给定关系的虚拟生成列引用替换
 * 为生成表达式
 *
 * 【作用】检查关系的元数据是否含虚拟生成列(has_generated_virtual)。若含,
 * 构造一个目标列表 tlist:生成列位置上放"用该关系自身 RT 索引展开的生成
 * 表达式"(build_generation_expression 得到定义后用 ChangeVarNodes 把内部
 * 的 varno 1 重写为 rt_index),普通列位置上放对应的 Var;然后通过
 * pullup_replace_vars 机制把查询树中所有对该关系的列引用按此 tlist 替换。
 * 返回修改后的查询树副本。
 *
 * 【设计思想】
 * - 复用"子查询上提"的 Var 替换管线:生成列的语义本质就是"把这个列看成
 *   一个派生表达式",与把子查询输出展开是同一类问题,故直接复用
 *   pullup_replace_vars_context / pullup_replace_vars;
 * - groupingSets 场景需要把每个输出包一层 PlaceHolderVar(wrap_option =
 *   REPLACE_WRAP_ALL),保持表达式身份以便与分组集列匹配(理由见
 *   pull_up_simple_subquery 的同类处理);
 * - 故意不触碰 ON CONFLICT 的 exclRelTlist:规划器多处假定它只含 Var,
 *   且不让 setrefs.c 把展开后的 EXCLUDED 虚拟列引用再变回原 Var,因此替换
 *   期间暂时清空它、事后恢复;
 * - 生成表达式可能引用其他列,替换是全树范围的;函数假设关系非 LATERAL
 *   (虚拟生成列不参与 lateral)。
 *
 * 【参数】
 *   root     —— PlannerInfo;
 *   parse    —— 当前查询树;
 *   rte      —— 目标关系 RTE(必须为 RTE_RELATION);
 *   rt_index —— 该关系在 rangetable 中的索引;
 *   relation —— 已打开的关系,用于读取列元数据与生成表达式。
 * 【返回值】处理后的查询树(含虚拟生成列时为新副本)。
 */
static Query *
expand_virtual_generated_columns(PlannerInfo *root, Query *parse,
								 RangeTblEntry *rte, int rt_index,
								 Relation relation)
{
	TupleDesc	tupdesc;

	/* Only normal relations can have virtual generated columns */
	Assert(rte->rtekind == RTE_RELATION);

	tupdesc = RelationGetDescr(relation);
	if (tupdesc->constr && tupdesc->constr->has_generated_virtual)
	{
		List	   *tlist = NIL;
		pullup_replace_vars_context rvcontext;
		List	   *save_exclRelTlist = NIL;

		for (int i = 0; i < tupdesc->natts; i++)
		{
			Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
			TargetEntry *tle;

			if (attr->attgenerated == ATTRIBUTE_GENERATED_VIRTUAL)
			{
				Node	   *defexpr;

				defexpr = build_generation_expression(relation, i + 1);
				ChangeVarNodes(defexpr, 1, rt_index, 0);

				tle = makeTargetEntry((Expr *) defexpr, i + 1, 0, false);
				tlist = lappend(tlist, tle);
			}
			else
			{
				Var		   *var;

				var = makeVar(rt_index,
							  i + 1,
							  attr->atttypid,
							  attr->atttypmod,
							  attr->attcollation,
							  0);

				tle = makeTargetEntry((Expr *) var, i + 1, 0, false);
				tlist = lappend(tlist, tle);
			}
		}

		Assert(list_length(tlist) > 0);
		Assert(!rte->lateral);

		/*
		 * The relation's targetlist items are now in the appropriate form to
		 * insert into the query, except that we may need to wrap them in
		 * PlaceHolderVars.  Set up required context data for
		 * pullup_replace_vars.
		 */
		rvcontext.root = root;
		rvcontext.targetlist = tlist;
		rvcontext.target_rte = rte;
		rvcontext.result_relation = parse->resultRelation;
		/* won't need these values */
		rvcontext.relids = NULL;
		rvcontext.nullinfo = NULL;
		/* pass NULL for outer_hasSubLinks */
		rvcontext.outer_hasSubLinks = NULL;
		rvcontext.varno = rt_index;
		/* this flag will be set below, if needed */
		rvcontext.wrap_option = REPLACE_WRAP_NONE;
		/* initialize cache array with indexes 0 .. length(tlist) */
		rvcontext.rv_cache = palloc0((list_length(tlist) + 1) *
									 sizeof(Node *));

		/*
		 * If the query uses grouping sets, we need a PlaceHolderVar for each
		 * expression of the relation's targetlist items.  (See comments in
		 * pull_up_simple_subquery().)
		 */
		if (parse->groupingSets)
			rvcontext.wrap_option = REPLACE_WRAP_ALL;

		/*
		 * Apply pullup variable replacement throughout the query tree.
		 *
		 * We intentionally do not touch the EXCLUDED pseudo-relation's
		 * targetlist here.  Various places in the planner assume that it
		 * contains only Vars, and we want that to remain the case.  More
		 * importantly, we don't want setrefs.c to turn any expanded
		 * EXCLUDED.virtual_column expressions in other parts of the query
		 * back into Vars referencing the original virtual column, which
		 * set_plan_refs() would do if exclRelTlist contained matching
		 * expressions.
		 */
		if (parse->onConflict)
		{
			save_exclRelTlist = parse->onConflict->exclRelTlist;
			parse->onConflict->exclRelTlist = NIL;
		}

		parse = (Query *) pullup_replace_vars((Node *) parse, &rvcontext);

		if (parse->onConflict)
			parse->onConflict->exclRelTlist = save_exclRelTlist;
	}

	return parse;
}

/*
 * replace_empty_jointree
 *		If the Query's jointree is empty, replace it with a dummy RTE_RESULT
 *		relation.
 *
 * By doing this, we can avoid a bunch of corner cases that formerly existed
 * for SELECTs with omitted FROM clauses.  An example is that a subquery
 * with empty jointree previously could not be pulled up, because that would
 * have resulted in an empty relid set, making the subquery not uniquely
 * identifiable for join or PlaceHolderVar processing.
 *
 * Unlike most other functions in this file, this function doesn't recurse;
 * we rely on other processing to invoke it on sub-queries at suitable times.
 */
/*
 * replace_empty_jointree - (中文)若查询连接树为空,用 RTE_RESULT 占位关系
 * 填充
 *
 * 【作用】当 Query 的 jointree->fromlist 为空(即无 FROM 子句的 SELECT)时,
 * 向 rangetable 追加一个 RTE_RESULT RTE,并把 jointree 改为只引用它。若
 * fromlist 非空或查询是 setop 树的顶层则不处理。
 *
 * 【设计思想】统一处理"无 FROM"特例:空连接树会让子查询无法上提(上提后
 * relid 集合为空,难以参与连接与 PlaceHolderVar 处理)。RTE_RESULT 固定
 * 返回一行且无列,语义上等价于空 FROM,却让后续所有代码都把连接树当
 * 非空处理,消灭大量分支。本函数不递归——子查询的空 jointree 由各自的
 * 处理路径(如 pull_up_simple_subquery)适时调用。
 *
 * 【参数】parse —— 待处理的查询(就地修改其 rtable 与 jointree)。
 * 【返回值】无。
 */
void
replace_empty_jointree(Query *parse)
{
	RangeTblEntry *rte;
	Index		rti;
	RangeTblRef *rtr;

	/* Nothing to do if jointree is already nonempty */
	if (parse->jointree->fromlist != NIL)
		return;

	/* We mustn't change it in the top level of a setop tree, either */
	if (parse->setOperations)
		return;

	/* Create suitable RTE */
	rte = makeNode(RangeTblEntry);
	rte->rtekind = RTE_RESULT;
	rte->eref = makeAlias("*RESULT*", NIL);

	/* Add it to rangetable */
	parse->rtable = lappend(parse->rtable, rte);
	rti = list_length(parse->rtable);

	/* And jam a reference into the jointree */
	rtr = makeNode(RangeTblRef);
	rtr->rtindex = rti;
	parse->jointree->fromlist = list_make1(rtr);
}

/*
 * pull_up_sublinks
 *		Attempt to pull up ANY and EXISTS SubLinks to be treated as
 *		semijoins or anti-semijoins.
 *
 * A clause "foo op ANY (sub-SELECT)" can be processed by pulling the
 * sub-SELECT up to become a rangetable entry and treating the implied
 * comparisons as quals of a semijoin.  However, this optimization *only*
 * works at the top level of WHERE or a JOIN/ON clause, because we cannot
 * distinguish whether the ANY ought to return FALSE or NULL in cases
 * involving NULL inputs.  Also, in an outer join's ON clause we can only
 * do this if the sublink is degenerate (ie, references only the nullable
 * side of the join).  In that case it is legal to push the semijoin
 * down into the nullable side of the join.  If the sublink references any
 * nonnullable-side variables then it would have to be evaluated as part
 * of the outer join, which makes things way too complicated.
 *
 * Under similar conditions, EXISTS and NOT EXISTS clauses can be handled
 * by pulling up the sub-SELECT and creating a semijoin or anti-semijoin.
 *
 * This routine searches for such clauses and does the necessary parsetree
 * transformations if any are found.
 *
 * This routine has to run before preprocess_expression(), so the quals
 * clauses are not yet reduced to implicit-AND format, and are not guaranteed
 * to be AND/OR-flat either.  That means we need to recursively search through
 * explicit AND clauses.  We stop as soon as we hit a non-AND item.
 */
/*
 * pull_up_sublinks - (中文)把可转换的 ANY / EXISTS SubLink 上提为半连接 /
 * 反连接
 *
 * 【作用】对外入口。递归扫描整个连接树,寻找满足条件的 SubLink:形如
 * "foo op ANY (sub-SELECT)" 的子链接可转换为半连接(等价于把子查询上提
 * 成 RTE 并在其与左部之间构造带比较条件的 JOIN_SEMI),EXISTS 同样,
 * NOT 包裹的 ANY/EXISTS 变成反连接(JOIN_ANTI)。转换后的 SubLink 在限定
 * 条件中替换为常量 TRUE(即删除),新产生的 JoinExpr 插入连接树。要求
 * 在 preprocess_expression 之前运行——此时 quals 尚未转为隐含 AND 格式,
 * 也不保证 AND/OR 平坦,故递归只沿显式 AND 结构下行,遇非 AND 即停。
 *
 * 【设计思想】
 * - 该优化只在"顶层 WHERE 或 JOIN/ON 限定条件"有效:ANY 在 NULL 输入下
 *   究竟返回 FALSE 还是 NULL 无法在一般上下文区分,把子链接上提会改变
 *   语义;例外是外连接 ON 条件中的"退化"子链接(只引用可空侧变量),此时
 *   可把半连接压入可空侧;
 * - 子查询上提为半连接后,其子查询里的子链接还可继续递归上提,因此新
 *   JoinExpr 的 quals 与两侧会继续交给本模块递归处理;
 * - 转换的具体构造(比较表达式变连接条件、生成 JoinExpr)由
 *   convert_ANY_sublink_to_join / convert_EXISTS_sublink_to_join
 *   (subselect.c)完成,本函数负责定位与组织递归;convert_VALUES_to_ANY
 *   负责把 "x = ANY (VALUES ...)" 退化回普通 ScalarArrayOpExpr。
 *
 * 【参数】root —— PlannerInfo,其 parse->jointree 被就地改写。
 * 【返回值】无。
 */
void
pull_up_sublinks(PlannerInfo *root)
{
	Node	   *jtnode;
	Relids		relids;

	/* Begin recursion through the jointree */
	jtnode = pull_up_sublinks_jointree_recurse(root,
											   (Node *) root->parse->jointree,
											   &relids);

	/*
	 * root->parse->jointree must always be a FromExpr, so insert a dummy one
	 * if we got a bare RangeTblRef or JoinExpr out of the recursion.
	 */
	if (IsA(jtnode, FromExpr))
		root->parse->jointree = (FromExpr *) jtnode;
	else
		root->parse->jointree = makeFromExpr(list_make1(jtnode), NULL);
}

/*
 * Recurse through jointree nodes for pull_up_sublinks()
 *
 * In addition to returning the possibly-modified jointree node, we return
 * a relids set of the contained rels into *relids.
 */
/*
 * pull_up_sublinks_jointree_recurse - (中文)pull_up_sublinks 对连接树节点的
 * 递归核心
 *
 * 【作用】递归处理连接树节点。RangeTblRef:返回原样,relids 为单元素;
 * FromExpr:先递归处理各子节点并汇总 relids,重建新的 FromExpr 并把原
 * quals 交给 pull_up_sublinks_qual_recurse(所有子节点都可用);JoinExpr:
 * 制作可修改副本,递归左右两侧,再按其连接类型把 quals 交给
 * pull_up_sublinks_qual_recurse 处理(INNER 时新连接堆在节点之上,FULL 不
 * 处理,LEFT/RIGHT 时压入对应的可空侧)。返回处理后的连接树节点并输出
 * 其 relids。
 *
 * 【设计思想】
 * - "可用关系集合(available_rels)"机制确保安全:只有引用了当前子树内关系
 *   的子链接才能就地转换,引用两侧关系的子链接无法转换(FULL 连接干脆
 *   不动其 quals);
 * - 结果可能是在原 FromExpr 上叠了一层 JoinExpr 栈,后续优化步骤负责把
 *   它们展平重排;
 * - relids 输出不含新上提的子查询(上层 quals 反正不能引用它们的输出),
 *   但 JoinExpr 情形必须包含 join 自身的 rtindex——连接别名变量尚未展开,
 *   否则上层会误判不能引用该连接。
 *
 * 【参数】
 *   root   —— PlannerInfo;
 *   jtnode —— 当前连接树节点;
 *   relids —— 输出:该子树包含的关系 relid 集合。
 * 【返回值】处理后的连接树节点(可能是新建的 FromExpr 或 JoinExpr 栈)。
 */
static Node *
pull_up_sublinks_jointree_recurse(PlannerInfo *root, Node *jtnode,
								  Relids *relids)
{
	/* Since this function recurses, it could be driven to stack overflow. */
	check_stack_depth();

	if (jtnode == NULL)
	{
		*relids = NULL;
	}
	else if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		*relids = bms_make_singleton(varno);
		/* jtnode is returned unmodified */
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		List	   *newfromlist = NIL;
		Relids		frelids = NULL;
		FromExpr   *newf;
		Node	   *jtlink;
		ListCell   *l;

		/* First, recurse to process children and collect their relids */
		foreach(l, f->fromlist)
		{
			Node	   *newchild;
			Relids		childrelids;

			newchild = pull_up_sublinks_jointree_recurse(root,
														 lfirst(l),
														 &childrelids);
			newfromlist = lappend(newfromlist, newchild);
			frelids = bms_join(frelids, childrelids);
		}
		/* Build the replacement FromExpr; no quals yet */
		newf = makeFromExpr(newfromlist, NULL);
		/* Set up a link representing the rebuilt jointree */
		jtlink = (Node *) newf;
		/* Now process qual --- all children are available for use */
		newf->quals = pull_up_sublinks_qual_recurse(root, f->quals,
													&jtlink, frelids,
													NULL, NULL);

		/*
		 * Note that the result will be either newf, or a stack of JoinExprs
		 * with newf at the base.  We rely on subsequent optimization steps to
		 * flatten this and rearrange the joins as needed.
		 *
		 * Although we could include the pulled-up subqueries in the returned
		 * relids, there's no need since upper quals couldn't refer to their
		 * outputs anyway.
		 */
		*relids = frelids;
		jtnode = jtlink;
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j;
		Relids		leftrelids;
		Relids		rightrelids;
		Node	   *jtlink;

		/*
		 * Make a modifiable copy of join node, but don't bother copying its
		 * subnodes (yet).
		 */
		j = palloc_object(JoinExpr);
		memcpy(j, jtnode, sizeof(JoinExpr));
		jtlink = (Node *) j;

		/* Recurse to process children and collect their relids */
		j->larg = pull_up_sublinks_jointree_recurse(root, j->larg,
													&leftrelids);
		j->rarg = pull_up_sublinks_jointree_recurse(root, j->rarg,
													&rightrelids);

		/*
		 * Now process qual, showing appropriate child relids as available,
		 * and attach any pulled-up jointree items at the right place. In the
		 * inner-join case we put new JoinExprs above the existing one (much
		 * as for a FromExpr-style join).  In outer-join cases the new
		 * JoinExprs must go into the nullable side of the outer join. The
		 * point of the available_rels machinations is to ensure that we only
		 * pull up quals for which that's okay.
		 *
		 * We don't expect to see any pre-existing JOIN_SEMI, JOIN_ANTI,
		 * JOIN_RIGHT_SEMI, or JOIN_RIGHT_ANTI jointypes here.
		 */
		switch (j->jointype)
		{
			case JOIN_INNER:
				j->quals = pull_up_sublinks_qual_recurse(root, j->quals,
														 &jtlink,
														 bms_union(leftrelids,
																   rightrelids),
														 NULL, NULL);
				break;
			case JOIN_LEFT:
				j->quals = pull_up_sublinks_qual_recurse(root, j->quals,
														 &j->rarg,
														 rightrelids,
														 NULL, NULL);
				break;
			case JOIN_FULL:
				/* can't do anything with full-join quals */
				break;
			case JOIN_RIGHT:
				j->quals = pull_up_sublinks_qual_recurse(root, j->quals,
														 &j->larg,
														 leftrelids,
														 NULL, NULL);
				break;
			default:
				elog(ERROR, "unrecognized join type: %d",
					 (int) j->jointype);
				break;
		}

		/*
		 * Although we could include the pulled-up subqueries in the returned
		 * relids, there's no need since upper quals couldn't refer to their
		 * outputs anyway.  But we *do* need to include the join's own rtindex
		 * because we haven't yet collapsed join alias variables, so upper
		 * levels would mistakenly think they couldn't use references to this
		 * join.
		 */
		*relids = bms_join(leftrelids, rightrelids);
		if (j->rtindex)
			*relids = bms_add_member(*relids, j->rtindex);
		jtnode = jtlink;
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
	return jtnode;
}

/*
 * Recurse through top-level qual nodes for pull_up_sublinks()
 *
 * jtlink1 points to the link in the jointree where any new JoinExprs should
 * be inserted if they reference available_rels1 (i.e., available_rels1
 * denotes the relations present underneath jtlink1).  Optionally, jtlink2 can
 * point to a second link where new JoinExprs should be inserted if they
 * reference available_rels2 (pass NULL for both those arguments if not used).
 * Note that SubLinks referencing both sets of variables cannot be optimized.
 * If we find multiple pull-up-able SubLinks, they'll get stacked onto jtlink1
 * and/or jtlink2 in the order we encounter them.  We rely on subsequent
 * optimization to rearrange the stack if appropriate.
 *
 * Returns the replacement qual node, or NULL if the qual should be removed.
 */
/*
 * pull_up_sublinks_qual_recurse - (中文)pull_up_sublinks 对顶层限定条件
 * (qual)的递归核心
 *
 * 【作用】递归处理限定条件节点:SubLink 节点——若为可转换的 ANY(先试
 * convert_VALUES_to_ANY 退化,再试 convert_ANY_sublink_to_join)或
 * EXISTS,成功则在 jtlink1(或 jtlink2)处插入新 JoinExpr,对其 rarg 递归
 * 处理,对自身 quals 递归处理,最后返回 NULL 代表"条件已化简为常量
 * TRUE";NOT 包裹的 SubLink 同理(反连接,子链接引用左部时不可再上提,只
 * 处理引用右部者);AND 节点——递归处理每个子句并重组;其他节点原样返回。
 *
 * 【设计思想】
 * - jtlink1/jtlink2 提供两个"插入点"与各自对应的可用关系集:上提的
 *   JoinExpr 根据其引用的关系归属到相应位置;引用两个集合变量的子链接
 *   无法优化(FULL 连接下 available_rels2 通常为 NULL);
 * - 上提后新 JoinExpr 的 quals 与两侧都要继续递归,可能继续叠上新连接,
 *   顺序即代码中的嵌套关系,后续优化负责重排;
 * - 转换后返回 NULL:上层 AND 重组时会把空句删掉,等价于子链接变 TRUE;
 *   这是"把子链接从限定条件中移除"的实现手段。
 *
 * 【参数】
 *   root            —— PlannerInfo;
 *   node            —— 当前限定条件节点;
 *   jtlink1         —— 插入点 1 的指针(可空侧/当前子树位置);
 *   available_rels1 —— 插入点 1 下的可用关系集合;
 *   jtlink2         —— 插入点 2(可空,通常为右子树的 rarg);
 *   available_rels2 —— 插入点 2 下的可用关系集合。
 * 【返回值】替换后的限定条件节点;返回 NULL 表示该条件应被移除(常量
 * TRUE)。
 */
static Node *
pull_up_sublinks_qual_recurse(PlannerInfo *root, Node *node,
							   Node **jtlink1, Relids available_rels1,
							   Node **jtlink2, Relids available_rels2)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, SubLink))
	{
		SubLink    *sublink = (SubLink *) node;
		JoinExpr   *j;
		Relids		child_rels;

		/* Is it a convertible ANY or EXISTS clause? */
		if (sublink->subLinkType == ANY_SUBLINK)
		{
			ScalarArrayOpExpr *saop;

			if ((saop = convert_VALUES_to_ANY(root,
											  sublink->testexpr,
											  (Query *) sublink->subselect)) != NULL)
			{
				/*
				 * The VALUES sequence was simplified.  Nothing more to do
				 * here.
				 */
				return (Node *) saop;
			}

			if ((j = convert_ANY_sublink_to_join(root, sublink, false,
												 available_rels1)) != NULL)
			{
				/* Yes; insert the new join node into the join tree */
				j->larg = *jtlink1;
				*jtlink1 = (Node *) j;
				/* Recursively process pulled-up jointree nodes */
				j->rarg = pull_up_sublinks_jointree_recurse(root,
															j->rarg,
															&child_rels);

				/*
				 * Now recursively process the pulled-up quals.  Any inserted
				 * joins can get stacked onto either j->larg or j->rarg,
				 * depending on which rels they reference.
				 */
				j->quals = pull_up_sublinks_qual_recurse(root,
														 j->quals,
														 &j->larg,
														 available_rels1,
														 &j->rarg,
														 child_rels);
				/* Return NULL representing constant TRUE */
				return NULL;
			}
			if (available_rels2 != NULL &&
				(j = convert_ANY_sublink_to_join(root, sublink, false,
												 available_rels2)) != NULL)
			{
				/* Yes; insert the new join node into the join tree */
				j->larg = *jtlink2;
				*jtlink2 = (Node *) j;
				/* Recursively process pulled-up jointree nodes */
				j->rarg = pull_up_sublinks_jointree_recurse(root,
															j->rarg,
															&child_rels);

				/*
				 * Now recursively process the pulled-up quals.  Any inserted
				 * joins can get stacked onto either j->larg or j->rarg,
				 * depending on which rels they reference.
				 */
				j->quals = pull_up_sublinks_qual_recurse(root,
														 j->quals,
														 &j->larg,
														 available_rels2,
														 &j->rarg,
														 child_rels);
				/* Return NULL representing constant TRUE */
				return NULL;
			}
		}
		else if (sublink->subLinkType == EXISTS_SUBLINK)
		{
			if ((j = convert_EXISTS_sublink_to_join(root, sublink, false,
													available_rels1)) != NULL)
			{
				/* Yes; insert the new join node into the join tree */
				j->larg = *jtlink1;
				*jtlink1 = (Node *) j;
				/* Recursively process pulled-up jointree nodes */
				j->rarg = pull_up_sublinks_jointree_recurse(root,
															j->rarg,
															&child_rels);

				/*
				 * Now recursively process the pulled-up quals.  Any inserted
				 * joins can get stacked onto either j->larg or j->rarg,
				 * depending on which rels they reference.
				 */
				j->quals = pull_up_sublinks_qual_recurse(root,
														 j->quals,
														 &j->larg,
														 available_rels1,
														 &j->rarg,
														 child_rels);
				/* Return NULL representing constant TRUE */
				return NULL;
			}
			if (available_rels2 != NULL &&
				(j = convert_EXISTS_sublink_to_join(root, sublink, false,
													available_rels2)) != NULL)
			{
				/* Yes; insert the new join node into the join tree */
				j->larg = *jtlink2;
				*jtlink2 = (Node *) j;
				/* Recursively process pulled-up jointree nodes */
				j->rarg = pull_up_sublinks_jointree_recurse(root,
															j->rarg,
															&child_rels);

				/*
				 * Now recursively process the pulled-up quals.  Any inserted
				 * joins can get stacked onto either j->larg or j->rarg,
				 * depending on which rels they reference.
				 */
				j->quals = pull_up_sublinks_qual_recurse(root,
														 j->quals,
														 &j->larg,
														 available_rels2,
														 &j->rarg,
														 child_rels);
				/* Return NULL representing constant TRUE */
				return NULL;
			}
		}
		/* Else return it unmodified */
		return node;
	}
	if (is_notclause(node))
	{
		/* If the immediate argument of NOT is ANY or EXISTS, try to convert */
		SubLink    *sublink = (SubLink *) get_notclausearg((Expr *) node);
		JoinExpr   *j;
		Relids		child_rels;

		if (sublink && IsA(sublink, SubLink))
		{
			if (sublink->subLinkType == ANY_SUBLINK)
			{
				if ((j = convert_ANY_sublink_to_join(root, sublink, true,
													 available_rels1)) != NULL)
				{
					/* Yes; insert the new join node into the join tree */
					j->larg = *jtlink1;
					*jtlink1 = (Node *) j;
					/* Recursively process pulled-up jointree nodes */
					j->rarg = pull_up_sublinks_jointree_recurse(root,
																j->rarg,
																&child_rels);

					/*
					 * Now recursively process the pulled-up quals.  Because
					 * we are underneath a NOT, we can't pull up sublinks that
					 * reference the left-hand stuff, but it's still okay to
					 * pull up sublinks referencing j->rarg.
					 */
					j->quals = pull_up_sublinks_qual_recurse(root,
															 j->quals,
															 &j->rarg,
															 child_rels,
															 NULL, NULL);
					/* Return NULL representing constant TRUE */
					return NULL;
				}
				if (available_rels2 != NULL &&
					(j = convert_ANY_sublink_to_join(root, sublink, true,
													 available_rels2)) != NULL)
				{
					/* Yes; insert the new join node into the join tree */
					j->larg = *jtlink2;
					*jtlink2 = (Node *) j;
					/* Recursively process pulled-up jointree nodes */
					j->rarg = pull_up_sublinks_jointree_recurse(root,
																j->rarg,
																&child_rels);

					/*
					 * Now recursively process the pulled-up quals.  Because
					 * we are underneath a NOT, we can't pull up sublinks that
					 * reference the left-hand stuff, but it's still okay to
					 * pull up sublinks referencing j->rarg.
					 */
					j->quals = pull_up_sublinks_qual_recurse(root,
															 j->quals,
															 &j->rarg,
															 child_rels,
															 NULL, NULL);
					/* Return NULL representing constant TRUE */
					return NULL;
				}
			}
			else if (sublink->subLinkType == EXISTS_SUBLINK)
			{
				if ((j = convert_EXISTS_sublink_to_join(root, sublink, true,
														available_rels1)) != NULL)
				{
					/* Yes; insert the new join node into the join tree */
					j->larg = *jtlink1;
					*jtlink1 = (Node *) j;
					/* Recursively process pulled-up jointree nodes */
					j->rarg = pull_up_sublinks_jointree_recurse(root,
																j->rarg,
																&child_rels);

					/*
					 * Now recursively process the pulled-up quals.  Because
					 * we are underneath a NOT, we can't pull up sublinks that
					 * reference the left-hand stuff, but it's still okay to
					 * pull up sublinks referencing j->rarg.
					 */
					j->quals = pull_up_sublinks_qual_recurse(root,
															 j->quals,
															 &j->rarg,
															 child_rels,
															 NULL, NULL);
					/* Return NULL representing constant TRUE */
					return NULL;
				}
				if (available_rels2 != NULL &&
					(j = convert_EXISTS_sublink_to_join(root, sublink, true,
														available_rels2)) != NULL)
				{
					/* Yes; insert the new join node into the join tree */
					j->larg = *jtlink2;
					*jtlink2 = (Node *) j;
					/* Recursively process pulled-up jointree nodes */
					j->rarg = pull_up_sublinks_jointree_recurse(root,
																j->rarg,
																&child_rels);

					/*
					 * Now recursively process the pulled-up quals.  Because
					 * we are underneath a NOT, we can't pull up sublinks that
					 * reference the left-hand stuff, but it's still okay to
					 * pull up sublinks referencing j->rarg.
					 */
					j->quals = pull_up_sublinks_qual_recurse(root,
															 j->quals,
															 &j->rarg,
															 child_rels,
															 NULL, NULL);
					/* Return NULL representing constant TRUE */
					return NULL;
				}
			}
		}
		/* Else return it unmodified */
		return node;
	}
	if (is_andclause(node))
	{
		/* Recurse into AND clause */
		List	   *newclauses = NIL;
		ListCell   *l;

		foreach(l, ((BoolExpr *) node)->args)
		{
			Node	   *oldclause = (Node *) lfirst(l);
			Node	   *newclause;

			newclause = pull_up_sublinks_qual_recurse(root,
													  oldclause,
													  jtlink1,
													  available_rels1,
													  jtlink2,
													  available_rels2);
			if (newclause)
				newclauses = lappend(newclauses, newclause);
		}
		/* We might have got back fewer clauses than we started with */
		if (newclauses == NIL)
			return NULL;
		else if (list_length(newclauses) == 1)
			return (Node *) linitial(newclauses);
		else
			return (Node *) make_andclause(newclauses);
	}
	/* Stop if not an AND */
	return node;
}

/*
 * preprocess_function_rtes
 *		Constant-simplify any FUNCTION RTEs in the FROM clause, and then
 *		attempt to "inline" any that can be converted to simple subqueries.
 *
 * If an RTE_FUNCTION rtable entry invokes a set-returning SQL function that
 * contains just a simple SELECT, we can convert the rtable entry to an
 * RTE_SUBQUERY entry exposing the SELECT directly.  Other sorts of functions
 * are also inline-able if they have a support function that can generate
 * the replacement sub-Query.  This is especially useful if the subquery can
 * then be "pulled up" for further optimization, but we do it even if not,
 * to reduce executor overhead.
 *
 * This has to be done before we have started to do any optimization of
 * subqueries, else any such steps wouldn't get applied to subqueries
 * obtained via inlining.  However, we do it after pull_up_sublinks
 * so that we can inline any functions used in SubLink subselects.
 *
 * The reason for applying const-simplification at this stage is that
 * (a) we'd need to do it anyway to inline a SRF, and (b) by doing it now,
 * we can be sure that pull_up_constant_function() will see constants
 * if there are constants to be seen.  This approach also guarantees
 * that every FUNCTION RTE has been const-simplified, allowing planner.c's
 * preprocess_expression() to skip doing it again.
 *
 * Like most of the planner, this feels free to scribble on its input data
 * structure.
 */
/*
 * preprocess_function_rtes - (中文)预处理 FROM 子句中的函数 RTE:常量化简
 * 与内联
 *
 * 【作用】遍历 rangetable,对每个 RTE_FUNCTION:先对其 functions 列表做
 * eval_const_expressions 常量化简;再尝试 inline_function_in_from 把
 * "内容只是一个简单 SELECT 的集合返回 SQL 函数"或"有支持函数能生成替换
 * 子查询"的函数内联成普通子查询——成功后把该 RTE 改成 RTE_SUBQUERY。
 *
 * 【设计思想】
 * - 必须先于任何子查询优化:否则通过内联产生的子查询会错过已进行的优化;
 *   又要晚于 pull_up_sublinks,以便内联 SubLink 子查询里的函数;
 * - 此处做常量化简的双重目的:(a) 内联 SRF 本就需要; (b) 保证
 *   pull_up_constant_function 之后能看到常量;同时让 planner.c 的
 *   preprocess_expression 不必对 FUNCTION RTE 再做一次化简;
 * - 内联成子查询后若再被上提,可以获得子查询级优化,即使不满足上提条件,
 *   也省去执行器按函数调用求值的开销;rte->functions 暂时保留给
 *   makeWholeRowVar 使用,由 setrefs.c 在加入扁平 rtable 时清掉。
 *
 * 【参数】root —— PlannerInfo,其 parse->rtable 被就地修改。
 * 【返回值】无。
 */
void
preprocess_function_rtes(PlannerInfo *root)
{
	ListCell   *rt;

	foreach(rt, root->parse->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(rt);

		if (rte->rtekind == RTE_FUNCTION)
		{
			Query	   *funcquery;

			/* Apply const-simplification */
			rte->functions = (List *)
				eval_const_expressions(root, (Node *) rte->functions);

			/* Check safety of expansion, and expand if possible */
			funcquery = inline_function_in_from(root, rte);
			if (funcquery)
			{
				/* Successful expansion, convert the RTE to a subquery */
				rte->rtekind = RTE_SUBQUERY;
				rte->subquery = funcquery;
				rte->security_barrier = false;

				/*
				 * Clear fields that should not be set in a subquery RTE.
				 * However, we leave rte->functions filled in for the moment,
				 * in case makeWholeRowVar needs to consult it.  We'll clear
				 * it in setrefs.c (see add_rte_to_flat_rtable) so that this
				 * abuse of the data structure doesn't escape the planner.
				 */
				rte->funcordinality = false;
			}
		}
	}
}

/*
 * pull_up_subqueries
 *		Look for subqueries in the rangetable that can be pulled up into
 *		the parent query.  If the subquery has no special features like
 *		grouping/aggregation then we can merge it into the parent's jointree.
 *		Also, subqueries that are simple UNION ALL structures can be
 *		converted into "append relations".
 */
/*
 * pull_up_subqueries - (中文)把可上提的子查询并入父查询的对外入口
 *
 * 【作用】对当前查询的 jointree 调用 pull_up_subqueries_recurse(初始无外层
 * 连接、无 appendrel 上下文),把"简单子查询"(见 is_simple_subquery)、
 * "简单 UNION ALL"(转 append 关系)、"简单 VALUES"与"常量函数"上提合并。
 *
 * 【设计思想】上提子查询的目标是消除一层间接,让子查询里的关系与条件直接
 * 参与父查询的路径枚举与连接重排,往往能显著改善计划质量。入口只做
 * 断言(顶层必须是从 FromExpr 开始)与收尾(结果仍须为 FromExpr)。
 *
 * 【参数】root —— PlannerInfo,其 parse->jointree 被就地改写。
 * 【返回值】无。
 */
void
pull_up_subqueries(PlannerInfo *root)
{
	/* Top level of jointree must always be a FromExpr */
	Assert(IsA(root->parse->jointree, FromExpr));
	/* Recursion starts with no containing join nor appendrel */
	root->parse->jointree = (FromExpr *)
		pull_up_subqueries_recurse(root, (Node *) root->parse->jointree,
								   NULL, NULL);
	/* We should still have a FromExpr */
	Assert(IsA(root->parse->jointree, FromExpr));
}

/*
 * pull_up_subqueries_recurse
 *		Recursive guts of pull_up_subqueries.
 *
 * This recursively processes the jointree and returns a modified jointree.
 *
 * If this jointree node is within either side of an outer join, then
 * lowest_outer_join references the lowest such JoinExpr node; otherwise
 * it is NULL.  We use this to constrain the effects of LATERAL subqueries.
 *
 * If we are looking at a member subquery of an append relation,
 * containing_appendrel describes that relation; else it is NULL.
 * This forces use of the PlaceHolderVar mechanism for all non-Var targetlist
 * items, and puts some additional restrictions on what can be pulled up.
 *
 * A tricky aspect of this code is that if we pull up a subquery we have
 * to replace Vars that reference the subquery's outputs throughout the
 * parent query, including quals attached to jointree nodes above the one
 * we are currently processing!  We handle this by being careful to maintain
 * validity of the jointree structure while recursing, in the following sense:
 * whenever we recurse, all qual expressions in the tree must be reachable
 * from the top level, in case the recursive call needs to modify them.
 *
 * Notice also that we can't turn pullup_replace_vars loose on the whole
 * jointree, because it'd return a mutated copy of the tree; we have to
 * invoke it just on the quals, instead.  This behavior is what makes it
 * reasonable to pass lowest_outer_join as a pointer rather than some
 * more-indirect way of identifying the lowest OJ.  Likewise, we don't
 * replace append_rel_list members but only their substructure, so the
 * containing_appendrel reference is safe to use.
 */
/*
 * pull_up_subqueries_recurse - (中文)pull_up_subqueries 的递归核心
 *
 * 【作用】递归遍历连接树。对 RangeTblRef:按顺序尝试四种上提——简单子查询
 * (pull_up_simple_subquery,且在 appendrel 成员时须 is_safe_append_member)、
 * 简单 UNION ALL(pull_up_simple_union_all)、简单 VALUES(pull_up_simple_values,
 * 不允许在外连接之下或 appendrel 中)、函数 RTE(pull_up_constant_function);
 * 对 FromExpr/JoinExpr:递归处理各子节点,并把 lowest_outer_join 正确传递
 * (进入外连接任一侧时指向该连接),以约束 LATERAL 子查询的上提。
 *
 * 【设计思想】
 * - lowest_outer_join 记录"本节点之上最低的外连接",用于限制 LATERAL
 *   子查询:其 lateral 引用不允许越过外层连接(否则会把限定条件从连接
 *   之下推迟到之上,语义复杂且易错,见 is_simple_subquery);
 * - containing_appendrel 表明本节点是 append 关系的成员子查询,此时限定
 *   更严格(is_safe_append_member)且非 Var 目标项须用 PlaceHolderVar;
 * - 关键不变量:递归期间整棵树的限定条件必须始终从顶层可达,因为上提
 *   子查询时的 Var 替换(pullup_replace_vars)可能改写任何位置的条件;
 *   因此它只作用于各节点自身的 quals,而不是替换整棵 jointree。
 *
 * 【参数】
 *   root                 —— PlannerInfo;
 *   jtnode               —— 当前连接树节点;
 *   lowest_outer_join    —— 之上最低的外连接 JoinExpr,无则 NULL;
 *   containing_appendrel —— 本节点所属的 append 关系(AppendRelInfo),非
 *                           append 成员则为 NULL。
 * 【返回值】改写后的连接树节点。
 */
static Node *
pull_up_subqueries_recurse(PlannerInfo *root, Node *jtnode,
						   JoinExpr *lowest_outer_join,
						   AppendRelInfo *containing_appendrel)
{
	/* Since this function recurses, it could be driven to stack overflow. */
	check_stack_depth();
	/* Also, since it's a bit expensive, let's check for query cancel. */
	CHECK_FOR_INTERRUPTS();

	Assert(jtnode != NULL);
	if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;
		RangeTblEntry *rte = rt_fetch(varno, root->parse->rtable);

		/*
		 * Is this a subquery RTE, and if so, is the subquery simple enough to
		 * pull up?
		 *
		 * If we are looking at an append-relation member, we can't pull it up
		 * unless is_safe_append_member says so.
		 */
		if (rte->rtekind == RTE_SUBQUERY &&
			is_simple_subquery(root, rte->subquery, rte, lowest_outer_join) &&
			(containing_appendrel == NULL ||
			 is_safe_append_member(rte->subquery)))
			return pull_up_simple_subquery(root, jtnode, rte,
										   lowest_outer_join,
										   containing_appendrel);

		/*
		 * Alternatively, is it a simple UNION ALL subquery?  If so, flatten
		 * into an "append relation".
		 *
		 * It's safe to do this regardless of whether this query is itself an
		 * appendrel member.  (If you're thinking we should try to flatten the
		 * two levels of appendrel together, you're right; but we handle that
		 * in set_append_rel_pathlist, not here.)
		 */
		if (rte->rtekind == RTE_SUBQUERY &&
			is_simple_union_all(rte->subquery))
			return pull_up_simple_union_all(root, jtnode, rte);

		/*
		 * Or perhaps it's a simple VALUES RTE?
		 *
		 * We don't allow VALUES pullup below an outer join nor into an
		 * appendrel (such cases are impossible anyway at the moment).
		 */
		if (rte->rtekind == RTE_VALUES &&
			lowest_outer_join == NULL &&
			containing_appendrel == NULL &&
			is_simple_values(root, rte))
			return pull_up_simple_values(root, jtnode, rte);

		/*
		 * Or perhaps it's a FUNCTION RTE that we could inline?
		 */
		if (rte->rtekind == RTE_FUNCTION)
			return pull_up_constant_function(root, jtnode, rte,
											 containing_appendrel);

		/* Otherwise, do nothing at this node. */
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		Assert(containing_appendrel == NULL);
		/* Recursively transform all the child nodes */
		foreach(l, f->fromlist)
		{
			lfirst(l) = pull_up_subqueries_recurse(root, lfirst(l),
												   lowest_outer_join,
												   NULL);
		}
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		Assert(containing_appendrel == NULL);
		/* Recurse, being careful to tell myself when inside outer join */
		switch (j->jointype)
		{
			case JOIN_INNER:
				j->larg = pull_up_subqueries_recurse(root, j->larg,
													 lowest_outer_join,
													 NULL);
				j->rarg = pull_up_subqueries_recurse(root, j->rarg,
													 lowest_outer_join,
													 NULL);
				break;
			case JOIN_LEFT:
			case JOIN_SEMI:
			case JOIN_ANTI:
				j->larg = pull_up_subqueries_recurse(root, j->larg,
													 j,
													 NULL);
				j->rarg = pull_up_subqueries_recurse(root, j->rarg,
													 j,
													 NULL);
				break;
			case JOIN_FULL:
				j->larg = pull_up_subqueries_recurse(root, j->larg,
													 j,
													 NULL);
				j->rarg = pull_up_subqueries_recurse(root, j->rarg,
													 j,
													 NULL);
				break;
			case JOIN_RIGHT:
				j->larg = pull_up_subqueries_recurse(root, j->larg,
													 j,
													 NULL);
				j->rarg = pull_up_subqueries_recurse(root, j->rarg,
													 j,
													 NULL);
				break;
			default:
				elog(ERROR, "unrecognized join type: %d",
					 (int) j->jointype);
				break;
		}
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
	return jtnode;
}

/*
 * pull_up_simple_subquery
 *		Attempt to pull up a single simple subquery.
 *
 * jtnode is a RangeTblRef that has been tentatively identified as a simple
 * subquery by pull_up_subqueries.  We return the replacement jointree node,
 * or jtnode itself if we determine that the subquery can't be pulled up
 * after all.
 *
 * rte is the RangeTblEntry referenced by jtnode.  Remaining parameters are
 * as for pull_up_subqueries_recurse.
 */
/*
 * pull_up_simple_subquery - (中文)上提单个简单子查询(本文件最复杂的函数)
 *
 * 【作用】把被 pull_up_subqueries 判定为"简单"的子查询(RTE_SUBQUERY)合并
 * 进父查询:制作子查询的可修改副本并建子 PlannerInfo(subroot),依次对其
 * 做 preprocess_relation_rtes / replace_empty_jointree / pull_up_sublinks /
 * preprocess_function_rtes / pull_up_subqueries 预处理,然后重新校验仍满足
 * 上提条件(不满足则放弃、返回原 jtnode);满足则展平其连接别名 Var、偏移
 * 其 varno 与 varlevelsup、把子查询目标列表变成 tlist 后用
 * perform_pullup_replace_vars 把父查询中所有对该子查询输出的引用替换为
 * 对应表达式(LATERAL 时按需包 PlaceHolderVar);随后把子查询的 rtable、
 * rowMarks、AppendRelInfo 并入父查询,修正 PlaceHolderVar / AppendRelInfo
 * 中的 relid,最后返回子查询的 jointree 以替换原来的 RangeTblRef。
 *
 * 【设计思想】
 * - "复制 + 试错":先复制子查询再加工,若中途发现不再简单(如预处理又
 *   引入无法上提的结构)就放弃,原 RTE 不动(代价是重新规划时会重做一遍);
 * - Var 替换是核心难点:子查询输出 Var 在全树(含上层连接条件)中被替换为
 *   子查询 tlist 对应表达式;LATERAL 子查询的表达式可能含对子查询外关系的
 *   引用,需要核对 nullingrels 决定哪些输出必须包 PlaceHolderVar,并用缓存
 *   rv_cache 保证相同输出只产生一个 PHV(避免重复求值、保证 equal() 可
 *   识别);
 * - groupingSets 父查询时所有 tlist 项都包 PHV(保持表达式身份,匹配分组集
 *   列);
 * - 把子查询的 AppendRelInfo 的 varno/level 也一并偏移,并修正父查询中
 *   引用了子查询 varno 的 PHV(替换为子查询 jointree 的关系集),最后把
 *   AppendRelInfo 并入父查询列表;
 * - 若子查询 jointree 退化为"无 quals 的单成员",直接返回该成员(省的
 *   FromExpr 包装);子查询的 hasSubLinks / hasRowSecurity 并入父查询。
 *
 * 【参数】
 *   root                 —— 父查询 PlannerInfo;
 *   jtnode               —— 引用子查询的 RangeTblRef;
 *   rte                  —— 对应的 RTE_SUBQUERY;
 *   lowest_outer_join    —— 之上最低外连接(透传自递归);
 *   containing_appendrel —— 所属 append 关系(透传自递归)。
 * 【返回值】替换 jointree 位置的节点:成功则子查询的 jointree(或退化的单
 * 成员),失败则原 jtnode。
 */
static Node *
pull_up_simple_subquery(PlannerInfo *root, Node *jtnode, RangeTblEntry *rte,
						JoinExpr *lowest_outer_join,
						AppendRelInfo *containing_appendrel)
{
	Query	   *parse = root->parse;
	int			varno = ((RangeTblRef *) jtnode)->rtindex;
	Query	   *subquery;
	PlannerInfo *subroot;
	int			rtoffset;
	pullup_replace_vars_context rvcontext;
	ListCell   *lc;

	/*
	 * Make a modifiable copy of the subquery to hack on, so that the RTE will
	 * be left unchanged in case we decide below that we can't pull it up
	 * after all.
	 */
	subquery = copyObject(rte->subquery);

	/*
	 * Create a PlannerInfo data structure for this subquery.
	 *
	 * NOTE: the next few steps should match the first processing in
	 * subquery_planner().  Can we refactor to avoid code duplication, or
	 * would that just make things uglier?
	 */
	subroot = makeNode(PlannerInfo);
	subroot->parse = subquery;
	subroot->glob = root->glob;
	subroot->query_level = root->query_level;
	subroot->plan_name = root->plan_name;
	subroot->alternative_plan_name = root->alternative_plan_name;
	subroot->parent_root = root->parent_root;
	subroot->plan_params = NIL;
	subroot->outer_params = NULL;
	subroot->planner_cxt = CurrentMemoryContext;
	subroot->init_plans = NIL;
	subroot->cte_plan_ids = NIL;
	subroot->multiexpr_params = NIL;
	subroot->join_domains = NIL;
	subroot->eq_classes = NIL;
	subroot->ec_merging_done = false;
	subroot->last_rinfo_serial = 0;
	subroot->all_result_relids = NULL;
	subroot->leaf_result_relids = NULL;
	subroot->append_rel_list = NIL;
	subroot->row_identity_vars = NIL;
	subroot->rowMarks = NIL;
	memset(subroot->upper_rels, 0, sizeof(subroot->upper_rels));
	memset(subroot->upper_targets, 0, sizeof(subroot->upper_targets));
	subroot->processed_groupClause = NIL;
	subroot->processed_distinctClause = NIL;
	subroot->processed_tlist = NIL;
	subroot->update_colnos = NIL;
	subroot->grouping_map = NULL;
	subroot->minmax_aggs = NIL;
	subroot->qual_security_level = 0;
	subroot->placeholdersFrozen = false;
	subroot->hasRecursion = false;
	subroot->assumeReplanning = false;
	subroot->wt_param_id = -1;
	subroot->non_recursive_path = NULL;
	/* We don't currently need a top JoinDomain for the subroot */

	/* No CTEs to worry about */
	Assert(subquery->cteList == NIL);

	/*
	 * Scan the rangetable for relation RTEs and retrieve the necessary
	 * catalog information for each relation.  Using this information, clear
	 * the inh flag for any relation that has no children, collect not-null
	 * attribute numbers for any relation that has column not-null
	 * constraints, and expand virtual generated columns for any relation that
	 * contains them.
	 */
	subquery = subroot->parse = preprocess_relation_rtes(subroot);

	/*
	 * If the FROM clause is empty, replace it with a dummy RTE_RESULT RTE, so
	 * that we don't need so many special cases to deal with that situation.
	 */
	replace_empty_jointree(subquery);

	/*
	 * Pull up any SubLinks within the subquery's quals, so that we don't
	 * leave unoptimized SubLinks behind.
	 */
	if (subquery->hasSubLinks)
		pull_up_sublinks(subroot);

	/*
	 * Similarly, preprocess its function RTEs to inline any set-returning
	 * functions in its rangetable.
	 */
	preprocess_function_rtes(subroot);

	/*
	 * Recursively pull up the subquery's subqueries, so that
	 * pull_up_subqueries' processing is complete for its jointree and
	 * rangetable.
	 *
	 * Note: it's okay that the subquery's recursion starts with NULL for
	 * containing-join info, even if we are within an outer join in the upper
	 * query; the lower query starts with a clean slate for outer-join
	 * semantics.  Likewise, we needn't pass down appendrel state.
	 */
	pull_up_subqueries(subroot);

	/*
	 * Now we must recheck whether the subquery is still simple enough to pull
	 * up.  If not, abandon processing it.
	 *
	 * We don't really need to recheck all the conditions involved, but it's
	 * easier just to keep this "if" looking the same as the one in
	 * pull_up_subqueries_recurse.
	 */
	if (is_simple_subquery(root, subquery, rte, lowest_outer_join) &&
		(containing_appendrel == NULL || is_safe_append_member(subquery)))
	{
		/* good to go */
	}
	else
	{
		/*
		 * Give up, return unmodified RangeTblRef.
		 *
		 * Note: The work we just did will be redone when the subquery gets
		 * planned on its own.  Perhaps we could avoid that by storing the
		 * modified subquery back into the rangetable, but I'm not gonna risk
		 * it now.
		 */
		return jtnode;
	}

	/*
	 * We must flatten any join alias Vars in the subquery's targetlist,
	 * because pulling up the subquery's subqueries might have changed their
	 * expansions into arbitrary expressions, which could affect
	 * pullup_replace_vars' decisions about whether PlaceHolderVar wrappers
	 * are needed for tlist entries.  (Likely it'd be better to do
	 * flatten_join_alias_vars on the whole query tree at some earlier stage,
	 * maybe even in the rewriter; but for now let's just fix this case here.)
	 */
	subquery->targetList = (List *)
		flatten_join_alias_vars(subroot, subroot->parse,
								(Node *) subquery->targetList);

	/*
	 * Adjust level-0 varnos in subquery so that we can append its rangetable
	 * to upper query's.  We have to fix the subquery's append_rel_list as
	 * well.
	 */
	rtoffset = list_length(parse->rtable);
	OffsetVarNodes((Node *) subquery, rtoffset, 0);
	OffsetVarNodes((Node *) subroot->append_rel_list, rtoffset, 0);

	/*
	 * Upper-level vars in subquery are now one level closer to their parent
	 * than before.
	 */
	IncrementVarSublevelsUp((Node *) subquery, -1, 1);
	IncrementVarSublevelsUp((Node *) subroot->append_rel_list, -1, 1);

	/*
	 * The subquery's targetlist items are now in the appropriate form to
	 * insert into the top query, except that we may need to wrap them in
	 * PlaceHolderVars.  Set up required context data for pullup_replace_vars.
	 * (Note that we should include the subquery's inner joins in relids,
	 * since it may include join alias vars referencing them.)
	 */
	rvcontext.root = root;
	rvcontext.targetlist = subquery->targetList;
	rvcontext.target_rte = rte;
	rvcontext.result_relation = 0;
	if (rte->lateral)
	{
		rvcontext.relids = get_relids_in_jointree((Node *) subquery->jointree,
												  true, true);
		rvcontext.nullinfo = get_nullingrels(parse);
	}
	else						/* won't need these values */
	{
		rvcontext.relids = NULL;
		rvcontext.nullinfo = NULL;
	}
	rvcontext.outer_hasSubLinks = &parse->hasSubLinks;
	rvcontext.varno = varno;
	/* this flag will be set below, if needed */
	rvcontext.wrap_option = REPLACE_WRAP_NONE;
	/* initialize cache array with indexes 0 .. length(tlist) */
	rvcontext.rv_cache = palloc0((list_length(subquery->targetList) + 1) *
								 sizeof(Node *));

	/*
	 * If the parent query uses grouping sets, we need a PlaceHolderVar for
	 * each expression of the subquery's targetlist items.  This ensures that
	 * expressions retain their separate identity so that they will match
	 * grouping set columns when appropriate.  (It'd be sufficient to wrap
	 * values used in grouping set columns, and do so only in non-aggregated
	 * portions of the tlist and havingQual, but that would require a lot of
	 * infrastructure that pullup_replace_vars hasn't currently got.)
	 */
	if (parse->groupingSets)
		rvcontext.wrap_option = REPLACE_WRAP_ALL;

	/*
	 * Replace all of the top query's references to the subquery's outputs
	 * with copies of the adjusted subtlist items, being careful not to
	 * replace any of the jointree structure.
	 */
	perform_pullup_replace_vars(root, &rvcontext,
								containing_appendrel);

	/*
	 * If the subquery had a LATERAL marker, propagate that to any of its
	 * child RTEs that could possibly now contain lateral cross-references.
	 * The children might or might not contain any actual lateral
	 * cross-references, but we have to mark the pulled-up child RTEs so that
	 * later planner stages will check for such.
	 */
	if (rte->lateral)
	{
		foreach(lc, subquery->rtable)
		{
			RangeTblEntry *child_rte = (RangeTblEntry *) lfirst(lc);

			switch (child_rte->rtekind)
			{
				case RTE_RELATION:
					if (child_rte->tablesample)
						child_rte->lateral = true;
					break;
				case RTE_SUBQUERY:
				case RTE_FUNCTION:
				case RTE_VALUES:
				case RTE_TABLEFUNC:
					child_rte->lateral = true;
					break;
				case RTE_JOIN:
				case RTE_CTE:
				case RTE_NAMEDTUPLESTORE:
				case RTE_RESULT:
				case RTE_GROUP:
					/* these can't contain any lateral references */
					break;
				case RTE_GRAPH_TABLE:
					/* shouldn't happen here */
					Assert(false);
					break;
			}
		}
	}

	/*
	 * Now append the adjusted rtable entries and their perminfos to upper
	 * query. (We hold off until after fixing the upper rtable entries; no
	 * point in running that code on the subquery ones too.)
	 */
	CombineRangeTables(&parse->rtable, &parse->rteperminfos,
					   subquery->rtable, subquery->rteperminfos);

	/*
	 * Pull up any FOR UPDATE/SHARE markers, too.  (OffsetVarNodes already
	 * adjusted the marker rtindexes, so just concat the lists.)
	 */
	parse->rowMarks = list_concat(parse->rowMarks, subquery->rowMarks);

	/*
	 * We also have to fix the relid sets of any PlaceHolderVar nodes in the
	 * parent query.  (This could perhaps be done by pullup_replace_vars(),
	 * but it seems cleaner to use two passes.)  Note in particular that any
	 * PlaceHolderVar nodes just created by pullup_replace_vars() will be
	 * adjusted, so having created them with the subquery's varno is correct.
	 *
	 * Likewise, relids appearing in AppendRelInfo nodes have to be fixed. We
	 * already checked that this won't require introducing multiple subrelids
	 * into the single-slot AppendRelInfo structs.
	 */
	if (root->glob->lastPHId != 0 || root->append_rel_list)
	{
		Relids		subrelids;

		subrelids = get_relids_in_jointree((Node *) subquery->jointree,
										   true, false);
		if (root->glob->lastPHId != 0)
			substitute_phv_relids((Node *) parse, varno, subrelids);
		fix_append_rel_relids(root, varno, subrelids);
	}

	/*
	 * And now add subquery's AppendRelInfos to our list.
	 */
	root->append_rel_list = list_concat(root->append_rel_list,
										subroot->append_rel_list);

	/*
	 * We don't have to do the equivalent bookkeeping for outer-join info,
	 * because that hasn't been set up yet.  placeholder_list likewise.
	 */
	Assert(root->join_info_list == NIL);
	Assert(subroot->join_info_list == NIL);
	Assert(root->placeholder_list == NIL);
	Assert(subroot->placeholder_list == NIL);

	/*
	 * We no longer need the RTE's copy of the subquery's query tree.  Getting
	 * rid of it saves nothing in particular so far as this level of query is
	 * concerned; but if this query level is in turn pulled up into a parent,
	 * we'd waste cycles copying the now-unused query tree.
	 */
	rte->subquery = NULL;

	/*
	 * Miscellaneous housekeeping.
	 *
	 * Although replace_rte_variables() faithfully updated parse->hasSubLinks
	 * if it copied any SubLinks out of the subquery's targetlist, we still
	 * could have SubLinks added to the query in the expressions of FUNCTION
	 * and VALUES RTEs copied up from the subquery.  So it's necessary to copy
	 * subquery->hasSubLinks anyway.  Perhaps this can be improved someday.
	 */
	parse->hasSubLinks |= subquery->hasSubLinks;

	/* If subquery had any RLS conditions, now main query does too */
	parse->hasRowSecurity |= subquery->hasRowSecurity;

	/*
	 * subquery won't be pulled up if it hasAggs, hasWindowFuncs, or
	 * hasTargetSRFs, so no work needed on those flags
	 */

	/*
	 * Return the adjusted subquery jointree to replace the RangeTblRef entry
	 * in parent's jointree; or, if the FromExpr is degenerate, just return
	 * its single member.
	 */
	Assert(IsA(subquery->jointree, FromExpr));
	Assert(subquery->jointree->fromlist != NIL);
	if (subquery->jointree->quals == NULL &&
		list_length(subquery->jointree->fromlist) == 1)
		return (Node *) linitial(subquery->jointree->fromlist);

	return (Node *) subquery->jointree;
}

/*
 * pull_up_simple_union_all
 *		Pull up a single simple UNION ALL subquery.
 *
 * jtnode is a RangeTblRef that has been identified as a simple UNION ALL
 * subquery by pull_up_subqueries.  We pull up the leaf subqueries and
 * build an "append relation" for the union set.  The result value is just
 * jtnode, since we don't actually need to change the query jointree.
 */
/*
 * pull_up_simple_union_all - (中文)上提单个简单 UNION ALL 子查询,展平为
 * append 关系
 *
 * 【作用】把判定为"简单 UNION ALL"的子查询展平:复制其 rtable(并减一层
 * varlevelsup、必要时把 LATERAL 标志传播给每个子 RTE)追加到父查询的
 * rangetable,调用 pull_up_union_leaf_queries 为每个叶子子查询建立
 * AppendRelInfo 并递归上提它们,最后把原 RTE 标记为继承父表(inh = true,
 * 表示它是一个 append 关系)。返回 jtnode 本身(连接树位置不变)。
 *
 * 【设计思想】
 * - 展平后,父查询里引用该 UNION 的 Var 被看成"引用整个 append 关系"的
 *   父 Var,各叶子通过 AppendRelInfo->translated_vars 做子/父列映射;
 * - 简单性保证(is_simple_union_all)意味着叶子类型一致、无排序/限制/锁
 *   等复杂特性,叶子可安全上提;
 * - 叶子之间不能互相引用,因此只需调整 varlevelsup,不需要偏移 varno。
 *
 * 【参数】
 *   root   —— 父查询 PlannerInfo;
 *   jtnode —— 引用该 UNION 子查询的 RangeTblRef;
 *   rte    —— 对应的 RTE_SUBQUERY(其 subquery 为 UNION ALL 查询)。
 * 【返回值】jtnode(原样)。
 */
static Node *
pull_up_simple_union_all(PlannerInfo *root, Node *jtnode, RangeTblEntry *rte)
{
	int			varno = ((RangeTblRef *) jtnode)->rtindex;
	Query	   *subquery = rte->subquery;
	int			rtoffset = list_length(root->parse->rtable);
	List	   *rtable;

	/*
	 * Make a modifiable copy of the subquery's rtable, so we can adjust
	 * upper-level Vars in it.  There are no such Vars in the setOperations
	 * tree proper, so fixing the rtable should be sufficient.
	 */
	rtable = copyObject(subquery->rtable);

	/*
	 * Upper-level vars in subquery are now one level closer to their parent
	 * than before.  We don't have to worry about offsetting varnos, though,
	 * because the UNION leaf queries can't cross-reference each other.
	 */
	IncrementVarSublevelsUp_rtable(rtable, -1, 1);

	/*
	 * If the UNION ALL subquery had a LATERAL marker, propagate that to all
	 * its children.  The individual children might or might not contain any
	 * actual lateral cross-references, but we have to mark the pulled-up
	 * child RTEs so that later planner stages will check for such.
	 */
	if (rte->lateral)
	{
		ListCell   *rt;

		foreach(rt, rtable)
		{
			RangeTblEntry *child_rte = (RangeTblEntry *) lfirst(rt);

			Assert(child_rte->rtekind == RTE_SUBQUERY);
			child_rte->lateral = true;
		}
	}

	/*
	 * Append child RTEs (and their perminfos) to parent rtable.
	 */
	CombineRangeTables(&root->parse->rtable, &root->parse->rteperminfos,
					   rtable, subquery->rteperminfos);

	/*
	 * Recursively scan the subquery's setOperations tree and add
	 * AppendRelInfo nodes for leaf subqueries to the parent's
	 * append_rel_list.  Also apply pull_up_subqueries to the leaf subqueries.
	 */
	Assert(subquery->setOperations);
	pull_up_union_leaf_queries(subquery->setOperations, root, varno, subquery,
							   rtoffset);

	/*
	 * Mark the parent as an append relation.
	 */
	rte->inh = true;

	return jtnode;
}

/*
 * pull_up_union_leaf_queries -- recursive guts of pull_up_simple_union_all
 *
 * Build an AppendRelInfo for each leaf query in the setop tree, and then
 * apply pull_up_subqueries to the leaf query.
 *
 * Note that setOpQuery is the Query containing the setOp node, whose tlist
 * contains references to all the setop output columns.  When called from
 * pull_up_simple_union_all, this is *not* the same as root->parse, which is
 * the parent Query we are pulling up into.
 *
 * parentRTindex is the appendrel parent's index in root->parse->rtable.
 *
 * The child RTEs have already been copied to the parent.  childRToffset
 * tells us where in the parent's range table they were copied.  When called
 * from flatten_simple_union_all, childRToffset is 0 since the child RTEs
 * were already in root->parse->rtable and no RT index adjustment is needed.
 */
/*
 * pull_up_union_leaf_queries - (中文)为 UNION ALL 集合运算树的每个叶子
 * 子查询构建 AppendRelInfo 并递归上提
 *
 * 【作用】递归扫描 setOp 树:叶子(RangeTblRef)处,计算其在父查询 rangetable
 * 中的索引(childRTindex = childRToffset + rtr->rtindex),用 make_setop_
 * translation_list 构建"父列 -> 子列"的翻译 Var 列表,新建 AppendRelInfo
 * 挂到 root->append_rel_list,然后用一个引用该叶子的 RangeTblRef 调用
 * pull_up_subqueries_recurse 递归上提该叶子(会就地改写 AppendRelInfo 中
 * 的 Var);非叶子(SetOperationStmt)则对左右递归。
 *
 * 【设计思想】
 * - 先建 AppendRelInfo 再上提叶子,是因为上提会修改其中的 Var(appendrel
 *   里唯一可能引用该叶子的位置),且上提时把 containing_appendrel 传给它,
 *   让 Var 替换走"仅改 translated_vars"的窄路径;
 * - childRToffset 的语义:从 pull_up_simple_union_all 调用时为 rtoffset(叶
 *   子已被复制到父 rtable 的偏移);从 flatten_simple_union_all 调用时为 0
 *   (叶子原本就在父 rtable 中,无需偏移)。
 *
 * 【参数】
 *   setOp         —— 当前集合运算节点;
 *   root          —— 父查询 PlannerInfo;
 *   parentRTindex —— append 父关系在父 rtable 中的索引;
 *   setOpQuery    —— 包含 setOp 树的查询(setop 输出 tlist 所在);
 *   childRToffset —— 叶子 RTE 在父 rtable 中相对其原索引的偏移。
 * 【返回值】无。
 */
static void
pull_up_union_leaf_queries(Node *setOp, PlannerInfo *root, int parentRTindex,
						   Query *setOpQuery, int childRToffset)
{
	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		int			childRTindex;
		AppendRelInfo *appinfo;

		/*
		 * Calculate the index in the parent's range table
		 */
		childRTindex = childRToffset + rtr->rtindex;

		/*
		 * Build a suitable AppendRelInfo, and attach to parent's list.
		 */
		appinfo = makeNode(AppendRelInfo);
		appinfo->parent_relid = parentRTindex;
		appinfo->child_relid = childRTindex;
		appinfo->parent_reltype = InvalidOid;
		appinfo->child_reltype = InvalidOid;
		make_setop_translation_list(setOpQuery, childRTindex, appinfo);
		appinfo->parent_reloid = InvalidOid;
		root->append_rel_list = lappend(root->append_rel_list, appinfo);

		/*
		 * Recursively apply pull_up_subqueries to the new child RTE.  (We
		 * must build the AppendRelInfo first, because this will modify it;
		 * indeed, that's the only part of the upper query where Vars
		 * referencing childRTindex can exist at this point.)
		 *
		 * Note that we can pass NULL for containing-join info even if we're
		 * actually under an outer join, because the child's expressions
		 * aren't going to propagate up to the join.  Also, we ignore the
		 * possibility that pull_up_subqueries_recurse() returns a different
		 * jointree node than what we pass it; if it does, the important thing
		 * is that it replaced the child relid in the AppendRelInfo node.
		 */
		rtr = makeNode(RangeTblRef);
		rtr->rtindex = childRTindex;
		(void) pull_up_subqueries_recurse(root, (Node *) rtr,
										  NULL, appinfo);
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		/* Recurse to reach leaf queries */
		pull_up_union_leaf_queries(op->larg, root, parentRTindex, setOpQuery,
								   childRToffset);
		pull_up_union_leaf_queries(op->rarg, root, parentRTindex, setOpQuery,
								   childRToffset);
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
	}
}

/*
 * make_setop_translation_list
 *	  Build the list of translations from parent Vars to child Vars for
 *	  a UNION ALL member.  (At this point it's just a simple list of
 *	  referencing Vars, but if we succeed in pulling up the member
 *	  subquery, the Vars will get replaced by pulled-up expressions.)
 *	  Also create the rather trivial reverse-translation array.
 */
/*
 * make_setop_translation_list - (中文)为 UNION ALL 成员构建"父列 -> 子列"
 * 的翻译 Var 列表
 *
 * 【作用】对给定叶子子查询(由 setOpQuery 提供其 targetList),生成翻译列表:
 * 每个非 resjunk 的目标条目对应一个引用 newvarno 关系的 Var(列号即原
 * resno),存入 appinfo->translated_vars;同时初始化反向数组 parent_colnos
 * (子列号 -> 父列号,resjunk 项保持 0)。
 *
 * 【设计思想】append 关系执行时,父计划的列必须从各叶子的对应列取出;这个
 * 翻译列表是 AppendRelInfo 的核心。若之后叶子被上提,translated_vars 里的
 * Var 会被替换为叶子 tlist 的表达式。
 *
 * 【参数】
 *   query   —— 叶子子查询(setOpQuery),提供 targetList;
 *   newvarno —— 生成的引用 Var 应使用的 varno(叶子在父 rtable 中的索引);
 *   appinfo —— 待填充的 AppendRelInfo。
 * 【返回值】无。
 */
static void
make_setop_translation_list(Query *query, int newvarno,
							AppendRelInfo *appinfo)
{
	List	   *vars = NIL;
	AttrNumber *pcolnos;
	ListCell   *l;

	/* Initialize reverse-translation array with all entries zero */
	/* (entries for resjunk columns will stay that way) */
	appinfo->num_child_cols = list_length(query->targetList);
	appinfo->parent_colnos = pcolnos =
		(AttrNumber *) palloc0(appinfo->num_child_cols * sizeof(AttrNumber));

	foreach(l, query->targetList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (tle->resjunk)
			continue;

		vars = lappend(vars, makeVarFromTargetEntry(newvarno, tle));
		pcolnos[tle->resno - 1] = tle->resno;
	}

	appinfo->translated_vars = vars;
}

/*
 * is_simple_subquery
 *	  Check a subquery in the range table to see if it's simple enough
 *	  to pull up into the parent query.
 *
 * rte is the RTE_SUBQUERY RangeTblEntry that contained the subquery.
 * (Note subquery is not necessarily equal to rte->subquery; it could be a
 * processed copy of that.)
 * lowest_outer_join is the lowest outer join above the subquery, or NULL.
 */
/*
 * is_simple_subquery - (中文)检查子查询是否"足够简单"可以上提
 *
 * 【作用】对 RTE_SUBQUERY 的子查询做一系列安全条件判定,全部满足才允许
 * 上提。拒绝的情形:命令非 SELECT、含 setops(除简单 UNION ALL 由另一条
 * 路径处理)、含聚合/窗口/SRF、GROUP BY/HAVING/SORT/DISTINCT/LIMIT/
 * FOR UPDATE、有 CTE、安全屏障视图、LATERAL 子查询带跨越外连接的引用
 * (或目标列表引用外连接之外的关系)、目标列表含 volatile 函数。
 *
 * 【设计思想】
 * - 上提的本质是把子查询的表达式"摊开"进父查询,任何"语义上要求子查询
 *   先独立完成"的特性(排序、去重、限量、聚合、锁)都会破坏等价性;
 * - volatile 函数被拒绝:上提后可能被复制到父查询多处求值,结果不可预测
 *   (PHV 机制也不能保证单次求值);
 * - LATERAL 的限制分两处:子查询的 WHERE/JOIN ON 里不能有越过外层连接的
 *   lateral 引用(否则需把条件从连接之下推迟到之上,复杂度不划算);当
 *   外层连接存在时,子查询目标列表引用外层连接之外关系的也不允许上提。
 *
 * 【参数】
 *   root             —— PlannerInfo;
 *   subquery         —— 待检查的子查询(可能是 rte->subquery 的处理副本);
 *   rte              —— 承载该子查询的 RTE_SUBQUERY;
 *   lowest_outer_join —— 该子查询之上最低的外连接,无则 NULL。
 * 【返回值】true 表示可以上提。
 */
static bool
is_simple_subquery(PlannerInfo *root, Query *subquery, RangeTblEntry *rte,
				   JoinExpr *lowest_outer_join)
{
	/*
	 * Let's just make sure it's a valid subselect ...
	 */
	if (!IsA(subquery, Query) ||
		subquery->commandType != CMD_SELECT)
		elog(ERROR, "subquery is bogus");

	/*
	 * Can't currently pull up a query with setops (unless it's simple UNION
	 * ALL, which is handled by a different code path). Maybe after querytree
	 * redesign...
	 */
	if (subquery->setOperations)
		return false;

	/*
	 * Can't pull up a subquery involving grouping, aggregation, SRFs,
	 * sorting, limiting, or WITH.  (XXX WITH could possibly be allowed later)
	 *
	 * We also don't pull up a subquery that has explicit FOR UPDATE/SHARE
	 * clauses, because pullup would cause the locking to occur semantically
	 * higher than it should.  Implicit FOR UPDATE/SHARE is okay because in
	 * that case the locking was originally declared in the upper query
	 * anyway.
	 */
	if (subquery->hasAggs ||
		subquery->hasWindowFuncs ||
		subquery->hasTargetSRFs ||
		subquery->groupClause ||
		subquery->groupingSets ||
		subquery->havingQual ||
		subquery->sortClause ||
		subquery->distinctClause ||
		subquery->limitOffset ||
		subquery->limitCount ||
		subquery->hasForUpdate ||
		subquery->cteList)
		return false;

	/*
	 * Don't pull up if the RTE represents a security-barrier view; we
	 * couldn't prevent information leakage once the RTE's Vars are scattered
	 * about in the upper query.
	 */
	if (rte->security_barrier)
		return false;

	/*
	 * If the subquery is LATERAL, check for pullup restrictions from that.
	 */
	if (rte->lateral)
	{
		bool		restricted;
		Relids		safe_upper_varnos;

		/*
		 * The subquery's WHERE and JOIN/ON quals mustn't contain any lateral
		 * references to rels outside a higher outer join (including the case
		 * where the outer join is within the subquery itself).  In such a
		 * case, pulling up would result in a situation where we need to
		 * postpone quals from below an outer join to above it, which is
		 * probably completely wrong and in any case is a complication that
		 * doesn't seem worth addressing at the moment.
		 */
		if (lowest_outer_join != NULL)
		{
			restricted = true;
			safe_upper_varnos = get_relids_in_jointree((Node *) lowest_outer_join,
													   true, true);
		}
		else
		{
			restricted = false;
			safe_upper_varnos = NULL;	/* doesn't matter */
		}

		if (jointree_contains_lateral_outer_refs(root,
												 (Node *) subquery->jointree,
												 restricted, safe_upper_varnos))
			return false;

		/*
		 * If there's an outer join above the LATERAL subquery, also disallow
		 * pullup if the subquery's targetlist has any references to rels
		 * outside the outer join, since these might get pulled into quals
		 * above the subquery (but in or below the outer join) and then lead
		 * to qual-postponement issues similar to the case checked for above.
		 * (We wouldn't need to prevent pullup if no such references appear in
		 * outer-query quals, but we don't have enough info here to check
		 * that.  Also, maybe this restriction could be removed if we forced
		 * such refs to be wrapped in PlaceHolderVars, even when they're below
		 * the nearest outer join?	But it's a pretty hokey usage, so not
		 * clear this is worth sweating over.)
		 *
		 * If you change this, see also the comments about lateral references
		 * in pullup_replace_vars_callback().
		 */
		if (lowest_outer_join != NULL)
		{
			Relids		lvarnos = pull_varnos_of_level(root,
													   (Node *) subquery->targetList,
													   1);

			if (!bms_is_subset(lvarnos, safe_upper_varnos))
				return false;
		}
	}

	/*
	 * Don't pull up a subquery that has any volatile functions in its
	 * targetlist.  Otherwise we might introduce multiple evaluations of these
	 * functions, if they get copied to multiple places in the upper query,
	 * leading to surprising results.  (Note: the PlaceHolderVar mechanism
	 * doesn't quite guarantee single evaluation; else we could pull up anyway
	 * and just wrap such items in PlaceHolderVars ...)
	 */
	if (contain_volatile_functions((Node *) subquery->targetList))
		return false;

	return true;
}

/*
 * pull_up_simple_values
 *		Pull up a single simple VALUES RTE.
 *
 * jtnode is a RangeTblRef that has been identified as a simple VALUES RTE
 * by pull_up_subqueries.  We always return a RangeTblRef representing a
 * RESULT RTE to replace it (all failure cases should have been detected by
 * is_simple_values()).  Actually, what we return is just jtnode, because
 * we replace the VALUES RTE in the rangetable with the RESULT RTE.
 *
 * rte is the RangeTblEntry referenced by jtnode.  Because of the limited
 * possible usage of VALUES RTEs, we do not need the remaining parameters
 * of pull_up_subqueries_recurse.
 */
/*
 * pull_up_simple_values - (中文)上提单个简单 VALUES RTE
 *
 * 【作用】把单行(单 VALUES 列表)、无集合返回/volatile 函数的 VALUES RTE
 * 上提:将其唯一 VALUES 列表的表达式制成目标列表,经 pullup_replace_vars
 * 把父查询中对这些列的引用替换为对应表达式,然后把该 VALUES RTE 原地换成
 * RTE_RESULT。返回 jtnode(连接树位置不变,仅 rtable 被替换)。
 *
 * 【设计思想】
 * - 单行 VALUES 固定输出一行,等价于 RTE_RESULT,故可如此转换;
 * - 限制条件由 is_simple_values 保证(单列表、无 SRF/volatile、且必须是
 *   当前查询唯一的 RTE),本函数只负责机械转换;
 * - VALUES 列表不含 level 0 的 Var,无需展平连接别名,也无需调整 nullingrels
 *   (不存在外连接);由于该查询只有一个 RTE(varno == 1),替换 rtable 即可。
 *
 * 【参数】
 *   root   —— PlannerInfo;
 *   jtnode —— 引用该 VALUES RTE 的 RangeTblRef;
 *   rte    —— 对应的 RTE_VALUES。
 * 【返回值】jtnode(原样,但 rtable 已把 VALUES 换成 RTE_RESULT)。
 */
static Node *
pull_up_simple_values(PlannerInfo *root, Node *jtnode, RangeTblEntry *rte)
{
	Query	   *parse = root->parse;
	int			varno = ((RangeTblRef *) jtnode)->rtindex;
	List	   *values_list;
	List	   *tlist;
	AttrNumber	attrno;
	pullup_replace_vars_context rvcontext;
	ListCell   *lc;

	Assert(rte->rtekind == RTE_VALUES);
	Assert(list_length(rte->values_lists) == 1);

	/*
	 * Need a modifiable copy of the VALUES list to hack on, just in case it's
	 * multiply referenced.
	 */
	values_list = copyObject(linitial(rte->values_lists));

	/*
	 * The VALUES RTE can't contain any Vars of level zero, let alone any that
	 * are join aliases, so no need to flatten join alias Vars.
	 */
	Assert(!contain_vars_of_level((Node *) values_list, 0));

	/*
	 * Set up required context data for pullup_replace_vars.  In particular,
	 * we have to make the VALUES list look like a subquery targetlist.
	 */
	tlist = NIL;
	attrno = 1;
	foreach(lc, values_list)
	{
		tlist = lappend(tlist,
						makeTargetEntry((Expr *) lfirst(lc),
										attrno,
										NULL,
										false));
		attrno++;
	}
	rvcontext.root = root;
	rvcontext.targetlist = tlist;
	rvcontext.target_rte = rte;
	rvcontext.result_relation = 0;
	rvcontext.relids = NULL;	/* can't be any lateral references here */
	rvcontext.nullinfo = NULL;
	rvcontext.outer_hasSubLinks = &parse->hasSubLinks;
	rvcontext.varno = varno;
	rvcontext.wrap_option = REPLACE_WRAP_NONE;
	/* initialize cache array with indexes 0 .. length(tlist) */
	rvcontext.rv_cache = palloc0((list_length(tlist) + 1) *
								 sizeof(Node *));

	/*
	 * Replace all of the top query's references to the RTE's outputs with
	 * copies of the adjusted VALUES expressions, being careful not to replace
	 * any of the jointree structure.  We can assume there's no outer joins or
	 * appendrels in the dummy Query that surrounds a VALUES RTE.
	 */
	perform_pullup_replace_vars(root, &rvcontext, NULL);

	/*
	 * There should be no appendrels to fix, nor any outer joins and hence no
	 * PlaceHolderVars.
	 */
	Assert(root->append_rel_list == NIL);
	Assert(root->join_info_list == NIL);
	Assert(root->placeholder_list == NIL);

	/*
	 * Replace the VALUES RTE with a RESULT RTE.  The VALUES RTE is the only
	 * rtable entry in the current query level, so this is easy.
	 */
	Assert(list_length(parse->rtable) == 1);

	/* Create suitable RTE */
	rte = makeNode(RangeTblEntry);
	rte->rtekind = RTE_RESULT;
	rte->eref = makeAlias("*RESULT*", NIL);

	/* Replace rangetable */
	parse->rtable = list_make1(rte);

	/* We could manufacture a new RangeTblRef, but the one we have is fine */
	Assert(varno == 1);

	return jtnode;
}

/*
 * is_simple_values
 *	  Check a VALUES RTE in the range table to see if it's simple enough
 *	  to pull up into the parent query.
 *
 * rte is the RTE_VALUES RangeTblEntry to check.
 */
/*
 * is_simple_values - (中文)检查 VALUES RTE 是否简单到可以上提
 *
 * 【作用】判定条件:恰好一个 VALUES 列表(多行无法语义等价地换成 RTE_RESULT);
 * 不含集合返回函数与 volatile 函数(与可上提子查询目标列表的考虑一致);
 * 且该 VALUES 必须是当前查询唯一的关系(这是解析器当前唯一会生成的形态,
 * 也极大简化了 pull_up_simple_values)。满足全部返回 true。
 *
 * 【设计思想】外连接之下不会出现 VALUES(即使出现也不上提),因此无需担心
 * LATERAL 与 PHV 合法性;对 volatile/SRF 的拒绝理由与 is_simple_subquery
 * 相同(上提后可能被多次求值或破坏单行假设)。
 *
 * 【参数】
 *   root —— PlannerInfo(用于检查其 rtable);
 *   rte  —— 待检查的 RTE_VALUES。
 * 【返回值】true 表示可上提。
 */
static bool
is_simple_values(PlannerInfo *root, RangeTblEntry *rte)
{
	Assert(rte->rtekind == RTE_VALUES);

	/*
	 * There must be exactly one VALUES list, else it's not semantically
	 * correct to replace the VALUES RTE with a RESULT RTE, nor would we have
	 * a unique set of expressions to substitute into the parent query.
	 */
	if (list_length(rte->values_lists) != 1)
		return false;

	/*
	 * Because VALUES can't appear under an outer join (or at least, we won't
	 * try to pull it up if it does), we need not worry about LATERAL, nor
	 * about validity of PHVs for the VALUES' outputs.
	 */

	/*
	 * Don't pull up a VALUES that contains any set-returning or volatile
	 * functions.  The considerations here are basically identical to the
	 * restrictions on a pull-able subquery's targetlist.
	 */
	if (expression_returns_set((Node *) rte->values_lists) ||
		contain_volatile_functions((Node *) rte->values_lists))
		return false;

	/*
	 * Do not pull up a VALUES that's not the only RTE in its parent query.
	 * This is actually the only case that the parser will generate at the
	 * moment, and assuming this is true greatly simplifies
	 * pull_up_simple_values().
	 */
	if (list_length(root->parse->rtable) != 1 ||
		rte != (RangeTblEntry *) linitial(root->parse->rtable))
		return false;

	return true;
}

/*
 * pull_up_constant_function
 *		Pull up an RTE_FUNCTION expression that was simplified to a constant.
 *
 * jtnode is a RangeTblRef that has been identified as a FUNCTION RTE by
 * pull_up_subqueries.  If its expression is just a Const, hoist that value
 * up into the parent query, and replace the RTE_FUNCTION with RTE_RESULT.
 *
 * In principle we could pull up any immutable expression, but we don't.
 * That might result in multiple evaluations of the expression, which could
 * be costly if it's not just a Const.  Also, the main value of this is
 * to let the constant participate in further const-folding, and of course
 * that won't happen for a non-Const.
 *
 * The pulled-up value might need to be wrapped in a PlaceHolderVar if the
 * RTE is below an outer join or is part of an appendrel; the extra
 * parameters show whether that's needed.
 */
/*
 * pull_up_constant_function - (中文)上提被化简为常量的函数 RTE
 *
 * 【作用】对单个、标量结果的 Const 函数表达式 RTE(且无 ORDINALITY、无
 * coldeflist、结果类型为标量)执行上提:把该 Const 制成单元素目标列表,
 * 用 pullup_replace_vars 把父查询中对这个函数 RTE 输出的引用替换为常量,
 * 再把 RTE 改为 RTE_RESULT(清空 functions、取消 lateral 标记)。不满足
 * 条件的直接返回 jtnode 不做处理。
 *
 * 【设计思想】
 * - 只对纯常量做上提:非常量(即使不可变)上提会被复制到多处求值,既可能
 *   昂贵,也无法继续参与常量折叠(上提的价值恰恰在于参与后续 const-folding);
 * - 复合类型/多列结果因实现复杂而放弃;RTE_RESULT 表示"不再扫描它",连接
 *   树节点可原样保留,后续 remove_useless_result_rtes 会进一步清理;
 * - 若父查询使用 groupingSets,输出须包 PHV(与子查询上提相同的理由);
 * - 上提后无需修正父查询中的 PHV:它们对 RT 索引的引用暂时仍有效,若之后
 *   能删掉该 RTE_RESULT 会被一并清理。
 *
 * 【参数】
 *   root                 —— PlannerInfo;
 *   jtnode               —— 引用该函数 RTE 的 RangeTblRef;
 *   rte                  —— 对应的 RTE_FUNCTION;
 *   containing_appendrel —— 所属 append 关系(决定是否需要 PHV 包裹)。
 * 【返回值】连接树节点(成功与否都返回 jtnode,RTE 形态可能已变)。
 */
static Node *
pull_up_constant_function(PlannerInfo *root, Node *jtnode,
						  RangeTblEntry *rte,
						  AppendRelInfo *containing_appendrel)
{
	Query	   *parse = root->parse;
	RangeTblFunction *rtf;
	TypeFuncClass functypclass;
	Oid			funcrettype;
	TupleDesc	tupdesc;
	pullup_replace_vars_context rvcontext;

	/* Fail if the RTE has ORDINALITY - we don't implement that here. */
	if (rte->funcordinality)
		return jtnode;

	/* Fail if RTE isn't a single, simple Const expr */
	if (list_length(rte->functions) != 1)
		return jtnode;
	rtf = linitial_node(RangeTblFunction, rte->functions);
	if (!IsA(rtf->funcexpr, Const))
		return jtnode;

	/*
	 * If the function's result is not a scalar, we punt.  In principle we
	 * could break the composite constant value apart into per-column
	 * constants, but for now it seems not worth the work.
	 */
	if (rtf->funccolcount != 1)
		return jtnode;			/* definitely composite */

	/* If it has a coldeflist, it certainly returns RECORD */
	if (rtf->funccolnames != NIL)
		return jtnode;			/* must be a one-column RECORD type */

	functypclass = get_expr_result_type(rtf->funcexpr,
										&funcrettype,
										&tupdesc);
	if (functypclass != TYPEFUNC_SCALAR)
		return jtnode;			/* must be a one-column composite type */

	/* Create context for applying pullup_replace_vars */
	rvcontext.root = root;
	rvcontext.targetlist = list_make1(makeTargetEntry((Expr *) rtf->funcexpr,
													  1,	/* resno */
													  NULL, /* resname */
													  false));	/* resjunk */
	rvcontext.target_rte = rte;
	rvcontext.result_relation = 0;

	/*
	 * Since this function was reduced to a Const, it doesn't contain any
	 * lateral references, even if it's marked as LATERAL.  This means we
	 * don't need to fill relids or nullinfo.
	 */
	rvcontext.relids = NULL;
	rvcontext.nullinfo = NULL;

	rvcontext.outer_hasSubLinks = &parse->hasSubLinks;
	rvcontext.varno = ((RangeTblRef *) jtnode)->rtindex;
	/* this flag will be set below, if needed */
	rvcontext.wrap_option = REPLACE_WRAP_NONE;
	/* initialize cache array with indexes 0 .. length(tlist) */
	rvcontext.rv_cache = palloc0((list_length(rvcontext.targetlist) + 1) *
								 sizeof(Node *));

	/*
	 * If the parent query uses grouping sets, we need a PlaceHolderVar for
	 * each expression of the subquery's targetlist items.  (See comments in
	 * pull_up_simple_subquery().)
	 */
	if (parse->groupingSets)
		rvcontext.wrap_option = REPLACE_WRAP_ALL;

	/*
	 * Replace all of the top query's references to the RTE's output with
	 * copies of the funcexpr, being careful not to replace any of the
	 * jointree structure.
	 */
	perform_pullup_replace_vars(root, &rvcontext,
								containing_appendrel);

	/*
	 * We don't need to bother with changing PlaceHolderVars in the parent
	 * query.  Their references to the RT index are still good for now, and
	 * will get removed later if we're able to drop the RTE_RESULT.
	 */

	/*
	 * Convert the RTE to be RTE_RESULT type, signifying that we don't need to
	 * scan it anymore, and zero out RTE_FUNCTION-specific fields.  Also make
	 * sure the RTE is not marked LATERAL, since elsewhere we don't expect
	 * RTE_RESULTs to be LATERAL.
	 */
	rte->rtekind = RTE_RESULT;
	rte->functions = NIL;
	rte->lateral = false;

	/*
	 * We can reuse the RangeTblRef node.
	 */
	return jtnode;
}

/*
 * is_simple_union_all
 *	  Check a subquery to see if it's a simple UNION ALL.
 *
 * We require all the setops to be UNION ALL (no mixing) and there can't be
 * any datatype coercions involved, ie, all the leaf queries must emit the
 * same datatypes.
 */
/*
 * is_simple_union_all - (中文)检查子查询是否是一棵纯 UNION ALL 树
 *
 * 【作用】判定:子查询必须是 SELECT,且是集合运算查询(setOperations 非空,
 * 顶层为 SetOperationStmt),没有 ORDER BY / LIMIT / 行锁 / CTE,且整棵集合
 * 运算树满足 is_simple_union_all_recurse(全部为 UNION ALL、叶子输出类型
 * 与顶层列类型一致)。
 *
 * 【设计思想】这是"展平为 append 关系"的前置检查:append 关系要求所有叶子
 * 列类型一致(否则需要转换节点)、无排序/限量/锁等复杂语义。与
 * is_simple_subquery 的差异是:UNION ALL 子查询不能整体上提,但可以展平。
 *
 * 【参数】subquery —— 待检查的子查询。
 * 【返回值】true 表示是简单 UNION ALL,可展平。
 */
static bool
is_simple_union_all(Query *subquery)
{
	SetOperationStmt *topop;

	/* Let's just make sure it's a valid subselect ... */
	if (!IsA(subquery, Query) ||
		subquery->commandType != CMD_SELECT)
		elog(ERROR, "subquery is bogus");

	/* Is it a set-operation query at all? */
	topop = castNode(SetOperationStmt, subquery->setOperations);
	if (!topop)
		return false;

	/* Can't handle ORDER BY, LIMIT/OFFSET, locking, or WITH */
	if (subquery->sortClause ||
		subquery->limitOffset ||
		subquery->limitCount ||
		subquery->rowMarks ||
		subquery->cteList)
		return false;

	/* Recursively check the tree of set operations */
	return is_simple_union_all_recurse((Node *) topop, subquery,
									   topop->colTypes);
}

/*
 * is_simple_union_all_recurse - (中文)递归检查集合运算树是否全部为类型一致
 * 的 UNION ALL
 *
 * 【作用】递归遍历 setOp 树:叶子(RangeTblRef)处用 tlist_same_datatypes
 * 检查其子查询输出列类型是否与顶层 colTypes 一致(不比较 typmod 与
 * collation);内部节点必须是 SETOP_UNION 且 all 标志为真,再对左右递归;
 * 任何不满足即返回 false。
 *
 * 【设计思想】append 展平要求"整棵树都是 UNION ALL 且列类型无需强制转换"
 * ——混合 INTERSECT/EXCEPT、去重 UNION 或类型不一致都会破坏 append 关系
 * 的语义,需要走通用集合运算规划路径。
 *
 * 【参数】
 *   setOp      —— 当前集合运算节点;
 *   setOpQuery —— 包含该节点的查询(提供 rtable 供叶子查找子查询);
 *   colTypes   —— 顶层结果列类型列表。
 * 【返回值】true 表示该子树可视为简单 UNION ALL。
 */
static bool
is_simple_union_all_recurse(Node *setOp, Query *setOpQuery, List *colTypes)
{
	/* Since this function recurses, it could be driven to stack overflow. */
	check_stack_depth();

	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		RangeTblEntry *rte = rt_fetch(rtr->rtindex, setOpQuery->rtable);
		Query	   *subquery = rte->subquery;

		Assert(subquery != NULL);

		/* Leaf nodes are OK if they match the toplevel column types */
		/* We don't have to compare typmods or collations here */
		return tlist_same_datatypes(subquery->targetList, colTypes, true);
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		/* Must be UNION ALL */
		if (op->op != SETOP_UNION || !op->all)
			return false;

		/* Recurse to check inputs */
		return is_simple_union_all_recurse(op->larg, setOpQuery, colTypes) &&
			is_simple_union_all_recurse(op->rarg, setOpQuery, colTypes);
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
		return false;			/* keep compiler quiet */
	}
}

/*
 * is_safe_append_member
 *	  Check a subquery that is a leaf of a UNION ALL appendrel to see if it's
 *	  safe to pull up.
 */
/*
 * is_safe_append_member - (中文)检查作为 UNION ALL append 叶子子查询的子
 * 查询能否安全上提
 *
 * 【作用】要求该子查询的 jointree 要么完全为空,要么"去掉所有 FromExpr
 * 包装后恰为一个 RangeTblRef"(中间不允许有 quals、不允许有多个成员)。
 * 满足返回 true。
 *
 * 【设计思想】AppendRelInfo 结构假设每个 append 成员恰好对应一个基关系
 * (relid 单值),否则 fix_append_rel_relids 等会把多关系成员弄乱;子查询
 * 有 WHERE 条件也没地方安置(append 关系的叶子不支持独立过滤)。完全空
 * 的 jointree 特例放行,因为上提时会由 pull_up_simple_subquery 插入单个
 * RTE_RESULT。
 *
 * 【参数】subquery —— 待检查的叶子子查询。
 * 【返回值】true 表示可安全上提为 append 成员。
 */
static bool
is_safe_append_member(Query *subquery)
{
	FromExpr   *jtnode;

	/*
	 * It's only safe to pull up the child if its jointree contains exactly
	 * one RTE, else the AppendRelInfo data structure breaks. The one base RTE
	 * could be buried in several levels of FromExpr, however.  Also, if the
	 * child's jointree is completely empty, we can pull up because
	 * pull_up_simple_subquery will insert a single RTE_RESULT RTE instead.
	 *
	 * Also, the child can't have any WHERE quals because there's no place to
	 * put them in an appendrel.  (This is a bit annoying...) If we didn't
	 * need to check this, we'd just test whether get_relids_in_jointree()
	 * yields a singleton set, to be more consistent with the coding of
	 * fix_append_rel_relids().
	 */
	jtnode = subquery->jointree;
	Assert(IsA(jtnode, FromExpr));
	/* Check the completely-empty case */
	if (jtnode->fromlist == NIL && jtnode->quals == NULL)
		return true;
	/* Check the more general case */
	while (IsA(jtnode, FromExpr))
	{
		if (jtnode->quals != NULL)
			return false;
		if (list_length(jtnode->fromlist) != 1)
			return false;
		jtnode = linitial(jtnode->fromlist);
	}
	if (!IsA(jtnode, RangeTblRef))
		return false;

	return true;
}

/*
 * jointree_contains_lateral_outer_refs
 *		Check for disallowed lateral references in a jointree's quals
 *
 * If restricted is false, all level-1 Vars are allowed (but we still must
 * search the jointree, since it might contain outer joins below which there
 * will be restrictions).  If restricted is true, return true when any qual
 * in the jointree contains level-1 Vars coming from outside the rels listed
 * in safe_upper_varnos.
 */
/*
 * jointree_contains_lateral_outer_refs - (中文)检查连接树的限定条件中是否含
 * 有被禁止的 lateral 外部引用
 *
 * 【作用】递归检查连接树(用于 LATERAL 子查询的可上提判定)。restricted 为
 * false 时仅需继续下潜(因为下方可能有外连接引入限制);restricted 为 true
 * 时,任何限定条件(FromExpr 的 quals、JoinExpr 的 quals)中出现"level-1
 * Var 不包含于 safe_upper_varnos"即返回 true。遇到非 INNER 连接时,其下的
 * 所有 lateral 引用都被禁止,故把 restricted 收紧为 true 并清空
 * safe_upper_varnos。
 *
 * 【设计思想】上提 LATERAL 子查询的危险在于"从外连接之下引用了外连接之
 * 外的关系":这种引用一旦上提,限定条件就必须从连接之下推迟到之上,语义
 * 复杂且易错,故直接禁止。
 *
 * 【参数】
 *   root              —— PlannerInfo;
 *   jtnode            —— 待检查的连接树节点;
 *   restricted        —— 是否已处于受限模式;
 *   safe_upper_varnos —— restricted 时,允许引用的上层关系集合。
 * 【返回值】true 表示发现被禁止的 lateral 引用。
 */
static bool
jointree_contains_lateral_outer_refs(PlannerInfo *root, Node *jtnode,
									 bool restricted,
									 Relids safe_upper_varnos)
{
	if (jtnode == NULL)
		return false;
	if (IsA(jtnode, RangeTblRef))
		return false;
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		/* First, recurse to check child joins */
		foreach(l, f->fromlist)
		{
			if (jointree_contains_lateral_outer_refs(root,
													 lfirst(l),
													 restricted,
													 safe_upper_varnos))
				return true;
		}

		/* Then check the top-level quals */
		if (restricted &&
			!bms_is_subset(pull_varnos_of_level(root, f->quals, 1),
						   safe_upper_varnos))
			return true;
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		/*
		 * If this is an outer join, we mustn't allow any upper lateral
		 * references in or below it.
		 */
		if (j->jointype != JOIN_INNER)
		{
			restricted = true;
			safe_upper_varnos = NULL;
		}

		/* Check the child joins */
		if (jointree_contains_lateral_outer_refs(root,
												 j->larg,
												 restricted,
												 safe_upper_varnos))
			return true;
		if (jointree_contains_lateral_outer_refs(root,
												 j->rarg,
												 restricted,
												 safe_upper_varnos))
			return true;

		/* Check the JOIN's qual clauses */
		if (restricted &&
			!bms_is_subset(pull_varnos_of_level(root, j->quals, 1),
						   safe_upper_varnos))
			return true;
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
	return false;
}

/*
 * Perform pullup_replace_vars everyplace it's needed in the query tree.
 *
 * Caller has already filled *rvcontext with data describing what to
 * substitute for Vars referencing the target subquery.  In addition
 * we need the identity of the containing appendrel if any.
 */
/*
 * perform_pullup_replace_vars - (中文)在查询树所有需要的位置执行
 * pullup_replace_vars
 *
 * 【作用】把父查询中所有引用被上提子查询输出的 Var 替换为对应表达式:
 * 依次处理 targetList、returningList、onConflict(Set/Where)、mergeActionList
 * 各动作的 qual/targetList、mergeJoinCondition、jointree 内各限定条件
 * (replace_vars_in_jointree)、havingQual、各 AppendRelInfo 的
 * translated_vars、各 RTE_JOIN 的 joinaliasvars 与 RTE_GROUP 的 groupexprs。
 * 若 containing_appendrel 非空(append 成员上提),只处理该 AppendRelInfo 的
 * translated_vars,并临时关闭 PHV 包裹。
 *
 * 【设计思想】
 * - 之所以逐项调用而非 query_tree_mutator 整树替换:后者会返回整树的副本,
 *   会破坏 jointree 的身份(外层递归持有 lowest_outer_join 指针等);
 * - 上层结构(targetList/returningList/havingQual 等)一定在外连接之上,
 *   必须用 PHV;jointree 内部的位置由 replace_vars_in_jointree 按所在连接
 *   类型决定是否需要 PHV(如 FULL 连接的 quals);
 * - ON CONFLICT 的 arbiter 字段与 exclRelTlist 假定不引用子查询,不处理。
 *
 * 【参数】
 *   root                 —— PlannerInfo;
 *   rvcontext            —— 已填好的替换上下文;
 *   containing_appendrel —— 所属 append 关系(若为 append 成员上提)。
 * 【返回值】无。
 */
static void
perform_pullup_replace_vars(PlannerInfo *root,
							pullup_replace_vars_context *rvcontext,
							AppendRelInfo *containing_appendrel)
{
	Query	   *parse = root->parse;
	ListCell   *lc;

	/*
	 * If we are considering an appendrel child subquery (that is, a UNION ALL
	 * member query that we're pulling up), then the only part of the upper
	 * query that could reference the child yet is the translated_vars list of
	 * the associated AppendRelInfo.  Furthermore, we do not want to force use
	 * of PHVs in the AppendRelInfo --- there isn't any outer join between.
	 */
	if (containing_appendrel)
	{
		ReplaceWrapOption save_wrap_option = rvcontext->wrap_option;

		rvcontext->wrap_option = REPLACE_WRAP_NONE;
		containing_appendrel->translated_vars = (List *)
			pullup_replace_vars((Node *) containing_appendrel->translated_vars,
								rvcontext);
		rvcontext->wrap_option = save_wrap_option;
		return;
	}

	/*
	 * Replace all of the top query's references to the subquery's outputs
	 * with copies of the adjusted subtlist items, being careful not to
	 * replace any of the jointree structure.  (This'd be a lot cleaner if we
	 * could use query_tree_mutator.)  We have to use PHVs in the targetList,
	 * returningList, and havingQual, since those are certainly above any
	 * outer join.  replace_vars_in_jointree tracks its location in the
	 * jointree and uses PHVs or not appropriately.
	 */
	parse->targetList = (List *)
		pullup_replace_vars((Node *) parse->targetList, rvcontext);
	parse->returningList = (List *)
		pullup_replace_vars((Node *) parse->returningList, rvcontext);

	if (parse->onConflict)
	{
		parse->onConflict->onConflictSet = (List *)
			pullup_replace_vars((Node *) parse->onConflict->onConflictSet,
								rvcontext);
		parse->onConflict->onConflictWhere =
			pullup_replace_vars(parse->onConflict->onConflictWhere,
								rvcontext);

		/*
		 * We assume ON CONFLICT's arbiterElems, arbiterWhere, exclRelTlist
		 * can't contain any references to a subquery.
		 */
	}
	if (parse->mergeActionList)
	{
		foreach(lc, parse->mergeActionList)
		{
			MergeAction *action = lfirst(lc);

			action->qual = pullup_replace_vars(action->qual, rvcontext);
			action->targetList = (List *)
				pullup_replace_vars((Node *) action->targetList, rvcontext);
		}
	}
	parse->mergeJoinCondition = pullup_replace_vars(parse->mergeJoinCondition,
													rvcontext);
	replace_vars_in_jointree((Node *) parse->jointree, rvcontext);
	Assert(parse->setOperations == NULL);
	parse->havingQual = pullup_replace_vars(parse->havingQual, rvcontext);

	/*
	 * Replace references in the translated_vars lists of appendrels.
	 */
	foreach(lc, root->append_rel_list)
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) lfirst(lc);

		appinfo->translated_vars = (List *)
			pullup_replace_vars((Node *) appinfo->translated_vars, rvcontext);
	}

	/*
	 * Replace references in the joinaliasvars lists of join RTEs and the
	 * groupexprs list of group RTE.
	 */
	foreach(lc, parse->rtable)
	{
		RangeTblEntry *otherrte = (RangeTblEntry *) lfirst(lc);

		if (otherrte->rtekind == RTE_JOIN)
			otherrte->joinaliasvars = (List *)
				pullup_replace_vars((Node *) otherrte->joinaliasvars,
									rvcontext);
		else if (otherrte->rtekind == RTE_GROUP)
			otherrte->groupexprs = (List *)
				pullup_replace_vars((Node *) otherrte->groupexprs,
									rvcontext);
	}
}

/*
 * Helper routine for perform_pullup_replace_vars: do pullup_replace_vars on
 * every expression in the jointree, without changing the jointree structure
 * itself.  Ugly, but there's no other way...
 */
/*
 * replace_vars_in_jointree - (中文)对连接树中每个表达式做 Var 替换而不改变
 * 连接树结构本身
 *
 * 【作用】遍历连接树:RangeTblRef 处,若它引用的是别的 LATERAL 关系(不是
 * 被上提的那个),则按 RTE 类型对其表达式(tablesample / subquery /
 * functions / tablefunc / values_lists)做 pullup_replace_vars;FromExpr 处
 * 递归子节点并替换其 quals;JoinExpr 处递归左右,并按连接类型决定 quals
 * 是否用 PHV 包裹(FULL 连接把 wrap_option 临时设为 REPLACE_WRAP_VARFREE)。
 *
 * 【设计思想】
 * - 从 jointree 驱动而不是从 rtable 驱动,可避免处理已不再被引用的 RTE;
 * - 被上提子查询自身(varno == context->varno)跳过;
 * - FULL 连接限定条件中的"无变量表达式"必须包 PHV:否则无法分辨它来自哪
 *   一侧,可能使任何连接条件都"看起来"无法成为可合并/可哈希条件,导致
 *   根本无法生成计划。
 *
 * 【参数】
 *   jtnode  —— 当前连接树节点;
 *   context —— 替换上下文。
 * 【返回值】无。
 */
static void
replace_vars_in_jointree(Node *jtnode,
						 pullup_replace_vars_context *context)
{
	if (jtnode == NULL)
		return;
	if (IsA(jtnode, RangeTblRef))
	{
		/*
		 * If the RangeTblRef refers to a LATERAL subquery (that isn't the
		 * same subquery we're pulling up), it might contain references to the
		 * target subquery, which we must replace.  We drive this from the
		 * jointree scan, rather than a scan of the rtable, so that we can
		 * avoid processing no-longer-referenced RTEs.
		 */
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		if (varno != context->varno)	/* ignore target subquery itself */
		{
			RangeTblEntry *rte = rt_fetch(varno, context->root->parse->rtable);

			Assert(rte != context->target_rte);
			if (rte->lateral)
			{
				switch (rte->rtekind)
				{
					case RTE_RELATION:
						/* shouldn't be marked LATERAL unless tablesample */
						Assert(rte->tablesample);
						rte->tablesample = (TableSampleClause *)
							pullup_replace_vars((Node *) rte->tablesample,
												context);
						break;
					case RTE_SUBQUERY:
						rte->subquery =
							pullup_replace_vars_subquery(rte->subquery,
														 context);
						break;
					case RTE_FUNCTION:
						rte->functions = (List *)
							pullup_replace_vars((Node *) rte->functions,
												context);
						break;
					case RTE_TABLEFUNC:
						rte->tablefunc = (TableFunc *)
							pullup_replace_vars((Node *) rte->tablefunc,
												context);
						break;
					case RTE_VALUES:
						rte->values_lists = (List *)
							pullup_replace_vars((Node *) rte->values_lists,
												context);
						break;
					case RTE_JOIN:
					case RTE_CTE:
					case RTE_NAMEDTUPLESTORE:
					case RTE_RESULT:
					case RTE_GROUP:
						/* these shouldn't be marked LATERAL */
						Assert(false);
						break;
					case RTE_GRAPH_TABLE:
						/* shouldn't happen here */
						Assert(false);
						break;
				}
			}
		}
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		foreach(l, f->fromlist)
			replace_vars_in_jointree(lfirst(l), context);
		f->quals = pullup_replace_vars(f->quals, context);
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;
		ReplaceWrapOption save_wrap_option = context->wrap_option;

		replace_vars_in_jointree(j->larg, context);
		replace_vars_in_jointree(j->rarg, context);

		/*
		 * Use PHVs within the join quals of a full join for variable-free
		 * expressions.  Otherwise, we cannot identify which side of the join
		 * a pulled-up variable-free expression came from, which can lead to
		 * failure to make a plan at all because none of the quals appear to
		 * be mergeable or hashable conditions.
		 */
		if (j->jointype == JOIN_FULL)
			context->wrap_option = REPLACE_WRAP_VARFREE;

		j->quals = pullup_replace_vars(j->quals, context);

		context->wrap_option = save_wrap_option;
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
}

/*
 * Apply pullup variable replacement throughout an expression tree
 *
 * Returns a modified copy of the tree, so this can't be used where we
 * need to do in-place replacement.
 */
/*
 * pullup_replace_vars - (中文)在一棵表达式树上应用上提替换
 *
 * 【作用】用 replace_rte_variables 遍历表达式,把引用 context->varno 的
 * level-0 Var 交给 pullup_replace_vars_callback 替换。返回修改后的新副本
 * (不改原树)。
 *
 * 【设计思想】replace_rte_variables 是通用的"替换指定 RTE 的 Var"工具,本
 * 函数只是把 varno、回调、上下文与"是否同步更新 hasSubLinks"参数准备好。
 *
 * 【参数】
 *   expr    —— 待替换的表达式(可为 NULL);
 *   context —— 替换上下文。
 * 【返回值】替换后的表达式副本。
 */
static Node *
pullup_replace_vars(Node *expr, pullup_replace_vars_context *context)
{
	return replace_rte_variables(expr,
								 context->varno, 0,
								 pullup_replace_vars_callback,
								 context,
								 context->outer_hasSubLinks);
}

/*
 * pullup_replace_vars_callback - (中文)单次 Var 替换的回调:生成替换表达式,
 * 必要时包 PlaceHolderVar 并传播 nullingrels
 *
 * 【作用】replace_rte_variables 对每个引用被上提子查询的 Var 调用本回调。
 * 处理步骤:(1) 系统列(varattno < 0)不替换,直接复制;(2) 依据
 * var->varnullingrels 非空或 wrap_option 决定是否需要 PHV;(3) 从 rv_cache
 * 取缓存或调用 ReplaceVarFromTargetList 生成替换表达式;(4) 需要 PHV 时按
 * wrap_option 与表达式结构决定是否包 PHV(简单 Var / 同层 Var / 同可空性
 * 子树的表达式可免包,并把缓存写入 rv_cache);(5) 把 var 的 varnullingrels
 * 合并进替换表达式(Var/PHV 直接加,复杂表达式用 add_nulling_relids 逐项
 * 处理,LATERAL 引用只加实际可能作用的 nullingrels);(6) 若原 Var 在更深
 * 子查询里(varlevelsup > 0),把替换表达式的相应引用上调。
 *
 * 【设计思想】
 * - PHV 的意义:某些被上提的输出在外连接之下求值,上提后仍须在正确的
 *   可空位置求值,包一层 PlaceHolderVar 即"该表达式必须在 phrels 位置之上
 *   求值"的标记;需要时可缓存,保证同一输出只产生一个 PHV(避免重复求值,
 *   保证 equal() 可识别);
 * - 免包规则:简单 Var 与 PHV 直接透传(仅调整 nullingrels);复杂表达式若
 *   只含"子查询自身的 Var/PHV 或与其同可空侧的关系",且无非严格构造,则
 *   可免包(把 nullingrels 直接加进去),这是优化:避免无谓的 PHV 层,外连接
 *   简化后往往能消除这些 nullingrels;
 * - nullingrels 传播必须精确:LATERAL 引用只加"它实际经过的外连接"的
 *   relid,而子查询自身的 Var 加全部;若传播遗漏会误判行可空性,导致错误
 *   计划。
 *
 * 【参数】
 *   var     —— 被替换的 Var;
 *   context —— replace_rte_variables 的上下文(其 callback_arg 指向
 *              pullup_replace_vars_context)。
 * 【返回值】替换后的表达式。
 */
static Node *
pullup_replace_vars_callback(const Var *var,
							 replace_rte_variables_context *context)
{
	pullup_replace_vars_context *rcon = (pullup_replace_vars_context *) context->callback_arg;
	int			varattno = var->varattno;
	bool		need_phv;
	Node	   *newnode;

	/* System columns are not replaced. */
	if (varattno < InvalidAttrNumber)
		return (Node *) copyObject(var);

	/*
	 * We need a PlaceHolderVar if the Var-to-be-replaced has nonempty
	 * varnullingrels (unless we find below that the replacement expression is
	 * a Var or PlaceHolderVar that we can just add the nullingrels to).  We
	 * also need one if the caller has instructed us that certain expression
	 * replacements need to be wrapped for identification purposes.
	 */
	need_phv = (var->varnullingrels != NULL) ||
		(rcon->wrap_option != REPLACE_WRAP_NONE);

	/*
	 * If PlaceHolderVars are needed, we cache the modified expressions in
	 * rcon->rv_cache[].  This is not in hopes of any material speed gain
	 * within this function, but to avoid generating identical PHVs with
	 * different IDs.  That would result in duplicate evaluations at runtime,
	 * and possibly prevent optimizations that rely on recognizing different
	 * references to the same subquery output as being equal().  So it's worth
	 * a bit of extra effort to avoid it.
	 *
	 * The cached items have phlevelsup = 0 and phnullingrels = NULL; we'll
	 * copy them and adjust those values for this reference site below.
	 */
	if (need_phv &&
		varattno >= InvalidAttrNumber &&
		varattno <= list_length(rcon->targetlist) &&
		rcon->rv_cache[varattno] != NULL)
	{
		/* Just copy the entry and fall through to adjust phlevelsup etc */
		newnode = copyObject(rcon->rv_cache[varattno]);
	}
	else
	{
		/*
		 * Generate the replacement expression.  This takes care of expanding
		 * wholerow references and dealing with non-default varreturningtype.
		 */
		newnode = ReplaceVarFromTargetList(var,
										   rcon->target_rte,
										   rcon->targetlist,
										   rcon->result_relation,
										   REPLACEVARS_REPORT_ERROR,
										   0);

		/* Insert PlaceHolderVar if needed */
		if (need_phv)
		{
			bool		wrap;

			if (rcon->wrap_option == REPLACE_WRAP_ALL)
			{
				/* Caller told us to wrap all expressions in a PlaceHolderVar */
				wrap = true;
			}
			else if (varattno == InvalidAttrNumber)
			{
				/*
				 * Insert PlaceHolderVar for whole-tuple reference.  Notice
				 * that we are wrapping one PlaceHolderVar around the whole
				 * RowExpr, rather than putting one around each element of the
				 * row.  This is because we need the expression to yield NULL,
				 * not ROW(NULL,NULL,...) when it is forced to null by an
				 * outer join.
				 */
				wrap = true;
			}
			else if (newnode && IsA(newnode, Var) &&
					 ((Var *) newnode)->varlevelsup == 0)
			{
				/*
				 * Simple Vars always escape being wrapped, unless they are
				 * lateral references to something outside the subquery being
				 * pulled up and the referenced rel is not under the same
				 * lowest nulling outer join.
				 */
				wrap = false;
				if (rcon->target_rte->lateral &&
					!bms_is_member(((Var *) newnode)->varno, rcon->relids))
				{
					nullingrel_info *nullinfo = rcon->nullinfo;
					int			lvarno = ((Var *) newnode)->varno;

					Assert(lvarno > 0 && lvarno <= nullinfo->rtlength);
					if (!bms_is_subset(nullinfo->nullingrels[rcon->varno],
									   nullinfo->nullingrels[lvarno]))
						wrap = true;
				}
			}
			else if (newnode && IsA(newnode, PlaceHolderVar) &&
					 ((PlaceHolderVar *) newnode)->phlevelsup == 0)
			{
				/* The same rules apply for a PlaceHolderVar */
				wrap = false;
				if (rcon->target_rte->lateral &&
					!bms_is_subset(((PlaceHolderVar *) newnode)->phrels,
								   rcon->relids))
				{
					nullingrel_info *nullinfo = rcon->nullinfo;
					Relids		lvarnos = ((PlaceHolderVar *) newnode)->phrels;
					int			lvarno;

					lvarno = -1;
					while ((lvarno = bms_next_member(lvarnos, lvarno)) >= 0)
					{
						Assert(lvarno > 0 && lvarno <= nullinfo->rtlength);
						if (!bms_is_subset(nullinfo->nullingrels[rcon->varno],
										   nullinfo->nullingrels[lvarno]))
						{
							wrap = true;
							break;
						}
					}
				}
			}
			else
			{
				/*
				 * If the node contains Var(s) or PlaceHolderVar(s) of the
				 * subquery being pulled up, or of rels that are under the
				 * same lowest nulling outer join as the subquery, and does
				 * not contain any non-strict constructs, then instead of
				 * adding a PHV on top we can add the required nullingrels to
				 * those Vars/PHVs.  (This is fundamentally a generalization
				 * of the above cases for bare Vars and PHVs.)
				 *
				 * This test is somewhat expensive, but it avoids pessimizing
				 * the plan in cases where the nullingrels get removed again
				 * later by outer join reduction.
				 *
				 * Note that we don't force wrapping of expressions containing
				 * lateral references, so long as they also contain Vars/PHVs
				 * of the subquery, or of rels that are under the same lowest
				 * nulling outer join as the subquery.  This is okay because
				 * of the restriction to strict constructs: if those Vars/PHVs
				 * have been forced to NULL by an outer join then the end
				 * result of the expression will be NULL too, regardless of
				 * the lateral references.  So it's not necessary to force the
				 * expression to be evaluated below the outer join.  This can
				 * be a very valuable optimization, because it may allow us to
				 * avoid using a nested loop to pass the lateral reference
				 * down.
				 *
				 * This analysis could be tighter: in particular, a non-strict
				 * construct hidden within a lower-level PlaceHolderVar is not
				 * reason to add another PHV.  But for now it doesn't seem
				 * worth the code to be more exact.  This is also why it's
				 * preferable to handle bare PHVs in the above branch, rather
				 * than this branch.  We also prefer to handle bare Vars in a
				 * separate branch, as it's cheaper this way and parallels the
				 * handling of PHVs.
				 *
				 * For a LATERAL subquery, we have to check the actual var
				 * membership of the node, but if it's non-lateral then any
				 * level-zero var must belong to the subquery.
				 */
				bool		contain_nullable_vars = false;

				if (!rcon->target_rte->lateral)
				{
					if (contain_vars_of_level(newnode, 0))
						contain_nullable_vars = true;
				}
				else
				{
					Relids		all_varnos;

					all_varnos = pull_varnos(rcon->root, newnode);
					if (bms_overlap(all_varnos, rcon->relids))
						contain_nullable_vars = true;
					else
					{
						nullingrel_info *nullinfo = rcon->nullinfo;
						int			varno;

						varno = -1;
						while ((varno = bms_next_member(all_varnos, varno)) >= 0)
						{
							Assert(varno > 0 && varno <= nullinfo->rtlength);
							if (bms_is_subset(nullinfo->nullingrels[rcon->varno],
											  nullinfo->nullingrels[varno]))
							{
								contain_nullable_vars = true;
								break;
							}
						}
					}
				}

				if (contain_nullable_vars &&
					!contain_nonstrict_functions(newnode))
				{
					/* No wrap needed */
					wrap = false;
				}
				else
				{
					/* Else wrap it in a PlaceHolderVar */
					wrap = true;
				}
			}

			if (wrap)
			{
				newnode = (Node *)
					make_placeholder_expr(rcon->root,
										  (Expr *) newnode,
										  bms_make_singleton(rcon->varno));

				/*
				 * Cache it if possible (ie, if the attno is in range, which
				 * it probably always should be).
				 */
				if (varattno >= InvalidAttrNumber &&
					varattno <= list_length(rcon->targetlist))
					rcon->rv_cache[varattno] = copyObject(newnode);
			}
		}
	}

	/* Propagate any varnullingrels into the replacement expression */
	if (var->varnullingrels != NULL)
	{
		if (IsA(newnode, Var))
		{
			Var		   *newvar = (Var *) newnode;

			Assert(newvar->varlevelsup == 0);
			newvar->varnullingrels = bms_add_members(newvar->varnullingrels,
													 var->varnullingrels);
		}
		else if (IsA(newnode, PlaceHolderVar))
		{
			PlaceHolderVar *newphv = (PlaceHolderVar *) newnode;

			Assert(newphv->phlevelsup == 0);
			newphv->phnullingrels = bms_add_members(newphv->phnullingrels,
													var->varnullingrels);
		}
		else
		{
			/*
			 * There should be Vars/PHVs within the expression that we can
			 * modify.  Vars/PHVs of the subquery should have the full
			 * var->varnullingrels added to them, but if there are lateral
			 * references within the expression, those must be marked with
			 * only the nullingrels that potentially apply to them.  (This
			 * corresponds to the fact that the expression will now be
			 * evaluated at the join level of the Var that we are replacing:
			 * the lateral references may have bubbled up through fewer outer
			 * joins than the subquery's Vars have.  Per the discussion above,
			 * we'll still get the right answers.)  That relid set could be
			 * different for different lateral relations, so we have to do
			 * this work for each one.
			 *
			 * (Currently, the restrictions in is_simple_subquery() mean that
			 * at most we have to remove the lowest outer join's relid from
			 * the nullingrels of a lateral reference.  However, we might
			 * relax those restrictions someday, so let's do this right.)
			 */
			if (rcon->target_rte->lateral)
			{
				nullingrel_info *nullinfo = rcon->nullinfo;
				Relids		lvarnos;
				int			lvarno;

				/*
				 * Identify lateral varnos used within newnode.  We must do
				 * this before injecting var->varnullingrels into the tree.
				 */
				lvarnos = pull_varnos(rcon->root, newnode);
				lvarnos = bms_del_members(lvarnos, rcon->relids);
				/* For each one, add relevant nullingrels if any */
				lvarno = -1;
				while ((lvarno = bms_next_member(lvarnos, lvarno)) >= 0)
				{
					Relids		lnullingrels;

					Assert(lvarno > 0 && lvarno <= nullinfo->rtlength);
					lnullingrels = bms_intersect(var->varnullingrels,
												 nullinfo->nullingrels[lvarno]);
					if (!bms_is_empty(lnullingrels))
						newnode = add_nulling_relids(newnode,
													 bms_make_singleton(lvarno),
													 lnullingrels);
				}
			}

			/* Finally, deal with Vars/PHVs of the subquery itself */
			newnode = add_nulling_relids(newnode,
										 rcon->relids,
										 var->varnullingrels);
			/* Assert we did put the varnullingrels into the expression */
			Assert(bms_is_subset(var->varnullingrels,
								 pull_varnos(rcon->root, newnode)));
		}
	}

	/* Must adjust varlevelsup if replaced Var is within a subquery */
	if (var->varlevelsup > 0)
		IncrementVarSublevelsUp(newnode, var->varlevelsup, 0);

	return newnode;
}

/*
 * Apply pullup variable replacement to a subquery
 *
 * This needs to be different from pullup_replace_vars() because
 * replace_rte_variables will think that it shouldn't increment sublevels_up
 * before entering the Query; so we need to call it with sublevels_up == 1.
 */
/*
 * pullup_replace_vars_subquery - (中文)对子查询做上提替换(用于 LATERAL
 * 引用被上提子查询的情形)
 *
 * 【作用】与 pullup_replace_vars 基本相同,但以 sublevels_up == 1 调用
 * replace_rte_variables:因为 replace_rte_variables 在进入 Query 之前不会
 * 自行递增嵌套层数,而这里要替换的是"当前子查询内部引用外层 varno 的
 * Var",必须先算作 level 1。
 *
 * 【设计思想】LATERAL 关系的表达式里可能直接引用被上提的子查询输出,因此
 * 必须用带嵌套层数的变体深入其 Query 内部做替换。
 *
 * 【参数】
 *   query   —— 待处理的子查询;
 *   context —— 替换上下文。
 * 【返回值】替换后的子查询副本。
 */
static Query *
pullup_replace_vars_subquery(Query *query,
							 pullup_replace_vars_context *context)
{
	Assert(IsA(query, Query));
	return (Query *) replace_rte_variables((Node *) query,
										   context->varno, 1,
										   pullup_replace_vars_callback,
										   context,
										   NULL);
}


/*
 * flatten_simple_union_all
 *		Try to optimize top-level UNION ALL structure into an appendrel
 *
 * If a query's setOperations tree consists entirely of simple UNION ALL
 * operations, flatten it into an append relation, which we can process more
 * intelligently than the general setops case.  Otherwise, do nothing.
 *
 * In most cases, this can succeed only for a top-level query, because for a
 * subquery in FROM, the parent query's invocation of pull_up_subqueries would
 * already have flattened the UNION via pull_up_simple_union_all.  But there
 * are a few cases we can support here but not in that code path, for example
 * when the subquery also contains ORDER BY.
 */
/*
 * flatten_simple_union_all - (中文)把顶层纯 UNION ALL 展平成 append 关系
 *
 * 【作用】对顶层查询的 setOperations 树,若其全部为类型一致的 UNION ALL
 * (is_simple_union_all_recurse)且非递归 UNION,则:复制最左叶子 RTE 作为
 * append 关系的子副本(原 RTE 改标 inh 作为父),setop 树改指该副本,在
 * jointree 中插入引用父 RTE 的 RangeTblRef,清空 setOperations,最后用
 * pull_up_union_leaf_queries 为各叶子建 AppendRelInfo 并上提它们。
 *
 * 【设计思想】与 pull_up_simple_union_all 处理"FROM 中的 UNION 子查询"不同,
 * 这里是顶层 UNION,支持后者不支持的情形(如子查询含 ORDER BY)。必须复制
 * 最左叶子 RTE 作为成员,是因为父查询的 Var 全部指向"整个 append 关系"
 * (最左 RTE),而树上的最左叶子又必须有一个具体成员。
 *
 * 【参数】root —— PlannerInfo,其 parse->setOperations 与 jointree 被改写。
 * 【返回值】无。
 */
void
flatten_simple_union_all(PlannerInfo *root)
{
	Query	   *parse = root->parse;
	SetOperationStmt *topop;
	Node	   *leftmostjtnode;
	int			leftmostRTI;
	RangeTblEntry *leftmostRTE;
	int			childRTI;
	RangeTblEntry *childRTE;
	RangeTblRef *rtr;

	/* Shouldn't be called unless query has setops */
	topop = castNode(SetOperationStmt, parse->setOperations);
	Assert(topop);

	/* Can't optimize away a recursive UNION */
	if (root->hasRecursion)
		return;

	/*
	 * Recursively check the tree of set operations.  If not all UNION ALL
	 * with identical column types, punt.
	 */
	if (!is_simple_union_all_recurse((Node *) topop, parse, topop->colTypes))
		return;

	/*
	 * Locate the leftmost leaf query in the setops tree.  The upper query's
	 * Vars all refer to this RTE (see transformSetOperationStmt).
	 */
	leftmostjtnode = topop->larg;
	while (leftmostjtnode && IsA(leftmostjtnode, SetOperationStmt))
		leftmostjtnode = ((SetOperationStmt *) leftmostjtnode)->larg;
	Assert(leftmostjtnode && IsA(leftmostjtnode, RangeTblRef));
	leftmostRTI = ((RangeTblRef *) leftmostjtnode)->rtindex;
	leftmostRTE = rt_fetch(leftmostRTI, parse->rtable);
	Assert(leftmostRTE->rtekind == RTE_SUBQUERY);

	/*
	 * Make a copy of the leftmost RTE and add it to the rtable.  This copy
	 * will represent the leftmost leaf query in its capacity as a member of
	 * the appendrel.  The original will represent the appendrel as a whole.
	 * (We must do things this way because the upper query's Vars have to be
	 * seen as referring to the whole appendrel.)
	 */
	childRTE = copyObject(leftmostRTE);
	parse->rtable = lappend(parse->rtable, childRTE);
	childRTI = list_length(parse->rtable);

	/* Modify the setops tree to reference the child copy */
	((RangeTblRef *) leftmostjtnode)->rtindex = childRTI;

	/* Modify the formerly-leftmost RTE to mark it as an appendrel parent */
	leftmostRTE->inh = true;

	/*
	 * Form a RangeTblRef for the appendrel, and insert it into FROM.  The top
	 * Query of a setops tree should have had an empty FromClause initially.
	 */
	rtr = makeNode(RangeTblRef);
	rtr->rtindex = leftmostRTI;
	Assert(parse->jointree->fromlist == NIL);
	parse->jointree->fromlist = list_make1(rtr);

	/*
	 * Now pretend the query has no setops.  We must do this before trying to
	 * do subquery pullup, because of Assert in pull_up_simple_subquery.
	 */
	parse->setOperations = NULL;

	/*
	 * Build AppendRelInfo information, and apply pull_up_subqueries to the
	 * leaf queries of the UNION ALL.  (We must do that now because they
	 * weren't previously referenced by the jointree, and so were missed by
	 * the main invocation of pull_up_subqueries.)
	 */
	pull_up_union_leaf_queries((Node *) topop, root, leftmostRTI, parse, 0);
}


/*
 * reduce_outer_joins
 *		Attempt to reduce outer joins to plain inner joins.
 *
 * The idea here is that given a query like
 *		SELECT ... FROM a LEFT JOIN b ON (...) WHERE b.y = 42;
 * we can reduce the LEFT JOIN to a plain JOIN if the "=" operator in WHERE
 * is strict.  The strict operator will always return NULL, causing the outer
 * WHERE to fail, on any row where the LEFT JOIN filled in NULLs for b's
 * columns.  Therefore, there's no need for the join to produce null-extended
 * rows in the first place --- which makes it a plain join not an outer join.
 * (This scenario may not be very likely in a query written out by hand, but
 * it's reasonably likely when pushing quals down into complex views.)
 *
 * More generally, an outer join can be reduced in strength if there is a
 * strict qual above it in the qual tree that constrains a Var from the
 * nullable side of the join to be non-null.  (For FULL joins this applies
 * to each side separately.)
 *
 * Another transformation we apply here is to recognize cases like
 *		SELECT ... FROM a LEFT JOIN b ON (a.x = b.y) WHERE b.z IS NULL;
 * If we can prove that b.z must be non-null for any matching row, either
 * because the join clause is strict for b.z and b.z happens to be the join
 * key b.y, or because b.z is defined NOT NULL by table constraints and is
 * not nullable due to lower-level outer joins, then only null-extended rows
 * could pass the upper WHERE, and we can conclude that what the query is
 * really specifying is an anti-semijoin.  We change the join type from
 * JOIN_LEFT to JOIN_ANTI.  The IS NULL clause then becomes redundant, and
 * must be removed to prevent bogus selectivity calculations, but we leave
 * it to distribute_qual_to_rels to get rid of such clauses.
 *
 * Also, we get rid of JOIN_RIGHT cases by flipping them around to become
 * JOIN_LEFT.  This saves some code here and in some later planner routines;
 * the main benefit is to reduce the number of jointypes that can appear in
 * SpecialJoinInfo nodes.  Note that we can still generate Paths and Plans
 * that use JOIN_RIGHT (or JOIN_RIGHT_ANTI) by switching the inputs again.
 *
 * To ease recognition of strict qual clauses, we require this routine to be
 * run after expression preprocessing (i.e., qual canonicalization and JOIN
 * alias-var expansion).
 */
/*
 * reduce_outer_joins - (中文)尝试把外连接降级为内连接 / 反连接
 *
 * 【作用】对外连接简化的总入口,运行在表达式预处理(qual 规范化、连接别名
 * 展开)之后。两遍扫描:pass1 自底向上收集每棵子树的关系集合、是否含外连
 * 接、可空侧关系集合;pass2 自顶向下携带"上层强制非空关系(nonnullable_rels)"
 * 与"上层强制 NULL 的 Var(forced_null_vars)"逐节点判定并改写连接类型。
 * 判定的规则:LEFT 的右侧被强制非空→INNER;FULL 的某一侧被强制非空→LEFT/
 * RIGHT(部分降级),两侧都→INNER;LEFT 的右侧有"被强制 NULL 且已知非空"
 * 的 Var→ANTI;RIGHT 一律翻转为 LEFT。最后对降级过的连接,调用
 * remove_nulling_relids 清理其作为 nulling rel 的引用(部分降级的 FULL
 * 逐个处理)。
 *
 * 【设计思想】
 * - 例:WHERE b.y = 42 中 '=' 严格,LEFT JOIN 填充的 NULL 行必被滤掉,故
 *   无需生成空扩展行,LEFT 等价 INNER;
 * - 例:WHERE b.z IS NULL 且 b.z 必非空(连接条件严格或列有 NOT NULL 约束),
 *   则只有"未匹配而被空扩展"的行才通过,即反连接;
 * - 强制 NULL 判定结合连接自身的严格性与表 NOT NULL 约束,还须排除下层
 *   外连接可能置空的列;
 * - 全量降级合并一次清理 nullingrels;部分降级(FULL→LEFT)因 except_relids
 *   不同须逐个清理。planner.c 只在查询确实含外连接时才调用本函数。
 *
 * 【参数】root —— PlannerInfo,其 parse / append_rel_list 被就地改写。
 * 【返回值】无。
 */
void
reduce_outer_joins(PlannerInfo *root)
{
	reduce_outer_joins_pass1_state *state1;
	reduce_outer_joins_pass2_state state2;
	ListCell   *lc;

	/*
	 * To avoid doing strictness checks on more quals than necessary, we want
	 * to stop descending the jointree as soon as there are no outer joins
	 * below our current point.  This consideration forces a two-pass process.
	 * The first pass gathers information about which base rels appear below
	 * each side of each join clause, about whether there are outer join(s)
	 * below each side of each join clause, and about which base rels are from
	 * the nullable side of those outer join(s).  The second pass examines
	 * qual clauses and changes join types as it descends the tree.
	 */
	state1 = reduce_outer_joins_pass1((Node *) root->parse->jointree);

	/* planner.c shouldn't have called me if no outer joins */
	if (state1 == NULL || !state1->contains_outer)
		elog(ERROR, "so where are the outer joins?");

	state2.inner_reduced = NULL;
	state2.partial_reduced = NIL;

	reduce_outer_joins_pass2((Node *) root->parse->jointree,
							 state1, &state2,
							 root, NULL, NIL);

	/*
	 * If we successfully reduced the strength of any outer joins, we must
	 * remove references to those joins as nulling rels.  This is handled as
	 * an additional pass, for simplicity and because we can handle all
	 * fully-reduced joins in a single pass over the parse tree.
	 */
	if (!bms_is_empty(state2.inner_reduced))
	{
		root->parse = (Query *)
			remove_nulling_relids((Node *) root->parse,
								  state2.inner_reduced,
								  NULL);
		/* There could be references in the append_rel_list, too */
		root->append_rel_list = (List *)
			remove_nulling_relids((Node *) root->append_rel_list,
								  state2.inner_reduced,
								  NULL);
	}

	/*
	 * Partially-reduced full joins have to be done one at a time, since
	 * they'll each need a different setting of except_relids.
	 */
	foreach(lc, state2.partial_reduced)
	{
		reduce_outer_joins_partial_state *statep = lfirst(lc);
		Relids		full_join_relids = bms_make_singleton(statep->full_join_rti);

		root->parse = (Query *)
			remove_nulling_relids((Node *) root->parse,
								  full_join_relids,
								  statep->unreduced_side);
		root->append_rel_list = (List *)
			remove_nulling_relids((Node *) root->append_rel_list,
								  full_join_relids,
								  statep->unreduced_side);
	}
}

/*
 * reduce_outer_joins_pass1 - phase 1 data collection
 *
 * Returns a state node describing the given jointree node.
 */
/*
 * reduce_outer_joins_pass1 - (中文)外连接简化的第一遍:收集子树信息
 *
 * 【作用】自底向上遍历连接树,为每个节点返回 reduce_outer_joins_pass1_state,
 * 记录:该子树包含的基关系集合(relids)、是否含有外连接(contains_outer)、
 * 该子树内被外连接潜在置空的关系集合(nullable_rels)、以及各子节点状态
 * (sub_states,FromExpr 下是各子节点列表,JoinExpr 下是左右两态)。
 *
 * 【设计思想】
 * - JOIN_INNER / JOIN_SEMI 不引入新的可空性,直接并集传播子状态;
 *   JOIN_LEFT / JOIN_ANTI 右可空;JOIN_RIGHT 左可空;JOIN_FULL 两侧都可空;
 * - 该信息供 pass2 判断"某连接是否可能被上层条件降级"以及"强制 NULL 判定
 *   时排除下层可空列"。join 自身的 RT 索引不计入 relids(基关系才计入)。
 *
 * 【参数】jtnode —— 当前连接树节点。
 * 【返回值】描述该子树的状态节点。
 */
static reduce_outer_joins_pass1_state *
reduce_outer_joins_pass1(Node *jtnode)
{
	reduce_outer_joins_pass1_state *result;

	result = palloc_object(reduce_outer_joins_pass1_state);
	result->relids = NULL;
	result->contains_outer = false;
	result->nullable_rels = NULL;
	result->sub_states = NIL;

	if (jtnode == NULL)
		return result;
	if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		result->relids = bms_make_singleton(varno);
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		foreach(l, f->fromlist)
		{
			reduce_outer_joins_pass1_state *sub_state;

			sub_state = reduce_outer_joins_pass1(lfirst(l));
			result->relids = bms_add_members(result->relids,
											 sub_state->relids);
			result->contains_outer |= sub_state->contains_outer;
			result->nullable_rels = bms_add_members(result->nullable_rels,
													sub_state->nullable_rels);
			result->sub_states = lappend(result->sub_states, sub_state);
		}
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;
		reduce_outer_joins_pass1_state *left_state;
		reduce_outer_joins_pass1_state *right_state;

		/* Recurse to children */
		left_state = reduce_outer_joins_pass1(j->larg);
		right_state = reduce_outer_joins_pass1(j->rarg);

		/* join's own RT index is not wanted in result->relids */
		result->relids = bms_union(left_state->relids, right_state->relids);

		/* Store children's states for pass 2 */
		result->sub_states = list_make2(left_state, right_state);

		/* Collect outer join information */
		switch (j->jointype)
		{
			case JOIN_INNER:
			case JOIN_SEMI:
				/* No new nullability; propagate state from children */
				result->contains_outer = left_state->contains_outer ||
					right_state->contains_outer;
				result->nullable_rels = bms_union(left_state->nullable_rels,
												  right_state->nullable_rels);
				break;
			case JOIN_LEFT:
			case JOIN_ANTI:
				/* RHS is nullable; LHS keeps existing status */
				result->contains_outer = true;
				result->nullable_rels = bms_union(left_state->nullable_rels,
												  right_state->relids);
				break;
			case JOIN_RIGHT:
				/* LHS is nullable; RHS keeps existing status */
				result->contains_outer = true;
				result->nullable_rels = bms_union(left_state->relids,
												  right_state->nullable_rels);
				break;
			case JOIN_FULL:
				/* Both sides are nullable */
				result->contains_outer = true;
				result->nullable_rels = bms_union(left_state->relids,
												  right_state->relids);
				break;
			default:
				elog(ERROR, "unrecognized join type: %d",
					 (int) j->jointype);
				break;
		}
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
	return result;
}

/*
 * reduce_outer_joins_pass2 - phase 2 processing
 *
 *	jtnode: current jointree node
 *	state1: state data collected by phase 1 for this node
 *	state2: where to accumulate info about successfully-reduced joins
 *	root: toplevel planner state
 *	nonnullable_rels: set of base relids forced non-null by upper quals
 *	forced_null_vars: multibitmapset of Vars forced null by upper quals
 *
 * Returns info in state2 about outer joins that were successfully simplified.
 * Joins that were fully reduced to inner joins are all added to
 * state2->inner_reduced.  If a full join is reduced to a left join,
 * it needs its own entry in state2->partial_reduced, since that will
 * require custom processing to remove only the correct nullingrel markers.
 */
/*
 * reduce_outer_joins_pass2 - (中文)外连接简化的第二遍:按上层约束改写连接
 * 类型
 *
 * 【作用】自顶向下处理连接树。FromExpr:从自身 quals 提取"强制非空关系"
 * (find_nonnullable_rels)与"强制 NULL 的 Var"(find_forced_null_vars),并入
 * 上层传入的集合后只对 contains_outer 的子树递归。JoinExpr:按连接类型判
 * 定能否降级(见 reduce_outer_joins 的设计思想);RIGHT 翻转为 LEFT;LEFT 且
 * 右侧有"强制 NULL 且必非空"的 Var 时降为 ANTI;连接类型改变时同步修改
 * 对应 RTE_JOIN 的 jointype,全降为 INNER 的连接 rtindex 记入
 * state2->inner_reduced;随后决定向左右子树传递何种约束(INNER/SEMI 传递
 * 本地+上层;LEFT/ANTI 的非可空侧传上层、可空侧传本地;FULL 不传),递归
 * 处理仍含外连接的子树。
 *
 * 【设计思想】
 * - 对 LEFT 连接,上层的非空约束不能向可空侧传(否则会错误地判定下层可降
 *   级),但可传给自己不可空侧;强制 NULL 约束更不能传进可空侧;
 * - SEMI 视同 INNER 处理(其右侧不可能被上层条件引用);
 * - 约束合并只在"本连接已降为内连接"时发生,否则上层约束对可空侧的推导
 *   无意义。
 *
 * 【参数】
 *   jtnode             —— 当前节点;
 *   state1             —— pass1 收集的本节点状态;
 *   state2             —— 汇总已成功降级连接的信息(inner_reduced /
 *                         partial_reduced);
 *   root               —— PlannerInfo;
 *   nonnullable_rels   —— 上层迫使非空的关系集合;
 *   forced_null_vars   —— 上层迫使为 NULL 的 Var 集合(多级位图集)。
 * 【返回值】无(结果写入 state2 与连接树/RTE)。
 */
static void
reduce_outer_joins_pass2(Node *jtnode,
						 reduce_outer_joins_pass1_state *state1,
						 reduce_outer_joins_pass2_state *state2,
						 PlannerInfo *root,
						 Relids nonnullable_rels,
						 List *forced_null_vars)
{
	/*
	 * pass 2 should never descend as far as an empty subnode or base rel,
	 * because it's only called on subtrees marked as contains_outer.
	 */
	if (jtnode == NULL)
		elog(ERROR, "reached empty jointree");
	if (IsA(jtnode, RangeTblRef))
		elog(ERROR, "reached base rel");
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;
		ListCell   *s;
		Relids		pass_nonnullable_rels;
		List	   *pass_forced_null_vars;

		/* Scan quals to see if we can add any constraints */
		pass_nonnullable_rels = find_nonnullable_rels(f->quals);
		pass_nonnullable_rels = bms_add_members(pass_nonnullable_rels,
												nonnullable_rels);
		pass_forced_null_vars = find_forced_null_vars(f->quals);
		pass_forced_null_vars = mbms_add_members(pass_forced_null_vars,
												 forced_null_vars);
		/* And recurse --- but only into interesting subtrees */
		Assert(list_length(f->fromlist) == list_length(state1->sub_states));
		forboth(l, f->fromlist, s, state1->sub_states)
		{
			reduce_outer_joins_pass1_state *sub_state = lfirst(s);

			if (sub_state->contains_outer)
				reduce_outer_joins_pass2(lfirst(l), sub_state,
										 state2, root,
										 pass_nonnullable_rels,
										 pass_forced_null_vars);
		}
		bms_free(pass_nonnullable_rels);
		/* can't so easily clean up var lists, unfortunately */
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;
		int			rtindex = j->rtindex;
		JoinType	jointype = j->jointype;
		reduce_outer_joins_pass1_state *left_state = linitial(state1->sub_states);
		reduce_outer_joins_pass1_state *right_state = lsecond(state1->sub_states);

		/* Can we simplify this join? */
		switch (jointype)
		{
			case JOIN_INNER:
				break;
			case JOIN_LEFT:
				if (bms_overlap(nonnullable_rels, right_state->relids))
					jointype = JOIN_INNER;
				break;
			case JOIN_RIGHT:
				if (bms_overlap(nonnullable_rels, left_state->relids))
					jointype = JOIN_INNER;
				break;
			case JOIN_FULL:
				if (bms_overlap(nonnullable_rels, left_state->relids))
				{
					if (bms_overlap(nonnullable_rels, right_state->relids))
						jointype = JOIN_INNER;
					else
					{
						jointype = JOIN_LEFT;
						/* Also report partial reduction in state2 */
						report_reduced_full_join(state2, rtindex,
												 right_state->relids);
					}
				}
				else
				{
					if (bms_overlap(nonnullable_rels, right_state->relids))
					{
						jointype = JOIN_RIGHT;
						/* Also report partial reduction in state2 */
						report_reduced_full_join(state2, rtindex,
												 left_state->relids);
					}
				}
				break;
			case JOIN_SEMI:
			case JOIN_ANTI:

				/*
				 * These could only have been introduced by pull_up_sublinks,
				 * so there's no way that upper quals could refer to their
				 * righthand sides, and no point in checking.  We don't expect
				 * to see JOIN_RIGHT_SEMI or JOIN_RIGHT_ANTI yet.
				 */
				break;
			default:
				elog(ERROR, "unrecognized join type: %d",
					 (int) jointype);
				break;
		}

		/*
		 * Convert JOIN_RIGHT to JOIN_LEFT.  Note that in the case where we
		 * reduced JOIN_FULL to JOIN_RIGHT, this will mean the JoinExpr no
		 * longer matches the internal ordering of any CoalesceExpr's built to
		 * represent merged join variables.  We don't care about that at
		 * present, but be wary of it ...
		 */
		if (jointype == JOIN_RIGHT)
		{
			Node	   *tmparg;

			tmparg = j->larg;
			j->larg = j->rarg;
			j->rarg = tmparg;
			jointype = JOIN_LEFT;
			right_state = linitial(state1->sub_states);
			left_state = lsecond(state1->sub_states);
		}

		/*
		 * See if we can reduce JOIN_LEFT to JOIN_ANTI.  This is the case if
		 * any var from the RHS was forced null by higher qual levels, but is
		 * known to be non-nullable.  We detect this either by seeing if the
		 * join's own quals are strict for the var, or by checking if the var
		 * is defined NOT NULL by table constraints (being careful to exclude
		 * vars that are nullable due to lower-level outer joins).  In either
		 * case, the only way the higher qual clause's requirement for NULL
		 * can be met is if the join fails to match, producing a null-extended
		 * row.  Thus, we can treat this as an anti-join.
		 */
		if (jointype == JOIN_LEFT && forced_null_vars != NIL)
		{
			List	   *nonnullable_vars;
			Bitmapset  *overlap;

			/* Find Vars in j->quals that must be non-null in joined rows */
			nonnullable_vars = find_nonnullable_vars(j->quals);

			/*
			 * It's not sufficient to check whether nonnullable_vars and
			 * forced_null_vars overlap: we need to know if the overlap
			 * includes any RHS variables.
			 *
			 * Also check if any forced-null var is defined NOT NULL by table
			 * constraints.
			 */
			overlap = mbms_overlap_sets(nonnullable_vars, forced_null_vars);
			if (bms_overlap(overlap, right_state->relids) ||
				has_notnull_forced_var(root, forced_null_vars, right_state))
				jointype = JOIN_ANTI;
		}

		/*
		 * Apply the jointype change, if any, to both jointree node and RTE.
		 * Also, if we changed an RTE to INNER, add its RTI to inner_reduced.
		 */
		if (rtindex && jointype != j->jointype)
		{
			RangeTblEntry *rte = rt_fetch(rtindex, root->parse->rtable);

			Assert(rte->rtekind == RTE_JOIN);
			Assert(rte->jointype == j->jointype);
			rte->jointype = jointype;
			if (jointype == JOIN_INNER)
				state2->inner_reduced = bms_add_member(state2->inner_reduced,
													   rtindex);
		}
		j->jointype = jointype;

		/* Only recurse if there's more to do below here */
		if (left_state->contains_outer || right_state->contains_outer)
		{
			Relids		local_nonnullable_rels;
			List	   *local_forced_null_vars;
			Relids		pass_nonnullable_rels;
			List	   *pass_forced_null_vars;

			/*
			 * If this join is (now) inner, we can add any constraints its
			 * quals provide to those we got from above.  But if it is outer,
			 * we can pass down the local constraints only into the nullable
			 * side, because an outer join never eliminates any rows from its
			 * non-nullable side.  Also, there is no point in passing upper
			 * constraints into the nullable side, since if there were any
			 * we'd have been able to reduce the join.  (In the case of upper
			 * forced-null constraints, we *must not* pass them into the
			 * nullable side --- they either applied here, or not.) The upshot
			 * is that we pass either the local or the upper constraints,
			 * never both, to the children of an outer join.
			 *
			 * Note that a SEMI join works like an inner join here: it's okay
			 * to pass down both local and upper constraints.  (There can't be
			 * any upper constraints affecting its inner side, but it's not
			 * worth having a separate code path to avoid passing them.)
			 *
			 * At a FULL join we just punt and pass nothing down --- is it
			 * possible to be smarter?
			 */
			if (jointype != JOIN_FULL)
			{
				local_nonnullable_rels = find_nonnullable_rels(j->quals);
				local_forced_null_vars = find_forced_null_vars(j->quals);
				if (jointype == JOIN_INNER || jointype == JOIN_SEMI)
				{
					/* OK to merge upper and local constraints */
					local_nonnullable_rels = bms_add_members(local_nonnullable_rels,
															 nonnullable_rels);
					local_forced_null_vars = mbms_add_members(local_forced_null_vars,
															  forced_null_vars);
				}
			}
			else
			{
				/* no use in calculating these */
				local_nonnullable_rels = NULL;
				local_forced_null_vars = NIL;
			}

			if (left_state->contains_outer)
			{
				if (jointype == JOIN_INNER || jointype == JOIN_SEMI)
				{
					/* pass union of local and upper constraints */
					pass_nonnullable_rels = local_nonnullable_rels;
					pass_forced_null_vars = local_forced_null_vars;
				}
				else if (jointype != JOIN_FULL) /* ie, LEFT or ANTI */
				{
					/* can't pass local constraints to non-nullable side */
					pass_nonnullable_rels = nonnullable_rels;
					pass_forced_null_vars = forced_null_vars;
				}
				else
				{
					/* no constraints pass through JOIN_FULL */
					pass_nonnullable_rels = NULL;
					pass_forced_null_vars = NIL;
				}
				reduce_outer_joins_pass2(j->larg, left_state,
										 state2, root,
										 pass_nonnullable_rels,
										 pass_forced_null_vars);
			}

			if (right_state->contains_outer)
			{
				if (jointype != JOIN_FULL)	/* ie, INNER/LEFT/SEMI/ANTI */
				{
					/* pass appropriate constraints, per comment above */
					pass_nonnullable_rels = local_nonnullable_rels;
					pass_forced_null_vars = local_forced_null_vars;
				}
				else
				{
					/* no constraints pass through JOIN_FULL */
					pass_nonnullable_rels = NULL;
					pass_forced_null_vars = NIL;
				}
				reduce_outer_joins_pass2(j->rarg, right_state,
										 state2, root,
										 pass_nonnullable_rels,
										 pass_forced_null_vars);
			}
			bms_free(local_nonnullable_rels);
		}
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
}

/* Helper for reduce_outer_joins_pass2 */
/*
 * report_reduced_full_join - (中文)登记一个被部分降级(变成 LEFT/RIGHT)的
 * FULL 连接
 *
 * 【作用】reduce_outer_joins_pass2 的辅助:把"由 FULL 降级而来的连接的 RT
 * 索引"及其"仍然可空的一侧关系集合"记录进 state2->partial_reduced,供
 * reduce_outer_joins 在收尾时逐个用 remove_nulling_relids 清理。
 *
 * 【设计思想】部分降级的 FULL 连接要删除的 nulling relid 是其 rtindex,但
 * 清理时须保留"仍然可空那一侧"的 nullingrels(except_relids),因此每条要
 * 单独记录,不能像全量降级那样合并成一张位图一次处理。
 *
 * 【参数】
 *   state2  —— 汇总状态;
 *   rtindex —— 被部分降级的连接的 RT 索引;
 *   relids  —— 该连接中"仍然可空"一侧的关系集合。
 * 【返回值】无。
 */
static void
report_reduced_full_join(reduce_outer_joins_pass2_state *state2,
						 int rtindex, Relids relids)
{
	reduce_outer_joins_partial_state *statep;

	statep = palloc_object(reduce_outer_joins_partial_state);
	statep->full_join_rti = rtindex;
	statep->unreduced_side = relids;
	state2->partial_reduced = lappend(state2->partial_reduced, statep);
}

/*
 * has_notnull_forced_var
 *		Check whether any forced-null Vars are for cols of the relations
 *		indicated by "right_state" that are known to be non-nullable due to
 *		table constraints.
 *
 * Note that we must also consider the situation where a NOT NULL Var can be
 * nulled by lower-level outer joins.
 *
 * Helper for reduce_outer_joins_pass2.
 */
/*
 * has_notnull_forced_var - (中文)检查"强制 NULL 的 Var"里是否存在属于给定
 * 子树、且由表约束保证非空的列
 *
 * 【作用】reduce_outer_joins_pass2 的辅助:遍历 forced_null_vars(按 varno
 * 组织、每项是一个属性号位图),对属于 right_state 子树、且不被该子树内
 * 下层外连接置空(nullable_rels)的关系,把位图成员偏移成真实属性号,若关系
 * 是普通表(RTE_RELATION,非继承父表),用 find_relation_notnullatts 查其
 * NOT NULL 约束,任一强制 NULL 属性恰为 NOT NULL 约束列即返回 true。
 *
 * 【设计思想】若某列"被上层强制为 NULL",而它又被约束保证非空,则唯一可能
 * 就是"该连接未匹配而被空扩展"——LEFT 可降级为 ANTI。排除 nullable_rels
 * 是防止下层外连接把本必非空的列置空;跳过继承父表是因为各子表约束可能
 * 不一致(分区表除外);系统列(负属性号)不可能为 NULL,直接命中。
 *
 * 【参数】
 *   root            —— PlannerInfo;
 *   forced_null_vars —— 强制 NULL 的 Var 集合(按 varno 的多级位图列表);
 *   right_state     —— 目标子树状态(提供 relids 与 nullable_rels)。
 * 【返回值】true 表示存在"必非空却被强制 NULL"的列。
 */
static bool
has_notnull_forced_var(PlannerInfo *root, List *forced_null_vars,
					   reduce_outer_joins_pass1_state *right_state)
{
	int			varno = -1;

	foreach_node(Bitmapset, attrs, forced_null_vars)
	{
		RangeTblEntry *rte;
		Bitmapset  *notnullattnums;
		Bitmapset  *forcednullattnums = NULL;
		int			lowest_attno;

		varno++;

		/* Skip empty bitmaps */
		if (bms_is_empty(attrs))
			continue;

		/* Skip Vars that do not belong to the target relations */
		if (!bms_is_member(varno, right_state->relids))
			continue;

		/*
		 * Skip Vars that can be nulled by lower-level outer joins within the
		 * given subtree.  These Vars might be NULL even if the schema defines
		 * them as NOT NULL.
		 */
		if (bms_is_member(varno, right_state->nullable_rels))
			continue;

		/* find the lowest member to check if system columns are present */
		lowest_attno = bms_next_member(attrs, -1);

		/* we checked for an empty set above */
		Assert(lowest_attno >= 0);

		/* system columns cannot be NULL */
		if (lowest_attno + FirstLowInvalidHeapAttributeNumber < 0)
			return true;

		/*
		 * Offset the bitmap members by FirstLowInvalidHeapAttributeNumber to
		 * get the actual attribute numbers.
		 */
		forcednullattnums = bms_offset_members(attrs,
											   FirstLowInvalidHeapAttributeNumber);

		rte = rt_fetch(varno, root->parse->rtable);

		/* We can only reason about ordinary relations */
		if (rte->rtekind != RTE_RELATION)
		{
			bms_free(forcednullattnums);
			continue;
		}

		/*
		 * We must skip inheritance parent tables, as some child tables may
		 * have a NOT NULL constraint for a column while others may not.  This
		 * cannot happen with partitioned tables, though.
		 */
		if (rte->inh && rte->relkind != RELKIND_PARTITIONED_TABLE)
		{
			bms_free(forcednullattnums);
			continue;
		}

		/* Get the column not-null constraint information for this relation */
		notnullattnums = find_relation_notnullatts(root, rte->relid);

		/*
		 * Check if any forced-null attributes are defined as NOT NULL by
		 * table constraints.
		 */
		if (bms_overlap(notnullattnums, forcednullattnums))
		{
			bms_free(forcednullattnums);
			return true;
		}

		bms_free(forcednullattnums);
	}

	return false;
}


/*
 * remove_useless_result_rtes
 *		Attempt to remove RTE_RESULT RTEs from the join tree.
 *		Also, elide single-child FromExprs where possible.
 *
 * We can remove RTE_RESULT entries from the join tree using the knowledge
 * that RTE_RESULT returns exactly one row and has no output columns.  Hence,
 * if one is inner-joined to anything else, we can delete it.  Optimizations
 * are also possible for some outer-join cases, as detailed below.
 *
 * This pass also replaces single-child FromExprs with their child node
 * where possible.  It's appropriate to do that here and not earlier because
 * RTE_RESULT removal might reduce a multiple-child FromExpr to have only one
 * child.  We can remove such a FromExpr if its quals are empty, or if it's
 * semantically valid to merge the quals into those of the parent node.
 * While removing unnecessary join tree nodes has some micro-efficiency value,
 * the real reason to do this is to eliminate cases where the nullable side of
 * an outer join node is a FromExpr whose single child is another outer join.
 * To correctly determine whether the two outer joins can commute,
 * deconstruct_jointree() must treat any quals of such a FromExpr as being
 * degenerate quals of the upper outer join.  The best way to do that is to
 * make them actually *be* quals of the upper join, by dropping the FromExpr
 * and hoisting the quals up into the upper join's quals.  (Note that there is
 * no hazard when the intermediate FromExpr has multiple children, since then
 * it represents an inner join that cannot commute with the upper outer join.)
 * As long as we have to do that, we might as well elide such FromExprs
 * everywhere.
 *
 * Some of these optimizations depend on recognizing empty (constant-true)
 * quals for FromExprs and JoinExprs.  That makes it useful to apply this
 * optimization pass after expression preprocessing, since that will have
 * eliminated constant-true quals, allowing more cases to be recognized as
 * optimizable.  What's more, the usual reason for an RTE_RESULT to be present
 * is that we pulled up a subquery or VALUES clause, thus very possibly
 * replacing Vars with constants, making it more likely that a qual can be
 * reduced to constant true.  Also, because some optimizations depend on
 * the outer-join type, it's best to have done reduce_outer_joins() first.
 *
 * A PlaceHolderVar referencing an RTE_RESULT RTE poses an obstacle to this
 * process: we must remove the RTE_RESULT's relid from the PHV's phrels, but
 * we must not reduce the phrels set to empty.  If that would happen, and
 * the RTE_RESULT is an immediate child of an outer join, we have to give up
 * and not remove the RTE_RESULT: there is noplace else to evaluate the
 * PlaceHolderVar.  (That is, in such cases the RTE_RESULT *does* have output
 * columns.)  But if the RTE_RESULT is an immediate child of an inner join,
 * we can usually change the PlaceHolderVar's phrels so as to evaluate it at
 * the inner join instead.  This is OK because we really only care that PHVs
 * are evaluated above or below the correct outer joins.  We can't, however,
 * postpone the evaluation of a PHV to above where it is used; so there are
 * some checks below on whether output PHVs are laterally referenced in the
 * other join input rel(s).
 *
 * We used to try to do this work as part of pull_up_subqueries() where the
 * potentially-optimizable cases get introduced; but it's way simpler, and
 * more effective, to do it separately.
 */
/*
 * remove_useless_result_rtes - (中文)从连接树中删除无用的 RTE_RESULT 关系
 * 并裁剪可省的单子 FromExpr
 *
 * 【作用】对外入口。收集全树基关系集合(查询含 PHV 时),递归调用
 * remove_useless_results_recurse 改写 jointree:删除"内连接于其他关系且无
 * 人依赖其输出 PHV"的 RTE_RESULT、对外连接/FULL/LEFT 情形做针对性化简,
 * 并裁剪单子 FromExpr;收尾时清理被删除外连接的 nullingrel 引用,以及删除
 * 指向任何 RTE_RESULT 的 PlanRowMark(幸存者也删——它只有一行,EPQ 无需
 * 标记)。
 *
 * 【设计思想】RTE_RESULT 恒返回一行且无输出列:内连接下直接删除;LEFT
 * 连接右端是它时左行必唯一匹配(ON TRUE)或结果无列,可弃;SEMI 时其 quals
 * 变 LHS 过滤器。删除的时机放在表达式预处理之后(reduce_outer_joins 之后),
 * 因为常量折叠会让更多 quals 变常量 TRUE/FALSE,便于识别。若 PHV 依赖该
 * RTE_RESULT 且它位于外连接可空侧,则无法删除(没有别的求值位置)。
 *
 * 【参数】root —— PlannerInfo,其 parse / append_rel_list / rowMarks 被改写。
 * 【返回值】无。
 */
void
remove_useless_result_rtes(PlannerInfo *root)
{
	Relids		baserels = NULL;
	Relids		dropped_outer_joins = NULL;
	ListCell   *cell;

	/*
	 * We'll need the set of baserels in the jointree to perform
	 * find_dependent_phvs() checks.  But if there are no PHVs anywhere in the
	 * query, those checks are no-ops, so we can skip the work.
	 */
	if (root->glob->lastPHId != 0)
		baserels = get_relids_in_jointree((Node *) root->parse->jointree,
										  false, false);

	/* Top level of jointree must always be a FromExpr */
	Assert(IsA(root->parse->jointree, FromExpr));
	/* Recurse ... */
	root->parse->jointree = (FromExpr *)
		remove_useless_results_recurse(root,
									   (Node *) root->parse->jointree,
									   baserels,
									   NULL,
									   &dropped_outer_joins);
	/* We should still have a FromExpr */
	Assert(IsA(root->parse->jointree, FromExpr));

	/*
	 * If we removed any outer-join nodes from the jointree, run around and
	 * remove references to those joins as nulling rels.  (There could be such
	 * references in PHVs that we pulled up out of the original subquery that
	 * the RESULT rel replaced.  This is kosher on the grounds that we now
	 * know that such an outer join wouldn't really have nulled anything.)  We
	 * don't do this during the main recursion, for simplicity and because we
	 * can handle all such joins in a single pass over the parse tree.
	 */
	if (!bms_is_empty(dropped_outer_joins))
	{
		root->parse = (Query *)
			remove_nulling_relids((Node *) root->parse,
								  dropped_outer_joins,
								  NULL);
		/* There could be references in the append_rel_list, too */
		root->append_rel_list = (List *)
			remove_nulling_relids((Node *) root->append_rel_list,
								  dropped_outer_joins,
								  NULL);
	}

	/*
	 * Remove any PlanRowMark referencing an RTE_RESULT RTE.  We obviously
	 * must do that for any RTE_RESULT that we just removed.  But one for a
	 * RTE that we did not remove can be dropped anyway: since the RTE has
	 * only one possible output row, there is no need for EPQ to mark and
	 * restore that row.
	 *
	 * It's necessary, not optional, to remove the PlanRowMark for a surviving
	 * RTE_RESULT RTE; otherwise we'll generate a whole-row Var for the
	 * RTE_RESULT, which the executor has no support for.
	 */
	foreach(cell, root->rowMarks)
	{
		PlanRowMark *rc = (PlanRowMark *) lfirst(cell);

		if (rt_fetch(rc->rti, root->parse->rtable)->rtekind == RTE_RESULT)
			root->rowMarks = foreach_delete_current(root->rowMarks, cell);
	}
}

/*
 * remove_useless_results_recurse
 *		Recursive guts of remove_useless_result_rtes.
 *
 * This recursively processes the jointree and returns a modified jointree.
 * In addition, the RT indexes of any removed outer-join nodes are added to
 * *dropped_outer_joins.
 *
 * jtnode is the current jointree node.  If it could be valid to merge
 * its quals into those of the parent node, parent_quals should point to
 * the parent's quals list; otherwise, pass NULL for parent_quals.
 * (Note that in some cases, parent_quals points to the quals of a parent
 * more than one level up in the tree.)
 *
 * baserels is the set of base (non-join) RT indexes in the whole jointree;
 * it can be NULL if the query contains no PHVs.
 */
/*
 * remove_useless_results_recurse - (中文)删除无用 RTE_RESULT 的递归核心
 *
 * 【作用】递归改写连接树。RangeTblRef:暂无动作。FromExpr:对每个子节点先
 * 递归(允许其把 quals 推给本 FromExpr 的 quals),若该子节点是 RTE_RESULT
 * 且存在兄弟、且兄弟不引用依赖它的 PHV,则从 fromlist 删除并记录 relid,
 * 循环后逐个 remove_result_refs 清理;若 fromlist 剩单成员且非顶层,尝试
 * 合并 quals 到父级(parent_quals)并返回该成员以裁剪 FromExpr。JoinExpr:
 * 递归左右(按 INNER/LEFT 允许 child 把 quals 上推到本连接或父级),再按
 * 连接类型化简:INNER 时一侧为 RTE_RESULT 则删除该侧(把 quals 并入父或建
 * FromExpr);LEFT 且右侧是 RTE_RESULT(无 quals 或 PHV 可挪)则弃右侧并登记
 * dropped_outer_joins;SEMI 且右侧是 RTE_RESULT 则把 quals 变成 LHS 过滤器。
 *
 * 【设计思想】
 * - "有人依赖"检查(find_dependent_phvs_in_jointree):若兄弟/另一侧
 *   LATERAL 引用了在 RTE_RESULT 处求值的 PHV,不能删除它(否则无处求值);
 * - 单子 FromExpr 裁剪的目的:消除"外连接可空侧是包着另一个外连接的
 *   FromExpr"的形态,使 deconstruct_jointree 能正确判定两外连接是否可交换
 *   (需要把 FromExpr 的 quals 提升为上层连接的 degenerate quals);
 * - parent_quals 指向"可能合法承接 pushed-up quals"的父级列表,按连接类型
 *   选择性允许(INNER 都行,LEFT 只允许右子提升,其余不允许)。
 *
 * 【参数】
 *   root                —— PlannerInfo;
 *   jtnode              —— 当前节点;
 *   baserels            —— 全树基关系集合(可为 NULL,若查询无 PHV);
 *   parent_quals        —— 父级 quals 列表的指针(允许时用于合并提升的 quals);
 *   dropped_outer_joins —— 输出:被删除的外连接 RT 索引集合。
 * 【返回值】改写后的连接树节点。
 */
static Node *
remove_useless_results_recurse(PlannerInfo *root, Node *jtnode,
								Relids baserels,
								Node **parent_quals,
								Relids *dropped_outer_joins)
{
	Assert(jtnode != NULL);
	if (IsA(jtnode, RangeTblRef))
	{
		/* Can't immediately do anything with a RangeTblRef */
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		Relids		result_relids = NULL;
		ListCell   *cell;

		/*
		 * We can drop RTE_RESULT rels from the fromlist so long as at least
		 * one child remains, since joining to a one-row table changes
		 * nothing.  (But we can't drop a RTE_RESULT that computes PHV(s) that
		 * are needed by some sibling.  The cleanup transformation below would
		 * reassign the PHVs to be computed at the join, which is too late for
		 * the sibling's use.)  The easiest way to mechanize this rule is to
		 * modify the list in-place.
		 */
		foreach(cell, f->fromlist)
		{
			Node	   *child = (Node *) lfirst(cell);
			int			varno;

			/* Recursively transform child, allowing it to push up quals ... */
			child = remove_useless_results_recurse(root, child,
												   baserels,
												   &f->quals,
												   dropped_outer_joins);
			/* ... and stick it back into the tree */
			lfirst(cell) = child;

			/*
			 * If it's an RTE_RESULT with at least one sibling, and no sibling
			 * references dependent PHVs, we can drop it.  We don't yet know
			 * what the inner join's final relid set will be, so postpone
			 * cleanup of PHVs etc till after this loop.
			 */
			if (list_length(f->fromlist) > 1 &&
				(varno = get_result_relid(root, child)) != 0 &&
				!find_dependent_phvs_in_jointree(root, (Node *) f, varno,
												 baserels))
			{
				f->fromlist = foreach_delete_current(f->fromlist, cell);
				result_relids = bms_add_member(result_relids, varno);
			}
		}

		/*
		 * Clean up if we dropped any RTE_RESULT RTEs.  This is a bit
		 * inefficient if there's more than one, but it seems better to
		 * optimize the support code for the single-relid case.
		 */
		if (result_relids)
		{
			int			varno = -1;

			while ((varno = bms_next_member(result_relids, varno)) >= 0)
				remove_result_refs(root, varno, (Node *) f);
		}

		/*
		 * If the FromExpr now has only one child, see if we can elide it.
		 * This is always valid if there are no quals, except at the top of
		 * the jointree (since Query.jointree is required to point to a
		 * FromExpr).  Otherwise, we can do it if we can push the quals up to
		 * the parent node.
		 *
		 * Note: while it would not be terribly hard to generalize this
		 * transformation to merge multi-child FromExprs into their parent
		 * FromExpr, that risks making the parent join too expensive to plan.
		 * We leave it to later processing to decide heuristically whether
		 * that's a good idea.  Pulling up a single child is always OK,
		 * however.
		 */
		if (list_length(f->fromlist) == 1 &&
			f != root->parse->jointree &&
			(f->quals == NULL || parent_quals != NULL))
		{
			/*
			 * Merge any quals up to parent.  They should be in implicit-AND
			 * format by now, so we just need to concatenate lists.  Put the
			 * child quals at the front, on the grounds that they should
			 * nominally be evaluated earlier.
			 */
			if (f->quals != NULL)
				*parent_quals = (Node *)
					list_concat(castNode(List, f->quals),
								castNode(List, *parent_quals));
			return (Node *) linitial(f->fromlist);
		}
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;
		int			varno;

		/*
		 * First, recurse.  We can absorb pushed-up FromExpr quals from either
		 * child into this node if the jointype is INNER, since then this is
		 * equivalent to a FromExpr.  When the jointype is LEFT, we can absorb
		 * quals from the RHS child into the current node, as they're
		 * essentially degenerate quals of the outer join.  Moreover, if we've
		 * been passed down a parent_quals pointer then we can allow quals of
		 * the LHS child to be absorbed into the parent.  (This is important
		 * to ensure we remove single-child FromExprs immediately below
		 * commutable left joins.)  For other jointypes, we can't move child
		 * quals up, or at least there's no particular reason to.
		 */
		j->larg = remove_useless_results_recurse(root, j->larg,
												 baserels,
												 (j->jointype == JOIN_INNER) ?
												 &j->quals :
												 (j->jointype == JOIN_LEFT) ?
												 parent_quals : NULL,
												 dropped_outer_joins);
		j->rarg = remove_useless_results_recurse(root, j->rarg,
												 baserels,
												 (j->jointype == JOIN_INNER ||
												  j->jointype == JOIN_LEFT) ?
												 &j->quals : NULL,
												 dropped_outer_joins);

		/* Apply join-type-specific optimization rules */
		switch (j->jointype)
		{
			case JOIN_INNER:

				/*
				 * An inner join is equivalent to a FromExpr, so if either
				 * side was simplified to an RTE_RESULT rel, we can replace
				 * the join with a FromExpr with just the other side.
				 * Furthermore, we can elide that FromExpr according to the
				 * same rules as above.
				 *
				 * Just as in the FromExpr case, we can't simplify if the
				 * other input rel references any PHVs that are marked as to
				 * be evaluated at the RTE_RESULT rel, because we can't
				 * postpone their evaluation in that case.  But we only have
				 * to check this in cases where it's syntactically legal for
				 * the other input to have a LATERAL reference to the
				 * RTE_RESULT rel.  Only RHSes of inner and left joins are
				 * allowed to have such refs.
				 */
				if ((varno = get_result_relid(root, j->larg)) != 0 &&
					!find_dependent_phvs_in_jointree(root, j->rarg, varno,
													 baserels))
				{
					remove_result_refs(root, varno, j->rarg);
					if (j->quals != NULL && parent_quals == NULL)
						jtnode = (Node *)
							makeFromExpr(list_make1(j->rarg), j->quals);
					else
					{
						/* Merge any quals up to parent */
						if (j->quals != NULL)
							*parent_quals = (Node *)
								list_concat(castNode(List, j->quals),
											castNode(List, *parent_quals));
						jtnode = j->rarg;
					}
				}
				else if ((varno = get_result_relid(root, j->rarg)) != 0)
				{
					remove_result_refs(root, varno, j->larg);
					if (j->quals != NULL && parent_quals == NULL)
						jtnode = (Node *)
							makeFromExpr(list_make1(j->larg), j->quals);
					else
					{
						/* Merge any quals up to parent */
						if (j->quals != NULL)
							*parent_quals = (Node *)
								list_concat(castNode(List, j->quals),
											castNode(List, *parent_quals));
						jtnode = j->larg;
					}
				}
				break;
			case JOIN_LEFT:

				/*
				 * We can simplify this case if the RHS is an RTE_RESULT, with
				 * two different possibilities:
				 *
				 * If the qual is empty (JOIN ON TRUE), then the join can be
				 * strength-reduced to a plain inner join, since each LHS row
				 * necessarily has exactly one join partner.  So we can always
				 * discard the RHS, much as in the JOIN_INNER case above.
				 * (Again, the LHS could not contain a lateral reference to
				 * the RHS.)
				 *
				 * Otherwise, it's still true that each LHS row should be
				 * returned exactly once, and since the RHS returns no columns
				 * (unless there are PHVs that have to be evaluated there), we
				 * don't much care if it's null-extended or not.  So in this
				 * case also, we can just ignore the qual and discard the left
				 * join.
				 */
				if ((varno = get_result_relid(root, j->rarg)) != 0 &&
					(j->quals == NULL ||
					 !find_dependent_phvs(root, varno, baserels)))
				{
					remove_result_refs(root, varno, j->larg);
					*dropped_outer_joins = bms_add_member(*dropped_outer_joins,
														  j->rtindex);
					jtnode = j->larg;
				}
				break;
			case JOIN_SEMI:

				/*
				 * We may simplify this case if the RHS is an RTE_RESULT; the
				 * join qual becomes effectively just a filter qual for the
				 * LHS, since we should either return the LHS row or not.  The
				 * filter clause must go into a new FromExpr if we can't push
				 * it up to the parent.
				 *
				 * There is a fine point about PHVs that are supposed to be
				 * evaluated at the RHS.  Such PHVs could only appear in the
				 * semijoin's qual, since the rest of the query cannot
				 * reference any outputs of the semijoin's RHS.  Therefore,
				 * they can't actually go to null before being examined, and
				 * it'd be OK to just remove the PHV wrapping.  We don't have
				 * infrastructure for that, but remove_result_refs() will
				 * relabel them as to be evaluated at the LHS, which is fine.
				 *
				 * Also, we don't need to worry about removing traces of the
				 * join's rtindex, since it hasn't got one.
				 */
				if ((varno = get_result_relid(root, j->rarg)) != 0)
				{
					Assert(j->rtindex == 0);
					remove_result_refs(root, varno, j->larg);
					if (j->quals != NULL && parent_quals == NULL)
						jtnode = (Node *)
							makeFromExpr(list_make1(j->larg), j->quals);
					else
					{
						/* Merge any quals up to parent */
						if (j->quals != NULL)
							*parent_quals = (Node *)
								list_concat(castNode(List, j->quals),
											castNode(List, *parent_quals));
						jtnode = j->larg;
					}
				}
				break;
			case JOIN_FULL:
			case JOIN_ANTI:
				/* We have no special smarts for these cases */
				break;
			default:
				/* Note: JOIN_RIGHT should be gone at this point */
				elog(ERROR, "unrecognized join type: %d",
					 (int) j->jointype);
				break;
		}
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
	return jtnode;
}

/*
 * get_result_relid
 *		If jtnode is a RangeTblRef for an RTE_RESULT RTE, return its relid;
 *		otherwise return 0.
 */
/*
 * get_result_relid - (中文)若连接树节点是引用 RTE_RESULT 的 RangeTblRef,
 * 返回其 relid,否则返回 0
 *
 * 【作用】辅助判定:jtnode 为 RangeTblRef 且其 RTE 类型是 RTE_RESULT 时
 * 返回该 RT 索引,否则 0。
 *
 * 【设计思想】remove_useless_results_recurse 需要频繁识别"可删除的
 * RTE_RESULT",此函数把节点类型检查与 RTE 类型检查封装起来。
 *
 * 【参数】
 *   root   —— PlannerInfo(用于查 rtable);
 *   jtnode —— 待检查的连接树节点。
 * 【返回值】RTE_RESULT 的 RT 索引;否则 0。
 */
static int
get_result_relid(PlannerInfo *root, Node *jtnode)
{
	int			varno;

	if (!IsA(jtnode, RangeTblRef))
		return 0;
	varno = ((RangeTblRef *) jtnode)->rtindex;
	if (rt_fetch(varno, root->parse->rtable)->rtekind != RTE_RESULT)
		return 0;
	return varno;
}

/*
 * remove_result_refs
 *		Helper routine for dropping an unneeded RTE_RESULT RTE.
 *
 * This doesn't physically remove the RTE from the jointree, because that's
 * more easily handled in remove_useless_results_recurse.  What it does do
 * is the necessary cleanup in the rest of the tree: we must adjust any PHVs
 * that may reference the RTE.  Be sure to call this at a point where the
 * jointree is valid (no disconnected nodes).
 *
 * Note that we don't need to process the append_rel_list, since RTEs
 * referenced directly in the jointree won't be appendrel members.
 *
 * varno is the RTE_RESULT's relid.
 * newjtloc is the jointree location at which any PHVs referencing the
 * RTE_RESULT should be evaluated instead.
 */
/*
 * remove_result_refs - (中文)删除 RTE_RESULT 时的全树清理
 *
 * 【作用】在被删除 RTE_RESULT(varno)之后,调整所有引用它的 PHV:把它们的
 * phrels 中 varno 替换为 newjtloc 处的关系集合(substitute_phv_relids),并
 * 修正 append_rel_list 中引用了 varno 的节点(fix_append_rel_relids)。
 * 物理删除节点由调用者负责,本函数只做"引用清理"。
 *
 * 【设计思想】删除 RTE_RESULT 后,原本在它那里求值的 PHV 必须改到"其所在
 * 连接(新的 jointree 位置)"求值;新位置的关系集合必然非空(PHV 不能失效)。
 * PlanRowMark 的删除推迟到 remove_useless_result_rtes 统一处理。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   varno   —— 被删除的 RTE_RESULT 的 RT 索引;
 *   newjtloc —— RTE_RESULT 所在的新 jointree 位置(承接 PHV 的关系集合源)。
 * 【返回值】无。
 */
static void
remove_result_refs(PlannerInfo *root, int varno, Node *newjtloc)
{
	/* Fix up PlaceHolderVars as needed */
	/* If there are no PHVs anywhere, we can skip this bit */
	if (root->glob->lastPHId != 0)
	{
		Relids		subrelids;

		subrelids = get_relids_in_jointree(newjtloc, true, false);
		Assert(!bms_is_empty(subrelids));
		substitute_phv_relids((Node *) root->parse, varno, subrelids);
		fix_append_rel_relids(root, varno, subrelids);
	}

	/*
	 * We also need to remove any PlanRowMark referencing the RTE, but we
	 * postpone that work until we return to remove_useless_result_rtes.
	 */
}

/*
 * find_dependent_phvs - are there any PlaceHolderVars whose base relids are
 * exactly the given varno?
 *
 * We ignore outer-join relids present in a PHV's phrels, by intersecting
 * with the caller-supplied "baserels" set.  This is necessary in part
 * because some of the OJ relids may be stale, that is we may have
 * already decided to remove those joins in remove_useless_result_rtes
 * and not yet have cleaned their relid bits out of upper PHVs.
 * But in general, it's the set of baserels that identify possible places
 * to evaluate a PHV, and we mustn't let that go to empty.  (The caller is
 * allowed to pass baserels as NULL if the query contains no PHVs at all,
 * since then there is no work to do anyway.)
 *
 * find_dependent_phvs should be used when we want to see if there are
 * any such PHVs anywhere in the Query.  Another use-case is to see if
 * a subtree of the join tree contains such PHVs; but for that, we have
 * to look not only at the join tree nodes themselves but at the
 * referenced RTEs.  For that, use find_dependent_phvs_in_jointree.
 */
typedef struct
{
	Relids		relids;			/* target relid, represented as a relid set */
	Relids		baserels;		/* base RT indexes in query, NULL if no PHVs */
	int			sublevels_up;	/* current nesting level */
} find_dependent_phvs_context;

/*
 * find_dependent_phvs_walker - (中文)遍历器:查找 phrels 的基关系部分恰好
 * 等于目标 relid 集合的 PlaceHolderVar
 *
 * 【作用】表达式遍历回调。遇到 PlaceHolderVar 且其 phlevelsup 与当前嵌套
 * 层一致时,取其 phrels 与 baserels 的交集(即其"基关系"部分),与目标
 * context->relids 比较,相等则返回 true 停止遍历;遇到 Query 时递增
 * sublevels_up 递归其内部;其余节点走 expression_tree_walker。
 *
 * 【设计思想】
 * - PHV 的 phrels 可能含外连接 relid(有的已陈旧),必须用 baserels 交集把
 *   它们滤掉,只看"决定求值位置的基关系集合"是否缩水到恰好等于被删关系;
 * - 在删除 RTE_RESULT 前必须确认没有 PHV"只能在那里求值"。
 *
 * 【参数】
 *   node    —— 当前节点;
 *   context —— 查找上下文(目标 relids、baserels、当前嵌套层)。
 * 【返回值】true 表示已找到依赖的 PHV。
 */
static bool
find_dependent_phvs_walker(Node *node,
						   find_dependent_phvs_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (phv->phlevelsup == context->sublevels_up)
		{
			Relids		phbaserels = bms_intersect(phv->phrels,
												   context->baserels);
			bool		match = bms_equal(context->relids, phbaserels);

			bms_free(phbaserels);
			if (match)
				return true;
		}
		/* fall through to examine children */
	}
	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node,
								   find_dependent_phvs_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	/* Shouldn't need to handle most planner auxiliary nodes here */
	Assert(!IsA(node, SpecialJoinInfo));
	Assert(!IsA(node, PlaceHolderInfo));
	Assert(!IsA(node, MinMaxAggInfo));

	return expression_tree_walker(node, find_dependent_phvs_walker, context);
}

/*
 * find_dependent_phvs - (中文)查询整棵查询树中是否存在依赖指定 RTE_RESULT
 * 的 PlaceHolderVar
 *
 * 【作用】对整棵查询树(parse)以及 append_rel_list 用 find_dependent_phvs_walker
 * 搜索 phrels 的基关系部分恰为 {varno} 的 PHV;查询无 PHV(lastPHId == 0)
 * 时直接返回 false。
 *
 * 【设计思想】这是"删除 RTE_RESULT 是否安全"的全局检查:任何 PHV 的基关系
 * 集合都不允许缩水为空。context->baserels 由调用者提供(全树基关系集合)。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   varno   —— 待检查的 RTE_RESULT 的 RT 索引;
 *   baserels —— 全树基关系集合(无 PHV 时可为 NULL)。
 * 【返回值】true 表示存在依赖该关系的 PHV。
 */
static bool
find_dependent_phvs(PlannerInfo *root, int varno, Relids baserels)
{
	find_dependent_phvs_context context;

	/* If there are no PHVs anywhere, we needn't work hard */
	if (root->glob->lastPHId == 0)
		return false;

	context.relids = bms_make_singleton(varno);
	context.baserels = baserels;
	context.sublevels_up = 0;

	if (query_tree_walker(root->parse, find_dependent_phvs_walker, &context, 0))
		return true;
	/* The append_rel_list could be populated already, so check it too */
	if (expression_tree_walker((Node *) root->append_rel_list,
							   find_dependent_phvs_walker,
							   &context))
		return true;
	return false;
}

/*
 * find_dependent_phvs_in_jointree - (中文)查询连接树片段内(含其引用的
 * LATERAL RTE)是否存在依赖指定 RTE_RESULT 的 PlaceHolderVar
 *
 * 【作用】先在连接树节点本身的限定条件中查找依赖 PHV;再收集该片段引用
 * 的基关系集合,对其中每个标记为 LATERAL 的 RTE(它们可能内含对被删关系
 * 的交叉引用)用 range_table_entry_walker 继续查找。
 *
 * 【设计思想】与 find_dependent_phvs 的差异在于作用域:删除兄弟节点前只需
 * 检查"兄弟们是否依赖它",而兄弟内部的 LATERAL 子查询可能引用被删关系,
 * 因此必须一并检查其 RTE 内容(join RTE 已展平,可忽略)。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   node    —— 待检查的连接树片段;
 *   varno   —— 被删 RTE_RESULT 的 RT 索引;
 *   baserels —— 全树基关系集合。
 * 【返回值】true 表示片段内存在依赖 PHV。
 */
static bool
find_dependent_phvs_in_jointree(PlannerInfo *root, Node *node, int varno,
								Relids baserels)
{
	find_dependent_phvs_context context;
	Relids		subrelids;
	int			relid;

	/* If there are no PHVs anywhere, we needn't work hard */
	if (root->glob->lastPHId == 0)
		return false;

	context.relids = bms_make_singleton(varno);
	context.baserels = baserels;
	context.sublevels_up = 0;

	/*
	 * See if the jointree fragment itself contains references (in join quals)
	 */
	if (find_dependent_phvs_walker(node, &context))
		return true;

	/*
	 * Otherwise, identify the set of referenced RTEs (we can ignore joins,
	 * since they should be flattened already, so their join alias lists no
	 * longer matter), and tediously check each RTE.  We can ignore RTEs that
	 * are not marked LATERAL, though, since they couldn't possibly contain
	 * any cross-references to other RTEs.
	 */
	subrelids = get_relids_in_jointree(node, false, false);
	relid = -1;
	while ((relid = bms_next_member(subrelids, relid)) >= 0)
	{
		RangeTblEntry *rte = rt_fetch(relid, root->parse->rtable);

		if (rte->lateral &&
			range_table_entry_walker(rte, find_dependent_phvs_walker, &context, 0))
			return true;
	}

	return false;
}

/*
 * substitute_phv_relids - adjust PlaceHolderVar relid sets after pulling up
 * a subquery or removing an RTE_RESULT jointree item
 *
 * Find any PlaceHolderVar nodes in the given tree that reference the
 * pulled-up relid, and change them to reference the replacement relid(s).
 *
 * NOTE: although this has the form of a walker, we cheat and modify the
 * nodes in-place.  This should be OK since the tree was copied by
 * pullup_replace_vars earlier.  Avoid scribbling on the original values of
 * the bitmapsets, though, because expression_tree_mutator doesn't copy those.
 */
typedef struct
{
	int			varno;
	int			sublevels_up;
	Relids		subrelids;
} substitute_phv_relids_context;

/*
 * substitute_phv_relids_walker - (中文)遍历器:把引用指定 relid 的 PHV 的
 * phrels 改写为替代关系集合
 *
 * 【作用】表达式遍历回调。遇到 PlaceHolderVar 且 phlevelsup 与当前层一致、
 * 且 phrels 含 context->varno 时:phrels 并上 subrelids、删除 varno(断言
 * 结果非空,PHV 求值位置不得为空);Query 节点递增 sublevels_up 递归;其余
 * 走 expression_tree_walker。
 *
 * 【设计思想】上提子查询或删除 RTE_RESULT 后,原来引用被删 varno 的 PHV
 * 必须改引用其替代位置的关系集合,否则 PHV 求值点失效。这里就地修改节点
 * (树此前已被复制过),但绝不动 bitmapsets 的原值(expression_tree_mutator
 * 不复制它们,故用 bms_union 新造)。
 *
 * 【参数】
 *   node    —— 当前节点;
 *   context —— 替换上下文(varno、subrelids、当前嵌套层)。
 * 【返回值】true 表示应停止遍历(实际这里只做修改,不提前停止)。
 */
static bool
substitute_phv_relids_walker(Node *node,
							 substitute_phv_relids_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		if (phv->phlevelsup == context->sublevels_up &&
			bms_is_member(context->varno, phv->phrels))
		{
			phv->phrels = bms_union(phv->phrels,
									context->subrelids);
			phv->phrels = bms_del_member(phv->phrels,
										 context->varno);
			/* Assert we haven't broken the PHV */
			Assert(!bms_is_empty(phv->phrels));
		}
		/* fall through to examine children */
	}
	if (IsA(node, Query))
	{
		/* Recurse into subselects */
		bool		result;

		context->sublevels_up++;
		result = query_tree_walker((Query *) node,
								   substitute_phv_relids_walker,
								   context, 0);
		context->sublevels_up--;
		return result;
	}
	/* Shouldn't need to handle planner auxiliary nodes here */
	Assert(!IsA(node, SpecialJoinInfo));
	Assert(!IsA(node, AppendRelInfo));
	Assert(!IsA(node, PlaceHolderInfo));
	Assert(!IsA(node, MinMaxAggInfo));

	return expression_tree_walker(node, substitute_phv_relids_walker, context);
}

/*
 * substitute_phv_relids - (中文)调整 PHV 的 relid 集合(对树做整体替换)
 *
 * 【作用】把给定树(Query 或裸表达式)中所有引用 varno 的 PHV 的 phrels 替
 * 换为 subrelids。用 query_or_expression_tree_walker 以 sublevels_up = 0
 * 启动,可同时处理 Query 与普通表达式入口。
 *
 * 【设计思想】封装 walker 的启动逻辑,供"上提子查询 / 删除 RTE_RESULT"两处
 * 复用。注意是就地修改(节点此前已复制)。
 *
 * 【参数】
 *   node      —— 待处理的树;
 *   varno     —— 要被替换掉的旧 relid;
 *   subrelids —— 替代关系集合。
 * 【返回值】无。
 */
static void
substitute_phv_relids(Node *node, int varno, Relids subrelids)
{
	substitute_phv_relids_context context;

	context.varno = varno;
	context.sublevels_up = 0;
	context.subrelids = subrelids;

	/*
	 * Must be prepared to start with a Query or a bare expression tree.
	 */
	query_or_expression_tree_walker(node,
									substitute_phv_relids_walker,
									&context,
									0);
}

/*
 * fix_append_rel_relids: update RT-index fields of AppendRelInfo nodes
 *
 * When we pull up a subquery, any AppendRelInfo references to the subquery's
 * RT index have to be replaced by the substituted relid (and there had better
 * be only one).  We also need to apply substitute_phv_relids to their
 * translated_vars lists, since those might contain PlaceHolderVars.
 *
 * We assume we may modify the AppendRelInfo nodes in-place.
 */
/*
 * fix_append_rel_relids - (中文)更新 AppendRelInfo 节点的 RT 索引字段
 *
 * 【作用】遍历 root->append_rel_list:若某个 AppendRelInfo 的 child_relid 等
 * 于被上提子查询的 varno,则替换为 subrelids 中唯一的成员(必须是单值,用
 * bms_singleton_member 提取);同时对其 translated_vars 中的 PHV 做
 * substitute_phv_relids 修正。
 *
 * 【设计思想】上提子查询后,append 关系里引用该子查询 relid 的地方都要指
 * 向"它上提后所在的关系集合"。延迟到"确有多个成员时才提取"是为了避免
 * 未引用时对非法(多成员)集合报错;parent_relid 不应是被上提目标(断言)。
 *
 * 【参数】
 *   root      —— PlannerInfo;
 *   varno     —— 被上提子查询的原 RT 索引;
 *   subrelids —— 替代关系集合。
 * 【返回值】无。
 */
static void
fix_append_rel_relids(PlannerInfo *root, int varno, Relids subrelids)
{
	ListCell   *l;
	int			subvarno = -1;

	/*
	 * We only want to extract the member relid once, but we mustn't fail
	 * immediately if there are multiple members; it could be that none of the
	 * AppendRelInfo nodes refer to it.  So compute it on first use. Note that
	 * bms_singleton_member will complain if set is not singleton.
	 */
	foreach(l, root->append_rel_list)
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) lfirst(l);

		/* The parent_relid shouldn't ever be a pullup target */
		Assert(appinfo->parent_relid != varno);

		if (appinfo->child_relid == varno)
		{
			if (subvarno < 0)
				subvarno = bms_singleton_member(subrelids);
			appinfo->child_relid = subvarno;
		}

		/* Also fix up any PHVs in its translated vars */
		if (root->glob->lastPHId != 0)
			substitute_phv_relids((Node *) appinfo->translated_vars,
								  varno, subrelids);
	}
}

/*
 * get_relids_in_jointree: get set of RT indexes present in a jointree
 *
 * Base-relation relids are always included in the result.
 * If include_outer_joins is true, outer-join RT indexes are included.
 * If include_inner_joins is true, inner-join RT indexes are included.
 *
 * Note that for most purposes in the planner, outer joins are included
 * in standard relid sets.  Setting include_inner_joins true is only
 * appropriate for special purposes during subquery flattening.
 */
/*
 * get_relids_in_jointree - (中文)获取连接树中出现的 RT 索引集合
 *
 * 【作用】递归收集连接树中的关系 RT 索引:基关系(RangeTblRef)总是计入;
 * 连接节点按 include_outer_joins / include_inner_joins 决定其 rtindex 是否
 * 计入(INNER 走前者开关,其余连接走后者开关)。
 *
 * 【设计思想】规划器中大多数场景外连接 rtindex 应计入标准 relid 集合,
 * 而 inner join 的 rtindex 通常只在子查询展平的特殊用途下才需要。
 *
 * 【参数】
 *   jtnode              —— 连接树节点;
 *   include_outer_joins —— 是否计入外连接 RT 索引;
 *   include_inner_joins —— 是否计入内连接 RT 索引。
 * 【返回值】RT 索引集合(位图)。
 */
Relids
get_relids_in_jointree(Node *jtnode, bool include_outer_joins,
					   bool include_inner_joins)
{
	Relids		result = NULL;

	if (jtnode == NULL)
		return result;
	if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		result = bms_make_singleton(varno);
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		foreach(l, f->fromlist)
		{
			result = bms_join(result,
							  get_relids_in_jointree(lfirst(l),
													 include_outer_joins,
													 include_inner_joins));
		}
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		result = get_relids_in_jointree(j->larg,
										include_outer_joins,
										include_inner_joins);
		result = bms_join(result,
						  get_relids_in_jointree(j->rarg,
												 include_outer_joins,
												 include_inner_joins));
		if (j->rtindex)
		{
			if (j->jointype == JOIN_INNER)
			{
				if (include_inner_joins)
					result = bms_add_member(result, j->rtindex);
			}
			else
			{
				if (include_outer_joins)
					result = bms_add_member(result, j->rtindex);
			}
		}
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
	return result;
}

/*
 * get_relids_for_join: get set of base+OJ RT indexes making up a join
 */
/*
 * get_relids_for_join - (中文)获取构成某连接的基关系 + 外连接 RT 索引集合
 *
 * 【作用】在查询连接树中定位 joinrelid 对应的节点(find_jointree_node_for_rel),
 * 找不到报错,找到则返回 get_relids_in_jointree(node, true, false) 的结果。
 *
 * 【设计思想】封装"按连接 RT 索引找其覆盖关系集"的常见需求;含外连接索引
 * 但排除内连接索引是规划器中连接关系 relid 的标准形态。
 *
 * 【参数】
 *   query      —— 查询;
 *   joinrelid  —— 连接的 RT 索引。
 * 【返回值】该连接覆盖的基关系 + 外连接 RT 索引集合。
 */
Relids
get_relids_for_join(Query *query, int joinrelid)
{
	Node	   *jtnode;

	jtnode = find_jointree_node_for_rel((Node *) query->jointree,
										joinrelid);
	if (!jtnode)
		elog(ERROR, "could not find join node %d", joinrelid);
	return get_relids_in_jointree(jtnode, true, false);
}

/*
 * find_jointree_node_for_rel: locate jointree node for a base or join RT index
 *
 * Returns NULL if not found
 */
/*
 * find_jointree_node_for_rel - (中文)在连接树中定位包含指定 RT 索引的节点
 *
 * 【作用】递归搜索连接树:RangeTblRef 直接命中;FromExpr 遍历子节点;JoinExpr
 * 先看自身的 rtindex 是否匹配,再递归左右子树。返回包含 relid 的最上层匹配
 * 节点(自身 rtindex 命中时即该连接节点),找不到返回 NULL。
 *
 * 【设计思想】基关系在 jointree 中必然以叶子出现;连接节点则通过其 rtindex
 * 命中(不是靠包含关系,因此与 get_relids_in_jointree 的判定不同)。
 *
 * 【参数】
 *   jtnode —— 连接树节点;
 *   relid  —— 要找的 RT 索引。
 * 【返回值】包含 relid 的连接树节点;不存在则为 NULL。
 */
static Node *
find_jointree_node_for_rel(Node *jtnode, int relid)
static Node *
find_jointree_node_for_rel(Node *jtnode, int relid)
{
	if (jtnode == NULL)
		return NULL;
	if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		if (relid == varno)
			return jtnode;
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		foreach(l, f->fromlist)
		{
			jtnode = find_jointree_node_for_rel(lfirst(l), relid);
			if (jtnode)
				return jtnode;
		}
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		if (relid == j->rtindex)
			return jtnode;
		jtnode = find_jointree_node_for_rel(j->larg, relid);
		if (jtnode)
			return jtnode;
		jtnode = find_jointree_node_for_rel(j->rarg, relid);
		if (jtnode)
			return jtnode;
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
	return NULL;
}

/*
 * get_nullingrels: collect info about which outer joins null which relations
 *
 * The result struct contains, for each leaf relation used in the query,
 * the set of relids of outer joins that potentially null that rel.
 */
/*
 * get_nullingrels - (中文)收集"哪些外连接会置空哪些关系"的信息
 *
 * 【作用】为每个在查询中使用的叶子关系记录"可能把它置空的外连接 relid
 * 集合"(数组按 RT 索引下标存放)。从 jointree 根开始调用
 * get_nullingrels_recurse,upper_nullingrels 初始为 NULL。
 *
 * 【设计思想】该信息供 perform_pullup_replace_vars 在把子查询输出上提到
 * 父查询时,为 Var 精确合成 varnullingrels;以及由连接树静态推导行可空性。
 *
 * 【参数】
 *   parse —— 查询(取 jointree 与 rtable)。
 * 【返回值】nullingrel_info:rtlength 为 rtable 长度,nullingrels 数组为各
 * 关系的潜在置空外连接集合(下标 1..rtlength)。
 */
static nullingrel_info *
get_nullingrels(Query *parse)
{
	nullingrel_info *result = palloc_object(nullingrel_info);

	result->rtlength = list_length(parse->rtable);
	result->nullingrels = palloc0_array(Relids, result->rtlength + 1);
	get_nullingrels_recurse((Node *) parse->jointree, NULL, result);
	return result;
}

/*
 * Recursive guts of get_nullingrels().
 *
 * Note: at any recursion level, the passed-down upper_nullingrels must be
 * treated as a constant, but it can be stored directly into *info
 * if we're at leaf level.  Upper recursion levels do not free their mutated
 * copies of the nullingrels, because those are probably referenced by
 * at least one leaf rel.
 */
/*
 * get_nullingrels_recurse - (中文)get_nullingrels 的递归核心
 *
 * 【作用】自顶向下遍历连接树,为每个叶子关系记录"会置空它的外连接集合"。
 * RangeTblRef:把当前累计的 upper_nullingrels 直接存给该关系。FromExpr:原样
 * 传递。JoinExpr:INNER 双侧传递原集合;LEFT/SEMI/ANTI 右子收到加入本连接
 * rtindex 后的集合(左子不变);FULL 双侧都加;RIGHT 左子加、右子不变。
 *
 * 【设计思想】
 * - 每个递归层的 upper_nullingrels 都须视为不可变:叶子直接存引用没问题,
 *   但上层"bms_add_member(bms_copy(...))"产生的局部副本可能被多个叶子引用,
 *   因此上层不得释放自己的副本;
 * - 连接的 rtindex 只在"该连接确实会置空某侧"时加入(LEFT 置空右、RIGHT
 *   置空左、FULL 置空双侧);SEMI/ANTI 对外行不产生空扩展,但按 PG 语义
 *   仍视作会置空右子(与 nullingrel 通用表示一致)。
 *
 * 【参数】
 *   jtnode            —— 当前连接树节点;
 *   upper_nullingrels —— 从根到当前路径上累计的"可能置空"外连接集合;
 *   info              —— 输出结构(各叶子关系的置空集合数组)。
 * 【返回值】无。
 */
static void
get_nullingrels_recurse(Node *jtnode, Relids upper_nullingrels,
						nullingrel_info *info)
static void
get_nullingrels_recurse(Node *jtnode, Relids upper_nullingrels,
						nullingrel_info *info)
{
	if (jtnode == NULL)
		return;
	if (IsA(jtnode, RangeTblRef))
	{
		int			varno = ((RangeTblRef *) jtnode)->rtindex;

		Assert(varno > 0 && varno <= info->rtlength);
		info->nullingrels[varno] = upper_nullingrels;
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		foreach(l, f->fromlist)
		{
			get_nullingrels_recurse(lfirst(l), upper_nullingrels, info);
		}
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;
		Relids		local_nullingrels;

		switch (j->jointype)
		{
			case JOIN_INNER:
				get_nullingrels_recurse(j->larg, upper_nullingrels, info);
				get_nullingrels_recurse(j->rarg, upper_nullingrels, info);
				break;
			case JOIN_LEFT:
			case JOIN_SEMI:
			case JOIN_ANTI:
				local_nullingrels = bms_add_member(bms_copy(upper_nullingrels),
												   j->rtindex);
				get_nullingrels_recurse(j->larg, upper_nullingrels, info);
				get_nullingrels_recurse(j->rarg, local_nullingrels, info);
				break;
			case JOIN_FULL:
				local_nullingrels = bms_add_member(bms_copy(upper_nullingrels),
												   j->rtindex);
				get_nullingrels_recurse(j->larg, local_nullingrels, info);
				get_nullingrels_recurse(j->rarg, local_nullingrels, info);
				break;
			case JOIN_RIGHT:
				local_nullingrels = bms_add_member(bms_copy(upper_nullingrels),
												   j->rtindex);
				get_nullingrels_recurse(j->larg, local_nullingrels, info);
				get_nullingrels_recurse(j->rarg, upper_nullingrels, info);
				break;
			default:
				elog(ERROR, "unrecognized join type: %d",
					 (int) j->jointype);
				break;
		}
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
}
