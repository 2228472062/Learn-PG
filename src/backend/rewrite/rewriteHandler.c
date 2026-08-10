/*-------------------------------------------------------------------------
 *
 * rewriteHandler.c
 *		Primary module of query rewriter.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/rewrite/rewriteHandler.c
 *
 * NOTES
 *	  Some of the terms used in this file are of historic nature: "retrieve"
 *	  was the PostQUEL keyword for what today is SELECT. "RIR" stands for
 *	  "Retrieve-Instead-Retrieve", that is an ON SELECT DO INSTEAD SELECT rule
 *	  (which has to be unconditional and where only one rule can exist on each
 *	  relation).
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/relation.h"
#include "access/sysattr.h"
#include "access/table.h"
#include "catalog/dependency.h"
#include "commands/trigger.h"
#include "executor/executor.h"
#include "foreign/fdwapi.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/optimizer.h"
#include "parser/analyze.h"
#include "parser/parse_coerce.h"
#include "parser/parse_relation.h"
#include "parser/parsetree.h"
#include "rewrite/rewriteDefine.h"
#include "rewrite/rewriteGraphTable.h"
#include "rewrite/rewriteHandler.h"
#include "rewrite/rewriteManip.h"
#include "rewrite/rewriteSearchCycle.h"
#include "rewrite/rowsecurity.h"
#include "tcop/tcopprot.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"


/* We use a list of these to detect recursion in RewriteQuery */
typedef struct rewrite_event
{
	Oid			relation;		/* OID of relation having rules */
	CmdType		event;			/* type of rule being fired */
} rewrite_event;

typedef struct acquireLocksOnSubLinks_context
{
	bool		for_execute;	/* AcquireRewriteLocks' forExecute param */
} acquireLocksOnSubLinks_context;

typedef struct fireRIRonSubLink_context
{
	List	   *activeRIRs;
	bool		hasRowSecurity;
} fireRIRonSubLink_context;

static bool acquireLocksOnSubLinks(Node *node,
								   acquireLocksOnSubLinks_context *context);
static Query *rewriteRuleAction(Query *parsetree,
								Query *rule_action,
								Node *rule_qual,
								int rt_index,
								CmdType event,
								bool *returning_flag);
static List *adjustJoinTreeList(Query *parsetree, bool removert, int rt_index);
static List *rewriteTargetListIU(List *targetList,
								 CmdType commandType,
								 OverridingKind override,
								 Relation target_relation,
								 RangeTblEntry *values_rte,
								 int values_rte_index,
								 Bitmapset **unused_values_attrnos);
static TargetEntry *process_matched_tle(TargetEntry *src_tle,
										TargetEntry *prior_tle,
										const char *attrName);
static Node *get_assignment_input(Node *node);
static Bitmapset *findDefaultOnlyColumns(RangeTblEntry *rte);
static bool rewriteValuesRTE(Query *parsetree, RangeTblEntry *rte, int rti,
							 Relation target_relation,
							 Bitmapset *unused_cols);
static void rewriteValuesRTEToNulls(Query *parsetree, RangeTblEntry *rte);
static void markQueryForLocking(Query *qry, Node *jtnode,
								LockClauseStrength strength, LockWaitPolicy waitPolicy,
								bool pushedDown);
static List *matchLocks(CmdType event, Relation relation,
						int varno, Query *parsetree, bool *hasUpdate);
static Query *fireRIRrules(Query *parsetree, List *activeRIRs);
static Bitmapset *adjust_view_column_set(Bitmapset *cols, List *targetlist);
static List *get_generated_columns(Relation rel, int rt_index, bool include_stored);


/*
 * ============================================================================
 * 【中文注释】AcquireRewriteLocks —— 在查询涉及的所有关系上获取合适锁并修正 JOIN 的已删除列
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在重写、规划和执行整个查询期间，先对查询树里所有被引用的关系加锁，防止
 *   这些关系的模式（schema）中途被其他会话修改。同时它还会顺带修正 JOIN RTE
 *   中对已删除列的引用（见"设计思想"第 3 点）。这是改写器、规划器和执行器能
 *   安全使用查询树的前置保证。
 *
 * 参数：
 *   parsetree           - 待加锁的查询树（Query），本函数可能就地修改它。
 *   forExecute          - 是否即将执行该查询。为 true 时按各 RTE 的 rellockmode
 *                         字段指定的锁模式加锁；为 false 时一律加 AccessShareLock
 *                         （该模式适合 ruleutils.c 等只需要模式稳定、不真正修改
 *                         数据的场景）。
 *   forUpdatePushedDown - 是否已有下推的 FOR [KEY] UPDATE/SHARE 作用于当前子查询，
 *                         此时所有关系至少需要 RowShareLock，并会相应提高 RTE 的
 *                         rellockmode 字段。顶层递归调用该参数恒为 false；当
 *                         forExecute 为 false 时该参数被忽略。
 *
 * 返回值：
 *   无（就地修改 parsetree）。
 *
 * 设计思想：
 *   1. 遍历当前查询层的整个 rtable：对 RTE_RELATION / RTE_GRAPH_TABLE 直接以相应
 *      锁模式打开关系（且不释放，一直持有到事务结束）；对 RTE_SUBQUERY 递归处理
 *      其内部子查询；对 RTE_JOIN 处理别名列；其余 RTE 类型忽略。
 *   2. 加锁顺序与视图展开顺序一致（先外层后内层），避免规则/视图展开过程中反复
 *      获取锁而造成死锁。
 *   3. 处理 JOIN 的已删除列：存储在规则里的 JOIN RTE 别名变量列表可能引用已删除
 *      的列（若该列未被查询其他位置显式引用，依赖机制不会认为它被规则使用，从而
 *      允许删除它）。为了让 get_rte_attribute_is_dropped() 正常工作，这里把引用
 *      已删除列的别名项替换为 NULL 指针。通过 strip_implicit_coercions 剥掉隐式
 *      强转、并用 curinputrte 缓存当前输入 RTE，避免重复取，从而规避 8.0 时代对
 *      嵌套 JOIN 递归检测造成的 O(N^2) 性能问题。
 *   4. 除 rtable 外，还会递归处理 cteList（WITH 子句）和表达式中的 SubLink 子查询
 *      （通过 acquireLocksOnSubLinks 遍历），但对后者不再深入 Query 节点，因为
 *      AcquireRewriteLocks 已经处理过其内部的子查询了。
 *   5. 该处理可能修改查询树，因此调用方通常应先对查询树做 copyObject() 得到当前
 *      内存上下文中的可写副本。
 * ============================================================================
 */
void
AcquireRewriteLocks(Query *parsetree,
					bool forExecute,
					bool forUpdatePushedDown)
{
	ListCell   *l;
	int			rt_index;
	acquireLocksOnSubLinks_context context;

	context.for_execute = forExecute;

	/*
	 * First, process RTEs of the current query level.
	 */
	rt_index = 0;
	foreach(l, parsetree->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(l);
		Relation	rel;
		LOCKMODE	lockmode;
		List	   *newaliasvars;
		Index		curinputvarno;
		RangeTblEntry *curinputrte;
		ListCell   *ll;

		++rt_index;
		switch (rte->rtekind)
		{
			case RTE_RELATION:
			case RTE_GRAPH_TABLE:

				/*
				 * Grab the appropriate lock type for the relation, and do not
				 * release it until end of transaction.  This protects the
				 * rewriter, planner, and executor against schema changes
				 * mid-query.
				 *
				 * If forExecute is false, ignore rellockmode and just use
				 * AccessShareLock.
				 */
				if (!forExecute)
					lockmode = AccessShareLock;
				else if (forUpdatePushedDown)
				{
					/* Upgrade RTE's lock mode to reflect pushed-down lock */
					if (rte->rellockmode == AccessShareLock)
						rte->rellockmode = RowShareLock;
					lockmode = rte->rellockmode;
				}
				else
					lockmode = rte->rellockmode;

				rel = relation_open(rte->relid, lockmode);

				/*
				 * While we have the relation open, update the RTE's relkind,
				 * just in case it changed since this rule was made.
				 */
				rte->relkind = rel->rd_rel->relkind;

				relation_close(rel, NoLock);
				break;

			case RTE_JOIN:

				/*
				 * Scan the join's alias var list to see if any columns have
				 * been dropped, and if so replace those Vars with null
				 * pointers.
				 *
				 * Since a join has only two inputs, we can expect to see
				 * multiple references to the same input RTE; optimize away
				 * multiple fetches.
				 */
				newaliasvars = NIL;
				curinputvarno = 0;
				curinputrte = NULL;
				foreach(ll, rte->joinaliasvars)
				{
					Var		   *aliasitem = (Var *) lfirst(ll);
					Var		   *aliasvar = aliasitem;

					/* Look through any implicit coercion */
					aliasvar = (Var *) strip_implicit_coercions((Node *) aliasvar);

					/*
					 * If the list item isn't a simple Var, then it must
					 * represent a merged column, ie a USING column, and so it
					 * couldn't possibly be dropped, since it's referenced in
					 * the join clause.  (Conceivably it could also be a null
					 * pointer already?  But that's OK too.)
					 */
					if (aliasvar && IsA(aliasvar, Var))
					{
						/*
						 * The elements of an alias list have to refer to
						 * earlier RTEs of the same rtable, because that's the
						 * order the planner builds things in.  So we already
						 * processed the referenced RTE, and so it's safe to
						 * use get_rte_attribute_is_dropped on it. (This might
						 * not hold after rewriting or planning, but it's OK
						 * to assume here.)
						 */
						Assert(aliasvar->varlevelsup == 0);
						if (aliasvar->varno != curinputvarno)
						{
							curinputvarno = aliasvar->varno;
							if (curinputvarno >= rt_index)
								elog(ERROR, "unexpected varno %d in JOIN RTE %d",
									 curinputvarno, rt_index);
							curinputrte = rt_fetch(curinputvarno,
												   parsetree->rtable);
						}
						if (get_rte_attribute_is_dropped(curinputrte,
														 aliasvar->varattno))
						{
							/* Replace the join alias item with a NULL */
							aliasitem = NULL;
						}
					}
					newaliasvars = lappend(newaliasvars, aliasitem);
				}
				rte->joinaliasvars = newaliasvars;
				break;

			case RTE_SUBQUERY:

				/*
				 * The subquery RTE itself is all right, but we have to
				 * recurse to process the represented subquery.
				 */
				AcquireRewriteLocks(rte->subquery,
									forExecute,
									(forUpdatePushedDown ||
									 get_parse_rowmark(parsetree, rt_index) != NULL));
				break;

			default:
				/* ignore other types of RTEs */
				break;
		}
	}

	/* Recurse into subqueries in WITH */
	foreach(l, parsetree->cteList)
	{
		CommonTableExpr *cte = (CommonTableExpr *) lfirst(l);

		AcquireRewriteLocks((Query *) cte->ctequery, forExecute, false);
	}

	/*
	 * Recurse into sublink subqueries, too.  But we already did the ones in
	 * the rtable and cteList.
	 */
	if (parsetree->hasSubLinks)
		query_tree_walker(parsetree, acquireLocksOnSubLinks, &context,
						  QTW_IGNORE_RC_SUBQUERIES);
}

/*
 * ============================================================================
 * 【中文注释】acquireLocksOnSubLinks —— 遍历表达式树为 SubLink 子查询加锁
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   作为 expression_tree_walker 的回调，在查询表达式中找到所有 SubLink 节点，
 *   并对每个 SubLink 内部的子查询调用 AcquireRewriteLocks 加锁。这是
 *   AcquireRewriteLocks 在 rtable 与 cteList 之外，对表达式（如 WHERE 条件、
 *   targetList）中出现的子链接子查询所做的补充处理。
 *
 * 参数：
 *   node    - 当前遍历到的节点；NULL 表示结束遍历（返回 false）。
 *   context - acquireLocksOnSubLinks_context，携带 AcquireRewriteLocks 的
 *             forExecute 参数，用于决定以何种锁模式加锁。
 *
 * 返回值：
 *   bool - 若返回 true 则终止遍历（本回调始终返回 false，即继续遍历）。
 *
 * 设计思想：
 *   1. 遇到 SubLink 节点时，先对其 subselect（子查询 Query）调用
 *      AcquireRewriteLocks，然后再继续遍历 SubLink 的 lefthand 参数表达式。
 *   2. 关键设计：刻意**不**递归进入 Query 节点，因为子查询内部的进一步处理已由
 *      那次对 AcquireRewriteLocks 的递归调用完成，若再进入会造成重复加锁或死锁
 *      误判。这一约定与 fireRIRonSubLink 的处理方式保持一致。
 *   3. 该函数也会被 rewriteRuleAction、CopyAndAddInvertedQual 以及 fireRIRrules
 *      中处理 RLS 条件时直接调用，用于对这些后加入的表达式补做加锁。
 * ============================================================================
 */
static bool
acquireLocksOnSubLinks(Node *node, acquireLocksOnSubLinks_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, SubLink))
	{
		SubLink    *sub = (SubLink *) node;

		/* Do what we came for */
		AcquireRewriteLocks((Query *) sub->subselect,
							context->for_execute,
							false);
		/* Fall through to process lefthand args of SubLink */
	}

	/*
	 * Do NOT recurse into Query nodes, because AcquireRewriteLocks already
	 * processed subselects of subselects for us.
	 */
	return expression_tree_walker(node, acquireLocksOnSubLinks, context);
}


/*
 * ============================================================================
 * 【中文注释】rewriteRuleAction —— 将规则动作与触发查询的限定条件合并并重写
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把一条规则的动作（rule_action，一个查询）改造为可以在触发查询（parsetree）
 *   的上下文中实际执行的查询：复制动作与限定条件、调整变量编号（varno）、合并
 *   rtable、拼接 JOIN 树、附加触发查询的限定条件、用触发查询的 targetList 替换
 *   动作中的 NEW 引用，并按需处理 RETURNING 子句。
 *
 * 参数：
 *   parsetree     - 触发规则的原始查询（只读使用，其 rtable 等会被复制后合并进
 *                   动作）。
 *   rule_action   - 规则的一个动作（Query），来自 relcache，是只读的，故本函数
 *                   先 copyObject。
 *   rule_qual     - 规则的 WHERE 条件；无条件规则为 NULL。
 *   rt_index      - 原始查询中结果关系（被规则命中的关系）在 rtable 中的下标。
 *   event         - 规则事件类型（CMD_INSERT/CMD_UPDATE/CMD_DELETE 等）。
 *   returning_flag- 输出参数：若本动作重写了 RETURNING 子句则置为 true（调用方
 *                   必须初始化为 false；若多个规则动作都带 RETURNING 会报错）。
 *
 * 返回值：
 *   Query * - 重写后的规则动作查询，可加入最终要执行的查询列表。
 *
 * 设计思想：
 *   1. 所有从 relcache 的拷贝都发生在当前内存上下文，且对 rtable、perminfos、
 *      CTE、jointree 等一律做深拷贝，保证最终查询树与主查询、与 relcache 不共享
 *      任何结构（规划器会破坏性地修改这些列表）。
 *   2. 变量编号调整是核心：用 OffsetVarNodes 把动作和条件的 varno 偏移 rt_length，
 *      使其能并入主查询 rtable；再把对 OLD（PRS2_OLD_VARNO）的引用改回 rt_index。
 *      若动作是 INSERT...SELECT，则要作用在 SELECT 部分（sub_action）而非顶层。
 *   3. 对动作中的子查询 RTE，若其包含引用本层（NEW/OLD）的 Var，自动打上 LATERAL
 *      标记，因为引用 NEW/OLD 的子查询本质上是横向（lateral）依赖。
 *   4. 合并 rtable 时把主查询的 rtable 放在动作 rtable 之前（RewriteQuery 依赖
 *      此顺序），同时合并 RTEPermissionInfo；INSTEAD 规则必须保留原查询的权限
 *      检查信息，以便对视图等做正确的权限校验。
 *   5. jointree 的合并规则：动作自身的 jointree 之前拼接主查询的 FROM 列表；当
 *      动作不使用 OLD、而规则条件或用户查询条件需要引用 OLD 时保留原 rt_index，
 *      否则去掉它，避免同一条目被 JOIN 两次。若动作是集合操作（setOperations）
 *      则无法拼接，报"conditional UNION/INTERSECT/EXCEPT"不支持错误。
 *   6. 处理 INSERT/UPDATE 时，先用触发查询的 targetList（以及为生成列构建的表达
 *      式）替换动作中的 new.attribute 引用——这要求生成列表达式本身先被重写一遍，
 *      因为它们内部也引用 new.attribute。
 *   7. RETURNING 的处理：触发查询没有 RETURNING 则丢弃动作的 RETURNING；否则用
 *      ReplaceVarsFromTargetList 把动作的 RETURNING 结果映射到触发查询期望的列，
 *      并把 OLD/NEW 别名替换为触发查询的别名。
 * ============================================================================
 */
static Query *
rewriteRuleAction(Query *parsetree,
				  Query *rule_action,
				  Node *rule_qual,
				  int rt_index,
				  CmdType event,
				  bool *returning_flag)
{
	int			current_varno,
				new_varno;
	int			rt_length;
	Query	   *sub_action;
	Query	  **sub_action_ptr;
	acquireLocksOnSubLinks_context context;
	ListCell   *lc;

	context.for_execute = true;

	/*
	 * Make modifiable copies of rule action and qual (what we're passed are
	 * the stored versions in the relcache; don't touch 'em!).
	 */
	rule_action = copyObject(rule_action);
	rule_qual = copyObject(rule_qual);

	/*
	 * Acquire necessary locks and fix any deleted JOIN RTE entries.
	 */
	AcquireRewriteLocks(rule_action, true, false);
	(void) acquireLocksOnSubLinks(rule_qual, &context);

	current_varno = rt_index;
	rt_length = list_length(parsetree->rtable);
	new_varno = PRS2_NEW_VARNO + rt_length;

	/*
	 * Adjust rule action and qual to offset its varnos, so that we can merge
	 * its rtable with the main parsetree's rtable.
	 *
	 * If the rule action is an INSERT...SELECT, the OLD/NEW rtable entries
	 * will be in the SELECT part, and we have to modify that rather than the
	 * top-level INSERT (kluge!).
	 */
	sub_action = getInsertSelectQuery(rule_action, &sub_action_ptr);

	OffsetVarNodes((Node *) sub_action, rt_length, 0);
	OffsetVarNodes(rule_qual, rt_length, 0);
	/* but references to OLD should point at original rt_index */
	ChangeVarNodes((Node *) sub_action,
				   PRS2_OLD_VARNO + rt_length, rt_index, 0);
	ChangeVarNodes(rule_qual,
				   PRS2_OLD_VARNO + rt_length, rt_index, 0);

	/*
	 * Mark any subquery RTEs in the rule action as LATERAL if they contain
	 * Vars referring to the current query level (references to NEW/OLD).
	 * Those really are lateral references, but we've historically not
	 * required users to mark such subqueries with LATERAL explicitly.  But
	 * the planner will complain if such Vars exist in a non-LATERAL subquery,
	 * so we have to fix things up here.
	 */
	foreach(lc, sub_action->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(lc);

		if (rte->rtekind == RTE_SUBQUERY && !rte->lateral &&
			contain_vars_of_level((Node *) rte->subquery, 1))
			rte->lateral = true;
	}

	/*
	 * Generate expanded rtable consisting of main parsetree's rtable plus
	 * rule action's rtable; this becomes the complete rtable for the rule
	 * action.  Some of the entries may be unused after we finish rewriting,
	 * but we leave them all in place to avoid having to adjust the query's
	 * varnos.  RT entries that are not referenced in the completed jointree
	 * will be ignored by the planner, so they do not affect query semantics.
	 *
	 * Also merge RTEPermissionInfo lists to ensure that all permissions are
	 * checked correctly.
	 *
	 * If the rule is INSTEAD, then the original query won't be executed at
	 * all, and so its rteperminfos must be preserved so that the executor
	 * will do the correct permissions checks on the relations referenced in
	 * it. This allows us to check that the caller has, say, insert-permission
	 * on a view, when the view is not semantically referenced at all in the
	 * resulting query.
	 *
	 * When a rule is not INSTEAD, the permissions checks done using the
	 * copied entries will be redundant with those done during execution of
	 * the original query, but we don't bother to treat that case differently.
	 *
	 * NOTE: because planner will destructively alter rtable and rteperminfos,
	 * we must ensure that rule action's lists are separate and shares no
	 * substructure with the main query's lists.  Hence do a deep copy here
	 * for both.
	 */
	{
		List	   *rtable_tail = sub_action->rtable;
		List	   *perminfos_tail = sub_action->rteperminfos;

		/*
		 * RewriteQuery relies on the fact that RT entries from the original
		 * query appear at the start of the expanded rtable, so we put the
		 * action's original table at the end of the list.
		 */
		sub_action->rtable = copyObject(parsetree->rtable);
		sub_action->rteperminfos = copyObject(parsetree->rteperminfos);
		CombineRangeTables(&sub_action->rtable, &sub_action->rteperminfos,
						   rtable_tail, perminfos_tail);
	}

	/*
	 * There could have been some SubLinks in parsetree's rtable, in which
	 * case we'd better mark the sub_action correctly.
	 */
	if (parsetree->hasSubLinks && !sub_action->hasSubLinks)
	{
		foreach(lc, parsetree->rtable)
		{
			RangeTblEntry *rte = (RangeTblEntry *) lfirst(lc);

			switch (rte->rtekind)
			{
				case RTE_RELATION:
					sub_action->hasSubLinks =
						checkExprHasSubLink((Node *) rte->tablesample);
					break;
				case RTE_FUNCTION:
					sub_action->hasSubLinks =
						checkExprHasSubLink((Node *) rte->functions);
					break;
				case RTE_TABLEFUNC:
					sub_action->hasSubLinks =
						checkExprHasSubLink((Node *) rte->tablefunc);
					break;
				case RTE_VALUES:
					sub_action->hasSubLinks =
						checkExprHasSubLink((Node *) rte->values_lists);
					break;
				default:
					/* other RTE types don't contain bare expressions */
					break;
			}
			sub_action->hasSubLinks |=
				checkExprHasSubLink((Node *) rte->securityQuals);
			if (sub_action->hasSubLinks)
				break;			/* no need to keep scanning rtable */
		}
	}

	/*
	 * Also, we might have absorbed some RTEs with RLS conditions into the
	 * sub_action.  If so, mark it as hasRowSecurity, whether or not those
	 * RTEs will be referenced after we finish rewriting.  (Note: currently
	 * this is a no-op because RLS conditions aren't added till later, but it
	 * seems like good future-proofing to do this anyway.)
	 */
	sub_action->hasRowSecurity |= parsetree->hasRowSecurity;

	/*
	 * Each rule action's jointree should be the main parsetree's jointree
	 * plus that rule's jointree, but usually *without* the original rtindex
	 * that we're replacing (if present, which it won't be for INSERT). Note
	 * that if the rule action refers to OLD, its jointree will add a
	 * reference to rt_index.  If the rule action doesn't refer to OLD, but
	 * either the rule_qual or the user query quals do, then we need to keep
	 * the original rtindex in the jointree to provide data for the quals.  We
	 * don't want the original rtindex to be joined twice, however, so avoid
	 * keeping it if the rule action mentions it.
	 *
	 * As above, the action's jointree must not share substructure with the
	 * main parsetree's.
	 */
	if (sub_action->commandType != CMD_UTILITY)
	{
		bool		keeporig;
		List	   *newjointree;

		Assert(sub_action->jointree != NULL);
		keeporig = (!rangeTableEntry_used((Node *) sub_action->jointree,
										  rt_index, 0)) &&
			(rangeTableEntry_used(rule_qual, rt_index, 0) ||
			 rangeTableEntry_used(parsetree->jointree->quals, rt_index, 0));
		newjointree = adjustJoinTreeList(parsetree, !keeporig, rt_index);
		if (newjointree != NIL)
		{
			/*
			 * If sub_action is a setop, manipulating its jointree will do no
			 * good at all, because the jointree is dummy.  (Perhaps someday
			 * we could push the joining and quals down to the member
			 * statements of the setop?)
			 */
			if (sub_action->setOperations != NULL)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("conditional UNION/INTERSECT/EXCEPT statements are not implemented")));

			sub_action->jointree->fromlist =
				list_concat(newjointree, sub_action->jointree->fromlist);

			/*
			 * There could have been some SubLinks in newjointree, in which
			 * case we'd better mark the sub_action correctly.
			 */
			if (parsetree->hasSubLinks && !sub_action->hasSubLinks)
				sub_action->hasSubLinks =
					checkExprHasSubLink((Node *) newjointree);
		}
	}

	/*
	 * If the original query has any CTEs, copy them into the rule action. But
	 * we don't need them for a utility action.
	 */
	if (parsetree->cteList != NIL && sub_action->commandType != CMD_UTILITY)
	{
		/*
		 * Annoying implementation restriction: because CTEs are identified by
		 * name within a cteList, we can't merge a CTE from the original query
		 * if it has the same name as any CTE in the rule action.
		 *
		 * This could possibly be fixed by using some sort of internally
		 * generated ID, instead of names, to link CTE RTEs to their CTEs.
		 * However, decompiling the results would be quite confusing; note the
		 * merge of hasRecursive flags below, which could change the apparent
		 * semantics of such redundantly-named CTEs.
		 */
		foreach(lc, parsetree->cteList)
		{
			CommonTableExpr *cte = (CommonTableExpr *) lfirst(lc);
			ListCell   *lc2;

			foreach(lc2, sub_action->cteList)
			{
				CommonTableExpr *cte2 = (CommonTableExpr *) lfirst(lc2);

				if (strcmp(cte->ctename, cte2->ctename) == 0)
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("WITH query name \"%s\" appears in both a rule action and the query being rewritten",
									cte->ctename)));
			}
		}

		/*
		 * OK, it's safe to combine the CTE lists.  Beware that RewriteQuery
		 * knows we concatenate the lists in this order.
		 */
		sub_action->cteList = list_concat(sub_action->cteList,
										  copyObject(parsetree->cteList));
		/* ... and don't forget about the associated flags */
		sub_action->hasRecursive |= parsetree->hasRecursive;
		sub_action->hasModifyingCTE |= parsetree->hasModifyingCTE;

		/*
		 * If rule_action is different from sub_action (i.e., the rule action
		 * is an INSERT...SELECT), then we might have just added some
		 * data-modifying CTEs that are not at the top query level.  This is
		 * disallowed by the parser and we mustn't generate such trees here
		 * either, so throw an error.
		 *
		 * Conceivably such cases could be supported by attaching the original
		 * query's CTEs to rule_action not sub_action.  But to do that, we'd
		 * have to increment ctelevelsup in RTEs and SubLinks copied from the
		 * original query.  For now, it doesn't seem worth the trouble.
		 */
		if (sub_action->hasModifyingCTE && rule_action != sub_action)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("INSERT ... SELECT rule actions are not supported for queries having data-modifying statements in WITH")));
	}

	/*
	 * Event Qualification forces copying of parsetree and splitting into two
	 * queries one w/rule_qual, one w/NOT rule_qual. Also add user query qual
	 * onto rule action
	 */
	AddQual(sub_action, rule_qual);

	AddQual(sub_action, parsetree->jointree->quals);

	/*
	 * Rewrite new.attribute with right hand side of target-list entry for
	 * appropriate field name in insert/update.
	 *
	 * KLUGE ALERT: since ReplaceVarsFromTargetList returns a mutated copy, we
	 * can't just apply it to sub_action; we have to remember to update the
	 * sublink inside rule_action, too.
	 */
	if ((event == CMD_INSERT || event == CMD_UPDATE) &&
		sub_action->commandType != CMD_UTILITY)
	{
		RangeTblEntry *new_rte = rt_fetch(new_varno, sub_action->rtable);
		Relation	new_rel;
		List	   *gen_cols;

		/*
		 * The target list does not contain entries for generated columns
		 * (they are removed by rewriteTargetListIU), so we must build entries
		 * for them here, so that new.gen_col can be rewritten correctly.
		 */
		new_rel = relation_open(new_rte->relid, NoLock);
		gen_cols = get_generated_columns(new_rel, new_varno, true);
		relation_close(new_rel, NoLock);

		/*
		 * The generated column expressions refer to new.attribute, so they
		 * must be rewritten before they can be used as replacements.
		 */
		gen_cols = (List *)
			ReplaceVarsFromTargetList((Node *) gen_cols,
									  new_varno,
									  0,
									  new_rte,
									  parsetree->targetList,
									  sub_action->resultRelation,
									  (event == CMD_UPDATE) ?
									  REPLACEVARS_CHANGE_VARNO :
									  REPLACEVARS_SUBSTITUTE_NULL,
									  current_varno,
									  &sub_action->hasSubLinks);

		/*
		 * Now rewrite new.attribute in sub_action, using both the target list
		 * and the rewritten generated column expressions.
		 */
		sub_action = (Query *)
			ReplaceVarsFromTargetList((Node *) sub_action,
									  new_varno,
									  0,
									  new_rte,
									  list_concat(gen_cols, parsetree->targetList),
									  sub_action->resultRelation,
									  (event == CMD_UPDATE) ?
									  REPLACEVARS_CHANGE_VARNO :
									  REPLACEVARS_SUBSTITUTE_NULL,
									  current_varno,
									  NULL);
		if (sub_action_ptr)
			*sub_action_ptr = sub_action;
		else
			rule_action = sub_action;
	}

	/*
	 * If rule_action is INSERT .. ON CONFLICT DO SELECT, the parser should
	 * have verified that it has a RETURNING clause, but we must also check
	 * that the triggering query has a RETURNING clause.
	 */
	if (rule_action->onConflict &&
		rule_action->onConflict->action == ONCONFLICT_SELECT &&
		(!rule_action->returningList || !parsetree->returningList))
		ereport(ERROR,
				errcode(ERRCODE_SYNTAX_ERROR),
				errmsg("ON CONFLICT DO SELECT requires a RETURNING clause"),
				errdetail("A rule action is INSERT ... ON CONFLICT DO SELECT, which requires a RETURNING clause."));

	/*
	 * If rule_action has a RETURNING clause, then either throw it away if the
	 * triggering query has no RETURNING clause, or rewrite it to emit what
	 * the triggering query's RETURNING clause asks for.  Throw an error if
	 * more than one rule has a RETURNING clause.
	 */
	if (!parsetree->returningList)
		rule_action->returningList = NIL;
	else if (rule_action->returningList)
	{
		if (*returning_flag)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("cannot have RETURNING lists in multiple rules")));
		*returning_flag = true;
		rule_action->returningList = (List *)
			ReplaceVarsFromTargetList((Node *) parsetree->returningList,
									  parsetree->resultRelation,
									  0,
									  rt_fetch(parsetree->resultRelation,
											   parsetree->rtable),
									  rule_action->returningList,
									  rule_action->resultRelation,
									  REPLACEVARS_REPORT_ERROR,
									  0,
									  &rule_action->hasSubLinks);

		/* use triggering query's aliases for OLD and NEW in RETURNING list */
		rule_action->returningOldAlias = parsetree->returningOldAlias;
		rule_action->returningNewAlias = parsetree->returningNewAlias;

		/*
		 * There could have been some SubLinks in parsetree's returningList,
		 * in which case we'd better mark the rule_action correctly.
		 */
		if (parsetree->hasSubLinks && !rule_action->hasSubLinks)
			rule_action->hasSubLinks =
				checkExprHasSubLink((Node *) rule_action->returningList);
	}

	return rule_action;
}

/*
 * ============================================================================
 * 【中文注释】adjustJoinTreeList —— 复制 FROM 列表并可选地移除指定结果关系条目
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   深拷贝主查询 jointree 的 fromlist，供规则动作使用；并可选地从副本中删除
 *   指定的 rt_index（作为顶层 Join 项出现时）。这样规则动作就拥有一个独立的
 *   FROM 列表，同时避免把被替换的原关系再次 JOIN 进来。
 *
 * 参数：
 *   parsetree - 原始查询，取其 jointree->fromlist 作为拷贝来源。
 *   removert  - 是否尝试移除给定 rt_index 对应的顶层 RangeTblRef。
 *   rt_index  - 需要从 fromlist 中移除的 rtable 下标。
 *
 * 返回值：
 *   List * - 与原始列表不共享任何节点的新 fromlist。
 *
 * 设计思想：
 *   1. 只用 copyObject 复制顶层列表并做深拷贝，保证与主查询完全隔离（规则动作
 *      需要独立、可被规划器随意修改的 jointree）。
 *   2. 只检查顶层项（IsA RangeTblRef）而不深入 JOIN 内部：因为期望被移除的是
 *      UPDATE/DELETE 的目标关系，它只会以顶层 FROM 项的形式出现。
 *   3. 若从列表中删除了一个项则立即 break，因为目标关系在 FROM 中只出现一次。
 * ============================================================================
 */
static List *
adjustJoinTreeList(Query *parsetree, bool removert, int rt_index)
{
	List	   *newjointree = copyObject(parsetree->jointree->fromlist);
	ListCell   *l;

	if (removert)
	{
		foreach(l, newjointree)
		{
			RangeTblRef *rtr = lfirst(l);

			if (IsA(rtr, RangeTblRef) &&
				rtr->rtindex == rt_index)
			{
				newjointree = foreach_delete_current(newjointree, l);
				break;
			}
		}
	}
	return newjointree;
}


/*
 * ============================================================================
 * 【中文注释】rewriteTargetListIU —— 把 INSERT/UPDATE 的 targetList 重写为标准形式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对 INSERT/UPDATE（以及 MERGE 中各动作、ON CONFLICT 的辅助 UPDATE）的目标列表
 *   做标准化处理，主要职责有四：
 *     (1) 为 INSERT 中未赋值的列补充默认值表达式（无默认值的列不补，留给规划器
 *         填 NULL），并把显式的 DEFAULT 占位符替换为真正的默认值表达式；
 *     (2) 把对同一列的多重赋值（如数组/记录的子字段更新）合并为单个赋值表达式；
 *     (3) 按 resno 对非 junk 项排序、junk 项排在最后，并重新编号；
 *     (4) 校验并处理 identity（自增）列与生成列（generated）的特殊约束。
 *
 * 参数：
 *   targetList           - 待重写的目标列表（INSERT 主 targetList、ON CONFLICT
 *                          辅助列表或 MERGE 动作 targetList 之一）。
 *   commandType          - CMD_INSERT 或 CMD_UPDATE（决定默认值/NULL 的处理策略）。
 *   override             - OVERRIDING 子句类型（OVERRIDING USER/SYSTEM VALUE），
 *                          仅对 identity 列的默认值处理有影响。
 *   target_relation      - 目标关系的 Relation 描述符（用于读取列属性、默认值）。
 *   values_rte           - 多行 INSERT 时承载 VALUES 列表的 RTE，否则为 NULL。
 *   values_rte_index     - values_rte 在 rtable 中的下标（无则忽略）。
 *   unused_values_attrnos- 输出参数：被默认值表达式替代后不再使用的 VALUES 列
 *                          的编号集合（Bitmapset），供 rewriteValuesRTE 把其中
 *                          残留的 DEFAULT 项改成 NULL；调用方需初始化为 NULL。
 *
 * 返回值：
 *   List * - 重写后的目标列表。
 *
 * 设计思想：
 *   1. 性能优化：先把非 junk 的 TLE 按 resno 存进数组 new_tles[]，再按属性号顺序
 *      扫描生成输出列表，避免对大列数表做 O(N^2) 处理；junk 项在第一次扫描时
 *      单独收集、重新编号后拼在输出列表末尾。
 *   2. 已删除的属性（attisdropped）一律跳过，保证重写结果不引用已删除列。
 *   3. 默认值判定：INSERT 且无对应 TLE，或 TLE 表达式是 SetToDefault 占位符时，
 *      需要生成默认值表达式。对 GENERATED ALWAYS 的 identity 列与生成列，非默认
 *      值插入会被禁止；若其值来自 VALUES RTE，则用 findDefaultOnlyColumns 检查该
 *      列是否全为 DEFAULT，是则允许默认。UPDATE 不允许 OVERRIDING 子句，对
 *      identity/生成列只允许显式设默认。
 *   4. 生成列：virtual 生成列存 NULL 值、stored 生成列由执行器随后计算，因此这里
 *      一律不为其保留 TLE（new_tle = NULL）。
 *   5. 无默认值时：INSERT 直接省略 TLE（规划器自会补 NULL）；UPDATE 则必须显式
 *      构造 NULL（经 coerce_null_to_domain 处理域约束）。
 *   6. 该函数必须在触发规则之前完成，否则规则对 NEW.foo 的引用会得到错误或不完整
 *      的替换结果；排序本身对改写不是必须的，但能让规划器受益，且几乎零成本。
 * ============================================================================
 */
static List *
rewriteTargetListIU(List *targetList,
					CmdType commandType,
					OverridingKind override,
					Relation target_relation,
					RangeTblEntry *values_rte,
					int values_rte_index,
					Bitmapset **unused_values_attrnos)
{
	TargetEntry **new_tles;
	List	   *new_tlist = NIL;
	List	   *junk_tlist = NIL;
	Form_pg_attribute att_tup;
	int			attrno,
				next_junk_attrno,
				numattrs;
	ListCell   *temp;
	Bitmapset  *default_only_cols = NULL;

	/*
	 * We process the normal (non-junk) attributes by scanning the input tlist
	 * once and transferring TLEs into an array, then scanning the array to
	 * build an output tlist.  This avoids O(N^2) behavior for large numbers
	 * of attributes.
	 *
	 * Junk attributes are tossed into a separate list during the same tlist
	 * scan, then appended to the reconstructed tlist.
	 */
	numattrs = RelationGetNumberOfAttributes(target_relation);
	new_tles = (TargetEntry **) palloc0(numattrs * sizeof(TargetEntry *));
	next_junk_attrno = numattrs + 1;

	foreach(temp, targetList)
	{
		TargetEntry *old_tle = (TargetEntry *) lfirst(temp);

		if (!old_tle->resjunk)
		{
			/* Normal attr: stash it into new_tles[] */
			attrno = old_tle->resno;
			if (attrno < 1 || attrno > numattrs)
				elog(ERROR, "bogus resno %d in targetlist", attrno);
			att_tup = TupleDescAttr(target_relation->rd_att, attrno - 1);

			/* We can (and must) ignore deleted attributes */
			if (att_tup->attisdropped)
				continue;

			/* Merge with any prior assignment to same attribute */
			new_tles[attrno - 1] =
				process_matched_tle(old_tle,
									new_tles[attrno - 1],
									NameStr(att_tup->attname));
		}
		else
		{
			/*
			 * Copy all resjunk tlist entries to junk_tlist, and assign them
			 * resnos above the last real resno.
			 *
			 * Typical junk entries include ORDER BY or GROUP BY expressions
			 * (are these actually possible in an INSERT or UPDATE?), system
			 * attribute references, etc.
			 */

			/* Get the resno right, but don't copy unnecessarily */
			if (old_tle->resno != next_junk_attrno)
			{
				old_tle = flatCopyTargetEntry(old_tle);
				old_tle->resno = next_junk_attrno;
			}
			junk_tlist = lappend(junk_tlist, old_tle);
			next_junk_attrno++;
		}
	}

	for (attrno = 1; attrno <= numattrs; attrno++)
	{
		TargetEntry *new_tle = new_tles[attrno - 1];
		bool		apply_default;

		att_tup = TupleDescAttr(target_relation->rd_att, attrno - 1);

		/* We can (and must) ignore deleted attributes */
		if (att_tup->attisdropped)
			continue;

		/*
		 * Handle the two cases where we need to insert a default expression:
		 * it's an INSERT and there's no tlist entry for the column, or the
		 * tlist entry is a DEFAULT placeholder node.
		 */
		apply_default = ((new_tle == NULL && commandType == CMD_INSERT) ||
						 (new_tle && new_tle->expr && IsA(new_tle->expr, SetToDefault)));

		if (commandType == CMD_INSERT)
		{
			int			values_attrno = 0;

			/* Source attribute number for values that come from a VALUES RTE */
			if (values_rte && new_tle && IsA(new_tle->expr, Var))
			{
				Var		   *var = (Var *) new_tle->expr;

				if (var->varno == values_rte_index)
					values_attrno = var->varattno;
			}

			/*
			 * Can only insert DEFAULT into GENERATED ALWAYS identity columns,
			 * unless either OVERRIDING USER VALUE or OVERRIDING SYSTEM VALUE
			 * is specified.
			 */
			if (att_tup->attidentity == ATTRIBUTE_IDENTITY_ALWAYS && !apply_default)
			{
				if (override == OVERRIDING_USER_VALUE)
					apply_default = true;
				else if (override != OVERRIDING_SYSTEM_VALUE)
				{
					/*
					 * If this column's values come from a VALUES RTE, test
					 * whether it contains only SetToDefault items.  Since the
					 * VALUES list might be quite large, we arrange to only
					 * scan it once.
					 */
					if (values_attrno != 0)
					{
						if (default_only_cols == NULL)
							default_only_cols = findDefaultOnlyColumns(values_rte);

						if (bms_is_member(values_attrno, default_only_cols))
							apply_default = true;
					}

					if (!apply_default)
						ereport(ERROR,
								(errcode(ERRCODE_GENERATED_ALWAYS),
								 errmsg("cannot insert a non-DEFAULT value into column \"%s\"",
										NameStr(att_tup->attname)),
								 errdetail("Column \"%s\" is an identity column defined as GENERATED ALWAYS.",
										   NameStr(att_tup->attname)),
								 errhint("Use OVERRIDING SYSTEM VALUE to override.")));
				}
			}

			/*
			 * Although inserting into a GENERATED BY DEFAULT identity column
			 * is allowed, apply the default if OVERRIDING USER VALUE is
			 * specified.
			 */
			if (att_tup->attidentity == ATTRIBUTE_IDENTITY_BY_DEFAULT &&
				override == OVERRIDING_USER_VALUE)
				apply_default = true;

			/*
			 * Can only insert DEFAULT into generated columns.  (The
			 * OVERRIDING clause does not apply to generated columns, so we
			 * don't consider it here.)
			 */
			if (att_tup->attgenerated && !apply_default)
			{
				/*
				 * If this column's values come from a VALUES RTE, test
				 * whether it contains only SetToDefault items, as above.
				 */
				if (values_attrno != 0)
				{
					if (default_only_cols == NULL)
						default_only_cols = findDefaultOnlyColumns(values_rte);

					if (bms_is_member(values_attrno, default_only_cols))
						apply_default = true;
				}

				if (!apply_default)
					ereport(ERROR,
							(errcode(ERRCODE_GENERATED_ALWAYS),
							 errmsg("cannot insert a non-DEFAULT value into column \"%s\"",
									NameStr(att_tup->attname)),
							 errdetail("Column \"%s\" is a generated column.",
									   NameStr(att_tup->attname))));
			}

			/*
			 * For an INSERT from a VALUES RTE, return the attribute numbers
			 * of any VALUES columns that will no longer be used (due to the
			 * targetlist entry being replaced by a default expression).
			 */
			if (values_attrno != 0 && apply_default && unused_values_attrnos)
				*unused_values_attrnos = bms_add_member(*unused_values_attrnos,
														values_attrno);
		}

		/*
		 * Updates to identity and generated columns follow the same rules as
		 * above, except that UPDATE doesn't admit OVERRIDING clauses.  Also,
		 * the source can't be a VALUES RTE, so we needn't consider that.
		 */
		if (commandType == CMD_UPDATE)
		{
			if (att_tup->attidentity == ATTRIBUTE_IDENTITY_ALWAYS &&
				new_tle && !apply_default)
				ereport(ERROR,
						(errcode(ERRCODE_GENERATED_ALWAYS),
						 errmsg("column \"%s\" can only be updated to DEFAULT",
								NameStr(att_tup->attname)),
						 errdetail("Column \"%s\" is an identity column defined as GENERATED ALWAYS.",
								   NameStr(att_tup->attname))));

			if (att_tup->attgenerated && new_tle && !apply_default)
				ereport(ERROR,
						(errcode(ERRCODE_GENERATED_ALWAYS),
						 errmsg("column \"%s\" can only be updated to DEFAULT",
								NameStr(att_tup->attname)),
						 errdetail("Column \"%s\" is a generated column.",
								   NameStr(att_tup->attname))));
		}

		if (att_tup->attgenerated)
		{
			/*
			 * virtual generated column stores a null value; stored generated
			 * column will be fixed in executor
			 */
			new_tle = NULL;
		}
		else if (apply_default)
		{
			Node	   *new_expr;

			new_expr = build_column_default(target_relation, attrno);

			/*
			 * If there is no default (ie, default is effectively NULL), we
			 * can omit the tlist entry in the INSERT case, since the planner
			 * can insert a NULL for itself, and there's no point in spending
			 * any more rewriter cycles on the entry.  But in the UPDATE case
			 * we've got to explicitly set the column to NULL.
			 */
			if (!new_expr)
			{
				if (commandType == CMD_INSERT)
					new_tle = NULL;
				else
					new_expr = coerce_null_to_domain(att_tup->atttypid,
													 att_tup->atttypmod,
													 att_tup->attcollation,
													 att_tup->attlen,
													 att_tup->attbyval);
			}

			if (new_expr)
				new_tle = makeTargetEntry((Expr *) new_expr,
										  attrno,
										  pstrdup(NameStr(att_tup->attname)),
										  false);
		}

		if (new_tle)
			new_tlist = lappend(new_tlist, new_tle);
	}

	pfree(new_tles);

	return list_concat(new_tlist, junk_tlist);
}


/*
 * ============================================================================
 * 【中文注释】process_matched_tle —— 把同一列的多个赋值 TLE 合并成一个赋值表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   当目标列表对同一目标属性出现多个赋值时（如 UPDATE 中对数组下标或记录字段
 *   的多处赋值），把这些赋值合并为单个嵌套的 FieldStore / SubscriptingRef 表达
 *   式，保证赋值按书写顺序自左向右生效；若无法合并则报错。
 *
 * 参数：
 *   src_tle   - 新遇到的赋值 TLE（较新的赋值）。
 *   prior_tle - 之前已为该属性合并出的 TLE；NULL 表示这是首次赋值。
 *   attrName  - 目标属性名，仅用于错误信息。
 *
 * 返回值：
 *   TargetEntry * - 合并后的 TLE（若 prior_tle 为 NULL 则原样返回 src_tle）。
 *
 * 设计思想：
 *   1. 首次赋值直接返回 src_tle；多次赋值才需要合并。
 *   2. 允许合并的条件：两个表达式都是 FieldStore 或 SubscriptingRef 赋值操作。
 *      例如 "UPDATE tab SET col.f1 = x, col.f2 = y" 可合并为
 *      FieldStore(FieldStore(col, f1, x), f2, y)，左起表达式放在最内层以保持
 *      从左到右的语义。对两个 FieldStore 可以合并成单个含多个字段的 FieldStore，
 *      涉及 SubscriptingRef 时则必须嵌套。
 *   3. 若目标列是域（domain）类型，每个赋值外层会包一层 CoerceToDomain（两侧
 *      resulttype 必须一致才可合并）；合并时先剥离 CoerceToDomain、组合完内部
 *      表达式后再重新套上，这样域的检查只需在所有子字段更新完成后做一次。
 *   4. 合并前用 get_assignment_input 取得各赋值的"底层输入"，要求二者完全相同
 *      （即引用的原始 Var 一致），否则说明赋值对象不是同一列，报
 *      "multiple assignments to same column" 错误。
 *   5. prior 可能是多次合并后的嵌套结构，因此循环剥到最底层再与 src 的输入比较。
 *   6. 结果通过 flatCopyTargetEntry 拷贝 src_tle 的结构、仅替换其 expr。
 * ============================================================================
 */
static TargetEntry *
process_matched_tle(TargetEntry *src_tle,
					TargetEntry *prior_tle,
					const char *attrName)
{
	TargetEntry *result;
	CoerceToDomain *coerce_expr = NULL;
	Node	   *src_expr;
	Node	   *prior_expr;
	Node	   *src_input;
	Node	   *prior_input;
	Node	   *priorbottom;
	Node	   *newexpr;

	if (prior_tle == NULL)
	{
		/*
		 * Normal case where this is the first assignment to the attribute.
		 */
		return src_tle;
	}

	/*----------
	 * Multiple assignments to same attribute.  Allow only if all are
	 * FieldStore or SubscriptingRef assignment operations.  This is a bit
	 * tricky because what we may actually be looking at is a nest of
	 * such nodes; consider
	 *		UPDATE tab SET col.fld1.subfld1 = x, col.fld2.subfld2 = y
	 * The two expressions produced by the parser will look like
	 *		FieldStore(col, fld1, FieldStore(placeholder, subfld1, x))
	 *		FieldStore(col, fld2, FieldStore(placeholder, subfld2, y))
	 * However, we can ignore the substructure and just consider the top
	 * FieldStore or SubscriptingRef from each assignment, because it works to
	 * combine these as
	 *		FieldStore(FieldStore(col, fld1,
	 *							  FieldStore(placeholder, subfld1, x)),
	 *				   fld2, FieldStore(placeholder, subfld2, y))
	 * Note the leftmost expression goes on the inside so that the
	 * assignments appear to occur left-to-right.
	 *
	 * For FieldStore, instead of nesting we can generate a single
	 * FieldStore with multiple target fields.  We must nest when
	 * SubscriptingRefs are involved though.
	 *
	 * As a further complication, the destination column might be a domain,
	 * resulting in each assignment containing a CoerceToDomain node over a
	 * FieldStore or SubscriptingRef.  These should have matching target
	 * domains, so we strip them and reconstitute a single CoerceToDomain over
	 * the combined FieldStore/SubscriptingRef nodes.  (Notice that this has
	 * the result that the domain's checks are applied only after we do all
	 * the field or element updates, not after each one.  This is desirable.)
	 *----------
	 */
	src_expr = (Node *) src_tle->expr;
	prior_expr = (Node *) prior_tle->expr;

	if (src_expr && IsA(src_expr, CoerceToDomain) &&
		prior_expr && IsA(prior_expr, CoerceToDomain) &&
		((CoerceToDomain *) src_expr)->resulttype ==
		((CoerceToDomain *) prior_expr)->resulttype)
	{
		/* we assume without checking that resulttypmod/resultcollid match */
		coerce_expr = (CoerceToDomain *) src_expr;
		src_expr = (Node *) ((CoerceToDomain *) src_expr)->arg;
		prior_expr = (Node *) ((CoerceToDomain *) prior_expr)->arg;
	}

	src_input = get_assignment_input(src_expr);
	prior_input = get_assignment_input(prior_expr);
	if (src_input == NULL ||
		prior_input == NULL ||
		exprType(src_expr) != exprType(prior_expr))
		ereport(ERROR,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("multiple assignments to same column \"%s\"",
						attrName)));

	/*
	 * Prior TLE could be a nest of assignments if we do this more than once.
	 */
	priorbottom = prior_input;
	for (;;)
	{
		Node	   *newbottom = get_assignment_input(priorbottom);

		if (newbottom == NULL)
			break;				/* found the original Var reference */
		priorbottom = newbottom;
	}
	if (!equal(priorbottom, src_input))
		ereport(ERROR,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("multiple assignments to same column \"%s\"",
						attrName)));

	/*
	 * Looks OK to nest 'em.
	 */
	if (IsA(src_expr, FieldStore))
	{
		FieldStore *fstore = makeNode(FieldStore);

		if (IsA(prior_expr, FieldStore))
		{
			/* combine the two */
			memcpy(fstore, prior_expr, sizeof(FieldStore));
			fstore->newvals =
				list_concat_copy(((FieldStore *) prior_expr)->newvals,
								 ((FieldStore *) src_expr)->newvals);
			fstore->fieldnums =
				list_concat_copy(((FieldStore *) prior_expr)->fieldnums,
								 ((FieldStore *) src_expr)->fieldnums);
		}
		else
		{
			/* general case, just nest 'em */
			memcpy(fstore, src_expr, sizeof(FieldStore));
			fstore->arg = (Expr *) prior_expr;
		}
		newexpr = (Node *) fstore;
	}
	else if (IsA(src_expr, SubscriptingRef))
	{
		SubscriptingRef *sbsref = makeNode(SubscriptingRef);

		memcpy(sbsref, src_expr, sizeof(SubscriptingRef));
		sbsref->refexpr = (Expr *) prior_expr;
		newexpr = (Node *) sbsref;
	}
	else
	{
		elog(ERROR, "cannot happen");
		newexpr = NULL;
	}

	if (coerce_expr)
	{
		/* put back the CoerceToDomain */
		CoerceToDomain *newcoerce = makeNode(CoerceToDomain);

		memcpy(newcoerce, coerce_expr, sizeof(CoerceToDomain));
		newcoerce->arg = (Expr *) newexpr;
		newexpr = (Node *) newcoerce;
	}

	result = flatCopyTargetEntry(src_tle);
	result->expr = (Expr *) newexpr;
	return result;
}

/*
 * ============================================================================
 * 【中文注释】get_assignment_input —— 取赋值节点的输入表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判断给定节点是否为"赋值操作"节点（FieldStore 或带赋值下标的 SubscriptingRef），
 *   若是则返回其输入（被赋值的底层表达式），否则返回 NULL。它是 process_matched_tle
 *   合并多重赋值时的核心辅助工具。
 *
 * 参数：
 *   node - 待检查的表达式节点。
 *
 * 返回值：
 *   Node * - FieldStore 返回其 arg；带 refassgnexpr 的 SubscriptingRef 返回其
 *            refexpr；其他情况（含无赋值的 SubscriptingRef）返回 NULL。
 *
 * 设计思想：
 *   1. FieldStore（记录字段赋值）直接返回 fstore->arg 作为输入。
 *   2. SubscriptingRef 只有在其 refassgnexpr 非空（确属赋值语义）时才视为赋值
 *      操作并返回 refexpr，否则返回 NULL，避免把普通下标读取误判为赋值。
 *   3. 通过"返回 NULL"与"返回表达式"两种结果区分叶子（原始 Var 引用）与可继续
 *      下钻的嵌套赋值，供 process_matched_tle 循环剥离嵌套。
 * ============================================================================
 */
static Node *
get_assignment_input(Node *node)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, FieldStore))
	{
		FieldStore *fstore = (FieldStore *) node;

		return (Node *) fstore->arg;
	}
	else if (IsA(node, SubscriptingRef))
	{
		SubscriptingRef *sbsref = (SubscriptingRef *) node;

		if (sbsref->refassgnexpr == NULL)
			return NULL;

		return (Node *) sbsref->refexpr;
	}

	return NULL;
}

/*
 * ============================================================================
 * 【中文注释】build_column_default —— 构造某列的默认值表达式树
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为指定关系列的默认值构造表达式树：依次考虑 identity 列、列级 DEFAULT、类型级
 *   默认值，并做必要的类型强制转换（coerce）。若该列没有任何默认值则返回 NULL。
 *
 * 参数：
 *   rel    - 目标关系的 Relation 描述符。
 *   attrno - 目标属性号（从 1 开始）。
 *
 * 返回值：
 *   Node * - 默认值表达式；无默认值时返回 NULL。
 *
 * 设计思想：
 *   1. 优先处理 identity 列（attidentity 非 0）：构造一个 NextValueExpr 节点，
 *      内含对应序列的 OID（由 getIdentitySequence 求得），执行时从序列取下一个值。
 *   2. 其次取列级 DEFAULT（atthasdef 置位时通过 TupleDescGetDefault 从 pg_attrdef
 *      取已解析的表达式）；没有列级默认时再取类型级默认（get_typdefault），但
 *      生成列（attgenerated）不享受类型级默认。
 *   3. 取到表达式后调用 coerce_to_target_type 强制转换到目标列类型（含 typmod），
 *      因为域类型的默认值可能存在类型不完全匹配的边角情况；此处理与解析器对普通
 *      赋值表达式的处理（transformAssignedExpr）保持一致。转换失败时报类型不匹配
 *      错误。
 *   4. 找不到任何默认值时返回 NULL，调用方（如 rewriteTargetListIU）据此决定是
 *      省略 TLE（INSERT）还是显式补 NULL（UPDATE）。
 * ============================================================================
 */
Node *
build_column_default(Relation rel, int attrno)
{
	TupleDesc	rd_att = rel->rd_att;
	Form_pg_attribute att_tup = TupleDescAttr(rd_att, attrno - 1);
	Oid			atttype = att_tup->atttypid;
	int32		atttypmod = att_tup->atttypmod;
	Node	   *expr = NULL;
	Oid			exprtype;

	if (att_tup->attidentity)
	{
		NextValueExpr *nve = makeNode(NextValueExpr);

		nve->seqid = getIdentitySequence(rel, attrno, false);
		nve->typeId = att_tup->atttypid;

		return (Node *) nve;
	}

	/*
	 * If relation has a default for this column, fetch that expression.
	 */
	if (att_tup->atthasdef)
	{
		expr = TupleDescGetDefault(rd_att, attrno);
		if (expr == NULL)
			elog(ERROR, "default expression not found for attribute %d of relation \"%s\"",
				 attrno, RelationGetRelationName(rel));
	}

	/*
	 * No per-column default, so look for a default for the type itself.  But
	 * not for generated columns.
	 */
	if (expr == NULL && !att_tup->attgenerated)
		expr = get_typdefault(atttype);

	if (expr == NULL)
		return NULL;			/* No default anywhere */

	/*
	 * Make sure the value is coerced to the target column type; this will
	 * generally be true already, but there seem to be some corner cases
	 * involving domain defaults where it might not be true. This should match
	 * the parser's processing of non-defaulted expressions --- see
	 * transformAssignedExpr().
	 */
	exprtype = exprType(expr);

	expr = coerce_to_target_type(NULL,	/* no UNKNOWN params here */
								 expr, exprtype,
								 atttype, atttypmod,
								 COERCION_ASSIGNMENT,
								 COERCE_IMPLICIT_CAST,
								 -1);
	if (expr == NULL)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("column \"%s\" is of type %s"
						" but default expression is of type %s",
						NameStr(att_tup->attname),
						format_type_be(atttype),
						format_type_be(exprtype)),
				 errhint("You will need to rewrite or cast the expression.")));

	return expr;
}


/*
 * ============================================================================
 * 【中文注释】searchForDefault —— 判断 VALUES RTE 中是否含有 DEFAULT 项
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   扫描 VALUES RTE 的所有 VALUES 行（values_lists），若任一单元格是
 *   SetToDefault 占位符（表示该处显式写了 DEFAULT）则返回 true。用于 rewriteValuesRTE
 *   预先判断是否有必要重建整个 VALUES 列表，避免对大 VALUES 列表做无谓开销。
 *
 * 参数：
 *   rte - RTE_VALUES 类型的 RangeTblEntry。
 *
 * 返回值：
 *   bool - 存在任何 SetToDefault 项返回 true，否则返回 false。
 *
 * 设计思想：
 *   重建所有 VALUES 列表在数据量大时开销较高，因此先做一次只读扫描；若整个
 *   VALUES RTE 中没有 DEFAULT 项，rewriteValuesRTE 可以直接返回、不做任何修改。
 * ============================================================================
 */
static bool
searchForDefault(RangeTblEntry *rte)
{
	ListCell   *lc;

	foreach(lc, rte->values_lists)
	{
		List	   *sublist = (List *) lfirst(lc);
		ListCell   *lc2;

		foreach(lc2, sublist)
		{
			Node	   *col = (Node *) lfirst(lc2);

			if (IsA(col, SetToDefault))
				return true;
		}
	}
	return false;
}


/*
 * ============================================================================
 * 【中文注释】findDefaultOnlyColumns —— 找出 VALUES RTE 中"全为 DEFAULT"的列
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在 VALUES RTE 的每一行中，找出所有单元格都写 DEFAULT（SetToDefault）的那些
 *   列，以 Bitmapset（键为列号，从 1 开始）返回这些列的编号。供 rewriteTargetListIU
 *   判断 identity/生成列的值是否全部来自 DEFAULT，从而决定是否允许插入。
 *
 * 参数：
 *   rte - RTE_VALUES 类型的 RangeTblEntry。
 *
 * 返回值：
 *   Bitmapset * - 全为 DEFAULT 的列的编号集合。
 *
 * 设计思想：
 *   1. 用首行初始化结果集合（首行中凡 DEFAULT 的列都加入），随后每一行只做集合
 *      收缩：某列出现非 DEFAULT 值就从集合中移除。
 *   2. 一旦结果集合为空即可提前终止（没有任何列能保持"全 DEFAULT"）。
 *   3. 该函数把多行扫描成本摊销到一次遍历，因为 VALUES 列表可能非常大，
 *      rewriteTargetListIU 中刻意只在需要时才调用它（default_only_cols 延迟计算）。
 * ============================================================================
 */
static Bitmapset *
findDefaultOnlyColumns(RangeTblEntry *rte)
{
	Bitmapset  *default_only_cols = NULL;
	ListCell   *lc;

	foreach(lc, rte->values_lists)
	{
		List	   *sublist = (List *) lfirst(lc);
		ListCell   *lc2;
		int			i;

		if (default_only_cols == NULL)
		{
			/* Populate the initial result bitmap from the first row */
			i = 0;
			foreach(lc2, sublist)
			{
				Node	   *col = (Node *) lfirst(lc2);

				i++;
				if (IsA(col, SetToDefault))
					default_only_cols = bms_add_member(default_only_cols, i);
			}
		}
		else
		{
			/* Update the result bitmap from this next row */
			i = 0;
			foreach(lc2, sublist)
			{
				Node	   *col = (Node *) lfirst(lc2);

				i++;
				if (!IsA(col, SetToDefault))
					default_only_cols = bms_del_member(default_only_cols, i);
			}
		}

		/*
		 * If no column in the rows read so far contains only DEFAULT items,
		 * we are done.
		 */
		if (bms_is_empty(default_only_cols))
			break;
	}

	return default_only_cols;
}


/*
 * ============================================================================
 * 【中文注释】rewriteValuesRTE —— 替换 INSERT ... VALUES 中 VALUES RTE 的 DEFAULT 项
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   处理多行 INSERT ... VALUES（带 VALUES RTE）时，把 VALUES 列表中的
 *   SetToDefault（DEFAULT）占位符替换为合适的默认值表达式。目标列表自身的重写
 *   由 rewriteTargetListIU 完成，本函数只负责 VALUES 表达式列表内部的替换。
 *
 * 参数：
 *   parsetree      - 正在改写的 INSERT 查询。
 *   rte             - VALUES RTE（将被就地修改其 values_lists）。
 *   rti             - VALUES RTE 在 rtable 中的下标。
 *   target_relation - 插入目标关系的描述符（读取列默认值）。
 *   unused_cols     - 已被目标列表默认值表达式取代、不再使用的 VALUES 列号集合
 *                     （Bitmapset），这些列中残留的 DEFAULT 一律改为 NULL。
 *
 * 返回值：
 *   bool - 是否所有 DEFAULT 项都被替换：返回 true 表示全部替换完，false 表示有的
 *          DEFAULT 项被保留（发生在可自动更新视图且视图无默认值的情况）。
 *
 * 设计思想：
 *   1. 先通过 searchForDefault 检查是否存在 DEFAULT，避免无谓重建大 VALUES 列表。
 *   2. 扫描目标列表找出引用 VALUES RTE 的简单 Var，建立"VALUES 列号 → 目标属性号"
 *      的映射数组 attrnos（attrno == 0 表示该 VALUES 列不再被目标列表使用）。
 *   3. 三种替换策略：
 *      - 未使用的列（在 unused_cols 中）：DEFAULT 直接替换为 NULL 常量；
 *      - 可自动更新视图（isAutoUpdatableView）：若视图列无默认值则保留 DEFAULT
 *        原样不动，等递归改写到基表时再用基表的默认值；此时返回 false；
 *      - 其他情形：用 build_column_default 求默认值，无默认则显式构造 NULL
 *        （经 coerce_null_to_domain 处理域），保证列语义正确。
 *   4. isAutoUpdatableView 的判定：目标为视图、无 INSTEAD OF 触发器、且没有无条件
 *      DO INSTEAD 规则时才假定可自动更新（若其实不可更新，rewriteTargetView 会
 *      抛错兜底）。
 *   5. 重建整个 values_lists 列表（newValues）后写回 rte->values_lists。
 * ============================================================================
 */
static bool
rewriteValuesRTE(Query *parsetree, RangeTblEntry *rte, int rti,
				 Relation target_relation,
				 Bitmapset *unused_cols)
{
	List	   *newValues;
	ListCell   *lc;
	bool		isAutoUpdatableView;
	bool		allReplaced;
	int			numattrs;
	int		   *attrnos;

	/* Steps below are not sensible for non-INSERT queries */
	Assert(parsetree->commandType == CMD_INSERT);
	Assert(rte->rtekind == RTE_VALUES);

	/*
	 * Rebuilding all the lists is a pretty expensive proposition in a big
	 * VALUES list, and it's a waste of time if there aren't any DEFAULT
	 * placeholders.  So first scan to see if there are any.
	 */
	if (!searchForDefault(rte))
		return true;			/* nothing to do */

	/*
	 * Scan the targetlist for entries referring to the VALUES RTE, and note
	 * the target attributes. As noted above, we should only need to do this
	 * for targetlist entries containing simple Vars --- nothing else in the
	 * VALUES RTE should contain DEFAULT items (except possibly for unused
	 * columns), and we complain if such a thing does occur.
	 */
	numattrs = list_length(linitial(rte->values_lists));
	attrnos = (int *) palloc0(numattrs * sizeof(int));

	foreach(lc, parsetree->targetList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(lc);

		if (IsA(tle->expr, Var))
		{
			Var		   *var = (Var *) tle->expr;

			if (var->varno == rti)
			{
				int			attrno = var->varattno;

				Assert(attrno >= 1 && attrno <= numattrs);
				attrnos[attrno - 1] = tle->resno;
			}
		}
	}

	/*
	 * Check if the target relation is an auto-updatable view, in which case
	 * unresolved defaults will be left untouched rather than being set to
	 * NULL.
	 */
	isAutoUpdatableView = false;
	if (target_relation->rd_rel->relkind == RELKIND_VIEW &&
		!view_has_instead_trigger(target_relation, CMD_INSERT, NIL))
	{
		List	   *locks;
		bool		hasUpdate;
		bool		found;
		ListCell   *l;

		/* Look for an unconditional DO INSTEAD rule */
		locks = matchLocks(CMD_INSERT, target_relation,
						   parsetree->resultRelation, parsetree, &hasUpdate);

		found = false;
		foreach(l, locks)
		{
			RewriteRule *rule_lock = (RewriteRule *) lfirst(l);

			if (rule_lock->isInstead &&
				rule_lock->qual == NULL)
			{
				found = true;
				break;
			}
		}

		/*
		 * If we didn't find an unconditional DO INSTEAD rule, assume that the
		 * view is auto-updatable.  If it isn't, rewriteTargetView() will
		 * throw an error.
		 */
		if (!found)
			isAutoUpdatableView = true;
	}

	newValues = NIL;
	allReplaced = true;
	foreach(lc, rte->values_lists)
	{
		List	   *sublist = (List *) lfirst(lc);
		List	   *newList = NIL;
		ListCell   *lc2;
		int			i;

		Assert(list_length(sublist) == numattrs);

		i = 0;
		foreach(lc2, sublist)
		{
			Node	   *col = (Node *) lfirst(lc2);
			int			attrno = attrnos[i++];

			if (IsA(col, SetToDefault))
			{
				Form_pg_attribute att_tup;
				Node	   *new_expr;

				/*
				 * If this column isn't used, just replace the DEFAULT with
				 * NULL (attrno will be 0 in this case because the targetlist
				 * entry will have been replaced by the default expression).
				 */
				if (bms_is_member(i, unused_cols))
				{
					SetToDefault *def = (SetToDefault *) col;

					newList = lappend(newList,
									  makeNullConst(def->typeId,
													def->typeMod,
													def->collation));
					continue;
				}

				if (attrno == 0)
					elog(ERROR, "cannot set value in column %d to DEFAULT", i);
				Assert(attrno > 0 && attrno <= target_relation->rd_att->natts);
				att_tup = TupleDescAttr(target_relation->rd_att, attrno - 1);

				if (!att_tup->attisdropped)
					new_expr = build_column_default(target_relation, attrno);
				else
					new_expr = NULL;	/* force a NULL if dropped */

				/*
				 * If there is no default (ie, default is effectively NULL),
				 * we've got to explicitly set the column to NULL, unless the
				 * target relation is an auto-updatable view.
				 */
				if (!new_expr)
				{
					if (isAutoUpdatableView)
					{
						/* Leave the value untouched */
						newList = lappend(newList, col);
						allReplaced = false;
						continue;
					}

					new_expr = coerce_null_to_domain(att_tup->atttypid,
													 att_tup->atttypmod,
													 att_tup->attcollation,
													 att_tup->attlen,
													 att_tup->attbyval);
				}
				newList = lappend(newList, new_expr);
			}
			else
				newList = lappend(newList, col);
		}
		newValues = lappend(newValues, newList);
	}
	rte->values_lists = newValues;

	pfree(attrnos);

	return allReplaced;
}

/*
 * ============================================================================
 * 【中文注释】rewriteValuesRTEToNulls —— 把 VALUES RTE 中残留的 DEFAULT 全部改为 NULL
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把给定 VALUES RTE 中所有残留的 SetToDefault 项替换为同类型的 NULL 常量。
 *   用于自动更新视图产生的 DO ALSO 规则产品查询：这类查询没有（也不必有）可依赖
 *   的目标关系，无法求默认值，因此按规则可更新视图的方式把 DEFAULT 一律置为 NULL。
 *
 * 参数：
 *   parsetree - 所在查询（当前实现未直接使用，仅保留签名一致性）。
 *   rte       - 待处理的 VALUES RTE（就地修改其 values_lists）。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   与 rewriteValuesRTE 不同，这里没有"保留 DEFAULT 交给基表"的分支，因为产品
 *   查询可能不是 INSERT、不一定有目标关系。直接把所有 DEFAULT 用 makeNullConst
 *   转成 NULL 常量最安全，等价于"该列无默认值"的 INSERT 语义。
 * ============================================================================
 */
static void
rewriteValuesRTEToNulls(Query *parsetree, RangeTblEntry *rte)
{
	List	   *newValues;
	ListCell   *lc;

	newValues = NIL;
	foreach(lc, rte->values_lists)
	{
		List	   *sublist = (List *) lfirst(lc);
		List	   *newList = NIL;
		ListCell   *lc2;

		foreach(lc2, sublist)
		{
			Node	   *col = (Node *) lfirst(lc2);

			if (IsA(col, SetToDefault))
			{
				SetToDefault *def = (SetToDefault *) col;

				newList = lappend(newList, makeNullConst(def->typeId,
														 def->typeMod,
														 def->collation));
			}
			else
				newList = lappend(newList, col);
		}
		newValues = lappend(newValues, newList);
	}
	rte->values_lists = newValues;
}


/*
 * ============================================================================
 * 【中文注释】matchLocks —— 从关系的规则集中挑出与当前事件匹配的规则
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   扫描关系的规则集（rd_rules），返回与当前命令事件类型匹配、且按会话复制角色
 *   （replication role）应当触发的规则列表；同时顺带报告该关系是否存在 UPDATE
 *   事件规则。这是 RewriteQuery 触发 INSERT/UPDATE/DELETE 规则的第一步。
 *
 * 参数：
 *   event     - 要匹配的事件类型（CMD_INSERT/CMD_UPDATE/CMD_DELETE 等）。
 *   relation  - 被查询结果关系引用、持有规则集的关系。
 *   varno     - 该关系在查询 rtable 中的下标。
 *   parsetree - 触发查询。
 *   hasUpdate - 输出参数：若关系上存在事件为 CMD_UPDATE 的规则则置 true
 *               （用于决定 ON CONFLICT 是否被禁止）。
 *
 * 返回值：
 *   List * - 匹配到的 RewriteRule 列表；无匹配或关系无规则时为空列表 NIL。
 *
 * 设计思想：
 *   1. 非 SELECT 命令要求 varno 恰好等于 parsetree->resultRelation，即规则只针对
 *      结果关系触发；SELECT 命令则要求该关系在查询中被实际引用
 *      （rangeTableEntry_used），否则不触发。
 *   2. 复制角色过滤：ON SELECT 规则无论如何都会应用（保证视图即使在 LOCAL/REPLICA
 *      角色下也正常工作）；非 SELECT 规则按 enabled 标志与当前 SessionReplicationRole
 *      的匹配决定是否跳过（RULE_FIRES_ON_REPLICA / RULE_DISABLED 等）。
 *   3. 对 MERGE 命令，禁止任何非 SELECT 规则（报 FEATURE_NOT_SUPPORTED），因为
 *      MERGE 与规则系统不兼容。
 *   4. 把发现的 UPDATE 规则事件写入 *hasUpdate，供 RewriteQuery 检查 INSERT ON
 *      CONFLICT 与规则共存时的限制。
 * ============================================================================
 */
static List *
matchLocks(CmdType event,
		   Relation relation,
		   int varno,
		   Query *parsetree,
		   bool *hasUpdate)
{
	RuleLock   *rulelocks = relation->rd_rules;
	List	   *matching_locks = NIL;
	int			nlocks;
	int			i;

	if (rulelocks == NULL)
		return NIL;

	if (parsetree->commandType != CMD_SELECT)
	{
		if (parsetree->resultRelation != varno)
			return NIL;
	}

	nlocks = rulelocks->numLocks;

	for (i = 0; i < nlocks; i++)
	{
		RewriteRule *oneLock = rulelocks->rules[i];

		if (oneLock->event == CMD_UPDATE)
			*hasUpdate = true;

		/*
		 * Suppress ON INSERT/UPDATE/DELETE rules that are disabled or
		 * configured to not fire during the current session's replication
		 * role. ON SELECT rules will always be applied in order to keep views
		 * working even in LOCAL or REPLICA role.
		 */
		if (oneLock->event != CMD_SELECT)
		{
			if (SessionReplicationRole == SESSION_REPLICATION_ROLE_REPLICA)
			{
				if (oneLock->enabled == RULE_FIRES_ON_ORIGIN ||
					oneLock->enabled == RULE_DISABLED)
					continue;
			}
			else				/* ORIGIN or LOCAL ROLE */
			{
				if (oneLock->enabled == RULE_FIRES_ON_REPLICA ||
					oneLock->enabled == RULE_DISABLED)
					continue;
			}

			/* Non-SELECT rules are not supported for MERGE */
			if (parsetree->commandType == CMD_MERGE)
				ereport(ERROR,
						errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						errmsg("cannot execute MERGE on relation \"%s\"",
							   RelationGetRelationName(relation)),
						errdetail("MERGE is not supported for relations with rules."));
		}

		if (oneLock->event == event)
		{
			if (parsetree->commandType != CMD_SELECT ||
				rangeTableEntry_used((Node *) parsetree, varno, 0))
				matching_locks = lappend(matching_locks, oneLock);
		}
	}

	return matching_locks;
}


/*
 * ============================================================================
 * 【中文注释】ApplyRetrieveRule —— 展开视图：把 ON SELECT 规则动作作为子查询接入
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把一条 ON SELECT（RIR）规则对应的视图查询展开进触发查询：复制视图定义查询、
 *   递归展开其内部视图、必要时把 FOR [KEY] UPDATE/SHARE 下推给视图中引用的表，
 *   最终把原视图对应的 RTE 从 RTE_RELATION 改写为引用展开后子查询的 RTE_SUBQUERY。
 *
 * 参数：
 *   parsetree  - 正在处理的查询（会被就地修改并返回）。
 *   rule       - 要应用的 ON SELECT 规则（必须恰好一个动作、无条件）。
 *   rt_index   - 视图在 parsetree->rtable 中的下标。
 *   relation   - 视图关系本身（用于取安全屏障标记、relkind 等）。
 *   activeRIRs - 正在展开的视图 OID 列表，用于检测递归（递归检测已在 fireRIRrules
 *                中完成）。
 *
 * 返回值：
 *   Query * - 展开后的查询。
 *
 * 设计思想：
 *   1. 若视图恰好是查询的结果关系且尚无规则改写它：INSERT 直接沿用原 RTE（留给
 *      INSTEAD OF 触发器处理）；UPDATE/DELETE/MERGE 则复制一份视图 RTE 追加到
 *      rtable 作为新结果关系，同时保留原 RTE 供源数据使用，并在 targetList 尾部
 *      加一个 resjunk 整行 Var，供执行器计算原始视图行传给 INSTEAD OF 触发器。
 *   2. 视图查询取自 relcache，必须深拷贝后使用；对其中引用的关系用
 *      AcquireRewriteLocks 加锁（若本视图有 FOR [KEY] UPDATE/SHARE，则强制这些
 *      关系至少 RowShareLock），再递归调用 fireRIRrules 展开嵌套视图。
 *   3. 若该视图被 FOR [KEY] UPDATE/SHARE 锁定（rc != NULL），调用 markQueryForLocking
 *      把锁定语义传播到视图引用的所有表，与解析器显式内联视图定义时行为一致。
 *   4. 把原 RTE 改为 RTE_SUBQUERY 挂上展开后的子查询，并按需设置 security_barrier
 *      （安全屏障视图）；保留 relid/relkind/rellockmode/perminfoindex 以便执行前
 *      加锁与权限检查；清理 tablesample、关闭 inh 标记。
 *   5. 兼容 CREATE OR REPLACE VIEW 加列的情形：若子查询输出列多于 RTE 原有
 *      colnames，补 "?column?" 占位名，保证 eref->colnames 与子查询非 junk 输出
 *      列数一致。
 * ============================================================================
 */
static Query *
ApplyRetrieveRule(Query *parsetree,
				  RewriteRule *rule,
				  int rt_index,
				  Relation relation,
				  List *activeRIRs)
{
	Query	   *rule_action;
	RangeTblEntry *rte;
	RowMarkClause *rc;
	int			numCols;

	if (list_length(rule->actions) != 1)
		elog(ERROR, "expected just one rule action");
	if (rule->qual != NULL)
		elog(ERROR, "cannot handle qualified ON SELECT rule");

	/* Check if the expansion of non-system views are restricted */
	if (unlikely((restrict_nonsystem_relation_kind & RESTRICT_RELKIND_VIEW) != 0 &&
				 RelationGetRelid(relation) >= FirstNormalObjectId))
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("access to non-system view \"%s\" is restricted",
						RelationGetRelationName(relation))));

	if (rt_index == parsetree->resultRelation)
	{
		/*
		 * We have a view as the result relation of the query, and it wasn't
		 * rewritten by any rule.  This case is supported if there is an
		 * INSTEAD OF trigger that will trap attempts to insert/update/delete
		 * view rows.  The executor will check that; for the moment just plow
		 * ahead.  We have two cases:
		 *
		 * For INSERT, we needn't do anything.  The unmodified RTE will serve
		 * fine as the result relation.
		 *
		 * For UPDATE/DELETE/MERGE, we need to expand the view so as to have
		 * source data for the operation.  But we also need an unmodified RTE
		 * to serve as the target.  So, copy the RTE and add the copy to the
		 * rangetable.  Note that the copy does not get added to the jointree.
		 * Also note that there's a hack in fireRIRrules to avoid calling this
		 * function again when it arrives at the copied RTE.
		 */
		if (parsetree->commandType == CMD_INSERT)
			return parsetree;
		else if (parsetree->commandType == CMD_UPDATE ||
				 parsetree->commandType == CMD_DELETE ||
				 parsetree->commandType == CMD_MERGE)
		{
			RangeTblEntry *newrte;
			Var		   *var;
			TargetEntry *tle;

			rte = rt_fetch(rt_index, parsetree->rtable);
			newrte = copyObject(rte);
			parsetree->rtable = lappend(parsetree->rtable, newrte);
			parsetree->resultRelation = list_length(parsetree->rtable);
			/* parsetree->mergeTargetRelation unchanged (use expanded view) */

			/*
			 * For the most part, Vars referencing the view should remain as
			 * they are, meaning that they implicitly represent OLD values.
			 * But in the RETURNING list if any, we want such Vars to
			 * represent NEW values, so change them to reference the new RTE.
			 *
			 * Since ChangeVarNodes scribbles on the tree in-place, copy the
			 * RETURNING list first for safety.
			 */
			parsetree->returningList = copyObject(parsetree->returningList);
			ChangeVarNodes((Node *) parsetree->returningList, rt_index,
						   parsetree->resultRelation, 0);

			/*
			 * To allow the executor to compute the original view row to pass
			 * to the INSTEAD OF trigger, we add a resjunk whole-row Var
			 * referencing the original RTE.  This will later get expanded
			 * into a RowExpr computing all the OLD values of the view row.
			 */
			var = makeWholeRowVar(rte, rt_index, 0, false);
			tle = makeTargetEntry((Expr *) var,
								  list_length(parsetree->targetList) + 1,
								  pstrdup("wholerow"),
								  true);

			parsetree->targetList = lappend(parsetree->targetList, tle);

			/* Now, continue with expanding the original view RTE */
		}
		else
			elog(ERROR, "unrecognized commandType: %d",
				 (int) parsetree->commandType);
	}

	/*
	 * Check if there's a FOR [KEY] UPDATE/SHARE clause applying to this view.
	 *
	 * Note: we needn't explicitly consider any such clauses appearing in
	 * ancestor query levels; their effects have already been pushed down to
	 * here by markQueryForLocking, and will be reflected in "rc".
	 */
	rc = get_parse_rowmark(parsetree, rt_index);

	/*
	 * Make a modifiable copy of the view query, and acquire needed locks on
	 * the relations it mentions.  Force at least RowShareLock for all such
	 * rels if there's a FOR [KEY] UPDATE/SHARE clause affecting this view.
	 */
	rule_action = copyObject(linitial(rule->actions));

	AcquireRewriteLocks(rule_action, true, (rc != NULL));

	/*
	 * If FOR [KEY] UPDATE/SHARE of view, mark all the contained tables as
	 * implicit FOR [KEY] UPDATE/SHARE, the same as the parser would have done
	 * if the view's subquery had been written out explicitly.
	 */
	if (rc != NULL)
		markQueryForLocking(rule_action, (Node *) rule_action->jointree,
							rc->strength, rc->waitPolicy, true);

	/*
	 * Recursively expand any view references inside the view.
	 */
	rule_action = fireRIRrules(rule_action, activeRIRs);

	/*
	 * Make sure the query is marked as having row security if the view query
	 * does.
	 */
	parsetree->hasRowSecurity |= rule_action->hasRowSecurity;

	/*
	 * Now, plug the view query in as a subselect, converting the relation's
	 * original RTE to a subquery RTE.
	 */
	rte = rt_fetch(rt_index, parsetree->rtable);

	rte->rtekind = RTE_SUBQUERY;
	rte->subquery = rule_action;
	rte->security_barrier = RelationIsSecurityView(relation);

	/*
	 * Clear fields that should not be set in a subquery RTE.  Note that we
	 * leave the relid, relkind, rellockmode, and perminfoindex fields set, so
	 * that the view relation can be appropriately locked before execution and
	 * its permissions checked.
	 */
	rte->tablesample = NULL;
	rte->inh = false;			/* must not be set for a subquery */

	/*
	 * Since we allow CREATE OR REPLACE VIEW to add columns to a view, the
	 * rule_action might emit more columns than we expected when the current
	 * query was parsed.  Various places expect rte->eref->colnames to be
	 * consistent with the non-junk output columns of the subquery, so patch
	 * things up if necessary by adding some dummy column names.
	 */
	numCols = ExecCleanTargetListLength(rule_action->targetList);
	while (list_length(rte->eref->colnames) < numCols)
	{
		rte->eref->colnames = lappend(rte->eref->colnames,
									  makeString(pstrdup("?column?")));
	}

	return parsetree;
}

/*
 * ============================================================================
 * 【中文注释】markQueryForLocking —— 递归为视图引用的所有关系打上 FOR UPDATE/SHARE 标记
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在视图展开后，把原本施加于视图的 FOR [KEY] UPDATE/SHARE 语义递归下推到视图
 *   定义引用的所有普通表（及嵌套子查询内部的关系），为其添加行级锁定子句。
 *
 * 参数：
 *   qry        - 待处理的查询。
 *   jtnode     - 当前要扫描的 jointree 节点（RangeTblRef/FromExpr/JoinExpr）。
 *   strength   - 锁强度（LockClauseStrength，FOR UPDATE/SHARE/KEY UPDATE 等）。
 *   waitPolicy - 等待策略（LockWaitPolicy，如 NOWAIT/SKIP LOCKED）。
 *   pushedDown - 该锁定是否为下推（从上层查询传播而来），沿用解析器语义。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 只沿 jointree 遍历（而非整个 rtable），这是历史遗留：当初需要避免给视图的
 *      OLD/NEW 相关关系打标记，仅给实际使用的关系打。逻辑必须与解析器的
 *      transformLockingClause 保持一致，否则语义会分叉。
 *   2. RangeTblRef：若是普通关系，调用 applyLockingClause 加行锁，并把权限位
 *      ACL_SELECT_FOR_UPDATE 并入其 RTEPermissionInfo；若是子查询，同样加锁并递归
 *      进入其内部 jointree（标记 pushedDown = true）。其他 RTE 类型不受影响。
 *   3. FromExpr / JoinExpr 分别递归左右两侧。
 *   4. 注意：这可能产生非法查询（如对含聚合的子查询加 FOR UPDATE），但交给规划器
 *      去报错，本函数不做校验。
 * ============================================================================
 */
static void
markQueryForLocking(Query *qry, Node *jtnode,
					LockClauseStrength strength, LockWaitPolicy waitPolicy,
					bool pushedDown)
{
	if (jtnode == NULL)
		return;
	if (IsA(jtnode, RangeTblRef))
	{
		int			rti = ((RangeTblRef *) jtnode)->rtindex;
		RangeTblEntry *rte = rt_fetch(rti, qry->rtable);

		if (rte->rtekind == RTE_RELATION)
		{
			RTEPermissionInfo *perminfo;

			applyLockingClause(qry, rti, strength, waitPolicy, pushedDown);

			perminfo = getRTEPermissionInfo(qry->rteperminfos, rte);
			perminfo->requiredPerms |= ACL_SELECT_FOR_UPDATE;
		}
		else if (rte->rtekind == RTE_SUBQUERY)
		{
			applyLockingClause(qry, rti, strength, waitPolicy, pushedDown);
			/* FOR UPDATE/SHARE of subquery is propagated to subquery's rels */
			markQueryForLocking(rte->subquery, (Node *) rte->subquery->jointree,
								strength, waitPolicy, true);
		}
		/* other RTE types are unaffected by FOR UPDATE */
	}
	else if (IsA(jtnode, FromExpr))
	{
		FromExpr   *f = (FromExpr *) jtnode;
		ListCell   *l;

		foreach(l, f->fromlist)
			markQueryForLocking(qry, lfirst(l), strength, waitPolicy, pushedDown);
	}
	else if (IsA(jtnode, JoinExpr))
	{
		JoinExpr   *j = (JoinExpr *) jtnode;

		markQueryForLocking(qry, j->larg, strength, waitPolicy, pushedDown);
		markQueryForLocking(qry, j->rarg, strength, waitPolicy, pushedDown);
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(jtnode));
}


/*
 * ============================================================================
 * 【中文注释】fireRIRonSubLink —— 对表达式树中的每个 SubLink 应用视图展开
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   作为 expression_tree_walker 的回调，遍历表达式树，对每个 SubLink 节点调用
 *   fireRIRrules 展开其子查询中的视图引用，并把展开后的子查询写回 sub->subselect；
 *   同时汇总各子查询是否启用了行级安全（hasRowSecurity）。
 *
 * 参数：
 *   node    - 当前遍历节点；NULL 结束遍历（返回 false）。
 *   context - fireRIRonSubLink_context：携带 activeRIRs（递归检测用视图 OID 列表）
 *             和 hasRowSecurity（累加标记）。
 *
 * 返回值：
 *   bool - 终止遍历标志（本回调恒返回 false）。
 *
 * 设计思想：
 *   1. 与其他递归例程不同，本函数必须"接管"SubLink 节点本身：直接改写
 *      sub->subselect 指针，因为 fireRIRrules 返回的是可能被替换的新子查询树。
 *   2. 与 acquireLocksOnSubLinks 相同：不递归进入 Query 节点，因为子查询内部的
 *      展开已由那次 fireRIRrules 递归完成；配合 QTW_IGNORE_RC_SUBQUERIES 保证
 *      query_tree_walker 不会重复进入。
 *   3. 会就地修改 SubLink 节点（在调用方持有的可写副本上），调用方须确保没有
 *      意外副作用。
 * ============================================================================
 */
static bool
fireRIRonSubLink(Node *node, fireRIRonSubLink_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, SubLink))
	{
		SubLink    *sub = (SubLink *) node;

		/* Do what we came for */
		sub->subselect = (Node *) fireRIRrules((Query *) sub->subselect,
											   context->activeRIRs);

		/*
		 * Remember if any of the sublinks have row security.
		 */
		context->hasRowSecurity |= ((Query *) sub->subselect)->hasRowSecurity;

		/* Fall through to process lefthand args of SubLink */
	}

	/*
	 * Do NOT recurse into Query nodes, because fireRIRrules already processed
	 * subselects of subselects for us.
	 */
	return expression_tree_walker(node, fireRIRonSubLink, context);
}


/*
 * ============================================================================
 * 【中文注释】fireRIRrules —— 对查询中每个 RTE 应用所有 Retrieve-Instead-Retrieve 规则
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   递归地把查询中所有视图（拥有 ON SELECT 规则的普通关系）展开为底层查询：遍历
 *   rtable 中的每个条目，对含 RIR 规则的关系调用 ApplyRetrieveRule 展开，并递归
 *   处理子查询 RTE、WITH 子句、表达式中的 SubLink；最后为各表应用行级安全（RLS）
 *   策略。这是视图展开的核心枢纽。
 *
 * 参数：
 *   parsetree - 待展开的查询（可能被就地修改或替换，返回处理后的版本）。
 *   activeRIRs- 当前正在展开的视图 OID 列表，用于检测"视图递归引用自己"造成的
 *               无限循环（顶层调用方 QueryRewrite 传入 NIL）。
 *
 * 返回值：
 *   Query * - 视图全部展开后的查询。
 *
 * 设计思想：
 *   1. 先顺手展开 CTE 中的 SEARCH / CYCLE 子句（rewriteSearchAndCycle），因为
 *      这里能看到每个 Query。
 *   2. rtable 遍历用 while 循环而非 foreach：ApplyRetrieveRule 会向 rtable 追加
 *      条目（结果关系副本、子查询等），列表长度随展开动态增长。
 *   3. RTE 分类处理：
 *      - RTE_GRAPH_TABLE：先经 rewriteGraphTable 转换为子查询；
 *      - RTE_SUBQUERY：递归展开其内部，并汇总 hasRowSecurity；
 *      - 其他非关系类型（JOIN 等）：忽略；
 *      - RTE_RELATION：跳过物化视图（MATVIEW）、ON CONFLICT 的 EXCLUDED 伪关系、
 *        未被查询引用的关系（rangeTableEntry_used 为假）以及 ApplyRetrieveRule
 *        新引入的结果关系，然后打开关系、收集其 CMD_SELECT 规则并逐个应用。
 *   4. 应用规则前用 list_member_oid(activeRIRs) 检测递归，若发现同一视图正在展开
 *      则报 "infinite recursion detected in rules" 错误；应用完把该视图 OID 从
 *      activeRIRs 移除（配合 ApplyRetrieveRule 内部对新展开视图的再次调用形成
 *      调用栈式递归检测）。
 *   5. 展开完 rtable 与 CTE 后，通过 query_tree_walker + fireRIRonSubLink 处理
 *      表达式（含 JOIN 条件、安全限定等）中的 SubLink 子查询。
 *   6. 最后为每个普通表/分区表调用 get_row_security_policies 获取 RLS 安全限定与
 *      WITH CHECK OPTION；新限定若有子查询，需先加锁（acquireLocksOnSubLinks）
 *      再展开（fireRIRonSubLink），并同样做递归检测。安全限定放在 RTE
 *      securityQuals 最前面（先于视图的安全屏障条件），并同步维护
 *      hasRowSecurity / hasSubLinks 标记。
 * ============================================================================
 */
static Query *
fireRIRrules(Query *parsetree, List *activeRIRs)
{
	int			origResultRelation = parsetree->resultRelation;
	int			rt_index;
	ListCell   *lc;

	/*
	 * Expand SEARCH and CYCLE clauses in CTEs.
	 *
	 * This is just a convenient place to do this, since we are already
	 * looking at each Query.
	 */
	foreach(lc, parsetree->cteList)
	{
		CommonTableExpr *cte = lfirst_node(CommonTableExpr, lc);

		if (cte->search_clause || cte->cycle_clause)
		{
			cte = rewriteSearchAndCycle(cte);
			lfirst(lc) = cte;
		}
	}

	/*
	 * don't try to convert this into a foreach loop, because rtable list can
	 * get changed each time through...
	 */
	rt_index = 0;
	while (rt_index < list_length(parsetree->rtable))
	{
		RangeTblEntry *rte;
		Relation	rel;
		List	   *locks;
		RuleLock   *rules;
		RewriteRule *rule;
		int			i;

		++rt_index;

		rte = rt_fetch(rt_index, parsetree->rtable);

		/*
		 * Convert GRAPH_TABLE clause into a subquery using relational
		 * operators.  (This will change the rtekind to subquery, so it must
		 * be done before the subquery handling below.)
		 */
		if (rte->rtekind == RTE_GRAPH_TABLE)
		{
			parsetree = rewriteGraphTable(parsetree, rt_index);
		}

		/*
		 * A subquery RTE can't have associated rules, so there's nothing to
		 * do to this level of the query, but we must recurse into the
		 * subquery to expand any rule references in it.
		 */
		if (rte->rtekind == RTE_SUBQUERY)
		{
			rte->subquery = fireRIRrules(rte->subquery, activeRIRs);

			/*
			 * While we are here, make sure the query is marked as having row
			 * security if any of its subqueries do.
			 */
			parsetree->hasRowSecurity |= rte->subquery->hasRowSecurity;

			continue;
		}

		/*
		 * Joins and other non-relation RTEs can be ignored completely.
		 */
		if (rte->rtekind != RTE_RELATION)
			continue;

		/*
		 * Always ignore RIR rules for materialized views referenced in
		 * queries.  (This does not prevent refreshing MVs, since they aren't
		 * referenced in their own query definitions.)
		 *
		 * Note: in the future we might want to allow MVs to be conditionally
		 * expanded as if they were regular views, if they are not scannable.
		 * In that case this test would need to be postponed till after we've
		 * opened the rel, so that we could check its state.
		 */
		if (rte->relkind == RELKIND_MATVIEW)
			continue;

		/*
		 * In INSERT ... ON CONFLICT, ignore the EXCLUDED pseudo-relation;
		 * even if it points to a view, we needn't expand it, and should not
		 * because we want the RTE to remain of RTE_RELATION type.  Otherwise,
		 * it would get changed to RTE_SUBQUERY type, which is an
		 * untested/unsupported situation.
		 */
		if (parsetree->onConflict &&
			rt_index == parsetree->onConflict->exclRelIndex)
			continue;

		/*
		 * If the table is not referenced in the query, then we ignore it.
		 * This prevents infinite expansion loop due to new rtable entries
		 * inserted by expansion of a rule. A table is referenced if it is
		 * part of the join set (a source table), or is referenced by any Var
		 * nodes, or is the result table.
		 */
		if (rt_index != parsetree->resultRelation &&
			!rangeTableEntry_used((Node *) parsetree, rt_index, 0))
			continue;

		/*
		 * Also, if this is a new result relation introduced by
		 * ApplyRetrieveRule, we don't want to do anything more with it.
		 */
		if (rt_index == parsetree->resultRelation &&
			rt_index != origResultRelation)
			continue;

		/*
		 * We can use NoLock here since either the parser or
		 * AcquireRewriteLocks should have locked the rel already.
		 */
		rel = relation_open(rte->relid, NoLock);

		/*
		 * Collect the RIR rules that we must apply
		 */
		rules = rel->rd_rules;
		if (rules != NULL)
		{
			locks = NIL;
			for (i = 0; i < rules->numLocks; i++)
			{
				rule = rules->rules[i];
				if (rule->event != CMD_SELECT)
					continue;

				locks = lappend(locks, rule);
			}

			/*
			 * If we found any, apply them --- but first check for recursion!
			 */
			if (locks != NIL)
			{
				ListCell   *l;

				if (list_member_oid(activeRIRs, RelationGetRelid(rel)))
					ereport(ERROR,
							(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
							 errmsg("infinite recursion detected in rules for relation \"%s\"",
									RelationGetRelationName(rel))));
				activeRIRs = lappend_oid(activeRIRs, RelationGetRelid(rel));

				foreach(l, locks)
				{
					rule = lfirst(l);

					parsetree = ApplyRetrieveRule(parsetree,
												  rule,
												  rt_index,
												  rel,
												  activeRIRs);
				}

				activeRIRs = list_delete_last(activeRIRs);
			}
		}

		table_close(rel, NoLock);
	}

	/* Recurse into subqueries in WITH */
	foreach(lc, parsetree->cteList)
	{
		CommonTableExpr *cte = (CommonTableExpr *) lfirst(lc);

		cte->ctequery = (Node *)
			fireRIRrules((Query *) cte->ctequery, activeRIRs);

		/*
		 * While we are here, make sure the query is marked as having row
		 * security if any of its CTEs do.
		 */
		parsetree->hasRowSecurity |= ((Query *) cte->ctequery)->hasRowSecurity;
	}

	/*
	 * Recurse into sublink subqueries, too.  But we already did the ones in
	 * the rtable and cteList.
	 */
	if (parsetree->hasSubLinks)
	{
		fireRIRonSubLink_context context;

		context.activeRIRs = activeRIRs;
		context.hasRowSecurity = false;

		query_tree_walker(parsetree, fireRIRonSubLink, &context,
						  QTW_IGNORE_RC_SUBQUERIES);

		/*
		 * Make sure the query is marked as having row security if any of its
		 * sublinks do.
		 */
		parsetree->hasRowSecurity |= context.hasRowSecurity;
	}

	/*
	 * Apply any row-level security policies.  We do this last because it
	 * requires special recursion detection if the new quals have sublink
	 * subqueries, and if we did it in the loop above query_tree_walker would
	 * then recurse into those quals a second time.
	 */
	rt_index = 0;
	foreach(lc, parsetree->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(lc);
		Relation	rel;
		List	   *securityQuals;
		List	   *withCheckOptions;
		bool		hasRowSecurity;
		bool		hasSubLinks;

		++rt_index;

		/* Only normal relations can have RLS policies */
		if (rte->rtekind != RTE_RELATION ||
			(rte->relkind != RELKIND_RELATION &&
			 rte->relkind != RELKIND_PARTITIONED_TABLE))
			continue;

		rel = relation_open(rte->relid, NoLock);

		/*
		 * Fetch any new security quals that must be applied to this RTE.
		 */
		get_row_security_policies(parsetree, rte, rt_index,
								  &securityQuals, &withCheckOptions,
								  &hasRowSecurity, &hasSubLinks);

		if (securityQuals != NIL || withCheckOptions != NIL)
		{
			if (hasSubLinks)
			{
				acquireLocksOnSubLinks_context context;
				fireRIRonSubLink_context fire_context;

				/*
				 * Recursively process the new quals, checking for infinite
				 * recursion.
				 */
				if (list_member_oid(activeRIRs, RelationGetRelid(rel)))
					ereport(ERROR,
							(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
							 errmsg("infinite recursion detected in policy for relation \"%s\"",
									RelationGetRelationName(rel))));

				activeRIRs = lappend_oid(activeRIRs, RelationGetRelid(rel));

				/*
				 * get_row_security_policies just passed back securityQuals
				 * and/or withCheckOptions, and there were SubLinks, make sure
				 * we lock any relations which are referenced.
				 *
				 * These locks would normally be acquired by the parser, but
				 * securityQuals and withCheckOptions are added post-parsing.
				 */
				context.for_execute = true;
				(void) acquireLocksOnSubLinks((Node *) securityQuals, &context);
				(void) acquireLocksOnSubLinks((Node *) withCheckOptions,
											  &context);

				/*
				 * Now that we have the locks on anything added by
				 * get_row_security_policies, fire any RIR rules for them.
				 */
				fire_context.activeRIRs = activeRIRs;
				fire_context.hasRowSecurity = false;

				expression_tree_walker((Node *) securityQuals,
									   fireRIRonSubLink, &fire_context);

				expression_tree_walker((Node *) withCheckOptions,
									   fireRIRonSubLink, &fire_context);

				/*
				 * We can ignore the value of fire_context.hasRowSecurity
				 * since we only reach this code in cases where hasRowSecurity
				 * is already true.
				 */
				Assert(hasRowSecurity);

				activeRIRs = list_delete_last(activeRIRs);
			}

			/*
			 * Add the new security barrier quals to the start of the RTE's
			 * list so that they get applied before any existing barrier quals
			 * (which would have come from a security-barrier view, and should
			 * get lower priority than RLS conditions on the table itself).
			 */
			rte->securityQuals = list_concat(securityQuals,
											 rte->securityQuals);

			parsetree->withCheckOptions = list_concat(withCheckOptions,
													  parsetree->withCheckOptions);
		}

		/*
		 * Make sure the query is marked correctly if row-level security
		 * applies, or if the new quals had sublinks.
		 */
		if (hasRowSecurity)
			parsetree->hasRowSecurity = true;
		if (hasSubLinks)
			parsetree->hasSubLinks = true;

		table_close(rel, NoLock);
	}

	return parsetree;
}


/*
 * ============================================================================
 * 【中文注释】CopyAndAddInvertedQual —— 向查询追加"规则条件为假"的反向限定条件
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   生成条件型 INSTEAD 规则的"else 分支"：把规则的 WHERE 条件取反后并入查询的
 *   WHERE（AddInvertedQual），使原查询只在规则条件不成立时才执行，从而与带条件
 *   的 INSTEAD 规则动作形成"case 分支"语义。
 *
 * 参数：
 *   parsetree - 待修改的查询（会被就地修改并返回）。
 *   rule_qual - 规则的 WHERE 条件（来自 relcache，只读，故先深拷贝）。
 *   rt_index  - 规则作用的关系在查询 rtable 中的下标（用于替换 OLD 引用）。
 *   event     - 规则事件类型（INSERT/UPDATE 时还需处理 NEW 引用）。
 *
 * 返回值：
 *   Query * - 追加了反向条件的查询。
 *
 * 设计思想：
 *   1. 必须用 "x IS NOT TRUE" 而非 "NOT x"：当条件求值为 NULL 时前者才符合直觉
 *      语义（NULL 视为不满足规则条件，原查询应执行），后者会错误地阻止原查询。
 *      规划器虽然更擅长处理 NOT，但此处语义优先。
 *   2. 条件中 OLD 引用被 ChangeVarNodes 改为指向 rt_index；INSERT/UPDATE 时 NEW
 *      引用必须用查询自身 targetList 中的对应表达式替换（用
 *      ReplaceVarsFromTargetList），生成列表达式同样需要先重写（否则 new.gen_col
 *      在条件中无法正确解析）。
 *   3. 处理前对条件内的子查询补加锁（acquireLocksOnSubLinks），与 rewriteRuleAction
 *      中的处理呼应，但此处是独立路径（注释建议未来合并，只处理一次限定条件）。
 *   4. 在 fireRules 中，多个条件型 INSTEAD 规则的反向条件会被 AND 到同一个
 *      *qual_product 查询上，最终由 RewriteQuery 决定是否执行它。
 * ============================================================================
 */
static Query *
CopyAndAddInvertedQual(Query *parsetree,
					   Node *rule_qual,
					   int rt_index,
					   CmdType event)
{
	/* Don't scribble on the passed qual (it's in the relcache!) */
	Node	   *new_qual = copyObject(rule_qual);
	acquireLocksOnSubLinks_context context;

	context.for_execute = true;

	/*
	 * In case there are subqueries in the qual, acquire necessary locks and
	 * fix any deleted JOIN RTE entries.  (This is somewhat redundant with
	 * rewriteRuleAction, but not entirely ... consider restructuring so that
	 * we only need to process the qual this way once.)
	 */
	(void) acquireLocksOnSubLinks(new_qual, &context);

	/* Fix references to OLD */
	ChangeVarNodes(new_qual, PRS2_OLD_VARNO, rt_index, 0);
	/* Fix references to NEW */
	if (event == CMD_INSERT || event == CMD_UPDATE)
	{
		RangeTblEntry *rte = rt_fetch(rt_index, parsetree->rtable);
		Relation	rel;
		List	   *gen_cols;

		/*
		 * As in rewriteRuleAction, build entries for generated columns so
		 * that new.gen_col in the rule qualification can be rewritten
		 * correctly.
		 */
		rel = relation_open(rte->relid, NoLock);
		gen_cols = get_generated_columns(rel, PRS2_NEW_VARNO, true);
		relation_close(rel, NoLock);

		/*
		 * The generated column expressions refer to new.attribute, so they
		 * must be rewritten before they can be used as replacements.
		 */
		gen_cols = (List *)
			ReplaceVarsFromTargetList((Node *) gen_cols,
									  PRS2_NEW_VARNO,
									  0,
									  rte,
									  parsetree->targetList,
									  parsetree->resultRelation,
									  (event == CMD_UPDATE) ?
									  REPLACEVARS_CHANGE_VARNO :
									  REPLACEVARS_SUBSTITUTE_NULL,
									  rt_index,
									  &parsetree->hasSubLinks);

		new_qual = ReplaceVarsFromTargetList(new_qual,
											 PRS2_NEW_VARNO,
											 0,
											 rte,
											 list_concat(gen_cols,
														 parsetree->targetList),
											 parsetree->resultRelation,
											 (event == CMD_UPDATE) ?
											 REPLACEVARS_CHANGE_VARNO :
											 REPLACEVARS_SUBSTITUTE_NULL,
											 rt_index,
											 &parsetree->hasSubLinks);
	}
	/* And attach the fixed qual */
	AddInvertedQual(parsetree, new_qual);

	return parsetree;
}


/*
 * ============================================================================
 * 【中文注释】fireRules —— 逐一触发规则锁，产出改写后的动作查询列表
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对匹配到的规则列表逐个处理：对条件型 INSTEAD 规则生成"反向条件"分支查询
 *   （*qual_product），对每条规则的每个动作调用 rewriteRuleAction 改写并收集到
 *   结果列表；同时通过输出参数汇报是否有无条件 INSTEAD 规则、是否有动作重写了
 *   RETURNING。
 *
 * 参数：
 *   parsetree     - 触发查询（用于改写动作时的上下文）。
 *   rt_index      - 结果关系在 rtable 中的下标。
 *   event         - 规则事件类型。
 *   locks         - 由 matchLocks 挑选出的、本次要触发的规则列表。
 *   instead_flag  - 输出参数：发现任意无条件 INSTEAD 规则则置 true（初始 false）。
 *   returning_flag- 输出参数：发现任意规则动作改写 RETURNING 则置 true（初始 false）。
 *   qual_product  - 输出参数：若存在条件型 INSTEAD 规则，指向"追加了所有反向条件"
 *                   的原始查询副本（初始为 NULL，首次需要时用 copyObject 创建）。
 *
 * 返回值：
 *   List * - 所有改写后的规则动作查询；无动作（CMD_NOTHING）会被跳过。
 *
 * 设计思想：
 *   1. 按规则类型给动作打 QuerySource 标记：QSRC_INSTEAD_RULE（无条件 INSTEAD）、
 *      QSRC_QUAL_INSTEAD_RULE（条件 INSTEAD）、QSRC_NON_INSTEAD_RULE（非 INSTEAD，
 *      即 DO ALSO）。所有动作的 canSetTag 先置 false（是否允许设置命令标签由
 *      QueryRewrite 最后统一决定）。
 *   2. 条件型 INSTEAD 规则的语义是 case 分支：只要存在条件 INSTEAD 规则，原查询
 *      仍要执行，但必须叠加所有规则条件的取反，使其只在所有条件都不成立时生效；
 *      多个条件规则的反向条件 AND 到同一个 *qual_product 上。若已存在无条件
 *      INSTEAD 规则，*qual_product 将不会被使用，于是跳过构建以省开销。
 *   3. 每个动作若 commandType 为 CMD_NOTHING（DO NOTHING）则直接跳过。
 *   4. 调用 rewriteRuleAction 时传入规则条件与事件类型，动作内部会完成 NEW/OLD
 *      变量替换、rtable 合并与 RETURNING 处理。
 * ============================================================================
 */
static List *
fireRules(Query *parsetree,
		  int rt_index,
		  CmdType event,
		  List *locks,
		  bool *instead_flag,
		  bool *returning_flag,
		  Query **qual_product)
{
	List	   *results = NIL;
	ListCell   *l;

	foreach(l, locks)
	{
		RewriteRule *rule_lock = (RewriteRule *) lfirst(l);
		Node	   *event_qual = rule_lock->qual;
		List	   *actions = rule_lock->actions;
		QuerySource qsrc;
		ListCell   *r;

		/* Determine correct QuerySource value for actions */
		if (rule_lock->isInstead)
		{
			if (event_qual != NULL)
				qsrc = QSRC_QUAL_INSTEAD_RULE;
			else
			{
				qsrc = QSRC_INSTEAD_RULE;
				*instead_flag = true;	/* report unqualified INSTEAD */
			}
		}
		else
			qsrc = QSRC_NON_INSTEAD_RULE;

		if (qsrc == QSRC_QUAL_INSTEAD_RULE)
		{
			/*
			 * If there are INSTEAD rules with qualifications, the original
			 * query is still performed. But all the negated rule
			 * qualifications of the INSTEAD rules are added so it does its
			 * actions only in cases where the rule quals of all INSTEAD rules
			 * are false. Think of it as the default action in a case. We save
			 * this in *qual_product so RewriteQuery() can add it to the query
			 * list after we mangled it up enough.
			 *
			 * If we have already found an unqualified INSTEAD rule, then
			 * *qual_product won't be used, so don't bother building it.
			 */
			if (!*instead_flag)
			{
				if (*qual_product == NULL)
					*qual_product = copyObject(parsetree);
				*qual_product = CopyAndAddInvertedQual(*qual_product,
													   event_qual,
													   rt_index,
													   event);
			}
		}

		/* Now process the rule's actions and add them to the result list */
		foreach(r, actions)
		{
			Query	   *rule_action = lfirst(r);

			if (rule_action->commandType == CMD_NOTHING)
				continue;

			rule_action = rewriteRuleAction(parsetree, rule_action,
											event_qual, rt_index, event,
											returning_flag);

			rule_action->querySource = qsrc;
			rule_action->canSetTag = false; /* might change later */

			results = lappend(results, rule_action);
		}
	}

	return results;
}


/*
 * ============================================================================
 * 【中文注释】get_view_query —— 取出视图 _RETURN 规则对应的定义查询
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从视图关系的规则集中找到事件为 CMD_SELECT 的规则（即 _RETURN 规则），返回其
 *   唯一动作（该动作就是视图定义对应的 Query）。
 *
 * 参数：
 *   view - 视图关系（调用方需已确认其 relkind 为 RELKIND_VIEW）。
 *
 * 返回值：
 *   Query * - 视图的定义查询。注意返回的是指向 relcache 的指针，调用方必须视为
 *             只读，不得修改。
 *
 * 设计思想：
 *   1. 直接遍历 view->rd_rules 的规则数组，找到 CMD_SELECT 规则；_RETURN 规则
 *      约定只有恰好一个动作，若动作数不是 1 说明目录数据异常，elog 报错。
 *   2. 找不到时同样 elog 报错（说明视图定义不完整），NULL 只是为满足编译器。
 *   3. 视图的 _RETURN 规则由 DefineQueryRewrite 在创建视图时生成，其动作 Query
 *      缓存在 relcache 中；调用方需要可写副本时必须自行 copyObject。
 * ============================================================================
 */
Query *
get_view_query(Relation view)
{
	int			i;

	Assert(view->rd_rel->relkind == RELKIND_VIEW);

	for (i = 0; i < view->rd_rules->numLocks; i++)
	{
		RewriteRule *rule = view->rd_rules->rules[i];

		if (rule->event == CMD_SELECT)
		{
			/* A _RETURN rule should have only one action */
			if (list_length(rule->actions) != 1)
				elog(ERROR, "invalid _RETURN rule action specification");

			return (Query *) linitial(rule->actions);
		}
	}

	elog(ERROR, "failed to find _RETURN rule for view");
	return NULL;				/* keep compiler quiet */
}


/*
 * ============================================================================
 * 【中文注释】view_has_instead_trigger —— 判断视图是否具备相应事件的 INSTEAD OF 触发器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查视图是否配置了处理指定命令事件的 INSTEAD OF 行级触发器。若有，则该视图
 *   走"触发器可更新"路径而非"自动更新"路径。对 MERGE 命令，要求 mergeActionList
 *   中每个数据修改动作都有对应的 INSTEAD OF 触发器才返回 true。
 *
 * 参数：
 *   view            - 视图关系。
 *   event           - 命令事件（CMD_INSERT/CMD_UPDATE/CMD_DELETE/CMD_MERGE）。
 *   mergeActionList - 仅 MERGE 时使用：各动作的类型列表，逐个核对触发器。
 *
 * 返回值：
 *   bool - 有（MERGE 时对所有动作都有）INSTEAD OF 触发器返回 true。
 *
 * 设计思想：
 *   1. 通过 TriggerDesc 中的预计算标志（trig_insert_instead_row 等）判断，O(1)
 *      检查，无需扫描触发器表。
 *   2. 该检查与"是否可自动更新"（view_query_is_auto_updatable）分离，因为它是
 *      事实性判断而非错误条件：有 INSTEAD OF 触发器时视图就不是自动可更新的。
 *   3. MERGE 特例：所有数据修改动作（INSERT/UPDATE/DELETE）都必须有触发器才视为
 *      触发器可更新；若只有 DO NOTHING 动作则返回 true，让视图按触发器可更新
 *      处理而非误报不可自动更新。
 *   4. 不能把"部分动作有触发器"的视图当自动更新处理，那正是 error_view_not_updatable
 *      在 rewriteTargetView 中针对 MERGE 要额外检查的情形。
 * ============================================================================
 */
bool
view_has_instead_trigger(Relation view, CmdType event, List *mergeActionList)
{
	TriggerDesc *trigDesc = view->trigdesc;

	switch (event)
	{
		case CMD_INSERT:
			if (trigDesc && trigDesc->trig_insert_instead_row)
				return true;
			break;
		case CMD_UPDATE:
			if (trigDesc && trigDesc->trig_update_instead_row)
				return true;
			break;
		case CMD_DELETE:
			if (trigDesc && trigDesc->trig_delete_instead_row)
				return true;
			break;
		case CMD_MERGE:
			foreach_node(MergeAction, action, mergeActionList)
			{
				switch (action->commandType)
				{
					case CMD_INSERT:
						if (!trigDesc || !trigDesc->trig_insert_instead_row)
							return false;
						break;
					case CMD_UPDATE:
						if (!trigDesc || !trigDesc->trig_update_instead_row)
							return false;
						break;
					case CMD_DELETE:
						if (!trigDesc || !trigDesc->trig_delete_instead_row)
							return false;
						break;
					case CMD_NOTHING:
						/* No trigger required */
						break;
					default:
						elog(ERROR, "unrecognized commandType: %d", action->commandType);
						break;
				}
			}
			return true;		/* no actions without an INSTEAD OF trigger */
		default:
			elog(ERROR, "unrecognized CmdType: %d", (int) event);
			break;
	}
	return false;
}


/*
 * ============================================================================
 * 【中文注释】view_col_is_auto_updatable —— 判断视图某列是否可自动更新
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查视图 targetList 中的单个输出列是否可直接映射到底层基表的用户列，从而
 *   支持自动更新。返回值 NULL 表示可更新，否则为说明不可更新原因的消息串。
 *
 * 参数：
 *   rtr - 指向视图唯一基表的 RangeTblRef（用于核对 Var 的 varno）。
 *   tle - 待检查的视图输出列（TargetEntry）。
 *
 * 返回值：
 *   const char * - NULL 表示可更新；否则为未翻译的原因字符串（调用方若用于错误
 *                  信息需自行 _() 翻译）。
 *
 * 设计思想：
 *   1. 可更新的唯一标准：该列是引用本视图唯一基表、levelsup 为 0 的普通用户列
 *      Var（resno 为正，排除系统列与整行引用）。
 *   2. 各类不可更新情形分别返回语义化消息：junk 列、非基表列 Var（表达式列）、
 *      系统列、整行引用。
 *   3. 只做"本层"检查：不递归验证底层基表是否可更新（那是 relation_is_updatable
 *      与递归改写的职责）。
 *   4. 该检查对视图每个输出列调用一次，供 view_query_is_auto_updatable 判断
 *      "是否存在至少一个可更新列"，以及供 view_cols_are_auto_updatable 校验指定
 *      列集合是否都可更新。
 * ============================================================================
 */
static const char *
view_col_is_auto_updatable(RangeTblRef *rtr, TargetEntry *tle)
{
	Var		   *var = (Var *) tle->expr;

	/*
	 * For now, the only updatable columns we support are those that are Vars
	 * referring to user columns of the underlying base relation.
	 *
	 * The view targetlist may contain resjunk columns (e.g., a view defined
	 * like "SELECT * FROM t ORDER BY a+b" is auto-updatable) but such columns
	 * are not auto-updatable, and in fact should never appear in the outer
	 * query's targetlist.
	 */
	if (tle->resjunk)
		return gettext_noop("Junk view columns are not updatable.");

	if (!IsA(var, Var) ||
		var->varno != rtr->rtindex ||
		var->varlevelsup != 0)
		return gettext_noop("View columns that are not columns of their base relation are not updatable.");

	if (var->varattno < 0)
		return gettext_noop("View columns that refer to system columns are not updatable.");

	if (var->varattno == 0)
		return gettext_noop("View columns that return whole-row references are not updatable.");

	return NULL;				/* the view column is updatable */
}


/*
 * ============================================================================
 * 【中文注释】view_query_is_auto_updatable —— 判断视图定义是否"可自动更新"
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按 SQL-92 及 PostgreSQL 扩充规则检查视图的定义查询，判断该视图能否被自动
 *   更新（即对视图的 INSERT/UPDATE/DELETE 能否直接映射到底表）。可更新返回 NULL，
 *   否则返回说明原因的消息串。
 *
 * 参数：
 *   viewquery - 视图的定义查询（来自 get_view_query，只读使用）。
 *   check_cols- 为 true 时额外要求视图至少有一个可更新列（INSERT/UPDATE 需要）；
 *               为 false 时不做列检查（DELETE 不需要）。
 *
 * 返回值：
 *   const char * - NULL 表示可自动更新；否则为未翻译的原因字符串。
 *
 * 设计思想：
 *   1. 逐条检查 SQL-92 约束：无 DISTINCT、无 GROUP BY/HAVING、无集合操作
 *      （UNION/INTERSECT/EXCEPT）、无 CTE、无 LIMIT/OFFSET、无聚合/窗口函数/
 *      集合返回函数；FROM 中恰好一个基表（普通表、外键表、视图或分区表），且该
 *      RTE 是 RTE_RELATION 类型。
 *   2. 有意的放宽：标准要求 WHERE 中不得有引用目标表的子查询，这里不强制，因为
 *      基于 MVCC 快照，这样的子查询反正看不到外层更新，无实际危害。
 *   3. 额外约束（PostgreSQL 扩展）：不支持 TABLESAMPLE；TLE 中不得有系统列或
 *      整行引用、窗口函数、集合返回函数。
 *   4. check_cols 为 true 时遍历 targetList 用 view_col_is_auto_updatable 寻找
 *      至少一个可更新列，一个都没有则判定不可更新。
 *   5. 只在"本层"检查，不递归展开视图；若基表本身是视图，后续递归处理。
 *   6. 返回值采用 gettext_noop 未翻译字符串，便于调用方区分"视图整体不可更新"
 *      与"指定列不可更新"两类错误。
 * ============================================================================
 */
const char *
view_query_is_auto_updatable(Query *viewquery, bool check_cols)
{
	RangeTblRef *rtr;
	RangeTblEntry *base_rte;

	/*----------
	 * Check if the view is simply updatable.  According to SQL-92 this means:
	 *	- No DISTINCT clause.
	 *	- Each TLE is a column reference, and each column appears at most once.
	 *	- FROM contains exactly one base relation.
	 *	- No GROUP BY or HAVING clauses.
	 *	- No set operations (UNION, INTERSECT or EXCEPT).
	 *	- No sub-queries in the WHERE clause that reference the target table.
	 *
	 * We ignore that last restriction since it would be complex to enforce
	 * and there isn't any actual benefit to disallowing sub-queries.  (The
	 * semantic issues that the standard is presumably concerned about don't
	 * arise in Postgres, since any such sub-query will not see any updates
	 * executed by the outer query anyway, thanks to MVCC snapshotting.)
	 *
	 * We also relax the second restriction by supporting part of SQL:1999
	 * feature T111, which allows for a mix of updatable and non-updatable
	 * columns, provided that an INSERT or UPDATE doesn't attempt to assign to
	 * a non-updatable column.
	 *
	 * In addition we impose these constraints, involving features that are
	 * not part of SQL-92:
	 *	- No CTEs (WITH clauses).
	 *	- No OFFSET or LIMIT clauses (this matches a SQL:2008 restriction).
	 *	- No system columns (including whole-row references) in the tlist.
	 *	- No window functions in the tlist.
	 *	- No set-returning functions in the tlist.
	 *
	 * Note that we do these checks without recursively expanding the view.
	 * If the base relation is a view, we'll recursively deal with it later.
	 *----------
	 */
	if (viewquery->distinctClause != NIL)
		return gettext_noop("Views containing DISTINCT are not automatically updatable.");

	if (viewquery->groupClause != NIL || viewquery->groupingSets)
		return gettext_noop("Views containing GROUP BY are not automatically updatable.");

	if (viewquery->havingQual != NULL)
		return gettext_noop("Views containing HAVING are not automatically updatable.");

	if (viewquery->setOperations != NULL)
		return gettext_noop("Views containing UNION, INTERSECT, or EXCEPT are not automatically updatable.");

	if (viewquery->cteList != NIL)
		return gettext_noop("Views containing WITH are not automatically updatable.");

	if (viewquery->limitOffset != NULL || viewquery->limitCount != NULL)
		return gettext_noop("Views containing LIMIT or OFFSET are not automatically updatable.");

	/*
	 * We must not allow window functions or set returning functions in the
	 * targetlist. Otherwise we might end up inserting them into the quals of
	 * the main query. We must also check for aggregates in the targetlist in
	 * case they appear without a GROUP BY.
	 *
	 * These restrictions ensure that each row of the view corresponds to a
	 * unique row in the underlying base relation.
	 */
	if (viewquery->hasAggs)
		return gettext_noop("Views that return aggregate functions are not automatically updatable.");

	if (viewquery->hasWindowFuncs)
		return gettext_noop("Views that return window functions are not automatically updatable.");

	if (viewquery->hasTargetSRFs)
		return gettext_noop("Views that return set-returning functions are not automatically updatable.");

	/*
	 * The view query should select from a single base relation, which must be
	 * a table or another view.
	 */
	if (list_length(viewquery->jointree->fromlist) != 1)
		return gettext_noop("Views that do not select from a single table or view are not automatically updatable.");

	rtr = (RangeTblRef *) linitial(viewquery->jointree->fromlist);
	if (!IsA(rtr, RangeTblRef))
		return gettext_noop("Views that do not select from a single table or view are not automatically updatable.");

	base_rte = rt_fetch(rtr->rtindex, viewquery->rtable);
	if (base_rte->rtekind != RTE_RELATION ||
		(base_rte->relkind != RELKIND_RELATION &&
		 base_rte->relkind != RELKIND_FOREIGN_TABLE &&
		 base_rte->relkind != RELKIND_VIEW &&
		 base_rte->relkind != RELKIND_PARTITIONED_TABLE))
		return gettext_noop("Views that do not select from a single table or view are not automatically updatable.");

	if (base_rte->tablesample)
		return gettext_noop("Views containing TABLESAMPLE are not automatically updatable.");

	/*
	 * Check that the view has at least one updatable column. This is required
	 * for INSERT/UPDATE but not for DELETE.
	 */
	if (check_cols)
	{
		ListCell   *cell;
		bool		found;

		found = false;
		foreach(cell, viewquery->targetList)
		{
			TargetEntry *tle = (TargetEntry *) lfirst(cell);

			if (view_col_is_auto_updatable(rtr, tle) == NULL)
			{
				found = true;
				break;
			}
		}

		if (!found)
			return gettext_noop("Views that have no updatable columns are not automatically updatable.");
	}

	return NULL;				/* the view is updatable */
}


/*
 * ============================================================================
 * 【中文注释】view_cols_are_auto_updatable —— 校验指定视图列集合是否全部可自动更新
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历视图 targetList，确认 required_cols 指定的列都是可更新的（即都是引用基表
 *   普通列的 Var）。若全部满足返回 NULL；否则返回未翻译的原因串，并可通过输出
 *   参数给出第一个违规列的名字。
 *
 * 参数：
 *   viewquery         - 视图定义查询（调用方须已用 view_query_is_auto_updatable
 *                       确认其可自动更新）。
 *   required_cols     - 本次操作需要更新的列集合（Bitmapset，位号为列号加偏移）。
 *                       其中的列不可更新时即判定失败。
 *   updatable_cols    - 输出参数（可为 NULL）：返回视图所有可更新列的集合。
 *   non_updatable_col - 输出参数（可为 NULL）：若失败，置为第一个违规列的列名。
 *
 * 返回值：
 *   const char * - NULL 表示要求的列都可更新；否则为未翻译的原因字符串。
 *
 * 设计思想：
 *   1. 通过 col 计数器把视图输出列按序号映射为"列号 + FirstLowInvalidHeapAttributeNumber"
 *      位号，与权限系统使用的位图编码一致（列号可为负，如系统列）。
 *   2. 对每个输出列调用 view_col_is_auto_updatable：可更新则加入 *updatable_cols；
 *      不可更新且属于 required_cols 则记录列名并立即返回原因。
 *   3. 只依赖视图定义本身，不递归检查基表列的可更新性。
 *   4. 用于 INSERT/UPDATE 前校验被修改列集合（rewriteTargetView），也用于
 *      relation_is_updatable 收集视图的可更新列。
 * ============================================================================
 */
static const char *
view_cols_are_auto_updatable(Query *viewquery,
							 Bitmapset *required_cols,
							 Bitmapset **updatable_cols,
							 char **non_updatable_col)
{
	RangeTblRef *rtr;
	AttrNumber	col;
	ListCell   *cell;

	/*
	 * The caller should have verified that this view is auto-updatable and so
	 * there should be a single base relation.
	 */
	Assert(list_length(viewquery->jointree->fromlist) == 1);
	rtr = linitial_node(RangeTblRef, viewquery->jointree->fromlist);

	/* Initialize the optional return values */
	if (updatable_cols != NULL)
		*updatable_cols = NULL;
	if (non_updatable_col != NULL)
		*non_updatable_col = NULL;

	/* Test each view column for updatability */
	col = -FirstLowInvalidHeapAttributeNumber;
	foreach(cell, viewquery->targetList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(cell);
		const char *col_update_detail;

		col++;
		col_update_detail = view_col_is_auto_updatable(rtr, tle);

		if (col_update_detail == NULL)
		{
			/* The column is updatable */
			if (updatable_cols != NULL)
				*updatable_cols = bms_add_member(*updatable_cols, col);
		}
		else if (bms_is_member(col, required_cols))
		{
			/* The required column is not updatable */
			if (non_updatable_col != NULL)
				*non_updatable_col = tle->resname;
			return col_update_detail;
		}
	}

	return NULL;				/* all the required view columns are updatable */
}


/*
 * ============================================================================
 * 【中文注释】relation_is_updatable —— 确定关系支持的更新事件集合
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   递归判定一个关系支持哪些 DML 事件（INSERT/UPDATE/DELETE），返回事件位掩码。
 *   这是信息模式（information_schema.views 等）判定"updatable / trigger_updatable"
 *   的依据，也可用于判断数据修改 SQL 是否可行。
 *
 * 参数：
 *   reloid          - 待检查关系的 OID。
 *   outer_reloids   - 递归路径上已检查过的外层关系 OID 列表（递归检测用；外部
 *                     调用方传 NIL）。
 *   include_triggers- 为 true 时把 INSTEAD OF 触发器提供的可更新能力也计入结果；
 *                     为 false（信息模式语义）则只计规则/自动更新能力。
 *   include_cols    - 非 NULL 时只考虑指定列集合，用于视图级权限或列级检查。
 *
 * 返回值：
 *   int - 位掩码，(1 << CMD_INSERT) | (1 << CMD_UPDATE) | (1 << CMD_DELETE)
 *         中对应支持事件位置位。
 *
 * 设计思想：
 *   1. 递归前先 check_stack_depth 防栈溢出；用 try_relation_open 打开关系，若已
 *      不存在（MVCC 下信息模式扫描可能引用到已删除表）则返回 0 而非报错。
 *   2. 递归检测：若 reloid 已在 outer_reloids 中（视图循环引用自身）返回 0。
 *   3. 普通表/分区表无条件支持全部事件。
 *   4. 规则贡献：所有无条件 DO INSTEAD 规则对应的（INSERT/UPDATE/DELETE）事件
 *      计入；一旦已集齐全部事件即可提前返回。
 *   5. 触发器贡献（include_triggers 时）：三种 INSTEAD OF 行触发器各计一事件，
 *      集齐即返回。
 *   6. 外键表：优先用 FDW 提供的 IsForeignRelUpdatable；缺失时按是否存在
 *      ExecForeignInsert/Update/Delete 回调推断。
 *   7. 视图：若可自动更新，先由 view_cols_are_auto_updatable 求可更新列集合
 *      （与 include_cols 求交集），空则只可能支持 DELETE；否则可能支持全部事件。
 *      基表若又是非普通表，则把视图的可更新列映射到底表列（adjust_view_column_set）
 *      后递归检查底表，得到的结果做按位与，即"两端都必须支持"。
 * ============================================================================
 */
int
relation_is_updatable(Oid reloid,
					  List *outer_reloids,
					  bool include_triggers,
					  Bitmapset *include_cols)
{
	int			events = 0;
	Relation	rel;
	RuleLock   *rulelocks;

#define ALL_EVENTS ((1 << CMD_INSERT) | (1 << CMD_UPDATE) | (1 << CMD_DELETE))

	/* Since this function recurses, it could be driven to stack overflow */
	check_stack_depth();

	rel = try_relation_open(reloid, AccessShareLock);

	/*
	 * If the relation doesn't exist, return zero rather than throwing an
	 * error.  This is helpful since scanning an information_schema view under
	 * MVCC rules can result in referencing rels that have actually been
	 * deleted already.
	 */
	if (rel == NULL)
		return 0;

	/* If we detect a recursive view, report that it is not updatable */
	if (list_member_oid(outer_reloids, RelationGetRelid(rel)))
	{
		relation_close(rel, AccessShareLock);
		return 0;
	}

	/* If the relation is a table, it is always updatable */
	if (rel->rd_rel->relkind == RELKIND_RELATION ||
		rel->rd_rel->relkind == RELKIND_PARTITIONED_TABLE)
	{
		relation_close(rel, AccessShareLock);
		return ALL_EVENTS;
	}

	/* Look for unconditional DO INSTEAD rules, and note supported events */
	rulelocks = rel->rd_rules;
	if (rulelocks != NULL)
	{
		int			i;

		for (i = 0; i < rulelocks->numLocks; i++)
		{
			if (rulelocks->rules[i]->isInstead &&
				rulelocks->rules[i]->qual == NULL)
			{
				events |= ((1 << rulelocks->rules[i]->event) & ALL_EVENTS);
			}
		}

		/* If we have rules for all events, we're done */
		if (events == ALL_EVENTS)
		{
			relation_close(rel, AccessShareLock);
			return events;
		}
	}

	/* Similarly look for INSTEAD OF triggers, if they are to be included */
	if (include_triggers)
	{
		TriggerDesc *trigDesc = rel->trigdesc;

		if (trigDesc)
		{
			if (trigDesc->trig_insert_instead_row)
				events |= (1 << CMD_INSERT);
			if (trigDesc->trig_update_instead_row)
				events |= (1 << CMD_UPDATE);
			if (trigDesc->trig_delete_instead_row)
				events |= (1 << CMD_DELETE);

			/* If we have triggers for all events, we're done */
			if (events == ALL_EVENTS)
			{
				relation_close(rel, AccessShareLock);
				return events;
			}
		}
	}

	/* If this is a foreign table, check which update events it supports */
	if (rel->rd_rel->relkind == RELKIND_FOREIGN_TABLE)
	{
		FdwRoutine *fdwroutine = GetFdwRoutineForRelation(rel, false);

		if (fdwroutine->IsForeignRelUpdatable != NULL)
			events |= fdwroutine->IsForeignRelUpdatable(rel);
		else
		{
			/* Assume presence of executor functions is sufficient */
			if (fdwroutine->ExecForeignInsert != NULL)
				events |= (1 << CMD_INSERT);
			if (fdwroutine->ExecForeignUpdate != NULL)
				events |= (1 << CMD_UPDATE);
			if (fdwroutine->ExecForeignDelete != NULL)
				events |= (1 << CMD_DELETE);
		}

		relation_close(rel, AccessShareLock);
		return events;
	}

	/* Check if this is an automatically updatable view */
	if (rel->rd_rel->relkind == RELKIND_VIEW)
	{
		Query	   *viewquery = get_view_query(rel);

		if (view_query_is_auto_updatable(viewquery, false) == NULL)
		{
			Bitmapset  *updatable_cols;
			int			auto_events;
			RangeTblRef *rtr;
			RangeTblEntry *base_rte;
			Oid			baseoid;

			/*
			 * Determine which of the view's columns are updatable. If there
			 * are none within the set of columns we are looking at, then the
			 * view doesn't support INSERT/UPDATE, but it may still support
			 * DELETE.
			 */
			view_cols_are_auto_updatable(viewquery, NULL,
										 &updatable_cols, NULL);

			if (include_cols != NULL)
				updatable_cols = bms_int_members(updatable_cols, include_cols);

			if (bms_is_empty(updatable_cols))
				auto_events = (1 << CMD_DELETE);	/* May support DELETE */
			else
				auto_events = ALL_EVENTS;	/* May support all events */

			/*
			 * The base relation must also support these update commands.
			 * Tables are always updatable, but for any other kind of base
			 * relation we must do a recursive check limited to the columns
			 * referenced by the locally updatable columns in this view.
			 */
			rtr = (RangeTblRef *) linitial(viewquery->jointree->fromlist);
			base_rte = rt_fetch(rtr->rtindex, viewquery->rtable);
			Assert(base_rte->rtekind == RTE_RELATION);

			if (base_rte->relkind != RELKIND_RELATION &&
				base_rte->relkind != RELKIND_PARTITIONED_TABLE)
			{
				baseoid = base_rte->relid;
				outer_reloids = lappend_oid(outer_reloids,
											RelationGetRelid(rel));
				include_cols = adjust_view_column_set(updatable_cols,
													  viewquery->targetList);
				auto_events &= relation_is_updatable(baseoid,
													 outer_reloids,
													 include_triggers,
													 include_cols);
				outer_reloids = list_delete_last(outer_reloids);
			}
			events |= auto_events;
		}
	}

	/* If we reach here, the relation may support some update commands */
	relation_close(rel, AccessShareLock);
	return events;
}


/*
 * ============================================================================
 * 【中文注释】adjust_view_column_set —— 把视图列号集合映射到底表列号集合
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   依据视图 targetList，把"视图列号"的集合（如权限检查的 insertedCols/
 *   updatedCols）映射为"底层基表列号"的集合。视图的可更新列都是引用基表普通列
 *   的 Var，因此可以用 targetList 做一一映射。
 *
 * 参数：
 *   cols       - 待映射的视图列号集合（Bitmapset，位号已加
 *                FirstLowInvalidHeapAttributeNumber 偏移）。
 *   targetlist - 视图的定义 targetList。
 *
 * 返回值：
 *   Bitmapset * - 映射后的基表列号集合。
 *
 * 设计思想：
 *   1. 普通列：位号还原为 attno 后用 get_tle_by_resno 找到对应视图输出列，取其
 *      表达式（须为引用基表的 Var）的 varattno 加入结果集合；找不到或非 Var 则
 *      elog 报错（调用方应已保证视图可自动更新）。
 *   2. 整行引用（attno == InvalidAttrNumber，即视图整行）：权限上视为引用了视图
 *      输出的每一列，但**不**转换成对基表的整行引用——因为视图可能只使用基表的
 *      部分列，整行引用会错误扩大权限需求。
 *   3. 位号统一使用"列号 - FirstLowInvalidHeapAttributeNumber"的编码，与权限位图
 *      （RTEPermissionInfo）的编码一致。
 *   4. 用于 rewriteTargetView 把对视图列的写权限映射到底表列，也用于
 *      relation_is_updatable 递归检查底表列。
 * ============================================================================
 */
static Bitmapset *
adjust_view_column_set(Bitmapset *cols, List *targetlist)
{
	Bitmapset  *result = NULL;
	int			col;

	col = -1;
	while ((col = bms_next_member(cols, col)) >= 0)
	{
		/* bit numbers are offset by FirstLowInvalidHeapAttributeNumber */
		AttrNumber	attno = col + FirstLowInvalidHeapAttributeNumber;

		if (attno == InvalidAttrNumber)
		{
			/*
			 * There's a whole-row reference to the view.  For permissions
			 * purposes, treat it as a reference to each column available from
			 * the view.  (We should *not* convert this to a whole-row
			 * reference to the base relation, since the view may not touch
			 * all columns of the base relation.)
			 */
			ListCell   *lc;

			foreach(lc, targetlist)
			{
				TargetEntry *tle = lfirst_node(TargetEntry, lc);
				Var		   *var;

				if (tle->resjunk)
					continue;
				var = castNode(Var, tle->expr);
				result = bms_add_member(result,
										var->varattno - FirstLowInvalidHeapAttributeNumber);
			}
		}
		else
		{
			/*
			 * Views do not have system columns, so we do not expect to see
			 * any other system attnos here.  If we do find one, the error
			 * case will apply.
			 */
			TargetEntry *tle = get_tle_by_resno(targetlist, attno);

			if (tle != NULL && !tle->resjunk && IsA(tle->expr, Var))
			{
				Var		   *var = (Var *) tle->expr;

				result = bms_add_member(result,
										var->varattno - FirstLowInvalidHeapAttributeNumber);
			}
			else
				elog(ERROR, "attribute number %d not found in view targetlist",
					 attno);
		}
	}

	return result;
}


/*
 * ============================================================================
 * 【中文注释】error_view_not_updatable —— 报出"视图不可更新"的错误
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   针对对不可更新视图的 INSERT/UPDATE/DELETE/MERGE 操作抛出带详细提示的错误，
 *   提示用户提供 INSTEAD OF 触发器或无条件的 ON ... DO INSTEAD 规则（MERGE 仅
 *   触发器）。
 *
 * 参数：
 *   view            - 目标视图关系（用于错误信息中的视图名与触发器描述）。
 *   command         - 被尝试的命令事件。
 *   mergeActionList - 仅 MERGE：逐个动作检查，对缺 INSTEAD OF 触发器的动作报错。
 *   detail          - 附加的错误细节（如不可更新的具体原因，来自
 *                     view_query_is_auto_updatable 的返回值）；为 NULL 时省略。
 *
 * 返回值：
 *   无（总是抛出 ERROR）。
 *
 * 设计思想：
 *   1. 每条消息都带 errhint 给出修复路径，detail 用 errdetail_internal 并 _()
 *      翻译（detail 本身是 gettext_noop 的未翻译串）。
 *   2. 主要调用点是 rewriteTargetView（重写器内，有详细原因），但执行器的
 *      CheckValidResultRel 也会在"理论不该失败"的兜底检查中调用本函数，此时
 *      detail 为 NULL。
 *   3. MERGE 分支特殊：错误提示只能指向 INSTEAD OF 触发器（MERGE 不支持规则），
 *      且必须逐个动作检查——因为调用方（rewriteTargetView）已经保证不存在完整的
 *      触发器集合，这里只需要对缺失触发器的具体动作报错。
 *   4. 错误码统一为 ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE。
 * ============================================================================
 */
void
error_view_not_updatable(Relation view,
						 CmdType command,
						 List *mergeActionList,
						 const char *detail)
{
	TriggerDesc *trigDesc = view->trigdesc;

	switch (command)
	{
		case CMD_INSERT:
			ereport(ERROR,
					errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
					errmsg("cannot insert into view \"%s\"",
						   RelationGetRelationName(view)),
					detail ? errdetail_internal("%s", _(detail)) : 0,
					errhint("To enable inserting into the view, provide an INSTEAD OF INSERT trigger or an unconditional ON INSERT DO INSTEAD rule."));
			break;
		case CMD_UPDATE:
			ereport(ERROR,
					errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
					errmsg("cannot update view \"%s\"",
						   RelationGetRelationName(view)),
					detail ? errdetail_internal("%s", _(detail)) : 0,
					errhint("To enable updating the view, provide an INSTEAD OF UPDATE trigger or an unconditional ON UPDATE DO INSTEAD rule."));
			break;
		case CMD_DELETE:
			ereport(ERROR,
					errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
					errmsg("cannot delete from view \"%s\"",
						   RelationGetRelationName(view)),
					detail ? errdetail_internal("%s", _(detail)) : 0,
					errhint("To enable deleting from the view, provide an INSTEAD OF DELETE trigger or an unconditional ON DELETE DO INSTEAD rule."));
			break;
		case CMD_MERGE:

			/*
			 * Note that the error hints here differ from above, since MERGE
			 * doesn't support rules.
			 */
			foreach_node(MergeAction, action, mergeActionList)
			{
				switch (action->commandType)
				{
					case CMD_INSERT:
						if (!trigDesc || !trigDesc->trig_insert_instead_row)
							ereport(ERROR,
									errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
									errmsg("cannot insert into view \"%s\"",
										   RelationGetRelationName(view)),
									detail ? errdetail_internal("%s", _(detail)) : 0,
									errhint("To enable inserting into the view using MERGE, provide an INSTEAD OF INSERT trigger."));
						break;
					case CMD_UPDATE:
						if (!trigDesc || !trigDesc->trig_update_instead_row)
							ereport(ERROR,
									errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
									errmsg("cannot update view \"%s\"",
										   RelationGetRelationName(view)),
									detail ? errdetail_internal("%s", _(detail)) : 0,
									errhint("To enable updating the view using MERGE, provide an INSTEAD OF UPDATE trigger."));
						break;
					case CMD_DELETE:
						if (!trigDesc || !trigDesc->trig_delete_instead_row)
							ereport(ERROR,
									errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
									errmsg("cannot delete from view \"%s\"",
										   RelationGetRelationName(view)),
									detail ? errdetail_internal("%s", _(detail)) : 0,
									errhint("To enable deleting from the view using MERGE, provide an INSTEAD OF DELETE trigger."));
						break;
					case CMD_NOTHING:
						break;
					default:
						elog(ERROR, "unrecognized commandType: %d", action->commandType);
						break;
				}
			}
			break;
		default:
			elog(ERROR, "unrecognized CmdType: %d", (int) command);
			break;
	}
}


/*
 * ============================================================================
 * 【中文注释】rewriteTargetView —— 把目标为视图的查询改写为直接作用于基表
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   实现"自动可更新视图"：当 INSERT/UPDATE/DELETE/MERGE 的目标关系是视图时，
 *   把视图定义查询内联展开，把对视图列的赋值映射到基表列，将视图 WHERE 限定
 *   合并进查询（含安全屏障/WITH CHECK OPTION 处理），最终使基表成为新的结果关系，
 *   再交给 RewriteQuery 递归改写。
 *
 * 参数：
 *   parsetree - 目标为视图的查询（就地修改，返回改写后的版本）。
 *   view      - 目标视图关系。
 *
 * 返回值：
 *   Query * - 改写后的查询（结果关系已变成视图的基表）。
 *
 * 设计思想：
 *   1. 前置校验：从 relcache 深拷贝视图定义查询（get_view_query 只读），先确认
 *      "整体可自动更新"（view_query_is_auto_updatable），失败即 error_view_not_updatable；
 *      INSERT/UPDATE（含 MERGE 内相应动作）还要计算被修改列集合
 *      （view_perminfo 的 insertedCols/updatedCols 并上 targetList 与 ON CONFLICT
 *      及 MERGE 动作的 resno），确认这些列都可更新，否则按列报错。
 *   2. FOR PORTION OF 的区间列同样要验证可更新（对 DELETE 也生效）。
 *   3. 基表尚未被加锁，先以 RowExclusiveLock 打开（后续递归 RewriteQuery 会假定
 *      已有合适锁），并刷新 base_rte->relkind。
 *   4. 把基表 RTE 追加到外层 rtable 末尾作为新目标（new_rt_index），INSERT 关闭
 *      inh，UPDATE/DELETE/MERGE 沿用视图查询的继承标志；把视图 targetList 的
 *      varno 从 base_rt_index 改为 new_rt_index，得到替换表达式（view_targetlist）。
 *   5. 权限处理：给基表建立新的 RTEPermissionInfo，关系级所需权限继承视图的
 *      requiredPerms（去掉 SELECT 位）；列级把视图的 insertedCols/updatedCols
 *      经 adjust_view_column_set 映射为基表列；selectedCols 保留视图定义中使用的
 *      基表列（视图属主必须对视图定义引用的所有列有读权限）。security_invoker
 *      视图按查询调用者检查（checkAsUser = InvalidOid），否则按视图属主检查。
 *   6. 用 ReplaceVarsFromTargetList 把外层查询中所有引用视图的 Var 替换为基表列
 *      表达式（REPORT_ERROR 保证视图列都能映射）；再用 ChangeVarNodes 把
 *      resultRelation 等 RTE 下标引用改为 new_rt_index。
 *   7. 对 INSERT/UPDATE 的 targetList、MERGE 动作 targetList、ON CONFLICT 辅助
 *      列表与 EXCLUDED 伪关系、FOR PORTION OF 的目标列表逐一按视图列号映射重排
 *      resno（视图列顺序可能不同于基表列顺序）；ON CONFLICT 需重建 EXCLUDED RTE
 *      （基于基表列）并重写相关 Var。
 *   8. 视图 WHERE 限定：非 INSERT 时拉入外层查询（安全屏障视图则作为新 RTE 的
 *      securityQuals 排在既有屏障条件之前）；INSERT/UPDATE 且带 WITH CHECK OPTION
 *      时构造 WCO_VIEW_CHECK 检查项加入 withCheckOptions 列表（CASCADED 需级联
 *      下传，LOCAL 且无自身限定时可省略），保证写入行满足视图定义。
 *   9. 基表若本身是视图，则交给 RewriteQuery 的递归继续改写；本函数只做一层映射。
 * ============================================================================
 */
static Query *
rewriteTargetView(Query *parsetree, Relation view)
{
	Query	   *viewquery;
	bool		insert_or_update;
	const char *auto_update_detail;
	RangeTblRef *rtr;
	int			base_rt_index;
	int			new_rt_index;
	RangeTblEntry *base_rte;
	RangeTblEntry *view_rte;
	RangeTblEntry *new_rte;
	RTEPermissionInfo *base_perminfo;
	RTEPermissionInfo *view_perminfo;
	RTEPermissionInfo *new_perminfo;
	Relation	base_rel;
	List	   *view_targetlist;
	ListCell   *lc;

	/*
	 * Get the Query from the view's ON SELECT rule.  We're going to munge the
	 * Query to change the view's base relation into the target relation,
	 * along with various other changes along the way, so we need to make a
	 * copy of it (get_view_query() returns a pointer into the relcache, so we
	 * have to treat it as read-only).
	 */
	viewquery = copyObject(get_view_query(view));

	/* Locate RTE and perminfo describing the view in the outer query */
	view_rte = rt_fetch(parsetree->resultRelation, parsetree->rtable);
	view_perminfo = getRTEPermissionInfo(parsetree->rteperminfos, view_rte);

	/*
	 * Are we doing INSERT/UPDATE, or MERGE containing INSERT/UPDATE?  If so,
	 * various additional checks on the view columns need to be applied, and
	 * any view CHECK OPTIONs need to be enforced.
	 */
	insert_or_update =
		(parsetree->commandType == CMD_INSERT ||
		 parsetree->commandType == CMD_UPDATE);

	if (parsetree->commandType == CMD_MERGE)
	{
		foreach_node(MergeAction, action, parsetree->mergeActionList)
		{
			if (action->commandType == CMD_INSERT ||
				action->commandType == CMD_UPDATE)
			{
				insert_or_update = true;
				break;
			}
		}
	}

	/* Check if the expansion of non-system views are restricted */
	if (unlikely((restrict_nonsystem_relation_kind & RESTRICT_RELKIND_VIEW) != 0 &&
				 RelationGetRelid(view) >= FirstNormalObjectId))
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("access to non-system view \"%s\" is restricted",
						RelationGetRelationName(view))));

	/*
	 * The view must be updatable, else fail.
	 *
	 * If we are doing INSERT/UPDATE (or MERGE containing INSERT/UPDATE), we
	 * also check that there is at least one updatable column.
	 */
	auto_update_detail =
		view_query_is_auto_updatable(viewquery, insert_or_update);

	if (auto_update_detail)
		error_view_not_updatable(view,
								 parsetree->commandType,
								 parsetree->mergeActionList,
								 auto_update_detail);

	/*
	 * For INSERT/UPDATE (or MERGE containing INSERT/UPDATE) the modified
	 * columns must all be updatable.
	 */
	if (insert_or_update)
	{
		Bitmapset  *modified_cols;
		char	   *non_updatable_col;

		/*
		 * Compute the set of modified columns as those listed in the result
		 * RTE's insertedCols and/or updatedCols sets plus those that are
		 * targets of the query's targetlist(s).  We must consider the query's
		 * targetlist because rewriteTargetListIU may have added additional
		 * targetlist entries for view defaults, and these must also be
		 * updatable.  But rewriteTargetListIU can also remove entries if they
		 * are DEFAULT markers and the column's default is NULL, so
		 * considering only the targetlist would also be wrong.
		 */
		modified_cols = bms_union(view_perminfo->insertedCols,
								  view_perminfo->updatedCols);

		foreach(lc, parsetree->targetList)
		{
			TargetEntry *tle = (TargetEntry *) lfirst(lc);

			if (!tle->resjunk)
				modified_cols = bms_add_member(modified_cols,
											   tle->resno - FirstLowInvalidHeapAttributeNumber);
		}

		if (parsetree->onConflict)
		{
			foreach(lc, parsetree->onConflict->onConflictSet)
			{
				TargetEntry *tle = (TargetEntry *) lfirst(lc);

				if (!tle->resjunk)
					modified_cols = bms_add_member(modified_cols,
												   tle->resno - FirstLowInvalidHeapAttributeNumber);
			}
		}

		foreach_node(MergeAction, action, parsetree->mergeActionList)
		{
			if (action->commandType == CMD_INSERT ||
				action->commandType == CMD_UPDATE)
			{
				foreach_node(TargetEntry, tle, action->targetList)
				{
					if (!tle->resjunk)
						modified_cols = bms_add_member(modified_cols,
													   tle->resno - FirstLowInvalidHeapAttributeNumber);
				}
			}
		}

		auto_update_detail = view_cols_are_auto_updatable(viewquery,
														  modified_cols,
														  NULL,
														  &non_updatable_col);
		if (auto_update_detail)
		{
			/*
			 * This is a different error, caused by an attempt to update a
			 * non-updatable column in an otherwise updatable view.
			 */
			switch (parsetree->commandType)
			{
				case CMD_INSERT:
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot insert into column \"%s\" of view \"%s\"",
									non_updatable_col,
									RelationGetRelationName(view)),
							 errdetail_internal("%s", _(auto_update_detail))));
					break;
				case CMD_UPDATE:
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot update column \"%s\" of view \"%s\"",
									non_updatable_col,
									RelationGetRelationName(view)),
							 errdetail_internal("%s", _(auto_update_detail))));
					break;
				case CMD_MERGE:
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot merge into column \"%s\" of view \"%s\"",
									non_updatable_col,
									RelationGetRelationName(view)),
							 errdetail_internal("%s", _(auto_update_detail))));
					break;
				default:
					elog(ERROR, "unrecognized CmdType: %d",
						 (int) parsetree->commandType);
					break;
			}
		}
	}

	/*
	 * Similarly, make sure the FOR PORTION OF column is updateable. This is
	 * not included in the columns tested above, and we have to test it even
	 * for DELETEs.
	 */
	if (parsetree->forPortionOf)
	{
		AttrNumber	rangeAttno;
		Bitmapset  *fpo_cols;
		char	   *non_updatable_col;
		const char *fpo_update_detail;

		rangeAttno = parsetree->forPortionOf->rangeVar->varattno;
		fpo_cols = bms_make_singleton(rangeAttno - FirstLowInvalidHeapAttributeNumber);

		fpo_update_detail = view_cols_are_auto_updatable(viewquery,
														 fpo_cols,
														 NULL,
														 &non_updatable_col);
		if (fpo_update_detail)
		{
			switch (parsetree->commandType)
			{
				case CMD_UPDATE:
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot update column \"%s\" of view \"%s\"",
									non_updatable_col,
									RelationGetRelationName(view)),
							 errdetail_internal("%s", _(fpo_update_detail))));
					break;
				case CMD_DELETE:
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot delete from view \"%s\" using FOR PORTION OF \"%s\"",
									RelationGetRelationName(view),
									non_updatable_col),
							 errdetail_internal("%s", _(fpo_update_detail))));
					break;
				default:
					elog(ERROR, "unrecognized CmdType: %d",
						 (int) parsetree->commandType);
					break;
			}
		}
	}

	/*
	 * For MERGE, there must not be any INSTEAD OF triggers on an otherwise
	 * updatable view.  The caller already checked that there isn't a full set
	 * of INSTEAD OF triggers, so this is to guard against having a partial
	 * set (mixing auto-update and trigger-update actions in a single command
	 * isn't supported).
	 */
	if (parsetree->commandType == CMD_MERGE)
	{
		foreach_node(MergeAction, action, parsetree->mergeActionList)
		{
			if (action->commandType != CMD_NOTHING &&
				view_has_instead_trigger(view, action->commandType, NIL))
				ereport(ERROR,
						errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						errmsg("cannot merge into view \"%s\"",
							   RelationGetRelationName(view)),
						errdetail("MERGE is not supported for views with INSTEAD OF triggers for some actions but not all."),
						errhint("To enable merging into the view, either provide a full set of INSTEAD OF triggers or drop the existing INSTEAD OF triggers."));
		}
	}

	/*
	 * If we get here, view_query_is_auto_updatable() has verified that the
	 * view contains a single base relation.
	 */
	Assert(list_length(viewquery->jointree->fromlist) == 1);
	rtr = linitial_node(RangeTblRef, viewquery->jointree->fromlist);

	base_rt_index = rtr->rtindex;
	base_rte = rt_fetch(base_rt_index, viewquery->rtable);
	Assert(base_rte->rtekind == RTE_RELATION);
	base_perminfo = getRTEPermissionInfo(viewquery->rteperminfos, base_rte);

	/*
	 * Up to now, the base relation hasn't been touched at all in our query.
	 * We need to acquire lock on it before we try to do anything with it.
	 * (The subsequent recursive call of RewriteQuery will suppose that we
	 * already have the right lock!)  Since it will become the query target
	 * relation, RowExclusiveLock is always the right thing.
	 */
	base_rel = relation_open(base_rte->relid, RowExclusiveLock);

	/*
	 * While we have the relation open, update the RTE's relkind, just in case
	 * it changed since this view was made (cf. AcquireRewriteLocks).
	 */
	base_rte->relkind = base_rel->rd_rel->relkind;

	/*
	 * If the view query contains any sublink subqueries then we need to also
	 * acquire locks on any relations they refer to.  We know that there won't
	 * be any subqueries in the range table or CTEs, so we can skip those, as
	 * in AcquireRewriteLocks.
	 */
	if (viewquery->hasSubLinks)
	{
		acquireLocksOnSubLinks_context context;

		context.for_execute = true;
		query_tree_walker(viewquery, acquireLocksOnSubLinks, &context,
						  QTW_IGNORE_RC_SUBQUERIES);
	}

	/*
	 * Create a new target RTE describing the base relation, and add it to the
	 * outer query's rangetable.  (What's happening in the next few steps is
	 * very much like what the planner would do to "pull up" the view into the
	 * outer query.  Perhaps someday we should refactor things enough so that
	 * we can share code with the planner.)
	 *
	 * Be sure to set rellockmode to the correct thing for the target table.
	 * Since we copied the whole viewquery above, we can just scribble on
	 * base_rte instead of copying it.
	 */
	new_rte = base_rte;
	new_rte->rellockmode = RowExclusiveLock;

	parsetree->rtable = lappend(parsetree->rtable, new_rte);
	new_rt_index = list_length(parsetree->rtable);

	/*
	 * INSERTs never inherit.  For UPDATE/DELETE/MERGE, we use the view
	 * query's inheritance flag for the base relation.
	 */
	if (parsetree->commandType == CMD_INSERT)
		new_rte->inh = false;

	/*
	 * Adjust the view's targetlist Vars to reference the new target RTE, ie
	 * make their varnos be new_rt_index instead of base_rt_index.  There can
	 * be no Vars for other rels in the tlist, so this is sufficient to pull
	 * up the tlist expressions for use in the outer query.  The tlist will
	 * provide the replacement expressions used by ReplaceVarsFromTargetList
	 * below.
	 */
	view_targetlist = viewquery->targetList;

	ChangeVarNodes((Node *) view_targetlist,
				   base_rt_index,
				   new_rt_index,
				   0);

	/*
	 * If the view has "security_invoker" set, mark the new target relation
	 * for the permissions checks that we want to enforce against the query
	 * caller. Otherwise we want to enforce them against the view owner.
	 *
	 * At the relation level, require the same INSERT/UPDATE/DELETE
	 * permissions that the query caller needs against the view.  We drop the
	 * ACL_SELECT bit that is presumably in new_perminfo->requiredPerms
	 * initially.
	 *
	 * Note: the original view's RTEPermissionInfo remains in the query's
	 * rteperminfos so that the executor still performs appropriate
	 * permissions checks for the query caller's use of the view.
	 *
	 * Disregard the perminfo in viewquery->rteperminfos that the base_rte
	 * would currently be pointing at, because we'd like it to point now to a
	 * new one that will be filled below.  Must set perminfoindex to 0 to not
	 * trip over the Assert in addRTEPermissionInfo().
	 */
	new_rte->perminfoindex = 0;
	new_perminfo = addRTEPermissionInfo(&parsetree->rteperminfos, new_rte);
	if (RelationHasSecurityInvoker(view))
		new_perminfo->checkAsUser = InvalidOid;
	else
		new_perminfo->checkAsUser = view->rd_rel->relowner;
	new_perminfo->requiredPerms = view_perminfo->requiredPerms;

	/*
	 * Now for the per-column permissions bits.
	 *
	 * Initially, new_perminfo (base_perminfo) contains selectedCols
	 * permission check bits for all base-rel columns referenced by the view,
	 * but since the view is a SELECT query its insertedCols/updatedCols is
	 * empty.  We set insertedCols and updatedCols to include all the columns
	 * the outer query is trying to modify, adjusting the column numbers as
	 * needed.  But we leave selectedCols as-is, so the view owner must have
	 * read permission for all columns used in the view definition, even if
	 * some of them are not read by the outer query.  We could try to limit
	 * selectedCols to only columns used in the transformed query, but that
	 * does not correspond to what happens in ordinary SELECT usage of a view:
	 * all referenced columns must have read permission, even if optimization
	 * finds that some of them can be discarded during query transformation.
	 * The flattening we're doing here is an optional optimization, too.  (If
	 * you are unpersuaded and want to change this, note that applying
	 * adjust_view_column_set to view_perminfo->selectedCols is clearly *not*
	 * the right answer, since that neglects base-rel columns used in the
	 * view's WHERE quals.)
	 *
	 * This step needs the modified view targetlist, so we have to do things
	 * in this order.
	 */
	Assert(bms_is_empty(new_perminfo->insertedCols) &&
		   bms_is_empty(new_perminfo->updatedCols));

	new_perminfo->selectedCols = base_perminfo->selectedCols;

	new_perminfo->insertedCols =
		adjust_view_column_set(view_perminfo->insertedCols, view_targetlist);

	new_perminfo->updatedCols =
		adjust_view_column_set(view_perminfo->updatedCols, view_targetlist);

	/*
	 * Move any security barrier quals from the view RTE onto the new target
	 * RTE.  Any such quals should now apply to the new target RTE and will
	 * not reference the original view RTE in the rewritten query.
	 */
	new_rte->securityQuals = view_rte->securityQuals;
	view_rte->securityQuals = NIL;

	/*
	 * Now update all Vars in the outer query that reference the view to
	 * reference the appropriate column of the base relation instead.
	 */
	parsetree = (Query *)
		ReplaceVarsFromTargetList((Node *) parsetree,
								  parsetree->resultRelation,
								  0,
								  view_rte,
								  view_targetlist,
								  new_rt_index,
								  REPLACEVARS_REPORT_ERROR,
								  0,
								  NULL);

	/*
	 * Update all other RTI references in the query that point to the view
	 * (for example, parsetree->resultRelation itself) to point to the new
	 * base relation instead.  Vars will not be affected since none of them
	 * reference parsetree->resultRelation any longer.
	 */
	ChangeVarNodes((Node *) parsetree,
				   parsetree->resultRelation,
				   new_rt_index,
				   0);
	Assert(parsetree->resultRelation == new_rt_index);

	/*
	 * For INSERT/UPDATE we must also update resnos in the targetlist to refer
	 * to columns of the base relation, since those indicate the target
	 * columns to be affected.  Similarly, for MERGE we must update the resnos
	 * in the merge action targetlists of any INSERT/UPDATE actions.
	 *
	 * Note that this destroys the resno ordering of the targetlists, but that
	 * will be fixed when we recurse through RewriteQuery, which will invoke
	 * rewriteTargetListIU again on the updated targetlists.
	 */
	if (parsetree->commandType != CMD_DELETE)
	{
		foreach(lc, parsetree->targetList)
		{
			TargetEntry *tle = (TargetEntry *) lfirst(lc);
			TargetEntry *view_tle;

			if (tle->resjunk)
				continue;

			view_tle = get_tle_by_resno(view_targetlist, tle->resno);
			if (view_tle != NULL && !view_tle->resjunk && IsA(view_tle->expr, Var))
				tle->resno = ((Var *) view_tle->expr)->varattno;
			else
				elog(ERROR, "attribute number %d not found in view targetlist",
					 tle->resno);
		}

		foreach_node(MergeAction, action, parsetree->mergeActionList)
		{
			if (action->commandType == CMD_INSERT ||
				action->commandType == CMD_UPDATE)
			{
				foreach_node(TargetEntry, tle, action->targetList)
				{
					TargetEntry *view_tle;

					if (tle->resjunk)
						continue;

					view_tle = get_tle_by_resno(view_targetlist, tle->resno);
					if (view_tle != NULL && !view_tle->resjunk && IsA(view_tle->expr, Var))
						tle->resno = ((Var *) view_tle->expr)->varattno;
					else
						elog(ERROR, "attribute number %d not found in view targetlist",
							 tle->resno);
				}
			}
		}
	}

	/*
	 * For INSERT .. ON CONFLICT .. DO SELECT/UPDATE, we must also update
	 * assorted stuff in the onConflict data structure.
	 */
	if (parsetree->onConflict &&
		(parsetree->onConflict->action == ONCONFLICT_UPDATE ||
		 parsetree->onConflict->action == ONCONFLICT_SELECT))
	{
		Index		old_exclRelIndex,
					new_exclRelIndex;
		ParseNamespaceItem *new_exclNSItem;
		RangeTblEntry *new_exclRte;
		List	   *tmp_tlist;

		/*
		 * For ON CONFLICT DO UPDATE, update the resnos in the auxiliary
		 * UPDATE targetlist to refer to columns of the base relation.
		 */
		foreach(lc, parsetree->onConflict->onConflictSet)
		{
			TargetEntry *tle = (TargetEntry *) lfirst(lc);
			TargetEntry *view_tle;

			if (tle->resjunk)
				continue;

			view_tle = get_tle_by_resno(view_targetlist, tle->resno);
			if (view_tle != NULL && !view_tle->resjunk && IsA(view_tle->expr, Var))
				tle->resno = ((Var *) view_tle->expr)->varattno;
			else
				elog(ERROR, "attribute number %d not found in view targetlist",
					 tle->resno);
		}

		/*
		 * Create a new RTE for the EXCLUDED pseudo-relation, using the
		 * query's new base rel (which may well have a different column list
		 * from the view, hence we need a new column alias list).  This should
		 * match transformOnConflictClause.  In particular, note that the
		 * relkind is set to composite to signal that we're not dealing with
		 * an actual relation.
		 */
		old_exclRelIndex = parsetree->onConflict->exclRelIndex;

		new_exclNSItem = addRangeTableEntryForRelation(make_parsestate(NULL),
													   base_rel,
													   RowExclusiveLock,
													   makeAlias("excluded", NIL),
													   false, false);
		new_exclRte = new_exclNSItem->p_rte;
		new_exclRte->relkind = RELKIND_COMPOSITE_TYPE;
		/* Ignore the RTEPermissionInfo that would've been added. */
		new_exclRte->perminfoindex = 0;

		parsetree->rtable = lappend(parsetree->rtable, new_exclRte);
		new_exclRelIndex = parsetree->onConflict->exclRelIndex =
			list_length(parsetree->rtable);

		/*
		 * Replace the targetlist for the EXCLUDED pseudo-relation with a new
		 * one, representing the columns from the new base relation.
		 */
		parsetree->onConflict->exclRelTlist =
			BuildOnConflictExcludedTargetlist(base_rel, new_exclRelIndex);

		/*
		 * Update all Vars in the ON CONFLICT clause that refer to the old
		 * EXCLUDED pseudo-relation.  We want to use the column mappings
		 * defined in the view targetlist, but we need the outputs to refer to
		 * the new EXCLUDED pseudo-relation rather than the new target RTE.
		 * Also notice that "EXCLUDED.*" will be expanded using the view's
		 * rowtype, which seems correct.
		 */
		tmp_tlist = copyObject(view_targetlist);

		ChangeVarNodes((Node *) tmp_tlist, new_rt_index,
					   new_exclRelIndex, 0);

		parsetree->onConflict = (OnConflictExpr *)
			ReplaceVarsFromTargetList((Node *) parsetree->onConflict,
									  old_exclRelIndex,
									  0,
									  view_rte,
									  tmp_tlist,
									  new_rt_index,
									  REPLACEVARS_REPORT_ERROR,
									  0,
									  &parsetree->hasSubLinks);
	}

	if (parsetree->forPortionOf && parsetree->commandType == CMD_UPDATE)
	{
		/*
		 * Like the INSERT/UPDATE code above, update the resnos in the
		 * auxiliary UPDATE targetlist to refer to columns of the base
		 * relation.
		 */
		foreach(lc, parsetree->forPortionOf->rangeTargetList)
		{
			TargetEntry *tle = (TargetEntry *) lfirst(lc);
			TargetEntry *view_tle;

			if (tle->resjunk)
				continue;

			view_tle = get_tle_by_resno(view_targetlist, tle->resno);
			if (view_tle != NULL && !view_tle->resjunk && IsA(view_tle->expr, Var))
				tle->resno = ((Var *) view_tle->expr)->varattno;
			else
				elog(ERROR, "attribute number %d not found in view targetlist",
					 tle->resno);
		}
	}

	/*
	 * For UPDATE/DELETE/MERGE, pull up any WHERE quals from the view.  We
	 * know that any Vars in the quals must reference the one base relation,
	 * so we need only adjust their varnos to reference the new target (just
	 * the same as we did with the view targetlist).
	 *
	 * If it's a security-barrier view, its WHERE quals must be applied before
	 * quals from the outer query, so we attach them to the RTE as security
	 * barrier quals rather than adding them to the main WHERE clause.
	 *
	 * For INSERT, the view's quals can be ignored in the main query.
	 */
	if (parsetree->commandType != CMD_INSERT &&
		viewquery->jointree->quals != NULL)
	{
		Node	   *viewqual = (Node *) viewquery->jointree->quals;

		/*
		 * Even though we copied viewquery already at the top of this
		 * function, we must duplicate the viewqual again here, because we may
		 * need to use the quals again below for a WithCheckOption clause.
		 */
		viewqual = copyObject(viewqual);

		ChangeVarNodes(viewqual, base_rt_index, new_rt_index, 0);

		if (RelationIsSecurityView(view))
		{
			/*
			 * The view's quals go in front of existing barrier quals: those
			 * would have come from an outer level of security-barrier view,
			 * and so must get evaluated later.
			 *
			 * Note: the parsetree has been mutated, so the new_rte pointer is
			 * stale and needs to be re-computed.
			 */
			new_rte = rt_fetch(new_rt_index, parsetree->rtable);
			new_rte->securityQuals = lcons(viewqual, new_rte->securityQuals);

			/*
			 * Do not set parsetree->hasRowSecurity, because these aren't RLS
			 * conditions (they aren't affected by enabling/disabling RLS).
			 */

			/*
			 * Make sure that the query is marked correctly if the added qual
			 * has sublinks.
			 */
			if (!parsetree->hasSubLinks)
				parsetree->hasSubLinks = checkExprHasSubLink(viewqual);
		}
		else
			AddQual(parsetree, viewqual);
	}

	/*
	 * For INSERT/UPDATE (or MERGE containing INSERT/UPDATE), if the view has
	 * the WITH CHECK OPTION, or any parent view specified WITH CASCADED CHECK
	 * OPTION, add the quals from the view to the query's withCheckOptions
	 * list.
	 */
	if (insert_or_update)
	{
		bool		has_wco = RelationHasCheckOption(view);
		bool		cascaded = RelationHasCascadedCheckOption(view);

		/*
		 * If the parent view has a cascaded check option, treat this view as
		 * if it also had a cascaded check option.
		 *
		 * New WithCheckOptions are added to the start of the list, so if
		 * there is a cascaded check option, it will be the first item in the
		 * list.
		 */
		if (parsetree->withCheckOptions != NIL)
		{
			WithCheckOption *parent_wco =
				(WithCheckOption *) linitial(parsetree->withCheckOptions);

			if (parent_wco->cascaded)
			{
				has_wco = true;
				cascaded = true;
			}
		}

		/*
		 * Add the new WithCheckOption to the start of the list, so that
		 * checks on inner views are run before checks on outer views, as
		 * required by the SQL standard.
		 *
		 * If the new check is CASCADED, we need to add it even if this view
		 * has no quals, since there may be quals on child views.  A LOCAL
		 * check can be omitted if this view has no quals.
		 */
		if (has_wco && (cascaded || viewquery->jointree->quals != NULL))
		{
			WithCheckOption *wco;

			wco = makeNode(WithCheckOption);
			wco->kind = WCO_VIEW_CHECK;
			wco->relname = pstrdup(RelationGetRelationName(view));
			wco->polname = NULL;
			wco->qual = NULL;
			wco->cascaded = cascaded;

			parsetree->withCheckOptions = lcons(wco,
												parsetree->withCheckOptions);

			if (viewquery->jointree->quals != NULL)
			{
				wco->qual = (Node *) viewquery->jointree->quals;
				ChangeVarNodes(wco->qual, base_rt_index, new_rt_index, 0);

				/*
				 * For INSERT, make sure that the query is marked correctly if
				 * the added qual has sublinks.  This can be skipped for
				 * UPDATE/MERGE, since the same qual will have already been
				 * added above, and the check will already have been done.
				 */
				if (!parsetree->hasSubLinks &&
					parsetree->commandType == CMD_INSERT)
					parsetree->hasSubLinks = checkExprHasSubLink(wco->qual);
			}
		}
	}

	table_close(base_rel, NoLock);

	return parsetree;
}


/*
 * ============================================================================
 * 【中文注释】RewriteQuery —— 对单个查询应用所有规则并递归改写生成的产品查询
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   查询重写的核心：对一个查询（SELECT 之外的 INSERT/UPDATE/DELETE/MERGE）先
 *   重写其目标列表，再匹配并触发该关系上的规则（fireRules），对可自动更新视图
 *   执行 rewriteTargetView，随后把所有产品查询（规则动作、改写后的视图查询）
 *   递归重写，最后按语义决定原查询是否保留/以何形式保留，返回最终要执行的
 *   查询列表。
 *
 * 参数：
 *   parsetree         - 待重写的查询。
 *   rewrite_events    - 当前已打开的重写动作（relation, event）列表，用于检测
 *                       无限递归。
 *   orig_rt_length    - 源查询 rtable 的长度：对 fireRules 产生的产品查询传源值，
 *                       用于跳过其中已处理的 VALUES RTE；否则为 0。
 *   num_ctes_processed- 已重写过的、位于 cteList 末尾的 CTE 数（避免重复改写 CTE
 *                       导致生成列表达式被展开两次而报错）。
 *
 * 返回值：
 *   List * - 重写后的查询列表（0 个或多个 Query）。
 *
 * 设计思想：
 *   1. 先递归处理 WITH 中的数据修改 CTE（须先于规则触发，因为 CTE 可能被拷入规则
 *      动作）。对单个 DO INSTEAD 动作把改写结果写回 CTE 节点；不支持的条件规则、
 *      DO ALSO、多语句 INSTEAD 规则、NOTHING 规则在 WITH 数据修改语句中都会报错。
 *   2. 对非 SELECT/UTILITY 命令：打开结果关系（假定已加锁），针对命令类型重写
 *      targetList：
 *      - INSERT：找 VALUES RTE（多行插入），用 rewriteTargetListIU 处理主列表与
 *        ON CONFLICT DO UPDATE 列表，rewriteValuesRTE 处理 VALUES 中的 DEFAULT；
 *      - UPDATE：处理 FOR PORTION OF 的限定与列（视图留待递归处理），然后
 *        rewriteTargetListIU；
 *      - MERGE：对每个动作的 targetList 分别 rewriteTargetListIU；
 *      - DELETE：仅处理 FOR PORTION OF 限定。
 *   3. matchLocks 收集规则，fireRules 产出产品查询；若 VALUES 中仍有未处理的
 *      DEFAULT 且存在产品查询，对每个产品查询的 VALUES RTE 用
 *      rewriteValuesRTEToNulls 收尾。
 *   4. 若没有无条件 INSTEAD 规则、目标是视图且无 INSTEAD OF 触发器，则尝试
 *      rewriteTargetView 自动更新（存在条件 INSTEAD 规则会使其失败）；改写结果按
 *      INSERT 前置 / 其他后置插入 product_queries，并把 instead/returning 置位
 *      防止原查询被重复加入。
 *   5. 对每个产品查询先做无限递归检查（rewrite_events 中 (relation,event) 重复即
 *      报错），压入当前事件后递归 RewriteQuery，再弹出事件。
 *   6. 若存在 INSTEAD 或条件 INSTEAD 而原查询带 RETURNING，但规则未改写 RETURNING，
 *      报错（因为 RETURNING 必须来自无条件 INSTEAD 规则）；ON CONFLICT 与带规则
 *      的表不兼容（可自动更新视图除外）。
 *   7. 最终组装：无条件 INSTEAD 规则存在时原查询完全不执行；否则 INSERT 的原查询
 *      放最前（先插后执行，保证后面扫描能看到），UPDATE/DELETE 放最后（先执行规则
 *      动作，避免命令计数器前进后动作扫描不到被删/被改的行）；存在条件 INSTEAD 时
 *      用叠加反向条件的 qual_product 替代原查询。
 *   8. 若原查询带 CTE 且改写出多个非 utility 查询则报错（每个查询都会拷贝同一份
 *      CTE，违反 CTE 只求值一次的语义）。
 * ============================================================================
 */
static List *
RewriteQuery(Query *parsetree, List *rewrite_events, int orig_rt_length,
			 int num_ctes_processed)
{
	CmdType		event = parsetree->commandType;
	bool		instead = false;
	bool		returning = false;
	bool		updatableview = false;
	Query	   *qual_product = NULL;
	List	   *rewritten = NIL;
	ListCell   *lc1;

	/*
	 * First, recursively process any insert/update/delete/merge statements in
	 * WITH clauses.  (We have to do this first because the WITH clauses may
	 * get copied into rule actions below.)
	 *
	 * Any new WITH clauses from rule actions are processed when we recurse
	 * into product queries below.  However, when recursing, we must take care
	 * to avoid rewriting a CTE query more than once (because expanding
	 * generated columns in the targetlist more than once would fail).  Since
	 * new CTEs from product queries are added to the start of the list (see
	 * rewriteRuleAction), we just skip the last num_ctes_processed items.
	 */
	foreach(lc1, parsetree->cteList)
	{
		CommonTableExpr *cte = lfirst_node(CommonTableExpr, lc1);
		Query	   *ctequery = castNode(Query, cte->ctequery);
		int			i = foreach_current_index(lc1);
		List	   *newstuff;

		/* Skip already-processed CTEs at the end of the list */
		if (i >= list_length(parsetree->cteList) - num_ctes_processed)
			break;

		if (ctequery->commandType == CMD_SELECT)
			continue;

		newstuff = RewriteQuery(ctequery, rewrite_events, 0, 0);

		/*
		 * Currently we can only handle unconditional, single-statement DO
		 * INSTEAD rules correctly; we have to get exactly one non-utility
		 * Query out of the rewrite operation to stuff back into the CTE node.
		 */
		if (list_length(newstuff) == 1)
		{
			/* Must check it's not a utility command */
			ctequery = linitial_node(Query, newstuff);
			if (!(ctequery->commandType == CMD_SELECT ||
				  ctequery->commandType == CMD_UPDATE ||
				  ctequery->commandType == CMD_INSERT ||
				  ctequery->commandType == CMD_DELETE ||
				  ctequery->commandType == CMD_MERGE))
			{
				/*
				 * Currently it could only be NOTIFY; this error message will
				 * need work if we ever allow other utility commands in rules.
				 */
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("DO INSTEAD NOTIFY rules are not supported for data-modifying statements in WITH")));
			}
			/* WITH queries should never be canSetTag */
			Assert(!ctequery->canSetTag);
			/* Push the single Query back into the CTE node */
			cte->ctequery = (Node *) ctequery;
		}
		else if (newstuff == NIL)
		{
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("DO INSTEAD NOTHING rules are not supported for data-modifying statements in WITH")));
		}
		else
		{
			ListCell   *lc2;

			/* examine queries to determine which error message to issue */
			foreach(lc2, newstuff)
			{
				Query	   *q = (Query *) lfirst(lc2);

				if (q->querySource == QSRC_QUAL_INSTEAD_RULE)
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("conditional DO INSTEAD rules are not supported for data-modifying statements in WITH")));
				if (q->querySource == QSRC_NON_INSTEAD_RULE)
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("DO ALSO rules are not supported for data-modifying statements in WITH")));
			}

			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("multi-statement DO INSTEAD rules are not supported for data-modifying statements in WITH")));
		}
	}
	num_ctes_processed = list_length(parsetree->cteList);

	/*
	 * If the statement is an insert, update, delete, or merge, adjust its
	 * targetlist as needed, and then fire INSERT/UPDATE/DELETE rules on it.
	 *
	 * SELECT rules are handled later when we have all the queries that should
	 * get executed.  Also, utilities aren't rewritten at all (do we still
	 * need that check?)
	 */
	if (event != CMD_SELECT && event != CMD_UTILITY)
	{
		int			result_relation;
		RangeTblEntry *rt_entry;
		Relation	rt_entry_relation;
		List	   *locks;
		int			product_orig_rt_length;
		List	   *product_queries;
		bool		hasUpdate = false;
		int			values_rte_index = 0;
		bool		defaults_remaining = false;

		result_relation = parsetree->resultRelation;
		Assert(result_relation != 0);
		rt_entry = rt_fetch(result_relation, parsetree->rtable);
		Assert(rt_entry->rtekind == RTE_RELATION);

		/*
		 * We can use NoLock here since either the parser or
		 * AcquireRewriteLocks should have locked the rel already.
		 */
		rt_entry_relation = relation_open(rt_entry->relid, NoLock);

		/* We don't support FOR PORTION OF on views with INSTEAD OF triggers. */
		if (parsetree->forPortionOf &&
			rt_entry_relation->rd_rel->relkind == RELKIND_VIEW &&
			view_has_instead_trigger(rt_entry_relation, event, NIL))
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("views with INSTEAD OF triggers do not support FOR PORTION OF")));

		/*
		 * Rewrite the targetlist as needed for the command type.
		 */
		if (event == CMD_INSERT)
		{
			ListCell   *lc2;
			RangeTblEntry *values_rte = NULL;

			/*
			 * Test if it's a multi-row INSERT ... VALUES (...), (...), ... by
			 * looking for a VALUES RTE in the fromlist.  For product queries,
			 * we must ignore any already-processed VALUES RTEs from the
			 * original query.  These appear at the start of the rangetable.
			 */
			foreach(lc2, parsetree->jointree->fromlist)
			{
				RangeTblRef *rtr = (RangeTblRef *) lfirst(lc2);

				if (IsA(rtr, RangeTblRef) && rtr->rtindex > orig_rt_length)
				{
					RangeTblEntry *rte = rt_fetch(rtr->rtindex,
												  parsetree->rtable);

					if (rte->rtekind == RTE_VALUES)
					{
						/* should not find more than one VALUES RTE */
						if (values_rte != NULL)
							elog(ERROR, "more than one VALUES RTE found");

						values_rte = rte;
						values_rte_index = rtr->rtindex;
					}
				}
			}

			if (values_rte)
			{
				Bitmapset  *unused_values_attrnos = NULL;

				/* Process the main targetlist ... */
				parsetree->targetList = rewriteTargetListIU(parsetree->targetList,
															parsetree->commandType,
															parsetree->override,
															rt_entry_relation,
															values_rte,
															values_rte_index,
															&unused_values_attrnos);
				/* ... and the VALUES expression lists */
				if (!rewriteValuesRTE(parsetree, values_rte, values_rte_index,
									  rt_entry_relation,
									  unused_values_attrnos))
					defaults_remaining = true;
			}
			else
			{
				/* Process just the main targetlist */
				parsetree->targetList =
					rewriteTargetListIU(parsetree->targetList,
										parsetree->commandType,
										parsetree->override,
										rt_entry_relation,
										NULL, 0, NULL);
			}

			if (parsetree->onConflict &&
				parsetree->onConflict->action == ONCONFLICT_UPDATE)
			{
				parsetree->onConflict->onConflictSet =
					rewriteTargetListIU(parsetree->onConflict->onConflictSet,
										CMD_UPDATE,
										parsetree->override,
										rt_entry_relation,
										NULL, 0, NULL);
			}
		}
		else if (event == CMD_UPDATE)
		{
			Assert(parsetree->override == OVERRIDING_NOT_SET);

			if (parsetree->forPortionOf)
			{
				/*
				 * Don't add FOR PORTION OF details until we're done rewriting
				 * a view update, so that we don't add the same qual and TLE
				 * on the recursion.
				 *
				 * Views don't need to do anything special here to remap Vars;
				 * that is handled by the tree walker.
				 */
				if (rt_entry_relation->rd_rel->relkind != RELKIND_VIEW)
				{
					ListCell   *tl;

					/*
					 * Add qual: UPDATE FOR PORTION OF should be limited to
					 * rows that overlap the target range.
					 */
					AddQual(parsetree, parsetree->forPortionOf->overlapsExpr);

					/* Update FOR PORTION OF column(s) automatically. */
					foreach(tl, parsetree->forPortionOf->rangeTargetList)
					{
						TargetEntry *tle = (TargetEntry *) lfirst(tl);

						parsetree->targetList = lappend(parsetree->targetList, tle);
					}
				}
			}

			parsetree->targetList =
				rewriteTargetListIU(parsetree->targetList,
									parsetree->commandType,
									parsetree->override,
									rt_entry_relation,
									NULL, 0, NULL);
		}
		else if (event == CMD_MERGE)
		{
			Assert(parsetree->override == OVERRIDING_NOT_SET);

			/*
			 * Rewrite each action targetlist separately
			 */
			foreach(lc1, parsetree->mergeActionList)
			{
				MergeAction *action = (MergeAction *) lfirst(lc1);

				switch (action->commandType)
				{
					case CMD_NOTHING:
					case CMD_DELETE:	/* Nothing to do here */
						break;
					case CMD_UPDATE:
					case CMD_INSERT:

						/*
						 * MERGE actions do not permit multi-row INSERTs, so
						 * there is no VALUES RTE to deal with here.
						 */
						action->targetList =
							rewriteTargetListIU(action->targetList,
												action->commandType,
												action->override,
												rt_entry_relation,
												NULL, 0, NULL);
						break;
					default:
						elog(ERROR, "unrecognized commandType: %d", action->commandType);
						break;
				}
			}
		}
		else if (event == CMD_DELETE)
		{
			if (parsetree->forPortionOf)
			{
				/*
				 * Don't add FOR PORTION OF details until we're done rewriting
				 * a view delete, so that we don't add the same qual on the
				 * recursion.
				 *
				 * Views don't need to do anything special here to remap Vars;
				 * that is handled by the tree walker.
				 */
				if (rt_entry_relation->rd_rel->relkind != RELKIND_VIEW)
				{
					/*
					 * Add qual: DELETE FOR PORTION OF should be limited to
					 * rows that overlap the target range.
					 */
					AddQual(parsetree, parsetree->forPortionOf->overlapsExpr);
				}
			}
		}
		else
			elog(ERROR, "unrecognized commandType: %d", (int) event);

		/*
		 * Collect and apply the appropriate rules.
		 */
		locks = matchLocks(event, rt_entry_relation,
						   result_relation, parsetree, &hasUpdate);

		product_orig_rt_length = list_length(parsetree->rtable);
		product_queries = fireRules(parsetree,
									result_relation,
									event,
									locks,
									&instead,
									&returning,
									&qual_product);

		/*
		 * If we have a VALUES RTE with any remaining untouched DEFAULT items,
		 * and we got any product queries, finalize the VALUES RTE for each
		 * product query (replacing the remaining DEFAULT items with NULLs).
		 * We don't do this for the original query, because we know that it
		 * must be an auto-insert on a view, and so should use the base
		 * relation's defaults for any remaining DEFAULT items.
		 */
		if (defaults_remaining && product_queries != NIL)
		{
			ListCell   *n;

			/*
			 * Each product query has its own copy of the VALUES RTE at the
			 * same index in the rangetable, so we must finalize each one.
			 *
			 * Note that if the product query is an INSERT ... SELECT, then
			 * the VALUES RTE will be at the same index in the SELECT part of
			 * the product query rather than the top-level product query
			 * itself.
			 */
			foreach(n, product_queries)
			{
				Query	   *pt = (Query *) lfirst(n);
				RangeTblEntry *values_rte;

				if (pt->commandType == CMD_INSERT &&
					pt->jointree && IsA(pt->jointree, FromExpr) &&
					list_length(pt->jointree->fromlist) == 1)
				{
					Node	   *jtnode = (Node *) linitial(pt->jointree->fromlist);

					if (IsA(jtnode, RangeTblRef))
					{
						int			rtindex = ((RangeTblRef *) jtnode)->rtindex;
						RangeTblEntry *src_rte = rt_fetch(rtindex, pt->rtable);

						if (src_rte->rtekind == RTE_SUBQUERY &&
							src_rte->subquery &&
							IsA(src_rte->subquery, Query) &&
							src_rte->subquery->commandType == CMD_SELECT)
							pt = src_rte->subquery;
					}
				}

				values_rte = rt_fetch(values_rte_index, pt->rtable);
				if (values_rte->rtekind != RTE_VALUES)
					elog(ERROR, "failed to find VALUES RTE in product query");

				rewriteValuesRTEToNulls(pt, values_rte);
			}
		}

		/*
		 * If there was no unqualified INSTEAD rule, and the target relation
		 * is a view without any INSTEAD OF triggers, see if the view can be
		 * automatically updated.  If so, we perform the necessary query
		 * transformation here and add the resulting query to the
		 * product_queries list, so that it gets recursively rewritten if
		 * necessary.  For MERGE, the view must be automatically updatable if
		 * any of the merge actions lack a corresponding INSTEAD OF trigger.
		 *
		 * If the view cannot be automatically updated, we throw an error here
		 * which is OK since the query would fail at runtime anyway.  Throwing
		 * the error here is preferable to the executor check since we have
		 * more detailed information available about why the view isn't
		 * updatable.
		 */
		if (!instead &&
			rt_entry_relation->rd_rel->relkind == RELKIND_VIEW &&
			!view_has_instead_trigger(rt_entry_relation, event,
									  parsetree->mergeActionList))
		{
			/*
			 * If there were any qualified INSTEAD rules, don't allow the view
			 * to be automatically updated (an unqualified INSTEAD rule or
			 * INSTEAD OF trigger is required).
			 */
			if (qual_product != NULL)
				error_view_not_updatable(rt_entry_relation,
										 parsetree->commandType,
										 parsetree->mergeActionList,
										 gettext_noop("Views with conditional DO INSTEAD rules are not automatically updatable."));

			/*
			 * Attempt to rewrite the query to automatically update the view.
			 * This throws an error if the view can't be automatically
			 * updated.
			 */
			parsetree = rewriteTargetView(parsetree, rt_entry_relation);

			/*
			 * At this point product_queries contains any DO ALSO rule
			 * actions. Add the rewritten query before or after those.  This
			 * must match the handling the original query would have gotten
			 * below, if we allowed it to be included again.
			 */
			if (parsetree->commandType == CMD_INSERT)
				product_queries = lcons(parsetree, product_queries);
			else
				product_queries = lappend(product_queries, parsetree);

			/*
			 * Set the "instead" flag, as if there had been an unqualified
			 * INSTEAD, to prevent the original query from being included a
			 * second time below.  The transformation will have rewritten any
			 * RETURNING list, so we can also set "returning" to forestall
			 * throwing an error below.
			 */
			instead = true;
			returning = true;
			updatableview = true;
		}

		/*
		 * If we got any product queries, recursively rewrite them --- but
		 * first check for recursion!
		 */
		if (product_queries != NIL)
		{
			ListCell   *n;
			rewrite_event *rev;

			foreach(n, rewrite_events)
			{
				rev = (rewrite_event *) lfirst(n);
				if (rev->relation == RelationGetRelid(rt_entry_relation) &&
					rev->event == event)
					ereport(ERROR,
							(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
							 errmsg("infinite recursion detected in rules for relation \"%s\"",
									RelationGetRelationName(rt_entry_relation))));
			}

			rev = palloc_object(rewrite_event);
			rev->relation = RelationGetRelid(rt_entry_relation);
			rev->event = event;
			rewrite_events = lappend(rewrite_events, rev);

			foreach(n, product_queries)
			{
				Query	   *pt = (Query *) lfirst(n);
				List	   *newstuff;

				/*
				 * For an updatable view, pt might be the rewritten version of
				 * the original query, in which case we pass on orig_rt_length
				 * to finish processing any VALUES RTE it contained.
				 *
				 * Otherwise, we have a product query created by fireRules().
				 * Any VALUES RTEs from the original query have been fully
				 * processed, and must be skipped when we recurse.
				 */
				newstuff = RewriteQuery(pt, rewrite_events,
										pt == parsetree ?
										orig_rt_length :
										product_orig_rt_length,
										num_ctes_processed);
				rewritten = list_concat(rewritten, newstuff);
			}

			rewrite_events = list_delete_last(rewrite_events);
		}

		/*
		 * If there is an INSTEAD, and the original query has a RETURNING, we
		 * have to have found a RETURNING in the rule(s), else fail. (Because
		 * DefineQueryRewrite only allows RETURNING in unconditional INSTEAD
		 * rules, there's no need to worry whether the substituted RETURNING
		 * will actually be executed --- it must be.)
		 */
		if ((instead || qual_product != NULL) &&
			parsetree->returningList &&
			!returning)
		{
			switch (event)
			{
				case CMD_INSERT:
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot perform INSERT RETURNING on relation \"%s\"",
									RelationGetRelationName(rt_entry_relation)),
							 errhint("You need an unconditional ON INSERT DO INSTEAD rule with a RETURNING clause.")));
					break;
				case CMD_UPDATE:
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot perform UPDATE RETURNING on relation \"%s\"",
									RelationGetRelationName(rt_entry_relation)),
							 errhint("You need an unconditional ON UPDATE DO INSTEAD rule with a RETURNING clause.")));
					break;
				case CMD_DELETE:
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot perform DELETE RETURNING on relation \"%s\"",
									RelationGetRelationName(rt_entry_relation)),
							 errhint("You need an unconditional ON DELETE DO INSTEAD rule with a RETURNING clause.")));
					break;
				default:
					elog(ERROR, "unrecognized commandType: %d",
						 (int) event);
					break;
			}
		}

		/*
		 * Updatable views are supported by ON CONFLICT, so don't prevent that
		 * case from proceeding
		 */
		if (parsetree->onConflict &&
			(product_queries != NIL || hasUpdate) &&
			!updatableview)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("INSERT with ON CONFLICT clause cannot be used with table that has INSERT or UPDATE rules")));

		table_close(rt_entry_relation, NoLock);
	}

	/*
	 * For INSERTs, the original query is done first; for UPDATE/DELETE, it is
	 * done last.  This is needed because update and delete rule actions might
	 * not do anything if they are invoked after the update or delete is
	 * performed. The command counter increment between the query executions
	 * makes the deleted (and maybe the updated) tuples disappear so the scans
	 * for them in the rule actions cannot find them.
	 *
	 * If we found any unqualified INSTEAD, the original query is not done at
	 * all, in any form.  Otherwise, we add the modified form if qualified
	 * INSTEADs were found, else the unmodified form.
	 */
	if (!instead)
	{
		if (parsetree->commandType == CMD_INSERT)
		{
			if (qual_product != NULL)
				rewritten = lcons(qual_product, rewritten);
			else
				rewritten = lcons(parsetree, rewritten);
		}
		else
		{
			if (qual_product != NULL)
				rewritten = lappend(rewritten, qual_product);
			else
				rewritten = lappend(rewritten, parsetree);
		}
	}

	/*
	 * If the original query has a CTE list, and we generated more than one
	 * non-utility result query, we have to fail because we'll have copied the
	 * CTE list into each result query.  That would break the expectation of
	 * single evaluation of CTEs.  This could possibly be fixed by
	 * restructuring so that a CTE list can be shared across multiple Query
	 * and PlannableStatement nodes.
	 */
	if (parsetree->cteList != NIL)
	{
		int			qcount = 0;

		foreach(lc1, rewritten)
		{
			Query	   *q = (Query *) lfirst(lc1);

			if (q->commandType != CMD_UTILITY)
				qcount++;
		}
		if (qcount > 1)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("WITH cannot be used in a query that is rewritten by rules into multiple queries")));
	}

	return rewritten;
}


/*
 * ============================================================================
 * 【中文注释】get_generated_columns —— 获取表的生成列定义列表
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历表描述符，收集所有生成列（stored 与/或 virtual），为每列构造包含其生成
 *   表达式（引用列号已调整为给定 rt_index）的 TargetEntry 列表。这些条目用于
 *   替换规则动作/条件中 new.generated_col 引用，或用于展开表达式中的 virtual
 *   生成列。
 *
 * 参数：
 *   rel           - 目标关系。
 *   rt_index      - 生成表达式里 Var 应引用的 rtable 下标（规则场景下是 NEW 的
 *                   varno，即 PRS2_NEW_VARNO + rt_length）。
 *   include_stored- true 时同时返回 stored 与 virtual 生成列；false 时仅 virtual。
 *
 * 返回值：
 *   List * - TargetEntry 列表，每项 resno 为生成列属性号、expr 为生成表达式。
 *
 * 设计思想：
 *   1. 先看 TupleDesc 的约束标志（has_generated_virtual / has_generated_stored）
 *      快速判断是否需要遍历，避免无生成列时白白扫描。
 *   2. 每个生成表达式用 build_generation_expression 从目录读出（含必要的 COLLATE
 *      包裹），再 ChangeVarNodes 把 varno 1 调整为 rt_index。
 *   3. 生成表达式内部引用 new.attribute，因此返回前通常还要再经
 *      ReplaceVarsFromTargetList 用查询 targetList 替换 NEW——调用方负责此步。
 * ============================================================================
 */
static List *
get_generated_columns(Relation rel, int rt_index, bool include_stored)
{
	List	   *gen_cols = NIL;
	TupleDesc	tupdesc;

	tupdesc = RelationGetDescr(rel);
	if (tupdesc->constr &&
		(tupdesc->constr->has_generated_virtual ||
		 (include_stored && tupdesc->constr->has_generated_stored)))
	{
		for (int i = 0; i < tupdesc->natts; i++)
		{
			Form_pg_attribute attr = TupleDescAttr(tupdesc, i);

			if (attr->attgenerated == ATTRIBUTE_GENERATED_VIRTUAL ||
				(include_stored && attr->attgenerated == ATTRIBUTE_GENERATED_STORED))
			{
				Node	   *defexpr;
				TargetEntry *te;

				defexpr = build_generation_expression(rel, i + 1);
				ChangeVarNodes(defexpr, 1, rt_index, 0);

				te = makeTargetEntry((Expr *) defexpr, i + 1, 0, false);
				gen_cols = lappend(gen_cols, te);
			}
		}
	}

	return gen_cols;
}

/*
 * ============================================================================
 * 【中文注释】expand_generated_columns_in_expr —— 在独立表达式中展开 virtual 生成列
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把给定表达式中对 virtual 生成列的引用（Var）替换为对应的生成表达式。用于
 *   不属于查询树本身的表达式，如默认值表达式、索引谓词等，其 rt_index 通常为 1。
 *
 * 参数：
 *   node    - 待展开的表达式（可能被就地改写，返回新表达式）。
 *   rel     - 生成列所属的关系。
 *   rt_index- 表达式中的 Var 所引用的 rtable 下标（通常为 1）。
 *
 * 返回值：
 *   Node * - 展开后的表达式。
 *
 * 设计思想：
 *   1. 只有存在 virtual 生成列时才需要处理（stored 生成列的值在行级计算，无需
 *      内联展开到表达式里）。
 *   2. 手工构造一个临时 RTE_RELATION RTE（eref 名称无关紧要）以调用
 *      ReplaceVarsFromTargetList，用 get_generated_columns(rel, rt_index, false)
 *      得到的表达式列表做替换，模式 REPLACEVARS_CHANGE_VARNO 保持 varno 映射。
 *   3. 外层 hasSubLinks 传 NULL 是安全的：生成表达式不可能包含 SubLink，替换不会
 *      引入新的子链接。
 * ============================================================================
 */
Node *
expand_generated_columns_in_expr(Node *node, Relation rel, int rt_index)
{
	TupleDesc	tupdesc = RelationGetDescr(rel);

	if (tupdesc->constr && tupdesc->constr->has_generated_virtual)
	{
		RangeTblEntry *rte;
		List	   *vcols;

		rte = makeNode(RangeTblEntry);
		/* eref needs to be set, but the actual name doesn't matter */
		rte->eref = makeAlias(RelationGetRelationName(rel), NIL);
		rte->rtekind = RTE_RELATION;
		rte->relid = RelationGetRelid(rel);

		vcols = get_generated_columns(rel, rt_index, false);

		if (vcols)
		{
			/*
			 * Passing NULL for outer_hasSubLinks is safe because generation
			 * expressions cannot contain SubLinks, so the replacement cannot
			 * introduce any.
			 */
			node = ReplaceVarsFromTargetList(node, rt_index, 0, rte, vcols, 0,
											 REPLACEVARS_CHANGE_VARNO, rt_index,
											 NULL);
		}
	}

	return node;
}

/*
 * ============================================================================
 * 【中文注释】build_generation_expression —— 构造生成列的计算表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   取出指定生成列的生成表达式：其存储形态与列默认值一致（生成定义存放在
 *   pg_attrdef），因此复用 build_column_default 读取，并补上列定义中指定的
 *   COLLATE 约束。若找不到生成表达式则报错。
 *
 * 参数：
 *   rel    - 目标关系。
 *   attrno - 生成列属性号（从 1 开始）。
 *
 * 返回值：
 *   Node * - 生成表达式树。
 *
 * 设计思想：
 *   1. 断言列确为 virtual/stored 生成列且表存在生成列约束，否则是内部错误。
 *   2. build_column_default 对生成列会跳过类型级默认值、直接返回目录中的生成
 *      定义表达式（生成列在此处相当于"必须存在的默认值"）；返回 NULL 说明目录
 *      数据损坏，elog 报错。
 *   3. 若列声明了排序规则（attcollation）且与表达式推算的排序规则不同，则用
 *      CollateExpr 包裹强制指定，保证语义与列定义一致。
 * ============================================================================
 */
Node *
build_generation_expression(Relation rel, int attrno)
{
	TupleDesc	rd_att = RelationGetDescr(rel);
	Form_pg_attribute att_tup = TupleDescAttr(rd_att, attrno - 1);
	Node	   *defexpr;
	Oid			attcollid;

	Assert(rd_att->constr &&
		   (rd_att->constr->has_generated_virtual ||
			rd_att->constr->has_generated_stored));
	Assert(att_tup->attgenerated == ATTRIBUTE_GENERATED_VIRTUAL ||
		   att_tup->attgenerated == ATTRIBUTE_GENERATED_STORED);

	defexpr = build_column_default(rel, attrno);
	if (defexpr == NULL)
		elog(ERROR, "no generation expression found for column number %d of table \"%s\"",
			 attrno, RelationGetRelationName(rel));

	/*
	 * If the column definition has a collation and it is different from the
	 * collation of the generation expression, put a COLLATE clause around the
	 * expression.
	 */
	attcollid = att_tup->attcollation;
	if (attcollid && attcollid != exprCollation(defexpr))
	{
		CollateExpr *ce = makeNode(CollateExpr);

		ce->arg = (Expr *) defexpr;
		ce->collOid = attcollid;
		ce->location = -1;

		defexpr = (Node *) ce;
	}

	return defexpr;
}


/*
 * ============================================================================
 * 【中文注释】QueryRewrite —— 查询重写系统的主入口
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对一个查询执行完整的重写流程：先由 RewriteQuery 应用所有非 SELECT 规则
 *  （INSERT/UPDATE/DELETE/MERGE），再由 fireRIRrules 对每条结果查询展开视图
 *  （RIR 规则），最后统一决定哪条查询负责设置命令结果标签（canSetTag），返回
 *  0 个或多个待执行的查询。
 *
 * 参数：
 *   parsetree - 待重写的查询，必须是顶层原始查询（querySource == QSRC_ORIGINAL
 *               且 canSetTag）。它必须来自解析器，或已被 AcquireRewriteLocks
 *               加过合适锁。
 *
 * 返回值：
 *   List * - 重写后的查询列表，可能为空。
 *
 * 设计思想：
 *   1. 分三步：
 *      - Step 1：RewriteQuery(parsetree, NIL, 0, 0) 应用非 SELECT 规则，可能得到
 *        0 个或多个查询（规则动作、视图改写产物等）；
 *      - Step 2：对每条查询调用 fireRIRrules(query, NIL) 展开其中的视图，并顺手
 *        把原始 queryId 写回每个结果查询；
 *      - Step 3：扫描结果列表决定 canSetTag：若原查询仍在列表中则由它设标签；
 *        否则由最后一条与原始命令同类型的 INSTEAD 查询设置；都不满足则无查询设
 *        标签（tcop 层会用原始查询构造默认标签兜底）。
 *   2. 断言保证列表中至多一条 canSetTag 的查询；非断言编译时可提前跳出循环。
 *   3. 视图展开（fireRIRrules）放在非 SELECT 规则之后，因为规则动作里可能引入
 *      新的视图引用，需要在最终执行前全部展开。
 * ============================================================================
 */
List *
QueryRewrite(Query *parsetree)
{
	int64		input_query_id = parsetree->queryId;
	List	   *querylist;
	List	   *results;
	ListCell   *l;
	CmdType		origCmdType;
	bool		foundOriginalQuery;
	Query	   *lastInstead;

	/*
	 * This function is only applied to top-level original queries
	 */
	Assert(parsetree->querySource == QSRC_ORIGINAL);
	Assert(parsetree->canSetTag);

	/*
	 * Step 1
	 *
	 * Apply all non-SELECT rules possibly getting 0 or many queries
	 */
	querylist = RewriteQuery(parsetree, NIL, 0, 0);

	/*
	 * Step 2
	 *
	 * Apply all the RIR rules on each query
	 *
	 * This is also a handy place to mark each query with the original queryId
	 */
	results = NIL;
	foreach(l, querylist)
	{
		Query	   *query = (Query *) lfirst(l);

		query = fireRIRrules(query, NIL);

		query->queryId = input_query_id;

		results = lappend(results, query);
	}

	/*
	 * Step 3
	 *
	 * Determine which, if any, of the resulting queries is supposed to set
	 * the command-result tag; and update the canSetTag fields accordingly.
	 *
	 * If the original query is still in the list, it sets the command tag.
	 * Otherwise, the last INSTEAD query of the same kind as the original is
	 * allowed to set the tag.  (Note these rules can leave us with no query
	 * setting the tag.  The tcop code has to cope with this by setting up a
	 * default tag based on the original un-rewritten query.)
	 *
	 * The Asserts verify that at most one query in the result list is marked
	 * canSetTag.  If we aren't checking asserts, we can fall out of the loop
	 * as soon as we find the original query.
	 */
	origCmdType = parsetree->commandType;
	foundOriginalQuery = false;
	lastInstead = NULL;

	foreach(l, results)
	{
		Query	   *query = (Query *) lfirst(l);

		if (query->querySource == QSRC_ORIGINAL)
		{
			Assert(query->canSetTag);
			Assert(!foundOriginalQuery);
			foundOriginalQuery = true;
#ifndef USE_ASSERT_CHECKING
			break;
#endif
		}
		else
		{
			Assert(!query->canSetTag);
			if (query->commandType == origCmdType &&
				(query->querySource == QSRC_INSTEAD_RULE ||
				 query->querySource == QSRC_QUAL_INSTEAD_RULE))
				lastInstead = query;
		}
	}

	if (!foundOriginalQuery && lastInstead != NULL)
		lastInstead->canSetTag = true;

	return results;
}
