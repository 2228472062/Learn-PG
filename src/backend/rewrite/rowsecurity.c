/*
 * rewrite/rowsecurity.c
 *	  Routines to support policies for row-level security (aka RLS).
 *
 * Policies in PostgreSQL provide a mechanism to limit what records are
 * returned to a user and what records a user is permitted to add to a table.
 *
 * Policies can be defined for specific roles, specific commands, or provided
 * by an extension.  Row security can also be enabled for a table without any
 * policies being explicitly defined, in which case a default-deny policy is
 * applied.
 *
 * Any part of the system which is returning records back to the user, or
 * which is accepting records from the user to add to a table, needs to
 * consider the policies associated with the table (if any).  For normal
 * queries, this is handled by calling get_row_security_policies() during
 * rewrite, for each RTE in the query.  This returns the expressions defined
 * by the table's policies as a list that is prepended to the securityQuals
 * list for the RTE.  For queries which modify the table, any WITH CHECK
 * clauses from the table's policies are also returned and prepended to the
 * list of WithCheckOptions for the Query to check each row that is being
 * added to the table.  Other parts of the system (eg: COPY) simply construct
 * a normal query and use that, if RLS is to be applied.
 *
 * The check to see if RLS should be enabled is provided through
 * check_enable_rls(), which returns an enum (defined in rowsecurity.h) to
 * indicate if RLS should be enabled (RLS_ENABLED), or bypassed (RLS_NONE or
 * RLS_NONE_ENV).  RLS_NONE_ENV indicates that RLS should be bypassed
 * in the current environment, but that may change if the row_security GUC or
 * the current role changes.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 */
#include "postgres.h"

#include "access/table.h"
#include "catalog/pg_class.h"
#include "catalog/pg_type.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/pg_list.h"
#include "parser/parse_relation.h"
#include "rewrite/rewriteDefine.h"
#include "rewrite/rewriteManip.h"
#include "rewrite/rowsecurity.h"
#include "utils/acl.h"
#include "utils/rel.h"
#include "utils/rls.h"

static void get_policies_for_relation(Relation relation,
									  CmdType cmd, Oid user_id,
									  List **permissive_policies,
									  List **restrictive_policies);

static void sort_policies_by_name(List *policies);

static int	row_security_policy_cmp(const ListCell *a, const ListCell *b);

static void add_security_quals(int rt_index,
							   List *permissive_policies,
							   List *restrictive_policies,
							   List **securityQuals,
							   bool *hasSubLinks);

static void add_with_check_options(Relation rel,
								   int rt_index,
								   WCOKind kind,
								   List *permissive_policies,
								   List *restrictive_policies,
								   List **withCheckOptions,
								   bool *hasSubLinks,
								   bool force_using);

static bool check_role_for_policy(ArrayType *policy_roles, Oid user_id);

/*
 * hooks to allow extensions to add their own security policies
 *
 * row_security_policy_hook_permissive can be used to add policies which
 * are combined with the other permissive policies, using OR.
 *
 * row_security_policy_hook_restrictive can be used to add policies which
 * are enforced, regardless of other policies (they are combined using AND).
 */
row_security_policy_hook_type row_security_policy_hook_permissive = NULL;
row_security_policy_hook_type row_security_policy_hook_restrictive = NULL;

/*
 * ============================================================================
 * 【中文注释】get_row_security_policies —— 获取 RTE 需要应用的行级安全限制表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   查询改写（rewrite）阶段的核心入口函数：为查询中的每一个 RTE（RangeTblEntry）
 *   检查其对应表是否启用了行级安全（RLS），若启用则根据命令类型与当前角色收集
 *   相关策略，并生成两类结果——用于限制"读"现有行的安全表达式（securityQuals）
 *   和用于校验"写"入行的 WITH CHECK 表达式（withCheckOptions），分别附加到 RTE
 *   与 Query 上。这是所有普通查询（包括 COPY 间接构造的查询）应用 RLS 的入口。
 *
 * 参数：
 *   root            - 当前正在改写的 Query 结构体，用于读取命令类型、目标关系索引、
 *                     FOR PORTION OF、ON CONFLICT、RETURNING 等信息。
 *   rte             - 待处理的关系 RTE，其 rtekind 必须是 RTE_RELATION。
 *   rt_index        - 该 RTE 在查询范围表（rtable）中的位置（从 1 开始）。
 *   securityQuals   - 输出参数，指向 RTE 安全表达式链表的指针，新增的"读"限制
 *                     表达式被追加到该链表中。
 *   withCheckOptions- 输出参数，指向 Query 的 WithCheckOptions 链表的指针，新增的
 *                     "写"校验选项被追加到该链表中。
 *   hasRowSecurity  - 输出参数，置为 true 表示该查询涉及 RLS（哪怕本 RTE 没有实际
 *                     限制表达式），供 plancache 判断是否需要因环境变化而重规划。
 *   hasSubLinks     - 输出参数，若返回的任何表达式包含子链接则置为 true。
 *
 * 返回值：
 *   无。所有结果通过上述输出参数返回。
 *
 * 设计思想：
 *   1. 先做快速路径判断：非普通关系（如索引、序列等）直接返回；调用
 *      check_enable_rls() 得到 RLS 状态，RLS_NONE 表示未启用直接返回，
 *      RLS_NONE_ENV 表示当前环境绕过但环境（GUC、角色）可能变化，因此仍把
 *      hasRowSecurity 置为 true 以强制环境变化时重规划。
 *   2. 身份确定：优先使用 RTE 的 checkAsUser（权限模拟用户），否则用当前用户
 *      GetUserId()，保证定义者安全与权限模拟场景下策略按正确身份生效。
 *   3. 策略收集与命令类型的关系是本函数最复杂的部分：目标关系使用查询自身的
 *      命令类型，FROM 子句中的非目标关系一律按 CMD_SELECT 处理；当查询要求更新
 *      权限（FOR UPDATE/SHARE）时额外取 UPDATE 策略，当要求 SELECT 权限
 *      （RETURNING、WHERE 引用列、ON CONFLICT、MERGE 等）时额外取 SELECT 策略，
 *      各类 USING 表达式按"高特权（UPDATE/DELETE 锁行）优先、SELECT 次之"的
 *      顺序追加到 securityQuals，与普通 ACL 权限要求的顺序保持一致。
 *   4. 写操作（INSERT/UPDATE/MERGE、ON CONFLICT、FOR PORTION OF 的补插）通过
 *      add_with_check_options 生成 WithCheckOption 附加到 Query，因为新增行违反
 *      策略必须报错而不是被静默丢弃。
 *   5. 收尾时调用 setRuleCheckAsUser 把 checkAsUser 传播到所有生成的表达式中，
 *      确保表达式内部子查询仍以正确的模拟身份执行，并把 hasRowSecurity 置 true。
 *   6. 打开的关系只加 NoLock：RLS 依赖的策略树随系统目录缓存失效自动重建，
 *      此处仅读取策略，无需额外锁，避免与其他环节发生锁顺序冲突。
 * ============================================================================
 */
void
get_row_security_policies(Query *root, RangeTblEntry *rte, int rt_index,
						  List **securityQuals, List **withCheckOptions,
						  bool *hasRowSecurity, bool *hasSubLinks)
{
	Oid			user_id;
	int			rls_status;
	Relation	rel;
	CmdType		commandType;
	List	   *permissive_policies;
	List	   *restrictive_policies;
	RTEPermissionInfo *perminfo;

	/* Defaults for the return values */
	*securityQuals = NIL;
	*withCheckOptions = NIL;
	*hasRowSecurity = false;
	*hasSubLinks = false;

	Assert(rte->rtekind == RTE_RELATION);

	/* If this is not a normal relation, just return immediately */
	if (rte->relkind != RELKIND_RELATION &&
		rte->relkind != RELKIND_PARTITIONED_TABLE)
		return;

	perminfo = getRTEPermissionInfo(root->rteperminfos, rte);

	/* Switch to checkAsUser if it's set */
	user_id = OidIsValid(perminfo->checkAsUser) ?
		perminfo->checkAsUser : GetUserId();

	/* Determine the state of RLS for this, pass checkAsUser explicitly */
	rls_status = check_enable_rls(rte->relid, perminfo->checkAsUser, false);

	/* If there is no RLS on this table at all, nothing to do */
	if (rls_status == RLS_NONE)
		return;

	/*
	 * RLS_NONE_ENV means we are not doing any RLS now, but that may change
	 * with changes to the environment, so we mark it as hasRowSecurity to
	 * force a re-plan when the environment changes.
	 */
	if (rls_status == RLS_NONE_ENV)
	{
		/*
		 * Indicate that this query may involve RLS and must therefore be
		 * replanned if the environment changes (GUCs, role), but we are not
		 * adding anything here.
		 */
		*hasRowSecurity = true;

		return;
	}

	/*
	 * RLS is enabled for this relation.
	 *
	 * Get the security policies that should be applied, based on the command
	 * type.  Note that if this isn't the target relation, we actually want
	 * the relation's SELECT policies, regardless of the query command type,
	 * for example in UPDATE t1 ... FROM t2 we need to apply t1's UPDATE
	 * policies and t2's SELECT policies.
	 */
	rel = table_open(rte->relid, NoLock);

	commandType = rt_index == root->resultRelation ?
		root->commandType : CMD_SELECT;

	/*
	 * In some cases, we need to apply USING policies (which control the
	 * visibility of records) associated with multiple command types (see
	 * specific cases below).
	 *
	 * When considering the order in which to apply these USING policies, we
	 * prefer to apply higher privileged policies, those which allow the user
	 * to lock records (UPDATE and DELETE), first, followed by policies which
	 * don't (SELECT).
	 *
	 * Note that the optimizer is free to push down and reorder quals which
	 * use leakproof functions.
	 *
	 * In all cases, if there are no policy clauses allowing access to rows in
	 * the table for the specific type of operation, then a single
	 * always-false clause (a default-deny policy) will be added (see
	 * add_security_quals).
	 */

	/*
	 * For a SELECT, if UPDATE privileges are required (eg: the user has
	 * specified FOR [KEY] UPDATE/SHARE), then add the UPDATE USING quals
	 * first.
	 *
	 * This way, we filter out any records from the SELECT FOR SHARE/UPDATE
	 * which the user does not have access to via the UPDATE USING policies,
	 * similar to how we require normal UPDATE rights for these queries.
	 */
	if (commandType == CMD_SELECT && perminfo->requiredPerms & ACL_UPDATE)
	{
		List	   *update_permissive_policies;
		List	   *update_restrictive_policies;

		get_policies_for_relation(rel, CMD_UPDATE, user_id,
								  &update_permissive_policies,
								  &update_restrictive_policies);

		add_security_quals(rt_index,
						   update_permissive_policies,
						   update_restrictive_policies,
						   securityQuals,
						   hasSubLinks);
	}

	/*
	 * For SELECT, UPDATE and DELETE, add security quals to enforce the USING
	 * policies.  These security quals control access to existing table rows.
	 * Restrictive policies are combined together using AND, and permissive
	 * policies are combined together using OR.
	 */

	get_policies_for_relation(rel, commandType, user_id, &permissive_policies,
							  &restrictive_policies);

	if (commandType == CMD_SELECT ||
		commandType == CMD_UPDATE ||
		commandType == CMD_DELETE)
		add_security_quals(rt_index,
						   permissive_policies,
						   restrictive_policies,
						   securityQuals,
						   hasSubLinks);

	/*
	 * Similar to above, during an UPDATE, DELETE, or MERGE, if SELECT rights
	 * are also required (eg: when a RETURNING clause exists, or the user has
	 * provided a WHERE clause which involves columns from the relation), we
	 * collect up CMD_SELECT policies and add them via add_security_quals
	 * first.
	 *
	 * This way, we filter out any records which are not visible through an
	 * ALL or SELECT USING policy.
	 */
	if ((commandType == CMD_UPDATE || commandType == CMD_DELETE ||
		 commandType == CMD_MERGE) &&
		perminfo->requiredPerms & ACL_SELECT)
	{
		List	   *select_permissive_policies;
		List	   *select_restrictive_policies;

		get_policies_for_relation(rel, CMD_SELECT, user_id,
								  &select_permissive_policies,
								  &select_restrictive_policies);

		add_security_quals(rt_index,
						   select_permissive_policies,
						   select_restrictive_policies,
						   securityQuals,
						   hasSubLinks);
	}

	/*
	 * For INSERT and UPDATE, add withCheckOptions to verify that any new
	 * records added are consistent with the security policies.  This will use
	 * each policy's WITH CHECK clause, or its USING clause if no explicit
	 * WITH CHECK clause is defined.
	 */
	if (commandType == CMD_INSERT || commandType == CMD_UPDATE)
	{
		/* This should be the target relation */
		Assert(rt_index == root->resultRelation);

		add_with_check_options(rel, rt_index,
							   commandType == CMD_INSERT ?
							   WCO_RLS_INSERT_CHECK : WCO_RLS_UPDATE_CHECK,
							   permissive_policies,
							   restrictive_policies,
							   withCheckOptions,
							   hasSubLinks,
							   false);

		/*
		 * Get and add ALL/SELECT policies, if SELECT rights are required for
		 * this relation (eg: when RETURNING is used).  These are added as WCO
		 * policies rather than security quals to ensure that an error is
		 * raised if a policy is violated; otherwise, we might end up silently
		 * dropping rows to be added.
		 */
		if (perminfo->requiredPerms & ACL_SELECT)
		{
			List	   *select_permissive_policies = NIL;
			List	   *select_restrictive_policies = NIL;

			get_policies_for_relation(rel, CMD_SELECT, user_id,
									  &select_permissive_policies,
									  &select_restrictive_policies);
			add_with_check_options(rel, rt_index,
								   commandType == CMD_INSERT ?
								   WCO_RLS_INSERT_CHECK : WCO_RLS_UPDATE_CHECK,
								   select_permissive_policies,
								   select_restrictive_policies,
								   withCheckOptions,
								   hasSubLinks,
								   true);
		}

		/*
		 * For INSERT ... ON CONFLICT DO SELECT/UPDATE we need additional
		 * policy checks for the SELECT/UPDATE which may be applied to the
		 * same RTE.
		 */
		if (commandType == CMD_INSERT && root->onConflict &&
			(root->onConflict->action == ONCONFLICT_UPDATE ||
			 root->onConflict->action == ONCONFLICT_SELECT))
		{
			List	   *conflict_permissive_policies = NIL;
			List	   *conflict_restrictive_policies = NIL;
			List	   *conflict_select_permissive_policies = NIL;
			List	   *conflict_select_restrictive_policies = NIL;

			if (perminfo->requiredPerms & ACL_UPDATE)
			{
				/*
				 * Get the policies that apply to the auxiliary UPDATE or
				 * SELECT FOR UPDATE/SHARE.
				 */
				get_policies_for_relation(rel, CMD_UPDATE, user_id,
										  &conflict_permissive_policies,
										  &conflict_restrictive_policies);

				/*
				 * Enforce the USING clauses of the UPDATE policies using WCOs
				 * rather than security quals.  This ensures that an error is
				 * raised if the conflicting row cannot be updated/locked due
				 * to RLS, rather than the change being silently dropped.
				 */
				add_with_check_options(rel, rt_index,
									   WCO_RLS_CONFLICT_CHECK,
									   conflict_permissive_policies,
									   conflict_restrictive_policies,
									   withCheckOptions,
									   hasSubLinks,
									   true);
			}

			/*
			 * Get and add ALL/SELECT policies, as WCO_RLS_CONFLICT_CHECK WCOs
			 * to ensure they are considered when taking the SELECT/UPDATE
			 * path of an INSERT .. ON CONFLICT, if SELECT rights are required
			 * for this relation, also as WCO policies, again, to avoid
			 * silently dropping data.  See above.
			 */
			if (perminfo->requiredPerms & ACL_SELECT)
			{
				get_policies_for_relation(rel, CMD_SELECT, user_id,
										  &conflict_select_permissive_policies,
										  &conflict_select_restrictive_policies);
				add_with_check_options(rel, rt_index,
									   WCO_RLS_CONFLICT_CHECK,
									   conflict_select_permissive_policies,
									   conflict_select_restrictive_policies,
									   withCheckOptions,
									   hasSubLinks,
									   true);
			}

			/*
			 * For INSERT .. ON CONFLICT DO UPDATE, add additional policies to
			 * be checked when the auxiliary UPDATE is executed.
			 */
			if (root->onConflict->action == ONCONFLICT_UPDATE)
			{
				/* Enforce the WITH CHECK clauses of the UPDATE policies */
				add_with_check_options(rel, rt_index,
									   WCO_RLS_UPDATE_CHECK,
									   conflict_permissive_policies,
									   conflict_restrictive_policies,
									   withCheckOptions,
									   hasSubLinks,
									   false);

				/*
				 * Add ALL/SELECT policies as WCO_RLS_UPDATE_CHECK WCOs, to
				 * ensure that the final updated row is visible when taking
				 * the UPDATE path of an INSERT .. ON CONFLICT, if SELECT
				 * rights are required for this relation.
				 */
				if (perminfo->requiredPerms & ACL_SELECT)
					add_with_check_options(rel, rt_index,
										   WCO_RLS_UPDATE_CHECK,
										   conflict_select_permissive_policies,
										   conflict_select_restrictive_policies,
										   withCheckOptions,
										   hasSubLinks,
										   true);
			}
		}
	}

	/*
	 * UPDATE/DELETE FOR PORTION OF may insert leftover rows to preserve the
	 * portions of the old row not covered by the target range.  Those hidden
	 * inserts go through ExecInsert(), so they need the same INSERT RLS WITH
	 * CHECK options as ordinary INSERTs.  SELECT rights are never needed for
	 * the leftover rows, because they are not considered by RETURNING.
	 */
	if (root->forPortionOf != NULL && rt_index == root->resultRelation &&
		(commandType == CMD_UPDATE || commandType == CMD_DELETE))
	{
		List	   *insert_permissive_policies;
		List	   *insert_restrictive_policies;

		get_policies_for_relation(rel, CMD_INSERT, user_id,
								  &insert_permissive_policies,
								  &insert_restrictive_policies);
		add_with_check_options(rel, rt_index,
							   WCO_RLS_INSERT_CHECK,
							   insert_permissive_policies,
							   insert_restrictive_policies,
							   withCheckOptions,
							   hasSubLinks,
							   false);
	}

	/*
	 * FOR MERGE, we fetch policies for UPDATE, DELETE and INSERT (and ALL)
	 * and set them up so that we can enforce the appropriate policy depending
	 * on the final action we take.
	 *
	 * We already fetched the SELECT policies above, to check existing rows,
	 * but we must also check that new rows created by INSERT/UPDATE actions
	 * are visible, if SELECT rights are required. For INSERT actions, we only
	 * do this if RETURNING is specified, to be consistent with a plain INSERT
	 * command, which can only require SELECT rights when RETURNING is used.
	 *
	 * We don't push the UPDATE/DELETE USING quals to the RTE because we don't
	 * really want to apply them while scanning the relation since we don't
	 * know whether we will be doing an UPDATE or a DELETE at the end. We
	 * apply the respective policy once we decide the final action on the
	 * target tuple.
	 *
	 * XXX We are setting up USING quals as WITH CHECK. If RLS prohibits
	 * UPDATE/DELETE on the target row, we shall throw an error instead of
	 * silently ignoring the row. This is different than how normal
	 * UPDATE/DELETE works and more in line with INSERT ON CONFLICT DO
	 * SELECT/UPDATE handling.
	 */
	if (commandType == CMD_MERGE)
	{
		List	   *merge_update_permissive_policies;
		List	   *merge_update_restrictive_policies;
		List	   *merge_delete_permissive_policies;
		List	   *merge_delete_restrictive_policies;
		List	   *merge_insert_permissive_policies;
		List	   *merge_insert_restrictive_policies;
		List	   *merge_select_permissive_policies = NIL;
		List	   *merge_select_restrictive_policies = NIL;

		/*
		 * Fetch the UPDATE policies and set them up to execute on the
		 * existing target row before doing UPDATE.
		 */
		get_policies_for_relation(rel, CMD_UPDATE, user_id,
								  &merge_update_permissive_policies,
								  &merge_update_restrictive_policies);

		/*
		 * WCO_RLS_MERGE_UPDATE_CHECK is used to check UPDATE USING quals on
		 * the existing target row.
		 */
		add_with_check_options(rel, rt_index,
							   WCO_RLS_MERGE_UPDATE_CHECK,
							   merge_update_permissive_policies,
							   merge_update_restrictive_policies,
							   withCheckOptions,
							   hasSubLinks,
							   true);

		/* Enforce the WITH CHECK clauses of the UPDATE policies */
		add_with_check_options(rel, rt_index,
							   WCO_RLS_UPDATE_CHECK,
							   merge_update_permissive_policies,
							   merge_update_restrictive_policies,
							   withCheckOptions,
							   hasSubLinks,
							   false);

		/*
		 * Add ALL/SELECT policies as WCO_RLS_UPDATE_CHECK WCOs, to ensure
		 * that the updated row is visible when executing an UPDATE action, if
		 * SELECT rights are required for this relation.
		 */
		if (perminfo->requiredPerms & ACL_SELECT)
		{
			get_policies_for_relation(rel, CMD_SELECT, user_id,
									  &merge_select_permissive_policies,
									  &merge_select_restrictive_policies);
			add_with_check_options(rel, rt_index,
								   WCO_RLS_UPDATE_CHECK,
								   merge_select_permissive_policies,
								   merge_select_restrictive_policies,
								   withCheckOptions,
								   hasSubLinks,
								   true);
		}

		/*
		 * Fetch the DELETE policies and set them up to execute on the
		 * existing target row before doing DELETE.
		 */
		get_policies_for_relation(rel, CMD_DELETE, user_id,
								  &merge_delete_permissive_policies,
								  &merge_delete_restrictive_policies);

		/*
		 * WCO_RLS_MERGE_DELETE_CHECK is used to check DELETE USING quals on
		 * the existing target row.
		 */
		add_with_check_options(rel, rt_index,
							   WCO_RLS_MERGE_DELETE_CHECK,
							   merge_delete_permissive_policies,
							   merge_delete_restrictive_policies,
							   withCheckOptions,
							   hasSubLinks,
							   true);

		/*
		 * No special handling is required for INSERT policies. They will be
		 * checked and enforced during ExecInsert(). But we must add them to
		 * withCheckOptions.
		 */
		get_policies_for_relation(rel, CMD_INSERT, user_id,
								  &merge_insert_permissive_policies,
								  &merge_insert_restrictive_policies);

		add_with_check_options(rel, rt_index,
							   WCO_RLS_INSERT_CHECK,
							   merge_insert_permissive_policies,
							   merge_insert_restrictive_policies,
							   withCheckOptions,
							   hasSubLinks,
							   false);

		/*
		 * Add ALL/SELECT policies as WCO_RLS_INSERT_CHECK WCOs, to ensure
		 * that the inserted row is visible when executing an INSERT action,
		 * if RETURNING is specified and SELECT rights are required for this
		 * relation.
		 */
		if (perminfo->requiredPerms & ACL_SELECT && root->returningList)
			add_with_check_options(rel, rt_index,
								   WCO_RLS_INSERT_CHECK,
								   merge_select_permissive_policies,
								   merge_select_restrictive_policies,
								   withCheckOptions,
								   hasSubLinks,
								   true);
	}

	table_close(rel, NoLock);

	/*
	 * Copy checkAsUser to the row security quals and WithCheckOption checks,
	 * in case they contain any subqueries referring to other relations.
	 */
	setRuleCheckAsUser((Node *) *securityQuals, perminfo->checkAsUser);
	setRuleCheckAsUser((Node *) *withCheckOptions, perminfo->checkAsUser);

	/*
	 * Mark this query as having row security, so plancache can invalidate it
	 * when necessary (eg: role changes)
	 */
	*hasRowSecurity = true;
}

/*
 * ============================================================================
 * 【中文注释】get_policies_for_relation —— 按命令类型与角色收集关系的全部适用策略
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从关系的 relcache 描述符（rd_rsdesc）中取出该表定义的所有行级安全策略，
 *   按"命令类型是否匹配"与"是否适用于指定角色"两个条件过滤后，分别整理成
 *   permissive（宽松型，OR 组合）与 restrictive（限制型，AND 组合）两个策略
 *   链表。此外还会把扩展通过 row_security_policy_hook_* 钩子提供的策略一并并入。
 *
 * 参数：
 *   relation            - 已打开的目标关系，要求其 rd_rsdesc 已加载（含策略信息）。
 *   cmd                 - 命令类型（CMD_SELECT/INSERT/UPDATE/DELETE/MERGE），决定
 *                         只收集匹配该命令的策略；'*'（ALL）策略始终匹配。
 *   user_id             - 判断策略适用性的角色 OID。
 *   permissive_policies - 输出参数，收集到的宽松策略链表（内部策略在前，钩子策略
 *                         追加在后）。
 *   restrictive_policies- 输出参数，收集到的限制策略链表（内置与钩子策略各按名称
 *                         排序，且内置在前、钩子在后）。
 *
 * 返回值：
 *   无。结果通过两个输出链表返回；可能为空链表（表示当前命令下无适用策略）。
 *
 * 设计思想：
 *   1. 策略的 polcmd 字段用单个字符表示命令（如 'r' 表示 SELECT），'*' 表示
 *      ALL。遍历关系策略时对命令逐一匹配；CMD_MERGE 没有独立策略，因此从其他
 *      命令的策略中推导，本函数不匹配 MERGE 专用策略。
 *   2. 角色匹配复用 check_role_for_policy()：策略 roles 数组含 ACL_ID_PUBLIC，
 *      或包含对 user_id 有权限成员关系的角色时即适用。
 *   3. 限制型策略被按名称排序（sort_policies_by_name），且刻意保持"内置在前、
 *      钩子在后"的顺序：restrictive 策略各生成独立的 WithCheckOption，为保证
 *      校验顺序可预测、错误报告稳定，排序是必须的；而 permissive 策略最终被
 *      OR 成一个表达式，顺序无关紧要，故无需排序。
 *   4. 钩子策略直接追加到内部策略之后，其中钩子的 restrictive 策略同样先排序；
 *      钩子未注册时静默跳过，不影响内置逻辑。
 *   5. 本函数只收集策略指针，不复制、不修改策略本体；真正的表达式变换
 *      （ChangeVarNodes、OR/AND 合并）发生在 add_security_quals 与
 *      add_with_check_options 中。
 * ============================================================================
 */
static void
get_policies_for_relation(Relation relation, CmdType cmd, Oid user_id,
						  List **permissive_policies,
						  List **restrictive_policies)
{
	ListCell   *item;

	*permissive_policies = NIL;
	*restrictive_policies = NIL;

	/* First find all internal policies for the relation. */
	foreach(item, relation->rd_rsdesc->policies)
	{
		bool		cmd_matches = false;
		RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);

		/* Always add ALL policies, if they exist. */
		if (policy->polcmd == '*')
			cmd_matches = true;
		else
		{
			/* Check whether the policy applies to the specified command type */
			switch (cmd)
			{
				case CMD_SELECT:
					if (policy->polcmd == ACL_SELECT_CHR)
						cmd_matches = true;
					break;
				case CMD_INSERT:
					if (policy->polcmd == ACL_INSERT_CHR)
						cmd_matches = true;
					break;
				case CMD_UPDATE:
					if (policy->polcmd == ACL_UPDATE_CHR)
						cmd_matches = true;
					break;
				case CMD_DELETE:
					if (policy->polcmd == ACL_DELETE_CHR)
						cmd_matches = true;
					break;
				case CMD_MERGE:

					/*
					 * We do not support a separate policy for MERGE command.
					 * Instead it derives from the policies defined for other
					 * commands.
					 */
					break;
				default:
					elog(ERROR, "unrecognized policy command type %d",
						 (int) cmd);
					break;
			}
		}

		/*
		 * Add this policy to the relevant list of policies if it applies to
		 * the specified role.
		 */
		if (cmd_matches && check_role_for_policy(policy->roles, user_id))
		{
			if (policy->permissive)
				*permissive_policies = lappend(*permissive_policies, policy);
			else
				*restrictive_policies = lappend(*restrictive_policies, policy);
		}
	}

	/*
	 * We sort restrictive policies by name so that any WCOs they generate are
	 * checked in a well-defined order.
	 */
	sort_policies_by_name(*restrictive_policies);

	/*
	 * Then add any permissive or restrictive policies defined by extensions.
	 * These are simply appended to the lists of internal policies, if they
	 * apply to the specified role.
	 */
	if (row_security_policy_hook_restrictive)
	{
		List	   *hook_policies =
			(*row_security_policy_hook_restrictive) (cmd, relation);

		/*
		 * As with built-in restrictive policies, we sort any hook-provided
		 * restrictive policies by name also.  Note that we also intentionally
		 * always check all built-in restrictive policies, in name order,
		 * before checking restrictive policies added by hooks, in name order.
		 */
		sort_policies_by_name(hook_policies);

		foreach(item, hook_policies)
		{
			RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);

			if (check_role_for_policy(policy->roles, user_id))
				*restrictive_policies = lappend(*restrictive_policies, policy);
		}
	}

	if (row_security_policy_hook_permissive)
	{
		List	   *hook_policies =
			(*row_security_policy_hook_permissive) (cmd, relation);

		foreach(item, hook_policies)
		{
			RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);

			if (check_role_for_policy(policy->roles, user_id))
				*permissive_policies = lappend(*permissive_policies, policy);
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】sort_policies_by_name —— 按名称对策略链表排序
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对传入的策略链表按策略名称排序，使后续生成的 WithCheckOption 以确定的、
 *   可预期的顺序被检查。该函数仅用于限制型（restrictive）策略。
 *
 * 参数：
 *   policies - 待排序的 RowSecurityPolicy 链表；会被原地重排（in-place）。
 *
 * 返回值：
 *   无。链表按名称升序排列。
 *
 * 设计思想：
 *   1. 直接调用通用链表排序 list_sort()，比较器使用 row_security_policy_cmp。
 *      list_sort 为就地重排，不产生新内存、不复制策略对象。
 *   2. 为什么只对 restrictive 策略排序：permissive 策略最终被 OR 合并为单个
 *      表达式，检查顺序无关紧要；而每个 restrictive 策略生成独立的
 *      WithCheckOption，其检查顺序会决定哪条策略先被报告，排序保证了跨会话、
 *      跨执行的一致性与可调试性。
 *   3. 排序规则（名称字符串比较）由 row_security_policy_cmp 实现，已兼容扩展
 *      提供的无名策略。
 * ============================================================================
 */
static void
sort_policies_by_name(List *policies)
{
	list_sort(policies, row_security_policy_cmp);
}

/*
 * ============================================================================
 * 【中文注释】row_security_policy_cmp —— 按名称比较两条行级安全策略的排序比较器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   list_sort 使用的比较器函数：比较两个 ListCell 中存放的 RowSecurityPolicy 的
 *   名称字符串，供 sort_policies_by_name 按名称对策略排序使用。
 *
 * 参数：
 *   a - 第一个链表单元，其 lfirst 指向的 RowSecurityPolicy 参与比较。
 *   b - 第二个链表单元，同上。
 *
 * 返回值：
 *   int - 与 strcmp 语义一致：pa 名称小于 pb 时返回负值，等于返回 0，大于返回
 *   正值。特例：策略名称为 NULL（扩展可能提供无名策略）时，NULL 被视为"最大"，
 *   排在所有具名策略之后。
 *
 * 设计思想：
 *   1. 对 NULL 策略名做保护性处理：a 为 NULL 而 b 非 NULL 时返回 1（a 排后），
 *      反之返回 -1（a 排前），两者皆为 NULL 返回 0，避免对 NULL 调用 strcmp。
 *      这是扩展钩子可能返回无名策略时的健壮性考虑。
 *   2. 两策略名均非 NULL 时直接委托 strcmp 完成字典序比较，保证排序结果稳定，
 *      与系统目录中按名字排序的规则一致。
 *   3. 纯比较器、无副作用，作为 list_sort 的回调被调用。
 * ============================================================================
 */
static int
row_security_policy_cmp(const ListCell *a, const ListCell *b)
{
	const RowSecurityPolicy *pa = (const RowSecurityPolicy *) lfirst(a);
	const RowSecurityPolicy *pb = (const RowSecurityPolicy *) lfirst(b);

	/* Guard against NULL policy names from extensions */
	if (pa->policy_name == NULL)
		return pb->policy_name == NULL ? 0 : 1;
	if (pb->policy_name == NULL)
		return -1;

	return strcmp(pa->policy_name, pb->policy_name);
}

/*
 * ============================================================================
 * 【中文注释】add_security_quals —— 把策略 USING 子句合成为 RTE 的安全表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   将给定策略集中适用于"读现有行"的 USING 子句转换成表达式，追加到 RTE 的
 *   securityQuals 链表中，从而在查询执行时过滤掉用户无权访问的行。组合规则：
 *   所有限制型（restrictive）策略用 AND 逐条并入，所有宽松型（permissive）策略
 *   用 OR 合并成单个表达式；若连一条宽松策略都没有，则加入恒为假的表达式，
 *   实现"默认拒绝"（default-deny）——此时表中任何行都不可见。
 *
 * 参数：
 *   rt_index            - 目标 RTE 在查询范围表中的位置，用于把策略表达式里的
 *                         varlevelsup=0、varno=1 的占位变量重写为该 RTE 的下标。
 *   permissive_policies - 宽松型策略链表，其 USING 子句用 OR 合并。
 *   restrictive_policies- 限制型策略链表，每个 USING 子句用 AND 独立并入。
 *   securityQuals       - 输出参数，指向 RTE 安全表达式链表的指针，生成的表达式
 *                         被追加到此。
 *   hasSubLinks         - 输出参数，若追加的任意表达式含子链接则置为 true。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 关键技巧——ChangeVarNodes(qual, 1, rt_index, 0)：策略表达式存储时使用
 *      约定俗成的占位号 varno=1，通过该调用把变量号重写为真实的 RTE 下标，使
 *      同一策略可被多个 RTE 复用；list_append_unique 保证同一表达式不会重复入链。
 *   2. 宽松策略必须存在，这是 RLS 的安全模型基石：restrictive 只能"加条件收紧"，
 *      绝不能单独授权，因此先用 OR 合并所有 permissive USING 子句（仅一条时直接
 *      复用该表达式，多条时构造 OR_EXPR），再叠加 AND 的 restrictive 子句。
 *   3. 若无 permissive 策略，安全上必须拒绝一切行，故追加一个 BOOLOID 的
 *      const false（makeConst）。这正是"启用 RLS 但未定义任何策略"时用户一张
 *      空表都读不到的机制所在。
 *   4. 表达式都经 copyObject 深拷贝，避免修改查询树中其他引用处的共享节点；
 *      hasSubLinks 的累加供上层判断是否需要子链接相关处理。
 * ============================================================================
 */
static void
add_security_quals(int rt_index,
				   List *permissive_policies,
				   List *restrictive_policies,
				   List **securityQuals,
				   bool *hasSubLinks)
{
	ListCell   *item;
	List	   *permissive_quals = NIL;
	Expr	   *rowsec_expr;

	/*
	 * First collect up the permissive quals.  If we do not find any
	 * permissive policies then no rows are visible (this is handled below).
	 */
	foreach(item, permissive_policies)
	{
		RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);

		if (policy->qual != NULL)
		{
			permissive_quals = lappend(permissive_quals,
									   copyObject(policy->qual));
			*hasSubLinks |= policy->hassublinks;
		}
	}

	/*
	 * We must have permissive quals, always, or no rows are visible.
	 *
	 * If we do not, then we simply return a single 'false' qual which results
	 * in no rows being visible.
	 */
	if (permissive_quals != NIL)
	{
		/*
		 * We now know that permissive policies exist, so we can now add
		 * security quals based on the USING clauses from the restrictive
		 * policies.  Since these need to be combined together using AND, we
		 * can just add them one at a time.
		 */
		foreach(item, restrictive_policies)
		{
			RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);
			Expr	   *qual;

			if (policy->qual != NULL)
			{
				qual = copyObject(policy->qual);
				ChangeVarNodes((Node *) qual, 1, rt_index, 0);

				*securityQuals = list_append_unique(*securityQuals, qual);
				*hasSubLinks |= policy->hassublinks;
			}
		}

		/*
		 * Then add a single security qual combining together the USING
		 * clauses from all the permissive policies using OR.
		 */
		if (list_length(permissive_quals) == 1)
			rowsec_expr = (Expr *) linitial(permissive_quals);
		else
			rowsec_expr = makeBoolExpr(OR_EXPR, permissive_quals, -1);

		ChangeVarNodes((Node *) rowsec_expr, 1, rt_index, 0);
		*securityQuals = list_append_unique(*securityQuals, rowsec_expr);
	}
	else

		/*
		 * A permissive policy must exist for rows to be visible at all.
		 * Therefore, if there were no permissive policies found, return a
		 * single always-false clause.
		 */
		*securityQuals = lappend(*securityQuals,
								 makeConst(BOOLOID, -1, InvalidOid,
										   sizeof(bool), BoolGetDatum(false),
										   false, true));
}

/*
 * ============================================================================
 * 【中文注释】add_with_check_options —— 生成校验新增/更新行的 WithCheckOption
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   针对 INSERT/UPDATE（以及 MERGE、INSERT..ON CONFLICT 等衍生场景）生成
 *   WithCheckOption 节点，用于在执行期校验将要写入表的新行是否符合行级安全策略。
 *   宽松型策略的校验子句（优先用显式 WITH CHECK 子句，否则退化为 USING 子句）
 *   被 OR 合并成一个 WCO；限制型策略则各自生成一个独立 WCO（以便报错时显示
 *   策略名）。若没有任何可用的宽松校验子句，则生成恒假的 WCO，默认拒绝所有新行。
 *
 * 参数：
 *   rel                 - 目标关系，用于在 WCO 中记录关系名（relname）。
 *   rt_index            - 目标 RTE 下标，配合 ChangeVarNodes 重写变量号。
 *   kind                - WCO 种类（WCO_RLS_INSERT_CHECK / WCO_RLS_UPDATE_CHECK /
 *                         WCO_RLS_CONFLICT_CHECK / WCO_RLS_MERGE_UPDATE_CHECK 等），
 *                         决定该检查属于哪个语义阶段。
 *   permissive_policies - 宽松型策略链表，其校验子句用 OR 合并为一个 WCO。
 *   restrictive_policies- 限制型策略链表，每条生成一个独立 WCO。
 *   withCheckOptions    - 输出参数，指向 Query 的 WithCheckOptions 链表，新 WCO
 *                         被追加到此。
 *   hasSubLinks         - 输出参数，含子链接的校验表达式置为 true。
 *   force_using         - 为 true 时强制一律使用 USING 子句（忽略显式 WITH CHECK），
 *                         用于"对既有行的检查"场景（如 ON CONFLICT 冲突行检查、
 *                         MERGE 的 USING 前置检查）。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 宏 QUAL_FOR_WCO(policy) 封装"取哪个子句"的决策：正常情况下优先用策略的
 *      with_check_qual，未显式定义时回退到 qual（USING 子句）——这与 SQL 中
 *      "WITH CHECK 缺省即为 USING"的语义一致；force_using 强制选择 USING。
 *   2. 宽松 WCO 的 polname 置为 NULL 是有意的：该检查失败意味着"没有任何策略
 *      授权这次写操作"，报错不应指向某一条具体策略；而 restrictive WCO 单独带
 *      polname，违反时能精确报告是哪条限制型策略被触犯。
 *   3. 与 add_security_quals 相比，写路径用"校验并报错"（WCO）而非"过滤行"
 *      （quals）：新行违反策略必须抛错，否则会造成用户以为写入成功却被静默丢弃
 *      的严重安全问题。这也是 ON CONFLICT、MERGE 把本用于"读"的 USING 子句
 *      也塞进 WCO 的原因。
 *   4. 每个 WCO 都用 pstrdup 持有关系名与策略名的副本，生命周期随 Query 树；
 *      list_append_unique 去重，ChangeVarNodes 完成变量号重写。
 * ============================================================================
 */
static void
add_with_check_options(Relation rel,
					   int rt_index,
					   WCOKind kind,
					   List *permissive_policies,
					   List *restrictive_policies,
					   List **withCheckOptions,
					   bool *hasSubLinks,
					   bool force_using)
{
	ListCell   *item;
	List	   *permissive_quals = NIL;

#define QUAL_FOR_WCO(policy) \
	( !force_using && \
	  (policy)->with_check_qual != NULL ? \
	  (policy)->with_check_qual : (policy)->qual )

	/*
	 * First collect up the permissive policy clauses, similar to
	 * add_security_quals.
	 */
	foreach(item, permissive_policies)
	{
		RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);
		Expr	   *qual = QUAL_FOR_WCO(policy);

		if (qual != NULL)
		{
			permissive_quals = lappend(permissive_quals, copyObject(qual));
			*hasSubLinks |= policy->hassublinks;
		}
	}

	/*
	 * There must be at least one permissive qual found or no rows are allowed
	 * to be added.  This is the same as in add_security_quals.
	 *
	 * If there are no permissive_quals then we fall through and return a
	 * single 'false' WCO, preventing all new rows.
	 */
	if (permissive_quals != NIL)
	{
		/*
		 * Add a single WithCheckOption for all the permissive policy clauses,
		 * combining them together using OR.  This check has no policy name,
		 * since if the check fails it means that no policy granted permission
		 * to perform the update, rather than any particular policy being
		 * violated.
		 */
		WithCheckOption *wco;

		wco = makeNode(WithCheckOption);
		wco->kind = kind;
		wco->relname = pstrdup(RelationGetRelationName(rel));
		wco->polname = NULL;
		wco->cascaded = false;

		if (list_length(permissive_quals) == 1)
			wco->qual = (Node *) linitial(permissive_quals);
		else
			wco->qual = (Node *) makeBoolExpr(OR_EXPR, permissive_quals, -1);

		ChangeVarNodes(wco->qual, 1, rt_index, 0);

		*withCheckOptions = list_append_unique(*withCheckOptions, wco);

		/*
		 * Now add WithCheckOptions for each of the restrictive policy clauses
		 * (which will be combined together using AND).  We use a separate
		 * WithCheckOption for each restrictive policy to allow the policy
		 * name to be included in error reports if the policy is violated.
		 */
		foreach(item, restrictive_policies)
		{
			RowSecurityPolicy *policy = (RowSecurityPolicy *) lfirst(item);
			Expr	   *qual = QUAL_FOR_WCO(policy);

			if (qual != NULL)
			{
				qual = copyObject(qual);
				ChangeVarNodes((Node *) qual, 1, rt_index, 0);

				wco = makeNode(WithCheckOption);
				wco->kind = kind;
				wco->relname = pstrdup(RelationGetRelationName(rel));
				wco->polname = pstrdup(policy->policy_name);
				wco->qual = (Node *) qual;
				wco->cascaded = false;

				*withCheckOptions = list_append_unique(*withCheckOptions, wco);
				*hasSubLinks |= policy->hassublinks;
			}
		}
	}
	else
	{
		/*
		 * If there were no policy clauses to check new data, add a single
		 * always-false WCO (a default-deny policy).
		 */
		WithCheckOption *wco;

		wco = makeNode(WithCheckOption);
		wco->kind = kind;
		wco->relname = pstrdup(RelationGetRelationName(rel));
		wco->polname = NULL;
		wco->qual = (Node *) makeConst(BOOLOID, -1, InvalidOid,
									   sizeof(bool), BoolGetDatum(false),
									   false, true);
		wco->cascaded = false;

		*withCheckOptions = lappend(*withCheckOptions, wco);
	}
}

/*
 * ============================================================================
 * 【中文注释】check_role_for_policy —— 判断策略是否适用于指定角色
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判断一条行级安全策略的适用角色数组（policy_roles）中，是否包含了可以令
 *   user_id 生效的角色：只要策略授权给 PUBLIC（ACL_ID_PUBLIC），或 user_id 拥有
 *   policy_roles 中任一角色的权限（含间接成员关系），则该策略对该用户适用。
 *
 * 参数：
 *   policy_roles - 策略的 roles 字段，一个 OID 数组（ArrayType），列出该策略适用
 *                  的角色或 PUBLIC。
 *   user_id      - 待判断的角色 OID（通常是当前用户或 RTE 的 checkAsUser）。
 *
 * 返回值：
 *   bool - true 表示该策略应作用于 user_id；false 表示不适用。
 *
 * 设计思想：
 *   1. 快速路径：数组首个元素是 ACL_ID_PUBLIC（即策略 TO PUBLIC）时立即返回
 *      true——PUBLIC 表示所有人，无需遍历。直接读 ARR_DATA_PTR 并假定第一个
 *      元素即 PUBLIC，是调用方约定（roles 数组以 PUBLIC 打头）下的高效写法。
 *   2. 逐元素调用 has_privs_of_role(user_id, roles[i])：它不仅检查直接角色成员，
 *      还检查通过其他角色间接继承的权限，确保策略对"角色层级"（如组角色）同样
 *      生效，与 ACL 权限检查的口径一致。
 *   3. 任一角色匹配即返回 true（策略适用列表是 OR 语义）；全部不匹配返回 false，
 *      表示该策略不参与该用户的 RLS 判定。
 * ============================================================================
 */
static bool
check_role_for_policy(ArrayType *policy_roles, Oid user_id)
{
	int			i;
	Oid		   *roles = (Oid *) ARR_DATA_PTR(policy_roles);

	/* Quick fall-thru for policies applied to all roles */
	if (roles[0] == ACL_ID_PUBLIC)
		return true;

	for (i = 0; i < ARR_DIMS(policy_roles)[0]; i++)
	{
		if (has_privs_of_role(user_id, roles[i]))
			return true;
	}

	return false;
}
