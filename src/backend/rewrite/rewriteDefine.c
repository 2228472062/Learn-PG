/*-------------------------------------------------------------------------
 *
 * rewriteDefine.c
 *	  routines for defining a rewrite rule
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/rewrite/rewriteDefine.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "access/relation.h"
#include "access/table.h"
#include "catalog/catalog.h"
#include "catalog/dependency.h"
#include "catalog/indexing.h"
#include "catalog/namespace.h"
#include "catalog/objectaccess.h"
#include "catalog/pg_rewrite.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "parser/parse_utilcmd.h"
#include "rewrite/rewriteDefine.h"
#include "rewrite/rewriteManip.h"
#include "rewrite/rewriteSupport.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/inval.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/syscache.h"


static void checkRuleResultList(List *targetList, TupleDesc resultDesc,
								bool isSelect, bool requireColumnNameMatch);
static bool setRuleCheckAsUser_walker(Node *node, Oid *context);
static void setRuleCheckAsUser_Query(Query *qry, Oid userid);


/*
 * ============================================================================
 * 【中文注释】InsertRule —— 将规则参数以行的形式插入系统目录 pg_rewrite
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   接收一条规则的全部要素（规则名、事件类型、所属关系、是否 INSTEAD、事件
 *   条件、动作列表），把规则序列化后写入 pg_rewrite 系统表，并建立相应的依赖
 *   关系。这是 CREATE RULE / CREATE VIEW 真正落盘规则的底层函数。
 *
 * 参数：
 *   rulname     - 规则名（如 "_RETURN"）。
 *   evtype      - 事件类型 CmdType（CMD_SELECT / CMD_INSERT / ...）。
 *   eventrel_oid- 规则所属关系的 OID（ev_class）。
 *   evinstead   - 是否为 INSTEAD 规则（true 表示替换原动作执行）。
 *   event_qual  - 事件条件表达式（规则触发条件，NULL 表示无条件）。
 *   action      - 动作查询列表（List<Query>）。
 *   replace     - 是否允许替换同名已有规则。
 *
 * 返回值：
 *   Oid - 新建（或更新后）规则的 OID。
 *
 * 设计思想：
 *   1. 先把难以直接存储的树形结构序列化为字符串：event_qual 与 action 都用
 *      nodeToString() 转成文本后放进 text 类型的 ev_qual / ev_action 列，读取时
 *      再 stringToNode() 反序列化。
 *   2. 通过 syscache RULERELNAME((关系OID,规则名)) 查找是否已存在同名规则：
 *      - 若存在：若不允许替换（replace=false）则报重复对象错误；否则用
 *        heap_modify_tuple 仅更新 ev_type/is_instead/ev_qual/ev_action 四列
 *        （保留 oid、ev_class、rulename），并标记 is_update 以重建依赖。
 *      - 若不存在：用 GetNewOidWithIndex 分配新 OID 后 heap_form_tuple 插入。
 *   3. 依赖管理（pg_depend）：
 *      - 规则依赖其所属关系：ON SELECT 规则用 DEPENDENCY_INTERNAL（内部依赖，
 *        防止删除视图时被级联误删 SELECT 规则），其他规则用 DEPENDENCY_AUTO
 *        （关系被删时规则自动删除）。
 *      - 规则还依赖动作与条件中引用的所有对象（表、函数等），用
 *        recordDependencyOnExpr 登记 DEPENDENCY_NORMAL，保证被引用对象删除时
 *        规则随之失效。
 *   4. 事件条件引用的 OLD/NEW 范围表变量需要在正确的 rtable 上下文中登记依赖，
 *      因此用 getInsertSelectQuery 找到含 OLD/NEW 条目的那个查询再登记。
 *   5. 触发对象后置创建钩子（InvokeObjectPostCreateHook），供扩展监视规则创建。
 * ============================================================================
 */
static Oid
InsertRule(const char *rulname,
		   int evtype,
		   Oid eventrel_oid,
		   bool evinstead,
		   Node *event_qual,
		   List *action,
		   bool replace)
{
	char	   *evqual = nodeToString(event_qual);
	char	   *actiontree = nodeToString((Node *) action);
	Datum		values[Natts_pg_rewrite];
	bool		nulls[Natts_pg_rewrite] = {0};
	NameData	rname;
	Relation	pg_rewrite_desc;
	HeapTuple	tup,
				oldtup;
	Oid			rewriteObjectId;
	ObjectAddress myself,
				referenced;
	bool		is_update = false;

	/*
	 * Set up *nulls and *values arrays
	 */
	namestrcpy(&rname, rulname);
	values[Anum_pg_rewrite_rulename - 1] = NameGetDatum(&rname);
	values[Anum_pg_rewrite_ev_class - 1] = ObjectIdGetDatum(eventrel_oid);
	values[Anum_pg_rewrite_ev_type - 1] = CharGetDatum(evtype + '0');
	values[Anum_pg_rewrite_ev_enabled - 1] = CharGetDatum(RULE_FIRES_ON_ORIGIN);
	values[Anum_pg_rewrite_is_instead - 1] = BoolGetDatum(evinstead);
	values[Anum_pg_rewrite_ev_qual - 1] = CStringGetTextDatum(evqual);
	values[Anum_pg_rewrite_ev_action - 1] = CStringGetTextDatum(actiontree);

	/*
	 * Ready to store new pg_rewrite tuple
	 */
	pg_rewrite_desc = table_open(RewriteRelationId, RowExclusiveLock);

	/*
	 * Check to see if we are replacing an existing tuple
	 */
	oldtup = SearchSysCache2(RULERELNAME,
							 ObjectIdGetDatum(eventrel_oid),
							 PointerGetDatum(rulname));

	if (HeapTupleIsValid(oldtup))
	{
		bool		replaces[Natts_pg_rewrite] = {0};

		if (!replace)
			ereport(ERROR,
					(errcode(ERRCODE_DUPLICATE_OBJECT),
					 errmsg("rule \"%s\" for relation \"%s\" already exists",
							rulname, get_rel_name(eventrel_oid))));

		/*
		 * When replacing, we don't need to replace every attribute
		 */
		replaces[Anum_pg_rewrite_ev_type - 1] = true;
		replaces[Anum_pg_rewrite_is_instead - 1] = true;
		replaces[Anum_pg_rewrite_ev_qual - 1] = true;
		replaces[Anum_pg_rewrite_ev_action - 1] = true;

		tup = heap_modify_tuple(oldtup, RelationGetDescr(pg_rewrite_desc),
								values, nulls, replaces);

		CatalogTupleUpdate(pg_rewrite_desc, &tup->t_self, tup);

		ReleaseSysCache(oldtup);

		rewriteObjectId = ((Form_pg_rewrite) GETSTRUCT(tup))->oid;
		is_update = true;
	}
	else
	{
		rewriteObjectId = GetNewOidWithIndex(pg_rewrite_desc,
											 RewriteOidIndexId,
											 Anum_pg_rewrite_oid);
		values[Anum_pg_rewrite_oid - 1] = ObjectIdGetDatum(rewriteObjectId);

		tup = heap_form_tuple(pg_rewrite_desc->rd_att, values, nulls);

		CatalogTupleInsert(pg_rewrite_desc, tup);
	}


	heap_freetuple(tup);

	/* If replacing, get rid of old dependencies and make new ones */
	if (is_update)
		deleteDependencyRecordsFor(RewriteRelationId, rewriteObjectId, false);

	/*
	 * Install dependency on rule's relation to ensure it will go away on
	 * relation deletion.  If the rule is ON SELECT, make the dependency
	 * implicit --- this prevents deleting a view's SELECT rule.  Other kinds
	 * of rules can be AUTO.
	 */
	myself.classId = RewriteRelationId;
	myself.objectId = rewriteObjectId;
	myself.objectSubId = 0;

	referenced.classId = RelationRelationId;
	referenced.objectId = eventrel_oid;
	referenced.objectSubId = 0;

	recordDependencyOn(&myself, &referenced,
					   (evtype == CMD_SELECT) ? DEPENDENCY_INTERNAL : DEPENDENCY_AUTO);

	/*
	 * Also install dependencies on objects referenced in action and qual.
	 */
	recordDependencyOnExpr(&myself, (Node *) action, NIL,
						   DEPENDENCY_NORMAL);

	if (event_qual != NULL)
	{
		/* Find query containing OLD/NEW rtable entries */
		Query	   *qry = linitial_node(Query, action);

		qry = getInsertSelectQuery(qry, NULL);
		recordDependencyOnExpr(&myself, event_qual, qry->rtable,
							   DEPENDENCY_NORMAL);
	}

	/* Post creation hook for new rule */
	InvokeObjectPostCreateHook(RewriteRelationId, rewriteObjectId, 0);

	table_close(pg_rewrite_desc, RowExclusiveLock);

	return rewriteObjectId;
}

/*
 * ============================================================================
 * 【中文注释】DefineRule —— 执行 CREATE RULE 命令
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   处理用户发出的 CREATE RULE 语句：先对规则的动作与条件做解析分析，再定位
 *   目标关系并加锁，最后把规则安装到系统目录。是规则创建命令的用户入口。
 *
 * 参数：
 *   stmt       - 解析后的 CREATE RULE 语法树（RuleStmt），包含规则名、目标关系、
 *                事件类型、是否 INSTEAD、是否 REPLACE、动作与条件。
 *   queryString- 原始 SQL 文本，用于解析过程中的错误定位与上下文。
 *
 * 返回值：
 *   ObjectAddress - 新建规则的（类ID, 对象ID, 子ID）地址，供 DDL 框架返回信息。
 *
 * 设计思想：
 *   1. 委托 transformRuleStmt() 完成解析分析：把动作里的查询、事件条件从原始
 *      语法变换成已解析的 Query/表达式树（期间会做 OLD/NEW 引用、列解析等）。
 *   2. 用 RangeVarGetRelid 解析关系名并加 AccessExclusiveLock（与
 *      DefineQueryRewrite 保持同一锁级别，二者可能互相调用，锁级别必须一致，
 *      否则会造成死锁或锁不匹配）。
 *   3. 其余工作全部交给 DefineQueryRewrite 完成——这里只是一个薄封装。
 * ============================================================================
 */
ObjectAddress
DefineRule(RuleStmt *stmt, const char *queryString)
{
	List	   *actions;
	Node	   *whereClause;
	Oid			relId;

	/* Parse analysis. */
	transformRuleStmt(stmt, queryString, &actions, &whereClause);

	/*
	 * Find and lock the relation.  Lock level should match
	 * DefineQueryRewrite.
	 */
	relId = RangeVarGetRelid(stmt->relation, AccessExclusiveLock, false);

	/* ... and execute */
	return DefineQueryRewrite(stmt->rulename,
							  relId,
							  whereClause,
							  stmt->event,
							  stmt->instead,
							  stmt->replace,
							  actions);
}


/*
 * ============================================================================
 * 【中文注释】DefineQueryRewrite —— 创建规则（动作/条件已完成解析分析）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把一条已通过解析分析的规则安装到系统目录。与 DefineRule 的区别在于：这里
 *   的动作(action)与条件(event_qual)已经是解析后的 Query 树/表达式，可直接使用。
 *   它也是 CREATE VIEW（通过 internal 调用安装 _RETURN 规则）的核心落地点。
 *
 * 参数：
 *   rulename   - 规则名。
 *   event_relid- 规则所属关系 OID。
 *   event_qual - 已解析的事件条件表达式（可 NULL）。
 *   event_type - 规则事件类型 CmdType。
 *   is_instead - 是否 INSTEAD 规则。
 *   replace    - 是否允许替换已有同名规则。
 *   action     - 已解析的动作查询列表（List<Query>）。
 *
 * 返回值：
 *   ObjectAddress - 规则的地址；注意当 action 为空且非 INSTEAD 时规则被视作
 *                   no-op 而不会真正插入，此时 objectId 为 InvalidOid。
 *
 * 设计思想：
 *   1. 打开事件关系并加 AccessExclusiveLock。锁级别与 DefineRule 保持一致；
 *      加最强表锁是为了保证：安装 ON SELECT 规则期间没有 SELECT 正在并发执行；
 *      对其他规则也至少能挡住并发 INSERT/UPDATE/DELETE 与并发 CREATE RULE。
 *      （理想情况下其他规则用 ShareRowExclusiveLock 就够，但由于目录访问的
 *        竞态问题暂统一用最强锁。）
 *   2. 一连串合法性校验：
 *      - 关系类型必须能挂规则（普通表/物化视图/视图/分区表），冲突日志表与系统
 *        目录禁止挂规则（除非 allowSystemTableMods）。
 *      - 调用者必须拥有该关系。
 *      - 规则动作不得改写 OLD 或 NEW 伪行（prs2_old_varno/prs2_new_varno），
 *        因为 Postgres 不实现该功能；注意用 getInsertSelectQuery 穿透
 *        INSERT/SELECT 包装，防止被其"伪装"成普通动作而漏检。
 *      - ON SELECT 规则有额外严格限制：关系必须是视图/物化视图、动作必须是且
 *        仅是一个 INSTEAD SELECT、不能带数据修改型 WITH、不能有条件、targetlist
 *        必须与事件关系精确匹配、关系上不能再有别的 ON SELECT 规则、规则名
 *        必须叫 _RETURN。
 *      - 非 SELECT 规则：RETURNING 列表至多出现在一个动作中、条件规则与
 *        非 INSTEAD 规则禁止带 RETURNING、RETURNING 必须与事件关系匹配、规则
 *        名不能是 _RETURN（防止误替换视图规则）。
 *   3. 校验通过后调用 InsertRule 落盘，并调用 SetRelationRuleStatus 把 pg_class
 *      的 relhasrules 置为 true——顺带广播 SI 失效消息强制所有后端刷新 relcache。
 *   4. 注意"空动作且非 INSTEAD"的规则是无意义规则，直接跳过安装。
 * ============================================================================
 */
ObjectAddress
DefineQueryRewrite(const char *rulename,
				   Oid event_relid,
				   Node *event_qual,
				   CmdType event_type,
				   bool is_instead,
				   bool replace,
				   List *action)
{
	Relation	event_relation;
	ListCell   *l;
	Query	   *query;
	Oid			ruleId = InvalidOid;
	ObjectAddress address;

	/*
	 * If we are installing an ON SELECT rule, we had better grab
	 * AccessExclusiveLock to ensure no SELECTs are currently running on the
	 * event relation. For other types of rules, it would be sufficient to
	 * grab ShareRowExclusiveLock to lock out insert/update/delete actions and
	 * to ensure that we lock out current CREATE RULE statements; but because
	 * of race conditions in access to catalog entries, we can't do that yet.
	 *
	 * Note that this lock level should match the one used in DefineRule.
	 */
	event_relation = table_open(event_relid, AccessExclusiveLock);

	/*
	 * Verify relation is of a type that rules can sensibly be applied to.
	 * Internal callers can target materialized views, but transformRuleStmt()
	 * blocks them for users.  Don't mention them in the error message.
	 */
	if (event_relation->rd_rel->relkind != RELKIND_RELATION &&
		event_relation->rd_rel->relkind != RELKIND_MATVIEW &&
		event_relation->rd_rel->relkind != RELKIND_VIEW &&
		event_relation->rd_rel->relkind != RELKIND_PARTITIONED_TABLE)
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("relation \"%s\" cannot have rules",
						RelationGetRelationName(event_relation)),
				 errdetail_relkind_not_supported(event_relation->rd_rel->relkind)));

	/*
	 * Conflict log tables are used internally for logical replication
	 * conflict logging and should not have rules, as it could disrupt
	 * conflict logging.
	 */
	if (IsConflictLogTableClass(event_relation->rd_rel))
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("conflict log table \"%s\" cannot have rules",
						RelationGetRelationName(event_relation)),
				 errdetail("Conflict log tables are system-managed tables for logical replication conflicts.")));

	if (!allowSystemTableMods && IsSystemRelation(event_relation))
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied: \"%s\" is a system catalog",
						RelationGetRelationName(event_relation))));

	/*
	 * Check user has permission to apply rules to this relation.
	 */
	if (!object_ownercheck(RelationRelationId, event_relid, GetUserId()))
		aclcheck_error(ACLCHECK_NOT_OWNER, get_relkind_objtype(event_relation->rd_rel->relkind),
					   RelationGetRelationName(event_relation));

	/*
	 * No rule actions that modify OLD or NEW
	 */
	foreach(l, action)
	{
		query = lfirst_node(Query, l);
		if (query->resultRelation == 0)
			continue;
		/* Don't be fooled by INSERT/SELECT */
		if (query != getInsertSelectQuery(query, NULL))
			continue;
		if (query->resultRelation == PRS2_OLD_VARNO)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("rule actions on OLD are not implemented"),
					 errhint("Use views or triggers instead.")));
		if (query->resultRelation == PRS2_NEW_VARNO)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("rule actions on NEW are not implemented"),
					 errhint("Use triggers instead.")));
	}

	if (event_type == CMD_SELECT)
	{
		/*
		 * Rules ON SELECT are restricted to view definitions
		 *
		 * So this had better be a view, ...
		 */
		if (event_relation->rd_rel->relkind != RELKIND_VIEW &&
			event_relation->rd_rel->relkind != RELKIND_MATVIEW)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("relation \"%s\" cannot have ON SELECT rules",
							RelationGetRelationName(event_relation)),
					 errdetail_relkind_not_supported(event_relation->rd_rel->relkind)));

		/*
		 * ... there cannot be INSTEAD NOTHING, ...
		 */
		if (action == NIL)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("INSTEAD NOTHING rules on SELECT are not implemented"),
					 errhint("Use views instead.")));

		/*
		 * ... there cannot be multiple actions, ...
		 */
		if (list_length(action) > 1)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("multiple actions for rules on SELECT are not implemented")));

		/*
		 * ... the one action must be a SELECT, ...
		 */
		query = linitial_node(Query, action);
		if (!is_instead ||
			query->commandType != CMD_SELECT)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("rules on SELECT must have action INSTEAD SELECT")));

		/*
		 * ... it cannot contain data-modifying WITH ...
		 */
		if (query->hasModifyingCTE)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("rules on SELECT must not contain data-modifying statements in WITH")));

		/*
		 * ... there can be no rule qual, ...
		 */
		if (event_qual != NULL)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("event qualifications are not implemented for rules on SELECT")));

		/*
		 * ... the targetlist of the SELECT action must exactly match the
		 * event relation, ...
		 */
		checkRuleResultList(query->targetList,
							RelationGetDescr(event_relation),
							true,
							event_relation->rd_rel->relkind !=
							RELKIND_MATVIEW);

		/*
		 * ... there must not be another ON SELECT rule already ...
		 */
		if (!replace && event_relation->rd_rules != NULL)
		{
			int			i;

			for (i = 0; i < event_relation->rd_rules->numLocks; i++)
			{
				RewriteRule *rule;

				rule = event_relation->rd_rules->rules[i];
				if (rule->event == CMD_SELECT)
					ereport(ERROR,
							(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
							 errmsg("\"%s\" is already a view",
									RelationGetRelationName(event_relation))));
			}
		}

		/*
		 * ... and finally the rule must be named _RETURN.
		 */
		if (strcmp(rulename, ViewSelectRuleName) != 0)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
					 errmsg("view rule for \"%s\" must be named \"%s\"",
							RelationGetRelationName(event_relation),
							ViewSelectRuleName)));
	}
	else
	{
		/*
		 * For non-SELECT rules, a RETURNING list can appear in at most one of
		 * the actions ... and there can't be any RETURNING list at all in a
		 * conditional or non-INSTEAD rule.  (Actually, there can be at most
		 * one RETURNING list across all rules on the same event, but it seems
		 * best to enforce that at rule expansion time.)  If there is a
		 * RETURNING list, it must match the event relation.
		 */
		bool		haveReturning = false;

		foreach(l, action)
		{
			query = lfirst_node(Query, l);

			if (!query->returningList)
				continue;
			if (haveReturning)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("cannot have multiple RETURNING lists in a rule")));
			haveReturning = true;
			if (event_qual != NULL)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("RETURNING lists are not supported in conditional rules")));
			if (!is_instead)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("RETURNING lists are not supported in non-INSTEAD rules")));
			checkRuleResultList(query->returningList,
								RelationGetDescr(event_relation),
								false, false);
		}

		/*
		 * And finally, if it's not an ON SELECT rule then it must *not* be
		 * named _RETURN.  This prevents accidentally or maliciously replacing
		 * a view's ON SELECT rule with some other kind of rule.
		 */
		if (strcmp(rulename, ViewSelectRuleName) == 0)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
					 errmsg("non-view rule for \"%s\" must not be named \"%s\"",
							RelationGetRelationName(event_relation),
							ViewSelectRuleName)));
	}

	/*
	 * This rule is allowed - prepare to install it.
	 */

	/* discard rule if it's null action and not INSTEAD; it's a no-op */
	if (action != NIL || is_instead)
	{
		ruleId = InsertRule(rulename,
							event_type,
							event_relid,
							is_instead,
							event_qual,
							action,
							replace);

		/*
		 * Set pg_class 'relhasrules' field true for event relation.
		 *
		 * Important side effect: an SI notice is broadcast to force all
		 * backends (including me!) to update relcache entries with the new
		 * rule.
		 */
		SetRelationRuleStatus(event_relid, true);
	}

	ObjectAddressSet(address, RewriteRelationId, ruleId);

	/* Close rel, but keep lock till commit... */
	table_close(event_relation, NoLock);

	return address;
}

/*
 * ============================================================================
 * 【中文注释】checkRuleResultList —— 校验规则动作输出与关系元组描述兼容
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查传入的 targetList（可能是 SELECT 规则的目标列表，也可能是 RETURNING
 *   列表）能否与事件关系的元组描述（TupleDesc）逐列对上号——数量、列名（可选）、
 *   类型、typmod 都必须匹配。不匹配时抛出带详细定位信息的错误。
 *
 * 参数：
 *   targetList            - 待校验的目标列表（List<TargetEntry>）。
 *   resultDesc            - 事件关系的元组描述（列数、每列的名字/类型等）。
 *   isSelect              - true 表示这是 SELECT 规则的目标列表，false 表示是
 *                           RETURNING 列表；用于选择错误提示文案。
 *   requireColumnNameMatch- 是否要求列名也一致（仅 SELECT 且针对普通视图时要求，
 *                           物化视图与 RETURNING 不要求）。
 *
 * 返回值：
 *   无；不匹配时直接报错。
 *
 * 设计思想：
 *   逐列做四个层次的校验，保证规则动作的返回结构精确等于关系结构：
 *   1. 数量：忽略 resjunk 条目后，目标列表项数必须等于关系列数，多了/少了都报错。
 *   2. 丢弃列：关系中 attisdropped 的列不允许出现在目标位置——把含丢弃列的表转成
 *      视图会破坏规则系统假定"目标列表列即表列"的不变量（resjunk 标记无法规避
 *      该不变量），因此直接拒绝。RETURNING 遇到丢弃列同样报错。
 *   3. 列名（仅当 requireColumnNameMatch）：目标条目的 resname 必须与关系列名
 *      完全一致。
 *   4. 类型与 typmod：exprType 必须与 atttypid 相等；typmod 允许一方为 -1（未指
 *      定）——例如 numeric 列在表上有默认精度，而规则表达式的 typmod 常为 -1，
 *      这种差异应被容忍。
 *   这样严格校验确保视图展开 / 规则动作替换后无需再做类型转换，可直接对上目标列。
 * ============================================================================
 */
static void
checkRuleResultList(List *targetList, TupleDesc resultDesc, bool isSelect,
					bool requireColumnNameMatch)
{
	ListCell   *tllist;
	int			i;

	/* Only a SELECT may require a column name match. */
	Assert(isSelect || !requireColumnNameMatch);

	i = 0;
	foreach(tllist, targetList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(tllist);
		Oid			tletypid;
		int32		tletypmod;
		Form_pg_attribute attr;
		char	   *attname;

		/* resjunk entries may be ignored */
		if (tle->resjunk)
			continue;
		i++;
		if (i > resultDesc->natts)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
					 isSelect ?
					 errmsg("SELECT rule's target list has too many entries") :
					 errmsg("RETURNING list has too many entries")));

		attr = TupleDescAttr(resultDesc, i - 1);
		attname = NameStr(attr->attname);

		/*
		 * Disallow dropped columns in the relation.  This is not really
		 * expected to happen when creating an ON SELECT rule.  It'd be
		 * possible if someone tried to convert a relation with dropped
		 * columns to a view, but the only case we care about supporting
		 * table-to-view conversion for is pg_dump, and pg_dump won't do that.
		 *
		 * Unfortunately, the situation is also possible when adding a rule
		 * with RETURNING to a regular table, and rejecting that case is
		 * altogether more annoying.  In principle we could support it by
		 * modifying the targetlist to include dummy NULL columns
		 * corresponding to the dropped columns in the tupdesc.  However,
		 * places like ruleutils.c would have to be fixed to not process such
		 * entries, and that would take an uncertain and possibly rather large
		 * amount of work.  (Note we could not dodge that by marking the dummy
		 * columns resjunk, since it's precisely the non-resjunk tlist columns
		 * that are expected to correspond to table columns.)
		 */
		if (attr->attisdropped)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 isSelect ?
					 errmsg("cannot convert relation containing dropped columns to view") :
					 errmsg("cannot create a RETURNING list for a relation containing dropped columns")));

		/* Check name match if required; no need for two error texts here */
		if (requireColumnNameMatch && strcmp(tle->resname, attname) != 0)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
					 errmsg("SELECT rule's target entry %d has different column name from column \"%s\"",
							i, attname),
					 errdetail("SELECT target entry is named \"%s\".",
							   tle->resname)));

		/* Check type match. */
		tletypid = exprType((Node *) tle->expr);
		if (attr->atttypid != tletypid)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
					 isSelect ?
					 errmsg("SELECT rule's target entry %d has different type from column \"%s\"",
							i, attname) :
					 errmsg("RETURNING list's entry %d has different type from column \"%s\"",
							i, attname),
					 isSelect ?
					 errdetail("SELECT target entry has type %s, but column has type %s.",
							   format_type_be(tletypid),
							   format_type_be(attr->atttypid)) :
					 errdetail("RETURNING list entry has type %s, but column has type %s.",
							   format_type_be(tletypid),
							   format_type_be(attr->atttypid))));

		/*
		 * Allow typmods to be different only if one of them is -1, ie,
		 * "unspecified".  This is necessary for cases like "numeric", where
		 * the table will have a filled-in default length but the select
		 * rule's expression will probably have typmod = -1.
		 */
		tletypmod = exprTypmod((Node *) tle->expr);
		if (attr->atttypmod != tletypmod &&
			attr->atttypmod != -1 && tletypmod != -1)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
					 isSelect ?
					 errmsg("SELECT rule's target entry %d has different size from column \"%s\"",
							i, attname) :
					 errmsg("RETURNING list's entry %d has different size from column \"%s\"",
							i, attname),
					 isSelect ?
					 errdetail("SELECT target entry has type %s, but column has type %s.",
							   format_type_with_typemod(tletypid, tletypmod),
							   format_type_with_typemod(attr->atttypid,
														attr->atttypmod)) :
					 errdetail("RETURNING list entry has type %s, but column has type %s.",
							   format_type_with_typemod(tletypid, tletypmod),
							   format_type_with_typemod(attr->atttypid,
														attr->atttypmod))));
	}

	if (i != resultDesc->natts)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
				 isSelect ?
				 errmsg("SELECT rule's target list has too few entries") :
				 errmsg("RETURNING list has too few entries")));
}

/*
 * ============================================================================
 * 【中文注释】setRuleCheckAsUser —— 把查询树中所有 RTEPermissionInfo 的权限检查
 *                                  用户统一设为指定用户
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   递归遍历一棵查询/表达式树，把其中出现的所有 RTEPermissionInfo 的
 *   checkAsUser 字段改写为给定的 userid。用于"以规则/视图定义者的身份检查权限"
 *   的语义实现。
 *
 * 参数：
 *   node   - 待遍历的查询树或表达式（通常是规则动作树）。
 *   userid - 希望作为权限检查主体的用户 OID。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 为何需要它？当规则/视图定义者通过 CREATE RULE / CREATE VIEW 设置了
 *      security_invoker 以外的权限语义时，规则动作涉及的表在规则展开后要按
 *      定义者（而非执行者）的权限去检查。实现手段就是把动作树里的每个
 *      RTEPermissionInfo->checkAsUser 记为定义者 OID，权限检查阶段据此切换身份。
 *   2. 具体实现是对外提供一个简单的入口（本函数），实际遍历交给
 *      setRuleCheckAsUser_walker：它遇到 Query 节点就深入处理该查询的
 *      perminfos/子查询/CTE，其余节点用 expression_tree_walker 继续递归。
 *   3. 注意这里统一改写所有 perminfo，包括可能来自系统表查询的部分；在规则的
 *      动作树上下文中这是正确的，因为整个动作树都应视为定义者执行的逻辑。
 * ============================================================================
 */
void
setRuleCheckAsUser(Node *node, Oid userid)
{
	(void) setRuleCheckAsUser_walker(node, &userid);
}

/*
 * ============================================================================
 * 【中文注释】setRuleCheckAsUser_walker —— 遍历器：分派 Query 与普通表达式节点
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   表达式遍历回调。遇到 Query 节点就调用 setRuleCheckAsUser_Query 处理其内部
 *   的所有权限信息并返回 false（不继续对其整体做通用遍历，因为子结构已处理）；
 *   其他节点交给 expression_tree_walker 继续递归。
 *
 * 参数：
 *   node    - 当前遍历到的节点。
 *   context - 指向 Oid（目标用户）的上下文指针。
 *
 * 返回值：
 *   bool - true 表示终止遍历（本函数从不主动终止），false 表示继续。
 *
 * 设计思想：
 *   标准的 expression_tree_walker 遍历器模式：把"需要特殊处理的节点类型"（Query）
 *   拦下来单独处理，其余类型交给通用遍历器兜底。Query 之所以特殊，是因为它的
 *   子结构（rtable 中的子查询、cteList、子链接里的查询）分布在多个字段里，通用
 *   遍历器无法完整覆盖，必须用专门的 setRuleCheckAsUser_Query 处理。
 * ============================================================================
 */
static bool
setRuleCheckAsUser_walker(Node *node, Oid *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Query))
	{
		setRuleCheckAsUser_Query((Query *) node, *context);
		return false;
	}
	return expression_tree_walker(node, setRuleCheckAsUser_walker,
								  context);
}

/*
 * ============================================================================
 * 【中文注释】setRuleCheckAsUser_Query —— 改写单个查询内部全部权限检查用户
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   处理一个 Query：先把本查询自带的 RTEPermissionInfo 的 checkAsUser 全部设为
 *   userid，再递归进入其子查询 RTE、WITH CTE，以及各子链接（subplan/sublink）
 *   里的查询，确保整棵查询树里的权限信息都被覆盖。
 *
 * 参数：
 *   qry    - 待处理的查询。
 *   userid - 权限检查主体用户 OID。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   按 Query 结构的"三处嵌套"分别递归，保证不遗漏：
 *   1. 直接字段 rteperminfos：本查询的目标/来源表的权限信息，直接逐个改写。
 *   2. rtable 里的 RTE_SUBQUERY：FROM (SELECT ...) 这样的内联子查询。
 *   3. cteList：WITH ... AS 定义的公共表表达式（其查询体也需改写）。
 *   4. 若本查询带子链接（hasSubLinks），用 query_tree_walker 找到子链接中嵌套
 *      的 Query 再递归——这里传 QTW_IGNORE_RC_SUBQUERIES 标志，避免对 rtable
 *      中已被第 2 步处理过的子查询 RTE 重复遍历。
 *   注意所有递归都复用同一个 userid，实现"整棵树统一以定义者身份检查权限"。
 * ============================================================================
 */
static void
setRuleCheckAsUser_Query(Query *qry, Oid userid)
{
	ListCell   *l;

	/* Set in all RTEPermissionInfos for this query. */
	foreach(l, qry->rteperminfos)
	{
		RTEPermissionInfo *perminfo = lfirst_node(RTEPermissionInfo, l);

		perminfo->checkAsUser = userid;
	}

	/* Now recurse to any subquery RTEs */
	foreach(l, qry->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(l);

		if (rte->rtekind == RTE_SUBQUERY)
			setRuleCheckAsUser_Query(rte->subquery, userid);
	}

	/* Recurse into subquery-in-WITH */
	foreach(l, qry->cteList)
	{
		CommonTableExpr *cte = (CommonTableExpr *) lfirst(l);

		setRuleCheckAsUser_Query(castNode(Query, cte->ctequery), userid);
	}

	/* If there are sublinks, search for them and process their RTEs */
	if (qry->hasSubLinks)
		query_tree_walker(qry, setRuleCheckAsUser_walker, &userid,
						  QTW_IGNORE_RC_SUBQUERIES);
}


/*
 * ============================================================================
 * 【中文注释】EnableDisableRule —— 修改既有规则的触发时机（ev_enabled）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把某关系上一条已存在规则的 ev_enabled 字段改为指定值，实现 ALTER TABLE ...
 *   ENABLE/DISABLE [ALWAYS|REPLICA] RULE 命令的语义（控制规则在何种复制模式下
 *   触发）。
 *
 * 参数：
 *   rel       - 规则所属的关系（已由调用方打开）。
 *   rulename  - 规则名。
 *   fires_when- 新的触发时机，取值 RULE_FIRES_ON_ORIGIN / RULE_FIRES_ON_REPLICA /
 *               RULE_FIRES_ON_ALWAYS / RULE_DISABLED 之一。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 打开 pg_rewrite，通过 syscache 找到对应规则元组的拷贝；找不到报错。
 *   2. 权限检查：调用者必须是规则所属关系的所有者。
 *   3. 仅当 ev_enabled 与目标值不同时才执行 CatalogTupleUpdate 写回；相同则跳过
 *      写目录（避免无谓的目录更新）。
 *   4. 只要发生了改动，就用 CacheInvalidateRelcache 广播 SI 失效消息，让所有
 *      后端（含自己）重建 relcache 条目——规则触发状态缓存在 relcache 里，不
 *      失效的话改动无法及时生效。
 *   5. 触发对象后置修改钩子 InvokeObjectPostAlterHook，供扩展感知变更。
 * ============================================================================
 */
void
EnableDisableRule(Relation rel, const char *rulename,
				  char fires_when)
{
	Relation	pg_rewrite_desc;
	Oid			owningRel = RelationGetRelid(rel);
	Oid			eventRelationOid;
	HeapTuple	ruletup;
	Form_pg_rewrite ruleform;
	bool		changed = false;

	/*
	 * Find the rule tuple to change.
	 */
	pg_rewrite_desc = table_open(RewriteRelationId, RowExclusiveLock);
	ruletup = SearchSysCacheCopy2(RULERELNAME,
								  ObjectIdGetDatum(owningRel),
								  PointerGetDatum(rulename));
	if (!HeapTupleIsValid(ruletup))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_OBJECT),
				 errmsg("rule \"%s\" for relation \"%s\" does not exist",
						rulename, get_rel_name(owningRel))));

	ruleform = (Form_pg_rewrite) GETSTRUCT(ruletup);

	/*
	 * Verify that the user has appropriate permissions.
	 */
	eventRelationOid = ruleform->ev_class;
	Assert(eventRelationOid == owningRel);
	if (!object_ownercheck(RelationRelationId, eventRelationOid, GetUserId()))
		aclcheck_error(ACLCHECK_NOT_OWNER, get_relkind_objtype(get_rel_relkind(eventRelationOid)),
					   get_rel_name(eventRelationOid));

	/*
	 * Change ev_enabled if it is different from the desired new state.
	 */
	if (ruleform->ev_enabled != fires_when)
	{
		ruleform->ev_enabled = fires_when;
		CatalogTupleUpdate(pg_rewrite_desc, &ruletup->t_self, ruletup);

		changed = true;
	}

	InvokeObjectPostAlterHook(RewriteRelationId, ruleform->oid, 0);

	heap_freetuple(ruletup);
	table_close(pg_rewrite_desc, RowExclusiveLock);

	/*
	 * If we changed anything, broadcast a SI inval message to force each
	 * backend (including our own!) to rebuild relation's relcache entry.
	 * Otherwise they will fail to apply the change promptly.
	 */
	if (changed)
		CacheInvalidateRelcache(rel);
}


/*
 * ============================================================================
 * 【中文注释】RangeVarCallbackForRenameRule —— 重命名规则前的关系权限/完整性检查
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   作为 RangeVarGetRelidExtended 的回调，在解析重命名 ALTER RULE 的目标关系时、
 *   真正加锁之前执行各种预检查：关系类型是否允许挂规则、是否系统目录/冲突日志
 *   表、调用者是否拥有该关系。这样能在加锁前尽早以清晰的错误拒绝非法操作。
 *
 * 参数：
 *   rv      - 用户写的关系名（RangeVar）。
 *   relid   - 已解析出的关系 OID（可能已被并发删除为 InvalidOid）。
 *   oldrelid- 之前解析出的 OID（本函数未使用）。
 *   arg     - 透传参数（本函数未使用）。
 *
 * 返回值：
 *   无；检查失败直接报错，concurrently dropped 时静默返回。
 *
 * 设计思想：
 *   PostgreSQL DDL 的标准"lockname 回调"模式：对关系的检查分两阶段，先把能
 *   做的权限/类型检查放在"加锁之前"的回调里，可以减少对锁的持有时间，也能在
 *   加锁前就反馈常见错误。此处检查：
 *   1. 关系必须可挂规则（普通表/视图/分区表）。
 *   2. 不能是冲突日志表、不能是系统目录（除非 allowSystemTableMods）。
 *   3. 必须是关系所有者。
 *   关系在解析与回调之间被并发删除时（relid 无效），syscache 查不到元组则直接
 *   return，把错误处理交给后续正式加锁/使用阶段。
 * ============================================================================
 */
static void
RangeVarCallbackForRenameRule(const RangeVar *rv, Oid relid, Oid oldrelid,
							  void *arg)
{
	HeapTuple	tuple;
	Form_pg_class form;

	tuple = SearchSysCache1(RELOID, ObjectIdGetDatum(relid));
	if (!HeapTupleIsValid(tuple))
		return;					/* concurrently dropped */
	form = (Form_pg_class) GETSTRUCT(tuple);

	/* only tables and views can have rules */
	if (form->relkind != RELKIND_RELATION &&
		form->relkind != RELKIND_VIEW &&
		form->relkind != RELKIND_PARTITIONED_TABLE)
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("relation \"%s\" cannot have rules", rv->relname),
				 errdetail_relkind_not_supported(form->relkind)));

	/*
	 * Conflict log tables are used internally for logical replication
	 * conflict logging and should not have rules, as it could disrupt
	 * conflict logging.
	 */
	if (IsConflictLogTableClass(form))
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("conflict log table \"%s\" cannot have rules",
						rv->relname),
				 errdetail("Conflict log tables are system-managed tables for logical replication conflicts.")));

	if (!allowSystemTableMods && IsSystemClass(relid, form))
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied: \"%s\" is a system catalog",
						rv->relname)));

	/* you must own the table to rename one of its rules */
	if (!object_ownercheck(RelationRelationId, relid, GetUserId()))
		aclcheck_error(ACLCHECK_NOT_OWNER, get_relkind_objtype(get_rel_relkind(relid)), rv->relname);

	ReleaseSysCache(tuple);
}

/*
 * ============================================================================
 * 【中文注释】RenameRewriteRule —— 重命名一条已存在的重写规则
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   实现 ALTER TABLE ... RENAME RULE 命令：把指定关系上名为 oldName 的规则改名
 *   为 newName，并做必要的权限、命名约束检查与缓存失效广播。
 *
 * 参数：
 *   relation - 目标关系的 RangeVar。
 *   oldName  - 规则旧名。
 *   newName  - 规则新名。
 *
 * 返回值：
 *   ObjectAddress - 被重命名规则的地址。
 *
 * 设计思想：
 *   1. 用 RangeVarGetRelidExtended 解析关系并加 AccessExclusiveLock（锁一直持有
 *      到事务结束，保证重命名期间无人并发使用该关系及其规则）。加锁前的预检查
 *      交给 RangeVarCallbackForRenameRule 回调完成。
 *   2. 校验规则必须存在；新名不得与同关系已有规则重名（IsDefinedRewriteRule）。
 *   3. 两条命名约束（与 DefineQueryRewrite 里的规则相呼应）：
 *      - ON SELECT 规则禁止重命名——视图的 _RETURN 规则名是约定俗成的，改名会
 *        破坏视图机制。
 *      - 反过来，非视图规则的新名不得叫 _RETURN，防止通过改名把视图规则替换成
 *        普通规则。
 *   4. 通过 syscache 拷贝元组、修改 rulename 后 CatalogTupleUpdate 写回，
 *      触发对象后置修改钩子。
 *   5. 广播 CacheInvalidateRelcache 强制所有后端刷新 relcache（规则名缓存在
 *      relcache 的规则集中）。
 * ============================================================================
 */
ObjectAddress
RenameRewriteRule(RangeVar *relation, const char *oldName,
				  const char *newName)
{
	Oid			relid;
	Relation	targetrel;
	Relation	pg_rewrite_desc;
	HeapTuple	ruletup;
	Form_pg_rewrite ruleform;
	Oid			ruleOid;
	ObjectAddress address;

	/*
	 * Look up name, check permissions, and acquire lock (which we will NOT
	 * release until end of transaction).
	 */
	relid = RangeVarGetRelidExtended(relation, AccessExclusiveLock,
									 0,
									 RangeVarCallbackForRenameRule,
									 NULL);

	/* Have lock already, so just need to build relcache entry. */
	targetrel = relation_open(relid, NoLock);

	/* Prepare to modify pg_rewrite */
	pg_rewrite_desc = table_open(RewriteRelationId, RowExclusiveLock);

	/* Fetch the rule's entry (it had better exist) */
	ruletup = SearchSysCacheCopy2(RULERELNAME,
								  ObjectIdGetDatum(relid),
								  PointerGetDatum(oldName));
	if (!HeapTupleIsValid(ruletup))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_OBJECT),
				 errmsg("rule \"%s\" for relation \"%s\" does not exist",
						oldName, RelationGetRelationName(targetrel))));
	ruleform = (Form_pg_rewrite) GETSTRUCT(ruletup);
	ruleOid = ruleform->oid;

	/* rule with the new name should not already exist */
	if (IsDefinedRewriteRule(relid, newName))
		ereport(ERROR,
				(errcode(ERRCODE_DUPLICATE_OBJECT),
				 errmsg("rule \"%s\" for relation \"%s\" already exists",
						newName, RelationGetRelationName(targetrel))));

	/*
	 * We disallow renaming ON SELECT rules, because they should always be
	 * named "_RETURN".
	 */
	if (ruleform->ev_type == CMD_SELECT + '0')
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
				 errmsg("renaming an ON SELECT rule is not allowed")));

	/*
	 * Conversely, if it's not an ON SELECT rule then it must *not* be named
	 * _RETURN.
	 */
	if (strcmp(newName, ViewSelectRuleName) == 0)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
				 errmsg("non-view rule for \"%s\" must not be named \"%s\"",
						RelationGetRelationName(targetrel),
						ViewSelectRuleName)));

	/* OK, do the update */
	namestrcpy(&(ruleform->rulename), newName);

	CatalogTupleUpdate(pg_rewrite_desc, &ruletup->t_self, ruletup);

	InvokeObjectPostAlterHook(RewriteRelationId, ruleOid, 0);

	heap_freetuple(ruletup);
	table_close(pg_rewrite_desc, RowExclusiveLock);

	/*
	 * Invalidate relation's relcache entry so that other backends (and this
	 * one too!) are sent SI message to make them rebuild relcache entries.
	 * (Ideally this should happen automatically...)
	 */
	CacheInvalidateRelcache(targetrel);

	ObjectAddressSet(address, RewriteRelationId, ruleOid);

	/*
	 * Close rel, but keep exclusive lock!
	 */
	relation_close(targetrel, NoLock);

	return address;
}
