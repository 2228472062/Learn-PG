/*-------------------------------------------------------------------------
 *
 * rewriteRemove.c
 *	  routines for removing rewrite rules
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/rewrite/rewriteRemove.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/genam.h"
#include "access/htup_details.h"
#include "access/table.h"
#include "catalog/catalog.h"
#include "catalog/indexing.h"
#include "catalog/pg_rewrite.h"
#include "miscadmin.h"
#include "rewrite/rewriteRemove.h"
#include "utils/fmgroids.h"
#include "utils/inval.h"
#include "utils/rel.h"

/*
 * ============================================================================
 * 【中文注释】RemoveRewriteRuleById —— 按规则 OID 删除规则的核心逻辑
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   根据给定的规则 OID，从系统目录 pg_rewrite 中删除对应的规则元组，并做必要的
 *   并发控制与缓存失效处理。这是 DROP RULE 语句最终落地的地方。
 *
 * 参数：
 *   ruleOid - 待删除规则的 OID（pg_rewrite 的 oid）。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 打开 pg_rewrite（RowExclusiveLock），按 OID 索引找到该规则元组；找不到则
 *      报错，说明该规则已被并发删除。
 *   2. 获取规则所属关系（ev_class）上的 AccessExclusiveLock。这是关键的安全考虑：
 *      必须保证在删除规则期间没有任何查询可能还依赖于该规则。注释里特别指出，
 *      若不是 ON SELECT 规则，其实较弱一点的锁（如 RowExclusiveLock）也足够，但
 *      为简单统一、并避免 ON SELECT 规则被引用的风险，这里一律使用最强的表锁。
 *   3. 若目标是系统目录且未开启 allowSystemTableMods，拒绝删除，防止破坏系统表。
 *   4. 调用 CatalogTupleDelete 删除 pg_rewrite 元组。
 *   5. 发送共享缓存失效消息（CacheInvalidateRelcache），强制所有后端（包括本进程）
 *      重建/刷新该表的 relcache 条目，以反映新的规则集合——因为 relcache 中缓存
 *      了解析后的规则树，不失效的话其他连接会继续使用已被删除的规则。
 *   6. 关闭关系但保留 AccessExclusiveLock 直到事务提交，保证删除的原子性。
 * ============================================================================
 */
void
RemoveRewriteRuleById(Oid ruleOid)
{
	Relation	RewriteRelation;
	ScanKeyData skey[1];
	SysScanDesc rcscan;
	Relation	event_relation;
	HeapTuple	tuple;
	Oid			eventRelationOid;

	/*
	 * Open the pg_rewrite relation.
	 */
	RewriteRelation = table_open(RewriteRelationId, RowExclusiveLock);

	/*
	 * Find the tuple for the target rule.
	 */
	ScanKeyInit(&skey[0],
				Anum_pg_rewrite_oid,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(ruleOid));

	rcscan = systable_beginscan(RewriteRelation, RewriteOidIndexId, true,
								NULL, 1, skey);

	tuple = systable_getnext(rcscan);

	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "could not find tuple for rule %u", ruleOid);

	/*
	 * We had better grab AccessExclusiveLock to ensure that no queries are
	 * going on that might depend on this rule.  (Note: a weaker lock would
	 * suffice if it's not an ON SELECT rule.)
	 */
	eventRelationOid = ((Form_pg_rewrite) GETSTRUCT(tuple))->ev_class;
	event_relation = table_open(eventRelationOid, AccessExclusiveLock);

	if (!allowSystemTableMods && IsSystemRelation(event_relation))
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied: \"%s\" is a system catalog",
						RelationGetRelationName(event_relation))));

	/*
	 * Now delete the pg_rewrite tuple for the rule
	 */
	CatalogTupleDelete(RewriteRelation, &tuple->t_self);

	systable_endscan(rcscan);

	table_close(RewriteRelation, RowExclusiveLock);

	/*
	 * Issue shared-inval notice to force all backends (including me!) to
	 * update relcache entries with the new rule set.
	 */
	CacheInvalidateRelcache(event_relation);

	/* Close rel, but keep lock till commit... */
	table_close(event_relation, NoLock);
}
