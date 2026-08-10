/*-------------------------------------------------------------------------
 *
 * rewriteSupport.c
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/rewrite/rewriteSupport.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "access/table.h"
#include "catalog/indexing.h"
#include "catalog/pg_class.h"
#include "catalog/pg_rewrite.h"
#include "rewrite/rewriteSupport.h"
#include "utils/inval.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"


/*
 * ============================================================================
 * 【中文注释】IsDefinedRewriteRule —— 判断指定关系上是否存在指定名称的重写规则
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   查询系统目录 pg_rewrite，判断"拥有者关系 + 规则名"这一对唯一键对应的规则
 *   是否已存在。通常用于重写规则创建前的重名检查，或用于判断某规则是否已定义。
 *
 * 参数：
 *   owningRel - 拥有规则的关系 OID（规则所属的表/视图）。
 *   ruleName  - 待检查的规则名称。
 *
 * 返回值：
 *   bool - 存在返回 true，不存在返回 false。
 *
 * 设计思想：
 *   直接借助 syscache 的 RULERELNAME 缓存（由(关系OID, 规则名)构成的唯一索引），
 *   调用 SearchSysCacheExists2 做存在性检查。使用 syscache 的好处是：绝大部分
 *   规则重名检查的查询可以命中内存缓存，避免每次都去扫描 pg_rewrite 系统表。
 * ============================================================================
 */
bool
IsDefinedRewriteRule(Oid owningRel, const char *ruleName)
{
	return SearchSysCacheExists2(RULERELNAME,
								 ObjectIdGetDatum(owningRel),
								 PointerGetDatum(ruleName));
}


/*
 * ============================================================================
 * 【中文注释】SetRelationRuleStatus —— 设置关系的 relhasrules 标志并广播缓存失效
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   更新 pg_class 中某关系元组的 relhasrules 字段（该字段表示此表是否挂有重写
 *   规则），并根据需要发送共享内存失效消息。通常在创建或删除规则时被调用，
 *   用来同步更新系统目录与各后端的 relcache。
 *
 * 参数：
 *   relationId - 目标关系 OID。
 *   relHasRules- 要设置的新值：true 表示该关系有规则，false 表示没有。
 *
 * 返回值：
 *   无。
 *
 * 设计思想：
 *   1. 通过 syscache（RELOID）获取 pg_class 元组的拷贝进行修改，若找不到则报错
 *      （说明关系不存在或缓存已失效）。
 *   2. 只有当字段当前值与新值不同时才真正执行 CatalogTupleUpdate 写回目录；
 *      若相同则无需改行。但**无论是否发生更新，都必须发送缓存失效消息**
 *      （CacheInvalidateRelcacheByTuple）。这是本函数最微妙的地方：即使值没变，
 *      其他后端也可能因各种原因持有过期的 relcache 视图（例如规则集合未变但
 *      relcache 数据被清掉），强制刷新能保证各后端看到一致且最新的规则集合。
 *   3. 该失效消息会发给所有后端——包括本进程自己——从而触发 relcache 以新的
 *      规则集合重建/更新对应条目。
 *
 * 注意事项：
 *   调用者必须先持有该关系上合适的锁（通常是 RowExclusiveLock 或更强），确保
 *   在修改期间不会有其他事务并发改写同一元组。
 * ============================================================================
 */
void
SetRelationRuleStatus(Oid relationId, bool relHasRules)
{
	Relation	relationRelation;
	HeapTuple	tuple;
	Form_pg_class classForm;

	/*
	 * Find the tuple to update in pg_class, using syscache for the lookup.
	 */
	relationRelation = table_open(RelationRelationId, RowExclusiveLock);
	tuple = SearchSysCacheCopy1(RELOID, ObjectIdGetDatum(relationId));
	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "cache lookup failed for relation %u", relationId);
	classForm = (Form_pg_class) GETSTRUCT(tuple);

	if (classForm->relhasrules != relHasRules)
	{
		/* Do the update */
		classForm->relhasrules = relHasRules;

		CatalogTupleUpdate(relationRelation, &tuple->t_self, tuple);
	}
	else
	{
		/* no need to change tuple, but force relcache rebuild anyway */
		CacheInvalidateRelcacheByTuple(tuple);
	}

	heap_freetuple(tuple);
	table_close(relationRelation, RowExclusiveLock);
}

/*
 * ============================================================================
 * 【中文注释】get_rewrite_oid —— 按（关系,规则名）查找规则 OID
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在系统目录 pg_rewrite 中，根据"所属关系 OID + 规则名"查找对应规则的 OID。
 *   是规则操作的通用查找工具：重命名规则、删除规则等都会用到。
 *
 * 参数：
 *   relid     - 规则所属的关系 OID。
 *   rulename  - 规则名称。
 *   missing_ok- 若为 false，规则不存在时抛出"rule ... does not exist"错误；
 *               若为 true，则静默返回 InvalidOid 表示未找到。
 *
 * 返回值：
 *   Oid - 找到的规则 OID；missing_ok 为 true 且不存在时返回 InvalidOid。
 *
 * 设计思想：
 *   1. 利用 syscache 的 RULERELNAME 键（(关系OID,规则名)唯一）查找 pg_rewrite 元组，
 *      并断言元组中的 ev_class 与传入的 relid 一致，防止缓存被污染。
 *   2. 未找到时按 missing_ok 决定是报错还是返回 InvalidOid，错误信息会带上规则名
 *      与所属表名（用 get_rel_name 转换），便于用户定位问题。
 *   3. 找到后读取元组中的 oid 字段返回，并立即释放 syscache 项（ReleaseSysCache），
 *      因为本函数不持有元组引用，调用方只需 OID 值即可。
 * ============================================================================
 */
Oid
get_rewrite_oid(Oid relid, const char *rulename, bool missing_ok)
{
	HeapTuple	tuple;
	Form_pg_rewrite ruleform;
	Oid			ruleoid;

	/* Find the rule's pg_rewrite tuple, get its OID */
	tuple = SearchSysCache2(RULERELNAME,
							ObjectIdGetDatum(relid),
							PointerGetDatum(rulename));
	if (!HeapTupleIsValid(tuple))
	{
		if (missing_ok)
			return InvalidOid;
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_OBJECT),
				 errmsg("rule \"%s\" for relation \"%s\" does not exist",
						rulename, get_rel_name(relid))));
	}
	ruleform = (Form_pg_rewrite) GETSTRUCT(tuple);
	Assert(relid == ruleform->ev_class);
	ruleoid = ruleform->oid;
	ReleaseSysCache(tuple);
	return ruleoid;
}
