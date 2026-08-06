/*-------------------------------------------------------------------------
 *
 * parse_enr.c
 *	  parser support routines dealing with ephemeral named relations
 *
 * 【中文总述】
 * 临时命名关系（Ephemeral Named Relation, ENR）的解析支持例程。
 * ENR 是 SQL 中用于 WITH 子句等场景的临时命名查询结果，
 * 本文件提供查询环境（QueryEnv）中 ENR 元数据的查找接口。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/parser/parse_enr.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "parser/parse_enr.h"

/*
 * name_matches_visible_ENR
 *		Check whether a reference name matches a visible ENR.
 *
 * 【中文总述】
 * 检查给定引用名（refname）是否在当前查询环境中
 * 对应一个可见的临时命名关系（ENR）。
 * 内部调用 get_visible_ENR_metadata()，若返回值非空则匹配。
 * 【调用链】SQL 解析 → name_matches_visible_ENR()
 *   → get_visible_ENR_metadata() → 返回 ENR 元数据或 NULL
 */
bool
name_matches_visible_ENR(ParseState *pstate, const char *refname)
{
	return (get_visible_ENR_metadata(pstate->p_queryEnv, refname) != NULL);
}

/*
 * get_visible_ENR
 *		Get the metadata of a visible ENR by reference name.
 *
 * 【中文总述】
 * 根据引用名获取临时命名关系（ENR）的元数据。
 * 直接委托给 get_visible_ENR_metadata()，是查询环境中
 * ENR 查找的统一入口。
 * 【调用链】SQL 解析 → get_visible_ENR()
 *   → get_visible_ENR_metadata() → 返回 ENR 元数据或 NULL
 */
EphemeralNamedRelationMetadata
get_visible_ENR(ParseState *pstate, const char *refname)
{
	return get_visible_ENR_metadata(pstate->p_queryEnv, refname);
}
