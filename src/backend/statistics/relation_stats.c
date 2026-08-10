/*-------------------------------------------------------------------------
 * relation_stats.c
 *
 *	  PostgreSQL relation statistics manipulation
 *
 * Code supporting the direct import of relation statistics, similar to
 * what is done by the ANALYZE command.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *       src/backend/statistics/relation_stats.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <math.h>

#include "access/heapam.h"
#include "catalog/indexing.h"
#include "catalog/namespace.h"
#include "nodes/makefuncs.h"
#include "statistics/statistics.h"
#include "statistics/stat_utils.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/fmgrprotos.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"


/*
 * Positional argument numbers, names, and types for
 * relation_statistics_update().
 */

enum relation_stats_argnum
{
	RELSCHEMA_ARG = 0,
	RELNAME_ARG,
	RELPAGES_ARG,
	RELTUPLES_ARG,
	RELALLVISIBLE_ARG,
	RELALLFROZEN_ARG,
	NUM_RELATION_STATS_ARGS
};

static struct StatsArgInfo relarginfo[] =
{
	[RELSCHEMA_ARG] = {"schemaname", TEXTOID},
	[RELNAME_ARG] = {"relname", TEXTOID},
	[RELPAGES_ARG] = {"relpages", INT4OID},
	[RELTUPLES_ARG] = {"reltuples", FLOAT4OID},
	[RELALLVISIBLE_ARG] = {"relallvisible", INT4OID},
	[RELALLFROZEN_ARG] = {"relallfrozen", INT4OID},
	[NUM_RELATION_STATS_ARGS] = {0}
};

static bool relation_statistics_update(FunctionCallInfo fcinfo);
static bool relation_statistics_update_internal(Oid reloid,
												FunctionCallInfo fcinfo);

/*
 * ============================================================================
 * 【中文注释】relation_statistics_update —— 更新/导入关系统计信息（入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   "导入或更新关系级统计"的入口。关系级统计指存放在 pg_class 中的四个字段：
 *   relpages（页数）、reltuples（估算行数）、relallvisible（全可见页数）、
 *   relallfrozen（全冻结页数）。本函数解析出 (schemaname, relname) 后加锁，
 *   转交 relation_statistics_update_internal() 实际写库。
 *
 * 参数：
 *   fcinfo - 位置参数，布局见枚举 relation_stats_argnum：
 *       RELSCHEMA_ARG(0)=模式名(text)、RELNAME_ARG(1)=表名(text)、
 *       RELPAGES_ARG(2)=页数(int4)、RELTUPLES_ARG(3)=行数(float4)、
 *       RELALLVISIBLE_ARG(4)=全可见页数(int4)、RELALLFROZEN_ARG(5)=全冻结页数(int4)。
 *       为 NULL 的参数表示该项不修改。
 *
 * 返回值：
 *   bool - true 成功；false 有参数校验失败（只发 WARNING，不中断）。
 *
 * 设计思想：
 *   与 attribute_statistics_update() 相同的前置模式：恢复期间禁止、先通过
 *   RangeVarGetRelidExtended() 加 ShareUpdateExclusiveLock 并在回调
 *   RangeVarCallbackForStats() 中做权限检查。
 * ============================================================================
 */
static bool
relation_statistics_update(FunctionCallInfo fcinfo)
{
	char	   *nspname;
	char	   *relname;
	Oid			reloid;
	Oid			locked_table = InvalidOid;

	stats_check_required_arg(fcinfo, relarginfo, RELSCHEMA_ARG);
	stats_check_required_arg(fcinfo, relarginfo, RELNAME_ARG);

	nspname = TextDatumGetCString(PG_GETARG_DATUM(RELSCHEMA_ARG));
	relname = TextDatumGetCString(PG_GETARG_DATUM(RELNAME_ARG));

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("Statistics cannot be modified during recovery.")));

	reloid = RangeVarGetRelidExtended(makeRangeVar(nspname, relname, -1),
									  ShareUpdateExclusiveLock, 0,
									  RangeVarCallbackForStats, &locked_table);

	return relation_statistics_update_internal(reloid, fcinfo);
}

/*
 * ============================================================================
 * 【中文注释】relation_statistics_update_internal —— 关系统计更新的工作函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 relpages / reltuples / relallvisible / relallfrozen 四个值中"被提供的"
 *   那些写入 pg_class 对应行。未提供的字段保持原值。
 *
 * 参数：
 *   reloid - 已锁定的关系 OID。
 *   fcinfo - 位置参数（见 relation_statistics_update()）。
 *
 * 返回值：
 *   bool - true 成功；false 因 reltuples 不合法（NaN/Inf/<-1）被拒。
 *
 * 设计思想：
 *   1.【数值合理性校验】：reltuples 必须为有限值且 >= -1.0（-1 表示"未知"，
 *      与 ANALYZE 约定一致）；非法则发 WARNING 并置 result=false。
 *   2.【增量更新】：只有"参数已提供"且"与 pg_class 现值不同"的字段才进入
 *      replaces 数组。用 heap_modify_tuple_by_cols() 一次性更新多列（比逐列更新
 *      高效），再 CatalogTupleUpdate() 写回。
 *   3.【锁级别与 VACUUM 保持一致】：对 pg_class 取 RowExclusiveLock，这与
 *      vac_update_relstats() 的做法一致，保证与并发 VACUUM/ANALYZE 的写冲突能
 *      被正确串行化。
 *   4. 末尾 CommandCounterIncrement()，保证本事务内后续可见。
 * ============================================================================
 */
static bool
relation_statistics_update_internal(Oid reloid, FunctionCallInfo fcinfo)
{
	BlockNumber relpages = 0;
	bool		update_relpages = false;
	float		reltuples = 0;
	bool		update_reltuples = false;
	BlockNumber relallvisible = 0;
	bool		update_relallvisible = false;
	BlockNumber relallfrozen = 0;
	bool		update_relallfrozen = false;
	Relation	crel;
	HeapTuple	ctup;
	Form_pg_class pgcform;
	int			replaces[4] = {0};
	Datum		values[4] = {0};
	bool		nulls[4] = {0};
	int			nreplaces = 0;
	bool		result = true;

	if (!PG_ARGISNULL(RELPAGES_ARG))
	{
		relpages = PG_GETARG_UINT32(RELPAGES_ARG);
		update_relpages = true;
	}

	if (!PG_ARGISNULL(RELTUPLES_ARG))
	{
		reltuples = PG_GETARG_FLOAT4(RELTUPLES_ARG);
		if (isnan(reltuples) || isinf(reltuples))
		{
			ereport(WARNING,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("argument \"%s\" must be a finite value", "reltuples")));
			result = false;
		}
		else if (reltuples < -1.0)
		{
			ereport(WARNING,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("argument \"%s\" must not be less than -1.0", "reltuples")));
			result = false;
		}
		else
			update_reltuples = true;
	}

	if (!PG_ARGISNULL(RELALLVISIBLE_ARG))
	{
		relallvisible = PG_GETARG_UINT32(RELALLVISIBLE_ARG);
		update_relallvisible = true;
	}

	if (!PG_ARGISNULL(RELALLFROZEN_ARG))
	{
		relallfrozen = PG_GETARG_UINT32(RELALLFROZEN_ARG);
		update_relallfrozen = true;
	}

	/*
	 * Take RowExclusiveLock on pg_class, consistent with
	 * vac_update_relstats().
	 */
	crel = table_open(RelationRelationId, RowExclusiveLock);

	ctup = SearchSysCache1(RELOID, ObjectIdGetDatum(reloid));
	if (!HeapTupleIsValid(ctup))
		elog(ERROR, "pg_class entry for relid %u not found", reloid);

	pgcform = (Form_pg_class) GETSTRUCT(ctup);

	if (update_relpages && relpages != pgcform->relpages)
	{
		replaces[nreplaces] = Anum_pg_class_relpages;
		values[nreplaces] = UInt32GetDatum(relpages);
		nreplaces++;
	}

	if (update_reltuples && reltuples != pgcform->reltuples)
	{
		replaces[nreplaces] = Anum_pg_class_reltuples;
		values[nreplaces] = Float4GetDatum(reltuples);
		nreplaces++;
	}

	if (update_relallvisible && relallvisible != pgcform->relallvisible)
	{
		replaces[nreplaces] = Anum_pg_class_relallvisible;
		values[nreplaces] = UInt32GetDatum(relallvisible);
		nreplaces++;
	}

	if (update_relallfrozen && relallfrozen != pgcform->relallfrozen)
	{
		replaces[nreplaces] = Anum_pg_class_relallfrozen;
		values[nreplaces] = UInt32GetDatum(relallfrozen);
		nreplaces++;
	}

	if (nreplaces > 0)
	{
		TupleDesc	tupdesc = RelationGetDescr(crel);
		HeapTuple	newtup;

		newtup = heap_modify_tuple_by_cols(ctup, tupdesc, nreplaces,
										   replaces, values, nulls);
		CatalogTupleUpdate(crel, &newtup->t_self, newtup);
		heap_freetuple(newtup);
	}

	ReleaseSysCache(ctup);

	/* release the lock, consistent with vac_update_relstats() */
	table_close(crel, RowExclusiveLock);

	CommandCounterIncrement();

	return result;
}

/*
 * ============================================================================
 * 【中文注释】pg_clear_relation_stats —— SQL 函数：重置关系统计信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把指定表的 pg_class 统计字段重置为"新建表"的初始状态：relpages=0、
 *   reltuples=-1（未知）、relallvisible=0、relallfrozen=0。
 *
 * 参数：
 *   fcinfo - 前两个位置参数为 (schemaname, relname)。
 *
 * 返回值：
 *   Datum（void）。
 *
 * 设计思想：
 *   构造一个 6 位置的 fcinfo：前两位原样复制传入的模式名/表名，后四位硬编码为
 *   初始值，然后复用 relation_statistics_update() 走统一路径（加锁+权限+写库），
 *   避免重复代码。
 * ============================================================================
 */
Datum
pg_clear_relation_stats(PG_FUNCTION_ARGS)
{
	LOCAL_FCINFO(newfcinfo, 6);

	InitFunctionCallInfoData(*newfcinfo, NULL, 6, InvalidOid, NULL, NULL);

	newfcinfo->args[0].value = PG_GETARG_DATUM(0);
	newfcinfo->args[0].isnull = PG_ARGISNULL(0);
	newfcinfo->args[1].value = PG_GETARG_DATUM(1);
	newfcinfo->args[1].isnull = PG_ARGISNULL(1);
	newfcinfo->args[2].value = UInt32GetDatum(0);
	newfcinfo->args[2].isnull = false;
	newfcinfo->args[3].value = Float4GetDatum(-1.0);
	newfcinfo->args[3].isnull = false;
	newfcinfo->args[4].value = UInt32GetDatum(0);
	newfcinfo->args[4].isnull = false;
	newfcinfo->args[5].value = UInt32GetDatum(0);
	newfcinfo->args[5].isnull = false;

	relation_statistics_update(newfcinfo);
	PG_RETURN_VOID();
}

/*
 * ============================================================================
 * 【中文注释】pg_restore_relation_stats —— SQL 函数：恢复（导入）关系统计信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   以"键-值对"变长参数的形式导入关系统计（对应 pg_class 的 relpages 等字段），
 *   例如 pg_restore_relation_stats('schemaname'=>'public', 'relname'=>'t',
 *   'relpages'=>100, 'reltuples'=>10000, ...)。
 *
 * 参数：
 *   fcinfo - 变长键值对参数。
 *
 * 返回值：
 *   bool - 由 stats_fill_fcinfo_from_arg_pairs() 与 relation_statistics_update()
 *          的结果合并。
 *
 * 设计思想：
 *   与 pg_restore_attribute_stats() 完全同构：先把变长键值对翻译成位置参数数组
 *   （relarginfo 定义名字→位置映射），再调用内部更新函数。
 * ============================================================================
 */
Datum
pg_restore_relation_stats(PG_FUNCTION_ARGS)
{
	LOCAL_FCINFO(positional_fcinfo, NUM_RELATION_STATS_ARGS);
	bool		result = true;

	InitFunctionCallInfoData(*positional_fcinfo, NULL,
							 NUM_RELATION_STATS_ARGS,
							 InvalidOid, NULL, NULL);

	if (!stats_fill_fcinfo_from_arg_pairs(fcinfo, positional_fcinfo,
										  relarginfo))
		result = false;

	if (!relation_statistics_update(positional_fcinfo))
		result = false;

	PG_RETURN_BOOL(result);
}

/*
 * ============================================================================
 * 【中文注释】import_relation_statistics —— 以 C 接口导入关系统计信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   面向 C 代码的导入接口：给定已打开的关系 rel 与四个统计项的 NullableDatum
 *   值，把它们写入 pg_class。逻辑上与 pg_restore_relation_stats() 相同，但参数
 *   以数组方式直接传递，无需解析键值对。
 *
 * 参数：
 *   rel         - 已打开的关系。
 *   version     - 版本号（当前忽略）。
 *   relpages / reltuples / relallvisible / relallfrozen - 对应统计值
 *       （NullableDatum，isnull=true 表示不修改该项）。
 *
 * 返回值：
 *   bool - 是否成功（转自内部更新函数）。
 *
 * 设计思想：
 *   构造一个 NUM_RELATION_STATS_ARGS 长度的位置 fcinfo，前两个位置（模式名/表名）
 *   由 rel 推导，后四个位置直接赋值 NullableDatum，然后复用
 *   relation_statistics_update_internal()。
 * ============================================================================
 */
bool
import_relation_statistics(Relation rel,
						   const NullableDatum *version,
						   const NullableDatum *relpages,
						   const NullableDatum *reltuples,
						   const NullableDatum *relallvisible,
						   const NullableDatum *relallfrozen)
{
	LOCAL_FCINFO(newfcinfo, NUM_RELATION_STATS_ARGS);

	Assert(relpages);
	Assert(reltuples);
	Assert(relallvisible);
	Assert(relallfrozen);

	InitFunctionCallInfoData(*newfcinfo, NULL, NUM_RELATION_STATS_ARGS,
							 InvalidOid, NULL, NULL);

	newfcinfo->args[RELSCHEMA_ARG].value =
		CStringGetTextDatum(get_namespace_name(RelationGetNamespace(rel)));
	newfcinfo->args[RELSCHEMA_ARG].isnull = false;
	newfcinfo->args[RELNAME_ARG].value =
		CStringGetTextDatum(RelationGetRelationName(rel));
	newfcinfo->args[RELNAME_ARG].isnull = false;

	newfcinfo->args[RELPAGES_ARG] = *relpages;
	newfcinfo->args[RELTUPLES_ARG] = *reltuples;
	newfcinfo->args[RELALLVISIBLE_ARG] = *relallvisible;
	newfcinfo->args[RELALLFROZEN_ARG] = *relallfrozen;

	return relation_statistics_update_internal(RelationGetRelid(rel),
											   newfcinfo);
}
