/*-------------------------------------------------------------------------
 * attribute_stats.c
 *
 *	  PostgreSQL relation attribute statistics manipulation.
 *
 * Code supporting the direct import of relation attribute statistics, similar
 * to what is done by the ANALYZE command.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *       src/backend/statistics/attribute_stats.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/heapam.h"
#include "catalog/indexing.h"
#include "catalog/namespace.h"
#include "catalog/pg_operator.h"
#include "nodes/makefuncs.h"
#include "statistics/statistics.h"
#include "statistics/stat_utils.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"

/*
 * Positional argument numbers, names, and types for
 * attribute_statistics_update() and pg_restore_attribute_stats().
 */

enum attribute_stats_argnum
{
	ATTRELSCHEMA_ARG = 0,
	ATTRELNAME_ARG,
	ATTNAME_ARG,
	ATTNUM_ARG,
	INHERITED_ARG,
	NULL_FRAC_ARG,
	AVG_WIDTH_ARG,
	N_DISTINCT_ARG,
	MOST_COMMON_VALS_ARG,
	MOST_COMMON_FREQS_ARG,
	HISTOGRAM_BOUNDS_ARG,
	CORRELATION_ARG,
	MOST_COMMON_ELEMS_ARG,
	MOST_COMMON_ELEM_FREQS_ARG,
	ELEM_COUNT_HISTOGRAM_ARG,
	RANGE_LENGTH_HISTOGRAM_ARG,
	RANGE_EMPTY_FRAC_ARG,
	RANGE_BOUNDS_HISTOGRAM_ARG,
	NUM_ATTRIBUTE_STATS_ARGS
};

static struct StatsArgInfo attarginfo[] =
{
	[ATTRELSCHEMA_ARG] = {"schemaname", TEXTOID},
	[ATTRELNAME_ARG] = {"relname", TEXTOID},
	[ATTNAME_ARG] = {"attname", TEXTOID},
	[ATTNUM_ARG] = {"attnum", INT2OID},
	[INHERITED_ARG] = {"inherited", BOOLOID},
	[NULL_FRAC_ARG] = {"null_frac", FLOAT4OID},
	[AVG_WIDTH_ARG] = {"avg_width", INT4OID},
	[N_DISTINCT_ARG] = {"n_distinct", FLOAT4OID},
	[MOST_COMMON_VALS_ARG] = {"most_common_vals", TEXTOID},
	[MOST_COMMON_FREQS_ARG] = {"most_common_freqs", FLOAT4ARRAYOID},
	[HISTOGRAM_BOUNDS_ARG] = {"histogram_bounds", TEXTOID},
	[CORRELATION_ARG] = {"correlation", FLOAT4OID},
	[MOST_COMMON_ELEMS_ARG] = {"most_common_elems", TEXTOID},
	[MOST_COMMON_ELEM_FREQS_ARG] = {"most_common_elem_freqs", FLOAT4ARRAYOID},
	[ELEM_COUNT_HISTOGRAM_ARG] = {"elem_count_histogram", FLOAT4ARRAYOID},
	[RANGE_LENGTH_HISTOGRAM_ARG] = {"range_length_histogram", TEXTOID},
	[RANGE_EMPTY_FRAC_ARG] = {"range_empty_frac", FLOAT4OID},
	[RANGE_BOUNDS_HISTOGRAM_ARG] = {"range_bounds_histogram", TEXTOID},
	[NUM_ATTRIBUTE_STATS_ARGS] = {0}
};

/*
 * Positional argument numbers, names, and types for
 * pg_clear_attribute_stats().
 */

enum clear_attribute_stats_argnum
{
	C_ATTRELSCHEMA_ARG = 0,
	C_ATTRELNAME_ARG,
	C_ATTNAME_ARG,
	C_INHERITED_ARG,
	C_NUM_ATTRIBUTE_STATS_ARGS
};

static struct StatsArgInfo cleararginfo[] =
{
	[C_ATTRELSCHEMA_ARG] = {"schemaname", TEXTOID},
	[C_ATTRELNAME_ARG] = {"relname", TEXTOID},
	[C_ATTNAME_ARG] = {"attname", TEXTOID},
	[C_INHERITED_ARG] = {"inherited", BOOLOID},
	[C_NUM_ATTRIBUTE_STATS_ARGS] = {0}
};

static bool attribute_statistics_update(FunctionCallInfo fcinfo);
static bool attribute_statistics_update_internal(Oid reloid,
												 const char *attname,
												 AttrNumber attnum,
												 bool inherited,
												 FunctionCallInfo fcinfo);
static void upsert_pg_statistic(Relation starel, HeapTuple oldtup,
								const Datum *values, const bool *nulls, const bool *replaces);
static bool delete_pg_statistic(Oid reloid, AttrNumber attnum, bool stainherit);

/*
 * ============================================================================
 * 【中文注释】attribute_statistics_update —— 更新/导入单个列的属性统计信息（入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   这是"导入或更新单列统计信息"的核心入口（SQL 层由 pg_restore_attribute_stats()
 *   调用）。它负责：从 fcinfo 位置参数中解析出目标模式名、表名、列标识（列名或列号）、
 *   是否统计继承表；加锁并做权限/类型等前置检查；然后把用户提供的各种统计值写入
 *   pg_statistic 系统表（由 attribute_statistics_update_internal() 完成）。
 *
 * 参数：
 *   fcinfo - 位置参数调用信息，参数布局由枚举 attribute_stats_argnum 定义，例如：
 *       ATTRELSCHEMA_ARG(0) = 模式名(text)、ATTRELNAME_ARG(1) = 表名(text)、
 *       ATTNAME_ARG(2) = 列名(text，与 ATT NUM 二选一)、ATTNUM_ARG(3) = 列号(int2)、
 *       INHERITED_ARG(4) = 是否含继承表(bool)、NULL_FRAC_ARG = 空值比例(float4)、
 *       AVG_WIDTH_ARG = 平均宽度(int4)、N_DISTINCT_ARG = 去重数估计(float4)、
 *       MOST_COMMON_VALS_ARG / MOST_COMMON_FREQS_ARG = MCV 值/频率、
 *       HISTOGRAM_BOUNDS_ARG = 直方图边界、CORRELATION_ARG = 相关性，
 *       以及数组类型专用的 MCELEM/DECHIST/范围类型统计等。
 *       凡 PG_ARGISNULL() 为真的参数表示"本次未指定"，对应统计项保持原值不变。
 *
 * 返回值：
 *   bool - true 表示所有指定统计项都成功；false 表示某个统计项因参数非法被跳过
 *          （该函数对这类问题只发 WARNING，不会中断整个操作）。
 *
 * 设计思想：
 *   1.【先加锁再查属性】：使用 RangeVarGetRelidExtended() 以 ShareUpdateExclusiveLock
 *      锁定目标表，并借助回调 RangeVarCallbackForStats() 在加锁过程中完成权限检查
 *      （要求表属主或拥有 MAINTAIN 权限）。这样做避免了"先解析名字、后加锁"之间的
 *      TOCTOU 竞态，也保证锁顺序一致。
 *   2.【恢复期间禁止写统计】：若正处于流式恢复（RecoveryInProgress），直接报 ERROR，
 *      防止在主库之外的实例上修改统计信息。
 *   3.【列标识二选一】：允许按列名(attname)或列号(attnum)指定列，但二者不可同时给出。
 *      按名字给时需用 get_attnum() 解析出列号；按列号给时反查列名，并用
 *      SearchSysCacheExistsAttName() 额外检查，因为 get_attname() 本身不检查
 *      attisdropped（已删除列）。
 *   4.【禁止系统列】：attnum < 0 表示系统列（如 ctid、xmin 等），不支持其统计信息，
 *      直接报错。
 *
 * 调用链：
 *   pg_restore_attribute_stats()(SQL) → attribute_statistics_update()
 *   → attribute_statistics_update_internal()（实际写库工作）
 * ============================================================================
 */
static bool
attribute_statistics_update(FunctionCallInfo fcinfo)
{
	char	   *nspname;
	char	   *relname;
	Oid			reloid;
	char	   *attname;
	AttrNumber	attnum;
	bool		inherited;
	Oid			locked_table = InvalidOid;

	stats_check_required_arg(fcinfo, attarginfo, ATTRELSCHEMA_ARG);
	stats_check_required_arg(fcinfo, attarginfo, ATTRELNAME_ARG);

	nspname = TextDatumGetCString(PG_GETARG_DATUM(ATTRELSCHEMA_ARG));
	relname = TextDatumGetCString(PG_GETARG_DATUM(ATTRELNAME_ARG));

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("Statistics cannot be modified during recovery.")));

	/* lock before looking up attribute */
	reloid = RangeVarGetRelidExtended(makeRangeVar(nspname, relname, -1),
									  ShareUpdateExclusiveLock, 0,
									  RangeVarCallbackForStats, &locked_table);

	/* user can specify either attname or attnum, but not both */
	if (!PG_ARGISNULL(ATTNAME_ARG))
	{
		if (!PG_ARGISNULL(ATTNUM_ARG))
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("cannot specify both \"%s\" and \"%s\"", "attname", "attnum")));
		attname = TextDatumGetCString(PG_GETARG_DATUM(ATTNAME_ARG));
		attnum = get_attnum(reloid, attname);
		/* note that this test covers attisdropped cases too: */
		if (attnum == InvalidAttrNumber)
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_COLUMN),
					 errmsg("column \"%s\" of relation \"%s\" does not exist",
							attname, relname)));
	}
	else if (!PG_ARGISNULL(ATTNUM_ARG))
	{
		attnum = PG_GETARG_INT16(ATTNUM_ARG);
		attname = get_attname(reloid, attnum, true);
		/* annoyingly, get_attname doesn't check attisdropped */
		if (attname == NULL ||
			!SearchSysCacheExistsAttName(reloid, attname))
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_COLUMN),
					 errmsg("column %d of relation \"%s\" does not exist",
							attnum, relname)));
	}
	else
	{
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("must specify either \"%s\" or \"%s\"", "attname", "attnum")));
		attname = NULL;			/* keep compiler quiet */
		attnum = 0;
	}

	if (attnum < 0)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot modify statistics on system column \"%s\"",
						attname)));

	stats_check_required_arg(fcinfo, attarginfo, INHERITED_ARG);
	inherited = PG_GETARG_BOOL(INHERITED_ARG);

	return attribute_statistics_update_internal(reloid, attname, attnum,
												inherited, fcinfo);
}

/*
 * ============================================================================
 * 【中文注释】attribute_statistics_update_internal —— 属性统计更新的工作函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   attribute_statistics_update() 的"干活"部分。调用方已经完成了加锁和列解析，
 *   本函数不再需要关心锁/权限/列名解析，只需根据 fcinfo 中的参数把各统计项
 *   （MCV、直方图、相关性、MCELEM、数组元素计数直方图、范围类型统计等）整理成
 *   pg_statistic 一条记录，然后 upsert 进 pg_statistic 表。
 *
 * 参数：
 *   reloid   - 已锁定关系的 OID。
 *   attname  - 列名（仅用于报错信息）。
 *   attnum   - 列号（已确保是用户列，attnum>0）。
 *   inherited- 统计是否针对继承树（stainherit 标志）。
 *   fcinfo   - 位置参数，与 attribute_statistics_update() 相同的布局。
 *
 * 返回值：
 *   bool - true 全部成功；false 某个统计项因"参数不合法/类型不支持"被降级跳过。
 *
 * 设计思想：
 *   1.【按需决定要写哪些统计项】：
 *     通过 do_mcv / do_histogram / do_correlation / do_mcelem / do_dechist /
 *     do_bounds_histogram / do_range_length_histogram 等布尔变量，判断哪些参数
 *     被提供。每个 do_* 还配合 stats_check_arg_*() 做前置校验，任何一处校验失败
 *     就把对应 do_* 置 false 并置 result=false，实现"单个统计项出错不影响其他项"。
 *   2.【从属性推导类型信息】：调用 statatt_get_type() 拿到列的类型 OID、typmod、
 *     排序/相等操作符等；若需要 MCELEM/DECHIST 再调 statatt_get_elem_type() 取
 *     元素类型。原因是 MCV 等统计以 anyarray 存储，必须用正确的元素类型来构建数组。
 *   3.【前置条件检查】：直方图与相关性需要小于操作符(lt_opr)；范围统计只对
 *     范围/多范围类型有效；否则发 WARNING 并放弃对应项。
 *   4.【更新或新建两条路径合一】：先用 SearchSysCache3(STATRELATTINH) 查是否已有
 *     该 (rel,attnum,inh) 的 pg_statistic 记录。若存在，用 heap_deform_tuple() 把
 *     旧值解出作为基础（未指定的项保持旧值）；若不存在，用
 *     statatt_init_empty_tuple() 构造全默认的空记录。之后对每个统计项通过
 *     statatt_set_slot() 填进对应 stakind 槽位，并记录 replaces[] 标记哪些列被改写。
 *   5.【范围类型直方图的顺序怪癖】：BOUNDS_HISTOGRAM 数值上大于
 *     RANGE_LENGTH_HISTOGRAM，但代码刻意把 BOUNDS 放在前面，为的是与 ANALYZE
 *     写入顺序保持一致（见原英文注释）。
 * ============================================================================
 */
static bool
attribute_statistics_update_internal(Oid reloid,
									 const char *attname, AttrNumber attnum,
									 bool inherited, FunctionCallInfo fcinfo)
{
	Relation	starel;
	HeapTuple	statup;

	Oid			atttypid = InvalidOid;
	int32		atttypmod;
	char		atttyptype;
	Oid			atttypcoll = InvalidOid;
	Oid			eq_opr = InvalidOid;
	Oid			lt_opr = InvalidOid;

	Oid			elemtypid = InvalidOid;
	Oid			elem_eq_opr = InvalidOid;

	FmgrInfo	array_in_fn;

	bool		do_mcv = !PG_ARGISNULL(MOST_COMMON_FREQS_ARG) &&
		!PG_ARGISNULL(MOST_COMMON_VALS_ARG);
	bool		do_histogram = !PG_ARGISNULL(HISTOGRAM_BOUNDS_ARG);
	bool		do_correlation = !PG_ARGISNULL(CORRELATION_ARG);
	bool		do_mcelem = !PG_ARGISNULL(MOST_COMMON_ELEMS_ARG) &&
		!PG_ARGISNULL(MOST_COMMON_ELEM_FREQS_ARG);
	bool		do_dechist = !PG_ARGISNULL(ELEM_COUNT_HISTOGRAM_ARG);
	bool		do_bounds_histogram = !PG_ARGISNULL(RANGE_BOUNDS_HISTOGRAM_ARG);
	bool		do_range_length_histogram = !PG_ARGISNULL(RANGE_LENGTH_HISTOGRAM_ARG) &&
		!PG_ARGISNULL(RANGE_EMPTY_FRAC_ARG);

	Datum		values[Natts_pg_statistic] = {0};
	bool		nulls[Natts_pg_statistic] = {0};
	bool		replaces[Natts_pg_statistic] = {0};

	bool		result = true;

	/*
	 * Check argument sanity. If some arguments are unusable, emit a WARNING
	 * and set the corresponding argument to NULL in fcinfo.
	 */

	if (!stats_check_arg_array(fcinfo, attarginfo, MOST_COMMON_FREQS_ARG))
	{
		do_mcv = false;
		result = false;
	}

	if (!stats_check_arg_array(fcinfo, attarginfo, MOST_COMMON_ELEM_FREQS_ARG))
	{
		do_mcelem = false;
		result = false;
	}
	if (!stats_check_arg_array(fcinfo, attarginfo, ELEM_COUNT_HISTOGRAM_ARG))
	{
		do_dechist = false;
		result = false;
	}

	if (!stats_check_arg_pair(fcinfo, attarginfo,
							  MOST_COMMON_VALS_ARG, MOST_COMMON_FREQS_ARG))
	{
		do_mcv = false;
		result = false;
	}

	if (!stats_check_arg_pair(fcinfo, attarginfo,
							  MOST_COMMON_ELEMS_ARG,
							  MOST_COMMON_ELEM_FREQS_ARG))
	{
		do_mcelem = false;
		result = false;
	}

	if (!stats_check_arg_pair(fcinfo, attarginfo,
							  RANGE_LENGTH_HISTOGRAM_ARG,
							  RANGE_EMPTY_FRAC_ARG))
	{
		do_range_length_histogram = false;
		result = false;
	}

	/* derive information from attribute */
	statatt_get_type(reloid, attnum,
					 &atttypid, &atttypmod,
					 &atttyptype, &atttypcoll,
					 &eq_opr, &lt_opr);

	/* if needed, derive element type */
	if (do_mcelem || do_dechist)
	{
		if (!statatt_get_elem_type(atttypid, atttyptype,
								   &elemtypid, &elem_eq_opr))
		{
			ereport(WARNING,
					(errmsg("could not determine element type of column \"%s\"", attname),
					 errdetail("Cannot set %s or %s.",
							   "STATISTIC_KIND_MCELEM", "STATISTIC_KIND_DECHIST")));
			elemtypid = InvalidOid;
			elem_eq_opr = InvalidOid;

			do_mcelem = false;
			do_dechist = false;
			result = false;
		}
	}

	/* histogram and correlation require less-than operator */
	if ((do_histogram || do_correlation) && !OidIsValid(lt_opr))
	{
		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("could not determine less-than operator for column \"%s\"", attname),
				 errdetail("Cannot set %s or %s.",
						   "STATISTIC_KIND_HISTOGRAM", "STATISTIC_KIND_CORRELATION")));

		do_histogram = false;
		do_correlation = false;
		result = false;
	}

	/* only range types can have range stats */
	if ((do_range_length_histogram || do_bounds_histogram) &&
		!(atttyptype == TYPTYPE_RANGE || atttyptype == TYPTYPE_MULTIRANGE))
	{
		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("column \"%s\" is not a range type", attname),
				 errdetail("Cannot set %s or %s.",
						   "STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM", "STATISTIC_KIND_BOUNDS_HISTOGRAM")));

		do_bounds_histogram = false;
		do_range_length_histogram = false;
		result = false;
	}

	fmgr_info(F_ARRAY_IN, &array_in_fn);

	starel = table_open(StatisticRelationId, RowExclusiveLock);

	statup = SearchSysCache3(STATRELATTINH, ObjectIdGetDatum(reloid), Int16GetDatum(attnum), BoolGetDatum(inherited));

	/* initialize from existing tuple if exists */
	if (HeapTupleIsValid(statup))
		heap_deform_tuple(statup, RelationGetDescr(starel), values, nulls);
	else
		statatt_init_empty_tuple(reloid, attnum, inherited, values, nulls,
								 replaces);

	/* if specified, set to argument values */
	if (!PG_ARGISNULL(NULL_FRAC_ARG))
	{
		values[Anum_pg_statistic_stanullfrac - 1] = PG_GETARG_DATUM(NULL_FRAC_ARG);
		replaces[Anum_pg_statistic_stanullfrac - 1] = true;
	}
	if (!PG_ARGISNULL(AVG_WIDTH_ARG))
	{
		values[Anum_pg_statistic_stawidth - 1] = PG_GETARG_DATUM(AVG_WIDTH_ARG);
		replaces[Anum_pg_statistic_stawidth - 1] = true;
	}
	if (!PG_ARGISNULL(N_DISTINCT_ARG))
	{
		values[Anum_pg_statistic_stadistinct - 1] = PG_GETARG_DATUM(N_DISTINCT_ARG);
		replaces[Anum_pg_statistic_stadistinct - 1] = true;
	}

	/* STATISTIC_KIND_MCV */
	if (do_mcv)
	{
		bool		converted;
		Datum		stanumbers = PG_GETARG_DATUM(MOST_COMMON_FREQS_ARG);
		Datum		stavalues = statatt_build_stavalues("most_common_vals",
														&array_in_fn,
														PG_GETARG_DATUM(MOST_COMMON_VALS_ARG),
														atttypid, atttypmod,
														&converted);

		if (converted)
		{
			ArrayType  *vals_arr = DatumGetArrayTypeP(stavalues);
			ArrayType  *nums_arr = DatumGetArrayTypeP(stanumbers);
			int			nvals = ARR_DIMS(vals_arr)[0];
			int			nnums = ARR_DIMS(nums_arr)[0];

			if (nvals != nnums)
			{
				ereport(WARNING,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("could not parse \"%s\": incorrect number of elements (same as \"%s\" required)",
								"most_common_vals",
								"most_common_freqs")));
				result = false;
			}
			else
			{
				statatt_set_slot(values, nulls, replaces,
								 STATISTIC_KIND_MCV,
								 eq_opr, atttypcoll,
								 stanumbers, false, stavalues, false);
			}
		}
		else
			result = false;
	}

	/* STATISTIC_KIND_HISTOGRAM */
	if (do_histogram)
	{
		Datum		stavalues;
		bool		converted = false;

		stavalues = statatt_build_stavalues("histogram_bounds",
											&array_in_fn,
											PG_GETARG_DATUM(HISTOGRAM_BOUNDS_ARG),
											atttypid, atttypmod,
											&converted);

		if (converted)
		{
			statatt_set_slot(values, nulls, replaces,
							 STATISTIC_KIND_HISTOGRAM,
							 lt_opr, atttypcoll,
							 0, true, stavalues, false);
		}
		else
			result = false;
	}

	/* STATISTIC_KIND_CORRELATION */
	if (do_correlation)
	{
		Datum		elems[] = {PG_GETARG_DATUM(CORRELATION_ARG)};
		ArrayType  *arry = construct_array_builtin(elems, 1, FLOAT4OID);
		Datum		stanumbers = PointerGetDatum(arry);

		statatt_set_slot(values, nulls, replaces,
						 STATISTIC_KIND_CORRELATION,
						 lt_opr, atttypcoll,
						 stanumbers, false, 0, true);
	}

	/* STATISTIC_KIND_MCELEM */
	if (do_mcelem)
	{
		Datum		stanumbers = PG_GETARG_DATUM(MOST_COMMON_ELEM_FREQS_ARG);
		bool		converted = false;
		Datum		stavalues;

		stavalues = statatt_build_stavalues("most_common_elems",
											&array_in_fn,
											PG_GETARG_DATUM(MOST_COMMON_ELEMS_ARG),
											elemtypid, atttypmod,
											&converted);

		if (converted)
		{
			statatt_set_slot(values, nulls, replaces,
							 STATISTIC_KIND_MCELEM,
							 elem_eq_opr, atttypcoll,
							 stanumbers, false, stavalues, false);
		}
		else
			result = false;
	}

	/* STATISTIC_KIND_DECHIST */
	if (do_dechist)
	{
		Datum		stanumbers = PG_GETARG_DATUM(ELEM_COUNT_HISTOGRAM_ARG);

		statatt_set_slot(values, nulls, replaces,
						 STATISTIC_KIND_DECHIST,
						 elem_eq_opr, atttypcoll,
						 stanumbers, false, 0, true);
	}

	/*
	 * STATISTIC_KIND_BOUNDS_HISTOGRAM
	 *
	 * This stakind appears before STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM even
	 * though it is numerically greater, and all other stakinds appear in
	 * numerical order. We duplicate this quirk for consistency.
	 */
	if (do_bounds_histogram)
	{
		bool		converted = false;
		Datum		stavalues;

		stavalues = statatt_build_stavalues("range_bounds_histogram",
											&array_in_fn,
											PG_GETARG_DATUM(RANGE_BOUNDS_HISTOGRAM_ARG),
											atttypid, atttypmod,
											&converted);

		if (converted &&
			statatt_check_bounds_histogram(stavalues))
		{
			statatt_set_slot(values, nulls, replaces,
							 STATISTIC_KIND_BOUNDS_HISTOGRAM,
							 InvalidOid, InvalidOid,
							 0, true, stavalues, false);
		}
		else
			result = false;
	}

	/* STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM */
	if (do_range_length_histogram)
	{
		/* The anyarray is always a float8[] for this stakind */
		Datum		elems[] = {PG_GETARG_DATUM(RANGE_EMPTY_FRAC_ARG)};
		ArrayType  *arry = construct_array_builtin(elems, 1, FLOAT4OID);
		Datum		stanumbers = PointerGetDatum(arry);

		bool		converted = false;
		Datum		stavalues;

		stavalues = statatt_build_stavalues("range_length_histogram",
											&array_in_fn,
											PG_GETARG_DATUM(RANGE_LENGTH_HISTOGRAM_ARG),
											FLOAT8OID, 0, &converted);

		if (converted)
		{
			statatt_set_slot(values, nulls, replaces,
							 STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM,
							 Float8LessOperator, InvalidOid,
							 stanumbers, false, stavalues, false);
		}
		else
			result = false;
	}

	upsert_pg_statistic(starel, statup, values, nulls, replaces);

	if (HeapTupleIsValid(statup))
		ReleaseSysCache(statup);
	table_close(starel, RowExclusiveLock);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】upsert_pg_statistic —— 向 pg_statistic 表插入或更新一条记录
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把一组值（values/nulls/replaces）写入 pg_statistic 表：若旧元组存在则按
 *   replaces 指定列做就地更新（heap_modify_tuple + CatalogTupleUpdate），否则
 *   插入一条新元组（heap_form_tuple + CatalogTupleInsert）。
 *
 * 参数：
 *   starel   - 已以 RowExclusiveLock 打开的 pg_statistic 关系。
 *   oldtup   - 从 syscache 取到的旧记录（可能为 NULL，表示此前无记录）。
 *   values   - Natts_pg_statistic 长度的列值数组。
 *   nulls    - 与 values 对应的"是否为 NULL"标志。
 *   replaces - 与 values 对应的"是否替换该列"标志（仅更新路径使用）。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   pg_statistic 是普通堆表（非 MVCC 语义的 catcache 索引由 CatalogTuple* 维护）。
 *   更新时用 heap_modify_tuple 同时传入 values/nulls/replaces 三个数组，
 *   replaces=true 的列取 values 里的新值，replaces=false 的列保留旧元组中的值，
 *   从而实现"只覆盖用户指定统计项"的语义。操作结束后 CommandCounterIncrement()
 *   提升命令计数器，确保后续同一命令中的查询能看到本次修改（系统表写操作的通用
 *   惯例）。
 * ============================================================================
 */
static void
upsert_pg_statistic(Relation starel, HeapTuple oldtup,
					const Datum *values, const bool *nulls, const bool *replaces)
{
	HeapTuple	newtup;

	if (HeapTupleIsValid(oldtup))
	{
		newtup = heap_modify_tuple(oldtup, RelationGetDescr(starel),
								   values, nulls, replaces);
		CatalogTupleUpdate(starel, &newtup->t_self, newtup);
	}
	else
	{
		newtup = heap_form_tuple(RelationGetDescr(starel), values, nulls);
		CatalogTupleInsert(starel, newtup);
	}

	heap_freetuple(newtup);

	CommandCounterIncrement();
}

/*
 * ============================================================================
 * 【中文注释】delete_pg_statistic —— 删除 pg_statistic 中的一条列统计记录
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   根据 (reloid, attnum, stainherit) 三元组，在 pg_statistic 表中查找并删除对应
 *   记录。它同时服务于 SQL 函数 pg_clear_attribute_stats() 和内部函数
 *   delete_attribute_statistics()。
 *
 * 参数：
 *   reloid    - 目标关系的 OID。
 *   attnum    - 目标列号。
 *   stainherit- 是否针对继承树的统计记录。
 *
 * 返回值：
 *   bool - true 表示确实删除了一条记录；false 表示本来就无此记录（幂等删除）。
 *
 * 设计思想：
 *   通过系统缓存 SearchSysCache3(STATRELATTINH) 按主键精确查找（该缓存键正好是
 *   (starelid, staattnum, stainherit)），命中后调用 CatalogTupleDelete() 删除。
 *   删除系统表元组必须经由 CatalogTupleDelete() 而非普通 heap_delete，以保持
 *   系统表索引同步。结尾同样调用 CommandCounterIncrement()。
 * ============================================================================
 */
static bool
delete_pg_statistic(Oid reloid, AttrNumber attnum, bool stainherit)
{
	Relation	sd = table_open(StatisticRelationId, RowExclusiveLock);
	HeapTuple	oldtup;
	bool		result = false;

	/* Is there already a pg_statistic tuple for this attribute? */
	oldtup = SearchSysCache3(STATRELATTINH,
							 ObjectIdGetDatum(reloid),
							 Int16GetDatum(attnum),
							 BoolGetDatum(stainherit));

	if (HeapTupleIsValid(oldtup))
	{
		CatalogTupleDelete(sd, &oldtup->t_self);
		ReleaseSysCache(oldtup);
		result = true;
	}

	table_close(sd, RowExclusiveLock);

	CommandCounterIncrement();

	return result;
}

/*
 * ============================================================================
 * 【中文注释】pg_clear_attribute_stats —— SQL 函数：清空指定列的统计信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   可直接从 SQL 调用的函数（对应目录 pg_proc 中的一项），删除某个表某列的
 *   pg_statistic 记录，使该列回到"无统计"状态。参数为
 *   (schemaname, relname, attname, inherited)。
 *
 * 参数：
 *   fcinfo - PG_FUNCTION_ARGS 宏展开的标准调用信息。
 *
 * 返回值：
 *   Datum（void）—— 无返回。
 *
 * 设计思想：
 *   与 attribute_statistics_update() 类似的前置处理：必需参数非空检查、恢复期间
 *   禁止操作、先加锁并做权限回调、用 get_attnum() 把列名转列号；额外拒绝系统列
 *   （attnum<0）并在列不存在时报错。之后直接调用 delete_pg_statistic() 完成删除。
 *   注意：本函数不允许用 attnum 指定列，只能给 attname，因此列存在性检查放在
 *   get_attnum() 之后（InvalidAttrNumber 表示不存在）。
 * ============================================================================
 */
Datum
pg_clear_attribute_stats(PG_FUNCTION_ARGS)
{
	char	   *nspname;
	char	   *relname;
	Oid			reloid;
	char	   *attname;
	AttrNumber	attnum;
	bool		inherited;
	Oid			locked_table = InvalidOid;

	stats_check_required_arg(fcinfo, cleararginfo, C_ATTRELSCHEMA_ARG);
	stats_check_required_arg(fcinfo, cleararginfo, C_ATTRELNAME_ARG);
	stats_check_required_arg(fcinfo, cleararginfo, C_ATTNAME_ARG);
	stats_check_required_arg(fcinfo, cleararginfo, C_INHERITED_ARG);

	nspname = TextDatumGetCString(PG_GETARG_DATUM(C_ATTRELSCHEMA_ARG));
	relname = TextDatumGetCString(PG_GETARG_DATUM(C_ATTRELNAME_ARG));

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("Statistics cannot be modified during recovery.")));

	reloid = RangeVarGetRelidExtended(makeRangeVar(nspname, relname, -1),
									  ShareUpdateExclusiveLock, 0,
									  RangeVarCallbackForStats, &locked_table);

	attname = TextDatumGetCString(PG_GETARG_DATUM(C_ATTNAME_ARG));
	attnum = get_attnum(reloid, attname);

	if (attnum < 0)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot clear statistics on system column \"%s\"",
						attname)));

	if (attnum == InvalidAttrNumber)
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_COLUMN),
				 errmsg("column \"%s\" of relation \"%s\" does not exist",
						attname, get_rel_name(reloid))));

	inherited = PG_GETARG_BOOL(C_INHERITED_ARG);

	delete_pg_statistic(reloid, attnum, inherited);
	PG_RETURN_VOID();
}

/*
 * ============================================================================
 * 【中文注释】pg_restore_attribute_stats —— SQL 函数：恢复（导入）单列统计信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   可直接从 SQL 调用的"恢复/导入列统计"函数。它以"键-值对"形式接收变长
 *   (variadic) 参数（形如 pg_restore_attribute_stats('schemaname'=>'public',
 *   'relname'=>'t', 'attname'=>'c', 'null_frac'=>0.1, ...)），把键值对翻译成
 *   位置参数后转交 attribute_statistics_update() 执行。
 *
 * 参数：
 *   fcinfo - 原始变长参数调用信息（name,value,name,value,...）。
 *
 * 返回值：
 *   bool - 由内部更新函数的结果合并而成；任一环节失败返回 false。
 *
 * 设计思想：
 *   之所以用"变长键值对"而非普通命名参数：键值对方式可以在不破坏既有调用的情况下
 *   灵活增删参数，便于长期演进。翻译工作由 stats_fill_fcinfo_from_arg_pairs() 完成，
 *   它把每个已知名字的键映射到位置参数数组的对应下标（未知名字或类型不匹配会发
 *   WARNING 并把 result 置 false，其余参数照常处理）。翻译后的结果存入栈上的
 *   LOCAL_FCINFO(positional_fcinfo)，再用它与目标参数个数匹配的尺寸初始化。
 *
 * 说明：参数与 pg_stats 视图列一一对应；ANYARRAY 类型的参数（如 most_common_vals）
 *   以文本形式传入，文本内容必须是"该列类型数组"的合法输入，解析失败时整个函数
 *   会报错。
 * ============================================================================
 */
Datum
pg_restore_attribute_stats(PG_FUNCTION_ARGS)
{
	LOCAL_FCINFO(positional_fcinfo, NUM_ATTRIBUTE_STATS_ARGS);
	bool		result = true;

	InitFunctionCallInfoData(*positional_fcinfo, NULL, NUM_ATTRIBUTE_STATS_ARGS,
							 InvalidOid, NULL, NULL);

	if (!stats_fill_fcinfo_from_arg_pairs(fcinfo, positional_fcinfo,
										  attarginfo))
		result = false;

	if (!attribute_statistics_update(positional_fcinfo))
		result = false;

	PG_RETURN_BOOL(result);
}

/*
 * ============================================================================
 * 【中文注释】import_attribute_statistics —— 以 C 接口导入单列统计信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 pg_restore_attribute_stats() 等价，但面向 C 代码而非 SQL 调用：它不接收
 *   变长键值对，而是接收已经按参数顺序排好的 NullableDatum 数组。调用方通常已经
 *   打开并锁定了 rel（例如从其他系统导入统计的代码）。
 *
 * 参数：
 *   rel      - 已打开的目标关系。
 *   attnum   - 目标列号。
 *   inherited- 是否统计继承树。
 *   version  - 版本号（当前忽略，预留用于解释旧版统计格式）。
 *   null_frac / avg_width / n_distinct / most_common_vals / most_common_freqs /
 *   histogram_bounds / correlation / most_common_elems / most_common_elem_freqs /
 *   elem_count_histogram / range_length_histogram / range_empty_frac /
 *   range_bounds_histogram - 每个统计项对应的 NullableDatum 值
 *                            （isnull=true 表示该项未指定/为 NULL）。
 *
 * 返回值：
 *   bool - true 表示全部成功；false 表示有统计项被降级跳过（见内部函数）。
 *
 * 设计思想：
 *   1. 先做断言，确保所有统计项指针非空（表示"已显式给出"，即使语义上可以是
 *      NULL）。
 *   2. 把所有输入值填进一个临时构造的位置参数 fcinfo（newfcinfo）：前 5 个位置
 *      （模式名/表名/列名/列号/继承标志）由 rel 与 attnum 推导，其余位置直接
 *      逐项复制 NullableDatum。
 *   3. 通过复用 attribute_statistics_update_internal() 完成与 SQL 路径完全一致的
 *      校验与写库逻辑，避免两套实现漂移。
 * ============================================================================
 */
bool
import_attribute_statistics(Relation rel, AttrNumber attnum, bool inherited,
							const NullableDatum *version,
							const NullableDatum *null_frac,
							const NullableDatum *avg_width,
							const NullableDatum *n_distinct,
							const NullableDatum *most_common_vals,
							const NullableDatum *most_common_freqs,
							const NullableDatum *histogram_bounds,
							const NullableDatum *correlation,
							const NullableDatum *most_common_elems,
							const NullableDatum *most_common_elem_freqs,
							const NullableDatum *elem_count_histogram,
							const NullableDatum *range_length_histogram,
							const NullableDatum *range_empty_frac,
							const NullableDatum *range_bounds_histogram)
{
	LOCAL_FCINFO(newfcinfo, NUM_ATTRIBUTE_STATS_ARGS);
	Oid			reloid = RelationGetRelid(rel);
	char	   *relname = RelationGetRelationName(rel);
	char	   *attname = get_attname(reloid, attnum, true);

	Assert(null_frac);
	Assert(avg_width);
	Assert(n_distinct);
	Assert(most_common_vals);
	Assert(most_common_freqs);
	Assert(histogram_bounds);
	Assert(correlation);
	Assert(most_common_elems);
	Assert(most_common_elem_freqs);
	Assert(elem_count_histogram);
	Assert(range_length_histogram);
	Assert(range_empty_frac);
	Assert(range_bounds_histogram);

	/* annoyingly, get_attname doesn't check attisdropped */
	if (attname == NULL ||
		!SearchSysCacheExistsAttName(reloid, attname))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_COLUMN),
				 errmsg("column %d of relation \"%s\" does not exist",
						attnum, relname)));

	InitFunctionCallInfoData(*newfcinfo, NULL, NUM_ATTRIBUTE_STATS_ARGS,
							 InvalidOid, NULL, NULL);

	newfcinfo->args[ATTRELSCHEMA_ARG].value =
		CStringGetTextDatum(get_namespace_name(RelationGetNamespace(rel)));
	newfcinfo->args[ATTRELSCHEMA_ARG].isnull = false;
	newfcinfo->args[ATTRELNAME_ARG].value = CStringGetTextDatum(relname);
	newfcinfo->args[ATTRELNAME_ARG].isnull = false;
	newfcinfo->args[ATTNAME_ARG].value = CStringGetTextDatum(attname);
	newfcinfo->args[ATTNAME_ARG].isnull = false;
	newfcinfo->args[ATTNUM_ARG].value = Int16GetDatum(attnum);
	newfcinfo->args[ATTNUM_ARG].isnull = false;
	newfcinfo->args[INHERITED_ARG].value = BoolGetDatum(inherited);
	newfcinfo->args[INHERITED_ARG].isnull = false;

	newfcinfo->args[NULL_FRAC_ARG] = *null_frac;
	newfcinfo->args[AVG_WIDTH_ARG] = *avg_width;
	newfcinfo->args[N_DISTINCT_ARG] = *n_distinct;
	newfcinfo->args[MOST_COMMON_VALS_ARG] = *most_common_vals;
	newfcinfo->args[MOST_COMMON_FREQS_ARG] = *most_common_freqs;
	newfcinfo->args[HISTOGRAM_BOUNDS_ARG] = *histogram_bounds;
	newfcinfo->args[CORRELATION_ARG] = *correlation;
	newfcinfo->args[MOST_COMMON_ELEMS_ARG] = *most_common_elems;
	newfcinfo->args[MOST_COMMON_ELEM_FREQS_ARG] = *most_common_elem_freqs;
	newfcinfo->args[ELEM_COUNT_HISTOGRAM_ARG] = *elem_count_histogram;
	newfcinfo->args[RANGE_LENGTH_HISTOGRAM_ARG] = *range_length_histogram;
	newfcinfo->args[RANGE_EMPTY_FRAC_ARG] = *range_empty_frac;
	newfcinfo->args[RANGE_BOUNDS_HISTOGRAM_ARG] = *range_bounds_histogram;

	return attribute_statistics_update_internal(reloid, attname, attnum,
												inherited, newfcinfo);
}

/*
 * ============================================================================
 * 【中文注释】delete_attribute_statistics —— 以 C 接口删除单列统计信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   面向 C 代码的封装：给定已打开的关系与列号，删除该列的 pg_statistic 记录。
 *   与 SQL 函数 pg_clear_attribute_stats() 等价，但不需要做参数解析/加锁/权限
 *   检查（这些由调用方负责）。
 *
 * 参数：
 *   rel      - 目标关系（由调用方持有锁）。
 *   attnum   - 列号。
 *   inherited- 是否针对继承树。
 *
 * 返回值：
 *   bool - 是否有记录被真正删除。
 *
 * 设计思想：
 *   薄封装，直接转调 delete_pg_statistic()，只负责把 Relation 转换为 relid。
 * ============================================================================
 */
bool
delete_attribute_statistics(Relation rel, AttrNumber attnum, bool inherited)
{
	return delete_pg_statistic(RelationGetRelid(rel), attnum, inherited);
}
