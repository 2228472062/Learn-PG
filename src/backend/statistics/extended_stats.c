/*-------------------------------------------------------------------------
 *
 * extended_stats.c
 *	  POSTGRES extended statistics
 *
 * Generic code supporting statistics objects created via CREATE STATISTICS.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/statistics/extended_stats.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/detoast.h"
#include "access/genam.h"
#include "access/htup_details.h"
#include "access/table.h"
#include "catalog/indexing.h"
#include "catalog/pg_statistic_ext.h"
#include "catalog/pg_statistic_ext_data.h"
#include "commands/defrem.h"
#include "commands/progress.h"
#include "executor/executor.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/optimizer.h"
#include "parser/parsetree.h"
#include "pgstat.h"
#include "postmaster/autovacuum.h"
#include "rewrite/rewriteHandler.h"
#include "statistics/extended_stats_internal.h"
#include "statistics/statistics.h"
#include "utils/acl.h"
#include "utils/array.h"
#include "utils/attoptcache.h"
#include "utils/builtins.h"
#include "utils/datum.h"
#include "utils/fmgroids.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/selfuncs.h"
#include "utils/syscache.h"

/*
 * To avoid consuming too much memory during analysis and/or too much space
 * in the resulting pg_statistic rows, we ignore varlena datums that are wider
 * than WIDTH_THRESHOLD (after detoasting!).  This is legitimate for MCV
 * and distinct-value calculations since a wide value is unlikely to be
 * duplicated at all, much less be a most-common value.  For the same reason,
 * ignoring wide values will not affect our estimates of histogram bin
 * boundaries very much.
 */
#define WIDTH_THRESHOLD  1024

/*
 * Used internally to refer to an individual statistics object, i.e.,
 * a pg_statistic_ext entry.
 */
typedef struct StatExtEntry
{
	Oid			statOid;		/* OID of pg_statistic_ext entry */
	char	   *schema;			/* statistics object's schema */
	char	   *name;			/* statistics object's name */
	Bitmapset  *columns;		/* attribute numbers covered by the object */
	List	   *types;			/* 'char' list of enabled statistics kinds */
	int			stattarget;		/* statistics target (-1 for default) */
	List	   *exprs;			/* expressions */
} StatExtEntry;


static List *fetch_statentries_for_relation(Relation pg_statext, Relation rel);
static VacAttrStats **lookup_var_attr_stats(Bitmapset *attrs, List *exprs,
											int nvacatts, VacAttrStats **vacatts);
static void statext_store(Oid statOid, bool inh,
						  MVNDistinct *ndistinct, MVDependencies *dependencies,
						  MCVList *mcv, Datum exprs, VacAttrStats **stats);
static int	statext_compute_stattarget(int stattarget,
									   int nattrs, VacAttrStats **stats);

/* Information needed to analyze a single simple expression. */
typedef struct AnlExprData
{
	Node	   *expr;			/* expression to analyze */
	VacAttrStats *vacattrstat;	/* statistics attrs to analyze */
} AnlExprData;

static void compute_expr_stats(Relation onerel, AnlExprData *exprdata,
							   int nexprs, HeapTuple *rows, int numrows);
static Datum serialize_expr_stats(AnlExprData *exprdata, int nexprs);
static Datum expr_fetch_func(VacAttrStatsP stats, int rownum, bool *isNull);
static AnlExprData *build_expr_data(List *exprs, int stattarget);

static StatsBuildData *make_build_data(Relation rel, StatExtEntry *stat,
									   int numrows, HeapTuple *rows,
									   VacAttrStats **stats, int stattarget);


/*
 * ============================================================================
 * 【中文注释】BuildRelationExtStatistics —— 计算并写回关系的扩展统计（顶层入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   使用普通单列 ANALYZE 采样的行数据，为表上定义的所有扩展统计对象计算其
 *   统计（ndistinct/dependencies/MCV/表达式统计），并序列化写回系统表
 *   pg_statistic_ext_data。
 *
 * 参数：
 *   onerel       - 被分析的关系。
 *   inh          - 是否包含继承子表。
 *   totalrows    - 全表估算行数。
 *   numrows      - 采样行数。
 *   rows         - 采样元组数组。
 *   natts        - 被分析的单列个数。
 *   vacattrstats - 单列的 VacAttrStats 数组（用于取列类型等信息）。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   1. 打开 pg_statistic_ext，用 fetch_statentries_for_relation() 取回该关系的所有
 *      统计对象列表（StatExtEntry）。
 *   2. 每个统计对象在独立内存上下文 cxt 中构建，循环结束 MemoryContextReset 释放，
 *      避免内存累积。
 *   3. 用 lookup_var_attr_stats() 检查本次分析的列是否覆盖该对象所需全部列；若
 *      不覆盖则（非 autovacuum 时）发 WARNING 并跳过。
 *   4. 用 statext_compute_stattarget() 计算统计目标；目标为 0 表示禁用该对象，跳过
 *      （保留旧统计，与单列统计的做法一致）。
 *   5. make_build_data() 评估表达式并准备 StatsBuildData；随后按对象请求的类型
 *      分别调用 statext_ndistinct_build/statext_dependencies_build/statext_mcv_build
 *      或表达式统计（build_expr_data + compute_expr_stats + serialize_expr_stats）。
 *   6. statext_store() 统一序列化并写回 catalog；通过
 *      pgstat_progress_update_* 上报进度。
 * ============================================================================
 */
void
BuildRelationExtStatistics(Relation onerel, bool inh, double totalrows,
						   int numrows, HeapTuple *rows,
						   int natts, VacAttrStats **vacattrstats)
{
	Relation	pg_stext;
	ListCell   *lc;
	List	   *statslist;
	MemoryContext cxt;
	MemoryContext oldcxt;
	int64		ext_cnt;

	/* Do nothing if there are no columns to analyze. */
	if (!natts)
		return;

	/* the list of stats has to be allocated outside the memory context */
	pg_stext = table_open(StatisticExtRelationId, RowExclusiveLock);
	statslist = fetch_statentries_for_relation(pg_stext, onerel);

	/* memory context for building each statistics object */
	cxt = AllocSetContextCreate(CurrentMemoryContext,
								"BuildRelationExtStatistics",
								ALLOCSET_DEFAULT_SIZES);
	oldcxt = MemoryContextSwitchTo(cxt);

	/* report this phase */
	if (statslist != NIL)
	{
		const int	index[] = {
			PROGRESS_ANALYZE_PHASE,
			PROGRESS_ANALYZE_EXT_STATS_TOTAL
		};
		const int64 val[] = {
			PROGRESS_ANALYZE_PHASE_COMPUTE_EXT_STATS,
			list_length(statslist)
		};

		pgstat_progress_update_multi_param(2, index, val);
	}

	ext_cnt = 0;
	foreach(lc, statslist)
	{
		StatExtEntry *stat = (StatExtEntry *) lfirst(lc);
		MVNDistinct *ndistinct = NULL;
		MVDependencies *dependencies = NULL;
		MCVList    *mcv = NULL;
		Datum		exprstats = (Datum) 0;
		VacAttrStats **stats;
		ListCell   *lc2;
		int			stattarget;
		StatsBuildData *data;

		/*
		 * Check if we can build these stats based on the column analyzed. If
		 * not, report this fact (except in autovacuum) and move on.
		 */
		stats = lookup_var_attr_stats(stat->columns, stat->exprs,
									  natts, vacattrstats);
		if (!stats)
		{
			if (!AmAutoVacuumWorkerProcess())
				ereport(WARNING,
						(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
						 errmsg("statistics object \"%s.%s\" could not be computed for relation \"%s.%s\"",
								stat->schema, stat->name,
								get_namespace_name(onerel->rd_rel->relnamespace),
								RelationGetRelationName(onerel)),
						 errtable(onerel)));
			continue;
		}

		/* compute statistics target for this statistics object */
		stattarget = statext_compute_stattarget(stat->stattarget,
												bms_num_members(stat->columns),
												stats);

		/*
		 * Don't rebuild statistics objects with statistics target set to 0
		 * (we just leave the existing values around, just like we do for
		 * regular per-column statistics).
		 */
		if (stattarget == 0)
			continue;

		/* evaluate expressions (if the statistics object has any) */
		data = make_build_data(onerel, stat, numrows, rows, stats, stattarget);

		/* compute statistic of each requested type */
		foreach(lc2, stat->types)
		{
			char		t = (char) lfirst_int(lc2);

			if (t == STATS_EXT_NDISTINCT)
				ndistinct = statext_ndistinct_build(totalrows, data);
			else if (t == STATS_EXT_DEPENDENCIES)
				dependencies = statext_dependencies_build(data);
			else if (t == STATS_EXT_MCV)
				mcv = statext_mcv_build(data, totalrows, stattarget);
			else if (t == STATS_EXT_EXPRESSIONS)
			{
				AnlExprData *exprdata;
				int			nexprs;

				/* should not happen, thanks to checks when defining stats */
				if (!stat->exprs)
					elog(ERROR, "requested expression stats, but there are no expressions");

				exprdata = build_expr_data(stat->exprs, stattarget);
				nexprs = list_length(stat->exprs);

				compute_expr_stats(onerel, exprdata, nexprs, rows, numrows);

				exprstats = serialize_expr_stats(exprdata, nexprs);
			}
		}

		/* store the statistics in the catalog */
		statext_store(stat->statOid, inh,
					  ndistinct, dependencies, mcv, exprstats, stats);

		/* for reporting progress */
		pgstat_progress_update_param(PROGRESS_ANALYZE_EXT_STATS_COMPUTED,
									 ++ext_cnt);

		/* free the data used for building this statistics object */
		MemoryContextReset(cxt);
	}

	MemoryContextSwitchTo(oldcxt);
	MemoryContextDelete(cxt);

	list_free(statslist);

	table_close(pg_stext, RowExclusiveLock);
}

/*
 * ============================================================================
 * 【中文注释】HasRelationExtStatistics —— 判断关系是否定义了扩展统计对象
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查 pg_statistic_ext 中是否存在 stxrelid 指向该关系的统计对象。
 *
 * 参数：
 *   onerel - 目标关系。
 *
 * 返回值：
 *   bool - 有则 true，无则 false。
 *
 * 设计思想：
 *   在 pg_statistic_ext 上按 stxrelid 索引（StatisticExtRelidIndexId）做等值扫描，
 *   取到第一条即存在。加 RowExclusiveLock 后扫描、关闭释放。
 * ============================================================================
 */
bool
HasRelationExtStatistics(Relation onerel)
{
	Relation	pg_statext;
	SysScanDesc scan;
	ScanKeyData skey;
	bool		found;

	pg_statext = table_open(StatisticExtRelationId, RowExclusiveLock);

	/*
	 * Prepare to scan pg_statistic_ext for entries having stxrelid = this
	 * rel.
	 */
	ScanKeyInit(&skey,
				Anum_pg_statistic_ext_stxrelid,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(RelationGetRelid(onerel)));

	scan = systable_beginscan(pg_statext, StatisticExtRelidIndexId, true,
							  NULL, 1, &skey);

	found = HeapTupleIsValid(systable_getnext(scan));

	systable_endscan(scan);

	table_close(pg_statext, RowExclusiveLock);

	return found;
}

/*
 * ============================================================================
 * 【中文注释】ComputeExtStatisticsRows —— 计算扩展统计所需的采样行数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   计算为了构建该表上的扩展统计，ANALYZE 需要采样多少行。只考虑"本次实际能构建"
 *   的统计对象——例如只分析了部分列时，会跳过需要额外列的统计对象。
 *
 * 参数：
 *   onerel       - 目标关系。
 *   natts        - 被分析的单列个数。
 *   vacattrstats - 单列 VacAttrStats 数组。
 *
 * 返回值：
 *   int - 需要的采样行数（= 300 * 最大统计目标），无可用对象时为 0。
 *
 * 设计思想：
 *   1. 遍历该关系的所有统计对象；用 lookup_var_attr_stats() 判断能否基于已分析
 *      列构建（不能则跳过，构建阶段的警告留到 BuildRelationExtStatistics）。
 *   2. 对每个可构建对象用 statext_compute_stattarget() 计算统计目标；取所有对象
 *      中的**最大值**（保证足够样本满足最"贪婪"的对象）。
 *   3. 最终按采样系数（300 行/目标）返回样本大小。
 *   关于统计目标的计算细节（对象目标、列目标、默认目标），参见
 *   statext_compute_stattarget()。
 * ============================================================================
 */
int
ComputeExtStatisticsRows(Relation onerel,
						 int natts, VacAttrStats **vacattrstats)
{
	Relation	pg_stext;
	ListCell   *lc;
	List	   *lstats;
	MemoryContext cxt;
	MemoryContext oldcxt;
	int			result = 0;

	/* If there are no columns to analyze, just return 0. */
	if (!natts)
		return 0;

	cxt = AllocSetContextCreate(CurrentMemoryContext,
								"ComputeExtStatisticsRows",
								ALLOCSET_DEFAULT_SIZES);
	oldcxt = MemoryContextSwitchTo(cxt);

	pg_stext = table_open(StatisticExtRelationId, RowExclusiveLock);
	lstats = fetch_statentries_for_relation(pg_stext, onerel);

	foreach(lc, lstats)
	{
		StatExtEntry *stat = (StatExtEntry *) lfirst(lc);
		int			stattarget;
		VacAttrStats **stats;
		int			nattrs = bms_num_members(stat->columns);

		/*
		 * Check if we can build this statistics object based on the columns
		 * analyzed. If not, ignore it (don't report anything, we'll do that
		 * during the actual build BuildRelationExtStatistics).
		 */
		stats = lookup_var_attr_stats(stat->columns, stat->exprs,
									  natts, vacattrstats);

		if (!stats)
			continue;

		/*
		 * Compute statistics target, based on what's set for the statistic
		 * object itself, and for its attributes.
		 */
		stattarget = statext_compute_stattarget(stat->stattarget,
												nattrs, stats);

		/* Use the largest value for all statistics objects. */
		if (stattarget > result)
			result = stattarget;
	}

	table_close(pg_stext, RowExclusiveLock);

	MemoryContextSwitchTo(oldcxt);
	MemoryContextDelete(cxt);

	/* compute sample size based on the statistics target */
	return (300 * result);
}

/*
 * ============================================================================
 * 【中文注释】statext_compute_stattarget —— 计算扩展统计对象的统计目标
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   解析一个扩展统计对象的最终统计目标（决定 MCV 项数等详细程度）。
 *
 * 参数：
 *   stattarget - 统计对象自身的统计目标（来自 ALTER STATISTICS ... SET STATISTICS）。
 *   nattrs     - 统计对象覆盖的列数。
 *   stats      - 对应列的 VacAttrStats 数组（含各列 attstattarget）。
 *
 * 返回值：
 *   int - 最终统计目标（>=0）。
 *
 * 设计思想：
 *   统计目标可能有三个来源，按优先级取：
 *   1. 统计对象自身：statstarget >= 0 时直接用（0 表示禁用该统计的构建）。
 *   2. 对象为 -1 时，取其所覆盖列中 attstattarget 的**最大值**。这主要是向后兼容：
 *      在扩展统计还没有自己目标之前就是这么做的。
 *   3. 若仍为负（对象与列都没设），用全局默认 default_statistics_target。
 *   最终断言目标在 [0, MAX_STATISTICS_TARGET] 内。
 * ============================================================================
 */
static int
statext_compute_stattarget(int stattarget, int nattrs, VacAttrStats **stats)
{
	int			i;

	/*
	 * If there's statistics target set for the statistics object, use it. It
	 * may be set to 0 which disables building of that statistic.
	 */
	if (stattarget >= 0)
		return stattarget;

	/*
	 * The target for the statistics object is set to -1, in which case we
	 * look at the maximum target set for any of the attributes the object is
	 * defined on.
	 */
	for (i = 0; i < nattrs; i++)
	{
		/* keep the maximum statistics target */
		if (stats[i]->attstattarget > stattarget)
			stattarget = stats[i]->attstattarget;
	}

	/*
	 * If the value is still negative (so neither the statistics object nor
	 * any of the columns have custom statistics target set), use the global
	 * default target.
	 */
	if (stattarget < 0)
		stattarget = default_statistics_target;

	/* As this point we should have a valid statistics target. */
	Assert((stattarget >= 0) && (stattarget <= MAX_STATISTICS_TARGET));

	return stattarget;
}

/*
 * ============================================================================
 * 【中文注释】statext_is_kind_built —— 判断某类统计是否已在数据元组中构建
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查给定的 pg_statistic_ext_data 元组中，指定统计种类对应的列是否非 NULL
 *   （即该统计是否已构建完成）。
 *
 * 参数：
 *   htup - pg_statistic_ext_data 元组。
 *   type - 统计种类（STATS_EXT_NDISTINCT / DEPENDENCIES / MCV / EXPRESSIONS）。
 *
 * 返回值：
 *   bool - 已构建（对应列非空）返回 true，否则 false。
 *
 * 设计思想：
 *   按种类映射到 stxdndistinct/stxddependencies/stxdmcv/stxdexpr 列号，用
 *   heap_attisnull() 判空。未知种类直接报错。
 * ============================================================================
 */
bool
statext_is_kind_built(HeapTuple htup, char type)
{
	AttrNumber	attnum;

	switch (type)
	{
		case STATS_EXT_NDISTINCT:
			attnum = Anum_pg_statistic_ext_data_stxdndistinct;
			break;

		case STATS_EXT_DEPENDENCIES:
			attnum = Anum_pg_statistic_ext_data_stxddependencies;
			break;

		case STATS_EXT_MCV:
			attnum = Anum_pg_statistic_ext_data_stxdmcv;
			break;

		case STATS_EXT_EXPRESSIONS:
			attnum = Anum_pg_statistic_ext_data_stxdexpr;
			break;

		default:
			elog(ERROR, "unexpected statistics type requested: %d", type);
	}

	return !heap_attisnull(htup, attnum, NULL);
}

/*
 * ============================================================================
 * 【中文注释】fetch_statentries_for_relation —— 取回关系的全部统计对象
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   扫描 pg_statistic_ext，返回该关系定义的所有扩展统计对象，每个对象解析为
 *   StatExtEntry 结构（含覆盖列、类型列表、目标、表达式等）。
 *
 * 参数：
 *   pg_statext - 已打开并加锁的 pg_statistic_ext 关系。
 *   rel        - 目标关系。
 *
 * 返回值：
 *   List* - StatExtEntry 列表。
 *
 * 设计思想：
 *   1. 按 stxrelid 索引做等值扫描。
 *   2. 每个元组解析：stxkeys（列号数组）、stxkind（统计种类数组）、stxstattarget、
 *      stxnamespace/stxname（用于报错信息）。
 *   3. 若 stxkind 含 'e'（表达式统计），解析 stxexpr 表达式数组（text[]，需反
 *      parse）；解析失败按 errsave 处理。
 *   4. 构造 StatExtEntry 时校验列数在 [1, STATS_MAX_DIMENSIONS] 内（用 errsave
 *      回调，解析失败可跳过）。
 * ============================================================================
 */
static List *
fetch_statentries_for_relation(Relation pg_statext, Relation rel)
{
	SysScanDesc scan;
	ScanKeyData skey;
	HeapTuple	htup;
	List	   *result = NIL;
	Oid			relid = RelationGetRelid(rel);

	/*
	 * Prepare to scan pg_statistic_ext for entries having stxrelid = this
	 * rel.
	 */
	ScanKeyInit(&skey,
				Anum_pg_statistic_ext_stxrelid,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(relid));

	scan = systable_beginscan(pg_statext, StatisticExtRelidIndexId, true,
							  NULL, 1, &skey);

	while (HeapTupleIsValid(htup = systable_getnext(scan)))
	{
		StatExtEntry *entry;
		Datum		datum;
		bool		isnull;
		int			i;
		ArrayType  *arr;
		char	   *enabled;
		Form_pg_statistic_ext staForm;
		List	   *exprs = NIL;

		entry = palloc0_object(StatExtEntry);
		staForm = (Form_pg_statistic_ext) GETSTRUCT(htup);
		entry->statOid = staForm->oid;
		entry->schema = get_namespace_name(staForm->stxnamespace);
		entry->name = pstrdup(NameStr(staForm->stxname));
		for (i = 0; i < staForm->stxkeys.dim1; i++)
		{
			entry->columns = bms_add_member(entry->columns,
											staForm->stxkeys.values[i]);
		}

		datum = SysCacheGetAttr(STATEXTOID, htup, Anum_pg_statistic_ext_stxstattarget, &isnull);
		entry->stattarget = isnull ? -1 : DatumGetInt16(datum);

		/* decode the stxkind char array into a list of chars */
		datum = SysCacheGetAttrNotNull(STATEXTOID, htup,
									   Anum_pg_statistic_ext_stxkind);
		arr = DatumGetArrayTypeP(datum);
		if (ARR_NDIM(arr) != 1 ||
			ARR_HASNULL(arr) ||
			ARR_ELEMTYPE(arr) != CHAROID)
			elog(ERROR, "stxkind is not a 1-D char array");
		enabled = (char *) ARR_DATA_PTR(arr);
		for (i = 0; i < ARR_DIMS(arr)[0]; i++)
		{
			Assert((enabled[i] == STATS_EXT_NDISTINCT) ||
				   (enabled[i] == STATS_EXT_DEPENDENCIES) ||
				   (enabled[i] == STATS_EXT_MCV) ||
				   (enabled[i] == STATS_EXT_EXPRESSIONS));
			entry->types = lappend_int(entry->types, (int) enabled[i]);
		}

		/* decode expression (if any) */
		datum = SysCacheGetAttr(STATEXTOID, htup,
								Anum_pg_statistic_ext_stxexprs, &isnull);

		if (!isnull)
		{
			char	   *exprsString;

			exprsString = TextDatumGetCString(datum);
			exprs = (List *) stringToNode(exprsString);

			pfree(exprsString);

			/* Expand virtual generated columns in the expressions */
			exprs = (List *) expand_generated_columns_in_expr((Node *) exprs, rel, 1);

			/*
			 * Run the expressions through eval_const_expressions. This is not
			 * just an optimization, but is necessary, because the planner
			 * will be comparing them to similarly-processed qual clauses, and
			 * may fail to detect valid matches without this.  We must not use
			 * canonicalize_qual, however, since these aren't qual
			 * expressions.
			 */
			exprs = (List *) eval_const_expressions(NULL, (Node *) exprs);

			/* May as well fix opfuncids too */
			fix_opfuncids((Node *) exprs);
		}

		entry->exprs = exprs;

		result = lappend(result, entry);
	}

	systable_endscan(scan);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】examine_attribute —— 单列预分析（构建 VacAttrStats）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判断一个表达式（通常是对列的直接引用）是否可分析；若可，为它创建并初始化
 *   一个 VacAttrStats 结构并返回；否则返回 NULL。
 *
 * 参数：
 *   expr - 待分析的表达式（这里实为列或表达式）。
 *
 * 返回值：
 *   VacAttrStats* - 初始化好的结构；不可分析时 NULL。
 *
 * 设计思想：
 *   1. 类型取自表达式树本身（attrtypid/attrtypmod/attrcollid），而非列的类型——
 *      因为 opclass 的存储类型（opckeytype）对我们不感兴趣。
 *   2. 从 syscache 取 Form_pg_type，填充 attrtype。
 *   3. stavalues 元素类型默认等于分析对象的类型，类型特定的 typanalyze 函数可按需
 *      修改。
 *   4. 调用类型特定的 typanalyze（缺省用 std_typanalyze）；若它表示不可分析
 *      （ok=false 或未设 compute_stats/minrows），则释放并返回 NULL。
 * ============================================================================
 */
static VacAttrStats *
examine_attribute(Node *expr)
{
	HeapTuple	typtuple;
	VacAttrStats *stats;
	int			i;
	bool		ok;

	/*
	 * Create the VacAttrStats struct.
	 */
	stats = palloc0_object(VacAttrStats);
	stats->attstattarget = -1;

	/*
	 * When analyzing an expression, believe the expression tree's type not
	 * the column datatype --- the latter might be the opckeytype storage type
	 * of the opclass, which is not interesting for our purposes.  (Note: if
	 * we did anything with non-expression statistics columns, we'd need to
	 * figure out where to get the correct type info from, but for now that's
	 * not a problem.)	It's not clear whether anyone will care about the
	 * typmod, but we store that too just in case.
	 */
	stats->attrtypid = exprType(expr);
	stats->attrtypmod = exprTypmod(expr);
	stats->attrcollid = exprCollation(expr);

	typtuple = SearchSysCacheCopy1(TYPEOID,
								   ObjectIdGetDatum(stats->attrtypid));
	if (!HeapTupleIsValid(typtuple))
		elog(ERROR, "cache lookup failed for type %u", stats->attrtypid);
	stats->attrtype = (Form_pg_type) GETSTRUCT(typtuple);

	/*
	 * We don't actually analyze individual attributes, so no need to set the
	 * memory context.
	 */
	stats->anl_context = NULL;
	stats->tupattnum = InvalidAttrNumber;

	/*
	 * The fields describing the stats->stavalues[n] element types default to
	 * the type of the data being analyzed, but the type-specific typanalyze
	 * function can change them if it wants to store something else.
	 */
	for (i = 0; i < STATISTIC_NUM_SLOTS; i++)
	{
		stats->statypid[i] = stats->attrtypid;
		stats->statyplen[i] = stats->attrtype->typlen;
		stats->statypbyval[i] = stats->attrtype->typbyval;
		stats->statypalign[i] = stats->attrtype->typalign;
	}

	/*
	 * Call the type-specific typanalyze function.  If none is specified, use
	 * std_typanalyze().
	 */
	if (OidIsValid(stats->attrtype->typanalyze))
		ok = DatumGetBool(OidFunctionCall1(stats->attrtype->typanalyze,
										   PointerGetDatum(stats)));
	else
		ok = std_typanalyze(stats);

	if (!ok || stats->compute_stats == NULL || stats->minrows <= 0)
	{
		heap_freetuple(typtuple);
		pfree(stats);
		return NULL;
	}

	return stats;
}

/*
 * ============================================================================
 * 【中文注释】examine_expression —— 单个表达式预分析（构建 VacAttrStats）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 examine_attribute() 类似，但用于统计对象里的**表达式**（如 lower(col)）：
 *   判断是否可分析并构建 VacAttrStats。
 *
 * 参数：
 *   expr       - 待分析的表达式（必非 NULL）。
 *   stattarget - 统计目标，用于填 VacAttrStats.attstattarget。
 *
 * 返回值：
 *   VacAttrStats* - 初始化好的结构；不可分析时 NULL。
 *
 * 设计思想：
 *   1. 表达式没有单独的统计目标设置，选用为扩展统计计算出的目标（比全局默认更
 *      合理）。
 *   2. 类型与 typmod 取表达式树的结果类型；排序规则取 exprCollation()——CREATE
 *      STATISTICS 不允许为表达式指定 collation，但表达式本身可写
 *      "(col COLLATE "en_US")"，此时 exprCollation() 会正确返回。
 *   3. 其余初始化（attrtype、anl_context、statypid 等）与 examine_attribute 相同，
 *      最后同样调用 typanalyze 判断可分析性。
 * ============================================================================
 */
static VacAttrStats *
examine_expression(Node *expr, int stattarget)
{
	HeapTuple	typtuple;
	VacAttrStats *stats;
	int			i;
	bool		ok;

	Assert(expr != NULL);

	/*
	 * Create the VacAttrStats struct.
	 */
	stats = palloc0_object(VacAttrStats);

	/*
	 * We can't have statistics target specified for the expression, so we
	 * could use either the default_statistics_target, or the target computed
	 * for the extended statistics. The second option seems more reasonable.
	 */
	stats->attstattarget = stattarget;

	/*
	 * When analyzing an expression, believe the expression tree's type.
	 */
	stats->attrtypid = exprType(expr);
	stats->attrtypmod = exprTypmod(expr);

	/*
	 * We don't allow collation to be specified in CREATE STATISTICS, so we
	 * have to use the collation specified for the expression. It's possible
	 * to specify the collation in the expression "(col COLLATE "en_US")" in
	 * which case exprCollation() does the right thing.
	 */
	stats->attrcollid = exprCollation(expr);

	typtuple = SearchSysCacheCopy1(TYPEOID,
								   ObjectIdGetDatum(stats->attrtypid));
	if (!HeapTupleIsValid(typtuple))
		elog(ERROR, "cache lookup failed for type %u", stats->attrtypid);

	stats->attrtype = (Form_pg_type) GETSTRUCT(typtuple);
	stats->anl_context = CurrentMemoryContext;	/* XXX should be using
												 * something else? */
	stats->tupattnum = InvalidAttrNumber;

	/*
	 * The fields describing the stats->stavalues[n] element types default to
	 * the type of the data being analyzed, but the type-specific typanalyze
	 * function can change them if it wants to store something else.
	 */
	for (i = 0; i < STATISTIC_NUM_SLOTS; i++)
	{
		stats->statypid[i] = stats->attrtypid;
		stats->statyplen[i] = stats->attrtype->typlen;
		stats->statypbyval[i] = stats->attrtype->typbyval;
		stats->statypalign[i] = stats->attrtype->typalign;
	}

	/*
	 * Call the type-specific typanalyze function.  If none is specified, use
	 * std_typanalyze().
	 */
	if (OidIsValid(stats->attrtype->typanalyze))
		ok = DatumGetBool(OidFunctionCall1(stats->attrtype->typanalyze,
										   PointerGetDatum(stats)));
	else
		ok = std_typanalyze(stats);

	if (!ok || stats->compute_stats == NULL || stats->minrows <= 0)
	{
		heap_freetuple(typtuple);
		pfree(stats);
		return NULL;
	}

	return stats;
}

/*
 * ============================================================================
 * 【中文注释】lookup_var_attr_stats —— 取出统计对象覆盖列的 VacAttrStats
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从大小为 nvacatts 的 vacatts 数组中，按 attrs 位图筛选出统计对象真正覆盖的
 *   那些列，返回一个新的 VacAttrStats 指针数组。表达式部分则逐一调用
 *   examine_expression() 构建。
 *
 * 参数：
 *   attrs     - 统计对象覆盖的列号位图。
 *   exprs     - 统计对象的表达式列表。
 *   nvacatts  - vacatts 数组长度。
 *   vacatts   - 本次 ANALYZE 得到的单列 VacAttrStats 数组。
 *
 * 返回值：
 *   VacAttrStats** - 按位图顺序排列的指针数组（含表达式统计的指针），长度
 *                    bms_num_members(attrs) + list_length(exprs)；
 *                    若缺失所需列的单列统计，返回 NULL（表示无法构建该对象）。
 *
 * 设计思想：
 *   若位图中的任一列没有对应的单列统计（说明本次未分析该列），说明我们没有构建
 *   扩展统计所需的全部数据，返回 NULL 让调用方跳过。位图成员本身即列号，直接用
 *   作下标；表达式统计追加在普通列之后。
 * ============================================================================
 */
static VacAttrStats **
lookup_var_attr_stats(Bitmapset *attrs, List *exprs,
					  int nvacatts, VacAttrStats **vacatts)
{
	int			i = 0;
	int			x = -1;
	int			natts;
	VacAttrStats **stats;
	ListCell   *lc;

	natts = bms_num_members(attrs) + list_length(exprs);

	stats = (VacAttrStats **) palloc(natts * sizeof(VacAttrStats *));

	/* lookup VacAttrStats info for the requested columns (same attnum) */
	while ((x = bms_next_member(attrs, x)) >= 0)
	{
		int			j;

		stats[i] = NULL;
		for (j = 0; j < nvacatts; j++)
		{
			if (x == vacatts[j]->tupattnum)
			{
				stats[i] = vacatts[j];
				break;
			}
		}

		if (!stats[i])
		{
			/*
			 * Looks like stats were not gathered for one of the columns
			 * required. We'll be unable to build the extended stats without
			 * this column.
			 */
			pfree(stats);
			return NULL;
		}

		i++;
	}

	/* also add info for expressions */
	foreach(lc, exprs)
	{
		Node	   *expr = (Node *) lfirst(lc);

		stats[i] = examine_attribute(expr);

		/*
		 * If the expression has been found as non-analyzable, give up.  We
		 * will not be able to build extended stats with it.
		 */
		if (stats[i] == NULL)
		{
			pfree(stats);
			return NULL;
		}

		/*
		 * XXX We need tuple descriptor later, and we just grab it from
		 * stats[0]->tupDesc (see e.g. statext_mcv_build). But as coded
		 * examine_attribute does not set that, so just grab it from the first
		 * vacatts element.
		 */
		stats[i]->tupDesc = vacatts[0]->tupDesc;

		i++;
	}

	return stats;
}

/*
 * ============================================================================
 * 【中文注释】statext_store —— 把计算好的扩展统计序列化并写入系统表
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把统计对象计算出的 ndistinct/dependencies/MCV/表达式统计序列化为 bytea，
 *   写入（或替换）pg_statistic_ext_data 中的一行。
 *
 * 参数：
 *   statOid     - 统计对象 OID。
 *   inh         - 是否针对继承树。
 *   ndistinct   - 多元去重统计（可为 NULL，表示该类型未计算）。
 *   dependencies- 函数依赖统计（可为 NULL）。
 *   mcv         - MCV 列表（可为 NULL）。
 *   exprs       - 表达式统计序列化结果（(Datum) 0 表示没有）。
 *   stats       - 各列 VacAttrStats（供 MCV 序列化读取类型信息）。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   1. 打开 pg_statistic_ext_data，构造 values/nulls 数组：固定列 stxoid、stxdinherit
 *      必填；各统计列按"是否有结果"决定填值还是 NULL。
 *   2. 用 RemoveStatisticsDataById() 删除旧元组，再插入新元组——比"先判断更新还是
 *      插入"更简单可靠。
 * ============================================================================
 */
static void
statext_store(Oid statOid, bool inh,
			  MVNDistinct *ndistinct, MVDependencies *dependencies,
			  MCVList *mcv, Datum exprs, VacAttrStats **stats)
{
	Relation	pg_stextdata;
	HeapTuple	stup;
	Datum		values[Natts_pg_statistic_ext_data];
	bool		nulls[Natts_pg_statistic_ext_data];

	pg_stextdata = table_open(StatisticExtDataRelationId, RowExclusiveLock);

	memset(nulls, true, sizeof(nulls));
	memset(values, 0, sizeof(values));

	/* basic info */
	values[Anum_pg_statistic_ext_data_stxoid - 1] = ObjectIdGetDatum(statOid);
	nulls[Anum_pg_statistic_ext_data_stxoid - 1] = false;

	values[Anum_pg_statistic_ext_data_stxdinherit - 1] = BoolGetDatum(inh);
	nulls[Anum_pg_statistic_ext_data_stxdinherit - 1] = false;

	/*
	 * Construct a new pg_statistic_ext_data tuple, replacing the calculated
	 * stats.
	 */
	if (ndistinct != NULL)
	{
		bytea	   *data = statext_ndistinct_serialize(ndistinct);

		nulls[Anum_pg_statistic_ext_data_stxdndistinct - 1] = (data == NULL);
		values[Anum_pg_statistic_ext_data_stxdndistinct - 1] = PointerGetDatum(data);
	}

	if (dependencies != NULL)
	{
		bytea	   *data = statext_dependencies_serialize(dependencies);

		nulls[Anum_pg_statistic_ext_data_stxddependencies - 1] = (data == NULL);
		values[Anum_pg_statistic_ext_data_stxddependencies - 1] = PointerGetDatum(data);
	}
	if (mcv != NULL)
	{
		bytea	   *data = statext_mcv_serialize(mcv, stats);

		nulls[Anum_pg_statistic_ext_data_stxdmcv - 1] = (data == NULL);
		values[Anum_pg_statistic_ext_data_stxdmcv - 1] = PointerGetDatum(data);
	}
	if (exprs != (Datum) 0)
	{
		nulls[Anum_pg_statistic_ext_data_stxdexpr - 1] = false;
		values[Anum_pg_statistic_ext_data_stxdexpr - 1] = exprs;
	}

	/*
	 * Delete the old tuple if it exists, and insert a new one. It's easier
	 * than trying to update or insert, based on various conditions.
	 */
	RemoveStatisticsDataById(statOid, inh);

	/* form and insert a new tuple */
	stup = heap_form_tuple(RelationGetDescr(pg_stextdata), values, nulls);
	CatalogTupleInsert(pg_stextdata, stup);

	heap_freetuple(stup);

	table_close(pg_stextdata, RowExclusiveLock);
}

/*
 * ============================================================================
 * 【中文注释】multi_sort_init —— 初始化多维排序支持结构
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   分配并初始化 MultiSortSupport，用于按"多列组合"对行排序。
 *
 * 参数：
 *   ndims - 排序维度数（列数），要求 >=2。
 *
 * 返回值：
 *   MultiSortSupport - 初始化好的结构（ndims 已设置，各维度 SortSupport 待
 *                      multi_sort_add_dimension() 填充）。
 * ============================================================================
 */
MultiSortSupport
multi_sort_init(int ndims)
{
	MultiSortSupport mss;

	Assert(ndims >= 2);

	mss = (MultiSortSupport) palloc0(offsetof(MultiSortSupportData, ssup)
									 + sizeof(SortSupportData) * ndims);

	mss->ndims = ndims;

	return mss;
}

/*
 * ============================================================================
 * 【中文注释】multi_sort_add_dimension —— 注册第 sortdim 维的排序支持
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   用给定的排序操作符与排序规则，为 MultiSortSupport 的第 sortdim 维准备
 *   SortSupport 信息。
 *
 * 参数：
 *   mss      - 多维排序支持结构。
 *   sortdim  - 维度下标。
 *   oper     - 排序操作符 OID。
 *   collation- 排序规则 OID。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   设置 SortSupport 的上下文/排序规则/NULL 排序位置（NULL 排后），然后调用
 *   PrepareSortSupportFromOrderingOp() 按操作符准备比较函数。
 * ============================================================================
 */
void
multi_sort_add_dimension(MultiSortSupport mss, int sortdim,
						 Oid oper, Oid collation)
{
	SortSupport ssup = &mss->ssup[sortdim];

	ssup->ssup_cxt = CurrentMemoryContext;
	ssup->ssup_collation = collation;
	ssup->ssup_nulls_first = false;

	PrepareSortSupportFromOrderingOp(oper, ssup);
}

/*
 * ============================================================================
 * 【中文注释】multi_sort_compare —— 按全部维度依次比较两个 SortItem
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   qsort 类回调：按维度顺序（0..ndims-1）依次比较两个 SortItem，第一个不等即
 *   返回结果；全部相等返回 0。
 *
 * 参数：
 *   a, b - 两个 SortItem 指针。
 *   arg  - MultiSortSupport 指针。
 *
 * 返回值：
 *   int - 比较结果（<0 / 0 / >0）。
 * ============================================================================
 */
int
multi_sort_compare(const void *a, const void *b, void *arg)
{
	MultiSortSupport mss = (MultiSortSupport) arg;
	const SortItem *ia = a;
	const SortItem *ib = b;
	int			i;

	for (i = 0; i < mss->ndims; i++)
	{
		int			compare;

		compare = ApplySortComparator(ia->values[i], ia->isnull[i],
									  ib->values[i], ib->isnull[i],
									  &mss->ssup[i]);

		if (compare != 0)
			return compare;
	}

	/* equal by default */
	return 0;
}

/*
 * ============================================================================
 * 【中文注释】multi_sort_compare_dim —— 只比较指定单一维度
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   仅用第 dim 维的值比较两个 SortItem。
 *
 * 参数：
 *   dim - 要比较的维度下标。
 *   a, b - 两个 SortItem。
 *   mss - 多维排序支持。
 *
 * 返回值：
 *   int - 第 dim 维的比较结果。
 * ============================================================================
 */
int
multi_sort_compare_dim(int dim, const SortItem *a, const SortItem *b,
					   MultiSortSupport mss)
{
	return ApplySortComparator(a->values[dim], a->isnull[dim],
							   b->values[dim], b->isnull[dim],
							   &mss->ssup[dim]);
}

/*
 * ============================================================================
 * 【中文注释】multi_sort_compare_dims —— 比较 start..end 这一区间的维度
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按维度 start..end（含端点）依次比较两个 SortItem，用于"忽略某些维度"的比较
 *   （例如函数依赖检测中只比较决定方各列）。
 *
 * 参数：
 *   start, end - 参与比较的维度区间。
 *   a, b       - 两个 SortItem。
 *   mss        - 多维排序支持。
 *
 * 返回值：
 *   int - 区间内第一个不等的维度的比较结果；全等返回 0。
 * ============================================================================
 */
int
multi_sort_compare_dims(int start, int end,
						const SortItem *a, const SortItem *b,
						MultiSortSupport mss)
{
	int			dim;

	for (dim = start; dim <= end; dim++)
	{
		int			r = ApplySortComparator(a->values[dim], a->isnull[dim],
											b->values[dim], b->isnull[dim],
											&mss->ssup[dim]);

		if (r != 0)
			return r;
	}

	return 0;
}

/*
 * ============================================================================
 * 【中文注释】compare_scalars_simple —— 简单标量比较器（qsort 包装）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 compare_datums_simple() 包装成 qsort 回调：a/b 是指向 Datum 的指针。
 *
 * 参数：
 *   a, b - 指向 Datum 的指针。
 *   arg  - SortSupport。
 *
 * 返回值：
 *   int - 两个标量的比较结果。
 * ============================================================================
 */
int
compare_scalars_simple(const void *a, const void *b, void *arg)
{
	return compare_datums_simple(*(const Datum *) a,
								 *(const Datum *) b,
								 (SortSupport) arg);
}

/*
 * ============================================================================
 * 【中文注释】compare_datums_simple —— 用 SortSupport 比较两个标量 Datum
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   直接用 ApplySortComparator 比较两个非 NULL 的标量 Datum（不涉及 isNull）。
 *
 * 参数：
 *   a, b - 待比较的 Datum。
 *   ssup - 排序支持。
 *
 * 返回值：
 *   int - 比较结果（<0 / 0 / >0）。
 * ============================================================================
 */
int
compare_datums_simple(Datum a, Datum b, SortSupport ssup)
{
	return ApplySortComparator(a, false, b, false, ssup);
}

/*
 * ============================================================================
 * 【中文注释】build_attnums_array —— 把位图转换成属性号数组
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把位图 attrs 中的每个成员转换成 AttrNumber 数组。位图用于扩展统计，其中
 *   普通列与表达式混合存放（表达式用负号区分），nexprs 指示表达式的个数。
 *
 * 参数：
 *   attrs    - 属性位图（成员为"偏移后的编号"，见下）。
 *   nexprs   - 表达式个数（普通列从 0 开始，表达式从 -nexprs 开始）。
 *   numattrs - 可选输出参数：返回数组长度。
 *
 * 返回值：
 *   AttrNumber* - 转换后的属性号数组。
 *
 * 设计思想：
 *   仅用于扩展统计，所有属性都是用户自定义列，无需按
 *   FirstLowInvalidHeapAttributeNumber 偏移（查询位图时也一致）。位图成员 j 对应
 *   属性号 (j - nexprs)。由于位图不能存负数，断言所有属性号合法且在上界内。
 * ============================================================================
 */
AttrNumber *
build_attnums_array(Bitmapset *attrs, int nexprs, int *numattrs)
{
	int			i,
				j;
	AttrNumber *attnums;
	int			num = bms_num_members(attrs);

	if (numattrs)
		*numattrs = num;

	/* build attnums from the bitmapset */
	attnums = palloc_array(AttrNumber, num);
	i = 0;
	j = -1;
	while ((j = bms_next_member(attrs, j)) >= 0)
	{
		int			attnum = (j - nexprs);

		/*
		 * Make sure the bitmap contains only user-defined attributes. As
		 * bitmaps can't contain negative values, this can be violated in two
		 * ways. Firstly, the bitmap might contain 0 as a member, and secondly
		 * the integer value might be larger than MaxAttrNumber.
		 */
		Assert(AttributeNumberIsValid(attnum));
		Assert(attnum <= MaxAttrNumber);
		Assert(attnum >= (-nexprs));

		attnums[i++] = (AttrNumber) attnum;

		/* protect against overflows */
		Assert(i <= num);
	}

	return attnums;
}

/*
 * ============================================================================
 * 【中文注释】build_sorted_items —— 从采样行构建排序好的 SortItem 数组
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 StatsBuildData 中的每行按指定列（attnums）的值打包成 SortItem（每行一个，
 *   含 numattrs 个 Datum 及其 NULL 标志），并按 mss 多维排序后返回。
 *
 * 参数：
 *   data     - 采样数据（含 exprvals/exprnulls 或按 attnums 取行内值）。
 *   nitems   - 输出参数：SortItem 个数（= 行数）。
 *   mss      - 多维排序支持。
 *   numattrs - 参与排序的列数。
 *   attnums  - 参与排序的列号数组（长度 numattrs）。
 *
 * 返回值：
 *   SortItem* - 排序后的数组；无行可处理时返回 NULL。
 *
 * 设计思想：
 *   1. 全部内存一次性分配（items + values + isnull 三块连续），调用方一次 pfree
 *      即可整体释放，减少分配开销。
 *   2. 每个 SortItem 的 values/isnull 指向各自维度的 Datum/布尔数组。
 *   3. 取值方式：若行数据来自 tuple 数组，则用 fetch 函数按列号取；否则直接用
 *      exprvals（表达式统计场景，Datum 已按行×列排布）。
 *   4. 用 qsort_interruptible() + multi_sort_compare() 排序。
 * ============================================================================
 */
SortItem *
build_sorted_items(StatsBuildData *data, int *nitems,
				   MultiSortSupport mss,
				   int numattrs, AttrNumber *attnums)
{
	int			i,
				j,
				nrows;
	int			nvalues = data->numrows * numattrs;
	Size		len;
	SortItem   *items;
	Datum	   *values;
	bool	   *isnull;
	char	   *ptr;
	int		   *typlen;

	/* Compute the total amount of memory we need (both items and values). */
	len = MAXALIGN(data->numrows * sizeof(SortItem)) +
		nvalues * (sizeof(Datum) + sizeof(bool));

	/* Allocate the memory and split it into the pieces. */
	ptr = palloc0(len);

	/* items to sort */
	items = (SortItem *) ptr;
	/* MAXALIGN ensures that the following Datums are suitably aligned */
	ptr += MAXALIGN(data->numrows * sizeof(SortItem));

	/* values and null flags */
	values = (Datum *) ptr;
	ptr += nvalues * sizeof(Datum);

	isnull = (bool *) ptr;
	ptr += nvalues * sizeof(bool);

	/* make sure we consumed the whole buffer exactly */
	Assert((ptr - (char *) items) == len);

	/* fix the pointers to Datum and bool arrays */
	nrows = 0;
	for (i = 0; i < data->numrows; i++)
	{
		items[nrows].values = &values[nrows * numattrs];
		items[nrows].isnull = &isnull[nrows * numattrs];

		nrows++;
	}

	/* build a local cache of typlen for all attributes */
	typlen = palloc_array(int, data->nattnums);
	for (i = 0; i < data->nattnums; i++)
		typlen[i] = get_typlen(data->stats[i]->attrtypid);

	nrows = 0;
	for (i = 0; i < data->numrows; i++)
	{
		bool		toowide = false;

		/* load the values/null flags from sample rows */
		for (j = 0; j < numattrs; j++)
		{
			Datum		value;
			bool		isnull;
			int			attlen;
			AttrNumber	attnum = attnums[j];

			int			idx;

			/* match attnum to the pre-calculated data */
			for (idx = 0; idx < data->nattnums; idx++)
			{
				if (attnum == data->attnums[idx])
					break;
			}

			Assert(idx < data->nattnums);

			value = data->values[idx][i];
			isnull = data->nulls[idx][i];
			attlen = typlen[idx];

			/*
			 * If this is a varlena value, check if it's too wide and if yes
			 * then skip the whole item. Otherwise detoast the value.
			 *
			 * XXX It may happen that we've already detoasted some preceding
			 * values for the current item. We don't bother to cleanup those
			 * on the assumption that those are small (below WIDTH_THRESHOLD)
			 * and will be discarded at the end of analyze.
			 */
			if ((!isnull) && (attlen == -1))
			{
				if (toast_raw_datum_size(value) > WIDTH_THRESHOLD)
				{
					toowide = true;
					break;
				}

				value = PointerGetDatum(PG_DETOAST_DATUM(value));
			}

			items[nrows].values[j] = value;
			items[nrows].isnull[j] = isnull;
		}

		if (toowide)
			continue;

		nrows++;
	}

	/* store the actual number of items (ignoring the too-wide ones) */
	*nitems = nrows;

	/* all items were too wide */
	if (nrows == 0)
	{
		/* everything is allocated as a single chunk */
		pfree(items);
		return NULL;
	}

	/* do the sort, using the multi-sort */
	qsort_interruptible(items, nrows, sizeof(SortItem),
						multi_sort_compare, mss);

	return items;
}

/*
 * ============================================================================
 * 【中文注释】has_stats_of_kind —— 列表中是否存在指定种类的统计
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历统计对象信息列表，检查是否存在 kind 等于 requiredkind 的对象。
 *
 * 参数：
 *   stats        - StatisticExtInfo 列表。
 *   requiredkind - 要求的统计种类（STATS_EXT_*）。
 *
 * 返回值：
 *   bool - 存在返回 true，否则 false。
 * ============================================================================
 */
bool
has_stats_of_kind(List *stats, char requiredkind)
{
	ListCell   *l;

	foreach(l, stats)
	{
		StatisticExtInfo *stat = (StatisticExtInfo *) lfirst(l);

		if (stat->kind == requiredkind)
			return true;
	}

	return false;
}

/*
 * ============================================================================
 * 【中文注释】stat_find_expression —— 在统计对象表达式列表中查找表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在统计对象的表达式列表中查找与给定表达式结构相等的项。
 *
 * 参数：
 *   stat - 统计对象信息（含 exprs 列表）。
 *   expr - 待查找的表达式。
 *
 * 返回值：
 *   int - 表达式在列表中的下标；未找到返回 -1。
 *
 * 设计思想：
 *   逐个用 equal()（结构相等比较）匹配。
 * ============================================================================
 */
static int
stat_find_expression(StatisticExtInfo *stat, Node *expr)
{
	ListCell   *lc;
	int			idx;

	idx = 0;
	foreach(lc, stat->exprs)
	{
		Node	   *stat_expr = (Node *) lfirst(lc);

		if (equal(stat_expr, expr))
			return idx;
		idx++;
	}

	/* Expression not found */
	return -1;
}

/*
 * ============================================================================
 * 【中文注释】stat_covers_expressions —— 统计对象是否覆盖全部表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判断统计对象是否定义了列表中所有的表达式（即每个表达式都能在对象中找到）。
 *
 * 参数：
 *   stat     - 统计对象信息。
 *   exprs    - 待检查的表达式列表。
 *   expr_idxs- 可选输出参数：收集所有表达式在对象中的下标位图。
 *
 * 返回值：
 *   bool - 全部覆盖返回 true，否则 false。
 *
 * 设计思想：
 *   逐个调用 stat_find_expression() 匹配；任一个找不到即返回 false。
 * ============================================================================
 */
static bool
stat_covers_expressions(StatisticExtInfo *stat, List *exprs,
						Bitmapset **expr_idxs)
{
	ListCell   *lc;

	foreach(lc, exprs)
	{
		Node	   *expr = (Node *) lfirst(lc);
		int			expr_idx;

		expr_idx = stat_find_expression(stat, expr);
		if (expr_idx == -1)
			return false;

		if (expr_idxs != NULL)
			*expr_idxs = bms_add_member(*expr_idxs, expr_idx);
	}

	/* If we reach here, all expressions are covered */
	return true;
}

/*
 * ============================================================================
 * 【中文注释】choose_best_statistics —— 挑选最适合当前子句的统计对象
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在给定列表中查找具有 requiredkind 种类、且其 keys（列）能匹配至少两个给定
 *   属性/表达式的统计对象，返回其中"最合适"的一个；找不到返回 NULL。
 *
 * 参数：
 *   stats         - 候选统计对象列表。
 *   requiredkind  - 需要的统计种类。
 *   inh           - 是否针对继承树（用于加载统计）。
 *   clause_attnums- 每个子句覆盖的属性位图数组；NULL 元素表示该子句不兼容或已被
 *                   估计。
 *   clause_exprs  - 每个子句匹配到的表达式列表。
 *   nclauses      - 子句个数。
 *
 * 返回值：
 *   StatisticExtInfo* - 选中的统计对象；无匹配时 NULL。
 *
 * 设计思想：
 *   选择准则很简单：
 *   目标1【最大化】：统计对象在"被覆盖且尚未估计"的子句中引用的属性数最多；
 *   目标2【最小化】：平局时选 keys（列+表达式）总数更少的对象。
 *   实现为贪心扫描：计算每个对象匹配的子句属性并集大小，按上述两级目标比较。
 *   XXX 若多个对象两项都打平，则选中的是列表中先出现的那个；未来可能需要更多
 *   平局裁决规则。
 * ============================================================================
 */
StatisticExtInfo *
choose_best_statistics(List *stats, char requiredkind, bool inh,
					   Bitmapset **clause_attnums, List **clause_exprs,
					   int nclauses)
{
	ListCell   *lc;
	StatisticExtInfo *best_match = NULL;
	int			best_num_matched = 2;	/* goal #1: maximize */
	int			best_match_keys = (STATS_MAX_DIMENSIONS + 1);	/* goal #2: minimize */

	foreach(lc, stats)
	{
		int			i;
		StatisticExtInfo *info = (StatisticExtInfo *) lfirst(lc);
		Bitmapset  *matched_attnums = NULL;
		Bitmapset  *matched_exprs = NULL;
		int			num_matched;
		int			numkeys;

		/* skip statistics that are not of the correct type */
		if (info->kind != requiredkind)
			continue;

		/* skip statistics with mismatching inheritance flag */
		if (info->inherit != inh)
			continue;

		/*
		 * Collect attributes and expressions in remaining (unestimated)
		 * clauses fully covered by this statistic object.
		 *
		 * We know already estimated clauses have both clause_attnums and
		 * clause_exprs set to NULL. We leave the pointers NULL if already
		 * estimated, or we reset them to NULL after estimating the clause.
		 */
		for (i = 0; i < nclauses; i++)
		{
			Bitmapset  *expr_idxs = NULL;

			/* ignore incompatible/estimated clauses */
			if (!clause_attnums[i] && !clause_exprs[i])
				continue;

			/* ignore clauses that are not covered by this object */
			if (!bms_is_subset(clause_attnums[i], info->keys) ||
				!stat_covers_expressions(info, clause_exprs[i], &expr_idxs))
				continue;

			/* record attnums and indexes of expressions covered */
			matched_attnums = bms_add_members(matched_attnums, clause_attnums[i]);
			matched_exprs = bms_add_members(matched_exprs, expr_idxs);
		}

		num_matched = bms_num_members(matched_attnums) + bms_num_members(matched_exprs);

		bms_free(matched_attnums);
		bms_free(matched_exprs);

		/*
		 * save the actual number of keys in the stats so that we can choose
		 * the narrowest stats with the most matching keys.
		 */
		numkeys = bms_num_members(info->keys) + list_length(info->exprs);

		/*
		 * Use this object when it increases the number of matched attributes
		 * and expressions or when it matches the same number of attributes
		 * and expressions but these stats have fewer keys than any previous
		 * match.
		 */
		if (num_matched > best_num_matched ||
			(num_matched == best_num_matched && numkeys < best_match_keys))
		{
			best_match = info;
			best_num_matched = num_matched;
			best_match_keys = numkeys;
		}
	}

	return best_match;
}

/*
 * ============================================================================
 * 【中文注释】statext_is_compatible_clause_internal —— 判断子句是否适用于 MCV（内部）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   递归检查一个子句是否可用于 MCV 列表的选择性估算。兼容的子句必须是"由受支持
 *   的子句组合而成"，这些子句由 Var 或子表达式（能精确匹配统计对象中表达式的
 *   表达式）构成。函数同时提取出需要与统计匹配的所有子表达式。
 *
 * 参数：
 *   clause - 待检查的（子）子句（裸子句，不是 RestrictInfo）。
 *   relid  - 子句中所有 Var 必须属于的关系。
 *   attnums- in/out：收集所有出现 Var 的属性号（不偏移，因此不支持系统列）。
 *   exprs  - in/out：收集子句树中的基本子表达式。
 *   leakproof - in/out：记录子句树是否为防泄漏的；初始应为 true，若某个 OpExpr
 *               使用非防泄漏的操作符函数则置 false。
 *
 * 返回值：
 *   bool - 遇到确定无法处理的子句返回 false；返回 true 时可继续用 *exprs 与统计
 *          匹配。
 *
 * 设计思想（支持的子句类型）：
 *   (a) OpExpr：(Var/Expr op Const) 或 (Const op Var/Expr)，op 为 =、<、>、>=、<=；
 *   (b) (Var/Expr IS [NOT] NULL)；
 *   (c) AND / OR / NOT 组合（递归展开，NOT 反转 leakproof 语义并调换等值处理）；
 *   (d) ScalarArrayOpExpr：(Var/Expr op ANY (Const)) 或 (Var/Expr op ALL (Const))，
 *       数组展开后要求元素为等值比较。
 *   其余类型一律当作"裸表达式"加入 exprs，交由上层决定是否匹配（对简单 Var 要
 *   校验其属于 relid 且非系统列/整行）。
 *   （未来可能扩展支持更复杂的情况，例如 (Var op Var)。）
 * ============================================================================
 */
static bool
statext_is_compatible_clause_internal(PlannerInfo *root, Node *clause,
									  Index relid, Bitmapset **attnums,
									  List **exprs, bool *leakproof)
{
	/* Look inside any binary-compatible relabeling (as in examine_variable) */
	if (IsA(clause, RelabelType))
		clause = (Node *) ((RelabelType *) clause)->arg;

	/* plain Var references (boolean Vars or recursive checks) */
	if (IsA(clause, Var))
	{
		Var		   *var = (Var *) clause;

		/* Ensure var is from the correct relation */
		if (var->varno != relid)
			return false;

		/* we also better ensure the Var is from the current level */
		if (var->varlevelsup > 0)
			return false;

		/*
		 * Also reject system attributes and whole-row Vars (we don't allow
		 * stats on those).
		 */
		if (!AttrNumberIsForUserDefinedAttr(var->varattno))
			return false;

		/* OK, record the attnum for later permissions checks. */
		*attnums = bms_add_member(*attnums, var->varattno);

		return true;
	}

	/* (Var/Expr op Const) or (Const op Var/Expr) */
	if (is_opclause(clause))
	{
		OpExpr	   *expr = (OpExpr *) clause;
		Node	   *clause_expr;

		/* Only expressions with two arguments are considered compatible. */
		if (list_length(expr->args) != 2)
			return false;

		/* Check if the expression has the right shape */
		if (!examine_opclause_args(expr->args, &clause_expr, NULL, NULL))
			return false;

		/*
		 * If it's not one of the supported operators ("=", "<", ">", etc.),
		 * just ignore the clause, as it's not compatible with MCV lists.
		 *
		 * This uses the function for estimating selectivity, not the operator
		 * directly (a bit awkward, but well ...).
		 */
		switch (get_oprrest(expr->opno))
		{
			case F_EQSEL:
			case F_NEQSEL:
			case F_SCALARLTSEL:
			case F_SCALARLESEL:
			case F_SCALARGTSEL:
			case F_SCALARGESEL:
				/* supported, will continue with inspection of the Var/Expr */
				break;

			default:
				/* other estimators are considered unknown/unsupported */
				return false;
		}

		/* Check if the operator is leakproof */
		if (*leakproof)
			*leakproof = get_func_leakproof(get_opcode(expr->opno));

		/* Check (Var op Const) or (Const op Var) clauses by recursing. */
		if (IsA(clause_expr, Var))
			return statext_is_compatible_clause_internal(root, clause_expr,
														 relid, attnums,
														 exprs, leakproof);

		/* Otherwise we have (Expr op Const) or (Const op Expr). */
		*exprs = lappend(*exprs, clause_expr);
		return true;
	}

	/* Var/Expr IN Array */
	if (IsA(clause, ScalarArrayOpExpr))
	{
		ScalarArrayOpExpr *expr = (ScalarArrayOpExpr *) clause;
		Node	   *clause_expr;
		bool		expronleft;

		/* Only expressions with two arguments are considered compatible. */
		if (list_length(expr->args) != 2)
			return false;

		/* Check if the expression has the right shape (one Var, one Const) */
		if (!examine_opclause_args(expr->args, &clause_expr, NULL, &expronleft))
			return false;

		/* We only support Var on left, Const on right */
		if (!expronleft)
			return false;

		/*
		 * If it's not one of the supported operators ("=", "<", ">", etc.),
		 * just ignore the clause, as it's not compatible with MCV lists.
		 *
		 * This uses the function for estimating selectivity, not the operator
		 * directly (a bit awkward, but well ...).
		 */
		switch (get_oprrest(expr->opno))
		{
			case F_EQSEL:
			case F_NEQSEL:
			case F_SCALARLTSEL:
			case F_SCALARLESEL:
			case F_SCALARGTSEL:
			case F_SCALARGESEL:
				/* supported, will continue with inspection of the Var/Expr */
				break;

			default:
				/* other estimators are considered unknown/unsupported */
				return false;
		}

		/* Check if the operator is leakproof */
		if (*leakproof)
			*leakproof = get_func_leakproof(get_opcode(expr->opno));

		/* Check Var IN Array clauses by recursing. */
		if (IsA(clause_expr, Var))
			return statext_is_compatible_clause_internal(root, clause_expr,
														 relid, attnums,
														 exprs, leakproof);

		/* Otherwise we have Expr IN Array. */
		*exprs = lappend(*exprs, clause_expr);
		return true;
	}

	/* AND/OR/NOT clause */
	if (is_andclause(clause) ||
		is_orclause(clause) ||
		is_notclause(clause))
	{
		/*
		 * AND/OR/NOT-clauses are supported if all sub-clauses are supported
		 *
		 * Perhaps we could improve this by handling mixed cases, when some of
		 * the clauses are supported and some are not. Selectivity for the
		 * supported subclauses would be computed using extended statistics,
		 * and the remaining clauses would be estimated using the traditional
		 * algorithm (product of selectivities).
		 *
		 * It however seems overly complex, and in a way we already do that
		 * because if we reject the whole clause as unsupported here, it will
		 * be eventually passed to clauselist_selectivity() which does exactly
		 * this (split into supported/unsupported clauses etc).
		 */
		BoolExpr   *expr = (BoolExpr *) clause;
		ListCell   *lc;

		foreach(lc, expr->args)
		{
			/*
			 * If we find an incompatible clause in the arguments, treat the
			 * whole clause as incompatible.
			 */
			if (!statext_is_compatible_clause_internal(root,
													   (Node *) lfirst(lc),
													   relid, attnums, exprs,
													   leakproof))
				return false;
		}

		return true;
	}

	/* Var/Expr IS NULL */
	if (IsA(clause, NullTest))
	{
		NullTest   *nt = (NullTest *) clause;

		/* Check Var IS NULL clauses by recursing. */
		if (IsA(nt->arg, Var))
			return statext_is_compatible_clause_internal(root,
														 (Node *) (nt->arg),
														 relid, attnums,
														 exprs, leakproof);

		/* Otherwise we have Expr IS NULL. */
		*exprs = lappend(*exprs, nt->arg);
		return true;
	}

	/*
	 * Treat any other expressions as bare expressions to be matched against
	 * expressions in statistics objects.
	 */
	*exprs = lappend(*exprs, clause);
	return true;
}

/*
 * ============================================================================
 * 【中文注释】statext_is_compatible_clause —— 判断子句是否适用于 MCV（外层封装）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 statext_is_compatible_clause_internal() 规则相同，但这一层处理 RestrictInfo
 *   外包装，并做权限检查，确认允许查看子句提到的所有 Var 的列。
 *
 * 参数：
 *   clause - 待检查的子句（RestrictInfo 形式）。
 *   relid  - 子句中所有 Var 必须属于的关系。
 *   attnums- in/out：收集所有出现 Var 的属性号。
 *   exprs  - in/out：收集子句树中的基本子表达式。
 *
 * 返回值：
 *   bool - 遇到无法处理的子句返回 false；返回 true 时可继续匹配。
 *
 * 设计思想：
 *   1. 拆开 RestrictInfo 取 clause，剥离伪常量。
 *   2. 委托内部函数完成结构兼容性判断。
 *   3. 若收集到了 attnums/exprs，用 pull_varattnos() 从这些节点再收集属性号，并
 *      调用 all_rows_selectable() 校验用户对这些列有 SELECT 权限（防信息泄漏）。
 * ============================================================================
 */
static bool
statext_is_compatible_clause(PlannerInfo *root, Node *clause, Index relid,
							 Bitmapset **attnums, List **exprs)
{
	RestrictInfo *rinfo;
	int			clause_relid;
	bool		leakproof;

	/*
	 * Special-case handling for bare BoolExpr AND clauses, because the
	 * restrictinfo machinery doesn't build RestrictInfos on top of AND
	 * clauses.
	 */
	if (is_andclause(clause))
	{
		BoolExpr   *expr = (BoolExpr *) clause;
		ListCell   *lc;

		/*
		 * Check that each sub-clause is compatible.  We expect these to be
		 * RestrictInfos.
		 */
		foreach(lc, expr->args)
		{
			if (!statext_is_compatible_clause(root, (Node *) lfirst(lc),
											  relid, attnums, exprs))
				return false;
		}

		return true;
	}

	/* Otherwise it must be a RestrictInfo. */
	if (!IsA(clause, RestrictInfo))
		return false;
	rinfo = (RestrictInfo *) clause;

	/* Pseudoconstants are not really interesting here. */
	if (rinfo->pseudoconstant)
		return false;

	/* Clauses referencing other varnos are incompatible. */
	if (!bms_get_singleton_member(rinfo->clause_relids, &clause_relid) ||
		clause_relid != relid)
		return false;

	/*
	 * Check the clause, determine what attributes it references, and whether
	 * it includes any non-leakproof operators.
	 */
	leakproof = true;
	if (!statext_is_compatible_clause_internal(root, (Node *) rinfo->clause,
											   relid, attnums, exprs,
											   &leakproof))
		return false;

	/*
	 * If the clause includes any non-leakproof operators, check that the user
	 * has permission to read all required attributes, otherwise the operators
	 * might reveal values from the MCV list that the user doesn't have
	 * permission to see.  We require all rows to be selectable --- there must
	 * be no securityQuals from security barrier views or RLS policies.  See
	 * similar code in examine_variable(), examine_simple_variable(), and
	 * statistic_proc_security_check().
	 *
	 * Note that for an inheritance child, the permission checks are performed
	 * on the inheritance root parent, and whole-table select privilege on the
	 * parent doesn't guarantee that the user could read all columns of the
	 * child. Therefore we must check all referenced columns.
	 */
	if (!leakproof)
	{
		Bitmapset  *clause_attnums;

		/*
		 * We have to check per-column privileges.  *attnums has the attnums
		 * for individual Vars we saw, but there may also be Vars within
		 * subexpressions in *exprs.  We can use pull_varattnos() to extract
		 * those, but there's an impedance mismatch: attnums returned by
		 * pull_varattnos() are offset by FirstLowInvalidHeapAttributeNumber,
		 * while attnums within *attnums aren't.  Convert *attnums to the
		 * offset style so we can combine the results.
		 */
		clause_attnums = bms_offset_members(*attnums,
											0 - FirstLowInvalidHeapAttributeNumber);
		/* Now merge attnums from *exprs into clause_attnums */
		if (*exprs != NIL)
			pull_varattnos((Node *) *exprs, relid, &clause_attnums);

		/* Must have permission to read all rows from these columns */
		if (!all_rows_selectable(root, relid, clause_attnums))
			return false;
	}

	/* If we reach here, the clause is OK */
	return true;
}

/*
 * ============================================================================
 * 【中文注释】statext_mcv_clauselist_selectivity —— 用 MCV 统计估计子句列表选择性
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   使用表上可用的多列 MCV 统计来估计子句列表的选择性。若存在多个可用统计对象，
 *   采用贪心策略：每轮选择"从子句中提取并被其覆盖的属性数最多"的统计对象进行
 *   估算，然后对剩余子句重复，直到没有可用的统计。
 *
 * 参数：
 *   root / varRelid / jointype / sjinfo / rel - 规划上下文。
 *   estimatedclauses - in/out 位图：对本函数估算过的子句（按 0 基下标）置位，
 *                      同时跳过已有位的子句。
 *   is_or - 子句是否为 OR 连接。
 *
 * 返回值：
 *   Selectivity - 估计的选择性。
 *
 * 设计思想（MCV 外推问题）：
 *   使用 MCV 列表的难点在于把估计外推到 MCV 未覆盖的数据。为此不仅计算"MCV
 *   选择性"（匹配子句的 MCV 项频率之和），还计算：
 *   - simple 选择性：不使用扩展统计、假设列/子句独立时得到的选择性；
 *   - base 选择性：与 simple 类似，但用扩展统计计算——把匹配 MCV 项的
 *     base_frequency（构建时算好并存下）累加；
 *   - total 选择性：整个 MCV 列表覆盖的选择性。
 *   三者交给 mcv_combine_selectivities() 合成，兼顾单列统计与多列 MCV 统计。
 * ============================================================================
 */
static Selectivity
statext_mcv_clauselist_selectivity(PlannerInfo *root, List *clauses, int varRelid,
								   JoinType jointype, SpecialJoinInfo *sjinfo,
								   RelOptInfo *rel, Bitmapset **estimatedclauses,
								   bool is_or)
{
	ListCell   *l;
	Bitmapset **list_attnums;	/* attnums extracted from the clause */
	List	  **list_exprs;		/* expressions matched to any statistic */
	int			listidx;
	Selectivity sel = (is_or) ? 0.0 : 1.0;
	RangeTblEntry *rte = planner_rt_fetch(rel->relid, root);

	/* check if there's any stats that might be useful for us. */
	if (!has_stats_of_kind(rel->statlist, STATS_EXT_MCV))
		return sel;

	list_attnums = palloc_array(Bitmapset *, list_length(clauses));

	/* expressions extracted from complex expressions */
	list_exprs = palloc_array(List *, list_length(clauses));

	/*
	 * Pre-process the clauses list to extract the attnums and expressions
	 * seen in each item.  We need to determine if there are any clauses which
	 * will be useful for selectivity estimations with extended stats.  Along
	 * the way we'll record all of the attnums and expressions for each clause
	 * in lists which we'll reference later so we don't need to repeat the
	 * same work again.
	 *
	 * We also skip clauses that we already estimated using different types of
	 * statistics (we treat them as incompatible).
	 */
	listidx = 0;
	foreach(l, clauses)
	{
		Node	   *clause = (Node *) lfirst(l);
		Bitmapset  *attnums = NULL;
		List	   *exprs = NIL;

		if (!bms_is_member(listidx, *estimatedclauses) &&
			statext_is_compatible_clause(root, clause, rel->relid, &attnums, &exprs))
		{
			list_attnums[listidx] = attnums;
			list_exprs[listidx] = exprs;
		}
		else
		{
			list_attnums[listidx] = NULL;
			list_exprs[listidx] = NIL;
		}

		listidx++;
	}

	/* apply as many extended statistics as possible */
	while (true)
	{
		StatisticExtInfo *stat;
		List	   *stat_clauses;
		Bitmapset  *simple_clauses;

		/* find the best suited statistics object for these attnums */
		stat = choose_best_statistics(rel->statlist, STATS_EXT_MCV, rte->inh,
									  list_attnums, list_exprs,
									  list_length(clauses));

		/*
		 * if no (additional) matching stats could be found then we've nothing
		 * to do
		 */
		if (!stat)
			break;

		/* Ensure choose_best_statistics produced an expected stats type. */
		Assert(stat->kind == STATS_EXT_MCV);

		/* now filter the clauses to be estimated using the selected MCV */
		stat_clauses = NIL;

		/* record which clauses are simple (single column or expression) */
		simple_clauses = NULL;

		listidx = -1;
		foreach(l, clauses)
		{
			/* Increment the index before we decide if to skip the clause. */
			listidx++;

			/*
			 * Ignore clauses from which we did not extract any attnums or
			 * expressions (this needs to be consistent with what we do in
			 * choose_best_statistics).
			 *
			 * This also eliminates already estimated clauses - both those
			 * estimated before and during applying extended statistics.
			 *
			 * XXX This check is needed because both bms_is_subset and
			 * stat_covers_expressions return true for empty attnums and
			 * expressions.
			 */
			if (!list_attnums[listidx] && !list_exprs[listidx])
				continue;

			/*
			 * The clause was not estimated yet, and we've extracted either
			 * attnums or expressions from it. Ignore it if it's not fully
			 * covered by the chosen statistics object.
			 *
			 * We need to check both attributes and expressions, and reject if
			 * either is not covered.
			 */
			if (!bms_is_subset(list_attnums[listidx], stat->keys) ||
				!stat_covers_expressions(stat, list_exprs[listidx], NULL))
				continue;

			/*
			 * Now we know the clause is compatible (we have either attnums or
			 * expressions extracted from it), and was not estimated yet.
			 */

			/* record simple clauses (single column or expression) */
			if ((list_attnums[listidx] == NULL &&
				 list_length(list_exprs[listidx]) == 1) ||
				(list_exprs[listidx] == NIL &&
				 bms_membership(list_attnums[listidx]) == BMS_SINGLETON))
				simple_clauses = bms_add_member(simple_clauses,
												list_length(stat_clauses));

			/* add clause to list and mark it as estimated */
			stat_clauses = lappend(stat_clauses, (Node *) lfirst(l));
			*estimatedclauses = bms_add_member(*estimatedclauses, listidx);

			/*
			 * Reset the pointers, so that choose_best_statistics knows this
			 * clause was estimated and does not consider it again.
			 */
			bms_free(list_attnums[listidx]);
			list_attnums[listidx] = NULL;

			list_free(list_exprs[listidx]);
			list_exprs[listidx] = NULL;
		}

		if (is_or)
		{
			bool	   *or_matches = NULL;
			Selectivity simple_or_sel = 0.0,
						stat_sel = 0.0;
			MCVList    *mcv_list;

			/* Load the MCV list stored in the statistics object */
			mcv_list = statext_mcv_load(stat->statOid, rte->inh);

			/*
			 * Compute the selectivity of the ORed list of clauses covered by
			 * this statistics object by estimating each in turn and combining
			 * them using the formula P(A OR B) = P(A) + P(B) - P(A AND B).
			 * This allows us to use the multivariate MCV stats to better
			 * estimate the individual terms and their overlap.
			 *
			 * Each time we iterate this formula, the clause "A" above is
			 * equal to all the clauses processed so far, combined with "OR".
			 */
			listidx = 0;
			foreach(l, stat_clauses)
			{
				Node	   *clause = (Node *) lfirst(l);
				Selectivity simple_sel,
							overlap_simple_sel,
							mcv_sel,
							mcv_basesel,
							overlap_mcvsel,
							overlap_basesel,
							mcv_totalsel,
							clause_sel,
							overlap_sel;

				/*
				 * "Simple" selectivity of the next clause and its overlap
				 * with any of the previous clauses.  These are our initial
				 * estimates of P(B) and P(A AND B), assuming independence of
				 * columns/clauses.
				 */
				simple_sel = clause_selectivity_ext(root, clause, varRelid,
													jointype, sjinfo, false);

				overlap_simple_sel = simple_or_sel * simple_sel;

				/*
				 * New "simple" selectivity of all clauses seen so far,
				 * assuming independence.
				 */
				simple_or_sel += simple_sel - overlap_simple_sel;
				CLAMP_PROBABILITY(simple_or_sel);

				/*
				 * Multi-column estimate of this clause using MCV statistics,
				 * along with base and total selectivities, and corresponding
				 * selectivities for the overlap term P(A AND B).
				 */
				mcv_sel = mcv_clause_selectivity_or(root, stat, mcv_list,
													clause, &or_matches,
													&mcv_basesel,
													&overlap_mcvsel,
													&overlap_basesel,
													&mcv_totalsel);

				/*
				 * Combine the simple and multi-column estimates.
				 *
				 * If this clause is a simple single-column clause, then we
				 * just use the simple selectivity estimate for it, since the
				 * multi-column statistics are unlikely to improve on that
				 * (and in fact could make it worse).  For the overlap, we
				 * always make use of the multi-column statistics.
				 */
				if (bms_is_member(listidx, simple_clauses))
					clause_sel = simple_sel;
				else
					clause_sel = mcv_combine_selectivities(simple_sel,
														   mcv_sel,
														   mcv_basesel,
														   mcv_totalsel);

				overlap_sel = mcv_combine_selectivities(overlap_simple_sel,
														overlap_mcvsel,
														overlap_basesel,
														mcv_totalsel);

				/* Factor these into the result for this statistics object */
				stat_sel += clause_sel - overlap_sel;
				CLAMP_PROBABILITY(stat_sel);

				listidx++;
			}

			/*
			 * Factor the result for this statistics object into the overall
			 * result.  We treat the results from each separate statistics
			 * object as independent of one another.
			 */
			sel = sel + stat_sel - sel * stat_sel;
		}
		else					/* Implicitly-ANDed list of clauses */
		{
			Selectivity simple_sel,
						mcv_sel,
						mcv_basesel,
						mcv_totalsel,
						stat_sel;

			/*
			 * "Simple" selectivity, i.e. without any extended statistics,
			 * essentially assuming independence of the columns/clauses.
			 */
			simple_sel = clauselist_selectivity_ext(root, stat_clauses,
													varRelid, jointype,
													sjinfo, false);

			/*
			 * Multi-column estimate using MCV statistics, along with base and
			 * total selectivities.
			 */
			mcv_sel = mcv_clauselist_selectivity(root, stat, stat_clauses,
												 varRelid, jointype, sjinfo,
												 rel, &mcv_basesel,
												 &mcv_totalsel);

			/* Combine the simple and multi-column estimates. */
			stat_sel = mcv_combine_selectivities(simple_sel,
												 mcv_sel,
												 mcv_basesel,
												 mcv_totalsel);

			/* Factor this into the overall result */
			sel *= stat_sel;
		}
	}

	return sel;
}

/*
 * ============================================================================
 * 【中文注释】statext_clauselist_selectivity —— 用最佳多列统计估计子句列表选择性
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对给定子句列表，先用多变量 MCV 列表估算（对每个适用的统计对象），再用函数
 *   依赖统计补充估算剩余子句，返回综合选择性。这是规划器在 clauselist_selectivity
 *   中调用扩展统计的主入口。
 *
 * 参数：
 *   root / varRelid / jointype / sjinfo / rel - 规划上下文。
 *   estimatedclauses - in/out 位图：已被估算的子句下标置位，避免重复估算。
 *   is_or - 子句是否为 OR 连接。
 *
 * 返回值：
 *   Selectivity - 估计的选择性（初始为 1.0，依次与各统计的估计相乘）。
 *
 * 设计思想：
 *   1. 先调用 statext_mcv_clauselist_selectivity() 用 MCV 统计估算（该函数内部会
 *      用 mcv_combine_selectivities() 结合单列统计与 MCV 修正）。
 *   2. 再用 dependencies_clauselist_selectivity() 用函数依赖统计估算——MCV 与
 *      函数依赖互补：MCV 能给出两列取值的精确选择性，函数依赖只反映依赖的整体
 *      强度。
 *   3. 每步都通过 estimatedclauses 标记已估算子句，避免重复计算。
 * ============================================================================
 */
Selectivity
statext_clauselist_selectivity(PlannerInfo *root, List *clauses, int varRelid,
							   JoinType jointype, SpecialJoinInfo *sjinfo,
							   RelOptInfo *rel, Bitmapset **estimatedclauses,
							   bool is_or)
{
	Selectivity sel;

	/* First, try estimating clauses using a multivariate MCV list. */
	sel = statext_mcv_clauselist_selectivity(root, clauses, varRelid, jointype,
											 sjinfo, rel, estimatedclauses, is_or);

	/*
	 * Functional dependencies only work for clauses connected by AND, so for
	 * OR clauses we're done.
	 */
	if (is_or)
		return sel;

	/*
	 * Then, apply functional dependencies on the remaining clauses by calling
	 * dependencies_clauselist_selectivity.  Pass 'estimatedclauses' so the
	 * function can properly skip clauses already estimated above.
	 *
	 * The reasoning for applying dependencies last is that the more complex
	 * stats can track more complex correlations between the attributes, and
	 * so may be considered more reliable.
	 *
	 * For example, MCV list can give us an exact selectivity for values in
	 * two columns, while functional dependencies can only provide information
	 * about the overall strength of the dependency.
	 */
	sel *= dependencies_clauselist_selectivity(root, clauses, varRelid,
											   jointype, sjinfo, rel,
											   estimatedclauses);

	return sel;
}

/*
 * ============================================================================
 * 【中文注释】examine_opclause_args —— 拆解操作符子句的参数（Expr 与 Const）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   尝试把操作符表达式的参数匹配为 (Expr op Const) 或 (Const op Expr) 两种形态
 *   （上层可能包着 RelabelType）。匹配成功返回 true，否则 false。
 *
 * 参数：
 *   args        - OpExpr 的参数列表（两个参数）。
 *   exprp       - 可选输出：提取出的表达式节点。
 *   cstp        - 可选输出：提取出的常量节点。
 *   expronleftp - 可选输出：表达式是否在操作符左边。
 *
 * 返回值：
 *   bool - 参数符合上述形态返回 true，否则 false。
 *
 * 设计思想：
 *   去掉 RelabelType（二进制兼容的重标注）后，检查两个操作数是否一个是表达式而
 *   另一个是常量（不要求顺序）；把常量放在固定一侧便于后续统一比较。
 * ============================================================================
 */
bool
examine_opclause_args(List *args, Node **exprp, Const **cstp,
					  bool *expronleftp)
{
	Node	   *expr;
	Const	   *cst;
	bool		expronleft;
	Node	   *leftop,
			   *rightop;

	/* enforced by statext_is_compatible_clause_internal */
	Assert(list_length(args) == 2);

	leftop = linitial(args);
	rightop = lsecond(args);

	/* strip RelabelType from either side of the expression */
	if (IsA(leftop, RelabelType))
		leftop = (Node *) ((RelabelType *) leftop)->arg;

	if (IsA(rightop, RelabelType))
		rightop = (Node *) ((RelabelType *) rightop)->arg;

	if (IsA(rightop, Const))
	{
		expr = leftop;
		cst = (Const *) rightop;
		expronleft = true;
	}
	else if (IsA(leftop, Const))
	{
		expr = rightop;
		cst = (Const *) leftop;
		expronleft = false;
	}
	else
		return false;

	/* return pointers to the extracted parts if requested */
	if (exprp)
		*exprp = expr;

	if (cstp)
		*cstp = cst;

	if (expronleftp)
		*expronleftp = expronleft;

	return true;
}


/*
 * ============================================================================
 * 【中文注释】compute_expr_stats —— 计算关系的表达式统计
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对统计对象定义的全部表达式，用采样行逐行计算表达式的值，然后调用各表达式
 *   类型的 compute_stats（由 typanalyze 设置）完成单表达式统计。
 *
 * 参数：
 *   onerel   - 目标关系。
 *   exprdata - 每个表达式的分析数据（含 VacAttrStats 与表达式）。
 *   nexprs   - 表达式个数。
 *   rows     - 采样元组数组。
 *   numrows  - 采样行数。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   1. 为表达式求值创建独立内存上下文，用 EState/ExprContext 逐行求值所有表达式，
 *      结果放入 exprdata[i].exprvals/exprnulls（按行×表达式个数排布）。
 *   2. 由于表达式统计不直接挂在列上，需要"伪造" fetch 函数（expr_fetch_func）
 *      从 Datum 数组取数据，代替通常的元组列取数。
 *   3. 收集足够行数后，对每个表达式调用其 compute_stats 计算统计，并释放求值
 *      上下文。
 * ============================================================================
 */
static void
compute_expr_stats(Relation onerel, AnlExprData *exprdata, int nexprs,
				   HeapTuple *rows, int numrows)
{
	MemoryContext expr_context,
				old_context;
	int			ind,
				i;

	expr_context = AllocSetContextCreate(CurrentMemoryContext,
										 "Analyze Expression",
										 ALLOCSET_DEFAULT_SIZES);
	old_context = MemoryContextSwitchTo(expr_context);

	for (ind = 0; ind < nexprs; ind++)
	{
		AnlExprData *thisdata = &exprdata[ind];
		VacAttrStats *stats = thisdata->vacattrstat;
		Node	   *expr = thisdata->expr;
		TupleTableSlot *slot;
		EState	   *estate;
		ExprContext *econtext;
		Datum	   *exprvals;
		bool	   *exprnulls;
		ExprState  *exprstate;
		int			tcnt;

		/* Are we still in the main context? */
		Assert(CurrentMemoryContext == expr_context);

		/*
		 * Need an EState for evaluation of expressions.  Create it in the
		 * per-expression context to be sure it gets cleaned up at the bottom
		 * of the loop.
		 */
		estate = CreateExecutorState();
		econtext = GetPerTupleExprContext(estate);

		/* Set up expression evaluation state */
		exprstate = ExecPrepareExpr((Expr *) expr, estate);

		/* Need a slot to hold the current heap tuple, too */
		slot = MakeSingleTupleTableSlot(RelationGetDescr(onerel),
										&TTSOpsHeapTuple);

		/* Arrange for econtext's scan tuple to be the tuple under test */
		econtext->ecxt_scantuple = slot;

		/* Compute and save expression values */
		exprvals = (Datum *) palloc(numrows * sizeof(Datum));
		exprnulls = (bool *) palloc(numrows * sizeof(bool));

		tcnt = 0;
		for (i = 0; i < numrows; i++)
		{
			Datum		datum;
			bool		isnull;

			/*
			 * Reset the per-tuple context each time, to reclaim any cruft
			 * left behind by evaluating the statistics expressions.
			 */
			ResetExprContext(econtext);

			/* Set up for expression evaluation */
			ExecStoreHeapTuple(rows[i], slot, false);

			/*
			 * Evaluate the expression. We do this in the per-tuple context so
			 * as not to leak memory, and then copy the result into the
			 * context created at the beginning of this function.
			 */
			datum = ExecEvalExprSwitchContext(exprstate,
											  GetPerTupleExprContext(estate),
											  &isnull);
			if (isnull)
			{
				exprvals[tcnt] = (Datum) 0;
				exprnulls[tcnt] = true;
			}
			else
			{
				/* Make sure we copy the data into the context. */
				Assert(CurrentMemoryContext == expr_context);

				exprvals[tcnt] = datumCopy(datum,
										   stats->attrtype->typbyval,
										   stats->attrtype->typlen);
				exprnulls[tcnt] = false;
			}

			tcnt++;
		}

		/*
		 * Now we can compute the statistics for the expression columns.
		 *
		 * XXX Unlike compute_index_stats we don't need to switch and reset
		 * memory contexts here, because we're only computing stats for a
		 * single expression (and not iterating over many indexes), so we just
		 * do it in expr_context. Note that compute_stats copies the result
		 * into stats->anl_context, so it does not disappear.
		 */
		if (tcnt > 0)
		{
			AttributeOpts *aopt =
				get_attribute_options(onerel->rd_id, stats->tupattnum);

			stats->exprvals = exprvals;
			stats->exprnulls = exprnulls;
			stats->rowstride = 1;
			stats->compute_stats(stats,
								 expr_fetch_func,
								 tcnt,
								 tcnt);

			/*
			 * If the n_distinct option is specified, it overrides the above
			 * computation.
			 */
			if (aopt != NULL && aopt->n_distinct != 0.0)
				stats->stadistinct = aopt->n_distinct;
		}

		/* And clean up */
		MemoryContextSwitchTo(expr_context);

		ExecDropSingleTupleTableSlot(slot);
		FreeExecutorState(estate);
		MemoryContextReset(expr_context);
	}

	MemoryContextSwitchTo(old_context);
	MemoryContextDelete(expr_context);
}


/*
 * ============================================================================
 * 【中文注释】expr_fetch_func —— 表达式统计的"取数"函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为表达式统计的 compute_stats 提供取数回调：从 Datum 数组直接取第 rownum 行
 *   的值，而不是构造元组再取列。
 *
 * 参数：
 *   stats  - VacAttrStats（含 exprvals/exprnulls/rowstride）。
 *   rownum - 行号。
 *   isNull - 输出参数：该值是否 NULL。
 *
 * 返回值：
 *   Datum - 该行该表达式的值。
 *
 * 设计思想：
 *   exprvals/exprnulls 已按列偏移排布（每行 stride 个值），直接用
 *   i = rownum * rowstride 定位。
 * ============================================================================
 */
static Datum
expr_fetch_func(VacAttrStatsP stats, int rownum, bool *isNull)
{
	int			i;

	/* exprvals and exprnulls are already offset for proper column */
	i = rownum * stats->rowstride;
	*isNull = stats->exprnulls[i];
	return stats->exprvals[i];
}

/*
 * ============================================================================
 * 【中文注释】build_expr_data —— 为表达式列表构建分析数据
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对统计对象的所有表达式逐一调用 examine_expression() 构建 VacAttrStats，
 *   组装成 AnlExprData 数组返回。
 *
 * 参数：
 *   exprs     - 表达式列表。
 *   stattarget- 统计目标（透传给 examine_expression）。
 *
 * 返回值：
 *   AnlExprData* - 长度为表达式个数的数组。
 *
 * 设计思想：
 *   表达式统计不直接绑定关系（表/索引），因此 examine_expression() 里有些字段是
 *   伪造的（如 tupattnum=InvalidAttrNumber）。
 * ============================================================================
 */
static AnlExprData *
build_expr_data(List *exprs, int stattarget)
{
	int			idx;
	int			nexprs = list_length(exprs);
	AnlExprData *exprdata;
	ListCell   *lc;

	exprdata = (AnlExprData *) palloc0(nexprs * sizeof(AnlExprData));

	idx = 0;
	foreach(lc, exprs)
	{
		Node	   *expr = (Node *) lfirst(lc);
		AnlExprData *thisdata = &exprdata[idx];

		thisdata->expr = expr;
		thisdata->vacattrstat = examine_expression(expr, stattarget);
		idx++;
	}

	return exprdata;
}

/*
 * ============================================================================
 * 【中文注释】serialize_expr_stats —— 把表达式统计序列化为 pg_statistic 行数组
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对每个表达式，把计算好的统计按 update_attstats() 的方式构造为一条
 *   pg_statistic 元组（复合类型），最后聚合成一个数组 Datum，供写入
 *   pg_statistic_ext_data.stxdexpr。
 *
 * 参数：
 *   exprdata - 表达式分析数据数组。
 *   nexprs   - 表达式个数。
 *
 * 返回值：
 *   Datum - 以 pg_statistic 复合类型构成的数组。
 *
 * 设计思想：
 *   1. 打开 pg_statistic 并取其复合类型 OID（pg_statistic[]）。
 *   2. 对每个表达式：starelid 用统计对象 OID 无效化处理（表达式不挂具体列），
 *      staattnum 用 1..nexprs 序号标识，stainherit 为 false；stavalues1..5 等由
 *      表达式统计里的 stavalues 复制，同时记录 nulls。
 *   3. 逐条 heap_form_tuple 构造 pg_statistic 元组并聚成数组。
 * ============================================================================
 */
static Datum
serialize_expr_stats(AnlExprData *exprdata, int nexprs)
{
	int			exprno;
	Oid			typOid;
	Relation	sd;

	ArrayBuildState *astate = NULL;

	sd = table_open(StatisticRelationId, RowExclusiveLock);

	/* lookup OID of composite type for pg_statistic */
	typOid = get_rel_type_id(StatisticRelationId);
	if (!OidIsValid(typOid))
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("relation \"%s\" does not have a composite type",
						"pg_statistic")));

	for (exprno = 0; exprno < nexprs; exprno++)
	{
		int			i,
					k;
		VacAttrStats *stats = exprdata[exprno].vacattrstat;

		Datum		values[Natts_pg_statistic];
		bool		nulls[Natts_pg_statistic];
		HeapTuple	stup;

		if (!stats->stats_valid)
		{
			astate = accumArrayResult(astate,
									  (Datum) 0,
									  true,
									  typOid,
									  CurrentMemoryContext);
			continue;
		}

		/*
		 * Construct a new pg_statistic tuple
		 */
		for (i = 0; i < Natts_pg_statistic; ++i)
		{
			nulls[i] = false;
		}

		values[Anum_pg_statistic_starelid - 1] = ObjectIdGetDatum(InvalidOid);
		values[Anum_pg_statistic_staattnum - 1] = Int16GetDatum(InvalidAttrNumber);
		values[Anum_pg_statistic_stainherit - 1] = BoolGetDatum(false);
		values[Anum_pg_statistic_stanullfrac - 1] = Float4GetDatum(stats->stanullfrac);
		values[Anum_pg_statistic_stawidth - 1] = Int32GetDatum(stats->stawidth);
		values[Anum_pg_statistic_stadistinct - 1] = Float4GetDatum(stats->stadistinct);
		i = Anum_pg_statistic_stakind1 - 1;
		for (k = 0; k < STATISTIC_NUM_SLOTS; k++)
		{
			values[i++] = Int16GetDatum(stats->stakind[k]); /* stakindN */
		}
		i = Anum_pg_statistic_staop1 - 1;
		for (k = 0; k < STATISTIC_NUM_SLOTS; k++)
		{
			values[i++] = ObjectIdGetDatum(stats->staop[k]);	/* staopN */
		}
		i = Anum_pg_statistic_stacoll1 - 1;
		for (k = 0; k < STATISTIC_NUM_SLOTS; k++)
		{
			values[i++] = ObjectIdGetDatum(stats->stacoll[k]);	/* stacollN */
		}
		i = Anum_pg_statistic_stanumbers1 - 1;
		for (k = 0; k < STATISTIC_NUM_SLOTS; k++)
		{
			int			nnum = stats->numnumbers[k];

			if (nnum > 0)
			{
				int			n;
				Datum	   *numdatums = (Datum *) palloc(nnum * sizeof(Datum));
				ArrayType  *arry;

				for (n = 0; n < nnum; n++)
					numdatums[n] = Float4GetDatum(stats->stanumbers[k][n]);
				arry = construct_array_builtin(numdatums, nnum, FLOAT4OID);
				values[i++] = PointerGetDatum(arry);	/* stanumbersN */
			}
			else
			{
				nulls[i] = true;
				values[i++] = (Datum) 0;
			}
		}
		i = Anum_pg_statistic_stavalues1 - 1;
		for (k = 0; k < STATISTIC_NUM_SLOTS; k++)
		{
			if (stats->numvalues[k] > 0)
			{
				ArrayType  *arry;

				arry = construct_array(stats->stavalues[k],
									   stats->numvalues[k],
									   stats->statypid[k],
									   stats->statyplen[k],
									   stats->statypbyval[k],
									   stats->statypalign[k]);
				values[i++] = PointerGetDatum(arry);	/* stavaluesN */
			}
			else
			{
				nulls[i] = true;
				values[i++] = (Datum) 0;
			}
		}

		stup = heap_form_tuple(RelationGetDescr(sd), values, nulls);

		astate = accumArrayResult(astate,
								  heap_copy_tuple_as_datum(stup, RelationGetDescr(sd)),
								  false,
								  typOid,
								  CurrentMemoryContext);
	}

	table_close(sd, RowExclusiveLock);

	return makeArrayResult(astate, CurrentMemoryContext);
}

/*
 * ============================================================================
 * 【中文注释】statext_expressions_load —— 加载某表达式的 pg_statistic 记录
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从 pg_statistic_ext_data.stxdexpr（表达式统计数组）中取出第 idx 个表达式
 *   对应的 pg_statistic 记录。
 *
 * 参数：
 *   stxoid - 统计对象 OID。
 *   inh    - 是否针对继承树。
 *   idx    - 表达式序号。
 *
 * 返回值：
 *   HeapTuple - 对应的 pg_statistic 记录；没有可用统计时返回 NULL。
 *
 * 设计思想：
 *   1. 按 syscache（STATEXTDATASTXOID）取 stxdexpr 列（ExpandedArrayHeader）。
 *   2. 若列为 NULL 或长度不足（下标越界）返回 NULL。
 *   3. 取第 idx 个元素，若该元素为 NULL 返回 NULL；否则把元素展开为 HeapTupleHeader
 *      并组装成 HeapTupleData 返回（注意展开内存生命周期由调用方/上下文管理）。
 * ============================================================================
 */
HeapTuple
statext_expressions_load(Oid stxoid, bool inh, int idx)
{
	bool		isnull;
	Datum		value;
	HeapTuple	htup;
	ExpandedArrayHeader *eah;
	HeapTupleHeader td;
	HeapTupleData tmptup;
	HeapTuple	tup;

	htup = SearchSysCache2(STATEXTDATASTXOID,
						   ObjectIdGetDatum(stxoid), BoolGetDatum(inh));
	if (!HeapTupleIsValid(htup))
		elog(ERROR, "cache lookup failed for statistics object %u", stxoid);

	value = SysCacheGetAttr(STATEXTDATASTXOID, htup,
							Anum_pg_statistic_ext_data_stxdexpr, &isnull);
	if (isnull)
		elog(ERROR,
			 "requested statistics kind \"%c\" is not yet built for statistics object %u",
			 STATS_EXT_EXPRESSIONS, stxoid);

	eah = DatumGetExpandedArray(value);

	deconstruct_expanded_array(eah);

	if (eah->dnulls && eah->dnulls[idx])
	{
		/* No data found for this expression, give up. */
		ReleaseSysCache(htup);
		return NULL;
	}

	td = DatumGetHeapTupleHeader(eah->dvalues[idx]);

	/* Build a temporary HeapTuple control structure */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(td);
	ItemPointerSetInvalid(&(tmptup.t_self));
	tmptup.t_tableOid = InvalidOid;
	tmptup.t_data = td;

	tup = heap_copytuple(&tmptup);

	ReleaseSysCache(htup);

	return tup;
}

/*
 * ============================================================================
 * 【中文注释】make_build_data —— 评估表达式并构建统计构建数据
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为构建一个统计对象的所有请求类型准备 StatsBuildData：把普通列的值与所有
 *   表达式的求值结果组织成统一的按"行×列"排布的 Datum 数组，供 ndistinct/
 *   dependencies/MCV 各构建函数使用。
 *
 * 参数：
 *   rel        - 目标关系。
 *   stat       - 统计对象信息（含列位图与表达式）。
 *   numrows    - 采样行数。
 *   rows       - 采样元组数组。
 *   stats      - 各列/表达式的 VacAttrStats 数组。
 *   stattarget - 统计目标。
 *
 * 返回值：
 *   StatsBuildData* - 构建好的数据。
 *
 * 设计思想：
 *   1. 若对象有表达式，用 EState/ExprContext 对每行求值所有表达式（结果集中存
 *      exprvals/exprnulls），昂贵表达式只求值一次即可供所有统计类型复用。
 *   2. result 里各字段：nattnums（列+表达式总数）、attnums（列号，表达式为负）、
 *      numrows、stats 数组、typcache（各列 typcache 条目）、values/isnull（列值）、
 *      exprvals/exprnulls（表达式值）等。
 *   3. 单列值也统一拷贝进 values/isnull，方便下游统一用 SortItem 处理。
 * ============================================================================
 */
static StatsBuildData *
make_build_data(Relation rel, StatExtEntry *stat, int numrows, HeapTuple *rows,
				VacAttrStats **stats, int stattarget)
{
	/* evaluated expressions */
	StatsBuildData *result;
	char	   *ptr;
	Size		len;

	int			i;
	int			k;
	int			idx;
	TupleTableSlot *slot;
	EState	   *estate;
	ExprContext *econtext;
	List	   *exprstates = NIL;
	int			nkeys = bms_num_members(stat->columns) + list_length(stat->exprs);
	ListCell   *lc;

	/* allocate everything as a single chunk, so we can free it easily */
	len = MAXALIGN(sizeof(StatsBuildData));
	len += MAXALIGN(sizeof(AttrNumber) * nkeys);	/* attnums */
	len += MAXALIGN(sizeof(VacAttrStats *) * nkeys);	/* stats */

	/* values */
	len += MAXALIGN(sizeof(Datum *) * nkeys);
	len += nkeys * MAXALIGN(sizeof(Datum) * numrows);

	/* nulls */
	len += MAXALIGN(sizeof(bool *) * nkeys);
	len += nkeys * MAXALIGN(sizeof(bool) * numrows);

	ptr = palloc(len);

	/* set the pointers */
	result = (StatsBuildData *) ptr;
	ptr += MAXALIGN(sizeof(StatsBuildData));

	/* attnums */
	result->attnums = (AttrNumber *) ptr;
	ptr += MAXALIGN(sizeof(AttrNumber) * nkeys);

	/* stats */
	result->stats = (VacAttrStats **) ptr;
	ptr += MAXALIGN(sizeof(VacAttrStats *) * nkeys);

	/* values */
	result->values = (Datum **) ptr;
	ptr += MAXALIGN(sizeof(Datum *) * nkeys);

	/* nulls */
	result->nulls = (bool **) ptr;
	ptr += MAXALIGN(sizeof(bool *) * nkeys);

	for (i = 0; i < nkeys; i++)
	{
		result->values[i] = (Datum *) ptr;
		ptr += MAXALIGN(sizeof(Datum) * numrows);

		result->nulls[i] = (bool *) ptr;
		ptr += MAXALIGN(sizeof(bool) * numrows);
	}

	Assert((ptr - (char *) result) == len);

	/* we have it allocated, so let's fill the values */
	result->nattnums = nkeys;
	result->numrows = numrows;

	/* fill the attribute info - first attributes, then expressions */
	idx = 0;
	k = -1;
	while ((k = bms_next_member(stat->columns, k)) >= 0)
	{
		result->attnums[idx] = k;
		result->stats[idx] = stats[idx];

		idx++;
	}

	k = -1;
	foreach(lc, stat->exprs)
	{
		Node	   *expr = (Node *) lfirst(lc);

		result->attnums[idx] = k;
		result->stats[idx] = examine_expression(expr, stattarget);

		idx++;
		k--;
	}

	/* first extract values for all the regular attributes */
	for (i = 0; i < numrows; i++)
	{
		idx = 0;
		k = -1;
		while ((k = bms_next_member(stat->columns, k)) >= 0)
		{
			result->values[idx][i] = heap_getattr(rows[i], k,
												  result->stats[idx]->tupDesc,
												  &result->nulls[idx][i]);

			idx++;
		}
	}

	/* Need an EState for evaluation expressions. */
	estate = CreateExecutorState();
	econtext = GetPerTupleExprContext(estate);

	/* Need a slot to hold the current heap tuple, too */
	slot = MakeSingleTupleTableSlot(RelationGetDescr(rel),
									&TTSOpsHeapTuple);

	/* Arrange for econtext's scan tuple to be the tuple under test */
	econtext->ecxt_scantuple = slot;

	/* Set up expression evaluation state */
	exprstates = ExecPrepareExprList(stat->exprs, estate);

	for (i = 0; i < numrows; i++)
	{
		/*
		 * Reset the per-tuple context each time, to reclaim any cruft left
		 * behind by evaluating the statistics object expressions.
		 */
		ResetExprContext(econtext);

		/* Set up for expression evaluation */
		ExecStoreHeapTuple(rows[i], slot, false);

		idx = bms_num_members(stat->columns);
		foreach(lc, exprstates)
		{
			Datum		datum;
			bool		isnull;
			ExprState  *exprstate = (ExprState *) lfirst(lc);

			/*
			 * XXX This probably leaks memory. Maybe we should use
			 * ExecEvalExprSwitchContext but then we need to copy the result
			 * somewhere else.
			 */
			datum = ExecEvalExpr(exprstate,
								 GetPerTupleExprContext(estate),
								 &isnull);
			if (isnull)
			{
				result->values[idx][i] = (Datum) 0;
				result->nulls[idx][i] = true;
			}
			else
			{
				result->values[idx][i] = datum;
				result->nulls[idx][i] = false;
			}

			idx++;
		}
	}

	ExecDropSingleTupleTableSlot(slot);
	FreeExecutorState(estate);

	return result;
}
