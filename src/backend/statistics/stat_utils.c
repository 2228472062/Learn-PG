/*-------------------------------------------------------------------------
 * stat_utils.c
 *
 *	  PostgreSQL statistics manipulation utilities.
 *
 * Code supporting the direct manipulation of statistics.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *       src/backend/statistics/stat_utils.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/htup_details.h"
#include "access/relation.h"
#include "catalog/index.h"
#include "catalog/namespace.h"
#include "catalog/pg_class.h"
#include "catalog/pg_collation.h"
#include "catalog/pg_database.h"
#include "catalog/pg_statistic.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "statistics/stat_utils.h"
#include "storage/lmgr.h"
#include "utils/acl.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/rangetypes.h"
#include "utils/rel.h"
#include "utils/syscache.h"
#include "utils/typcache.h"

/* Default values assigned to new pg_statistic tuples. */
#define DEFAULT_STATATT_NULL_FRAC      Float4GetDatum(0.0)	/* stanullfrac */
#define DEFAULT_STATATT_AVG_WIDTH      Int32GetDatum(0) /* stawidth, same as
														 * unknown */
#define DEFAULT_STATATT_N_DISTINCT     Float4GetDatum(0.0)	/* stadistinct, same as
															 * unknown */

static Node *statatt_get_index_expr(Relation rel, int attnum);

/*
 * ============================================================================
 * 【中文注释】stats_check_required_arg —— 检查参数是否为 NULL
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对"必填参数"做空值检查：若该位置参数为 NULL 则直接报 ERROR。用于导入统计的
 *   函数（如 pg_restore_attribute_stats）中必须提供的基础参数（表名、列名等）。
 *
 * 参数：
 *   fcinfo - 位置参数调用信息。
 *   arginfo- 参数名/类型描述表（StatsArgInfo 数组），用于取参数名字。
 *   argnum - 要检查的位置下标。
 *
 * 返回值：无（检查失败直接 ereport ERROR）。
 *
 * 设计思想：
 *   StatsArgInfo 数组把"位置下标"映射到"参数名字与类型"，便于报错信息里输出
 *   用户可见的参数名。
 * ============================================================================
 */
void
stats_check_required_arg(FunctionCallInfo fcinfo,
						 struct StatsArgInfo *arginfo,
						 int argnum)
{
	if (PG_ARGISNULL(argnum))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("argument \"%s\" must not be null",
						arginfo[argnum].argname)));
}

/*
 * ============================================================================
 * 【中文注释】stats_check_arg_array —— 检查数组类参数是否合法
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查某个数组参数：若为 NULL 视为"未指定"，直接通过；否则要求它是一维数组且
 *   不含 NULL 元素（对应 pg_statistic 中 stanumbers/stavalues 的约束）。
 *
 * 参数：
 *   fcinfo - 位置参数调用信息。
 *   arginfo- 参数名/类型描述表。
 *   argnum - 待检查的位置下标。
 *
 * 返回值：
 *   bool - true 合法（或为 NULL）；false 非法（已发 WARNING）。
 *
 * 设计思想：
 *   统计值数组（如 MCV 频率、直方图桶数）必须是扁平的一维数组，且每个元素都要有
 *   值——NULL 元素会破坏统计语义。校验失败不报 ERROR，而是返回 false 让上层
 *   降级跳过该项统计，保证其它统计项仍可写入。
 * ============================================================================
 */
bool
stats_check_arg_array(FunctionCallInfo fcinfo,
					  struct StatsArgInfo *arginfo,
					  int argnum)
{
	ArrayType  *arr;

	if (PG_ARGISNULL(argnum))
		return true;

	arr = DatumGetArrayTypeP(PG_GETARG_DATUM(argnum));

	if (ARR_NDIM(arr) != 1)
	{
		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("argument \"%s\" must not be a multidimensional array",
						arginfo[argnum].argname)));
		return false;
	}

	if (array_contains_nulls(arr))
	{
		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("argument \"%s\" array must not contain null values",
						arginfo[argnum].argname)));
		return false;
	}

	return true;
}

/*
 * ============================================================================
 * 【中文注释】stats_check_arg_pair —— 检查必须成对出现的参数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   强制两个参数"要么都提供、要么都不提供"。例如 MCV 统计必须同时给
 *   most_common_vals 和 most_common_freqs；只给其中一个属于不一致输入。
 *
 * 参数：
 *   fcinfo     - 位置参数调用信息。
 *   arginfo    - 参数名/类型描述表。
 *   argnum1/argnum2 - 两个要配对检查的位置下标。
 *
 * 返回值：
 *   bool - true 合法；false 非法（已发 WARNING）。
 *
 * 设计思想：
 *   各种统计项在 pg_statistic 里往往同时占用 stanumbers 和 stavalues 两个列，
 *   单独给一个会产生残缺数据，因此必须成对校验。与其它 check 函数一致，失败仅
 *   返回 false，由调用方决定降级处理。
 * ============================================================================
 */
bool
stats_check_arg_pair(FunctionCallInfo fcinfo,
					 struct StatsArgInfo *arginfo,
					 int argnum1, int argnum2)
{
	if (PG_ARGISNULL(argnum1) && PG_ARGISNULL(argnum2))
		return true;

	if (PG_ARGISNULL(argnum1) || PG_ARGISNULL(argnum2))
	{
		int			nullarg = PG_ARGISNULL(argnum1) ? argnum1 : argnum2;
		int			otherarg = PG_ARGISNULL(argnum1) ? argnum2 : argnum1;

		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("argument \"%s\" must be specified when argument \"%s\" is specified",
						arginfo[nullarg].argname,
						arginfo[otherarg].argname)));

		return false;
	}

	return true;
}

/*
 * ============================================================================
 * 【中文注释】RangeVarCallbackForStats —— 统计操作的表名解析回调
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   作为 RangeVarGetRelidExtended() 的回调，在按名字解析并加锁目标表的过程中被
 *   反复调用（首次解析、以及发生重命名/删除导致重试时）。它负责三类事情：
 *   (1) 处理"并发改名/删除"导致的锁状态修正；
 *   (2) 校验关系类型（必须可用 ANALYZE 的类型）且非共享关系；
 *   (3) 校验权限：数据库属主可免检（owns DB 且表非共享），否则需要 MAINTAIN 权限。
 *
 * 参数：
 *   relation - 用户给出的 RangeVar。
 *   relId    - 本次解析得到的 OID（可能为 InvalidOid）。
 *   oldRelId - 上一次解析得到的 OID（用于检测是否发生变化）。
 *   arg      - 用户数据指针，此处指向一个 Oid*，用于跨次调用记录"已锁定的表 OID"。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   1.【竞态处理】：
 *     - 若本次 relId 与上次不同且我们之前锁过别的表，则先释放旧锁。
 *     - 若 relId==oldRelId，说明是"重试后拿到同一 OID"，此时要区分两种情况：
 *       上次发现是索引但这次不是（索引被删、OID 被复用）→ 报错；
 *       上次不是索引但这次是（关系被删、OID 被复用来建索引）→ 报错。
 *       这两种情况都因为"无法安全补锁/释放"而选择直接报错，避免死锁。
 *     - 若关系是索引，则真正要锁/校验的是它所属的堆表（IndexGetRelation）。
 *   (2) 只允许 RELKIND_RELATION / MATVIEW / FOREIGN_TABLE / PARTITIONED_TABLE
 *       这些可与 ANALYZE 配合的关系类型。
 *   (3) 权限：数据库属主拥有数据库内一切对象的修改权（非共享表），否则必须有
 *       MAINTAIN 权限（PG 15+ 引入的细粒度维护权限）。
 *   4.【锁顺序】："先锁堆表、后锁索引"以避免死锁。因此当目标是索引时，这里会显式
 *      再对父表加 ShareUpdateExclusiveLock 并记录到 *locked_oid。
 * ============================================================================
 */
void
RangeVarCallbackForStats(const RangeVar *relation,
						 Oid relId, Oid oldRelId, void *arg)
{
	Oid		   *locked_oid = (Oid *) arg;
	Oid			table_oid = relId;
	HeapTuple	tuple;
	Form_pg_class form;
	char		relkind;

	/*
	 * If we previously locked some other index's heap, and the name we're
	 * looking up no longer refers to that relation, release the now-useless
	 * lock.
	 */
	if (relId != oldRelId && OidIsValid(*locked_oid))
	{
		UnlockRelationOid(*locked_oid, ShareUpdateExclusiveLock);
		*locked_oid = InvalidOid;
	}

	/* If the relation does not exist, there's nothing more to do. */
	if (!OidIsValid(relId))
		return;

	/* If the relation does exist, check whether it's an index. */
	relkind = get_rel_relkind(relId);
	if (relkind == RELKIND_INDEX ||
		relkind == RELKIND_PARTITIONED_INDEX)
		table_oid = IndexGetRelation(relId, false);

	/*
	 * If retrying yields the same OID, there are a couple of extremely
	 * unlikely scenarios we need to handle.
	 */
	if (relId == oldRelId)
	{
		/*
		 * If a previous lookup found an index, but the current lookup did
		 * not, the index was dropped and the OID was reused for something
		 * else between lookups.  In theory, we could simply drop our lock on
		 * the index's parent table and proceed, but in the interest of
		 * avoiding complexity, we just error.
		 */
		if (table_oid == relId && OidIsValid(*locked_oid))
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_OBJECT),
					 errmsg("index \"%s\" was concurrently dropped",
							relation->relname)));

		/*
		 * If the current lookup found an index but a previous lookup either
		 * did not find an index or found one with a different parent
		 * relation, the relation was dropped and the OID was reused for an
		 * index between lookups.  RangeVarGetRelidExtended() will have
		 * already locked the index at this point, so we can't just lock the
		 * newly discovered parent table OID without risking deadlock.  As
		 * above, we just error in this case.
		 */
		if (table_oid != relId && table_oid != *locked_oid)
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_OBJECT),
					 errmsg("index \"%s\" was concurrently created",
							relation->relname)));
	}

	tuple = SearchSysCache1(RELOID, ObjectIdGetDatum(table_oid));
	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "cache lookup failed for OID %u", table_oid);
	form = (Form_pg_class) GETSTRUCT(tuple);

	/* the relkinds that can be used with ANALYZE */
	switch (form->relkind)
	{
		case RELKIND_RELATION:
		case RELKIND_MATVIEW:
		case RELKIND_FOREIGN_TABLE:
		case RELKIND_PARTITIONED_TABLE:
			break;
		default:
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot modify statistics for relation \"%s\"",
							NameStr(form->relname)),
					 errdetail_relkind_not_supported(form->relkind)));
	}

	if (form->relisshared)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot modify statistics for shared relation")));

	/* Check permissions */
	if (!object_ownercheck(DatabaseRelationId, MyDatabaseId, GetUserId()))
	{
		AclResult	aclresult = pg_class_aclcheck(table_oid,
												  GetUserId(),
												  ACL_MAINTAIN);

		if (aclresult != ACLCHECK_OK)
			aclcheck_error(aclresult,
						   get_relkind_objtype(form->relkind),
						   NameStr(form->relname));
	}

	ReleaseSysCache(tuple);

	/* Lock heap before index to avoid deadlock. */
	if (relId != oldRelId && table_oid != relId)
	{
		LockRelationOid(table_oid, ShareUpdateExclusiveLock);
		*locked_oid = table_oid;
	}
}


/*
 * ============================================================================
 * 【中文注释】get_arg_by_name —— 按参数名字查找位置下标
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在参数描述表 arginfo 中按名字（大小写不敏感）查找对应位置下标，供
 *   stats_fill_fcinfo_from_arg_pairs() 把"键值对"翻译成"位置参数"时使用。
 *
 * 参数：
 *   argname - 要查找的参数名。
 *   arginfo - 参数名/类型描述表（以 argname==NULL 的哨兵项结尾）。
 *
 * 返回值：
 *   int - 匹配的位置下标；找不到时发 WARNING 并返回 -1。
 *
 * 设计思想：
 *   用 pg_strcasecmp 做大小写不敏感比较，对用户更友好。arginfo 的末尾必须是
 *   {NULL,...} 哨兵，作为循环结束条件。
 * ============================================================================
 */
static int
get_arg_by_name(const char *argname, struct StatsArgInfo *arginfo)
{
	int			argnum;

	for (argnum = 0; arginfo[argnum].argname != NULL; argnum++)
		if (pg_strcasecmp(argname, arginfo[argnum].argname) == 0)
			return argnum;

	ereport(WARNING,
			(errmsg("unrecognized argument name: \"%s\"", argname)));

	return -1;
}

/*
 * ============================================================================
 * 【中文注释】stats_check_arg_type —— 检查参数类型是否与期望一致
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   校验某参数的运行时类型（Oid）与描述表中声明的类型一致，防止用户以错误类型
 *   传参导致后续解释混乱。
 *
 * 参数：
 *   argname     - 参数名（仅用于报错）。
 *   argtype     - 实际传入的类型 OID。
 *   expectedtype- 期望的类型 OID。
 *
 * 返回值：
 *   bool - true 类型一致；false 不一致（已发 WARNING，并在信息中打印两种类型的
 *          可读名字）。
 *
 * 设计思想：
 *   类型不匹配不报 ERROR，仅返回 false 由调用方决定是否整体放弃。
 * ============================================================================
 */
static bool
stats_check_arg_type(const char *argname, Oid argtype, Oid expectedtype)
{
	if (argtype != expectedtype)
	{
		ereport(WARNING,
				(errmsg("argument \"%s\" has type %s, expected type %s",
						argname, format_type_be(argtype),
						format_type_be(expectedtype))));
		return false;
	}

	return true;
}

/*
 * ============================================================================
 * 【中文注释】statatt_get_index_expr —— 取索引表达式列对应的表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   当目标列是"索引表达式"（即索引列不是普通列，而是表达式，如 (a+b)）时，返回
 *   该列对应的表达式树节点；否则返回 NULL。这是为了能对表达式索引做正确的类型
 *   推导（表达式类型可能与其存储的 opckeytype 不同）。
 *
 * 参数：
 *   rel    - 目标关系（需是索引关系）。
 *   attnum - 索引中的列号（1 基）。
 *
 * 返回值：
 *   Node* - 若该列是表达式则返回表达式树，否则返回 NULL。
 *
 * 设计思想：
 *   1. 非索引关系直接返回 NULL。
 *   2. 索引的 indkey 数组里，普通列的 attnum 是"表列号（非 0）"，表达式列的
 *      attnum 是 0。因此若 indkey.values[attnum-1] != 0，说明是普通列，返回 NULL。
 *   3. 表达式都集中在 rd_indexprs 链表里，顺序与索引列一一对应；为了找到第 attnum
 *      列的表达式，必须跳过前面所有表达式列（indkey 为 0 的项）来推进链表指针。
 * ============================================================================
 */
static Node *
statatt_get_index_expr(Relation rel, int attnum)
{
	List	   *index_exprs;
	ListCell   *indexpr_item;

	/* relation is not an index */
	if (rel->rd_rel->relkind != RELKIND_INDEX &&
		rel->rd_rel->relkind != RELKIND_PARTITIONED_INDEX)
		return NULL;

	index_exprs = RelationGetIndexExpressions(rel);

	/* index has no expressions to give */
	if (index_exprs == NIL)
		return NULL;

	/*
	 * The index's attnum points directly to a relation attnum, hence it is
	 * not an expression attribute.
	 */
	if (rel->rd_index->indkey.values[attnum - 1] != 0)
		return NULL;

	indexpr_item = list_head(rel->rd_indexprs);

	for (int i = 0; i < attnum - 1; i++)
		if (rel->rd_index->indkey.values[i] == 0)
			indexpr_item = lnext(rel->rd_indexprs, indexpr_item);

	if (indexpr_item == NULL)	/* shouldn't happen */
		elog(ERROR, "too few entries in indexprs list");

	return (Node *) lfirst(indexpr_item);
}

/*
 * ============================================================================
 * 【中文注释】stats_fill_fcinfo_from_arg_pairs —— 变长键值对 → 位置参数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把"变长键值对"形式的 SQL 参数（name,value,name,value,...）翻译成位置参数数组，
 *   填充进预先初始化好的 positional_fcinfo，供关系/属性统计更新函数使用。
 *
 * 参数：
 *   pairs_fcinfo      - 原始变长参数调用信息（PG_GETARG 按 0..n 顺序取值）。
 *   positional_fcinfo - 目标位置参数调用信息（已用正确尺寸初始化）。
 *   arginfo           - 与目标函数配套的参数名/类型描述表。
 *
 * 返回值：
 *   bool - true 全部参数翻译成功；false 存在未知参数名或类型不匹配（已发 WARNING，
 *          其余合法参数仍被翻译）。
 *
 * 设计思想：
 *   1. 先清空目标位置参数（全部置 NULL），保证"未提供"的参数语义正确。
 *   2. extract_variadic_args() 取出变长参数并拆成 名字/值/类型 三个数组；个数必须
 *      为偶数，否则 ERROR。
 *   3. "version" 是保留键：目前接受但忽略（预留给未来解释旧版统计）。
 *   4. 逐个键值对：名字必须是 text 且非 NULL；用 get_arg_by_name() 找位置下标，
 *      再用 stats_check_arg_type() 校验类型；合法则写入目标位置参数。
 * ============================================================================
 */
bool
stats_fill_fcinfo_from_arg_pairs(FunctionCallInfo pairs_fcinfo,
								 FunctionCallInfo positional_fcinfo,
								 struct StatsArgInfo *arginfo)
{
	Datum	   *args;
	bool	   *argnulls;
	Oid		   *types;
	int			nargs;
	bool		result = true;

	/* clear positional args */
	for (int i = 0; arginfo[i].argname != NULL; i++)
	{
		positional_fcinfo->args[i].value = (Datum) 0;
		positional_fcinfo->args[i].isnull = true;
	}

	nargs = extract_variadic_args(pairs_fcinfo, 0, true,
								  &args, &types, &argnulls);

	if (nargs % 2 != 0)
		ereport(ERROR,
				errmsg("variadic arguments must be name/value pairs"),
				errhint("Provide an even number of variadic arguments that can be divided into pairs."));

	/*
	 * For each argument name/value pair, find corresponding positional
	 * argument for the argument name, and assign the argument value to
	 * positional_fcinfo.
	 */
	for (int i = 0; i < nargs; i += 2)
	{
		int			argnum;
		char	   *argname;

		if (argnulls[i])
			ereport(ERROR,
					(errmsg("name at variadic position %d is null", i + 1)));

		if (types[i] != TEXTOID)
			ereport(ERROR,
					(errmsg("name at variadic position %d has type %s, expected type %s",
							i + 1, format_type_be(types[i]),
							format_type_be(TEXTOID))));

		if (argnulls[i + 1])
			continue;

		argname = TextDatumGetCString(args[i]);

		/*
		 * The 'version' argument is a special case, not handled by arginfo
		 * because it's not a valid positional argument.
		 *
		 * For now, 'version' is accepted but ignored. In the future it can be
		 * used to interpret older statistics properly.
		 */
		if (pg_strcasecmp(argname, "version") == 0)
			continue;

		argnum = get_arg_by_name(argname, arginfo);

		if (argnum < 0 || !stats_check_arg_type(argname, types[i + 1],
												arginfo[argnum].argtype))
		{
			result = false;
			continue;
		}

		positional_fcinfo->args[argnum].value = args[i + 1];
		positional_fcinfo->args[argnum].isnull = false;
	}

	return result;
}

/*
 * ============================================================================
 * 【中文注释】statatt_get_type —— 从关系属性推导类型与操作符信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   根据 (reloid, attnum) 查询 pg_attribute/pg_type，得到该列的：类型 OID、typmod、
 *   排序规则 OID、类型分类（base/domain/range/...）、相等操作符、小于操作符。
 *   这是调用其它 statatt_*() 系列函数（如 statatt_build_stavalues、
 *   statatt_set_slot）的前提。
 *
 * 参数：
 *   reloid     - 关系 OID。
 *   attnum     - 列号。
 *   atttypid   - 输出：类型 OID。
 *   atttypmod  - 输出：typmod。
 *   atttyptype - 输出：类型分类（TYPTYPE_*，如 TYPTYPE_RANGE）。
 *   atttypcoll - 输出：排序规则 OID。
 *   eq_opr     - 输出：相等操作符 OID。
 *   lt_opr     - 输出：小于操作符 OID。
 *
 * 返回值：无（失败直接 ERROR）。
 *
 * 设计思想：
 *   1. 与 analyze.c 的 examine_attribute() 逻辑重复，但刻意"不因 attstattarget==0
 *      而跳过该列"，因为导入统计时不关心分析目标设置。
 *   2.【表达式索引特例】：若该列是索引表达式，则相信表达式树的类型而非列的存储
 *      类型（后者可能是 opclass 的 opckeytype 存储类型，对统计无意义）——与
 *      examine_attribute() 行为保持一致。
 *   3.【多范围类型】：若类型是多范围(multirange)，下降到其底层范围类型，与
 *      multirange_typanalyze() 一致。
 *   4. 用 lookup_type_cache() 找操作符，天然穿透 domain（域类型查底层基类型操作符）。
 *   5. tsvector 特例：其排序规则固定为 DEFAULT_COLLATION_OID（见
 *      compute_tsvector_stats()）。
 * ============================================================================
 */
void
statatt_get_type(Oid reloid, AttrNumber attnum,
				 Oid *atttypid, int32 *atttypmod,
				 char *atttyptype, Oid *atttypcoll,
				 Oid *eq_opr, Oid *lt_opr)
{
	Relation	rel = relation_open(reloid, AccessShareLock);
	Form_pg_attribute attr;
	HeapTuple	atup;
	Node	   *expr;
	TypeCacheEntry *typcache;

	atup = SearchSysCache2(ATTNUM, ObjectIdGetDatum(reloid),
						   Int16GetDatum(attnum));

	/* Attribute not found */
	if (!HeapTupleIsValid(atup))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_COLUMN),
				 errmsg("column %d of relation \"%s\" does not exist",
						attnum, RelationGetRelationName(rel))));

	attr = (Form_pg_attribute) GETSTRUCT(atup);

	if (attr->attisdropped)
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_COLUMN),
				 errmsg("column %d of relation \"%s\" does not exist",
						attnum, RelationGetRelationName(rel))));

	expr = statatt_get_index_expr(rel, attr->attnum);

	/*
	 * When analyzing an expression index, believe the expression tree's type
	 * not the column datatype --- the latter might be the opckeytype storage
	 * type of the opclass, which is not interesting for our purposes.  This
	 * mimics the behavior of examine_attribute().
	 */
	if (expr == NULL)
	{
		*atttypid = attr->atttypid;
		*atttypmod = attr->atttypmod;
		*atttypcoll = attr->attcollation;
	}
	else
	{
		*atttypid = exprType(expr);
		*atttypmod = exprTypmod(expr);

		if (OidIsValid(attr->attcollation))
			*atttypcoll = attr->attcollation;
		else
			*atttypcoll = exprCollation(expr);
	}
	ReleaseSysCache(atup);

	/*
	 * If it's a multirange, step down to the range type, as is done by
	 * multirange_typanalyze().
	 */
	if (type_is_multirange(*atttypid))
		*atttypid = get_multirange_range(*atttypid);

	/* finds the right operators even if atttypid is a domain */
	typcache = lookup_type_cache(*atttypid, TYPECACHE_LT_OPR | TYPECACHE_EQ_OPR);
	*atttyptype = typcache->typtype;
	*eq_opr = typcache->eq_opr;
	*lt_opr = typcache->lt_opr;

	/*
	 * Special case: collation for tsvector is DEFAULT_COLLATION_OID. See
	 * compute_tsvector_stats().
	 */
	if (*atttypid == TSVECTOROID)
		*atttypcoll = DEFAULT_COLLATION_OID;

	relation_close(rel, NoLock);
}

/*
 * ============================================================================
 * 【中文注释】statatt_get_elem_type —— 推导"容器类型"的元素类型
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对于数组/向量等"含子元素"的类型，推导其元素类型及元素相等操作符。用于
 *   MCELEM（最常用元素）与 DECHIST（元素个数直方图）这两类统计。
 *
 * 参数：
 *   atttypid   - 输入：容器类型 OID（来自 statatt_get_type()）。
 *   atttyptype - 输入：类型分类。
 *   elemtypid  - 输出：元素类型 OID。
 *   elem_eq_opr- 输出：元素相等操作符 OID。
 *
 * 返回值：
 *   bool - true 成功；false 无法确定元素类型/操作符。
 *
 * 设计思想：
 *   1. tsvector 特例：其"元素"视为 text（与 compute_tsvector_stats() 一致）。
 *   2. 其余情况用 get_base_element_type() 穿透 domain 得到底层元素类型。
 *   3. 元素类型不存在（非容器类型）或找不到相等操作符时返回 false。
 * ============================================================================
 */
bool
statatt_get_elem_type(Oid atttypid, char atttyptype,
					  Oid *elemtypid, Oid *elem_eq_opr)
{
	TypeCacheEntry *elemtypcache;

	if (atttypid == TSVECTOROID)
	{
		/*
		 * Special case: element type for tsvector is text. See
		 * compute_tsvector_stats().
		 */
		*elemtypid = TEXTOID;
	}
	else
	{
		/* find underlying element type through any domain */
		*elemtypid = get_base_element_type(atttypid);
	}

	if (!OidIsValid(*elemtypid))
		return false;

	/* finds the right operator even if elemtypid is a domain */
	elemtypcache = lookup_type_cache(*elemtypid, TYPECACHE_EQ_OPR);
	if (!OidIsValid(elemtypcache->eq_opr))
		return false;

	*elem_eq_opr = elemtypcache->eq_opr;

	return true;
}

/*
 * ============================================================================
 * 【中文注释】statatt_build_stavalues —— 用文本输入构建统计值数组
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把用户以 text 形式提供的数组字面量（如 '{1,2,3}'），通过指定类型的数组输入
 *   函数解析成一个 ArrayType Datum，作为 pg_statistic 的 stavalues 列值。
 *
 * 参数：
 *   staname  - 参数名（仅用于报错信息，如 "most_common_vals"）。
 *   array_in - 已初始化的 array_in 函数信息（FmgrInfo）。
 *   d        - 输入的 text Datum。
 *   typid    - 数组元素类型 OID（来自 statatt_get_type()）。
 *   typmod   - 元素 typmod。
 *   ok       - 输出：true 表示解析成功；false 表示解析出错或结果非法（已发
 *              WARNING）。
 *
 * 返回值：
 *   Datum - 成功时返回 ArrayType；失败返回 (Datum) 0。
 *
 * 设计思想：
 *   1. 用 InputFunctionCallSafe() 进行"安全"输入转换：出错时不直接抛 ERROR，而是
 *      捕获 ErrorSaveContext 里的错误、把级别降为 WARNING 再抛出，由调用方决定
 *      是否放弃该项统计（保证单个统计项失败不影响其它项）。
 *   2. 结果必须是"一维数组"且"不含 NULL 元素"，否则发 WARNING 并返回失败。
 *      （这些是 pg_statistic 对 stavalues 的格式要求。）
 * ============================================================================
 */
Datum
statatt_build_stavalues(const char *staname, FmgrInfo *array_in, Datum d, Oid typid,
						int32 typmod, bool *ok)
{
	char	   *s;
	Datum		result;
	ErrorSaveContext escontext = {T_ErrorSaveContext};

	escontext.details_wanted = true;

	s = TextDatumGetCString(d);

	if (!InputFunctionCallSafe(array_in, s, typid, typmod,
							   (Node *) &escontext, &result))
	{
		pfree(s);
		escontext.error_data->elevel = WARNING;
		ThrowErrorData(escontext.error_data);
		*ok = false;
		return (Datum) 0;
	}

	pfree(s);

	if (ARR_NDIM(DatumGetArrayTypeP(result)) != 1)
	{
		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("\"%s\" must be a one-dimensional array", staname)));
		*ok = false;
		return (Datum) 0;
	}

	if (array_contains_nulls(DatumGetArrayTypeP(result)))
	{
		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("\"%s\" array must not contain null values", staname)));
		*ok = false;
		return (Datum) 0;
	}

	*ok = true;

	return result;
}

/*
 * ============================================================================
 * 【中文注释】statatt_set_slot —— 把某类统计写入 pg_statistic 的 stakind 槽位
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在 values/nulls/replaces 数组中定位某个 stakind 对应的槽位（pg_statistic 共有
 *   STATISTIC_NUM_SLOTS 组 stakind/staop/stacoll/stanumbers/stavalues），并写入
 *   stakind 标识、排序规则、操作符以及该统计类的数值/值数组。若该 stakind 已存在
 *   则就地覆盖，否则占用第一个空槽位。
 *
 * 参数：
 *   values / nulls / replaces - 目标 pg_statistic 列数组。
 *   stakind   - 统计种类编号（STATISTIC_KIND_*，如 MCV=1、HISTOGRAM=2）。
 *   staop     - 该统计关联的操作符 OID（如相等/小于操作符；扩展类型可自由选择）。
 *   stacoll   - 排序规则 OID。
 *   stanumbers / stanumbers_isnull - 数值数组值及是否 NULL。
 *   stavalues / stavalues_isnull   - 值数组值及是否 NULL。
 *
 * 返回值：无（槽位满时 ERROR）。
 *
 * 设计思想：
 *   1. 顺序扫描各槽位，先记录第一个空槽位（stakind==0），若找到与 stakind 相同
 *      的已有槽位则用之；都没有再退回用第一个空槽位；若连空槽位都没有，报
 *      "max statistics slots exceeded"。
 *   2. 更新时采用"值不同才置 replaces=true"的懒策略，减少不必要的写列。
 *   3. stakind 为 0 表示"未使用"。核心统计的 staop 由调用方根据类型推导或硬编码；
 *      扩展类型的统计不受 STATISTIC_KIND_* 约束。
 * ============================================================================
 */
void
statatt_set_slot(Datum *values, bool *nulls, bool *replaces,
				 int16 stakind, Oid staop, Oid stacoll,
				 Datum stanumbers, bool stanumbers_isnull,
				 Datum stavalues, bool stavalues_isnull)
{
	int			slotidx;
	int			first_empty = -1;
	AttrNumber	stakind_attnum;
	AttrNumber	staop_attnum;
	AttrNumber	stacoll_attnum;

	/* find existing slot with given stakind */
	for (slotidx = 0; slotidx < STATISTIC_NUM_SLOTS; slotidx++)
	{
		stakind_attnum = Anum_pg_statistic_stakind1 - 1 + slotidx;

		if (first_empty < 0 &&
			DatumGetInt16(values[stakind_attnum]) == 0)
			first_empty = slotidx;
		if (DatumGetInt16(values[stakind_attnum]) == stakind)
			break;
	}

	if (slotidx >= STATISTIC_NUM_SLOTS && first_empty >= 0)
		slotidx = first_empty;

	if (slotidx >= STATISTIC_NUM_SLOTS)
		ereport(ERROR,
				(errmsg("maximum number of statistics slots exceeded: %d",
						slotidx + 1)));

	stakind_attnum = Anum_pg_statistic_stakind1 - 1 + slotidx;
	staop_attnum = Anum_pg_statistic_staop1 - 1 + slotidx;
	stacoll_attnum = Anum_pg_statistic_stacoll1 - 1 + slotidx;

	if (DatumGetInt16(values[stakind_attnum]) != stakind)
	{
		values[stakind_attnum] = Int16GetDatum(stakind);
		replaces[stakind_attnum] = true;
	}
	if (DatumGetObjectId(values[staop_attnum]) != staop)
	{
		values[staop_attnum] = ObjectIdGetDatum(staop);
		replaces[staop_attnum] = true;
	}
	if (DatumGetObjectId(values[stacoll_attnum]) != stacoll)
	{
		values[stacoll_attnum] = ObjectIdGetDatum(stacoll);
		replaces[stacoll_attnum] = true;
	}
	if (!stanumbers_isnull)
	{
		values[Anum_pg_statistic_stanumbers1 - 1 + slotidx] = stanumbers;
		nulls[Anum_pg_statistic_stanumbers1 - 1 + slotidx] = false;
		replaces[Anum_pg_statistic_stanumbers1 - 1 + slotidx] = true;
	}
	if (!stavalues_isnull)
	{
		values[Anum_pg_statistic_stavalues1 - 1 + slotidx] = stavalues;
		nulls[Anum_pg_statistic_stavalues1 - 1 + slotidx] = false;
		replaces[Anum_pg_statistic_stavalues1 - 1 + slotidx] = true;
	}
}

/*
 * ============================================================================
 * 【中文注释】statatt_init_empty_tuple —— 初始化一条"全默认"的 pg_statistic 记录
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 values/null s/replaces 三个数组初始化成一条"新记录"的默认形态：
 *   非空固定列（starelid/staattnum/stainherit）设为指定值，stanullfrac=0、
 *   stawidth=0、stadistinct=0，所有 stakind 槽位全部清空（stakind=0、staop=无效、
 *   stacoll=无效）。
 *
 * 参数：
 *   reloid   - 关系 OID（若无用传 InvalidOid）。
 *   attnum   - 列号（若无用传 InvalidAttrNumber）。
 *   inherited- 是否继承统计标志。
 *   values / nulls / replaces - 长度为 Natts_pg_statistic 的数组，由调用方分配。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   两种使用场景：
 *   1. 插入到 pg_statistic：reloid/attnum/inherited 有效；
 *   2. 作为 pg_statistic_ext_data.stxdexpr 数组元素（表达式统计）：三个标识列
 *      分别置 InvalidOid / InvalidAttrNumber / false。
 *   nulls 与 replaces 全部初始化为 true 后，再对"必须非空的列"逐个置 false。
 * ============================================================================
 */
void
statatt_init_empty_tuple(Oid reloid, int16 attnum, bool inherited,
						 Datum *values, bool *nulls, bool *replaces)
{
	memset(nulls, true, sizeof(bool) * Natts_pg_statistic);
	memset(replaces, true, sizeof(bool) * Natts_pg_statistic);

	/* This must initialize non-NULL attributes */
	values[Anum_pg_statistic_starelid - 1] = ObjectIdGetDatum(reloid);
	nulls[Anum_pg_statistic_starelid - 1] = false;
	values[Anum_pg_statistic_staattnum - 1] = Int16GetDatum(attnum);
	nulls[Anum_pg_statistic_staattnum - 1] = false;
	values[Anum_pg_statistic_stainherit - 1] = BoolGetDatum(inherited);
	nulls[Anum_pg_statistic_stainherit - 1] = false;

	values[Anum_pg_statistic_stanullfrac - 1] = DEFAULT_STATATT_NULL_FRAC;
	nulls[Anum_pg_statistic_stanullfrac - 1] = false;
	values[Anum_pg_statistic_stawidth - 1] = DEFAULT_STATATT_AVG_WIDTH;
	nulls[Anum_pg_statistic_stawidth - 1] = false;
	values[Anum_pg_statistic_stadistinct - 1] = DEFAULT_STATATT_N_DISTINCT;
	nulls[Anum_pg_statistic_stadistinct - 1] = false;

	/* initialize stakind, staop, and stacoll slots */
	for (int slotnum = 0; slotnum < STATISTIC_NUM_SLOTS; slotnum++)
	{
		values[Anum_pg_statistic_stakind1 + slotnum - 1] = (Datum) 0;
		nulls[Anum_pg_statistic_stakind1 + slotnum - 1] = false;
		values[Anum_pg_statistic_staop1 + slotnum - 1] = ObjectIdGetDatum(InvalidOid);
		nulls[Anum_pg_statistic_staop1 + slotnum - 1] = false;
		values[Anum_pg_statistic_stacoll1 + slotnum - 1] = ObjectIdGetDatum(InvalidOid);
		nulls[Anum_pg_statistic_stacoll1 + slotnum - 1] = false;
	}
}

/*
 * ============================================================================
 * 【中文注释】statatt_check_bounds_histogram —— 校验导入的范围边界直方图
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   校验用户导入的 BOUNDS_HISTOGRAM（范围类型边界直方图）是否与 ANALYZE 在
 *   compute_range_stats() 中生成的形态一致：数组中不能包含空范围，且每个范围的
 *   lower/upper 边界必须按升序排列。
 *
 * 参数：
 *   arrayval - 已解析出的 ArrayType Datum（元素为范围类型）。
 *
 * 返回值：
 *   bool - true 校验通过；false 不符合要求（已发 WARNING）。
 *
 * 设计思想：
 *   1. 元素类型理论上必为范围类型；若 lookup_type_cache 显示其不是范围
 *      （rngelemtype==NULL），则范围估计器根本不会使用该直方图，无需校验，直接
 *      返回 true（防御性设计）。
 *   2. 逐个反序列化范围（range_deserialize），检查 empty 标志，并利用
 *      range_cmp_bounds() 与前一项比较，确认 lower、upper 都单调不减。
 *   3. 由于 statatt_build_stavalues() 已保证数组一维且无 NULL，这里不必再查。
 * ============================================================================
 */
bool
statatt_check_bounds_histogram(Datum arrayval)
{
	ArrayType  *arr = DatumGetArrayTypeP(arrayval);
	Oid			rngtypid = ARR_ELEMTYPE(arr);
	TypeCacheEntry *typcache;
	int16		elmlen;
	bool		elmbyval;
	char		elmalign;
	Datum	   *elems;
	bool	   *nulls;
	int			nelems;
	RangeBound	prev_lower = {0};
	RangeBound	prev_upper = {0};

	typcache = lookup_type_cache(rngtypid, TYPECACHE_RANGE_INFO);

	/*
	 * The element type should always be a range type here.  This is
	 * defensive. If it isn't, the bounds histogram is never consulted by the
	 * range estimator, and there is nothing to verify.
	 */
	if (typcache->rngelemtype == NULL)
		return true;

	get_typlenbyvalalign(rngtypid, &elmlen, &elmbyval, &elmalign);
	deconstruct_array(arr, rngtypid, elmlen, elmbyval, elmalign,
					  &elems, &nulls, &nelems);

	for (int i = 0; i < nelems; i++)
	{
		RangeBound	lower,
					upper;
		bool		empty;

		/*
		 * NULL elements are already rejected by statatt_build_stavalues() and
		 * array_in_safe().
		 */
		range_deserialize(typcache, DatumGetRangeTypeP(elems[i]),
						  &lower, &upper, &empty);

		if (empty)
		{
			ereport(WARNING,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("\"%s\" must not contain empty ranges",
							"range_bounds_histogram")));
			return false;
		}

		if (i > 0 &&
			(range_cmp_bounds(typcache, &lower, &prev_lower) < 0 ||
			 range_cmp_bounds(typcache, &upper, &prev_upper) < 0))
		{
			ereport(WARNING,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("\"%s\" must have its lower and upper bounds sorted in ascending order",
							"range_bounds_histogram")));
			return false;
		}

		prev_lower = lower;
		prev_upper = upper;
	}

	return true;
}
