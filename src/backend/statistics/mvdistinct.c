/*-------------------------------------------------------------------------
 *
 * mvdistinct.c
 *	  POSTGRES multivariate ndistinct coefficients
 *
 * Estimating number of groups in a combination of columns (e.g. for GROUP BY)
 * is tricky, and the estimation error is often significant.

 * The multivariate ndistinct coefficients address this by storing ndistinct
 * estimates for combinations of the user-specified columns.  So for example
 * given a statistics object on three columns (a,b,c), this module estimates
 * and stores n-distinct for (a,b), (a,c), (b,c) and (a,b,c).  The per-column
 * estimates are already available in pg_statistic.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/statistics/mvdistinct.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <math.h>

#include "catalog/pg_statistic_ext.h"
#include "catalog/pg_statistic_ext_data.h"
#include "statistics/extended_stats_internal.h"
#include "utils/syscache.h"
#include "utils/typcache.h"
#include "varatt.h"

static double ndistinct_for_combination(double totalrows, StatsBuildData *data,
										int k, int *combination);
static double estimate_ndistinct(double totalrows, int numrows, int d, int f1);
static int	n_choose_k(int n, int k);
static int	num_combinations(int n);

/* size of the struct header fields (magic, type, nitems) */
#define SizeOfHeader		(3 * sizeof(uint32))

/* size of a serialized ndistinct item (coefficient, natts, atts) */
#define SizeOfItem(natts) \
	(sizeof(double) + sizeof(int) + (natts) * sizeof(AttrNumber))

/* minimal size of a ndistinct item (with two attributes) */
#define MinSizeOfItem	SizeOfItem(2)

/* minimal size of mvndistinct, when all items are minimal */
#define MinSizeOfItems(nitems)	\
	(SizeOfHeader + (nitems) * MinSizeOfItem)

/* Combination generator API */

/* internal state for generator of k-combinations of n elements */
typedef struct CombinationGenerator
{
	int			k;				/* size of the combination */
	int			n;				/* total number of elements */
	int			current;		/* index of the next combination to return */
	int			ncombinations;	/* number of combinations (size of array) */
	int		   *combinations;	/* array of pre-built combinations */
} CombinationGenerator;

static CombinationGenerator *generator_init(int n, int k);
static void generator_free(CombinationGenerator *state);
static int *generator_next(CombinationGenerator *state);
static void generate_combinations(CombinationGenerator *state);


/*
 * ============================================================================
 * 【中文注释】statext_ndistinct_build —— 计算多元统计对象的 n-distinct 系数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   基于采样数据，为统计对象所覆盖列的所有"组合"估算去重组数（ndistinct），
 *   生成并返回 MVNDistinct 结构。例如对 (a,b,c) 三列会生成 (a,b)、(a,c)、(b,c)、
 *   (a,b,c) 四个组合的系数；单列的去重数已经由普通 ANALYZE 存进 pg_statistic。
 *
 * 参数：
 *   totalrows - 表的估算总行数。
 *   data      - StatsBuildData：包含采样行数、每列的 Datum/空值数组、attnums、
 *               VacAttrStats 数组等（由 make_build_data() 提供）。
 *
 * 返回值：
 *   MVNDistinct* - 内存中的多元去重数结构（内含 nitems 个 MVNDistinctItem）。
 *
 * 设计思想：
 *   1. 组合数量 = 2^N - N - 1（去掉单列组合），见 num_combinations()。
 *   2. 对每个 k（2..N）用组合生成器枚举所有 k 元组合，把"索引"翻译回真实 attnum
 *      （表达式用负 attnum 表示）。
 *   3. 每个组合的去重数由 ndistinct_for_combination() 估算，使用的估计器与
 *      analyze.c 的 compute_scalar_stats() 完全相同（Duj1 估计器），保证单列与
 *      多列口径一致。
 *   4. 结构头部写入 magic/type/nitems，便于后续序列化与校验。
 * ============================================================================
 */
MVNDistinct *
statext_ndistinct_build(double totalrows, StatsBuildData *data)
{
	MVNDistinct *result;
	int			k;
	uint32		itemcnt;
	int			numattrs = data->nattnums;
	int			numcombs = num_combinations(numattrs);

	result = palloc(offsetof(MVNDistinct, items) +
					numcombs * sizeof(MVNDistinctItem));
	result->magic = STATS_NDISTINCT_MAGIC;
	result->type = STATS_NDISTINCT_TYPE_BASIC;
	result->nitems = numcombs;

	itemcnt = 0;
	for (k = 2; k <= numattrs; k++)
	{
		int		   *combination;
		CombinationGenerator *generator;

		/* generate combinations of K out of N elements */
		generator = generator_init(numattrs, k);

		while ((combination = generator_next(generator)))
		{
			MVNDistinctItem *item = &result->items[itemcnt];
			int			j;

			item->attributes = palloc_array(AttrNumber, k);
			item->nattributes = k;

			/* translate the indexes to attnums */
			for (j = 0; j < k; j++)
			{
				item->attributes[j] = data->attnums[combination[j]];

				Assert(AttributeNumberIsValid(item->attributes[j]));
			}

			item->ndistinct =
				ndistinct_for_combination(totalrows, data, k, combination);

			itemcnt++;
			Assert(itemcnt <= result->nitems);
		}

		generator_free(generator);
	}

	/* must consume exactly the whole output array */
	Assert(itemcnt == result->nitems);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】statext_ndistinct_load —— 从系统表加载 ndistinct 统计
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从 pg_statistic_ext_data 表的 stxdndistinct 列加载并反序列化某个统计对象的
 *   MVNDistinct。供规划器/相关代码在使用该统计前读取。
 *
 * 参数：
 *   mvoid - 统计对象 OID（pg_statistic_ext.oid）。
 *   inh   - 是否加载继承树版本（stxdinherit）。
 *
 * 返回值：
 *   MVNDistinct* - 反序列化后的结构。
 *
 * 设计思想：
 *   通过 syscache(STATEXTDATASTXOID) 按 (mvoid, inh) 精确查找 pg_statistic_ext_data
 *   元组；若该统计种类尚未构建（列为 NULL），报"not yet built"错误。之后调用
 *   statext_ndistinct_deserialize() 把磁盘 bytea 转成内存结构，并释放 syscache
 *   引用。
 * ============================================================================
 */
MVNDistinct *
statext_ndistinct_load(Oid mvoid, bool inh)
{
	MVNDistinct *result;
	bool		isnull;
	Datum		ndist;
	HeapTuple	htup;

	htup = SearchSysCache2(STATEXTDATASTXOID,
						   ObjectIdGetDatum(mvoid), BoolGetDatum(inh));
	if (!HeapTupleIsValid(htup))
		elog(ERROR, "cache lookup failed for statistics object %u", mvoid);

	ndist = SysCacheGetAttr(STATEXTDATASTXOID, htup,
							Anum_pg_statistic_ext_data_stxdndistinct, &isnull);
	if (isnull)
		elog(ERROR,
			 "requested statistics kind \"%c\" is not yet built for statistics object %u",
			 STATS_EXT_NDISTINCT, mvoid);

	result = statext_ndistinct_deserialize(DatumGetByteaPP(ndist));

	ReleaseSysCache(htup);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】statext_ndistinct_serialize —— 序列化 MVNDistinct 为磁盘格式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把内存中的 MVNDistinct 结构编码成一个 bytea（varlena），以便存入
 *   pg_statistic_ext_data.stxdndistinct。
 *
 * 参数：
 *   ndistinct - 要序列化的内存结构。
 *
 * 返回值：
 *   bytea* - 序列化结果。
 *
 * 设计思想：
 *   磁盘布局（紧凑、不关心对齐）：
 *     [ varlena 头 | magic(uint32) | type(uint32) | nitems(uint32) ]
 *     然后对每个 item：[ ndistinct(double) | nattributes(int) |
 *                        attnums(AttrNumber*nattributes) ]
 *   序列化前先计算总长（SizeOfItem 宏），分配一次内存，逐字段 memcpy；并用
 *   Assert 保证写入字节数与预估完全一致（防溢出/防写穿）。
 * ============================================================================
 */
bytea *
statext_ndistinct_serialize(MVNDistinct *ndistinct)
{
	bytea	   *output;
	char	   *tmp;
	Size		len;

	Assert(ndistinct->magic == STATS_NDISTINCT_MAGIC);
	Assert(ndistinct->type == STATS_NDISTINCT_TYPE_BASIC);

	/*
	 * Base size is size of scalar fields in the struct, plus one base struct
	 * for each item, including number of items for each.
	 */
	len = VARHDRSZ + SizeOfHeader;

	/* and also include space for the actual attribute numbers */
	for (uint32 i = 0; i < ndistinct->nitems; i++)
	{
		int			nmembers;

		nmembers = ndistinct->items[i].nattributes;
		Assert(nmembers >= 2);

		len += SizeOfItem(nmembers);
	}

	output = (bytea *) palloc(len);
	SET_VARSIZE(output, len);

	tmp = VARDATA(output);

	/* Store the base struct values (magic, type, nitems) */
	memcpy(tmp, &ndistinct->magic, sizeof(uint32));
	tmp += sizeof(uint32);
	memcpy(tmp, &ndistinct->type, sizeof(uint32));
	tmp += sizeof(uint32);
	memcpy(tmp, &ndistinct->nitems, sizeof(uint32));
	tmp += sizeof(uint32);

	/*
	 * store number of attributes and attribute numbers for each entry
	 */
	for (uint32 i = 0; i < ndistinct->nitems; i++)
	{
		MVNDistinctItem item = ndistinct->items[i];
		int			nmembers = item.nattributes;

		memcpy(tmp, &item.ndistinct, sizeof(double));
		tmp += sizeof(double);
		memcpy(tmp, &nmembers, sizeof(int));
		tmp += sizeof(int);

		memcpy(tmp, item.attributes, sizeof(AttrNumber) * nmembers);
		tmp += nmembers * sizeof(AttrNumber);

		/* protect against overflows */
		Assert(tmp <= ((char *) output + len));
	}

	/* check we used exactly the expected space */
	Assert(tmp == ((char *) output + len));

	return output;
}

/*
 * ============================================================================
 * 【中文注释】statext_ndistinct_deserialize —— 反序列化磁盘格式为 MVNDistinct
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 statext_ndistinct_serialize() 互逆：把 bytea 解码回内存 MVNDistinct 结构。
 *
 * 参数：
 *   data - 磁盘 bytea。
 *
 * 返回值：
 *   MVNDistinct* - 内存结构（含为每个 item 单独 palloc 的 attributes 数组），
 *                  数据为 NULL 时返回 NULL。
 *
 * 设计思想：
 *   健壮性优先：
 *   1. 先检查长度下限（至少能容纳头部），再读 header 并校验 magic/type/nitems 的
 *      合法性；nitems 非零。
 *   2. 再校验整体最小长度（MinSizeOfItems），防止伪造的短 bytea。
 *   3. 分配结构后逐 item 读 ndistinct/nattributes/attnums，并断言 nattributes 在
 *      [2, STATS_MAX_DIMENSIONS] 内。
 *   4. 全程 Assert"指针不越过 bytea 末尾、最后恰好消费完整段数据"。
 * ============================================================================
 */
MVNDistinct *
statext_ndistinct_deserialize(bytea *data)
{
	Size		minimum_size;
	MVNDistinct ndist;
	MVNDistinct *ndistinct;
	char	   *tmp;

	if (data == NULL)
		return NULL;

	/* we expect at least the basic fields of MVNDistinct struct */
	if (VARSIZE_ANY_EXHDR(data) < SizeOfHeader)
		elog(ERROR, "invalid MVNDistinct size %zu (expected at least %zu)",
			 VARSIZE_ANY_EXHDR(data), SizeOfHeader);

	/* initialize pointer to the data part (skip the varlena header) */
	tmp = VARDATA_ANY(data);

	/* read the header fields and perform basic sanity checks */
	memcpy(&ndist.magic, tmp, sizeof(uint32));
	tmp += sizeof(uint32);
	memcpy(&ndist.type, tmp, sizeof(uint32));
	tmp += sizeof(uint32);
	memcpy(&ndist.nitems, tmp, sizeof(uint32));
	tmp += sizeof(uint32);

	if (ndist.magic != STATS_NDISTINCT_MAGIC)
		elog(ERROR, "invalid ndistinct magic %08x (expected %08x)",
			 ndist.magic, STATS_NDISTINCT_MAGIC);
	if (ndist.type != STATS_NDISTINCT_TYPE_BASIC)
		elog(ERROR, "invalid ndistinct type %d (expected %d)",
			 ndist.type, STATS_NDISTINCT_TYPE_BASIC);
	if (ndist.nitems == 0)
		elog(ERROR, "invalid zero-length item array in MVNDistinct");

	/* what minimum bytea size do we expect for those parameters */
	minimum_size = MinSizeOfItems(ndist.nitems);
	if (VARSIZE_ANY_EXHDR(data) < minimum_size)
		elog(ERROR, "invalid MVNDistinct size %zu (expected at least %zu)",
			 VARSIZE_ANY_EXHDR(data), minimum_size);

	/*
	 * Allocate space for the ndistinct items (no space for each item's
	 * attnos: those live in bitmapsets allocated separately)
	 */
	ndistinct = palloc0(MAXALIGN(offsetof(MVNDistinct, items)) +
						(ndist.nitems * sizeof(MVNDistinctItem)));
	ndistinct->magic = ndist.magic;
	ndistinct->type = ndist.type;
	ndistinct->nitems = ndist.nitems;

	for (uint32 i = 0; i < ndistinct->nitems; i++)
	{
		MVNDistinctItem *item = &ndistinct->items[i];

		/* ndistinct value */
		memcpy(&item->ndistinct, tmp, sizeof(double));
		tmp += sizeof(double);

		/* number of attributes */
		memcpy(&item->nattributes, tmp, sizeof(int));
		tmp += sizeof(int);
		Assert((item->nattributes >= 2) && (item->nattributes <= STATS_MAX_DIMENSIONS));

		item->attributes
			= (AttrNumber *) palloc(item->nattributes * sizeof(AttrNumber));

		memcpy(item->attributes, tmp, sizeof(AttrNumber) * item->nattributes);
		tmp += sizeof(AttrNumber) * item->nattributes;

		/* still within the bytea */
		Assert(tmp <= ((char *) data + VARSIZE_ANY(data)));
	}

	/* we should have consumed the whole bytea exactly */
	Assert(tmp == ((char *) data + VARSIZE_ANY(data)));

	return ndistinct;
}

/*
 * ============================================================================
 * 【中文注释】statext_ndistinct_free —— 释放 MVNDistinct 结构
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   释放一个 MVNDistinct 及其所有 item 的 attributes 数组。
 *
 * 参数：
 *   ndistinct - 要释放的结构。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   反序列化时每个 item 的 attributes 是独立 palloc 的，因此需要逐 item 释放；
 *   结构体本身最后释放。
 * ============================================================================
 */
void
statext_ndistinct_free(MVNDistinct *ndistinct)
{
	for (uint32 i = 0; i < ndistinct->nitems; i++)
		pfree(ndistinct->items[i].attributes);
	pfree(ndistinct);
}

/*
 * ============================================================================
 * 【中文注释】statext_ndistinct_validate —— 校验 ndistinct 与统计对象定义一致
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   校验导入的 MVNDistinct 里所有 item 的 attnums 是否与该统计对象（stxkeys +
 *   numexprs）的定义吻合。用于 pg_restore_extended_stats() 导入数据时防止
 *   提交与对象定义不匹配的统计。
 *
 * 参数：
 *   ndistinct - 待校验的 ndistinct 结构。
 *   stxkeys   - 统计对象覆盖的普通列（int2vector）。
 *   numexprs  - 统计对象中的表达式个数。
 *   elevel    - 校验失败时使用的错误级别（WARNING 或 ERROR）。
 *
 * 返回值：
 *   bool - true 合法；false 发现非法 attnum（已按 elevel 报错）。
 *
 * 设计思想：
 *   规则：正 attnum 必须出现在 stxkeys 中；负 attnum 代表表达式序号，其下界为
 *   (0 - numexprs)。任一 item 的任一属性违反规则即判整体非法，返回 false。
 * ============================================================================
 */
bool
statext_ndistinct_validate(const MVNDistinct *ndistinct,
						   const int2vector *stxkeys,
						   int numexprs, int elevel)
{
	int			attnum_expr_lowbound = 0 - numexprs;

	/* Scan through each MVNDistinct entry */
	for (uint32 i = 0; i < ndistinct->nitems; i++)
	{
		MVNDistinctItem item = ndistinct->items[i];

		/*
		 * Cross-check each attribute in a MVNDistinct entry with the extended
		 * stats object definition.
		 */
		for (int j = 0; j < item.nattributes; j++)
		{
			AttrNumber	attnum = item.attributes[j];
			bool		ok = false;

			if (attnum > 0)
			{
				/* attribute number in stxkeys */
				for (int k = 0; k < stxkeys->dim1; k++)
				{
					if (attnum == stxkeys->values[k])
					{
						ok = true;
						break;
					}
				}
			}
			else if ((attnum < 0) && (attnum >= attnum_expr_lowbound))
			{
				/* attribute number for an expression */
				ok = true;
			}

			if (!ok)
			{
				ereport(elevel,
						(errcode(ERRCODE_INVALID_TEXT_REPRESENTATION),
						 errmsg("could not validate \"%s\" object: invalid attribute number %d found",
								"pg_ndistinct", attnum)));
				return false;
			}
		}
	}

	return true;
}

/*
 * ============================================================================
 * 【中文注释】ndistinct_for_combination —— 估算某一列组合的去重数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对一个具体的 k 元列组合，基于采样数据估算去重数。方法：把采样行按该组合各列
 *   排序，统计"不同组合值的个数 d"和"只出现过一次的组合值个数 f1"，再套用
 *   estimate_ndistinct()（Duj1 估计器）外推到全表。
 *
 * 参数：
 *   totalrows  - 表估算总行数。
 *   data       - 采样数据（StatsBuildData）。
 *   k          - 组合大小（列数）。
 *   combination- 长度为 k 的数组，元素是"该组合对应的列在 data->attnums 中的索引"。
 *
 * 返回值：
 *   double - 该组合的去重数估算值（已取整）。
 *
 * 设计思想：
 *   1. 为 k 列构建多列排序支持 multi_sort_init()/multi_sort_add_dimension()，
 *      排序操作符用各列默认的小于操作符与排序规则。
 *   2. 把采样行的各列数据分别拷贝到 values[]/isnull[] 二维数组（行×列），组成
 *      SortItem 数组后 qsort 一次排序，再扫描相邻元素即可统计不同组数 d 与 f1。
 *      ——排序后再统计，避免了哈希，复杂度 O(n log n)。
 *   3. 估计公式（Duj1）：ndistinct = n*d / (n - f1 + f1*n/N)，其中 n=样本行数、
 *      N=totalrows。该公式是 analyze.c 计算单列 stadistinct 的同一公式，保证
 *      多列估计与单列口径一致。
 * ============================================================================
 */
static double
ndistinct_for_combination(double totalrows, StatsBuildData *data,
						  int k, int *combination)
{
	int			i,
				j;
	int			f1,
				cnt,
				d;
	bool	   *isnull;
	Datum	   *values;
	SortItem   *items;
	MultiSortSupport mss;
	int			numrows = data->numrows;

	mss = multi_sort_init(k);

	/*
	 * In order to determine the number of distinct elements, create separate
	 * values[]/isnull[] arrays with all the data we have, then sort them
	 * using the specified column combination as dimensions.  We could try to
	 * sort in place, but it'd probably be more complex and bug-prone.
	 */
	items = palloc_array(SortItem, numrows);
	values = palloc0_array(Datum, numrows * k);
	isnull = palloc0_array(bool, numrows * k);

	for (i = 0; i < numrows; i++)
	{
		items[i].values = &values[i * k];
		items[i].isnull = &isnull[i * k];
	}

	/*
	 * For each dimension, set up sort-support and fill in the values from the
	 * sample data.
	 *
	 * We use the column data types' default sort operators and collations;
	 * perhaps at some point it'd be worth using column-specific collations?
	 */
	for (i = 0; i < k; i++)
	{
		Oid			typid;
		TypeCacheEntry *type;
		Oid			collid = InvalidOid;
		VacAttrStats *colstat = data->stats[combination[i]];

		typid = colstat->attrtypid;
		collid = colstat->attrcollid;

		type = lookup_type_cache(typid, TYPECACHE_LT_OPR);
		if (type->lt_opr == InvalidOid) /* shouldn't happen */
			elog(ERROR, "cache lookup failed for ordering operator for type %u",
				 typid);

		/* prepare the sort function for this dimension */
		multi_sort_add_dimension(mss, i, type->lt_opr, collid);

		/* accumulate all the data for this dimension into the arrays */
		for (j = 0; j < numrows; j++)
		{
			items[j].values[i] = data->values[combination[i]][j];
			items[j].isnull[i] = data->nulls[combination[i]][j];
		}
	}

	/* We can sort the array now ... */
	qsort_interruptible(items, numrows, sizeof(SortItem),
						multi_sort_compare, mss);

	/* ... and count the number of distinct combinations */

	f1 = 0;
	cnt = 1;
	d = 1;
	for (i = 1; i < numrows; i++)
	{
		if (multi_sort_compare(&items[i], &items[i - 1], mss) != 0)
		{
			if (cnt == 1)
				f1 += 1;

			d++;
			cnt = 0;
		}

		cnt += 1;
	}

	if (cnt == 1)
		f1 += 1;

	return estimate_ndistinct(totalrows, numrows, d, f1);
}

/*
 * ============================================================================
 * 【中文注释】estimate_ndistinct —— Duj1 去重数估计器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   用 Duj1（Dujardin-1）公式根据样本估算总体去重数：由样本中不同值个数 d、
 *   仅出现一次的值个数 f1、样本行数 numrows、总体行数 totalrows 推算出总体
 *   去重数。这是 analyze.c 的单列统计使用的同一个估计器。
 *
 * 参数：
 *   totalrows - 总体行数 N。
 *   numrows   - 样本行数 n。
 *   d         - 样本中不同值个数。
 *   f1        - 样本中恰好出现一次的值个数。
 *
 * 返回值：
 *   double - 估算的去重数（四舍五入取整）。
 *
 * 设计思想：
 *   公式：ndistinct = n*d / (n - f1 + f1*n/N)。
 *   直观含义：f1 个"稀有值"很可能在未采样部分还有同类，n*d 近似于"如果每个样本
 *   值都代表唯一的总体值，总体去重数应为多少"，分母用 f1 修正"稀有值低估"的问题。
 *   最后把结果夹到 [d, totalrows] 并做四舍五入，防止除零/舍入误差产生荒谬结果。
 * ============================================================================
 */
static double
estimate_ndistinct(double totalrows, int numrows, int d, int f1)
{
	double		numer,
				denom,
				ndistinct;

	numer = (double) numrows * (double) d;

	denom = (double) (numrows - f1) +
		(double) f1 * (double) numrows / totalrows;

	ndistinct = numer / denom;

	/* Clamp to sane range in case of roundoff error */
	if (ndistinct < (double) d)
		ndistinct = (double) d;

	if (ndistinct > totalrows)
		ndistinct = totalrows;

	return floor(ndistinct + 0.5);
}

/*
 * ============================================================================
 * 【中文注释】n_choose_k —— 计算组合数 C(n,k)
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   计算二项式系数 C(n,k)（k 元组合数），算法兼顾效率与防溢出。
 *
 * 参数：
 *   n, k - 非负整数，要求 k>0 且 n>=k。
 *
 * 返回值：
 *   int - C(n,k) 的值。
 *
 * 设计思想：
 *   1. 利用对称性 C(n,k)=C(n,n-k)，先取 k=min(k,n-k) 减少循环次数。
 *   2. 采用累乘/累除交替：r = r*(n--)/d。每次先乘后除能保持中间结果接近最终值，
 *      降低溢出风险（相比先算 n! 再除）。
 * ============================================================================
 */
static int
n_choose_k(int n, int k)
{
	int			d,
				r;

	Assert((k > 0) && (n >= k));

	/* use symmetry of the binomial coefficients */
	k = Min(k, n - k);

	r = 1;
	for (d = 1; d <= k; ++d)
	{
		r *= n--;
		r /= d;
	}

	return r;
}

/*
 * ============================================================================
 * 【中文注释】num_combinations —— 计算"非平凡"组合的数量
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   n 个元素所有子集的数量是 2^n，去掉空集（1 个）和所有单元素子集（n 个），
 *   剩下的就是"至少 2 元"的组合数，即多元统计需要覆盖的组合数。
 *
 * 参数：
 *   n - 列/属性总数。
 *
 * 返回值：
 *   int - 2^n - n - 1。
 *
 * 设计思想：
 *   使用位运算 1<<n 快速求 2 的幂。
 * ============================================================================
 */
static int
num_combinations(int n)
{
	return (1 << n) - (n + 1);
}

/*
 * ============================================================================
 * 【中文注释】generator_init —— 初始化组合生成器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   创建并初始化一个"在 0..N 中枚举所有 k 元组合"的生成器，并把所有组合预先
 *   生成好存进内部数组。
 *
 * 参数：
 *   n - 元素总数。
 *   k - 组合大小，要求 n>=k>0。
 *
 * 返回值：
 *   CombinationGenerator* - 生成器状态。
 *
 * 设计思想：
 *   一次性预生成所有组合（字典序），比在 generator_next() 里现场生成更简单。
 *   内存布局：状态结构 + 一个能容纳 ncombinations*k 个 int 的连续数组。
 *   生成后断言 current==ncombinations，然后把 current 重置为 0 以便从头遍历。
 * ============================================================================
 */
static CombinationGenerator *
generator_init(int n, int k)
{
	CombinationGenerator *state;

	Assert((n >= k) && (k > 0));

	/* allocate the generator state as a single chunk of memory */
	state = palloc_object(CombinationGenerator);

	state->ncombinations = n_choose_k(n, k);

	/* pre-allocate space for all combinations */
	state->combinations = palloc_array(int, k * state->ncombinations);

	state->current = 0;
	state->k = k;
	state->n = n;

	/* now actually pre-generate all the combinations of K elements */
	generate_combinations(state);

	/* make sure we got the expected number of combinations */
	Assert(state->current == state->ncombinations);

	/* reset the number, so we start with the first one */
	state->current = 0;

	return state;
}

/*
 * ============================================================================
 * 【中文注释】generator_next —— 取下一个组合
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从预生成数组里返回下一个 k 元组合（数组下标形式，元素范围 0..N-1）；
 *   耗尽时返回 NULL。
 *
 * 参数：
 *   state - 生成器状态。
 *
 * 返回值：
 *   int* - 指向长度为 k 的组合数组（位于 state->combinations 内，无需释放）；
 *          无更多组合时返回 NULL。
 *
 * 设计思想：
 *   组合数组是连续排布的，第 current 个组合的起始位置即
 *   &combinations[k*current]。
 * ============================================================================
 */
static int *
generator_next(CombinationGenerator *state)
{
	if (state->current == state->ncombinations)
		return NULL;

	return &state->combinations[state->k * state->current++];
}

/*
 * ============================================================================
 * 【中文注释】generator_free —— 释放组合生成器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   释放生成器内部状态（组合数组与状态结构本身）。
 *
 * 参数：
 *   state - 生成器状态。
 *
 * 返回值：无。
 * ============================================================================
 */
static void
generator_free(CombinationGenerator *state)
{
	pfree(state->combinations);
	pfree(state);
}

/*
 * ============================================================================
 * 【中文注释】generate_combinations_recurse —— 递归生成组合（核心）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   给定已确定的组合前缀（前 index 个元素），递归填充后续元素，生成所有可能的
 *   k 元组合。组合按字典序（元素严格递增）生成，从而避免同一组合的排列被重复
 *   计入。
 *
 * 参数：
 *   state   - 生成器状态。
 *   index   - 当前要确定第几个元素（0 基）。
 *   start   - 当前元素可取的最小值（保证严格递增，即下一个元素必须大于前一个）。
 *   current - 正在构造的组合的临时缓冲（长度为 k）。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   经典回溯：若 index<k 则对 i 从 start 到 n-1 递归填充；若 index==k 说明组合
 *   完整，memcpy 进预分配数组并递增 current。递增枚举 + 起始值约束保证了字典序
 *   且无重复、无缺失。
 * ============================================================================
 */
static void
generate_combinations_recurse(CombinationGenerator *state,
							  int index, int start, int *current)
{
	/* If we haven't filled all the elements, simply recurse. */
	if (index < state->k)
	{
		int			i;

		/*
		 * The values have to be in ascending order, so make sure we start
		 * with the value passed by parameter.
		 */

		for (i = start; i < state->n; i++)
		{
			current[index] = i;
			generate_combinations_recurse(state, (index + 1), (i + 1), current);
		}

		return;
	}
	else
	{
		/* we got a valid combination, add it to the array */
		memcpy(&state->combinations[(state->k * state->current)],
			   current, state->k * sizeof(int));
		state->current++;
	}
}

/*
 * ============================================================================
 * 【中文注释】generate_combinations —— 生成 N 个元素的所有 k 元组合
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   驱动 generate_combinations_recurse() 生成全部 k 元组合的入口：分配临时缓冲，
 *   从 (index=0, start=0) 开始递归。
 *
 * 参数：
 *   state - 生成器状态（内含 k、n、组合存储数组）。
 *
 * 返回值：无。
 * ============================================================================
 */
static void
generate_combinations(CombinationGenerator *state)
{
	int		   *current = palloc0_array(int, state->k);

	generate_combinations_recurse(state, 0, 0, current);

	pfree(current);
}
