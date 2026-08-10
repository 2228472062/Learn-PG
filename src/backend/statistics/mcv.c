/*-------------------------------------------------------------------------
 *
 * mcv.c
 *	  POSTGRES multivariate MCV lists
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/statistics/mcv.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "catalog/pg_statistic_ext.h"
#include "catalog/pg_statistic_ext_data.h"
#include "fmgr.h"
#include "funcapi.h"
#include "nodes/nodeFuncs.h"
#include "statistics/extended_stats_internal.h"
#include "statistics/statistics.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/fmgrprotos.h"
#include "utils/lsyscache.h"
#include "utils/selfuncs.h"
#include "utils/syscache.h"
#include "utils/typcache.h"

/*
 * Computes size of a serialized MCV item, depending on the number of
 * dimensions (columns) the statistic is defined on. The datum values are
 * stored in a separate array (deduplicated, to minimize the size), and
 * so the serialized items only store uint16 indexes into that array.
 *
 * Each serialized item stores (in this order):
 *
 * - indexes to values	  (ndim * sizeof(uint16))
 * - null flags			  (ndim * sizeof(bool))
 * - frequency			  (sizeof(double))
 * - base_frequency		  (sizeof(double))
 *
 * There is no alignment padding within an MCV item.
 * So in total each MCV item requires this many bytes:
 *
 *	 ndim * (sizeof(uint16) + sizeof(bool)) + 2 * sizeof(double)
 */
#define ITEM_SIZE(ndims)	\
	((ndims) * (sizeof(uint16) + sizeof(bool)) + 2 * sizeof(double))

/*
 * Used to compute size of serialized MCV list representation.
 */
#define MinSizeOfMCVList		\
	(VARHDRSZ + sizeof(uint32) * 3 + sizeof(AttrNumber))

/*
 * Size of the serialized MCV list, excluding the space needed for
 * deduplicated per-dimension values. The macro is meant to be used
 * when it's not yet safe to access the serialized info about amount
 * of data for each column.
 */
#define SizeOfMCVList(ndims,nitems)	\
	((MinSizeOfMCVList + sizeof(Oid) * (ndims)) + \
	 ((ndims) * sizeof(DimensionInfo)) + \
	 ((nitems) * ITEM_SIZE(ndims)))

static MultiSortSupport build_mss(StatsBuildData *data);

static SortItem *build_distinct_groups(int numrows, SortItem *items,
									   MultiSortSupport mss, int *ndistinct);

static SortItem **build_column_frequencies(SortItem *groups, int ngroups,
										   MultiSortSupport mss, int *ncounts);

static int	count_distinct_groups(int numrows, SortItem *items,
								  MultiSortSupport mss);

/*
 * Compute new value for bitmap item, considering whether it's used for
 * clauses connected by AND/OR.
 */
#define RESULT_MERGE(value, is_or, match) \
	((is_or) ? ((value) || (match)) : ((value) && (match)))

/*
 * When processing a list of clauses, the bitmap item may get set to a value
 * such that additional clauses can't change it. For example, when processing
 * a list of clauses connected to AND, as soon as the item gets set to 'false'
 * then it'll remain like that. Similarly clauses connected by OR and 'true'.
 *
 * Returns true when the value in the bitmap can't change no matter how the
 * remaining clauses are evaluated.
 */
#define RESULT_IS_FINAL(value, is_or)	((is_or) ? (value) : (!(value)))

/*
 * ============================================================================
 * 【中文注释】get_mincount_for_mcv_list —— 计算纳入 MCV 列表所需的最小出现次数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   决定一个值在采样数据中至少要出现多少次，才值得把它纳入多元 MCV 列表。这是
 *   MCV 列表的"入选阈值"。
 *
 * 参数：
 *   samplerows - 样本行数 n。
 *   totalrows  - 全表估算行数 N。
 *
 * 返回值：
 *   double - 最小出现次数阈值 cnt（出现次数大于该阈值的组才进入 MCV 列表）。
 *
 * 设计思想：
 *   1. 只保留在样本中"出现足够频繁"的值，这样把样本频率外推到全表才可靠。
 *      方法是对样本频率的相对标准误差设置上界，保证规划器基于 MCV 统计的估算
 *      足够准确。
 *   2. 无放回抽样下，某个值的样本频率服从超几何分布。经验法则：样本中至少出现
 *      10 次后，该分布可近似为正态分布，从而可套用标准误差分析。
 *      比例 p=cnt/n 的标准误差为
 *          SE = sqrt(p*(1-p)/n) * sqrt((N-n)/(N-1))
 *      第二项是有限总体校正因子。
 *   3. 要求相对标准误差 SE/p < 0.2（20%，经验上工作良好），反解得出现次数下界：
 *          cnt > n*(N-n) / (N-n+0.04*n*(N-1))
 *      该下界最大为 25；当 n→0 或 n→N 时趋于 0。n→0 实际不会发生（样本至少
 *      300 行）；n→N 意味着抽样了整个表，此时保留整个 MCV 列表（阈值=0）也合理，
 *      因此该公式对所有输入都适用。
 *   4. 另一视角：假设出现次数按比例放大到全表，总体计数 K=N*cnt/n，样本分布是
 *      参数为 (N,n,K) 的超几何分布；上述下界等价于要求该分布的“标准差 < 均值的
 *      20%”，即基于 MCV 统计产生的规划估计相对误差不会太大。
 * ============================================================================
 */
static double
get_mincount_for_mcv_list(int samplerows, double totalrows)
{
	double		n = samplerows;
	double		N = totalrows;
	double		numer,
				denom;

	numer = n * (N - n);
	denom = N - n + 0.04 * n * (N - 1);

	/* Guard against division by zero (possible if n = N = 1) */
	if (denom == 0.0)
		return 0.0;

	return numer / denom;
}

/*
 * ============================================================================
 * 【中文注释】statext_mcv_build —— 从采样数据构建多元 MCV 列表（顶层入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   这是构建多元 MCV（Most Common Values，最常见组合值）统计的入口函数。它把
 *   采样到的若干行数据按所有列组合排序、分组、筛选出高频的组合，最终生成 MCVList
 *   结构，供 ANALYZE 存入 pg_statistic_ext_data.stxdmcv。
 *
 * 参数：
 *   data      - 采样数据（StatsBuildData）：包含采样行数、各列 Datum/空值数组、
 *               attnums、VacAttrStats 数组等。
 *   totalrows - 全表估算行数。
 *   stattarget- 统计对象的目标数（该对象/列/系统默认三者取最小值），即 MCV 列表
 *               最多保留多少个组合。
 *
 * 返回值：
 *   MCVList* - 构建好的 MCV 列表；无有效列表（如样本为空）时返回 NULL。
 *
 * 设计思想（算法四步走）：
 *   1. 用 build_mss() 为所有列建立 MultiSortSupport，再用 build_sorted_items()
 *      按"全列组合"排序采样行。
 *   2. 用 build_distinct_groups() 把排序后的行聚成不同的组，并统计每组出现次数；
 *      组按频率降序排列。
 *   3. 确定保留多少项：上限取 stattarget 与总组数的较小值；然后用
 *      get_mincount_for_mcv_list() 计算入选阈值，从频率最高往下数，凡是组出现
 *      次数不低于阈值的都保留。
 *   4. 若保留项数 >0，则构造 MCVList：用 build_column_frequencies() 计算各列
 *      （单独一列）的每个值在样本中的频率，从而算出每项的 base_frequency（若列
 *      相互独立时该项的期望频率 = 各列频率之积）。这就是 MCV 项"实际频率 vs 独立
 *      假设频率"的对照依据。
 *   5. 释放中间数组（items、groups、nfreqs、freqs），返回 mcvlist。
 *
 * 与单列 MCV 的区别：单列 MCV 只关心组频率本身；多元 MCV 更关心"实际频率与独立
 * 假设（base_frequency）的偏差"，所以阈值算法不同（这里直接对所有保留项用最小
 * 出现次数阈值，而不考虑与平均频率的比较）。
 * ============================================================================
 */
MCVList *
statext_mcv_build(StatsBuildData *data, double totalrows, int stattarget)
{
	int			i,
				numattrs,
				numrows,
				ngroups,
				nitems;
	double		mincount;
	SortItem   *items;
	SortItem   *groups;
	MCVList    *mcvlist = NULL;
	MultiSortSupport mss;

	/* comparator for all the columns */
	mss = build_mss(data);

	/* sort the rows */
	items = build_sorted_items(data, &nitems, mss,
							   data->nattnums, data->attnums);

	if (!items)
		return NULL;

	/* for convenience */
	numattrs = data->nattnums;
	numrows = data->numrows;

	/* transform the sorted rows into groups (sorted by frequency) */
	groups = build_distinct_groups(nitems, items, mss, &ngroups);

	/*
	 * The maximum number of MCV items to store, based on the statistics
	 * target we computed for the statistics object (from the target set for
	 * the object itself, attributes and the system default). In any case, we
	 * can't keep more groups than we have available.
	 */
	nitems = stattarget;
	if (nitems > ngroups)
		nitems = ngroups;

	/*
	 * Decide how many items to keep in the MCV list. We can't use the same
	 * algorithm as per-column MCV lists, because that only considers the
	 * actual group frequency - but we're primarily interested in how the
	 * actual frequency differs from the base frequency (product of simple
	 * per-column frequencies, as if the columns were independent).
	 *
	 * Using the same algorithm might exclude items that are close to the
	 * "average" frequency of the sample. But that does not say whether the
	 * observed frequency is close to the base frequency or not. We also need
	 * to consider unexpectedly uncommon items (again, compared to the base
	 * frequency), and the single-column algorithm does not have to.
	 *
	 * We simply decide how many items to keep by computing the minimum count
	 * using get_mincount_for_mcv_list() and then keep all items that seem to
	 * be more common than that.
	 */
	mincount = get_mincount_for_mcv_list(numrows, totalrows);

	/*
	 * Walk the groups until we find the first group with a count below the
	 * mincount threshold (the index of that group is the number of groups we
	 * want to keep).
	 */
	for (i = 0; i < nitems; i++)
	{
		if (groups[i].count < mincount)
		{
			nitems = i;
			break;
		}
	}

	/*
	 * At this point, we know the number of items for the MCV list. There
	 * might be none (for uniform distribution with many groups), and in that
	 * case, there will be no MCV list. Otherwise, construct the MCV list.
	 */
	if (nitems > 0)
	{
		int			j;
		SortItem	key;
		MultiSortSupport tmp;

		/* frequencies for values in each attribute */
		SortItem  **freqs;
		int		   *nfreqs;

		/* used to search values */
		tmp = (MultiSortSupport) palloc(offsetof(MultiSortSupportData, ssup)
										+ sizeof(SortSupportData));

		/* compute frequencies for values in each column */
		nfreqs = palloc0_array(int, numattrs);
		freqs = build_column_frequencies(groups, ngroups, mss, nfreqs);

		/*
		 * Allocate the MCV list structure, set the global parameters.
		 */
		mcvlist = (MCVList *) palloc0(offsetof(MCVList, items) +
									  sizeof(MCVItem) * nitems);

		mcvlist->magic = STATS_MCV_MAGIC;
		mcvlist->type = STATS_MCV_TYPE_BASIC;
		mcvlist->ndimensions = numattrs;
		mcvlist->nitems = nitems;

		/* store info about data type OIDs */
		for (i = 0; i < numattrs; i++)
			mcvlist->types[i] = data->stats[i]->attrtypid;

		/* Copy the first chunk of groups into the result. */
		for (i = 0; i < nitems; i++)
		{
			/* just point to the proper place in the list */
			MCVItem    *item = &mcvlist->items[i];

			item->values = palloc_array(Datum, numattrs);
			item->isnull = palloc_array(bool, numattrs);

			/* copy values for the group */
			memcpy(item->values, groups[i].values, sizeof(Datum) * numattrs);
			memcpy(item->isnull, groups[i].isnull, sizeof(bool) * numattrs);

			/* groups should be sorted by frequency in descending order */
			Assert((i == 0) || (groups[i - 1].count >= groups[i].count));

			/* group frequency */
			item->frequency = (double) groups[i].count / numrows;

			/* base frequency, if the attributes were independent */
			item->base_frequency = 1.0;
			for (j = 0; j < numattrs; j++)
			{
				SortItem   *freq;

				/* single dimension */
				tmp->ndims = 1;
				tmp->ssup[0] = mss->ssup[j];

				/* fill search key */
				key.values = &groups[i].values[j];
				key.isnull = &groups[i].isnull[j];

				freq = (SortItem *) bsearch_arg(&key, freqs[j], nfreqs[j],
												sizeof(SortItem),
												multi_sort_compare, tmp);

				item->base_frequency *= ((double) freq->count) / numrows;
			}
		}

		pfree(nfreqs);
		pfree(freqs);
	}

	pfree(items);
	pfree(groups);

	return mcvlist;
}

/*
 * ============================================================================
 * 【中文注释】build_mss —— 为给定统计数据构建多列排序支持结构
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为 MCV 构建过程中需要按"多列组合"排序采样行，而多列排序需要 MultiSortSupport
 *   （每列一个 SortSupport + 维度数）。本函数根据 data 中各列的类型构建该结构。
 *
 * 参数：
 *   data - 采样数据，其中 data->stats[i]->attrtypid 给出第 i 列类型、
 *          attrcollid 给出排序规则。
 *
 * 返回值：
 *   MultiSortSupport - 初始化好的排序支持结构。
 *
 * 设计思想：
 *   1. multi_sort_init(numattrs) 创建结构；
 *   2. 对每一列用 lookup_type_cache(attrtypid, TYPECACHE_LT_OPR) 查找该类型的
 *      小于操作符（排序用），找不到则报错（理论不会发生）；
 *   3. 调用 multi_sort_add_dimension() 把该列的排序操作符与排序规则注册进去。
 * ============================================================================
 */
static MultiSortSupport
build_mss(StatsBuildData *data)
{
	int			i;
	int			numattrs = data->nattnums;

	/* Sort by multiple columns (using array of SortSupport) */
	MultiSortSupport mss = multi_sort_init(numattrs);

	/* prepare the sort functions for all the attributes */
	for (i = 0; i < numattrs; i++)
	{
		VacAttrStats *colstat = data->stats[i];
		TypeCacheEntry *type;

		type = lookup_type_cache(colstat->attrtypid, TYPECACHE_LT_OPR);
		if (type->lt_opr == InvalidOid) /* shouldn't happen */
			elog(ERROR, "cache lookup failed for ordering operator for type %u",
				 colstat->attrtypid);

		multi_sort_add_dimension(mss, i, type->lt_opr, colstat->attrcollid);
	}

	return mss;
}

/*
 * ============================================================================
 * 【中文注释】count_distinct_groups —— 统计不同"列组合值"的组数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   统计已排序的 SortItem 数组中有多少组互不相同的多列组合值（即去重后的行数）。
 *
 * 参数：
 *   numrows - 数组长度。
 *   items   - 排序好的 SortItem 数组。
 *   mss     - 多列排序支持（用于逐组比较）。
 *
 * 返回值：
 *   int - 不同组合的组数。
 *
 * 设计思想：
 *   数组已按 mss 排序，因此只需相邻两两比较：不同则组数+1。初始 ndistinct=1
 *   （至少一个元素）。比较用 multi_sort_compare()。
 * ============================================================================
 */
static int
count_distinct_groups(int numrows, SortItem *items, MultiSortSupport mss)
{
	int			i;
	int			ndistinct;

	ndistinct = 1;
	for (i = 1; i < numrows; i++)
	{
		/* make sure the array really is sorted */
		Assert(multi_sort_compare(&items[i], &items[i - 1], mss) >= 0);

		if (multi_sort_compare(&items[i], &items[i - 1], mss) != 0)
			ndistinct += 1;
	}

	return ndistinct;
}

/*
 * ============================================================================
 * 【中文注释】compare_sort_item_count —— 按出现次数降序比较 SortItem 的比较器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   qsort_interruptible() 的回调：把 SortItem 数组按 count（出现次数）从大到小
 *   排序，用于把不同组按频率排序。
 *
 * 参数：
 *   a, b - 两个待比较的 SortItem 指针。
 *   arg  - 未使用（标准 qsort 参数）。
 *
 * 返回值：
 *   int - a.count < b.count 时 >0，a.count > b.count 时 <0，相等时 0
 *         （注意返回值方向与常规比较器相反，实现降序）。
 * ============================================================================
 */
static int
compare_sort_item_count(const void *a, const void *b, void *arg)
{
	const SortItem *ia = a;
	const SortItem *ib = b;

	if (ia->count == ib->count)
		return 0;
	else if (ia->count > ib->count)
		return -1;

	return 1;
}

/*
 * ============================================================================
 * 【中文注释】build_distinct_groups —— 把排序后的行聚成组并统计频率
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   给定按多列组合排序的 SortItem 数组，把相邻的相同组合聚成一组，计算每组的
 *   出现次数（count），并返回一个按 count 降序排列的组数组。
 *
 * 参数：
 *   numrows   - items 数组长度。
 *   items     - 已排序的 SortItem 数组。
 *   mss       - 多列排序支持。
 *   ndistinct - 输出参数：不同组的个数。
 *
 * 返回值：
 *   SortItem* - 组数组（长度 *ndistinct），每组带 count；按 count 降序。
 *
 * 设计思想：
 *   1. 先用 count_distinct_groups() 算出组数 ngroups，一次性分配空间。
 *   2. 扫描排序数组：与前一元素不同则开启新组，相同则当前组 count++。
 *   3. 用 qsort_interruptible() + compare_sort_item_count() 按频率降序排序。
 *   4. 断言 j+1 == ngroups，保证恰好填满。
 * ============================================================================
 */
static SortItem *
build_distinct_groups(int numrows, SortItem *items, MultiSortSupport mss,
					  int *ndistinct)
{
	int			i,
				j;
	int			ngroups = count_distinct_groups(numrows, items, mss);

	SortItem   *groups = (SortItem *) palloc(ngroups * sizeof(SortItem));

	j = 0;
	groups[0] = items[0];
	groups[0].count = 1;

	for (i = 1; i < numrows; i++)
	{
		/* Assume sorted in ascending order. */
		Assert(multi_sort_compare(&items[i], &items[i - 1], mss) >= 0);

		/* New distinct group detected. */
		if (multi_sort_compare(&items[i], &items[i - 1], mss) != 0)
		{
			groups[++j] = items[i];
			groups[j].count = 0;
		}

		groups[j].count++;
	}

	/* ensure we filled the expected number of distinct groups */
	Assert(j + 1 == ngroups);

	/* Sort the distinct groups by frequency (in descending order). */
	qsort_interruptible(groups, ngroups, sizeof(SortItem),
						compare_sort_item_count, NULL);

	*ndistinct = ngroups;
	return groups;
}

/*
 * ============================================================================
 * 【中文注释】sort_item_compare —— 按单列比较两个 SortItem 的比较器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   仅按 SortItem 的第一个值（values[0]/isnull[0]）比较两个 SortItem，用于对
 *   build_column_frequencies() 中"某一列的取值数组"排序/去重。
 *
 * 参数：
 *   a, b - 待比较的 SortItem 指针。
 *   arg  - SortSupport 指针（该列的排序支持）。
 *
 * 返回值：
 *   int - 按 ApplySortComparator 比较第 0 维的结果。
 *
 * 设计思想：
 *   与 multi_sort_compare 不同，这里只比较单列，故直接把 SortSupport 作为比较
 *   上下文，用 ApplySortComparator 处理 NULL 排序等逻辑。
 * ============================================================================
 */
static int
sort_item_compare(const void *a, const void *b, void *arg)
{
	SortSupport ssup = (SortSupport) arg;
	const SortItem *ia = a;
	const SortItem *ib = b;

	return ApplySortComparator(ia->values[0], ia->isnull[0],
							   ib->values[0], ib->isnull[0],
							   ssup);
}

/*
 * ============================================================================
 * 【中文注释】build_column_frequencies —— 统计各列单值的出现频率
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对 MCV 覆盖的每一列，统计该列每个"单值"在样本中出现的总次数（可能来自多个
 *   MCV 项），返回每列一个按值排序的 SortItem 数组。这些单值频率用于计算 MCV 项
 *   的 base_frequency（列独立假设下的期望频率）。
 *
 * 参数：
 *   groups  - 组的 SortItem 数组（含每组每列的取值与组 count）。
 *   ngroups - 组的个数。
 *   mss     - 多列排序支持（含各列的 SortSupport）。
 *   ncounts - 输出参数：每列的去重值个数。
 *
 * 返回值：
 *   SortItem** - 长度为 ndims 的指针数组，第 dim 个是长度为 ncounts[dim]、
 *                按该列值排序去重的 SortItem 数组。
 *
 * 设计思想：
 *   1. 内存一次性分配（单块），一次 pfree 即可全部释放。
 *   2. 每个 SortItem 的 values/isnull 直接"指向"输入 groups 中对应位置
 *      （&groups[i].values[dim]），不额外拷贝，节省内存。
 *   3. 每列做法：取出各组在该列的值并按 sort_item_compare 排序，然后去重：相同
 *      值的 count 累加（因为同一单值可出现在多个 MCV 组里）。ncounts[dim] 记录
 *      该列去重后的值个数。
 * ============================================================================
 */
static SortItem **
build_column_frequencies(SortItem *groups, int ngroups,
						 MultiSortSupport mss, int *ncounts)
{
	int			i,
				dim;
	SortItem  **result;
	char	   *ptr;

	Assert(groups);
	Assert(ncounts);

	/* allocate arrays for all columns as a single chunk */
	ptr = palloc(MAXALIGN(sizeof(SortItem *) * mss->ndims) +
				 mss->ndims * MAXALIGN(sizeof(SortItem) * ngroups));

	/* initial array of pointers */
	result = (SortItem **) ptr;
	ptr += MAXALIGN(sizeof(SortItem *) * mss->ndims);

	for (dim = 0; dim < mss->ndims; dim++)
	{
		SortSupport ssup = &mss->ssup[dim];

		/* array of values for a single column */
		result[dim] = (SortItem *) ptr;
		ptr += MAXALIGN(sizeof(SortItem) * ngroups);

		/* extract data for the dimension */
		for (i = 0; i < ngroups; i++)
		{
			/* point into the input groups */
			result[dim][i].values = &groups[i].values[dim];
			result[dim][i].isnull = &groups[i].isnull[dim];
			result[dim][i].count = groups[i].count;
		}

		/* sort the values, deduplicate */
		qsort_interruptible(result[dim], ngroups, sizeof(SortItem),
							sort_item_compare, ssup);

		/*
		 * Identify distinct values, compute frequency (there might be
		 * multiple MCV items containing this value, so we need to sum counts
		 * from all of them.
		 */
		ncounts[dim] = 1;
		for (i = 1; i < ngroups; i++)
		{
			if (sort_item_compare(&result[dim][i - 1], &result[dim][i], ssup) == 0)
			{
				result[dim][ncounts[dim] - 1].count += result[dim][i].count;
				continue;
			}

			result[dim][ncounts[dim]] = result[dim][i];

			ncounts[dim]++;
		}
	}

	return result;
}

/*
 * ============================================================================
 * 【中文注释】statext_mcv_load —— 从系统表加载 MCV 列表
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从 pg_statistic_ext_data 表加载并反序列化某个统计对象的 MCVList，供规划器
 *   在估算选择性时使用。
 *
 * 参数：
 *   mvoid - 统计对象 OID。
 *   inh   - 是否加载继承树版本（stxdinherit）。
 *
 * 返回值：
 *   MCVList* - 反序列化后的 MCV 列表。
 *
 * 设计思想：
 *   通过 syscache（STATEXTDATASTXOID）按 (mvoid, inh) 精确查找 pg_statistic_ext_data
 *   元组；找不到元组则报"cache lookup failed"；stxdmcv 列为 NULL 说明该统计尚未
 *   构建，报 "not yet built" 错误。随后调用 statext_mcv_deserialize() 解析 bytea，
 *   并 ReleaseSysCache 释放缓存引用。
 * ============================================================================
 */
MCVList *
statext_mcv_load(Oid mvoid, bool inh)
{
	MCVList    *result;
	bool		isnull;
	Datum		mcvlist;
	HeapTuple	htup = SearchSysCache2(STATEXTDATASTXOID,
									   ObjectIdGetDatum(mvoid), BoolGetDatum(inh));

	if (!HeapTupleIsValid(htup))
		elog(ERROR, "cache lookup failed for statistics object %u", mvoid);

	mcvlist = SysCacheGetAttr(STATEXTDATASTXOID, htup,
							  Anum_pg_statistic_ext_data_stxdmcv, &isnull);

	if (isnull)
		elog(ERROR,
			 "requested statistics kind \"%c\" is not yet built for statistics object %u",
			 STATS_EXT_MCV, mvoid);

	result = statext_mcv_deserialize(DatumGetByteaP(mcvlist));

	ReleaseSysCache(htup);

	return result;
}


/*
 * ============================================================================
 * 【中文注释】statext_mcv_serialize —— 把 MCV 列表序列化为 pg_mcv_list（bytea）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把内存中的 MCVList 编码成 bytea 以便写入 pg_statistic_ext_data.stxdmcv 列
 *   （该列类型即 pg_mcv_list）。
 *
 * 参数：
 *   mcvlist - 内存中的 MCV 列表。
 *   stats   - VacAttrStats 数组（每列一个），用于读取各列类型的 typlen/typbyval
 *             等信息以确定序列化格式。
 *
 * 返回值：
 *   bytea* - 序列化结果（varlena），调用方负责 pfree。
 *
 * 设计思想：
 *   1.【去重】：MCV 项可能含多种类型的值，且同一属性值常在不同 MCV 项里重复出现，
 *      所以先把每列的取值去重成数组，再用"数组下标"代替具体值，减少体积。
 *   2.【整体布局】：
 *         +---------------+----------------+---------------------+-------+
 *         | header fields | dimension info | deduplicated values | items |
 *         +---------------+----------------+---------------------+-------+
 *      其中 dimension info 描述每列类型的信息（typlen、typbyval、去重后值个数等）；
 *      deduplicated values 是各列去重后的值；items 是真正的 MCV 项，值被替换成
 *      uint16 下标。
 *   3.【下标宽度】：用 uint16 存下标。MCV 项数受统计目标限制（当前上限 1 万），
 *      即使放宽到 6.5 万也仍在 uint16 范围内，有足够余量；且该上限是按"每列去重
 *      值个数"而言，实际通常很少，故 uint16 足够。
 *   4.【体积预期】：不指望像直方图那样省很多空间——MCV 没有做桶分裂（那是直方图
 *      高冗余的来源）。
 *
 *   TODO：可考虑把每个 item 的 NULL 标志打包成单个 char（或更长类型），而不是
 *   用一个 bool 数组。
 * ============================================================================
 */
bytea *
statext_mcv_serialize(MCVList *mcvlist, VacAttrStats **stats)
{
	int			dim;
	int			ndims = mcvlist->ndimensions;

	SortSupport ssup;
	DimensionInfo *info;

	Size		total_length;

	/* serialized items (indexes into arrays, etc.) */
	bytea	   *raw;
	char	   *ptr;
	char	   *endptr PG_USED_FOR_ASSERTS_ONLY;

	/* values per dimension (and number of non-NULL values) */
	Datum	  **values = palloc0_array(Datum *, ndims);
	int		   *counts = palloc0_array(int, ndims);

	/*
	 * We'll include some rudimentary information about the attribute types
	 * (length, by-val flag), so that we don't have to look them up while
	 * deserializing the MCV list (we already have the type OID in the
	 * header).  This is safe because when changing the type of the attribute
	 * the statistics gets dropped automatically.  We need to store the info
	 * about the arrays of deduplicated values anyway.
	 */
	info = palloc0_array(DimensionInfo, ndims);

	/* sort support data for all attributes included in the MCV list */
	ssup = palloc0_array(SortSupportData, ndims);

	/* collect and deduplicate values for each dimension (attribute) */
	for (dim = 0; dim < ndims; dim++)
	{
		int			ndistinct;
		TypeCacheEntry *typentry;

		/*
		 * Lookup the LT operator (can't get it from stats extra_data, as we
		 * don't know how to interpret that - scalar vs. array etc.).
		 */
		typentry = lookup_type_cache(stats[dim]->attrtypid, TYPECACHE_LT_OPR);

		/* copy important info about the data type (length, by-value) */
		info[dim].typlen = stats[dim]->attrtype->typlen;
		info[dim].typbyval = stats[dim]->attrtype->typbyval;

		/* allocate space for values in the attribute and collect them */
		values[dim] = palloc0_array(Datum, mcvlist->nitems);

		for (uint32 i = 0; i < mcvlist->nitems; i++)
		{
			/* skip NULL values - we don't need to deduplicate those */
			if (mcvlist->items[i].isnull[dim])
				continue;

			/* append the value at the end */
			values[dim][counts[dim]] = mcvlist->items[i].values[dim];
			counts[dim] += 1;
		}

		/* if there are just NULL values in this dimension, we're done */
		if (counts[dim] == 0)
			continue;

		/* sort and deduplicate the data */
		ssup[dim].ssup_cxt = CurrentMemoryContext;
		ssup[dim].ssup_collation = stats[dim]->attrcollid;
		ssup[dim].ssup_nulls_first = false;

		PrepareSortSupportFromOrderingOp(typentry->lt_opr, &ssup[dim]);

		qsort_interruptible(values[dim], counts[dim], sizeof(Datum),
							compare_scalars_simple, &ssup[dim]);

		/*
		 * Walk through the array and eliminate duplicate values, but keep the
		 * ordering (so that we can do a binary search later). We know there's
		 * at least one item as (counts[dim] != 0), so we can skip the first
		 * element.
		 */
		ndistinct = 1;			/* number of distinct values */
		for (int i = 1; i < counts[dim]; i++)
		{
			/* expect sorted array */
			Assert(compare_datums_simple(values[dim][i - 1], values[dim][i], &ssup[dim]) <= 0);

			/* if the value is the same as the previous one, we can skip it */
			if (!compare_datums_simple(values[dim][i - 1], values[dim][i], &ssup[dim]))
				continue;

			values[dim][ndistinct] = values[dim][i];
			ndistinct += 1;
		}

		/* we must not exceed PG_UINT16_MAX, as we use uint16 indexes */
		Assert(ndistinct <= PG_UINT16_MAX);

		/*
		 * Store additional info about the attribute - number of deduplicated
		 * values, and also size of the serialized data. For fixed-length data
		 * types this is trivial to compute, for varwidth types we need to
		 * actually walk the array and sum the sizes.
		 */
		info[dim].nvalues = ndistinct;

		if (info[dim].typbyval) /* by-value data types */
		{
			info[dim].nbytes = info[dim].nvalues * info[dim].typlen;

			/*
			 * We copy the data into the MCV item during deserialization, so
			 * we don't need to allocate any extra space.
			 */
			info[dim].nbytes_aligned = 0;
		}
		else if (info[dim].typlen > 0)	/* fixed-length by-ref */
		{
			/*
			 * We don't care about alignment in the serialized data, so we
			 * pack the data as much as possible. But we also track how much
			 * data will be needed after deserialization, and in that case we
			 * need to account for alignment of each item.
			 *
			 * Note: As the items are fixed-length, we could easily compute
			 * this during deserialization, but we do it here anyway.
			 */
			info[dim].nbytes = info[dim].nvalues * info[dim].typlen;
			info[dim].nbytes_aligned = info[dim].nvalues * MAXALIGN(info[dim].typlen);
		}
		else if (info[dim].typlen == -1)	/* varlena */
		{
			info[dim].nbytes = 0;
			info[dim].nbytes_aligned = 0;
			for (int i = 0; i < info[dim].nvalues; i++)
			{
				Size		len;

				/*
				 * For varlena values, we detoast the values and store the
				 * length and data separately. We don't bother with alignment
				 * here, which means that during deserialization we need to
				 * copy the fields and only access the copies.
				 */
				values[dim][i] = PointerGetDatum(PG_DETOAST_DATUM(values[dim][i]));

				/* serialized length (uint32 length + data) */
				len = VARSIZE_ANY_EXHDR(DatumGetPointer(values[dim][i]));
				info[dim].nbytes += sizeof(uint32); /* length */
				info[dim].nbytes += len;	/* value (no header) */

				/*
				 * During deserialization we'll build regular varlena values
				 * with full headers, and we need to align them properly.
				 */
				info[dim].nbytes_aligned += MAXALIGN(VARHDRSZ + len);
			}
		}
		else if (info[dim].typlen == -2)	/* cstring */
		{
			info[dim].nbytes = 0;
			info[dim].nbytes_aligned = 0;
			for (int i = 0; i < info[dim].nvalues; i++)
			{
				Size		len;

				/*
				 * cstring is handled similar to varlena - first we store the
				 * length as uint32 and then the data. We don't care about
				 * alignment, which means that during deserialization we need
				 * to copy the fields and only access the copies.
				 */

				/* c-strings include terminator, so +1 byte */
				len = strlen(DatumGetCString(values[dim][i])) + 1;
				info[dim].nbytes += sizeof(uint32); /* length */
				info[dim].nbytes += len;	/* value */

				/* space needed for properly aligned deserialized copies */
				info[dim].nbytes_aligned += MAXALIGN(len);
			}
		}

		/* we know (count>0) so there must be some data */
		Assert(info[dim].nbytes > 0);
	}

	/*
	 * Now we can finally compute how much space we'll actually need for the
	 * whole serialized MCV list (varlena header, MCV header, dimension info
	 * for each attribute, deduplicated values and items).
	 */
	total_length = (3 * sizeof(uint32)) /* magic + type + nitems */
		+ sizeof(AttrNumber)	/* ndimensions */
		+ (ndims * sizeof(Oid));	/* attribute types */

	/* dimension info */
	total_length += ndims * sizeof(DimensionInfo);

	/* add space for the arrays of deduplicated values */
	for (int i = 0; i < ndims; i++)
		total_length += info[i].nbytes;

	/*
	 * And finally account for the items (those are fixed-length, thanks to
	 * replacing values with uint16 indexes into the deduplicated arrays).
	 */
	total_length += mcvlist->nitems * ITEM_SIZE(dim);

	/*
	 * Allocate space for the whole serialized MCV list (we'll skip bytes, so
	 * we set them to zero to make the result more compressible).
	 */
	raw = (bytea *) palloc0(VARHDRSZ + total_length);
	SET_VARSIZE(raw, VARHDRSZ + total_length);

	ptr = VARDATA(raw);
	endptr = ptr + total_length;

	/* copy the MCV list header fields, one by one */
	memcpy(ptr, &mcvlist->magic, sizeof(uint32));
	ptr += sizeof(uint32);

	memcpy(ptr, &mcvlist->type, sizeof(uint32));
	ptr += sizeof(uint32);

	memcpy(ptr, &mcvlist->nitems, sizeof(uint32));
	ptr += sizeof(uint32);

	memcpy(ptr, &mcvlist->ndimensions, sizeof(AttrNumber));
	ptr += sizeof(AttrNumber);

	memcpy(ptr, mcvlist->types, sizeof(Oid) * ndims);
	ptr += (sizeof(Oid) * ndims);

	/* store information about the attributes (data amounts, ...) */
	memcpy(ptr, info, sizeof(DimensionInfo) * ndims);
	ptr += sizeof(DimensionInfo) * ndims;

	/* Copy the deduplicated values for all attributes to the output. */
	for (dim = 0; dim < ndims; dim++)
	{
		/* remember the starting point for Asserts later */
		char	   *start PG_USED_FOR_ASSERTS_ONLY = ptr;

		for (int i = 0; i < info[dim].nvalues; i++)
		{
			Datum		value = values[dim][i];

			if (info[dim].typbyval) /* passed by value */
			{
				Datum		tmp;

				/*
				 * For byval types, we need to copy just the significant bytes
				 * - we can't use memcpy directly, as that assumes
				 * little-endian behavior.  store_att_byval does almost what
				 * we need, but it requires a properly aligned buffer - the
				 * output buffer does not guarantee that. So we simply use a
				 * local Datum variable (which guarantees proper alignment),
				 * and then copy the value from it.
				 */
				store_att_byval(&tmp, value, info[dim].typlen);

				memcpy(ptr, &tmp, info[dim].typlen);
				ptr += info[dim].typlen;
			}
			else if (info[dim].typlen > 0)	/* passed by reference */
			{
				/* no special alignment needed, treated as char array */
				memcpy(ptr, DatumGetPointer(value), info[dim].typlen);
				ptr += info[dim].typlen;
			}
			else if (info[dim].typlen == -1)	/* varlena */
			{
				uint32		len = VARSIZE_ANY_EXHDR(DatumGetPointer(value));

				/* copy the length */
				memcpy(ptr, &len, sizeof(uint32));
				ptr += sizeof(uint32);

				/* data from the varlena value (without the header) */
				memcpy(ptr, VARDATA_ANY(DatumGetPointer(value)), len);
				ptr += len;
			}
			else if (info[dim].typlen == -2)	/* cstring */
			{
				uint32		len = (uint32) strlen(DatumGetCString(value)) + 1;

				/* copy the length */
				memcpy(ptr, &len, sizeof(uint32));
				ptr += sizeof(uint32);

				/* value */
				memcpy(ptr, DatumGetCString(value), len);
				ptr += len;
			}

			/* no underflows or overflows */
			Assert((ptr > start) && ((ptr - start) <= info[dim].nbytes));
		}

		/* we should get exactly nbytes of data for this dimension */
		Assert((ptr - start) == info[dim].nbytes);
	}

	/* Serialize the items, with uint16 indexes instead of the values. */
	for (uint32 i = 0; i < mcvlist->nitems; i++)
	{
		MCVItem    *mcvitem = &mcvlist->items[i];

		/* don't write beyond the allocated space */
		Assert(ptr <= (endptr - ITEM_SIZE(dim)));

		/* copy NULL and frequency flags into the serialized MCV */
		memcpy(ptr, mcvitem->isnull, sizeof(bool) * ndims);
		ptr += sizeof(bool) * ndims;

		memcpy(ptr, &mcvitem->frequency, sizeof(double));
		ptr += sizeof(double);

		memcpy(ptr, &mcvitem->base_frequency, sizeof(double));
		ptr += sizeof(double);

		/* store the indexes last */
		for (dim = 0; dim < ndims; dim++)
		{
			uint16		index = 0;
			Datum	   *value;

			/* do the lookup only for non-NULL values */
			if (!mcvitem->isnull[dim])
			{
				value = (Datum *) bsearch_arg(&mcvitem->values[dim], values[dim],
											  info[dim].nvalues, sizeof(Datum),
											  compare_scalars_simple, &ssup[dim]);

				Assert(value != NULL);	/* serialization or deduplication
										 * error */

				/* compute index within the deduplicated array */
				index = (uint16) (value - values[dim]);

				/* check the index is within expected bounds */
				Assert(index < info[dim].nvalues);
			}

			/* copy the index into the serialized MCV */
			memcpy(ptr, &index, sizeof(uint16));
			ptr += sizeof(uint16);
		}

		/* make sure we don't overflow the allocated value */
		Assert(ptr <= endptr);
	}

	/* at this point we expect to match the total_length exactly */
	Assert(ptr == endptr);

	pfree(values);
	pfree(counts);

	return raw;
}

/*
 * ============================================================================
 * 【中文注释】statext_mcv_deserialize —— 反序列化 pg_mcv_list 为 MCVList 结构
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 statext_mcv_serialize() 互逆：把磁盘上的 bytea（pg_mcv_list）解码回内存
 *   中的 MCVList 结构。
 *
 * 参数：
 *   data - 序列化的 bytea（可为 NULL，此时返回 NULL）。
 *
 * 返回值：
 *   MCVList* - 反序列化结果。MCV 列表所需内存全部一次性分配（单块），因此一次
 *              pfree 即可整体释放。
 *
 * 设计思想：
 *   1. 先做健壮性检查：数据长度必须不小于 MinSizeOfMCVList（至少容纳完整头部），
 *      否则报"invalid MCV size"。
 *   2. 从 VARDATA_ANY 处开始，依次解析 magic/type/ndimensions/nitems 等头部字段，
 *      并校验 magic/type 合法、ndims 在 [1, STATS_MAX_DIMENSIONS] 内、nitems 不为 0。
 *   3. 根据头部计算所需的 DimensionInfo 区、去重值区、items 区的偏移，用
 *      mcv_total_size() 等宏校验总长度是否与头部声明一致（防损坏数据越界）。
 *   4. 解析每列的 dimension info 与去重值，建立 datum 映射表（map[dim][index]）；
 *      然后逐 item 按下标把值填回，NULL 标志单独处理。
 *   5. 全程用 ptr/endptr 断言防越界（ptr==endptr 表示恰好消费完整段数据），最后
 *      释放用于映射的临时 buffer。
 * ============================================================================
 */
MCVList *
statext_mcv_deserialize(bytea *data)
{
	int			dim,
				i;
	Size		expected_size;
	MCVList    *mcvlist;
	char	   *raw;
	char	   *ptr;
	char	   *endptr PG_USED_FOR_ASSERTS_ONLY;

	int			ndims,
				nitems;
	DimensionInfo *info = NULL;

	/* local allocation buffer (used only for deserialization) */
	Datum	  **map = NULL;

	/* MCV list */
	Size		mcvlen;

	/* buffer used for the result */
	Size		datalen;
	char	   *dataptr;
	char	   *valuesptr;
	char	   *isnullptr;

	if (data == NULL)
		return NULL;

	/*
	 * We can't possibly deserialize a MCV list if there's not even a complete
	 * header. We need an explicit formula here, because we serialize the
	 * header fields one by one, so we need to ignore struct alignment.
	 */
	if (VARSIZE_ANY(data) < MinSizeOfMCVList)
		elog(ERROR, "invalid MCV size %zu (expected at least %zu)",
			 VARSIZE_ANY(data), MinSizeOfMCVList);

	/* read the MCV list header */
	mcvlist = (MCVList *) palloc0(offsetof(MCVList, items));

	/* pointer to the data part (skip the varlena header) */
	raw = (char *) data;
	ptr = VARDATA_ANY(raw);
	endptr = raw + VARSIZE_ANY(data);

	/* get the header and perform further sanity checks */
	memcpy(&mcvlist->magic, ptr, sizeof(uint32));
	ptr += sizeof(uint32);

	memcpy(&mcvlist->type, ptr, sizeof(uint32));
	ptr += sizeof(uint32);

	memcpy(&mcvlist->nitems, ptr, sizeof(uint32));
	ptr += sizeof(uint32);

	memcpy(&mcvlist->ndimensions, ptr, sizeof(AttrNumber));
	ptr += sizeof(AttrNumber);

	if (mcvlist->magic != STATS_MCV_MAGIC)
		elog(ERROR, "invalid MCV magic %u (expected %u)",
			 mcvlist->magic, STATS_MCV_MAGIC);

	if (mcvlist->type != STATS_MCV_TYPE_BASIC)
		elog(ERROR, "invalid MCV type %u (expected %u)",
			 mcvlist->type, STATS_MCV_TYPE_BASIC);

	if (mcvlist->ndimensions == 0)
		elog(ERROR, "invalid zero-length dimension array in MCVList");
	else if ((mcvlist->ndimensions > STATS_MAX_DIMENSIONS) ||
			 (mcvlist->ndimensions < 0))
		elog(ERROR, "invalid length (%d) dimension array in MCVList",
			 mcvlist->ndimensions);

	if (mcvlist->nitems == 0)
		elog(ERROR, "invalid zero-length item array in MCVList");
	else if (mcvlist->nitems > STATS_MCVLIST_MAX_ITEMS)
		elog(ERROR, "invalid length (%u) item array in MCVList",
			 mcvlist->nitems);

	nitems = mcvlist->nitems;
	ndims = mcvlist->ndimensions;

	/*
	 * Check amount of data including DimensionInfo for all dimensions and
	 * also the serialized items (including uint16 indexes). Also, walk
	 * through the dimension information and add it to the sum.
	 */
	expected_size = SizeOfMCVList(ndims, nitems);

	/*
	 * Check that we have at least the dimension and info records, along with
	 * the items. We don't know the size of the serialized values yet. We need
	 * to do this check first, before accessing the dimension info.
	 */
	if (VARSIZE_ANY(data) < expected_size)
		elog(ERROR, "invalid MCV size %zu (expected %zu)",
			 VARSIZE_ANY(data), expected_size);

	/* Now copy the array of type Oids. */
	memcpy(mcvlist->types, ptr, sizeof(Oid) * ndims);
	ptr += (sizeof(Oid) * ndims);

	/* Now it's safe to access the dimension info. */
	info = palloc(ndims * sizeof(DimensionInfo));

	memcpy(info, ptr, ndims * sizeof(DimensionInfo));
	ptr += (ndims * sizeof(DimensionInfo));

	/* account for the value arrays */
	for (dim = 0; dim < ndims; dim++)
	{
		/*
		 * XXX I wonder if we can/should rely on asserts here. Maybe those
		 * checks should be done every time?
		 */
		Assert(info[dim].nvalues >= 0);
		Assert(info[dim].nbytes >= 0);

		expected_size += info[dim].nbytes;
	}

	/*
	 * Now we know the total expected MCV size, including all the pieces
	 * (header, dimension info. items and deduplicated data). So do the final
	 * check on size.
	 */
	if (VARSIZE_ANY(data) != expected_size)
		elog(ERROR, "invalid MCV size %zu (expected %zu)",
			 VARSIZE_ANY(data), expected_size);

	/*
	 * We need an array of Datum values for each dimension, so that we can
	 * easily translate the uint16 indexes later. We also need a top-level
	 * array of pointers to those per-dimension arrays.
	 *
	 * While allocating the arrays for dimensions, compute how much space we
	 * need for a copy of the by-ref data, as we can't simply point to the
	 * original values (it might go away).
	 */
	datalen = 0;				/* space for by-ref data */
	map = palloc_array(Datum *, ndims);

	for (dim = 0; dim < ndims; dim++)
	{
		map[dim] = palloc_array(Datum, info[dim].nvalues);

		/* space needed for a copy of data for by-ref types */
		datalen += info[dim].nbytes_aligned;
	}

	/*
	 * Now resize the MCV list so that the allocation includes all the data.
	 *
	 * Allocate space for a copy of the data, as we can't simply reference the
	 * serialized data - it's not aligned properly, and it may disappear while
	 * we're still using the MCV list, e.g. due to catcache release.
	 *
	 * We do care about alignment here, because we will allocate all the
	 * pieces at once, but then use pointers to different parts.
	 */
	mcvlen = MAXALIGN(offsetof(MCVList, items) + (sizeof(MCVItem) * nitems));

	/* arrays of values and isnull flags for all MCV items */
	mcvlen += nitems * MAXALIGN(sizeof(Datum) * ndims);
	mcvlen += nitems * MAXALIGN(sizeof(bool) * ndims);

	/* we don't quite need to align this, but it makes some asserts easier */
	mcvlen += MAXALIGN(datalen);

	/* now resize the deserialized MCV list, and compute pointers to parts */
	mcvlist = repalloc(mcvlist, mcvlen);

	/* pointer to the beginning of values/isnull arrays */
	valuesptr = (char *) mcvlist
		+ MAXALIGN(offsetof(MCVList, items) + (sizeof(MCVItem) * nitems));

	isnullptr = valuesptr + (nitems * MAXALIGN(sizeof(Datum) * ndims));

	dataptr = isnullptr + (nitems * MAXALIGN(sizeof(bool) * ndims));

	/*
	 * Build mapping (index => value) for translating the serialized data into
	 * the in-memory representation.
	 */
	for (dim = 0; dim < ndims; dim++)
	{
		/* remember start position in the input array */
		char	   *start PG_USED_FOR_ASSERTS_ONLY = ptr;

		if (info[dim].typbyval)
		{
			/* for by-val types we simply copy data into the mapping */
			for (i = 0; i < info[dim].nvalues; i++)
			{
				Datum		v = 0;

				memcpy(&v, ptr, info[dim].typlen);
				ptr += info[dim].typlen;

				map[dim][i] = fetch_att(&v, true, info[dim].typlen);

				/* no under/overflow of input array */
				Assert(ptr <= (start + info[dim].nbytes));
			}
		}
		else
		{
			/* for by-ref types we need to also make a copy of the data */

			/* passed by reference, but fixed length (name, tid, ...) */
			if (info[dim].typlen > 0)
			{
				for (i = 0; i < info[dim].nvalues; i++)
				{
					memcpy(dataptr, ptr, info[dim].typlen);
					ptr += info[dim].typlen;

					/* just point into the array */
					map[dim][i] = PointerGetDatum(dataptr);
					dataptr += MAXALIGN(info[dim].typlen);
				}
			}
			else if (info[dim].typlen == -1)
			{
				/* varlena */
				for (i = 0; i < info[dim].nvalues; i++)
				{
					uint32		len;

					/* read the uint32 length */
					memcpy(&len, ptr, sizeof(uint32));
					ptr += sizeof(uint32);

					/* the length is data-only */
					SET_VARSIZE(dataptr, len + VARHDRSZ);
					memcpy(VARDATA(dataptr), ptr, len);
					ptr += len;

					/* just point into the array */
					map[dim][i] = PointerGetDatum(dataptr);

					/* skip to place of the next deserialized value */
					dataptr += MAXALIGN(len + VARHDRSZ);
				}
			}
			else if (info[dim].typlen == -2)
			{
				/* cstring */
				for (i = 0; i < info[dim].nvalues; i++)
				{
					uint32		len;

					memcpy(&len, ptr, sizeof(uint32));
					ptr += sizeof(uint32);

					memcpy(dataptr, ptr, len);
					ptr += len;

					/* just point into the array */
					map[dim][i] = PointerGetDatum(dataptr);
					dataptr += MAXALIGN(len);
				}
			}

			/* no under/overflow of input array */
			Assert(ptr <= (start + info[dim].nbytes));

			/* no overflow of the output mcv value */
			Assert(dataptr <= ((char *) mcvlist + mcvlen));
		}

		/* check we consumed input data for this dimension exactly */
		Assert(ptr == (start + info[dim].nbytes));
	}

	/* we should have also filled the MCV list exactly */
	Assert(dataptr == ((char *) mcvlist + mcvlen));

	/* deserialize the MCV items and translate the indexes to Datums */
	for (i = 0; i < nitems; i++)
	{
		MCVItem    *item = &mcvlist->items[i];

		item->values = (Datum *) valuesptr;
		valuesptr += MAXALIGN(sizeof(Datum) * ndims);

		item->isnull = (bool *) isnullptr;
		isnullptr += MAXALIGN(sizeof(bool) * ndims);

		memcpy(item->isnull, ptr, sizeof(bool) * ndims);
		ptr += sizeof(bool) * ndims;

		memcpy(&item->frequency, ptr, sizeof(double));
		ptr += sizeof(double);

		memcpy(&item->base_frequency, ptr, sizeof(double));
		ptr += sizeof(double);

		/* finally translate the indexes (for non-NULL only) */
		for (dim = 0; dim < ndims; dim++)
		{
			uint16		index;

			memcpy(&index, ptr, sizeof(uint16));
			ptr += sizeof(uint16);

			if (item->isnull[dim])
				continue;

			item->values[dim] = map[dim][index];
		}

		/* check we're not overflowing the input */
		Assert(ptr <= endptr);
	}

	/* check that we processed all the data */
	Assert(ptr == endptr);

	/* release the buffers used for mapping */
	for (dim = 0; dim < ndims; dim++)
		pfree(map[dim]);

	pfree(map);

	return mcvlist;
}

/*
 * ============================================================================
 * 【中文注释】pg_stats_ext_mcvlist_items —— 把 MCV 列表展开为 SRF 结果集
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   这是一个集合返回函数（SRF），用于把给定的 pg_mcv_list（序列化 bytea）展开成
 *   一组可读的记录，方便用户直接查看 MCV 列表内容。
 *
 * 参数：
 *   PG_FUNCTION_ARGS - 参数 0 是 pg_mcv_list 类型的 bytea。
 *
 * 返回值：
 *   Datum - 每个 MCV 项返回一行，列结构为：
 *           - item ID（0...nitems，int4）
 *           - values（各列值的 text 数组）
 *           - nulls（各列是否为 NULL 的 boolean 数组）
 *           - frequency（该组合实际频率，float8）
 *           - base_frequency（列独立假设下的期望频率，float8）
 *     若统计对象没有 MCV 数据则返回空集。
 *
 * 设计思想：
 *   1. SRF 三阶段模式：首调用初始化 funcctx 并反序列化 MCV 列表（存 user_fctx），
 *      记录 max_calls=nitems；后续每次调用返回一项；耗尽后 SRF_RETURN_DONE。
 *   2. 每个 item 的 values 列用各列类型的输出函数（getTypeOutputInfo）把 Datum
 *      转成 text 后聚成 text 数组；NULL 值单独记录进 nulls 数组。
 *   3. 通过 get_call_result_type() 获取返回类型的 TupleDesc，用 heap_form_tuple
 *      构造元组。
 * ============================================================================
 */
Datum
pg_stats_ext_mcvlist_items(PG_FUNCTION_ARGS)
{
	FuncCallContext *funcctx;

	/* stuff done only on the first call of the function */
	if (SRF_IS_FIRSTCALL())
	{
		MemoryContext oldcontext;
		MCVList    *mcvlist;
		TupleDesc	tupdesc;

		/* create a function context for cross-call persistence */
		funcctx = SRF_FIRSTCALL_INIT();

		/* switch to memory context appropriate for multiple function calls */
		oldcontext = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx);

		mcvlist = statext_mcv_deserialize(PG_GETARG_BYTEA_P(0));

		funcctx->user_fctx = mcvlist;

		/* total number of tuples to be returned */
		funcctx->max_calls = 0;
		if (funcctx->user_fctx != NULL)
			funcctx->max_calls = mcvlist->nitems;

		/* Build a tuple descriptor for our result type */
		if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("function returning record called in context "
							"that cannot accept type record")));
		tupdesc = BlessTupleDesc(tupdesc);

		/*
		 * generate attribute metadata needed later to produce tuples from raw
		 * C strings
		 */
		funcctx->attinmeta = TupleDescGetAttInMetadata(tupdesc);

		MemoryContextSwitchTo(oldcontext);
	}

	/* stuff done on every call of the function */
	funcctx = SRF_PERCALL_SETUP();

	if (funcctx->call_cntr < funcctx->max_calls)	/* do when there is more
													 * left to send */
	{
		Datum		values[5];
		bool		nulls[5];
		HeapTuple	tuple;
		Datum		result;
		ArrayBuildState *astate_values = NULL;
		ArrayBuildState *astate_nulls = NULL;

		int			i;
		MCVList    *mcvlist;
		MCVItem    *item;

		mcvlist = (MCVList *) funcctx->user_fctx;

		Assert(funcctx->call_cntr < mcvlist->nitems);

		item = &mcvlist->items[funcctx->call_cntr];

		for (i = 0; i < mcvlist->ndimensions; i++)
		{

			astate_nulls = accumArrayResult(astate_nulls,
											BoolGetDatum(item->isnull[i]),
											false,
											BOOLOID,
											CurrentMemoryContext);

			if (!item->isnull[i])
			{
				bool		isvarlena;
				Oid			outfunc;
				FmgrInfo	fmgrinfo;
				Datum		val;
				text	   *txt;

				/* lookup output func for the type */
				getTypeOutputInfo(mcvlist->types[i], &outfunc, &isvarlena);
				fmgr_info(outfunc, &fmgrinfo);

				val = FunctionCall1(&fmgrinfo, item->values[i]);
				txt = cstring_to_text(DatumGetPointer(val));

				astate_values = accumArrayResult(astate_values,
												 PointerGetDatum(txt),
												 false,
												 TEXTOID,
												 CurrentMemoryContext);
			}
			else
				astate_values = accumArrayResult(astate_values,
												 (Datum) 0,
												 true,
												 TEXTOID,
												 CurrentMemoryContext);
		}

		values[0] = Int32GetDatum(funcctx->call_cntr);
		values[1] = makeArrayResult(astate_values, CurrentMemoryContext);
		values[2] = makeArrayResult(astate_nulls, CurrentMemoryContext);
		values[3] = Float8GetDatum(item->frequency);
		values[4] = Float8GetDatum(item->base_frequency);

		/* no NULLs in the tuple */
		memset(nulls, 0, sizeof(nulls));

		/* build a tuple */
		tuple = heap_form_tuple(funcctx->attinmeta->tupdesc, values, nulls);

		/* make the tuple into a datum */
		result = HeapTupleGetDatum(tuple);

		SRF_RETURN_NEXT(funcctx, result);
	}
	else						/* do when there is no more left */
	{
		SRF_RETURN_DONE(funcctx);
	}
}

/*
 * ============================================================================
 * 【中文注释】pg_mcv_list_in —— pg_mcv_list 类型的文本输入函数（禁用）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   pg_mcv_list 类型"真实到足以作为表列"，但没有任何自身的操作，也不允许文本
 *   输入——该类型只由统计构建过程写入，用户无法手工输入。
 *
 * 参数：
 *   PG_FUNCTION_ARGS - 调用参数（实际不会有效执行）。
 *
 * 返回值：
 *   直接报错：cannot accept a value of type pg_mcv_list。
 *
 * 设计思想：
 *   pg_mcv_list 以二进制形式存储（bytea 序列化），无需解析文本输入，故直接拒绝。
 * ============================================================================
 */
Datum
pg_mcv_list_in(PG_FUNCTION_ARGS)
{
	/*
	 * pg_mcv_list stores the data in binary form and parsing text input is
	 * not needed, so disallow this.
	 */
	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("cannot accept a value of type %s", "pg_mcv_list")));

	PG_RETURN_VOID();			/* keep compiler quiet */
}


/*
 * ============================================================================
 * 【中文注释】pg_mcv_list_out —— pg_mcv_list 类型的文本输出函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   MCV 列表内部就是序列化后的 bytea，因此直接复用 byteaout() 把它转成文本。
 *
 * 参数：
 *   PG_FUNCTION_ARGS - 调用参数。
 *
 * 返回值：
 *   Datum - bytea 的文本表示。
 *
 * 设计思想：
 *   XXX 理想情况下应输出有意义的表示（类似 pg_dependencies_out 那样），便于人类
 *   查看；但涉及去重值的展开策略未定，暂时用 byteaout 兜底。
 * ============================================================================
 */
Datum
pg_mcv_list_out(PG_FUNCTION_ARGS)
{
	return byteaout(fcinfo);
}

/*
 * ============================================================================
 * 【中文注释】pg_mcv_list_recv —— pg_mcv_list 类型的二进制输入函数（禁用）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 pg_mcv_list_in 类似，pg_mcv_list 不允许二进制输入，直接报错。
 *
 * 参数：
 *   PG_FUNCTION_ARGS - 调用参数（实际不会有效执行）。
 *
 * 返回值：
 *   直接报错：cannot accept a value of type pg_mcv_list。
 * ============================================================================
 */
Datum
pg_mcv_list_recv(PG_FUNCTION_ARGS)
{
	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("cannot accept a value of type %s", "pg_mcv_list")));

	PG_RETURN_VOID();			/* keep compiler quiet */
}

/*
 * ============================================================================
 * 【中文注释】pg_mcv_list_send —— pg_mcv_list 类型的二进制输出函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   MCV 列表本身就是序列化好的 bytea，直接复用 byteasend() 发送。
 *
 * 参数：
 *   PG_FUNCTION_ARGS - 调用参数。
 *
 * 返回值：
 *   Datum - 序列化后的二进制表示。
 * ============================================================================
 */
Datum
pg_mcv_list_send(PG_FUNCTION_ARGS)
{
	return byteasend(fcinfo);
}

/*
 * ============================================================================
 * 【中文注释】mcv_match_expression —— 把表达式匹配到统计的某个维度
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判断给定的表达式（一个 Var 或一个表达式）对应 MCV 统计的第几个维度（列），
 *   返回该维度的零基下标。
 *
 * 参数：
 *   expr   - 待匹配的节点：若是 Var 则按 varattno 匹配；否则当作统计的表达式之一。
 *   keys   - 统计对象覆盖的普通列号位图（bms）。
 *   exprs  - 统计对象定义的表达式列表。
 *   collid - 可选输出参数：返回该表达式/列的排序规则 OID。
 *
 * 返回值：
 *   int - 匹配到的维度下标（0 基）。匹配不到则 ERROR。
 *
 * 设计思想：
 *   1. Var：直接用 bms_member_index(keys, varattno) 找到该列在 keys 中的下标；
 *      idx<0 说明该列不在统计对象里，报错。collid 取 var->varcollid。
 *   2. 表达式：普通列排在前面（个数 = bms_num_members(keys)），表达式排在其后，
 *      逐个用 equal() 与 stat_expr 比较；找不到则报错。collid 取 exprCollation。
 * ============================================================================
 */
static int
mcv_match_expression(Node *expr, Bitmapset *keys, List *exprs, Oid *collid)
{
	int			idx;

	if (IsA(expr, Var))
	{
		/* simple Var, so just lookup using varattno */
		Var		   *var = (Var *) expr;

		if (collid)
			*collid = var->varcollid;

		idx = bms_member_index(keys, var->varattno);

		if (idx < 0)
			elog(ERROR, "variable not found in statistics object");
	}
	else
	{
		/* expression - lookup in stats expressions */
		ListCell   *lc;

		if (collid)
			*collid = exprCollation(expr);

		/* expressions are stored after the simple columns */
		idx = bms_num_members(keys);
		foreach(lc, exprs)
		{
			Node	   *stat_expr = (Node *) lfirst(lc);

			if (equal(expr, stat_expr))
				break;

			idx++;
		}

		if (lc == NULL)
			elog(ERROR, "expression not found in statistics object");
	}

	return idx;
}

/*
 * ============================================================================
 * 【中文注释】mcv_get_match_bitmap —— 用 MCV 列表评估子句并维护匹配位图
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   用给定的一串子句（AND 或 OR 连接）逐个评估 MCV 列表中每个 item 是否可能匹配，
 *   返回每个 item 的匹配/不匹配位图。评估过程中用位图跳过不可能再改变结果的 item。
 *
 * 参数：
 *   root    - PlannerInfo（规划上下文）。
 *   clauses - 待评估的子句列表（AND 连接时全匹配才匹配，OR 连接时任一匹配即匹配）。
 *   keys    - 统计覆盖的列号位图。
 *   exprs   - 统计定义的表达式列表。
 *   mcvlist - MCV 列表。
 *   is_or   - true 表示按 OR 逻辑合并（任一子句匹配即认为 item 匹配），false 表示
 *             AND 逻辑（所有子句都匹配才认为匹配）。
 *
 * 返回值：
 *   bool* - 长度 mcvlist->nitems 的匹配位图。
 *
 * 设计思想：
 *   1. 位图初始化为 !is_or：AND 列表初始全 true（先假定匹配，遇不匹配变 false）、
 *      OR 列表初始全 false（先假定不匹配，遇匹配变 true）。
 *   2. 对每个子句评估所有 item：
 *      - OpClause：用 mcv_match_expression() 找到维度，逐 item 调操作符函数比较
 *        值与常量（注意严格函数下 NULL 直接判不匹配）；跳过 RESULT_IS_FINAL 的项。
 *      - ScalarArrayOpExpr：对数组每个元素做同样比较后合并。
 *      - NullTest / BoolExpr（AND/OR/NOT）递归处理。
 *   3. RESULT_IS_FINAL 用于提前终止：AND 列表中某项已是 false 就不会再变 true，
 *      反之 OR 列表中已是 true 的项也不会再变 false，可跳过后续子句。
 *   XXX 位图用 bool 数组略浪费（其实 1 bit 足够，还能用 &/| 加速合并），但 MCV
 *   列表大小有上限，位图仍很小，暂不优化。
 * ============================================================================
 */
static bool *
mcv_get_match_bitmap(PlannerInfo *root, List *clauses,
					 Bitmapset *keys, List *exprs,
					 MCVList *mcvlist, bool is_or)
{
	ListCell   *l;
	bool	   *matches;

	/* The bitmap may be partially built. */
	Assert(clauses != NIL);
	Assert(mcvlist != NULL);
	Assert(mcvlist->nitems > 0);
	Assert(mcvlist->nitems <= STATS_MCVLIST_MAX_ITEMS);

	matches = palloc_array(bool, mcvlist->nitems);
	memset(matches, !is_or, sizeof(bool) * mcvlist->nitems);

	/*
	 * Loop through the list of clauses, and for each of them evaluate all the
	 * MCV items not yet eliminated by the preceding clauses.
	 */
	foreach(l, clauses)
	{
		Node	   *clause = (Node *) lfirst(l);

		/* if it's a RestrictInfo, then extract the clause */
		if (IsA(clause, RestrictInfo))
			clause = (Node *) ((RestrictInfo *) clause)->clause;

		/*
		 * Handle the various types of clauses - OpClause, NullTest and
		 * AND/OR/NOT
		 */
		if (is_opclause(clause))
		{
			OpExpr	   *expr = (OpExpr *) clause;
			FmgrInfo	opproc;

			/* valid only after examine_opclause_args returns true */
			Node	   *clause_expr;
			Const	   *cst;
			bool		expronleft;
			int			idx;
			Oid			collid;

			fmgr_info(get_opcode(expr->opno), &opproc);

			/* extract the var/expr and const from the expression */
			if (!examine_opclause_args(expr->args, &clause_expr, &cst, &expronleft))
				elog(ERROR, "incompatible clause");

			/* match the attribute/expression to a dimension of the statistic */
			idx = mcv_match_expression(clause_expr, keys, exprs, &collid);

			/*
			 * Walk through the MCV items and evaluate the current clause. We
			 * can skip items that were already ruled out, and terminate if
			 * there are no remaining MCV items that might possibly match.
			 */
			for (uint32 i = 0; i < mcvlist->nitems; i++)
			{
				bool		match = true;
				MCVItem    *item = &mcvlist->items[i];

				Assert(idx >= 0);

				/*
				 * When the MCV item or the Const value is NULL we can treat
				 * this as a mismatch. We must not call the operator because
				 * of strictness.
				 */
				if (item->isnull[idx] || cst->constisnull)
				{
					matches[i] = RESULT_MERGE(matches[i], is_or, false);
					continue;
				}

				/*
				 * Skip MCV items that can't change result in the bitmap. Once
				 * the value gets false for AND-lists, or true for OR-lists,
				 * we don't need to look at more clauses.
				 */
				if (RESULT_IS_FINAL(matches[i], is_or))
					continue;

				/*
				 * First check whether the constant is below the lower
				 * boundary (in that case we can skip the bucket, because
				 * there's no overlap).
				 *
				 * We don't store collations used to build the statistics, but
				 * we can use the collation for the attribute itself, as
				 * stored in varcollid. We do reset the statistics after a
				 * type change (including collation change), so this is OK.
				 * For expressions, we use the collation extracted from the
				 * expression itself.
				 */
				if (expronleft)
					match = DatumGetBool(FunctionCall2Coll(&opproc,
														   collid,
														   item->values[idx],
														   cst->constvalue));
				else
					match = DatumGetBool(FunctionCall2Coll(&opproc,
														   collid,
														   cst->constvalue,
														   item->values[idx]));

				/* update the match bitmap with the result */
				matches[i] = RESULT_MERGE(matches[i], is_or, match);
			}
		}
		else if (IsA(clause, ScalarArrayOpExpr))
		{
			ScalarArrayOpExpr *expr = (ScalarArrayOpExpr *) clause;
			FmgrInfo	opproc;

			/* valid only after examine_opclause_args returns true */
			Node	   *clause_expr;
			Const	   *cst;
			bool		expronleft;
			Oid			collid;
			int			idx;

			/* array evaluation */
			ArrayType  *arrayval;
			int16		elmlen;
			bool		elmbyval;
			char		elmalign;
			int			num_elems;
			Datum	   *elem_values;
			bool	   *elem_nulls;

			fmgr_info(get_opcode(expr->opno), &opproc);

			/* extract the var/expr and const from the expression */
			if (!examine_opclause_args(expr->args, &clause_expr, &cst, &expronleft))
				elog(ERROR, "incompatible clause");

			/* We expect Var on left */
			if (!expronleft)
				elog(ERROR, "incompatible clause");

			/*
			 * Deconstruct the array constant, unless it's NULL (we'll cover
			 * that case below)
			 */
			if (!cst->constisnull)
			{
				arrayval = DatumGetArrayTypeP(cst->constvalue);
				get_typlenbyvalalign(ARR_ELEMTYPE(arrayval),
									 &elmlen, &elmbyval, &elmalign);
				deconstruct_array(arrayval,
								  ARR_ELEMTYPE(arrayval),
								  elmlen, elmbyval, elmalign,
								  &elem_values, &elem_nulls, &num_elems);
			}

			/* match the attribute/expression to a dimension of the statistic */
			idx = mcv_match_expression(clause_expr, keys, exprs, &collid);

			/*
			 * Walk through the MCV items and evaluate the current clause. We
			 * can skip items that were already ruled out, and terminate if
			 * there are no remaining MCV items that might possibly match.
			 */
			for (uint32 i = 0; i < mcvlist->nitems; i++)
			{
				int			j;
				bool		match = !expr->useOr;
				MCVItem    *item = &mcvlist->items[i];

				/*
				 * When the MCV item or the Const value is NULL we can treat
				 * this as a mismatch. We must not call the operator because
				 * of strictness.
				 */
				if (item->isnull[idx] || cst->constisnull)
				{
					matches[i] = RESULT_MERGE(matches[i], is_or, false);
					continue;
				}

				/*
				 * Skip MCV items that can't change result in the bitmap. Once
				 * the value gets false for AND-lists, or true for OR-lists,
				 * we don't need to look at more clauses.
				 */
				if (RESULT_IS_FINAL(matches[i], is_or))
					continue;

				for (j = 0; j < num_elems; j++)
				{
					Datum		elem_value = elem_values[j];
					bool		elem_isnull = elem_nulls[j];
					bool		elem_match;

					/* NULL values always evaluate as not matching. */
					if (elem_isnull)
					{
						match = RESULT_MERGE(match, expr->useOr, false);
						continue;
					}

					/*
					 * Stop evaluating the array elements once we reach a
					 * matching value that can't change - ALL() is the same as
					 * AND-list, ANY() is the same as OR-list.
					 */
					if (RESULT_IS_FINAL(match, expr->useOr))
						break;

					elem_match = DatumGetBool(FunctionCall2Coll(&opproc,
																collid,
																item->values[idx],
																elem_value));

					match = RESULT_MERGE(match, expr->useOr, elem_match);
				}

				/* update the match bitmap with the result */
				matches[i] = RESULT_MERGE(matches[i], is_or, match);
			}
		}
		else if (IsA(clause, NullTest))
		{
			NullTest   *expr = (NullTest *) clause;
			Node	   *clause_expr = (Node *) (expr->arg);

			/* match the attribute/expression to a dimension of the statistic */
			int			idx = mcv_match_expression(clause_expr, keys, exprs, NULL);

			/*
			 * Walk through the MCV items and evaluate the current clause. We
			 * can skip items that were already ruled out, and terminate if
			 * there are no remaining MCV items that might possibly match.
			 */
			for (uint32 i = 0; i < mcvlist->nitems; i++)
			{
				bool		match = false;	/* assume mismatch */
				MCVItem    *item = &mcvlist->items[i];

				/* if the clause mismatches the MCV item, update the bitmap */
				switch (expr->nulltesttype)
				{
					case IS_NULL:
						match = (item->isnull[idx]) ? true : match;
						break;

					case IS_NOT_NULL:
						match = (!item->isnull[idx]) ? true : match;
						break;
				}

				/* now, update the match bitmap, depending on OR/AND type */
				matches[i] = RESULT_MERGE(matches[i], is_or, match);
			}
		}
		else if (is_orclause(clause) || is_andclause(clause))
		{
			/* AND/OR clause, with all subclauses being compatible */

			BoolExpr   *bool_clause = ((BoolExpr *) clause);
			List	   *bool_clauses = bool_clause->args;

			/* match/mismatch bitmap for each MCV item */
			bool	   *bool_matches = NULL;

			Assert(bool_clauses != NIL);
			Assert(list_length(bool_clauses) >= 2);

			/* build the match bitmap for the OR-clauses */
			bool_matches = mcv_get_match_bitmap(root, bool_clauses, keys, exprs,
												mcvlist, is_orclause(clause));

			/*
			 * Merge the bitmap produced by mcv_get_match_bitmap into the
			 * current one. We need to consider if we're evaluating AND or OR
			 * condition when merging the results.
			 */
			for (uint32 i = 0; i < mcvlist->nitems; i++)
				matches[i] = RESULT_MERGE(matches[i], is_or, bool_matches[i]);

			pfree(bool_matches);
		}
		else if (is_notclause(clause))
		{
			/* NOT clause, with all subclauses compatible */

			BoolExpr   *not_clause = ((BoolExpr *) clause);
			List	   *not_args = not_clause->args;

			/* match/mismatch bitmap for each MCV item */
			bool	   *not_matches = NULL;

			Assert(not_args != NIL);
			Assert(list_length(not_args) == 1);

			/* build the match bitmap for the NOT-clause */
			not_matches = mcv_get_match_bitmap(root, not_args, keys, exprs,
											   mcvlist, false);

			/*
			 * Merge the bitmap produced by mcv_get_match_bitmap into the
			 * current one. We're handling a NOT clause, so invert the result
			 * before merging it into the global bitmap.
			 */
			for (uint32 i = 0; i < mcvlist->nitems; i++)
				matches[i] = RESULT_MERGE(matches[i], is_or, !not_matches[i]);

			pfree(not_matches);
		}
		else if (IsA(clause, Var))
		{
			/* Var (has to be a boolean Var, possibly from below NOT) */

			Var		   *var = (Var *) (clause);

			/* match the attribute to a dimension of the statistic */
			int			idx = bms_member_index(keys, var->varattno);

			Assert(var->vartype == BOOLOID);

			/*
			 * Walk through the MCV items and evaluate the current clause. We
			 * can skip items that were already ruled out, and terminate if
			 * there are no remaining MCV items that might possibly match.
			 */
			for (uint32 i = 0; i < mcvlist->nitems; i++)
			{
				MCVItem    *item = &mcvlist->items[i];
				bool		match = false;

				/* if the item is NULL, it's a mismatch */
				if (!item->isnull[idx] && DatumGetBool(item->values[idx]))
					match = true;

				/* update the result bitmap */
				matches[i] = RESULT_MERGE(matches[i], is_or, match);
			}
		}
		else
		{
			/* Otherwise, it must be a bare boolean-returning expression */
			int			idx;

			/* match the expression to a dimension of the statistic */
			idx = mcv_match_expression(clause, keys, exprs, NULL);

			/*
			 * Walk through the MCV items and evaluate the current clause. We
			 * can skip items that were already ruled out, and terminate if
			 * there are no remaining MCV items that might possibly match.
			 */
			for (uint32 i = 0; i < mcvlist->nitems; i++)
			{
				bool		match;
				MCVItem    *item = &mcvlist->items[i];

				/* "match" just means it's bool TRUE */
				match = !item->isnull[idx] && DatumGetBool(item->values[idx]);

				/* now, update the match bitmap, depending on OR/AND type */
				matches[i] = RESULT_MERGE(matches[i], is_or, match);
			}
		}
	}

	return matches;
}


/*
 * ============================================================================
 * 【中文注释】mcv_combine_selectivities —— 合并单列与多元 MCV 的选择性估计
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把"仅用单列统计、假设列独立"得到的简单选择性（simple_sel）与基于多元 MCV
 *   统计的估计结合起来，得到最终的选择性。
 *
 * 参数：
 *   simple_sel  - 简单选择性：不使用任何扩展统计，本质上假设列/子句相互独立。
 *   mcv_sel     - 所有"匹配"MCV 项的频率之和。
 *   mcv_basesel - 所有匹配 MCV 项的 base_frequency 之和。
 *   mcv_totalsel- 全部 MCV 项频率之和（无论是否匹配），作为"未覆盖部分"的上界。
 *
 * 返回值：
 *   Selectivity - 合并后的选择性（在 [0,1] 内）。
 *
 * 设计思想：
 *   1. 记 mcv_basesel 是"MCV 匹配项在列独立假设下的总选择性"，而 simple_sel 是
 *      "无扩展统计时的估计"。二者计算方式不同（前者=匹配项 base_frequency 求和，
 *      后者=各子句估计乘积），故通常不等，差异来自：(a) MCV 列表未覆盖全部数据、
 *      (b) 部分 MCV 项未匹配当前子句。
 *   2. 由于 (a)(b) 都会压低 mcv_basesel，一般 simple_sel >= mcv_basesel；若 MCV
 *      覆盖全部数据，二者可能相等。
 *   3. 合并公式：
 *        other_sel = clamp(simple_sel - mcv_basesel)   // 未被 MCV 覆盖部分的估计
 *        且 other_sel 不能超过 1 - mcv_totalsel
 *        sel = mcv_sel + other_sel                      // MCV 部分 + 非 MCV 部分
 *   4. 即 (mcv_sel - mcv_basesel) 可视作对 simple_sel 的修正项，与上面 other_sel
 *      的表述在数学上等价。
 * ============================================================================
 */
Selectivity
mcv_combine_selectivities(Selectivity simple_sel,
						  Selectivity mcv_sel,
						  Selectivity mcv_basesel,
						  Selectivity mcv_totalsel)
{
	Selectivity other_sel;
	Selectivity sel;

	/* estimated selectivity of values not covered by MCV matches */
	other_sel = simple_sel - mcv_basesel;
	CLAMP_PROBABILITY(other_sel);

	/* this non-MCV selectivity cannot exceed 1 - mcv_totalsel */
	if (other_sel > 1.0 - mcv_totalsel)
		other_sel = 1.0 - mcv_totalsel;

	/* overall selectivity is the sum of the MCV and non-MCV parts */
	sel = mcv_sel + other_sel;
	CLAMP_PROBABILITY(sel);

	return sel;
}


/*
 * ============================================================================
 * 【中文注释】mcv_clauselist_selectivity —— 用 MCV 统计估计 AND 子句列表选择性
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   用多元 MCV 统计估计一个隐式 AND 连接的子句列表的选择性：找出哪些 MCV 项同时
 *   匹配列表中的每个子句，返回这些项的频率之和作为选择性。
 *
 * 参数：
 *   root    - PlannerInfo。
 *   stat    - 正在使用的扩展统计对象信息。
 *   clauses - 隐式 AND 的子句列表。
 *   varRelid/jointype/sjinfo/rel - 规划上下文（本函数未直接使用，保留接口一致）。
 *   basesel - 输出参数：所有匹配项 base_frequency 之和（列独立假设下各匹配项的
 *             选择性之和）。
 *   totalsel- 输出参数：全部 MCV 项频率之和（无论是否匹配）。
 *
 * 返回值：
 *   Selectivity - 匹配项的频率之和，即基于 MCV 的选择性。
 *
 * 设计思想：
 *   1. 加载统计对象存储的 MCV 列表（statext_mcv_load），继承标志取自 rel 对应
 *      的 RTE（root->simple_rte_array[rel->relid]->inh）。
 *   2. 调用 mcv_get_match_bitmap(..., is_or=false) 得到每个 item 是否匹配。
 *   3. 遍历 items：totalsel 累加所有 item 频率；对匹配项再累加 base_frequency 与
 *      频率 s。
 *   4. 返回的 s、*basesel、*totalsel 与"简单选择性"一起交给
 *      mcv_combine_selectivities() 合成最终估计（同时利用单列与多列统计）。
 * ============================================================================
 */
Selectivity
mcv_clauselist_selectivity(PlannerInfo *root, StatisticExtInfo *stat,
						   List *clauses, int varRelid,
						   JoinType jointype, SpecialJoinInfo *sjinfo,
						   RelOptInfo *rel,
						   Selectivity *basesel, Selectivity *totalsel)
{
	MCVList    *mcv;
	Selectivity s = 0.0;
	RangeTblEntry *rte = root->simple_rte_array[rel->relid];

	/* match/mismatch bitmap for each MCV item */
	bool	   *matches = NULL;

	/* load the MCV list stored in the statistics object */
	mcv = statext_mcv_load(stat->statOid, rte->inh);

	/* build a match bitmap for the clauses */
	matches = mcv_get_match_bitmap(root, clauses, stat->keys, stat->exprs,
								   mcv, false);

	/* sum frequencies for all the matching MCV items */
	*basesel = 0.0;
	*totalsel = 0.0;
	for (uint32 i = 0; i < mcv->nitems; i++)
	{
		*totalsel += mcv->items[i].frequency;

		if (matches[i] != false)
		{
			*basesel += mcv->items[i].base_frequency;
			s += mcv->items[i].frequency;
		}
	}

	return s;
}


/*
 * ============================================================================
 * 【中文注释】mcv_clause_selectivity_or —— 用 MCV 估计 OR 子句列表中单个子句的选择性
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   针对 OR 连接的子句列表中的某个子句，用 MCV 统计估计其选择性，并同时输出
 *   用于计算"OR 列表整体选择性"的重叠信息（见下述算法）。OR 列表中每个子句都要
 *   调用本函数一次。
 *
 * 参数：
 *   root / stat / mcv - 规划上下文、统计对象信息、已加载的 MCV 列表。
 *   clause   - 待估计的单个子句。
 *   or_matches - in/out 参数：累积"已评估子句"的匹配位图；首次调用时应传 NULL，
 *                函数内部首次分配并清零。
 *   basesel  - 输出：本子句匹配项的 base_frequency 之和。
 *   overlap_mcvsel / overlap_basesel - 输出：与已评估子句"重叠"（即也匹配先前
 *                某子句）的那些项的 frequency / base_frequency 之和，对应下面公式
 *                中的重叠项。
 *   totalsel - 输出：所有 MCV 项频率之和。
 *
 * 返回值：
 *   Selectivity - 本子句匹配项的 frequency 之和（该子句的选择性）。
 *
 * 设计思想：
 *   1. 令 P[n]=P(C[1] OR ... OR C[n]) 为前 n 个子句的合并选择性，则加入第 n+1
 *      个子句后：
 *          P[n+1] = P[n] + P(C[n+1]) - P((C[1] OR ... OR C[n]) AND C[n+1])
 *      末项是先前子句与新子句的重叠，通过"已评估子句位图 ∩ 新子句位图"来估计。
 *   2. 流程：若 *or_matches 为 NULL 则分配清零；用 mcv_get_match_bitmap(...,false)
 *      生成新子句的匹配位图；遍历 items 累加新子句的选择性 s、basesel，以及重叠
 *      项（同时匹配先前子句）的 overlap_mcvsel/overlap_basesel；最后把新子句的
 *      匹配并入 *or_matches（按位或）。
 *   3. 输出的 totalsel 供 mcv_combine_selectivities() 使用。
 * ============================================================================
 */
Selectivity
mcv_clause_selectivity_or(PlannerInfo *root, StatisticExtInfo *stat,
						  MCVList *mcv, Node *clause, bool **or_matches,
						  Selectivity *basesel, Selectivity *overlap_mcvsel,
						  Selectivity *overlap_basesel, Selectivity *totalsel)
{
	Selectivity s = 0.0;
	bool	   *new_matches;

	/* build the OR-matches bitmap, if not built already */
	if (*or_matches == NULL)
		*or_matches = palloc0_array(bool, mcv->nitems);

	/* build the match bitmap for the new clause */
	new_matches = mcv_get_match_bitmap(root, list_make1(clause), stat->keys,
									   stat->exprs, mcv, false);

	/*
	 * Sum the frequencies for all the MCV items matching this clause and also
	 * those matching the overlap between this clause and any of the preceding
	 * clauses as described above.
	 */
	*basesel = 0.0;
	*overlap_mcvsel = 0.0;
	*overlap_basesel = 0.0;
	*totalsel = 0.0;
	for (uint32 i = 0; i < mcv->nitems; i++)
	{
		*totalsel += mcv->items[i].frequency;

		if (new_matches[i])
		{
			s += mcv->items[i].frequency;
			*basesel += mcv->items[i].base_frequency;

			if ((*or_matches)[i])
			{
				*overlap_mcvsel += mcv->items[i].frequency;
				*overlap_basesel += mcv->items[i].base_frequency;
			}
		}

		/* update the OR-matches bitmap for the next clause */
		(*or_matches)[i] = (*or_matches)[i] || new_matches[i];
	}

	pfree(new_matches);

	return s;
}

/*
 * ============================================================================
 * 【中文注释】statext_mcv_free —— 释放 MCVList 结构
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   释放 MCVList 的内存：先释放每个 item 的 values/isnull 数组，再释放结构本身。
 *
 * 参数：
 *   mcvlist - 待释放的 MCV 列表。
 *
 * 返回值：无。
 *
 * 设计思想：
 *   反序列化/构建时每个 item 的 values、isnull 是独立 palloc 的，因此需逐项释放。
 * ============================================================================
 */
void
statext_mcv_free(MCVList *mcvlist)
{
	for (uint32 i = 0; i < mcvlist->nitems; i++)
	{
		MCVItem    *item = &mcvlist->items[i];

		pfree(item->values);
		pfree(item->isnull);
	}
	pfree(mcvlist);
}

/*
 * ============================================================================
 * 【中文注释】statext_mcv_import —— 从 SQL 导入 MCV 列表并序列化
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把用户通过 SQL 提供的 MCV 元素数组组装成 MCVList 并序列化为 bytea（pg_mcv_list
 *   值），用于 pg_restore_extended_stats() 等导入场景。
 *
 * 参数：
 *   elevel      - 出错时的错误级别（< ERROR 时返回 NULL Datum 而非抛错）。
 *   numattrs    - 维度（列）个数。
 *   atttypids   - 每列的类型 OID。
 *   atttypmods  - 每列的 typmod。
 *   atttypcolls - 每列的排序规则。
 *   nitems      - MCV 项个数。
 *   mcv_elems   - 长度 numitems*numattrs 的元素数组（列主序存储）。
 *   mcv_nulls   - 对应的 NULL 标志数组。
 *   freqs / base_freqs - 每项的实际频率与独立假设频率。
 *
 * 返回值：
 *   Datum - 序列化后的 bytea Datum；任何元素转换失败且 elevel<ERROR 时返回
 *           (Datum) 0。
 *
 * 设计思想：
 *   1. 分配 MCVList，填头部（magic/type/ndimensions/nitems）与每项的 frequency、
 *      base_frequency。
 *   2. 逐"列"处理：取该列类型的输入函数（getTypeInputInfo），对该列的所有值用
 *      InputFunctionCallSafe 做文本→类型转换；NULL 值跳过输入（isnull 置 true）。
 *      转换失败按 elevel 报错并跳转到 error 标签。
 *   3. statext_mcv_serialize() 需要 VacAttrStats 数组，此处用类型元组构造一份只含
 *      attrtype/attrtypid/attrcollid 的轻量 VacAttrStats。
 *   4. 序列化后释放临时内存；bytes 为 NULL（如序列化失败）时按 elevel 报错。
 *   5. error 标签统一释放 mcvlist 并返回 (Datum) 0。
 * ============================================================================
 */
Datum
statext_mcv_import(int elevel, int numattrs,
				   Oid *atttypids, int32 *atttypmods, Oid *atttypcolls,
				   int nitems, Datum *mcv_elems, bool *mcv_nulls,
				   float8 *freqs, float8 *base_freqs)
{
	MCVList    *mcvlist;
	bytea	   *bytes;
	VacAttrStats **vastats;

	/*
	 * Allocate the MCV list structure, set the global parameters.
	 */
	mcvlist = (MCVList *) palloc0(offsetof(MCVList, items) +
								  (sizeof(MCVItem) * nitems));

	mcvlist->magic = STATS_MCV_MAGIC;
	mcvlist->type = STATS_MCV_TYPE_BASIC;
	mcvlist->ndimensions = numattrs;
	mcvlist->nitems = nitems;

	/* Set the values for the 1-D arrays and allocate space for the 2-D arrays */
	for (int i = 0; i < nitems; i++)
	{
		MCVItem    *item = &mcvlist->items[i];

		item->frequency = freqs[i];
		item->base_frequency = base_freqs[i];
		item->values = (Datum *) palloc0_array(Datum, numattrs);
		item->isnull = (bool *) palloc0_array(bool, numattrs);
	}

	/*
	 * Walk through each dimension, determine the input function for that
	 * type, and then attempt to convert all values in that column via that
	 * function.  We approach this column-wise because it is simpler to deal
	 * with one input function at time, and possibly more cache-friendly.
	 */
	for (int j = 0; j < numattrs; j++)
	{
		FmgrInfo	finfo;
		Oid			ioparam;
		Oid			infunc;
		int			index = j;

		getTypeInputInfo(atttypids[j], &infunc, &ioparam);
		fmgr_info(infunc, &finfo);

		/* store info about data type OIDs */
		mcvlist->types[j] = atttypids[j];

		for (int i = 0; i < nitems; i++)
		{
			MCVItem    *item = &mcvlist->items[i];

			if (mcv_nulls[index])
			{
				/* NULL value detected, hence no input to process */
				item->values[j] = (Datum) 0;
				item->isnull[j] = true;
			}
			else
			{
				char	   *s = TextDatumGetCString(mcv_elems[index]);
				ErrorSaveContext escontext = {T_ErrorSaveContext};

				if (!InputFunctionCallSafe(&finfo, s, ioparam, atttypmods[j],
										   (Node *) &escontext, &item->values[j]))
				{
					ereport(elevel,
							(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
							 errmsg("could not parse MCV element \"%s\": incorrect value", s)));
					pfree(s);
					goto error;
				}

				pfree(s);
			}

			index += numattrs;
		}
	}

	/*
	 * The function statext_mcv_serialize() requires an array of pointers to
	 * VacAttrStats records, but only a few fields within those records have
	 * to be filled out.
	 */
	vastats = (VacAttrStats **) palloc0_array(VacAttrStats *, numattrs);

	for (int i = 0; i < numattrs; i++)
	{
		Oid			typid = atttypids[i];
		HeapTuple	typtuple;

		typtuple = SearchSysCacheCopy1(TYPEOID, ObjectIdGetDatum(typid));

		if (!HeapTupleIsValid(typtuple))
			elog(ERROR, "cache lookup failed for type %u", typid);

		vastats[i] = palloc0_object(VacAttrStats);

		vastats[i]->attrtype = (Form_pg_type) GETSTRUCT(typtuple);
		vastats[i]->attrtypid = typid;
		vastats[i]->attrcollid = atttypcolls[i];
	}

	bytes = statext_mcv_serialize(mcvlist, vastats);

	for (int i = 0; i < numattrs; i++)
	{
		pfree(vastats[i]);
	}
	pfree((void *) vastats);

	pfree(mcv_elems);
	pfree(mcv_nulls);

	if (bytes == NULL)
	{
		ereport(elevel,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("could not import MCV list")));
		goto error;
	}

	return PointerGetDatum(bytes);

error:
	statext_mcv_free(mcvlist);
	return (Datum) 0;
}
