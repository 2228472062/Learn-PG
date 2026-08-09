/*------------------------------------------------------------------------
 *
 * geqo_misc.c
 *	   misc. printout and debug stuff
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/optimizer/geqo/geqo_misc.c
 *
 * 【模块总览(中文)】
 * 本文件提供 GEQO 的调试与状态输出工具,全部函数都包裹在
 * #ifdef GEQO_DEBUG 中,仅在编译期启用了 GEQO_DEBUG 宏时才会被编译进
 * 代码。GEQO 的正常运行完全不依赖本文件,它只服务于开发者观察遗传算法
 * 的演化过程。
 *
 * 功能清单:
 * - avg_pool:计算种群池所有个体适应度的平均值(静态辅助函数);
 * - print_pool:把池中指定下标区间[start, stop)的个体以"下标、基因串、
 *   适应度"格式打印到文件;
 * - print_gen:打印某一世代的统计摘要——最优(Best)、最差(Worst)、中位
 *   数(Mean)、平均值(Avg),由 geqo_main.c 的演化循环按固定世代间隔调用;
 * - print_edge_table:打印 ERX 边表的内容,便于调试边重组算子。
 *
 * 输出约定:适应度用 %g 浮点格式,基因串用空格分隔的城市号;所有输出以
 * fflush 立即刷到文件,保证调试信息即使程序崩溃也不会滞留在缓冲区。
 * 本文件依赖 geqo_pool.h(Pool 结构)、geqo_recombination.h(Edge 结构)中
 * 的数据结构定义。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_misc.c
 *
 *-------------------------------------------------------------------------
 */

/*
 * contributed by:
 * =*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=
 * *  Martin Utesch				 * Institute of Automatic Control	   *
 * =							 = University of Mining and Technology =
 * *  utesch@aut.tu-freiberg.de  * Freiberg, Germany				   *
 * =*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=
 */

#include "postgres.h"

#include "optimizer/geqo_misc.h"


#ifdef GEQO_DEBUG


/*
 * avg_pool
 */
/*
 * avg_pool - (中文)计算种群池适应度的平均值
 *
 * 【作用】返回池中所有个体 worth 的算术平均值。仅被 print_gen 调用,用于
 * 调试输出中展示种群的总体健康程度。
 *
 * 【设计思想】累加时先除以 pool->size 再求和,而不是先求和再除,以规避
 * 溢出:池中可能出现多个 DBL_MAX 的个体(非法个体未被丢弃时),直接累加
 * 会迅速溢出为 NaN/Inf;先除再和虽然损失一点精度与速度,但对调试打印
 * 完全可接受。入口先做防御检查:池规模 <= 0 时 elog(ERROR)。注意本函数
 * 假设池已按 worth 排序,但排序对本函数无影响(均值与顺序无关)。
 *
 * 【参数】pool —— 种群池(只读)。
 * 【返回值】所有个体 worth 的平均值。
 */
static double
avg_pool(Pool *pool)
{
	int			i;
	double		cumulative = 0.0;

	if (pool->size <= 0)
		elog(ERROR, "pool_size is zero");

	/*
	 * Since the pool may contain multiple occurrences of DBL_MAX, divide by
	 * pool->size before summing, not after, to avoid overflow.  This loses a
	 * little in speed and accuracy, but this routine is only used for debug
	 * printouts, so we don't care that much.
	 */
	for (i = 0; i < pool->size; i++)
		cumulative += pool->data[i].worth / pool->size;

	return cumulative;
}

/*
 * print_pool
 */
/*
 * print_pool - (中文)打印种群池指定区间内的个体
 *
 * 【作用】把池中下标 [start, stop) 的每个个体以一行"下标 \t 基因串 \t
 * 适应度"的格式输出到文件 fp。由 geqo_main.c 在 GEQO_DEBUG 下打印整个
 * 池(调用 start=0, stop=pool_size-1)。
 *
 * 【设计思想】入口对 start/stop 做多层防御校验:start < 0 归零、stop 超过
 * 池规模则截断、若 start + stop > 池规模(说明区间参数混乱)直接重置为
 * 整个池。这些防御保证调试打印不会越界访问 pool->data。循环内逐个体打印:
 * 下标 i、逐基因输出城市号(空格分隔)、最后输出 worth(%g)。末尾 fflush
 * 确保输出立即落盘。本函数依赖池的字符串长度 pool->string_length 来遍历
 * 基因串。
 *
 * 【参数】
 *   fp    —— 输出文件流;
 *   pool  —— 种群池(只读);
 *   start —— 起始下标(含);
 *   stop  —— 结束下标(不含)。
 * 【返回值】无。
 */
void
print_pool(FILE *fp, Pool *pool, int start, int stop)
{
	int			i,
				j;

	/* be extra careful that start and stop are valid inputs */

	if (start < 0)
		start = 0;
	if (stop > pool->size)
		stop = pool->size;

	if (start + stop > pool->size)
	{
		start = 0;
		stop = pool->size;
	}

	for (i = start; i < stop; i++)
	{
		fprintf(fp, "%d)\t", i);
		for (j = 0; j < pool->string_length; j++)
			fprintf(fp, "%d ", pool->data[i].string[j]);
		fprintf(fp, "%g\n", pool->data[i].worth);
	}

	fflush(fp);
}

/*
 * print_gen
 *
 *	 printout for chromosome: best, worst, mean, average
 */
/*
 * print_gen - (中文)打印某一世代的种群统计摘要
 *
 * 【作用】输出当前世代号 generation 及该世代时池的统计指标:最优
 * (Best=data[0])、最差(Worst)、中位数(Mean)、平均值(Avg)。由
 * geqo_main.c 在演化循环中按 status_interval(默认 10)代间隔调用,用于
 * 观察收敛进度。
 *
 * 【设计思想】依赖池按 worth 升序排序的不变量:data[0] 恒为最优,
 * data[size/2] 为近似中位数,末尾为最差。最差的取法有个细节:取
 * pool->size - 2 而非末尾——因为池中最后一个槽位(size-1)在演化中常被
 * 作为"缓冲区"(新个体先写入末尾再轮转到正确位置,见 spread_chromo),
 * 取值不可靠;若池规模只有 1,则退化为取 data[0]。均值由 avg_pool 计算
 * (已处理 DBL_MAX 溢出)。输出格式 "%5d | Best: %g  Worst: %g  Mean: %g
 *  Avg: %g\n" 后紧跟 fflush。
 *
 * 【参数】
 *   fp         —— 输出文件流;
 *   pool       —— 已排序的种群池(只读);
 *   generation —— 当前世代号。
 * 【返回值】无。
 */
void
print_gen(FILE *fp, Pool *pool, int generation)
{
	int			lowest;

	/* Get index to lowest ranking gene in population. */
	/* Use 2nd to last since last is buffer. */
	lowest = pool->size > 1 ? pool->size - 2 : 0;

	fprintf(fp,
			"%5d | Best: %g  Worst: %g  Mean: %g  Avg: %g\n",
			generation,
			pool->data[0].worth,
			pool->data[lowest].worth,
			pool->data[pool->size / 2].worth,
			avg_pool(pool));

	fflush(fp);
}


/*
 * print_edge_table - (中文)打印 ERX 边表内容
 *
 * 【作用】把边表每个城市(1..num_gene)及其当前未使用的相邻城市列表打印
 * 到文件 fp,用于调试边重组交叉算子(geqo_erx.c)的中间状态。
 *
 * 【设计思想】只打印 unused_edges 个条目(未用边),因为它们才是算法后续
 * 会用到的候选;已用边(被 -1 哨兵剔除或已消费)不展示。打印内容为城市号
 * 和其 edge_list 原始值——负值代表共享边,便于观察共享边分布。格式为
 * "城市号 : 邻居列表",末尾空行分隔,随后 fflush。仅供 GEQO_DEBUG 使用,
 * 不影响算法任何状态(只读)。
 *
 * 【参数】
 *   fp         —— 输出文件流;
 *   edge_table —— ERX 边表(只读),下标 1..num_gene 有效;
 *   num_gene   —— 城市个数。
 * 【返回值】无。
 */
void
print_edge_table(FILE *fp, Edge *edge_table, int num_gene)
{
	int			i,
				j;

	fprintf(fp, "\nEDGE TABLE\n");

	for (i = 1; i <= num_gene; i++)
	{
		fprintf(fp, "%d :", i);
		for (j = 0; j < edge_table[i].unused_edges; j++)
			fprintf(fp, " %d", edge_table[i].edge_list[j]);
		fprintf(fp, "\n");
	}

	fprintf(fp, "\n");

	fflush(fp);
}

#endif							/* GEQO_DEBUG */
