/*-------------------------------------------------------------------------
 *
 * geqo_selection.c
 *	  linear selection scheme for the genetic query optimizer
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/optimizer/geqo/geqo_selection.c
 *
 * 【模块总览(中文)】
 * 本文件实现 GEQO 的"选择算子"(selection),即遗传算法"选择—交叉—
 * 变异"流程中的第一步:按个体适应度从种群池中挑选两个父代(momma 与
 * daddy)用于繁殖下一代。
 *
 * 选择策略是"线性偏差选择"(linear bias selection):以线性概率密度函数
 * f(x) = bias - 2(bias - 1)x 对池下标 x(0..pool_size)抽样。bias 是 GUC
 * 参数 Geqo_selection_bias(默认 2.0),表示"第一名被选中的概率是中间名
 * 被选中概率的多少倍"。bias 越大,越偏向池中最优个体(贪婪);bias = 1
 * 时退化为均匀随机。线性而非指数分布,是为了在"偏向最优"与"保留多样性"
 * 之间取平衡——最优个体有更高概率被选,但较差个体仍有机会参与繁殖。
 *
 * 该概率分布的逆变换抽样在 linear_rand 中实现:通过求解一元二次方程把
 * 均匀随机数 u 映射为满足 f 分布的池下标。geqo_selection 则负责调用两次
 * linear_rand,并保证选出的两个父代不是同一个个体(池规模为 1 时除外,
 * 此时只能允许相同),随后用 geqo_copy 把选中的个体内容复制到调用方提供
 * 的 momma/daddy 工作缓冲区,供后续交叉算子使用。
 *
 * 本模块与 geqo_random.c(随机源)、geqo_copy.c(个体拷贝)、geqo_pool.c
 * (池的排序不变量 data[0] 最优)紧密配合,是演化循环(geqo_main.c)中
 * 每代的第一步。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_selection.c
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

/* this is adopted from D. Whitley's Genitor algorithm */

/*************************************************************/
/*															 */
/*	Copyright (c) 1990										 */
/*	Darrell L. Whitley										 */
/*	Computer Science Department								 */
/*	Colorado State University								 */
/*															 */
/*	Permission is hereby granted to copy all or any part of  */
/*	this program for free distribution.   The author's name  */
/*	and this copyright notice must be included in any copy.  */
/*															 */
/*************************************************************/

#include "postgres.h"

#include <math.h>

#include "optimizer/geqo_copy.h"
#include "optimizer/geqo_random.h"
#include "optimizer/geqo_selection.h"

static int	linear_rand(PlannerInfo *root, int pool_size, double bias);


/*
 * geqo_selection
 *	 according to bias described by input parameters,
 *	 first and second genes are selected from the pool
 */
/*
 * geqo_selection - (中文)按线性偏差从种群池中选出两个父代
 *
 * 【作用】依据线性偏差分布,从池中独立随机抽取两个下标 first、second,
 * 把对应个体分别复制到 momma 与 daddy 染色体中。由 geqo_main.c 在演化
 * 循环的每一代开头调用,是每代遗传操作的第一步。
 *
 * 【设计思想】父代选择质量决定遗传算法的收敛方向:bias 偏大时 high-rank
 * (靠前、适应度好)个体被选概率更高,推动种群向最优解收敛;但若完全不
 * 给差个体机会,会过早丢失多样性、陷入局部最优。线性分布正是这两者间的
 * 折中。两个父代各自独立抽样,但要求 first != second(池规模 > 1 时):
 * 若两次抽到同一个体,就重抽 second,保证"交叉"在两个不同个体间进行,
 * 否则重组退化为复制、失去探索意义。抽到的个体内容是浅指针(指向池内),
 * 必须用 geqo_copy 深拷贝到 momma/daddy 工作区——后续交叉算子会改写
 * momma->string,若共享指针会污染池内数据。
 *
 * 【参数】
 *   root   —— PlannerInfo,传给随机数接口与 geqo_copy;
 *   momma  —— 输出,父代一(调用方分配,内容被覆盖);
 *   daddy  —— 输出,父代二(调用方分配,内容被覆盖);
 *   pool   —— 已排序的种群池(data[0] 最优),只读;
 *   bias   —— 线性偏差参数(通常为 GUC Geqo_selection_bias,默认 2.0)。
 * 【返回值】无。
 */
void
geqo_selection(PlannerInfo *root, Chromosome *momma, Chromosome *daddy,
			   Pool *pool, double bias)
{
	int			first,
				second;

	first = linear_rand(root, pool->size, bias);
	second = linear_rand(root, pool->size, bias);

	/*
	 * Ensure we have selected different genes, except if pool size is only
	 * one, when we can't.
	 */
	if (pool->size > 1)
	{
		while (first == second)
			second = linear_rand(root, pool->size, bias);
	}

	geqo_copy(root, momma, &pool->data[first], pool->string_length);
	geqo_copy(root, daddy, &pool->data[second], pool->string_length);
}

/*
 * linear_rand
 *	  generates random integer between 0 and input max number
 *	  using input linear bias
 *
 *	  bias is y-intercept of linear distribution
 *
 *	  probability distribution function is: f(x) = bias - 2(bias - 1)x
 *			 bias = (prob of first rule) / (prob of middle rule)
 */
/*
 * linear_rand - (中文)按线性偏差分布抽样一个池下标
 *
 * 【作用】生成服从 f(x) = bias - 2(bias - 1)x 概率密度的池下标,即返回
 * [0, pool_size) 内的随机整数,取值越靠前(适应度越好)概率越大。由
 * geqo_selection 调用两次,分别决定 momma 与 daddy。
 *
 * 【设计思想】采用"逆变换抽样"(inverse transform sampling):先取均匀
 * 随机数 u = geqo_rand(root) ∈ [0,1),再解 f 对应的累积分布函数
 * F(x) = bias·x - (bias-1)·x² = u,得到 x = [bias - sqrt(bias² - 4(bias-1)u)]
 * / (2(bias-1)),即把均匀分布"弯"成线性递减分布。sqrt 里若为 0(理论上
 * u 恰使判别式为 0)则跳过开方直接按 0 处理。随后 index = max * 该根,
 * 把它缩放到 [0, pool_size)。由于浮点误差可能使 index 越界(负或 >= max),
 * 且 geqo_rand 理论上不可能返回 1.0(若异常返回则 index 恰好等于 max),
 * 用 do/while 循环重试直至 index ∈ [0, max),再截断为 int。返回 0 的概率
 * 最高,随下标增大概率递减,pool 靠前的最优个体由此获得更高选中率。
 *
 * 【参数】
 *   root     —— PlannerInfo,传给 geqo_rand;
 *   pool_size —— 池大小(返回值的上界);
 *   bias     —— 偏差:y 截距,取 (1, +∞) 有效;bias 越大越偏向前排。
 * 【返回值】[0, pool_size) 内的随机下标,服从线性偏差分布。
 */
static int
linear_rand(PlannerInfo *root, int pool_size, double bias)
{
	double		index;			/* index between 0 and pool_size */
	double		max = (double) pool_size;

	/*
	 * geqo_rand() is not supposed to return 1.0, but if it does then we will
	 * get exactly max from this equation, whereas we need 0 <= index < max.
	 * Also it seems possible that roundoff error might deliver values
	 * slightly outside the range; in particular avoid passing a value
	 * slightly less than 0 to sqrt().  If we get a bad value just try again.
	 */
	do
	{
		double		sqrtval;

		sqrtval = (bias * bias) - 4.0 * (bias - 1.0) * geqo_rand(root);
		if (sqrtval > 0.0)
			sqrtval = sqrt(sqrtval);
		index = max * (bias - sqrtval) / 2.0 / (bias - 1.0);
	} while (index < 0.0 || index >= max);

	return (int) index;
}
