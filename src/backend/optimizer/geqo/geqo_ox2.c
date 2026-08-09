/*------------------------------------------------------------------------
*
* geqo_ox2.c
*
*	 order crossover [OX] routines;
*	 OX2 operator according to Syswerda
*	 (The Genetic Algorithms Handbook, ed L Davis)
*
 * src/backend/optimizer/geqo/geqo_ox2.c
 *
 * 【模块总览(中文)】
 * 本文件实现"顺序交叉"(Order Crossover,OX2)算子的第二种变体,源自
 * Syswerda(The Genetic Algorithms Handbook,ed L Davis)。OX2 与 OX1 都是
 * 基于位置的顺序交叉,由 geqo.h 的 #define OX2 启用,由 geqo_main.c 在
 * 演化循环中调用。
 *
 * 与 OX1 最大的区别在于继承方式:
 * - OX1 继承的是"父代一的一段连续位置区间";
 * - OX2 继承的是"父代一中的若干个随机位置(不连续)":先随机选出
 *   [num_gene/3, 2*num_gene/3] 个位置,把 tour1 在这些位置上的城市原样
 *   搬到子代对应位置(同时标记城市已用);其余位置,按 tour2 的城市顺序,
 *   把未用城市依次放入(即这些位置上的城市排列保持 tour2 的相对顺序)。
 * 这样既保留了父代一在"关键位置"的基因,又保留了父代二的整体排列顺序,
 * 是一种更分散的基因继承策略。
 *
 * 辅助数据结构:
 * - City.select_list:长度 num_gene 的临时数组(复用城市表),记录"被选中
 *   继承的位置 → 该位置来自 tour1 的城市"。OX2 需要额外的一步——把散落
 *   的选中位置"压实"(consolidate)到数组前部,形成一个紧凑的选择列表,
 *   便于按序取出;
 * - City.used:标记某城市是否已被继承,用于判断 tour2 中哪些城市还能用。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_ox2.c
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

/* the ox algorithm is adopted from Genitor : */
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
#include "optimizer/geqo.h"

#if defined(OX2)

#include "optimizer/geqo_random.h"
#include "optimizer/geqo_recombination.h"

/*
 * ox2
 *
 *	 position crossover
 */
/*
 * ox2 - (中文)顺序交叉算子(OX2):继承父代一的随机位置、父代二的相对顺序
 *
 * 【作用】由父代 tour1、tour2 生成子代 offspring:随机挑选 tour1 的若干
 * 位置(数目在 [num_gene/3, 2*num_gene/3] 间),这些位置的城市原样继承;
 * 其余位置按 tour2 的城市顺序填充未用城市。由 geqo_main.c 在 #define OX2
 * 模式下每代调用。结果仍是合法置换。
 *
 * 【设计思想】四步走:
 * 1. 初始化:清零 city_table[k].used(城市占用标记),并把 select_list
 *    全部置为 -1(空槽哨兵;注意初始化循环从 k-1 下标开始写,即覆盖
 *    city_table[0..num_gene-1] 的 select_list 字段);
 * 2. 选位置:num_positions 在 [num_gene/3, 2*num_gene/3] 间随机;重复随机
 *    抽取位置 pos(允许重复,若重复则覆盖 select_list 并再次标记 used,
 *    实际继承的位置数可能略少于 num_positions),把 tour1[pos] 记录到
 *    city_table[pos].select_list,并把该城市标为 used;
 * 3. 压实(consolidate):让选中位置紧凑排列在 select_list 前部——扫描
 *    k=0..,遇到空槽(-1)就向后找第一个非空槽 j,把 select_list[j] 的值搬
 *    到 k 并清空 j;这样前 num_positions 个元素即所有被选中的(tour1 中)
 *    城市,按被压实后的顺序排队;
 * 4. 生成子代:按 k=0..num_gene-1 扫描 tour2,若 tour2[k] 已被继承(used)
 *    说明该位置应当放入"被选中的城市",从压实列表依次取出
 *    (offspring[k] = select_list[select++]);否则该位置保持 tour2 的基因。
 *    最终:被选位置的城市 = 来自 tour1 的被选集合(顺序按压实列表),
 *    其余位置 = tour2 未用城市的相对顺序,集合完整且无重复。
 *
 * 【参数】
 *   root       —— PlannerInfo,传给随机数接口;
 *   tour1      —— 父代一(被选中位置的城市来源);
 *   tour2      —— 父代二(其余城市顺序来源);
 *   offspring  —— 输出,子代路径;
 *   num_gene   —— 城市个数;
 *   city_table —— 长度 num_gene+1 的城市表,同时使用 used 与 select_list。
 * 【返回值】无。
 */
void
ox2(PlannerInfo *root, Gene *tour1, Gene *tour2, Gene *offspring, int num_gene, City * city_table)
{
	int			k,
				j,
				count,
				pos,
				select,
				num_positions;

	/* initialize city table */
	for (k = 1; k <= num_gene; k++)
	{
		city_table[k].used = 0;
		city_table[k - 1].select_list = -1;
	}

	/* determine the number of positions to be inherited from tour1  */
	num_positions = geqo_randint(root, 2 * num_gene / 3, num_gene / 3);

	/* make a list of selected cities */
	for (k = 0; k < num_positions; k++)
	{
		pos = geqo_randint(root, num_gene - 1, 0);
		city_table[pos].select_list = (int) tour1[pos];
		city_table[(int) tour1[pos]].used = 1;	/* mark used */
	}


	count = 0;
	k = 0;

	/* consolidate the select list to adjacent positions */
	while (count < num_positions)
	{
		if (city_table[k].select_list == -1)
		{
			j = k + 1;
			while ((city_table[j].select_list == -1) && (j < num_gene))
				j++;

			city_table[k].select_list = city_table[j].select_list;
			city_table[j].select_list = -1;
			count++;
		}
		else
			count++;
		k++;
	}

	select = 0;

	for (k = 0; k < num_gene; k++)
	{
		if (city_table[(int) tour2[k]].used)
		{
			offspring[k] = (Gene) city_table[select].select_list;
			select++;			/* next city in  the select list   */
		}
		else
			/* city isn't used yet, so inherit from tour2 */
			offspring[k] = tour2[k];
	}
}

#endif							/* defined(OX2) */
