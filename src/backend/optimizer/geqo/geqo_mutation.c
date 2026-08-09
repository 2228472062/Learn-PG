/*------------------------------------------------------------------------
*
* geqo_mutation.c
*
*	 TSP mutation routines
*
 * src/backend/optimizer/geqo/geqo_mutation.c
 *
 * 【模块总览(中文)】
 * 本文件实现 GEQO 的"变异算子"(mutation):对一个染色体路径做若干次随机
 * 两两交换,打乱其中部分基因的顺序,为种群注入新的遗传多样性。
 *
 * 遗传算法的标准结构是"选择—交叉—变异"三阶段:交叉负责组合两个父代的
 * 优良片段,变异则负责在交叉结果上引入随机扰动,避免种群过早收敛到局部
 * 最优解。在 GEQO 中,变异算子只在 #define CX(循环交叉)模式下被使用:
 * 当 CX 算子产生的子代与父代一完全相同(cycle_diffs == 0,说明交叉没有
 * 产生任何变化,种群多样性正在流失)时,geqo_main.c 会调用本算子强行把
 * 子代打散。
 *
 * 变异采用"随机交换一对基因"(swap mutation)的形式:对路径中两个随机
 * 位置的城市进行对调。由于 TSP 路径要求每个城市恰好出现一次,而交换
 * 恰好保持集合不变(只是调整顺序),因此这种变异天然保持子代是合法排列,
 * 无需任何修复步骤,这是它被选为变异实现的原因。
 *
 * 变异次数按 num_gene / 3 随机生成(0 到 num_gene/3 之间),使变异强度
 * 随问题规模(关系个数)自适应:关系越多,需要打乱的范围越大。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_mutation.c
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

/* this is adopted from Genitor : */
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

#if defined(CX)					/* currently used only in CX mode */

#include "optimizer/geqo_mutation.h"
#include "optimizer/geqo_random.h"

/*
 * geqo_mutation - (中文)对路径做随机两两交换的变异操作
 *
 * 【作用】在路径 tour 上执行若干次随机位置对调,以引入遗传多样性。由
 * geqo_main.c 在 CX 模式下,当交叉算子返回的子代与父代完全一致
 * (cycle_diffs == 0)时调用,就地修改 kid 的基因串。
 *
 * 【设计思想】变异强度由 num_swaps = geqo_randint(root, num_gene/3, 0)
 * 决定:交换次数随机取 0..num_gene/3,与路径长度成正比,保证问题规模
 * 增大时变异能覆盖足够多的位置。每次交换:随机选两个下标 swap1、swap2,
 * 若相等则重掷 swap2(保证必然是一次"真正的"交换);然后交换两个位置的
 * 城市。核心性质:交换不改变基因集合,只改变排列次序,因此每次变异后
 * 路径依然是 1..num_gene 的合法置换,无需修复,也不破坏交叉算子保证的
 * 合法性。若 num_swaps 恰好为 0(小概率),则本函数不做任何事,路径保持
 * 原样——这是概率性变异允许的平凡情形。
 *
 * 【参数】
 *   root     —— PlannerInfo,传给随机数接口;
 *   tour     —— 待变异的路径,就地修改;
 *   num_gene —— 城市个数。
 * 【返回值】无。
 */
void
geqo_mutation(PlannerInfo *root, Gene *tour, int num_gene)
{
	int			swap1;
	int			swap2;
	int			num_swaps = geqo_randint(root, num_gene / 3, 0);
	Gene		temp;


	while (num_swaps > 0)
	{
		swap1 = geqo_randint(root, num_gene - 1, 0);
		swap2 = geqo_randint(root, num_gene - 1, 0);

		while (swap1 == swap2)
			swap2 = geqo_randint(root, num_gene - 1, 0);

		temp = tour[swap1];
		tour[swap1] = tour[swap2];
		tour[swap2] = temp;


		num_swaps -= 1;
	}
}

#endif							/* defined(CX) */
