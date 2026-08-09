/*------------------------------------------------------------------------
*
* geqo_cx.c
*
*	 cycle crossover [CX] routines;
*	 CX operator according to Oliver et al
*	 (Proc 2nd Int'l Conf on GA's)
*
 * src/backend/optimizer/geqo/geqo_cx.c
 *
 * 【模块总览(中文)】
 * 本文件实现遗传算法的"循环交叉"(Cycle Crossover,CX)算子,源自
 * Oliver 等人(Proc 2nd Int'l Conf on GA's)。CX 是在两个父代路径
 * (tour)之间产生一个合法子代路径的六种可选重组机制之一,由 geqo.h 中的
 * 编译期宏 #define CX 启用,并在 geqo_main.c 的演化主循环里被调用。
 *
 * 与边重组(ERX)、部分匹配(PMX)等算子不同,CX 的核心思想是"位置继承":
 * 子代中每个基因都严格占据父代之一的位置——要么从 tour1 继承该位置的
 * 城市,要么从 tour2 继承。它通过 city_table 这一辅助查找表,在 tour1 与
 * tour2 之间交替跳转,形成一个"基因置换环"(cycle),环内的城市全部取自
 * tour1,环外的城市全部取自 tour2,从而保证子代仍是合法排列(每个城市
 * 恰好出现一次)。
 *
 * 辅助数据结构 City(定义于 geqo_recombination.h)字段含义:
 * - tour2_position / tour1_position:某城市在两个父代路径中的下标,用于
 *   O(1) 地在两个路径间跳转;
 * - used:标记该城市是否已被写入子代。
 * 由于 CX 的环结构几乎总能覆盖所有城市,它天然很少产生重复/缺失,但
 * 极端情况下(两个父代完全相同)子代会与父代完全相同,此时 geqo_main.c
 * 会用变异算子(geqo_mutation)打散子代以维持种群多样性。
 *
 * CX 算子返回子代与 tour1 的"差异基因数",供上层判断是否发生了有效
 * 重组、是否需要触发变异。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_cx.c
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

/* the cx algorithm is adopted from Genitor : */
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

#if defined(CX)

#include "optimizer/geqo_random.h"
#include "optimizer/geqo_recombination.h"

/*
 * cx
 *
 *	 cycle crossover
 */
/*
 * cx - (中文)循环交叉算子:用两个父代路径生成一个合法子代
 *
 * 【作用】根据父代 tour1、tour2 生成子代 offspring,使子代中每个位置要么
 * 继承 tour1 的基因、要么继承 tour2 的基因,最终构成合法排列。由
 * geqo_main.c 在 #define CX 模式下每个世代调用一次。函数返回 offspring 与
 * tour1 不同基因的个数(num_diffs);若为 0,说明两个父代在该基因串上完全
 * 一致、子代无变化,上层会据此触发变异算子。
 *
 * 【设计思想】
 * CX 的思想是"找置换环":先随机选一个起始位置 start_pos,把 tour1 的
 * 该城市放入子代,然后按如下规则在两条路径间交替跳转:
 *   1. 看 tour2 在当前位置的城市 X;
 *   2. 由于子代中 X 必须来自两个父代之一,而我们想让环内城市统一来自
 *      tour1,就去查 X 在 tour1 中的位置(即 tour1_position),把该位置的
 *      tour1 城市放入子代;
 *   3. 重复直到回到起点城市,此时形成一个闭合的环(STEP 1)。
 * 环内所有城市取自 tour1;若环没有覆盖全部城市(STEP 2),剩下的位置用
 * 对应城市的 tour2 基因补齐——此时由于环是闭合的,取自 tour2 的城市不会
 * 与环内城市重复,子代仍为合法排列。
 * 若两个父代完全相同,则环可能退化为整个路径、num_diffs == 0,这是 CX
 * 无法产生多样性的边界情况,交由上层变异处理。
 *
 * city_table 被用作 O(1) 跳转表:key 是城市编号(1..num_gene),value 是
 * 该城市在两个父代中的位置以及 used 标记。注意 city_table 的下标按城市号
 * 而非路径下标组织,初始化时必须把 tour1/tour2 中每个城市的两个位置都登记
 * 进去。循环不变式:任何时刻子代每个基因都合法,未填位置用 -1 之外的
 * 实际城市值占位。
 *
 * 【参数】
 *   root       —— PlannerInfo,传给随机数接口;
 *   tour1      —— 父代一(路径数组,长度 num_gene);
 *   tour2      —— 父代二;
 *   offspring  —— 输出,生成的子代路径;
 *   num_gene   —— 基因(城市)个数;
 *   city_table —— 长度 num_gene+1 的辅助查找表(调用方分配,本函数只使用)。
 * 【返回值】offspring 与 tour1 不同的基因个数;0 表示子代与父代一完全相同。
 */
int
cx(PlannerInfo *root, Gene *tour1, Gene *tour2, Gene *offspring,
   int num_gene, City * city_table)
{
	int			i,
				start_pos,
				curr_pos;
	int			count = 0;
	int			num_diffs = 0;

	/* initialize city table */
	for (i = 1; i <= num_gene; i++)
	{
		city_table[i].used = 0;
		city_table[tour2[i - 1]].tour2_position = i - 1;
		city_table[tour1[i - 1]].tour1_position = i - 1;
	}

	/* choose random cycle starting position */
	start_pos = geqo_randint(root, num_gene - 1, 0);

	/* child inherits first city  */
	offspring[start_pos] = tour1[start_pos];

	/* begin cycle with tour1 */
	curr_pos = start_pos;
	city_table[(int) tour1[start_pos]].used = 1;

	count++;

	/* cx main part */


/* STEP 1 */

	while (tour2[curr_pos] != tour1[start_pos])
	{
		city_table[(int) tour2[curr_pos]].used = 1;
		curr_pos = city_table[(int) tour2[curr_pos]].tour1_position;
		offspring[curr_pos] = tour1[curr_pos];
		count++;
	}


/* STEP 2 */

	/* failed to create a complete tour */
	if (count < num_gene)
	{
		for (i = 1; i <= num_gene; i++)
		{
			if (!city_table[i].used)
			{
				offspring[city_table[i].tour2_position] =
					tour2[(int) city_table[i].tour2_position];
				count++;
			}
		}
	}


/* STEP 3 */

	/* still failed to create a complete tour */
	if (count < num_gene)
	{

		/* count the number of differences between mom and offspring */
		for (i = 0; i < num_gene; i++)
			if (tour1[i] != offspring[i])
				num_diffs++;
	}

	return num_diffs;
}

#endif							/* defined(CX) */
