/*------------------------------------------------------------------------
*
* geqo_px.c
*
*	 position crossover [PX] routines;
*	 PX operator according to Syswerda
*	 (The Genetic Algorithms Handbook, L Davis, ed)
*
 * src/backend/optimizer/geqo/geqo_px.c
 *
 * 【模块总览(中文)】
 * 本文件实现"位置交叉"(Position Crossover,PX)算子,源自 Syswerda
 * (The Genetic Algorithms Handbook,L Davis,ed)。PX 是 GEQO 六种可选
 * 交叉机制之一,由 geqo.h 的 #define PX 启用,由 geqo_main.c 在演化循环
 * 中调用。
 *
 * PX 的设计思想非常直观:"直接继承父代一的随机位置基因,其余位置按父代
 * 二的顺序补全"——
 * - 从 tour1 中随机选 [num_gene/3, 2*num_gene/3] 个位置,这些位置上的
 *   城市被原样搬到子代的相同下标(这些"被选中城市"在子代中的绝对位置
 *   与 tour1 完全一致);
 * - 剩下未填的位置,按 tour2 的城市顺序依次填入"尚未被占用"的城市。
 * 由此,被选中城市保持其在 tour1 中的位置,未选中城市保持其在 tour2 中的
 * 相对顺序,两者拼接成合法置换。
 *
 * 需要的辅助结构是城市表 City(geqo_recombination.c 分配),仅使用其 used
 * 字段:标记"某城市已被继承到子代",用于判断 tour2 中哪些城市还能用。
 * 与 OX1/OX2/CX 共用同一块城市表内存,生命周期由 geqo_main.c 管理。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_px.c
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

/* the px algorithm is adopted from Genitor : */
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

#if defined(PX)

#include "optimizer/geqo_random.h"
#include "optimizer/geqo_recombination.h"

/*
 * px
 *
 *	 position crossover
 */
/*
 * px - (中文)位置交叉算子(PX):继承父代一随机位置 + 父代二相对顺序
 *
 * 【作用】由父代 tour1、tour2 生成子代 offspring:先随机挑选 tour1 中
 * [num_gene/3, 2*num_gene/3] 个位置原样继承,再把剩余空位按 tour2 中
 * 未用城市的相对顺序填满。由 geqo_main.c 在 #define PX 模式下每代调用。
 * 结果保证是合法置换。
 *
 * 【设计思想】三步:
 * 1. 清零 city_table[1..num_gene].used;
 * 2. 选位置:num_positions 在 [num_gene/3, 2*num_gene/3] 间随机(与 OX2
 *    的量级一致,保证继承比例既不退化也不过强);循环 num_positions 次,
 *    每次随机取位置 pos,把 tour1[pos] 写入 offspring[pos] 并标记该城市
 *    used。注意随机位置允许重复:若重复,该位置被再次写入相同城市、无
 *    额外影响(实际继承的位置数可能略少),实现上不特判,简单可靠;
 * 3. 填剩余:offspring_index 与 tour2_index 均从 0 开始环形推进:
 *    - 若当前位置 offspring[offspring_index] 已被选中位置占据(即
 *      tour1[offspring_index] 这个城市已 used——因为被选中位置的城市恰
 *      来自 tour1,用 tour1[offspring_index] 是否 used 即可判断当前位置
 *      是否已被占),则跳过该位置、offspring_index++ 继续;
 *    - 否则该位置空闲,考察 tour2[tour2_index]:若该城市未 used,放入并
 *      同时推进两个下标;若已 used 则只推进 tour2_index(它已被继承,
 *      不能重复出现)。
 *    循环直到子代填满。这个双下标推进的技巧保证:继承自 tour1 的位置
 *    不被破坏,其余位置按 tour2 顺序依次放置,且每个城市恰好一次。
 *
 * 【参数】
 *   root       —— PlannerInfo,传给随机数接口;
 *   tour1      —— 父代一(随机位置基因来源);
 *   tour2      —— 父代二(剩余城市顺序来源);
 *   offspring  —— 输出,子代路径;
 *   num_gene   —— 城市个数;
 *   city_table —— 长度 num_gene+1 的城市表,只使用 used 标记。
 * 【返回值】无。
 */
void
px(PlannerInfo *root, Gene *tour1, Gene *tour2, Gene *offspring, int num_gene,
   City * city_table)
{
	int			num_positions;
	int			i,
				pos,
				tour2_index,
				offspring_index;

	/* initialize city table */
	for (i = 1; i <= num_gene; i++)
		city_table[i].used = 0;

	/* choose random positions that will be inherited directly from parent */
	num_positions = geqo_randint(root, 2 * num_gene / 3, num_gene / 3);

	/* choose random position */
	for (i = 0; i < num_positions; i++)
	{
		pos = geqo_randint(root, num_gene - 1, 0);

		offspring[pos] = tour1[pos];	/* transfer cities to child */
		city_table[(int) tour1[pos]].used = 1;	/* mark city used */
	}

	tour2_index = 0;
	offspring_index = 0;


	/* px main part */

	while (offspring_index < num_gene)
	{

		/* next position in offspring filled */
		if (!city_table[(int) tour1[offspring_index]].used)
		{

			/* next city in tour1 not used */
			if (!city_table[(int) tour2[tour2_index]].used)
			{

				/* inherit from tour1 */
				offspring[offspring_index] = tour2[tour2_index];

				tour2_index++;
				offspring_index++;
			}
			else
			{					/* next city in tour2 has been used */
				tour2_index++;
			}
		}
		else
		{						/* next position in offspring is filled */
			offspring_index++;
		}
	}
}

#endif							/* defined(PX) */
