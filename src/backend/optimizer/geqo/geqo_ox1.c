/*------------------------------------------------------------------------
*
* geqo_ox1.c
*
*	 order crossover [OX] routines;
*	 OX1 operator according to Davis
*	 (Proc Int'l Joint Conf on AI)
*
 * src/backend/optimizer/geqo/geqo_ox1.c
 *
 * 【模块总览(中文)】
 * 本文件实现"顺序交叉"(Order Crossover,OX1)算子,源自 Davis
 * (Proc Int'l Joint Conf on AI)。OX1 是 GEQO 六种可选交叉机制之一,由
 * geqo.h 中的 #define OX1 启用,由 geqo_main.c 在演化循环中调用,在
 * geqo_selection 选出父代 momma/daddy 后、geqo_eval 评估之前执行。
 *
 * OX1 的设计思想是"保留父代一的连续片段 + 保留父代二的相对顺序":
 * - 从 tour1 中随机选一段连续区间 [left, right],原样复制到子代对应位置,
 *   并把区间内城市标记为已用;
 * - 其余位置的填充顺序来自 tour2:从区间右端之后的第一个位置开始,按
 *   tour2 的循环顺序扫描,把"尚未被占用"的城市依次填入子代。
 * 这样既完整继承了父代一的一段优秀局部结构(连续位置关系被原样保留),
 * 又继承了父代二的整体城市排列相对顺序,同时保证每个城市恰好出现一次
 * (合法置换)。
 *
 * 需要辅助的城市表 City(geqo_recombination.c 分配):只用到 used 标记,
 * 按城市编号组织,用于 O(1) 判断"某城市是否已被写入子代"。与其它基于
 * 位置的算子(OX2/PX/CX)共享同一套城市表内存。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_ox1.c
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

#if defined(OX1)

#include "optimizer/geqo_random.h"
#include "optimizer/geqo_recombination.h"

/*
 * ox1
 *
 *	 position crossover
 */
/*
 * ox1 - (中文)顺序交叉算子(OX1):保留父代一连续片段与父代二相对顺序
 *
 * 【作用】由父代 tour1、tour2 生成子代 offspring:先把 tour1 的随机一段
 * 连续区间复制到子代,再用 tour2 中未用城市的相对顺序填满其余位置。由
 * geqo_main.c 在 #define OX1 模式下每代调用。结果仍是合法置换(每个城市
 * 恰好一次)。
 *
 * 【设计思想】三步骤:
 * 1. 初始化 city_table 的 used 标记清零;
 * 2. 随机取两个切割点 left、right(各自在 [0, num_gene-1] 均匀取样),若
 *    left > right 则交换使 left <= right(区间左右边界任意、不要求有序,
 *    排序后得到"规范区间");把 tour1[left..right] 逐位置复制到子代,并
 *    把区间内城市标为 used;
 * 3. 填剩余位置:k 从 (right+1) % num_gene 起按环形顺序推进(这是子代
 *    中紧邻区间右端的第一个空位),p 同样从该下标起按环形顺序扫描 tour2;
 *    对 tour2[p] 若未 used 则填入 offspring[k] 并推进 k、标记 used;无论
 *    填没填,p 都前进一位。循环直到 k 回到 left(区间左端),所有空位被填
 *    满。环形取模保证了区间是"环上的区间",换到其它位置同样正确。
 * 核心不变量:任何时刻已填子代位置集合 = 区间 ∪ 已消费的 tour2 城市,
 * 且不重复;最终区间内城市全部来自 tour1,区间外城市全部是 tour2 的
 * 未用者,故无重复、无遗漏。
 *
 * 【参数】
 *   root       —— PlannerInfo,传给随机数接口;
 *   tour1      —— 父代一(提供连续继承区间);
 *   tour2      —— 父代二(提供剩余城市的顺序);
 *   offspring  —— 输出,子代路径;
 *   num_gene   —— 城市个数;
 *   city_table —— 长度 num_gene+1 的城市表,只使用 used 标记。
 * 【返回值】无。
 */
void
ox1(PlannerInfo *root, Gene *tour1, Gene *tour2, Gene *offspring, int num_gene,
	City * city_table)
{
	int			left,
				right,
				k,
				p,
				temp;

	/* initialize city table */
	for (k = 1; k <= num_gene; k++)
		city_table[k].used = 0;

	/* select portion to copy from tour1 */
	left = geqo_randint(root, num_gene - 1, 0);
	right = geqo_randint(root, num_gene - 1, 0);

	if (left > right)
	{
		temp = left;
		left = right;
		right = temp;
	}

	/* copy portion from tour1 to offspring */
	for (k = left; k <= right; k++)
	{
		offspring[k] = tour1[k];
		city_table[(int) tour1[k]].used = 1;
	}

	k = (right + 1) % num_gene; /* index into offspring */
	p = k;						/* index into tour2 */

	/* copy stuff from tour2 to offspring */
	while (k != left)
	{
		if (!city_table[(int) tour2[p]].used)
		{
			offspring[k] = tour2[p];
			k = (k + 1) % num_gene;
			city_table[(int) tour2[p]].used = 1;
		}
		p = (p + 1) % num_gene; /* increment tour2-index */
	}
}

#endif							/* defined(OX1) */
