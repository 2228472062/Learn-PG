/*------------------------------------------------------------------------
*
* geqo_pmx.c
*
*	 partially matched crossover [PMX] routines;
*	 PMX operator according to Goldberg & Lingle
*	 (Proc Int'l Conf on GA's)
*
 * src/backend/optimizer/geqo/geqo_pmx.c
 *
 * 【模块总览(中文)】
 * 本文件实现"部分匹配交叉"(Partially Matched Crossover,PMX)算子,源自
 * Goldberg & Lingle(Proc Int'l Conf on GA's)。PMX 是 GEQO 六种交叉机制
 * 之一,由 geqo.h 的 #define PMX 启用,由 geqo_main.c 在演化循环中调用。
 *
 * PMX 的思想是"位置继承 + 冲突修复":先随机取两个切割点 left/right 把
 * 父代一 tour1 与父代二 tour2 各切成三段;把 tour2 整体复制为子代基底,
 * 再把 tour1 的 [left,right] 段覆盖到子代相应位置(继承父代一的"片段
 * 基因")。问题在于:覆盖会把 tour2 中已经放好的城市挤掉,导致子代出现
 * 城市重复/缺失。为此 PMX 需要用"映射替换"修复:
 * - 对区间内每个位置,若 tour1[k] 与 tour2[k] 相同则无需处理;否则需要
 *   找到子代中仍然持有 tour1[k] 的位置(该位置来自 tour2 部分),用
 *   tour2[k] 把它替换掉——因为 tour1[k] 已经入位,原持有者必须被驱逐;
 * - 驱逐后若区间内还有处理不了的(未找到持有者),说明被覆盖造成两处冲突,
 *   记入 failed/indx 延迟到下一步处理;
 * - STEP 2 针对 failed 的基因再尝试一轮替换(failed[k] 表示被覆盖后仍
 *   重复的城市,indx[k] 是它在区间内的位置,需要用 tour2[indx[k]] 驱逐
 *   子代中仍存活的 failed[k]);
 * - 若仍有多余的重复(check_list[k] > 1,用计数数组跟踪每个城市在子代中
 *   出现次数),STEP 3 做兜底:把重复的 DAD 来源城市就地替换为某个出现
 *   次数为 0 的缺失城市。
 * 该修复过程保证最终子代是 1..num_gene 的合法置换。
 *
 * 实现依赖四个调用方 palloc 的临时数组(failed/from/indx/check_list,长度
 * num_gene+1,用后在本函数内 pfree),不依赖城市表;DAD/MOM 宏(定义于
 * geqo_pool.h)标记某位置基因来自哪个父代,是修复逻辑的重要依据。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_pmx.c
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

/* the pmx algorithm is adopted from Genitor : */
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

#if defined(PMX)

#include "optimizer/geqo_random.h"
#include "optimizer/geqo_recombination.h"

/*
 * pmx
 *
 *	 partially matched crossover
 */
/*
 * pmx - (中文)部分匹配交叉算子(PMX):片段继承 + 映射修复冲突
 *
 * 【作用】由父代 tour1、tour2 生成子代 offspring。随机取两切割点,把
 * tour1 的中间片段覆盖到以 tour2 为基底的子代上,再通过"映射替换"修复
 * 由此产生的城市重复/缺失,最终得到合法置换。由 geqo_main.c 在
 * #define PMX 模式下每代调用。
 *
 * 【设计思想】完整算法分四部分:
 * (A) 准备:四个临时数组 failed/from/indx/check_list 由调用方分配
 *     (palloc_array,num_gene+1),本函数负责初始化与 pfree。初始化
 *     failed[k]=-1、from[k]=-1、check_list[k+1]=0。随后随机取 left/right
 *     并规范成 left<=right;
 * (B) 基底与覆盖:先整条复制 tour2 为子代,from 标记全部 DAD,check_list
 *     累计各城市出现次数;再把 tour1[left..right] 覆盖到子代,被覆盖
 *     位置 from 改标 MOM,check_list 对应调整(旧城市减一、新城市加一);
 * (C) STEP 1(映射修复主循环):对区间内每个位置 k:若 tour1[k]==tour2[k]
 *     该城市天生一致,跳过;否则在子代里找仍持有 tour1[k] 的 DAD 来源
 *     位置 j,用 tour2[k] 替换它(check_list 相应增减)。找不到就说明冲突
 *     暂时无法就地解决,把 (tour1[k], k) 记入 failed/indx、mx_fail 计数;
 * (D) STEP 2/3(兜底):STEP 2 对 failed 列表再逐项尝试——在子代中找值为
 *     failed[k] 的 DAD 位置,用 tour2[indx[k]] 替换,成功则 mx_fail 递减;
 *     若仍存在 check_list[k]>1(城市 k 在子代中重复),STEP 3 找到第一个
 *     check_list[j]==0(缺失城市),把重复的 DAD 位置改填 j,使重复数减少、
 *     缺失数也减少,逐步把计数全部归一为 1。所有 check_list 操作保证
 *     最终每个城市恰好出现一次。
 * DAD/MOM 标记是修复的核心依据:只允许动"来自 tour2(DAD)"的位置,因为
 * 被覆盖进来的 tour1 片段(MOM)应当保持原样。各数组下标约定:
 * check_list[1..num_gene] 对应城市号 1..num_gene;failed/indx 用独立计数
 * mx_fail 管理,不使用 -1 哨兵覆盖真实下标。
 *
 * 【参数】
 *   root      —— PlannerInfo,传给随机数接口;
 *   tour1     —— 父代一(提供中间片段);
 *   tour2     —— 父代二(提供基底与其余顺序);
 *   offspring —— 输出,子代路径;
 *   num_gene  —— 城市个数。
 * 【返回值】无。
 */
void
pmx(PlannerInfo *root, Gene *tour1, Gene *tour2, Gene *offspring, int num_gene)
{
	int		   *failed = palloc_array(int, num_gene + 1);
	int		   *from = palloc_array(int, num_gene + 1);
	int		   *indx = palloc_array(int, num_gene + 1);
	int		   *check_list = palloc_array(int, num_gene + 1);

	int			left,
				right,
				temp,
				i,
				j,
				k;
	int			mx_fail,
				found,
				mx_hold;


/* no mutation so start up the pmx replacement algorithm */
/* initialize failed[], from[], check_list[] */
	for (k = 0; k < num_gene; k++)
	{
		failed[k] = -1;
		from[k] = -1;
		check_list[k + 1] = 0;
	}

/* locate crossover points */
	left = geqo_randint(root, num_gene - 1, 0);
	right = geqo_randint(root, num_gene - 1, 0);

	if (left > right)
	{
		temp = left;
		left = right;
		right = temp;
	}


/* copy tour2 into offspring */
	for (k = 0; k < num_gene; k++)
	{
		offspring[k] = tour2[k];
		from[k] = DAD;
		check_list[tour2[k]]++;
	}

/* copy tour1 into offspring */
	for (k = left; k <= right; k++)
	{
		check_list[offspring[k]]--;
		offspring[k] = tour1[k];
		from[k] = MOM;
		check_list[tour1[k]]++;
	}


/* pmx main part */

	mx_fail = 0;

/* STEP 1 */

	for (k = left; k <= right; k++)
	{							/* for all elements in the tour1-2 */

		if (tour1[k] == tour2[k])
			found = 1;			/* find match in tour2 */

		else
		{
			found = 0;			/* substitute elements */

			j = 0;
			while (!(found) && (j < num_gene))
			{
				if ((offspring[j] == tour1[k]) && (from[j] == DAD))
				{

					check_list[offspring[j]]--;
					offspring[j] = tour2[k];
					found = 1;
					check_list[tour2[k]]++;
				}

				j++;
			}
		}

		if (!(found))
		{						/* failed to replace gene */
			failed[mx_fail] = (int) tour1[k];
			indx[mx_fail] = k;
			mx_fail++;
		}
	}							/* ... for */


/* STEP 2 */

	/* see if any genes could not be replaced */
	if (mx_fail > 0)
	{
		mx_hold = mx_fail;

		for (k = 0; k < mx_hold; k++)
		{
			found = 0;

			j = 0;
			while (!(found) && (j < num_gene))
			{

				if ((failed[k] == (int) offspring[j]) && (from[j] == DAD))
				{
					check_list[offspring[j]]--;
					offspring[j] = tour2[indx[k]];
					check_list[tour2[indx[k]]]++;

					found = 1;
					failed[k] = -1;
					mx_fail--;
				}

				j++;
			}
		}						/* ... for	 */
	}							/* ... if	 */


/* STEP 3 */

	for (k = 1; k <= num_gene; k++)
	{

		if (check_list[k] > 1)
		{
			i = 0;

			while (i < num_gene)
			{
				if ((offspring[i] == (Gene) k) && (from[i] == DAD))
				{
					j = 1;

					while (j <= num_gene)
					{
						if (check_list[j] == 0)
						{
							offspring[i] = (Gene) j;
							check_list[k]--;
							check_list[j]++;
							i = num_gene + 1;
							j = i;
						}

						j++;
					}
				}				/* ... if	 */

				i++;
			}					/* end while */
		}
	}							/* ... for	 */

	pfree(failed);
	pfree(from);
	pfree(indx);
	pfree(check_list);
}

#endif							/* defined(PMX) */
