/*------------------------------------------------------------------------
 *
 * geqo_copy.c
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/optimizer/geqo/geqo_copy.c
 *
 * 【模块总览(中文)】
 * 本文件实现遗传算法(GA)中最基本的"染色体复制"原语:把一个染色体
 * (Chromosome,由 Gene 串和适应度 worth 组成)的完整内容复制到另一个
 * 染色体中。它是整个 GEQO 演化循环里最底层的搬运操作,被两个地方直接调用:
 * - geqo_selection.c 的 geqo_selection():把从种群池中选出的父代
 *   (momma/daddy)复制到专用缓冲区,供后续交叉算子读取;
 * - geqo_pool.c 的 spread_chromo():把新生代染色体(后代)复制进种群池,
 *   顶替掉最差的个体。
 *
 * 之所以需要专门的逐基因拷贝函数,而不是简单的结构体赋值,是因为
 * Chromosome.string 是指向独立 palloc 内存的指针:直接赋值会让两个染色体
 * 共享同一块基因串内存,后续任何一方被 free 或改写都会互相污染。因此必须
 * 把 string 数组的每个元素逐一复制,再单独复制 worth 标量。
 *
 * 本实现取自 D. Whitley 的 Genitor 算法,是 GEQO 算法家族各文件共同的
 * "无突变的默认拷贝语义"。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_copy.c
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
#include "optimizer/geqo_copy.h"

/*
 * geqo_copy
 *
 *	 copies one gene to another
 *
 */
/*
 * geqo_copy - (中文)将一个染色体完整复制到另一个染色体
 *
 * 【作用】把 chromo2 的基因串(string 数组)与适应度(worth)全部复制到
 * chromo1 中。这是 GEQO 内部通用的"染色体值拷贝"工具,由
 * geqo_selection.c(选择父代)与 geqo_pool.c:spread_chromo(后代入池)调用,
 * 交叉/变异阶段之前为父代制作工作副本,入池阶段把后代覆盖到目标槽位。
 *
 * 【设计思想】染色体的 Gene 串是 palloc 出来的独立内存块,不能通过结构体
 * 赋值共享指针,否则同一基因串会被两个染色体同时持有、互相踩踏。因此这里
 * 采用"逐基因循环拷贝 + 标量 worth 拷贝"的深拷贝语义。注意本函数不分配
 * 任何内存:调用方必须保证 chromo1->string 已经指向足够容纳 string_length
 * 个 Gene 的缓冲区(pool 初始化时每个染色体都分配了 string_length + 1 的
 * 空间)。string_length 与 root 仅作为接口约定保持一致,root 当前未被使用,
 * 是为未来接入优化器上下文预留的参数。
 *
 * 【参数】
 *   root          —— PlannerInfo,当前未使用(为接口统一而保留);
 *   chromo1       —— 目标染色体,内容被覆盖写入;
 *   chromo2       —— 源染色体,只读;
 *   string_length —— 基因串长度(即待拷贝的基因个数)。
 * 【返回值】无。
 */
void
geqo_copy(PlannerInfo *root, Chromosome *chromo1, Chromosome *chromo2,
		  int string_length)
{
	int			i;

	for (i = 0; i < string_length; i++)
		chromo1->string[i] = chromo2->string[i];

	chromo1->worth = chromo2->worth;
}
