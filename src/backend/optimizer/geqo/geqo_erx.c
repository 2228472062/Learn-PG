/*------------------------------------------------------------------------
*
* geqo_erx.c
*	 edge recombination crossover [ER]
*
 * src/backend/optimizer/geqo/geqo_erx.c
 *
 * 【模块总览(中文)】
 * 本文件实现遗传算法的"边重组交叉"(Edge Recombination Crossover,ERX)
 * 算子,是 geqo.h 中默认启用(#define ERX)的重组机制。ERX 源自 D. Whitley
 * 的 Genitor 算法,其核心思想与其它交叉算子截然不同:它不直接拼接父代
 * 路径片段,而是先提取两个父代路径中蕴含的"相邻城市关系"(即边),构造
 * 一张"边表"(edge_table),再基于这张边表逐步重构出一条新路径。
 *
 * 因为查询优化问题被建模成 TSP(每个基因对应一个基本关系,相邻基因表示
 * 相邻的连接顺序),两个父代共享的"边"(相邻关系)往往代表着两个方案
 * 都认可的、较优的局部连接次序,继承这些边比随机重组更能保留优良基因
 * 组合,这正是 ERX 的设计动机。
 *
 * 核心数据结构 Edge(定义于 geqo_recombination.h):
 * - edge_list[4]:与该城市相邻的城市列表(无向,去重,最多 4 个;
 *   负值表示"共享边",即两个父代都拥有的边);
 * - total_edges:初始登记的总边数(登记时可能去重);
 * - unused_edges:尚未在构造路径时使用的边数。
 *
 * 主要函数协作关系(全部在 geqo_main.c 的 ERX 分支中被串联调用):
 *   1. alloc_edge_table / free_edge_table:边表内存的分配与释放;
 *   2. gimme_edge_table:把两个父代路径的边去重登记进边表,共享边记为
 *      负值,返回"平均每城市边数"作为多样性度量;
 *   3. gimme_tour:从边表逐步构建子代路径,优先使用共享边,失败时调用
 *      edge_failure 兜底;
 *   4. gimme_edge / remove_gene / gimme_gene:分别为"登记一条边"、
 *      "从边表删除某城市的所有入边"、"在边表中挑选下一个城市"的辅助
 *      原语。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_erx.c
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

/* the edge recombination algorithm is adopted from Genitor : */
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

#if defined(ERX)

#include "optimizer/geqo_random.h"
#include "optimizer/geqo_recombination.h"

static int	gimme_edge(PlannerInfo *root, Gene gene1, Gene gene2, Edge *edge_table);
static void remove_gene(PlannerInfo *root, Gene gene, Edge edge, Edge *edge_table);
static Gene gimme_gene(PlannerInfo *root, Edge edge, Edge *edge_table);

static Gene edge_failure(PlannerInfo *root, Gene *gene, int index, Edge *edge_table, int num_gene);


/*
 * alloc_edge_table
 *
 *	 allocate memory for edge table
 *
 */
/*
 * alloc_edge_table - (中文)为边表分配内存
 *
 * 【作用】为 num_gene 个城市各分配一个 Edge 结构,返回边表首地址。由
 * geqo_main.c 在 ERX 模式的演化循环开始前调用一次,生命周期持续到整个
 * 演化结束,期间每次世代复用(gegmo_edge_table 会覆盖旧内容)。
 *
 * 【设计思想】分配 num_gene + 1 个元素:城市编号从 1 到 num_gene,下标 0
 * 闲置不用,这样 edge_table[i] 可以直接用城市号 i 索引,避免到处做
 * "下标 - 1"的换算。内存使用 palloc(当前内存上下文),由上层 geqo()
 * 结束时用 free_edge_table 释放。
 *
 * 【参数】
 *   root     —— PlannerInfo,当前未使用;
 *   num_gene —— 城市(基因)个数。
 * 【返回值】Edge 数组指针,下标 1..num_gene 有效,下标 0 未初始化。
 */
Edge *
alloc_edge_table(PlannerInfo *root, int num_gene)
{
	Edge	   *edge_table;

	/*
	 * palloc one extra location so that nodes numbered 1..n can be indexed
	 * directly; 0 will not be used
	 */

	edge_table = palloc_array(Edge, num_gene + 1);

	return edge_table;
}

/*
 * free_edge_table
 *
 *	  deallocate memory of edge table
 *
 */
/*
 * free_edge_table - (中文)释放边表内存
 *
 * 【作用】回收 alloc_edge_table 分配的边表内存。由 geqo_main.c 在演化
 * 循环结束、不再需要边表时调用。与 alloc_edge_table 配对的资源管理函数。
 *
 * 【设计思想】边表整块由 palloc 分配、整块 pfree 释放,无需逐元素释放
 * (Edge 内部没有指针,只有定长数组 edge_list[4] 和两个计数)。
 *
 * 【参数】
 *   root       —— PlannerInfo,当前未使用;
 *   edge_table —— alloc_edge_table 返回的边表指针。
 * 【返回值】无。
 */
void
free_edge_table(PlannerInfo *root, Edge *edge_table)
{
	pfree(edge_table);
}

/*
 * gimme_edge_table
 *
 *	 fills a data structure which represents the set of explicit
 *	 edges between points in the (2) input genes
 *
 *	 assumes circular tours and bidirectional edges
 *
 *	 gimme_edge() will set "shared" edges to negative values
 *
 *	 returns average number edges/city in range 2.0 - 4.0
 *	 where 2.0=homogeneous; 4.0=diverse
 *
 */
/*
 * gimme_edge_table - (中文)把两个父代路径的边去重登记进边表
 *
 * 【作用】扫描父代 tour1、tour2 的全部相邻城市对(按环状路径理解),通过
 * gimme_edge 把每条无向边登记进 edge_table;两个父代共有的边会被标记为
 * 负值("共享边")。返回"平均每个城市拥有的不同边数",范围 2.0~4.0。
 * 由 geqo_main.c 在每个 ERX 世代调用,是 gimme_tour 的前置步骤。
 *
 * 【设计思想】
 * - 把路径视为"环":第 num_gene-1 个元素与第 0 个元素也互为邻居,
 *   用 (index1 + 1) % num_gene 计算后继下标;
 * - 边是无向的(1->2 与 2->1 是同一条边),所以每条实际边要调用两次
 *   gimme_edge,把两个方向都登记,由 gimme_edge 内部完成去重;
 * - 同一城市最多与 4 个城市相邻(无向环上相邻城市数上限为 2,但登记的是
 *   "两个方向各自的目标集合",配合去重后不超过 4),因此 Edge.edge_list
 *   定长 4 足够;
 * - edge_total 累计的是"新登记"的边数(每个方向调用返回 0/1),最终
 *   (edge_total * 2) / num_gene 即平均每城市边数:数值接近 2 表示两个
 *   父代高度同质(几乎只差一条边),接近 4 表示差异巨大。
 * 调用前必须先清零 total_edges / unused_edges(本函数开头就做这件事),
 * 因为同一张边表会在多个世代间复用。
 *
 * 【参数】
 *   root       —— PlannerInfo,传给 gimme_edge(当前未被 gimme_edge 使用);
 *   tour1      —— 父代一路径;
 *   tour2      —— 父代二路径;
 *   num_gene   —— 城市个数;
 *   edge_table —— 输出,登记了全部边的边表(长度 num_gene + 1)。
 * 【返回值】平均每城市边数(2.0 表示同质,4.0 表示差异最大)。
 */
float
gimme_edge_table(PlannerInfo *root, Gene *tour1, Gene *tour2,
				 int num_gene, Edge *edge_table)
{
	int			i,
				index1,
				index2;
	int			edge_total;		/* total number of unique edges in two genes */

	/* at first clear the edge table's old data */
	for (i = 1; i <= num_gene; i++)
	{
		edge_table[i].total_edges = 0;
		edge_table[i].unused_edges = 0;
	}

	/* fill edge table with new data */

	edge_total = 0;

	for (index1 = 0; index1 < num_gene; index1++)
	{
		/*
		 * presume the tour is circular, i.e. 1->2, 2->3, 3->1 this operation
		 * maps n back to 1
		 */

		index2 = (index1 + 1) % num_gene;

		/*
		 * edges are bidirectional, i.e. 1->2 is same as 2->1 call gimme_edge
		 * twice per edge
		 */

		edge_total += gimme_edge(root, tour1[index1], tour1[index2], edge_table);
		gimme_edge(root, tour1[index2], tour1[index1], edge_table);

		edge_total += gimme_edge(root, tour2[index1], tour2[index2], edge_table);
		gimme_edge(root, tour2[index2], tour2[index1], edge_table);
	}

	/* return average number of edges per index */
	return ((float) (edge_total * 2) / (float) num_gene);
}

/*
 * gimme_edge
 *
 *	  registers edge from city1 to city2 in input edge table
 *
 *	  no assumptions about directionality are made;
 *	  therefore it is up to the calling routine to
 *	  call gimme_edge twice to make a bi-directional edge
 *	  between city1 and city2;
 *	  uni-directional edges are possible as well (just call gimme_edge
 *	  once with the direction from city1 to city2)
 *
 *	  returns 1 if edge was not already registered and was just added;
 *			  0 if edge was already registered and edge_table is unchanged
 */
/*
 * gimme_edge - (中文)把有向边 city1->city2 登记进边表(带去重与共享标记)
 *
 * 【作用】检查 edge_table[city1] 的 edge_list 中是否已有目标城市 city2;
 * 若没有,追加登记并递增 total_edges / unused_edges 返回 1;若已有,则把
 * 该边改写为负值(city2 的相反数)表示"这是两个父代共有的共享边",返回 0。
 * 由 gimme_edge_table 对每条无向边双向各调用一次。
 *
 * 【设计思想】
 * - 去重依赖"同一个城市在一张表中登记的出边不重复":若再次遇到同一目标,
 *   说明第二个父代也有这条边,于是把它从正值翻成负值,用符号位标记"共享"。
 *   后续 gimme_gene 只需检查负值即可优先选用共享边,无需单独的共享标记位;
 * - 负值的语义贯穿 ERX 全流程:abs() 取回真实城市号,所有比较都用
 *   abs(edge_list[i]),避免被负号干扰;
 * - 之所以逐条线性扫描 edge_list,是因为每个列表至多 4 个元素,线性查找
 *   足够快,不值得为常数规模建立哈希。
 *
 * 【参数】
 *   root       —— PlannerInfo,当前未使用;
 *   gene1      —— 出边城市(源),作为边表下标;
 *   gene2      —— 入边城市(目标);
 *   edge_table —— 边表。
 * 【返回值】1 表示新登记的边;0 表示该边已存在(此时它被标记为共享边)。
 */
static int
gimme_edge(PlannerInfo *root, Gene gene1, Gene gene2, Edge *edge_table)
{
	int			i;
	int			edges;
	int			city1 = (int) gene1;
	int			city2 = (int) gene2;


	/* check whether edge city1->city2 already exists */
	edges = edge_table[city1].total_edges;

	for (i = 0; i < edges; i++)
	{
		if ((Gene) abs(edge_table[city1].edge_list[i]) == city2)
		{

			/* mark shared edges as negative */
			edge_table[city1].edge_list[i] = 0 - city2;

			return 0;
		}
	}

	/* add city1->city2; */
	edge_table[city1].edge_list[edges] = city2;

	/* increment the number of edges from city1 */
	edge_table[city1].total_edges++;
	edge_table[city1].unused_edges++;

	return 1;
}

/*
 * gimme_tour
 *
 *	  creates a new tour using edges from the edge table.
 *	  priority is given to "shared" edges (i.e. edges which
 *	  all parent genes possess and are marked as negative
 *	  in the edge table.)
 *
 */
/*
 * gimme_tour - (中文)根据边表逐步构建子代路径(ERX 的核心步骤)
 *
 * 【作用】以边表为依据,逐个位置挑选下一个城市,生成子代路径 new_gene。
 * 优先选择"共享边"(负值),其次选择"未使用边最少"的候选,最后靠
 * edge_failure 处理"无可用边"的失败情形。返回整个构建过程中的边失败次数
 * (edge_failures,通常为 0)。由 geqo_main.c 在每次 ERX 世代调用。
 *
 * 【设计思想】
 * - 起点随机:new_gene[0] 在 1..num_gene 间均匀随机选取,给算法注入随机性,
 *   使相同父代也可能产生不同子代;
 * - 每次确定一个城市后,立即调用 remove_gene 把"它的所有邻居表项"里的
 *   该城市删掉(注意 remove_gene 用 unused_edges 计数控制删除范围),再置
 *   unused_edges = -1 标记"本城市已入环、彻底退出候选"——这个 -1 哨兵同时
 *   兼作"已使用"标记,edge_failure 靠它判断剩余城市;
 * - 选择策略三优先:① 负值共享边直接采纳;② 否则在候选城市中挑
 *   "unused_edges 最小"的(模拟 TSP 的最近邻居启发式,尽早处理孤立点);
 *   ③ 有并列最小者时随机挑选,避免确定性偏向。
 * - 失败兜底:若当前城市已无未用边(环被过早封闭),调用 edge_failure 从
 *   剩余城市中随机挑一个续上,保证子代总是合法排列(这是启发式算法允许的
 *   不完美——失败会产生跨环的坏边,但绝不让子代非法)。
 *
 * 【参数】
 *   root       —— PlannerInfo,传给随机数接口;
 *   edge_table —— 已由 gimme_edge_table 填好的边表(会被本函数破坏性修改);
 *   new_gene   —— 输出,生成的子代路径;
 *   num_gene   —— 城市个数。
 * 【返回值】边失败次数;0 表示完全沿共享/最优边构建,无失败。
 */
int
gimme_tour(PlannerInfo *root, Edge *edge_table, Gene *new_gene, int num_gene)
{
	int			i;
	int			edge_failures = 0;

	/* choose int between 1 and num_gene */
	new_gene[0] = (Gene) geqo_randint(root, num_gene, 1);

	for (i = 1; i < num_gene; i++)
	{
		/*
		 * as each point is entered into the tour, remove it from the edge
		 * table
		 */

		remove_gene(root, new_gene[i - 1], edge_table[(int) new_gene[i - 1]], edge_table);

		/* find destination for the newly entered point */

		if (edge_table[new_gene[i - 1]].unused_edges > 0)
			new_gene[i] = gimme_gene(root, edge_table[(int) new_gene[i - 1]], edge_table);

		else
		{						/* cope with fault */
			edge_failures++;

			new_gene[i] = edge_failure(root, new_gene, i - 1, edge_table, num_gene);
		}

		/* mark this node as incorporated */
		edge_table[(int) new_gene[i - 1]].unused_edges = -1;
	}							/* for (i=1; i<num_gene; i++) */

	return edge_failures;
}

/*
 * remove_gene
 *
 *	 removes input gene from edge_table.
 *	 input edge is used
 *	 to identify deletion locations within edge table.
 *
 */
/*
 * remove_gene - (中文)把指定城市从边表中所有邻居的边列表里删除
 *
 * 【作用】城市 gene 已经确定进入子代路径,它不能再作为任何后续城市的
 * 候选邻居。本函数扫描 edge(即 edge_table[gene])的未使用边列表,对每个
 * 邻居城市,在其自己的边列表中找到 gene 并删除(unused_edges 减一,列表
 * 尾元素顶上)。由 gimme_tour 在每写入一个城市后调用。
 *
 * 【设计思想】
 * - 双层循环的语义:外层遍历"与 gene 相邻的未用城市",内层在那些城市的
 *   边列表里定位并摘除 gene,保证对称性——既然 gene 已入环,别人也不该
 *   再把它当候选;
 * - 删除用"末尾元素覆盖 + 尾指针收缩"实现 O(1) 摘除,同时必须同步递减
 *   unused_edges,因为后续所有循环(包括本函数外层循环自身)都以
 *   unused_edges 作为边界;这也解释了为何不能只改 total_edges;
 * - 只收缩 unused_edges、不收缩 total_edges:total_edges 保留的是"最初
 *   登记的边数",edge_failure 需要它判断城市是否属于"初始四边"类型;
 * - 入参 edge 按值传递的是 edge_table[gene] 的快照,函数内部对它只读;
 *   真正的修改发生在 edge_table[possess_edge],即各个邻居的表项上。
 *
 * 【参数】
 *   root       —— PlannerInfo,当前未使用;
 *   gene       —— 要删除的城市号;
 *   edge       —— edge_table[gene] 的值拷贝(其未用边列表给出所有邻居);
 *   edge_table —— 边表(被就地修改)。
 * 【返回值】无。
 */
static void
remove_gene(PlannerInfo *root, Gene gene, Edge edge, Edge *edge_table)
{
	int			i,
				j;
	int			possess_edge;
	int			genes_remaining;

	/*
	 * do for every gene known to have an edge to input gene (i.e. in
	 * edge_list for input edge)
	 */

	for (i = 0; i < edge.unused_edges; i++)
	{
		possess_edge = abs(edge.edge_list[i]);
		genes_remaining = edge_table[possess_edge].unused_edges;

		/* find the input gene in all edge_lists and delete it */
		for (j = 0; j < genes_remaining; j++)
		{

			if ((Gene) abs(edge_table[possess_edge].edge_list[j]) == gene)
			{

				edge_table[possess_edge].unused_edges--;

				edge_table[possess_edge].edge_list[j] =
					edge_table[possess_edge].edge_list[genes_remaining - 1];

				break;
			}
		}
	}
}

/*
 * gimme_gene
 *
 *	  priority is given to "shared" edges
 *	  (i.e. edges which both genes possess)
 *
 */
/*
 * gimme_gene - (中文)从边表候选邻居中挑选下一个城市
 *
 * 【作用】给定当前城市 edge(即 edge_table[某城市] 的值拷贝),在其未使用
 * 的邻居列表里挑选一个作为路径下一个城市。挑选优先级:共享边(负值)最高;
 * 其次选"未使用边最少"的邻居(最孤立的城市最先被处理);存在并列时随机
 * 决定。返回被选中的城市号。由 gimme_tour 在边表还有未用边时调用。
 *
 * 【设计思想】
 * - 共享边直接返回:负值在列表里出现即代表两个父代都认可这条相邻关系,
 *   是 ERX 最想保留的基因,遇到就无条件采纳;
 * - 否则计算所有候选邻居中 unused_edges 的最小值 minimum_edges:每个城市
 *   至多 4 条边(列表定长 4),所以初始值 5 必然被第一次比较替换;
 *   minimum_count 统计"拥有最少未用边的候选个数",供随机挑选使用;
 * - 最小边优先的道理:邻居越孤立,它的选择窗口越窄,越可能在下轮变成
 *   "无路可走"的失败点;及早把它消进路径能显著减少 edge_failure;
 * - 第一遍扫描只统计,第二遍扫描才"随机命中"第 rand_decision 个并列最小
 *   者,两遍都基于同一份 edge 列表,保证两次扫描看到一致的 unused_edges;
 * - 若干合法性边界:若某候选的 unused_edges 小于当前最小值,minimum_count
 *   必须重置为 1(elog ERROR 断言防止 minimum_count 未设置);若既无共享边
 *   又无任何候选(elog ERROR "neither shared nor minimum number nor random
 *   edge found"),说明调用方传入的列表已空,属内部错误。
 *
 * 【参数】
 *   root       —— PlannerInfo,传给随机数接口;
 *   edge       —— 当前城市的 Edge 值拷贝(unused_edges 决定扫描范围);
 *   edge_table —— 边表,用于查询各候选城市自己的 unused_edges。
 * 【返回值】被选中的城市号。
 */
static Gene
gimme_gene(PlannerInfo *root, Edge edge, Edge *edge_table)
{
	int			i;
	Gene		friend;
	int			minimum_edges;
	int			minimum_count = -1;
	int			rand_decision;

	/*
	 * no point has edges to more than 4 other points thus, this contrived
	 * minimum will be replaced
	 */

	minimum_edges = 5;

	/* consider candidate destination points in edge list */

	for (i = 0; i < edge.unused_edges; i++)
	{
		friend = (Gene) edge.edge_list[i];

		/*
		 * give priority to shared edges that are negative; so return 'em
		 */

		/*
		 * negative values are caught here so we need not worry about
		 * converting to absolute values
		 */
		if (friend < 0)
			return (Gene) abs(friend);


		/*
		 * give priority to candidates with fewest remaining unused edges;
		 * find out what the minimum number of unused edges is
		 * (minimum_edges); if there is more than one candidate with the
		 * minimum number of unused edges keep count of this number
		 * (minimum_count);
		 */

		/*
		 * The test for minimum_count can probably be removed at some point
		 * but comments should probably indicate exactly why it is guaranteed
		 * that the test will always succeed the first time around.  If it can
		 * fail then the code is in error
		 */


		if (edge_table[(int) friend].unused_edges < minimum_edges)
		{
			minimum_edges = edge_table[(int) friend].unused_edges;
			minimum_count = 1;
		}
		else if (minimum_count == -1)
			elog(ERROR, "minimum_count not set");
		else if (edge_table[(int) friend].unused_edges == minimum_edges)
			minimum_count++;
	}							/* for (i=0; i<edge.unused_edges; i++) */


	/* random decision of the possible candidates to use */
	rand_decision = geqo_randint(root, minimum_count - 1, 0);


	for (i = 0; i < edge.unused_edges; i++)
	{
		friend = (Gene) edge.edge_list[i];

		/* return the chosen candidate point */
		if (edge_table[(int) friend].unused_edges == minimum_edges)
		{
			minimum_count--;

			if (minimum_count == rand_decision)
				return friend;
		}
	}

	/* ... should never be reached */
	elog(ERROR, "neither shared nor minimum number nor random edge found");
	return 0;					/* to keep the compiler quiet */
}

/*
 * edge_failure
 *
 *	  routine for handling edge failure
 *
 */
/*
 * edge_failure - (中文)边失败处理:当前城市无可用边时挑选一个续接城市
 *
 * 【作用】当 gimme_tour 发现当前城市已无未用边(unused_edges == 0)时
 * 被调用,负责在尚未入环的城市里随机挑一个作为路径下一站,返回该城市号。
 * 优先挑"初始就有 4 条边"的城市,其次挑"还有剩余边"的城市,最后退化为
 * 任意未使用城市。
 *
 * 【设计思想】
 * - 边失败的本质:ERX 贪婪地按共享边/最小边前进,可能把某个城市提前"圈死"
 *   (它的所有邻居都已入环),导致当前城市无法延续。此时必须牺牲"边"的
 *   连续性,保证子代仍是合法排列;
 * - 统计阶段先扫一遍全表:remaining_edges 统计尚未入环(unused_edges != -1)
 *   且不是失败城市本身的城市数;four_count 进一步限定 total_edges == 4。
 *   优先选四边城市是为了"先把结构最复杂、最可能被孤立者解决掉";
 * - 随机挑选:在符合条件的城市中,用 geqo_randint 产生随机序号,遍历时
 *   递减计数器命中即返回,使每个合格城市被选中的概率相等;
 * - 边界情形:若连剩余边城市都没有(几乎只在最后一个位置出现),则兜底
 *   逻辑线性找一个 unused_edges >= 0 的城市返回——因为此时所有城市都已
 *   入环或只剩它,必定能找到。所有分支若意外走空都会 elog(ERROR) 报错,
 *   代表边表状态不一致的内部错误。
 *
 * 【参数】
 *   root       —— PlannerInfo,传给随机数接口;
 *   gene       —— 正在构建的子代路径(用于取失败城市 gene[index]);
 *   index      —— 失败城市在路径中的下标(前一个已入环城市);
 *   edge_table —— 边表(只读);
 *   num_gene   —— 城市个数。
 * 【返回值】挑中的续接城市号。
 */
static Gene
edge_failure(PlannerInfo *root, Gene *gene, int index, Edge *edge_table, int num_gene)
{
	int			i;
	Gene		fail_gene = gene[index];
	int			remaining_edges = 0;
	int			four_count = 0;
	int			rand_decision;


	/*
	 * how many edges remain? how many gene with four total (initial) edges
	 * remain?
	 */

	for (i = 1; i <= num_gene; i++)
	{
		if ((edge_table[i].unused_edges != -1) && (i != (int) fail_gene))
		{
			remaining_edges++;

			if (edge_table[i].total_edges == 4)
				four_count++;
		}
	}

	/*
	 * random decision of the gene with remaining edges and whose total_edges
	 * == 4
	 */

	if (four_count != 0)
	{

		rand_decision = geqo_randint(root, four_count - 1, 0);

		for (i = 1; i <= num_gene; i++)
		{

			if ((Gene) i != fail_gene &&
				edge_table[i].unused_edges != -1 &&
				edge_table[i].total_edges == 4)
			{

				four_count--;

				if (rand_decision == four_count)
					return (Gene) i;
			}
		}

		elog(LOG, "no edge found via random decision and total_edges == 4");
	}
	else if (remaining_edges != 0)
	{
		/* random decision of the gene with remaining edges */
		rand_decision = geqo_randint(root, remaining_edges - 1, 0);

		for (i = 1; i <= num_gene; i++)
		{

			if ((Gene) i != fail_gene &&
				edge_table[i].unused_edges != -1)
			{

				remaining_edges--;

				if (rand_decision == remaining_edges)
					return i;
			}
		}

		elog(LOG, "no edge found via random decision with remaining edges");
	}

	/*
	 * edge table seems to be empty; this happens sometimes on the last point
	 * due to the fact that the first point is removed from the table even
	 * though only one of its edges has been determined
	 */

	else
	{							/* occurs only at the last point in the tour;
								 * simply look for the point which is not yet
								 * used */

		for (i = 1; i <= num_gene; i++)
			if (edge_table[i].unused_edges >= 0)
				return (Gene) i;

		elog(LOG, "no edge found via looking for the last unused point");
	}


	/* ... should never be reached */
	elog(ERROR, "no edge found");
	return 0;					/* to keep the compiler quiet */
}

#endif							/* defined(ERX) */
