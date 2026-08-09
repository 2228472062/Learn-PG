/*------------------------------------------------------------------------
*
* geqo_recombination.c
*	 misc recombination procedures
*
 * src/backend/optimizer/geqo/geqo_recombination.c
 *
 * 【模块总览(中文)】
 * 本文件是 GEQO 各重组(crossover)算子的"公共设施模块",提供两类底层服务:
 * (1) 随机初始化一条合法路径的 init_tour;
 * (2) "城市表"(City)内存的分配与释放 alloc_city_table / free_city_table。
 *
 * 所谓"城市表"是为 CX、PX、OX1、OX2 这四种基于位置的交叉算子准备的辅助
 * 查找结构(定义于 geqo_recombination.h)。每个算子在生成子代时,都需要
 * 快速判断"某城市是否已被写入子代"(去重用),城市表正是为此设计:它按
 * 城市编号(1..num_gene)组织,每条记录携带该城市在两个父代中的位置
 * (tour1_position / tour2_position)以及 used 标记。之所以分配 num_gene + 1
 * 个元素,是让下标与城市编号 1..num_gene 直接一一对应,下标 0 闲置,
 * 从而免去所有"城市号减一"的下标换算。整个城市表由 geqo_main.c 在演化
 * 循环外分配一次、全程复用,循环结束时统一释放。
 *
 * init_tour 则负责为种群池的每个初始个体随机生成一条合法排列,是
 * random_init_pool(geqo_pool.c)的基石;它保证每个城市恰好出现一次,
 * 是 GEQO 所有后续操作(交叉、变异、评估)都依赖的"合法染色体"起点。
 *
 * 注意:ERX 算子使用的是独立的"边表"(Edge,geqo_erx.c),不经过本文件;
 * 本文件的城市表仅服务上述四种位置型交叉算子。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_recombination.c
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

/* -- parts of this are adapted from D. Whitley's Genitor algorithm -- */

#include "postgres.h"

#include "optimizer/geqo_random.h"
#include "optimizer/geqo_recombination.h"


/*
 * init_tour
 *
 *	 Randomly generates a legal "traveling salesman" tour
 *	 (i.e. where each point is visited only once.)
 */
/*
 * init_tour - (中文)随机生成一条包含全部城市的合法路径(初代个体)
 *
 * 【作用】用随机置换填充 tour[],生成一个合法的 TSP 路径,即每个城市号
 * (1..num_gene)恰好出现一次。由 geqo_pool.c 的 random_init_pool 在初始化
 * 种群时对每个个体调用,是遗传算法第一代个体的唯一来源。
 *
 * 【设计思想】采用 Fisher-Yates 洗牌的"inside-out"(由内向外)变体,一遍
 * 线性扫描即可得到均匀随机置换。算法逻辑:把第 i+1 个城市"追加"到数组
 * 末尾,再与随机选中的 tour[j](0 <= j <= i)交换;当 i == j 时不交换
 * (即"与自身交换"),这是必要的,否则最后一个城市永远无法留在末尾、
 * 某些置换将无法生成。注意 j = geqo_randint(root, i, 0) 上界是 i 而不是
 * i+1,配合 "i != j 时不读取未初始化元素" 的检查:当 j < i 时 tour[j]
 * 已被前一轮写入,读它并搬到 tour[i] 是安全的;当 j == i 时保持原值。
 * 与经典"先填 1..n 再两两交换"的洗牌相比,本变体省去了初始化数组的
 * 一次遍历,且天然只生成合法置换。城市编号从 1 开始,以 Gene(实为 int)
 * 存储,正好对应用户关系中 1..num_gene 的编号约定。
 *
 * 【参数】
 *   root     —— PlannerInfo,传给随机数接口;
 *   tour     —— 输出,长度为 num_gene 的路径数组(调用方分配);
 *   num_gene —— 城市个数;为 0 时本函数不做任何事。
 * 【返回值】无(结果写入 tour[])。
 */
void
init_tour(PlannerInfo *root, Gene *tour, int num_gene)
{
	int			i,
				j;

	/*
	 * We must fill the tour[] array with a random permutation of the numbers
	 * 1 .. num_gene.  We can do that in one pass using the "inside-out"
	 * variant of the Fisher-Yates shuffle algorithm.  Notionally, we append
	 * each new value to the array and then swap it with a randomly-chosen
	 * array element (possibly including itself, else we fail to generate
	 * permutations with the last city last).  The swap step can be optimized
	 * by combining it with the insertion.
	 */
	if (num_gene > 0)
		tour[0] = (Gene) 1;

	for (i = 1; i < num_gene; i++)
	{
		j = geqo_randint(root, i, 0);
		/* i != j check avoids fetching uninitialized array element */
		if (i != j)
			tour[i] = tour[j];
		tour[j] = (Gene) (i + 1);
	}
}

/* city table is used in these recombination methods: */
#if defined(CX) || defined(PX) || defined(OX1) || defined(OX2)

/*
 * alloc_city_table
 *
 *	 allocate memory for city table
 */
/*
 * alloc_city_table - (中文)为城市表分配内存
 *
 * 【作用】分配一个长度为 num_gene + 1 的 City 数组并返回首地址。由
 * geqo_main.c 在 CX / PX / OX1 / OX2 模式的演化循环开始前调用一次,整个
 * 演化期间复用,循环结束时由 free_city_table 释放。
 *
 * 【设计思想】多分配一个元素(下标 0 闲置)是为了让 city_table[i] 能被
 * 城市编号 i(1..num_gene)直接索引,从而在算子代码中避免 "城市号 - 1"
 * 的换算,既省时又减少出错。数组内容由各交叉算子在使用前自行初始化
 * (如清零 used 标记),本函数只负责分配,不负责置初值。内存使用 palloc,
 * 归属当前内存上下文,无需逐元素释放(City 内部只有标量字段)。
 *
 * 【参数】
 *   root     —— PlannerInfo,当前未使用;
 *   num_gene —— 城市(基因)个数。
 * 【返回值】City 数组指针,下标 1..num_gene 有效,下标 0 未使用。
 */
City *
alloc_city_table(PlannerInfo *root, int num_gene)
{
	City	   *city_table;

	/*
	 * palloc one extra location so that nodes numbered 1..n can be indexed
	 * directly; 0 will not be used
	 */
	city_table = palloc_array(City, num_gene + 1);

	return city_table;
}

/*
 * free_city_table
 *
 *	  deallocate memory of city table
 */
/*
 * free_city_table - (中文)释放城市表内存
 *
 * 【作用】回收 alloc_city_table 分配的城市表。由 geqo_main.c 在演化循环
 * 结束后调用,与 alloc_city_table 配对,确保 GEQO 运行期间不泄漏内存。
 *
 * 【设计思想】城市表是一整块 palloc 内存,整块 pfree 即可;City 结构内部
 * 没有指针成员,不存在需要逐元素释放的嵌套内存。调用后 city_table 指针
 * 变为悬垂,调用方不应再引用它。
 *
 * 【参数】
 *   root       —— PlannerInfo,当前未使用;
 *   city_table —— alloc_city_table 返回的城市表指针。
 * 【返回值】无。
 */
void
free_city_table(PlannerInfo *root, City * city_table)
{
	pfree(city_table);
}

#endif							/* CX || PX || OX1 || OX2 */
