/*------------------------------------------------------------------------
 *
 * geqo_pool.c
 *	  Genetic Algorithm (GA) pool stuff
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/optimizer/geqo/geqo_pool.c
 *
 * 【模块总览(中文)】
 * 本文件实现 GEQO 的"种群池"(Pool)管理,是整个遗传算法的"舞台"。
 * Pool 结构(定义于 geqo_pool.h)由两部分组成:
 * - size / string_length:种群个体数与每条染色体(路径)的长度;
 * - data[]:Chromosome 数组。每个 Chromosome 由基因串 string(指针,指向
 *   单独 palloc 的 Gene 数组,长度 string_length + 1)与适应度 worth
 *   (Cost,数值越小越好)组成。
 *
 * 本模块的功能覆盖种群生命周期的全部阶段:
 * 1. alloc_pool / free_pool:整池内存的分配与释放(每个个体的基因串各占
 *    一块独立内存);
 * 2. random_init_pool:用 init_tour(geqo_recombination.c)随机生成初代个体,
 *    并用 geqo_eval 评估其适应度,直接丢弃非法个体(评估返回 DBL_MAX),
 *    保证池中每个槽位都对应一条合法路径;
 * 3. sort_pool:按 worth 从小到大 qsort,使池保持"最优在前、最差在后"
 *    的排序不变量;
 * 4. spread_chromo:把新个体插入到按 worth 排序的池中正确位置,并顶替掉
 *    最差个体,维持池规模不变——这是演化循环中"后代进入种群"的入口;
 * 5. alloc_chromo / free_chromo:为交叉算子分配/释放单个染色体的工作区
 *    (父代 momma/daddy 与子代 kid 的载体)。
 *
 * 各函数间的调用关系(全部由 geqo_main.c 的 geqo() 驱动):
 * alloc_pool → random_init_pool → sort_pool → (演化循环内)
 * geqo_selection + 交叉算子 + geqo_eval → spread_chromo → (循环后)
 * free_chromo/free_pool。geqo_copy.c 的 geqo_copy 是 spread_chromo 落池
 * 时使用的拷贝原语。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_pool.c
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

#include <float.h>
#include <limits.h>

#include "optimizer/geqo_copy.h"
#include "optimizer/geqo_pool.h"
#include "optimizer/geqo_recombination.h"


static int	compare(const void *arg1, const void *arg2);

/*
 * alloc_pool
 *		allocates memory for GA pool
 */
/*
 * alloc_pool - (中文)为 GA 种群池分配内存
 *
 * 【作用】分配并初始化一个 Pool:包括 Pool 结构体、data 染色体数组,以及
 * 每个染色体独立的基因串内存。由 geqo_main.c 在演化循环开始前调用一次,
 * 生命周期贯穿整个 GEQO 过程,结束时由 free_pool 释放。
 *
 * 【设计思想】内存分三层分配:Pool 结构 → data 数组 → 每个 data[i].string
 * 基因串。每个染色体的基因串分配 string_length + 1 个元素,多出的一个
 * 槽位是历史约定(部分算子可能在下标 num_gene 处访问),不可省去。
 * 基因串为每个染色体独立 palloc,而非共享一块大内存,是为了配合
 * sort_pool 的 qsort:qsort 会整体搬移 Chromosome 结构,若各染色体共享
 * 基因串内存,排序后的 string 指针会指向错误的个体;而独立分配意味着
 * qsort 只交换 string 指针(64 位),不会拷贝昂贵的基因串数据。注意本
 * 函数不初始化染色体内容,基因串与 worth 由调用方(random_init_pool)随后
 * 填写。
 *
 * 【参数】
 *   root          —— PlannerInfo,当前未使用;
 *   pool_size     —— 种群个体数;
 *   string_length —— 每个个体基因串长度(城市/关系个数)。
 * 【返回值】初始化好的 Pool 指针。
 */
Pool *
alloc_pool(PlannerInfo *root, int pool_size, int string_length)
{
	Pool	   *new_pool;
	Chromosome *chromo;
	int			i;

	/* pool */
	new_pool = palloc_object(Pool);
	new_pool->size = pool_size;
	new_pool->string_length = string_length;

	/* all chromosome */
	new_pool->data = palloc_array(Chromosome, pool_size);

	/* all gene */
	chromo = (Chromosome *) new_pool->data; /* vector of all chromos */
	for (i = 0; i < pool_size; i++)
		chromo[i].string = palloc_array(Gene, string_length + 1);

	return new_pool;
}

/*
 * free_pool
 *		deallocates memory for GA pool
 */
/*
 * free_pool - (中文)释放 GA 种群池的内存
 *
 * 【作用】回收 alloc_pool 分配的全部内存:先逐个 pfree 每个染色体的基因
 * 串,再释放 data 数组,最后释放 Pool 结构体。由 geqo_main.c 在演化循环
 * 结束后调用。
 *
 * 【设计思想】释放顺序与分配顺序严格相反(基因串 → 数组 → 结构体),
 * 避免先释放 Pool 结构后无法定位内部指针;同时必须以 pool->size 为准
 * 遍历基因串,不能按分配时的 pool_size 假设,因为 pool->size 在本函数
 * 调用前未被修改(池规模在整个演化中保持不变)。调用后 pool 指针悬垂。
 *
 * 【参数】
 *   root —— PlannerInfo,当前未使用;
 *   pool —— 待释放的 Pool。
 * 【返回值】无。
 */
void
free_pool(PlannerInfo *root, Pool *pool)
{
	Chromosome *chromo;
	int			i;

	/* all gene */
	chromo = (Chromosome *) pool->data; /* vector of all chromos */
	for (i = 0; i < pool->size; i++)
		pfree(chromo[i].string);

	/* all chromosome */
	pfree(pool->data);

	/* pool */
	pfree(pool);
}

/*
 * random_init_pool
 *		initialize genetic pool
 */
/*
 * random_init_pool - (中文)随机初始化种群池(生成初代个体)
 *
 * 【作用】为池中每个槽位生成一个随机的合法路径个体并评估其适应度。由
 * geqo_main.c 在演化循环开始前调用。评估为"非法"的个体(geqo_eval 返回
 * DBL_MAX)被立即丢弃,不会占用池空间。
 *
 * 【设计思想】对每个槽位:先用 init_tour(geqo_recombination.c)生成随机
 * 合法路径,再用 geqo_eval 计算其总代价作为适应度 worth。由于 geqo_eval
 * 会尝试把路径翻译成可执行的连接顺序,而某些路径(受连接顺序限制、
 * LATERAL 语义等约束)无法形成合法连接树,此时返回 DBL_MAX 表示"无解"。
 * 这类个体对演化毫无意义,应直接跳过、继续尝试下一个随机路径。为防止
 * 无限循环,若连续 10000 次(i == 0 时计数从 bad 累计)都无法生成第一个
 * 合法个体,判定 GEQO 无法工作,elog(ERROR) 终止。注意 DBL_MAX 是
 * "无限大"标志:任何真实的连接代价都远小于它,所以比较用 "< DBL_MAX"
 * 即可可靠区分合法与非法。GEQO_DEBUG 下会打印丢弃的非法个体数量。
 *
 * 【参数】
 *   root —— PlannerInfo,传给 init_tour 与 geqo_eval;
 *   pool —— 待填充的池,data[i].string 必须已由 alloc_pool 分配。
 * 【返回值】无(填充 pool->data[i].worth 与 string)。
 */
void
random_init_pool(PlannerInfo *root, Pool *pool)
{
	Chromosome *chromo = (Chromosome *) pool->data;
	int			i;
	int			bad = 0;

	/*
	 * We immediately discard any invalid individuals (those that geqo_eval
	 * returns DBL_MAX for), thereby not wasting pool space on them.
	 *
	 * If we fail to make any valid individuals after 10000 tries, give up;
	 * this probably means something is broken, and we shouldn't just let
	 * ourselves get stuck in an infinite loop.
	 */
	i = 0;
	while (i < pool->size)
	{
		init_tour(root, chromo[i].string, pool->string_length);
		pool->data[i].worth = geqo_eval(root, chromo[i].string,
										pool->string_length);
		if (pool->data[i].worth < DBL_MAX)
			i++;
		else
		{
			bad++;
			if (i == 0 && bad >= 10000)
				elog(ERROR, "geqo failed to make a valid plan");
		}
	}

#ifdef GEQO_DEBUG
	if (bad > 0)
		elog(DEBUG1, "%d invalid tours found while selecting %d pool entries",
			 bad, pool->size);
#endif
}

/*
 * sort_pool
 *	 sorts input pool according to worth, from smallest to largest
 *
 *	 maybe you have to change compare() for different ordering ...
 */
/*
 * sort_pool - (中文)按适应度从好到差排序种群池
 *
 * 【作用】对池中所有个体按 worth 升序排序(worth 最小=代价最低=最优,
 * 排在最前)。由 geqo_main.c 在初始化后调用一次,之后不再需要整体排序:
 * 因为后续每代的后代都通过 spread_chromo 插入正确位置,维持全局有序。
 *
 * 【设计思想】直接用 C 标准库 qsort 对 data[] 数组排序,比较函数是
 * compare()。排序时整个 Chromosome 结构(两个指针/标量)被搬移,基因串
 * 本体不动——这正是 alloc_pool 为每个染色体独立分配基因串的原因。
 * 排序后建立并维护不变量:data[0] 恒为当前最优个体(演化结束时 geqo()
 * 直接取 data[0] 作为最终方案),data[pool_size-1] 恒为最差个体
 * (spread_chromo 每次顶替它)。注意 compare() 是"大于返回 1",与常规
 * 认识相反的方向约定,但它与 qsort 的要求一致。
 *
 * 【参数】
 *   root —— PlannerInfo,当前未使用;
 *   pool —— 待排序的池。
 * 【返回值】无(就地排序)。
 */
void
sort_pool(PlannerInfo *root, Pool *pool)
{
	qsort(pool->data, pool->size, sizeof(Chromosome), compare);
}

/*
 * compare
 *	 qsort comparison function for sort_pool
 */
/*
 * compare - (中文)qsort 用的染色体比较函数
 *
 * 【作用】作为 sort_pool 中 qsort 的比较回调,比较两个 Chromosome 的
 * 适应度 worth,决定排序方向:worth 小的(代价低、适应度好)排前面。
 *
 * 【设计思想】比较三个大小关系:小于返回 -1,大于返回 1,相等返回 0。
 * 注意返回值方向(大→1)恰好满足 qsort 的契约,使升序排序成立。qsort
 * 要求比较函数是严格全序且可传递的,worth 是浮点 Cost,这里用 == 直接
 * 判断相等——浮点相等在"两个代价恰好算出相同数值"时成立,对排序的
 * 稳定性与正确性没有影响。函数是纯函数、无副作用,符合 qsort 回调要求。
 *
 * 【参数】
 *   arg1 —— 指向第一个 Chromosome 的 const void 指针;
 *   arg2 —— 指向第二个 Chromosome 的 const void 指针。
 * 【返回值】arg1 < arg2 返回 -1;arg1 > arg2 返回 1;相等返回 0。
 */
static int
compare(const void *arg1, const void *arg2)
{
	const Chromosome *chromo1 = (const Chromosome *) arg1;
	const Chromosome *chromo2 = (const Chromosome *) arg2;

	if (chromo1->worth == chromo2->worth)
		return 0;
	else if (chromo1->worth > chromo2->worth)
		return 1;
	else
		return -1;
}

/*
 * alloc_chromo
 *	  allocates a chromosome and string space
 */
/*
 * alloc_chromo - (中文)分配一个染色体结构及其基因串空间
 *
 * 【作用】分配一个 Chromosome 结构体以及一块足以容纳 string_length + 1
 * 个基因的字符串内存,返回指向染色体的指针。由 geqo_main.c 为父代
 * momma/daddy(所有交叉模式)和子代 kid(非 ERX 模式)分配工作区。
 *
 * 【设计思想】Chromosome 包含 string(指针)与 worth 两个字段;这里必须
 * 同时分配 string 指向的内存,否则调用方随后 geqo_copy 往 string 里写
 * 会访问未分配内存。分配 string_length + 1 与 alloc_pool 的约定一致
 * (多出的槽位供可能的下标 num_gene 访问)。由 free_chromo 配对释放。
 *
 * 【参数】
 *   root          —— PlannerInfo,当前未使用;
 *   string_length —— 基因串长度。
 * 【返回值】Chromosome 指针;其 string 字段已分配且长度合法,worth 未初始化。
 */
Chromosome *
alloc_chromo(PlannerInfo *root, int string_length)
{
	Chromosome *chromo;

	chromo = palloc_object(Chromosome);
	chromo->string = palloc_array(Gene, string_length + 1);

	return chromo;
}

/*
 * free_chromo
 *	  deallocates a chromosome and string space
 */
/*
 * free_chromo - (中文)释放一个染色体结构及其基因串空间
 *
 * 【作用】回收 alloc_chromo 分配的内存:先 pfree 基因串,再 pfree 染色体
 * 结构体。由 geqo_main.c 在演化循环结束后对 momma/daddy/kid 调用。
 *
 * 【设计思想】释放顺序必须"先内后外"——先释放 string 指针指向的内存,
 * 再释放结构体本身;颠倒会导致悬垂指针或内存泄漏。本函数只释放单个
 * 染色体,与 free_pool(释放整个池)职责不同,二者不可混用。
 *
 * 【参数】
 *   root   —— PlannerInfo,当前未使用;
 *   chromo —— 待释放的染色体(必须由 alloc_chromo 分配)。
 * 【返回值】无。
 */
void
free_chromo(PlannerInfo *root, Chromosome *chromo)
{
	pfree(chromo->string);
	pfree(chromo);
}

/*
 * spread_chromo
 *	 inserts a new chromosome into the pool, displacing worst gene in pool
 *	 assumes best->worst = smallest->largest
 */
/*
 * spread_chromo - (中文)把新个体插入排序池的正确位置,顶替最差个体
 *
 * 【作用】把后代染色体 chromo 插入到已按 worth 升序排列的池中,保持有序,
 * 并把最差个体挤出池外(池规模不变)。由 geqo_main.c 在每个世代评估完
 * 子代后调用。若 chromo 比当前最差个体还差,则直接放弃、不改变池。
 *
 * 【设计思想】整个过程分三步,核心是"把新个体塞进有序数组并丢弃末尾":
 * 1. 若 chromo->worth > pool->data[pool_size-1].worth,说明新个体连最差
 *    都不如,入池无意义,直接返回;
 * 2. 二分查找插入位置 index:维护 top/mid/bot 三个下标,利用池已有序的
 *    不变量快速定位 chromo 应落入的槽位。四种情形直接得答案:比 data[top]
 *    小(插最前)、等于 data[mid]/data[bot]、或区间已收缩到 bot-top<=1
 *    (只能插 bot 处);否则依据与 data[mid] 的大小关系收缩区间。注意
 *    查找里用到的相等判断是为了减少比较次数,不等时用区间收缩逼近;
 * 3. 落位:先把新个体拷到末尾槽位(geqo_copy),再用三变量轮转
 *    (swap_chromo/tmp_chromo)把基因串指针与 worth 从 index 到末尾逐位
 *    向后搬一格,最终 data[index] 即新个体,原末尾最差个体被挤出。
 *    交换的是 string 指针而非基因串内容,成本恒定,这也是独立分配基因串
 *    的好处。预排序保证每次插入 O(log n + n) 均摊高效。
 *
 * 【参数】
 *   root   —— PlannerInfo,传给 geqo_copy;
 *   chromo —— 待入池的后代(只读);
 *   pool   —— 已排序的池,前提是 data[0..size-1] 有序且 size >= 2。
 * 【返回值】无。
 */
void
spread_chromo(PlannerInfo *root, Chromosome *chromo, Pool *pool)
{
	int			top,
				mid,
				bot;
	int			i,
				index;
	Chromosome	swap_chromo,
				tmp_chromo;

	/* new chromo is so bad we can't use it */
	if (chromo->worth > pool->data[pool->size - 1].worth)
		return;

	/* do a binary search to find the index of the new chromo */

	top = 0;
	mid = pool->size / 2;
	bot = pool->size - 1;
	index = -1;

	while (index == -1)
	{
		/* these 4 cases find a new location */

		if (chromo->worth <= pool->data[top].worth)
			index = top;
		else if (chromo->worth == pool->data[mid].worth)
			index = mid;
		else if (chromo->worth == pool->data[bot].worth)
			index = bot;
		else if (bot - top <= 1)
			index = bot;


		/*
		 * these 2 cases move the search indices since a new location has not
		 * yet been found.
		 */

		else if (chromo->worth < pool->data[mid].worth)
		{
			bot = mid;
			mid = top + ((bot - top) / 2);
		}
		else
		{						/* (chromo->worth > pool->data[mid].worth) */
			top = mid;
			mid = top + ((bot - top) / 2);
		}
	}							/* ... while */

	/* now we have index for chromo */

	/*
	 * move every gene from index on down one position to make room for chromo
	 */

	/*
	 * copy new gene into pool storage; always replace worst gene in pool
	 */

	geqo_copy(root, &pool->data[pool->size - 1], chromo, pool->string_length);

	swap_chromo.string = pool->data[pool->size - 1].string;
	swap_chromo.worth = pool->data[pool->size - 1].worth;

	for (i = index; i < pool->size; i++)
	{
		tmp_chromo.string = pool->data[i].string;
		tmp_chromo.worth = pool->data[i].worth;

		pool->data[i].string = swap_chromo.string;
		pool->data[i].worth = swap_chromo.worth;

		swap_chromo.string = tmp_chromo.string;
		swap_chromo.worth = tmp_chromo.worth;
	}
}
