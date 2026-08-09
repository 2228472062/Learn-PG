/*------------------------------------------------------------------------
 *
 * geqo_main.c
 *	  solution to the query optimization problem
 *	  by means of a Genetic Algorithm (GA)
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/optimizer/geqo/geqo_main.c
 *
 * 【模块总览(中文)】
 * 本文件是 GEQO(Genetic Query Optimizer,遗传算法查询优化器)的主控模块,
 * 实现函数 geqo():把"查询优化问题"当作受限旅行商问题(TSP)求解——
 * 染色体(Chromosome)的每个基因对应一个基本关系(initial_rels 中的一个),
 * 基因串的顺序代表连接顺序,适应度(worth)是 geqo_eval 算出的连接树总
 * 代价。geqo() 由优化器主流程 planner.c 在候选关系数超过
 * geqo_threshold(默认 12)时调用,取代传统的动态规划(join_search_one_level)
 * 来寻找近似最优的连接顺序。
 *
 * 演化主循环的结构(每代):
 *   1. 选择:geqo_selection(geqo_selection.c)按线性偏差选父代 momma/daddy;
 *   2. 交叉:按编译期宏选择的重组算子产生子代 kid——
 *      - ERX(默认):geqo_erx.c 的 gimme_edge_table + gimme_tour;
 *      - PMX:geqo_pmx.c 的 pmx;
 *      - CX:geqo_cx.c 的 cx(若子代与父代无差异则调用 geqo_mutation.c 变异);
 *      - PX / OX1 / OX2:geqo_px.c / geqo_ox1.c / geqo_ox2.c 对应算子;
 *   3. 评估:geqo_eval(geqo_eval.c)计算 kid 的 worth;
 *   4. 入池:spread_chromo(geqo_pool.c)把 kid 插入排序池并顶替最差个体。
 * 循环次数与池规模由 gimme_pool_size / gimme_number_generations 依据 GUC
 * (Geqo_pool_size / Geqo_generations / Geqo_effort)或关系数的启发式计算。
 * 循环结束后取池中最优个体(data[0])再次 gimme_tree 还原为真正的连接树,
 * 返回给优化器作为 GEQO 的结果计划。
 *
 * 随机性:Geqo_seed 控制播种,geqo_random.c 统一管理随机流;结果可复现。
 * GEQO 把 PlannerInfo 扩展状态(GeqoPrivateData)与 GUC 参数(Geqo_effort
 * 等,在 guc_tables.c 注册)作为自己的配置通道。注意 geqo_main.c 的交叉
 * 分支全部由 #if defined(...) 编译期宏切换,运行期只存在其中一种。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_main.c
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

#include <math.h>

#include "optimizer/geqo.h"

#include "optimizer/geqo_misc.h"
#if defined(CX)
#include "optimizer/geqo_mutation.h"
#endif
#include "optimizer/geqo_pool.h"
#include "optimizer/geqo_random.h"
#include "optimizer/geqo_recombination.h"
#include "optimizer/geqo_selection.h"


/*
 * Configuration options
 */
int			Geqo_effort;
int			Geqo_pool_size;
int			Geqo_generations;
double		Geqo_selection_bias;
double		Geqo_seed;

/* GEQO is treated as an in-core planner extension */
int			Geqo_planner_extension_id = -1;

static int	gimme_pool_size(int nr_rel);
static int	gimme_number_generations(int pool_size);

/* complain if no recombination mechanism is #define'd */
#if !defined(ERX) && \
	!defined(PMX) && \
	!defined(CX)  && \
	!defined(PX)  && \
	!defined(OX1) && \
	!defined(OX2)
#error "must choose one GEQO recombination mechanism in geqo.h"
#endif


/*
 * geqo
 *	  solution of the query optimization problem
 *	  similar to a constrained Traveling Salesman Problem (TSP)
 */

/*
 * geqo - (中文)GEQO 主函数:用遗传算法求解查询连接顺序
 *
 * 【作用】给定全部基本关系 initial_rels 与关系数 number_of_rels,运行完整
 * 的遗传算法演化流程,返回最优连接顺序对应的连接树(RelOptInfo)。由
 * planner.c 在关系数超过 geqo_threshold 时调用。返回的 joinrel 的
 * cheapest_total_path 即为 GEQO 提交给上层计划流程的结果路径。
 *
 * 【设计思想】整个流程可拆为"准备 → 演化循环 → 收尾"三阶段:
 * - 准备:注册 GEQO 为 planner 扩展(GetPlannerExtensionId)以复用
 *   PlannerInfo 扩展状态机制;把 initial_rels 存入私有数据;置
 *   assumeReplanning=true 告知上层"GEQO 可能返回次优计划,允许重规划";
 *   用 Geqo_seed 播种;由 GUC/启发式确定池规模与世代数;alloc_pool 分配
 *   池,random_init_pool 随机生成初代,sort_pool 完成初始排序(此后靠
 *   spread_chromo 维持有序,无需再整体排序);分配父代工作区 momma/daddy,
 *   并按所选交叉模式分配 kid / 边表 / 城市表;
 * - 演化循环(number_generations 代):每代选择两个父代→用编译期宏选定的
 *   交叉算子生成子代→geqo_eval 评估→spread_chromo 入池。CX 模式下若
 *   cycle_diffs==0(交叉无效)则变异打散;GEQO_DEBUG 下按 status_interval
 *   打印世代摘要并累计 edge_failures/mutations 统计;
 * - 收尾:取池最优个体 data[0] 的基因串,再次调用 gimme_tree 生成真正的
 *   连接树(若失败 elog ERROR);释放所有分配(父代、子代、边表/城市表、
 *   池),清除扩展状态。ERX 模式下 kid 直接复用 momma 的指针(kid = momma),
 *   故无需单独释放 kid。内存布局注意:池内各染色体的基因串是独立分配、
 *   排序只交换 string 指针,因此最终 best_tour 指针仍有效。
 *
 * 【参数】
 *   root          —— PlannerInfo;
 *   number_of_rels —— 基本关系个数(染色体长度 num_gene);
 *   initial_rels   —— 基本关系列表(RelOptInfo),按 1..number_of_rels 编号。
 * 【返回值】最优连接顺序对应的顶层 joinrel(其 cheapest_total_path 为结果
 * 计划);失败时 elog(ERROR)。
 */
RelOptInfo *
geqo(PlannerInfo *root, int number_of_rels, List *initial_rels)
{
	GeqoPrivateData private;
	int			generation;
	Chromosome *momma;
	Chromosome *daddy;
	Chromosome *kid;
	Pool	   *pool;
	int			pool_size,
				number_generations;

#ifdef GEQO_DEBUG
	int			status_interval;
#endif
	Gene	   *best_tour;
	RelOptInfo *best_rel;

#if defined(ERX)
	Edge	   *edge_table;		/* list of edges */
	int			edge_failures = 0;
#endif
#if defined(CX) || defined(PX) || defined(OX1) || defined(OX2)
	City	   *city_table;		/* list of cities */
#endif
#if defined(CX)
	int			cycle_diffs = 0;
	int			mutations = 0;
#endif

	if (Geqo_planner_extension_id < 0)
		Geqo_planner_extension_id = GetPlannerExtensionId("geqo");

/* set up private information */
	SetPlannerInfoExtensionState(root, Geqo_planner_extension_id, &private);
	private.initial_rels = initial_rels;

/* inform core planner that we may replan */
	root->assumeReplanning = true;

/* initialize private number generator */
	geqo_set_seed(root, Geqo_seed);

/* set GA parameters */
	pool_size = gimme_pool_size(number_of_rels);
	number_generations = gimme_number_generations(pool_size);
#ifdef GEQO_DEBUG
	status_interval = 10;
#endif

/* allocate genetic pool memory */
	pool = alloc_pool(root, pool_size, number_of_rels);

/* random initialization of the pool */
	random_init_pool(root, pool);

/* sort the pool according to cheapest path as fitness */
	sort_pool(root, pool);		/* we have to do it only one time, since all
								 * kids replace the worst individuals in
								 * future (-> geqo_pool.c:spread_chromo ) */

#ifdef GEQO_DEBUG
	elog(DEBUG1, "GEQO selected %d pool entries, best %.2f, worst %.2f",
		 pool_size,
		 pool->data[0].worth,
		 pool->data[pool_size - 1].worth);
#endif

/* allocate chromosome momma and daddy memory */
	momma = alloc_chromo(root, pool->string_length);
	daddy = alloc_chromo(root, pool->string_length);

#if defined (ERX)
#ifdef GEQO_DEBUG
	elog(DEBUG2, "using edge recombination crossover [ERX]");
#endif
/* allocate edge table memory */
	edge_table = alloc_edge_table(root, pool->string_length);
#elif defined(PMX)
#ifdef GEQO_DEBUG
	elog(DEBUG2, "using partially matched crossover [PMX]");
#endif
/* allocate chromosome kid memory */
	kid = alloc_chromo(root, pool->string_length);
#elif defined(CX)
#ifdef GEQO_DEBUG
	elog(DEBUG2, "using cycle crossover [CX]");
#endif
/* allocate city table memory */
	kid = alloc_chromo(root, pool->string_length);
	city_table = alloc_city_table(root, pool->string_length);
#elif defined(PX)
#ifdef GEQO_DEBUG
	elog(DEBUG2, "using position crossover [PX]");
#endif
/* allocate city table memory */
	kid = alloc_chromo(root, pool->string_length);
	city_table = alloc_city_table(root, pool->string_length);
#elif defined(OX1)
#ifdef GEQO_DEBUG
	elog(DEBUG2, "using order crossover [OX1]");
#endif
/* allocate city table memory */
	kid = alloc_chromo(root, pool->string_length);
	city_table = alloc_city_table(root, pool->string_length);
#elif defined(OX2)
#ifdef GEQO_DEBUG
	elog(DEBUG2, "using order crossover [OX2]");
#endif
/* allocate city table memory */
	kid = alloc_chromo(root, pool->string_length);
	city_table = alloc_city_table(root, pool->string_length);
#endif


/* my pain main part: */
/* iterative optimization */

	for (generation = 0; generation < number_generations; generation++)
	{
		/* SELECTION: using linear bias function */
		geqo_selection(root, momma, daddy, pool, Geqo_selection_bias);

#if defined (ERX)
		/* EDGE RECOMBINATION CROSSOVER */
		gimme_edge_table(root, momma->string, daddy->string, pool->string_length, edge_table);

		kid = momma;

		/* are there any edge failures ? */
		edge_failures += gimme_tour(root, edge_table, kid->string, pool->string_length);
#elif defined(PMX)
		/* PARTIALLY MATCHED CROSSOVER */
		pmx(root, momma->string, daddy->string, kid->string, pool->string_length);
#elif defined(CX)
		/* CYCLE CROSSOVER */
		cycle_diffs = cx(root, momma->string, daddy->string, kid->string, pool->string_length, city_table);
		/* mutate the child */
		if (cycle_diffs == 0)
		{
			mutations++;
			geqo_mutation(root, kid->string, pool->string_length);
		}
#elif defined(PX)
		/* POSITION CROSSOVER */
		px(root, momma->string, daddy->string, kid->string, pool->string_length, city_table);
#elif defined(OX1)
		/* ORDER CROSSOVER */
		ox1(root, momma->string, daddy->string, kid->string, pool->string_length, city_table);
#elif defined(OX2)
		/* ORDER CROSSOVER */
		ox2(root, momma->string, daddy->string, kid->string, pool->string_length, city_table);
#endif


		/* EVALUATE FITNESS */
		kid->worth = geqo_eval(root, kid->string, pool->string_length);

		/* push the kid into the wilderness of life according to its worth */
		spread_chromo(root, kid, pool);


#ifdef GEQO_DEBUG
		if (status_interval && !(generation % status_interval))
			print_gen(stdout, pool, generation);
#endif

	}


#if defined(ERX)
#if defined(GEQO_DEBUG)
	if (edge_failures != 0)
		elog(LOG, "[GEQO] failures: %d, average: %d",
			 edge_failures, (int) number_generations / edge_failures);
	else
		elog(LOG, "[GEQO] no edge failures detected");
#else
	/* suppress variable-set-but-not-used warnings from some compilers */
	(void) edge_failures;
#endif
#endif

#if defined(CX) && defined(GEQO_DEBUG)
	if (mutations != 0)
		elog(LOG, "[GEQO] mutations: %d, generations: %d",
			 mutations, number_generations);
	else
		elog(LOG, "[GEQO] no mutations processed");
#endif

#ifdef GEQO_DEBUG
	print_pool(stdout, pool, 0, pool_size - 1);
#endif

#ifdef GEQO_DEBUG
	elog(DEBUG1, "GEQO best is %.2f after %d generations",
		 pool->data[0].worth, number_generations);
#endif


	/*
	 * got the cheapest query tree processed by geqo; first element of the
	 * population indicates the best query tree
	 */
	best_tour = (Gene *) pool->data[0].string;

	best_rel = gimme_tree(root, best_tour, pool->string_length);

	if (best_rel == NULL)
		elog(ERROR, "geqo failed to make a valid plan");

	/* DBG: show the query plan */
#ifdef NOT_USED
	print_plan(best_plan, root);
#endif

	/* ... free memory stuff */
	free_chromo(root, momma);
	free_chromo(root, daddy);

#if defined (ERX)
	free_edge_table(root, edge_table);
#elif defined(PMX)
	free_chromo(root, kid);
#elif defined(CX)
	free_chromo(root, kid);
	free_city_table(root, city_table);
#elif defined(PX)
	free_chromo(root, kid);
	free_city_table(root, city_table);
#elif defined(OX1)
	free_chromo(root, kid);
	free_city_table(root, city_table);
#elif defined(OX2)
	free_chromo(root, kid);
	free_city_table(root, city_table);
#endif

	free_pool(root, pool);

	/* ... clear root pointer to our private storage */
	SetPlannerInfoExtensionState(root, Geqo_planner_extension_id, NULL);

	return best_rel;
}


/*
 * Return either configured pool size or a good default
 *
 * The default is based on query size (no. of relations) = 2^(QS+1),
 * but constrained to a range based on the effort value.
 */
/*
 * gimme_pool_size - (中文)确定种群池规模
 *
 * 【作用】返回 GEQO 使用的池规模:若用户显式配置了 Geqo_pool_size 且 >= 2,
 * 直接采用;否则按关系数启发式计算一个随问题规模增长的默认值。由 geqo()
 * 在演化开始前调用。
 *
 * 【设计思想】默认值遵循"池规模与搜索空间大小相关"的经验:候选连接顺序
 * 的空间随关系数指数增长,规模取 2^(nr_rel + 1) 以匹配;但受 Geqo_effort
 * (GUC,1..10)夹取范围:上限 maxsize = 50 * effort(50~500),下限
 * minsize = 10 * effort(10~100)。若 2^(nr_rel+1) 超出上限就取上限,小于
 * 下限就取下限,否则取 2^(nr_rel+1) 的上取整(ceil)。这样关系多时池不会
 * 无限膨胀、关系少时也不会小到无法承载多样种群。池规模必须 >= 2 才有
 * 交叉意义(选择需要两个父代),因此显式配置为 1 时被忽略、走默认逻辑。
 *
 * 【参数】nr_rel —— 基本关系个数。
 * 【返回值】池个体数(>= 2)。
 */
static int
gimme_pool_size(int nr_rel)
{
	double		size;
	int			minsize;
	int			maxsize;

	/* Legal pool size *must* be at least 2, so ignore attempt to select 1 */
	if (Geqo_pool_size >= 2)
		return Geqo_pool_size;

	size = pow(2.0, nr_rel + 1.0);

	maxsize = 50 * Geqo_effort; /* 50 to 500 individuals */
	if (size > maxsize)
		return maxsize;

	minsize = 10 * Geqo_effort; /* 10 to 100 individuals */
	if (size < minsize)
		return minsize;

	return (int) ceil(size);
}


/*
 * Return either configured number of generations or a good default
 *
 * The default is the same as the pool size, which allows us to be
 * sure that less-fit individuals get pushed out of the breeding
 * population before the run finishes.
 */
static int
gimme_number_generations(int pool_size)
{
	if (Geqo_generations > 0)
		return Geqo_generations;

	return pool_size;
}
