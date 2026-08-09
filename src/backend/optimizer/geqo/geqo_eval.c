/*------------------------------------------------------------------------
 *
 * geqo_eval.c
 *	  Routines to evaluate query trees
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/optimizer/geqo/geqo_eval.c
 *
 * 【模块总览(中文)】
 * 本文件实现 GEQO 的"适应度评估"(fitness evaluation)机制,是整个遗传
 * 算法的核心评估环节:把一条染色体(即一个连接顺序方案,tour)翻译成
 * 具体的连接树,并用 PostgreSQL 代价模型算出总代价,作为该个体的
 * 适应度 worth(代价越低越好)。评估结果驱动选择、排序、入池等所有后续
 * 环节。
 *
 * 关键机制:GEQO 没有为每个个体真正构建完整的执行计划,而是借用优化器
 * 标准的 joinrel 构建机制(make_join_rel / set_cheapest 等)按 tour 指定的
 * 顺序增量式地连接各个关系,只保留"当前连接方式下最便宜的路径"的代价。
 * 为了不污染真正的规划状态,geqo_eval 在评估每个个体时:
 * - 建立独立的私有内存上下文 "GEQO",gimme_tree 内产生的临时 RelOptInfo
 *   与路径都落在这里,评估完整体删除回收;
 * - 记录评估前 root->join_rel_list 的长度,评估后 list_truncate 还原,
 *   并临时把 join_rel_hash 置 NULL 避开哈希表污染;
 * - 断言 join_rel_level 未被占用(评估期间不使用分层连接构建)。
 *
 * 主流程分为两级:
 * - geqo_eval(root, tour, num_gene):对外入口。建上下文、调用 gimme_tree、
 *   取结果 joinrel 的最便宜路径代价;若无法形成合法连接树则返回 DBL_MAX
 *   (无穷大标志非法个体);
 * - gimme_tree:把 tour 中的关系按顺序处理,用"团"(Clump)机制合并。
 *   每个新关系先并入第一个能合法连接的团;不行就自成一个团;若产生新团
 *   又能与其它团合并则递归合并。全部扫完后,若还剩多个团,则忽略启发式
 *   规则、强行按合法顺序合并;仍无法合成一个团则返回 NULL(非法)。
 *   merge_clump 负责合并与按规模排序插入,desirable_join 判断两个关系
 *   之间是否应当优先连接(有连接条件或连接顺序限制)。
 *
 * 本模块与 geqo_pool.c(random_init_pool 评估初代)、geqo_main.c(每代评估
 * 子代)直接协作;评估产生的代价即 Chromosome.worth,是种群排序与选择的
 * 依据。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_eval.c
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

#include "postgres.h"

#include <float.h>
#include <limits.h>

#include "optimizer/geqo.h"
#include "optimizer/joininfo.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "utils/memutils.h"


/* A "clump" of already-joined relations within gimme_tree */
typedef struct
{
	RelOptInfo *joinrel;		/* joinrel for the set of relations */
	int			size;			/* number of input relations in clump */
} Clump;

static List *merge_clump(PlannerInfo *root, List *clumps, Clump *new_clump,
						 int num_gene, bool force);
static bool desirable_join(PlannerInfo *root,
						   RelOptInfo *outer_rel, RelOptInfo *inner_rel);


/*
 * geqo_eval
 *
 * Returns cost of a query tree as an individual of the population.
 *
 * If no legal join order can be extracted from the proposed tour,
 * returns DBL_MAX.
 */
/*
 * geqo_eval - (中文)评估一条染色体(tour)的适应度,返回连接树总代价
 *
 * 【作用】把给定的连接顺序 tour 交给 gimme_tree 构建连接树,取其最便宜
 * 路径的 total_cost 作为该个体的适应度。若 tour 无法构成合法连接顺序,
 * 返回 DBL_MAX(无穷大,表示非法个体)。由 random_init_pool(评估初代)与
 * geqo_main.c(每代评估子代)调用,是 GEQO 中评估次最频繁的函数。
 *
 * 【设计思想】评估必须在"不污染真正规划状态"的前提下进行,因此本函数
 * 做了三层隔离:
 * 1. 内存隔离:新建名为 "GEQO" 的私有内存上下文,切换到它再调用
 *    gimme_tree,所有临时 RelOptInfo/Path 都落在其中;评估完切换回原
 *    上下文并整体 MemoryContextDelete,一次性回收。把它设为规划器常规
 *    上下文的子上下文,即使中途 ereport(ERROR) 也能被父上下文连带回收;
 * 2. 列表隔离:gimme_tree 会向 root->join_rel_list 追加新 joinrel(假定
 *    总是追加在尾部),评估前记录原始长度、评估后 list_truncate 还原,
 *    保证真正的规划流程看不到这些临时关系;
 * 3. 哈希隔离:若有 join_rel_hash,评估期间把它临时置 NULL,使 gimme_tree
 *    内部的连接构建走局部哈希/线性查找,结束后恢复;同时断言
 *    join_rel_level 为空,避免与分层连接逻辑冲突。
 * 评估结果的取值:若 gimme_tree 返回合法 joinrel,取 cheapest_total_path
 * 的 total_cost(注意此处只评估代价,不追求完整路径);否则 fitness 为
 * DBL_MAX。把 DBL_MAX 当作"非法"哨兵是 GEQO 的全局约定,上游据此丢弃
 * 个体。已知局限见源码注释:GEQO 尚不支持部分结果检索(partial result
 * retrieval)与参数化路径的优化,这些场景下评估可能不够精确。
 *
 * 【参数】
 *   root     —— PlannerInfo;
 *   tour     —— 待评估的连接顺序(城市号 1..num_gene,对应 initial_rels);
 *   num_gene —— 关系个数。
 * 【返回值】合法方案的 total_cost(越小越好);非法方案返回 DBL_MAX。
 */
Cost
geqo_eval(PlannerInfo *root, Gene *tour, int num_gene)
{
	MemoryContext mycontext;
	MemoryContext oldcxt;
	RelOptInfo *joinrel;
	Cost		fitness;
	int			savelength;
	struct HTAB *savehash;

	/*
	 * Create a private memory context that will hold all temp storage
	 * allocated inside gimme_tree().
	 *
	 * Since geqo_eval() will be called many times, we can't afford to let all
	 * that memory go unreclaimed until end of statement.  Note we make the
	 * temp context a child of the planner's normal context, so that it will
	 * be freed even if we abort via ereport(ERROR).
	 */
	mycontext = AllocSetContextCreate(CurrentMemoryContext,
									  "GEQO",
									  ALLOCSET_DEFAULT_SIZES);
	oldcxt = MemoryContextSwitchTo(mycontext);

	/*
	 * gimme_tree will add entries to root->join_rel_list, which may or may
	 * not already contain some entries.  The newly added entries will be
	 * recycled by the MemoryContextDelete below, so we must ensure that the
	 * list is restored to its former state before exiting.  We can do this by
	 * truncating the list to its original length.  NOTE this assumes that any
	 * added entries are appended at the end!
	 *
	 * We also must take care not to mess up the outer join_rel_hash, if there
	 * is one.  We can do this by just temporarily setting the link to NULL.
	 * (If we are dealing with enough join rels, which we very likely are, a
	 * new hash table will get built and used locally.)
	 *
	 * join_rel_level[] shouldn't be in use, so just Assert it isn't.
	 */
	savelength = list_length(root->join_rel_list);
	savehash = root->join_rel_hash;
	Assert(root->join_rel_level == NULL);

	root->join_rel_hash = NULL;

	/* construct the best path for the given combination of relations */
	joinrel = gimme_tree(root, tour, num_gene);

	/*
	 * compute fitness, if we found a valid join
	 *
	 * XXX geqo does not currently support optimization for partial result
	 * retrieval, nor do we take any cognizance of possible use of
	 * parameterized paths --- how to fix?
	 */
	if (joinrel)
	{
		Path	   *best_path = joinrel->cheapest_total_path;

		fitness = best_path->total_cost;
	}
	else
		fitness = DBL_MAX;

	/*
	 * Restore join_rel_list to its former state, and put back original
	 * hashtable if any.
	 */
	root->join_rel_list = list_truncate(root->join_rel_list,
										savelength);
	root->join_rel_hash = savehash;

	/* release all the memory acquired within gimme_tree */
	MemoryContextSwitchTo(oldcxt);
	MemoryContextDelete(mycontext);

	return fitness;
}

/*
 * gimme_tree
 *	  Form planner estimates for a join tree constructed in the specified
 *	  order.
 *
 *	 'tour' is the proposed join order, of length 'num_gene'
 *
 * Returns a new join relation whose cheapest path is the best plan for
 * this join order.  NB: will return NULL if join order is invalid and
 * we can't modify it into a valid order.
 *
 * The original implementation of this routine always joined in the specified
 * order, and so could only build left-sided plans (and right-sided and
 * mixtures, as a byproduct of the fact that make_join_rel() is symmetric).
 * It could never produce a "bushy" plan.  This had a couple of big problems,
 * of which the worst was that there are situations involving join order
 * restrictions where the only valid plans are bushy.
 *
 * The present implementation takes the given tour as a guideline, but
 * postpones joins that are illegal or seem unsuitable according to some
 * heuristic rules.  This allows correct bushy plans to be generated at need,
 * and as a nice side-effect it seems to materially improve the quality of the
 * generated plans.  Note however that since it's just a heuristic, it can
 * still fail in some cases.  (In particular, we might clump together
 * relations that actually mustn't be joined yet due to LATERAL restrictions;
 * since there's no provision for un-clumping, this must lead to failure.)
 */
/*
 * gimme_tree - (中文)按指定顺序构建连接树并返回最外层 joinrel
 *
 * 【作用】把 tour 中列出的 num_gene 个基本关系按给定顺序、用"团"(Clump)
 * 机制合并成一棵连接树,返回根 joinrel(其 cheapest_total_path 即该连接
 * 顺序下的最优计划)。由 geqo_eval 评估个体与 geqo_main.c 提取最终方案时
 * 调用;若无法合并成单一连接树则返回 NULL。
 *
 * 【设计思想】tour 只是"推荐顺序",而不是必须严格遵守的连接次序——这是
 * 本实现与早期版本的根本区别。原因:真实的连接顺序常受连接条件、外连接
 * 方向、LATERAL 等语义限制,严格按 tour 顺序只能构造左深树,而某些合法
 * 计划必须是稠密树(bushy)或顺序受限。因此 gimme_tree 采用启发式"团"
 * 算法:
 * 1. 依 tour 顺序逐个取出关系,包成单元素 Clump(joinrel=该关系,size=1);
 * 2. 用 merge_clump 尝试把它并入现有团——条件是"理想连接"
 *    (desirable_join:有关系连接条件或连接顺序限制)。能并入就并入,并入后
 *    递归尝试与其它团再合并;不能并入就作为独立团,按 size 降序插入列表
 *    (大的在前,便于优先扩张);
 * 3. 全部扫完后若还残留多个团,说明启发式保守了:此时用 force=true 再走
 *    一遍 merge_clump,允许做笛卡尔积强行把团并完(至少按某种合法顺序);
 * 4. 最终若仍不止一个团(例如 LATERAL 限制使得某两个关系必须相邻、但顺序
 *    上被拆开,团机制无法撤销),返回 NULL 表示该 tour 非法,由上层把该
 *    个体标为 DBL_MAX。
 * 每个 joinrel 生成后会调用 generate_partitionwise_join_paths、
 * generate_useful_gather_paths(顶层除外)、set_cheapest 等标准路径生成流程,
 * 使 joinrel 的 cheapest_total_path 反映真实可用的代价。团列表内 Clump
 * 的生命周期完全由本函数管理(合并成功的 new_clump 会被 pfree)。
 *
 * 【参数】
 *   root     —— PlannerInfo;
 *   tour     —— 推荐连接顺序(城市号 1..num_gene);
 *   num_gene —— 关系个数。
 * 【返回值】合并后的根 joinrel;tour 非法时返回 NULL。
 */
RelOptInfo *
gimme_tree(PlannerInfo *root, Gene *tour, int num_gene)
{
	GeqoPrivateData *private = GetGeqoPrivateData(root);
	List	   *clumps;
	int			rel_count;

	/*
	 * Sometimes, a relation can't yet be joined to others due to heuristics
	 * or actual semantic restrictions.  We maintain a list of "clumps" of
	 * successfully joined relations, with larger clumps at the front. Each
	 * new relation from the tour is added to the first clump it can be joined
	 * to; if there is none then it becomes a new clump of its own. When we
	 * enlarge an existing clump we check to see if it can now be merged with
	 * any other clumps.  After the tour is all scanned, we forget about the
	 * heuristics and try to forcibly join any remaining clumps.  If we are
	 * unable to merge all the clumps into one, fail.
	 */
	clumps = NIL;

	for (rel_count = 0; rel_count < num_gene; rel_count++)
	{
		int			cur_rel_index;
		RelOptInfo *cur_rel;
		Clump	   *cur_clump;

		/* Get the next input relation */
		cur_rel_index = (int) tour[rel_count];
		cur_rel = (RelOptInfo *) list_nth(private->initial_rels,
										  cur_rel_index - 1);

		/* Make it into a single-rel clump */
		cur_clump = palloc_object(Clump);
		cur_clump->joinrel = cur_rel;
		cur_clump->size = 1;

		/* Merge it into the clumps list, using only desirable joins */
		clumps = merge_clump(root, clumps, cur_clump, num_gene, false);
	}

	if (list_length(clumps) > 1)
	{
		/* Force-join the remaining clumps in some legal order */
		List	   *fclumps;
		ListCell   *lc;

		fclumps = NIL;
		foreach(lc, clumps)
		{
			Clump	   *clump = (Clump *) lfirst(lc);

			fclumps = merge_clump(root, fclumps, clump, num_gene, true);
		}
		clumps = fclumps;
	}

	/* Did we succeed in forming a single join relation? */
	if (list_length(clumps) != 1)
		return NULL;

	return ((Clump *) linitial(clumps))->joinrel;
}

/*
 * Merge a "clump" into the list of existing clumps for gimme_tree.
 *
 * We try to merge the clump into some existing clump, and repeat if
 * successful.  When no more merging is possible, insert the clump
 * into the list, preserving the list ordering rule (namely, that
 * clumps of larger size appear earlier).
 *
 * If force is true, merge anywhere a join is legal, even if it causes
 * a cartesian join to be performed.  When force is false, do only
 * "desirable" joins.
 */
/*
 * merge_clump - (中文)把一个团并入团列表,能合并则递归合并,否则按规模插入
 *
 * 【作用】尝试把 new_clump 与列表中的某个团合并(生成两团的连接 joinrel,
 * 吸收到旧团里并扩大其 size);合并成功后递归继续尝试合并(可能连锁合并
 * 多个团);无法合并时按 size 降序把 new_clump 插回列表。返回处理后的
 * 团列表。由 gimme_tree 对每个新关系以及收尾的强制合并阶段调用。
 *
 * 【设计思想】这是"团算法"的合并引擎,要点如下:
 * - 合并条件:force=true 时只要两团能构造出合法连接关系就合并(允许笛卡尔
 *   积);force=false 时还要求 desirable_join 成立,即两团之间存在连接条件
 *   或连接顺序限制——这是"理想连接"启发式,推迟无连接条件关系的连接,
 *   以减少笛卡尔积、提高计划质量;
 * - 合并动作:make_join_rel 构造新 joinrel。由于 gimme_tree 是在 geqo_eval
 *   的私有内存上下文里运行,且 root->join_rel_hash 被临时置 NULL,这个
 *   joinrel 不会出现在 root->join_rel_list 的正式列表里(评估后被截断),
 *   因此其路径只含本函数生成的候选。joinrel 生成后,若非顶层关系,调用
 *   generate_partitionwise_join_paths / generate_useful_gather_paths /
 *   set_cheapest 完善路径选择(顶层关系则留到 grouping_planner 统一处理
 *   聚集路径);若存在分组关系(joinrel->grouped_rel)且非顶层,还会生成
 *   分组路径;
 * - 吸收与递归:旧团吸收新团(joinrel 更新、size 相加),new_clump 被 pfree,
 *   旧团先从列表移除,再以"扩大后的旧团"递归调用本函数——因为扩大后
 *   它可能又具备与其它团合并的资格,这一递归保证贪心扩张尽量彻底;
 * - 无法合并时:按"size 大的在前"的规则插入。size==1 的新团几乎总是放
 *   队尾(它是孤立关系,暂时没有任何团能合并它),这是最常用的快路径;
 *   否则线性扫描找第一个 size 更小的位置插入,维持列表全局降序。
 *
 * 【参数】
 *   root      —— PlannerInfo;
 *   clumps    —— 现有的团列表(按 size 降序);
 *   new_clump —— 待并入的团;
 *   num_gene  —— 关系个数(当前实现中未直接使用,保留为接口约定);
 *   force     —— true 时允许一切合法合并(含笛卡尔积),false 时只做理想连接。
 * 【返回值】处理后的团列表(可能返回新分配的列表)。
 */
static List *
merge_clump(PlannerInfo *root, List *clumps, Clump *new_clump, int num_gene,
			bool force)
{
	ListCell   *lc;
	int			pos;

	/* Look for a clump that new_clump can join to */
	foreach(lc, clumps)
	{
		Clump	   *old_clump = (Clump *) lfirst(lc);

		if (force ||
			desirable_join(root, old_clump->joinrel, new_clump->joinrel))
		{
			RelOptInfo *joinrel;

			/*
			 * Construct a RelOptInfo representing the join of these two input
			 * relations.  Note that we expect the joinrel not to exist in
			 * root->join_rel_list yet, and so the paths constructed for it
			 * will only include the ones we want.
			 */
			joinrel = make_join_rel(root,
									old_clump->joinrel,
									new_clump->joinrel);

			/* Keep searching if join order is not valid */
			if (joinrel)
			{
				bool		is_top_rel = bms_equal(joinrel->relids,
												   root->all_query_rels);

				/* Create paths for partitionwise joins. */
				generate_partitionwise_join_paths(root, joinrel);

				/*
				 * Except for the topmost scan/join rel, consider gathering
				 * partial paths.  We'll do the same for the topmost scan/join
				 * rel once we know the final targetlist (see
				 * grouping_planner).
				 */
				if (!is_top_rel)
					generate_useful_gather_paths(root, joinrel, false);

				/* Find and save the cheapest paths for this joinrel */
				set_cheapest(joinrel);

				/*
				 * Except for the topmost scan/join rel, consider generating
				 * partial aggregation paths for the grouped relation on top
				 * of the paths of this rel.  After that, we're done creating
				 * paths for the grouped relation, so run set_cheapest().
				 */
				if (joinrel->grouped_rel != NULL && !is_top_rel)
				{
					RelOptInfo *grouped_rel = joinrel->grouped_rel;

					Assert(IS_GROUPED_REL(grouped_rel));

					generate_grouped_paths(root, grouped_rel, joinrel);
					set_cheapest(grouped_rel);
				}

				/* Absorb new clump into old */
				old_clump->joinrel = joinrel;
				old_clump->size += new_clump->size;
				pfree(new_clump);

				/* Remove old_clump from list */
				clumps = foreach_delete_current(clumps, lc);

				/*
				 * Recursively try to merge the enlarged old_clump with
				 * others.  When no further merge is possible, we'll reinsert
				 * it into the list.
				 */
				return merge_clump(root, clumps, old_clump, num_gene, force);
			}
		}
	}

	/*
	 * No merging is possible, so add new_clump as an independent clump, in
	 * proper order according to size.  We can be fast for the common case
	 * where it has size 1 --- it should always go at the end.
	 */
	if (clumps == NIL || new_clump->size == 1)
		return lappend(clumps, new_clump);

	/* Else search for the place to insert it */
	for (pos = 0; pos < list_length(clumps); pos++)
	{
		Clump	   *old_clump = (Clump *) list_nth(clumps, pos);

		if (new_clump->size > old_clump->size)
			break;				/* new_clump belongs before old_clump */
	}
	clumps = list_insert_nth(clumps, pos, new_clump);

	return clumps;
}

/*
 * Heuristics for gimme_tree: do we want to join these two relations?
 */
/*
 * desirable_join - (中文)判断两个关系是否"应当"优先连接
 *
 * 【作用】作为 gimme_tree 的启发式过滤器:决定给定的两个关系集合当前是否
 * 值得立即连接。返回 true 时 merge_clump 会执行合并,false 则推迟。
 *
 * 【设计思想】连接启发式的判断依据只有两个:
 * 1. 两个关系之间存在可用的连接子句(have_relevant_joinclause):有共同
 *    列或连接条件,连接必然能产生有意义的结果,应当尽早做,避免产生大量
 *    无意义的笛卡尔积;
 * 2. 存在连接顺序限制(have_join_order_restriction):例如外连接或 LATERAL
 *    语义强制这两个关系必须被连接(顺序受约束),此时即便没有显式连接
 *    条件也必须先连。
 * 两者都满足其一即"理想连接"。其余情况(无连接条件、无顺序限制)返回
 * false,把连接推迟到强制合并阶段——这是"尽量推迟笛卡尔积"策略的体现:
 * 先保证有条件的连接全部完成,最后才用笛卡尔积把残余团拼起来。
 *
 * 【参数】
 *   root     —— PlannerInfo;
 *   outer_rel —— 外层关系;
 *   inner_rel —— 内层关系。
 * 【返回值】true 表示应当立即连接,false 表示推迟。
 */
static bool
desirable_join(PlannerInfo *root,
			   RelOptInfo *outer_rel, RelOptInfo *inner_rel)
{
	/*
	 * Join if there is an applicable join clause, or if there is a join order
	 * restriction forcing these rels to be joined.
	 */
	if (have_relevant_joinclause(root, outer_rel, inner_rel) ||
		have_join_order_restriction(root, outer_rel, inner_rel))
		return true;

	/* Otherwise postpone the join till later. */
	return false;
}
