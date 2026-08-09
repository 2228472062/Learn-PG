/*-------------------------------------------------------------------------
 *
 * clausesel.c
 *	  Routines to compute clause selectivities
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本模块(clausesel.c)负责计算"子句选择率"(selectivity):即一个布尔表达
 * 式子句在某个关系上成立的元组比例(取值 0.0 ~ 1.0)。选择率是规划器估算
 * 中间结果大小的基础,直接影响连接顺序选择、路径代价估算与最终执行计划。
 *
 * 【职责】
 * - 对 AND/OR 组合的子句列表、以及单个任意布尔表达式估算选择率;
 * - 优先使用"扩展统计信息"(多列/表达式统计,见 statistics.c)以捕捉
 *   跨列依赖,其余子句再逐个用单列统计(直方图、MCV、唯一值数等)估算;
 * - 识别"区间查询"(range query)配对(如 x > 34 AND x < 42),利用区间
 *   几何关系得到比简单相乘更准确的联合选择率;
 * - 区分"限制子句"(restriction,只涉及单表)与"连接子句"(join,涉及
 *   多表),分别交给 oprrest 或 oprjoin 对应的估算器估算。
 *
 * 【设计思想】
 * - 顶层入口是 clauselist_selectivity / clause_selectivity,二者都是
 *   _ext 版本的薄封装(_ext 多一个 use_extended_stats 开关);
 * - 本模块本质上是"调度中心":决定某个子句该走哪个底层估算器
 *   (selfuncs.c 的 scalarltsel/eqsel/join_selectivity 或 statistics.c
 *   的 statext_clauselist_selectivity),并把结果缓存下来;
 * - 对 RestrictInfo 节点,估算结果缓存在 norm_selec / outer_selec 字段,
 *   避免同一子句被反复估算;
 * - 区间查询配对通过 RangeQueryClause 链表组织:同一变量上的 "<" 与 ">"
 *   子句成对后,用 hisel + losel - 1(+ NULL 修正)代替简单相乘。
 *
 * 【核心数据结构】RangeQueryClause:按"公共变量"归组的区间子句候选,
 * 记录低界/高界是否已找到及其各自的选择率。
 *
 * 本文件与 joininfo.c(连接子句收集)、equivclass.c(等价类)、selfuncs.c
 * (具体的选择性估算函数)以及 statistics.c(扩展统计)紧密配合。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/path/clausesel.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/plancat.h"
#include "statistics/statistics.h"
#include "utils/fmgroids.h"
#include "utils/lsyscache.h"
#include "utils/selfuncs.h"

/*
 * Data structure for accumulating info about possible range-query
 * clause pairs in clauselist_selectivity.
 */
typedef struct RangeQueryClause
{
	struct RangeQueryClause *next;	/* next in linked list */
	Node	   *var;			/* The common variable of the clauses */
	bool		have_lobound;	/* found a low-bound clause yet? */
	bool		have_hibound;	/* found a high-bound clause yet? */
	Selectivity lobound;		/* Selectivity of a var > something clause */
	Selectivity hibound;		/* Selectivity of a var < something clause */
} RangeQueryClause;

static void addRangeClause(RangeQueryClause **rqlist, Node *clause,
						   bool varonleft, bool isLTsel, Selectivity s2);
static RelOptInfo *find_single_rel_for_clauses(PlannerInfo *root,
											   List *clauses);
static Selectivity clauselist_selectivity_or(PlannerInfo *root,
											 List *clauses,
											 int varRelid,
											 JoinType jointype,
											 SpecialJoinInfo *sjinfo,
											 bool use_extended_stats);

/****************************************************************************
 *		ROUTINES TO COMPUTE SELECTIVITIES
 ****************************************************************************/

/*
 * clauselist_selectivity -
 *	  Compute the selectivity of an implicitly-ANDed list of boolean
 *	  expression clauses.  The list can be empty, in which case 1.0
 *	  must be returned.  List elements may be either RestrictInfos
 *	  or bare expression clauses --- the former is preferred since
 *	  it allows caching of results.
 *
 * See clause_selectivity() for the meaning of the additional parameters.
 *
 * The basic approach is to apply extended statistics first, on as many
 * clauses as possible, in order to capture cross-column dependencies etc.
 * The remaining clauses are then estimated by taking the product of their
 * selectivities, but that's only right if they have independent
 * probabilities, and in reality they are often NOT independent even if they
 * only refer to a single column.  So, we want to be smarter where we can.
 *
 * We also recognize "range queries", such as "x > 34 AND x < 42".  Clauses
 * are recognized as possible range query components if they are restriction
 * opclauses whose operators have scalarltsel or a related function as their
 * restriction selectivity estimator.  We pair up clauses of this form that
 * refer to the same variable.  An unpairable clause of this kind is simply
 * multiplied into the selectivity product in the normal way.  But when we
 * find a pair, we know that the selectivities represent the relative
 * positions of the low and high bounds within the column's range, so instead
 * of figuring the selectivity as hisel * losel, we can figure it as hisel +
 * losel - 1.  (To visualize this, see that hisel is the fraction of the range
 * below the high bound, while losel is the fraction above the low bound; so
 * hisel can be interpreted directly as a 0..1 value but we need to convert
 * losel to 1-losel before interpreting it as a value.  Then the available
 * range is 1-losel to hisel.  However, this calculation double-excludes
 * nulls, so really we need hisel + losel + null_frac - 1.)
 *
 * If either selectivity is exactly DEFAULT_INEQ_SEL, we forget this equation
 * and instead use DEFAULT_RANGE_INEQ_SEL.  The same applies if the equation
 * yields an impossible (negative) result.
 *
 * A free side-effect is that we can recognize redundant inequalities such
 * as "x < 4 AND x < 5"; only the tighter constraint will be counted.
 *
 * Of course this is all very dependent on the behavior of the inequality
 * selectivity functions; perhaps some day we can generalize the approach.
 */
/*
 * clauselist_selectivity - (中文)计算"隐式 AND 连接"的子句列表的整体选择率
 *
 * 【作用】对一组按 AND 隐含组合的布尔子句求总选择率,是规划器估算 WHERE
 * 条件结果集大小的顶层入口之一(如 restrictlist_selectivity 会调用它)。
 * 列表可以为空,此时返回 1.0。列表元素可以是 RestrictInfo 或裸表达式,
 * 优先传 RestrictInfo,因为可以利用其缓存字段。本函数只是
 * clauselist_selectivity_ext() 的薄封装,真实算法见后者。
 *
 * 【设计思想】把 use_extended_stats 固定为 true,即"尽可能使用扩展统计
 * 信息"。扩展统计优先的思想:跨列依赖无法由单列统计描述,因此凡能由扩展
 * 统计一次估出多个子句的,都交给 statext_clauselist_selectivity 处理。
 *
 * 【参数】
 *   root     —— PlannerInfo,规划全局上下文;
 *   clauses  —— 子句列表(隐式 AND);
 *   varRelid —— 非 0 时只把属于该关系的变量视为变量、其余视为常量(用于
 *               nestloop 内层扫描的限制条件估算);0 表示全部按变量处理;
 *   jointype —— 连接类型(对非连接子句传 JOIN_INNER);
 *   sjinfo   —— 连接上下文(SpecialJoinInfo);非连接子句传 NULL。
 * 【返回值】整个子句列表的联合选择率,取值 [0.0, 1.0]。
 */
Selectivity
clauselist_selectivity(PlannerInfo *root,
					   List *clauses,
					   int varRelid,
					   JoinType jointype,
					   SpecialJoinInfo *sjinfo)
{
	return clauselist_selectivity_ext(root, clauses, varRelid,
									  jointype, sjinfo, true);
}

/*
 * clauselist_selectivity_ext -
 *	  Extended version of clauselist_selectivity().  If "use_extended_stats"
 *	  is false, all extended statistics will be ignored, and only per-column
 *	  statistics will be used.
 */
/*
 * clauselist_selectivity_ext - (中文)计算隐式 AND 子句列表选择率的扩展版
 *
 * 【作用】clauselist_selectivity() 的实现本体。先尝试用扩展统计一次估出
 * 尽可能多的子句,剩下的子句再逐个按普通方式估算,并识别区间查询配对以
 * 提高精度。由 clauselist_selectivity() 以及 clause_selectivity_ext() 的
 * AND 分支调用。
 *
 * 【设计思想】整体分三步:
 * 1. 若全部子句只引用单一关系且该关系有扩展统计(statlist 非空),调用
 *    statext_clauselist_selectivity() 估算其中能处理的子句,并把已估子句
 *    的 0 基列表下标记录到 estimatedclauses(位图),后续跳过;
 * 2. 逐个处理剩余子句:伪常量(pseudoconstant)直接乘上 1.0/0.0;对形如
 *    "var op 常量" 的两目运算符子句,若其 oprrest 是标量不等比较估算器
 *    (<、<=、>、>=),则加入 rqlist 等待配对;其余按普通方式乘入 s1;
 * 3. 收尾扫描 rqlist:同一变量上一对"下界 + 上界"子句,选择率按
 *    hisel + losel - 1 计算(而非乘法),并补上对 NULL 双重排除的修正
 *    (+null_frac);若出现负值或命中默认值,回退到 DEFAULT_RANGE_INEQ_SEL。
 *    只找到单边时,按普通方式乘入。
 *
 * 【关键不变量】estimatedclauses 记录"已被扩展统计估过"的子句下标,避免
 * 重复估算;rqlist 中的配对判定用 equal() 比较完整表达式(变量可能是同一
 * 关系的多属性函数表达式)。
 *
 * 【参数】
 *   root              —— PlannerInfo;
 *   clauses           —— 子句列表(隐式 AND);
 *   varRelid          —— 同上(见 clauselist_selectivity);
 *   jointype          —— 连接类型;
 *   sjinfo            —— 连接上下文;
 *   use_extended_stats —— false 时完全忽略扩展统计,只使用单列统计。
 * 【返回值】联合选择率,取值 [0.0, 1.0]。
 */
Selectivity
clauselist_selectivity_ext(PlannerInfo *root,
						   List *clauses,
						   int varRelid,
						   JoinType jointype,
						   SpecialJoinInfo *sjinfo,
						   bool use_extended_stats)
{
	Selectivity s1 = 1.0;
	RelOptInfo *rel;
	Bitmapset  *estimatedclauses = NULL;
	RangeQueryClause *rqlist = NULL;
	ListCell   *l;
	int			listidx;

	/*
	 * If there's exactly one clause, just go directly to
	 * clause_selectivity_ext(). None of what we might do below is relevant.
	 */
	if (list_length(clauses) == 1)
		return clause_selectivity_ext(root, (Node *) linitial(clauses),
									  varRelid, jointype, sjinfo,
									  use_extended_stats);

	/*
	 * Determine if these clauses reference a single relation.  If so, and if
	 * it has extended statistics, try to apply those.
	 */
	rel = find_single_rel_for_clauses(root, clauses);
	if (use_extended_stats && rel && rel->rtekind == RTE_RELATION && rel->statlist != NIL)
	{
		/*
		 * Estimate as many clauses as possible using extended statistics.
		 *
		 * 'estimatedclauses' is populated with the 0-based list position
		 * index of clauses estimated here, and that should be ignored below.
		 */
		s1 = statext_clauselist_selectivity(root, clauses, varRelid,
											jointype, sjinfo, rel,
											&estimatedclauses, false);
	}

	/*
	 * Apply normal selectivity estimates for remaining clauses. We'll be
	 * careful to skip any clauses which were already estimated above.
	 *
	 * Anything that doesn't look like a potential rangequery clause gets
	 * multiplied into s1 and forgotten. Anything that does gets inserted into
	 * an rqlist entry.
	 */
	listidx = -1;
	foreach(l, clauses)
	{
		Node	   *clause = (Node *) lfirst(l);
		RestrictInfo *rinfo;
		Selectivity s2;

		listidx++;

		/*
		 * Skip this clause if it's already been estimated by some other
		 * statistics above.
		 */
		if (bms_is_member(listidx, estimatedclauses))
			continue;

		/* Compute the selectivity of this clause in isolation */
		s2 = clause_selectivity_ext(root, clause, varRelid, jointype, sjinfo,
									use_extended_stats);

		/*
		 * Check for being passed a RestrictInfo.
		 *
		 * If it's a pseudoconstant RestrictInfo, then s2 is either 1.0 or
		 * 0.0; just use that rather than looking for range pairs.
		 */
		if (IsA(clause, RestrictInfo))
		{
			rinfo = (RestrictInfo *) clause;
			if (rinfo->pseudoconstant)
			{
				s1 = s1 * s2;
				continue;
			}
			clause = (Node *) rinfo->clause;
		}
		else
			rinfo = NULL;

		/*
		 * See if it looks like a restriction clause with a pseudoconstant on
		 * one side.  (Anything more complicated than that might not behave in
		 * the simple way we are expecting.)  Most of the tests here can be
		 * done more efficiently with rinfo than without.
		 */
		if (is_opclause(clause) && list_length(((OpExpr *) clause)->args) == 2)
		{
			OpExpr	   *expr = (OpExpr *) clause;
			bool		varonleft = true;
			bool		ok;

			if (rinfo)
			{
				ok = (rinfo->num_base_rels == 1) &&
					(is_pseudo_constant_clause_relids(lsecond(expr->args),
													  rinfo->right_relids) ||
					 (varonleft = false,
					  is_pseudo_constant_clause_relids(linitial(expr->args),
													   rinfo->left_relids)));
			}
			else
			{
				ok = (NumRelids(root, clause) == 1) &&
					(is_pseudo_constant_clause(lsecond(expr->args)) ||
					 (varonleft = false,
					  is_pseudo_constant_clause(linitial(expr->args))));
			}

			if (ok)
			{
				/*
				 * If it's not a "<"/"<="/">"/">=" operator, just merge the
				 * selectivity in generically.  But if it's the right oprrest,
				 * add the clause to rqlist for later processing.
				 */
				switch (get_oprrest(expr->opno))
				{
					case F_SCALARLTSEL:
					case F_SCALARLESEL:
						addRangeClause(&rqlist, clause,
									   varonleft, true, s2);
						break;
					case F_SCALARGTSEL:
					case F_SCALARGESEL:
						addRangeClause(&rqlist, clause,
									   varonleft, false, s2);
						break;
					default:
						/* Just merge the selectivity in generically */
						s1 = s1 * s2;
						break;
				}
				continue;		/* drop to loop bottom */
			}
		}

		/* Not the right form, so treat it generically. */
		s1 = s1 * s2;
	}

	/*
	 * Now scan the rangequery pair list.
	 */
	while (rqlist != NULL)
	{
		RangeQueryClause *rqnext;

		if (rqlist->have_lobound && rqlist->have_hibound)
		{
			/* Successfully matched a pair of range clauses */
			Selectivity s2;

			/*
			 * Exact equality to the default value probably means the
			 * selectivity function punted.  This is not airtight but should
			 * be good enough.
			 */
			if (rqlist->hibound == DEFAULT_INEQ_SEL ||
				rqlist->lobound == DEFAULT_INEQ_SEL)
			{
				s2 = DEFAULT_RANGE_INEQ_SEL;
			}
			else
			{
				s2 = rqlist->hibound + rqlist->lobound - 1.0;

				/* Adjust for double-exclusion of NULLs */
				s2 += nulltestsel(root, IS_NULL, rqlist->var,
								  varRelid, jointype, sjinfo);

				/*
				 * A zero or slightly negative s2 should be converted into a
				 * small positive value; we probably are dealing with a very
				 * tight range and got a bogus result due to roundoff errors.
				 * However, if s2 is very negative, then we probably have
				 * default selectivity estimates on one or both sides of the
				 * range that we failed to recognize above for some reason.
				 */
				if (s2 <= 0.0)
				{
					if (s2 < -0.01)
					{
						/*
						 * No data available --- use a default estimate that
						 * is small, but not real small.
						 */
						s2 = DEFAULT_RANGE_INEQ_SEL;
					}
					else
					{
						/*
						 * It's just roundoff error; use a small positive
						 * value
						 */
						s2 = 1.0e-10;
					}
				}
			}
			/* Merge in the selectivity of the pair of clauses */
			s1 *= s2;
		}
		else
		{
			/* Only found one of a pair, merge it in generically */
			if (rqlist->have_lobound)
				s1 *= rqlist->lobound;
			else
				s1 *= rqlist->hibound;
		}
		/* release storage and advance */
		rqnext = rqlist->next;
		pfree(rqlist);
		rqlist = rqnext;
	}

	return s1;
}

/*
 * clauselist_selectivity_or -
 *	  Compute the selectivity of an implicitly-ORed list of boolean
 *	  expression clauses.  The list can be empty, in which case 0.0
 *	  must be returned.  List elements may be either RestrictInfos
 *	  or bare expression clauses --- the former is preferred since
 *	  it allows caching of results.
 *
 * See clause_selectivity() for the meaning of the additional parameters.
 *
 * The basic approach is to apply extended statistics first, on as many
 * clauses as possible, in order to capture cross-column dependencies etc.
 * The remaining clauses are then estimated as if they were independent.
 */
/*
 * clauselist_selectivity_or - (中文)计算"隐式 OR 连接"的子句列表的整体选择率
 *
 * 【作用】对一组按 OR 隐含组合的布尔子句求总选择率,是
 * clause_selectivity_ext() 遇到 OR 表达式时的处理入口。列表可以为空,此时
 * 返回 0.0。与 AND 版本不同,这里不识别区间配对,只按"独立性假设"合并。
 *
 * 【设计思想】OR 的并集概率按容斥公式 s1 = s1 + s2 - s1*s2 合并,以考虑
 * 两组选中元组可能重叠。同样先尝试用扩展统计(statext_clauselist_selectivity
 * 最后一个参数传 true)估出尽量多的子句,剩余子句再按上述公式逐个并入。
 * 源码注释中的 XXX 提示:这个估算可能过于保守(重叠部分被高估)。
 *
 * 【参数】
 *   root              —— PlannerInfo;
 *   clauses           —— 子句列表(隐式 OR);
 *   varRelid          —— 同上(见 clauselist_selectivity);
 *   jointype          —— 连接类型;
 *   sjinfo            —— 连接上下文;
 *   use_extended_stats —— false 时忽略扩展统计。
 * 【返回值】联合选择率,取值 [0.0, 1.0]。
 */
static Selectivity
clauselist_selectivity_or(PlannerInfo *root,
						  List *clauses,
						  int varRelid,
						  JoinType jointype,
						  SpecialJoinInfo *sjinfo,
						  bool use_extended_stats)
{
	Selectivity s1 = 0.0;
	RelOptInfo *rel;
	Bitmapset  *estimatedclauses = NULL;
	ListCell   *lc;
	int			listidx;

	/*
	 * Determine if these clauses reference a single relation.  If so, and if
	 * it has extended statistics, try to apply those.
	 */
	rel = find_single_rel_for_clauses(root, clauses);
	if (use_extended_stats && rel && rel->rtekind == RTE_RELATION && rel->statlist != NIL)
	{
		/*
		 * Estimate as many clauses as possible using extended statistics.
		 *
		 * 'estimatedclauses' is populated with the 0-based list position
		 * index of clauses estimated here, and that should be ignored below.
		 */
		s1 = statext_clauselist_selectivity(root, clauses, varRelid,
											jointype, sjinfo, rel,
											&estimatedclauses, true);
	}

	/*
	 * Estimate the remaining clauses as if they were independent.
	 *
	 * Selectivities for an OR clause are computed as s1+s2 - s1*s2 to account
	 * for the probable overlap of selected tuple sets.
	 *
	 * XXX is this too conservative?
	 */
	listidx = -1;
	foreach(lc, clauses)
	{
		Selectivity s2;

		listidx++;

		/*
		 * Skip this clause if it's already been estimated by some other
		 * statistics above.
		 */
		if (bms_is_member(listidx, estimatedclauses))
			continue;

		s2 = clause_selectivity_ext(root, (Node *) lfirst(lc), varRelid,
									jointype, sjinfo, use_extended_stats);

		s1 = s1 + s2 - s1 * s2;
	}

	return s1;
}

/*
 * addRangeClause --- add a new range clause for clauselist_selectivity
 *
 * Here is where we try to match up pairs of range-query clauses
 */
/*
 * addRangeClause - (中文)把一个区间子句加入范围查询配对链表
 *
 * 【作用】clauselist_selectivity_ext() 的辅助函数:把一条"var op 常量"
 * 的不等比较子句按其涉及变量归入 rqlist 中对应的 RangeQueryClause 项。
 * 若该变量尚未有分组,则新建一项;若该方向(低界/高界)已有子句,则保留
 * 约束更紧(选择率更小)的那一条。由 clauselist_selectivity_ext() 调用。
 *
 * 【设计思想】
 * - 先判定变量与界方向:varonleft 为 true 时变量在左操作数,`x < c` 是
 *   高界(hibound)、`x > c` 是低界(lobound);变量在右时方向相反
 *   (`c < x` 是低界,`c > x` 是高界);
 * - 用 equal() 完整比较变量表达式(可能是同一关系的多属性函数表达式),
 *   找到同组后按"更紧者胜出"更新:如 `x < 4 AND x < 5`,只保留 x<4;
 * - 找不到同组变量时,新建 RangeQueryClause 并头插到链表。
 *
 * 【参数】
 *   rqlist    —— 指向链表头指针的指针(可能被修改为指向新节点);
 *   clause    —— 待加入的不等比较子句(OpExpr);
 *   varonleft —— true 表示变量在运算符左侧;
 *   isLTsel   —— true 表示是 "<"/"<="(标量 LT 选择率),false 表示
 *                ">"/">=";
 *   s2        —— 该子句单独估算出的选择率。
 * 【返回值】无(副作用:修改 *rqlist 指向的链表)。
 */
static void
addRangeClause(RangeQueryClause **rqlist, Node *clause,
			   bool varonleft, bool isLTsel, Selectivity s2)
{
	RangeQueryClause *rqelem;
	Node	   *var;
	bool		is_lobound;

	if (varonleft)
	{
		var = get_leftop((Expr *) clause);
		is_lobound = !isLTsel;	/* x < something is high bound */
	}
	else
	{
		var = get_rightop((Expr *) clause);
		is_lobound = isLTsel;	/* something < x is low bound */
	}

	for (rqelem = *rqlist; rqelem; rqelem = rqelem->next)
	{
		/*
		 * We use full equal() here because the "var" might be a function of
		 * one or more attributes of the same relation...
		 */
		if (!equal(var, rqelem->var))
			continue;
		/* Found the right group to put this clause in */
		if (is_lobound)
		{
			if (!rqelem->have_lobound)
			{
				rqelem->have_lobound = true;
				rqelem->lobound = s2;
			}
			else
			{

				/*------
				 * We have found two similar clauses, such as
				 * x < y AND x <= z.
				 * Keep only the more restrictive one.
				 *------
				 */
				if (rqelem->lobound > s2)
					rqelem->lobound = s2;
			}
		}
		else
		{
			if (!rqelem->have_hibound)
			{
				rqelem->have_hibound = true;
				rqelem->hibound = s2;
			}
			else
			{

				/*------
				 * We have found two similar clauses, such as
				 * x > y AND x >= z.
				 * Keep only the more restrictive one.
				 *------
				 */
				if (rqelem->hibound > s2)
					rqelem->hibound = s2;
			}
		}
		return;
	}

	/* No matching var found, so make a new clause-pair data structure */
	rqelem = palloc_object(RangeQueryClause);
	rqelem->var = var;
	if (is_lobound)
	{
		rqelem->have_lobound = true;
		rqelem->have_hibound = false;
		rqelem->lobound = s2;
	}
	else
	{
		rqelem->have_lobound = false;
		rqelem->have_hibound = true;
		rqelem->hibound = s2;
	}
	rqelem->next = *rqlist;
	*rqlist = rqelem;
}

/*
 * find_single_rel_for_clauses
 *		Examine each clause in 'clauses' and determine if all clauses
 *		reference only a single relation.  If so return that relation,
 *		otherwise return NULL.
 */
/*
 * find_single_rel_for_clauses - (中文)判断一组子句是否只引用单一关系
 *
 * 【作用】检查 clauses 中所有子句是否都只涉及同一个关系;若是,返回该
 * 关系的 RelOptInfo,否则返回 NULL。clauselist_selectivity_ext() 用它判断
 * 是否可以尝试使用扩展统计(扩展统计只在单一关系上生效)。
 *
 * 【设计思想】逐条扫描子句,跟踪 lastrelid:
 * - 元素必须是 RestrictInfo(裸子句会被拒绝,因为扩展统计机制不会处理
 *   非 RestrictInfo 子句),例外是裸的 AND BoolExpr——规划器不会在 AND
 *   之上构建 RestrictInfo,因此递归展开其 args 再检查;
 * - 空 relids(不含变量的子句)可忽略;
 * - 若某子句涉及多个关系或与之前不同的关系,立即返回 NULL;
 * - 全部通过后,用最后一个 relid 取基表 RelOptInfo 返回;一个子句都没有
 *   时返回 NULL。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   clauses —— 待检查的子句列表(元素通常为 RestrictInfo)。
 * 【返回值】单一关系对应的 RelOptInfo;若不存在(引用多表、非 RestrictInfo、
 * 或列表为空)则返回 NULL。
 */
static RelOptInfo *
find_single_rel_for_clauses(PlannerInfo *root, List *clauses)
{
	int			lastrelid = 0;
	ListCell   *l;

	foreach(l, clauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(l);
		int			relid;

		/*
		 * If we have a list of bare clauses rather than RestrictInfos, we
		 * could pull out their relids the hard way with pull_varnos().
		 * However, currently the extended-stats machinery won't do anything
		 * with non-RestrictInfo clauses anyway, so there's no point in
		 * spending extra cycles; just fail if that's what we have.
		 *
		 * An exception to that rule is if we have a bare BoolExpr AND clause.
		 * We treat this as a special case because the restrictinfo machinery
		 * doesn't build RestrictInfos on top of AND clauses.
		 */
		if (is_andclause(rinfo))
		{
			RelOptInfo *rel;

			rel = find_single_rel_for_clauses(root,
											  ((BoolExpr *) rinfo)->args);

			if (rel == NULL)
				return NULL;
			if (lastrelid == 0)
				lastrelid = rel->relid;
			else if (rel->relid != lastrelid)
				return NULL;

			continue;
		}

		if (!IsA(rinfo, RestrictInfo))
			return NULL;

		if (bms_is_empty(rinfo->clause_relids))
			continue;			/* we can ignore variable-free clauses */
		if (!bms_get_singleton_member(rinfo->clause_relids, &relid))
			return NULL;		/* multiple relations in this clause */
		if (lastrelid == 0)
			lastrelid = relid;	/* first clause referencing a relation */
		else if (relid != lastrelid)
			return NULL;		/* relation not same as last one */
	}

	if (lastrelid != 0)
		return find_base_rel(root, lastrelid);

	return NULL;				/* no clauses */
}

/*
 * treat_as_join_clause -
 *	  Decide whether an operator clause is to be handled by the
 *	  restriction or join estimator.  Subroutine for clause_selectivity().
 */
/*
 * treat_as_join_clause - (中文)判断一个运算符子句应交给连接估算器还是限制估算器
 *
 * 【作用】clause_selectivity_ext() 的辅助函数:决定一个 OpExpr(或
 * DistinctExpr、函数等)应该用连接选择率估算器(oprjoin)还是限制选择率
 * 估算器(oprrest)来估算。
 *
 * 【设计思想】三种情况直接判定:
 * - varRelid != 0:调用者强制按限制模式处理(如正在估算 nestloop 内层
 *   索引扫描的 qual),返回 false;
 * - sjinfo == NULL:该子句在扫描节点上求值,必然只涉及单表,是限制子句;
 * - 其余情况:只要涉及的基表数 > 1 就算连接子句。有了 rinfo 可用
 *   rinfo->num_base_rels 快速判断(它只统计基表,不统计外层连接,目的
 *   是把因外层连接而延迟的单表子句导向限制估算器,避免错误地当作连接
 *   子句去处理)。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   clause  —— 被判断的子句表达式;
 *   rinfo   —— 若该子句包装在 RestrictInfo 中则为对应节点,否则 NULL;
 *   varRelid —— 非 0 表示调用者强制限制模式(内层索引扫描);
 *   sjinfo  —— 连接上下文;NULL 表示该子句在扫描节点求值。
 * 【返回值】true:应作为连接子句估算;false:应作为限制子句估算。
 */
static inline bool
treat_as_join_clause(PlannerInfo *root, Node *clause, RestrictInfo *rinfo,
					 int varRelid, SpecialJoinInfo *sjinfo)
{
	if (varRelid != 0)
	{
		/*
		 * Caller is forcing restriction mode (eg, because we are examining an
		 * inner indexscan qual).
		 */
		return false;
	}
	else if (sjinfo == NULL)
	{
		/*
		 * It must be a restriction clause, since it's being evaluated at a
		 * scan node.
		 */
		return false;
	}
	else
	{
		/*
		 * Otherwise, it's a join if there's more than one base relation used.
		 * We can optimize this calculation if an rinfo was passed.
		 *
		 * XXX	Since we know the clause is being evaluated at a join, the
		 * only way it could be single-relation is if it was delayed by outer
		 * joins.  We intentionally count only baserels here, not OJs that
		 * might be present in rinfo->clause_relids, so that we direct such
		 * cases to the restriction qual estimators not join estimators.
		 * Eventually some notice should be taken of the possibility of
		 * injected nulls, but we'll likely want to do that in the restriction
		 * estimators rather than starting to treat such cases as join quals.
		 */
		if (rinfo)
			return (rinfo->num_base_rels > 1);
		else
			return (NumRelids(root, clause) > 1);
	}
}


/*
 * clause_selectivity -
 *	  Compute the selectivity of a general boolean expression clause.
 *
 * The clause can be either a RestrictInfo or a plain expression.  If it's
 * a RestrictInfo, we try to cache the selectivity for possible re-use,
 * so passing RestrictInfos is preferred.
 *
 * varRelid is either 0 or a rangetable index.
 *
 * When varRelid is not 0, only variables belonging to that relation are
 * considered in computing selectivity; other vars are treated as constants
 * of unknown values.  This is appropriate for estimating the selectivity of
 * a join clause that is being used as a restriction clause in a scan of a
 * nestloop join's inner relation --- varRelid should then be the ID of the
 * inner relation.
 *
 * When varRelid is 0, all variables are treated as variables.  This
 * is appropriate for ordinary join clauses and restriction clauses.
 *
 * jointype is the join type, if the clause is a join clause.  Pass JOIN_INNER
 * if the clause isn't a join clause.
 *
 * sjinfo is NULL for a non-join clause, otherwise it provides additional
 * context information about the join being performed.  There are some
 * special cases:
 *	1. For a special (not INNER) join, sjinfo is always a member of
 *	   root->join_info_list.
 *	2. For an INNER join, sjinfo is just a transient struct, and only the
 *	   relids and jointype fields in it can be trusted.
 * It is possible for jointype to be different from sjinfo->jointype.
 * This indicates we are considering a variant join: either with
 * the LHS and RHS switched, or with one input unique-ified.
 *
 * Note: when passing nonzero varRelid, it's normally appropriate to set
 * jointype == JOIN_INNER, sjinfo == NULL, even if the clause is really a
 * join clause; because we aren't treating it as a join clause.
 */
/*
 * clause_selectivity - (中文)计算单个通用布尔表达式子句的选择率
 *
 * 【作用】对任意布尔表达式子句估算选择率,是选择率计算的通用入口,由
 * 多处估算代码(如 clauselist_selectivity_ext、restrictlist 相关代码)调用。
 * 子句可以是 RestrictInfo 或裸表达式——传 RestrictInfo 时结果可被缓存。
 *
 * 【设计思想】本函数是 clause_selectivity_ext() 的封装(use_extended_stats
 * 固定为 true)。估算按子句节点类型分派:Var(布尔变量)、Const、Param、
 * NOT/AND/OR、OpExpr/DistinctExpr、函数、ScalarArrayOpExpr、
 * RowCompareExpr、NullTest、BooleanTest、CurrentOfExpr、RelabelType、
 * CoerceToDomain 等,各自交给对应的估算器;无法识别的类型最后用
 * boolvarsel() 兜底(要求是不可变且只引用单表的表达式,否则返回默认值)。
 *
 * 【参数】
 *   root    —— PlannerInfo;
 *   clause  —— 待估算的子句(RestrictInfo 或裸表达式);
 *   varRelid —— 0 表示全按变量处理;非 0 表示只把该关系变量当变量
 *               (用于内层索引扫描估算);
 *   jointype —— 连接类型;非连接子句传 JOIN_INNER;
 *   sjinfo  —— 连接上下文;非连接子句传 NULL。
 * 【返回值】该子句的选择率 [0.0, 1.0];无法识别时返回默认值 0.5。
 */
Selectivity
clause_selectivity(PlannerInfo *root,
				   Node *clause,
				   int varRelid,
				   JoinType jointype,
				   SpecialJoinInfo *sjinfo)
{
	return clause_selectivity_ext(root, clause, varRelid,
								  jointype, sjinfo, true);
}

/*
 * clause_selectivity_ext -
 *	  Extended version of clause_selectivity().  If "use_extended_stats" is
 *	  false, all extended statistics will be ignored, and only per-column
 *	  statistics will be used.
 */
/*
 * clause_selectivity_ext - (中文)单子句选择率估算的扩展版实现
 *
 * 【作用】clause_selectivity() 的实现本体。按子句节点类型分派到各专用
 * 估算器,并处理 RestrictInfo 的解包与结果缓存。由 clause_selectivity()
 * 以及 clauselist_selectivity_ext()(逐条估算单个子句时)调用。
 *
 * 【设计思想】
 * - 解包 RestrictInfo:伪常量(pseudoconstant)只作门控,不影响行数估计,
 *   恒为 true 返回 1.0(常量 false 除外,返回 0.0 直接淘汰);
 * - 缓存:当 varRelid 为 0,或子句只含该关系的变量时,结果可缓存。INNER
 *   连接结果存 rinfo->norm_selec,其它连接类型存 rinfo->outer_selec
 *   (外层连接子句可能以真实 jointype 或 JOIN_INNER 两种方式被检查,故需
 *   两个缓存槽)。若子句是 OR 表达式,则展开 rinfo->orclause 以便逐个子句
 *   缓存;
 * - 分派:按节点类型一一处理。OpExpr/DistinctExpr 用 treat_as_join_clause()
 *   决定走 join_selectivity 还是 restriction_selectivity;DistinctExpr(等
 *   价于 "<>")结果是原估算的补集 1-s1;函数若有支持函数用
 *   function_selectivity,否则回退 boolvarsel;ScalarArrayOpExpr、
 *   RowCompareExpr、NullTest、BooleanTest、CurrentOfExpr(CURRENT OF 至多
 *   选一行)等各有专用估算器;最后兜底 boolvarsel。
 *
 * 【参数】
 *   root              —— PlannerInfo;
 *   clause            —— 待估算子句;
 *   varRelid          —— 同上(见 clause_selectivity);
 *   jointype          —— 连接类型;
 *   sjinfo            —— 连接上下文;
 *   use_extended_stats —— false 时忽略扩展统计(影响 AND/OR 子句的递归估算)。
 * 【返回值】子句选择率 [0.0, 1.0];默认 0.5。
 */
Selectivity
clause_selectivity_ext(PlannerInfo *root,
					   Node *clause,
					   int varRelid,
					   JoinType jointype,
					   SpecialJoinInfo *sjinfo,
					   bool use_extended_stats)
{
	Selectivity s1 = 0.5;		/* default for any unhandled clause type */
	RestrictInfo *rinfo = NULL;
	bool		cacheable = false;

	if (clause == NULL)			/* can this still happen? */
		return s1;

	if (IsA(clause, RestrictInfo))
	{
		rinfo = (RestrictInfo *) clause;

		/*
		 * If the clause is marked pseudoconstant, then it will be used as a
		 * gating qual and should not affect selectivity estimates; hence
		 * return 1.0.  The only exception is that a constant FALSE may be
		 * taken as having selectivity 0.0, since it will surely mean no rows
		 * out of the plan.  This case is simple enough that we need not
		 * bother caching the result.
		 */
		if (rinfo->pseudoconstant)
		{
			if (!IsA(rinfo->clause, Const))
				return (Selectivity) 1.0;
		}

		/*
		 * If possible, cache the result of the selectivity calculation for
		 * the clause.  We can cache if varRelid is zero or the clause
		 * contains only vars of that relid --- otherwise varRelid will affect
		 * the result, so mustn't cache.  Outer join quals might be examined
		 * with either their join's actual jointype or JOIN_INNER, so we need
		 * two cache variables to remember both cases.  Note: we assume the
		 * result won't change if we are switching the input relations or
		 * considering a unique-ified case, so we only need one cache variable
		 * for all non-JOIN_INNER cases.
		 */
		if (varRelid == 0 ||
			rinfo->num_base_rels == 0 ||
			(rinfo->num_base_rels == 1 &&
			 bms_is_member(varRelid, rinfo->clause_relids)))
		{
			/* Cacheable --- do we already have the result? */
			if (jointype == JOIN_INNER)
			{
				if (rinfo->norm_selec >= 0)
					return rinfo->norm_selec;
			}
			else
			{
				if (rinfo->outer_selec >= 0)
					return rinfo->outer_selec;
			}
			cacheable = true;
		}

		/*
		 * Proceed with examination of contained clause.  If the clause is an
		 * OR-clause, we want to look at the variant with sub-RestrictInfos,
		 * so that per-subclause selectivities can be cached.
		 */
		if (rinfo->orclause)
			clause = (Node *) rinfo->orclause;
		else
			clause = (Node *) rinfo->clause;
	}

	if (IsA(clause, Var))
	{
		Var		   *var = (Var *) clause;

		/*
		 * We probably shouldn't ever see an uplevel Var here, but if we do,
		 * return the default selectivity...
		 */
		if (var->varlevelsup == 0 &&
			(varRelid == 0 || varRelid == (int) var->varno))
		{
			/* Use the restriction selectivity function for a bool Var */
			s1 = boolvarsel(root, (Node *) var, varRelid);
		}
	}
	else if (IsA(clause, Const))
	{
		/* bool constant is pretty easy... */
		Const	   *con = (Const *) clause;

		s1 = con->constisnull ? 0.0 :
			DatumGetBool(con->constvalue) ? 1.0 : 0.0;
	}
	else if (IsA(clause, Param))
	{
		/* see if we can replace the Param */
		Node	   *subst = estimate_expression_value(root, clause);

		if (IsA(subst, Const))
		{
			/* bool constant is pretty easy... */
			Const	   *con = (Const *) subst;

			s1 = con->constisnull ? 0.0 :
				DatumGetBool(con->constvalue) ? 1.0 : 0.0;
		}
		else
		{
			/* XXX any way to do better than default? */
		}
	}
	else if (is_notclause(clause))
	{
		/* inverse of the selectivity of the underlying clause */
		s1 = 1.0 - clause_selectivity_ext(root,
										  (Node *) get_notclausearg((Expr *) clause),
										  varRelid,
										  jointype,
										  sjinfo,
										  use_extended_stats);
	}
	else if (is_andclause(clause))
	{
		/* share code with clauselist_selectivity() */
		s1 = clauselist_selectivity_ext(root,
										((BoolExpr *) clause)->args,
										varRelid,
										jointype,
										sjinfo,
										use_extended_stats);
	}
	else if (is_orclause(clause))
	{
		/*
		 * Almost the same thing as clauselist_selectivity, but with the
		 * clauses connected by OR.
		 */
		s1 = clauselist_selectivity_or(root,
									   ((BoolExpr *) clause)->args,
									   varRelid,
									   jointype,
									   sjinfo,
									   use_extended_stats);
	}
	else if (is_opclause(clause) || IsA(clause, DistinctExpr))
	{
		OpExpr	   *opclause = (OpExpr *) clause;
		Oid			opno = opclause->opno;

		if (treat_as_join_clause(root, clause, rinfo, varRelid, sjinfo))
		{
			/* Estimate selectivity for a join clause. */
			s1 = join_selectivity(root, opno,
								  opclause->args,
								  opclause->inputcollid,
								  jointype,
								  sjinfo);
		}
		else
		{
			/* Estimate selectivity for a restriction clause. */
			s1 = restriction_selectivity(root, opno,
										 opclause->args,
										 opclause->inputcollid,
										 varRelid);
		}

		/*
		 * DistinctExpr has the same representation as OpExpr, but the
		 * contained operator is "=" not "<>", so we must negate the result.
		 * This estimation method doesn't give the right behavior for nulls,
		 * but it's better than doing nothing.
		 */
		if (IsA(clause, DistinctExpr))
			s1 = 1.0 - s1;
	}
	else if (is_funcclause(clause))
	{
		FuncExpr   *funcclause = (FuncExpr *) clause;

		/* Try to get an estimate from the support function, if any */
		s1 = function_selectivity(root,
								  funcclause->funcid,
								  funcclause->args,
								  funcclause->inputcollid,
								  treat_as_join_clause(root, clause, rinfo,
													   varRelid, sjinfo),
								  varRelid,
								  jointype,
								  sjinfo);

		/* If no support, fall back on boolvarsel */
		if (s1 < 0)
			s1 = boolvarsel(root, clause, varRelid);
	}
	else if (IsA(clause, ScalarArrayOpExpr))
	{
		/* Use node specific selectivity calculation function */
		s1 = scalararraysel(root,
							(ScalarArrayOpExpr *) clause,
							treat_as_join_clause(root, clause, rinfo,
												 varRelid, sjinfo),
							varRelid,
							jointype,
							sjinfo);
	}
	else if (IsA(clause, RowCompareExpr))
	{
		/* Use node specific selectivity calculation function */
		s1 = rowcomparesel(root,
						   (RowCompareExpr *) clause,
						   varRelid,
						   jointype,
						   sjinfo);
	}
	else if (IsA(clause, NullTest))
	{
		/* Use node specific selectivity calculation function */
		s1 = nulltestsel(root,
						 ((NullTest *) clause)->nulltesttype,
						 (Node *) ((NullTest *) clause)->arg,
						 varRelid,
						 jointype,
						 sjinfo);
	}
	else if (IsA(clause, BooleanTest))
	{
		/* Use node specific selectivity calculation function */
		s1 = booltestsel(root,
						 ((BooleanTest *) clause)->booltesttype,
						 (Node *) ((BooleanTest *) clause)->arg,
						 varRelid,
						 jointype,
						 sjinfo);
	}
	else if (IsA(clause, CurrentOfExpr))
	{
		/* CURRENT OF selects at most one row of its table */
		CurrentOfExpr *cexpr = (CurrentOfExpr *) clause;
		RelOptInfo *crel = find_base_rel(root, cexpr->cvarno);

		if (crel->tuples > 0)
			s1 = 1.0 / crel->tuples;
	}
	else if (IsA(clause, RelabelType))
	{
		/* Not sure this case is needed, but it can't hurt */
		s1 = clause_selectivity_ext(root,
									(Node *) ((RelabelType *) clause)->arg,
									varRelid,
									jointype,
									sjinfo,
									use_extended_stats);
	}
	else if (IsA(clause, CoerceToDomain))
	{
		/* Not sure this case is needed, but it can't hurt */
		s1 = clause_selectivity_ext(root,
									(Node *) ((CoerceToDomain *) clause)->arg,
									varRelid,
									jointype,
									sjinfo,
									use_extended_stats);
	}
	else
	{
		/*
		 * For anything else, see if we can consider it as a boolean variable.
		 * This only works if it's an immutable expression in Vars of a single
		 * relation; but there's no point in us checking that here because
		 * boolvarsel() will do it internally, and return a suitable default
		 * selectivity if not.
		 */
		s1 = boolvarsel(root, clause, varRelid);
	}

	/* Cache the result if possible */
	if (cacheable)
	{
		if (jointype == JOIN_INNER)
			rinfo->norm_selec = s1;
		else
			rinfo->outer_selec = s1;
	}

#ifdef SELECTIVITY_DEBUG
	elog(DEBUG4, "clause_selectivity: s1 %f", s1);
#endif							/* SELECTIVITY_DEBUG */

	return s1;
}
