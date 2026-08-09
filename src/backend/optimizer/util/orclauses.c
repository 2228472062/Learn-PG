/*-------------------------------------------------------------------------
 *
 * orclauses.c
 *	  Routines to extract restriction OR clauses from join OR clauses
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件实现"从连接 OR 条件中提取限制 OR 条件"的变换:把形如
 * (a.x = 42 AND b.y = 43) OR (a.x = 44 AND b.z = 45) 的连接条件,额外
 * 派生出只涉及单个基表、可在扫描阶段就过滤行的条件
 * (a.x = 42 OR a.x = 44) 与 (b.y = 43 OR b.z = 45),并挂到相应基表的
 * baserestrictinfo 上。
 *
 * 【设计思想】这是一次"部分的 CNF(合取范式)变换":不做完整的展开(那
 * 会使条件表达式过度膨胀),只抽出每个 OR 分支中"只涉及一个关系"的子句。
 * 被抽出的条件与原 OR 条件部分冗余,会导致 joinrel 大小被低估;为抵消这
 * 一偏差,还要反向修正原 OR 条件的缓存选择性(见 consider_new_or_clause),
 * 使连接规模的估算保持大致不变。
 *
 * 【主要函数关系】
 * extract_restriction_or_clauses 是唯一对外入口,遍历每个基表及其
 * joininfo 列表;is_safe_restriction_clause_for 判断某个子句是否可安全
 * 移到指定关系;extract_or_clause 递归地从 OR 树的每个分支中提取只涉及
 * 目标关系的子句;consider_new_or_clause 决定提取出的 OR 是否值得采用,
 * 并做选择性补偿。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/orclauses.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/optimizer.h"
#include "optimizer/orclauses.h"
#include "optimizer/paths.h"
#include "optimizer/restrictinfo.h"


static bool is_safe_restriction_clause_for(RestrictInfo *rinfo, RelOptInfo *rel);
static Expr *extract_or_clause(RestrictInfo *or_rinfo, RelOptInfo *rel);
static void consider_new_or_clause(PlannerInfo *root, RelOptInfo *rel,
								   Expr *orclause, RestrictInfo *join_or_rinfo);


/*
 * extract_restriction_or_clauses
 *	  Examine join OR-of-AND clauses to see if any useful restriction OR
 *	  clauses can be extracted.  If so, add them to the query.
 *
 * Although a join clause must reference multiple relations overall,
 * an OR of ANDs clause might contain sub-clauses that reference just one
 * relation and can be used to build a restriction clause for that rel.
 * For example consider
 *		WHERE ((a.x = 42 AND b.y = 43) OR (a.x = 44 AND b.z = 45));
 * We can transform this into
 *		WHERE ((a.x = 42 AND b.y = 43) OR (a.x = 44 AND b.z = 45))
 *			AND (a.x = 42 OR a.x = 44)
 *			AND (b.y = 43 OR b.z = 45);
 * which allows the latter clauses to be applied during the scans of a and b,
 * perhaps as index qualifications, and in any case reducing the number of
 * rows arriving at the join.  In essence this is a partial transformation to
 * CNF (AND of ORs format).  It is not complete, however, because we do not
 * unravel the original OR --- doing so would usually bloat the qualification
 * expression to little gain.
 *
 * The added quals are partially redundant with the original OR, and therefore
 * would cause the size of the joinrel to be underestimated when it is finally
 * formed.  (This would be true of a full transformation to CNF as well; the
 * fault is not really in the transformation, but in clauselist_selectivity's
 * inability to recognize redundant conditions.)  We can compensate for this
 * redundancy by changing the cached selectivity of the original OR clause,
 * canceling out the (valid) reduction in the estimated sizes of the base
 * relations so that the estimated joinrel size remains the same.  This is
 * a MAJOR HACK: it depends on the fact that clause selectivities are cached
 * and on the fact that the same RestrictInfo node will appear in every
 * joininfo list that might be used when the joinrel is formed.
 * And it doesn't work in cases where the size estimation is nonlinear
 * (i.e., outer and IN joins).  But it beats not doing anything.
 *
 * We examine each base relation to see if join clauses associated with it
 * contain extractable restriction conditions.  If so, add those conditions
 * to the rel's baserestrictinfo and update the cached selectivities of the
 * join clauses.  Note that the same join clause will be examined afresh
 * from the point of view of each baserel that participates in it, so its
 * cached selectivity may get updated multiple times.
 */
/*
 * extract_restriction_or_clauses - (中文)为各基表提取可用的限制 OR 条件
 *
 * 【作用】规划器阶段的入口函数(在 deconstruct_jointree 之后、基表路径
 * 生成之前被调用)。遍历每个基表,扫描其 joininfo 列表,凡是"OR 形式的
 * 连接条件"且可安全移动到该基表上的,尝试提取出只涉及该基表的 OR 限制
 * 条件并加入 baserestrictinfo;同时修正原连接条件的缓存选择性,以抵消
 * 冗余带来的估算偏差。
 *
 * 【设计思想】连接条件必须整体涉及多个关系,但其 OR-of-ANDs 结构中的
 * 某些子句可能只引用一个关系,可在扫描该表时作为过滤条件使用(甚至可做
 * 索引条件),从而减少到达连接节点的行数。核心难点在于补偿冗余:新加条件
 * 与原 OR 冗余,若直接让两者都参与估算,joinrel 行数会被低估。这里采用
 * 的"MAJOR HACK"是:利用 RestrictInfo 的选择性缓存,把原 OR 条件的
 * norm_selec 调整为"原估算 ÷ 新条件选择性",从而抵消基表行数下降带来的
 * 连锁效应。该手段依赖"同一 RestrictInfo 节点会出现在所有相关 joininfo
 * 列表"以及"选择性会被缓存"两个事实,且对非线性估算(外连接、IN 连接)
 * 并不完全有效——但聊胜于无。
 *
 * 遍历时跳过空槽位与非 RELOPT_BASEREL 的"other rel";可移动性判断复用
 * 参数化路径机制中的 join_clause_is_movable_to(虽然这里并非真的要生成
 * 参数化路径)。
 *
 * 【参数】root —— 规划上下文(PlannerInfo),内含 simple_rel_array。
 * 【返回值】无。
 */
void
extract_restriction_or_clauses(PlannerInfo *root)
{
	Index		rti;

	/* Examine each baserel for potential join OR clauses */
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *rel = root->simple_rel_array[rti];
		ListCell   *lc;

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (rel == NULL)
			continue;

		Assert(rel->relid == rti);	/* sanity check on array */

		/* ignore RTEs that are "other rels" */
		if (rel->reloptkind != RELOPT_BASEREL)
			continue;

		/*
		 * Find potentially interesting OR joinclauses.  We can use any
		 * joinclause that is considered safe to move to this rel by the
		 * parameterized-path machinery, even though what we are going to do
		 * with it is not exactly a parameterized path.
		 */
		foreach(lc, rel->joininfo)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			if (restriction_is_or_clause(rinfo) &&
				join_clause_is_movable_to(rinfo, rel))
			{
				/* Try to extract a qual for this rel only */
				Expr	   *orclause = extract_or_clause(rinfo, rel);

				/*
				 * If successful, decide whether we want to use the clause,
				 * and insert it into the rel's restrictinfo list if so.
				 */
				if (orclause)
					consider_new_or_clause(root, rel, orclause, rinfo);
			}
		}
	}
}

/*
 * Is the given primitive (non-OR) RestrictInfo safe to move to the rel?
 */
/*
 * is_safe_restriction_clause_for - (中文)判断给定的原子(非 OR)限制条件
 * 能否安全地移到指定关系上
 *
 * 【作用】被 extract_or_clause 递归调用,对 OR 树中的每个叶子 RestrictInfo
 * 做"能否当作该关系自身的限制条件"的检查。
 *
 * 【设计思想】三个判据依次过滤:
 * - pseudoconstant 的伪常量子句(与 rel 无任何关系)直接拒绝;
 * - 子句必须恰好只引用该关系(bms_equal(clause_relids, rel->relids)),
 *   这是"可提取为单表限制条件"的本质要求;
 * - 不能含有易变(volatile)函数,否则把它从 OR 中抽出并在扫描阶段额外
 *   求值,会改变求值次数、造成与语义不一致的副作用。
 *
 * 【参数】
 *   rinfo —— 待检查的原子 RestrictInfo;
 *   rel   —— 目标基表。
 * 【返回值】true:可安全移动到 rel;false:不可。
 */
static bool
is_safe_restriction_clause_for(RestrictInfo *rinfo, RelOptInfo *rel)
{
	/*
	 * We want clauses that mention the rel, and only the rel.  So in
	 * particular pseudoconstant clauses can be rejected quickly.  Then check
	 * the clause's Var membership.
	 */
	if (rinfo->pseudoconstant)
		return false;
	if (!bms_equal(rinfo->clause_relids, rel->relids))
		return false;

	/* We don't want extra evaluations of any volatile functions */
	if (contain_volatile_functions((Node *) rinfo->clause))
		return false;

	return true;
}

/*
 * Try to extract a restriction clause mentioning only "rel" from the given
 * join OR-clause.
 *
 * We must be able to extract at least one qual for this rel from each of
 * the arms of the OR, else we can't use it.
 *
 * Returns an OR clause (not a RestrictInfo!) pertaining to rel, or NULL
 * if no OR clause could be extracted.
 */
/*
 * extract_or_clause - (中文)尝试从给定的连接 OR 条件中提取只涉及指定
 * 关系的限制 OR 条件
 *
 * 【作用】被 extract_restriction_or_clauses 调用。对 or_rinfo 所代表的
 * OR-of-ANDs 条件,逐个分支(OR 的每个参数)提取"只涉及 rel"的子句。
 * 只有每个分支都能提取出至少一个子句时才成功,最终返回一个由这些子句
 * 拼成的 OR 表达式(注意:返回的是裸 Expr,不是 RestrictInfo!);否则返回
 * NULL。
 *
 * 【设计思想】递归结构是这里的关键:OR 的每个参数可能是 AND、普通条件或
 * 嵌套 OR。对 AND,遍历其各参数并逐个用 is_safe_restriction_clause_for
 * 过滤;对嵌套 OR 必须递归调用本函数(不仅是优化,而是必须下钻足够深,
 * 才能把整棵树中的 RestrictInfo 都剥离干净)。每处理完一个分支,若没提取
 * 到任何子句则整体失败;提取到多个子句时用 make_ands_explicit 合成 AND,
 * 若合成的子句本身又是 OR,则把它的参数直接并入结果列表,以保持"AND/OR
 * 扁平化"(不允许 OR 下面直接套 OR)。返回时同样剥去 RestrictInfo 外壳,
 * 因为限制条件与连接条件的缓存信息(选择性等)计算口径不同,不能复用原
 * 节点;之后接受该条件时会重新构造 RestrictInfo。
 *
 * 【参数】
 *   or_rinfo —— 候选的 OR 连接条件(RestrictInfo,其 orclause 字段是 OR);
 *   rel      —— 希望为其提取限制条件的目标基表。
 * 【返回值】成功时返回提取出的 OR 表达式(裸 Expr);失败返回 NULL。
 */
static Expr *
extract_or_clause(RestrictInfo *or_rinfo, RelOptInfo *rel)
{
	List	   *clauselist = NIL;
	ListCell   *lc;

	/*
	 * Scan each arm of the input OR clause.  Notice we descend into
	 * or_rinfo->orclause, which has RestrictInfo nodes embedded below the
	 * toplevel OR/AND structure.  This is useful because we can use the info
	 * in those nodes to make is_safe_restriction_clause_for()'s checks
	 * cheaper.  We'll strip those nodes from the returned tree, though,
	 * meaning that fresh ones will be built if the clause is accepted as a
	 * restriction clause.  This might seem wasteful --- couldn't we re-use
	 * the existing RestrictInfos?	But that'd require assuming that
	 * selectivity and other cached data is computed exactly the same way for
	 * a restriction clause as for a join clause, which seems undesirable.
	 */
	Assert(is_orclause(or_rinfo->orclause));
	foreach(lc, ((BoolExpr *) or_rinfo->orclause)->args)
	{
		Node	   *orarg = (Node *) lfirst(lc);
		List	   *subclauses = NIL;
		Node	   *subclause;

		/* OR arguments should be ANDs or sub-RestrictInfos */
		if (is_andclause(orarg))
		{
			List	   *andargs = ((BoolExpr *) orarg)->args;
			ListCell   *lc2;

			foreach(lc2, andargs)
			{
				RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc2);

				if (restriction_is_or_clause(rinfo))
				{
					/*
					 * Recurse to deal with nested OR.  Note we *must* recurse
					 * here, this isn't just overly-tense optimization: we
					 * have to descend far enough to find and strip all
					 * RestrictInfos in the expression.
					 */
					Expr	   *suborclause;

					suborclause = extract_or_clause(rinfo, rel);
					if (suborclause)
						subclauses = lappend(subclauses, suborclause);
				}
				else if (is_safe_restriction_clause_for(rinfo, rel))
					subclauses = lappend(subclauses, rinfo->clause);
			}
		}
		else
		{
			RestrictInfo *rinfo = castNode(RestrictInfo, orarg);

			Assert(!restriction_is_or_clause(rinfo));
			if (is_safe_restriction_clause_for(rinfo, rel))
				subclauses = lappend(subclauses, rinfo->clause);
		}

		/*
		 * If nothing could be extracted from this arm, we can't do anything
		 * with this OR clause.
		 */
		if (subclauses == NIL)
			return NULL;

		/*
		 * OK, add subclause(s) to the result OR.  If we found more than one,
		 * we need an AND node.  But if we found only one, and it is itself an
		 * OR node, add its subclauses to the result instead; this is needed
		 * to preserve AND/OR flatness (ie, no OR directly underneath OR).
		 */
		subclause = (Node *) make_ands_explicit(subclauses);
		if (is_orclause(subclause))
			clauselist = list_concat(clauselist,
									 ((BoolExpr *) subclause)->args);
		else
			clauselist = lappend(clauselist, subclause);
	}

	/*
	 * If we got a restriction clause from every arm, wrap them up in an OR
	 * node.  (In theory the OR node might be unnecessary, if there was only
	 * one arm --- but then the input OR node was also redundant.)
	 */
	if (clauselist != NIL)
		return make_orclause(clauselist);
	return NULL;
}

/*
 * Consider whether a successfully-extracted restriction OR clause is
 * actually worth using.  If so, add it to the planner's data structures,
 * and adjust the original join clause (join_or_rinfo) to compensate.
 */
/*
 * consider_new_or_clause - (中文)评估一个新提取的限制 OR 条件是否值得
 * 采用,并做选择性补偿
 *
 * 【作用】extract_or_clause 提取成功后才被调用:先把新 OR 条件构造成
 * RestrictInfo 并估算选择性;若选择性 <= 0.9(即能过滤掉相当比例的行)
 * 则把它挂到 rel->baserestrictinfo;随后反向修正原连接条件
 * join_or_rinfo 的缓存选择性,抵消冗余。
 *
 * 【设计思想】两条经验法则决定"是否值得":
 * - 选择性阈值 0.9:新条件若只滤掉 <10% 的行,收益远小于它带来的重复
 *   计算(连接时仍要检查原 OR),因此放弃;
 * - 补偿公式:把 join_or_rinfo->norm_selec 改成 orig_selec / or_selec
 *   (其中 orig_selec 是以 JOIN_INNER 语义、对去掉 rel 的剩余关系计算原
 *   条件的连接选择性)。这样 joinrel 的行数估算与未做变换前大致相同。
 *
 * 两个 "major hack" 必须在注释中讲明:(1) 依赖选择性被缓存在
 * RestrictInfo 上这一事实;(2) 只调整 norm_selec 而不动 outer_selec,
 * 因为外连接情况下本函数能到达这里意味着 rel 必在可空侧,连接规模对 rel
 * 大小是非线性的,强行修正 outer_selec 反而可能更错。补偿时还需现场构造
 * 一个 JOIN_INNER 语义的 dummy SpecialJoinInfo(与 costsize.c 的
 * approx_tuple_count 手法一致)来算 orig_selec。
 *
 * 【参数】
 *   root          —— 规划上下文;
 *   rel           —— 目标基表;
 *   orclause      —— 提取出的 OR 表达式(裸 Expr);
 *   join_or_rinfo —— 原始的连接 OR 条件(RestrictInfo),其缓存选择性会被修正。
 * 【返回值】无。
 */
static void
consider_new_or_clause(PlannerInfo *root, RelOptInfo *rel,
					   Expr *orclause, RestrictInfo *join_or_rinfo)
{
	RestrictInfo *or_rinfo;
	Selectivity or_selec,
				orig_selec;

	/*
	 * Build a RestrictInfo from the new OR clause.  We can assume it's valid
	 * as a base restriction clause.
	 */
	or_rinfo = make_restrictinfo(root,
								 orclause,
								 true,
								 false,
								 false,
								 false,
								 join_or_rinfo->security_level,
								 NULL,
								 NULL,
								 NULL);

	/*
	 * Estimate its selectivity.  (We could have done this earlier, but doing
	 * it on the RestrictInfo representation allows the result to get cached,
	 * saving work later.)
	 */
	or_selec = clause_selectivity(root, (Node *) or_rinfo,
								  0, JOIN_INNER, NULL);

	/*
	 * The clause is only worth adding to the query if it rejects a useful
	 * fraction of the base relation's rows; otherwise, it's just going to
	 * cause duplicate computation (since we will still have to check the
	 * original OR clause when the join is formed).  Somewhat arbitrarily, we
	 * set the selectivity threshold at 0.9.
	 */
	if (or_selec > 0.9)
		return;					/* forget it */

	/*
	 * OK, add it to the rel's restriction-clause list.
	 */
	rel->baserestrictinfo = lappend(rel->baserestrictinfo, or_rinfo);
	rel->baserestrict_min_security = Min(rel->baserestrict_min_security,
										 or_rinfo->security_level);

	/*
	 * Adjust the original join OR clause's cached selectivity to compensate
	 * for the selectivity of the added (but redundant) lower-level qual. This
	 * should result in the join rel getting approximately the same rows
	 * estimate as it would have gotten without all these shenanigans.
	 *
	 * XXX major hack alert: this depends on the assumption that the
	 * selectivity will stay cached.
	 *
	 * XXX another major hack: we adjust only norm_selec, the cached
	 * selectivity for JOIN_INNER semantics, even though the join clause
	 * might've been an outer-join clause.  This is partly because we can't
	 * easily identify the relevant SpecialJoinInfo here, and partly because
	 * the linearity assumption we're making would fail anyway.  (If it is an
	 * outer-join clause, "rel" must be on the nullable side, else we'd not
	 * have gotten here.  So the computation of the join size is going to be
	 * quite nonlinear with respect to the size of "rel", so it's not clear
	 * how we ought to adjust outer_selec even if we could compute its
	 * original value correctly.)
	 */
	if (or_selec > 0)
	{
		SpecialJoinInfo sjinfo;

		/*
		 * Make up a SpecialJoinInfo for JOIN_INNER semantics.  (Compare
		 * approx_tuple_count() in costsize.c.)
		 */
		init_dummy_sjinfo(&sjinfo,
						  bms_difference(join_or_rinfo->clause_relids,
										 rel->relids),
						  rel->relids);

		/* Compute inner-join size */
		orig_selec = clause_selectivity(root, (Node *) join_or_rinfo,
										0, JOIN_INNER, &sjinfo);

		/* And hack cached selectivity so join size remains the same */
		join_or_rinfo->norm_selec = orig_selec / or_selec;
		/* ensure result stays in sane range */
		if (join_or_rinfo->norm_selec > 1)
			join_or_rinfo->norm_selec = 1;
		/* as explained above, we don't touch outer_selec */
	}
}
