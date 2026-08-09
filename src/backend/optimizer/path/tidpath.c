/*-------------------------------------------------------------------------
 *
 * tidpath.c
 *	  Routines to determine which TID conditions are usable for scanning
 *	  a given relation, and create TidPaths and TidRangePaths accordingly.
 *
 * For TidPaths, we look for WHERE conditions of the form
 * "CTID = pseudoconstant", which can be implemented by just fetching
 * the tuple directly via heap_fetch().  We can also handle OR'd conditions
 * such as (CTID = const1) OR (CTID = const2), as well as ScalarArrayOpExpr
 * conditions of the form CTID = ANY(pseudoconstant_array).  In particular
 * this allows
 *		WHERE ctid IN (tid1, tid2, ...)
 *
 * As with indexscans, our definition of "pseudoconstant" is pretty liberal:
 * we allow anything that doesn't involve a volatile function or a Var of
 * the relation under consideration.  Vars belonging to other relations of
 * the query are allowed, giving rise to parameterized TID scans.
 *
 * We also support "WHERE CURRENT OF cursor" conditions (CurrentOfExpr),
 * which amount to "CTID = run-time-determined-TID".  These could in
 * theory be translated to a simple comparison of CTID to the result of
 * a function, but in practice it works better to keep the special node
 * representation all the way through to execution.
 *
 * Additionally, TidRangePaths may be created for conditions of the form
 * "CTID relop pseudoconstant", where relop is one of >,>=,<,<=, and
 * AND-clauses composed of such conditions.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件负责为基表识别可用的 TID 条件,并据此生成 TidPath(直接按元组
 * 标识符取行的路径)与 TidRangePath(TID 范围扫描路径)。TID 是物理定位
 * 符,命中时能以最少的页访问直达目标元组,是特定场景下的高效路径。
 *
 * 【设计思想】识别三类可用条件:
 * - 等值类:TidPath 支持 CTID = 伪常量、CTID = ANY(伪常量数组)、多个
 *   等值条件的 OR 组合,以及 CurrentOfExpr("WHERE CURRENT OF 游标",
 *   运行时才知 TID,保持专有节点到执行期);
 * - 范围类:TidRangePath 支持 CTID <op> 伪常量(op 为 >、>=、<、<=)及
 *   这类条件的 AND 组合;
 * - 参数化:TID 等值条件可引用查询中其他关系的 Var(只要不含易变函数),
 *   从而生成带 required_outer 的参数化 TidPath。
 * "伪常量"的定义与索引扫描一致:不含易变函数、不含本关系 Var。
 *
 * 【主要函数关系】
 * 判定层:IsCTIDVar(是否为 CTID Var)、IsBinaryTidClause(二元 TID 子句
 * 基类)、IsTidEqualClause / IsTidRangeClause / IsTidEqualAnyClause /
 * IsCurrentOfClause、RestrictInfoIsTidQual(综合判定);提取层:
 * TidQualFromRestrictInfoList / TidRangeQualFromRestrictInfoList(从条件
 * 列表递归提取);路径生成:create_tidscan_paths 是唯一对外入口,内部经
 * BuildParameterizedTidPaths 生成参数化路径(含基于等价类 EC 的隐含等值
 * 条件,回调 ec_member_matches_ctid)。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/path/tidpath.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/sysattr.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/restrictinfo.h"


/*
 * Does this Var represent the CTID column of the specified baserel?
 */
/*
 * IsCTIDVar - (中文)判断该 Var 是否是指定基表的 CTID 列
 *
 * 【作用】判定层的基础谓词:检查 var 是否表示 rel 的 ctid 系统列。被
 * IsBinaryTidClause / IsTidEqualAnyClause / ec_member_matches_ctid 复用。
 *
 * 【设计思想】要求 varattno 为 SelfItemPointerAttributeNumber(-1,即 ctid
 * 系统列)、类型为 TIDOID、varno 等于 rel->relid、未被任何外连接置空
 * (varnullingrels 为空)、层级为 0(本层)。类型检查只是保险(vartype 是
 * 严格的,防止来自其他来源的同名系统列)。
 *
 * 【参数】
 *   var —— 待检查的 Var;
 *   rel —— 目标基表。
 * 【返回值】true:var 是 rel 的 CTID Var;false:不是。
 */
static inline bool
IsCTIDVar(Var *var, RelOptInfo *rel)
{
	/* The vartype check is strictly paranoia */
	if (var->varattno == SelfItemPointerAttributeNumber &&
		var->vartype == TIDOID &&
		var->varno == rel->relid &&
		var->varnullingrels == NULL &&
		var->varlevelsup == 0)
		return true;
	return false;
}

/*
 * Check to see if a RestrictInfo is of the form
 *		CTID OP pseudoconstant
 * or
 *		pseudoconstant OP CTID
 * where OP is a binary operation, the CTID Var belongs to relation "rel",
 * and nothing on the other side of the clause does.
 */
/*
 * IsBinaryTidClause - (中文)判断 RestrictInfo 是否为"CTID OP 伪常量"形式
 * 的二元子句
 *
 * 【作用】识别 CTID 位于二元操作符任一侧、另一侧不引用 rel 的伪常量、
 * 且整个子句不含易变函数的 OpExpr。是等值与范围两类 TID 子句的共同
 * 基类判定。
 *
 * 【设计思想】先确认是二元 OpExpr;再在左右参数中找 CTID(任一位置均可,
 * 后续实际算子判断交由上层决定),记录"另一侧"及其 relids;最后要求
 * 另一侧不含 rel 的 relid 且不含易变函数——这正是"伪常量"的定义。返回
 * true 只保证形式合格,算子是否为 = 或范围操作符由上层分别判定。
 *
 * 【参数】
 *   rinfo —— 待判定的连接/限制条件;
 *   rel   —— 目标基表。
 * 【返回值】true:形式为 CTID OP 伪常量;false:不是。
 */
static bool
IsBinaryTidClause(RestrictInfo *rinfo, RelOptInfo *rel)
{
	OpExpr	   *node;
	Node	   *arg1,
			   *arg2,
			   *other;
	Relids		other_relids;

	/* Must be an OpExpr */
	if (!is_opclause(rinfo->clause))
		return false;
	node = (OpExpr *) rinfo->clause;

	/* OpExpr must have two arguments */
	if (list_length(node->args) != 2)
		return false;
	arg1 = linitial(node->args);
	arg2 = lsecond(node->args);

	/* Look for CTID as either argument */
	other = NULL;
	other_relids = NULL;
	if (arg1 && IsA(arg1, Var) &&
		IsCTIDVar((Var *) arg1, rel))
	{
		other = arg2;
		other_relids = rinfo->right_relids;
	}
	if (!other && arg2 && IsA(arg2, Var) &&
		IsCTIDVar((Var *) arg2, rel))
	{
		other = arg1;
		other_relids = rinfo->left_relids;
	}
	if (!other)
		return false;

	/* The other argument must be a pseudoconstant */
	if (bms_is_member(rel->relid, other_relids) ||
		contain_volatile_functions(other))
		return false;

	return true;				/* success */
}

/*
 * Check to see if a RestrictInfo is of the form
 *		CTID = pseudoconstant
 * or
 *		pseudoconstant = CTID
 * where the CTID Var belongs to relation "rel", and nothing on the
 * other side of the clause does.
 */
/*
 * IsTidEqualClause - (中文)判断是否"CTID = 伪常量"形式的 TID 等值子句
 *
 * 【作用】在 IsBinaryTidClause 成立的基础上,进一步要求操作符是
 * TIDEqualOperator(tideq),即精确匹配单一 TID。
 *
 * 【设计思想】直接复用二元基类判定再查算子 OID,保持两个判定的职责单一
 * 清晰。
 *
 * 【参数】
 *   rinfo —— 待判定条件;
 *   rel   —— 目标基表。
 * 【返回值】true:CTID = 伪常量;false:不是。
 */
static bool
IsTidEqualClause(RestrictInfo *rinfo, RelOptInfo *rel)
{
	if (!IsBinaryTidClause(rinfo, rel))
		return false;

	if (((OpExpr *) rinfo->clause)->opno == TIDEqualOperator)
		return true;

	return false;
}

/*
 * Check to see if a RestrictInfo is of the form
 *		CTID OP pseudoconstant
 * or
 *		pseudoconstant OP CTID
 * where OP is a range operator such as <, <=, >, or >=, the CTID Var belongs
 * to relation "rel", and nothing on the other side of the clause does.
 */
/*
 * IsTidRangeClause - (中文)判断是否"CTID <op> 伪常量"形式的 TID 范围
 * 子句
 *
 * 【作用】在 IsBinaryTidClause 成立的基础上,要求操作符是 <、<=、> 或 >=
 * 四个 TID 范围比较操作符之一,用于 TidRangePath。
 *
 * 【设计思想】同样复用二元基类判定,再查操作符 OID 集合。范围条件可多条
 * AND 组合(由 TidRangeQualFromRestrictInfoList 收集)。
 *
 * 【参数】
 *   rinfo —— 待判定条件;
 *   rel   —— 目标基表。
 * 【返回值】true:CTID <op> 伪常量(范围比较);false:不是。
 */
static bool
IsTidRangeClause(RestrictInfo *rinfo, RelOptInfo *rel)
{
	Oid			opno;

	if (!IsBinaryTidClause(rinfo, rel))
		return false;
	opno = ((OpExpr *) rinfo->clause)->opno;

	if (opno == TIDLessOperator || opno == TIDLessEqOperator ||
		opno == TIDGreaterOperator || opno == TIDGreaterEqOperator)
		return true;

	return false;
}

/*
 * Check to see if a RestrictInfo is of the form
 *		CTID = ANY (pseudoconstant_array)
 * where the CTID Var belongs to relation "rel", and nothing on the
 * other side of the clause does.
 */
/*
 * IsTidEqualAnyClause - (中文)判断是否"CTID = ANY(伪常量数组)"形式的
 * TID 等值子句
 *
 * 【作用】识别 ScalarArrayOpExpr 形式的 TID 等值:操作符为 tideq、useOr
 * 为 true(即 ANY)、CTID 必须是第一个参数、数组参数不含 rel 的 Var 且无
 * 易变函数。它支撑 WHERE ctid IN (tid1, tid2, ...) 这类写法。
 *
 * 【设计思想】单独识别 ScalarArrayOpExpr 而非把它展开成多个等值,是为
 * 了保留数组形式、方便执行器一次取多个 TID。CTID 固定要求在第一参数
 * (数组在第二参数)。
 *
 * 【参数】
 *   root  —— 规划上下文,用于 pull_varnos;
 *   rinfo —— 待判定条件;
 *   rel   —— 目标基表。
 * 【返回值】true:CTID = ANY(伪常量数组);false:不是。
 */
static bool
IsTidEqualAnyClause(PlannerInfo *root, RestrictInfo *rinfo, RelOptInfo *rel)
{
	ScalarArrayOpExpr *node;
	Node	   *arg1,
			   *arg2;

	/* Must be a ScalarArrayOpExpr */
	if (!(rinfo->clause && IsA(rinfo->clause, ScalarArrayOpExpr)))
		return false;
	node = (ScalarArrayOpExpr *) rinfo->clause;

	/* Operator must be tideq */
	if (node->opno != TIDEqualOperator)
		return false;
	if (!node->useOr)
		return false;
	Assert(list_length(node->args) == 2);
	arg1 = linitial(node->args);
	arg2 = lsecond(node->args);

	/* CTID must be first argument */
	if (arg1 && IsA(arg1, Var) &&
		IsCTIDVar((Var *) arg1, rel))
	{
		/* The other argument must be a pseudoconstant */
		if (bms_is_member(rel->relid, pull_varnos(root, arg2)) ||
			contain_volatile_functions(arg2))
			return false;

		return true;			/* success */
	}

	return false;
}

/*
 * Check to see if a RestrictInfo is a CurrentOfExpr referencing "rel".
 */
/*
 * IsCurrentOfClause - (中文)判断 RestrictInfo 是否为引用 rel 的
 * CurrentOfExpr
 *
 * 【作用】识别 "WHERE CURRENT OF 游标" 条件:它是"CTID = 运行时确定的
 * TID"的抽象,保持专有节点直到执行期由游标位置解析实际 TID。
 *
 * 【设计思想】CurrentOfExpr 的 cvarno 记录目标关系的 varno,与 rel->relid
 * 相等即为本关系的 CURRENT OF 条件。
 *
 * 【参数】
 *   rinfo —— 待判定条件;
 *   rel   —— 目标基表。
 * 【返回值】true:是引用 rel 的 CURRENT OF 条件;false:不是。
 */
static bool
IsCurrentOfClause(RestrictInfo *rinfo, RelOptInfo *rel)
{
	CurrentOfExpr *node;

	/* Must be a CurrentOfExpr */
	if (!(rinfo->clause && IsA(rinfo->clause, CurrentOfExpr)))
		return false;
	node = (CurrentOfExpr *) rinfo->clause;

	/* If it references this rel, we're good */
	if (node->cvarno == rel->relid)
		return true;

	return false;
}

/*
 * Is the RestrictInfo usable as a CTID qual for the specified rel?
 *
 * This function considers only base cases; AND/OR combination is handled
 * below.
 */
/*
 * RestrictInfoIsTidQual - (中文)综合判断单个 RestrictInfo 能否用作 rel
 * 的 CTID 限定条件
 *
 * 【作用】基表(单子句)级判定,只处理基础情形;AND/OR 组合由上层
 * TidQualFromRestrictInfoList 负责。是 TidPath 条件筛选的核心闸门。
 *
 * 【设计思想】依次排除:伪常量子句(不含 Var,不可能命中)、不能安全提前
 * 求值的子句(restriction_is_securely_promotable,即可能被更低安全等级
 * 条件延迟);再依次尝试等值、=ANY、CURRENT OF 三类基础形式,任一命中即
 * 通过。注意范围条件不属于 TidPath 的限定(它属于 TidRangePath,不走此
 * 函数)。
 *
 * 【参数】
 *   root  —— 规划上下文;
 *   rinfo —— 待判定条件;
 *   rel   —— 目标基表。
 * 【返回值】true:可作为 rel 的 CTID 限定条件;false:不可。
 */
static bool
RestrictInfoIsTidQual(PlannerInfo *root, RestrictInfo *rinfo, RelOptInfo *rel)
{
	/*
	 * We may ignore pseudoconstant clauses (they can't contain Vars, so could
	 * not match anyway).
	 */
	if (rinfo->pseudoconstant)
		return false;

	/*
	 * If clause must wait till after some lower-security-level restriction
	 * clause, reject it.
	 */
	if (!restriction_is_securely_promotable(rinfo, rel))
		return false;

	/*
	 * Check all base cases.
	 */
	if (IsTidEqualClause(rinfo, rel) ||
		IsTidEqualAnyClause(root, rinfo, rel) ||
		IsCurrentOfClause(rinfo, rel))
		return true;

	return false;
}

/*
 * Extract a set of CTID conditions from implicit-AND List of RestrictInfos
 *
 * Returns a List of CTID qual RestrictInfos for the specified rel (with
 * implicit OR semantics across the list), or NIL if there are no usable
 * equality conditions.
 *
 * This function is mainly concerned with handling AND/OR recursion.
 * However, we do have a special rule to enforce: if there is a CurrentOfExpr
 * qual, we *must* return that and only that, else the executor may fail.
 * Ordinarily a CurrentOfExpr would be all alone anyway because of grammar
 * restrictions, but it is possible for RLS quals to appear AND'ed with it.
 * It's even possible (if fairly useless) for the RLS quals to be CTID quals.
 * So we must scan the whole rlist to see if there's a CurrentOfExpr.  Since
 * we have to do that, we also apply some very-trivial preference rules about
 * which of the other possibilities should be chosen, in the unlikely event
 * that there's more than one choice.
 */
/*
 * TidQualFromRestrictInfoList - (中文)从隐式 AND 的条件列表中提取 CTID
 * 限定条件集合
 *
 * 【作用】从 rel 的限制/连接条件列表(rlist)中提取可用的 TID 限定条件,
 * 返回一个"列表内隐含 OR 语义"的 CTID 条件列表,无可用时返回 NIL。对
 * AND 内嵌的 OR 条件,要求 OR 的每个分支都能提取出至少一个 CTID 子句。
 *
 * 【设计思想】特殊规则:CURRENT OF 条件一旦存在,必须"只返回它"——否则
 * 执行器无法工作。正常情况下 CURRENT OF 因语法限制总是孤立,但 RLS 条件
 * 可能以 AND 形式与它并存,甚至 RLS 条件也可能是 CTID 条件,故必须扫描
 * 整个 rlist 先确认有无 CurrentOfExpr。顺带实现两条极简偏好:普通单子句
 * 优先于 OR 组合;多个可用 OR 组合时取较短者。
 *
 * 【参数】
 *   root        —— 规划上下文;
 *   rlist       —— 隐式 AND 的 RestrictInfo 列表;
 *   rel         —— 目标基表;
 *   isCurrentOf —— 输出:是否命中了 CURRENT OF 条件。
 * 【返回值】CTID 限定条件(RestrictInfo)列表,隐含 OR 语义;无则 NIL。
 */
static List *
TidQualFromRestrictInfoList(PlannerInfo *root, List *rlist, RelOptInfo *rel,
							bool *isCurrentOf)
{
	RestrictInfo *tidclause = NULL; /* best simple CTID qual so far */
	List	   *orlist = NIL;	/* best OR'ed CTID qual so far */
	ListCell   *l;

	*isCurrentOf = false;

	foreach(l, rlist)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, l);

		if (restriction_is_or_clause(rinfo))
		{
			List	   *rlst = NIL;
			ListCell   *j;

			/*
			 * We must be able to extract a CTID condition from every
			 * sub-clause of an OR, or we can't use it.
			 */
			foreach(j, ((BoolExpr *) rinfo->orclause)->args)
			{
				Node	   *orarg = (Node *) lfirst(j);
				List	   *sublist;

				/* OR arguments should be ANDs or sub-RestrictInfos */
				if (is_andclause(orarg))
				{
					List	   *andargs = ((BoolExpr *) orarg)->args;
					bool		sublistIsCurrentOf;

					/* Recurse in case there are sub-ORs */
					sublist = TidQualFromRestrictInfoList(root, andargs, rel,
														  &sublistIsCurrentOf);
					if (sublistIsCurrentOf)
						elog(ERROR, "IS CURRENT OF within OR clause");
				}
				else
				{
					RestrictInfo *ri = castNode(RestrictInfo, orarg);

					Assert(!restriction_is_or_clause(ri));
					if (RestrictInfoIsTidQual(root, ri, rel))
						sublist = list_make1(ri);
					else
						sublist = NIL;
				}

				/*
				 * If nothing found in this arm, we can't do anything with
				 * this OR clause.
				 */
				if (sublist == NIL)
				{
					rlst = NIL; /* forget anything we had */
					break;		/* out of loop over OR args */
				}

				/*
				 * OK, continue constructing implicitly-OR'ed result list.
				 */
				rlst = list_concat(rlst, sublist);
			}

			if (rlst)
			{
				/*
				 * Accept the OR'ed list if it's the first one, or if it's
				 * shorter than the previous one.
				 */
				if (orlist == NIL || list_length(rlst) < list_length(orlist))
					orlist = rlst;
			}
		}
		else
		{
			/* Not an OR clause, so handle base cases */
			if (RestrictInfoIsTidQual(root, rinfo, rel))
			{
				/* We can stop immediately if it's a CurrentOfExpr */
				if (IsCurrentOfClause(rinfo, rel))
				{
					*isCurrentOf = true;
					return list_make1(rinfo);
				}

				/*
				 * Otherwise, remember the first non-OR CTID qual.  We could
				 * try to apply some preference order if there's more than
				 * one, but such usage seems very unlikely, so don't bother.
				 */
				if (tidclause == NULL)
					tidclause = rinfo;
			}
		}
	}

	/*
	 * Prefer any singleton CTID qual to an OR'ed list.  Again, it seems
	 * unlikely to be worth thinking harder than that.
	 */
	if (tidclause)
		return list_make1(tidclause);
	return orlist;
}

/*
 * Extract a set of CTID range conditions from implicit-AND List of RestrictInfos
 *
 * Returns a List of CTID range qual RestrictInfos for the specified rel
 * (with implicit AND semantics across the list), or NIL if there are no
 * usable range conditions or if the rel's table AM does not support TID range
 * scans.
 */
/*
 * TidRangeQualFromRestrictInfoList - (中文)从隐式 AND 条件列表提取 CTID
 * 范围条件集合
 *
 * 【作用】收集 rlist 中所有 IsTidRangeClause 命中的范围条件,返回"隐含
 * AND 语义"的列表;若关系表 AM 不支持 TID 范围扫描(rel->amflags 无
 * AMFLAG_HAS_TID_RANGE)则直接返回 NIL。
 *
 * 【设计思想】与 TidQualFromRestrictInfoList 不同,这里不做 AND/OR 递归
 * 组合——范围条件只按简单的"每条都收"处理,多条条件之间的 AND 语义由
 * 执行器合并。
 *
 * 【参数】
 *   rlist —— 隐式 AND 的 RestrictInfo 列表;
 *   rel   —— 目标基表。
 * 【返回值】CTID 范围条件(RestrictInfo)列表;无则 NIL。
 */
static List *
TidRangeQualFromRestrictInfoList(List *rlist, RelOptInfo *rel)
{
	List	   *rlst = NIL;
	ListCell   *l;

	if ((rel->amflags & AMFLAG_HAS_TID_RANGE) == 0)
		return NIL;

	foreach(l, rlist)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, l);

		if (IsTidRangeClause(rinfo, rel))
			rlst = lappend(rlst, rinfo);
	}

	return rlst;
}

/*
 * Given a list of join clauses involving our rel, create a parameterized
 * TidPath for each one that is a suitable TidEqual clause.
 *
 * In principle we could combine clauses that reference the same outer rels,
 * but it doesn't seem like such cases would arise often enough to be worth
 * troubling over.
 */
/*
 * BuildParameterizedTidPaths - (中文)为每条可用的 TID 等值连接条件生成
 * 参数化 TidPath
 *
 * 【作用】遍历给定连接条件列表(clauses,可能来自等价类推导或 joininfo),
 * 为每个符合条件的 TID 等值子句生成一个带 required_outer 的 TidPath 并
 * 加入 rel 的路径列表。
 *
 * 【设计思想】虽然理论可把引用相同外层关系的多个子句合并成一条路径,但
 * 此类情形罕见,不值得为它复杂化。筛选步骤:跳过伪常量、不可安全提前、
 * 非 IsTidEqualClause 的子句;再用 join_clause_is_movable_to 确认可移到
 * rel(对 EC 推导出的子句这步基本冗余,但对"松散"连接子句是必要的)。
 * required_outer = (子句 required_relids ∪ rel 的 lateral_relids) 去掉
 * rel 自身。参数化 TID 扫描只考虑等值子句:SAOP 与 CURRENT OF 不会在此
 * 出现,故不调用综合判定 RestrictInfoIsTidQual,但其余规则须与其保持一致。
 *
 * 【参数】
 *   root    —— 规划上下文;
 *   rel     —— 目标基表;
 *   clauses —— 候选连接条件(RestrictInfo)列表。
 * 【返回值】无(路径经 add_path 加入 rel)。
 */
static void
BuildParameterizedTidPaths(PlannerInfo *root, RelOptInfo *rel, List *clauses)
{
	ListCell   *l;

	foreach(l, clauses)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, l);
		List	   *tidquals;
		Relids		required_outer;

		/*
		 * Validate whether each clause is actually usable; we must check this
		 * even when examining clauses generated from an EquivalenceClass,
		 * since they might not satisfy the restriction on not having Vars of
		 * our rel on the other side, or somebody might've built an operator
		 * class that accepts type "tid" but has other operators in it.
		 *
		 * We currently consider only TidEqual join clauses.  In principle we
		 * might find a suitable ScalarArrayOpExpr in the rel's joininfo list,
		 * but it seems unlikely to be worth expending the cycles to check.
		 * And we definitely won't find a CurrentOfExpr here.  Hence, we don't
		 * use RestrictInfoIsTidQual; but this must match that function
		 * otherwise.
		 */
		if (rinfo->pseudoconstant ||
			!restriction_is_securely_promotable(rinfo, rel) ||
			!IsTidEqualClause(rinfo, rel))
			continue;

		/*
		 * Check if clause can be moved to this rel; this is probably
		 * redundant when considering EC-derived clauses, but we must check it
		 * for "loose" join clauses.
		 */
		if (!join_clause_is_movable_to(rinfo, rel))
			continue;

		/* OK, make list of clauses for this path */
		tidquals = list_make1(rinfo);

		/* Compute required outer rels for this path */
		required_outer = bms_union(rinfo->required_relids, rel->lateral_relids);
		required_outer = bms_del_member(required_outer, rel->relid);

		add_path(rel, (Path *) create_tidscan_path(root, rel, tidquals,
												   required_outer));
	}
}

/*
 * Test whether an EquivalenceClass member matches our rel's CTID Var.
 *
 * This is a callback for use by generate_implied_equalities_for_column.
 */
/*
 * ec_member_matches_ctid - (中文)等价类成员匹配 rel 的 CTID Var 的回调
 *
 * 【作用】作为 generate_implied_equalities_for_column 的回调使用:判断
 * 等价类成员 em 的表达式是否就是 rel 的 CTID Var,是则返回 true,触发
 * 该等价类为 CTID 列生成隐含等值条件。
 *
 * 【设计思想】把 IsCTIDVar 包装成回调协议(em->em_expr 必须是 Var 且
 * 是 CTID),与路径生成的其余部分解耦,便于复用通用 EC 工具。
 *
 * 【参数】
 *   root —— 规划上下文;
 *   rel  —— 目标基表;
 *   ec   —— 当前等价类(本函数不使用,符合回调协议);
 *   em   —— 待检查的等价类成员;
 *   arg  —— 额外参数(本函数不使用)。
 * 【返回值】true:em 即 rel 的 CTID Var;false:不是。
 */
static bool
ec_member_matches_ctid(PlannerInfo *root, RelOptInfo *rel,
					   EquivalenceClass *ec, EquivalenceMember *em,
					   void *arg)
{
	if (em->em_expr && IsA(em->em_expr, Var) &&
		IsCTIDVar((Var *) em->em_expr, rel))
		return true;
	return false;
}

/*
 * create_tidscan_paths
 *	  Create paths corresponding to direct TID scans of the given rel and add
 *	  them to the corresponding path list via add_path or add_partial_path.
 */
/*
 * create_tidscan_paths - (中文)为给定基表创建 TID 扫描路径并加入路径列表
 *
 * 【作用】TID 路径生成的唯一对外入口(由 set_base_rel_pathlists 等调
 * 用):为 rel 生成普通 TidPath、TidRangePath(含并行版本)以及参数化
 * TidPath,并通过 add_path / add_partial_path 加入 rel 的路径集合。
 *
 * 【设计思想】执行流程:
 * - 先看基表限制条件里能否提取 CTID 限定条件;若命中,在 TID 扫描启用
 *   或命中 CURRENT OF 时生成普通 TidPath。CURRENT OF 时返回 true,告知
 *   调用方"该路径是执行器唯一能处理的,别再添加其他路径";
 * - TID 扫描禁用则到此为止(返回 false);
 * - 提取范围条件生成 TidRangePath;若关系可并行且无外部参数,再计算
 *   并行 worker 数生成并行部分路径;
 * - 有等价类连接时,经 generate_implied_equalities_for_column + 回调
 *   ec_member_matches_ctid 推导隐含等值条件,为每条生成参数化 TidPath
 *   ("t1.ctid = t2.ctid" 这类条件会变成 EC,此处保证它们仍能催生 TID
 *   路径);
 * - 最后对 joininfo 中的"松散"连接条件同样尝试参数化 TidPath。
 * 注意 pgs_mask 的 PGS_TIDSCAN 是启用开关(来自测试钩子等)。
 *
 * 【参数】
 *   root —— 规划上下文;
 *   rel  —— 目标基表。
 * 【返回值】true:仅生成了 CURRENT OF 路径(调用方不应再添加其他路径);
 *          false:正常情况。
 */
bool
create_tidscan_paths(PlannerInfo *root, RelOptInfo *rel)
{
	List	   *tidquals;
	List	   *tidrangequals;
	bool		isCurrentOf;
	bool		enabled = (rel->pgs_mask & PGS_TIDSCAN) != 0;

	/*
	 * If any suitable quals exist in the rel's baserestrict list, generate a
	 * plain (unparameterized) TidPath with them.
	 *
	 * We skip this when TID scans are disabled, except when the qual is
	 * CurrentOfExpr. In that case, a TID scan is the only correct path.
	 */
	tidquals = TidQualFromRestrictInfoList(root, rel->baserestrictinfo, rel,
										   &isCurrentOf);

	if (tidquals != NIL && (enabled || isCurrentOf))
	{
		/*
		 * This path uses no join clauses, but it could still have required
		 * parameterization due to LATERAL refs in its tlist.
		 */
		Relids		required_outer = rel->lateral_relids;

		add_path(rel, (Path *) create_tidscan_path(root, rel, tidquals,
												   required_outer));

		/*
		 * When the qual is CurrentOfExpr, the path that we just added is the
		 * only one the executor can handle, so we should return before adding
		 * any others. Returning true lets the caller know not to add any
		 * others, either.
		 */
		if (isCurrentOf)
			return true;
	}

	/* Skip the rest if TID scans are disabled. */
	if (!enabled)
		return false;

	/*
	 * If there are range quals in the baserestrict list, generate a
	 * TidRangePath.
	 */
	tidrangequals = TidRangeQualFromRestrictInfoList(rel->baserestrictinfo,
													 rel);

	if (tidrangequals != NIL)
	{
		/*
		 * This path uses no join clauses, but it could still have required
		 * parameterization due to LATERAL refs in its tlist.
		 */
		Relids		required_outer = rel->lateral_relids;

		add_path(rel, (Path *) create_tidrangescan_path(root, rel,
														tidrangequals,
														required_outer,
														0));

		/* If appropriate, consider parallel tid range scan. */
		if (rel->consider_parallel && required_outer == NULL)
		{
			int			parallel_workers;

			parallel_workers = compute_parallel_worker(rel, rel->pages, -1,
													   max_parallel_workers_per_gather);

			if (parallel_workers > 0)
				add_partial_path(rel, (Path *) create_tidrangescan_path(root,
																		rel,
																		tidrangequals,
																		required_outer,
																		parallel_workers));
		}
	}

	/*
	 * Try to generate parameterized TidPaths using equality clauses extracted
	 * from EquivalenceClasses.  (This is important since simple "t1.ctid =
	 * t2.ctid" clauses will turn into ECs.)
	 */
	if (rel->has_eclass_joins)
	{
		List	   *clauses;

		/* Generate clauses, skipping any that join to lateral_referencers */
		clauses = generate_implied_equalities_for_column(root,
														 rel,
														 ec_member_matches_ctid,
														 NULL,
														 rel->lateral_referencers);

		/* Generate a path for each usable join clause */
		BuildParameterizedTidPaths(root, rel, clauses);
	}

	/*
	 * Also consider parameterized TidPaths using "loose" join quals.  Quals
	 * of the form "t1.ctid = t2.ctid" would turn into these if they are outer
	 * join quals, for example.
	 */
	BuildParameterizedTidPaths(root, rel, rel->joininfo);

	return false;
}
