/*-------------------------------------------------------------------------
 *
 * prepagg.c
 *	  Routines to preprocess aggregate function calls
 *
 * If there are identical aggregate calls in the query, they only need to
 * be computed once.  Also, some aggregate functions can share the same
 * transition state, so that we only need to call the final function for
 * them separately.  These optimizations are independent of how the
 * aggregates are executed.
 *
 * preprocess_aggrefs() detects those cases, creates AggInfo and
 * AggTransInfo structs for each aggregate and transition state that needs
 * to be computed, and sets the 'aggno' and 'transno' fields in the Aggrefs
 * accordingly.  It also resolves polymorphic transition types, and sets
 * the 'aggtranstype' fields accordingly.
 *
 * XXX: The AggInfo and AggTransInfo structs are thrown away after
 * planning, so executor startup has to perform some of the same lookups
 * of transition functions and initial values that we do here.  One day, we
 * might want to carry that information to the Agg nodes to save the effort
 * at executor startup.  The Agg nodes are constructed much later in the
 * planning, however, so it's not trivial.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 优化器"预处理器"(prep 模块)的成员,专门负责对查询中
 * 的聚合函数调用(Aggref)做计划前预处理。它属于"生成计划之前重写查询树"的
 * 环节,核心目标是把多个聚合调用归类、去重,并为每个必须独立计算的聚合
 * 与转移状态建立元数据,供后续代价估算与 Agg 计划节点(GroupAgg/HashedAgg)
 * 的构造使用。
 *
 * 【本模块的职责】
 * - preprocess_aggrefs():主入口。遍历整棵表达式树,对每个 Aggref 解析其
 *   转移状态类型、决定它是否与已见过的聚合"完全相同"(可复用最终结果)或
 *   "输入相同但转移可共享"(可复用转移状态),并把结果编号写回 Aggref 的
 *   aggno / aggtransno 字段;
 * - get_agg_clause_costs():消费 preprocess_aggrefs 建立的 agginfos /
 *   aggtransinfos 列表,估算各聚合函数的转移/合并/最终函数执行代价,以及
 *   HashAgg 所需的哈希表空间,为代价模型提供输入。
 *
 * 【设计思想】
 * 聚合计算可分为"转移阶段"(transfn,逐行更新转移状态)与"最终阶段"
 * (finalfn,把转移状态换算成输出)。本模块的关键洞察:
 * - 若两个 Aggref 在参数、输入整理规则(ORDER BY/DISTINCT/FILTER)、转移
 *   函数、初始值等所有"转移阶段相关属性"上都相同,则它们可共享同一个
 *   转移状态(transno),甚至完全相同者可直接共享最终结果(aggno);
 * - 最终函数若被标记为 AGGMODIFY_READ_WRITE(会破坏转移状态),则不能
 *   与其他聚合共享转移状态,故用 shareable 标志提前排除;
 * - 部分聚合(partial aggregation)是否可行(combinefn、序列化/反序列化
 *   函数是否齐全)也在这里初步判定,结果记录在 root->hasNonPartialAggs /
 *   root->hasNonSerialAggs,供上层决定采用 GroupAgg 还是 HashAgg、是否拆分
 *   为两阶段聚合。
 *
 * 【核心数据结构】
 * - root->agginfos(List of AggInfo):每个需要"调用最终函数"的聚合一项;
 *   记录 finalfn_oid、shareable、以及引用该聚合的全部 Aggref(aggrefs 列表)
 *   和它使用的转移状态编号(transno);
 * - root->aggtransinfos(List of AggTransInfo):每个需要"运行转移函数"的
 *   转移状态一项;记录参数(args)、过滤器(aggfilter)、transfn/combinefn/
 *   serialfn/deserialfn、转移类型与初始值等全部转移阶段信息;
 * - Aggref->aggno / aggtransno:上面两表的下标,计划阶段由 Agg 节点按编号
 *   引用对应的函数与参数。
 *
 * 【函数关系】
 * preprocess_aggrefs(入口) -> preprocess_aggrefs_walker(递归遍历) ->
 * preprocess_aggref(处理单个聚合) -> find_compatible_agg(找可复用最终结果
 * 的同类聚合,顺带收集"输入相同"的转移状态候选) -> find_compatible_trans
 * (进一步核对转移函数/初始值以决定是否共享转移状态);GetAggInitVal 被
 * preprocess_aggref 用来把文本形式的初始值解析为 Datum;get_agg_clause_costs
 * 独立消费上述两表做代价与空间估算。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/prep/prepagg.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/htup_details.h"
#include "catalog/pg_aggregate.h"
#include "catalog/pg_type.h"
#include "nodes/nodeFuncs.h"
#include "nodes/pathnodes.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/plancat.h"
#include "optimizer/prep.h"
#include "parser/parse_agg.h"
#include "utils/builtins.h"
#include "utils/datum.h"
#include "utils/fmgroids.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/syscache.h"

static bool preprocess_aggrefs_walker(Node *node, PlannerInfo *root);
static int	find_compatible_agg(PlannerInfo *root, Aggref *newagg,
								List **same_input_transnos);
static int	find_compatible_trans(PlannerInfo *root, Aggref *newagg,
								  bool shareable,
								  Oid aggtransfn, Oid aggtranstype,
								  int transtypeLen, bool transtypeByVal,
								  Oid aggcombinefn,
								  Oid aggserialfn, Oid aggdeserialfn,
								  Datum initValue, bool initValueIsNull,
								  List *transnos);
static Datum GetAggInitVal(Datum textInitVal, Oid transtype);

/* -----------------
 * Resolve the transition type of all Aggrefs, and determine which Aggrefs
 * can share aggregate or transition state.
 *
 * Information about the aggregates and transition functions are collected
 * in the root->agginfos and root->aggtransinfos lists.  The 'aggtranstype',
 * 'aggno', and 'aggtransno' fields of each Aggref are filled in.
 *
 * NOTE: This modifies the Aggrefs in the input expression in-place!
 *
 * We try to optimize by detecting duplicate aggregate functions so that
 * their state and final values are re-used, rather than needlessly being
 * re-calculated independently.  We also detect aggregates that are not
 * the same, but which can share the same transition state.
 *
 * Scenarios:
 *
 * 1. Identical aggregate function calls appear in the query:
 *
 *	  SELECT SUM(x) FROM ... HAVING SUM(x) > 0
 *
 *	  Since these aggregates are identical, we only need to calculate
 *	  the value once.  Both aggregates will share the same 'aggno' value.
 *
 * 2. Two different aggregate functions appear in the query, but the
 *	  aggregates have the same arguments, transition functions and
 *	  initial values (and, presumably, different final functions):
 *
 *	  SELECT AVG(x), STDDEV(x) FROM ...
 *
 *	  In this case we must create a new AggInfo for the varying aggregate,
 *	  and we need to call the final functions separately, but we need
 *	  only run the transition function once.  (This requires that the
 *	  final functions be nondestructive of the transition state, but
 *	  that's required anyway for other reasons.)
 *
 * For either of these optimizations to be valid, all aggregate properties
 * used in the transition phase must be the same, including any modifiers
 * such as ORDER BY, DISTINCT and FILTER, and the arguments mustn't
 * contain any volatile functions.
 * -----------------
 */

/*
 * preprocess_aggrefs - (中文)聚合预处理的对外入口:遍历表达式并为每个
 * 聚合解析转移类型、分配编号
 *
 * 【作用】在规划早期(subquery_planner 调用 preprocess_expression 之前,
 * 由 planner.c 对每个查询级别调用)对整个 clause(通常是整棵 expression
 * 树或目标列表)做一次扫描,对其中的每个 Aggref 调用 preprocess_aggref
 * 完成归类。注意它只是 walker 的薄封装,实际遍历由
 * preprocess_aggrefs_walker 完成,本函数丢弃 walker 的返回值。
 *
 * 【设计思想】把"扫描表达式树"与"处理单个聚合"分离:walker 负责遍历与
 * 剪枝(遇到 Aggref 不再向下递归),preprocess_aggref 负责系统表查找与
 * 归类编号。设计上保证本模块只对"顶层聚合"(agglevelsup == 0)负责,
 * 嵌套在子查询里的聚合由其自己的查询级别另行处理。
 *
 * 【参数】
 *   root  —— 顶层 PlannerInfo,处理结果(agginfos / aggtransinfos 列表、
 *            numOrderedAggs / hasNonPartialAggs / hasNonSerialAggs 标志、
 *            以及每个 Aggref 的 aggno / aggtransno)都写回它;
 *   clause —— 需要扫描的表达式根节点,会被就地修改(Aggref 字段被填充)。
 * 【返回值】无。
 */
void
preprocess_aggrefs(PlannerInfo *root, Node *clause)
{
	(void) preprocess_aggrefs_walker(clause, root);
}

/*
 * preprocess_aggref - (中文)处理单个 Aggref:解析转移类型、归类聚合、分配
 * aggno 与 aggtransno
 *
 * 【作用】由 preprocess_aggrefs_walker 对每个顶层 Aggref 调用。它从
 * pg_aggregate 系统目录读出该聚合函数的 transfn/finalfn/combinefn/
 * serialfn/deserialfn、声明的转移类型与初始值,解析多态转移类型的真实
 * 类型,然后依次尝试:(1) 在 root->agginfos 中找"完全相同的聚合调用",
 * 找到则复用其 aggno;(2) 否则新建 AggInfo,并在 root->aggtransinfos 中
 * 找"可共享转移状态"的项,找到则复用其 transno,找不到则新建
 * AggTransInfo。最后把编号写回 aggref->aggno / aggref->aggtransno。
 *
 * 【设计思想】
 * - "完全相同"判定的依据是转换阶段属性逐项相等,由 find_compatible_agg
 *   用 equal() 比较;最终函数是否相同反而无所谓——相同最终函数且相同
 *   输入才真正合并为一个 AggInfo;
 * - 转移类型多态解析:用 get_aggregate_argtypes 取出实参类型后调用
 *   resolve_aggregate_transtype;typmod 沿用第一个实参的 typmod(对
 *   MAX/MIN 等场景成立,否则也只是"大概合理");
 * - 共享转移状态的硬性前提是 aggfinalmodify != AGGMODIFY_READ_WRITE
 *   (shareable),因为最终函数会破坏转移状态,不能多个聚合共用;
 * - 部分聚合可行性检查:无 combinefn 则 hasNonPartialAggs = true;
 *   INTERNAL 转移类型缺 serial/deserial 函数则 hasNonSerialAggs = true
 *   (array_agg 的序列化/反序列化还额外要求被聚合类型有 send/receive 函数);
 * - 有序聚合(aggorder/aggdistinct 非空)会同时计数 numOrderedAggs 并
 *   禁止部分聚合。
 *
 * 【参数】
 *   aggref —— 待处理的聚合引用节点,本函数就地填充其 aggtranstype /
 *             aggno / aggtransno 字段;
 *   root   —— 当前 PlannerInfo,聚合元数据列表与统计标志都存于其中。
 * 【返回值】无。
 */
static void
preprocess_aggref(Aggref *aggref, PlannerInfo *root)
{
	HeapTuple	aggTuple;
	Form_pg_aggregate aggform;
	Oid			aggtransfn;
	Oid			aggfinalfn;
	Oid			aggcombinefn;
	Oid			aggserialfn;
	Oid			aggdeserialfn;
	Oid			aggtranstype;
	int32		aggtranstypmod;
	int32		aggtransspace;
	bool		shareable;
	int			aggno;
	int			transno;
	List	   *same_input_transnos;
	int16		resulttypeLen;
	bool		resulttypeByVal;
	Datum		textInitVal;
	Datum		initValue;
	bool		initValueIsNull;
	bool		transtypeByVal;
	int16		transtypeLen;
	Oid			inputTypes[FUNC_MAX_ARGS];
	int			numArguments;

	Assert(aggref->agglevelsup == 0);

	/*
	 * Fetch info about the aggregate from pg_aggregate.  Note it's correct to
	 * ignore the moving-aggregate variant, since what we're concerned with
	 * here is aggregates not window functions.
	 */
	aggTuple = SearchSysCache1(AGGFNOID,
							   ObjectIdGetDatum(aggref->aggfnoid));
	if (!HeapTupleIsValid(aggTuple))
		elog(ERROR, "cache lookup failed for aggregate %u",
			 aggref->aggfnoid);
	aggform = (Form_pg_aggregate) GETSTRUCT(aggTuple);
	aggtransfn = aggform->aggtransfn;
	aggfinalfn = aggform->aggfinalfn;
	aggcombinefn = aggform->aggcombinefn;
	aggserialfn = aggform->aggserialfn;
	aggdeserialfn = aggform->aggdeserialfn;
	aggtranstype = aggform->aggtranstype;
	aggtransspace = aggform->aggtransspace;

	/*
	 * Resolve the possibly-polymorphic aggregate transition type.
	 */

	/* extract argument types (ignoring any ORDER BY expressions) */
	numArguments = get_aggregate_argtypes(aggref, inputTypes);

	/* resolve actual type of transition state, if polymorphic */
	aggtranstype = resolve_aggregate_transtype(aggref->aggfnoid,
											   aggtranstype,
											   inputTypes,
											   numArguments);
	aggref->aggtranstype = aggtranstype;

	/*
	 * If transition state is of same type as first aggregated input, assume
	 * it's the same typmod (same width) as well.  This works for cases like
	 * MAX/MIN and is probably somewhat reasonable otherwise.
	 */
	aggtranstypmod = -1;
	if (aggref->args)
	{
		TargetEntry *tle = (TargetEntry *) linitial(aggref->args);

		if (aggtranstype == exprType((Node *) tle->expr))
			aggtranstypmod = exprTypmod((Node *) tle->expr);
	}

	/*
	 * If finalfn is marked read-write, we can't share transition states; but
	 * it is okay to share states for AGGMODIFY_SHAREABLE aggs.
	 *
	 * In principle, in a partial aggregate, we could share the transition
	 * state even if the final function is marked as read-write, because the
	 * partial aggregate doesn't execute the final function.  But it's too
	 * early to know whether we're going perform a partial aggregate.
	 */
	shareable = (aggform->aggfinalmodify != AGGMODIFY_READ_WRITE);

	/* get info about the output value's datatype */
	get_typlenbyval(aggref->aggtype,
					&resulttypeLen,
					&resulttypeByVal);

	/* get initial value */
	textInitVal = SysCacheGetAttr(AGGFNOID, aggTuple,
								  Anum_pg_aggregate_agginitval,
								  &initValueIsNull);
	if (initValueIsNull)
		initValue = (Datum) 0;
	else
		initValue = GetAggInitVal(textInitVal, aggtranstype);

	ReleaseSysCache(aggTuple);

	/*
	 * 1. See if this is identical to another aggregate function call that
	 * we've seen already.
	 */
	aggno = find_compatible_agg(root, aggref, &same_input_transnos);
	if (aggno != -1)
	{
		AggInfo    *agginfo = list_nth_node(AggInfo, root->agginfos, aggno);

		agginfo->aggrefs = lappend(agginfo->aggrefs, aggref);
		transno = agginfo->transno;
	}
	else
	{
		AggInfo    *agginfo = makeNode(AggInfo);

		agginfo->finalfn_oid = aggfinalfn;
		agginfo->aggrefs = list_make1(aggref);
		agginfo->shareable = shareable;

		aggno = list_length(root->agginfos);
		root->agginfos = lappend(root->agginfos, agginfo);

		/*
		 * Count it, and check for cases requiring ordered input.  Note that
		 * ordered-set aggs always have nonempty aggorder.  Any ordered-input
		 * case also defeats partial aggregation.
		 */
		if (aggref->aggorder != NIL || aggref->aggdistinct != NIL)
		{
			root->numOrderedAggs++;
			root->hasNonPartialAggs = true;
		}

		get_typlenbyval(aggtranstype,
						&transtypeLen,
						&transtypeByVal);

		/*
		 * 2. See if this aggregate can share transition state with another
		 * aggregate that we've initialized already.
		 */
		transno = find_compatible_trans(root, aggref, shareable,
										aggtransfn, aggtranstype,
										transtypeLen, transtypeByVal,
										aggcombinefn,
										aggserialfn, aggdeserialfn,
										initValue, initValueIsNull,
										same_input_transnos);
		if (transno == -1)
		{
			AggTransInfo *transinfo = makeNode(AggTransInfo);

			transinfo->args = aggref->args;
			transinfo->aggfilter = aggref->aggfilter;
			transinfo->transfn_oid = aggtransfn;
			transinfo->combinefn_oid = aggcombinefn;
			transinfo->serialfn_oid = aggserialfn;
			transinfo->deserialfn_oid = aggdeserialfn;
			transinfo->aggtranstype = aggtranstype;
			transinfo->aggtranstypmod = aggtranstypmod;
			transinfo->transtypeLen = transtypeLen;
			transinfo->transtypeByVal = transtypeByVal;
			transinfo->aggtransspace = aggtransspace;
			transinfo->initValue = initValue;
			transinfo->initValueIsNull = initValueIsNull;

			transno = list_length(root->aggtransinfos);
			root->aggtransinfos = lappend(root->aggtransinfos, transinfo);

			/*
			 * Check whether partial aggregation is feasible, unless we
			 * already found out that we can't do it.
			 */
			if (!root->hasNonPartialAggs)
			{
				/*
				 * If there is no combine function, then partial aggregation
				 * is not possible.
				 */
				if (!OidIsValid(transinfo->combinefn_oid))
					root->hasNonPartialAggs = true;

				/*
				 * If we have any aggs with transtype INTERNAL then we must
				 * check whether they have serialization/deserialization
				 * functions; if not, we can't serialize partial-aggregation
				 * results.
				 */
				else if (transinfo->aggtranstype == INTERNALOID)
				{

					if (!OidIsValid(transinfo->serialfn_oid) ||
						!OidIsValid(transinfo->deserialfn_oid))
						root->hasNonSerialAggs = true;

					/*
					 * array_agg_serialize and array_agg_deserialize make use
					 * of the aggregate non-byval input type's send and
					 * receive functions.  There's a chance that the type
					 * being aggregated has one or both of these functions
					 * missing.  In this case we must not allow the
					 * aggregate's serial and deserial functions to be used.
					 * It would be nice not to have special case this and
					 * instead provide some sort of supporting function within
					 * the aggregate to do this, but for now, that seems like
					 * overkill for this one case.
					 */
					if ((transinfo->serialfn_oid == F_ARRAY_AGG_SERIALIZE ||
						 transinfo->deserialfn_oid == F_ARRAY_AGG_DESERIALIZE) &&
						!agg_args_support_sendreceive(aggref))
						root->hasNonSerialAggs = true;
				}
			}
		}
		agginfo->transno = transno;
	}

	/*
	 * Fill in the fields in the Aggref (aggtranstype was set above already)
	 */
	aggref->aggno = aggno;
	aggref->aggtransno = transno;
}

/*
 * preprocess_aggrefs_walker - (中文)表达式树遍历器:找到 Aggref 即交给
 * preprocess_aggref 处理
 *
 * 【作用】expression_tree_walker 的回调,从 preprocess_aggrefs 进入,深度
 * 优先遍历表达式树。遇到 Aggref 节点时调用 preprocess_aggref 处理它,并
 * 返回 false 表示"不再向下递归该节点";遇到 SubLink 直接断言报错(顶层
 * 查询的 SubLink 应已被子查询规划阶段处理,不应出现在这里);其余节点
 * 交给 expression_tree_walker 继续遍历子树。
 *
 * 【设计思想】聚合的"参数、直接参数(directargs)、FILTER 子句"内不允许
 * 再嵌套同层聚合(解析器已保证),因此遇到 Aggref 后无需递归到它的子表达
 * 式,可安全剪枝;返回 false 会让 walker 停止当前分支的遍历。walker 的
 * 返回值语义是"是否提前终止整棵树的遍历",这里始终返回 false(继续)。
 *
 * 【参数】
 *   node —— 当前访问的节点;
 *   root —— 透传给 preprocess_aggref 的 PlannerInfo。
 * 【返回值】false:表示遍历器不应提前终止(所有分支都继续扫描)。
 */
static bool
preprocess_aggrefs_walker(Node *node, PlannerInfo *root)
{
	if (node == NULL)
		return false;
	if (IsA(node, Aggref))
	{
		Aggref	   *aggref = (Aggref *) node;

		preprocess_aggref(aggref, root);

		/*
		 * We assume that the parser checked that there are no aggregates (of
		 * this level anyway) in the aggregated arguments, direct arguments,
		 * or filter clause.  Hence, we need not recurse into any of them.
		 */
		return false;
	}
	Assert(!IsA(node, SubLink));
	return expression_tree_walker(node, preprocess_aggrefs_walker, root);
}


/*
 * find_compatible_agg - search for a previously initialized per-Agg struct
 *
 * Searches the previously looked at aggregates to find one which is compatible
 * with this one, with the same input parameters.  If no compatible aggregate
 * can be found, returns -1.
 *
 * As a side-effect, this also collects a list of existing, shareable per-Trans
 * structs with matching inputs.  If no identical Aggref is found, the list is
 * passed later to find_compatible_trans, to see if we can at least reuse
 * the state value of another aggregate.
 */
/*
 * find_compatible_agg - (中文)在已见过的聚合中查找"完全相同"的聚合,并
 * 顺带收集输入相同的可共享转移状态编号
 *
 * 【作用】在 root->agginfos 中逐一与每个已登记聚合的第一个 Aggref 比较。
 * 若找到完全相同(含相同最终函数)的聚合调用,返回其 aggno,并清空
 * *same_input_transnos(既然直接复用了最终结果,就不再需要转移状态候选);
 * 若找不到,返回 -1,同时把"输入相同、且可共享转移状态"的那些聚合所使用
 * 的 transno 累积进 *same_input_transnos,供 find_compatible_trans 后续
 * 尝试复用其转移状态。
 *
 * 【设计思想】
 * - 先剔除含 volatile 函数的聚合:volatile 函数每次求值结果都可能不同,
 *   共享结果会造成语义错误,直接返回 -1;
 * - "输入相同"指输入整理属性(输入 collation、转移类型、aggstar/
 *   aggvariadic/aggkind、args/aggorder/aggdistinct/aggfilter)全部 equal(),
 *   而"完全相同"还要求聚合函数本身(aggfnoid)、输出类型、输出 collation
 *   和直接参数相同;
 * - 只要一个聚合的 finalfn 是可共享的(shareable),它的 transno 就值得
 *   报告;即使多个候选都指向同一个 transno,也没关系——find_compatible_trans
 *   代价很低,不值得为去重花额外功夫。
 *
 * 【参数】
 *   root                 —— PlannerInfo,agginfos 列表所在;
 *   newagg               —— 正在处理的新 Aggref;
 *   same_input_transnos  —— 输出参数:收集"输入相同"的候选 transno 列表。
 * 【返回值】若找到完全相同的既有聚合,返回其 aggno(≥0);否则返回 -1。
 */
static int
find_compatible_agg(PlannerInfo *root, Aggref *newagg,
					List **same_input_transnos)
{
	ListCell   *lc;
	int			aggno;

	*same_input_transnos = NIL;

	/* we mustn't reuse the aggref if it contains volatile function calls */
	if (contain_volatile_functions((Node *) newagg))
		return -1;

	/*
	 * Search through the list of already seen aggregates.  If we find an
	 * existing identical aggregate call, then we can re-use that one.  While
	 * searching, we'll also collect a list of Aggrefs with the same input
	 * parameters.  If no matching Aggref is found, the caller can potentially
	 * still re-use the transition state of one of them.  (At this stage we
	 * just compare the parsetrees; whether different aggregates share the
	 * same transition function will be checked later.)
	 */
	aggno = -1;
	foreach(lc, root->agginfos)
	{
		AggInfo    *agginfo = lfirst_node(AggInfo, lc);
		Aggref	   *existingRef;

		aggno++;

		existingRef = linitial_node(Aggref, agginfo->aggrefs);

		/* all of the following must be the same or it's no match */
		if (newagg->inputcollid != existingRef->inputcollid ||
			newagg->aggtranstype != existingRef->aggtranstype ||
			newagg->aggstar != existingRef->aggstar ||
			newagg->aggvariadic != existingRef->aggvariadic ||
			newagg->aggkind != existingRef->aggkind ||
			!equal(newagg->args, existingRef->args) ||
			!equal(newagg->aggorder, existingRef->aggorder) ||
			!equal(newagg->aggdistinct, existingRef->aggdistinct) ||
			!equal(newagg->aggfilter, existingRef->aggfilter))
			continue;

		/* if it's the same aggregate function then report exact match */
		if (newagg->aggfnoid == existingRef->aggfnoid &&
			newagg->aggtype == existingRef->aggtype &&
			newagg->aggcollid == existingRef->aggcollid &&
			equal(newagg->aggdirectargs, existingRef->aggdirectargs))
		{
			list_free(*same_input_transnos);
			*same_input_transnos = NIL;
			return aggno;
		}

		/*
		 * Not identical, but it had the same inputs.  If the final function
		 * permits sharing, return its transno to the caller, in case we can
		 * re-use its per-trans state.  (If there's already sharing going on,
		 * we might report a transno more than once.  find_compatible_trans is
		 * cheap enough that it's not worth spending cycles to avoid that.)
		 */
		if (agginfo->shareable)
			*same_input_transnos = lappend_int(*same_input_transnos,
											   agginfo->transno);
	}

	return -1;
}

/*
 * find_compatible_trans - search for a previously initialized per-Trans
 * struct
 *
 * Searches the list of transnos for a per-Trans struct with the same
 * transition function and initial condition. (The inputs have already been
 * verified to match.)
 */
/*
 * find_compatible_trans - (中文)在候选转移状态中查找可以共享的既有项
 *
 * 【作用】find_compatible_agg 已确认"输入相同",本函数在
 * *same_input_transnos(实际是 find_compatible_agg 收集的候选 transno 列表)
 * 基础上做进一步核对:转移函数(transfn)、转移类型、序列化/反序列化函数、
 * 合并函数(combinefn)必须全部相同,且初始值相等,才认为可以共享同一个
 * 转移状态并返回其 transno;任何一项不匹配则继续找下一个,全部不匹配
 * 返回 -1(此时调用者将新建 AggTransInfo)。
 *
 * 【设计思想】
 * - 转移状态共享的前提是"状态迁移方式完全一致",否则后调用的最终函数
 *   会读到错误内容;serialfn/deserialfn 决定转移状态的持久化格式,不同则
 *   无法共享;combinefn 用于部分聚合的合并,也必须一致(规划早期还不知道
 *   是否做部分聚合,只能保守要求全部相同);
 * - 初始值比较分两种情况:两者都为 NULL 即认为相等;否则用
 *   datumIsEqual 按值的"按引用/按值"属性比较。
 *
 * 【参数】
 *   root           —— PlannerInfo,aggtransinfos 列表所在;
 *   newagg         —— 新 Aggref(主要用于在注释场景下提供上下文,当前
 *                     实现未直接使用其字段);
 *   shareable      —— 新聚合是否允许共享转移状态(由 finalfn 的
 *                     aggfinalmodify 决定),为 false 直接放弃;
 *   aggtransfn     —— 新聚合的转移函数 OID;
 *   aggtranstype   —— 转移状态类型 OID(已解析多态后);
 *   transtypeLen/transtypeByVal —— 转移类型的长度与按值/按引用属性,用于
 *                      datumIsEqual;
 *   aggcombinefn/aggserialfn/aggdeserialfn —— 合并与序列化相关函数 OID;
 *   initValue/initValueIsNull —— 新聚合的初始值及其是否为 NULL;
 *   transnos       —— 候选转移状态编号列表(来自 find_compatible_agg)。
 * 【返回值】可共享的既有转移状态编号(≥0);找不到则返回 -1。
 */
static int
find_compatible_trans(PlannerInfo *root, Aggref *newagg, bool shareable,
					  Oid aggtransfn, Oid aggtranstype,
					  int transtypeLen, bool transtypeByVal,
					  Oid aggcombinefn,
					  Oid aggserialfn, Oid aggdeserialfn,
					  Datum initValue, bool initValueIsNull,
					  List *transnos)
{
	ListCell   *lc;

	/* If this aggregate can't share transition states, give up */
	if (!shareable)
		return -1;

	foreach(lc, transnos)
	{
		int			transno = lfirst_int(lc);
		AggTransInfo *pertrans = list_nth_node(AggTransInfo,
											   root->aggtransinfos,
											   transno);

		/*
		 * if the transfns or transition state types are not the same then the
		 * state can't be shared.
		 */
		if (aggtransfn != pertrans->transfn_oid ||
			aggtranstype != pertrans->aggtranstype)
			continue;

		/*
		 * The serialization and deserialization functions must match, if
		 * present, as we're unable to share the trans state for aggregates
		 * which will serialize or deserialize into different formats.
		 * Remember that these will be InvalidOid if they're not required for
		 * this agg node.
		 */
		if (aggserialfn != pertrans->serialfn_oid ||
			aggdeserialfn != pertrans->deserialfn_oid)
			continue;

		/*
		 * Combine function must also match.  We only care about the combine
		 * function with partial aggregates, but it's too early in the
		 * planning to know if we will do partial aggregation, so be
		 * conservative.
		 */
		if (aggcombinefn != pertrans->combinefn_oid)
			continue;

		/*
		 * Check that the initial condition matches, too.
		 */
		if (initValueIsNull && pertrans->initValueIsNull)
			return transno;

		if (!initValueIsNull && !pertrans->initValueIsNull &&
			datumIsEqual(initValue, pertrans->initValue,
						 transtypeByVal, transtypeLen))
			return transno;
	}
	return -1;
}

/*
 * GetAggInitVal - (中文)把 pg_aggregate.agginitval 的文本初始值解析为
 * 转移类型的 Datum
 *
 * 【作用】pg_aggregate 系统目录里聚合的初始值以文本形式存放。本函数通过
 * 转移类型的输入函数把该文本转换为对应类型的 Datum,供 AggTransInfo 的
 * initValue 使用。
 *
 * 【设计思想】初始值的表示与转移类型强相关,必须调用该类型自己的输入函数
 * 才能得到正确字节布局。text 形式到 C 字符串用 TextDatumGetCString 转换,
 * 输入函数用 OidInputFunctionCall 调用(typioparam 用于参数化类型),
 * 解析得到的字符串随后 pfree 释放。
 *
 * 【参数】
 *   textInitVal —— 文本形式的初始值(Datum,实际指向 text 值);
 *   transtype   —— 转移状态类型 OID,决定用哪个输入函数解析。
 * 【返回值】解析后的初始值 Datum(内存由当前内存上下文管理,无需调用者
 * 显式释放)。
 */
static Datum
GetAggInitVal(Datum textInitVal, Oid transtype)
{
	Oid			typinput,
				typioparam;
	char	   *strInitVal;
	Datum		initVal;

	getTypeInputInfo(transtype, &typinput, &typioparam);
	strInitVal = TextDatumGetCString(textInitVal);
	initVal = OidInputFunctionCall(typinput, strInitVal,
								   typioparam, -1);
	pfree(strInitVal);
	return initVal;
}


/*
 * get_agg_clause_costs
 *	  Process the PlannerInfo's 'aggtransinfos' and 'agginfos' lists
 *	  accumulating the cost information about them.
 *
 * 'aggsplit' tells us the expected partial-aggregation mode, which affects
 * the cost estimates.
 *
 * NOTE that the costs are ADDED to those already in *costs ... so the caller
 * is responsible for zeroing the struct initially.
 *
 * For each AggTransInfo, we add the cost of an aggregate transition using
 * either the transfn or combinefn depending on the 'aggsplit' value.  We also
 * account for the costs of any aggfilters and any serializations and
 * deserializations of the transition state and also estimate the total space
 * needed for the transition states as if each aggregate's state was stored in
 * memory concurrently (as would be done in a HashAgg plan).
 *
 * For each AggInfo in the 'agginfos' list we add the cost of running the
 * final function and the direct args, if any.
 */
/*
 * get_agg_clause_costs - (中文)汇总聚合函数执行的代价与 HashAgg 所需空间
 *
 * 【作用】遍历 PlannerInfo 的 aggtransinfos 与 agginfos 两个列表,把各聚合
 * 的转移/合并/序列化/反序列化函数与最终函数的执行代价累加进 *costs,同时
 * 估算所有转移状态若同时驻留内存(HashAgg 场景)所需的总空间
 * (transitionSpace)。由 cost_agg / create_agg_path 等在构造 Agg 路径、
 * 选择 GroupAgg 还是 HashAgg 时调用。
 *
 * 【设计思想】
 * - aggsplit 决定当前聚合节点处于部分聚合(partial)还是最终聚合(final)
 *   阶段:DO_AGGSPLIT_COMBINE 为真表示本节点用 combinefn 合并子节点的
 *   转移状态;DO_AGGSPLIT_DESERIALIZE/SERIALIZE 表示转移状态需要先反序列
 *   化/再序列化(INTERNAL 类型跨进程传递时);
 * - 输入表达式与 FILTER 子句的代价只计入"最底层聚合节点"
 *   (!DO_AGGSPLIT_COMBINE),避免上层重复计费;
 * - 空间估算:按值类型不计空间;按引用类型按 avgwidth(优先用聚合定义的
 *   aggtransspace,array_append 特判为 ALLOCSET_SMALL_INITSIZE,否则用
 *   类型统计宽度)加 palloc 头部估算;INTERNAL 类型虽然按值,但实际是指针,
 *   用 aggtransspace 或默认上下文初值估算;
 * - 注意代价是"累加"进 *costs 而非覆盖,调用者须先清零结构体。
 *
 * 【参数】
 *   root    —— PlannerInfo,含 agginfos / aggtransinfos 列表;
 *   aggsplit —— 预期的部分聚合模式(AggSplit 枚举),影响采用 transfn 还是
 *               combinefn、是否计序列化代价;
 *   costs   —— 输出:AggClauseCosts 结构,累积转移与最终代价及空间需求。
 * 【返回值】无。
 */
void
get_agg_clause_costs(PlannerInfo *root, AggSplit aggsplit, AggClauseCosts *costs)
{
	ListCell   *lc;

	foreach(lc, root->aggtransinfos)
	{
		AggTransInfo *transinfo = lfirst_node(AggTransInfo, lc);

		/*
		 * Add the appropriate component function execution costs to
		 * appropriate totals.
		 */
		if (DO_AGGSPLIT_COMBINE(aggsplit))
		{
			/* charge for combining previously aggregated states */
			add_function_cost(root, transinfo->combinefn_oid, NULL,
							  &costs->transCost);
		}
		else
			add_function_cost(root, transinfo->transfn_oid, NULL,
							  &costs->transCost);
		if (DO_AGGSPLIT_DESERIALIZE(aggsplit) &&
			OidIsValid(transinfo->deserialfn_oid))
			add_function_cost(root, transinfo->deserialfn_oid, NULL,
							  &costs->transCost);
		if (DO_AGGSPLIT_SERIALIZE(aggsplit) &&
			OidIsValid(transinfo->serialfn_oid))
			add_function_cost(root, transinfo->serialfn_oid, NULL,
							  &costs->finalCost);

		/*
		 * These costs are incurred only by the initial aggregate node, so we
		 * mustn't include them again at upper levels.
		 */
		if (!DO_AGGSPLIT_COMBINE(aggsplit))
		{
			/* add the input expressions' cost to per-input-row costs */
			QualCost	argcosts;

			cost_qual_eval_node(&argcosts, (Node *) transinfo->args, root);
			costs->transCost.startup += argcosts.startup;
			costs->transCost.per_tuple += argcosts.per_tuple;

			/*
			 * Add any filter's cost to per-input-row costs.
			 *
			 * XXX Ideally we should reduce input expression costs according
			 * to filter selectivity, but it's not clear it's worth the
			 * trouble.
			 */
			if (transinfo->aggfilter)
			{
				cost_qual_eval_node(&argcosts, (Node *) transinfo->aggfilter,
									root);
				costs->transCost.startup += argcosts.startup;
				costs->transCost.per_tuple += argcosts.per_tuple;
			}
		}

		/*
		 * If the transition type is pass-by-value then it doesn't add
		 * anything to the required size of the hashtable.  If it is
		 * pass-by-reference then we have to add the estimated size of the
		 * value itself, plus palloc overhead.
		 */
		if (!transinfo->transtypeByVal)
		{
			int32		avgwidth;

			/* Use average width if aggregate definition gave one */
			if (transinfo->aggtransspace > 0)
				avgwidth = transinfo->aggtransspace;
			else if (transinfo->transfn_oid == F_ARRAY_APPEND)
			{
				/*
				 * If the transition function is array_append(), it'll use an
				 * expanded array as transvalue, which will occupy at least
				 * ALLOCSET_SMALL_INITSIZE and possibly more.  Use that as the
				 * estimate for lack of a better idea.
				 */
				avgwidth = ALLOCSET_SMALL_INITSIZE;
			}
			else
			{
				avgwidth = get_typavgwidth(transinfo->aggtranstype, transinfo->aggtranstypmod);
			}

			avgwidth = MAXALIGN(avgwidth);
			costs->transitionSpace += avgwidth + 2 * sizeof(void *);
		}
		else if (transinfo->aggtranstype == INTERNALOID)
		{
			/*
			 * INTERNAL transition type is a special case: although INTERNAL
			 * is pass-by-value, it's almost certainly being used as a pointer
			 * to some large data structure.  The aggregate definition can
			 * provide an estimate of the size.  If it doesn't, then we assume
			 * ALLOCSET_DEFAULT_INITSIZE, which is a good guess if the data is
			 * being kept in a private memory context, as is done by
			 * array_agg() for instance.
			 */
			if (transinfo->aggtransspace > 0)
				costs->transitionSpace += transinfo->aggtransspace;
			else
				costs->transitionSpace += ALLOCSET_DEFAULT_INITSIZE;
		}
	}

	foreach(lc, root->agginfos)
	{
		AggInfo    *agginfo = lfirst_node(AggInfo, lc);
		Aggref	   *aggref = linitial_node(Aggref, agginfo->aggrefs);

		/*
		 * Add the appropriate component function execution costs to
		 * appropriate totals.
		 */
		if (!DO_AGGSPLIT_SKIPFINAL(aggsplit) &&
			OidIsValid(agginfo->finalfn_oid))
			add_function_cost(root, agginfo->finalfn_oid, NULL,
							  &costs->finalCost);

		/*
		 * If there are direct arguments, treat their evaluation cost like the
		 * cost of the finalfn.
		 */
		if (aggref->aggdirectargs)
		{
			QualCost	argcosts;

			cost_qual_eval_node(&argcosts, (Node *) aggref->aggdirectargs,
								root);
			costs->finalCost.startup += argcosts.startup;
			costs->finalCost.per_tuple += argcosts.per_tuple;
		}
	}
}
