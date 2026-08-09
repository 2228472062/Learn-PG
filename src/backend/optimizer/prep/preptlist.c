/*-------------------------------------------------------------------------
 *
 * preptlist.c
 *	  Routines to preprocess the parse tree target list
 *
 * For an INSERT, the targetlist must contain an entry for each attribute of
 * the target relation in the correct order.
 *
 * For an UPDATE, the targetlist just contains the expressions for the new
 * column values.
 *
 * For UPDATE and DELETE queries, the targetlist must also contain "junk"
 * tlist entries needed to allow the executor to identify the rows to be
 * updated or deleted; for example, the ctid of a heap row.  (The planner
 * adds these; they're not in what we receive from the parser/rewriter.)
 *
 * For all query types, there can be additional junk tlist entries, such as
 * sort keys, Vars needed for a RETURNING list, and row ID information needed
 * for SELECT FOR UPDATE locking and/or EvalPlanQual checking.
 *
 * The query rewrite phase also does preprocessing of the targetlist (see
 * rewriteTargetListIU).  The division of labor between here and there is
 * partially historical, but it's not entirely arbitrary.  The stuff done
 * here is closely connected to physical access to tables, whereas the
 * rewriter's work is more concerned with SQL semantics.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 优化器"预处理器"(prep 模块)的成员,负责预处理查询
 * 树的目标列表(targetlist),即"输出哪些列、按什么顺序、以什么形式提供给
 * 上层"。它是"生成计划之前重写查询树"的一部分。
 *
 * 【本模块的职责】
 * - preprocess_targetlist():主入口。根据命令类型补齐/调整目标列表:
 *   INSERT 必须为结果关系的每个用户属性都生成条目(缺失的属性补 NULL);
 *   UPDATE 提取被更新列编号列表并重排 resno 为连续编号;为 UPDATE/DELETE/
 *   MERGE 增加定位行所需的 "junk"(垃圾)列(如 ctid);为 FOR UPDATE/SHARE
 *   的行锁与 EvalPlanQual 重检增加行标识列(ctid / wholerow / tableoid);
 *   为 RETURNING 和 MERGE 动作中引用的外部关系 Var 增加 junk 条目;
 * - expand_insert_targetlist():INSERT 专用的目标列表展开(补列、排序);
 * - extract_update_targetlist_colnos():把 UPDATE 目标列表里的列编号抽取成
 *   独立列表并把 resno 改成连续编号;
 * - get_plan_rowmark():在行锁标记列表中按 RT 索引查找 PlanRowMark。
 *
 * 【设计思想】
 * - "junk" 列的约定:标记 resjunk = true 的目标条目不对外输出,只供执行器
 *   内部使用(定位待更新/删除的行、行锁、RETURNING 计算等),这样既不打乱
 *   用户可见列的顺序,又能把执行所需的隐藏数据一路传递到计划节点;
 * - 与重写器的分工:rewriteTargetListIU 已经处理了大部分 SQL 语义层面的
 *   目标列表工作,本文件处理"物理访问表"层面的内容(补齐 INSERT 缺列、
 *   增加行身份列),两者历史地互补;
 * - INSERT 补齐列时的三个特例:已删除列(dropped)补 INT4 型 NULL、生成列
 *   (generated)补基类型 NULL 以跳过域约束、普通列补带域约束检查的 NULL
 *   (coerce_null_to_domain 可捕获域 NOT NULL 违规)。
 *
 * 【函数关系】
 * preprocess_targetlist(入口,由 planner.c 在 preprocess_expression 之前
 * 调用)在 INSERT 时调 expand_insert_targetlist,在 UPDATE 时调
 * extract_update_targetlist_colnos;结果存回 root->processed_tlist(及
 * root->update_colnos);get_plan_rowmark 是通用的行锁标记查找工具。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/prep/preptlist.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/sysattr.h"
#include "access/table.h"
#include "catalog/pg_type_d.h"
#include "nodes/makefuncs.h"
#include "optimizer/appendinfo.h"
#include "optimizer/optimizer.h"
#include "optimizer/prep.h"
#include "optimizer/tlist.h"
#include "parser/parse_coerce.h"
#include "parser/parsetree.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"

static List *expand_insert_targetlist(PlannerInfo *root, List *tlist,
									  Relation rel);


/*
 * preprocess_targetlist
 *	  Driver for preprocessing the parse tree targetlist.
 *
 * The preprocessed targetlist is returned in root->processed_tlist.
 * Also, if this is an UPDATE, we return a list of target column numbers
 * in root->update_colnos.  (Resnos in processed_tlist will be consecutive,
 * so do not look at that to find out which columns are targets!)
 */
/*
 * preprocess_targetlist - (中文)目标列表预处理的总驱动
 *
 * 【作用】由 planner.c 在规划早期对每个查询调用。完成:INSERT 用
 * expand_insert_targetlist 补齐缺失属性并把非 junk 列排成表属性顺序;
 * UPDATE 用 extract_update_targetlist_colnos 提取列编号并重排 resno;
 * 非继承的 UPDATE/DELETE/MERGE 用 add_row_identity_columns 增加行身份
 * (junk)列;MERGE 对每个动作做同样的 tlist 处理并收集动作/连接条件中
 * 引用的外部 Var;为 FOR UPDATE/SHARE 的行锁与 EvalPlanQual 增加
 * ctid/wholerow/tableoid junk 列;为 RETURNING 引用的其他关系 Var 增加
 * junk 条目。结果存入 root->processed_tlist(UPDATE 还设置
 * root->update_colnos)。
 *
 * 【设计思想】
 * - 结果关系(结果表的 RTE)在前期已被加锁,这里用 NoLock 打开 relcache 即
 *   可;结果关系必须是普通表(RTE_RELATION),否则解析器/重写器有误;
 * - INSERT 的 tlist 约定是"与表属性顺序一致、缺列补 NULL";UPDATE 的
 *   约定则是"resno = 被更新列编号",因此必须抽取成 update_colnos 并把
 *   processed_tlist 重新编号为连续,此后不要再依赖 resno 找目标列;
 * - 继承情况:行身份列的添加推迟到 expand_inherited_rtentry() 处理叶子
 *   关系时,这里只为非继承情况直接添加;
 * - 行锁 juk 列只对"父 RT"(rti == prti)添加,子关系复用父关系的;需要
 *   TID 时加 ctid,需要整行复制时加 wholerow,继承父表另加 tableoid;
 * - RETURNING / MERGE 引用的非结果关系 Var 若不在 tlist 中,补 resjunk
 *   条目,使执行器能拿到这些值;结果关系自身的 Var 不需要(直接引用堆元组)。
 *
 * 【参数】root —— PlannerInfo,其 parse / rowMarks 等字段被读写,处理结果
 * 写入 root->processed_tlist 与 root->update_colnos。
 * 【返回值】无。
 */
void
preprocess_targetlist(PlannerInfo *root)
{
	Query	   *parse = root->parse;
	int			result_relation = parse->resultRelation;
	List	   *range_table = parse->rtable;
	CmdType		command_type = parse->commandType;
	RangeTblEntry *target_rte = NULL;
	Relation	target_relation = NULL;
	List	   *tlist;
	ListCell   *lc;

	/*
	 * If there is a result relation, open it so we can look for missing
	 * columns and so on.  We assume that previous code already acquired at
	 * least AccessShareLock on the relation, so we need no lock here.
	 */
	if (result_relation)
	{
		target_rte = rt_fetch(result_relation, range_table);

		/*
		 * Sanity check: it'd better be a real relation not, say, a subquery.
		 * Else parser or rewriter messed up.
		 */
		if (target_rte->rtekind != RTE_RELATION)
			elog(ERROR, "result relation must be a regular relation");

		target_relation = table_open(target_rte->relid, NoLock);
	}
	else
		Assert(command_type == CMD_SELECT);

	/*
	 * In an INSERT, the executor expects the targetlist to match the exact
	 * order of the target table's attributes, including entries for
	 * attributes not mentioned in the source query.
	 *
	 * In an UPDATE, we don't rearrange the tlist order, but we need to make a
	 * separate list of the target attribute numbers, in tlist order, and then
	 * renumber the processed_tlist entries to be consecutive.
	 */
	tlist = parse->targetList;
	if (command_type == CMD_INSERT)
		tlist = expand_insert_targetlist(root, tlist, target_relation);
	else if (command_type == CMD_UPDATE)
		root->update_colnos = extract_update_targetlist_colnos(tlist);

	/*
	 * For non-inherited UPDATE/DELETE/MERGE, register any junk column(s)
	 * needed to allow the executor to identify the rows to be updated or
	 * deleted.  In the inheritance case, we do nothing now, leaving this to
	 * be dealt with when expand_inherited_rtentry() makes the leaf target
	 * relations.  (But there might not be any leaf target relations, in which
	 * case we must do this in distribute_row_identity_vars().)
	 */
	if ((command_type == CMD_UPDATE || command_type == CMD_DELETE ||
		 command_type == CMD_MERGE) &&
		!target_rte->inh)
	{
		/* row-identity logic expects to add stuff to processed_tlist */
		root->processed_tlist = tlist;
		add_row_identity_columns(root, result_relation,
								 target_rte, target_relation);
		tlist = root->processed_tlist;
	}

	/*
	 * For MERGE we also need to handle the target list for each INSERT and
	 * UPDATE action separately.  In addition, we examine the qual of each
	 * action and add any Vars there (other than those of the target rel) to
	 * the subplan targetlist.
	 */
	if (command_type == CMD_MERGE)
	{
		ListCell   *l;
		List	   *vars;

		/*
		 * For MERGE, handle targetlist of each MergeAction separately. Give
		 * the same treatment to MergeAction->targetList as we would have
		 * given to a regular INSERT.  For UPDATE, collect the column numbers
		 * being modified.
		 */
		foreach(l, parse->mergeActionList)
		{
			MergeAction *action = (MergeAction *) lfirst(l);
			ListCell   *l2;

			if (action->commandType == CMD_INSERT)
				action->targetList = expand_insert_targetlist(root,
															  action->targetList,
															  target_relation);
			else if (action->commandType == CMD_UPDATE)
				action->updateColnos =
					extract_update_targetlist_colnos(action->targetList);

			/*
			 * Add resjunk entries for any Vars and PlaceHolderVars used in
			 * each action's targetlist and WHEN condition that belong to
			 * relations other than the target.  We don't expect to see any
			 * aggregates or window functions here.
			 */
			vars = pull_var_clause((Node *)
								   list_concat_copy((List *) action->qual,
													action->targetList),
								   PVC_INCLUDE_PLACEHOLDERS);
			foreach(l2, vars)
			{
				Var		   *var = (Var *) lfirst(l2);
				TargetEntry *tle;

				if (IsA(var, Var) && var->varno == result_relation)
					continue;	/* don't need it */

				if (tlist_member((Expr *) var, tlist))
					continue;	/* already got it */

				tle = makeTargetEntry((Expr *) var,
									  list_length(tlist) + 1,
									  NULL, true);
				tlist = lappend(tlist, tle);
			}
			list_free(vars);
		}

		/*
		 * Add resjunk entries for any Vars and PlaceHolderVars used in the
		 * join condition that belong to relations other than the target.  We
		 * don't expect to see any aggregates or window functions here.
		 */
		vars = pull_var_clause(parse->mergeJoinCondition,
							   PVC_INCLUDE_PLACEHOLDERS);
		foreach(l, vars)
		{
			Var		   *var = (Var *) lfirst(l);
			TargetEntry *tle;

			if (IsA(var, Var) && var->varno == result_relation)
				continue;		/* don't need it */

			if (tlist_member((Expr *) var, tlist))
				continue;		/* already got it */

			tle = makeTargetEntry((Expr *) var,
								  list_length(tlist) + 1,
								  NULL, true);
			tlist = lappend(tlist, tle);
		}
	}

	/*
	 * Add necessary junk columns for rowmarked rels.  These values are needed
	 * for locking of rels selected FOR UPDATE/SHARE, and to do EvalPlanQual
	 * rechecking.  See comments for PlanRowMark in plannodes.h.  If you
	 * change this stanza, see also expand_inherited_rtentry(), which has to
	 * be able to add on junk columns equivalent to these.
	 *
	 * (Someday it might be useful to fold these resjunk columns into the
	 * row-identity-column management used for UPDATE/DELETE.  Today is not
	 * that day, however.  One notable issue is that it seems important that
	 * the whole-row Vars made here use the real table rowtype, not RECORD, so
	 * that conversion to/from child relations' rowtypes will happen.  Also,
	 * since these entries don't potentially bloat with more and more child
	 * relations, there's not really much need for column sharing.)
	 */
	foreach(lc, root->rowMarks)
	{
		PlanRowMark *rc = (PlanRowMark *) lfirst(lc);
		Var		   *var;
		char		resname[32];
		TargetEntry *tle;

		/* child rels use the same junk attrs as their parents */
		if (rc->rti != rc->prti)
			continue;

		if (rc->allMarkTypes & ~(1 << ROW_MARK_COPY))
		{
			/* Need to fetch TID */
			var = makeVar(rc->rti,
						  SelfItemPointerAttributeNumber,
						  TIDOID,
						  -1,
						  InvalidOid,
						  0);
			snprintf(resname, sizeof(resname), "ctid%u", rc->rowmarkId);
			tle = makeTargetEntry((Expr *) var,
								  list_length(tlist) + 1,
								  pstrdup(resname),
								  true);
			tlist = lappend(tlist, tle);
		}
		if (rc->allMarkTypes & (1 << ROW_MARK_COPY))
		{
			/* Need the whole row as a junk var */
			var = makeWholeRowVar(rt_fetch(rc->rti, range_table),
								  rc->rti,
								  0,
								  false);
			snprintf(resname, sizeof(resname), "wholerow%u", rc->rowmarkId);
			tle = makeTargetEntry((Expr *) var,
								  list_length(tlist) + 1,
								  pstrdup(resname),
								  true);
			tlist = lappend(tlist, tle);
		}

		/* If parent of inheritance tree, always fetch the tableoid too. */
		if (rc->isParent)
		{
			var = makeVar(rc->rti,
						  TableOidAttributeNumber,
						  OIDOID,
						  -1,
						  InvalidOid,
						  0);
			snprintf(resname, sizeof(resname), "tableoid%u", rc->rowmarkId);
			tle = makeTargetEntry((Expr *) var,
								  list_length(tlist) + 1,
								  pstrdup(resname),
								  true);
			tlist = lappend(tlist, tle);
		}
	}

	/*
	 * If the query has a RETURNING list, add resjunk entries for any Vars
	 * used in RETURNING that belong to other relations.  We need to do this
	 * to make these Vars available for the RETURNING calculation.  Vars that
	 * belong to the result rel don't need to be added, because they will be
	 * made to refer to the actual heap tuple.
	 */
	if (parse->returningList && list_length(parse->rtable) > 1)
	{
		List	   *vars;
		ListCell   *l;

		vars = pull_var_clause((Node *) parse->returningList,
							   PVC_RECURSE_AGGREGATES |
							   PVC_RECURSE_WINDOWFUNCS |
							   PVC_INCLUDE_PLACEHOLDERS);
		foreach(l, vars)
		{
			Var		   *var = (Var *) lfirst(l);
			TargetEntry *tle;

			if (IsA(var, Var) &&
				var->varno == result_relation)
				continue;		/* don't need it */

			if (tlist_member((Expr *) var, tlist))
				continue;		/* already got it */

			tle = makeTargetEntry((Expr *) var,
								  list_length(tlist) + 1,
								  NULL,
								  true);

			tlist = lappend(tlist, tle);
		}
		list_free(vars);
	}

	root->processed_tlist = tlist;

	if (target_relation)
		table_close(target_relation, NoLock);
}

/*
 * extract_update_targetlist_colnos
 * 		Extract a list of the target-table column numbers that
 * 		an UPDATE's targetlist wants to assign to, then renumber.
 *
 * The convention in the parser and rewriter is that the resnos in an
 * UPDATE's non-resjunk TLE entries are the target column numbers
 * to assign to.  Here, we extract that info into a separate list, and
 * then convert the tlist to the sequential-numbering convention that's
 * used by all other query types.
 *
 * This is also applied to the tlist associated with INSERT ... ON CONFLICT
 * ... UPDATE, although not till much later in planning.
 */
/*
 * extract_update_targetlist_colnos - (中文)抽取 UPDATE 目标列表中被更新列
 * 的编号并重排 resno
 *
 * 【作用】解析器/重写器约定:UPDATE 的非 junk TLE 的 resno 就是"要赋值给
 * 的目标表列号"。本函数遍历目标列表,把非 junk 条目的 resno 按顺序收集成
 * 一个整型列表返回,同时把每个条目的 resno 改成 1..N 的连续编号(其他所有
 * 查询类型都采用这一约定,便于执行器按输出顺序访问)。它也在规划后期被
 * 用于处理 INSERT ... ON CONFLICT ... UPDATE 的目标列表。
 *
 * 【设计思想】把"目标列是谁"与"输出顺序是什么"两件事解耦:列编号列表
 * (update_colnos)供执行器知道每列写入表的哪个属性,连续的 resno 让上层
 * 规划代码可以用下标直接访问。junk 条目保留其 resjunk 属性,只参与编号
 * 但不进入 update_colnos。
 *
 * 【参数】tlist —— UPDATE 的目标列表(TargetEntry 列表)。
 * 【返回值】被更新列编号列表(List of int,与 tlist 中非 junk 条目的原
 * resno 顺序一致)。
 */
List *
extract_update_targetlist_colnos(List *tlist)
{
	List	   *update_colnos = NIL;
	AttrNumber	nextresno = 1;
	ListCell   *lc;

	foreach(lc, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(lc);

		if (!tle->resjunk)
			update_colnos = lappend_int(update_colnos, tle->resno);
		tle->resno = nextresno++;
	}
	return update_colnos;
}


/*****************************************************************************
 *
 *		TARGETLIST EXPANSION
 *
 *****************************************************************************/

/*
 * expand_insert_targetlist
 *	  Given a target list as generated by the parser and a result relation,
 *	  add targetlist entries for any missing attributes, and ensure the
 *	  non-junk attributes appear in proper field order.
 *
 * Once upon a time we also did more or less this with UPDATE targetlists,
 * but now this code is only applied to INSERT targetlists.
 */
/*
 * expand_insert_targetlist - (中文)展开 INSERT 的目标列表:补齐缺失属性并
 * 保证属性顺序正确
 *
 * 【作用】给定解析器生成的 INSERT 目标列表与结果关系,生成新的目标列表:
 * 按表的属性顺序(1..numattrs)逐列检查——已有对应 TLE 则沿用,否则构造
 * 一个新 TLE(通常为 NULL 常量);最后把剩余 resjunk 条目追加到末尾并校正
 * 其 resno,使它们都排在真实属性之后。
 *
 * 【设计思想】
 * - 重写器应已保证 TLE 顺序正确,这里只需为"未提及的属性"补条目;
 * - 补列的表达式有三类特例:
 *   1) 已删除列(attisdropped):补 INT4 型 NULL——不能用已不存在的列类型,
 *      而 NULL 的表示与类型无关;
 *   2) 生成列(attgenerated):补基类型(去掉域包装后的类型)NULL,且不做域
 *      约束检查——生成值会被忽略,不能让域 NOT NULL 误报错;
 *   3) 普通列:coerce_null_to_domain 生成带域约束的 NULL,以捕获域 NOT NULL
 *      等约束违规;若非 Const(可能产生了转换表达式),再跑一遍
 *      eval_const_expressions 做常量折叠;
 * - 追加 resjunk 时若 resno 与连续编号不一致,用 flatCopyTargetEntry 复制
 *   一份再改(避免共享节点被多处修改);非 junk 出现在末尾说明顺序错了,报错。
 *
 * 【参数】
 *   root —— PlannerInfo(用于 eval_const_expressions 等);
 *   tlist —— 解析器生成的 INSERT 目标列表;
 *   rel  —— 结果关系,提供属性元数据(rd_att)。
 * 【返回值】展开后的新目标列表。
 */
static List *
expand_insert_targetlist(PlannerInfo *root, List *tlist, Relation rel)
{
	List	   *new_tlist = NIL;
	ListCell   *tlist_item;
	int			attrno,
				numattrs;

	tlist_item = list_head(tlist);

	/*
	 * The rewriter should have already ensured that the TLEs are in correct
	 * order; but we have to insert TLEs for any missing attributes.
	 *
	 * Scan the tuple description in the relation's relcache entry to make
	 * sure we have all the user attributes in the right order.
	 */
	numattrs = RelationGetNumberOfAttributes(rel);

	for (attrno = 1; attrno <= numattrs; attrno++)
	{
		Form_pg_attribute att_tup = TupleDescAttr(rel->rd_att, attrno - 1);
		TargetEntry *new_tle = NULL;

		if (tlist_item != NULL)
		{
			TargetEntry *old_tle = (TargetEntry *) lfirst(tlist_item);

			if (!old_tle->resjunk && old_tle->resno == attrno)
			{
				new_tle = old_tle;
				tlist_item = lnext(tlist, tlist_item);
			}
		}

		if (new_tle == NULL)
		{
			/*
			 * Didn't find a matching tlist entry, so make one.
			 *
			 * INSERTs should insert NULL in this case.  (We assume the
			 * rewriter would have inserted any available non-NULL default
			 * value.)  Also, normally we must apply any domain constraints
			 * that might exist --- this is to catch domain NOT NULL.
			 *
			 * When generating a NULL constant for a dropped column, we label
			 * it INT4 (any other guaranteed-to-exist datatype would do as
			 * well). We can't label it with the dropped column's datatype
			 * since that might not exist anymore.  It does not really matter
			 * what we claim the type is, since NULL is NULL --- its
			 * representation is datatype-independent.  This could perhaps
			 * confuse code comparing the finished plan to the target
			 * relation, however.
			 *
			 * Another exception is that if the column is generated, the value
			 * we produce here will be ignored, and we don't want to risk
			 * throwing an error.  So in that case we *don't* want to apply
			 * domain constraints, so we must produce a NULL of the base type.
			 * Again, code comparing the finished plan to the target relation
			 * must account for this.
			 */
			Node	   *new_expr;

			if (att_tup->attisdropped)
			{
				/* Insert NULL for dropped column */
				new_expr = (Node *) makeConst(INT4OID,
											  -1,
											  InvalidOid,
											  sizeof(int32),
											  (Datum) 0,
											  true, /* isnull */
											  true /* byval */ );
			}
			else if (att_tup->attgenerated)
			{
				/* Generated column, insert a NULL of the base type */
				Oid			baseTypeId = att_tup->atttypid;
				int32		baseTypeMod = att_tup->atttypmod;

				baseTypeId = getBaseTypeAndTypmod(baseTypeId, &baseTypeMod);
				new_expr = (Node *) makeConst(baseTypeId,
											  baseTypeMod,
											  att_tup->attcollation,
											  att_tup->attlen,
											  (Datum) 0,
											  true, /* isnull */
											  att_tup->attbyval);
			}
			else
			{
				/* Normal column, insert a NULL of the column datatype */
				new_expr = coerce_null_to_domain(att_tup->atttypid,
												 att_tup->atttypmod,
												 att_tup->attcollation,
												 att_tup->attlen,
												 att_tup->attbyval);
				/* Must run expression preprocessing on any non-const nodes */
				if (!IsA(new_expr, Const))
					new_expr = eval_const_expressions(root, new_expr);
			}

			new_tle = makeTargetEntry((Expr *) new_expr,
									  attrno,
									  pstrdup(NameStr(att_tup->attname)),
									  false);
		}

		new_tlist = lappend(new_tlist, new_tle);
	}

	/*
	 * The remaining tlist entries should be resjunk; append them all to the
	 * end of the new tlist, making sure they have resnos higher than the last
	 * real attribute.  (Note: although the rewriter already did such
	 * renumbering, we have to do it again here in case we added NULL entries
	 * above.)
	 */
	while (tlist_item)
	{
		TargetEntry *old_tle = (TargetEntry *) lfirst(tlist_item);

		if (!old_tle->resjunk)
			elog(ERROR, "targetlist is not sorted correctly");
		/* Get the resno right, but don't copy unnecessarily */
		if (old_tle->resno != attrno)
		{
			old_tle = flatCopyTargetEntry(old_tle);
			old_tle->resno = attrno;
		}
		new_tlist = lappend(new_tlist, old_tle);
		attrno++;
		tlist_item = lnext(tlist, tlist_item);
	}

	return new_tlist;
}


/*
 * Locate PlanRowMark for given RT index, or return NULL if none
 *
 * This probably ought to be elsewhere, but there's no very good place
 */
/*
 * get_plan_rowmark - (中文)按 RT 索引查找 PlanRowMark
 *
 * 【作用】在给定的行锁标记列表(rowMarks)中线性查找 rti 等于指定值的
 * PlanRowMark,找到返回其指针,找不到返回 NULL。
 *
 * 【设计思想】纯查找工具,放在本文件属历史原因(没有更合适的归属)。执行
 * 器与规划器多处需要根据关系索引获取其行锁标记(例如 EPQ 检查与 FOR
 * UPDATE 处理时)。
 *
 * 【参数】
 *   rowmarks —— PlanRowMark 列表;
 *   rtindex  —— 要查找的关系 RT 索引。
 * 【返回值】匹配的 PlanRowMark 指针;未找到返回 NULL。
 */
PlanRowMark *
get_plan_rowmark(List *rowmarks, Index rtindex)
{
	ListCell   *l;

	foreach(l, rowmarks)
	{
		PlanRowMark *rc = (PlanRowMark *) lfirst(l);

		if (rc->rti == rtindex)
			return rc;
	}
	return NULL;
}
