/*-------------------------------------------------------------------------
 *
 * inherit.c
 *	  Routines to process child relations in inheritance trees
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件处理继承树 / 分区表中的"子关系集合":把带有 inh 标志的 range
 * table 项展开成全部相关子表(或分区、或 UNION ALL 子查询)的 RTE、
 * RelOptInfo、AppendRelInfo,并把父关系上的条件(quals)、行标记(FOR
 * UPDATE/SHARE 的 PlanRowMark)、列权限、被更新列等翻译并分发到各子表。
 * 由此生成"appendrel"(Append 路径的输入集合),供路径生成阶段做 UNION
 * ALL 式连接或分区裁剪。
 *
 * 【两种 appendrel 来源】
 * - 继承 / 分区:RTE 的 relkind 为普通表/分区表,展开后为每个叶子(以及
 *   每个中间分区)建 RTE + AppendRelInfo + RelOptInfo;分区表递归展开
 *   (每一级分区套一层 AppendRelInfo),并利用父关系上的约束做分区裁剪
 *   (prune_append_rel_partitions),被剪掉的叶子不建任何对象;
 * - UNION ALL 子查询:subquery_planner 已把子查询展平并把 RTE/AppendRelInfo
 *   造好,这里只需为各子查询建 RelOptInfo(expand_appendrel_subquery)。
 *
 * 【主要函数关系】
 * expand_inherited_rtentry 是总入口,按 relkind 分流到
 * expand_partitioned_rtentry(分区,递归)或 find_all_inheritors 遍历
 * (传统继承),每个叶子交给 expand_single_inheritance_child 生成 RTE、
 * AppendRelInfo 与 PlanRowMark;随后把新出现的行标记需要的 TID / wholerow
 * / tableoid 等 junk 列追加进 processed_tlist。get_rel_all_updated_cols 取
 * UPDATE 涉及的全部列(经 translate_col_privs / translate_col_privs_multilevel
 * 做列号翻译,再并入依赖的生成列);apply_child_basequals 把父关系的
 * baserestrictinfo 翻译成子关系自身的限制条件,并把常量假/空条件识别出来
 * 以把子表标记为 dummy(这是约束排除能生效的关键)。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/inherit.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <limits.h>

#include "access/sysattr.h"
#include "access/table.h"
#include "catalog/partition.h"
#include "catalog/pg_inherits.h"
#include "catalog/pg_type.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "optimizer/appendinfo.h"
#include "optimizer/inherit.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/plancat.h"
#include "optimizer/planmain.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/restrictinfo.h"
#include "parser/parsetree.h"
#include "parser/parse_relation.h"
#include "partitioning/partdesc.h"
#include "partitioning/partprune.h"
#include "utils/rel.h"


static void expand_partitioned_rtentry(PlannerInfo *root, RelOptInfo *relinfo,
									   RangeTblEntry *parentrte,
									   Index parentRTindex, Relation parentrel,
									   Bitmapset *parent_updatedCols,
									   PlanRowMark *top_parentrc, LOCKMODE lockmode);
static void expand_single_inheritance_child(PlannerInfo *root,
											RangeTblEntry *parentrte,
											Index parentRTindex, Relation parentrel,
											PlanRowMark *top_parentrc, Relation childrel,
											RangeTblEntry **childrte_p,
											Index *childRTindex_p);
static Bitmapset *translate_col_privs(const Bitmapset *parent_privs,
									  List *translated_vars);
static Bitmapset *translate_col_privs_multilevel(PlannerInfo *root,
												 RelOptInfo *rel,
												 RelOptInfo *parent_rel,
												 Bitmapset *parent_cols);
static void expand_appendrel_subquery(PlannerInfo *root, RelOptInfo *rel,
									  RangeTblEntry *rte, Index rti);


/*
 * expand_inherited_rtentry
 *		Expand a rangetable entry that has the "inh" bit set.
 *
 * "inh" is only allowed in two cases: RELATION and SUBQUERY RTEs.
 *
 * "inh" on a plain RELATION RTE means that it is a partitioned table or the
 * parent of a traditional-inheritance set.  In this case we must add entries
 * for all the interesting child tables to the query's rangetable, and build
 * additional planner data structures for them, including RelOptInfos,
 * AppendRelInfos, and possibly PlanRowMarks.
 *
 * Note that the original RTE is considered to represent the whole inheritance
 * set.  In the case of traditional inheritance, the first of the generated
 * RTEs is an RTE for the same table, but with inh = false, to represent the
 * parent table in its role as a simple member of the inheritance set.  For
 * partitioning, we don't need a second RTE because the partitioned table
 * itself has no data and need not be scanned.
 *
 * "inh" on a SUBQUERY RTE means that it's the parent of a UNION ALL group,
 * which is treated as an appendrel similarly to inheritance cases; however,
 * we already made RTEs and AppendRelInfos for the subqueries.  We only need
 * to build RelOptInfos for them, which is done by expand_appendrel_subquery.
 */
/*
 * expand_inherited_rtentry - (中文)展开带 inh 标志的 range table 项
 *
 * 【作用】把查询里"表示整个继承/分区集合"的一个 RTE(rel, rti)展开成
 * 全部子关系:为每个子表建 RTE、AppendRelInfo、RelOptInfo,必要时建
 * PlanRowMark,并把行标记需要的 junk 列(TID / wholerow / tableoid)加入
 * 顶层 processed_tlist。由 subquery_planner / preprocess 阶段对每个 rel 调用。
 *
 * 【设计思想】按 relkind 分流:
 * - 分区表 → expand_partitioned_rtentry 递归展开(分区表本身无数据、不被
 *   扫描,不生成表示自身的子 RTE,且会先做分区裁剪);
 * - 普通表 → find_all_inheritors 找出整个继承集合(含父表自身,第一个元素
 *   即父表),逐个调用 expand_single_inheritance_child;其中属于其他会话的
 *   临时表会被静默跳过。传统继承下父表自身也会生成一个 inh=false 的 RTE,
 *   充当集合中的普通成员。
 * 行标记方面:父 RTE 若被 FOR UPDATE/SHARE,先把父 PlanRowMark 的 isParent
 * 置 true,再为每个子表生成子 PlanRowMark;所有子表的 markType 会累积进
 * 父表 allMarkTypes。展开结束后,若累积出的 mark 类型比展开前多了,就把
 * 对应 junk 列(TID 需要 ROW_MARK 非 COPY 类、整行需要 ROW_MARK_COPY、
 * tableoid 在父表此前未被标记时需要)追加进 processed_tlist 并补进父表
 * reltarget——与 preprocess_targetlist 早先针对父表本应添加的列保持一致。
 *
 * 【参数】
 *   root —— 规划上下文;rel —— 表示该继承集合的 RelOptInfo;
 *   rte  —— 带 inh 标志的 RTE;rti —— 它的 RTE 下标。
 * 【返回值】无。
 */
void
expand_inherited_rtentry(PlannerInfo *root, RelOptInfo *rel,
						 RangeTblEntry *rte, Index rti)
{
	Oid			parentOID;
	Relation	oldrelation;
	LOCKMODE	lockmode;
	PlanRowMark *oldrc;
	bool		old_isParent = false;
	int			old_allMarkTypes = 0;

	Assert(rte->inh);			/* else caller error */

	if (rte->rtekind == RTE_SUBQUERY)
	{
		expand_appendrel_subquery(root, rel, rte, rti);
		return;
	}

	Assert(rte->rtekind == RTE_RELATION);

	parentOID = rte->relid;

	/*
	 * We used to check has_subclass() here, but there's no longer any need
	 * to, because subquery_planner already did.
	 */

	/*
	 * The rewriter should already have obtained an appropriate lock on each
	 * relation named in the query, so we can open the parent relation without
	 * locking it.  However, for each child relation we add to the query, we
	 * must obtain an appropriate lock, because this will be the first use of
	 * those relations in the parse/rewrite/plan pipeline.  Child rels should
	 * use the same lockmode as their parent.
	 */
	oldrelation = table_open(parentOID, NoLock);
	lockmode = rte->rellockmode;

	/*
	 * If parent relation is selected FOR UPDATE/SHARE, we need to mark its
	 * PlanRowMark as isParent = true, and generate a new PlanRowMark for each
	 * child.
	 */
	oldrc = get_plan_rowmark(root->rowMarks, rti);
	if (oldrc)
	{
		old_isParent = oldrc->isParent;
		oldrc->isParent = true;
		/* Save initial value of allMarkTypes before children add to it */
		old_allMarkTypes = oldrc->allMarkTypes;
	}

	/* Scan the inheritance set and expand it */
	if (oldrelation->rd_rel->relkind == RELKIND_PARTITIONED_TABLE)
	{
		RTEPermissionInfo *perminfo;

		perminfo = getRTEPermissionInfo(root->parse->rteperminfos, rte);

		/*
		 * Partitioned table, so set up for partitioning.
		 */
		Assert(rte->relkind == RELKIND_PARTITIONED_TABLE);

		/*
		 * Recursively expand and lock the partitions.  While at it, also
		 * extract the partition key columns of all the partitioned tables.
		 */
		expand_partitioned_rtentry(root, rel, rte, rti,
								   oldrelation,
								   perminfo->updatedCols,
								   oldrc, lockmode);
	}
	else
	{
		/*
		 * Ordinary table, so process traditional-inheritance children.  (Note
		 * that partitioned tables are not allowed to have inheritance
		 * children, so it's not possible for both cases to apply.)
		 */
		List	   *inhOIDs;
		ListCell   *l;

		/* Scan for all members of inheritance set, acquire needed locks */
		inhOIDs = find_all_inheritors(parentOID, lockmode, NULL);

		/*
		 * We used to special-case the situation where the table no longer has
		 * any children, by clearing rte->inh and exiting.  That no longer
		 * works, because this function doesn't get run until after decisions
		 * have been made that depend on rte->inh.  We have to treat such
		 * situations as normal inheritance.  The table itself should always
		 * have been found, though.
		 */
		Assert(inhOIDs != NIL);
		Assert(linitial_oid(inhOIDs) == parentOID);

		/* Expand simple_rel_array and friends to hold child objects. */
		expand_planner_arrays(root, list_length(inhOIDs));

		/*
		 * Expand inheritance children in the order the OIDs were returned by
		 * find_all_inheritors.
		 */
		foreach(l, inhOIDs)
		{
			Oid			childOID = lfirst_oid(l);
			Relation	newrelation;
			RangeTblEntry *childrte;
			Index		childRTindex;

			/* Open rel if needed; we already have required locks */
			if (childOID != parentOID)
				newrelation = table_open(childOID, NoLock);
			else
				newrelation = oldrelation;

			/*
			 * It is possible that the parent table has children that are temp
			 * tables of other backends.  We cannot safely access such tables
			 * (because of buffering issues), and the best thing to do seems
			 * to be to silently ignore them.
			 */
			if (childOID != parentOID && RELATION_IS_OTHER_TEMP(newrelation))
			{
				table_close(newrelation, lockmode);
				continue;
			}

			/* Create RTE and AppendRelInfo, plus PlanRowMark if needed. */
			expand_single_inheritance_child(root, rte, rti, oldrelation,
											oldrc, newrelation,
											&childrte, &childRTindex);

			/* Create the otherrel RelOptInfo too. */
			(void) build_simple_rel(root, childRTindex, rel);

			/* Close child relations, but keep locks */
			if (childOID != parentOID)
				table_close(newrelation, NoLock);
		}
	}

	/*
	 * Some children might require different mark types, which would've been
	 * reported into oldrc.  If so, add relevant entries to the top-level
	 * targetlist and update parent rel's reltarget.  This should match what
	 * preprocess_targetlist() would have added if the mark types had been
	 * requested originally.
	 *
	 * (Someday it might be useful to fold these resjunk columns into the
	 * row-identity-column management used for UPDATE/DELETE.  Today is not
	 * that day, however.)
	 */
	if (oldrc)
	{
		int			new_allMarkTypes = oldrc->allMarkTypes;
		Var		   *var;
		TargetEntry *tle;
		char		resname[32];
		List	   *newvars = NIL;

		/* Add TID junk Var if needed, unless we had it already */
		if (new_allMarkTypes & ~(1 << ROW_MARK_COPY) &&
			!(old_allMarkTypes & ~(1 << ROW_MARK_COPY)))
		{
			/* Need to fetch TID */
			var = makeVar(oldrc->rti,
						  SelfItemPointerAttributeNumber,
						  TIDOID,
						  -1,
						  InvalidOid,
						  0);
			snprintf(resname, sizeof(resname), "ctid%u", oldrc->rowmarkId);
			tle = makeTargetEntry((Expr *) var,
								  list_length(root->processed_tlist) + 1,
								  pstrdup(resname),
								  true);
			root->processed_tlist = lappend(root->processed_tlist, tle);
			newvars = lappend(newvars, var);
		}

		/* Add whole-row junk Var if needed, unless we had it already */
		if ((new_allMarkTypes & (1 << ROW_MARK_COPY)) &&
			!(old_allMarkTypes & (1 << ROW_MARK_COPY)))
		{
			var = makeWholeRowVar(planner_rt_fetch(oldrc->rti, root),
								  oldrc->rti,
								  0,
								  false);
			snprintf(resname, sizeof(resname), "wholerow%u", oldrc->rowmarkId);
			tle = makeTargetEntry((Expr *) var,
								  list_length(root->processed_tlist) + 1,
								  pstrdup(resname),
								  true);
			root->processed_tlist = lappend(root->processed_tlist, tle);
			newvars = lappend(newvars, var);
		}

		/* Add tableoid junk Var, unless we had it already */
		if (!old_isParent)
		{
			var = makeVar(oldrc->rti,
						  TableOidAttributeNumber,
						  OIDOID,
						  -1,
						  InvalidOid,
						  0);
			snprintf(resname, sizeof(resname), "tableoid%u", oldrc->rowmarkId);
			tle = makeTargetEntry((Expr *) var,
								  list_length(root->processed_tlist) + 1,
								  pstrdup(resname),
								  true);
			root->processed_tlist = lappend(root->processed_tlist, tle);
			newvars = lappend(newvars, var);
		}

		/*
		 * Add the newly added Vars to parent's reltarget.  We needn't worry
		 * about the children's reltargets, they'll be made later.
		 */
		add_vars_to_targetlist(root, newvars, bms_make_singleton(0));
	}

	table_close(oldrelation, NoLock);
}

/*
 * expand_partitioned_rtentry
 *		Recursively expand an RTE for a partitioned table.
 */
/*
 * expand_partitioned_rtentry - (中文)递归展开分区表 RTE
 *
 * 【作用】对单个分区表:取出分区描述,用父表限制条件做分区裁剪,然后为
 * 每个存活分区建 RTE、AppendRelInfo、RelOptInfo;若分区自身仍是分区表,
 * 递归展开它。同时维护父 RelOptInfo 的 part_rels 数组与 all_partrels 位图。
 *
 * 【设计思想】逐层展开(level-by-level):每个分区都与其直接父分区构成
 * 一条 AppendRelInfo 映射,中间层分区同时是"子"与"父"。分区裁剪
 * (prune_append_rel_partitions)先把不需要的叶子砍掉,存活的以 PartitionDesc
 * 下标记录在 relinfo->live_parts;part_rels 用 palloc0 分配,被剪掉的下标
 * 槽位保持 NULL。对每个存活分区:
 * - try_table_open 打开(刚被 DETACH+DROP 的分区会打开失败,视为被剪掉);
 * - 其他会话的临时分区直接报错(定义时本就不允许);
 * - expand_single_inheritance_child 建 RTE/AppendRelInfo/PlanRowMark,
 *   build_simple_rel 建 RelOptInfo 并填入 part_rels、并入 all_partrels;
 * - 若是分区表,用 translate_col_privs 把父的 updatedCols 翻译成本分区的
 *   列号后递归。updatedCols 沿继承链逐层翻译,是后续 get_rel_all_updated_cols
 *   的数据来源。递归用 check_stack_depth 防止深分区层级爆栈。
 *
 * 【参数】
 *   root             —— 规划上下文;relinfo —— 父分区关系的 RelOptInfo;
 *   parentrte / parentRTindex —— 父分区 RTE 及其下标;
 *   parentrel        —— 已打开的父分区关系;
 *   parent_updatedCols —— 父的更新列位图(将翻译给子分区);
 *   top_parentrc     —— 顶层结果的 PlanRowMark(若有);
 *   lockmode         —— 给子分区加锁的模式。
 * 【返回值】无。
 */
static void
expand_partitioned_rtentry(PlannerInfo *root, RelOptInfo *relinfo,
						   RangeTblEntry *parentrte,
						   Index parentRTindex, Relation parentrel,
						   Bitmapset *parent_updatedCols,
						   PlanRowMark *top_parentrc, LOCKMODE lockmode)
{
	PartitionDesc partdesc;
	int			num_live_parts;
	int			i;

	check_stack_depth();

	Assert(parentrte->inh);

	partdesc = PartitionDirectoryLookup(root->glob->partition_directory,
										parentrel);

	/* A partitioned table should always have a partition descriptor. */
	Assert(partdesc);

	/* Nothing further to do here if there are no partitions. */
	if (partdesc->nparts == 0)
		return;

	/*
	 * Perform partition pruning using restriction clauses assigned to parent
	 * relation.  live_parts will contain PartitionDesc indexes of partitions
	 * that survive pruning.  Below, we will initialize child objects for the
	 * surviving partitions.
	 */
	relinfo->live_parts = prune_append_rel_partitions(relinfo);

	/* Expand simple_rel_array and friends to hold child objects. */
	num_live_parts = bms_num_members(relinfo->live_parts);
	if (num_live_parts > 0)
		expand_planner_arrays(root, num_live_parts);

	/*
	 * We also store partition RelOptInfo pointers in the parent relation.
	 * Since we're palloc0'ing, slots corresponding to pruned partitions will
	 * contain NULL.
	 */
	Assert(relinfo->part_rels == NULL);
	relinfo->part_rels = (RelOptInfo **)
		palloc0(relinfo->nparts * sizeof(RelOptInfo *));

	/*
	 * Create a child RTE for each live partition.  Note that unlike
	 * traditional inheritance, we don't need a child RTE for the partitioned
	 * table itself, because it's not going to be scanned.
	 */
	i = -1;
	while ((i = bms_next_member(relinfo->live_parts, i)) >= 0)
	{
		Oid			childOID = partdesc->oids[i];
		Relation	childrel;
		RangeTblEntry *childrte;
		Index		childRTindex;
		RelOptInfo *childrelinfo;

		/*
		 * Open rel, acquiring required locks.  If a partition was recently
		 * detached and subsequently dropped, then opening it will fail.  In
		 * this case, behave as though the partition had been pruned.
		 */
		childrel = try_table_open(childOID, lockmode);
		if (childrel == NULL)
		{
			relinfo->live_parts = bms_del_member(relinfo->live_parts, i);
			continue;
		}

		/*
		 * Temporary partitions belonging to other sessions should have been
		 * disallowed at definition, but for paranoia's sake, let's double
		 * check.
		 */
		if (RELATION_IS_OTHER_TEMP(childrel))
			elog(ERROR, "temporary relation from another session found as partition");

		/* Create RTE and AppendRelInfo, plus PlanRowMark if needed. */
		expand_single_inheritance_child(root, parentrte, parentRTindex,
										parentrel, top_parentrc, childrel,
										&childrte, &childRTindex);

		/* Create the otherrel RelOptInfo too. */
		childrelinfo = build_simple_rel(root, childRTindex, relinfo);
		relinfo->part_rels[i] = childrelinfo;
		relinfo->all_partrels = bms_add_members(relinfo->all_partrels,
												childrelinfo->relids);

		/* If this child is itself partitioned, recurse */
		if (childrel->rd_rel->relkind == RELKIND_PARTITIONED_TABLE)
		{
			AppendRelInfo *appinfo = root->append_rel_array[childRTindex];
			Bitmapset  *child_updatedCols;

			child_updatedCols = translate_col_privs(parent_updatedCols,
													appinfo->translated_vars);

			expand_partitioned_rtentry(root, childrelinfo,
									   childrte, childRTindex,
									   childrel,
									   child_updatedCols,
									   top_parentrc, lockmode);
		}

		/* Close child relation, but keep locks */
		table_close(childrel, NoLock);
	}
}

/*
 * expand_single_inheritance_child
 *		Build a RangeTblEntry and an AppendRelInfo, plus maybe a PlanRowMark.
 *
 * We now expand the partition hierarchy level by level, creating a
 * corresponding hierarchy of AppendRelInfos and RelOptInfos, where each
 * partitioned descendant acts as a parent of its immediate partitions.
 * (This is a difference from what older versions of PostgreSQL did and what
 * is still done in the case of table inheritance for unpartitioned tables,
 * where the hierarchy is flattened during RTE expansion.)
 *
 * PlanRowMarks still carry the top-parent's RTI, and the top-parent's
 * allMarkTypes field still accumulates values from all descendents.
 *
 * "parentrte" and "parentRTindex" are immediate parent's RTE and
 * RTI. "top_parentrc" is top parent's PlanRowMark.
 *
 * The child RangeTblEntry and its RTI are returned in "childrte_p" and
 * "childRTindex_p" resp.
 */
/*
 * expand_single_inheritance_child - (中文)为单个子关系建 RTE/AppendRelInfo/PlanRowMark
 *
 * 【作用】为给定的父子关系对构建完整的三件套:child RTE(挂入 parse->rtable)、
 * AppendRelInfo(挂入 append_rel_list 与 append_rel_array)、以及在父被 FOR
 * UPDATE/SHARE 时的子 PlanRowMark(挂入 root->rowMarks)。同时维护
 * all_result_relids / leaf_result_relids,并注册目标子表所需的行标识列。
 *
 * 【设计思想】子 RTE 用"平拷贝父 RTE + 替换关键字段"生成:relid、relkind、
 * inh(仅当子仍是分区表时为 true,以便上层继续展开)、securityQuals 清空
 * (RLS 只按父的语义应用,父的限制条件会随 base quals 分发下去)、
 * perminfoindex 置 0(子 RTE 不参与权限检查,权限由父统一负责)。列的别名
 * (alias/eref)根据 parent_colnos 反向映射逐列从父的列名复制,EXPLAIN 才能
 * 打印出正确的子表列名。若该子表被标记 FOR UPDATE/SHARE,子 PlanRowMark
 * 的 markType 按子表 relkind 重新选择,partitioned 子表标记 isParent(executor
 * 忽略它,只借它完成加锁);各子表 markType 累积进顶层父的 allMarkTypes。
 * 对 UPDATE/DELETE/MERGE 的目标集合:把本子表加入 all_result_relids(叶子则
 * 再加进 leaf_result_relids),并为非分区叶子注册 tableoid 与所需行标识列
 * (add_row_identity_var / add_row_identity_columns)。
 *
 * 【参数】
 *   root           —— 规划上下文;parentrte / parentRTindex —— 直接父 RTE 及下标;
 *   parentrel      —— 直接父关系;childrel —— 已打开的子关系;
 *   top_parentrc   —— 顶层父的 PlanRowMark(可能为 NULL);
 *   childrte_p     —— 输出参数:生成的子 RTE;
 *   childRTindex_p —— 输出参数:子 RTE 下标。
 * 【返回值】无(通过输出参数返回)。
 */
static void
expand_single_inheritance_child(PlannerInfo *root, RangeTblEntry *parentrte,
								Index parentRTindex, Relation parentrel,
								PlanRowMark *top_parentrc, Relation childrel,
								RangeTblEntry **childrte_p,
								Index *childRTindex_p)
{
	Query	   *parse = root->parse;
	Oid			parentOID = RelationGetRelid(parentrel);
	Oid			childOID = RelationGetRelid(childrel);
	RangeTblEntry *childrte;
	Index		childRTindex;
	AppendRelInfo *appinfo;
	TupleDesc	child_tupdesc;
	List	   *parent_colnames;
	List	   *child_colnames;

	/*
	 * Build an RTE for the child, and attach to query's rangetable list. We
	 * copy most scalar fields of the parent's RTE, but replace relation OID,
	 * relkind, and inh for the child.  Set the child's securityQuals to
	 * empty, because we only want to apply the parent's RLS conditions
	 * regardless of what RLS properties individual children may have. (This
	 * is an intentional choice to make inherited RLS work like regular
	 * permissions checks.) The parent securityQuals will be propagated to
	 * children along with other base restriction clauses, so we don't need to
	 * do it here.  Other infrastructure of the parent RTE has to be
	 * translated to match the child table's column ordering, which we do
	 * below, so a "flat" copy is sufficient to start with.
	 */
	childrte = makeNode(RangeTblEntry);
	memcpy(childrte, parentrte, sizeof(RangeTblEntry));
	Assert(parentrte->rtekind == RTE_RELATION); /* else this is dubious */
	childrte->relid = childOID;
	childrte->relkind = childrel->rd_rel->relkind;
	/* A partitioned child will need to be expanded further. */
	if (childrte->relkind == RELKIND_PARTITIONED_TABLE)
	{
		Assert(childOID != parentOID);
		childrte->inh = true;
	}
	else
		childrte->inh = false;
	childrte->securityQuals = NIL;

	/* No permission checking for child RTEs. */
	childrte->perminfoindex = 0;

	/* Link not-yet-fully-filled child RTE into data structures */
	parse->rtable = lappend(parse->rtable, childrte);
	childRTindex = list_length(parse->rtable);
	*childrte_p = childrte;
	*childRTindex_p = childRTindex;

	/*
	 * Retrieve column not-null constraint information for the child relation
	 * if its relation OID is different from the parent's.
	 */
	if (childOID != parentOID)
		get_relation_notnullatts(root, childrel);

	/*
	 * Build an AppendRelInfo struct for each parent/child pair.
	 */
	appinfo = make_append_rel_info(parentrel, childrel,
								   parentRTindex, childRTindex);
	root->append_rel_list = lappend(root->append_rel_list, appinfo);

	/* tablesample is probably null, but copy it */
	childrte->tablesample = copyObject(parentrte->tablesample);

	/*
	 * Construct an alias clause for the child, which we can also use as eref.
	 * This is important so that EXPLAIN will print the right column aliases
	 * for child-table columns.  (Since ruleutils.c doesn't have any easy way
	 * to reassociate parent and child columns, we must get the child column
	 * aliases right to start with.  Note that setting childrte->alias forces
	 * ruleutils.c to use these column names, which it otherwise would not.)
	 */
	child_tupdesc = RelationGetDescr(childrel);
	parent_colnames = parentrte->eref->colnames;
	child_colnames = NIL;
	for (int cattno = 0; cattno < child_tupdesc->natts; cattno++)
	{
		Form_pg_attribute att = TupleDescAttr(child_tupdesc, cattno);
		const char *attname;

		if (att->attisdropped)
		{
			/* Always insert an empty string for a dropped column */
			attname = "";
		}
		else if (appinfo->parent_colnos[cattno] > 0 &&
				 appinfo->parent_colnos[cattno] <= list_length(parent_colnames))
		{
			/* Duplicate the query-assigned name for the parent column */
			attname = strVal(list_nth(parent_colnames,
									  appinfo->parent_colnos[cattno] - 1));
		}
		else
		{
			/* New column, just use its real name */
			attname = NameStr(att->attname);
		}
		child_colnames = lappend(child_colnames, makeString(pstrdup(attname)));
	}

	/*
	 * We just duplicate the parent's table alias name for each child.  If the
	 * plan gets printed, ruleutils.c has to sort out unique table aliases to
	 * use, which it can handle.
	 */
	childrte->alias = childrte->eref = makeAlias(parentrte->eref->aliasname,
												 child_colnames);

	/*
	 * Store the RTE and appinfo in the respective PlannerInfo arrays, which
	 * the caller must already have allocated space for.
	 */
	Assert(childRTindex < root->simple_rel_array_size);
	Assert(root->simple_rte_array[childRTindex] == NULL);
	root->simple_rte_array[childRTindex] = childrte;
	Assert(root->append_rel_array[childRTindex] == NULL);
	root->append_rel_array[childRTindex] = appinfo;

	/*
	 * Build a PlanRowMark if parent is marked FOR UPDATE/SHARE.
	 */
	if (top_parentrc)
	{
		PlanRowMark *childrc = makeNode(PlanRowMark);

		childrc->rti = childRTindex;
		childrc->prti = top_parentrc->rti;
		childrc->rowmarkId = top_parentrc->rowmarkId;
		/* Reselect rowmark type, because relkind might not match parent */
		childrc->markType = select_rowmark_type(childrte,
												top_parentrc->strength);
		childrc->allMarkTypes = (1 << childrc->markType);
		childrc->strength = top_parentrc->strength;
		childrc->waitPolicy = top_parentrc->waitPolicy;

		/*
		 * We mark RowMarks for partitioned child tables as parent RowMarks so
		 * that the executor ignores them (except their existence means that
		 * the child tables will be locked using the appropriate mode).
		 */
		childrc->isParent = (childrte->relkind == RELKIND_PARTITIONED_TABLE);

		/* Include child's rowmark type in top parent's allMarkTypes */
		top_parentrc->allMarkTypes |= childrc->allMarkTypes;

		root->rowMarks = lappend(root->rowMarks, childrc);
	}

	/*
	 * If we are creating a child of the query target relation (only possible
	 * in UPDATE/DELETE/MERGE), add it to all_result_relids, as well as
	 * leaf_result_relids if appropriate, and make sure that we generate
	 * required row-identity data.
	 */
	if (bms_is_member(parentRTindex, root->all_result_relids))
	{
		/* OK, record the child as a result rel too. */
		root->all_result_relids = bms_add_member(root->all_result_relids,
												 childRTindex);

		/* Non-leaf partitions don't need any row identity info. */
		if (childrte->relkind != RELKIND_PARTITIONED_TABLE)
		{
			Var		   *rrvar;

			root->leaf_result_relids = bms_add_member(root->leaf_result_relids,
													  childRTindex);

			/*
			 * If we have any child target relations, assume they all need to
			 * generate a junk "tableoid" column.  (If only one child survives
			 * pruning, we wouldn't really need this, but it's not worth
			 * thrashing about to avoid it.)
			 */
			rrvar = makeVar(childRTindex,
							TableOidAttributeNumber,
							OIDOID,
							-1,
							InvalidOid,
							0);
			add_row_identity_var(root, rrvar, childRTindex, "tableoid");

			/* Register any row-identity columns needed by this child. */
			add_row_identity_columns(root, childRTindex,
									 childrte, childrel);
		}
	}
}

/*
 * get_rel_all_updated_cols
 * 		Returns the set of columns of a given "simple" relation that are
 * 		updated by this query.
 */
/*
 * get_rel_all_updated_cols - (中文)返回某关系被本查询更新的全部列集合
 *
 * 【作用】仅用于 UPDATE 查询:返回关系 rel(必须是简单关系)中被本查询
 * 更新(含其依赖的生成列)的全部列号位图。供权限检查、行约束处理等处使用。
 *
 * 【设计思想】updatedCols 的权威来源是 resultRelation 对应 RTEPermissionInfo
 * 的 updatedCols 位图(记录查询直接 SET 的列)。若 rel 不是 resultRelation
 * (即某个继承叶子),则用 translate_col_privs_multilevel 把该位图逐级翻译
 * 到 rel 的列号(translate_col_privs 会把父的整行引用展开为全部继承列)。
 * 最后用 get_dependent_generated_columns 查出依赖于这些列的计算列,并并入
 * 结果。注意列号位图以 FirstLowInvalidHeapAttributeNumber 作偏移,系统列
 * 也在其中。
 *
 * 【参数】
 *   root —— 规划上下文;rel —— 目标"简单"关系(基表或其它关系)。
 * 【返回值】被更新列号位图(含依赖的生成列)。
 */
Bitmapset *
get_rel_all_updated_cols(PlannerInfo *root, RelOptInfo *rel)
{
	Index		relid;
	RangeTblEntry *rte;
	RTEPermissionInfo *perminfo;
	Bitmapset  *updatedCols,
			   *extraUpdatedCols;

	Assert(root->parse->commandType == CMD_UPDATE);
	Assert(IS_SIMPLE_REL(rel));

	/*
	 * We obtain updatedCols for the query's result relation.  Then, if
	 * necessary, we map it to the column numbers of the relation for which
	 * they were requested.
	 */
	relid = root->parse->resultRelation;
	rte = planner_rt_fetch(relid, root);
	perminfo = getRTEPermissionInfo(root->parse->rteperminfos, rte);

	updatedCols = perminfo->updatedCols;

	if (rel->relid != relid)
	{
		RelOptInfo *top_parent_rel = find_base_rel(root, relid);

		Assert(IS_OTHER_REL(rel));

		updatedCols = translate_col_privs_multilevel(root, rel, top_parent_rel,
													 updatedCols);
	}

	/*
	 * Now we must check to see if there are any generated columns that depend
	 * on the updatedCols, and add them to the result.
	 */
	extraUpdatedCols = get_dependent_generated_columns(root, rel->relid,
													   updatedCols);

	return bms_union(updatedCols, extraUpdatedCols);
}

/*
 * translate_col_privs
 *	  Translate a bitmapset representing per-column privileges from the
 *	  parent rel's attribute numbering to the child's.
 *
 * The only surprise here is that we don't translate a parent whole-row
 * reference into a child whole-row reference.  That would mean requiring
 * permissions on all child columns, which is overly strict, since the
 * query is really only going to reference the inherited columns.  Instead
 * we set the per-column bits for all inherited columns.
 */
/*
 * translate_col_privs - (中文)把父表的列权限位图翻译成子表的列权限位图
 *
 * 【作用】将父关系上的"按列权限/更新列"位图(parent_privs,列号按
 * FirstLowInvalidHeapAttributeNumber 偏移)按 translated_vars 翻译成子表的
 * 对应位图。系统列号在父子表中一致,直接透传;普通列按 Var 的 varattno
 * 映射;父表的整行引用不翻译为子表的整行引用(那会要求对所有子列都有权限,
 * 过于严格),而是展开为全部继承列的逐列位。
 *
 * 【设计思想】系统列先原样复制(attno 负值段,列号相等即权限相等);然后
 * 检查父表是否有整行引用(InvalidAttrNumber 位)。对 translated_vars 逐项
 * 遍历:跳过 NULL(父表已删列,无权限语义);若父位图含整行位或含该父列位,
 * 就把子表对应列的位(mapped varattno)加入结果。子表多出的列(父列号为 0
 * 的翻译项)不可能出现在结果中,因为它们没有对应父列。
 *
 * 【参数】
 *   parent_privs   —— 父表的列权限位图;
 *   translated_vars —— 该父子对的翻译列表(AppendRelInfo.translated_vars)。
 * 【返回值】翻译后的子表列权限位图。
 */
static Bitmapset *
translate_col_privs(const Bitmapset *parent_privs,
					List *translated_vars)
{
	Bitmapset  *child_privs = NULL;
	bool		whole_row;
	int			attno;
	ListCell   *lc;

	/* System attributes have the same numbers in all tables */
	for (attno = FirstLowInvalidHeapAttributeNumber + 1; attno < 0; attno++)
	{
		if (bms_is_member(attno - FirstLowInvalidHeapAttributeNumber,
						  parent_privs))
			child_privs = bms_add_member(child_privs,
										 attno - FirstLowInvalidHeapAttributeNumber);
	}

	/* Check if parent has whole-row reference */
	whole_row = bms_is_member(InvalidAttrNumber - FirstLowInvalidHeapAttributeNumber,
							  parent_privs);

	/* And now translate the regular user attributes, using the vars list */
	attno = InvalidAttrNumber;
	foreach(lc, translated_vars)
	{
		Var		   *var = lfirst_node(Var, lc);

		attno++;
		if (var == NULL)		/* ignore dropped columns */
			continue;
		if (whole_row ||
			bms_is_member(attno - FirstLowInvalidHeapAttributeNumber,
						  parent_privs))
			child_privs = bms_add_member(child_privs,
										 var->varattno - FirstLowInvalidHeapAttributeNumber);
	}

	return child_privs;
}

/*
 * translate_col_privs_multilevel
 *		Recursively translates the column numbers contained in 'parent_cols'
 *		to the column numbers of a descendant relation given by 'rel'
 *
 * Note that because this is based on translate_col_privs, it will expand
 * a whole-row reference into all inherited columns.  This is not an issue
 * for current usages, but beware.
 */
/*
 * translate_col_privs_multilevel - (中文)跨多级继承翻译列号位图
 *
 * 【作用】把顶层父表上的列号位图(parent_cols)翻译到后代关系 rel 的列号。
 * 沿 rel->parent 链自底向上递归,逐级调用 translate_col_privs。
 *
 * 【设计思想】与其它 multilevel 翻译函数同样的递归模式:rel 的立即父不是
 * 顶层父时,先递归把位图翻译到立即父,再用该层的 AppendRelInfo 翻译到 rel。
 * parent_cols 为空时快速返回 NULL。
 *
 * 【参数】
 *   root        —— 规划上下文;rel —— 目标后代关系;
 *   parent_rel  —— 顶层父关系;parent_cols —— 顶层父表的列号位图。
 * 【返回值】翻译到 rel 的列号位图。
 */
static Bitmapset *
translate_col_privs_multilevel(PlannerInfo *root, RelOptInfo *rel,
							   RelOptInfo *parent_rel,
							   Bitmapset *parent_cols)
{
	AppendRelInfo *appinfo;

	/* Fast path for easy case. */
	if (parent_cols == NULL)
		return NULL;

	/* Recurse if immediate parent is not the top parent. */
	if (rel->parent != parent_rel)
	{
		if (rel->parent)
			parent_cols = translate_col_privs_multilevel(root, rel->parent,
														 parent_rel,
														 parent_cols);
		else
			elog(ERROR, "rel with relid %u is not a child rel", rel->relid);
	}

	/* Now translate for this child. */
	Assert(root->append_rel_array != NULL);
	appinfo = root->append_rel_array[rel->relid];
	Assert(appinfo != NULL);

	return translate_col_privs(parent_cols, appinfo->translated_vars);
}

/*
 * expand_appendrel_subquery
 *		Add "other rel" RelOptInfos for the children of an appendrel baserel
 *
 * "rel" is a subquery relation that has the rte->inh flag set, meaning it
 * is a UNION ALL subquery that's been flattened into an appendrel, with
 * child subqueries listed in root->append_rel_list.  We need to build
 * a RelOptInfo for each child relation so that we can plan scans on them.
 */
/*
 * expand_appendrel_subquery - (中文)为被展平的 UNION ALL 子查询建 RelOptInfo
 *
 * 【作用】当 rel 是一个带 inh 标志的子查询 RTE(即 UNION ALL 集合的父)时,
 * 为它的每个子查询(其 RTE 与 AppendRelInfo 已在 subquery_planner 阶段造好)
 * 构建 RelOptInfo,以便后续可对每个子查询规划扫描路径。
 *
 * 【设计思想】父与子的关系已由 root->append_rel_list 中的 AppendRelInfo
 * 表达(并非本函数创建),这里只需遍历该列表、筛出 parent_relid == rti 的
 * 条目,用 build_simple_rel 为 child_relid 建 RelOptInfo。子查询自身仍可能
 * 是继承/分区的 UNION ALL 成员(childrte->inh),此时递归调用
 * expand_inherited_rtentry 继续展开。
 *
 * 【参数】
 *   root —— 规划上下文;rel —— 父(子查询)RelOptInfo;
 *   rte  —— 父 RTE;rti —— 父 RTE 下标。
 * 【返回值】无。
 */
static void
expand_appendrel_subquery(PlannerInfo *root, RelOptInfo *rel,
						  RangeTblEntry *rte, Index rti)
{
	ListCell   *l;

	foreach(l, root->append_rel_list)
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) lfirst(l);
		Index		childRTindex = appinfo->child_relid;
		RangeTblEntry *childrte;
		RelOptInfo *childrel;

		/* append_rel_list contains all append rels; ignore others */
		if (appinfo->parent_relid != rti)
			continue;

		/* find the child RTE, which should already exist */
		Assert(childRTindex < root->simple_rel_array_size);
		childrte = root->simple_rte_array[childRTindex];
		Assert(childrte != NULL);

		/* Build the child RelOptInfo. */
		childrel = build_simple_rel(root, childRTindex, rel);

		/* Child may itself be an inherited rel, either table or subquery. */
		if (childrte->inh)
			expand_inherited_rtentry(root, childrel, childrte, childRTindex);
	}
}


/*
 * apply_child_basequals
 *		Populate childrel's base restriction quals from parent rel's quals,
 *		translating them using appinfo.
 *
 * If any of the resulting clauses evaluate to constant false or NULL, we
 * return false and don't apply any quals.  Caller should mark the relation as
 * a dummy rel in this case, since it doesn't need to be scanned.  Constant
 * true quals are ignored.
 */
/*
 * apply_child_basequals - (中文)把父关系的限制条件翻译分发到子关系
 *
 * 【作用】把父关系 parentrel 的 baserestrictinfo 中每个限制条件用
 * appendrel 翻译成子关系版本,并做常量折叠,得到子关系的 baserestrictinfo。
 * 任一条件折叠成常量 false 或 NULL(即子表不可能有满足条件的行)时立即返回
 * false,调用方据此把该子表标记为 dummy(不需要扫描)——这正是约束排除/
 * 分区裁剪的逻辑基础。常量 true 条件被丢弃。
 *
 * 【设计思想】逐条 RestrictInfo 独立处理,原因有二:其一,子表 reltarget
 * 可能含非 Var 表达式,翻译后的条件可能暴露出常量折叠或伪常量子句的机会,
 * 必须分别变换求值;其二,要保持每个条件的 security_level 以便排序。每条
 * 条件流程:adjust_appendrel_attrs 翻译 → eval_const_expressions 折叠 →
 * 常量判定(假/空 → 整体失败;真 → 跳过)→ make_ands_implicit 展开 AND
 * → 逐个子句判伪常量(无 Var 且无易变函数,若有则置 root->hasPseudoConstantQuals
 * 让 createplan 生成 gating quals)→ make_restrictinfo 重建(继承父条件的
 * is_pushed_down / has_clone / is_clone / security_level)。另外,子表 RTE
 * 自身的 securityQuals(目前仅 UNION ALL 子查询会有)也要并入,安全等级从
 * 0 递增分配。最后把结果与最小安全等级写入 childrel。
 *
 * 【参数】
 *   root      —— 规划上下文;parentrel —— 父(appendrel 父)关系;
 *   childrel  —— 待填充的子关系;childRTE —— 子关系的 RTE;
 *   appinfo   —— 该父子对的 AppendRelInfo。
 * 【返回值】true 表示成功应用了子表限制条件;false 表示有条件是常量假/空,
 * 调用方应把子关系标记为 dummy。
 */
bool
apply_child_basequals(PlannerInfo *root, RelOptInfo *parentrel,
					  RelOptInfo *childrel, RangeTblEntry *childRTE,
					  AppendRelInfo *appinfo)
{
	List	   *childquals;
	Index		cq_min_security;
	ListCell   *lc;

	/*
	 * The child rel's targetlist might contain non-Var expressions, which
	 * means that substitution into the quals could produce opportunities for
	 * const-simplification, and perhaps even pseudoconstant quals. Therefore,
	 * transform each RestrictInfo separately to see if it reduces to a
	 * constant or pseudoconstant.  (We must process them separately to keep
	 * track of the security level of each qual.)
	 */
	childquals = NIL;
	cq_min_security = UINT_MAX;
	foreach(lc, parentrel->baserestrictinfo)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
		Node	   *childqual;
		ListCell   *lc2;

		Assert(IsA(rinfo, RestrictInfo));
		childqual = adjust_appendrel_attrs(root,
										   (Node *) rinfo->clause,
										   1, &appinfo);
		childqual = eval_const_expressions(root, childqual);
		/* check for flat-out constant */
		if (childqual && IsA(childqual, Const))
		{
			if (((Const *) childqual)->constisnull ||
				!DatumGetBool(((Const *) childqual)->constvalue))
			{
				/* Restriction reduces to constant FALSE or NULL */
				return false;
			}
			/* Restriction reduces to constant TRUE, so drop it */
			continue;
		}
		/* might have gotten an AND clause, if so flatten it */
		foreach(lc2, make_ands_implicit((Expr *) childqual))
		{
			Node	   *onecq = (Node *) lfirst(lc2);
			bool		pseudoconstant;
			RestrictInfo *childrinfo;

			/* check for pseudoconstant (no Vars or volatile functions) */
			pseudoconstant =
				!contain_vars_of_level(onecq, 0) &&
				!contain_volatile_functions(onecq);
			if (pseudoconstant)
			{
				/* tell createplan.c to check for gating quals */
				root->hasPseudoConstantQuals = true;
			}
			/* reconstitute RestrictInfo with appropriate properties */
			childrinfo = make_restrictinfo(root,
										   (Expr *) onecq,
										   rinfo->is_pushed_down,
										   rinfo->has_clone,
										   rinfo->is_clone,
										   pseudoconstant,
										   rinfo->security_level,
										   NULL, NULL, NULL);

			childquals = lappend(childquals, childrinfo);
			/* track minimum security level among child quals */
			cq_min_security = Min(cq_min_security, childrinfo->security_level);
		}
	}

	/*
	 * In addition to the quals inherited from the parent, we might have
	 * securityQuals associated with this particular child node.  (Currently
	 * this can only happen in appendrels originating from UNION ALL;
	 * inheritance child tables don't have their own securityQuals, see
	 * expand_single_inheritance_child().)  Pull any such securityQuals up
	 * into the baserestrictinfo for the child.  This is similar to
	 * process_security_barrier_quals() for the parent rel, except that we
	 * can't make any general deductions from such quals, since they don't
	 * hold for the whole appendrel.
	 */
	if (childRTE->securityQuals)
	{
		Index		security_level = 0;

		foreach(lc, childRTE->securityQuals)
		{
			List	   *qualset = (List *) lfirst(lc);
			ListCell   *lc2;

			foreach(lc2, qualset)
			{
				Expr	   *qual = (Expr *) lfirst(lc2);

				/* not likely that we'd see constants here, so no check */
				childquals = lappend(childquals,
									 make_restrictinfo(root, qual,
													   true,
													   false, false,
													   false,
													   security_level,
													   NULL, NULL, NULL));
				cq_min_security = Min(cq_min_security, security_level);
			}
			security_level++;
		}
		Assert(security_level <= root->qual_security_level);
	}

	/*
	 * OK, we've got all the baserestrictinfo quals for this child.
	 */
	childrel->baserestrictinfo = childquals;
	childrel->baserestrict_min_security = cq_min_security;

	return true;
}
