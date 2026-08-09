/*-------------------------------------------------------------------------
 *
 * appendinfo.c
 *	  Routines for mapping between append parent(s) and children
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件提供"append 父表(appendrel parent)与子表(child)之间映射"的
 * 全部例程,是继承/分区表(以及被展平的 UNION ALL 子查询)查询规划的
 * 核心支撑模块。其核心职责是:把引用父关系的表达式翻译成引用子关系
 * (或分区)的等价表达式,保证规划器中的一切操作都能在"叶子关系"上展开。
 *
 * 【核心数据结构】
 * - AppendRelInfo:记录一对父子关系的映射。关键字段包括
 *   parent_relid / child_relid(父/子 RTE 在 range table 中的下标)、
 *   parent_reltype / child_reltype(行类型 OID)、parent_reloid(父表的
 *   真实 OID,用于校验列存在性时的报错)、translated_vars(父列 → 子列
 *   的翻译列表,元素为 Var 或 NULL;NULL 表示父表中已被删除的列)、
 *   num_child_cols 与 parent_colnos(反向翻译数组:子列号 → 父列号,
 *   0 表示该子列在父表中不存在)。
 * - RowIdentityVarInfo 与 ROWID_VAR 占位 Var:为继承目标表的
 *   UPDATE/DELETE/MERGE 注册"行标识列"(如 ctid、tableoid、wholerow)。
 *   同一逻辑列被多个叶子目标关系共享时,只登记一个 RowIdentityVarInfo,
 *   由执行器据此取回要修改的行。
 *
 * 【主要函数关系】
 * make_append_rel_info 调用 make_inh_translation_list 建立翻译列表;
 * adjust_appendrel_attrs(及其 static 的 mutator)用 AppendRelInfo 把
 * 整个表达式树中的父 Var 替换为子 Var,是 apply_child_basequals、
 * set_append_rel_size 等一切子关系处理的基础;
 * adjust_appendrel_attrs_multilevel / adjust_child_relids_multilevel /
 * adjust_inherited_attnums_multilevel 负责跨多级继承的递归翻译;
 * adjust_child_relids 翻译 relid 位图;adjust_inherited_attnums 翻译
 * 列号列表;get_translated_update_targetlist 为 UPDATE 的子目标关系取
 * 翻译后的 processed_tlist;find_appinfos_by_relids 按 relid 集合查出
 * 对应的 AppendRelInfo 数组;add_row_identity_var / add_row_identity_columns /
 * distribute_row_identity_vars 构成行标识列管理三件套,支撑继承目标表的
 * UPDATE/DELETE/MERGE。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/appendinfo.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "access/sysattr.h"
#include "access/table.h"
#include "foreign/fdwapi.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/appendinfo.h"
#include "optimizer/pathnode.h"
#include "optimizer/planmain.h"
#include "parser/parsetree.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/syscache.h"


typedef struct
{
	PlannerInfo *root;
	int			nappinfos;
	AppendRelInfo **appinfos;
} adjust_appendrel_attrs_context;

static void make_inh_translation_list(Relation oldrelation,
									  Relation newrelation,
									  Index newvarno,
									  AppendRelInfo *appinfo);
static Node *adjust_appendrel_attrs_mutator(Node *node,
											adjust_appendrel_attrs_context *context);


/*
 * make_append_rel_info
 *	  Build an AppendRelInfo for the parent-child pair
 */
/*
 * make_append_rel_info - (中文)为给定的父子关系对构建 AppendRelInfo
 *
 * 【作用】创建并初始化一个 AppendRelInfo:填入父/子 RTE 下标、父/子的
 * 行类型 OID、父表真实 OID,并调用 make_inh_translation_list 建立"父列
 * → 子列"的翻译列表。调用者(如 inherit.c 的 expand_single_inheritance_child)
 * 随后把它挂到 root->append_rel_list 与 root->append_rel_array 中。
 *
 * 【设计思想】AppendRelInfo 是规划器"父子关系映射"的最小单元,一个
 * 继承/分区层级中每一对相邻父子关系各有一个。行类型 OID 用于判断"父表
 * 与子表行类型是否相同"(决定整行 Var 翻译时是否需要 ConvertRowtypeExpr),
 * parent_reloid 用于在报错时打印父表名字。本函数只负责构造,不负责注册。
 *
 * 【参数】
 *   parentrel     —— 父关系(Relation),用于取行类型与 OID;
 *   childrel      —— 子关系(Relation);
 *   parentRTindex —— 父 RTE 在 range table 中的下标;
 *   childRTindex  —— 子 RTE 在 range table 中的下标。
 * 【返回值】新建的 AppendRelInfo 节点(内存由当前内存上下文管理)。
 */
AppendRelInfo *
make_append_rel_info(Relation parentrel, Relation childrel,
					 Index parentRTindex, Index childRTindex)
{
	AppendRelInfo *appinfo = makeNode(AppendRelInfo);

	appinfo->parent_relid = parentRTindex;
	appinfo->child_relid = childRTindex;
	appinfo->parent_reltype = parentrel->rd_rel->reltype;
	appinfo->child_reltype = childrel->rd_rel->reltype;
	make_inh_translation_list(parentrel, childrel, childRTindex, appinfo);
	appinfo->parent_reloid = RelationGetRelid(parentrel);

	return appinfo;
}

/*
 * make_inh_translation_list
 *	  Build the list of translations from parent Vars to child Vars for
 *	  an inheritance child, as well as a reverse-translation array.
 *
 * The reverse-translation array has an entry for each child relation
 * column, which is either the 1-based index of the corresponding parent
 * column, or 0 if there's no match (that happens for dropped child columns,
 * as well as child columns beyond those of the parent, which are allowed in
 * traditional inheritance though not partitioning).
 *
 * For paranoia's sake, we match type/collation as well as attribute name.
 */
/*
 * make_inh_translation_list - (中文)建立父列到子列的翻译列表及反向数组
 *
 * 【作用】被 make_append_rel_info 调用,负责填满 AppendRelInfo 的两个
 * 核心字段:translated_vars(按父列序排列的列表,元素是引用子表的 Var,
 * 或 NULL)与 parent_colnos(按子列序排列的数组,元素是父列号或 0)。
 *
 * 【设计思想】父表的每个非删除列都要在子表中找到"同名且类型/排序规则
 * 一致"的列(这是传统继承的要求:同名列必须完全匹配,否则报错)。由于
 * ALTER TABLE ADD COLUMN、多继承等原因,同名列的位置在父子表中可能不
 * 一致,因此不能只按位置对齐。算法采用"投机 + 兜底"两步走:先试新表中
 * 紧跟上次命中列之后的下一列(简单情形下列顺序大多一致,可避免查系统
 * 缓存);若不符再走 syscache 按名查找。父表中已删除的列在 translated_vars
 * 里对应 NULL(子表相应位置可能仍存在列);子表多出的列在 parent_colnos
 * 中对应 0。当 oldrelation == newrelation(父表自身的"自我翻译",用于给
 * 传统继承集合中的父表自身建 RTE)时,直接按位置逐一生成 Var,无需搜索。
 *
 * 【参数】
 *   oldrelation —— 父关系;newrelation —— 子关系;
 *   newvarno    —— 生成子 Var 时使用的 varno(子 RTE 下标);
 *   appinfo     —— 待填充的 AppendRelInfo(只填翻译相关字段)。
 * 【返回值】无(appinfo 的字段被就地填充)。
 */
static void
make_inh_translation_list(Relation oldrelation, Relation newrelation,
						  Index newvarno,
						  AppendRelInfo *appinfo)
{
	List	   *vars = NIL;
	AttrNumber *pcolnos;
	TupleDesc	old_tupdesc = RelationGetDescr(oldrelation);
	TupleDesc	new_tupdesc = RelationGetDescr(newrelation);
	Oid			new_relid = RelationGetRelid(newrelation);
	int			oldnatts = old_tupdesc->natts;
	int			newnatts = new_tupdesc->natts;
	int			old_attno;
	int			new_attno = 0;

	/* Initialize reverse-translation array with all entries zero */
	appinfo->num_child_cols = newnatts;
	appinfo->parent_colnos = pcolnos =
		(AttrNumber *) palloc0(newnatts * sizeof(AttrNumber));

	for (old_attno = 0; old_attno < oldnatts; old_attno++)
	{
		Form_pg_attribute att;
		char	   *attname;
		Oid			atttypid;
		int32		atttypmod;
		Oid			attcollation;

		att = TupleDescAttr(old_tupdesc, old_attno);
		if (att->attisdropped)
		{
			/* Just put NULL into this list entry */
			vars = lappend(vars, NULL);
			continue;
		}
		attname = NameStr(att->attname);
		atttypid = att->atttypid;
		atttypmod = att->atttypmod;
		attcollation = att->attcollation;

		/*
		 * When we are generating the "translation list" for the parent table
		 * of an inheritance set, no need to search for matches.
		 */
		if (oldrelation == newrelation)
		{
			vars = lappend(vars, makeVar(newvarno,
										 (AttrNumber) (old_attno + 1),
										 atttypid,
										 atttypmod,
										 attcollation,
										 0));
			pcolnos[old_attno] = old_attno + 1;
			continue;
		}

		/*
		 * Otherwise we have to search for the matching column by name.
		 * There's no guarantee it'll have the same column position, because
		 * of cases like ALTER TABLE ADD COLUMN and multiple inheritance.
		 * However, in simple cases, the relative order of columns is mostly
		 * the same in both relations, so try the column of newrelation that
		 * follows immediately after the one that we just found, and if that
		 * fails, let syscache handle it.
		 */
		if (new_attno >= newnatts ||
			(att = TupleDescAttr(new_tupdesc, new_attno))->attisdropped ||
			strcmp(attname, NameStr(att->attname)) != 0)
		{
			HeapTuple	newtup;

			newtup = SearchSysCacheAttName(new_relid, attname);
			if (!HeapTupleIsValid(newtup))
				elog(ERROR, "could not find inherited attribute \"%s\" of relation \"%s\"",
					 attname, RelationGetRelationName(newrelation));
			new_attno = ((Form_pg_attribute) GETSTRUCT(newtup))->attnum - 1;
			Assert(new_attno >= 0 && new_attno < newnatts);
			ReleaseSysCache(newtup);

			att = TupleDescAttr(new_tupdesc, new_attno);
		}

		/* Found it, check type and collation match */
		if (atttypid != att->atttypid || atttypmod != att->atttypmod)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_COLUMN_DEFINITION),
					 errmsg("attribute \"%s\" of relation \"%s\" does not match parent's type",
							attname, RelationGetRelationName(newrelation))));
		if (attcollation != att->attcollation)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_COLUMN_DEFINITION),
					 errmsg("attribute \"%s\" of relation \"%s\" does not match parent's collation",
							attname, RelationGetRelationName(newrelation))));

		vars = lappend(vars, makeVar(newvarno,
									 (AttrNumber) (new_attno + 1),
									 atttypid,
									 atttypmod,
									 attcollation,
									 0));
		pcolnos[new_attno] = old_attno + 1;
		new_attno++;
	}

	appinfo->translated_vars = vars;
}

/*
 * adjust_appendrel_attrs
 *	  Copy the specified query or expression and translate Vars referring to a
 *	  parent rel to refer to the corresponding child rel instead.  We also
 *	  update rtindexes appearing outside Vars, such as resultRelation and
 *	  jointree relids.
 *
 * Note: this is only applied after conversion of sublinks to subplans,
 * so we don't need to cope with recursion into sub-queries.
 *
 * Note: this is not hugely different from what pullup_replace_vars() does;
 * maybe we should try to fold the two routines together.
 */
/*
 * adjust_appendrel_attrs - (中文)把表达式中的父 Var 翻译成子 Var
 *
 * 【作用】对给定的表达式(或查询结构)做一份拷贝,并把其中引用父关系的
 * Var 替换成引用相应子关系/分区的表达式。这是 appendrel 处理的总入口,
 * 被 apply_child_basequals、set_append_rel_size、get_translated_update_targetlist
 * 等大量子关系处理函数调用。除 Var 外,还会调整表达式中的 relid 位图
 * (PlaceHolderVar.phrels、RestrictInfo 的若干 relids 字段等)以及
 * CurrentOfExpr.cvarno 等"引用关系下标"的字段。
 *
 * 【设计思想】本质是一次携带"多个 AppendRelInfo"上下文的深拷贝(mutator)。
 * 每个 Var 根据其 varno 在 appinfos 数组中查找对应的 AppendRelInfo:找到则
 * 换成翻译列表中的对应节点(varattno > 0 时逐列替换;varattno == 0 时对整行
 * 引用做 RowExpr / ConvertRowtypeExpr 展开);varno == ROWID_VAR 时做行标识
 * 占位符的叶子化替换;找不到则原样保留。翻译后的 Var 会清除 varnosyn /
 * varattnosyn 等语法标签(它是生成列),并合并 var->varnullingrels(子 Var
 * 可能已带 nullingrel 位,不能丢)。RestrictInfo、PathTarget、RelAggInfo 等
 * 节点携带大量派生缓存(选择率、代价等),必须复制后把派生字段复位、只对
 * 逻辑字段做翻译。注意:sublink 在调用本函数之前必须已经变成 subplan,所以
 * 无需递归进子查询。
 *
 * 【参数】
 *   root     —— 规划上下文(用于取 rtable、leaf_result_relids 等);
 *   node     —— 待翻译的表达式或节点,不会被修改;
 *   nappinfos / appinfos —— 本次要应用的父子映射数组。
 * 【返回值】翻译后的节点拷贝(与输入无共享可变部分)。
 */
Node *
adjust_appendrel_attrs(PlannerInfo *root, Node *node, int nappinfos,
					   AppendRelInfo **appinfos)
{
	adjust_appendrel_attrs_context context;

	context.root = root;
	context.nappinfos = nappinfos;
	context.appinfos = appinfos;

	/* If there's nothing to adjust, don't call this function. */
	Assert(nappinfos >= 1 && appinfos != NULL);

	/* Should never be translating a Query tree. */
	Assert(node == NULL || !IsA(node, Query));

	return adjust_appendrel_attrs_mutator(node, &context);
}

/*
 * adjust_appendrel_attrs_mutator - (中文)adjust_appendrel_attrs 的递归执行体
 *
 * 【作用】对节点树做深拷贝式的递归翻译:逐节点处理 Var、CurrentOfExpr、
 * PlaceHolderVar、RestrictInfo、RelAggInfo、PathTarget 等特殊节点,其余
 * 节点交给 expression_tree_mutator 继续递归。
 *
 * 【设计思想】按节点类型分流:
 * - Var:先处理 varlevelsup != 0 的上层引用(不动);再在 appinfos 中按
 *   varno 找映射。varattno > 0 时用 translated_vars 对应项替换并合并
 *   nullingrels;varattno == 0(整行)时,若子表有命名行类型则生成子表整行
 *   Var(必要时包 ConvertRowtypeExpr 转回父行类型),否则(通常 RECORDOID)
 *   生成 RowExpr,列名取自父 RTE 的 eref。系统列(varattno < 0)无需翻译。
 * - ROWID_VAR:在 leaf_result_relids 中确定唯一叶子目标关系,若该叶子能
 *   产生该行标识列(row_identity_vars 中登记的 rowidvar)则替换成对应 Var,
 *   否则替换成 NULL 常量;非叶子层原样保留占位符。
 * - PlaceHolderVar:先递归翻译内部表达式,再把 phrels 中的父 relid 换成
 *   子 relid(phnullingrels 不需要动,它只涉及外连接)。
 * - RestrictInfo:平拷贝全部字段后只翻译 clause/orclause 与各 relids 集,
 *   并把 scansel_cache、选择率、宽度等派生缓存全部复位(子关系上要重新
 *   计算);left_ec/right_ec 保留,因为子 Var 与父 Var 语义等价、仍属于
 *   同一个等价类。
 * - RelAggInfo / PathTarget:同样"平拷贝 + 递归翻译逻辑字段",PathTarget
 *   还要复制 sortgrouprefs 数组。
 * 另外通过断言明确禁止把本函数用在 SubLink、Query、RangeTblRef 等尚在
 * 规划前期的节点上。
 *
 * 【参数】
 *   node    —— 当前节点(可能是 NULL,直接返回 NULL);
 *   context —— 携带 root、appinfos 数组及其长度。
 * 【返回值】翻译后的节点;对 Var/整行引用等场景可能返回非 Var 节点。
 */
static Node *
adjust_appendrel_attrs_mutator(Node *node,
							   adjust_appendrel_attrs_context *context)
{
	AppendRelInfo **appinfos = context->appinfos;
	int			nappinfos = context->nappinfos;
	int			cnt;

	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) copyObject(node);
		AppendRelInfo *appinfo = NULL;

		if (var->varlevelsup != 0)
			return (Node *) var;	/* no changes needed */

		/*
		 * You might think we need to adjust var->varnullingrels, but that
		 * shouldn't need any changes.  It will contain outer-join relids,
		 * while the transformation we are making affects only baserels.
		 * Below, we just merge var->varnullingrels into the translated Var.
		 * (We must merge not just copy: the child Var could have some
		 * nullingrel bits set already, and we mustn't drop those.)
		 *
		 * If var->varnullingrels isn't empty, and the translation wouldn't be
		 * a Var, we have to fail.  One could imagine wrapping the translated
		 * expression in a PlaceHolderVar, but that won't work because this is
		 * typically used after freezing placeholders.  Fortunately, the case
		 * appears unreachable at the moment.  We can see nonempty
		 * var->varnullingrels here, but only in cases involving partitionwise
		 * joining, and in such cases the translations will always be Vars.
		 * (Non-Var translations occur only for appendrels made by flattening
		 * UNION ALL subqueries.)  Should we need to make this work in future,
		 * a possible fix is to mandate that prepjointree.c create PHVs for
		 * all non-Var outputs of such subqueries, and then we could look up
		 * the pre-existing PHV here.  Or perhaps just wrap the translations
		 * that way to begin with?
		 *
		 * If var->varreturningtype is not VAR_RETURNING_DEFAULT, then that
		 * also needs to be copied to the translated Var.  That too would fail
		 * if the translation wasn't a Var, but that should never happen since
		 * a non-default var->varreturningtype is only used for Vars referring
		 * to the result relation, which should never be a flattened UNION ALL
		 * subquery.
		 */

		for (cnt = 0; cnt < nappinfos; cnt++)
		{
			if (var->varno == appinfos[cnt]->parent_relid)
			{
				appinfo = appinfos[cnt];
				break;
			}
		}

		if (appinfo)
		{
			var->varno = appinfo->child_relid;
			/* it's now a generated Var, so drop any syntactic labeling */
			var->varnosyn = 0;
			var->varattnosyn = 0;
			if (var->varattno > 0)
			{
				Node	   *newnode;

				if (var->varattno > list_length(appinfo->translated_vars))
					elog(ERROR, "attribute %d of relation \"%s\" does not exist",
						 var->varattno, get_rel_name(appinfo->parent_reloid));
				newnode = copyObject(list_nth(appinfo->translated_vars,
											  var->varattno - 1));
				if (newnode == NULL)
					elog(ERROR, "attribute %d of relation \"%s\" does not exist",
						 var->varattno, get_rel_name(appinfo->parent_reloid));
				if (IsA(newnode, Var))
				{
					Var		   *newvar = (Var *) newnode;

					newvar->varreturningtype = var->varreturningtype;
					newvar->varnullingrels = bms_add_members(newvar->varnullingrels,
															 var->varnullingrels);
				}
				else
				{
					if (var->varreturningtype != VAR_RETURNING_DEFAULT)
						elog(ERROR, "failed to apply returningtype to a non-Var");
					if (var->varnullingrels != NULL)
						elog(ERROR, "failed to apply nullingrels to a non-Var");
				}
				return newnode;
			}
			else if (var->varattno == 0)
			{
				/*
				 * Whole-row Var: if we are dealing with named rowtypes, we
				 * can use a whole-row Var for the child table plus a coercion
				 * step to convert the tuple layout to the parent's rowtype.
				 * Otherwise we have to generate a RowExpr.
				 */
				if (OidIsValid(appinfo->child_reltype))
				{
					Assert(var->vartype == appinfo->parent_reltype);
					if (appinfo->parent_reltype != appinfo->child_reltype)
					{
						ConvertRowtypeExpr *r = makeNode(ConvertRowtypeExpr);

						r->arg = (Expr *) var;
						r->resulttype = appinfo->parent_reltype;
						r->convertformat = COERCE_IMPLICIT_CAST;
						r->location = -1;
						/* Make sure the Var node has the right type ID, too */
						var->vartype = appinfo->child_reltype;
						return (Node *) r;
					}
				}
				else
				{
					/*
					 * Build a RowExpr containing the translated variables.
					 *
					 * In practice var->vartype will always be RECORDOID here,
					 * so we need to come up with some suitable column names.
					 * We use the parent RTE's column names.
					 *
					 * Note: we can't get here for inheritance cases, so there
					 * is no need to worry that translated_vars might contain
					 * some dummy NULLs.
					 */
					RowExpr    *rowexpr;
					List	   *fields;
					RangeTblEntry *rte;

					rte = rt_fetch(appinfo->parent_relid,
								   context->root->parse->rtable);
					fields = copyObject(appinfo->translated_vars);
					rowexpr = makeNode(RowExpr);
					rowexpr->args = fields;
					rowexpr->row_typeid = var->vartype;
					rowexpr->row_format = COERCE_IMPLICIT_CAST;
					rowexpr->colnames = copyObject(rte->eref->colnames);
					rowexpr->location = -1;

					if (var->varreturningtype != VAR_RETURNING_DEFAULT)
						elog(ERROR, "failed to apply returningtype to a non-Var");
					if (var->varnullingrels != NULL)
						elog(ERROR, "failed to apply nullingrels to a non-Var");

					return (Node *) rowexpr;
				}
			}
			/* system attributes don't need any other translation */
		}
		else if (var->varno == ROWID_VAR)
		{
			/*
			 * If it's a ROWID_VAR placeholder, see if we've reached a leaf
			 * target rel, for which we can translate the Var to a specific
			 * instantiation.  We should never be asked to translate to a set
			 * of relids containing more than one leaf target rel, so the
			 * answer will be unique.  If we're still considering non-leaf
			 * inheritance levels, return the ROWID_VAR Var as-is.
			 */
			Relids		leaf_result_relids = context->root->leaf_result_relids;
			Index		leaf_relid = 0;

			for (cnt = 0; cnt < nappinfos; cnt++)
			{
				if (bms_is_member(appinfos[cnt]->child_relid,
								  leaf_result_relids))
				{
					if (leaf_relid)
						elog(ERROR, "cannot translate to multiple leaf relids");
					leaf_relid = appinfos[cnt]->child_relid;
				}
			}

			if (leaf_relid)
			{
				RowIdentityVarInfo *ridinfo = (RowIdentityVarInfo *)
					list_nth(context->root->row_identity_vars, var->varattno - 1);

				if (bms_is_member(leaf_relid, ridinfo->rowidrels))
				{
					/* Substitute the Var given in the RowIdentityVarInfo */
					var = copyObject(ridinfo->rowidvar);
					/* ... but use the correct relid */
					var->varno = leaf_relid;
					/* identity vars shouldn't have nulling rels */
					Assert(var->varnullingrels == NULL);
					/* varnosyn in the RowIdentityVarInfo is probably wrong */
					var->varnosyn = 0;
					var->varattnosyn = 0;
				}
				else
				{
					/*
					 * This leaf rel can't return the desired value, so
					 * substitute a NULL of the correct type.
					 */
					return (Node *) makeNullConst(var->vartype,
												  var->vartypmod,
												  var->varcollid);
				}
			}
		}
		return (Node *) var;
	}
	if (IsA(node, CurrentOfExpr))
	{
		CurrentOfExpr *cexpr = (CurrentOfExpr *) copyObject(node);

		for (cnt = 0; cnt < nappinfos; cnt++)
		{
			AppendRelInfo *appinfo = appinfos[cnt];

			if (cexpr->cvarno == appinfo->parent_relid)
			{
				cexpr->cvarno = appinfo->child_relid;
				break;
			}
		}
		return (Node *) cexpr;
	}
	if (IsA(node, PlaceHolderVar))
	{
		/* Copy the PlaceHolderVar node with correct mutation of subnodes */
		PlaceHolderVar *phv;

		phv = (PlaceHolderVar *) expression_tree_mutator(node,
														 adjust_appendrel_attrs_mutator,
														 context);
		/* now fix PlaceHolderVar's relid sets */
		if (phv->phlevelsup == 0)
		{
			phv->phrels = adjust_child_relids(phv->phrels,
											  nappinfos, appinfos);
			/* as above, we needn't touch phnullingrels */
		}
		return (Node *) phv;
	}
	/* Shouldn't need to handle planner auxiliary nodes here */
	Assert(!IsA(node, SpecialJoinInfo));
	Assert(!IsA(node, AppendRelInfo));
	Assert(!IsA(node, PlaceHolderInfo));
	Assert(!IsA(node, MinMaxAggInfo));

	/*
	 * We have to process RestrictInfo nodes specially.  (Note: although
	 * set_append_rel_pathlist will hide RestrictInfos in the parent's
	 * baserestrictinfo list from us, it doesn't hide those in joininfo.)
	 */
	if (IsA(node, RestrictInfo))
	{
		RestrictInfo *oldinfo = (RestrictInfo *) node;
		RestrictInfo *newinfo = makeNode(RestrictInfo);

		/* Copy all flat-copiable fields, notably including rinfo_serial */
		memcpy(newinfo, oldinfo, sizeof(RestrictInfo));

		/* Recursively fix the clause itself */
		newinfo->clause = (Expr *)
			adjust_appendrel_attrs_mutator((Node *) oldinfo->clause, context);

		/* and the modified version, if an OR clause */
		newinfo->orclause = (Expr *)
			adjust_appendrel_attrs_mutator((Node *) oldinfo->orclause, context);

		/* adjust relid sets too */
		newinfo->clause_relids = adjust_child_relids(oldinfo->clause_relids,
													 context->nappinfos,
													 context->appinfos);
		newinfo->required_relids = adjust_child_relids(oldinfo->required_relids,
													   context->nappinfos,
													   context->appinfos);
		newinfo->outer_relids = adjust_child_relids(oldinfo->outer_relids,
													context->nappinfos,
													context->appinfos);
		newinfo->left_relids = adjust_child_relids(oldinfo->left_relids,
												   context->nappinfos,
												   context->appinfos);
		newinfo->right_relids = adjust_child_relids(oldinfo->right_relids,
													context->nappinfos,
													context->appinfos);

		/*
		 * Reset cached derivative fields, since these might need to have
		 * different values when considering the child relation.  Note we
		 * don't reset left_ec/right_ec: each child variable is implicitly
		 * equivalent to its parent, so still a member of the same EC if any.
		 */
		newinfo->eval_cost.startup = -1;
		newinfo->norm_selec = -1;
		newinfo->outer_selec = -1;
		newinfo->left_em = NULL;
		newinfo->right_em = NULL;
		newinfo->scansel_cache = NIL;
		newinfo->left_bucketsize = -1;
		newinfo->right_bucketsize = -1;
		newinfo->left_mcvfreq = -1;
		newinfo->right_mcvfreq = -1;

		return (Node *) newinfo;
	}

	/*
	 * We have to process RelAggInfo nodes specially.
	 */
	if (IsA(node, RelAggInfo))
	{
		RelAggInfo *oldinfo = (RelAggInfo *) node;
		RelAggInfo *newinfo = makeNode(RelAggInfo);

		newinfo->target = (PathTarget *)
			adjust_appendrel_attrs_mutator((Node *) oldinfo->target,
										   context);

		newinfo->agg_input = (PathTarget *)
			adjust_appendrel_attrs_mutator((Node *) oldinfo->agg_input,
										   context);

		newinfo->group_clauses = oldinfo->group_clauses;

		newinfo->group_exprs = (List *)
			adjust_appendrel_attrs_mutator((Node *) oldinfo->group_exprs,
										   context);

		return (Node *) newinfo;
	}

	/*
	 * We have to process PathTarget nodes specially.
	 */
	if (IsA(node, PathTarget))
	{
		PathTarget *oldtarget = (PathTarget *) node;
		PathTarget *newtarget = makeNode(PathTarget);

		/* Copy all flat-copiable fields */
		memcpy(newtarget, oldtarget, sizeof(PathTarget));

		newtarget->exprs = (List *)
			adjust_appendrel_attrs_mutator((Node *) oldtarget->exprs,
										   context);

		if (oldtarget->sortgrouprefs)
		{
			Size		nbytes = list_length(oldtarget->exprs) * sizeof(Index);

			newtarget->sortgrouprefs = (Index *) palloc(nbytes);
			memcpy(newtarget->sortgrouprefs, oldtarget->sortgrouprefs, nbytes);
		}

		return (Node *) newtarget;
	}

	/*
	 * NOTE: we do not need to recurse into sublinks, because they should
	 * already have been converted to subplans before we see them.
	 */
	Assert(!IsA(node, SubLink));
	Assert(!IsA(node, Query));
	/* We should never see these Query substructures, either. */
	Assert(!IsA(node, RangeTblRef));
	Assert(!IsA(node, JoinExpr));

	return expression_tree_mutator(node, adjust_appendrel_attrs_mutator, context);
}

/*
 * adjust_appendrel_attrs_multilevel
 *	  Apply Var translations from an appendrel parent down to a child.
 *
 * Replace Vars in the "node" expression that reference "parentrel" with
 * the appropriate Vars for "childrel".  childrel can be more than one
 * inheritance level removed from parentrel.
 */
/*
 * adjust_appendrel_attrs_multilevel - (中文)跨多级继承翻译父引用到子引用
 *
 * 【作用】把表达式中引用 parentrel 的 Var 翻译成引用 childrel 的 Var。
 * childrel 可以是距离 parentrel 任意层级的后代(例如祖父 → 子)。先沿
 * childrel->parent 链递归到顶层,再逐级调用 adjust_appendrel_attrs 应用
 * 每一层的翻译。
 *
 * 【设计思想】多级继承(分区套分区,或传统继承嵌套)下,父子映射是一棵树。
 * 本函数沿"child → ... → parent"的自底向上递归,每层取该层父子对应的
 * AppendRelInfo(find_appinfos_by_relids),完成一层的 Var 替换后再进入更
 * 高层,直到最顶层。这样每次翻译的目标都恰好是"上一层映射中的父",保证
 * 各层翻译可正确串接。若 childrel->parent 为 NULL 却又要向上走,说明调用
 * 参数错误,直接 elog。
 *
 * 【参数】
 *   root      —— 规划上下文;
 *   node      —— 待翻译的表达式;
 *   childrel  —— 目标子关系;parentrel —— 被替换掉的顶层父关系。
 * 【返回值】翻译后的节点拷贝。
 */
Node *
adjust_appendrel_attrs_multilevel(PlannerInfo *root, Node *node,
								  RelOptInfo *childrel,
								  RelOptInfo *parentrel)
{
	AppendRelInfo **appinfos;
	int			nappinfos;

	/* Recurse if immediate parent is not the top parent. */
	if (childrel->parent != parentrel)
	{
		if (childrel->parent)
			node = adjust_appendrel_attrs_multilevel(root, node,
													 childrel->parent,
													 parentrel);
		else
			elog(ERROR, "childrel is not a child of parentrel");
	}

	/* Now translate for this child. */
	appinfos = find_appinfos_by_relids(root, childrel->relids, &nappinfos);

	node = adjust_appendrel_attrs(root, node, nappinfos, appinfos);

	pfree(appinfos);

	return node;
}

/*
 * Substitute child relids for parent relids in a Relid set.  The array of
 * appinfos specifies the substitutions to be performed.
 */
/*
 * adjust_child_relids - (中文)把 relid 位图里的父 relid 换成子 relid
 *
 * 【作用】遍历 appinfos 数组:凡位图中含某条映射的 parent_relid,就把它
 * 从位图删掉并加入对应的 child_relid。用于翻译 RestrictInfo 的 relids
 * 位图、PlaceHolderVar.phrels 等"关系引用集合"。返回新位图,若没有任何
 * 替换发生则返回原位图本身。
 *
 * 【设计思想】只做"删父加子"的原地映射,不做合并;多条映射的父 relid
 * 彼此不同,处理顺序无关紧要。位图是不可变共享结构,所以一旦需要修改就
 * 必须 bms_copy 再改,避免污染其他引用者;没有改动时直接返回输入指针以
 * 省去拷贝。调用方(adjust_appendrel_attrs_mutator 等)负责 pfree 或复用。
 *
 * 【参数】
 *   relids   —— 输入 relid 位图(不可变);
 *   nappinfos / appinfos —— 父子映射数组。
 * 【返回值】替换后的位图;若无替换则为原位图(与输入指针相同)。
 */
Relids
adjust_child_relids(Relids relids, int nappinfos, AppendRelInfo **appinfos)
{
	Bitmapset  *result = NULL;
	int			cnt;

	for (cnt = 0; cnt < nappinfos; cnt++)
	{
		AppendRelInfo *appinfo = appinfos[cnt];

		/* Remove parent, add child */
		if (bms_is_member(appinfo->parent_relid, relids))
		{
			/* Make a copy if we are changing the set. */
			if (!result)
				result = bms_copy(relids);

			result = bms_del_member(result, appinfo->parent_relid);
			result = bms_add_member(result, appinfo->child_relid);
		}
	}

	/* If we made any changes, return the modified copy. */
	if (result)
		return result;

	/* Otherwise, return the original set without modification. */
	return relids;
}

/*
 * Substitute child's relids for parent's relids in a Relid set.
 * The childrel can be multiple inheritance levels below the parent.
 */
/*
 * adjust_child_relids_multilevel - (中文)跨多级继承翻译 relid 位图
 *
 * 【作用】把 relids 位图中属于 parentrel 的 relid 翻译成 childrel 的
 * relid,支持任意层级。是 adjust_appendrel_attrs_multilevel 的位图版本。
 *
 * 【设计思想】与 adjust_appendrel_attrs_multilevel 相同的自底向上递归:
 * 逐级调用 adjust_child_relids。位图可能完全不含父 relid,此时加一个快速
 * 判定(bms_overlap)直接原样返回,避免不必要的递归和拷贝。
 *
 * 【参数】
 *   root      —— 规划上下文;
 *   relids    —— 输入位图;
 *   childrel  —— 目标子关系;parentrel —— 顶层父关系。
 * 【返回值】翻译后的位图;若无需翻译则原样返回输入。
 */
Relids
adjust_child_relids_multilevel(PlannerInfo *root, Relids relids,
							   RelOptInfo *childrel,
							   RelOptInfo *parentrel)
{
	AppendRelInfo **appinfos;
	int			nappinfos;

	/*
	 * If the given relids set doesn't contain any of the parent relids, it
	 * will remain unchanged.
	 */
	if (!bms_overlap(relids, parentrel->relids))
		return relids;

	/* Recurse if immediate parent is not the top parent. */
	if (childrel->parent != parentrel)
	{
		if (childrel->parent)
			relids = adjust_child_relids_multilevel(root, relids,
													childrel->parent,
													parentrel);
		else
			elog(ERROR, "childrel is not a child of parentrel");
	}

	/* Now translate for this child. */
	appinfos = find_appinfos_by_relids(root, childrel->relids, &nappinfos);

	relids = adjust_child_relids(relids, nappinfos, appinfos);

	pfree(appinfos);

	return relids;
}

/*
 * adjust_inherited_attnums
 *	  Translate an integer list of attribute numbers from parent to child.
 */
/*
 * adjust_inherited_attnums - (中文)把父列号列表翻译成子列号列表
 *
 * 【作用】对传入的父表列号(attnum)列表,利用 AppendRelInfo 的
 * translated_vars 逐一查出每个父列在子表中的对应列号,返回新列表。
 * 仅用于传统继承(UPDATE 的列集合从父结果关系映射到各叶子),断言要求
 * context->parent_reloid 有效以排除 UNION ALL。
 *
 * 【设计思想】列号翻译只对"普通列"有效:translated_vars 中的元素必须是
 * Var(映射后要取其 varattno),否则说明该父列在子表不可用,报错。遍历时
 * 对越界列号、NULL 翻译项、非 Var 翻译项一律报"属性不存在"错误。注意
 * 系统列(varattno <= 0)不经过此函数。
 *
 * 【参数】
 *   attnums —— 父表列号列表(List of int);
 *   context —— 该父子对的 AppendRelInfo。
 * 【返回值】子表列号列表(List of int),长度与输入相同。
 */
List *
adjust_inherited_attnums(List *attnums, AppendRelInfo *context)
{
	List	   *result = NIL;
	ListCell   *lc;

	/* This should only happen for an inheritance case, not UNION ALL */
	Assert(OidIsValid(context->parent_reloid));

	/* Look up each attribute in the AppendRelInfo's translated_vars list */
	foreach(lc, attnums)
	{
		AttrNumber	parentattno = lfirst_int(lc);
		Var		   *childvar;

		/* Look up the translation of this column: it must be a Var */
		if (parentattno <= 0 ||
			parentattno > list_length(context->translated_vars))
			elog(ERROR, "attribute %d of relation \"%s\" does not exist",
				 parentattno, get_rel_name(context->parent_reloid));
		childvar = (Var *) list_nth(context->translated_vars, parentattno - 1);
		if (childvar == NULL || !IsA(childvar, Var))
			elog(ERROR, "attribute %d of relation \"%s\" does not exist",
				 parentattno, get_rel_name(context->parent_reloid));

		result = lappend_int(result, childvar->varattno);
	}
	return result;
}

/*
 * adjust_inherited_attnums_multilevel
 *	  As above, but traverse multiple inheritance levels as needed.
 */
/*
 * adjust_inherited_attnums_multilevel - (中文)跨多级继承翻译列号列表
 *
 * 【作用】adjust_inherited_attnums 的多级版本:给定子目标关系 relid 与
 * 顶层父关系 relid,把父列号列表沿继承链逐级翻译到最底层子表。
 *
 * 【设计思想】与前面多级翻译函数相同的"自底向上递归"模式,但递归路径
 * 由 root->append_rel_array 直接索引(child_relid 数组槽位存的就是指向
 * 其直接父的 AppendRelInfo),无需遍历 RelOptInfo 链。逐级调用单级版本
 * adjust_inherited_attnums 完成列号映射。
 *
 * 【参数】
 *   root            —— 规划上下文;
 *   attnums         —— 父表列号列表;
 *   child_relid     —— 目标(最底层)子关系 RTE 下标;
 *   top_parent_relid —— 顶层父关系 RTE 下标。
 * 【返回值】翻译到 child_relid 的列号列表。
 */
List *
adjust_inherited_attnums_multilevel(PlannerInfo *root, List *attnums,
									Index child_relid, Index top_parent_relid)
{
	AppendRelInfo *appinfo = root->append_rel_array[child_relid];

	if (!appinfo)
		elog(ERROR, "child rel %d not found in append_rel_array", child_relid);

	/* Recurse if immediate parent is not the top parent. */
	if (appinfo->parent_relid != top_parent_relid)
		attnums = adjust_inherited_attnums_multilevel(root, attnums,
													  appinfo->parent_relid,
													  top_parent_relid);

	/* Now translate for this child */
	return adjust_inherited_attnums(attnums, appinfo);
}

/*
 * get_translated_update_targetlist
 *	  Get the processed_tlist of an UPDATE query, translated as needed to
 *	  match a child target relation.
 *
 * Optionally also return the list of target column numbers translated
 * to this target relation.  (The resnos in processed_tlist MUST NOT be
 * relied on for this purpose.)
 */
/*
 * get_translated_update_targetlist - (中文)取翻译到子目标关系的 UPDATE 目标列表
 *
 * 【作用】为 UPDATE 查询取回某目标关系 relid 的 processed_tlist;若 relid
 * 不是 resultRelation(即继承的叶子目标表),则先做多级 Var 翻译,并顺带把
 * update_colnos(被更新列号列表)也翻译到该关系。仅在 root->parse->commandType
 * 为 CMD_UPDATE 时才有意义。
 *
 * 【设计思想】继承 UPDATE 的每个叶子目标表都要独立执行"读取旧行 → 修改 →
 * 写回",因此需要把父结果关系的目标列表展开到各叶子。非继承情形直接浅拷贝
 * processed_tlist 与 update_colnos(供调用方安全改写);继承情形调用
 * adjust_appendrel_attrs_multilevel 与 adjust_inherited_attnums_multilevel
 * 做两级翻译。注意 processed_tlist 中的 resno 不可靠(它反映父表的列号),
 * 取"该表更新了哪些列"必须用 update_colnos。
 *
 * 【参数】
 *   root            —— 规划上下文;
 *   relid           —— 目标关系 RTE 下标;
 *   processed_tlist —— 输出参数:翻译后的目标列表;
 *   update_colnos   —— 可选输出参数:翻译后的被更新列号列表。
 * 【返回值】无(通过输出参数返回)。
 */
void
get_translated_update_targetlist(PlannerInfo *root, Index relid,
								 List **processed_tlist, List **update_colnos)
{
	/* This is pretty meaningless for commands other than UPDATE. */
	Assert(root->parse->commandType == CMD_UPDATE);
	if (relid == root->parse->resultRelation)
	{
		/*
		 * Non-inheritance case, so it's easy.  The caller might be expecting
		 * a tree it can scribble on, though, so copy.
		 */
		*processed_tlist = copyObject(root->processed_tlist);
		if (update_colnos)
			*update_colnos = copyObject(root->update_colnos);
	}
	else
	{
		Assert(bms_is_member(relid, root->all_result_relids));
		*processed_tlist = (List *)
			adjust_appendrel_attrs_multilevel(root,
											  (Node *) root->processed_tlist,
											  find_base_rel(root, relid),
											  find_base_rel(root, root->parse->resultRelation));
		if (update_colnos)
			*update_colnos =
				adjust_inherited_attnums_multilevel(root, root->update_colnos,
													relid,
													root->parse->resultRelation);
	}
}

/*
 * find_appinfos_by_relids
 * 		Find AppendRelInfo structures for base relations listed in relids.
 *
 * The relids argument is typically a join relation's relids, which can
 * include outer-join RT indexes in addition to baserels.  We silently
 * ignore the outer joins.
 *
 * The AppendRelInfos are returned in an array, which can be pfree'd by the
 * caller. *nappinfos is set to the number of entries in the array.
 */
/*
 * find_appinfos_by_relids - (中文)按 relid 集合查找 AppendRelInfo 数组
 *
 * 【作用】给定一个 relid 位图(通常是某个 join 关系的 relids,可能同时含
 * 基础关系与外连接 RTI),返回其中每个基础关系对应的 AppendRelInfo 组成的
 * 数组,并在 *nappinfos 中给出条目数。
 *
 * 【设计思想】利用 root->append_rel_array 的"RTE 下标 → AppendRelInfo"
 * 直接索引,逐个取出位图成员的映射。对外连接 RTI 静默跳过(它们没有
 * AppendRelInfo,也不该有);对"确为基本关系但数组里没有条目"的情况(理论
 * 上只可能是代码错误)报错。数组大小按位图成员数申请,必然足够。
 *
 * 【参数】
 *   root      —— 规划上下文;
 *   relids    —— 待查找的 relid 位图;
 *   nappinfos —— 输出参数:数组条目数。
 * 【返回值】palloc 分配的 AppendRelInfo 数组,调用方负责 pfree。
 */
AppendRelInfo **
find_appinfos_by_relids(PlannerInfo *root, Relids relids, int *nappinfos)
{
	AppendRelInfo **appinfos;
	int			cnt = 0;
	int			i;

	/* Allocate an array that's certainly big enough */
	appinfos = palloc_array(AppendRelInfo *, bms_num_members(relids));

	i = -1;
	while ((i = bms_next_member(relids, i)) >= 0)
	{
		AppendRelInfo *appinfo = root->append_rel_array[i];

		if (!appinfo)
		{
			/* Probably i is an OJ index, but let's check */
			if (find_base_rel_ignore_join(root, i) == NULL)
				continue;
			/* It's a base rel, but we lack an append_rel_array entry */
			elog(ERROR, "child rel %d not found in append_rel_array", i);
		}

		appinfos[cnt++] = appinfo;
	}
	*nappinfos = cnt;
	return appinfos;
}


/*****************************************************************************
 *
 *		ROW-IDENTITY VARIABLE MANAGEMENT
 *
 * This code lacks a good home, perhaps.  We choose to keep it here because
 * adjust_appendrel_attrs_mutator() is its principal co-conspirator.  That
 * function does most of what is needed to expand ROWID_VAR Vars into the
 * right things.
 *
 *****************************************************************************/

/*
 * add_row_identity_var
 *	  Register a row-identity column to be used in UPDATE/DELETE/MERGE.
 *
 * The Var must be equal(), aside from varno, to any other row-identity
 * column with the same rowid_name.  Thus, for example, "wholerow"
 * row identities had better use vartype == RECORDOID.
 *
 * rtindex is currently redundant with rowid_var->varno, but we specify
 * it as a separate parameter in case this is ever generalized to support
 * non-Var expressions.  (We could reasonably handle expressions over
 * Vars of the specified rtindex, but for now that seems unnecessary.)
 */
/*
 * add_row_identity_var - (中文)为 UPDATE/DELETE/MERGE 注册一个行标识列
 *
 * 【作用】登记目标关系 rtindex 需要的一列"行标识"(如 ctid、tableoid、
 * wholerow)。同一逻辑行标识列若被多个叶子目标表需要,则共享同一个
 * RowIdentityVarInfo,并确保它出现在 processed_tlist 中供执行器使用。
 *
 * 【设计思想】非继承情形(rtindex 就是 resultRelation)简单:把原 Var 直接
 * 作为 junk TargetEntry 追加到 processed_tlist。继承情形则要把 Var 的
 * varno 统一改写为 ROWID_VAR 占位符(仅改 varno,其余字段不变,使不同叶子
 * 表对同一逻辑列的 Var 可以 equal() 匹配),然后在 root->row_identity_vars
 * 里按 rowid_name 查找已有条目:找到且 Var 相等则仅把 rtindex 加入
 * rowidrels 位图;找到但 Var 不等(同名列却不同含义)报错;找不到则新建
 * RowIdentityVarInfo 并把 varattno 改为列表下标,这样执行器/展开阶段可用
 * varattno 索引回 row_identity_vars。占位 Var 本身也作为 junk TLE 加入
 * processed_tlist,之后由 adjust_appendrel_attrs_mutator 的 ROWID_VAR 分支
 * 展开成各叶子的具体取值。
 *
 * 【参数】
 *   root       —— 规划上下文;
 *   orig_var   —— 表示该行标识列的 Var(varno 必须等于 rtindex);
 *   rtindex    —— 需要该列的目标关系 RTE 下标;
 *   rowid_name —— 行标识列的名字("ctid"/"wholerow"/"tableoid" 等)。
 * 【返回值】无。
 */
void
add_row_identity_var(PlannerInfo *root, Var *orig_var,
					 Index rtindex, const char *rowid_name)
{
	TargetEntry *tle;
	Var		   *rowid_var;
	RowIdentityVarInfo *ridinfo;
	ListCell   *lc;

	/* For now, the argument must be just a Var of the given rtindex */
	Assert(IsA(orig_var, Var));
	Assert(orig_var->varno == rtindex);
	Assert(orig_var->varlevelsup == 0);
	Assert(orig_var->varnullingrels == NULL);

	/*
	 * If we're doing non-inherited UPDATE/DELETE/MERGE, there's little need
	 * for ROWID_VAR shenanigans.  Just shove the presented Var into the
	 * processed_tlist, and we're done.
	 */
	if (rtindex == root->parse->resultRelation)
	{
		tle = makeTargetEntry((Expr *) orig_var,
							  list_length(root->processed_tlist) + 1,
							  pstrdup(rowid_name),
							  true);
		root->processed_tlist = lappend(root->processed_tlist, tle);
		return;
	}

	/*
	 * Otherwise, rtindex should reference a leaf target relation that's being
	 * added to the query during expand_inherited_rtentry().
	 */
	Assert(bms_is_member(rtindex, root->leaf_result_relids));
	Assert(root->append_rel_array[rtindex] != NULL);

	/*
	 * We have to find a matching RowIdentityVarInfo, or make one if there is
	 * none.  To allow using equal() to match the vars, change the varno to
	 * ROWID_VAR, leaving all else alone.
	 */
	rowid_var = copyObject(orig_var);
	/* This could eventually become ChangeVarNodes() */
	rowid_var->varno = ROWID_VAR;

	/* Look for an existing row-id column of the same name */
	foreach(lc, root->row_identity_vars)
	{
		ridinfo = (RowIdentityVarInfo *) lfirst(lc);
		if (strcmp(rowid_name, ridinfo->rowidname) != 0)
			continue;
		if (equal(rowid_var, ridinfo->rowidvar))
		{
			/* Found a match; we need only record that rtindex needs it too */
			ridinfo->rowidrels = bms_add_member(ridinfo->rowidrels, rtindex);
			return;
		}
		else
		{
			/* Ooops, can't handle this */
			elog(ERROR, "conflicting uses of row-identity name \"%s\"",
				 rowid_name);
		}
	}

	/* No request yet, so add a new RowIdentityVarInfo */
	ridinfo = makeNode(RowIdentityVarInfo);
	ridinfo->rowidvar = copyObject(rowid_var);
	/* for the moment, estimate width using just the datatype info */
	ridinfo->rowidwidth = get_typavgwidth(exprType((Node *) rowid_var),
										  exprTypmod((Node *) rowid_var));
	ridinfo->rowidname = pstrdup(rowid_name);
	ridinfo->rowidrels = bms_make_singleton(rtindex);

	root->row_identity_vars = lappend(root->row_identity_vars, ridinfo);

	/* Change rowid_var into a reference to this row_identity_vars entry */
	rowid_var->varattno = list_length(root->row_identity_vars);

	/* Push the ROWID_VAR reference variable into processed_tlist */
	tle = makeTargetEntry((Expr *) rowid_var,
						  list_length(root->processed_tlist) + 1,
						  pstrdup(rowid_name),
						  true);
	root->processed_tlist = lappend(root->processed_tlist, tle);
}

/*
 * add_row_identity_columns
 *
 * This function adds the row identity columns needed by the core code.
 * FDWs might call add_row_identity_var() for themselves to add nonstandard
 * columns.  (Duplicate requests are fine.)
 */
/*
 * add_row_identity_columns - (中文)为核心代码注册目标关系所需的行标识列
 *
 * 【作用】根据目标关系的 relkind 为 UPDATE/DELETE/MERGE 的目标关系注册
 * 必需的"行标识列":
 * - 普通表 / 物化视图 / 分区表:注册 ctid(executor 靠它定位要改的行);
 * - 外表:让 FDW 通过 AddForeignUpdateTargets 回调自行追加,并且对 UPDATE
 *   或存在行级触发器的情况再注册一个 wholerow 整行引用(executor 需要完整
 *   新行来组装,触发器需要旧行)。
 * 重复注册是无害的(add_row_identity_var 会去重)。
 *
 * 【设计思想】CTID 是本地表的物理行指针,是"改哪一行"的最可靠依据;
 * 外表没有 CTID,只能依赖 FDW 自定义标识(通常是行主键)与整行数据。
 * wholerow 之所以仅在 UPDATE/触发器时注册,是因为 DELETE 只需定位,而
 * UPDATE 必须取回未被修改的列才能拼出完整新元组;行触发器(无论前后)也
 * 需要旧整行。
 *
 * 【参数】
 *   root            —— 规划上下文;
 *   rtindex         —— 目标关系 RTE 下标;
 *   target_rte      —— 该 RTE;target_relation —— 已打开的关系。
 * 【返回值】无。
 */
void
add_row_identity_columns(PlannerInfo *root, Index rtindex,
						 RangeTblEntry *target_rte,
						 Relation target_relation)
{
	CmdType		commandType = root->parse->commandType;
	char		relkind = target_relation->rd_rel->relkind;
	Var		   *var;

	Assert(commandType == CMD_UPDATE || commandType == CMD_DELETE || commandType == CMD_MERGE);

	if (relkind == RELKIND_RELATION ||
		relkind == RELKIND_MATVIEW ||
		relkind == RELKIND_PARTITIONED_TABLE)
	{
		/*
		 * Emit CTID so that executor can find the row to merge, update or
		 * delete.
		 */
		var = makeVar(rtindex,
					  SelfItemPointerAttributeNumber,
					  TIDOID,
					  -1,
					  InvalidOid,
					  0);
		add_row_identity_var(root, var, rtindex, "ctid");
	}
	else if (relkind == RELKIND_FOREIGN_TABLE)
	{
		/*
		 * Let the foreign table's FDW add whatever junk TLEs it wants.
		 */
		FdwRoutine *fdwroutine;

		fdwroutine = GetFdwRoutineForRelation(target_relation, false);

		if (fdwroutine->AddForeignUpdateTargets != NULL)
			fdwroutine->AddForeignUpdateTargets(root, rtindex,
												target_rte, target_relation);

		/*
		 * For UPDATE, we need to make the FDW fetch unchanged columns by
		 * asking it to fetch a whole-row Var.  That's because the top-level
		 * targetlist only contains entries for changed columns, but
		 * ExecUpdate will need to build the complete new tuple.  (Actually,
		 * we only really need this in UPDATEs that are not pushed to the
		 * remote side, but it's hard to tell if that will be the case at the
		 * point when this function is called.)
		 *
		 * We will also need the whole row if there are any row triggers, so
		 * that the executor will have the "old" row to pass to the trigger.
		 * Alas, this misses system columns.
		 */
		if (commandType == CMD_UPDATE ||
			(target_relation->trigdesc &&
			 (target_relation->trigdesc->trig_delete_after_row ||
			  target_relation->trigdesc->trig_delete_before_row)))
		{
			var = makeVar(rtindex,
						  InvalidAttrNumber,
						  RECORDOID,
						  -1,
						  InvalidOid,
						  0);
			add_row_identity_var(root, var, rtindex, "wholerow");
		}
	}
}

/*
 * distribute_row_identity_vars
 *
 * After we have finished identifying all the row identity columns
 * needed by an inherited UPDATE/DELETE/MERGE query, make sure that
 * these columns will be generated by all the target relations.
 *
 * This is more or less like what build_base_rel_tlists() does,
 * except that it would not understand what to do with ROWID_VAR Vars.
 * Since that function runs before inheritance relations are expanded,
 * it will never see any such Vars anyway.
 */
/*
 * distribute_row_identity_vars - (中文)把行标识列传播到所有目标关系
 *
 * 【作用】在继承 UPDATE/DELETE/MERGE 的所有行标识列确定之后,确保它们
 * 会被所有目标关系生成。非继承查询无操作;继承查询则把 processed_tlist
 * 中的 ROWID_VAR 占位 Var 拷进顶层目标关系的 reltarget,后续 appendrel
 * 展开时(set_append_rel_size)会随翻译复制到各叶子。
 *
 * 【设计思想】作用类似 build_base_rel_tlists(把 tlist 里的 Var 塞进基础
 * 关系的 reltarget),但后者不认识 ROWID_VAR 占位符;而且它在继承展开之前
 * 运行,根本看不到这类 Var,所以这里要在展开后补做。两个边界情况:
 * (1) 若约束排除把所有叶子都剪掉了,row_identity_vars 会是空的,此时
 *     重新打开顶层结果关系按非继承方式补上行标识列,并重跑
 *     build_base_rel_tlists 保证 reltarget 就绪(executor 要求计划必须带行
 *     标识列);
 * (2) 正常情况直接扫描 processed_tlist,把 varno == ROWID_VAR 的 Var 拷入
 *     顶层目标关系的 reltarget(不计算代价/宽度,留待以后)。
 *
 * 【参数】root —— 规划上下文。
 * 【返回值】无。
 */
void
distribute_row_identity_vars(PlannerInfo *root)
{
	Query	   *parse = root->parse;
	int			result_relation = parse->resultRelation;
	RangeTblEntry *target_rte;
	RelOptInfo *target_rel;
	ListCell   *lc;

	/*
	 * There's nothing to do if this isn't an inherited UPDATE/DELETE/MERGE.
	 */
	if (parse->commandType != CMD_UPDATE && parse->commandType != CMD_DELETE &&
		parse->commandType != CMD_MERGE)
	{
		Assert(root->row_identity_vars == NIL);
		return;
	}
	target_rte = rt_fetch(result_relation, parse->rtable);
	if (!target_rte->inh)
	{
		Assert(root->row_identity_vars == NIL);
		return;
	}

	/*
	 * Ordinarily, we expect that leaf result relation(s) will have added some
	 * ROWID_VAR Vars to the query.  However, it's possible that constraint
	 * exclusion suppressed every leaf relation.  The executor will get upset
	 * if the plan has no row identity columns at all, even though it will
	 * certainly process no rows.  Handle this edge case by re-opening the top
	 * result relation and adding the row identity columns it would have used,
	 * as preprocess_targetlist() would have done if it weren't marked "inh".
	 * Then re-run build_base_rel_tlists() to ensure that the added columns
	 * get propagated to the relation's reltarget.  (This is a bit ugly, but
	 * it seems better to confine the ugliness and extra cycles to this
	 * unusual corner case.)
	 */
	if (root->row_identity_vars == NIL)
	{
		Relation	target_relation;

		target_relation = table_open(target_rte->relid, NoLock);
		add_row_identity_columns(root, result_relation,
								 target_rte, target_relation);
		table_close(target_relation, NoLock);
		build_base_rel_tlists(root, root->processed_tlist);
		/* There are no ROWID_VAR Vars in this case, so we're done. */
		return;
	}

	/*
	 * Dig through the processed_tlist to find the ROWID_VAR reference Vars,
	 * and forcibly copy them into the reltarget list of the topmost target
	 * relation.  That's sufficient because they'll be copied to the
	 * individual leaf target rels (with appropriate translation) later,
	 * during appendrel expansion --- see set_append_rel_size().
	 */
	target_rel = find_base_rel(root, result_relation);

	foreach(lc, root->processed_tlist)
	{
		TargetEntry *tle = lfirst(lc);
		Var		   *var = (Var *) tle->expr;

		if (var && IsA(var, Var) && var->varno == ROWID_VAR)
		{
			target_rel->reltarget->exprs =
				lappend(target_rel->reltarget->exprs, copyObject(var));
			/* reltarget cost and width will be computed later */
		}
	}
}
