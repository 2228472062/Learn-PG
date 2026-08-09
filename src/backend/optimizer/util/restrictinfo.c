/*-------------------------------------------------------------------------
 *
 * restrictinfo.c
 *	  RestrictInfo node manipulation routines.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * 【模块总览(中文)】
 * 本文件提供 RestrictInfo 节点的构造与操纵例程。RestrictInfo 是规划器中
 * 最核心的"条件描述"结构:一个 WHERE/ON 子句(可能带 AND/OR 结构)经
 * 规范化后,以 RestrictInfo 的形式挂在基表的 baserestrictinfo(限制条件)
 * 或 joininfo(连接条件)列表上,并携带大量便于路径生成与代价估算的缓存
 * 信息。
 *
 * 【核心数据结构】
 * - RestrictInfo:含 clause(原始子句)、orclause(OR 子句的变形)、
 *   clause_relids / left_relids / right_relids(关系引用位图)、
 *   required_relids(计算所需关系,含外连接)、pseudoconstant、
 *   is_pushed_down、security_level / leakproof(安全与提前求值控制)、
 *   can_join(是否像普通二元连接条件)、merge/hash 相关缓存
 *   (mergeopfamilies、left/right_ec、scansel_cache、hashjoinoperator、
 *   bucketsize 等)、rinfo_serial(去重与克隆用序列号)。
 *
 * 【主要函数关系】
 * make_restrictinfo 是主入口,内部把 OR 子句交给 make_sub_restrictinfos
 * 递归地在每个子句上方插入 RestrictInfo,非 OR 子句则直接交给
 * make_plain_restrictinfo 完成常规字段初始化;commute_restrictinfo 交换
 * 二元子句左右操作数(用于索引派生条件);restriction_is_or_clause /
 * restriction_is_securely_promotable / rinfo_is_constant_true 是三个小型
 * 判定例程;get_actual_clauses / extract_actual_clauses /
 * extract_actual_join_clauses 从 RestrictInfo 列表提取裸子句;
 * join_clause_is_movable_to / join_clause_is_movable_into 判定连接条件
 * 能否"下推/移入"某扫描层或连接层,支撑参数化路径生成。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/restrictinfo.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/restrictinfo.h"


static Expr *make_sub_restrictinfos(PlannerInfo *root,
									Expr *clause,
									bool is_pushed_down,
									bool has_clone,
									bool is_clone,
									bool pseudoconstant,
									Index security_level,
									Relids required_relids,
									Relids incompatible_relids,
									Relids outer_relids);


/*
 * make_restrictinfo
 *
 * Build a RestrictInfo node containing the given subexpression.
 *
 * The is_pushed_down, has_clone, is_clone, and pseudoconstant flags for the
 * RestrictInfo must be supplied by the caller, as well as the correct values
 * for security_level, incompatible_relids, and outer_relids.
 * required_relids can be NULL, in which case it defaults to the actual clause
 * contents (i.e., clause_relids).
 *
 * We initialize fields that depend only on the given subexpression, leaving
 * others that depend on context (or may never be needed at all) to be filled
 * later.
 */
/*
 * make_restrictinfo - (中文)构造一个包含给定子表达式的 RestrictInfo
 *
 * 【作用】规划期构造 RestrictInfo 的总入口。若 clause 是 OR 子句,则构建
 * 一个"在每个顶层 AND/OR 结构的分支上方插入了 RestrictInfo"的修改版拷贝
 * (见 make_sub_restrictinfos);否则直接走 make_plain_restrictinfo 初始化。
 * is_pushed_down、has_clone、is_clone、pseudoconstant、security_level、
 * incompatible_relids、outer_relids 必须由调用者提供;required_relids 可
 * 为 NULL,此时默认取实际子句内容(clause_relids)。
 *
 * 【设计思想】OR 子句与普通子句在规划器中待遇不同(OR 需要能够逐分支
 * 提取限制条件,故每个分支都要有独立的 RestrictInfo 包装),因此这里按
 * 类型分流。传入的 clause 本身不会被修改,OR 情况创建的是树形拷贝。
 *
 * 【参数】
 *   root               —— 规划上下文;
 *   clause             —— 待包装的布尔表达式;
 *   is_pushed_down     —— 是否已被下推到其语义层之下;
 *   has_clone / is_clone —— 是否拥有/是"克隆"(外连接条件变体)标志;
 *   pseudoconstant     —— 是否伪常量(可在任何地方求值一次);
 *   security_level     —— 安全等级(RLS 等),决定求值顺序;
 *   required_relids    —— 计算该条件所需的最小关系集,可为 NULL;
 *   incompatible_relids —— 与其不兼容(不可同时使用)的关系集;
 *   outer_relids       —— 该条件所在的外连接相关关系集。
 * 【返回值】新建的 RestrictInfo 节点。
 */
RestrictInfo *
make_restrictinfo(PlannerInfo *root,
				  Expr *clause,
				  bool is_pushed_down,
				  bool has_clone,
				  bool is_clone,
				  bool pseudoconstant,
				  Index security_level,
				  Relids required_relids,
				  Relids incompatible_relids,
				  Relids outer_relids)
{
	/*
	 * If it's an OR clause, build a modified copy with RestrictInfos inserted
	 * above each subclause of the top-level AND/OR structure.
	 */
	if (is_orclause(clause))
		return (RestrictInfo *) make_sub_restrictinfos(root,
													   clause,
													   is_pushed_down,
													   has_clone,
													   is_clone,
													   pseudoconstant,
													   security_level,
													   required_relids,
													   incompatible_relids,
													   outer_relids);

	/* Shouldn't be an AND clause, else AND/OR flattening messed up */
	Assert(!is_andclause(clause));

	return make_plain_restrictinfo(root,
								   clause,
								   NULL,
								   is_pushed_down,
								   has_clone,
								   is_clone,
								   pseudoconstant,
								   security_level,
								   required_relids,
								   incompatible_relids,
								   outer_relids);
}

/*
 * make_plain_restrictinfo
 *
 * Common code for the main entry points and the recursive cases.  Also,
 * useful while constructing RestrictInfos above OR clause, which already has
 * RestrictInfos above its subclauses.
 */
/*
 * make_plain_restrictinfo - (中文)构造 RestrictInfo 的公共实现
 *
 * 【作用】make_restrictinfo 与 make_sub_restrictinfos 递归情况的共同实现,
 * 也用于"在已经带子 RestrictInfo 的 OR 结构上再套一层 RestrictInfo"。
 * 负责把 RestrictInfo 的全部字段初始化到位。
 *
 * 【设计思想】重点说明几个字段的初始化逻辑:
 * - can_join:纯语法判定——二元 OpExpr 且左右操作数引用不相交的非空关系
 *   集合时置真(注意这是无上下文语境的判定,是否真的能用来连接由后续
 *   阶段结合上下文决定);
 * - leakproof:security_level > 0 时才真正检测(低层条件不会被安全等级
 *   延迟,没必要测);否则置 false 表示"未知";
 * - has_volatile:置 VOLATILITY_UNKNOWN,首次需要时由
 *   contain_volatile_functions 惰性确定;
 * - required_relids 缺省取 clause_relids;
 * - num_base_rels:从 clause_relids 中剔除 outer_join_rels 后计数。这里
 *   存在一点"看起来不安全"的做法——调用发生在 deconstruct_jointree 的
 *   遍历中,outer_join_rels 正在被填充;但由于递归顺序保证"任何会被本
 *   子句提到的外连接都已被访问过",实际是安全的;
 * - 各种缓存字段(选择性、代价、merge/hash 信息)统一置"未设置"哨兵值,
 *   只有在相应上下文(如连接条件列表顶层)中才被惰性计算,避免无谓开销。
 *
 * 【参数】同 make_restrictinfo,另加 orclause —— 若本 RestrictInfo 代表
 *         一个 OR 子句,这里存放其"带子 RestrictInfo 的 OR 树"。
 * 【返回值】新建的 RestrictInfo 节点。
 */
RestrictInfo *
make_plain_restrictinfo(PlannerInfo *root,
						Expr *clause,
						Expr *orclause,
						bool is_pushed_down,
						bool has_clone,
						bool is_clone,
						bool pseudoconstant,
						Index security_level,
						Relids required_relids,
						Relids incompatible_relids,
						Relids outer_relids)
{
	RestrictInfo *restrictinfo = makeNode(RestrictInfo);
	Relids		baserels;

	restrictinfo->clause = clause;
	restrictinfo->orclause = orclause;
	restrictinfo->is_pushed_down = is_pushed_down;
	restrictinfo->pseudoconstant = pseudoconstant;
	restrictinfo->has_clone = has_clone;
	restrictinfo->is_clone = is_clone;
	restrictinfo->can_join = false; /* may get set below */
	restrictinfo->security_level = security_level;
	restrictinfo->incompatible_relids = incompatible_relids;
	restrictinfo->outer_relids = outer_relids;

	/*
	 * If it's potentially delayable by lower-level security quals, figure out
	 * whether it's leakproof.  We can skip testing this for level-zero quals,
	 * since they would never get delayed on security grounds anyway.
	 */
	if (security_level > 0)
		restrictinfo->leakproof = !contain_leaked_vars((Node *) clause);
	else
		restrictinfo->leakproof = false;	/* really, "don't know" */

	/*
	 * Mark volatility as unknown.  The contain_volatile_functions function
	 * will determine if there are any volatile functions when called for the
	 * first time with this RestrictInfo.
	 */
	restrictinfo->has_volatile = VOLATILITY_UNKNOWN;

	/*
	 * If it's a binary opclause, set up left/right relids info. In any case
	 * set up the total clause relids info.
	 */
	if (is_opclause(clause) && list_length(((OpExpr *) clause)->args) == 2)
	{
		restrictinfo->left_relids = pull_varnos(root, get_leftop(clause));
		restrictinfo->right_relids = pull_varnos(root, get_rightop(clause));

		restrictinfo->clause_relids = bms_union(restrictinfo->left_relids,
												restrictinfo->right_relids);

		/*
		 * Does it look like a normal join clause, i.e., a binary operator
		 * relating expressions that come from distinct relations? If so we
		 * might be able to use it in a join algorithm.  Note that this is a
		 * purely syntactic test that is made regardless of context.
		 */
		if (!bms_is_empty(restrictinfo->left_relids) &&
			!bms_is_empty(restrictinfo->right_relids) &&
			!bms_overlap(restrictinfo->left_relids,
						 restrictinfo->right_relids))
		{
			restrictinfo->can_join = true;
			/* pseudoconstant should certainly not be true */
			Assert(!restrictinfo->pseudoconstant);
		}
	}
	else
	{
		/* Not a binary opclause, so mark left/right relid sets as empty */
		restrictinfo->left_relids = NULL;
		restrictinfo->right_relids = NULL;
		/* and get the total relid set the hard way */
		restrictinfo->clause_relids = pull_varnos(root, (Node *) clause);
	}

	/* required_relids defaults to clause_relids */
	if (required_relids != NULL)
		restrictinfo->required_relids = required_relids;
	else
		restrictinfo->required_relids = restrictinfo->clause_relids;

	/*
	 * Count the number of base rels appearing in clause_relids.  To do this,
	 * we just delete rels mentioned in root->outer_join_rels and count the
	 * survivors.  Because we are called during deconstruct_jointree which is
	 * the same tree walk that populates outer_join_rels, this is a little bit
	 * unsafe-looking; but it should be fine because the recursion in
	 * deconstruct_jointree should already have visited any outer join that
	 * could be mentioned in this clause.
	 */
	baserels = bms_difference(restrictinfo->clause_relids,
							  root->outer_join_rels);
	restrictinfo->num_base_rels = bms_num_members(baserels);
	bms_free(baserels);

	/*
	 * Label this RestrictInfo with a fresh serial number.
	 */
	restrictinfo->rinfo_serial = ++(root->last_rinfo_serial);

	/*
	 * Fill in all the cacheable fields with "not yet set" markers. None of
	 * these will be computed until/unless needed.  Note in particular that we
	 * don't mark a binary opclause as mergejoinable or hashjoinable here;
	 * that happens only if it appears in the right context (top level of a
	 * joinclause list).
	 */
	restrictinfo->parent_ec = NULL;

	restrictinfo->eval_cost.startup = -1;
	restrictinfo->norm_selec = -1;
	restrictinfo->outer_selec = -1;

	restrictinfo->mergeopfamilies = NIL;

	restrictinfo->left_ec = NULL;
	restrictinfo->right_ec = NULL;
	restrictinfo->left_em = NULL;
	restrictinfo->right_em = NULL;
	restrictinfo->scansel_cache = NIL;

	restrictinfo->outer_is_left = false;

	restrictinfo->hashjoinoperator = InvalidOid;

	restrictinfo->left_bucketsize = -1;
	restrictinfo->right_bucketsize = -1;
	restrictinfo->left_mcvfreq = -1;
	restrictinfo->right_mcvfreq = -1;

	restrictinfo->left_hasheqoperator = InvalidOid;
	restrictinfo->right_hasheqoperator = InvalidOid;

	return restrictinfo;
}

/*
 * Recursively insert sub-RestrictInfo nodes into a boolean expression.
 *
 * We put RestrictInfos above simple (non-AND/OR) clauses and above
 * sub-OR clauses, but not above sub-AND clauses, because there's no need.
 * This may seem odd but it is closely related to the fact that we use
 * implicit-AND lists at top level of RestrictInfo lists.  Only ORs and
 * simple clauses are valid RestrictInfos.
 *
 * The same is_pushed_down, has_clone, is_clone, and pseudoconstant flag
 * values can be applied to all RestrictInfo nodes in the result.  Likewise
 * for security_level, incompatible_relids, and outer_relids.
 *
 * The given required_relids are attached to our top-level output,
 * but any OR-clause constituents are allowed to default to just the
 * contained rels.
 */
/*
 * make_sub_restrictinfos - (中文)递归地在布尔表达式的子句上方插入
 * 子 RestrictInfo
 *
 * 【作用】处理 OR 子句时的递归辅助:把 RestrictInfo 放到"简单(非 AND/OR)
 * 子句"与"子 OR 子句"之上,但不在"子 AND 子句"之上——因为顶层用
 * 隐式 AND 列表,只有 OR 和简单子句才是合法 RestrictInfo。is_pushed_down
 * 等标志对结果中所有节点一视同仁;顶层输出应用给定的 required_relids,
 * 但 OR 的分支子句允许缺省为仅含自身引用关系。
 *
 * 【设计思想】与"顶层列表是隐式 AND"的设计相呼应:AND 的每个参数本来
 * 就会各自进入列表,无需包装;OR 分支则必须各自包装成 RestrictInfo 以便
 * 独立管理。递归同时下钻 OR/AND 两层,直到简单子句。
 *
 * 【参数】同 make_restrictinfo(required_relids 语义见上述说明)。
 * 【返回值】重建后的表达式树(节点上已插入 RestrictInfo)。
 */
static Expr *
make_sub_restrictinfos(PlannerInfo *root,
					   Expr *clause,
					   bool is_pushed_down,
					   bool has_clone,
					   bool is_clone,
					   bool pseudoconstant,
					   Index security_level,
					   Relids required_relids,
					   Relids incompatible_relids,
					   Relids outer_relids)
{
	if (is_orclause(clause))
	{
		List	   *orlist = NIL;
		ListCell   *temp;

		foreach(temp, ((BoolExpr *) clause)->args)
			orlist = lappend(orlist,
							 make_sub_restrictinfos(root,
													lfirst(temp),
													is_pushed_down,
													has_clone,
													is_clone,
													pseudoconstant,
													security_level,
													NULL,
													incompatible_relids,
													outer_relids));
		return (Expr *) make_plain_restrictinfo(root,
												clause,
												make_orclause(orlist),
												is_pushed_down,
												has_clone,
												is_clone,
												pseudoconstant,
												security_level,
												required_relids,
												incompatible_relids,
												outer_relids);
	}
	else if (is_andclause(clause))
	{
		List	   *andlist = NIL;
		ListCell   *temp;

		foreach(temp, ((BoolExpr *) clause)->args)
			andlist = lappend(andlist,
							  make_sub_restrictinfos(root,
													 lfirst(temp),
													 is_pushed_down,
													 has_clone,
													 is_clone,
													 pseudoconstant,
													 security_level,
													 required_relids,
													 incompatible_relids,
													 outer_relids));
		return make_andclause(andlist);
	}
	else
		return (Expr *) make_plain_restrictinfo(root,
												clause,
												NULL,
												is_pushed_down,
												has_clone,
												is_clone,
												pseudoconstant,
												security_level,
												required_relids,
												incompatible_relids,
												outer_relids);
}

/*
 * commute_restrictinfo
 *
 * Given a RestrictInfo containing a binary opclause, produce a RestrictInfo
 * representing the commutation of that clause.  The caller must pass the
 * OID of the commutator operator (which it's presumably looked up, else
 * it would not know this is valid).
 *
 * Beware that the result shares sub-structure with the given RestrictInfo.
 * That's okay for the intended usage with derived index quals, but might
 * be hazardous if the source is subject to change.  Also notice that we
 * assume without checking that the commutator op is a member of the same
 * btree and hash opclasses as the original op.
 */
/*
 * commute_restrictinfo - (中文)生成给定二元连接条件交换操作数后的
 * RestrictInfo
 *
 * 【作用】为索引派生条件等场景,把 rinfo 中二元 OpExpr 的左右操作数交换、
 * 算子换成调用者提供的交换算子 comm_op,生成新的 RestrictInfo。调用者
 * 必须已查得 comm_op 的 OID(否则它不会知道交换是否合法)。
 *
 * 【设计思想】用 memcpy 扁平复制 clause 与 rinfo 两份结构,再修改需要变
 * 的部分,以最大化复用:
 * - 交换 opno 为 comm_op、重置 opfuncid(待重新解析)、交换 args;
 * - left/right_relids、left/right_ec、left/right_em、bucketsize/mcvfreq
 *   全部交叉互换;
 * - 缓存的选择性/代价、parent_ec、rinfo_serial 直接保留——交换后这些
 *   数值不变;
 * - scansel_cache 重置(不为它费心)、左右 hasheqoperator 复位;
 * - 若原 hashjoinoperator 正是被交换的算子,则改为 comm_op,否则置
 *   InvalidOid。
 * 警告:结果与源结构共享子结构,故源对象不能随后被修改;并假设交换算子
 * 与原算子属于同一 btree/hash 操作符类(不做检查)。
 *
 * 【参数】
 *   rinfo   —— 源连接条件(RestrictInfo,内含二元 OpExpr);
 *   comm_op —— 交换算子(commutator)的 OID。
 * 【返回值】交换后的新 RestrictInfo。
 */
RestrictInfo *
commute_restrictinfo(RestrictInfo *rinfo, Oid comm_op)
{
	RestrictInfo *result;
	OpExpr	   *newclause;
	OpExpr	   *clause = castNode(OpExpr, rinfo->clause);

	Assert(list_length(clause->args) == 2);

	/* flat-copy all the fields of clause ... */
	newclause = makeNode(OpExpr);
	memcpy(newclause, clause, sizeof(OpExpr));

	/* ... and adjust those we need to change to commute it */
	newclause->opno = comm_op;
	newclause->opfuncid = InvalidOid;
	newclause->args = list_make2(lsecond(clause->args),
								 linitial(clause->args));

	/* likewise, flat-copy all the fields of rinfo ... */
	result = makeNode(RestrictInfo);
	memcpy(result, rinfo, sizeof(RestrictInfo));

	/*
	 * ... and adjust those we need to change.  Note in particular that we can
	 * preserve any cached selectivity or cost estimates, since those ought to
	 * be the same for the new clause.  Likewise we can keep the source's
	 * parent_ec.  It's also important that we keep the same rinfo_serial.
	 */
	result->clause = (Expr *) newclause;
	result->left_relids = rinfo->right_relids;
	result->right_relids = rinfo->left_relids;
	Assert(result->orclause == NULL);
	result->left_ec = rinfo->right_ec;
	result->right_ec = rinfo->left_ec;
	result->left_em = rinfo->right_em;
	result->right_em = rinfo->left_em;
	result->scansel_cache = NIL;	/* not worth updating this */
	if (rinfo->hashjoinoperator == clause->opno)
		result->hashjoinoperator = comm_op;
	else
		result->hashjoinoperator = InvalidOid;
	result->left_bucketsize = rinfo->right_bucketsize;
	result->right_bucketsize = rinfo->left_bucketsize;
	result->left_mcvfreq = rinfo->right_mcvfreq;
	result->right_mcvfreq = rinfo->left_mcvfreq;
	result->left_hasheqoperator = InvalidOid;
	result->right_hasheqoperator = InvalidOid;

	return result;
}

/*
 * restriction_is_or_clause
 *
 * Returns t iff the restrictinfo node contains an 'or' clause.
 */
/*
 * restriction_is_or_clause - (中文)判断 RestrictInfo 是否包含 OR 子句
 *
 * 【作用】利用 orclause 字段快速判断:make_restrictinfo 在遇到 OR 子句时
 * 会为其填充 orclause 字段,非 OR 子句该字段为 NULL,故非空即真。
 *
 * 【设计思想】该字段专为此判定而设,比检查 clause 本身是否 BoolExpr 更
 * 可靠(经 make_sub_restrictinfos 处理后,顶层 RestrictInfo 的 clause 仍
 * 是原始 OR,但其 orclause 是带子包装的版本)。
 *
 * 【参数】restrictinfo —— 待检查的 RestrictInfo。
 * 【返回值】true:是 OR 子句;false:不是。
 */
bool
restriction_is_or_clause(RestrictInfo *restrictinfo)
{
	if (restrictinfo->orclause != NULL)
		return true;
	else
		return false;
}

/*
 * restriction_is_securely_promotable
 *
 * Returns true if it's okay to evaluate this clause "early", that is before
 * other restriction clauses attached to the specified relation.
 */
/*
 * restriction_is_securely_promotable - (中文)判断该条件能否"安全地提前
 * 求值"
 *
 * 【作用】决定一个限制条件能否被提到本关系其他限制条件之前执行(例如
 * 提前到扫描阶段做 TID 扫描、提前过滤等)。
 *
 * 【设计思想】安全的前提:要么本条件等级不高于该关系当前最低安全等级
 * (baserestrict_min_security)——即前面没有必须比它更早执行的更安全条件;
 * 要么本条件 leakproof(不泄露数据),即使等级较高提前求值也不违反安全。
 *
 * 【参数】
 *   restrictinfo —— 待检查条件;
 *   rel          —— 所属基表,提供 baserestrict_min_security。
 * 【返回值】true:可安全提前求值;false:不可。
 */
bool
restriction_is_securely_promotable(RestrictInfo *restrictinfo,
								   RelOptInfo *rel)
{
	/*
	 * It's okay if there are no baserestrictinfo clauses for the rel that
	 * would need to go before this one, *or* if this one is leakproof.
	 */
	if (restrictinfo->security_level <= rel->baserestrict_min_security ||
		restrictinfo->leakproof)
		return true;
	else
		return false;
}

/*
 * Detect whether a RestrictInfo's clause is constant TRUE (note that it's
 * surely of type boolean).  No such WHERE clause could survive qual
 * canonicalization, but equivclass.c may generate such RestrictInfos for
 * reasons discussed therein.  We should drop them again when creating
 * the finished plan, which is handled by the next few functions.
 */
/*
 * rinfo_is_constant_true - (中文)判断 RestrictInfo 的子句是否为常量 TRUE
 *
 * 【作用】检测 rinfo->clause 是否是"非空且为真的布尔常量"。此类 WHERE
 * 子句本不该通过限定条件规范化(qual canonicalization)存活,但
 * equivclass.c 出于其内部原因可能生成这样的 RestrictInfo,故在生成最终
 * 计划时应将其丢弃(由后续几个提取函数处理)。
 *
 * 【设计思想】纯粹是布尔常量判定的封装:IsA Const + !constisnull +
 * DatumGetBool。供 get_actual_clauses、extract_actual_clauses、
 * extract_actual_join_clauses 复用。
 *
 * 【参数】rinfo —— 待检查的 RestrictInfo。
 * 【返回值】true:子句是常量 TRUE;false:不是。
 */
static inline bool
rinfo_is_constant_true(RestrictInfo *rinfo)
{
	return IsA(rinfo->clause, Const) &&
		!((Const *) rinfo->clause)->constisnull &&
		DatumGetBool(((Const *) rinfo->clause)->constvalue);
}

/*
 * get_actual_clauses
 *
 * Returns a list containing the bare clauses from 'restrictinfo_list'.
 *
 * This is only to be used in cases where none of the RestrictInfos can
 * be pseudoconstant clauses (for instance, it's OK on indexqual lists).
 */
/*
 * get_actual_clauses - (中文)从 RestrictInfo 列表提取裸子句列表
 *
 * 【作用】返回 restrictinfo_list 中每个节点的裸子句(rinfo->clause)组成
 * 的列表。只允许在"不存在伪常量"的场合使用(如 indexqual 列表)。
 *
 * 【设计思想】逐个断言非伪常量、非常量 TRUE(恒真子句将被丢弃),直接
 * lappend 取出裸子句。用断言而非运行期检查,因为调用者已保证前置条件。
 *
 * 【参数】restrictinfo_list —— RestrictInfo 列表。
 * 【返回值】裸子句(Expr)列表。
 */
List *
get_actual_clauses(List *restrictinfo_list)
{
	List	   *result = NIL;
	ListCell   *l;

	foreach(l, restrictinfo_list)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, l);

		Assert(!rinfo->pseudoconstant);
		Assert(!rinfo_is_constant_true(rinfo));

		result = lappend(result, rinfo->clause);
	}
	return result;
}

/*
 * extract_actual_clauses
 *
 * Extract bare clauses from 'restrictinfo_list', returning either the
 * regular ones or the pseudoconstant ones per 'pseudoconstant'.
 * Constant-TRUE clauses are dropped in any case.
 */
/*
 * extract_actual_clauses - (中文)按伪常量标志提取裸子句,恒真子句一律丢弃
 *
 * 【作用】从 restrictinfo_list 中提取裸子句,按参数 pseudoconstant 决定
 * 提取"普通"还是"伪常量"子句;常量 TRUE 在任何情况下都被丢弃。
 *
 * 【设计思想】与 get_actual_clauses 的差异在于:这里允许出现伪常量,并
 * 由调用者选择提取哪一类;恒真子句(见 rinfo_is_constant_true)对执行
 * 无意义,统一剔除。
 *
 * 【参数】
 *   restrictinfo_list —— RestrictInfo 列表;
 *   pseudoconstant    —— true:只提取伪常量子句;false:只提取普通子句。
 * 【返回值】提取出的裸子句列表。
 */
List *
extract_actual_clauses(List *restrictinfo_list,
					   bool pseudoconstant)
{
	List	   *result = NIL;
	ListCell   *l;

	foreach(l, restrictinfo_list)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, l);

		if (rinfo->pseudoconstant == pseudoconstant &&
			!rinfo_is_constant_true(rinfo))
			result = lappend(result, rinfo->clause);
	}
	return result;
}

/*
 * extract_actual_join_clauses
 *
 * Extract bare clauses from 'restrictinfo_list', separating those that
 * semantically match the join level from those that were pushed down.
 * Pseudoconstant and constant-TRUE clauses are excluded from the results.
 *
 * This is only used at outer joins, since for plain joins we don't care
 * about pushed-down-ness.
 */
/*
 * extract_actual_join_clauses - (中文)把 RestrictInfo 列表拆分为"本层连接
 * 条件"与"下推条件"两组裸子句
 *
 * 【作用】仅在外连接处使用:把 restrictinfo_list 按 RINFO_IS_PUSHED_DOWN
 * 分成 joinquals(语义上属于本连接层的条件)与 otherquals(被下推到本层
 * 的条件),各自返回裸子句;伪常量与常量 TRUE 被排除在外。
 *
 * 【设计思想】对普通(内)连接我们并不关心"是否下推",故本函数只服务于
 * 外连接。joinquals 不应被标记为伪常量(有断言兜底);下推类若为伪常量
 * 或恒真则剔除。
 *
 * 【参数】
 *   restrictinfo_list —— RestrictInfo 列表;
 *   joinrelids        —— 当前连接层的关系集合,用于判定是否下推;
 *   joinquals         —— 输出:本层连接条件裸子句列表;
 *   otherquals        —— 输出:下推条件裸子句列表。
 * 【返回值】无(结果经输出参数返回)。
 */
void
extract_actual_join_clauses(List *restrictinfo_list,
							Relids joinrelids,
							List **joinquals,
							List **otherquals)
{
	ListCell   *l;

	*joinquals = NIL;
	*otherquals = NIL;

	foreach(l, restrictinfo_list)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, l);

		if (RINFO_IS_PUSHED_DOWN(rinfo, joinrelids))
		{
			if (!rinfo->pseudoconstant &&
				!rinfo_is_constant_true(rinfo))
				*otherquals = lappend(*otherquals, rinfo->clause);
		}
		else
		{
			/* joinquals shouldn't have been marked pseudoconstant */
			Assert(!rinfo->pseudoconstant);
			if (!rinfo_is_constant_true(rinfo))
				*joinquals = lappend(*joinquals, rinfo->clause);
		}
	}
}

/*
 * join_clause_is_movable_to
 *		Test whether a join clause is a safe candidate for parameterization
 *		of a scan on the specified base relation.
 *
 * A movable join clause is one that can safely be evaluated at a rel below
 * its normal semantic level (ie, its required_relids), if the values of
 * variables that it would need from other rels are provided.
 *
 * We insist that the clause actually reference the target relation; this
 * prevents undesirable movement of degenerate join clauses, and ensures
 * that there is a unique place that a clause can be moved down to.
 *
 * We cannot move an outer-join clause into the non-nullable side of its
 * outer join, as that would change the results (rows would be suppressed
 * rather than being null-extended).
 *
 * Also there must not be an outer join below the clause that would null the
 * Vars coming from the target relation.  Otherwise the clause might give
 * results different from what it would give at its normal semantic level.
 *
 * Also, the join clause must not use any relations that have LATERAL
 * references to the target relation, since we could not put such rels on
 * the outer side of a nestloop with the target relation.
 *
 * Also, we reject is_clone versions of outer-join clauses.  This has the
 * effect of preventing us from generating variant parameterized paths
 * that differ only in which outer joins null the parameterization rel(s).
 * Generating one path from the minimally-parameterized has_clone version
 * is sufficient.
 */
/*
 * join_clause_is_movable_to - (中文)判断连接条件能否被移入(用于参数化)
 * 指定基表的扫描
 *
 * 【作用】参数化路径生成的基础判定:连接条件能否安全地在其正常语义层
 * (required_relids)之下的某个基表扫描处求值,前提是它所需的其它关系变量
 * 通过参数传入。它既要求条件确实引用目标关系(保证移动有唯一去处),又
 * 要排除会改变结果的各种情况。
 *
 * 【设计思想】五个必要条件:
 * 1. 条件必须实际引用目标基表(否则是退化连接,移动无意义且不唯一);
 * 2. 不能把外连接条件移进其连接的外侧(那会把"空扩展"变成"被过滤",
 *    结果改变);
 * 3. 目标基表的 Var 不能被任何外连接置空——利用 clause_relids 已含
 *    varnullingrels 的特点,直接检查 clause_relids 与 baserel->nulling_relids
 *    是否相交。即使相交的 OJ relid 来自别的关系的 Var,也说明该条件来自
 *    那个外连接之上、本就不该下推,故不会误判;
 * 4. 条件不能使用任何"对目标关系有 LATERAL 反向引用"的关系(否则无法把
 *    它们放在以目标关系为内层的 nestloop 外侧);
 * 5. 拒绝 is_clone(克隆变体)版本的外连接条件——避免生成仅在"哪个外连接
 *    置空参数化关系"上有差异的冗余参数化路径,由最小参数化的 has_clone
 *    版本生成一条即可。
 *
 * 【参数】
 *   rinfo   —— 待判定连接条件;
 *   baserel —— 候选的目标基表。
 * 【返回值】true:可移入 baserel 扫描;false:不可。
 */
bool
join_clause_is_movable_to(RestrictInfo *rinfo, RelOptInfo *baserel)
{
	/* Clause must physically reference target rel */
	if (!bms_is_member(baserel->relid, rinfo->clause_relids))
		return false;

	/* Cannot move an outer-join clause into the join's outer side */
	if (bms_is_member(baserel->relid, rinfo->outer_relids))
		return false;

	/*
	 * Target rel's Vars must not be nulled by any outer join.  We can check
	 * this without groveling through the individual Vars by seeing whether
	 * clause_relids (which includes all such Vars' varnullingrels) includes
	 * any outer join that can null the target rel.  You might object that
	 * this could reject the clause on the basis of an OJ relid that came from
	 * some other rel's Var.  However, that would still mean that the clause
	 * came from above that outer join and shouldn't be pushed down; so there
	 * should be no false positives.
	 */
	if (bms_overlap(rinfo->clause_relids, baserel->nulling_relids))
		return false;

	/* Clause must not use any rels with LATERAL references to this rel */
	if (bms_overlap(baserel->lateral_referencers, rinfo->clause_relids))
		return false;

	/* Ignore clones, too */
	if (rinfo->is_clone)
		return false;

	return true;
}

/*
 * join_clause_is_movable_into
 *		Test whether a join clause is movable and can be evaluated within
 *		the current join context.
 *
 * currentrelids: the relids of the proposed evaluation location
 * current_and_outer: the union of currentrelids and the required_outer
 *		relids (parameterization's outer relations)
 *
 * The API would be a bit clearer if we passed the current relids and the
 * outer relids separately and did bms_union internally; but since most
 * callers need to apply this function to multiple clauses, we make the
 * caller perform the union.
 *
 * Obviously, the clause must only refer to Vars available from the current
 * relation plus the outer rels.  We also check that it does reference at
 * least one current Var, ensuring that the clause will be pushed down to
 * a unique place in a parameterized join tree.  And we check that we're
 * not pushing the clause into its outer-join outer side.
 *
 * We used to need to check that we're not pushing the clause into a lower
 * outer join's inner side.  However, now that clause_relids includes
 * references to potentially-nulling outer joins, the other tests handle that
 * concern.  If the clause references any Var coming from the inside of a
 * lower outer join, its clause_relids will mention that outer join, causing
 * the evaluability check to fail; while if it references no such Vars, the
 * references-a-target-rel check will fail.
 *
 * There's no check here equivalent to join_clause_is_movable_to's test on
 * lateral_referencers.  We assume the caller wouldn't be inquiring unless
 * it'd verified that the proposed outer rels don't have lateral references
 * to the current rel(s).  (If we are considering join paths with the outer
 * rels on the outside and the current rels on the inside, then this should
 * have been checked at the outset of such consideration; see join_is_legal
 * and the path parameterization checks in joinpath.c.)  On the other hand,
 * in join_clause_is_movable_to we are asking whether the clause could be
 * moved for some valid set of outer rels, so we don't have the benefit of
 * relying on prior checks for lateral-reference validity.
 *
 * Likewise, we don't check is_clone here: rejecting the inappropriate
 * variants of a cloned clause must be handled upstream.
 *
 * Note: if this returns true, it means that the clause could be moved to
 * this join relation, but that doesn't mean that this is the lowest join
 * it could be moved to.  Caller may need to make additional calls to verify
 * that this doesn't succeed on either of the inputs of a proposed join.
 *
 * Note: get_joinrel_parampathinfo depends on the fact that if
 * current_and_outer is NULL, this function will always return false
 * (since one or the other of the first two tests must fail).
 */
/*
 * join_clause_is_movable_into - (中文)判断连接条件能否移入给定的连接层
 * 上下文
 *
 * 【作用】在已经确定"可移"(movable)之后,再判定条件能否在指定的求值
 * 位置(当前连接层 currentrelids 及其外参数 current_and_outer)处求值。
 * 供 get_joinrel_parampathinfo 等生成参数化连接路径的代码使用。
 *
 * 【设计思想】三个必要条件:
 * 1. 可求值性:clause_relids 必须是 current_and_outer 的子集;
 * 2. 引用唯一性:条件必须至少引用一个当前层关系,保证在参数化连接树中
 *    有唯一的下推位置;
 * 3. 不得推入其外连接的外侧(currentrelids 与 outer_relids 不相交)。
 * 与 join_clause_is_movable_to 的差异:这里不再检查 LATERAL 反向引用
 * (假定调用方在考虑连接路径时已经于 join_is_legal 等处预先验证过外部
 * 关系与当前关系的 LATERAL 合法性),也不检查 is_clone(克隆变体的取舍
 * 由上游决定)。注意:返回 true 只表示"能移到本层",并不保证本层是最低
 * 可移层,调用者可能需对连接的每个输入再做检查。另外
 * get_joinrel_parampathinfo 依赖一个性质:current_and_outer 为 NULL 时
 * 本函数必返回 false。
 *
 * 【参数】
 *   rinfo             —— 待判定连接条件;
 *   currentrelids     —— 拟求值位置的关系集合;
 *   current_and_outer —— currentrelids 与 required_outer(参数化外层)的并集。
 * 【返回值】true:条件可在给定上下文求值;false:不可。
 */
bool
join_clause_is_movable_into(RestrictInfo *rinfo,
							Relids currentrelids,
							Relids current_and_outer)
{
	/* Clause must be evaluable given available context */
	if (!bms_is_subset(rinfo->clause_relids, current_and_outer))
		return false;

	/* Clause must physically reference at least one target rel */
	if (!bms_overlap(currentrelids, rinfo->clause_relids))
		return false;

	/* Cannot move an outer-join clause into the join's outer side */
	if (bms_overlap(currentrelids, rinfo->outer_relids))
		return false;

	return true;
}
