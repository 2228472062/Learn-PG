/*-------------------------------------------------------------------------
 *
 * execExpr.c
 *	  Expression evaluation infrastructure.
 *
 *	During executor startup, we compile each expression tree (which has
 *	previously been processed by the parser and planner) into an ExprState,
 *	using ExecInitExpr() et al.  This converts the tree into a flat array
 *	of ExprEvalSteps, which may be thought of as instructions in a program.
 *	At runtime, we'll execute steps, starting with the first, until we reach
 *	an EEOP_DONE_{RETURN|NO_RETURN} opcode.
 *
 *	This file contains the "compilation" logic.  It is independent of the
 *	specific execution technology we use (switch statement, computed goto,
 *	JIT compilation, etc).
 *
 *	See src/backend/executor/README for some background, specifically the
 *	"Expression Trees and ExprState nodes", "Expression Initialization",
 *	and "Expression Evaluation" sections.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execExpr.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * ============================================================================
 * 【中文注释】execExpr.c —— 表达式求值基础设施：把表达式树"编译"成可执行的步骤序列
 * ----------------------------------------------------------------------------
 * 文件定位：
 *   本文件是 PostgreSQL 执行器"表达式求值"的编译核心：执行器启动时（ExecInitExpr
 *   及其同族函数）把一棵表达式树（Expr 节点树，已经过 parser/planner 的规范化
 *   处理）编译成一个 ExprState；执行时（见 execExprInterp.c 的 ExecInterpExpr）
 *   逐条解释执行 ExprState->steps 数组中的步骤，直到遇见 EEOP_DONE_RETURN 或
 *   EEOP_DONE_NO_RETURN。本文件只负责"编译"，与具体执行技术（switch 语句、
 *   computed goto、JIT 生成机器码）完全解耦；执行技术由 ExecReadyExpr 选择。
 *
 * 核心数据结构：
 *   - ExprState：一个已编译表达式的运行时状态容器，内含 steps（ExprEvalStep
 *     数组）、resvalue/resnull（最终结果存放处）、resultslot、各种 flags，以及
 *     innermost_caseval/innermost_domainval 等编译期上下文。
 *   - ExprEvalStep：一条"指令"（如 EEOP_SCAN_VAR、EEOP_FUNCEXPR、EEOP_JUMP 等），
 *     由 opcode 与联合体 d 描述；步骤数组等价于一个简单的虚拟机程序，步骤之间
 *     通过 jumpdone 等字段实现跳转（短路求值、CASE/COALESCE 等）。
 *   - ExprSetupInfo：预扫描阶段收集的"setup 需求"——各 TupleTableSlot 需要变形
 *     （deform）到多少列，以及 MULTIEXPR 子计划列表。
 *
 * 三步构建流程：
 *   1. ExecCreateExprSetupSteps：用 expr_setup_walker 预扫描表达式，统计所有
 *      Var 引用的各槽位最大属性号并收集 MULTIEXPR SubPlan；随后
 *      ExecPushExprSetupSteps 生成 EEOP_*_FETCHSOME（元组变形）与子计划执行步骤。
 *   2. ExecInitExprRec：深度优先递归遍历表达式树，按节点类型（一个巨大的
 *      switch）把每个子表达式的求值压成相应的 ExprEvalStep 并回填跳转目标。
 *   3. ExecReadyExpr 定稿：先尝试 jit_compile_expr() 让 JIT 引擎把步骤序列编译
 *      成原生代码（成功则直接返回，状态挂 JIT 生成的执行函数），失败或未启用
 *      JIT 时回退 ExecReadyInterpretedExpr() 做解释执行准备。
 *
 * 设计思想：
 *   - "编译一次、执行多次"：编译期把可预先查到的 catalog 信息（函数 OID、类型
 *     信息、域约束集合等）直接烘焙进步骤结构，参数求值结果也下沉到 fcinfo 槽，
 *     运行时对每一元组只剩顺序执行步骤的开销（case 分发只在编译期发生一次）。
 *   - Var 读取被编译成 EEOP_*_VAR（及 SYSVAR/WHOLEROW/FETCHSOME 等）专用步骤，
 *     varno/varreturningtype 等属性在编译期就决定了读哪个槽、置哪个 flag。
 *   - 没有 ExecEndExpr：ExprState 依赖的资源统一随所属内存上下文释放，需要额外
 *     清理的函数通过 ExprContext 的 shutdown 回调完成。
 * ============================================================================
 */
#include "postgres.h"

#include "access/nbtree.h"
#include "catalog/objectaccess.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "executor/execExpr.h"
#include "executor/nodeSubplan.h"
#include "funcapi.h"
#include "jit/jit.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/subscripting.h"
#include "optimizer/optimizer.h"
#include "pgstat.h"
#include "utils/acl.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/jsonfuncs.h"
#include "utils/jsonpath.h"
#include "utils/lsyscache.h"
#include "utils/typcache.h"


typedef struct ExprSetupInfo
{
	/*
	 * Highest attribute numbers fetched from inner/outer/scan/old/new tuple
	 * slots:
	 */
	AttrNumber	last_inner;
	AttrNumber	last_outer;
	AttrNumber	last_scan;
	AttrNumber	last_old;
	AttrNumber	last_new;
	/* MULTIEXPR SubPlan nodes appearing in the expression: */
	List	   *multiexpr_subplans;
} ExprSetupInfo;

static void ExecReadyExpr(ExprState *state);
static void ExecInitExprRec(Expr *node, ExprState *state,
							Datum *resv, bool *resnull);
static void ExecInitFunc(ExprEvalStep *scratch, Expr *node, List *args,
						 Oid funcid, Oid inputcollid,
						 ExprState *state);
static void ExecInitSubPlanExpr(SubPlan *subplan,
								ExprState *state,
								Datum *resv, bool *resnull);
static void ExecCreateExprSetupSteps(ExprState *state, Node *node);
static void ExecPushExprSetupSteps(ExprState *state, ExprSetupInfo *info);
static bool expr_setup_walker(Node *node, ExprSetupInfo *info);
static bool ExecComputeSlotInfo(ExprState *state, ExprEvalStep *op);
static void ExecInitWholeRowVar(ExprEvalStep *scratch, Var *variable,
								ExprState *state);
static void ExecInitSubscriptingRef(ExprEvalStep *scratch,
									SubscriptingRef *sbsref,
									ExprState *state,
									Datum *resv, bool *resnull);
static bool isAssignmentIndirectionExpr(Expr *expr);
static void ExecInitCoerceToDomain(ExprEvalStep *scratch, CoerceToDomain *ctest,
								   ExprState *state,
								   Datum *resv, bool *resnull);
static void ExecBuildAggTransCall(ExprState *state, AggState *aggstate,
								  ExprEvalStep *scratch,
								  FunctionCallInfo fcinfo, AggStatePerTrans pertrans,
								  int transno, int setno, int setoff, bool ishash,
								  bool nullcheck);
static void ExecInitJsonExpr(JsonExpr *jsexpr, ExprState *state,
							 Datum *resv, bool *resnull,
							 ExprEvalStep *scratch);
static void ExecInitJsonCoercion(ExprState *state, JsonReturning *returning,
								 ErrorSaveContext *escontext, bool omit_quotes,
								 bool exists_coerce,
								 Datum *resv, bool *resnull);


/*
 * ============================================================================
 * 【中文注释】ExecInitExpr —— 编译一棵表达式树为可执行状态（对外主入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   将一棵（已由 parser/planner 预处理过的）Expr 节点树编译为 ExprState：内部
 *   依次完成 setup 步骤生成、表达式主体步骤生成（ExecInitExprRec 递归）以及
 *   DONE 步骤追加，最后交给 ExecReadyExpr 定稿。返回的 ExprState 可交给
 *   ExecEvalExpr（见 execExprInterp.c）反复执行。
 *
 * 参数：
 *   node   - 表达式树根；可为 NULL（此时返回 NULL，方便调用方统一处理
 *            "可能没有表达式"的场景）。
 *   parent - 拥有该表达式的 PlanState；聚合/窗口函数/子计划等节点必须登记在
 *            它的子结构上，故这些表达式的编译必须带 parent。独立表达式（无
 *            计划树）场景传 NULL，此时不允许出现聚合等，且应走 ExecPrepareExpr。
 *
 * 返回值：
 *   ExprState* - 编译结果；node 为 NULL 时返回 NULL。注意 NULL 状态不能交给
 *                ExecEvalExpr，但 ExecQual/ExecCheck 接受（当作恒真）。
 *
 * 设计思想：
 *   1. NULL 特例：翻译成 NULL 指针而非空 ExprState——条件为空是极常见场景
 *      （无过滤的扫描），让热路径直接跳过求值。
 *   2. 调用链：ExecCreateExprSetupSteps（预扫描+变形/子计划步骤）→
 *      ExecInitExprRec（按节点类型生成主体步骤）→ EEOP_DONE_RETURN 收尾 →
 *      ExecReadyExpr（JIT 或解释执行定稿）。
 *   3. 树只读、状态可复用：编译过程不修改 Expr 树，同一计划树可被多个执行器
 *      并发使用；但 ExprState 运行时是可变的（执行状态、缓存、jump 修正），
 *      不能并发复用。
 *   4. 内存上下文：调用方须保证当前上下文生命周期覆盖"反复执行"（典型是每查询
 *      上下文）；无 ExecEndExpr 即因资源回收依赖整个上下文的整体释放。
 *   5. 被调用方：ExecInitExprList、ExecInitCheck、ExecBuildUpdateProjection、
 *      各节点执行器（如 ExecInitAgg、ExecInitWindowAgg、ExecInitSubPlan 等）。
 * ============================================================================
 */
ExprState *
ExecInitExpr(Expr *node, PlanState *parent)
{
	ExprState  *state;
	ExprEvalStep scratch = {0};

	/* Special case: NULL expression produces a NULL ExprState pointer */
	if (node == NULL)
		return NULL;

	/* Initialize ExprState with empty step list */
	state = makeNode(ExprState);
	state->expr = node;
	state->parent = parent;
	state->ext_params = NULL;

	/* Insert setup steps as needed */
	ExecCreateExprSetupSteps(state, (Node *) node);

	/* Compile the expression proper */
	ExecInitExprRec(node, state, &state->resvalue, &state->resnull);

	/* Finally, append a DONE step */
	scratch.opcode = EEOP_DONE_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitExprWithParams —— 带外部参数列表的独立表达式编译
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 ExecInitExpr 相同，但没有 parent PlanState；外部参数（PARAM_EXTERN）由
 *   调用方通过 ext_params（ParamListInfo）直接提供，供编译期记录并在运行时由
 *   EEOP_PARAM_EXTERN 步骤读取。
 *
 * 参数：
 *   node       - 表达式树根（可为 NULL，返回 NULL）。
 *   ext_params - 描述 PARAM_EXTERN 参数的 ParamListInfo；可为 NULL（此时运行时
 *                按父节点 EState 的参数列表或"未提供的 NULL 参数"处理）。
 *
 * 返回值：
 *   ExprState* - 编译结果。
 *
 * 设计思想：
 *   与 ExecInitExpr 的差异只有两处：state->parent = NULL、state->ext_params 被
 *   设置。execExprInterp.c 的 ExecEvalParamExtern 正是优先读 state->ext_params，
 *   因此本入口是"脱离计划树执行带外部参数的表达式"的标准通道，被说明语言执行器
 *   （如 plpgsql 内部表达式）与扩展模块使用；有父节点的场景优先取父节点 EState
 *   的参数列表而非这里传入的 ext_params。ext_params 中的 paramCompile hook 允许
 *   参数类型自定义编译行为（如参数类型强制转换）。
 * ============================================================================
 */
ExprState *
ExecInitExprWithParams(Expr *node, ParamListInfo ext_params)
{
	ExprState  *state;
	ExprEvalStep scratch = {0};

	/* Special case: NULL expression produces a NULL ExprState pointer */
	if (node == NULL)
		return NULL;

	/* Initialize ExprState with empty step list */
	state = makeNode(ExprState);
	state->expr = node;
	state->parent = NULL;
	state->ext_params = ext_params;

	/* Insert setup steps as needed */
	ExecCreateExprSetupSteps(state, (Node *) node);

	/* Compile the expression proper */
	ExecInitExprRec(node, state, &state->resvalue, &state->resnull);

	/* Finally, append a DONE step */
	scratch.opcode = EEOP_DONE_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitQual —— 编译隐式 AND 连接词表达式（WHERE 子句专用入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把"隐式 AND"语义的 qual 列表（如 WHERE 子句的条件列表、JOIN 条件）编译成
 *   供 ExecQual 使用的 ExprState。空列表返回 NULL（恒真）；若任一子表达式为假
 *   或为 NULL，则整体为假——这正好是 SQL 对 WHERE 的语义（NULL 条件不选行）。
 *
 * 参数：
 *   qual   - 条件表达式列表（List of Expr，元素间是隐式 AND）。
 *   parent - 所属 PlanState。
 *
 * 返回值：
 *   ExprState* - NULL 表示恒真（空条件）；非 NULL 时必须用 ExecQual 执行
 *                （flags 已置 EEO_FLAG_IS_QUAL，禁止直接 ExecEvalExpr）。
 *
 * 设计思想：
 *   1. 空列表优化：翻译为 NULL 指针而非"计算恒 TRUE 的 ExprState"——无过滤的
 *      表扫描是最常见的场景，热路径调用方检测到 NULL 可干脆不调 ExecQual。
 *   2. 短路求值：每个子表达式求值后紧跟一条 EEOP_QUAL 步骤，一旦结果为假（或
 *      NULL）立即跳到整个 qual 之后，不再求值其余条件——WHERE 条件不求值是
 *      重要的性能手段，为此专门设计了比 BOOL_AND 更简单的 EEOP_QUAL opcode
 *      （它的 NULL 处理只有"返回 false"一种，无需三值逻辑）。
 *   3. 两遍填充跳转：先以 -1 占位记录步骤下标，全部子表达式编译完后统一回填
 *      jumpdone——这是本文件所有"跳转类"编译的通用模式（步骤数组可能在构建期
 *      扩容移动，不能提前取指针）。
 *   4. 结果的存放：每个子表达式的值直接落到 state->resvalue/resnull，最后一次
 *      求值结果即 qual 的最终结果，故无需额外的收尾步骤。
 *   5. 与 ExecInitCheck 的对比：CHECK 约束把 NULL 视为"通过"，走普通 AND；
 *      WHERE 把 NULL 视为"不通过"，走 EEOP_QUAL——本函数刻意为之。
 * ============================================================================
 */
ExprState *
ExecInitQual(List *qual, PlanState *parent)
{
	ExprState  *state;
	ExprEvalStep scratch = {0};
	List	   *adjust_jumps = NIL;

	/* short-circuit (here and in ExecQual) for empty restriction list */
	if (qual == NIL)
		return NULL;

	Assert(IsA(qual, List));

	state = makeNode(ExprState);
	state->expr = (Expr *) qual;
	state->parent = parent;
	state->ext_params = NULL;

	/* mark expression as to be used with ExecQual() */
	state->flags = EEO_FLAG_IS_QUAL;

	/* Insert setup steps as needed */
	ExecCreateExprSetupSteps(state, (Node *) qual);

	/*
	 * ExecQual() needs to return false for an expression returning NULL. That
	 * allows us to short-circuit the evaluation the first time a NULL is
	 * encountered.  As qual evaluation is a hot-path this warrants using a
	 * special opcode for qual evaluation that's simpler than BOOL_AND (which
	 * has more complex NULL handling).
	 */
	scratch.opcode = EEOP_QUAL;

	/*
	 * We can use ExprState's resvalue/resnull as target for each qual expr.
	 */
	scratch.resvalue = &state->resvalue;
	scratch.resnull = &state->resnull;

	foreach_ptr(Expr, node, qual)
	{
		/* first evaluate expression */
		ExecInitExprRec(node, state, &state->resvalue, &state->resnull);

		/* then emit EEOP_QUAL to detect if it's false (or null) */
		scratch.d.qualexpr.jumpdone = -1;
		ExprEvalPushStep(state, &scratch);
		adjust_jumps = lappend_int(adjust_jumps,
								   state->steps_len - 1);
	}

	/* adjust jump targets */
	foreach_int(jump, adjust_jumps)
	{
		ExprEvalStep *as = &state->steps[jump];

		Assert(as->opcode == EEOP_QUAL);
		Assert(as->d.qualexpr.jumpdone == -1);
		as->d.qualexpr.jumpdone = state->steps_len;
	}

	/*
	 * At the end, we don't need to do anything more.  The last qual expr must
	 * have yielded TRUE, and since its result is stored in the desired output
	 * location, we're done.
	 */
	scratch.opcode = EEOP_DONE_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitCheck —— 编译 CHECK 约束表达式（供 ExecCheck 执行）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 CHECK 约束（隐式 AND 列表）编译为 ExprState。与 ExecInitQual 的关键差异：
 *   当整个合取式结果为 NULL 时视为 TRUE（约束通过）——SQL 规定 NULL 约束条件
 *   不算违反，例如 CHECK (x > 0) 在 x 为 NULL 时通过。
 *
 * 参数：
 *   qual   - 隐式 AND 列表。
 *   parent - 所属 PlanState。
 *
 * 返回值：
 *   ExprState* - NULL 表示恒真；非 NULL 时用 ExecCheck 求值。
 *
 * 设计思想：
 *   实现上不自行编译，而是把隐式 AND 列表用 make_ands_explicit 展开成显式 AND
 *   的 BoolExpr（多于一项时），再交给 ExecInitExpr 走通用编译——因为 NULL 不能
 *   被短路为"失败"，必须用标准 AND 的三值逻辑（NULL AND x 的结果是 NULL）。
 *   调用方若已持有显式 AND 表达式，也可直接 ExecInitExpr 后交给 ExecCheck。
 *   主要在 ALTER TABLE ... ADD CONSTRAINT 校验、INSERT/UPDATE 时元组约束检查
 *   （heap 层经 ExecCheck 驱动）以及域类型检查之外的表级 CHECK 中使用。
 * ============================================================================
 */
ExprState *
ExecInitCheck(List *qual, PlanState *parent)
{
	/* short-circuit (here and in ExecCheck) for empty restriction list */
	if (qual == NIL)
		return NULL;

	Assert(IsA(qual, List));

	/*
	 * Just convert the implicit-AND list to an explicit AND (if there's more
	 * than one entry), and compile normally.  Unlike ExecQual, we can't
	 * short-circuit on NULL results, so the regular AND behavior is needed.
	 */
	return ExecInitExpr(make_ands_explicit(qual), parent);
}

/*
 * ============================================================================
 * 【中文注释】ExecInitExprList —— 批量编译表达式列表
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对表达式列表中的每个元素调用 ExecInitExpr，返回与输入一一对应的
 *   ExprState 列表。
 *
 * 设计思想：
 *   纯模板化遍历（foreach + lappend），保持列表顺序；供"一组并列表达式"的场景
 *   复用，如窗口函数的参数列表（ExecInitExprRec 的 T_WindowFunc 分支）等。
 *   每个元素编译成独立状态，互不影响。
 * ============================================================================
 */
List *
ExecInitExprList(List *nodes, PlanState *parent)
{
	List	   *result = NIL;
	ListCell   *lc;

	foreach(lc, nodes)
	{
		Expr	   *e = lfirst(lc);

		result = lappend(result, ExecInitExpr(e, parent));
	}

	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildProjectionInfo —— 构建"投影"执行器（tlist 求值并写入结果槽）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把一个目标列表（targetList）整体编译成一个"一步完成"的 ExprState，并用
 *   ProjectionInfo 包装：执行后结果直接写入给定 TupleTableSlot（resultslot）。
 *   调用方须保证 slot 的描述符与 tlist 一致（由调用方在建立 plan 时保证）。
 *
 * 参数：
 *   targetList - 规划器生成的 TargetEntry 列表（v10 之前此处传 ExprState 列表，
 *                现在统一在本函数内完成编译）。
 *   econtext   - 投影求值所用的表达式上下文。
 *   slot       - 结果写入的元组槽。
 *   parent     - 所属 PlanState。
 *   inputDesc  - 可为 NULL；非 NULL 时把 tlist 中的"简单 Var"与源关系描述符做
 *                相容性检查（防止计划生成后表被 ALTER 造成列错位），关系扫描类
 *                节点建议提供；上层节点无需重复检查。
 *
 * 返回值：
 *   ProjectionInfo* - 其 pi_state 内嵌 ExprState（省一次 palloc），pi_exprContext
 *                     记录执行上下文。
 *
 * 设计思想：
 *   1. 快路径：Safe Var（非系统列；有 inputDesc 时还要求列未 drop、类型匹配，
 *      无 inputDesc 时"无从校验则直接信任"）生成一条 EEOP_ASSIGN_*_VAR 步骤，
 *      一步完成取列与落位；按 varno 分派 INNER/OUTER/SCAN 槽，按
 *      varreturningtype 分派 OLD/NEW 槽（RETURNING 语义）并置相应 flag。
 *   2. 慢路径：普通表达式编译成步骤求值到 state->resvalue/resnull，再用
 *      EEOP_ASSIGN_TMP 搬到结果槽；varlena（变长，可能是可写展开对象）类型
 *      额外加 EEOP_ASSIGN_TMP_MAKE_RO 强制只读——投影结果可能被上层节点多处
 *      引用，可写对象被某处修改会破坏值语义。
 *   3. 结尾用 EEOP_DONE_NO_RETURN：结果已写进槽，无需再返回 datum。
 *   4. 运行时由 ExecProject 驱动（execUtils.c），执行器上层（各节点的
 *      ps_ProjInfo）几乎全靠它；ExecBuildUpdateProjection 是其 UPDATE 特化版。
 * ============================================================================
 */
ProjectionInfo *
ExecBuildProjectionInfo(List *targetList,
						ExprContext *econtext,
						TupleTableSlot *slot,
						PlanState *parent,
						TupleDesc inputDesc)
{
	ProjectionInfo *projInfo = makeNode(ProjectionInfo);
	ExprState  *state;
	ExprEvalStep scratch = {0};
	ListCell   *lc;

	projInfo->pi_exprContext = econtext;
	/* We embed ExprState into ProjectionInfo instead of doing extra palloc */
	projInfo->pi_state.type = T_ExprState;
	state = &projInfo->pi_state;
	state->expr = (Expr *) targetList;
	state->parent = parent;
	state->ext_params = NULL;

	state->resultslot = slot;

	/* Insert setup steps as needed */
	ExecCreateExprSetupSteps(state, (Node *) targetList);

	/* Now compile each tlist column */
	foreach(lc, targetList)
	{
		TargetEntry *tle = lfirst_node(TargetEntry, lc);
		Var		   *variable = NULL;
		AttrNumber	attnum = 0;
		bool		isSafeVar = false;

		/*
		 * If tlist expression is a safe non-system Var, use the fast-path
		 * ASSIGN_*_VAR opcodes.  "Safe" means that we don't need to apply
		 * CheckVarSlotCompatibility() during plan startup.  If a source slot
		 * was provided, we make the equivalent tests here; if a slot was not
		 * provided, we assume that no check is needed because we're dealing
		 * with a non-relation-scan-level expression.
		 */
		if (tle->expr != NULL &&
			IsA(tle->expr, Var) &&
			((Var *) tle->expr)->varattno > 0)
		{
			/* Non-system Var, but how safe is it? */
			variable = (Var *) tle->expr;
			attnum = variable->varattno;

			if (inputDesc == NULL)
				isSafeVar = true;	/* can't check, just assume OK */
			else if (attnum <= inputDesc->natts)
			{
				Form_pg_attribute attr = TupleDescAttr(inputDesc, attnum - 1);

				/*
				 * If user attribute is dropped or has a type mismatch, don't
				 * use ASSIGN_*_VAR.  Instead let the normal expression
				 * machinery handle it (which'll possibly error out).
				 */
				if (!attr->attisdropped && variable->vartype == attr->atttypid)
				{
					isSafeVar = true;
				}
			}
		}

		if (isSafeVar)
		{
			/* Fast-path: just generate an EEOP_ASSIGN_*_VAR step */
			switch (variable->varno)
			{
				case INNER_VAR:
					/* get the tuple from the inner node */
					scratch.opcode = EEOP_ASSIGN_INNER_VAR;
					break;

				case OUTER_VAR:
					/* get the tuple from the outer node */
					scratch.opcode = EEOP_ASSIGN_OUTER_VAR;
					break;

					/* INDEX_VAR is handled by default case */

				default:

					/*
					 * Get the tuple from the relation being scanned, or the
					 * old/new tuple slot, if old/new values were requested.
					 */
					switch (variable->varreturningtype)
					{
						case VAR_RETURNING_DEFAULT:
							scratch.opcode = EEOP_ASSIGN_SCAN_VAR;
							break;
						case VAR_RETURNING_OLD:
							scratch.opcode = EEOP_ASSIGN_OLD_VAR;
							state->flags |= EEO_FLAG_HAS_OLD;
							break;
						case VAR_RETURNING_NEW:
							scratch.opcode = EEOP_ASSIGN_NEW_VAR;
							state->flags |= EEO_FLAG_HAS_NEW;
							break;
					}
					break;
			}

			scratch.d.assign_var.attnum = attnum - 1;
			scratch.d.assign_var.resultnum = tle->resno - 1;
			ExprEvalPushStep(state, &scratch);
		}
		else
		{
			/*
			 * Otherwise, compile the column expression normally.
			 *
			 * We can't tell the expression to evaluate directly into the
			 * result slot, as the result slot (and the exprstate for that
			 * matter) can change between executions.  We instead evaluate
			 * into the ExprState's resvalue/resnull and then move.
			 */
			ExecInitExprRec(tle->expr, state,
							&state->resvalue, &state->resnull);

			/*
			 * Column might be referenced multiple times in upper nodes, so
			 * force value to R/O - but only if it could be an expanded datum.
			 */
			if (get_typlen(exprType((Node *) tle->expr)) == -1)
				scratch.opcode = EEOP_ASSIGN_TMP_MAKE_RO;
			else
				scratch.opcode = EEOP_ASSIGN_TMP;
			scratch.d.assign_tmp.resultnum = tle->resno - 1;
			ExprEvalPushStep(state, &scratch);
		}
	}

	scratch.opcode = EEOP_DONE_NO_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return projInfo;
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildUpdateProjection —— 构建 UPDATE 专用投影（写新值+拷回旧列）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为 UPDATE 构造"新元组"构建投影：把 targetList 的赋值表达式结果写入目标列
 *   （targetColnos 指定的列），未被赋值的旧列从"scan 槽"（UPDATE 的旧元组）拷回，
 *   被 drop 的列置 NULL，最终完整元组写入结果槽。同时执行与 ExecCheckPlanOutput
 *   等价的健全性检查——因为这里没有与"待赋整行"等价的普通 tlist，无法直接复用
 *   ExecCheckPlanOutput，只能在此手工校验。
 *
 * 参数：
 *   targetList     - UPDATE ... SET 表达式列表。
 *   evalTargetList - true：tlist 需要真正求值（表达式可引用 outer/inner/scan 槽）；
 *                    false：tlist 的值已由子计划节点算好，直接从"outer 槽"按序取。
 *   targetColnos   - 与每个非 resjunk 项一一对应的目标列号列表。
 *   relDesc        - 被更新关系的描述符。
 *   econtext / slot / parent - 同 ExecBuildProjectionInfo。
 *
 * 设计思想：
 *   1. 先校验后生成：验证 tlist 中非 resjunk 列必须连续排在 resjunk 列之前
 *      （子计划目标列表顺序约定）、targetColnos 数量与列号范围/类型/是否 drop
 *      列；用 Bitmapset 记录已赋值列以避免 list_member 的 O(N^2)。
 *   2. 赋值列求值方式与 ExecBuildProjectionInfo 不同：不搞"Safe Var"快路径
 *      （UPDATE 路径相对低频，不值得扩展开销），统一"编译 + EEOP_ASSIGN_TMP"；
 *      也不强制只读（赋值后不再被共享）。
 *   3. 变形深度：scan 槽至少要变形到"最后一个未被赋值的非 drop 旧列"；
 *      evalTargetList=false 时只需 outer 槽前 nAssignableCols 列（子计划输出
 *      恰好按此顺序排列），evalTargetList=true 时把 tlist 的 Var 需求也并入。
 *   4. 兜底列：未赋值且未 drop 的旧列按列号正序生成 EEOP_ASSIGN_SCAN_VAR 拷回
 *      （类型天然一致，无需检查）；drop 列先 EEOP_CONST(NULL) 再 ASSIGN_TMP，
 *      保证新元组的物理完整性。
 *   5. 被调用方：nodeModifyTable.c 的 ExecUpdate/ExecMerge 与 execPartition.c
 *      （分区 UPDATE/MERGE 的每条路由路径）。
 * ============================================================================
 */
ProjectionInfo *
ExecBuildUpdateProjection(List *targetList,
						  bool evalTargetList,
						  List *targetColnos,
						  TupleDesc relDesc,
						  ExprContext *econtext,
						  TupleTableSlot *slot,
						  PlanState *parent)
{
	ProjectionInfo *projInfo = makeNode(ProjectionInfo);
	ExprState  *state;
	int			nAssignableCols;
	bool		sawJunk;
	Bitmapset  *assignedCols;
	ExprSetupInfo deform = {0, 0, 0, 0, 0, NIL};
	ExprEvalStep scratch = {0};
	int			outerattnum;
	ListCell   *lc,
			   *lc2;

	projInfo->pi_exprContext = econtext;
	/* We embed ExprState into ProjectionInfo instead of doing extra palloc */
	projInfo->pi_state.type = T_ExprState;
	state = &projInfo->pi_state;
	if (evalTargetList)
		state->expr = (Expr *) targetList;
	else
		state->expr = NULL;		/* not used */
	state->parent = parent;
	state->ext_params = NULL;

	state->resultslot = slot;

	/*
	 * Examine the targetList to see how many non-junk columns there are, and
	 * to verify that the non-junk columns come before the junk ones.
	 */
	nAssignableCols = 0;
	sawJunk = false;
	foreach(lc, targetList)
	{
		TargetEntry *tle = lfirst_node(TargetEntry, lc);

		if (tle->resjunk)
			sawJunk = true;
		else
		{
			if (sawJunk)
				elog(ERROR, "subplan target list is out of order");
			nAssignableCols++;
		}
	}

	/* We should have one targetColnos entry per non-junk column */
	if (nAssignableCols != list_length(targetColnos))
		elog(ERROR, "targetColnos does not match subplan target list");

	/*
	 * Build a bitmapset of the columns in targetColnos.  (We could just use
	 * list_member_int() tests, but that risks O(N^2) behavior with many
	 * columns.)
	 */
	assignedCols = NULL;
	foreach(lc, targetColnos)
	{
		AttrNumber	targetattnum = lfirst_int(lc);

		assignedCols = bms_add_member(assignedCols, targetattnum);
	}

	/*
	 * We need to insert EEOP_*_FETCHSOME steps to ensure the input tuples are
	 * sufficiently deconstructed.  The scan tuple must be deconstructed at
	 * least as far as the last old column we need.
	 */
	for (int attnum = relDesc->natts; attnum > 0; attnum--)
	{
		CompactAttribute *attr = TupleDescCompactAttr(relDesc, attnum - 1);

		if (attr->attisdropped)
			continue;
		if (bms_is_member(attnum, assignedCols))
			continue;
		deform.last_scan = attnum;
		break;
	}

	/*
	 * If we're actually evaluating the tlist, incorporate its input
	 * requirements too; otherwise, we'll just need to fetch the appropriate
	 * number of columns of the "outer" tuple.
	 */
	if (evalTargetList)
		expr_setup_walker((Node *) targetList, &deform);
	else
		deform.last_outer = nAssignableCols;

	ExecPushExprSetupSteps(state, &deform);

	/*
	 * Now generate code to evaluate the tlist's assignable expressions or
	 * fetch them from the outer tuple, incidentally validating that they'll
	 * be of the right data type.  The checks above ensure that the forboth()
	 * will iterate over exactly the non-junk columns.  Note that we don't
	 * bother evaluating any remaining resjunk columns.
	 */
	outerattnum = 0;
	forboth(lc, targetList, lc2, targetColnos)
	{
		TargetEntry *tle = lfirst_node(TargetEntry, lc);
		AttrNumber	targetattnum = lfirst_int(lc2);
		Form_pg_attribute attr;

		Assert(!tle->resjunk);

		/*
		 * Apply sanity checks comparable to ExecCheckPlanOutput().
		 */
		if (targetattnum <= 0 || targetattnum > relDesc->natts)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("table row type and query-specified row type do not match"),
					 errdetail("Query has too many columns.")));
		attr = TupleDescAttr(relDesc, targetattnum - 1);

		if (attr->attisdropped)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("table row type and query-specified row type do not match"),
					 errdetail("Query provides a value for a dropped column at ordinal position %d.",
							   targetattnum)));
		if (exprType((Node *) tle->expr) != attr->atttypid)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("table row type and query-specified row type do not match"),
					 errdetail("Table has type %s at ordinal position %d, but query expects %s.",
							   format_type_be(attr->atttypid),
							   targetattnum,
							   format_type_be(exprType((Node *) tle->expr)))));

		/* OK, generate code to perform the assignment. */
		if (evalTargetList)
		{
			/*
			 * We must evaluate the TLE's expression and assign it.  We do not
			 * bother jumping through hoops for "safe" Vars like
			 * ExecBuildProjectionInfo does; this is a relatively less-used
			 * path and it doesn't seem worth expending code for that.
			 */
			ExecInitExprRec(tle->expr, state,
							&state->resvalue, &state->resnull);
			/* Needn't worry about read-only-ness here, either. */
			scratch.opcode = EEOP_ASSIGN_TMP;
			scratch.d.assign_tmp.resultnum = targetattnum - 1;
			ExprEvalPushStep(state, &scratch);
		}
		else
		{
			/* Just assign from the outer tuple. */
			scratch.opcode = EEOP_ASSIGN_OUTER_VAR;
			scratch.d.assign_var.attnum = outerattnum;
			scratch.d.assign_var.resultnum = targetattnum - 1;
			ExprEvalPushStep(state, &scratch);
		}
		outerattnum++;
	}

	/*
	 * Now generate code to copy over any old columns that were not assigned
	 * to, and to ensure that dropped columns are set to NULL.
	 */
	for (int attnum = 1; attnum <= relDesc->natts; attnum++)
	{
		CompactAttribute *attr = TupleDescCompactAttr(relDesc, attnum - 1);

		if (attr->attisdropped)
		{
			/* Put a null into the ExprState's resvalue/resnull ... */
			scratch.opcode = EEOP_CONST;
			scratch.resvalue = &state->resvalue;
			scratch.resnull = &state->resnull;
			scratch.d.constval.value = (Datum) 0;
			scratch.d.constval.isnull = true;
			ExprEvalPushStep(state, &scratch);
			/* ... then assign it to the result slot */
			scratch.opcode = EEOP_ASSIGN_TMP;
			scratch.d.assign_tmp.resultnum = attnum - 1;
			ExprEvalPushStep(state, &scratch);
		}
		else if (!bms_is_member(attnum, assignedCols))
		{
			/* Certainly the right type, so needn't check */
			scratch.opcode = EEOP_ASSIGN_SCAN_VAR;
			scratch.d.assign_var.attnum = attnum - 1;
			scratch.d.assign_var.resultnum = attnum - 1;
			ExprEvalPushStep(state, &scratch);
		}
	}

	scratch.opcode = EEOP_DONE_NO_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return projInfo;
}

/*
 * ============================================================================
 * 【中文注释】ExecPrepareExpr —— 独立表达式（脱离计划树）的执行准备入口
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在 EState 的查询上下文（es_query_cxt）中，先把表达式树经 expression_planner
 *   做执行前转换（常量折叠、子查询展开、规范化等），再以 parent=NULL 编译成
 *   ExprState 并返回。
 *
 * 参数：
 *   node   - 表达式树（可为 NULL，返回 NULL）。
 *   estate - 提供 es_query_cxt（编译产物所在上下文）的 EState。
 *
 * 返回值：
 *   ExprState* - 编译结果；node 为 NULL 时返回 NULL。
 *
 * 设计思想：
 *   与 ExecInitExpr 的两点差异：
 *   1. 调用方很可能不在查询上下文中执行本函数，这里显式切进 es_query_cxt，
 *      保证编译产物与查询同生命周期（依赖"无 ExecEndExpr、上下文整体释放"的
 *      资源管理约定）。
 *   2. 普通计划树中的表达式已由规划流程完成转换；但独立表达式（如触发器
 *      WHEN 条件、规则动作片段、RI 约束表达式、说明语言调用的 SQL 表达式）
 *      没有经过规划器，必须补一步 expression_planner。
 *   典型调用方：plpgsql/SPI 的表达式执行路径、ExecPrepareExprList 批量场景。
 * ============================================================================
 */
ExprState *
ExecPrepareExpr(Expr *node, EState *estate)
{
	ExprState  *result;
	MemoryContext oldcontext;

	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	node = expression_planner(node);

	result = ExecInitExpr(node, NULL);

	MemoryContextSwitchTo(oldcontext);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecPrepareQual —— 独立场景的 WHERE 条件编译入口
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在 es_query_cxt 中先对 qual 列表做 expression_planner，再调用 ExecInitQual
 *   编译为可交给 ExecQual 的 ExprState。与 ExecPrepareExpr 的关系对应
 *   ExecInitQual 与 ExecInitExpr 的关系（NULL 视为不通过、短路求值、空列表
 *   返回 NULL 恒真）。
 *
 * 参数：
 *   qual   - 隐式 AND 列表。
 *   estate - 提供 es_query_cxt 的 EState。
 *
 * 返回值：
 *   ExprState* - 编译结果（空列表为 NULL）。
 *
 * 设计思想：
 *   供脱离计划树的场景（触发器、扩展模块等）编译 WHERE 式条件；结果以
 *   EEO_FLAG_IS_QUAL 标记，运行时只能走 ExecQual。与 ExecPrepareExpr 一样
 *   负责"规划器缺失"的补课（expression_planner）与上下文切换。
 * ============================================================================
 */
ExprState *
ExecPrepareQual(List *qual, EState *estate)
{
	ExprState  *result;
	MemoryContext oldcontext;

	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	qual = (List *) expression_planner((Expr *) qual);

	result = ExecInitQual(qual, NULL);

	MemoryContextSwitchTo(oldcontext);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecPrepareCheck —— 独立场景的 CHECK 约束编译入口
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在 es_query_cxt 中先对约束表达式做 expression_planner，再调用 ExecInitCheck
 *   编译 CHECK 约束表达式。细节同 ExecPrepareExpr（规划器补课 + 上下文切换）与
 *   ExecInitCheck（NULL 视为通过）。
 *
 * 参数：
 *   qual   - 隐式 AND 列表。
 *   estate - 提供 es_query_cxt 的 EState。
 *
 * 返回值：
 *   ExprState* - 编译结果（空列表为 NULL）。
 *
 * 设计思想：
 *   CHECK 约束（CREATE TABLE/ALTER TABLE 的表级与列级约束校验、域类型约束
 *   之外的程序化约束检查）在未嵌入计划树时由本入口准备，结果交给 ExecCheck
 *   执行——NULL 结果按"约束通过"处理。典型调用方是 RI 触发器与
 *   ExecConstraints（heaptuple.c / execUtils.c 中的约束检查路径）。
 * ============================================================================
 */
ExprState *
ExecPrepareCheck(List *qual, EState *estate)
{
	ExprState  *result;
	MemoryContext oldcontext;

	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	qual = (List *) expression_planner((Expr *) qual);

	result = ExecInitCheck(qual, NULL);

	MemoryContextSwitchTo(oldcontext);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecPrepareExprList —— 批量准备独立表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对列表内每个表达式调用 ExecPrepareExpr，生成与输入一一对应的 ExprState
 *   列表；同时保证列表的 List 节点本身也分配在 es_query_cxt 中。
 *
 * 参数：
 *   nodes  - 表达式列表。
 *   estate - 提供 es_query_cxt 的 EState。
 *
 * 返回值：
 *   List* - ExprState 列表（顺序保持）。
 *
 * 设计思想：
 *   除了逐项编译，还特意把 List 及其 cell 切进查询上下文——若调用方在更短生命
 *   周期的上下文里构造列表，返回值将失去意义；这是"编译产物与其容器同上下文"
 *   原则的体现，也是 SPI/触发器等批处理场景的标准批量入口。
 * ============================================================================
 */
List *
ExecPrepareExprList(List *nodes, EState *estate)
{
	List	   *result = NIL;
	MemoryContext oldcontext;
	ListCell   *lc;

	/* Ensure that the list cell nodes are in the right context too */
	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	foreach(lc, nodes)
	{
		Expr	   *e = (Expr *) lfirst(lc);

		result = lappend(result, ExecPrepareExpr(e, estate));
	}

	MemoryContextSwitchTo(oldcontext);

	return result;
}

/*
 * ============================================================================
 * 【中文注释】ExecCheck —— 执行 CHECK 约束求值（NULL 视为通过）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对 ExprState 求值并返回布尔结果。结果（或任一中间条件）为 NULL 时一律视为
 *   true——SQL 规定 CHECK 约束的 NULL 条件不算违反，例如 CHECK (x > 0) 在
 *   x 为 NULL 时通过。
 *
 * 参数：
 *   state    - ExecInitCheck（或 ExecPrepareCheck）编译的结果；也可接收普通
 *              ExecInitExpr/ExecPrepareExpr 编译的显式 AND 布尔表达式；NULL
 *              视为恒真。不得是 ExecInitQual 编译的结果（其求值与 NULL 语义是
 *              WHERE 专用的）。
 *   econtext - 执行上下文（提供槽位绑定、参数等）。
 *
 * 返回值：
 *   bool - 约束是否通过。
 *
 * 设计思想：
 *   1. 先断言 state 未带 EEO_FLAG_IS_QUAL 标记，从机制上防止把 WHERE 语义
 *      （NULL 即不通过）误用于 CHECK 约束。
 *   2. 求值走 ExecEvalExprSwitchContext：先切到 econtext 的表达式内存上下文再
 *      执行，保证求值期间的临时分配落在正确上下文、随执行结束整体释放。
 *   3. NULL 与 false 的唯一区别在返回侧（NULL→true），故在调用侧区分即可，
 *      执行器内部无需专门的三值返回。
 *   4. 被调用方：heap 元组约束检查（ExecConstraints）、ALTER TABLE 校验、
 *      域类型检查等。
 * ============================================================================
 */
bool
ExecCheck(ExprState *state, ExprContext *econtext)
{
	Datum		ret;
	bool		isnull;

	/* short-circuit (here and in ExecInitCheck) for empty restriction list */
	if (state == NULL)
		return true;

	/* verify that expression was not compiled using ExecInitQual */
	Assert(!(state->flags & EEO_FLAG_IS_QUAL));

	ret = ExecEvalExprSwitchContext(state, econtext, &isnull);

	if (isnull)
		return true;

	return DatumGetBool(ret);
}

/*
 * ============================================================================
 * 【中文注释】ExecReadyExpr —— ExprState 定稿：选择执行技术（JIT 优先）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在步骤序列构建完成后做"定稿"：先调用 jit_compile_expr(state) 尝试用 JIT
 *   把步骤序列编译为原生代码；成功则直接返回（state->evalfunc 指向 JIT 生成的
 *   函数），失败或未启用 JIT 时回退 ExecReadyInterpretedExpr()（解释执行准备：
 *   步骤重排、预计算跳转偏移等，见 execExprInterp.c）。
 *
 * 参数：
 *   state - 已完成步骤填充、即将交付执行的 ExprState。
 *
 * 设计思想：
 *   这是"执行技术选择"的唯一切面：所有编译入口（ExecInitExpr、
 *   ExecInitExprWithParams、ExecBuildProjectionInfo、ExecBuildAggTrans、
 *   ExecBuildHash32* 等）在返回前都调用它，保证任何 ExprState 在执行前必经
 *   定稿。将来新增求值技术只需扩展此函数，各调用方零改动。
 * ============================================================================
 */
static void
ExecReadyExpr(ExprState *state)
{
	if (jit_compile_expr(state))
		return;

	ExecReadyInterpretedExpr(state);
}

/*
 * ============================================================================
 * 【中文注释】ExecInitExprRec —— 表达式编译核心递归：按节点类型生成步骤（主分发器）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   深度优先递归遍历表达式树：把 node 求值所需的步骤追加到 state->steps，并使
 *   最终结果写入调用方给定的 resv/resnull（Datum 与"是否为 NULL"的存放地址）。
 *   这是本文件的"主分发器"：除少数复杂节点转交给专门的 static 函数外，所有
 *   Expr 节点类型（Var/Const/Param/Aggref/WindowFunc/FuncExpr/OpExpr/Case/
 *   ArrayRef/RowExpr/CoerceToDomain 等三十余种）的编译逻辑都内联在本函数的
 *   switch 中。
 *
 * 参数：
 *   node    - 当前要编译的子表达式（根为整棵树时由 ExecInitExpr 传入）。
 *   state   - 正在构建的 ExprState（步骤数组、flags、innermost_caseval/
 *             innermost_domainval 等编译期上下文都挂在它上面）。
 *   resv/resnull - 本子表达式结果的存放位置；由调用方决定（可能是
 *             state->resvalue/resnull，也可能是 fcinfo 参数槽、数组元素槽、
 *             CASE 工作区等），这是"结果下沉、避免搬运"的关键设计。
 *
 * 设计思想（按节点类型分组）：
 *   1. Var 三态：varattno==0 是整行 Var（转 ExecInitWholeRowVar）；
 *      varattno<0 是系统列（xmin/ctid 等，EEOP_*_SYSVAR）；>0 是普通用户列
 *      （EEOP_*_VAR）。varno 决定从 inner/outer/scan 哪个槽取，而
 *      varreturningtype（DEFAULT/OLD/NEW）决定从 default/OLD/NEW 槽取并置
 *      EEO_FLAG_HAS_OLD/NEW（RETURNING 语义）。
 *   2. Const：常量值与是否 NULL 编译期直接烘焙成 EEOP_CONST，运行时零开销；
 *      Param：PARAM_EXEC 用 EEOP_PARAM_EXEC（按 paramid 运行时查
 *      es_param_exec_vals）；PARAM_EXTERN 优先调用 ParamListInfo 的 paramCompile
 *      hook（允许参数类型自定义编译，如扩展实现"参数化表达式"），否则用
 *      EEOP_PARAM_EXTERN 读外部参数。
 *   3. Aggref/GroupingFunc/WindowFunc：把节点登记进父 AggState 的 aggs 列表
 *      /WindowAggState 的 funcs 列表（含 WindowFuncExprState 参数预编译、嵌套
 *      窗口函数防御），生成 EEOP_AGGREF / EEOP_GROUPING_FUNC / EEOP_WINDOW_FUNC
 *      步骤；父节点不对（非 Agg/WindowAgg）直接报错——planner 出错。
 *   4. MergeSupportFunc：MERGE 专用辅助函数步骤，父节点必须是 CMD_MERGE 的
 *      ModifyTableState。
 *   5. FuncExpr/OpExpr/DistinctExpr/NullIfExpr：统一走 ExecInitFunc（权限检查、
 *      fmgr 初始化、参数下沉），再由本分支覆盖 opcode 为 EEOP_DISTINCT /
 *      EEOP_NULLIF（"函数调用+特化语义"的组合，NULLIF 对 varlena 参数还要
 *      强制只读）。
 *   6. ScalarArrayOpExpr：IN/NOT IN。hashfuncid 有效时（可哈希的 IN/NOT IN，
 *      含 hashed NOT IN 用等值函数探测哈希表）生成 EEOP_HASHED_SCALARARRAYOP，
 *      比线性扫描快得多；否则 EEOP_SCALARARRAYOP。编译期完成两枚函数的
 *      ACL 检查与 fmgr 查找；标量参数直接下沉到 fcinfo->args[0]。
 *   7. BoolExpr：AND/OR 的每个参数拆成 STEP_FIRST（1 个）/ STEP（0 或多个）/
 *      STEP_LAST（1 个）三种步骤以支持短路与 NULL 传播（共享 anynull 记录）；
 *      跳转目标最后统一回填。NOT 是单步 EEOP_BOOL_NOT_STEP。
 *   8. SubPlan：MULTIEXPR 子计划已在 setup 阶段整体执行过，这里只生成"返回
 *      NULL 记录"的占位步骤（它的输出以参数形式被引用）；普通子计划转
 *      ExecInitSubPlanExpr。
 *   9. FieldSelect/FieldStore：复合字段读取与赋值。FieldStore 先把输入元组拆到
 *      values/nulls 工作区（EEOP_FIELDSTORE_DEFORM），用 CaseTestExpr 机制把
 *      "被替换字段的旧值"传给嵌套赋值表达式（FieldStore/数组赋值的 arg 直接
 *      读该旧值），最后 EEOP_FIELDSTORE_FORM 合成新复合值。
 *   10. RelabelType：运行时无操作（类型重标注是编译期语义），只递归子表达式。
 *       CoerceViaIO：源类型 output + 目标类型 input 合并进单个 EEOP_IOCOERCE
 *       步骤（高频路径），input 的 typioparam/typmod 常量参数预填；带 escontext
 *       时用 *_SAFE 变体支持软错误。
 *   11. ArrayCoerceExpr：数组逐元素强转——元素表达式单独编译成一个"子
 *       ExprState"（运行时对每个元素调用）；若元素表达式退化为"直接读
 *       CaseTestExpr"（恒等转换）则子状态置 NULL，彻底免除运行时开销。
 *       ConvertRowtypeExpr：行类型转换，带输入/输出两个类型缓存槽避免重复
 *       catalog 查找。
 *   12. CaseExpr/CaseTestExpr：先求测试表达式到 caseval 工作区（varlena 强制
 *       只读——值可能被多次读取），每个 WHEN 条件里可放 CaseTestExpr 占位符
 *       （innermost_caseval 机制，支持嵌套 CASE 的保存/恢复）；步骤模式为
 *       "条件假则跳到下一个 WHEN → 命中则求 THEN 并跳到 CASE 尾 → ELSE"。
 *   13. ArrayExpr/RowExpr/RowCompareExpr/CoalesceExpr/MinMaxExpr：
 *       各元素求到工作区数组后一次性合成（EEOP_ARRAYEXPR/EEOP_ROW/
 *       EEOP_ROWCOMPARE_STEP、EEOP_ROWCOMPARE_FINAL、EEOP_JUMP_IF_NOT_NULL、
 *       EEOP_MINMAX）。RowExpr 处理
 *       named 类型缺列补 NULL、drop 列替换为 int4 NULL 与类型错位检查；
 *       RowCompareExpr 逐字段比较并按"结果为 NULL / 非零"回填跳转。
 *   14. XML/JSON 系列：SQLValueFunction（CURRENT_TIMESTAMP 类）、XmlExpr、
 *       JsonValueExpr、JsonConstructorExpr（常量参数免求值）、JsonIsPredicate；
 *       JsonExpr 除 JSON_TABLE_OP（上游 tfuncFetchRows 只需要 formatted_expr）
 *       外转 ExecInitJsonExpr。
 *   15. NullTest/BooleanTest：生成 EEOP_NULLTEST_* / EEOP_BOOLTEST_IS_* 步骤；
 *       IS UNKNOWN 等价于标量 IS NULL，直接复用 NULLTEST 步骤；行式参数用
 *       行级变体（ROWISNULL 等，带 rowtype 缓存）。
 *   16. CoerceToDomain/CoerceToDomainValue：转 ExecInitCoerceToDomain；
 *       CoerceToDomainValue 读 innermost_domainval（独立域检查场景读
 *       econtext->domainValue_datum，即 EEOP_DOMAIN_TESTVAL_EXT）。
 *   17. CurrentOfExpr/NextValueExpr/ReturningExpr：游标 CURRENT OF、序列
 *       nextval、以及 MERGE/UPDATE RETURNING 的"OLD/NEW 行不存在时跳过求值"
 *       （EEOP_RETURNINGEXPR 按空行 flag 跳转）。
 *
 * 通用机制：
 *   - scratch 复用：单个 ExprEvalStep scratch 贯穿全程，每次 push 前按需覆盖；
 *     push 是按值拷贝，入栈后修改 scratch 不影响已生成的步骤。
 *   - 跳转目标两遍回填：所有短路口先以 -1 占位并把步骤下标记入 adjust_jumps，
 *     子表达式全部编译完后统一修正为 state->steps_len——步骤数组构建期可能
 *     扩容移动，不能提前持有指针。
 *   - check_stack_depth 防御：表达式树可被构造得很深，防止递归栈溢出。
 *   - 被调用方：ExecInitExpr、ExecInitQual、ExecBuildProjectionInfo、
 *     ExecBuildAggTrans 等所有编译入口。
 * ============================================================================
 */
static void
ExecInitExprRec(Expr *node, ExprState *state,
				Datum *resv, bool *resnull)
{
	ExprEvalStep scratch = {0};

	/* Guard against stack overflow due to overly complex expressions */
	check_stack_depth();

	/* Step's output location is always what the caller gave us */
	Assert(resv != NULL && resnull != NULL);
	scratch.resvalue = resv;
	scratch.resnull = resnull;

	/* cases should be ordered as they are in enum NodeTag */
	switch (nodeTag(node))
	{
		case T_Var:
			{
				Var		   *variable = (Var *) node;

				if (variable->varattno == InvalidAttrNumber)
				{
					/* whole-row Var */
					ExecInitWholeRowVar(&scratch, variable, state);
				}
				else if (variable->varattno <= 0)
				{
					/* system column */
					scratch.d.var.attnum = variable->varattno;
					scratch.d.var.vartype = variable->vartype;
					scratch.d.var.varreturningtype = variable->varreturningtype;
					switch (variable->varno)
					{
						case INNER_VAR:
							scratch.opcode = EEOP_INNER_SYSVAR;
							break;
						case OUTER_VAR:
							scratch.opcode = EEOP_OUTER_SYSVAR;
							break;

							/* INDEX_VAR is handled by default case */

						default:
							switch (variable->varreturningtype)
							{
								case VAR_RETURNING_DEFAULT:
									scratch.opcode = EEOP_SCAN_SYSVAR;
									break;
								case VAR_RETURNING_OLD:
									scratch.opcode = EEOP_OLD_SYSVAR;
									state->flags |= EEO_FLAG_HAS_OLD;
									break;
								case VAR_RETURNING_NEW:
									scratch.opcode = EEOP_NEW_SYSVAR;
									state->flags |= EEO_FLAG_HAS_NEW;
									break;
							}
							break;
					}
				}
				else
				{
					/* regular user column */
					scratch.d.var.attnum = variable->varattno - 1;
					scratch.d.var.vartype = variable->vartype;
					scratch.d.var.varreturningtype = variable->varreturningtype;
					switch (variable->varno)
					{
						case INNER_VAR:
							scratch.opcode = EEOP_INNER_VAR;
							break;
						case OUTER_VAR:
							scratch.opcode = EEOP_OUTER_VAR;
							break;

							/* INDEX_VAR is handled by default case */

						default:
							switch (variable->varreturningtype)
							{
								case VAR_RETURNING_DEFAULT:
									scratch.opcode = EEOP_SCAN_VAR;
									break;
								case VAR_RETURNING_OLD:
									scratch.opcode = EEOP_OLD_VAR;
									state->flags |= EEO_FLAG_HAS_OLD;
									break;
								case VAR_RETURNING_NEW:
									scratch.opcode = EEOP_NEW_VAR;
									state->flags |= EEO_FLAG_HAS_NEW;
									break;
							}
							break;
					}
				}

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_Const:
			{
				Const	   *con = (Const *) node;

				scratch.opcode = EEOP_CONST;
				scratch.d.constval.value = con->constvalue;
				scratch.d.constval.isnull = con->constisnull;

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_Param:
			{
				Param	   *param = (Param *) node;
				ParamListInfo params;

				switch (param->paramkind)
				{
					case PARAM_EXEC:
						scratch.opcode = EEOP_PARAM_EXEC;
						scratch.d.param.paramid = param->paramid;
						scratch.d.param.paramtype = param->paramtype;
						ExprEvalPushStep(state, &scratch);
						break;
					case PARAM_EXTERN:

						/*
						 * If we have a relevant ParamCompileHook, use it;
						 * otherwise compile a standard EEOP_PARAM_EXTERN
						 * step.  ext_params, if supplied, takes precedence
						 * over info from the parent node's EState (if any).
						 */
						if (state->ext_params)
							params = state->ext_params;
						else if (state->parent &&
								 state->parent->state)
							params = state->parent->state->es_param_list_info;
						else
							params = NULL;
						if (params && params->paramCompile)
						{
							params->paramCompile(params, param, state,
												 resv, resnull);
						}
						else
						{
							scratch.opcode = EEOP_PARAM_EXTERN;
							scratch.d.param.paramid = param->paramid;
							scratch.d.param.paramtype = param->paramtype;
							ExprEvalPushStep(state, &scratch);
						}
						break;
					default:
						elog(ERROR, "unrecognized paramkind: %d",
							 (int) param->paramkind);
						break;
				}
				break;
			}

		case T_Aggref:
			{
				Aggref	   *aggref = (Aggref *) node;

				scratch.opcode = EEOP_AGGREF;
				scratch.d.aggref.aggno = aggref->aggno;

				if (state->parent && IsA(state->parent, AggState))
				{
					AggState   *aggstate = (AggState *) state->parent;

					aggstate->aggs = lappend(aggstate->aggs, aggref);
				}
				else
				{
					/* planner messed up */
					elog(ERROR, "Aggref found in non-Agg plan node");
				}

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_GroupingFunc:
			{
				GroupingFunc *grp_node = (GroupingFunc *) node;
				Agg		   *agg;

				if (!state->parent || !IsA(state->parent, AggState) ||
					!IsA(state->parent->plan, Agg))
					elog(ERROR, "GroupingFunc found in non-Agg plan node");

				scratch.opcode = EEOP_GROUPING_FUNC;

				agg = (Agg *) (state->parent->plan);

				if (agg->groupingSets)
					scratch.d.grouping_func.clauses = grp_node->cols;
				else
					scratch.d.grouping_func.clauses = NIL;

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_WindowFunc:
			{
				WindowFunc *wfunc = (WindowFunc *) node;
				WindowFuncExprState *wfstate = makeNode(WindowFuncExprState);

				wfstate->wfunc = wfunc;

				if (state->parent && IsA(state->parent, WindowAggState))
				{
					WindowAggState *winstate = (WindowAggState *) state->parent;
					int			nfuncs;

					winstate->funcs = lappend(winstate->funcs, wfstate);
					nfuncs = ++winstate->numfuncs;
					if (wfunc->winagg)
						winstate->numaggs++;

					/* for now initialize agg using old style expressions */
					wfstate->args = ExecInitExprList(wfunc->args,
													 state->parent);
					wfstate->aggfilter = ExecInitExpr(wfunc->aggfilter,
													  state->parent);

					/*
					 * Complain if the windowfunc's arguments contain any
					 * windowfuncs; nested window functions are semantically
					 * nonsensical.  (This should have been caught earlier,
					 * but we defend against it here anyway.)
					 */
					if (nfuncs != winstate->numfuncs)
						ereport(ERROR,
								(errcode(ERRCODE_WINDOWING_ERROR),
								 errmsg("window function calls cannot be nested")));
				}
				else
				{
					/* planner messed up */
					elog(ERROR, "WindowFunc found in non-WindowAgg plan node");
				}

				scratch.opcode = EEOP_WINDOW_FUNC;
				scratch.d.window_func.wfstate = wfstate;
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_MergeSupportFunc:
			{
				/* must be in a MERGE, else something messed up */
				if (!state->parent ||
					!IsA(state->parent, ModifyTableState) ||
					((ModifyTableState *) state->parent)->operation != CMD_MERGE)
					elog(ERROR, "MergeSupportFunc found in non-merge plan node");

				scratch.opcode = EEOP_MERGE_SUPPORT_FUNC;
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_SubscriptingRef:
			{
				SubscriptingRef *sbsref = (SubscriptingRef *) node;

				ExecInitSubscriptingRef(&scratch, sbsref, state, resv, resnull);
				break;
			}

		case T_FuncExpr:
			{
				FuncExpr   *func = (FuncExpr *) node;

				ExecInitFunc(&scratch, node,
							 func->args, func->funcid, func->inputcollid,
							 state);
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_OpExpr:
			{
				OpExpr	   *op = (OpExpr *) node;

				ExecInitFunc(&scratch, node,
							 op->args, op->opfuncid, op->inputcollid,
							 state);
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_DistinctExpr:
			{
				DistinctExpr *op = (DistinctExpr *) node;

				ExecInitFunc(&scratch, node,
							 op->args, op->opfuncid, op->inputcollid,
							 state);

				/*
				 * Change opcode of call instruction to EEOP_DISTINCT.
				 *
				 * XXX: historically we've not called the function usage
				 * pgstat infrastructure - that seems inconsistent given that
				 * we do so for normal function *and* operator evaluation.  If
				 * we decided to do that here, we'd probably want separate
				 * opcodes for FUSAGE or not.
				 */
				scratch.opcode = EEOP_DISTINCT;
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_NullIfExpr:
			{
				NullIfExpr *op = (NullIfExpr *) node;

				ExecInitFunc(&scratch, node,
							 op->args, op->opfuncid, op->inputcollid,
							 state);

				/*
				 * If first argument is of varlena type, we'll need to ensure
				 * that the value passed to the comparison function is a
				 * read-only pointer.
				 */
				scratch.d.func.make_ro =
					(get_typlen(exprType((Node *) linitial(op->args))) == -1);

				/*
				 * Change opcode of call instruction to EEOP_NULLIF.
				 *
				 * XXX: historically we've not called the function usage
				 * pgstat infrastructure - that seems inconsistent given that
				 * we do so for normal function *and* operator evaluation.  If
				 * we decided to do that here, we'd probably want separate
				 * opcodes for FUSAGE or not.
				 */
				scratch.opcode = EEOP_NULLIF;
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr *opexpr = (ScalarArrayOpExpr *) node;
				Expr	   *scalararg;
				Expr	   *arrayarg;
				FmgrInfo   *finfo;
				FunctionCallInfo fcinfo;
				AclResult	aclresult;
				Oid			cmpfuncid;

				/*
				 * Select the correct comparison function.  When we do hashed
				 * NOT IN clauses, the opfuncid will be the inequality
				 * comparison function and negfuncid will be set to equality.
				 * We need to use the equality function for hash probes.
				 */
				if (OidIsValid(opexpr->negfuncid))
				{
					Assert(OidIsValid(opexpr->hashfuncid));
					cmpfuncid = opexpr->negfuncid;
				}
				else
					cmpfuncid = opexpr->opfuncid;

				Assert(list_length(opexpr->args) == 2);
				scalararg = (Expr *) linitial(opexpr->args);
				arrayarg = (Expr *) lsecond(opexpr->args);

				/* Check permission to call function */
				aclresult = object_aclcheck(ProcedureRelationId, cmpfuncid,
											GetUserId(),
											ACL_EXECUTE);
				if (aclresult != ACLCHECK_OK)
					aclcheck_error(aclresult, OBJECT_FUNCTION,
								   get_func_name(cmpfuncid));
				InvokeFunctionExecuteHook(cmpfuncid);

				if (OidIsValid(opexpr->hashfuncid))
				{
					aclresult = object_aclcheck(ProcedureRelationId, opexpr->hashfuncid,
												GetUserId(),
												ACL_EXECUTE);
					if (aclresult != ACLCHECK_OK)
						aclcheck_error(aclresult, OBJECT_FUNCTION,
									   get_func_name(opexpr->hashfuncid));
					InvokeFunctionExecuteHook(opexpr->hashfuncid);
				}

				/* Set up the primary fmgr lookup information */
				finfo = palloc0_object(FmgrInfo);
				fcinfo = palloc0(SizeForFunctionCallInfo(2));
				fmgr_info(cmpfuncid, finfo);
				fmgr_info_set_expr((Node *) node, finfo);
				InitFunctionCallInfoData(*fcinfo, finfo, 2,
										 opexpr->inputcollid, NULL, NULL);

				/*
				 * If hashfuncid is set, we create a EEOP_HASHED_SCALARARRAYOP
				 * step instead of a EEOP_SCALARARRAYOP.  This provides much
				 * faster lookup performance than the normal linear search
				 * when the number of items in the array is anything but very
				 * small.
				 */
				if (OidIsValid(opexpr->hashfuncid))
				{
					/* Evaluate scalar directly into left function argument */
					ExecInitExprRec(scalararg, state,
									&fcinfo->args[0].value, &fcinfo->args[0].isnull);

					/*
					 * Evaluate array argument into our return value.  There's
					 * no danger in that, because the return value is
					 * guaranteed to be overwritten by
					 * EEOP_HASHED_SCALARARRAYOP, and will not be passed to
					 * any other expression.
					 */
					ExecInitExprRec(arrayarg, state, resv, resnull);

					/* And perform the operation */
					scratch.opcode = EEOP_HASHED_SCALARARRAYOP;
					scratch.d.hashedscalararrayop.inclause = opexpr->useOr;
					scratch.d.hashedscalararrayop.finfo = finfo;
					scratch.d.hashedscalararrayop.fcinfo_data = fcinfo;
					scratch.d.hashedscalararrayop.saop = opexpr;


					ExprEvalPushStep(state, &scratch);
				}
				else
				{
					/* Evaluate scalar directly into left function argument */
					ExecInitExprRec(scalararg, state,
									&fcinfo->args[0].value,
									&fcinfo->args[0].isnull);

					/*
					 * Evaluate array argument into our return value.  There's
					 * no danger in that, because the return value is
					 * guaranteed to be overwritten by EEOP_SCALARARRAYOP, and
					 * will not be passed to any other expression.
					 */
					ExecInitExprRec(arrayarg, state, resv, resnull);

					/* And perform the operation */
					scratch.opcode = EEOP_SCALARARRAYOP;
					scratch.d.scalararrayop.element_type = InvalidOid;
					scratch.d.scalararrayop.useOr = opexpr->useOr;
					scratch.d.scalararrayop.finfo = finfo;
					scratch.d.scalararrayop.fcinfo_data = fcinfo;
					scratch.d.scalararrayop.fn_addr = finfo->fn_addr;
					ExprEvalPushStep(state, &scratch);
				}
				break;
			}

		case T_BoolExpr:
			{
				BoolExpr   *boolexpr = (BoolExpr *) node;
				int			nargs = list_length(boolexpr->args);
				List	   *adjust_jumps = NIL;
				int			off;
				ListCell   *lc;

				/* allocate scratch memory used by all steps of AND/OR */
				if (boolexpr->boolop != NOT_EXPR)
					scratch.d.boolexpr.anynull = palloc_object(bool);

				/*
				 * For each argument evaluate the argument itself, then
				 * perform the bool operation's appropriate handling.
				 *
				 * We can evaluate each argument into our result area, since
				 * the short-circuiting logic means we only need to remember
				 * previous NULL values.
				 *
				 * AND/OR is split into separate STEP_FIRST (one) / STEP (zero
				 * or more) / STEP_LAST (one) steps, as each of those has to
				 * perform different work.  The FIRST/LAST split is valid
				 * because AND/OR have at least two arguments.
				 */
				off = 0;
				foreach(lc, boolexpr->args)
				{
					Expr	   *arg = (Expr *) lfirst(lc);

					/* Evaluate argument into our output variable */
					ExecInitExprRec(arg, state, resv, resnull);

					/* Perform the appropriate step type */
					switch (boolexpr->boolop)
					{
						case AND_EXPR:
							Assert(nargs >= 2);

							if (off == 0)
								scratch.opcode = EEOP_BOOL_AND_STEP_FIRST;
							else if (off + 1 == nargs)
								scratch.opcode = EEOP_BOOL_AND_STEP_LAST;
							else
								scratch.opcode = EEOP_BOOL_AND_STEP;
							break;
						case OR_EXPR:
							Assert(nargs >= 2);

							if (off == 0)
								scratch.opcode = EEOP_BOOL_OR_STEP_FIRST;
							else if (off + 1 == nargs)
								scratch.opcode = EEOP_BOOL_OR_STEP_LAST;
							else
								scratch.opcode = EEOP_BOOL_OR_STEP;
							break;
						case NOT_EXPR:
							Assert(nargs == 1);

							scratch.opcode = EEOP_BOOL_NOT_STEP;
							break;
						default:
							elog(ERROR, "unrecognized boolop: %d",
								 (int) boolexpr->boolop);
							break;
					}

					scratch.d.boolexpr.jumpdone = -1;
					ExprEvalPushStep(state, &scratch);
					adjust_jumps = lappend_int(adjust_jumps,
											   state->steps_len - 1);
					off++;
				}

				/* adjust jump targets */
				foreach(lc, adjust_jumps)
				{
					ExprEvalStep *as = &state->steps[lfirst_int(lc)];

					Assert(as->d.boolexpr.jumpdone == -1);
					as->d.boolexpr.jumpdone = state->steps_len;
				}

				break;
			}

		case T_SubPlan:
			{
				SubPlan    *subplan = (SubPlan *) node;

				/*
				 * Real execution of a MULTIEXPR SubPlan has already been
				 * done. What we have to do here is return a dummy NULL record
				 * value in case this targetlist element is assigned
				 * someplace.
				 */
				if (subplan->subLinkType == MULTIEXPR_SUBLINK)
				{
					scratch.opcode = EEOP_CONST;
					scratch.d.constval.value = (Datum) 0;
					scratch.d.constval.isnull = true;
					ExprEvalPushStep(state, &scratch);
					break;
				}

				ExecInitSubPlanExpr(subplan, state, resv, resnull);
				break;
			}

		case T_FieldSelect:
			{
				FieldSelect *fselect = (FieldSelect *) node;

				/* evaluate row/record argument into result area */
				ExecInitExprRec(fselect->arg, state, resv, resnull);

				/* and extract field */
				scratch.opcode = EEOP_FIELDSELECT;
				scratch.d.fieldselect.fieldnum = fselect->fieldnum;
				scratch.d.fieldselect.resulttype = fselect->resulttype;
				scratch.d.fieldselect.rowcache.cacheptr = NULL;

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_FieldStore:
			{
				FieldStore *fstore = (FieldStore *) node;
				TupleDesc	tupDesc;
				ExprEvalRowtypeCache *rowcachep;
				Datum	   *values;
				bool	   *nulls;
				int			ncolumns;
				ListCell   *l1,
						   *l2;

				/* find out the number of columns in the composite type */
				tupDesc = lookup_rowtype_tupdesc(fstore->resulttype, -1);
				ncolumns = tupDesc->natts;
				ReleaseTupleDesc(tupDesc);

				/* create workspace for column values */
				values = palloc_array(Datum, ncolumns);
				nulls = palloc_array(bool, ncolumns);

				/* create shared composite-type-lookup cache struct */
				rowcachep = palloc_object(ExprEvalRowtypeCache);
				rowcachep->cacheptr = NULL;

				/* emit code to evaluate the composite input value */
				ExecInitExprRec(fstore->arg, state, resv, resnull);

				/* next, deform the input tuple into our workspace */
				scratch.opcode = EEOP_FIELDSTORE_DEFORM;
				scratch.d.fieldstore.fstore = fstore;
				scratch.d.fieldstore.rowcache = rowcachep;
				scratch.d.fieldstore.values = values;
				scratch.d.fieldstore.nulls = nulls;
				scratch.d.fieldstore.ncolumns = ncolumns;
				ExprEvalPushStep(state, &scratch);

				/* evaluate new field values, store in workspace columns */
				forboth(l1, fstore->newvals, l2, fstore->fieldnums)
				{
					Expr	   *e = (Expr *) lfirst(l1);
					AttrNumber	fieldnum = lfirst_int(l2);
					Datum	   *save_innermost_caseval;
					bool	   *save_innermost_casenull;

					if (fieldnum <= 0 || fieldnum > ncolumns)
						elog(ERROR, "field number %d is out of range in FieldStore",
							 fieldnum);

					/*
					 * Use the CaseTestExpr mechanism to pass down the old
					 * value of the field being replaced; this is needed in
					 * case the newval is itself a FieldStore or
					 * SubscriptingRef that has to obtain and modify the old
					 * value.  It's safe to reuse the CASE mechanism because
					 * there cannot be a CASE between here and where the value
					 * would be needed, and a field assignment can't be within
					 * a CASE either.  (So saving and restoring
					 * innermost_caseval is just paranoia, but let's do it
					 * anyway.)
					 *
					 * Another non-obvious point is that it's safe to use the
					 * field's values[]/nulls[] entries as both the caseval
					 * source and the result address for this subexpression.
					 * That's okay only because (1) both FieldStore and
					 * SubscriptingRef evaluate their arg or refexpr inputs
					 * first, and (2) any such CaseTestExpr is directly the
					 * arg or refexpr input.  So any read of the caseval will
					 * occur before there's a chance to overwrite it.  Also,
					 * if multiple entries in the newvals/fieldnums lists
					 * target the same field, they'll effectively be applied
					 * left-to-right which is what we want.
					 */
					save_innermost_caseval = state->innermost_caseval;
					save_innermost_casenull = state->innermost_casenull;
					state->innermost_caseval = &values[fieldnum - 1];
					state->innermost_casenull = &nulls[fieldnum - 1];

					ExecInitExprRec(e, state,
									&values[fieldnum - 1],
									&nulls[fieldnum - 1]);

					state->innermost_caseval = save_innermost_caseval;
					state->innermost_casenull = save_innermost_casenull;
				}

				/* finally, form result tuple */
				scratch.opcode = EEOP_FIELDSTORE_FORM;
				scratch.d.fieldstore.fstore = fstore;
				scratch.d.fieldstore.rowcache = rowcachep;
				scratch.d.fieldstore.values = values;
				scratch.d.fieldstore.nulls = nulls;
				scratch.d.fieldstore.ncolumns = ncolumns;
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_RelabelType:
			{
				/* relabel doesn't need to do anything at runtime */
				RelabelType *relabel = (RelabelType *) node;

				ExecInitExprRec(relabel->arg, state, resv, resnull);
				break;
			}

		case T_CoerceViaIO:
			{
				CoerceViaIO *iocoerce = (CoerceViaIO *) node;
				Oid			iofunc;
				bool		typisvarlena;
				Oid			typioparam;
				FunctionCallInfo fcinfo_in;

				/* evaluate argument into step's result area */
				ExecInitExprRec(iocoerce->arg, state, resv, resnull);

				/*
				 * Prepare both output and input function calls, to be
				 * evaluated inside a single evaluation step for speed - this
				 * can be a very common operation.
				 *
				 * We don't check permissions here as a type's input/output
				 * function are assumed to be executable by everyone.
				 */
				if (state->escontext == NULL)
					scratch.opcode = EEOP_IOCOERCE;
				else
					scratch.opcode = EEOP_IOCOERCE_SAFE;

				/* lookup the source type's output function */
				scratch.d.iocoerce.finfo_out = palloc0_object(FmgrInfo);
				scratch.d.iocoerce.fcinfo_data_out = palloc0(SizeForFunctionCallInfo(1));

				getTypeOutputInfo(exprType((Node *) iocoerce->arg),
								  &iofunc, &typisvarlena);
				fmgr_info(iofunc, scratch.d.iocoerce.finfo_out);
				fmgr_info_set_expr((Node *) node, scratch.d.iocoerce.finfo_out);
				InitFunctionCallInfoData(*scratch.d.iocoerce.fcinfo_data_out,
										 scratch.d.iocoerce.finfo_out,
										 1, InvalidOid, NULL, NULL);

				/* lookup the result type's input function */
				scratch.d.iocoerce.finfo_in = palloc0_object(FmgrInfo);
				scratch.d.iocoerce.fcinfo_data_in = palloc0(SizeForFunctionCallInfo(3));

				getTypeInputInfo(iocoerce->resulttype,
								 &iofunc, &typioparam);
				fmgr_info(iofunc, scratch.d.iocoerce.finfo_in);
				fmgr_info_set_expr((Node *) node, scratch.d.iocoerce.finfo_in);
				InitFunctionCallInfoData(*scratch.d.iocoerce.fcinfo_data_in,
										 scratch.d.iocoerce.finfo_in,
										 3, InvalidOid, NULL, NULL);

				/*
				 * We can preload the second and third arguments for the input
				 * function, since they're constants.
				 */
				fcinfo_in = scratch.d.iocoerce.fcinfo_data_in;
				fcinfo_in->args[1].value = ObjectIdGetDatum(typioparam);
				fcinfo_in->args[1].isnull = false;
				fcinfo_in->args[2].value = Int32GetDatum(-1);
				fcinfo_in->args[2].isnull = false;

				fcinfo_in->context = (Node *) state->escontext;

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_ArrayCoerceExpr:
			{
				ArrayCoerceExpr *acoerce = (ArrayCoerceExpr *) node;
				Oid			resultelemtype;
				ExprState  *elemstate;

				/* evaluate argument into step's result area */
				ExecInitExprRec(acoerce->arg, state, resv, resnull);

				resultelemtype = get_element_type(acoerce->resulttype);
				if (!OidIsValid(resultelemtype))
					ereport(ERROR,
							(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
							 errmsg("target type is not an array")));

				/*
				 * Construct a sub-expression for the per-element expression;
				 * but don't ready it until after we check it for triviality.
				 * We assume it hasn't any Var references, but does have a
				 * CaseTestExpr representing the source array element values.
				 */
				elemstate = makeNode(ExprState);
				elemstate->expr = acoerce->elemexpr;
				elemstate->parent = state->parent;
				elemstate->ext_params = state->ext_params;

				elemstate->innermost_caseval = palloc_object(Datum);
				elemstate->innermost_casenull = palloc_object(bool);

				ExecInitExprRec(acoerce->elemexpr, elemstate,
								&elemstate->resvalue, &elemstate->resnull);

				if (elemstate->steps_len == 1 &&
					elemstate->steps[0].opcode == EEOP_CASE_TESTVAL)
				{
					/* Trivial, so we need no per-element work at runtime */
					elemstate = NULL;
				}
				else
				{
					/* Not trivial, so append a DONE step */
					scratch.opcode = EEOP_DONE_RETURN;
					ExprEvalPushStep(elemstate, &scratch);
					/* and ready the subexpression */
					ExecReadyExpr(elemstate);
				}

				scratch.opcode = EEOP_ARRAYCOERCE;
				scratch.d.arraycoerce.elemexprstate = elemstate;
				scratch.d.arraycoerce.resultelemtype = resultelemtype;

				if (elemstate)
				{
					/* Set up workspace for array_map */
					scratch.d.arraycoerce.amstate = palloc0_object(ArrayMapState);
				}
				else
				{
					/* Don't need workspace if there's no subexpression */
					scratch.d.arraycoerce.amstate = NULL;
				}

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_ConvertRowtypeExpr:
			{
				ConvertRowtypeExpr *convert = (ConvertRowtypeExpr *) node;
				ExprEvalRowtypeCache *rowcachep;

				/* cache structs must be out-of-line for space reasons */
				rowcachep = palloc(2 * sizeof(ExprEvalRowtypeCache));
				rowcachep[0].cacheptr = NULL;
				rowcachep[1].cacheptr = NULL;

				/* evaluate argument into step's result area */
				ExecInitExprRec(convert->arg, state, resv, resnull);

				/* and push conversion step */
				scratch.opcode = EEOP_CONVERT_ROWTYPE;
				scratch.d.convert_rowtype.inputtype =
					exprType((Node *) convert->arg);
				scratch.d.convert_rowtype.outputtype = convert->resulttype;
				scratch.d.convert_rowtype.incache = &rowcachep[0];
				scratch.d.convert_rowtype.outcache = &rowcachep[1];
				scratch.d.convert_rowtype.map = NULL;

				ExprEvalPushStep(state, &scratch);
				break;
			}

			/* note that CaseWhen expressions are handled within this block */
		case T_CaseExpr:
			{
				CaseExpr   *caseExpr = (CaseExpr *) node;
				List	   *adjust_jumps = NIL;
				Datum	   *caseval = NULL;
				bool	   *casenull = NULL;
				ListCell   *lc;

				/*
				 * If there's a test expression, we have to evaluate it and
				 * save the value where the CaseTestExpr placeholders can find
				 * it.
				 */
				if (caseExpr->arg != NULL)
				{
					/* Evaluate testexpr into caseval/casenull workspace */
					caseval = palloc_object(Datum);
					casenull = palloc_object(bool);

					ExecInitExprRec(caseExpr->arg, state,
									caseval, casenull);

					/*
					 * Since value might be read multiple times, force to R/O
					 * - but only if it could be an expanded datum.
					 */
					if (get_typlen(exprType((Node *) caseExpr->arg)) == -1)
					{
						/* change caseval in-place */
						scratch.opcode = EEOP_MAKE_READONLY;
						scratch.resvalue = caseval;
						scratch.resnull = casenull;
						scratch.d.make_readonly.value = caseval;
						scratch.d.make_readonly.isnull = casenull;
						ExprEvalPushStep(state, &scratch);
						/* restore normal settings of scratch fields */
						scratch.resvalue = resv;
						scratch.resnull = resnull;
					}
				}

				/*
				 * Prepare to evaluate each of the WHEN clauses in turn; as
				 * soon as one is true we return the value of the
				 * corresponding THEN clause.  If none are true then we return
				 * the value of the ELSE clause, or NULL if there is none.
				 */
				foreach(lc, caseExpr->args)
				{
					CaseWhen   *when = (CaseWhen *) lfirst(lc);
					Datum	   *save_innermost_caseval;
					bool	   *save_innermost_casenull;
					int			whenstep;

					/*
					 * Make testexpr result available to CaseTestExpr nodes
					 * within the condition.  We must save and restore prior
					 * setting of innermost_caseval fields, in case this node
					 * is itself within a larger CASE.
					 *
					 * If there's no test expression, we don't actually need
					 * to save and restore these fields; but it's less code to
					 * just do so unconditionally.
					 */
					save_innermost_caseval = state->innermost_caseval;
					save_innermost_casenull = state->innermost_casenull;
					state->innermost_caseval = caseval;
					state->innermost_casenull = casenull;

					/* evaluate condition into CASE's result variables */
					ExecInitExprRec(when->expr, state, resv, resnull);

					state->innermost_caseval = save_innermost_caseval;
					state->innermost_casenull = save_innermost_casenull;

					/* If WHEN result isn't true, jump to next CASE arm */
					scratch.opcode = EEOP_JUMP_IF_NOT_TRUE;
					scratch.d.jump.jumpdone = -1;	/* computed later */
					ExprEvalPushStep(state, &scratch);
					whenstep = state->steps_len - 1;

					/*
					 * If WHEN result is true, evaluate THEN result, storing
					 * it into the CASE's result variables.
					 */
					ExecInitExprRec(when->result, state, resv, resnull);

					/* Emit JUMP step to jump to end of CASE's code */
					scratch.opcode = EEOP_JUMP;
					scratch.d.jump.jumpdone = -1;	/* computed later */
					ExprEvalPushStep(state, &scratch);

					/*
					 * Don't know address for that jump yet, compute once the
					 * whole CASE expression is built.
					 */
					adjust_jumps = lappend_int(adjust_jumps,
											   state->steps_len - 1);

					/*
					 * But we can set WHEN test's jump target now, to make it
					 * jump to the next WHEN subexpression or the ELSE.
					 */
					state->steps[whenstep].d.jump.jumpdone = state->steps_len;
				}

				/* transformCaseExpr always adds a default */
				Assert(caseExpr->defresult);

				/* evaluate ELSE expr into CASE's result variables */
				ExecInitExprRec(caseExpr->defresult, state,
								resv, resnull);

				/* adjust jump targets */
				foreach(lc, adjust_jumps)
				{
					ExprEvalStep *as = &state->steps[lfirst_int(lc)];

					Assert(as->opcode == EEOP_JUMP);
					Assert(as->d.jump.jumpdone == -1);
					as->d.jump.jumpdone = state->steps_len;
				}

				break;
			}

		case T_CaseTestExpr:
			{
				/*
				 * Read from location identified by innermost_caseval.  Note
				 * that innermost_caseval could be NULL, if this node isn't
				 * actually within a CaseExpr, ArrayCoerceExpr, etc structure.
				 * That can happen because some parts of the system abuse
				 * CaseTestExpr to cause a read of a value externally supplied
				 * in econtext->caseValue_datum.  We'll take care of that by
				 * generating a specialized operation.
				 */
				if (state->innermost_caseval == NULL)
					scratch.opcode = EEOP_CASE_TESTVAL_EXT;
				else
				{
					scratch.opcode = EEOP_CASE_TESTVAL;
					scratch.d.casetest.value = state->innermost_caseval;
					scratch.d.casetest.isnull = state->innermost_casenull;
				}
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_ArrayExpr:
			{
				ArrayExpr  *arrayexpr = (ArrayExpr *) node;
				int			nelems = list_length(arrayexpr->elements);
				ListCell   *lc;
				int			elemoff;

				/*
				 * Evaluate by computing each element, and then forming the
				 * array.  Elements are computed into scratch arrays
				 * associated with the ARRAYEXPR step.
				 */
				scratch.opcode = EEOP_ARRAYEXPR;
				scratch.d.arrayexpr.elemvalues =
					palloc_array(Datum, nelems);
				scratch.d.arrayexpr.elemnulls =
					palloc_array(bool, nelems);
				scratch.d.arrayexpr.nelems = nelems;

				/* fill remaining fields of step */
				scratch.d.arrayexpr.multidims = arrayexpr->multidims;
				scratch.d.arrayexpr.elemtype = arrayexpr->element_typeid;

				/* do one-time catalog lookup for type info */
				get_typlenbyvalalign(arrayexpr->element_typeid,
									 &scratch.d.arrayexpr.elemlength,
									 &scratch.d.arrayexpr.elembyval,
									 &scratch.d.arrayexpr.elemalign);

				/* prepare to evaluate all arguments */
				elemoff = 0;
				foreach(lc, arrayexpr->elements)
				{
					Expr	   *e = (Expr *) lfirst(lc);

					ExecInitExprRec(e, state,
									&scratch.d.arrayexpr.elemvalues[elemoff],
									&scratch.d.arrayexpr.elemnulls[elemoff]);
					elemoff++;
				}

				/* and then collect all into an array */
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_RowExpr:
			{
				RowExpr    *rowexpr = (RowExpr *) node;
				int			nelems = list_length(rowexpr->args);
				TupleDesc	tupdesc;
				int			i;
				ListCell   *l;

				/* Build tupdesc to describe result tuples */
				if (rowexpr->row_typeid == RECORDOID)
				{
					/* generic record, use types of given expressions */
					tupdesc = ExecTypeFromExprList(rowexpr->args);
					/* ... but adopt RowExpr's column aliases */
					ExecTypeSetColNames(tupdesc, rowexpr->colnames);
					/* Bless the tupdesc so it can be looked up later */
					BlessTupleDesc(tupdesc);
				}
				else
				{
					/* it's been cast to a named type, use that */
					tupdesc = lookup_rowtype_tupdesc_copy(rowexpr->row_typeid, -1);
				}

				/*
				 * In the named-type case, the tupdesc could have more columns
				 * than are in the args list, since the type might have had
				 * columns added since the ROW() was parsed.  We want those
				 * extra columns to go to nulls, so we make sure that the
				 * workspace arrays are large enough and then initialize any
				 * extra columns to read as NULLs.
				 */
				Assert(nelems <= tupdesc->natts);
				nelems = Max(nelems, tupdesc->natts);

				/*
				 * Evaluate by first building datums for each field, and then
				 * a final step forming the composite datum.
				 */
				scratch.opcode = EEOP_ROW;
				scratch.d.row.tupdesc = tupdesc;

				/* space for the individual field datums */
				scratch.d.row.elemvalues =
					palloc_array(Datum, nelems);
				scratch.d.row.elemnulls =
					palloc_array(bool, nelems);
				/* as explained above, make sure any extra columns are null */
				memset(scratch.d.row.elemnulls, true, sizeof(bool) * nelems);

				/* Set up evaluation, skipping any deleted columns */
				i = 0;
				foreach(l, rowexpr->args)
				{
					Form_pg_attribute att = TupleDescAttr(tupdesc, i);
					Expr	   *e = (Expr *) lfirst(l);

					if (!att->attisdropped)
					{
						/*
						 * Guard against ALTER COLUMN TYPE on rowtype since
						 * the RowExpr was created.  XXX should we check
						 * typmod too?	Not sure we can be sure it'll be the
						 * same.
						 */
						if (exprType((Node *) e) != att->atttypid)
							ereport(ERROR,
									(errcode(ERRCODE_DATATYPE_MISMATCH),
									 errmsg("ROW() column has type %s instead of type %s",
											format_type_be(exprType((Node *) e)),
											format_type_be(att->atttypid))));
					}
					else
					{
						/*
						 * Ignore original expression and insert a NULL. We
						 * don't really care what type of NULL it is, so
						 * always make an int4 NULL.
						 */
						e = (Expr *) makeNullConst(INT4OID, -1, InvalidOid);
					}

					/* Evaluate column expr into appropriate workspace slot */
					ExecInitExprRec(e, state,
									&scratch.d.row.elemvalues[i],
									&scratch.d.row.elemnulls[i]);
					i++;
				}

				/* And finally build the row value */
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_RowCompareExpr:
			{
				RowCompareExpr *rcexpr = (RowCompareExpr *) node;
				int			nopers = list_length(rcexpr->opnos);
				List	   *adjust_jumps = NIL;
				ListCell   *l_left_expr,
						   *l_right_expr,
						   *l_opno,
						   *l_opfamily,
						   *l_inputcollid;
				ListCell   *lc;

				/*
				 * Iterate over each field, prepare comparisons.  To handle
				 * NULL results, prepare jumps to after the expression.  If a
				 * comparison yields a != 0 result, jump to the final step.
				 */
				Assert(list_length(rcexpr->largs) == nopers);
				Assert(list_length(rcexpr->rargs) == nopers);
				Assert(list_length(rcexpr->opfamilies) == nopers);
				Assert(list_length(rcexpr->inputcollids) == nopers);

				forfive(l_left_expr, rcexpr->largs,
						l_right_expr, rcexpr->rargs,
						l_opno, rcexpr->opnos,
						l_opfamily, rcexpr->opfamilies,
						l_inputcollid, rcexpr->inputcollids)
				{
					Expr	   *left_expr = (Expr *) lfirst(l_left_expr);
					Expr	   *right_expr = (Expr *) lfirst(l_right_expr);
					Oid			opno = lfirst_oid(l_opno);
					Oid			opfamily = lfirst_oid(l_opfamily);
					Oid			inputcollid = lfirst_oid(l_inputcollid);
					int			strategy;
					Oid			lefttype;
					Oid			righttype;
					Oid			proc;
					FmgrInfo   *finfo;
					FunctionCallInfo fcinfo;

					get_op_opfamily_properties(opno, opfamily, false,
											   &strategy,
											   &lefttype,
											   &righttype);
					proc = get_opfamily_proc(opfamily,
											 lefttype,
											 righttype,
											 BTORDER_PROC);
					if (!OidIsValid(proc))
						elog(ERROR, "missing support function %d(%u,%u) in opfamily %u",
							 BTORDER_PROC, lefttype, righttype, opfamily);

					/* Set up the primary fmgr lookup information */
					finfo = palloc0_object(FmgrInfo);
					fcinfo = palloc0(SizeForFunctionCallInfo(2));
					fmgr_info(proc, finfo);
					fmgr_info_set_expr((Node *) node, finfo);
					InitFunctionCallInfoData(*fcinfo, finfo, 2,
											 inputcollid, NULL, NULL);

					/*
					 * If we enforced permissions checks on index support
					 * functions, we'd need to make a check here.  But the
					 * index support machinery doesn't do that, and thus
					 * neither does this code.
					 */

					/* evaluate left and right args directly into fcinfo */
					ExecInitExprRec(left_expr, state,
									&fcinfo->args[0].value, &fcinfo->args[0].isnull);
					ExecInitExprRec(right_expr, state,
									&fcinfo->args[1].value, &fcinfo->args[1].isnull);

					scratch.opcode = EEOP_ROWCOMPARE_STEP;
					scratch.d.rowcompare_step.finfo = finfo;
					scratch.d.rowcompare_step.fcinfo_data = fcinfo;
					scratch.d.rowcompare_step.fn_addr = finfo->fn_addr;
					/* jump targets filled below */
					scratch.d.rowcompare_step.jumpnull = -1;
					scratch.d.rowcompare_step.jumpdone = -1;

					ExprEvalPushStep(state, &scratch);
					adjust_jumps = lappend_int(adjust_jumps,
											   state->steps_len - 1);
				}

				/*
				 * We could have a zero-column rowtype, in which case the rows
				 * necessarily compare equal.
				 */
				if (nopers == 0)
				{
					scratch.opcode = EEOP_CONST;
					scratch.d.constval.value = Int32GetDatum(0);
					scratch.d.constval.isnull = false;
					ExprEvalPushStep(state, &scratch);
				}

				/* Finally, examine the last comparison result */
				scratch.opcode = EEOP_ROWCOMPARE_FINAL;
				scratch.d.rowcompare_final.cmptype = rcexpr->cmptype;
				ExprEvalPushStep(state, &scratch);

				/* adjust jump targets */
				foreach(lc, adjust_jumps)
				{
					ExprEvalStep *as = &state->steps[lfirst_int(lc)];

					Assert(as->opcode == EEOP_ROWCOMPARE_STEP);
					Assert(as->d.rowcompare_step.jumpdone == -1);
					Assert(as->d.rowcompare_step.jumpnull == -1);

					/* jump to comparison evaluation */
					as->d.rowcompare_step.jumpdone = state->steps_len - 1;
					/* jump to the following expression */
					as->d.rowcompare_step.jumpnull = state->steps_len;
				}

				break;
			}

		case T_CoalesceExpr:
			{
				CoalesceExpr *coalesce = (CoalesceExpr *) node;
				List	   *adjust_jumps = NIL;
				ListCell   *lc;

				/* We assume there's at least one arg */
				Assert(coalesce->args != NIL);

				/*
				 * Prepare evaluation of all coalesced arguments, after each
				 * one push a step that short-circuits if not null.
				 */
				foreach(lc, coalesce->args)
				{
					Expr	   *e = (Expr *) lfirst(lc);

					/* evaluate argument, directly into result datum */
					ExecInitExprRec(e, state, resv, resnull);

					/* if it's not null, skip to end of COALESCE expr */
					scratch.opcode = EEOP_JUMP_IF_NOT_NULL;
					scratch.d.jump.jumpdone = -1;	/* adjust later */
					ExprEvalPushStep(state, &scratch);

					adjust_jumps = lappend_int(adjust_jumps,
											   state->steps_len - 1);
				}

				/*
				 * No need to add a constant NULL return - we only can get to
				 * the end of the expression if a NULL already is being
				 * returned.
				 */

				/* adjust jump targets */
				foreach(lc, adjust_jumps)
				{
					ExprEvalStep *as = &state->steps[lfirst_int(lc)];

					Assert(as->opcode == EEOP_JUMP_IF_NOT_NULL);
					Assert(as->d.jump.jumpdone == -1);
					as->d.jump.jumpdone = state->steps_len;
				}

				break;
			}

		case T_MinMaxExpr:
			{
				MinMaxExpr *minmaxexpr = (MinMaxExpr *) node;
				int			nelems = list_length(minmaxexpr->args);
				TypeCacheEntry *typentry;
				FmgrInfo   *finfo;
				FunctionCallInfo fcinfo;
				ListCell   *lc;
				int			off;

				/* Look up the btree comparison function for the datatype */
				typentry = lookup_type_cache(minmaxexpr->minmaxtype,
											 TYPECACHE_CMP_PROC);
				if (!OidIsValid(typentry->cmp_proc))
					ereport(ERROR,
							(errcode(ERRCODE_UNDEFINED_FUNCTION),
							 errmsg("could not identify a comparison function for type %s",
									format_type_be(minmaxexpr->minmaxtype))));

				/*
				 * If we enforced permissions checks on index support
				 * functions, we'd need to make a check here.  But the index
				 * support machinery doesn't do that, and thus neither does
				 * this code.
				 */

				/* Perform function lookup */
				finfo = palloc0_object(FmgrInfo);
				fcinfo = palloc0(SizeForFunctionCallInfo(2));
				fmgr_info(typentry->cmp_proc, finfo);
				fmgr_info_set_expr((Node *) node, finfo);
				InitFunctionCallInfoData(*fcinfo, finfo, 2,
										 minmaxexpr->inputcollid, NULL, NULL);

				scratch.opcode = EEOP_MINMAX;
				/* allocate space to store arguments */
				scratch.d.minmax.values = palloc_array(Datum, nelems);
				scratch.d.minmax.nulls = palloc_array(bool, nelems);
				scratch.d.minmax.nelems = nelems;

				scratch.d.minmax.op = minmaxexpr->op;
				scratch.d.minmax.finfo = finfo;
				scratch.d.minmax.fcinfo_data = fcinfo;

				/* evaluate expressions into minmax->values/nulls */
				off = 0;
				foreach(lc, minmaxexpr->args)
				{
					Expr	   *e = (Expr *) lfirst(lc);

					ExecInitExprRec(e, state,
									&scratch.d.minmax.values[off],
									&scratch.d.minmax.nulls[off]);
					off++;
				}

				/* and push the final comparison */
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_SQLValueFunction:
			{
				SQLValueFunction *svf = (SQLValueFunction *) node;

				scratch.opcode = EEOP_SQLVALUEFUNCTION;
				scratch.d.sqlvaluefunction.svf = svf;

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_XmlExpr:
			{
				XmlExpr    *xexpr = (XmlExpr *) node;
				int			nnamed = list_length(xexpr->named_args);
				int			nargs = list_length(xexpr->args);
				int			off;
				ListCell   *arg;

				scratch.opcode = EEOP_XMLEXPR;
				scratch.d.xmlexpr.xexpr = xexpr;

				/* allocate space for storing all the arguments */
				if (nnamed)
				{
					scratch.d.xmlexpr.named_argvalue = palloc_array(Datum, nnamed);
					scratch.d.xmlexpr.named_argnull = palloc_array(bool, nnamed);
				}
				else
				{
					scratch.d.xmlexpr.named_argvalue = NULL;
					scratch.d.xmlexpr.named_argnull = NULL;
				}

				if (nargs)
				{
					scratch.d.xmlexpr.argvalue = palloc_array(Datum, nargs);
					scratch.d.xmlexpr.argnull = palloc_array(bool, nargs);
				}
				else
				{
					scratch.d.xmlexpr.argvalue = NULL;
					scratch.d.xmlexpr.argnull = NULL;
				}

				/* prepare argument execution */
				off = 0;
				foreach(arg, xexpr->named_args)
				{
					Expr	   *e = (Expr *) lfirst(arg);

					ExecInitExprRec(e, state,
									&scratch.d.xmlexpr.named_argvalue[off],
									&scratch.d.xmlexpr.named_argnull[off]);
					off++;
				}

				off = 0;
				foreach(arg, xexpr->args)
				{
					Expr	   *e = (Expr *) lfirst(arg);

					ExecInitExprRec(e, state,
									&scratch.d.xmlexpr.argvalue[off],
									&scratch.d.xmlexpr.argnull[off]);
					off++;
				}

				/* and evaluate the actual XML expression */
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_JsonValueExpr:
			{
				JsonValueExpr *jve = (JsonValueExpr *) node;

				Assert(jve->raw_expr != NULL);
				ExecInitExprRec(jve->raw_expr, state, resv, resnull);
				Assert(jve->formatted_expr != NULL);
				ExecInitExprRec(jve->formatted_expr, state, resv, resnull);
				break;
			}

		case T_JsonConstructorExpr:
			{
				JsonConstructorExpr *ctor = (JsonConstructorExpr *) node;
				List	   *args = ctor->args;
				ListCell   *lc;
				int			nargs = list_length(args);
				int			argno = 0;

				if (ctor->func)
				{
					ExecInitExprRec(ctor->func, state, resv, resnull);
				}
				else if ((ctor->type == JSCTOR_JSON_PARSE && !ctor->unique) ||
						 ctor->type == JSCTOR_JSON_SERIALIZE)
				{
					/* Use the value of the first argument as result */
					ExecInitExprRec(linitial(args), state, resv, resnull);
				}
				else
				{
					JsonConstructorExprState *jcstate;

					jcstate = palloc0_object(JsonConstructorExprState);

					scratch.opcode = EEOP_JSON_CONSTRUCTOR;
					scratch.d.json_constructor.jcstate = jcstate;

					jcstate->constructor = ctor;
					jcstate->arg_values = palloc_array(Datum, nargs);
					jcstate->arg_nulls = palloc_array(bool, nargs);
					jcstate->arg_types = palloc_array(Oid, nargs);
					jcstate->nargs = nargs;

					foreach(lc, args)
					{
						Expr	   *arg = (Expr *) lfirst(lc);

						jcstate->arg_types[argno] = exprType((Node *) arg);

						if (IsA(arg, Const))
						{
							/* Don't evaluate const arguments every round */
							Const	   *con = (Const *) arg;

							jcstate->arg_values[argno] = con->constvalue;
							jcstate->arg_nulls[argno] = con->constisnull;
						}
						else
						{
							ExecInitExprRec(arg, state,
											&jcstate->arg_values[argno],
											&jcstate->arg_nulls[argno]);
						}
						argno++;
					}

					/* prepare type cache for datum_to_json[b]() */
					if (ctor->type == JSCTOR_JSON_SCALAR)
					{
						bool		is_jsonb =
							ctor->returning->format->format_type == JS_FORMAT_JSONB;

						jcstate->arg_type_cache =
							palloc(sizeof(*jcstate->arg_type_cache) * nargs);

						for (int i = 0; i < nargs; i++)
						{
							JsonTypeCategory category;
							Oid			outfuncid;
							Oid			typid = jcstate->arg_types[i];

							json_categorize_type(typid, is_jsonb,
												 &category, &outfuncid);

							jcstate->arg_type_cache[i].outfuncid = outfuncid;
							jcstate->arg_type_cache[i].category = (int) category;
						}
					}

					ExprEvalPushStep(state, &scratch);
				}

				if (ctor->coercion)
				{
					Datum	   *innermost_caseval = state->innermost_caseval;
					bool	   *innermost_isnull = state->innermost_casenull;

					state->innermost_caseval = resv;
					state->innermost_casenull = resnull;

					ExecInitExprRec(ctor->coercion, state, resv, resnull);

					state->innermost_caseval = innermost_caseval;
					state->innermost_casenull = innermost_isnull;
				}
			}
			break;

		case T_JsonIsPredicate:
			{
				JsonIsPredicate *pred = (JsonIsPredicate *) node;

				ExecInitExprRec((Expr *) pred->expr, state, resv, resnull);

				scratch.opcode = EEOP_IS_JSON;
				scratch.d.is_json.pred = pred;

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_JsonExpr:
			{
				JsonExpr   *jsexpr = castNode(JsonExpr, node);

				/*
				 * No need to initialize a full JsonExprState For
				 * JSON_TABLE(), because the upstream caller tfuncFetchRows()
				 * is only interested in the value of formatted_expr.
				 */
				if (jsexpr->op == JSON_TABLE_OP)
					ExecInitExprRec((Expr *) jsexpr->formatted_expr, state,
									resv, resnull);
				else
					ExecInitJsonExpr(jsexpr, state, resv, resnull, &scratch);
				break;
			}

		case T_NullTest:
			{
				NullTest   *ntest = (NullTest *) node;

				if (ntest->nulltesttype == IS_NULL)
				{
					if (ntest->argisrow)
						scratch.opcode = EEOP_NULLTEST_ROWISNULL;
					else
						scratch.opcode = EEOP_NULLTEST_ISNULL;
				}
				else if (ntest->nulltesttype == IS_NOT_NULL)
				{
					if (ntest->argisrow)
						scratch.opcode = EEOP_NULLTEST_ROWISNOTNULL;
					else
						scratch.opcode = EEOP_NULLTEST_ISNOTNULL;
				}
				else
				{
					elog(ERROR, "unrecognized nulltesttype: %d",
						 (int) ntest->nulltesttype);
				}
				/* initialize cache in case it's a row test */
				scratch.d.nulltest_row.rowcache.cacheptr = NULL;

				/* first evaluate argument into result variable */
				ExecInitExprRec(ntest->arg, state,
								resv, resnull);

				/* then push the test of that argument */
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_BooleanTest:
			{
				BooleanTest *btest = (BooleanTest *) node;

				/*
				 * Evaluate argument, directly into result datum.  That's ok,
				 * because resv/resnull is definitely not used anywhere else,
				 * and will get overwritten by the below EEOP_BOOLTEST_IS_*
				 * step.
				 */
				ExecInitExprRec(btest->arg, state, resv, resnull);

				switch (btest->booltesttype)
				{
					case IS_TRUE:
						scratch.opcode = EEOP_BOOLTEST_IS_TRUE;
						break;
					case IS_NOT_TRUE:
						scratch.opcode = EEOP_BOOLTEST_IS_NOT_TRUE;
						break;
					case IS_FALSE:
						scratch.opcode = EEOP_BOOLTEST_IS_FALSE;
						break;
					case IS_NOT_FALSE:
						scratch.opcode = EEOP_BOOLTEST_IS_NOT_FALSE;
						break;
					case IS_UNKNOWN:
						/* Same as scalar IS NULL test */
						scratch.opcode = EEOP_NULLTEST_ISNULL;
						break;
					case IS_NOT_UNKNOWN:
						/* Same as scalar IS NOT NULL test */
						scratch.opcode = EEOP_NULLTEST_ISNOTNULL;
						break;
					default:
						elog(ERROR, "unrecognized booltesttype: %d",
							 (int) btest->booltesttype);
				}

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_CoerceToDomain:
			{
				CoerceToDomain *ctest = (CoerceToDomain *) node;

				ExecInitCoerceToDomain(&scratch, ctest, state,
									   resv, resnull);
				break;
			}

		case T_CoerceToDomainValue:
			{
				/*
				 * Read from location identified by innermost_domainval.  Note
				 * that innermost_domainval could be NULL, if we're compiling
				 * a standalone domain check rather than one embedded in a
				 * larger expression.  In that case we must read from
				 * econtext->domainValue_datum.  We'll take care of that by
				 * generating a specialized operation.
				 */
				if (state->innermost_domainval == NULL)
					scratch.opcode = EEOP_DOMAIN_TESTVAL_EXT;
				else
				{
					scratch.opcode = EEOP_DOMAIN_TESTVAL;
					/* we share instruction union variant with case testval */
					scratch.d.casetest.value = state->innermost_domainval;
					scratch.d.casetest.isnull = state->innermost_domainnull;
				}
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_CurrentOfExpr:
			{
				scratch.opcode = EEOP_CURRENTOFEXPR;
				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_NextValueExpr:
			{
				NextValueExpr *nve = (NextValueExpr *) node;

				scratch.opcode = EEOP_NEXTVALUEEXPR;
				scratch.d.nextvalueexpr.seqid = nve->seqid;
				scratch.d.nextvalueexpr.seqtypid = nve->typeId;

				ExprEvalPushStep(state, &scratch);
				break;
			}

		case T_ReturningExpr:
			{
				ReturningExpr *rexpr = (ReturningExpr *) node;
				int			retstep;

				/* Skip expression evaluation if OLD/NEW row doesn't exist */
				scratch.opcode = EEOP_RETURNINGEXPR;
				scratch.d.returningexpr.nullflag = rexpr->retold ?
					EEO_FLAG_OLD_IS_NULL : EEO_FLAG_NEW_IS_NULL;
				scratch.d.returningexpr.jumpdone = -1;	/* set below */
				ExprEvalPushStep(state, &scratch);
				retstep = state->steps_len - 1;

				/* Steps to evaluate expression to return */
				ExecInitExprRec(rexpr->retexpr, state, resv, resnull);

				/* Jump target used if OLD/NEW row doesn't exist */
				state->steps[retstep].d.returningexpr.jumpdone = state->steps_len;

				/* Update ExprState flags */
				if (rexpr->retold)
					state->flags |= EEO_FLAG_HAS_OLD;
				else
					state->flags |= EEO_FLAG_HAS_NEW;

				break;
			}

		default:
			elog(ERROR, "unrecognized node type: %d",
				 (int) nodeTag(node));
			break;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExprEvalPushStep —— 向步骤数组追加一条求值步骤（动态扩容）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 s 按值拷贝到 es->steps 尾部（steps_len 自增）。首次 push 分配 16 个槽，
 *   满员时翻倍（repalloc）。本文件所有"生成步骤"的地方都经由此函数。
 *
 * 参数：
 *   es - 目标 ExprState。
 *   s  - 待追加的步骤（结构体按值拷贝，之后调用方对 scratch 的修改不影响
 *        已入栈项）。
 *
 * 设计思想：
 *   注意 es->steps 可能因 repalloc 而整体移动，因此"正在构建表达式"期间任何人
 *   不得持有指向 steps 数组的指针并跨过 push 调用——全文件的回填模式都是
 *   "先记下标、最后再取 &state->steps[i]"（见 ExecInitExprRec 的 adjust_jumps
 *   两遍回填）。
 * ============================================================================
 */
void
ExprEvalPushStep(ExprState *es, const ExprEvalStep *s)
{
	if (es->steps_alloc == 0)
	{
		es->steps_alloc = 16;
		es->steps = palloc_array(ExprEvalStep, es->steps_alloc);
	}
	else if (es->steps_alloc == es->steps_len)
	{
		es->steps_alloc *= 2;
		es->steps = repalloc(es->steps,
							 sizeof(ExprEvalStep) * es->steps_alloc);
	}

	memcpy(&es->steps[es->steps_len++], s, sizeof(ExprEvalStep));
}

/*
 * ============================================================================
 * 【中文注释】ExecInitFunc —— 编译"函数式"表达式（函数调用/运算符的共同基础）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为一次函数调用做全部准备工作：①编译期 ACL 权限检查；②FmgrInfo 与
 *   FunctionCallInfo 的初始化；③生成参数求值步骤（结果直接下沉到 fcinfo 参数
 *   槽）；④按函数严格性与 pgstat 统计等级选择最合适的 opcode。本函数不 push
 *   步骤——调用方（ExecInitExprRec 的 FuncExpr/OpExpr 分支等）需自行覆盖 opcode
 *   （如 EEOP_DISTINCT/EEOP_NULLIF）后再 push。
 *
 * 参数：
 *   scratch     - 待填充的步骤结构（含执行时所需的 finfo/fcinfo 工作区指针）。
 *   node        - 原始表达式节点（供 fmgr_info_set_expr 记录调用来源与错误定位）。
 *   args        - 函数参数表达式列表。
 *   funcid      - 被调函数 OID。
 *   inputcollid - 输入排序规则（已合并）。
 *   state       - 所属 ExprState。
 *
 * 设计思想：
 *   1. 编译期权限检查：object_aclcheck 验证调用者对被调函数有 EXECUTE 权限并
 *      触发对象访问 hook，失败立即抛错——把"每次调用都检查"降为"编译一次检查"，
 *      是执行期零开销的重要来源。
 *   2. 参数直接下沉进 fcinfo->args：子表达式结果直接写到函数参数槽，省去中间
 *      搬运；Const 参数编译期直接填入（"不要每轮循环重复求常量"，比较运算中
 *      尤其常见），是热路径优化。
 *   3. opcode 选择矩阵（两维：是否跟踪统计 x 是否严格）：
 *      - 关闭统计（pgstat_track_functions <= fn_stats）且 strict 时按参数个数选
 *        EEOP_FUNCEXPR_STRICT_1 / STRICT_2 / STRICT 通用——strict 语义是"任一
 *        参数为 NULL 直接返回 NULL、不调用函数"，参数越少检查越轻（1/2 参数
 *        特化展开）。
 *      - 开启统计则用 *_FUSAGE 变体，运行时把"函数被调用次数"记入 pgstat。
 *   4. 防御性检查：nargs 超过 FUNC_MAX_ARGS 报错（正常情况下解析器已保证）；
 *      fn_retset（集合返回函数）直接报错——本上下文不支持集合（应由 SRF 节点
 *      处理）。
 *   5. 被调用方：FuncExpr、OpExpr、DistinctExpr、NullIfExpr 分支；执行器为
 *      execExprInterp.c 的 EEOP_FUNCEXPR* 系列步骤。
 * ============================================================================
 */
static void
ExecInitFunc(ExprEvalStep *scratch, Expr *node, List *args, Oid funcid,
			 Oid inputcollid, ExprState *state)
{
	int			nargs = list_length(args);
	AclResult	aclresult;
	FmgrInfo   *flinfo;
	FunctionCallInfo fcinfo;
	int			argno;
	ListCell   *lc;

	/* Check permission to call function */
	aclresult = object_aclcheck(ProcedureRelationId, funcid, GetUserId(), ACL_EXECUTE);
	if (aclresult != ACLCHECK_OK)
		aclcheck_error(aclresult, OBJECT_FUNCTION, get_func_name(funcid));
	InvokeFunctionExecuteHook(funcid);

	/*
	 * Safety check on nargs.  Under normal circumstances this should never
	 * fail, as parser should check sooner.  But possibly it might fail if
	 * server has been compiled with FUNC_MAX_ARGS smaller than some functions
	 * declared in pg_proc?
	 */
	if (nargs > FUNC_MAX_ARGS)
		ereport(ERROR,
				(errcode(ERRCODE_TOO_MANY_ARGUMENTS),
				 errmsg_plural("cannot pass more than %d argument to a function",
							   "cannot pass more than %d arguments to a function",
							   FUNC_MAX_ARGS,
							   FUNC_MAX_ARGS)));

	/* Allocate function lookup data and parameter workspace for this call */
	scratch->d.func.finfo = palloc0_object(FmgrInfo);
	scratch->d.func.fcinfo_data = palloc0(SizeForFunctionCallInfo(nargs));
	flinfo = scratch->d.func.finfo;
	fcinfo = scratch->d.func.fcinfo_data;

	/* Set up the primary fmgr lookup information */
	fmgr_info(funcid, flinfo);
	fmgr_info_set_expr((Node *) node, flinfo);

	/* Initialize function call parameter structure too */
	InitFunctionCallInfoData(*fcinfo, flinfo,
							 nargs, inputcollid, NULL, NULL);

	/* Keep extra copies of this info to save an indirection at runtime */
	scratch->d.func.fn_addr = flinfo->fn_addr;
	scratch->d.func.nargs = nargs;

	/* We only support non-set functions here */
	if (flinfo->fn_retset)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("set-valued function called in context that cannot accept a set"),
				 state->parent ?
				 executor_errposition(state->parent->state,
									  exprLocation((Node *) node)) : 0));

	/* Build code to evaluate arguments directly into the fcinfo struct */
	argno = 0;
	foreach(lc, args)
	{
		Expr	   *arg = (Expr *) lfirst(lc);

		if (IsA(arg, Const))
		{
			/*
			 * Don't evaluate const arguments every round; especially
			 * interesting for constants in comparisons.
			 */
			Const	   *con = (Const *) arg;

			fcinfo->args[argno].value = con->constvalue;
			fcinfo->args[argno].isnull = con->constisnull;
		}
		else
		{
			ExecInitExprRec(arg, state,
							&fcinfo->args[argno].value,
							&fcinfo->args[argno].isnull);
		}
		argno++;
	}

	/* Insert appropriate opcode depending on strictness and stats level */
	if (pgstat_track_functions <= flinfo->fn_stats)
	{
		if (flinfo->fn_strict && nargs > 0)
		{
			/* Choose nargs optimized implementation if available. */
			if (nargs == 1)
				scratch->opcode = EEOP_FUNCEXPR_STRICT_1;
			else if (nargs == 2)
				scratch->opcode = EEOP_FUNCEXPR_STRICT_2;
			else
				scratch->opcode = EEOP_FUNCEXPR_STRICT;
		}
		else
			scratch->opcode = EEOP_FUNCEXPR;
	}
	else
	{
		if (flinfo->fn_strict && nargs > 0)
			scratch->opcode = EEOP_FUNCEXPR_STRICT_FUSAGE;
		else
			scratch->opcode = EEOP_FUNCEXPR_FUSAGE;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecInitSubPlanExpr —— 编译普通子计划表达式（含参数传递步骤）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为 SubPlan 节点生成三类步骤：①对每个 parParam 参数，"求参数表达式 →
 *   EEOP_PARAM_SET 写入参数槽"；②调用 ExecInitSubPlan 初始化真正的子计划状态
 *   （SubPlanState，登记进父节点 PlanState 的 subPlan 列表）；③EEOP_SUBPLAN
 *   步骤（运行时执行子计划并把结果写到 resv/resnull）。
 *
 * 参数：
 *   subplan   - 子计划表达式（规划器已设定参数对应关系 parParam/args）。
 *   state     - 所属 ExprState（其 parent 必须非空——子计划必须有宿主计划）。
 *   resv/resnull - 子计划结果的存放位置。
 *
 * 设计思想：
 *   1. 参数约定：先求参数表达式，再立刻用 EEOP_PARAM_SET 把值存进
 *      es_param_exec_vals[paramid]。特意"先求到 resv/resnull 再赋值"而不是直接
 *      求进参数槽——避免生成代码对参数槽指针稳定性的依赖；多个参数共享
 *      resv/resnull 是安全的，因为每个求值后紧跟一次 PARAM_SET 落盘。
 *   2. 参数值的生命周期：参数只需活到子计划执行完毕，放在父 econtext 即可；
 *      真正进入子查询的值在 ExecutorRun 时由 es_param_exec_vals 传递。
 *   3. MULTIEXPR 子计划不走本函数（由 setup 阶段提前整体执行，见
 *      ExecPushExprSetupSteps），且其运行结果不同于普通子计划——见
 *      ExecInitExprRec 的 T_SubPlan 分支。
 * ============================================================================
 */
static void
ExecInitSubPlanExpr(SubPlan *subplan,
					ExprState *state,
					Datum *resv, bool *resnull)
{
	ExprEvalStep scratch = {0};
	SubPlanState *sstate;
	ListCell   *pvar;
	ListCell   *l;

	if (!state->parent)
		elog(ERROR, "SubPlan found with no parent plan");

	/*
	 * Generate steps to evaluate input arguments for the subplan.
	 *
	 * We evaluate the argument expressions into resv/resnull, and then use
	 * PARAM_SET to update the parameter. We do that, instead of evaluating
	 * directly into the param, to avoid depending on the pointer value
	 * remaining stable / being included in the generated expression. It's ok
	 * to use resv/resnull for multiple params, as each parameter evaluation
	 * is immediately followed by an EEOP_PARAM_SET (and thus are saved before
	 * they could be overwritten again).
	 *
	 * Any calculation we have to do can be done in the parent econtext, since
	 * the Param values don't need to have per-query lifetime.
	 */
	Assert(list_length(subplan->parParam) == list_length(subplan->args));
	forboth(l, subplan->parParam, pvar, subplan->args)
	{
		int			paramid = lfirst_int(l);
		Expr	   *arg = (Expr *) lfirst(pvar);

		ExecInitExprRec(arg, state, resv, resnull);

		scratch.opcode = EEOP_PARAM_SET;
		scratch.resvalue = resv;
		scratch.resnull = resnull;
		scratch.d.param.paramid = paramid;
		/* paramtype's not actually used, but we might as well fill it */
		scratch.d.param.paramtype = exprType((Node *) arg);
		ExprEvalPushStep(state, &scratch);
	}

	sstate = ExecInitSubPlan(subplan, state->parent);

	/* add SubPlanState nodes to state->parent->subPlan */
	state->parent->subPlan = lappend(state->parent->subPlan,
									 sstate);

	scratch.opcode = EEOP_SUBPLAN;
	scratch.resvalue = resv;
	scratch.resnull = resnull;
	scratch.d.subplan.sstate = sstate;

	ExprEvalPushStep(state, &scratch);
}

/*
 * ============================================================================
 * 【中文注释】ExecCreateExprSetupSteps / ExecPushExprSetupSteps —— 生成表达式 setup 步骤
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   ExecCreateExprSetupSteps：对整棵表达式做一次预扫描（expr_setup_walker）得到
 *   ExprSetupInfo，再调用 ExecPushExprSetupSteps 生成步骤。
 *   ExecPushExprSetupSteps：按 Info 生成两类"前置"步骤——
 *   ①当表达式引用 inner/outer/scan/old/new 槽的 Var 时，按"所需最大属性号"生成
 *     对应的 EEOP_*_FETCHSOME 变形步骤（让元组在求值前被 deform 到足够深度，
 *     一次变形、多列共用）；
 *   ②对每个 MULTIEXPR SubPlan 生成执行步骤（必须在引用其输出参数的 Param 被
 *     求值之前完成）。
 *
 * 参数：
 *   state - 目标 ExprState；
 *   node  -（Create 版）表达式树根；info -（Push 版）预扫描统计结果。
 *
 * 设计思想：
 *   1. "先 setup 后主体"的顺序保证不变式：FETCHSOME 步骤恒位于所有求值步骤
 *      之前；deform 是元组级一次性开销，只做到所需列数，窄列场景收益显著。
 *   2. FETCHSOME 是否真正需要经过 ExecComputeSlotInfo 判定（固定且虚拟的槽
 *      已变形完成，可免步骤），返回 false 时不入栈。
 *   3. MULTIEXPR 子计划之间不存在相互引用，按收集顺序执行即可；其输出以
 *      PARAM_EXEC 形式被主体表达式引用。
 *   4. ExecPushExprSetupSteps 还被 ExecBuildUpdateProjection 与
 *      ExecBuildAggTrans 复用，以支持"一个 ExprState 覆盖多个表达式"的场景。
 * ============================================================================
 */
static void
ExecCreateExprSetupSteps(ExprState *state, Node *node)
{
	ExprSetupInfo info = {0, 0, 0, 0, 0, NIL};

	/* Prescan to find out what we need. */
	expr_setup_walker(node, &info);

	/* And generate those steps. */
	ExecPushExprSetupSteps(state, &info);
}

static void
ExecPushExprSetupSteps(ExprState *state, ExprSetupInfo *info)
{
	ExprEvalStep scratch = {0};
	ListCell   *lc;

	scratch.resvalue = NULL;
	scratch.resnull = NULL;

	/*
	 * Add steps deforming the ExprState's inner/outer/scan/old/new slots as
	 * much as required by any Vars appearing in the expression.
	 */
	if (info->last_inner > 0)
	{
		scratch.opcode = EEOP_INNER_FETCHSOME;
		scratch.d.fetch.last_var = info->last_inner;
		scratch.d.fetch.fixed = false;
		scratch.d.fetch.kind = NULL;
		scratch.d.fetch.known_desc = NULL;
		if (ExecComputeSlotInfo(state, &scratch))
			ExprEvalPushStep(state, &scratch);
	}
	if (info->last_outer > 0)
	{
		scratch.opcode = EEOP_OUTER_FETCHSOME;
		scratch.d.fetch.last_var = info->last_outer;
		scratch.d.fetch.fixed = false;
		scratch.d.fetch.kind = NULL;
		scratch.d.fetch.known_desc = NULL;
		if (ExecComputeSlotInfo(state, &scratch))
			ExprEvalPushStep(state, &scratch);
	}
	if (info->last_scan > 0)
	{
		scratch.opcode = EEOP_SCAN_FETCHSOME;
		scratch.d.fetch.last_var = info->last_scan;
		scratch.d.fetch.fixed = false;
		scratch.d.fetch.kind = NULL;
		scratch.d.fetch.known_desc = NULL;
		if (ExecComputeSlotInfo(state, &scratch))
			ExprEvalPushStep(state, &scratch);
	}
	if (info->last_old > 0)
	{
		scratch.opcode = EEOP_OLD_FETCHSOME;
		scratch.d.fetch.last_var = info->last_old;
		scratch.d.fetch.fixed = false;
		scratch.d.fetch.kind = NULL;
		scratch.d.fetch.known_desc = NULL;
		if (ExecComputeSlotInfo(state, &scratch))
			ExprEvalPushStep(state, &scratch);
	}
	if (info->last_new > 0)
	{
		scratch.opcode = EEOP_NEW_FETCHSOME;
		scratch.d.fetch.last_var = info->last_new;
		scratch.d.fetch.fixed = false;
		scratch.d.fetch.kind = NULL;
		scratch.d.fetch.known_desc = NULL;
		if (ExecComputeSlotInfo(state, &scratch))
			ExprEvalPushStep(state, &scratch);
	}

	/*
	 * Add steps to execute any MULTIEXPR SubPlans appearing in the
	 * expression.  We need to evaluate these before any of the Params
	 * referencing their outputs are used, but after we've prepared for any
	 * Var references they may contain.  (There cannot be cross-references
	 * between MULTIEXPR SubPlans, so we needn't worry about their order.)
	 */
	foreach(lc, info->multiexpr_subplans)
	{
		SubPlan    *subplan = (SubPlan *) lfirst(lc);

		Assert(subplan->subLinkType == MULTIEXPR_SUBLINK);

		/* The result can be ignored, but we better put it somewhere */
		ExecInitSubPlanExpr(subplan, state,
							&state->resvalue, &state->resnull);
	}
}

/*
 * ============================================================================
 * 【中文注释】expr_setup_walker —— 表达式预扫描：统计槽位需求与 MULTIEXPR 子计划
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   递归遍历表达式树并维护 ExprSetupInfo：按 varno 把引用的 Var 的最大属性号
 *   记入 last_inner/last_outer/last_scan/last_old/last_new（OLD/NEW 按
 *   varreturningtype 区分），把遇到的 MULTIEXPR SubPlan 收集到
 *   multiexpr_subplans。
 *
 * 参数：
 *   node - 当前节点；info - 累计统计结果（多处复用同一结构以合并需求）。
 *
 * 返回值：
 *   bool - expression_tree_walker 约定（true 提前终止）；本函数总是遍历完整棵树，
 *          返回 false。
 *
 * 设计思想：
 *   1. 属性号取 Max 即可：FETCHSOME 按最大列变形后，更小的列号自然可用；
 *      负属性号（系统列）不影响 last_* > 0 的判定。
 *   2. Aggref/WindowFunc/GroupingFunc 的参数不求值在当前 econtext（聚合参数
 *      的求值归聚合执行器管，窗口函数同），故不深入其内部；GroupingFunc 参数
 *      根本不求值。
 *   3. 这是"两遍编译"里的第一遍（轻量只读统计），真正的步骤生成由
 *      ExecInitExprRec 在第二遍完成。
 * ============================================================================
 */
static bool
expr_setup_walker(Node *node, ExprSetupInfo *info)
{
	if (node == NULL)
		return false;
	if (IsA(node, Var))
	{
		Var		   *variable = (Var *) node;
		AttrNumber	attnum = variable->varattno;

		switch (variable->varno)
		{
			case INNER_VAR:
				info->last_inner = Max(info->last_inner, attnum);
				break;

			case OUTER_VAR:
				info->last_outer = Max(info->last_outer, attnum);
				break;

				/* INDEX_VAR is handled by default case */

			default:
				switch (variable->varreturningtype)
				{
					case VAR_RETURNING_DEFAULT:
						info->last_scan = Max(info->last_scan, attnum);
						break;
					case VAR_RETURNING_OLD:
						info->last_old = Max(info->last_old, attnum);
						break;
					case VAR_RETURNING_NEW:
						info->last_new = Max(info->last_new, attnum);
						break;
				}
				break;
		}
		return false;
	}

	/* Collect all MULTIEXPR SubPlans, too */
	if (IsA(node, SubPlan))
	{
		SubPlan    *subplan = (SubPlan *) node;

		if (subplan->subLinkType == MULTIEXPR_SUBLINK)
			info->multiexpr_subplans = lappend(info->multiexpr_subplans,
											   subplan);
	}

	/*
	 * Don't examine the arguments or filters of Aggrefs or WindowFuncs,
	 * because those do not represent expressions to be evaluated within the
	 * calling expression's econtext.  GroupingFunc arguments are never
	 * evaluated at all.
	 */
	if (IsA(node, Aggref))
		return false;
	if (IsA(node, WindowFunc))
		return false;
	if (IsA(node, GroupingFunc))
		return false;
	return expression_tree_walker(node, expr_setup_walker, info);
}

/*
 * ============================================================================
 * 【中文注释】ExecComputeSlotInfo —— 判定 FETCHSOME 步骤的"固定性"（固定槽优化）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为一条 EEOP_*_FETCHSOME 步骤确定是否"固定"：若每次求值都会遇到相同类型的
 *   槽、相同描述符，则把 tts_ops 与描述符直接烘焙进步骤（固定路径，运行时免去
 *   动态判定），否则以"运行时检查"模式执行；并返回该步骤是否真的需要入栈。
 *
 * 参数：
 *   state - 所属 ExprState（其 parent 提供 innerops/outerops/scanops 等信息）。
 *   op    - 待分析的 FETCHSOME 步骤（opcode 决定查询哪个槽）。
 *
 * 返回值：
 *   bool - true 需要生成该步骤；false 无需（如固定且恒为虚拟槽——虚拟槽的
 *          数据天然已变形，再变形是浪费）。
 *
 * 设计思想：
 *   1. 信息出处：inner/outer 槽看 parent->innerops/outerops 与相应子计划结果
 *      类型；scan/old/new 槽统一看 parent->scandesc 与 scanops（OLD/NEW 的
 *      描述符同样来自父扫描节点，仅槽位不同）。注意 inneropsset 但
 *      !inneropsfixed 的情况（中继算子可换槽型），此时不能烘焙。
 *   2. 未固定时以通用模式运行：每次按实际槽类型决定变形方式，正确性优先。
 *   3. 特例豁免：固定且为 TTSOpsVirtual 时直接返回 false——虚拟槽的 datums
 *      数组就是"变形后"形态，FETCHSOME 无意义；这正是把"deform 决策"前移到
 *      编译期的收益。
 * ============================================================================
 */
static bool
ExecComputeSlotInfo(ExprState *state, ExprEvalStep *op)
{
	PlanState  *parent = state->parent;
	TupleDesc	desc = NULL;
	const TupleTableSlotOps *tts_ops = NULL;
	bool		isfixed = false;
	ExprEvalOp	opcode = op->opcode;

	Assert(opcode == EEOP_INNER_FETCHSOME ||
		   opcode == EEOP_OUTER_FETCHSOME ||
		   opcode == EEOP_SCAN_FETCHSOME ||
		   opcode == EEOP_OLD_FETCHSOME ||
		   opcode == EEOP_NEW_FETCHSOME);

	if (op->d.fetch.known_desc != NULL)
	{
		desc = op->d.fetch.known_desc;
		tts_ops = op->d.fetch.kind;
		isfixed = op->d.fetch.kind != NULL;
	}
	else if (!parent)
	{
		isfixed = false;
	}
	else if (opcode == EEOP_INNER_FETCHSOME)
	{
		PlanState  *is = innerPlanState(parent);

		if (parent->inneropsset && !parent->inneropsfixed)
		{
			isfixed = false;
		}
		else if (parent->inneropsset && parent->innerops)
		{
			isfixed = true;
			tts_ops = parent->innerops;
			desc = ExecGetResultType(is);
		}
		else if (is)
		{
			tts_ops = ExecGetResultSlotOps(is, &isfixed);
			desc = ExecGetResultType(is);
		}
	}
	else if (opcode == EEOP_OUTER_FETCHSOME)
	{
		PlanState  *os = outerPlanState(parent);

		if (parent->outeropsset && !parent->outeropsfixed)
		{
			isfixed = false;
		}
		else if (parent->outeropsset && parent->outerops)
		{
			isfixed = true;
			tts_ops = parent->outerops;
			desc = ExecGetResultType(os);
		}
		else if (os)
		{
			tts_ops = ExecGetResultSlotOps(os, &isfixed);
			desc = ExecGetResultType(os);
		}
	}
	else if (opcode == EEOP_SCAN_FETCHSOME ||
			 opcode == EEOP_OLD_FETCHSOME ||
			 opcode == EEOP_NEW_FETCHSOME)
	{
		desc = parent->scandesc;

		if (parent->scanops)
			tts_ops = parent->scanops;

		if (parent->scanopsset)
			isfixed = parent->scanopsfixed;
	}

	if (isfixed && desc != NULL && tts_ops != NULL)
	{
		op->d.fetch.fixed = true;
		op->d.fetch.kind = tts_ops;
		op->d.fetch.known_desc = desc;
	}
	else
	{
		op->d.fetch.fixed = false;
		op->d.fetch.kind = NULL;
		op->d.fetch.known_desc = NULL;
	}

	/* if the slot is known to always virtual we never need to deform */
	if (op->d.fetch.fixed && op->d.fetch.kind == &TTSOpsVirtual)
		return false;

	return true;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitWholeRowVar —— 编译整行 Var（表.* / row.*）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   生成 EEOP_WHOLEROW 步骤的固定字段：记录 Var、首次标志、tupdesc（运行时
 *   填写）与可选的 JunkFilter——用于剔除子查询结果里的 resjunk 列（GROUP BY/
 *   ORDER BY 列），保证整行值只含用户可见列。调用方仍需 push 该步骤。
 *
 * 参数：
 *   scratch  - 待填充步骤；variable - 整行 Var（varattno == 0）；
 *   state    - 所属 ExprState（parent 用于判断是否可能带 junk 列）。
 *
 * 设计思想：
 *   1. 只有父节点是 SubqueryScanState / CteScanState 时输入才可能含 resjunk
 *      列（子查询投影），因此仅在这两种父节点下检查子计划 tlist 并按需构建
 *      JunkFilter（用父 EState 的额外虚拟槽承接清洗结果）；独立表达式（无
 *      parent）假定引用的是普通表行，无需过滤。
 *   2. OLD/NEW 整行引用同样置 EEO_FLAG_HAS_OLD/NEW，使执行器准备对应槽位。
 *   3. tupdesc 延迟到运行时由槽描述符填充，避免编译期与运行时描述符漂移。
 * ============================================================================
 */
static void
ExecInitWholeRowVar(ExprEvalStep *scratch, Var *variable, ExprState *state)
{
	PlanState  *parent = state->parent;

	/* fill in all but the target */
	scratch->opcode = EEOP_WHOLEROW;
	scratch->d.wholerow.var = variable;
	scratch->d.wholerow.first = true;
	scratch->d.wholerow.slow = false;
	scratch->d.wholerow.tupdesc = NULL; /* filled at runtime */
	scratch->d.wholerow.junkFilter = NULL;

	/* update ExprState flags if Var refers to OLD/NEW */
	if (variable->varreturningtype == VAR_RETURNING_OLD)
		state->flags |= EEO_FLAG_HAS_OLD;
	else if (variable->varreturningtype == VAR_RETURNING_NEW)
		state->flags |= EEO_FLAG_HAS_NEW;

	/*
	 * If the input tuple came from a subquery, it might contain "resjunk"
	 * columns (such as GROUP BY or ORDER BY columns), which we don't want to
	 * keep in the whole-row result.  We can get rid of such columns by
	 * passing the tuple through a JunkFilter --- but to make one, we have to
	 * lay our hands on the subquery's targetlist.  Fortunately, there are not
	 * very many cases where this can happen, and we can identify all of them
	 * by examining our parent PlanState.  We assume this is not an issue in
	 * standalone expressions that don't have parent plans.  (Whole-row Vars
	 * can occur in such expressions, but they will always be referencing
	 * table rows.)
	 */
	if (parent)
	{
		PlanState  *subplan = NULL;

		switch (nodeTag(parent))
		{
			case T_SubqueryScanState:
				subplan = ((SubqueryScanState *) parent)->subplan;
				break;
			case T_CteScanState:
				subplan = ((CteScanState *) parent)->cteplanstate;
				break;
			default:
				break;
		}

		if (subplan)
		{
			bool		junk_filter_needed = false;
			ListCell   *tlist;

			/* Detect whether subplan tlist actually has any junk columns */
			foreach(tlist, subplan->plan->targetlist)
			{
				TargetEntry *tle = (TargetEntry *) lfirst(tlist);

				if (tle->resjunk)
				{
					junk_filter_needed = true;
					break;
				}
			}

			/* If so, build the junkfilter now */
			if (junk_filter_needed)
			{
				scratch->d.wholerow.junkFilter =
					ExecInitJunkFilter(subplan->plan->targetlist,
									   ExecInitExtraTupleSlot(parent->state, NULL,
															  &TTSOpsVirtual));
			}
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecInitSubscriptingRef —— 编译下标访问/赋值（数组 arr[i]、切片等）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 SubscriptingRef（读：arr[i]；写：arr[i] := v，含切片与嵌套赋值）编译成
 *   一组步骤：求容器表达式 → 可选 NULL 短路 → 求上/下界下标 → 下标检查（可选）
 *   → 取旧值（仅嵌套赋值需要）→ 求替换值 → EEOP_SBSREF_FETCH/ASSIGN 收尾。
 *   下标计算、旧值提取、赋值等"容器类型相关"操作全部经由 SubscriptRoutines
 *   的回调（exec_setup 填好的 methods）委托给类型特定实现（数组、可下标化
 *   复合类型等）。
 *
 * 参数：
 *   scratch - 步骤工作区（sbsref 相关字段）；sbsref - 下标引用节点；
 *   state   - 所属 ExprState（innermost_caseval 等上下文）；
 *   resv/resnull - 结果存放地址。
 *
 * 设计思想：
 *   1. SubscriptingRefState 一次性 palloc 出 上/下界 Datum、是否提供、是否 NULL
 *      六组数组（连续内存，避免多次小分配）；切片时某边界表达式为 NULL 表示
 *      省略，记 provided=false 由类型代码解释。
 *   2. 容器表达式可以安全地直接求进 resv/resnull（最后的 FETCH/ASSIGN 步骤
 *      一定覆盖它）。严格取值的类型（fetch_strict，如数组"元素为 NULL"语义）
 *      在容器为 NULL 时直接跳到结尾返回 NULL——EEOP_JUMP_IF_NULL 天然实现
 *      NULL 传播。
 *   3. 嵌套赋值（a[i].f := v）的旧值传递复用 CaseTestExpr 机制：仅当替换表达式
 *      是"赋值间接表达式"（isAssignmentIndirectionExpr）且类型支持取旧值时，
 *      才生成 EEOP_SBSREF_OLD 把旧元素取到 prevvalue/prevnull 并设为
 *      innermost_caseval；普通单层赋值不产生该开销。
 *   4. 跳转目标（NULL 短路与下标检查失败）统一在最后回填，模式与其他分支一致。
 * ============================================================================
 */
static void
ExecInitSubscriptingRef(ExprEvalStep *scratch, SubscriptingRef *sbsref,
						ExprState *state, Datum *resv, bool *resnull)
{
	bool		isAssignment = (sbsref->refassgnexpr != NULL);
	int			nupper = list_length(sbsref->refupperindexpr);
	int			nlower = list_length(sbsref->reflowerindexpr);
	const SubscriptRoutines *sbsroutines;
	SubscriptingRefState *sbsrefstate;
	SubscriptExecSteps methods;
	char	   *ptr;
	List	   *adjust_jumps = NIL;
	ListCell   *lc;
	int			i;

	/* Look up the subscripting support methods */
	sbsroutines = getSubscriptingRoutines(sbsref->refcontainertype, NULL);
	if (!sbsroutines)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("cannot subscript type %s because it does not support subscripting",
						format_type_be(sbsref->refcontainertype)),
				 state->parent ?
				 executor_errposition(state->parent->state,
									  exprLocation((Node *) sbsref)) : 0));

	/* Allocate sbsrefstate, with enough space for per-subscript arrays too */
	sbsrefstate = palloc0(MAXALIGN(sizeof(SubscriptingRefState)) +
						  (nupper + nlower) * (sizeof(Datum) +
											   2 * sizeof(bool)));

	/* Fill constant fields of SubscriptingRefState */
	sbsrefstate->isassignment = isAssignment;
	sbsrefstate->numupper = nupper;
	sbsrefstate->numlower = nlower;
	/* Set up per-subscript arrays */
	ptr = ((char *) sbsrefstate) + MAXALIGN(sizeof(SubscriptingRefState));
	sbsrefstate->upperindex = (Datum *) ptr;
	ptr += nupper * sizeof(Datum);
	sbsrefstate->lowerindex = (Datum *) ptr;
	ptr += nlower * sizeof(Datum);
	sbsrefstate->upperprovided = (bool *) ptr;
	ptr += nupper * sizeof(bool);
	sbsrefstate->lowerprovided = (bool *) ptr;
	ptr += nlower * sizeof(bool);
	sbsrefstate->upperindexnull = (bool *) ptr;
	ptr += nupper * sizeof(bool);
	sbsrefstate->lowerindexnull = (bool *) ptr;
	/* ptr += nlower * sizeof(bool); */

	/*
	 * Let the container-type-specific code have a chance.  It must fill the
	 * "methods" struct with function pointers for us to possibly use in
	 * execution steps below; and it can optionally set up some data pointed
	 * to by the workspace field.
	 */
	memset(&methods, 0, sizeof(methods));
	sbsroutines->exec_setup(sbsref, sbsrefstate, &methods);

	/*
	 * Evaluate array input.  It's safe to do so into resv/resnull, because we
	 * won't use that as target for any of the other subexpressions, and it'll
	 * be overwritten by the final EEOP_SBSREF_FETCH/ASSIGN step, which is
	 * pushed last.
	 */
	ExecInitExprRec(sbsref->refexpr, state, resv, resnull);

	/*
	 * If refexpr yields NULL, and the operation should be strict, then result
	 * is NULL.  We can implement this with just JUMP_IF_NULL, since we
	 * evaluated the array into the desired target location.
	 */
	if (!isAssignment && sbsroutines->fetch_strict)
	{
		scratch->opcode = EEOP_JUMP_IF_NULL;
		scratch->d.jump.jumpdone = -1;	/* adjust later */
		ExprEvalPushStep(state, scratch);
		adjust_jumps = lappend_int(adjust_jumps,
								   state->steps_len - 1);
	}

	/* Evaluate upper subscripts */
	i = 0;
	foreach(lc, sbsref->refupperindexpr)
	{
		Expr	   *e = (Expr *) lfirst(lc);

		/* When slicing, individual subscript bounds can be omitted */
		if (!e)
		{
			sbsrefstate->upperprovided[i] = false;
			sbsrefstate->upperindexnull[i] = true;
		}
		else
		{
			sbsrefstate->upperprovided[i] = true;
			/* Each subscript is evaluated into appropriate array entry */
			ExecInitExprRec(e, state,
							&sbsrefstate->upperindex[i],
							&sbsrefstate->upperindexnull[i]);
		}
		i++;
	}

	/* Evaluate lower subscripts similarly */
	i = 0;
	foreach(lc, sbsref->reflowerindexpr)
	{
		Expr	   *e = (Expr *) lfirst(lc);

		/* When slicing, individual subscript bounds can be omitted */
		if (!e)
		{
			sbsrefstate->lowerprovided[i] = false;
			sbsrefstate->lowerindexnull[i] = true;
		}
		else
		{
			sbsrefstate->lowerprovided[i] = true;
			/* Each subscript is evaluated into appropriate array entry */
			ExecInitExprRec(e, state,
							&sbsrefstate->lowerindex[i],
							&sbsrefstate->lowerindexnull[i]);
		}
		i++;
	}

	/* SBSREF_SUBSCRIPTS checks and converts all the subscripts at once */
	if (methods.sbs_check_subscripts)
	{
		scratch->opcode = EEOP_SBSREF_SUBSCRIPTS;
		scratch->d.sbsref_subscript.subscriptfunc = methods.sbs_check_subscripts;
		scratch->d.sbsref_subscript.state = sbsrefstate;
		scratch->d.sbsref_subscript.jumpdone = -1;	/* adjust later */
		ExprEvalPushStep(state, scratch);
		adjust_jumps = lappend_int(adjust_jumps,
								   state->steps_len - 1);
	}

	if (isAssignment)
	{
		Datum	   *save_innermost_caseval;
		bool	   *save_innermost_casenull;

		/* Check for unimplemented methods */
		if (!methods.sbs_assign)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("type %s does not support subscripted assignment",
							format_type_be(sbsref->refcontainertype))));

		/*
		 * We might have a nested-assignment situation, in which the
		 * refassgnexpr is itself a FieldStore or SubscriptingRef that needs
		 * to obtain and modify the previous value of the array element or
		 * slice being replaced.  If so, we have to extract that value from
		 * the array and pass it down via the CaseTestExpr mechanism.  It's
		 * safe to reuse the CASE mechanism because there cannot be a CASE
		 * between here and where the value would be needed, and an array
		 * assignment can't be within a CASE either.  (So saving and restoring
		 * innermost_caseval is just paranoia, but let's do it anyway.)
		 *
		 * Since fetching the old element might be a nontrivial expense, do it
		 * only if the argument actually needs it.
		 */
		if (isAssignmentIndirectionExpr(sbsref->refassgnexpr))
		{
			if (!methods.sbs_fetch_old)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("type %s does not support subscripted assignment",
								format_type_be(sbsref->refcontainertype))));
			scratch->opcode = EEOP_SBSREF_OLD;
			scratch->d.sbsref.subscriptfunc = methods.sbs_fetch_old;
			scratch->d.sbsref.state = sbsrefstate;
			ExprEvalPushStep(state, scratch);
		}

		/* SBSREF_OLD puts extracted value into prevvalue/prevnull */
		save_innermost_caseval = state->innermost_caseval;
		save_innermost_casenull = state->innermost_casenull;
		state->innermost_caseval = &sbsrefstate->prevvalue;
		state->innermost_casenull = &sbsrefstate->prevnull;

		/* evaluate replacement value into replacevalue/replacenull */
		ExecInitExprRec(sbsref->refassgnexpr, state,
						&sbsrefstate->replacevalue, &sbsrefstate->replacenull);

		state->innermost_caseval = save_innermost_caseval;
		state->innermost_casenull = save_innermost_casenull;

		/* and perform the assignment */
		scratch->opcode = EEOP_SBSREF_ASSIGN;
		scratch->d.sbsref.subscriptfunc = methods.sbs_assign;
		scratch->d.sbsref.state = sbsrefstate;
		ExprEvalPushStep(state, scratch);
	}
	else
	{
		/* array fetch is much simpler */
		scratch->opcode = EEOP_SBSREF_FETCH;
		scratch->d.sbsref.subscriptfunc = methods.sbs_fetch;
		scratch->d.sbsref.state = sbsrefstate;
		ExprEvalPushStep(state, scratch);
	}

	/* adjust jump targets */
	foreach(lc, adjust_jumps)
	{
		ExprEvalStep *as = &state->steps[lfirst_int(lc)];

		if (as->opcode == EEOP_SBSREF_SUBSCRIPTS)
		{
			Assert(as->d.sbsref_subscript.jumpdone == -1);
			as->d.sbsref_subscript.jumpdone = state->steps_len;
		}
		else
		{
			Assert(as->opcode == EEOP_JUMP_IF_NULL);
			Assert(as->d.jump.jumpdone == -1);
			as->d.jump.jumpdone = state->steps_len;
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】isAssignmentIndirectionExpr —— 判定赋值目标是否为"嵌套赋值"表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判断替换表达式（SubscriptingRef 的 refassgnexpr）是否直接或间接（透过
 *   CoerceToDomain/RelabelType）需要"旧值"输入——即其 arg/refexpr 是
 *   CaseTestExpr 的 FieldStore/SubscriptingRef。用于决定是否需要生成取旧元素
 *   步骤（EEOP_SBSREF_OLD）。
 *
 * 参数：
 *   expr - 赋值目标表达式（可为 NULL）。
 *
 * 返回值：
 *   bool - true 表示需要旧值。
 *
 * 设计思想：
 *   1. 不需要递归深挖：嵌套赋值结构里每层都有各自的 CaseTestExpr，且顶层节点的
 *      arg/refexpr 就是该 CaseTestExpr 的直接位置；唯一例外是"数组元素为域类型"
 *      时外层有 CoerceToDomain/RelabelType 包着，因此只对这两种节点递归一层。
 *   2. FieldStore 不采用本判定：FieldStore 里传旧值几乎零成本，无条件传输即可；
 *      只有数组/切片的取旧值可能有明显开销，才按需生成。
 * ============================================================================
 */
static bool
isAssignmentIndirectionExpr(Expr *expr)
{
	if (expr == NULL)
		return false;			/* just paranoia */
	if (IsA(expr, FieldStore))
	{
		FieldStore *fstore = (FieldStore *) expr;

		if (fstore->arg && IsA(fstore->arg, CaseTestExpr))
			return true;
	}
	else if (IsA(expr, SubscriptingRef))
	{
		SubscriptingRef *sbsRef = (SubscriptingRef *) expr;

		if (sbsRef->refexpr && IsA(sbsRef->refexpr, CaseTestExpr))
			return true;
	}
	else if (IsA(expr, CoerceToDomain))
	{
		CoerceToDomain *cd = (CoerceToDomain *) expr;

		return isAssignmentIndirectionExpr(cd->arg);
	}
	else if (IsA(expr, RelabelType))
	{
		RelabelType *r = (RelabelType *) expr;

		return isAssignmentIndirectionExpr(r->arg);
	}
	return false;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitCoerceToDomain —— 编译域类型强转（含全体约束检查）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为 CoerceToDomain 生成步骤序列：先求值参数（直接写 resv/resnull——约束失败
 *   会抛错，成功即最终结果），再把域上定义的全部约束编译成步骤：
 *   NOT NULL 约束 → EEOP_DOMAIN_NOTNULL；CHECK 约束 → 以 CoerceToDomainValue
 *   机制把待检值传给检查表达式，再用 EEOP_DOMAIN_CHECK 判定结果。
 *
 * 参数：
 *   scratch - 步骤工作区（domaincheck 字段）；ctest - 域强转节点；
 *   state   - 所属 ExprState；resv/resnull - 结果地址。
 *
 * 设计思想：
 *   1. 约束在编译期"烘焙"进 ExprState（v10 起不再每次求值重查约束集），用
 *      DomainConstraintRef 锁定约束集合（内含检查表达式）。
 *   2. 检查值通道：域检查表达式经 CoerceToDomainValue 节点读
 *      innermost_domainval（编译为 EEOP_DOMAIN_TESTVAL）；嵌套域检查时保存/
 *      恢复 innermost_domainval，保证任意嵌套深度正确。
 *   3. varlena（可能是可写展开对象）且确有 CHECK 时插入 EEOP_MAKE_READONLY：
 *      检查函数可能改写共享值，必须只读形态参与检查，但最终结果仍返回原来的
 *      可写指针；非 varlena 直接以 resv/resnull 作检查源，零拷贝。
 *   4. 被调用方：ExecInitExprRec 的 T_CoerceToDomain 分支；运行时步骤为
 *      execExprInterp.c 的 EEOP_DOMAIN_* 系列。
 * ============================================================================
 */
static void
ExecInitCoerceToDomain(ExprEvalStep *scratch, CoerceToDomain *ctest,
					   ExprState *state, Datum *resv, bool *resnull)
{
	DomainConstraintRef *constraint_ref;
	Datum	   *domainval = NULL;
	bool	   *domainnull = NULL;
	ListCell   *l;

	scratch->d.domaincheck.resulttype = ctest->resulttype;
	/* we'll allocate workspace only if needed */
	scratch->d.domaincheck.checkvalue = NULL;
	scratch->d.domaincheck.checknull = NULL;
	scratch->d.domaincheck.escontext = state->escontext;

	/*
	 * Evaluate argument - it's fine to directly store it into resv/resnull,
	 * if there's constraint failures there'll be errors, otherwise it's what
	 * needs to be returned.
	 */
	ExecInitExprRec(ctest->arg, state, resv, resnull);

	/*
	 * Note: if the argument is of varlena type, it could be a R/W expanded
	 * object.  We want to return the R/W pointer as the final result, but we
	 * have to pass a R/O pointer as the value to be tested by any functions
	 * in check expressions.  We don't bother to emit a MAKE_READONLY step
	 * unless there's actually at least one check expression, though.  Until
	 * we've tested that, domainval/domainnull are NULL.
	 */

	/*
	 * Collect the constraints associated with the domain.
	 *
	 * Note: before PG v10 we'd recheck the set of constraints during each
	 * evaluation of the expression.  Now we bake them into the ExprState
	 * during executor initialization.  That means we don't need typcache.c to
	 * provide compiled exprs.
	 */
	constraint_ref = palloc_object(DomainConstraintRef);
	InitDomainConstraintRef(ctest->resulttype,
							constraint_ref,
							CurrentMemoryContext,
							false);

	/*
	 * Compile code to check each domain constraint.  NOTNULL constraints can
	 * just be applied on the resv/resnull value, but for CHECK constraints we
	 * need more pushups.
	 */
	foreach(l, constraint_ref->constraints)
	{
		DomainConstraintState *con = (DomainConstraintState *) lfirst(l);
		Datum	   *save_innermost_domainval;
		bool	   *save_innermost_domainnull;

		scratch->d.domaincheck.constraintname = con->name;

		switch (con->constrainttype)
		{
			case DOM_CONSTRAINT_NOTNULL:
				scratch->opcode = EEOP_DOMAIN_NOTNULL;
				ExprEvalPushStep(state, scratch);
				break;
			case DOM_CONSTRAINT_CHECK:
				/* Allocate workspace for CHECK output if we didn't yet */
				if (scratch->d.domaincheck.checkvalue == NULL)
				{
					scratch->d.domaincheck.checkvalue =
						palloc_object(Datum);
					scratch->d.domaincheck.checknull =
						palloc_object(bool);
				}

				/*
				 * If first time through, determine where CoerceToDomainValue
				 * nodes should read from.
				 */
				if (domainval == NULL)
				{
					/*
					 * Since value might be read multiple times, force to R/O
					 * - but only if it could be an expanded datum.
					 */
					if (get_typlen(ctest->resulttype) == -1)
					{
						ExprEvalStep scratch2 = {0};

						/* Yes, so make output workspace for MAKE_READONLY */
						domainval = palloc_object(Datum);
						domainnull = palloc_object(bool);

						/* Emit MAKE_READONLY */
						scratch2.opcode = EEOP_MAKE_READONLY;
						scratch2.resvalue = domainval;
						scratch2.resnull = domainnull;
						scratch2.d.make_readonly.value = resv;
						scratch2.d.make_readonly.isnull = resnull;
						ExprEvalPushStep(state, &scratch2);
					}
					else
					{
						/* No, so it's fine to read from resv/resnull */
						domainval = resv;
						domainnull = resnull;
					}
				}

				/*
				 * Set up value to be returned by CoerceToDomainValue nodes.
				 * We must save and restore innermost_domainval/null fields,
				 * in case this node is itself within a check expression for
				 * another domain.
				 */
				save_innermost_domainval = state->innermost_domainval;
				save_innermost_domainnull = state->innermost_domainnull;
				state->innermost_domainval = domainval;
				state->innermost_domainnull = domainnull;

				/* evaluate check expression value */
				ExecInitExprRec(con->check_expr, state,
								scratch->d.domaincheck.checkvalue,
								scratch->d.domaincheck.checknull);

				state->innermost_domainval = save_innermost_domainval;
				state->innermost_domainnull = save_innermost_domainnull;

				/* now test result */
				scratch->opcode = EEOP_DOMAIN_CHECK;
				ExprEvalPushStep(state, scratch);

				break;
			default:
				elog(ERROR, "unrecognized constraint type: %d",
					 (int) con->constrainttype);
				break;
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildAggTrans —— 构建聚合过渡函数求值表达式（含 grouping sets 批量）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为聚合执行器（AggState）构建一个 ExprState：对"一个阶段（phase）内"所有
 *   过渡函数调用，生成"过滤 → 求参数 → strict NULL 检查 → 调用过渡/合并函数"
 *   的步骤序列；排序型（doSort）与哈希型（doHash）可分别或同时覆盖，并按
 *   grouping sets 的数量展开（每个 set 一份 pergroup 状态）。
 *
 * 参数：
 *   aggstate - 聚合执行状态（pertrans/numtrans/aggcontexts/hashcontext 等）。
 *   phase    - 当前阶段（numsets 决定排序型展开份数）。
 *   doSort/doHash - 是否覆盖排序型/哈希型过渡调用。
 *   nullcheck- 是否生成"pergroup 状态为 NULL 指针即跳过"的检查（用于单趟
 *              交换式扫描中"新 group 尚无 pergroup 状态"的情形）。
 *
 * 返回值：
 *   ExprState* - 以 EEOP_DONE_NO_RETURN 收尾（结果写进 pergroup 状态而非返回）。
 *
 * 设计思想：
 *   1. 前置 setup：把所有过渡的 aggref 参数/排序/过滤表达式一次性统计并生成
 *      FETCHSOME 步骤——聚合输入往往同源（同一元组），合并变形优于逐表达式
 *      重复变形。
 *   2. 每个过渡的步骤顺序固定：aggfilter 最先求（避免无谓计算与副作用；合并
 *      模式 isCombine 已过滤完，不再求）→ 参数求值（合并模式下参数是经
 *      deserialfn 反序列化来的过渡值，见 EEOP_AGG_DESERIALIZE）→ strict 输入
 *      检查（存在 NULL 则跳过本次过渡，保留旧 transValue）→ 预排序 DISTINCT
 *      检查（EEOP_AGG_PRESORTED_DISTINCT_*）→ 为每个 grouping set 各生成一次
 *      ExecBuildAggTransCall（排序段 & 哈希段）。
 *   3. 所有"提前跳出"的跳转目标（adjust_bailout 列表）在整表达式编译完后统一
 *      回填。
 *   4. 该方法把"聚合每行的过渡函数调用"也变成步骤序列，使 JIT/解释器统一受益；
 *      参数结果下沉到 trans_fcinfo->args（0 号永远留给过渡值本身）。
 *   5. 被调用方：nodeAgg.c 的 ExecAgg 初始化（evaltrans/evaltrans_cache），
 *      phase 内每次切换分组集时使用缓存版本的 ExprState。
 * ============================================================================
 */
ExprState *
ExecBuildAggTrans(AggState *aggstate, AggStatePerPhase phase,
				  bool doSort, bool doHash, bool nullcheck)
{
	ExprState  *state = makeNode(ExprState);
	PlanState  *parent = &aggstate->ss.ps;
	ExprEvalStep scratch = {0};
	bool		isCombine = DO_AGGSPLIT_COMBINE(aggstate->aggsplit);
	ExprSetupInfo deform = {0, 0, 0, 0, 0, NIL};

	state->expr = (Expr *) aggstate;
	state->parent = parent;

	scratch.resvalue = &state->resvalue;
	scratch.resnull = &state->resnull;

	/*
	 * First figure out which slots, and how many columns from each, we're
	 * going to need.
	 */
	for (int transno = 0; transno < aggstate->numtrans; transno++)
	{
		AggStatePerTrans pertrans = &aggstate->pertrans[transno];

		expr_setup_walker((Node *) pertrans->aggref->aggdirectargs,
						  &deform);
		expr_setup_walker((Node *) pertrans->aggref->args,
						  &deform);
		expr_setup_walker((Node *) pertrans->aggref->aggorder,
						  &deform);
		expr_setup_walker((Node *) pertrans->aggref->aggdistinct,
						  &deform);
		expr_setup_walker((Node *) pertrans->aggref->aggfilter,
						  &deform);
	}
	ExecPushExprSetupSteps(state, &deform);

	/*
	 * Emit instructions for each transition value / grouping set combination.
	 */
	for (int transno = 0; transno < aggstate->numtrans; transno++)
	{
		AggStatePerTrans pertrans = &aggstate->pertrans[transno];
		FunctionCallInfo trans_fcinfo = pertrans->transfn_fcinfo;
		List	   *adjust_bailout = NIL;
		NullableDatum *strictargs = NULL;
		bool	   *strictnulls = NULL;
		int			argno;
		ListCell   *bail;

		/*
		 * If filter present, emit. Do so before evaluating the input, to
		 * avoid potentially unneeded computations, or even worse, unintended
		 * side-effects.  When combining, all the necessary filtering has
		 * already been done.
		 */
		if (pertrans->aggref->aggfilter && !isCombine)
		{
			/* evaluate filter expression */
			ExecInitExprRec(pertrans->aggref->aggfilter, state,
							&state->resvalue, &state->resnull);
			/* and jump out if false */
			scratch.opcode = EEOP_JUMP_IF_NOT_TRUE;
			scratch.d.jump.jumpdone = -1;	/* adjust later */
			ExprEvalPushStep(state, &scratch);
			adjust_bailout = lappend_int(adjust_bailout,
										 state->steps_len - 1);
		}

		/*
		 * Evaluate arguments to aggregate/combine function.
		 */
		argno = 0;
		if (isCombine)
		{
			/*
			 * Combining two aggregate transition values. Instead of directly
			 * coming from a tuple the input is a, potentially deserialized,
			 * transition value.
			 */
			TargetEntry *source_tle;

			Assert(pertrans->numSortCols == 0);
			Assert(list_length(pertrans->aggref->args) == 1);

			strictargs = trans_fcinfo->args + 1;
			source_tle = (TargetEntry *) linitial(pertrans->aggref->args);

			/*
			 * deserialfn_oid will be set if we must deserialize the input
			 * state before calling the combine function.
			 */
			if (!OidIsValid(pertrans->deserialfn_oid))
			{
				/*
				 * Start from 1, since the 0th arg will be the transition
				 * value
				 */
				ExecInitExprRec(source_tle->expr, state,
								&trans_fcinfo->args[argno + 1].value,
								&trans_fcinfo->args[argno + 1].isnull);
			}
			else
			{
				FunctionCallInfo ds_fcinfo = pertrans->deserialfn_fcinfo;

				/* evaluate argument */
				ExecInitExprRec(source_tle->expr, state,
								&ds_fcinfo->args[0].value,
								&ds_fcinfo->args[0].isnull);

				/* Dummy second argument for type-safety reasons */
				ds_fcinfo->args[1].value = PointerGetDatum(NULL);
				ds_fcinfo->args[1].isnull = false;

				/*
				 * Don't call a strict deserialization function with NULL
				 * input
				 */
				if (pertrans->deserialfn.fn_strict)
					scratch.opcode = EEOP_AGG_STRICT_DESERIALIZE;
				else
					scratch.opcode = EEOP_AGG_DESERIALIZE;

				scratch.d.agg_deserialize.fcinfo_data = ds_fcinfo;
				scratch.d.agg_deserialize.jumpnull = -1;	/* adjust later */
				scratch.resvalue = &trans_fcinfo->args[argno + 1].value;
				scratch.resnull = &trans_fcinfo->args[argno + 1].isnull;

				ExprEvalPushStep(state, &scratch);
				/* don't add an adjustment unless the function is strict */
				if (pertrans->deserialfn.fn_strict)
					adjust_bailout = lappend_int(adjust_bailout,
												 state->steps_len - 1);

				/* restore normal settings of scratch fields */
				scratch.resvalue = &state->resvalue;
				scratch.resnull = &state->resnull;
			}
			argno++;

			Assert(pertrans->numInputs == argno);
		}
		else if (!pertrans->aggsortrequired)
		{
			ListCell   *arg;

			/*
			 * Normal transition function without ORDER BY / DISTINCT or with
			 * ORDER BY / DISTINCT but the planner has given us pre-sorted
			 * input.
			 */
			strictargs = trans_fcinfo->args + 1;

			foreach(arg, pertrans->aggref->args)
			{
				TargetEntry *source_tle = (TargetEntry *) lfirst(arg);

				/*
				 * Don't initialize args for any ORDER BY clause that might
				 * exist in a presorted aggregate.
				 */
				if (argno == pertrans->numTransInputs)
					break;

				/*
				 * Start from 1, since the 0th arg will be the transition
				 * value
				 */
				ExecInitExprRec(source_tle->expr, state,
								&trans_fcinfo->args[argno + 1].value,
								&trans_fcinfo->args[argno + 1].isnull);
				argno++;
			}
			Assert(pertrans->numTransInputs == argno);
		}
		else if (pertrans->numInputs == 1)
		{
			/*
			 * Non-presorted DISTINCT and/or ORDER BY case, with a single
			 * column sorted on.
			 */
			TargetEntry *source_tle =
				(TargetEntry *) linitial(pertrans->aggref->args);

			Assert(list_length(pertrans->aggref->args) == 1);

			ExecInitExprRec(source_tle->expr, state,
							&state->resvalue,
							&state->resnull);
			strictnulls = &state->resnull;
			argno++;

			Assert(pertrans->numInputs == argno);
		}
		else
		{
			/*
			 * Non-presorted DISTINCT and/or ORDER BY case, with multiple
			 * columns sorted on.
			 */
			Datum	   *values = pertrans->sortslot->tts_values;
			bool	   *nulls = pertrans->sortslot->tts_isnull;
			ListCell   *arg;

			strictnulls = nulls;

			foreach(arg, pertrans->aggref->args)
			{
				TargetEntry *source_tle = (TargetEntry *) lfirst(arg);

				ExecInitExprRec(source_tle->expr, state,
								&values[argno], &nulls[argno]);
				argno++;
			}
			Assert(pertrans->numInputs == argno);
		}

		/*
		 * For a strict transfn, nothing happens when there's a NULL input; we
		 * just keep the prior transValue. This is true for both plain and
		 * sorted/distinct aggregates.
		 */
		if (trans_fcinfo->flinfo->fn_strict && pertrans->numTransInputs > 0)
		{
			if (strictnulls)
				scratch.opcode = EEOP_AGG_STRICT_INPUT_CHECK_NULLS;
			else if (strictargs && pertrans->numTransInputs == 1)
				scratch.opcode = EEOP_AGG_STRICT_INPUT_CHECK_ARGS_1;
			else
				scratch.opcode = EEOP_AGG_STRICT_INPUT_CHECK_ARGS;
			scratch.d.agg_strict_input_check.nulls = strictnulls;
			scratch.d.agg_strict_input_check.args = strictargs;
			scratch.d.agg_strict_input_check.jumpnull = -1; /* adjust later */
			scratch.d.agg_strict_input_check.nargs = pertrans->numTransInputs;
			ExprEvalPushStep(state, &scratch);
			adjust_bailout = lappend_int(adjust_bailout,
										 state->steps_len - 1);
		}

		/* Handle DISTINCT aggregates which have pre-sorted input */
		if (pertrans->numDistinctCols > 0 && !pertrans->aggsortrequired)
		{
			if (pertrans->numDistinctCols > 1)
				scratch.opcode = EEOP_AGG_PRESORTED_DISTINCT_MULTI;
			else
				scratch.opcode = EEOP_AGG_PRESORTED_DISTINCT_SINGLE;

			scratch.d.agg_presorted_distinctcheck.pertrans = pertrans;
			scratch.d.agg_presorted_distinctcheck.jumpdistinct = -1;	/* adjust later */
			ExprEvalPushStep(state, &scratch);
			adjust_bailout = lappend_int(adjust_bailout,
										 state->steps_len - 1);
		}

		/*
		 * Call transition function (once for each concurrently evaluated
		 * grouping set). Do so for both sort and hash based computations, as
		 * applicable.
		 */
		if (doSort)
		{
			int			processGroupingSets = Max(phase->numsets, 1);
			int			setoff = 0;

			for (int setno = 0; setno < processGroupingSets; setno++)
			{
				ExecBuildAggTransCall(state, aggstate, &scratch, trans_fcinfo,
									  pertrans, transno, setno, setoff, false,
									  nullcheck);
				setoff++;
			}
		}

		if (doHash)
		{
			int			numHashes = aggstate->num_hashes;
			int			setoff;

			/* in MIXED mode, there'll be preceding transition values */
			if (aggstate->aggstrategy != AGG_HASHED)
				setoff = aggstate->maxsets;
			else
				setoff = 0;

			for (int setno = 0; setno < numHashes; setno++)
			{
				ExecBuildAggTransCall(state, aggstate, &scratch, trans_fcinfo,
									  pertrans, transno, setno, setoff, true,
									  nullcheck);
				setoff++;
			}
		}

		/* adjust early bail out jump target(s) */
		foreach(bail, adjust_bailout)
		{
			ExprEvalStep *as = &state->steps[lfirst_int(bail)];

			if (as->opcode == EEOP_JUMP_IF_NOT_TRUE)
			{
				Assert(as->d.jump.jumpdone == -1);
				as->d.jump.jumpdone = state->steps_len;
			}
			else if (as->opcode == EEOP_AGG_STRICT_INPUT_CHECK_ARGS ||
					 as->opcode == EEOP_AGG_STRICT_INPUT_CHECK_ARGS_1 ||
					 as->opcode == EEOP_AGG_STRICT_INPUT_CHECK_NULLS)
			{
				Assert(as->d.agg_strict_input_check.jumpnull == -1);
				as->d.agg_strict_input_check.jumpnull = state->steps_len;
			}
			else if (as->opcode == EEOP_AGG_STRICT_DESERIALIZE)
			{
				Assert(as->d.agg_deserialize.jumpnull == -1);
				as->d.agg_deserialize.jumpnull = state->steps_len;
			}
			else if (as->opcode == EEOP_AGG_PRESORTED_DISTINCT_SINGLE ||
					 as->opcode == EEOP_AGG_PRESORTED_DISTINCT_MULTI)
			{
				Assert(as->d.agg_presorted_distinctcheck.jumpdistinct == -1);
				as->d.agg_presorted_distinctcheck.jumpdistinct = state->steps_len;
			}
			else
				Assert(false);
		}
	}

	scratch.resvalue = NULL;
	scratch.resnull = NULL;
	scratch.opcode = EEOP_DONE_NO_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildAggTransCall —— 单个过渡值的过渡函数调用步骤
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为"一个聚合过渡函数在某个 grouping set（或哈希组）上的一次调用"生成步骤：
 *   可选 pergroup 空指针检查 → 按过渡值类型（byval/byref）与函数严格性选择最
 *   合适的 EEOP_AGG_*_TRANS 变体 → push 并回填跳转目标。从 ExecBuildAggTrans
 *   中拆出是因为排序型与哈希型两条路径（多个 grouping set、多哈希表）共用。
 *
 * 参数：
 *   state/scratch - 目标状态与步骤工作区；aggstate - 提供运行上下文选择
 *            （排序型取 aggcontexts[setno]，哈希型取 hashcontext）；
 *   fcinfo - 过渡函数调用信息；pertrans - 过渡描述（transtypeByVal、
 *            initValueIsNull、aggsortrequired、numInputs 等）；
 *   transno/setno/setoff - 过渡编号/分组集编号/偏移（setoff 用于 pergroup
 *            数组定位）；ishash - 哈希型还是排序型；nullcheck - 是否生成
 *            pergroup 空指针跳过检查。
 *
 * 设计思想：
 *   1. 变体矩阵（聚合是热点，多一步分支都有代价）：
 *      - 非排序聚合：严格且无初始值 → EEOP_AGG_PLAIN_TRANS_INIT_STRICT_*
 *        （首个非 NULL 输入直接采纳为初始态）；严格且有初始值 →
 *        EEOP_AGG_PLAIN_TRANS_STRICT_*（过渡态已 NULL 则跳过调用）；否则
 *        EEOP_AGG_PLAIN_TRANS_*。每种再按过渡类型 byval/byref 分两种（byval
 *        无需内存管理，可内联）。
 *      - 排序聚合（ORDER BY/DISTINCT 需先排序）：单列 → ORDERED_TRANS_DATUM，
 *        多列 → ORDERED_TRANS_TUPLE（列进 sortslot）；严格性判定推迟到
 *        finalize 阶段（process_ordered_aggregate_*），此处不做。
 *   2. 各变体责任重叠并不优雅，但聚合性能敏感，值得以"专用步骤"换取一次分支
 *      的节省——原注释明确承认这一权衡。
 *   3. jumpnull 在 push 之后回填到"本过渡调用之后"的位置，保证 pergroup 为
 *      NULL（nullcheck 模式）时跳过整段过渡逻辑。
 * ============================================================================
 */
static void
ExecBuildAggTransCall(ExprState *state, AggState *aggstate,
					  ExprEvalStep *scratch,
					  FunctionCallInfo fcinfo, AggStatePerTrans pertrans,
					  int transno, int setno, int setoff, bool ishash,
					  bool nullcheck)
{
	ExprContext *aggcontext;
	int			adjust_jumpnull = -1;

	if (ishash)
		aggcontext = aggstate->hashcontext;
	else
		aggcontext = aggstate->aggcontexts[setno];

	/* add check for NULL pointer? */
	if (nullcheck)
	{
		scratch->opcode = EEOP_AGG_PLAIN_PERGROUP_NULLCHECK;
		scratch->d.agg_plain_pergroup_nullcheck.setoff = setoff;
		/* adjust later */
		scratch->d.agg_plain_pergroup_nullcheck.jumpnull = -1;
		ExprEvalPushStep(state, scratch);
		adjust_jumpnull = state->steps_len - 1;
	}

	/*
	 * Determine appropriate transition implementation.
	 *
	 * For non-ordered aggregates and ORDER BY / DISTINCT aggregates with
	 * presorted input:
	 *
	 * If the initial value for the transition state doesn't exist in the
	 * pg_aggregate table then we will let the first non-NULL value returned
	 * from the outer procNode become the initial value. (This is useful for
	 * aggregates like max() and min().) The noTransValue flag signals that we
	 * need to do so. If true, generate a
	 * EEOP_AGG_INIT_STRICT_PLAIN_TRANS{,_BYVAL} step. This step also needs to
	 * do the work described next:
	 *
	 * If the function is strict, but does have an initial value, choose
	 * EEOP_AGG_STRICT_PLAIN_TRANS{,_BYVAL}, which skips the transition
	 * function if the transition value has become NULL (because a previous
	 * transition function returned NULL). This step also needs to do the work
	 * described next:
	 *
	 * Otherwise we call EEOP_AGG_PLAIN_TRANS{,_BYVAL}, which does not have to
	 * perform either of the above checks.
	 *
	 * Having steps with overlapping responsibilities is not nice, but
	 * aggregations are very performance sensitive, making this worthwhile.
	 *
	 * For ordered aggregates:
	 *
	 * Only need to choose between the faster path for a single ordered
	 * column, and the one between multiple columns. Checking strictness etc
	 * is done when finalizing the aggregate. See
	 * process_ordered_aggregate_{single, multi} and
	 * advance_transition_function.
	 */
	if (!pertrans->aggsortrequired)
	{
		if (pertrans->transtypeByVal)
		{
			if (fcinfo->flinfo->fn_strict &&
				pertrans->initValueIsNull)
				scratch->opcode = EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYVAL;
			else if (fcinfo->flinfo->fn_strict)
				scratch->opcode = EEOP_AGG_PLAIN_TRANS_STRICT_BYVAL;
			else
				scratch->opcode = EEOP_AGG_PLAIN_TRANS_BYVAL;
		}
		else
		{
			if (fcinfo->flinfo->fn_strict &&
				pertrans->initValueIsNull)
				scratch->opcode = EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYREF;
			else if (fcinfo->flinfo->fn_strict)
				scratch->opcode = EEOP_AGG_PLAIN_TRANS_STRICT_BYREF;
			else
				scratch->opcode = EEOP_AGG_PLAIN_TRANS_BYREF;
		}
	}
	else if (pertrans->numInputs == 1)
		scratch->opcode = EEOP_AGG_ORDERED_TRANS_DATUM;
	else
		scratch->opcode = EEOP_AGG_ORDERED_TRANS_TUPLE;

	scratch->d.agg_trans.pertrans = pertrans;
	scratch->d.agg_trans.setno = setno;
	scratch->d.agg_trans.setoff = setoff;
	scratch->d.agg_trans.transno = transno;
	scratch->d.agg_trans.aggcontext = aggcontext;
	ExprEvalPushStep(state, scratch);

	/* fix up jumpnull */
	if (adjust_jumpnull != -1)
	{
		ExprEvalStep *as = &state->steps[adjust_jumpnull];

		Assert(as->opcode == EEOP_AGG_PLAIN_PERGROUP_NULLCHECK);
		Assert(as->d.agg_plain_pergroup_nullcheck.jumpnull == -1);
		as->d.agg_plain_pergroup_nullcheck.jumpnull = state->steps_len;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildHash32FromAttrs —— 构建"按属性列计算 32 位哈希"的表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   构建把 inner 槽元组的指定列用给定哈希函数（每列一个）散列并混合成单个
 *   uint32 的 ExprState：先按最高列号生成一条 FETCHSOME，再逐列"取列 →
 *   EEOP_HASHDATUM_FIRST/NEXT32 哈希"，多列时后列哈希与前列中间结果混合，
 *   最终结果存 state->resvalue。
 *
 * 参数：
 *   desc - 待哈希列的元组描述符；ops - 槽类型（供固定性分析）；
 *   hashfunctions - 每列一个 FmgrInfo（被直接引用进 ExprState，调用方须保证
 *            其生命周期不短于结果状态）；collations - 每列排序规则；
 *   numCols/keyColIdx - 列数与列号数组；parent - 宿主 PlanState；
 *   init_value - 哈希种子（默认 0；非零略慢但可注入固定偏移/参与混合）。
 *
 * 设计思想：
 *   1. 单列且无种子时用 EEOP_HASHDATUM_FIRST 直接产出结果（不做混合）；其余
 *      情形先 SET_INITVAL 放种子再逐列 NEXT32——FIRST 会覆盖已存种子故不可用。
 *   2. 列值与哈希调用之间 resv 指向 fcinfo->args[0]（参数下沉），哈希结果写
 *      中间 NullableDatum（多列时）或 state->resvalue（最后一列），避免冗余
 *      拷贝。
 *   3. 哈希函数总是按严格处理：输入为 NULL 时不调用函数，结果置 NULL（由执行
 *      器语义决定，通常意味着"无法哈希"）。
 *   4. 被调用方：execGrouping.c 的哈希表键哈希（hash join/分组）、nodeSubplan.c
 *      （子计划左边参数哈希，配合 ExecBuildGroupingEqual 判等）。
 * ============================================================================
 */
ExprState *
ExecBuildHash32FromAttrs(TupleDesc desc, const TupleTableSlotOps *ops,
						 FmgrInfo *hashfunctions, Oid *collations,
						 int numCols, AttrNumber *keyColIdx,
						 PlanState *parent, uint32 init_value)
{
	ExprState  *state = makeNode(ExprState);
	ExprEvalStep scratch = {0};
	NullableDatum *iresult = NULL;
	intptr_t	opcode;
	AttrNumber	last_attnum = 0;

	Assert(numCols >= 0);

	state->parent = parent;

	/*
	 * Make a place to store intermediate hash values between subsequent
	 * hashing of individual columns.  We only need this if there is more than
	 * one column to hash or an initial value plus one column.
	 */
	if ((int64) numCols + (init_value != 0) > 1)
		iresult = palloc_object(NullableDatum);

	/* find the highest attnum so we deform the tuple to that point */
	for (int i = 0; i < numCols; i++)
		last_attnum = Max(last_attnum, keyColIdx[i]);

	scratch.opcode = EEOP_INNER_FETCHSOME;
	scratch.d.fetch.last_var = last_attnum;
	scratch.d.fetch.fixed = false;
	scratch.d.fetch.kind = ops;
	scratch.d.fetch.known_desc = desc;
	if (ExecComputeSlotInfo(state, &scratch))
		ExprEvalPushStep(state, &scratch);

	if (init_value == 0)
	{
		/*
		 * No initial value, so we can assign the result of the hash function
		 * for the first attribute without having to concern ourselves with
		 * combining the result with any initial value.
		 */
		opcode = EEOP_HASHDATUM_FIRST;
	}
	else
	{
		/*
		 * Set up operation to set the initial value.  Normally we store this
		 * in the intermediate hash value location, but if there are no
		 * columns to hash, store it in the ExprState's result field.
		 */
		scratch.opcode = EEOP_HASHDATUM_SET_INITVAL;
		scratch.d.hashdatum_initvalue.init_value = UInt32GetDatum(init_value);
		scratch.resvalue = numCols > 0 ? &iresult->value : &state->resvalue;
		scratch.resnull = numCols > 0 ? &iresult->isnull : &state->resnull;

		ExprEvalPushStep(state, &scratch);

		/*
		 * When using an initial value use the NEXT32 ops as the FIRST ops
		 * would overwrite the stored initial value.
		 */
		opcode = EEOP_HASHDATUM_NEXT32;
	}

	for (int i = 0; i < numCols; i++)
	{
		FmgrInfo   *finfo;
		FunctionCallInfo fcinfo;
		Oid			inputcollid = collations[i];
		AttrNumber	attnum = keyColIdx[i] - 1;

		finfo = &hashfunctions[i];
		fcinfo = palloc0(SizeForFunctionCallInfo(1));

		/* Initialize function call parameter structure too */
		InitFunctionCallInfoData(*fcinfo, finfo, 1, inputcollid, NULL, NULL);

		/*
		 * Fetch inner Var for this attnum and store it in the 1st arg of the
		 * hash func.
		 */
		scratch.opcode = EEOP_INNER_VAR;
		scratch.resvalue = &fcinfo->args[0].value;
		scratch.resnull = &fcinfo->args[0].isnull;
		scratch.d.var.attnum = attnum;
		scratch.d.var.vartype = TupleDescAttr(desc, attnum)->atttypid;
		scratch.d.var.varreturningtype = VAR_RETURNING_DEFAULT;

		ExprEvalPushStep(state, &scratch);

		/* Call the hash function */
		scratch.opcode = opcode;

		if (i == numCols - 1)
		{
			/*
			 * The result for hashing the final column is stored in the
			 * ExprState.
			 */
			scratch.resvalue = &state->resvalue;
			scratch.resnull = &state->resnull;
		}
		else
		{
			Assert(iresult != NULL);

			/* intermediate values are stored in an intermediate result */
			scratch.resvalue = &iresult->value;
			scratch.resnull = &iresult->isnull;
		}

		/*
		 * NEXT32 opcodes need to look at the intermediate result.  We might
		 * as well just set this for all ops.  FIRSTs won't look at it.
		 */
		scratch.d.hashdatum.iresult = iresult;

		scratch.d.hashdatum.finfo = finfo;
		scratch.d.hashdatum.fcinfo_data = fcinfo;
		scratch.d.hashdatum.fn_addr = finfo->fn_addr;
		scratch.d.hashdatum.jumpdone = -1;

		ExprEvalPushStep(state, &scratch);

		/* subsequent attnums must be combined with the previous */
		opcode = EEOP_HASHDATUM_NEXT32;
	}

	scratch.resvalue = NULL;
	scratch.resnull = NULL;
	scratch.opcode = EEOP_DONE_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildHash32Expr —— 构建"按任意表达式计算 32 位哈希"的表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 ExecBuildHash32FromAttrs 同构，但哈希对象从"属性列"泛化为"任意表达式
 *   列表"（hash_exprs）：逐表达式求值后哈希并混合；当某表达式为 NULL 且其
 *   对应运算（opstrict[i] 为 true）严格时，结果直接为 NULL；非严格运算符按
 *   "NULL 的哈希值为零"处理——通过选择 *_STRICT / 非 STRICT 步骤变体区分。
 *
 * 参数：
 *   desc/ops - 槽描述与类型（供 FETCHSOME 及 Var 编译分析）；hashfunc_oids -
 *              每表达式哈希函数 OID；collations - 每表达式排序规则；
 *   hash_exprs - 待哈希表达式列表；opstrict - 与表达式一一对应的运算符严格性；
 *   parent/init_value - 同 ExecBuildHash32FromAttrs。
 *
 * 设计思想：
 *   1. 步骤序列：setup（FETCHSOME）→ 可选 SET_INITVAL → 对每个表达式：求值进
 *      fcinfo->args[0] → 按 opstrict 与位置选 FIRST（含 STRICT 变体）或
 *      NEXT32（含 STRICT 变体）→ 结果写中间或最终位置。严格变体遇 NULL 时
 *      跳到结尾返回 NULL，跳转目标最后统一回填。
 *   2. 与 FromAttrs 版的分工：连接键/分组键若是"表达式"（如 a+b、函数调用）
 *      而非裸列，则用本入口；HashJoin 的表达式化连接键（nodeHashjoin.c）是
 *      典型调用方。
 * ============================================================================
 */
ExprState *
ExecBuildHash32Expr(TupleDesc desc, const TupleTableSlotOps *ops,
					const Oid *hashfunc_oids, const List *collations,
					const List *hash_exprs, const bool *opstrict,
					PlanState *parent, uint32 init_value)
{
	ExprState  *state = makeNode(ExprState);
	ExprEvalStep scratch = {0};
	NullableDatum *iresult = NULL;
	List	   *adjust_jumps = NIL;
	ListCell   *lc;
	ListCell   *lc2;
	intptr_t	strict_opcode;
	intptr_t	opcode;
	int			num_exprs = list_length(hash_exprs);

	Assert(num_exprs == list_length(collations));

	state->parent = parent;

	/* Insert setup steps as needed. */
	ExecCreateExprSetupSteps(state, (Node *) hash_exprs);

	/*
	 * Make a place to store intermediate hash values between subsequent
	 * hashing of individual expressions.  We only need this if there is more
	 * than one expression to hash or an initial value plus one expression.
	 */
	if ((int64) num_exprs + (init_value != 0) > 1)
		iresult = palloc_object(NullableDatum);

	if (init_value == 0)
	{
		/*
		 * No initial value, so we can assign the result of the hash function
		 * for the first hash_expr without having to concern ourselves with
		 * combining the result with any initial value.
		 */
		strict_opcode = EEOP_HASHDATUM_FIRST_STRICT;
		opcode = EEOP_HASHDATUM_FIRST;
	}
	else
	{
		/*
		 * Set up operation to set the initial value.  Normally we store this
		 * in the intermediate hash value location, but if there are no exprs
		 * to hash, store it in the ExprState's result field.
		 */
		scratch.opcode = EEOP_HASHDATUM_SET_INITVAL;
		scratch.d.hashdatum_initvalue.init_value = UInt32GetDatum(init_value);
		scratch.resvalue = num_exprs > 0 ? &iresult->value : &state->resvalue;
		scratch.resnull = num_exprs > 0 ? &iresult->isnull : &state->resnull;

		ExprEvalPushStep(state, &scratch);

		/*
		 * When using an initial value use the NEXT32/NEXT32_STRICT ops as the
		 * FIRST/FIRST_STRICT ops would overwrite the stored initial value.
		 */
		strict_opcode = EEOP_HASHDATUM_NEXT32_STRICT;
		opcode = EEOP_HASHDATUM_NEXT32;
	}

	forboth(lc, hash_exprs, lc2, collations)
	{
		Expr	   *expr = (Expr *) lfirst(lc);
		FmgrInfo   *finfo;
		FunctionCallInfo fcinfo;
		int			i = foreach_current_index(lc);
		Oid			funcid;
		Oid			inputcollid = lfirst_oid(lc2);

		funcid = hashfunc_oids[i];

		/* Allocate hash function lookup data. */
		finfo = palloc0_object(FmgrInfo);
		fcinfo = palloc0(SizeForFunctionCallInfo(1));

		fmgr_info(funcid, finfo);

		/*
		 * Build the steps to evaluate the hash function's argument, placing
		 * the value in the 0th argument of the hash func.
		 */
		ExecInitExprRec(expr,
						state,
						&fcinfo->args[0].value,
						&fcinfo->args[0].isnull);

		if (i == num_exprs - 1)
		{
			/* the result for hashing the final expr is stored in the state */
			scratch.resvalue = &state->resvalue;
			scratch.resnull = &state->resnull;
		}
		else
		{
			Assert(iresult != NULL);

			/* intermediate values are stored in an intermediate result */
			scratch.resvalue = &iresult->value;
			scratch.resnull = &iresult->isnull;
		}

		/*
		 * NEXT32 opcodes need to look at the intermediate result.  We might
		 * as well just set this for all ops.  FIRSTs won't look at it.
		 */
		scratch.d.hashdatum.iresult = iresult;

		/* Initialize function call parameter structure too */
		InitFunctionCallInfoData(*fcinfo, finfo, 1, inputcollid, NULL, NULL);

		scratch.d.hashdatum.finfo = finfo;
		scratch.d.hashdatum.fcinfo_data = fcinfo;
		scratch.d.hashdatum.fn_addr = finfo->fn_addr;

		scratch.opcode = opstrict[i] ? strict_opcode : opcode;
		scratch.d.hashdatum.jumpdone = -1;

		ExprEvalPushStep(state, &scratch);
		adjust_jumps = lappend_int(adjust_jumps, state->steps_len - 1);

		/*
		 * For subsequent keys we must combine the hash value with the
		 * previous hashes.
		 */
		strict_opcode = EEOP_HASHDATUM_NEXT32_STRICT;
		opcode = EEOP_HASHDATUM_NEXT32;
	}

	/* adjust jump targets */
	foreach(lc, adjust_jumps)
	{
		ExprEvalStep *as = &state->steps[lfirst_int(lc)];

		Assert(as->opcode == EEOP_HASHDATUM_FIRST ||
			   as->opcode == EEOP_HASHDATUM_FIRST_STRICT ||
			   as->opcode == EEOP_HASHDATUM_NEXT32 ||
			   as->opcode == EEOP_HASHDATUM_NEXT32_STRICT);
		Assert(as->d.hashdatum.jumpdone == -1);
		as->d.hashdatum.jumpdone = state->steps_len;
	}

	scratch.resvalue = NULL;
	scratch.resnull = NULL;
	scratch.opcode = EEOP_DONE_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildGroupingEqual —— 构建"组内相等"判定表达式（NOT DISTINCT）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   构建可用 ExecQual 求值的 ExprState：逐列比较 inner/outer 槽的 numCols 个
 *   键，对每列用给定等值函数求"NOT DISTINCT FROM"（两个 NULL 相等、NULL 与
 *   非 NULL 不等），返回 true 表示"同一组/同一条记录"。HashAgg 输入的前后行
 *   判定、子计划左右两边记录配对等直接复用。
 *
 * 参数：
 *   ldesc/rdesc（lops/rops）- 两侧槽描述与槽类型；numCols/keyColIdx - 键列数
 *            与列号数组（label:按 keyColIdx 指向两侧各自同号列）；
 *   eqfunctions - 每列的等值函数 OID；collations - 每列排序规则；
 *   parent - 宿主计划节点（也可为 NULL，此时跳过固定性分析）。
 *
 * 设计思想：
 *   1. 空键（numCols==0）返回 NULL ExprState——ExecQual 对 NULL 状态恒真，
 *      正好表达"空 GROUP BY 全部相等"。
 *   2. 两遍 FETCHSOME：两侧各自按最大键列变形，一次到位。
 *   3. 从最后一列（最不重要的排序键）倒序比较：若输入来自排序源，低位键最
 *      可能出现差异，先比它们可以在更早的 EEOP_QUAL 跳出，减少平均比较次数。
 *   4. NULL 语义由 EEOP_NOT_DISTINCT 步骤实现（等值函数 + NULL 处理逻辑），
 *      而非简单调用等值函数；每列比较后都紧跟 EEOP_QUAL（false/NULL 即跳出）。
 *   5. 被调用方：execGrouping.c 的 ExecuteEqualityFuncs（排序分组）、
 *      nodeSubplan.c（左右表连接键判等，配合 ExecBuildHash32FromAttrs）。
 * ============================================================================
 */
ExprState *
ExecBuildGroupingEqual(TupleDesc ldesc, TupleDesc rdesc,
					   const TupleTableSlotOps *lops, const TupleTableSlotOps *rops,
					   int numCols,
					   const AttrNumber *keyColIdx,
					   const Oid *eqfunctions,
					   const Oid *collations,
					   PlanState *parent)
{
	ExprState  *state = makeNode(ExprState);
	ExprEvalStep scratch = {0};
	int			maxatt = -1;
	List	   *adjust_jumps = NIL;
	ListCell   *lc;

	/*
	 * When no columns are actually compared, the result's always true. See
	 * special case in ExecQual().
	 */
	if (numCols == 0)
		return NULL;

	state->expr = NULL;
	state->flags = EEO_FLAG_IS_QUAL;
	state->parent = parent;

	scratch.resvalue = &state->resvalue;
	scratch.resnull = &state->resnull;

	/* compute max needed attribute */
	for (int natt = 0; natt < numCols; natt++)
	{
		int			attno = keyColIdx[natt];

		if (attno > maxatt)
			maxatt = attno;
	}
	Assert(maxatt >= 0);

	/* push deform steps */
	scratch.opcode = EEOP_INNER_FETCHSOME;
	scratch.d.fetch.last_var = maxatt;
	scratch.d.fetch.fixed = false;
	scratch.d.fetch.known_desc = ldesc;
	scratch.d.fetch.kind = lops;
	if (ExecComputeSlotInfo(state, &scratch))
		ExprEvalPushStep(state, &scratch);

	scratch.opcode = EEOP_OUTER_FETCHSOME;
	scratch.d.fetch.last_var = maxatt;
	scratch.d.fetch.fixed = false;
	scratch.d.fetch.known_desc = rdesc;
	scratch.d.fetch.kind = rops;
	if (ExecComputeSlotInfo(state, &scratch))
		ExprEvalPushStep(state, &scratch);

	/*
	 * Start comparing at the last field (least significant sort key). That's
	 * the most likely to be different if we are dealing with sorted input.
	 */
	for (int natt = numCols; --natt >= 0;)
	{
		int			attno = keyColIdx[natt];
		Form_pg_attribute latt = TupleDescAttr(ldesc, attno - 1);
		Form_pg_attribute ratt = TupleDescAttr(rdesc, attno - 1);
		Oid			foid = eqfunctions[natt];
		Oid			collid = collations[natt];
		FmgrInfo   *finfo;
		FunctionCallInfo fcinfo;
		AclResult	aclresult;

		/* Check permission to call function */
		aclresult = object_aclcheck(ProcedureRelationId, foid, GetUserId(), ACL_EXECUTE);
		if (aclresult != ACLCHECK_OK)
			aclcheck_error(aclresult, OBJECT_FUNCTION, get_func_name(foid));

		InvokeFunctionExecuteHook(foid);

		/* Set up the primary fmgr lookup information */
		finfo = palloc0_object(FmgrInfo);
		fcinfo = palloc0(SizeForFunctionCallInfo(2));
		fmgr_info(foid, finfo);
		fmgr_info_set_expr(NULL, finfo);
		InitFunctionCallInfoData(*fcinfo, finfo, 2,
								 collid, NULL, NULL);

		/* left arg */
		scratch.opcode = EEOP_INNER_VAR;
		scratch.d.var.attnum = attno - 1;
		scratch.d.var.vartype = latt->atttypid;
		scratch.d.var.varreturningtype = VAR_RETURNING_DEFAULT;
		scratch.resvalue = &fcinfo->args[0].value;
		scratch.resnull = &fcinfo->args[0].isnull;
		ExprEvalPushStep(state, &scratch);

		/* right arg */
		scratch.opcode = EEOP_OUTER_VAR;
		scratch.d.var.attnum = attno - 1;
		scratch.d.var.vartype = ratt->atttypid;
		scratch.d.var.varreturningtype = VAR_RETURNING_DEFAULT;
		scratch.resvalue = &fcinfo->args[1].value;
		scratch.resnull = &fcinfo->args[1].isnull;
		ExprEvalPushStep(state, &scratch);

		/* evaluate distinctness */
		scratch.opcode = EEOP_NOT_DISTINCT;
		scratch.d.func.finfo = finfo;
		scratch.d.func.fcinfo_data = fcinfo;
		scratch.d.func.fn_addr = finfo->fn_addr;
		scratch.d.func.nargs = 2;
		scratch.resvalue = &state->resvalue;
		scratch.resnull = &state->resnull;
		ExprEvalPushStep(state, &scratch);

		/* then emit EEOP_QUAL to detect if result is false (or null) */
		scratch.opcode = EEOP_QUAL;
		scratch.d.qualexpr.jumpdone = -1;
		scratch.resvalue = &state->resvalue;
		scratch.resnull = &state->resnull;
		ExprEvalPushStep(state, &scratch);
		adjust_jumps = lappend_int(adjust_jumps,
								   state->steps_len - 1);
	}

	/* adjust jump targets */
	foreach(lc, adjust_jumps)
	{
		ExprEvalStep *as = &state->steps[lfirst_int(lc)];

		Assert(as->opcode == EEOP_QUAL);
		Assert(as->d.qualexpr.jumpdone == -1);
		as->d.qualexpr.jumpdone = state->steps_len;
	}

	scratch.resvalue = NULL;
	scratch.resnull = NULL;
	scratch.opcode = EEOP_DONE_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecBuildParamSetEqual —— 构建"参数集与元组相等"判定表达式
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   构建可交给 ExecQual 的 ExprState：把 inner 槽的前 N 列与 outer 槽对应列
 *   逐个按"NOT DISTINCT"比较（两个 NULL 相等、NULL 与非 NULL 不等）。与
 *   ExecBuildGroupingEqual 的差异：两侧键列号固定为连续的 0..N-1，类型取自
 *   同一个 desc——专门用于把"已算好的一组键"与输入元组前若干列配对。
 *
 * 参数：
 *   desc - 两侧共同使用的元组描述符；lops/rops - 两侧槽类型；
 *   eqfunctions/collations - 每列等值函数与排序规则数组；
 *   param_exprs - 表达式列表（其长度决定比较列数 N；语义上这些表达式的结果
 *            已按序放进了 inner 槽的前 N 列）；parent - 宿主节点。
 *
 * 设计思想：
 *   1. 比较按正序进行（与 GroupingEqual 的倒序相反）：本函数服务的是"键已备
 *      好、逐列比对"的场景，没有"低位键先不同"的排序统计前提。
 *   2. EEO_FLAG_IS_QUAL 标记 + EEOP_QUAL 收尾：ExecQual 遇任一列 NULL 直接
 *      返回 false，保证"NULL 键不匹配"语义。
 *   3. 被调用方：nodeMemoize.c 的 Memoize 节点——用哈希键的前缀列与缓存条目
 *      做精确回访判定（哈希碰撞后的最终确认）。
 * ============================================================================
 */
ExprState *
ExecBuildParamSetEqual(TupleDesc desc,
					   const TupleTableSlotOps *lops,
					   const TupleTableSlotOps *rops,
					   const Oid *eqfunctions,
					   const Oid *collations,
					   const List *param_exprs,
					   PlanState *parent)
{
	ExprState  *state = makeNode(ExprState);
	ExprEvalStep scratch = {0};
	int			maxatt = list_length(param_exprs);
	List	   *adjust_jumps = NIL;
	ListCell   *lc;

	state->expr = NULL;
	state->flags = EEO_FLAG_IS_QUAL;
	state->parent = parent;

	scratch.resvalue = &state->resvalue;
	scratch.resnull = &state->resnull;

	/* push deform steps */
	scratch.opcode = EEOP_INNER_FETCHSOME;
	scratch.d.fetch.last_var = maxatt;
	scratch.d.fetch.fixed = false;
	scratch.d.fetch.known_desc = desc;
	scratch.d.fetch.kind = lops;
	if (ExecComputeSlotInfo(state, &scratch))
		ExprEvalPushStep(state, &scratch);

	scratch.opcode = EEOP_OUTER_FETCHSOME;
	scratch.d.fetch.last_var = maxatt;
	scratch.d.fetch.fixed = false;
	scratch.d.fetch.known_desc = desc;
	scratch.d.fetch.kind = rops;
	if (ExecComputeSlotInfo(state, &scratch))
		ExprEvalPushStep(state, &scratch);

	for (int attno = 0; attno < maxatt; attno++)
	{
		Form_pg_attribute att = TupleDescAttr(desc, attno);
		Oid			foid = eqfunctions[attno];
		Oid			collid = collations[attno];
		FmgrInfo   *finfo;
		FunctionCallInfo fcinfo;
		AclResult	aclresult;

		/* Check permission to call function */
		aclresult = object_aclcheck(ProcedureRelationId, foid, GetUserId(), ACL_EXECUTE);
		if (aclresult != ACLCHECK_OK)
			aclcheck_error(aclresult, OBJECT_FUNCTION, get_func_name(foid));

		InvokeFunctionExecuteHook(foid);

		/* Set up the primary fmgr lookup information */
		finfo = palloc0_object(FmgrInfo);
		fcinfo = palloc0(SizeForFunctionCallInfo(2));
		fmgr_info(foid, finfo);
		fmgr_info_set_expr(NULL, finfo);
		InitFunctionCallInfoData(*fcinfo, finfo, 2,
								 collid, NULL, NULL);

		/* left arg */
		scratch.opcode = EEOP_INNER_VAR;
		scratch.d.var.attnum = attno;
		scratch.d.var.vartype = att->atttypid;
		scratch.d.var.varreturningtype = VAR_RETURNING_DEFAULT;
		scratch.resvalue = &fcinfo->args[0].value;
		scratch.resnull = &fcinfo->args[0].isnull;
		ExprEvalPushStep(state, &scratch);

		/* right arg */
		scratch.opcode = EEOP_OUTER_VAR;
		scratch.d.var.attnum = attno;
		scratch.d.var.vartype = att->atttypid;
		scratch.d.var.varreturningtype = VAR_RETURNING_DEFAULT;
		scratch.resvalue = &fcinfo->args[1].value;
		scratch.resnull = &fcinfo->args[1].isnull;
		ExprEvalPushStep(state, &scratch);

		/* evaluate distinctness */
		scratch.opcode = EEOP_NOT_DISTINCT;
		scratch.d.func.finfo = finfo;
		scratch.d.func.fcinfo_data = fcinfo;
		scratch.d.func.fn_addr = finfo->fn_addr;
		scratch.d.func.nargs = 2;
		scratch.resvalue = &state->resvalue;
		scratch.resnull = &state->resnull;
		ExprEvalPushStep(state, &scratch);

		/* then emit EEOP_QUAL to detect if result is false (or null) */
		scratch.opcode = EEOP_QUAL;
		scratch.d.qualexpr.jumpdone = -1;
		scratch.resvalue = &state->resvalue;
		scratch.resnull = &state->resnull;
		ExprEvalPushStep(state, &scratch);
		adjust_jumps = lappend_int(adjust_jumps,
								   state->steps_len - 1);
	}

	/* adjust jump targets */
	foreach(lc, adjust_jumps)
	{
		ExprEvalStep *as = &state->steps[lfirst_int(lc)];

		Assert(as->opcode == EEOP_QUAL);
		Assert(as->d.qualexpr.jumpdone == -1);
		as->d.qualexpr.jumpdone = state->steps_len;
	}

	scratch.resvalue = NULL;
	scratch.resnull = NULL;
	scratch.opcode = EEOP_DONE_RETURN;
	ExprEvalPushStep(state, &scratch);

	ExecReadyExpr(state);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitJsonExpr —— 编译 JsonExpr（JSON_VALUE/JSON_QUERY/JSON_EXISTS）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   生成 JsonExpr 的完整求值步骤序列：求 formatted_expr（JSON 输入值）与
 *   path_spec（jsonpath 路径）→ 两者任一为 NULL 则结果为 NULL → 求 PASSING
 *   命名参数 → EEOP_JSONEXPR_PATH 执行 jsonpath 求值 → 按 RETURNING 类型强转
 *   （json 强转或 IO 强转）→ 按 ON ERROR / ON EMPTY 行为处理错误与空结果。
 *
 * 参数：
 *   jsexpr - JsonExpr 节点；state - 所属 ExprState；resv/resnull - 结果地址；
 *   scratch - 步骤工作区（jsonexpr 字段）。
 *
 * 设计思想：
 *   1. JsonExprState 承载全部运行时状态：formatted_expr/pathspec 的求值结果、
 *      命名参数列表（JsonPathVariable）、错误与空标志（error/empty）、软错误
 *      上下文（escontext）与强转函数信息。
 *   2. 错误软化：on_error 不是 ERROR 行为时建立 ErrorSaveContext 传给 jsonpath
 *      求值与强转步骤（错误先不抛），由 EEOP_JSONEXPR_COERCION_FINISH 统一
 *      检查并把控制流转到 ON ERROR 表达式；行为是 ERROR 时 escontext 为 NULL，
 *      错误正常抛出。
 *   3. NULL/空/错误分支的"跳过优化"：ON ERROR / ON EMPTY 的默认表达式是
 *      "NULL 常量"时，只要 RETURNING 不是域类型（域需要走约束检查），整个处理
 *      分支都省略——jsonpath 求值器在出错/为空时本来就返回 NULL；
 *      formatted_expr 或 path_spec 为 NULL 时也直接 JUMP 到尾部的 NULL 常量
 *      步骤（此时 ON EMPTY/ON ERROR 不生效）。
 *   4. ON ERROR/ON EMPTY 表达式自身的求值与强转同样以软错误方式编译（临时切换
 *      state->escontext），并在其强转（若需要）后补 COERCION_FINISH 把潜在
 *      错误重新抛出；两个分支最后都跳到 jump_end，跳转目标在全部步骤生成后
 *      统一回填。
 *   5. 被调用方：ExecInitExprRec 的 T_JsonExpr 分支（JSON_TABLE_OP 除外——
 *      上游 tfuncFetchRows 只需要 formatted_expr 的值）。
 * ============================================================================
 */
static void
ExecInitJsonExpr(JsonExpr *jsexpr, ExprState *state,
				 Datum *resv, bool *resnull,
				 ExprEvalStep *scratch)
{
	JsonExprState *jsestate = palloc0_object(JsonExprState);
	ListCell   *argexprlc;
	ListCell   *argnamelc;
	List	   *jumps_return_null = NIL;
	List	   *jumps_to_end = NIL;
	ListCell   *lc;
	ErrorSaveContext *escontext;
	bool		returning_domain =
		get_typtype(jsexpr->returning->typid) == TYPTYPE_DOMAIN;

	Assert(jsexpr->on_error != NULL);

	jsestate->jsexpr = jsexpr;

	/*
	 * Evaluate formatted_expr storing the result into
	 * jsestate->formatted_expr.
	 */
	ExecInitExprRec((Expr *) jsexpr->formatted_expr, state,
					&jsestate->formatted_expr.value,
					&jsestate->formatted_expr.isnull);

	/* JUMP to return NULL if formatted_expr evaluates to NULL */
	jumps_return_null = lappend_int(jumps_return_null, state->steps_len);
	scratch->opcode = EEOP_JUMP_IF_NULL;
	scratch->resnull = &jsestate->formatted_expr.isnull;
	scratch->d.jump.jumpdone = -1;	/* set below */
	ExprEvalPushStep(state, scratch);

	/*
	 * Evaluate pathspec expression storing the result into
	 * jsestate->pathspec.
	 */
	ExecInitExprRec((Expr *) jsexpr->path_spec, state,
					&jsestate->pathspec.value,
					&jsestate->pathspec.isnull);

	/* JUMP to return NULL if path_spec evaluates to NULL */
	jumps_return_null = lappend_int(jumps_return_null, state->steps_len);
	scratch->opcode = EEOP_JUMP_IF_NULL;
	scratch->resnull = &jsestate->pathspec.isnull;
	scratch->d.jump.jumpdone = -1;	/* set below */
	ExprEvalPushStep(state, scratch);

	/* Steps to compute PASSING args. */
	jsestate->args = NIL;
	forboth(argexprlc, jsexpr->passing_values,
			argnamelc, jsexpr->passing_names)
	{
		Expr	   *argexpr = (Expr *) lfirst(argexprlc);
		String	   *argname = lfirst_node(String, argnamelc);
		JsonPathVariable *var = palloc_object(JsonPathVariable);

		var->name = argname->sval;
		var->namelen = strlen(var->name);
		var->typid = exprType((Node *) argexpr);
		var->typmod = exprTypmod((Node *) argexpr);

		ExecInitExprRec(argexpr, state, &var->value, &var->isnull);

		jsestate->args = lappend(jsestate->args, var);
	}

	/* Step for jsonpath evaluation; see ExecEvalJsonExprPath(). */
	scratch->opcode = EEOP_JSONEXPR_PATH;
	scratch->resvalue = resv;
	scratch->resnull = resnull;
	scratch->d.jsonexpr.jsestate = jsestate;
	ExprEvalPushStep(state, scratch);

	/*
	 * Step to return NULL after jumping to skip the EEOP_JSONEXPR_PATH step
	 * when either formatted_expr or pathspec is NULL.  Adjust jump target
	 * addresses of JUMPs that we added above.
	 */
	foreach(lc, jumps_return_null)
	{
		ExprEvalStep *as = &state->steps[lfirst_int(lc)];

		as->d.jump.jumpdone = state->steps_len;
	}
	scratch->opcode = EEOP_CONST;
	scratch->resvalue = resv;
	scratch->resnull = resnull;
	scratch->d.constval.value = (Datum) 0;
	scratch->d.constval.isnull = true;
	ExprEvalPushStep(state, scratch);

	escontext = jsexpr->on_error->btype != JSON_BEHAVIOR_ERROR ?
		&jsestate->escontext : NULL;

	/*
	 * To handle coercion errors softly, use the following ErrorSaveContext to
	 * pass to ExecInitExprRec() when initializing the coercion expressions
	 * and in the EEOP_JSONEXPR_COERCION step.
	 */
	jsestate->escontext.type = T_ErrorSaveContext;

	/*
	 * Steps to coerce the result value computed by EEOP_JSONEXPR_PATH or the
	 * NULL returned on NULL input as described above.
	 */
	jsestate->jump_eval_coercion = -1;
	if (jsexpr->use_json_coercion)
	{
		jsestate->jump_eval_coercion = state->steps_len;

		ExecInitJsonCoercion(state, jsexpr->returning, escontext,
							 jsexpr->omit_quotes,
							 jsexpr->op == JSON_EXISTS_OP,
							 resv, resnull);
	}
	else if (jsexpr->use_io_coercion)
	{
		/*
		 * Here we only need to initialize the FunctionCallInfo for the target
		 * type's input function, which is called by ExecEvalJsonExprPath()
		 * itself, so no additional step is necessary.
		 */
		Oid			typinput;
		Oid			typioparam;
		FmgrInfo   *finfo;
		FunctionCallInfo fcinfo;

		getTypeInputInfo(jsexpr->returning->typid, &typinput, &typioparam);
		finfo = palloc0_object(FmgrInfo);
		fcinfo = palloc0(SizeForFunctionCallInfo(3));
		fmgr_info(typinput, finfo);
		fmgr_info_set_expr((Node *) jsexpr->returning, finfo);
		InitFunctionCallInfoData(*fcinfo, finfo, 3, InvalidOid, NULL, NULL);

		/*
		 * We can preload the second and third arguments for the input
		 * function, since they're constants.
		 */
		fcinfo->args[1].value = ObjectIdGetDatum(typioparam);
		fcinfo->args[1].isnull = false;
		fcinfo->args[2].value = Int32GetDatum(jsexpr->returning->typmod);
		fcinfo->args[2].isnull = false;
		fcinfo->context = (Node *) escontext;

		jsestate->input_fcinfo = fcinfo;
	}

	/*
	 * Add a special step, if needed, to check if the coercion evaluation ran
	 * into an error but was not thrown because the ON ERROR behavior is not
	 * ERROR.  It will set jsestate->error if an error did occur.
	 */
	if (jsestate->jump_eval_coercion >= 0 && escontext != NULL)
	{
		scratch->opcode = EEOP_JSONEXPR_COERCION_FINISH;
		scratch->d.jsonexpr.jsestate = jsestate;
		ExprEvalPushStep(state, scratch);
	}

	jsestate->jump_empty = jsestate->jump_error = -1;

	/*
	 * Step to check jsestate->error and return the ON ERROR expression if
	 * there is one.  This handles both the errors that occur during jsonpath
	 * evaluation in EEOP_JSONEXPR_PATH and subsequent coercion evaluation.
	 *
	 * Speed up common cases by avoiding extra steps for a NULL-valued ON
	 * ERROR expression unless RETURNING a domain type, where constraints must
	 * be checked. ExecEvalJsonExprPath() already returns NULL on error,
	 * making additional steps unnecessary in typical scenarios. Note that the
	 * default ON ERROR behavior for JSON_VALUE() and JSON_QUERY() is to
	 * return NULL.
	 */
	if (jsexpr->on_error->btype != JSON_BEHAVIOR_ERROR &&
		(!(IsA(jsexpr->on_error->expr, Const) &&
		   ((Const *) jsexpr->on_error->expr)->constisnull) ||
		 returning_domain))
	{
		ErrorSaveContext *saved_escontext;

		jsestate->jump_error = state->steps_len;

		/* JUMP to end if false, that is, skip the ON ERROR expression. */
		jumps_to_end = lappend_int(jumps_to_end, state->steps_len);
		scratch->opcode = EEOP_JUMP_IF_NOT_TRUE;
		scratch->resvalue = &jsestate->error.value;
		scratch->resnull = &jsestate->error.isnull;
		scratch->d.jump.jumpdone = -1;	/* set below */
		ExprEvalPushStep(state, scratch);

		/*
		 * Steps to evaluate the ON ERROR expression; handle errors softly to
		 * rethrow them in COERCION_FINISH step that will be added later.
		 */
		saved_escontext = state->escontext;
		state->escontext = escontext;
		ExecInitExprRec((Expr *) jsexpr->on_error->expr,
						state, resv, resnull);
		state->escontext = saved_escontext;

		/* Step to coerce the ON ERROR expression if needed */
		if (jsexpr->on_error->coerce)
			ExecInitJsonCoercion(state, jsexpr->returning, escontext,
								 jsexpr->omit_quotes, false,
								 resv, resnull);

		/*
		 * Add a COERCION_FINISH step to check for errors that may occur when
		 * coercing and rethrow them.
		 */
		if (jsexpr->on_error->coerce ||
			IsA(jsexpr->on_error->expr, CoerceViaIO) ||
			IsA(jsexpr->on_error->expr, CoerceToDomain))
		{
			scratch->opcode = EEOP_JSONEXPR_COERCION_FINISH;
			scratch->resvalue = resv;
			scratch->resnull = resnull;
			scratch->d.jsonexpr.jsestate = jsestate;
			ExprEvalPushStep(state, scratch);
		}

		/* JUMP to end to skip the ON EMPTY steps added below. */
		jumps_to_end = lappend_int(jumps_to_end, state->steps_len);
		scratch->opcode = EEOP_JUMP;
		scratch->d.jump.jumpdone = -1;
		ExprEvalPushStep(state, scratch);
	}

	/*
	 * Step to check jsestate->empty and return the ON EMPTY expression if
	 * there is one.
	 *
	 * See the comment above for details on the optimization for NULL-valued
	 * expressions.
	 */
	if (jsexpr->on_empty != NULL &&
		jsexpr->on_empty->btype != JSON_BEHAVIOR_ERROR &&
		(!(IsA(jsexpr->on_empty->expr, Const) &&
		   ((Const *) jsexpr->on_empty->expr)->constisnull) ||
		 returning_domain))
	{
		ErrorSaveContext *saved_escontext;

		jsestate->jump_empty = state->steps_len;

		/* JUMP to end if false, that is, skip the ON EMPTY expression. */
		jumps_to_end = lappend_int(jumps_to_end, state->steps_len);
		scratch->opcode = EEOP_JUMP_IF_NOT_TRUE;
		scratch->resvalue = &jsestate->empty.value;
		scratch->resnull = &jsestate->empty.isnull;
		scratch->d.jump.jumpdone = -1;	/* set below */
		ExprEvalPushStep(state, scratch);

		/*
		 * Steps to evaluate the ON EMPTY expression; handle errors softly to
		 * rethrow them in COERCION_FINISH step that will be added later.
		 */
		saved_escontext = state->escontext;
		state->escontext = escontext;
		ExecInitExprRec((Expr *) jsexpr->on_empty->expr,
						state, resv, resnull);
		state->escontext = saved_escontext;

		/* Step to coerce the ON EMPTY expression if needed */
		if (jsexpr->on_empty->coerce)
			ExecInitJsonCoercion(state, jsexpr->returning, escontext,
								 jsexpr->omit_quotes, false,
								 resv, resnull);

		/*
		 * Add a COERCION_FINISH step to check for errors that may occur when
		 * coercing and rethrow them.
		 */
		if (jsexpr->on_empty->coerce ||
			IsA(jsexpr->on_empty->expr, CoerceViaIO) ||
			IsA(jsexpr->on_empty->expr, CoerceToDomain))
		{

			scratch->opcode = EEOP_JSONEXPR_COERCION_FINISH;
			scratch->resvalue = resv;
			scratch->resnull = resnull;
			scratch->d.jsonexpr.jsestate = jsestate;
			ExprEvalPushStep(state, scratch);
		}
	}

	foreach(lc, jumps_to_end)
	{
		ExprEvalStep *as = &state->steps[lfirst_int(lc)];

		as->d.jump.jumpdone = state->steps_len;
	}

	jsestate->jump_end = state->steps_len;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitJsonCoercion —— 生成 JSON 结果强转步骤（EEOP_JSONEXPR_COERCION）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   生成一条把 resv 中的值为按 JsonReturning 指定的类型强转的步骤：运行时由
 *   json_populate_type 依据 JSON 类别做目标类型转换（数值/字符串/布尔/复合等），
 *   支持软错误（escontext）与 JSON_EXISTS 的特殊形态（结果强转为 int 表示
 *   true/false、跳过域约束检查）。
 *
 * 参数：
 *   state - 所属 ExprState；returning - RETURNING 类型规格（typid/typmod）；
 *   escontext - 软错误上下文（可为 NULL）；omit_quotes - 强转时是否对文本值
 *           去引号（JSON_QUERY 语义）；exists_coerce - 是否为 JSON_EXISTS 的
 *           bool→目标类型强转；resv/resnull - 值所在地址。
 *
 * 设计思想：
 *   EXISTS 强转特例：把 bool 结果强转为目标类型（目标是 int4 时用专用快速路径
 *   exists_cast_to_int），并检测目标是否为域类型（DomainHasConstraints）以决定
 *   是否需要保留域约束检查。被 ExecInitJsonExpr 的正常强转路径与 ON ERROR /
 *   ON EMPTY 分支复用。
 * ============================================================================
 */
static void
ExecInitJsonCoercion(ExprState *state, JsonReturning *returning,
					 ErrorSaveContext *escontext, bool omit_quotes,
					 bool exists_coerce,
					 Datum *resv, bool *resnull)
{
	ExprEvalStep scratch = {0};

	/* For json_populate_type() */
	scratch.opcode = EEOP_JSONEXPR_COERCION;
	scratch.resvalue = resv;
	scratch.resnull = resnull;
	scratch.d.jsonexpr_coercion.targettype = returning->typid;
	scratch.d.jsonexpr_coercion.targettypmod = returning->typmod;
	scratch.d.jsonexpr_coercion.json_coercion_cache = NULL;
	scratch.d.jsonexpr_coercion.escontext = escontext;
	scratch.d.jsonexpr_coercion.omit_quotes = omit_quotes;
	scratch.d.jsonexpr_coercion.exists_coerce = exists_coerce;
	scratch.d.jsonexpr_coercion.exists_cast_to_int = exists_coerce &&
		getBaseType(returning->typid) == INT4OID;
	scratch.d.jsonexpr_coercion.exists_check_domain = exists_coerce &&
		DomainHasConstraints(returning->typid, NULL);
	ExprEvalPushStep(state, &scratch);
}
