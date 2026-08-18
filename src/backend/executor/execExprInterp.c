/*-------------------------------------------------------------------------
 *
 * execExprInterp.c
 *	  Interpreted evaluation of an expression step list.
 *
 * This file provides either a "direct threaded" (for gcc, clang and
 * compatible) or a "switch threaded" (for all compilers) implementation of
 * expression evaluation.  The former is amongst the fastest known methods
 * of interpreting programs without resorting to assembly level work, or
 * just-in-time compilation, but it requires support for computed gotos.
 * The latter is amongst the fastest approaches doable in standard C.
 *
 * In either case we use ExprEvalStep->opcode to dispatch to the code block
 * within ExecInterpExpr() that implements the specific opcode type.
 *
 * Switch-threading uses a plain switch() statement to perform the
 * dispatch.  This has the advantages of being plain C and allowing the
 * compiler to warn if implementation of a specific opcode has been forgotten.
 * The disadvantage is that dispatches will, as commonly implemented by
 * compilers, happen from a single location, requiring more jumps and causing
 * bad branch prediction.
 *
 * In direct threading, we use gcc's label-as-values extension - also adopted
 * by some other compilers - to replace ExprEvalStep->opcode with the address
 * of the block implementing the instruction. Dispatch to the next instruction
 * is done by a "computed goto".  This allows for better branch prediction
 * (as the jumps are happening from different locations) and fewer jumps
 * (as no preparatory jump to a common dispatch location is needed).
 *
 * When using direct threading, ExecReadyInterpretedExpr will replace
 * each step's opcode field with the address of the relevant code block and
 * ExprState->flags will contain EEO_FLAG_DIRECT_THREADED to remember that
 * that's been done.
 *
 * For very simple instructions the overhead of the full interpreter
 * "startup", as minimal as it is, is noticeable.  Therefore
 * ExecReadyInterpretedExpr will choose to implement certain simple
 * opcode patterns using special fast-path routines (ExecJust*).
 *
 * Complex or uncommon instructions are not implemented in-line in
 * ExecInterpExpr(), rather we call out to a helper function appearing later
 * in this file.  For one reason, there'd not be a noticeable performance
 * benefit, but more importantly those complex routines are intended to be
 * shared between different expression evaluation approaches.  For instance
 * a JIT compiler would generate calls to them.  (This is why they are
 * exported rather than being "static" in this file.)
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/executor/execExprInterp.c
 *
 *-------------------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】execExprInterp.c —— 表达式 step 列表的解释执行引擎（表达式执行核心）
 * ----------------------------------------------------------------------------
 * 文件作用：
 *   本文件是 PostgreSQL 表达式执行的"运行时"核心：由 execExpr.c 编译生成的
 *   ExprEvalStep 步列表（存于 ExprState->steps）在这里被逐条解释执行，
 *   ExecInterpExpr() 是主解释器入口，文件中实现了全部 EEOP_* opcode 的求值逻辑。
 *   与 execExpr.c 的分工：execExpr.c 负责"编译"——把表达式树展开成平坦的
 *   step 数组并做各种优化决策；本文件负责"执行"——逐 step 求值，并把复杂
 *   指令外包给本文件后部的 ExecEval* 辅助函数。二者共同构成 ExprState 的
 *   完整生命周期。
 *
 * 设计思想：
 *   1. 编译型解释器（flat step list）：
 *      表达式求值不再采用递归树遍历，而是先把表达式树压平为顺序的
 *      ExprEvalStep 数组（每个 step 对应一个 opcode 与执行数据 op->d.*）。
 *      解释器用大 switch（或 JIT 编译后的原生代码）逐条求值，控制流
 *      （AND/OR 短路、CASE 分支、ON ERROR 跳转等）由 EEO_JUMP/EEO_NEXT 跳转
 *      指令实现。平坦布局避免了递归调用的开销，同时该布局对 JIT 友好——
 *      LLVM 可以直接把它翻译为原生机器码。
 *   2. 两种派发方式（性能要点）：
 *      - 直接线程化（direct threading，gcc/clang 的计算 goto 扩展）：执行前
 *        由 ExecReadyInterpretedExpr 把每个 step 的 opcode 域替换为对应实现
 *        代码块的地址，用 "computed goto" 完成跳转；分支预测更好、跳转更少，
 *        是已知最快的解释执行方式之一。
 *      - 开关线程化（switch threading）：标准 C 的 switch 语句派发，兼容所有
 *        编译器，且编译器能警告遗漏的 opcode 实现。
 *      两种方式通过本文件的 EEO_* 宏体系（EEO_CASE / EEO_DISPATCH / EEO_NEXT /
 *      EEO_JUMP）完全屏蔽差异，EEO_SWITCH 在开关方式下是 switch、在直接线程
 *      方式下为空。
 *   3. 执行性能细节：
 *      - step 内嵌常量、槽指针、上下文指针、fcinfo 等，避免运行时查找；
 *      - 每个 step 的结果写入 op->resvalue/op->resnull（常见情形就是
 *        state->resvalue/state->resnull），实现"寄存器式"结果传递；
 *      - 取值用 fetch_att 式的数组直取（配合 FETCHSOME 预变形），避开慢路径；
 *      - 函数调用是超级热路径，因此拆出 EEOP_FUNCEXPR_STRICT/_1/_2/_FUSAGE
 *        等专门 opcode，按"是否严格、参数个数、是否统计函数调用"分派；
 *      - 复杂或罕见指令（数组、JSON、XML、聚合转移等）不内联，改为调用
 *        本文件后部的导出辅助函数（非 static）——它们与 JIT 共享：JIT 编译器
 *        直接生成对这些函数的调用，这就是它们被导出的原因。
 *   4. 快速路径（ExecJust*）：对极简单的表达式（如直接的 Var 引用、Const、
 *      CASE_TESTVAL+严格函数等），ExecReadyInterpretedExpr 会按 steps_len 与
 *      opcode 模式匹配专用的 ExecJust* 函数，省去解释器启动开销。
 *   5. 有效性校验：ExecInterpExprStillValid / CheckExprStillValid 在计划被
 *      缓存复用、schema 可能已变化时，于首次执行前校验 Var 引用的属性类型
 *      仍与槽的元组描述符匹配（查表/切换执行函数只做一次），防止类型错乱；
 *      校验通过后才把 evalfunc 切换为真正的执行函数。
 *   6. 与 JIT 的协作：exprjit.c（LLVM 编译）直接复制本文件解释器骨架来生成
 *      原生代码，因此本文件的函数布局、EEO 宏体系被刻意保持稳定，修改时
 *      需同步考虑 execExprJit.c。
 * ============================================================================
 */
#include "postgres.h"

#include "access/heaptoast.h"
#include "access/tupconvert.h"
#include "catalog/pg_type.h"
#include "commands/sequence.h"
#include "executor/execExpr.h"
#include "executor/nodeSubplan.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/miscnodes.h"
#include "nodes/nodeFuncs.h"
#include "pgstat.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/date.h"
#include "utils/datum.h"
#include "utils/expandedrecord.h"
#include "utils/json.h"
#include "utils/jsonfuncs.h"
#include "utils/jsonpath.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/timestamp.h"
#include "utils/tuplesort.h"
#include "utils/typcache.h"
#include "utils/xml.h"

/*
 * Use computed-goto-based opcode dispatch when computed gotos are available.
 * But use a separate symbol so that it's easy to adjust locally in this file
 * for development and testing.
 */
#ifdef HAVE_COMPUTED_GOTO
#define EEO_USE_COMPUTED_GOTO
#endif							/* HAVE_COMPUTED_GOTO */

/*
 * Macros for opcode dispatch.
 *
 * EEO_SWITCH - just hides the switch if not in use.
 * EEO_CASE - labels the implementation of named expression step type.
 * EEO_DISPATCH - jump to the implementation of the step type for 'op'.
 * EEO_OPCODE - compute opcode required by used expression evaluation method.
 * EEO_NEXT - increment 'op' and jump to correct next step type.
 * EEO_JUMP - jump to the specified step number within the current expression.
 */
#if defined(EEO_USE_COMPUTED_GOTO)

/* struct for jump target -> opcode lookup table */
typedef struct ExprEvalOpLookup
{
	const void *opcode;
	ExprEvalOp	op;
} ExprEvalOpLookup;

/* to make dispatch_table accessible outside ExecInterpExpr() */
static const void **dispatch_table = NULL;

/* jump target -> opcode lookup table */
static ExprEvalOpLookup reverse_dispatch_table[EEOP_LAST];

#define EEO_SWITCH()
#define EEO_CASE(name)		CASE_##name:
#define EEO_DISPATCH()		goto *((void *) op->opcode)
#define EEO_OPCODE(opcode)	((intptr_t) dispatch_table[opcode])

#else							/* !EEO_USE_COMPUTED_GOTO */

#define EEO_SWITCH()		starteval: switch ((ExprEvalOp) op->opcode)
#define EEO_CASE(name)		case name:
#define EEO_DISPATCH()		goto starteval
#define EEO_OPCODE(opcode)	(opcode)

#endif							/* EEO_USE_COMPUTED_GOTO */

#define EEO_NEXT() \
	do { \
		op++; \
		EEO_DISPATCH(); \
	} while (0)

#define EEO_JUMP(stepno) \
	do { \
		op = &state->steps[stepno]; \
		EEO_DISPATCH(); \
	} while (0)


static Datum ExecInterpExpr(ExprState *state, ExprContext *econtext, bool *isnull);
static void ExecInitInterpreter(void);

/* support functions */
static void CheckVarSlotCompatibility(TupleTableSlot *slot, int attnum, Oid vartype);
static void CheckOpSlotCompatibility(ExprEvalStep *op, TupleTableSlot *slot);
static TupleDesc get_cached_rowtype(Oid type_id, int32 typmod,
									ExprEvalRowtypeCache *rowcache,
									bool *changed);
static void ExecEvalRowNullInt(ExprState *state, ExprEvalStep *op,
							   ExprContext *econtext, bool checkisnull);

/* fast-path evaluation functions */
static Datum ExecJustInnerVar(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustOuterVar(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustScanVar(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustAssignInnerVar(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustAssignOuterVar(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustAssignScanVar(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustApplyFuncToCase(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustConst(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustInnerVarVirt(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustOuterVarVirt(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustScanVarVirt(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustAssignInnerVarVirt(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustAssignOuterVarVirt(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustAssignScanVarVirt(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustHashInnerVarWithIV(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustHashOuterVar(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustHashInnerVar(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustHashOuterVarVirt(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustHashInnerVarVirt(ExprState *state, ExprContext *econtext, bool *isnull);
static Datum ExecJustHashOuterVarStrict(ExprState *state, ExprContext *econtext, bool *isnull);

/* execution helper functions */
static pg_always_inline void ExecEvalArrayCompareInternal(FunctionCallInfo fcinfo,
														  ArrayType *arr,
														  int16 typlen,
														  bool typbyval,
														  char typalign,
														  bool useOr,
														  Datum *result,
														  bool *resultnull);
static pg_always_inline void ExecAggPlainTransByVal(AggState *aggstate,
													AggStatePerTrans pertrans,
													AggStatePerGroup pergroup,
													ExprContext *aggcontext,
													int setno);
static pg_always_inline void ExecAggPlainTransByRef(AggState *aggstate,
													AggStatePerTrans pertrans,
													AggStatePerGroup pergroup,
													ExprContext *aggcontext,
													int setno);
static char *ExecGetJsonValueItemString(JsonbValue *item, bool *resnull);

/*
 * ScalarArrayOpExprHashEntry
 * 		Hash table entry type used during EEOP_HASHED_SCALARARRAYOP
 */
typedef struct ScalarArrayOpExprHashEntry
{
	Datum		key;
	uint32		status;			/* hash status */
	uint32		hash;			/* hash value (cached) */
} ScalarArrayOpExprHashEntry;

#define SH_PREFIX saophash
#define SH_ELEMENT_TYPE ScalarArrayOpExprHashEntry
#define SH_KEY_TYPE Datum
#define SH_SCOPE static inline
#define SH_DECLARE
#include "lib/simplehash.h"

static bool saop_hash_element_match(struct saophash_hash *tb, Datum key1,
									Datum key2);
static uint32 saop_element_hash(struct saophash_hash *tb, Datum key);

/*
 * ScalarArrayOpExprHashTable
 *		Hash table for EEOP_HASHED_SCALARARRAYOP
 */
typedef struct ScalarArrayOpExprHashTable
{
	saophash_hash *hashtab;		/* underlying hash table */
	struct ExprEvalStep *op;
	FmgrInfo	hash_finfo;		/* function's lookup data */
	FunctionCallInfoBaseData hash_fcinfo_data;	/* arguments etc */
} ScalarArrayOpExprHashTable;

/* Define parameters for ScalarArrayOpExpr hash table code generation. */
#define SH_PREFIX saophash
#define SH_ELEMENT_TYPE ScalarArrayOpExprHashEntry
#define SH_KEY_TYPE Datum
#define SH_KEY key
#define SH_HASH_KEY(tb, key) saop_element_hash(tb, key)
#define SH_EQUAL(tb, a, b) saop_hash_element_match(tb, a, b)
#define SH_SCOPE static inline
#define SH_STORE_HASH
#define SH_GET_HASH(tb, a) a->hash
#define SH_DEFINE
#include "lib/simplehash.h"

/*
 * ============================================================================
 * 【中文注释】ExecReadyInterpretedExpr —— 为解释执行准备 ExprState（出口函数）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对外出口：给定编译完成的 ExprState（其中含 steps 数组），完成解释执行
 *   的全部准备：初始化派发表、挂上"先用校验再执行"的 evalfunc、为极简单
 *   表达式选择 ExecJust* 快速路径、并将 opcode 替换为代码块地址（直接线程
 *   方式）。execExpr.c 的 ExecInitExprRec 编译完步骤后会调用本函数收尾。
 *
 * 参数：
 *   state - 已编译好的 ExprState，其后 steps_len >= 1 且最后一步必须是
 *           EEOP_DONE_RETURN（返回结果）或 EEOP_DONE_NO_RETURN（无结果）。
 *
 * 设计思想：
 *   1. 校验与防重：断言 step 列表非空且以 DONE 步骤收尾；EEO_FLAG_INTERPRETER_
 *      INITIALIZED 标志防止重复初始化（未来若出现依赖解释执行的其它求值方法
 *      也不至于重复做）。
 *   2. "先校验后执行"的延迟接线：把 state->evalfunc 初始化为
 *      ExecInterpExprStillValid——第一次真正执行时调用它做 schema 兼容性检查
 *      （计划可能因 DDL 而过期），成功后就原地替换为真正的执行函数
 *      （evalfunc_private），检查只做一次。
 *   3. 快速路径选择：按 steps_len（2~5）与 opcode 模式组合匹配 ExecJust* 专用
 *      函数（如 FETCHSOME+INNER_VAR 两个 step 直接匹配 ExecJustInnerVar），
 *      避免小表达式也要走完整解释器的启动开销；没有匹配则走通用解释器。
 *   4. 直接线程化（仅计算 goto 可用时）：把每一步 op->opcode 原地替换为对应
 *      CASE_* 代码块的地址（EEO_OPCODE 宏从 dispatch_table 查地址），置
 *      EEO_FLAG_DIRECT_THREADED 标志，此后 ExecEvalStepOp() 需要靠反查表
 *      reverse_dispatch_table 才能还原 opcode。
 * ============================================================================
 */
void
ExecReadyInterpretedExpr(ExprState *state)
{
	/* Ensure one-time interpreter setup has been done */
	ExecInitInterpreter();

	/* Simple validity checks on expression */
	Assert(state->steps_len >= 1);
	Assert(state->steps[state->steps_len - 1].opcode == EEOP_DONE_RETURN ||
		   state->steps[state->steps_len - 1].opcode == EEOP_DONE_NO_RETURN);

	/*
	 * Don't perform redundant initialization. This is unreachable in current
	 * cases, but might be hit if there's additional expression evaluation
	 * methods that rely on interpreted execution to work.
	 */
	if (state->flags & EEO_FLAG_INTERPRETER_INITIALIZED)
		return;

	/*
	 * First time through, check whether attribute matches Var.  Might not be
	 * ok anymore, due to schema changes. We do that by setting up a callback
	 * that does checking on the first call, which then sets the evalfunc
	 * callback to the actual method of execution.
	 */
	state->evalfunc = ExecInterpExprStillValid;

	/* DIRECT_THREADED should not already be set */
	Assert((state->flags & EEO_FLAG_DIRECT_THREADED) == 0);

	/*
	 * There shouldn't be any errors before the expression is fully
	 * initialized, and even if so, it'd lead to the expression being
	 * abandoned.  So we can set the flag now and save some code.
	 */
	state->flags |= EEO_FLAG_INTERPRETER_INITIALIZED;

	/*
	 * Select fast-path evalfuncs for very simple expressions.  "Starting up"
	 * the full interpreter is a measurable overhead for these, and these
	 * patterns occur often enough to be worth optimizing.
	 */
	if (state->steps_len == 5)
	{
		ExprEvalOp	step0 = state->steps[0].opcode;
		ExprEvalOp	step1 = state->steps[1].opcode;
		ExprEvalOp	step2 = state->steps[2].opcode;
		ExprEvalOp	step3 = state->steps[3].opcode;

		if (step0 == EEOP_INNER_FETCHSOME &&
			step1 == EEOP_HASHDATUM_SET_INITVAL &&
			step2 == EEOP_INNER_VAR &&
			step3 == EEOP_HASHDATUM_NEXT32)
		{
			state->evalfunc_private = (void *) ExecJustHashInnerVarWithIV;
			return;
		}
	}
	else if (state->steps_len == 4)
	{
		ExprEvalOp	step0 = state->steps[0].opcode;
		ExprEvalOp	step1 = state->steps[1].opcode;
		ExprEvalOp	step2 = state->steps[2].opcode;

		if (step0 == EEOP_OUTER_FETCHSOME &&
			step1 == EEOP_OUTER_VAR &&
			step2 == EEOP_HASHDATUM_FIRST)
		{
			state->evalfunc_private = (void *) ExecJustHashOuterVar;
			return;
		}
		else if (step0 == EEOP_INNER_FETCHSOME &&
				 step1 == EEOP_INNER_VAR &&
				 step2 == EEOP_HASHDATUM_FIRST)
		{
			state->evalfunc_private = (void *) ExecJustHashInnerVar;
			return;
		}
		else if (step0 == EEOP_OUTER_FETCHSOME &&
				 step1 == EEOP_OUTER_VAR &&
				 step2 == EEOP_HASHDATUM_FIRST_STRICT)
		{
			state->evalfunc_private = (void *) ExecJustHashOuterVarStrict;
			return;
		}
	}
	else if (state->steps_len == 3)
	{
		ExprEvalOp	step0 = state->steps[0].opcode;
		ExprEvalOp	step1 = state->steps[1].opcode;

		if (step0 == EEOP_INNER_FETCHSOME &&
			step1 == EEOP_INNER_VAR)
		{
			state->evalfunc_private = ExecJustInnerVar;
			return;
		}
		else if (step0 == EEOP_OUTER_FETCHSOME &&
				 step1 == EEOP_OUTER_VAR)
		{
			state->evalfunc_private = ExecJustOuterVar;
			return;
		}
		else if (step0 == EEOP_SCAN_FETCHSOME &&
				 step1 == EEOP_SCAN_VAR)
		{
			state->evalfunc_private = ExecJustScanVar;
			return;
		}
		else if (step0 == EEOP_INNER_FETCHSOME &&
				 step1 == EEOP_ASSIGN_INNER_VAR)
		{
			state->evalfunc_private = ExecJustAssignInnerVar;
			return;
		}
		else if (step0 == EEOP_OUTER_FETCHSOME &&
				 step1 == EEOP_ASSIGN_OUTER_VAR)
		{
			state->evalfunc_private = ExecJustAssignOuterVar;
			return;
		}
		else if (step0 == EEOP_SCAN_FETCHSOME &&
				 step1 == EEOP_ASSIGN_SCAN_VAR)
		{
			state->evalfunc_private = ExecJustAssignScanVar;
			return;
		}
		else if (step0 == EEOP_CASE_TESTVAL &&
				 (step1 == EEOP_FUNCEXPR_STRICT ||
				  step1 == EEOP_FUNCEXPR_STRICT_1 ||
				  step1 == EEOP_FUNCEXPR_STRICT_2))
		{
			state->evalfunc_private = ExecJustApplyFuncToCase;
			return;
		}
		else if (step0 == EEOP_INNER_VAR &&
				 step1 == EEOP_HASHDATUM_FIRST)
		{
			state->evalfunc_private = (void *) ExecJustHashInnerVarVirt;
			return;
		}
		else if (step0 == EEOP_OUTER_VAR &&
				 step1 == EEOP_HASHDATUM_FIRST)
		{
			state->evalfunc_private = (void *) ExecJustHashOuterVarVirt;
			return;
		}
	}
	else if (state->steps_len == 2)
	{
		ExprEvalOp	step0 = state->steps[0].opcode;

		if (step0 == EEOP_CONST)
		{
			state->evalfunc_private = ExecJustConst;
			return;
		}
		else if (step0 == EEOP_INNER_VAR)
		{
			state->evalfunc_private = ExecJustInnerVarVirt;
			return;
		}
		else if (step0 == EEOP_OUTER_VAR)
		{
			state->evalfunc_private = ExecJustOuterVarVirt;
			return;
		}
		else if (step0 == EEOP_SCAN_VAR)
		{
			state->evalfunc_private = ExecJustScanVarVirt;
			return;
		}
		else if (step0 == EEOP_ASSIGN_INNER_VAR)
		{
			state->evalfunc_private = ExecJustAssignInnerVarVirt;
			return;
		}
		else if (step0 == EEOP_ASSIGN_OUTER_VAR)
		{
			state->evalfunc_private = ExecJustAssignOuterVarVirt;
			return;
		}
		else if (step0 == EEOP_ASSIGN_SCAN_VAR)
		{
			state->evalfunc_private = ExecJustAssignScanVarVirt;
			return;
		}
	}

#if defined(EEO_USE_COMPUTED_GOTO)

	/*
	 * In the direct-threaded implementation, replace each opcode with the
	 * address to jump to.  (Use ExecEvalStepOp() to get back the opcode.)
	 */
	for (int off = 0; off < state->steps_len; off++)
	{
		ExprEvalStep *op = &state->steps[off];

		op->opcode = EEO_OPCODE(op->opcode);
	}

	state->flags |= EEO_FLAG_DIRECT_THREADED;
#endif							/* EEO_USE_COMPUTED_GOTO */

	state->evalfunc_private = ExecInterpExpr;
}


/*
 * ============================================================================
 * 【中文注释】ExecInterpExpr —— 解释执行表达式 step 列表（核心解释器）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   主解释器：从 state->steps[0] 开始逐条解释执行 ExprEvalStep，直至遇到
 *   EEOP_DONE_RETURN 为止，把最终结果写入 *isnull 并作为 Datum 返回。每个
 *   EEOP_* opcode 对应 `EEO_CASE` 中的一个代码块；块内通过 EEO_NEXT()（下一
 *   step）或 EEO_JUMP()（跳转到指定 step）推进控制流。这是全库最热的执行
 *   路径之一：任何 SQL 表达式的求值最终都会汇聚到这。
 *
 * 参数：
 *   state   - ExprState：steps 数组、共享结果寄存器 resvalue/resnull、
 *             resultslot（结果槽）、flags 等。
 *   econtext- ExprContext：提供 innertuple/outertuple/scantuple/oldtuple/
 *             newtuple 五个输入元组槽、参数、caseValue/domainValue 等。
 *   isnull  - 输出：结果是否为 NULL（EEOP_DONE_NO_RETURN 时可为 NULL 指针）。
 *
 * 返回值：
 *   Datum - 表达式的值（DDONE_NO_RETURN 时恒为 (Datum) 0）。
 *
 * 设计思想：
 *   1. 单一 dispatch 循环：开头把五个输入槽指针缓存在局部变量中（相当于
 *      寄存器，避免每次访存），然后进入 EEO_SWITCH 大循环。直接线程化时
 *      每个 step 的 opcode 已被替换为代码块地址，EEO_DISPATCH 用计算 goto
 *      直达目标块；开关方式则回到 starteval 重新 switch。两种方式共享同一
 *      套 CASE 代码，因此逻辑只写一遍。
 *   2. op 与结果寄存器约定：op 指向当前 step；每个 step 执行后把结果写到
 *      *op->resvalue 与 *op->resnull（通常即 state->resvalue/state->resnull，
 *      编译期按需重定向到临时槽），配合 EEO_NEXT 实现"寄存器式"流水线。
 *   3. 宏体系语义：
 *      EEO_NEXT()  = op++ 然后派发（顺序执行下一步）；
 *      EEO_JUMP(n) = op = &state->steps[n] 然后派发（控制流跳转，供短路
 *                    求值、CASE 分支、ON ERROR 等使用，跳转目标由编译期
 *                    算好，无需运行时解释）；
 *      dispatch_table（静态数组）与 switch case 顺序必须与 execExpr.h 中
 *      的 enum ExprEvalOp 完全一致（StaticAssertDecl 保证数组长度匹配）。
 *   4. 特例：state == NULL 时返回 dispatch_table 的地址——这是
 *      ExecInitInterpreter 在直接线程方式下获取派发表数据的暗号，绝不
 *      会被当作正常求值调用。
 *   5. 简单指令尽量内联手写汇编级代码；复杂指令（数组/JSON/聚合等）则
 *      EEO_CASE 里只写一行调用，委托给本文件后部的 ExecEval* 函数，这些
 *      函数同样被 JIT 直接调用。
 * ============================================================================
 */
static Datum
ExecInterpExpr(ExprState *state, ExprContext *econtext, bool *isnull)
{
	ExprEvalStep *op;
	TupleTableSlot *resultslot;
	TupleTableSlot *innerslot;
	TupleTableSlot *outerslot;
	TupleTableSlot *scanslot;
	TupleTableSlot *oldslot;
	TupleTableSlot *newslot;

	/*
	 * This array has to be in the same order as enum ExprEvalOp.
	 */
#if defined(EEO_USE_COMPUTED_GOTO)
	static const void *const dispatch_table[] = {
		&&CASE_EEOP_DONE_RETURN,
		&&CASE_EEOP_DONE_NO_RETURN,
		&&CASE_EEOP_INNER_FETCHSOME,
		&&CASE_EEOP_OUTER_FETCHSOME,
		&&CASE_EEOP_SCAN_FETCHSOME,
		&&CASE_EEOP_OLD_FETCHSOME,
		&&CASE_EEOP_NEW_FETCHSOME,
		&&CASE_EEOP_INNER_VAR,
		&&CASE_EEOP_OUTER_VAR,
		&&CASE_EEOP_SCAN_VAR,
		&&CASE_EEOP_OLD_VAR,
		&&CASE_EEOP_NEW_VAR,
		&&CASE_EEOP_INNER_SYSVAR,
		&&CASE_EEOP_OUTER_SYSVAR,
		&&CASE_EEOP_SCAN_SYSVAR,
		&&CASE_EEOP_OLD_SYSVAR,
		&&CASE_EEOP_NEW_SYSVAR,
		&&CASE_EEOP_WHOLEROW,
		&&CASE_EEOP_ASSIGN_INNER_VAR,
		&&CASE_EEOP_ASSIGN_OUTER_VAR,
		&&CASE_EEOP_ASSIGN_SCAN_VAR,
		&&CASE_EEOP_ASSIGN_OLD_VAR,
		&&CASE_EEOP_ASSIGN_NEW_VAR,
		&&CASE_EEOP_ASSIGN_TMP,
		&&CASE_EEOP_ASSIGN_TMP_MAKE_RO,
		&&CASE_EEOP_CONST,
		&&CASE_EEOP_FUNCEXPR,
		&&CASE_EEOP_FUNCEXPR_STRICT,
		&&CASE_EEOP_FUNCEXPR_STRICT_1,
		&&CASE_EEOP_FUNCEXPR_STRICT_2,
		&&CASE_EEOP_FUNCEXPR_FUSAGE,
		&&CASE_EEOP_FUNCEXPR_STRICT_FUSAGE,
		&&CASE_EEOP_BOOL_AND_STEP_FIRST,
		&&CASE_EEOP_BOOL_AND_STEP,
		&&CASE_EEOP_BOOL_AND_STEP_LAST,
		&&CASE_EEOP_BOOL_OR_STEP_FIRST,
		&&CASE_EEOP_BOOL_OR_STEP,
		&&CASE_EEOP_BOOL_OR_STEP_LAST,
		&&CASE_EEOP_BOOL_NOT_STEP,
		&&CASE_EEOP_QUAL,
		&&CASE_EEOP_JUMP,
		&&CASE_EEOP_JUMP_IF_NULL,
		&&CASE_EEOP_JUMP_IF_NOT_NULL,
		&&CASE_EEOP_JUMP_IF_NOT_TRUE,
		&&CASE_EEOP_NULLTEST_ISNULL,
		&&CASE_EEOP_NULLTEST_ISNOTNULL,
		&&CASE_EEOP_NULLTEST_ROWISNULL,
		&&CASE_EEOP_NULLTEST_ROWISNOTNULL,
		&&CASE_EEOP_BOOLTEST_IS_TRUE,
		&&CASE_EEOP_BOOLTEST_IS_NOT_TRUE,
		&&CASE_EEOP_BOOLTEST_IS_FALSE,
		&&CASE_EEOP_BOOLTEST_IS_NOT_FALSE,
		&&CASE_EEOP_PARAM_EXEC,
		&&CASE_EEOP_PARAM_EXTERN,
		&&CASE_EEOP_PARAM_CALLBACK,
		&&CASE_EEOP_PARAM_SET,
		&&CASE_EEOP_CASE_TESTVAL,
		&&CASE_EEOP_CASE_TESTVAL_EXT,
		&&CASE_EEOP_MAKE_READONLY,
		&&CASE_EEOP_IOCOERCE,
		&&CASE_EEOP_IOCOERCE_SAFE,
		&&CASE_EEOP_DISTINCT,
		&&CASE_EEOP_NOT_DISTINCT,
		&&CASE_EEOP_NULLIF,
		&&CASE_EEOP_SQLVALUEFUNCTION,
		&&CASE_EEOP_CURRENTOFEXPR,
		&&CASE_EEOP_NEXTVALUEEXPR,
		&&CASE_EEOP_RETURNINGEXPR,
		&&CASE_EEOP_ARRAYEXPR,
		&&CASE_EEOP_ARRAYCOERCE,
		&&CASE_EEOP_ROW,
		&&CASE_EEOP_ROWCOMPARE_STEP,
		&&CASE_EEOP_ROWCOMPARE_FINAL,
		&&CASE_EEOP_MINMAX,
		&&CASE_EEOP_FIELDSELECT,
		&&CASE_EEOP_FIELDSTORE_DEFORM,
		&&CASE_EEOP_FIELDSTORE_FORM,
		&&CASE_EEOP_SBSREF_SUBSCRIPTS,
		&&CASE_EEOP_SBSREF_OLD,
		&&CASE_EEOP_SBSREF_ASSIGN,
		&&CASE_EEOP_SBSREF_FETCH,
		&&CASE_EEOP_DOMAIN_TESTVAL,
		&&CASE_EEOP_DOMAIN_TESTVAL_EXT,
		&&CASE_EEOP_DOMAIN_NOTNULL,
		&&CASE_EEOP_DOMAIN_CHECK,
		&&CASE_EEOP_HASHDATUM_SET_INITVAL,
		&&CASE_EEOP_HASHDATUM_FIRST,
		&&CASE_EEOP_HASHDATUM_FIRST_STRICT,
		&&CASE_EEOP_HASHDATUM_NEXT32,
		&&CASE_EEOP_HASHDATUM_NEXT32_STRICT,
		&&CASE_EEOP_CONVERT_ROWTYPE,
		&&CASE_EEOP_SCALARARRAYOP,
		&&CASE_EEOP_HASHED_SCALARARRAYOP,
		&&CASE_EEOP_XMLEXPR,
		&&CASE_EEOP_JSON_CONSTRUCTOR,
		&&CASE_EEOP_IS_JSON,
		&&CASE_EEOP_JSONEXPR_PATH,
		&&CASE_EEOP_JSONEXPR_COERCION,
		&&CASE_EEOP_JSONEXPR_COERCION_FINISH,
		&&CASE_EEOP_AGGREF,
		&&CASE_EEOP_GROUPING_FUNC,
		&&CASE_EEOP_WINDOW_FUNC,
		&&CASE_EEOP_MERGE_SUPPORT_FUNC,
		&&CASE_EEOP_SUBPLAN,
		&&CASE_EEOP_AGG_STRICT_DESERIALIZE,
		&&CASE_EEOP_AGG_DESERIALIZE,
		&&CASE_EEOP_AGG_STRICT_INPUT_CHECK_ARGS,
		&&CASE_EEOP_AGG_STRICT_INPUT_CHECK_ARGS_1,
		&&CASE_EEOP_AGG_STRICT_INPUT_CHECK_NULLS,
		&&CASE_EEOP_AGG_PLAIN_PERGROUP_NULLCHECK,
		&&CASE_EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYVAL,
		&&CASE_EEOP_AGG_PLAIN_TRANS_STRICT_BYVAL,
		&&CASE_EEOP_AGG_PLAIN_TRANS_BYVAL,
		&&CASE_EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYREF,
		&&CASE_EEOP_AGG_PLAIN_TRANS_STRICT_BYREF,
		&&CASE_EEOP_AGG_PLAIN_TRANS_BYREF,
		&&CASE_EEOP_AGG_PRESORTED_DISTINCT_SINGLE,
		&&CASE_EEOP_AGG_PRESORTED_DISTINCT_MULTI,
		&&CASE_EEOP_AGG_ORDERED_TRANS_DATUM,
		&&CASE_EEOP_AGG_ORDERED_TRANS_TUPLE,
		&&CASE_EEOP_LAST
	};

	StaticAssertDecl(lengthof(dispatch_table) == EEOP_LAST + 1,
					 "dispatch_table out of whack with ExprEvalOp");

	if (unlikely(state == NULL))
		return PointerGetDatum(dispatch_table);
#else
	Assert(state != NULL);
#endif							/* EEO_USE_COMPUTED_GOTO */

	/* setup state */
	op = state->steps;
	resultslot = state->resultslot;
	innerslot = econtext->ecxt_innertuple;
	outerslot = econtext->ecxt_outertuple;
	scanslot = econtext->ecxt_scantuple;
	oldslot = econtext->ecxt_oldtuple;
	newslot = econtext->ecxt_newtuple;

#if defined(EEO_USE_COMPUTED_GOTO)
	EEO_DISPATCH();
#endif

	EEO_SWITCH()
	{
		/* 【中文注释】EEOP_DONE_RETURN —— 正常收尾：把 state 的结果寄存器
		 * （resvalue/resnull，由前面的 step 写入）原样返回给调用方。
		 * EEOP_DONE_NO_RETURN —— 无结果收尾：仅执行副作用（如把值写入
		 * 结果槽的 Assign 系列），isnull 可为 NULL，恒返回 0。 */
		EEO_CASE(EEOP_DONE_RETURN)
		{
			*isnull = state->resnull;
			return state->resvalue;
		}

		EEO_CASE(EEOP_DONE_NO_RETURN)
		{
			Assert(isnull == NULL);
			return (Datum) 0;
		}

		/* 【中文注释】EEOP_*_FETCHSOME —— 惰性元组变形：确保取自
		 * inner/outer/scan/old/new 槽的前 last_var 列已被变形到槽的
		 * tts_values/tts_isnull 数组中。slot_getsomeattrs 是廉价调用
		 * （已变形过的部分直接返回），compiler 只对需要的列发出该 step，
		 * 后续 EEOP_*_VAR 才能安全直取数组元素。CheckOpSlotCompatibility
		 * 顺带校验槽的实现类型与编译期预期一致。 */
		EEO_CASE(EEOP_INNER_FETCHSOME)
		{
			CheckOpSlotCompatibility(op, innerslot);

			slot_getsomeattrs(innerslot, op->d.fetch.last_var);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_OUTER_FETCHSOME)
		{
			CheckOpSlotCompatibility(op, outerslot);

			slot_getsomeattrs(outerslot, op->d.fetch.last_var);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_SCAN_FETCHSOME)
		{
			CheckOpSlotCompatibility(op, scanslot);

			slot_getsomeattrs(scanslot, op->d.fetch.last_var);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_OLD_FETCHSOME)
		{
			CheckOpSlotCompatibility(op, oldslot);

			slot_getsomeattrs(oldslot, op->d.fetch.last_var);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_NEW_FETCHSOME)
		{
			CheckOpSlotCompatibility(op, newslot);

			slot_getsomeattrs(newslot, op->d.fetch.last_var);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_(INNER|OUTER|SCAN|OLD|NEW)_VAR —— 取引用元组槽的
		 * 普通用户列。依赖前面 FETCHSOME step 已把该列变形好（Assert
		 * attnum < tts_nvalid 验证），直接从 tts_values/tts_isnull 数组
		 * 拷贝到结果寄存器——没有 slot_getattr 的边界/类型检查，速度最快。
		 * 五个变体仅槽来源不同：inner=连接内表、outer=外表、scan=当前
		 * 扫描关系（单表查询的缺省来源）、old/new=触发器的 OLD/NEW 行。 */
		EEO_CASE(EEOP_INNER_VAR)
		{
			int			attnum = op->d.var.attnum;

			/*
			 * Since we already extracted all referenced columns from the
			 * tuple with a FETCHSOME step, we can just grab the value
			 * directly out of the slot's decomposed-data arrays.  But let's
			 * have an Assert to check that that did happen.
			 */
			Assert(attnum >= 0 && attnum < innerslot->tts_nvalid);
			*op->resvalue = innerslot->tts_values[attnum];
			*op->resnull = innerslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_OUTER_VAR)
		{
			int			attnum = op->d.var.attnum;

			/* See EEOP_INNER_VAR comments */

			Assert(attnum >= 0 && attnum < outerslot->tts_nvalid);
			*op->resvalue = outerslot->tts_values[attnum];
			*op->resnull = outerslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_SCAN_VAR)
		{
			int			attnum = op->d.var.attnum;

			/* See EEOP_INNER_VAR comments */

			Assert(attnum >= 0 && attnum < scanslot->tts_nvalid);
			*op->resvalue = scanslot->tts_values[attnum];
			*op->resnull = scanslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_OLD_VAR)
		{
			int			attnum = op->d.var.attnum;

			/* See EEOP_INNER_VAR comments */

			Assert(attnum >= 0 && attnum < oldslot->tts_nvalid);
			*op->resvalue = oldslot->tts_values[attnum];
			*op->resnull = oldslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_NEW_VAR)
		{
			int			attnum = op->d.var.attnum;

			/* See EEOP_INNER_VAR comments */

			Assert(attnum >= 0 && attnum < newslot->tts_nvalid);
			*op->resvalue = newslot->tts_values[attnum];
			*op->resnull = newslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_*_SYSVAR —— 系统列（ctid/xmin 等）取值。系统列不
		 * 在 FETCHSOME 变形范围，必须走 ExecEvalSysVar 经 slot_getsysattr
		 * 计算（如 ctid 需要从行指针构造）。五个变体对应五个来源槽。 */
		EEO_CASE(EEOP_INNER_SYSVAR)
		{
			ExecEvalSysVar(state, op, econtext, innerslot);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_OUTER_SYSVAR)
		{
			ExecEvalSysVar(state, op, econtext, outerslot);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_SCAN_SYSVAR)
		{
			ExecEvalSysVar(state, op, econtext, scanslot);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_OLD_SYSVAR)
		{
			ExecEvalSysVar(state, op, econtext, oldslot);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_NEW_SYSVAR)
		{
			ExecEvalSysVar(state, op, econtext, newslot);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_WHOLEROW)
		{
			/* too complex for an inline implementation */
			ExecEvalWholeRowVar(state, op, econtext);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_ASSIGN_*_VAR —— 把引用槽的某一列直接写入结果槽的
		 * resultnum 列（零拷贝 Datum 搬运）。用于 SELECT 目标列直通、INSERT
		 * 时把输入行按位写入新行等场景；编译期已做过类型校验，这里不再
		 * 检查（仅 Assert 下标范围）。EEOP_ASSIGN_TMP / _MAKE_RO 则把当前
		 * 结果寄存器（临时值）写入结果槽，_MAKE_RO 额外把可变对象转只读
		 * （后续可能被多路复用读取）。 */
		EEO_CASE(EEOP_ASSIGN_INNER_VAR)
		{
			int			resultnum = op->d.assign_var.resultnum;
			int			attnum = op->d.assign_var.attnum;

			/*
			 * We do not need CheckVarSlotCompatibility here; that was taken
			 * care of at compilation time.  But see EEOP_INNER_VAR comments.
			 */
			Assert(attnum >= 0 && attnum < innerslot->tts_nvalid);
			Assert(resultnum >= 0 && resultnum < resultslot->tts_tupleDescriptor->natts);
			resultslot->tts_values[resultnum] = innerslot->tts_values[attnum];
			resultslot->tts_isnull[resultnum] = innerslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ASSIGN_OUTER_VAR)
		{
			int			resultnum = op->d.assign_var.resultnum;
			int			attnum = op->d.assign_var.attnum;

			/*
			 * We do not need CheckVarSlotCompatibility here; that was taken
			 * care of at compilation time.  But see EEOP_INNER_VAR comments.
			 */
			Assert(attnum >= 0 && attnum < outerslot->tts_nvalid);
			Assert(resultnum >= 0 && resultnum < resultslot->tts_tupleDescriptor->natts);
			resultslot->tts_values[resultnum] = outerslot->tts_values[attnum];
			resultslot->tts_isnull[resultnum] = outerslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ASSIGN_SCAN_VAR)
		{
			int			resultnum = op->d.assign_var.resultnum;
			int			attnum = op->d.assign_var.attnum;

			/*
			 * We do not need CheckVarSlotCompatibility here; that was taken
			 * care of at compilation time.  But see EEOP_INNER_VAR comments.
			 */
			Assert(attnum >= 0 && attnum < scanslot->tts_nvalid);
			Assert(resultnum >= 0 && resultnum < resultslot->tts_tupleDescriptor->natts);
			resultslot->tts_values[resultnum] = scanslot->tts_values[attnum];
			resultslot->tts_isnull[resultnum] = scanslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ASSIGN_OLD_VAR)
		{
			int			resultnum = op->d.assign_var.resultnum;
			int			attnum = op->d.assign_var.attnum;

			/*
			 * We do not need CheckVarSlotCompatibility here; that was taken
			 * care of at compilation time.  But see EEOP_INNER_VAR comments.
			 */
			Assert(attnum >= 0 && attnum < oldslot->tts_nvalid);
			Assert(resultnum >= 0 && resultnum < resultslot->tts_tupleDescriptor->natts);
			resultslot->tts_values[resultnum] = oldslot->tts_values[attnum];
			resultslot->tts_isnull[resultnum] = oldslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ASSIGN_NEW_VAR)
		{
			int			resultnum = op->d.assign_var.resultnum;
			int			attnum = op->d.assign_var.attnum;

			/*
			 * We do not need CheckVarSlotCompatibility here; that was taken
			 * care of at compilation time.  But see EEOP_INNER_VAR comments.
			 */
			Assert(attnum >= 0 && attnum < newslot->tts_nvalid);
			Assert(resultnum >= 0 && resultnum < resultslot->tts_tupleDescriptor->natts);
			resultslot->tts_values[resultnum] = newslot->tts_values[attnum];
			resultslot->tts_isnull[resultnum] = newslot->tts_isnull[attnum];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ASSIGN_TMP)
		{
			int			resultnum = op->d.assign_tmp.resultnum;

			Assert(resultnum >= 0 && resultnum < resultslot->tts_tupleDescriptor->natts);
			resultslot->tts_values[resultnum] = state->resvalue;
			resultslot->tts_isnull[resultnum] = state->resnull;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ASSIGN_TMP_MAKE_RO)
		{
			int			resultnum = op->d.assign_tmp.resultnum;

			Assert(resultnum >= 0 && resultnum < resultslot->tts_tupleDescriptor->natts);
			resultslot->tts_isnull[resultnum] = state->resnull;
			if (!resultslot->tts_isnull[resultnum])
				resultslot->tts_values[resultnum] =
					MakeExpandedObjectReadOnlyInternal(state->resvalue);
			else
				resultslot->tts_values[resultnum] = state->resvalue;

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_CONST —— 常量：编译期已把值/是否为 NULL 内嵌进 step，
		 * 直接拷贝到结果寄存器，无任何运行时计算。 */
		EEO_CASE(EEOP_CONST)
		{
			*op->resnull = op->d.constval.isnull;
			*op->resvalue = op->d.constval.value;

			EEO_NEXT();
		}

		/*
		 * 【中文注释】函数调用族（EEOP_FUNCEXPR / _STRICT / _STRICT_1 /
		 * _STRICT_2 / _FUSAGE / _STRICT_FUSAGE）：实参在编译期已被求值并
		 * 直接写入 fcinfo->args，这里只做"调函数+收结果"。由于函数调用是
		 * 最热的热路径（运算符底层也是函数），特意按"是否严格、参数个数
		 * （1/2/多）、是否统计调用次数（pg_stat_function_calls 等）"拆成
		 * 六个 opcode，每种形态的手写代码都是最短路径：
		 * - 非严格：无条件调 fn_addr；
		 * - 严格：先扫参，遇 NULL 直接短路为 NULL 结果（goto strictfail）
		 *   不调用函数（严格函数定义：输入含 NULL 则结果恒 NULL）；
		 * - _FUSAGE：包 pgstat_init/end_function_usage 统计函数调用，
		 *   不常见，不值得内联。
		 * 注：这里用临时变量 `d` 接返回值而非直接 *op->resvalue = fn()——
		 * 某些编译器会误以为 fn() 可能改动 op->resvalue，
		 * 为保险把 op->resvalue 先压入寄存器再做函数调用，多一行代码可
		 * 省掉一次无用的寄存器溢出/重载。
		 */
		EEO_CASE(EEOP_FUNCEXPR)
		{
			FunctionCallInfo fcinfo = op->d.func.fcinfo_data;
			Datum		d;

			fcinfo->isnull = false;
			d = op->d.func.fn_addr(fcinfo);
			*op->resvalue = d;
			*op->resnull = fcinfo->isnull;

			EEO_NEXT();
		}

		/* 严格函数，参数多于 2 个：逐参查 NULL，任一为 NULL 即短路返回 NULL */
		EEO_CASE(EEOP_FUNCEXPR_STRICT)
		{
			FunctionCallInfo fcinfo = op->d.func.fcinfo_data;
			NullableDatum *args = fcinfo->args;
			int			nargs = op->d.func.nargs;
			Datum		d;

			Assert(nargs > 2);

			/* strict function, so check for NULL args */
			for (int argno = 0; argno < nargs; argno++)
			{
				if (args[argno].isnull)
				{
					*op->resnull = true;
					goto strictfail;
				}
			}
			fcinfo->isnull = false;
			d = op->d.func.fn_addr(fcinfo);
			*op->resvalue = d;
			*op->resnull = fcinfo->isnull;

	strictfail:
			EEO_NEXT();
		}

		/* 严格函数，恰好 1 个参数：常见形态（如 abs(x)、upper(s)），单次判空 */
		EEO_CASE(EEOP_FUNCEXPR_STRICT_1)
		{
			FunctionCallInfo fcinfo = op->d.func.fcinfo_data;
			NullableDatum *args = fcinfo->args;

			Assert(op->d.func.nargs == 1);

			/* strict function, so check for NULL args */
			if (args[0].isnull)
				*op->resnull = true;
			else
			{
				Datum		d;

				fcinfo->isnull = false;
				d = op->d.func.fn_addr(fcinfo);
				*op->resvalue = d;
				*op->resnull = fcinfo->isnull;
			}

			EEO_NEXT();
		}

		/* 严格函数，恰好 2 个参数：最常见形态（如 x = y），二元判空 */
		EEO_CASE(EEOP_FUNCEXPR_STRICT_2)
		{
			FunctionCallInfo fcinfo = op->d.func.fcinfo_data;
			NullableDatum *args = fcinfo->args;

			Assert(op->d.func.nargs == 2);

			/* strict function, so check for NULL args */
			if (args[0].isnull || args[1].isnull)
				*op->resnull = true;
			else
			{
				Datum		d;

				fcinfo->isnull = false;
				d = op->d.func.fn_addr(fcinfo);
				*op->resvalue = d;
				*op->resnull = fcinfo->isnull;
			}

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_FUNCEXPR_FUSAGE / _STRICT_FUSAGE —— 需要 pg_stat
		 * 函数调用统计的版本（如"函数调用次数/耗时"采样）。不常见，直接
		 * 委托 out-of-line 实现，避免污染热路径。 */
		EEO_CASE(EEOP_FUNCEXPR_FUSAGE)
		{
			/* not common enough to inline */
			ExecEvalFuncExprFusage(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_FUNCEXPR_STRICT_FUSAGE)
		{
			/* not common enough to inline */
			ExecEvalFuncExprStrictFusage(state, op, econtext);

			EEO_NEXT();
		}

		/*
		 * 【中文注释】EEOP_BOOL_AND_STEP* —— AND 三段式求值（布尔短路
		 * 语义）：只要有一个子句为 FALSE，整个 AND 恒为 FALSE，可立即
		 * 短路跳转到 jumpdone；否则若有任意子句为 NULL 则结果 NULL
		 * （把 NULL 解释为"未知"：未知可能本应是 FALSE）；只有全部子句
		 * 都确知为 TRUE 时结果才为 TRUE。三段分工：
		 * - _STEP_FIRST：清空 anynull 标志（每组 AND 的第一步专用），
		 *   然后落入 _STEP；
		 * - _STEP：子句结果在结果寄存器中：NULL 则置 anynull；FALSE 则
		 *   结果寄存器已是 FALSE，可以提前 EEO_JUMP 到 jumpdone 收工；
		 * - _STEP_LAST：末位子句，无须跳转（跳转目标与自然结束相同，
		 *   反而更贵）：FALSE 直接收尾；TRUE 且 anynull 则改写结果为
		 *   NULL；全 TRUE 则保持 TRUE。结果布尔值最初由编译器预置为
		 *   TRUE（AND 的恒真初值）。
		 */
		EEO_CASE(EEOP_BOOL_AND_STEP_FIRST)
		{
			*op->d.boolexpr.anynull = false;

			/*
			 * EEOP_BOOL_AND_STEP_FIRST resets anynull, otherwise it's the
			 * same as EEOP_BOOL_AND_STEP - so fall through to that.
			 */

			/* FALL THROUGH */
		}

		EEO_CASE(EEOP_BOOL_AND_STEP)
		{
			if (*op->resnull)
			{
				*op->d.boolexpr.anynull = true;
			}
			else if (!DatumGetBool(*op->resvalue))
			{
				/* result is already set to FALSE, need not change it */
				/* bail out early */
				EEO_JUMP(op->d.boolexpr.jumpdone);
			}

			EEO_NEXT();
		}

		EEO_CASE(EEOP_BOOL_AND_STEP_LAST)
		{
			if (*op->resnull)
			{
				/* result is already set to NULL, need not change it */
			}
			else if (!DatumGetBool(*op->resvalue))
			{
				/* result is already set to FALSE, need not change it */

				/*
				 * No point jumping early to jumpdone - would be same target
				 * (as this is the last argument to the AND expression),
				 * except more expensive.
				 */
			}
			else if (*op->d.boolexpr.anynull)
			{
				*op->resvalue = (Datum) 0;
				*op->resnull = true;
			}
			else
			{
				/* result is already set to TRUE, need not change it */
			}

			EEO_NEXT();
		}

		/*
		 * 【中文注释】EEOP_BOOL_OR_STEP* —— OR 三段式求值，与 AND 完全
		 * 对偶：只要有一个子句为 TRUE 即短路返回 TRUE（NULL 视为"未知"，
		 * 未知可能本应是 TRUE）；有子句为 NULL 且其余全 FALSE 则结果 NULL；
		 * 只有全部子句确知为 FALSE 时结果才为 FALSE。_STEP_FIRST 先清空
		 * anynull 再落入 _STEP；_STEP 遇 TRUE 提前 EEO_JUMP 收工；_STEP_LAST
		 * 无跳转地合并最终结果。结果初值由编译器预置为 FALSE。
		 */
		EEO_CASE(EEOP_BOOL_OR_STEP_FIRST)
		{
			*op->d.boolexpr.anynull = false;

			/*
			 * EEOP_BOOL_OR_STEP_FIRST resets anynull, otherwise it's the same
			 * as EEOP_BOOL_OR_STEP - so fall through to that.
			 */

			/* FALL THROUGH */
		}

		EEO_CASE(EEOP_BOOL_OR_STEP)
		{
			if (*op->resnull)
			{
				*op->d.boolexpr.anynull = true;
			}
			else if (DatumGetBool(*op->resvalue))
			{
				/* result is already set to TRUE, need not change it */
				/* bail out early */
				EEO_JUMP(op->d.boolexpr.jumpdone);
			}

			EEO_NEXT();
		}

		EEO_CASE(EEOP_BOOL_OR_STEP_LAST)
		{
			if (*op->resnull)
			{
				/* result is already set to NULL, need not change it */
			}
			else if (DatumGetBool(*op->resvalue))
			{
				/* result is already set to TRUE, need not change it */

				/*
				 * No point jumping to jumpdone - would be same target (as
				 * this is the last argument to the AND expression), except
				 * more expensive.
				 */
			}
			else if (*op->d.boolexpr.anynull)
			{
				*op->resvalue = (Datum) 0;
				*op->resnull = true;
			}
			else
			{
				/* result is already set to FALSE, need not change it */
			}

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_BOOL_NOT_STEP —— NOT 取反：布尔取反对 NULL 也安全
		 * （NULL 取反仍是 NULL，符合 SQL 语义），因此无视 resnull 直接
		 * 翻转 Datum 中的布尔位。 */
		EEO_CASE(EEOP_BOOL_NOT_STEP)
		{
			/*
			 * Evaluation of 'not' is simple... if expr is false, then return
			 * 'true' and vice versa.  It's safe to do this even on a
			 * nominally null value, so we ignore resnull; that means that
			 * NULL in produces NULL out, which is what we want.
			 */
			*op->resvalue = BoolGetDatum(!DatumGetBool(*op->resvalue));

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_QUAL —— 供 ExecQual() 使用的简化版 AND 步：子句
		 * 为 FALSE 或 NULL 都视为不合格，直接置 FALSE 跳到 jumpdone；
		 * 全 TRUE 则保留结果（末位子句时 TRUE 即最终答案）。 */
		EEO_CASE(EEOP_QUAL)
		{
			/* simplified version of BOOL_AND_STEP for use by ExecQual() */

			/* If argument (also result) is false or null ... */
			if (*op->resnull ||
				!DatumGetBool(*op->resvalue))
			{
				/* ... bail out early, returning FALSE */
				*op->resnull = false;
				*op->resvalue = BoolGetDatum(false);
				EEO_JUMP(op->d.qualexpr.jumpdone);
			}

			/*
			 * Otherwise, leave the TRUE value in place, in case this is the
			 * last qual.  Then, TRUE is the correct answer.
			 */

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_JUMP / _IF_NULL / _IF_NOT_NULL / _IF_NOT_TRUE ——
		 * 无条件/条件跳转族，是解释器的控制流指令：AND/OR 短路、
		 * CASE 分支、NULLIF 等全部依赖它们跳到编译期算好的 step 编号。
		 * 条件跳转以当前结果寄存器的 NULL 位/布尔值决定是否转移。 */
		EEO_CASE(EEOP_JUMP)
		{
			/* Unconditionally jump to target step */
			EEO_JUMP(op->d.jump.jumpdone);
		}

		EEO_CASE(EEOP_JUMP_IF_NULL)
		{
			/* Transfer control if current result is null */
			if (*op->resnull)
				EEO_JUMP(op->d.jump.jumpdone);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_JUMP_IF_NOT_NULL)
		{
			/* Transfer control if current result is non-null */
			if (!*op->resnull)
				EEO_JUMP(op->d.jump.jumpdone);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_JUMP_IF_NOT_TRUE)
		{
			/* Transfer control if current result is null or false */
			if (*op->resnull || !DatumGetBool(*op->resvalue))
				EEO_JUMP(op->d.jump.jumpdone);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_NULLTEST_ISNULL / _ISNOTNULL —— 标量 IS [NOT] NULL：
		 * 把结果寄存器的 NULL 位直接转换为布尔结果（IS NULL = resnull 本身；
		 * IS NOT NULL = 取反），再清空 NULL 位。
		 * EEOP_NULLTEST_ROWISNULL / _ROWISNOTNULL —— 行值 IS [NOT] NULL：
		 * 需按行类型逐字段检查，委托 ExecEvalRowNull/ExecEvalRowNotNull。 */
		EEO_CASE(EEOP_NULLTEST_ISNULL)
		{
			*op->resvalue = BoolGetDatum(*op->resnull);
			*op->resnull = false;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_NULLTEST_ISNOTNULL)
		{
			*op->resvalue = BoolGetDatum(!*op->resnull);
			*op->resnull = false;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_NULLTEST_ROWISNULL)
		{
			/* out of line implementation: too large */
			ExecEvalRowNull(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_NULLTEST_ROWISNOTNULL)
		{
			/* out of line implementation: too large */
			ExecEvalRowNotNull(state, op, econtext);

			EEO_NEXT();
		}

		/* BooleanTest implementations for all booltesttypes */

		/* 【中文注释】EEOP_BOOLTEST_* —— BooleanTest 四种形态（IS TRUE /
		 * IS NOT TRUE / IS FALSE / IS NOT FALSE）。SQL 语义：NULL 与
		 * TRUE/FALSE 比较结果见"未知"处理——IS TRUE 对 NULL 为 FALSE，
		 * IS NOT TRUE 对 NULL 为 TRUE，非 NULL 时等价于布尔取反/原样。 */
		EEO_CASE(EEOP_BOOLTEST_IS_TRUE)
		{
			if (*op->resnull)
			{
				*op->resvalue = BoolGetDatum(false);
				*op->resnull = false;
			}
			/* else, input value is the correct output as well */

			EEO_NEXT();
		}

		EEO_CASE(EEOP_BOOLTEST_IS_NOT_TRUE)
		{
			if (*op->resnull)
			{
				*op->resvalue = BoolGetDatum(true);
				*op->resnull = false;
			}
			else
				*op->resvalue = BoolGetDatum(!DatumGetBool(*op->resvalue));

			EEO_NEXT();
		}

		EEO_CASE(EEOP_BOOLTEST_IS_FALSE)
		{
			if (*op->resnull)
			{
				*op->resvalue = BoolGetDatum(false);
				*op->resnull = false;
			}
			else
				*op->resvalue = BoolGetDatum(!DatumGetBool(*op->resvalue));

			EEO_NEXT();
		}

		EEO_CASE(EEOP_BOOLTEST_IS_NOT_FALSE)
		{
			if (*op->resnull)
			{
				*op->resvalue = BoolGetDatum(true);
				*op->resnull = false;
			}
			/* else, input value is the correct output as well */

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_PARAM_EXEC —— 内部执行参数（PARAM_EXEC，如子计划
		 * 结果、InitPlan 结果）：按编号取 econtext->ecxt_param_exec_vals；
		 * 若该参数还挂着待求值的执行计划（execPlan 非空，说明是 InitPlan
		 * 首次引用），先 ExecSetParamPlan 执行计划把结果填进参数槽再取值。
		 * EEOP_PARAM_EXTERN —— 外部参数（$1 等 Prepare 参数）：从
		 * ecxt_param_list_info 取，支持 paramFetch 钩子（动态参数）；
		 * EEOP_PARAM_CALLBACK —— 允许扩展模块通过回调自定义取值；
		 * EEOP_PARAM_SET —— 反向写入：把当前结果寄存器值写回某个
		 * PARAM_EXEC 参数（用于给 InitPlan/子查询结果赋值，供本查询
		 * 后续引用）。 */
		EEO_CASE(EEOP_PARAM_EXEC)
		{
			/* out of line implementation: too large */
			ExecEvalParamExec(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_PARAM_EXTERN)
		{
			/* out of line implementation: too large */
			ExecEvalParamExtern(state, op, econtext);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_PARAM_CALLBACK)
		{
			/* allow an extension module to supply a PARAM_EXTERN value */
			op->d.cparam.paramfunc(state, op, econtext);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_PARAM_SET)
		{
			/* out of line, unlikely to matter performance-wise */
			ExecEvalParamSet(state, op, econtext);
			EEO_NEXT();
		}

		/* 【中文注释】EEOP_CASE_TESTVAL / _EXT —— 读取 CASE 基值（CASE 表达式
		 * 与域检查共用的 CaseTestExpr 机制的结果）：内联形态从编译期固定的
		 * 指针读（caseValue 槽在 econtext 中由外层设置），_EXT 形态从
		 * econtext->caseValue_datum/isNull 读。基值由 `stmt`（WHEN 判定前）
		 * 预先求值，供 WHEN 相等比较与 THEN 结果共用，避免重复求值。 */
		EEO_CASE(EEOP_CASE_TESTVAL)
		{
			*op->resvalue = *op->d.casetest.value;
			*op->resnull = *op->d.casetest.isnull;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_CASE_TESTVAL_EXT)
		{
			*op->resvalue = econtext->caseValue_datum;
			*op->resnull = econtext->caseValue_isNull;

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_MAKE_READONLY —— 把可能被多次读取的 varlena 值强制
		 * 转只读：展开对象若处于可写状态，后续任何读者都可能就地修改它，
		 * 因此这里统一 MakeExpandedObjectReadOnlyInternal 收敛为只读快照，
		 * 保证多路复用安全。 */
		EEO_CASE(EEOP_MAKE_READONLY)
		{
			/*
			 * Force a varlena value that might be read multiple times to R/O
			 */
			if (!*op->d.make_readonly.isnull)
				*op->resvalue =
					MakeExpandedObjectReadOnlyInternal(*op->d.make_readonly.value);
			*op->resnull = *op->d.make_readonly.isnull;

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_IOCOERCE —— CoerceViaIO（通过类型的 I/O 函数做
		 * 隐式/显式转换，如 text <-> 其它类型）内联实现，热路径；NULL
		 * 不调用输出函数。EEOP_IOCOERCE_SAFE 为软错误版本（错误保存到
		 * ErrorSaveContext 而非直接报错，供 JSON 等需要捕获错误的场景），
		 * 委托 ExecEvalCoerceViaIOSafe。修改内联版时需同步改 SAFE 版。 */
		EEO_CASE(EEOP_IOCOERCE)
		{
			/*
			 * Evaluate a CoerceViaIO node.  This can be quite a hot path, so
			 * inline as much work as possible.  The source value is in our
			 * result variable.
			 *
			 * Also look at ExecEvalCoerceViaIOSafe() if you change anything
			 * here.
			 */
			char	   *str;

			/* call output function (similar to OutputFunctionCall) */
			if (*op->resnull)
			{
				/* output functions are not called on nulls */
				str = NULL;
			}
			else
			{
				FunctionCallInfo fcinfo_out;

				fcinfo_out = op->d.iocoerce.fcinfo_data_out;
				fcinfo_out->args[0].value = *op->resvalue;
				fcinfo_out->args[0].isnull = false;

				fcinfo_out->isnull = false;
				str = DatumGetCString(FunctionCallInvoke(fcinfo_out));

				/* OutputFunctionCall assumes result isn't null */
				Assert(!fcinfo_out->isnull);
			}

			/* call input function (similar to InputFunctionCall) */
			if (!op->d.iocoerce.finfo_in->fn_strict || str != NULL)
			{
				FunctionCallInfo fcinfo_in;
				Datum		d;

				fcinfo_in = op->d.iocoerce.fcinfo_data_in;
				fcinfo_in->args[0].value = PointerGetDatum(str);
				fcinfo_in->args[0].isnull = *op->resnull;
				/* second and third arguments are already set up */

				fcinfo_in->isnull = false;
				d = FunctionCallInvoke(fcinfo_in);
				*op->resvalue = d;

				/* Should get null result if and only if str is NULL */
				if (str == NULL)
				{
					Assert(*op->resnull);
					Assert(fcinfo_in->isnull);
				}
				else
				{
					Assert(!*op->resnull);
					Assert(!fcinfo_in->isnull);
				}
			}

			EEO_NEXT();
		}

		EEO_CASE(EEOP_IOCOERCE_SAFE)
		{
			ExecEvalCoerceViaIOSafe(state, op);
			EEO_NEXT();
		}

		/* 【中文注释】EEOP_DISTINCT —— a IS DISTINCT FROM b：
		 * 先判 NULL（两参都 NULL → FALSE；仅一参 NULL → TRUE），两参都
		 * 非 NULL 才调用类型标准相等函数，结果取反。NULL 语义与普通 =
		 * 不同，因此不能复用 EEOP_FUNCEXPR。EEOP_NOT_DISTINCT 为取反版。 */
		EEO_CASE(EEOP_DISTINCT)
		{
			/*
			 * IS DISTINCT FROM must evaluate arguments (already done into
			 * fcinfo->args) to determine whether they are NULL; if either is
			 * NULL then the result is determined.  If neither is NULL, then
			 * proceed to evaluate the comparison function, which is just the
			 * type's standard equality operator.  We need not care whether
			 * that function is strict.  Because the handling of nulls is
			 * different, we can't just reuse EEOP_FUNCEXPR.
			 */
			FunctionCallInfo fcinfo = op->d.func.fcinfo_data;

			/* check function arguments for NULLness */
			if (fcinfo->args[0].isnull && fcinfo->args[1].isnull)
			{
				/* Both NULL? Then is not distinct... */
				*op->resvalue = BoolGetDatum(false);
				*op->resnull = false;
			}
			else if (fcinfo->args[0].isnull || fcinfo->args[1].isnull)
			{
				/* Only one is NULL? Then is distinct... */
				*op->resvalue = BoolGetDatum(true);
				*op->resnull = false;
			}
			else
			{
				/* Neither null, so apply the equality function */
				Datum		eqresult;

				fcinfo->isnull = false;
				eqresult = op->d.func.fn_addr(fcinfo);
				/* Must invert result of "="; safe to do even if null */
				*op->resvalue = BoolGetDatum(!DatumGetBool(eqresult));
				*op->resnull = fcinfo->isnull;
			}

			EEO_NEXT();
		}

		/* 同 EEOP_DISTINCT 的中文注释，这里只是结果取反（NOT DISTINCT FROM） */
		EEO_CASE(EEOP_NOT_DISTINCT)
		{
			FunctionCallInfo fcinfo = op->d.func.fcinfo_data;

			if (fcinfo->args[0].isnull && fcinfo->args[1].isnull)
			{
				*op->resvalue = BoolGetDatum(true);
				*op->resnull = false;
			}
			else if (fcinfo->args[0].isnull || fcinfo->args[1].isnull)
			{
				*op->resvalue = BoolGetDatum(false);
				*op->resnull = false;
			}
			else
			{
				Datum		eqresult;

				fcinfo->isnull = false;
				eqresult = op->d.func.fn_addr(fcinfo);
				*op->resvalue = eqresult;
				*op->resnull = fcinfo->isnull;
			}

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_NULLIF —— NULLIF(a, b)：两参都非 NULL 且相等（相等
		 * 函数返回真）时结果为 NULL，否则返回第一个参数。注意相等比较前
		 * 若 a 是 varlena，要先把 a 置为只读指针（MakeExpandedObjectReadOnly）
		 * ——避免比较函数就地修改对象；而最终若返回 a 时仍用原始指针
		 * （save_arg0），保持可写状态。 */
		EEO_CASE(EEOP_NULLIF)
		{
			/*
			 * The arguments are already evaluated into fcinfo->args.
			 */
			FunctionCallInfo fcinfo = op->d.func.fcinfo_data;
			Datum		save_arg0 = fcinfo->args[0].value;

			/* if either argument is NULL they can't be equal */
			if (!fcinfo->args[0].isnull && !fcinfo->args[1].isnull)
			{
				Datum		result;

				/*
				 * If first argument is of varlena type, it might be an
				 * expanded datum.  We need to ensure that the value passed to
				 * the comparison function is a read-only pointer.  However,
				 * if we end by returning the first argument, that will be the
				 * original read-write pointer if it was read-write.
				 */
				if (op->d.func.make_ro)
					fcinfo->args[0].value =
						MakeExpandedObjectReadOnlyInternal(save_arg0);

				fcinfo->isnull = false;
				result = op->d.func.fn_addr(fcinfo);

				/* if the arguments are equal return null */
				if (!fcinfo->isnull && DatumGetBool(result))
				{
					*op->resvalue = (Datum) 0;
					*op->resnull = true;

					EEO_NEXT();
				}
			}

			/* Arguments aren't equal, so return the first one */
			*op->resvalue = save_arg0;
			*op->resnull = fcinfo->args[0].isnull;

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_SQLVALUEFUNCTION —— CURRENT_DATE/CURRENT_TIME/
		 * CURRENT_USER/CURRENT_SCHEMA 等 SQL 值函数，委托
		 * ExecEvalSQLValueFunction。
		 * EEOP_CURRENTOFEXPR —— WHERE CURRENT OF（游标定位），正常计划
		 * 应已被规划器转成 TidScan 等，执行到这里说明表类型不支持，报错。
		 * EEOP_NEXTVALUEEXPR —— 序列 nextval：触发序列推进，结果按
		 * 序列类型转换后返回。 */
		EEO_CASE(EEOP_SQLVALUEFUNCTION)
		{
			/*
			 * Doesn't seem worthwhile to have an inline implementation
			 * efficiency-wise.
			 */
			ExecEvalSQLValueFunction(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_CURRENTOFEXPR)
		{
			/* error invocation uses space, and shouldn't ever occur */
			ExecEvalCurrentOfExpr(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_NEXTVALUEEXPR)
		{
			/*
			 * Doesn't seem worthwhile to have an inline implementation
			 * efficiency-wise.
			 */
			ExecEvalNextValueExpr(state, op);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_RETURNINGEXPR —— 触发器 RETURNING 支持：若 OLD/NEW
		 * 行不存在（state->flags 里相应位被置位），跳过其后真正求值的
		 * step，直接返回 NULL；行存在则照常执行。 */
		EEO_CASE(EEOP_RETURNINGEXPR)
		{
			/*
			 * The next op actually evaluates the expression.  If the OLD/NEW
			 * row doesn't exist, skip that and return NULL.
			 */
			if (state->flags & op->d.returningexpr.nullflag)
			{
				*op->resvalue = (Datum) 0;
				*op->resnull = true;

				EEO_JUMP(op->d.returningexpr.jumpdone);
			}

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_ARRAYEXPR —— ARRAY[] 构造：元素已在编译期预分配的
		 * elemvalues/elemnulls 数组中求值，委托 ExecEvalArrayExpr 组装为
		 * ArrayType（含多维合并、NULL 位图、维度校验）。
		 * EEOP_ARRAYCOERCE —— ArrayCoerceExpr：对数组逐元素施加转换
		 * （元素类型不同时 array_map；二进制兼容时只改头部 elemtype）。
		 * EEOP_ROW —— ROW(...) 行构造：把已求值字段用 heap_form_tuple
		 * 组装成复合类型 Datum。 */
		EEO_CASE(EEOP_ARRAYEXPR)
		{
			/* too complex for an inline implementation */
			ExecEvalArrayExpr(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ARRAYCOERCE)
		{
			/* too complex for an inline implementation */
			ExecEvalArrayCoerce(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ROW)
		{
			/* too complex for an inline implementation */
			ExecEvalRow(state, op);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_ROWCOMPARE_STEP —— 行比较（(a,b) < (c,d)）的逐列
		 * 步：对当前列对调用比较函数，返回 int32 比较值；严格函数遇
		 * NULL 或函数结果 NULL 直接跳到 jumpnull（NULL 语义：行比较任
		 * 一列 NULL 结果即 NULL）；比较值非 0 说明已分出大小，跳到
		 * jumpdone 收尾；相等则 EEO_NEXT 比较下一列。
		 * EEOP_ROWCOMPARE_FINAL —— 末列之后把最终 int32 比较值按操作符
		 * （<、<=、>=、>）换算成布尔结果（EQ/NE 不会出现在这里）。 */
		EEO_CASE(EEOP_ROWCOMPARE_STEP)
		{
			FunctionCallInfo fcinfo = op->d.rowcompare_step.fcinfo_data;
			Datum		d;

			/* force NULL result if strict fn and NULL input */
			if (op->d.rowcompare_step.finfo->fn_strict &&
				(fcinfo->args[0].isnull || fcinfo->args[1].isnull))
			{
				*op->resnull = true;
				EEO_JUMP(op->d.rowcompare_step.jumpnull);
			}

			/* Apply comparison function */
			fcinfo->isnull = false;
			d = op->d.rowcompare_step.fn_addr(fcinfo);
			*op->resvalue = d;

			/* force NULL result if NULL function result */
			if (fcinfo->isnull)
			{
				*op->resnull = true;
				EEO_JUMP(op->d.rowcompare_step.jumpnull);
			}
			*op->resnull = false;

			/* If unequal, no need to compare remaining columns */
			if (DatumGetInt32(*op->resvalue) != 0)
			{
				EEO_JUMP(op->d.rowcompare_step.jumpdone);
			}

			EEO_NEXT();
		}

		EEO_CASE(EEOP_ROWCOMPARE_FINAL)
		{
			int32		cmpresult = DatumGetInt32(*op->resvalue);
			CompareType cmptype = op->d.rowcompare_final.cmptype;

			*op->resnull = false;
			switch (cmptype)
			{
					/* EQ and NE cases aren't allowed here */
				case COMPARE_LT:
					*op->resvalue = BoolGetDatum(cmpresult < 0);
					break;
				case COMPARE_LE:
					*op->resvalue = BoolGetDatum(cmpresult <= 0);
					break;
				case COMPARE_GE:
					*op->resvalue = BoolGetDatum(cmpresult >= 0);
					break;
				case COMPARE_GT:
					*op->resvalue = BoolGetDatum(cmpresult > 0);
					break;
				default:
					Assert(false);
					break;
			}

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_MINMAX —— GREATEST/LEAST（注意不是聚合 MIN/MAX）：
		 * 跳过 NULL 输入，用比较函数两两挑选极值。EEOP_FIELDSELECT ——
		 * 复合类型取字段（行表达式 (t).col）。EEOP_FIELDSTORE_DEFORM /
		 * _FORM —— FieldStore 两步式：先把源行变形到 values/nulls 数组，
		 * 各字段新值求值覆盖其中若干元素后，_FORM 用 heap_form_tuple 组
		 * 装新行（如 UPDATE 复合列赋值）。 */
		EEO_CASE(EEOP_MINMAX)
		{
			/* too complex for an inline implementation */
			ExecEvalMinMax(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_FIELDSELECT)
		{
			/* too complex for an inline implementation */
			ExecEvalFieldSelect(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_FIELDSTORE_DEFORM)
		{
			/* too complex for an inline implementation */
			ExecEvalFieldStoreDeForm(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_FIELDSTORE_FORM)
		{
			/* too complex for an inline implementation */
			ExecEvalFieldStoreForm(state, op, econtext);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_SBSREF_* —— 下标引用族（数组/JSON/域的子下标赋值
		 * 与取值，SubscriptingRef）：_SUBSCRIPTS 先求值并校验所有下标
		 * （下标为 NULL 时整个 SubscriptingRef 短路为 NULL）；_OLD 取
		 * 被替换的旧值（赋值场景构造"原值+改动"需要）、_ASSIGN 执行
		 * 赋值、_FETCH 执行取值。具体行为由类型相关的 subscriptfunc 回调
		 * （array_subscript_exec 等）实现。 */
		EEO_CASE(EEOP_SBSREF_SUBSCRIPTS)
		{
			/* Precheck SubscriptingRef subscript(s) */
			if (op->d.sbsref_subscript.subscriptfunc(state, op, econtext))
			{
				EEO_NEXT();
			}
			else
			{
				/* Subscript is null, short-circuit SubscriptingRef to NULL */
				EEO_JUMP(op->d.sbsref_subscript.jumpdone);
			}
		}

		EEO_CASE(EEOP_SBSREF_OLD)
			EEO_CASE(EEOP_SBSREF_ASSIGN)
			EEO_CASE(EEOP_SBSREF_FETCH)
		{
			/* Perform a SubscriptingRef fetch or assignment */
			op->d.sbsref.subscriptfunc(state, op, econtext);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_CONVERT_ROWTYPE —— 行类型转换（ConvertRowtypeExpr，
		 * 如把父表行转成子表行、显式 ::type 行转换）：按属性名重排字段并
		 * 重打结果类型标记；二进制兼容时仅改复合头类型 OID。
		 * EEOP_SCALARARRAYOP —— x op ANY/ALL (数组)：逐个数组元素应用
		 * 操作符，ANY 用 OR 合并、ALL 用 AND 合并，可短路。
		 * EEOP_HASHED_SCALARARRAYOP —— 常数数组的 x = ANY(...) 优化版：
		 * 首次求值时把数组元素建哈希表，后续行 O(1) 查表。 */
		EEO_CASE(EEOP_CONVERT_ROWTYPE)
		{
			/* too complex for an inline implementation */
			ExecEvalConvertRowtype(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_SCALARARRAYOP)
		{
			/* too complex for an inline implementation */
			ExecEvalScalarArrayOp(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_HASHED_SCALARARRAYOP)
		{
			/* too complex for an inline implementation */
			ExecEvalHashedScalarArrayOp(state, op, econtext);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_DOMAIN_TESTVAL / _EXT —— 读取域检查的基值（与
		 * CASE_TESTVAL 同机制，见其注释）：domainValue 在 econtext 中。
		 * EEOP_DOMAIN_NOTNULL —— 域 NOT NULL 约束检查，违反则报错
		 * （errsave 支持软错误）。
		 * EEOP_DOMAIN_CHECK —— 域 CHECK 约束表达式求值后校验，违反
		 * 则报错；返回 FALSE 或 NULL 都不通过。 */
		EEO_CASE(EEOP_DOMAIN_TESTVAL)
		{
			*op->resvalue = *op->d.casetest.value;
			*op->resnull = *op->d.casetest.isnull;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_DOMAIN_TESTVAL_EXT)
		{
			*op->resvalue = econtext->domainValue_datum;
			*op->resnull = econtext->domainValue_isNull;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_DOMAIN_NOTNULL)
		{
			/* too complex for an inline implementation */
			ExecEvalConstraintNotNull(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_DOMAIN_CHECK)
		{
			/* too complex for an inline implementation */
			ExecEvalConstraintCheck(state, op);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_HASHDATUM_* —— 哈希元组键合成族（Hash 连接/聚合
		 * 键值哈希）：用类型哈希函数把各键列依次散列并循环旋转异或合并
		 * （pg_rotate_left32 保证列顺序敏感、位数充分混合）。
		 * - _SET_INITVAL：装入种子初值（JOIN 优化后的专用步）；
		 * - _FIRST：第一列——NULL 输入以 0 参与合并（_FIRST_STRICT 则
		 *   遇 NULL 直接短路，整个键哈希结果为 NULL，供严格键使用）；
		 * - _NEXT32(_STRICT)：后续列合并——NULL 列不改变已合并值
		 *   （等价于 SQL 语义里 NULL 键与任何 NULL 键相等/分组同组）；
		 * _STRICT 变体遇 NULL 直接使整键为 NULL。 */
		EEO_CASE(EEOP_HASHDATUM_SET_INITVAL)
		{
			*op->resvalue = op->d.hashdatum_initvalue.init_value;
			*op->resnull = false;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_HASHDATUM_FIRST)
		{
			FunctionCallInfo fcinfo = op->d.hashdatum.fcinfo_data;

			/*
			 * Save the Datum on non-null inputs, otherwise store 0 so that
			 * subsequent NEXT32 operations combine with an initialized value.
			 */
			if (!fcinfo->args[0].isnull)
				*op->resvalue = op->d.hashdatum.fn_addr(fcinfo);
			else
				*op->resvalue = (Datum) 0;

			*op->resnull = false;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_HASHDATUM_FIRST_STRICT)
		{
			FunctionCallInfo fcinfo = op->d.hashdatum.fcinfo_data;

			if (fcinfo->args[0].isnull)
			{
				/*
				 * With strict we have the expression return NULL instead of
				 * ignoring NULL input values.  We've nothing more to do after
				 * finding a NULL.
				 */
				state->resnull = true;
				state->resvalue = (Datum) 0;
				EEO_JUMP(op->d.hashdatum.jumpdone);
			}

			/* execute the hash function and save the resulting value */
			*op->resvalue = op->d.hashdatum.fn_addr(fcinfo);
			*op->resnull = false;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_HASHDATUM_NEXT32)
		{
			FunctionCallInfo fcinfo = op->d.hashdatum.fcinfo_data;
			uint32		existinghash;

			existinghash = DatumGetUInt32(op->d.hashdatum.iresult->value);
			/* combine successive hash values by rotating */
			existinghash = pg_rotate_left32(existinghash, 1);

			/* leave the hash value alone on NULL inputs */
			if (!fcinfo->args[0].isnull)
			{
				uint32		hashvalue;

				/* execute hash func and combine with previous hash value */
				hashvalue = DatumGetUInt32(op->d.hashdatum.fn_addr(fcinfo));
				existinghash = existinghash ^ hashvalue;
			}

			*op->resvalue = UInt32GetDatum(existinghash);
			*op->resnull = false;

			EEO_NEXT();
		}

		EEO_CASE(EEOP_HASHDATUM_NEXT32_STRICT)
		{
			FunctionCallInfo fcinfo = op->d.hashdatum.fcinfo_data;

			if (fcinfo->args[0].isnull)
			{
				/*
				 * With strict we have the expression return NULL instead of
				 * ignoring NULL input values.  We've nothing more to do after
				 * finding a NULL.
				 */
				state->resnull = true;
				state->resvalue = (Datum) 0;
				EEO_JUMP(op->d.hashdatum.jumpdone);
			}
			else
			{
				uint32		existinghash;
				uint32		hashvalue;

				existinghash = DatumGetUInt32(op->d.hashdatum.iresult->value);
				/* combine successive hash values by rotating */
				existinghash = pg_rotate_left32(existinghash, 1);

				/* execute hash func and combine with previous hash value */
				hashvalue = DatumGetUInt32(op->d.hashdatum.fn_addr(fcinfo));
				*op->resvalue = UInt32GetDatum(existinghash ^ hashvalue);
				*op->resnull = false;
			}

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_XMLEXPR —— XmlExpr（xmlconcat/forest/element/
		 * parse/pi/root/serialize/IS DOCUMENT）委托 ExecEvalXmlExpr。
		 * EEOP_JSON_CONSTRUCTOR —— SQL/JSON 构造器（JSON_ARRAY/OBJECT/
		 * JSON 标量/JSON(...) 解析），委托 ExecEvalJsonConstructor。
		 * EEOP_IS_JSON —— IS JSON 谓词。
		 * EEOP_JSONEXPR_PATH —— 对文档执行 jsonpath 并依据 ON EMPTY /
		 * ON ERROR 决定后续跳转，委托 ExecEvalJsonExprPath（返回值即
		 * 下一个 step 编号，因此用 EEO_JUMP 而非 EEO_NEXT）。
		 * EEOP_JSONEXPR_COERCION / _FINISH —— 结果向 RETURNING 类型
		 * 转换（软错误模式）与事后错误处理两步。 */
		EEO_CASE(EEOP_XMLEXPR)
		{
			/* too complex for an inline implementation */
			ExecEvalXmlExpr(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_JSON_CONSTRUCTOR)
		{
			/* too complex for an inline implementation */
			ExecEvalJsonConstructor(state, op, econtext);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_IS_JSON)
		{
			/* too complex for an inline implementation */
			ExecEvalJsonIsPredicate(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_JSONEXPR_PATH)
		{
			/* too complex for an inline implementation */
			EEO_JUMP(ExecEvalJsonExprPath(state, op, econtext));
		}

		EEO_CASE(EEOP_JSONEXPR_COERCION)
		{
			/* too complex for an inline implementation */
			ExecEvalJsonCoercion(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_JSONEXPR_COERCION_FINISH)
		{
			/* too complex for an inline implementation */
			ExecEvalJsonCoercionFinish(state, op);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_AGGREF —— 聚合引用：结果早由聚合节点按组算好并
		 * 放入 econtext->ecxt_aggvalues/ecxt_aggnulls，这里按 aggno 直接
		 * 取数（零计算）。
		 * EEOP_GROUPING_FUNC —— GROUPING(...) 分组位掩码（计算当前行
		 * 属于哪个分组集合，用于区分聚合的行被折叠与否）。
		 * EEOP_WINDOW_FUNC —— 窗口函数引用，同 AGGREF 按 wfuncno 取
		 * 预计算结果。 */
		EEO_CASE(EEOP_AGGREF)
		{
			/*
			 * Returns a Datum whose value is the precomputed aggregate value
			 * found in the given expression context.
			 */
			int			aggno = op->d.aggref.aggno;

			Assert(econtext->ecxt_aggvalues != NULL);

			*op->resvalue = econtext->ecxt_aggvalues[aggno];
			*op->resnull = econtext->ecxt_aggnulls[aggno];

			EEO_NEXT();
		}

		EEO_CASE(EEOP_GROUPING_FUNC)
		{
			/* too complex/uncommon for an inline implementation */
			ExecEvalGroupingFunc(state, op);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_WINDOW_FUNC)
		{
			/*
			 * Like Aggref, just return a precomputed value from the econtext.
			 */
			WindowFuncExprState *wfunc = op->d.window_func.wfstate;

			Assert(econtext->ecxt_aggvalues != NULL);

			*op->resvalue = econtext->ecxt_aggvalues[wfunc->wfuncno];
			*op->resnull = econtext->ecxt_aggnulls[wfunc->wfuncno];

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_MERGE_SUPPORT_FUNC —— MERGE 支持函数：返回当前
		 * 执行的 MERGE 动作名（'INSERT'/'UPDATE'/'DELETE' 文本），供
		 * RETURNING 列表使用。EEOP_SUBPLAN —— 子计划（子查询）执行：
		 * 委托 ExecSubPlan（内含 InitPlan/相关子查询的缓存与参数回填）。 */
		EEO_CASE(EEOP_MERGE_SUPPORT_FUNC)
		{
			/* too complex/uncommon for an inline implementation */
			ExecEvalMergeSupportFunc(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_SUBPLAN)
		{
			/* too complex for an inline implementation */
			ExecEvalSubPlan(state, op, econtext);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_AGG_STRICT_DESERIALIZE —— 串行聚合的严格反序列化
		 * 步骤：序列化状态（serialtype datum）为 NULL 时严格反序列化函数
		 * 不应被调用，直接跳到 jumpnull。
		 * EEOP_AGG_DESERIALIZE —— 调用反序列化函数把串行聚合状态还原为
		 * 内存内 transtype 状态；在每输入元组的临时内存上下文中执行，
		 * 结果自动随元组释放。 */
		EEO_CASE(EEOP_AGG_STRICT_DESERIALIZE)
		{
			/* Don't call a strict deserialization function with NULL input */
			if (op->d.agg_deserialize.fcinfo_data->args[0].isnull)
				EEO_JUMP(op->d.agg_deserialize.jumpnull);

			/* fallthrough */
		}

		/* evaluate aggregate deserialization function (non-strict portion) */
		EEO_CASE(EEOP_AGG_DESERIALIZE)
		{
			FunctionCallInfo fcinfo = op->d.agg_deserialize.fcinfo_data;
			AggState   *aggstate = castNode(AggState, state->parent);
			MemoryContext oldContext;

			/*
			 * We run the deserialization functions in per-input-tuple memory
			 * context.
			 */
			oldContext = MemoryContextSwitchTo(aggstate->tmpcontext->ecxt_per_tuple_memory);
			fcinfo->isnull = false;
			*op->resvalue = FunctionCallInvoke(fcinfo);
			*op->resnull = fcinfo->isnull;
			MemoryContextSwitchTo(oldContext);

			EEO_NEXT();
		}

		/*
		 * Check that a strict aggregate transition / combination function's
		 * input is not NULL.
		 */

		/* 【中文注释】EEOP_AGG_STRICT_INPUT_CHECK_* —— 严格转移/组合函数的
		 * 输入判空步骤：任一输入为 NULL（_ARGS 查 fcinfo 参数数组、
		 * _NULLS 查独立 nulls 数组、_ARGS_1 是单参数特化）即跳到
		 * jumpnull，直接按"严格函数遇 NULL 不调用"处理，避免调用。 */
		EEO_CASE(EEOP_AGG_STRICT_INPUT_CHECK_ARGS)
		{
			NullableDatum *args = op->d.agg_strict_input_check.args;
			int			nargs = op->d.agg_strict_input_check.nargs;

			Assert(nargs > 1);

			for (int argno = 0; argno < nargs; argno++)
			{
				if (args[argno].isnull)
					EEO_JUMP(op->d.agg_strict_input_check.jumpnull);
			}
			EEO_NEXT();
		}

		/* 单输入特化：只查一个参数是否为 NULL */
		EEO_CASE(EEOP_AGG_STRICT_INPUT_CHECK_ARGS_1)
		{
			NullableDatum *args = op->d.agg_strict_input_check.args;
			PG_USED_FOR_ASSERTS_ONLY int nargs = op->d.agg_strict_input_check.nargs;

			Assert(nargs == 1);

			if (args[0].isnull)
				EEO_JUMP(op->d.agg_strict_input_check.jumpnull);
			EEO_NEXT();
		}

		EEO_CASE(EEOP_AGG_STRICT_INPUT_CHECK_NULLS)
		{
			bool	   *nulls = op->d.agg_strict_input_check.nulls;
			int			nargs = op->d.agg_strict_input_check.nargs;

			for (int argno = 0; argno < nargs; argno++)
			{
				if (nulls[argno])
					EEO_JUMP(op->d.agg_strict_input_check.jumpnull);
			}
			EEO_NEXT();
		}

		/* 【中文注释】EEOP_AGG_PLAIN_PERGROUP_NULLCHECK —— 检查本行所属分组
		 * 的 per-group 状态指针是否已分配（第一个输入行之前为 NULL）：
		 * 未分配则跳走，由聚合节点负责初始化该分组的状态数组。 */
		EEO_CASE(EEOP_AGG_PLAIN_PERGROUP_NULLCHECK)
		{
			AggState   *aggstate = castNode(AggState, state->parent);
			AggStatePerGroup pergroup_allaggs =
				aggstate->all_pergroups[op->d.agg_plain_pergroup_nullcheck.setoff];

			if (pergroup_allaggs == NULL)
				EEO_JUMP(op->d.agg_plain_pergroup_nullcheck.jumpnull);

			EEO_NEXT();
		}

		/*
		 * 【中文注释】EEOP_AGG_PLAIN_TRANS_* —— 普通（无 ORDER BY）聚合
		 * 转移函数调用族。按三个正交维度拆成 6 个 opcode 以消除运行时
		 * 分支（聚合是每行必走的超热路径）：
		 *   维度1 转移值类型：byval（int8 等，值传递）/ byref（text 等，
		 *   引用传递，需拷入 aggcontext 管理生命周期）；
		 *   维度2 是否需要用输入值初始化首行转移值（INIT_：组内首行
		 *   noTransValue 为真时执行 ExecAggInitGroup 用输入值播种）；
		 *   维度3 转移函数是否严格（STRICT：输入 NULL 则保持原转移值，
		 *   不调用函数）。
		 * 每步逻辑：非严格 INIT 首行播种；随后若非 NULL 则调用
		 * ExecAggPlainTransByVal/ByRef 执行转移；严格时 NULL 输入自然
		 * 跳过调用。
		 */
		EEO_CASE(EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYVAL)
		{
			AggState   *aggstate = castNode(AggState, state->parent);
			AggStatePerTrans pertrans = op->d.agg_trans.pertrans;
			AggStatePerGroup pergroup =
				&aggstate->all_pergroups[op->d.agg_trans.setoff][op->d.agg_trans.transno];

			Assert(pertrans->transtypeByVal);

			if (pergroup->noTransValue)
			{
				/* If transValue has not yet been initialized, do so now. */
				ExecAggInitGroup(aggstate, pertrans, pergroup,
								 op->d.agg_trans.aggcontext);
				/* copied trans value from input, done this round */
			}
			else if (likely(!pergroup->transValueIsNull))
			{
				/* invoke transition function, unless prevented by strictness */
				ExecAggPlainTransByVal(aggstate, pertrans, pergroup,
									   op->d.agg_trans.aggcontext,
									   op->d.agg_trans.setno);
			}

			EEO_NEXT();
		}

		/* 同 EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYVAL 的三维度拆分注释（byval+非 INIT+严格） */
		EEO_CASE(EEOP_AGG_PLAIN_TRANS_STRICT_BYVAL)
		{
			AggState   *aggstate = castNode(AggState, state->parent);
			AggStatePerTrans pertrans = op->d.agg_trans.pertrans;
			AggStatePerGroup pergroup =
				&aggstate->all_pergroups[op->d.agg_trans.setoff][op->d.agg_trans.transno];

			Assert(pertrans->transtypeByVal);

			if (likely(!pergroup->transValueIsNull))
				ExecAggPlainTransByVal(aggstate, pertrans, pergroup,
									   op->d.agg_trans.aggcontext,
									   op->d.agg_trans.setno);

			EEO_NEXT();
		}

		/* 同 EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYVAL 的三维度拆分注释（byval+非 INIT+非严格） */
		EEO_CASE(EEOP_AGG_PLAIN_TRANS_BYVAL)
		{
			AggState   *aggstate = castNode(AggState, state->parent);
			AggStatePerTrans pertrans = op->d.agg_trans.pertrans;
			AggStatePerGroup pergroup =
				&aggstate->all_pergroups[op->d.agg_trans.setoff][op->d.agg_trans.transno];

			Assert(pertrans->transtypeByVal);

			ExecAggPlainTransByVal(aggstate, pertrans, pergroup,
								   op->d.agg_trans.aggcontext,
								   op->d.agg_trans.setno);

			EEO_NEXT();
		}

		/* 同 EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYVAL 的三维度拆分注释（byref+INIT+严格） */
		EEO_CASE(EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYREF)
		{
			AggState   *aggstate = castNode(AggState, state->parent);
			AggStatePerTrans pertrans = op->d.agg_trans.pertrans;
			AggStatePerGroup pergroup =
				&aggstate->all_pergroups[op->d.agg_trans.setoff][op->d.agg_trans.transno];

			Assert(!pertrans->transtypeByVal);

			if (pergroup->noTransValue)
				ExecAggInitGroup(aggstate, pertrans, pergroup,
								 op->d.agg_trans.aggcontext);
			else if (likely(!pergroup->transValueIsNull))
				ExecAggPlainTransByRef(aggstate, pertrans, pergroup,
									   op->d.agg_trans.aggcontext,
									   op->d.agg_trans.setno);

			EEO_NEXT();
		}

		/* 同 EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYVAL 的三维度拆分注释（byref+非 INIT+严格） */
		EEO_CASE(EEOP_AGG_PLAIN_TRANS_STRICT_BYREF)
		{
			AggState   *aggstate = castNode(AggState, state->parent);
			AggStatePerTrans pertrans = op->d.agg_trans.pertrans;
			AggStatePerGroup pergroup =
				&aggstate->all_pergroups[op->d.agg_trans.setoff][op->d.agg_trans.transno];

			Assert(!pertrans->transtypeByVal);

			if (likely(!pergroup->transValueIsNull))
				ExecAggPlainTransByRef(aggstate, pertrans, pergroup,
									   op->d.agg_trans.aggcontext,
									   op->d.agg_trans.setno);
			EEO_NEXT();
		}

		/* 同 EEOP_AGG_PLAIN_TRANS_INIT_STRICT_BYVAL 的三维度拆分注释（byref+非 INIT+非严格） */
		EEO_CASE(EEOP_AGG_PLAIN_TRANS_BYREF)
		{
			AggState   *aggstate = castNode(AggState, state->parent);
			AggStatePerTrans pertrans = op->d.agg_trans.pertrans;
			AggStatePerGroup pergroup =
				&aggstate->all_pergroups[op->d.agg_trans.setoff][op->d.agg_trans.transno];

			Assert(!pertrans->transtypeByVal);

			ExecAggPlainTransByRef(aggstate, pertrans, pergroup,
								   op->d.agg_trans.aggcontext,
								   op->d.agg_trans.setno);

			EEO_NEXT();
		}

		/* 【中文注释】EEOP_AGG_PRESORTED_DISTINCT_SINGLE / _MULTI —— 预排序
		 * DISTINCT 聚合的去重判定：假定输入已按排序顺序到达（由查询计划
		 * 中 ORDER BY 支持），仅需与"上一个输入"比较即可去重。单列版比较
		 * 上一个 datum，多列版把输入装入 sortslot 后用 ExecQual 比较；
		 * 与上一个不同（或没有上一个）才需要调用转移函数（返回 true 走
		 * EEO_NEXT），否则跳过（EEO_JUMP 到 jumpdistinct）。 */
		EEO_CASE(EEOP_AGG_PRESORTED_DISTINCT_SINGLE)
		{
			AggStatePerTrans pertrans = op->d.agg_presorted_distinctcheck.pertrans;
			AggState   *aggstate = castNode(AggState, state->parent);

			if (ExecEvalPreOrderedDistinctSingle(aggstate, pertrans))
				EEO_NEXT();
			else
				EEO_JUMP(op->d.agg_presorted_distinctcheck.jumpdistinct);
		}

		EEO_CASE(EEOP_AGG_PRESORTED_DISTINCT_MULTI)
		{
			AggState   *aggstate = castNode(AggState, state->parent);
			AggStatePerTrans pertrans = op->d.agg_presorted_distinctcheck.pertrans;

			if (ExecEvalPreOrderedDistinctMulti(aggstate, pertrans))
				EEO_NEXT();
			else
				EEO_JUMP(op->d.agg_presorted_distinctcheck.jumpdistinct);
		}

		/* 【中文注释】EEOP_AGG_ORDERED_TRANS_DATUM —— 有序聚合（ORDER BY
		 * 内聚）的单列形态：把已求值的 datum 输入写入 tuplesort 排序
		 * 状态，聚合结束后统一在排序序上执行转移函数。
		 * EEOP_AGG_ORDERED_TRANS_TUPLE —— 多列形态：把输入行存入
		 * sortslot 后整体 tuplesort_puttupleslot。 */
		EEO_CASE(EEOP_AGG_ORDERED_TRANS_DATUM)
		{
			/* too complex for an inline implementation */
			ExecEvalAggOrderedTransDatum(state, op, econtext);

			EEO_NEXT();
		}

		/* 有序聚合多列形态：同 EEOP_AGG_ORDERED_TRANS_DATUM，但输入是整行（写入 sortslot 后排序） */
		EEO_CASE(EEOP_AGG_ORDERED_TRANS_TUPLE)
		{
			/* too complex for an inline implementation */
			ExecEvalAggOrderedTransTuple(state, op, econtext);

			EEO_NEXT();
		}

		EEO_CASE(EEOP_LAST)
		{
			/* unreachable */
			Assert(false);
			goto out_error;
		}
	}

out_error:
	pg_unreachable();
	return (Datum) 0;
}

/*
 * ============================================================================
 * 【中文注释】ExecInterpExprStillValid —— 先校验再执行的延迟接线入口
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   首次执行表达式时的过渡 evalfunc：先做"表达式与当前 schema 是否仍然
 *   兼容"的校验（计划可能是在老的 schema 下生成的、被缓存的），通过后把
 *   evalfunc 换成真正的执行函数并立即执行本次求值。声明为 extern 是因为
 *   其它执行方式（如 JIT）也要使用同样的校验机制。
 *
 * 参数：
 *   state   - ExprState（steps、evalfunc_private 等）。
 *   econtext- 求值上下文（提供输入槽，校验需要对照槽的元组描述符）。
 *   isNull  - 输出：结果是否 NULL。
 *
 * 设计思想：
 *   1. 惰性校验：如果每次执行都做全量校验会拖慢热路径，而校验又必须在
 *      "任何一次真正求值之前"完成，因此把校验挂成首次调用的回调；本次
 *      调用里先 CheckExprStillValid 全量检查，然后 state->evalfunc 原地替换
 *      为 evalfunc_private（真正的执行函数），后续调用不再有任何校验开销。
 *   2. 该校验能拦截的典型场景：计划缓存复用 + 执行期间 DDL（如 ALTER
 *      TABLE DROP COLUMN / ALTER COLUMN TYPE）导致 Var 引用的属性类型或
 *      存在性与槽描述符不符，返回清晰错误而不是内存越界/静默错值。
 *   3. 由 ExecReadyInterpretedExpr 在准备阶段把 evalfunc 置为本函数；
 *      校验完成后不可能再回头，因此本函数只被调用一次（每次执行计划）。
 * ============================================================================
 */
Datum
ExecInterpExprStillValid(ExprState *state, ExprContext *econtext, bool *isNull)
{
	/*
	 * First time through, check whether attribute matches Var.  Might not be
	 * ok anymore, due to schema changes.
	 */
	CheckExprStillValid(state, econtext);

	/* skip the check during further executions */
	state->evalfunc = (ExprStateEvalFunc) state->evalfunc_private;

	/* and actually execute */
	return state->evalfunc(state, econtext, isNull);
}

/*
 * ============================================================================
 * 【中文注释】CheckExprStillValid —— 全量校验表达式与当前 schema 的兼容性
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历 ExprState 的全部 step，对每个 EEOP_*_VAR 步检查其引用的属性：
 *   编号是否仍在槽描述符内、属性是否被 DROP、类型是否与编译期记录的
 *   vartype 一致；不一致即报错（拒绝执行过期计划）。
 *
 * 参数：
 *   state   - ExprState（含 steps 数组）。
 *   econtext- 求值上下文，提供 inner/outer/scan/old/new 五个槽用于对照。
 *
 * 设计思想：
 *   1. 一次性防线：正常流程中计划树本身已注册依赖（plan invalidation），
 *      schema 变化会导致计划失效重建；本函数是"计划被错误复用"场景的兜底
 *      防御——代价是首次执行前 O(steps) 的一次遍历，之后再不执行。
 *   2. 只检查 VAR 步（且由 ExecEvalStepOp 把直接线程化下的 opcode 反查
 *      回枚举，兼容两种派发模式）；系统列类型永不变，无需检查。
 *   3. 被 ExecInterpExprStillValid 调用；JIT 等其它求值方式也可复用。
 *   4. 逐属性的深度校验（类型/丢弃/越界）委托 CheckVarSlotCompatibility，
 *      这里只负责遍历与分派。
 * ============================================================================
 */
void
CheckExprStillValid(ExprState *state, ExprContext *econtext)
{
	TupleTableSlot *innerslot;
	TupleTableSlot *outerslot;
	TupleTableSlot *scanslot;
	TupleTableSlot *oldslot;
	TupleTableSlot *newslot;

	innerslot = econtext->ecxt_innertuple;
	outerslot = econtext->ecxt_outertuple;
	scanslot = econtext->ecxt_scantuple;
	oldslot = econtext->ecxt_oldtuple;
	newslot = econtext->ecxt_newtuple;

	for (int i = 0; i < state->steps_len; i++)
	{
		ExprEvalStep *op = &state->steps[i];

		switch (ExecEvalStepOp(state, op))
		{
			case EEOP_INNER_VAR:
				{
					int			attnum = op->d.var.attnum;

					CheckVarSlotCompatibility(innerslot, attnum + 1, op->d.var.vartype);
					break;
				}

			case EEOP_OUTER_VAR:
				{
					int			attnum = op->d.var.attnum;

					CheckVarSlotCompatibility(outerslot, attnum + 1, op->d.var.vartype);
					break;
				}

			case EEOP_SCAN_VAR:
				{
					int			attnum = op->d.var.attnum;

					CheckVarSlotCompatibility(scanslot, attnum + 1, op->d.var.vartype);
					break;
				}

			case EEOP_OLD_VAR:
				{
					int			attnum = op->d.var.attnum;

					CheckVarSlotCompatibility(oldslot, attnum + 1, op->d.var.vartype);
					break;
				}

			case EEOP_NEW_VAR:
				{
					int			attnum = op->d.var.attnum;

					CheckVarSlotCompatibility(newslot, attnum + 1, op->d.var.vartype);
					break;
				}
			default:
				break;
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】CheckVarSlotCompatibility —— 校验 Var 引用的用户列仍与槽描述符兼容
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查槽中第 attnum 个（1 基）属性能否被引用 vartype 类型的 Var 安全
 *   求值：编号越界、属性已被 DROP、类型与 Var 不符时分别报出明确错误。
 *
 * 参数：
 *   slot   - 提供列定义的元组槽（取 tts_tupleDescriptor）。
 *   attnum - 1 基属性号（系统列传 <=0，无需检查，类型永不变）。
 *   vartype- 表达式编译时记录的属性类型 OID。
 *
 * 设计思想：
 *   1. 触发场景：计划在 DDL 之前生成并缓存，执行时 schema 已变——例如
 *      ALTER TABLE DROP COLUMN 后旧计划仍在执行。正常机制下计划会因依赖
 *      失效而被重建，这里只是最后一道防线，因此只在首次执行时做一次。
 *   2. 只查 typid 不查 typmod 的原因：很多情况下槽描述符由
 *      ExecTypeFromTL() 生成，无法保证 typmod 精确（部分表达式节点不携带
 *      typmod），而恰好也没有任何关键依赖落在 typmod 上，查了反而误报。
 *   3. 虚拟生成列（attgenerated == VIRTUAL）不应出现在此处——它们没有
 *      物理存储，FETCHSOME 前的 Deform 也不会展开它们，出现即内部错误。
 *   4. 报错采用 SQLSTATE UNDEFINED_COLUMN / DATATYPE_MISMATCH，并把表类型
 *      与预期类型都打印出来，便于诊断过期计划。
 * ============================================================================
 */
static void
CheckVarSlotCompatibility(TupleTableSlot *slot, int attnum, Oid vartype)
{
	/*
	 * What we have to check for here is the possibility of an attribute
	 * having been dropped or changed in type since the plan tree was created.
	 * Ideally the plan will get invalidated and not re-used, but just in
	 * case, we keep these defenses.  Fortunately it's sufficient to check
	 * once on the first time through.
	 *
	 * Note: ideally we'd check typmod as well as typid, but that seems
	 * impractical at the moment: in many cases the tupdesc will have been
	 * generated by ExecTypeFromTL(), and that can't guarantee to generate an
	 * accurate typmod in all cases, because some expression node types don't
	 * carry typmod.  Fortunately, for precisely that reason, there should be
	 * no places with a critical dependency on the typmod of a value.
	 *
	 * System attributes don't require checking since their types never
	 * change.
	 */
	if (attnum > 0)
	{
		TupleDesc	slot_tupdesc = slot->tts_tupleDescriptor;
		Form_pg_attribute attr;

		if (attnum > slot_tupdesc->natts)	/* should never happen */
			elog(ERROR, "attribute number %d exceeds number of columns %d",
				 attnum, slot_tupdesc->natts);

		attr = TupleDescAttr(slot_tupdesc, attnum - 1);

		/* Internal error: somebody forgot to expand it. */
		if (attr->attgenerated == ATTRIBUTE_GENERATED_VIRTUAL)
			elog(ERROR, "unexpected virtual generated column reference");

		if (attr->attisdropped)
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_COLUMN),
					 errmsg("attribute %d of type %s has been dropped",
							attnum, format_type_be(slot_tupdesc->tdtypeid))));

		if (vartype != attr->atttypid)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("attribute %d of type %s has wrong type",
							attnum, format_type_be(slot_tupdesc->tdtypeid)),
					 errdetail("Table has type %s, but query expects %s.",
							   format_type_be(attr->atttypid),
							   format_type_be(vartype))));
	}
}

/*
 * ============================================================================
 * 【中文注释】CheckOpSlotCompatibility —— 校验 FETCHSOME 步与槽实现类型匹配
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   校验即将执行 slot_getsomeattrs 的槽，其实现类型（tts_ops）与编译期
 *   记录的预期类型 op->d.fetch.kind 一致。仅编译断言（USE_ASSERT_CHECKING）
 *   下生效，生产构建为空操作。
 *
 * 参数：
 *   op   - FETCHSOME 步（d.fetch.kind = 编译期预期的 TTSOps 指针）。
 *   slot - 实际传入的槽。
 *
 * 设计思想：
 *   1. 为什么需要：FETCHSOME 在编译期按某个来源（如 HeapTuple 槽）生成，
 *      运行时实际传入的可能是另一种实现（如 BufferHeapTuple 槽），两种
 *      实现 deforming 行为不同但常互换使用；此检查防止开发者"想当然"
 *      地混用导致读取未变形数组。
 *   2. 放宽规则：
 *      - buffer 与 heap 槽可互换（历史上一直如此，统一放宽）；
 *      - 虚拟槽（Virtual）总是允许——虚拟槽永远无需变形，用哪个
 *        FETCHSOME 都成立；
 *      - 其余情况必须与预期种类完全一致。
 *   3. 被 EEOP_*_FETCHSOME 内联执行与各 ExecJust* 快速路径在取列前调用。
 * ============================================================================
 */
static void
CheckOpSlotCompatibility(ExprEvalStep *op, TupleTableSlot *slot)
{
#ifdef USE_ASSERT_CHECKING
	/* there's nothing to check */
	if (!op->d.fetch.fixed)
		return;

	/*
	 * Should probably fixed at some point, but for now it's easier to allow
	 * buffer and heap tuples to be used interchangeably.
	 */
	if (slot->tts_ops == &TTSOpsBufferHeapTuple &&
		op->d.fetch.kind == &TTSOpsHeapTuple)
		return;
	if (slot->tts_ops == &TTSOpsHeapTuple &&
		op->d.fetch.kind == &TTSOpsBufferHeapTuple)
		return;

	/*
	 * At the moment we consider it OK if a virtual slot is used instead of a
	 * specific type of slot, as a virtual slot never needs to be deformed.
	 */
	if (slot->tts_ops == &TTSOpsVirtual)
		return;

	Assert(op->d.fetch.kind == slot->tts_ops);
#endif
}

/*
 * ============================================================================
 * 【中文注释】get_cached_rowtype —— 按 (type_id, typmod) 缓存地查找行类型描述符
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   以"带身份校验的缓存"方式获取复合类型的 TupleDesc：命名复合类型走
 *   类型缓存（typcache，可失效重建），RECORD 类型走 lookup_rowtype_tupdesc。
 *   用于需要在执行期间反复取行类型描述符的 step（行 IS NULL、字段选择、
 *   FieldStore、行转换等）。
 *
 * 参数：
 *   type_id , typmod - 行类型的身份（type OID 与 typmod）。
 *   rowcache - ExprEvalRowtypeCache 缓存空间（cacheptr 首次调用前须为 NULL）。
 *   changed  - 非 NULL 时，任何一次"重新查找"都会置 *changed = true，
 *              调用方据此重建依赖描述符的中间结构（如属性映射）。
 *
 * 返回值：
 *   TupleDesc —— 注意：未保证 pin（引用计数已计入），需要跨"可能触发缓存
 *   失效的操作"（如 detoast 输入元组）使用时，调用方必须自行
 *   IncrTupleDescRefCount。
 *
 * 设计思想：
 *   1. 为什么必须"每次执行都可能重查"：复合类型内容可变（ALTER TYPE、
 *      ALTER TABLE 增删列），缓存身份用 typcache 的 tupDesc_identifier 或
 *      RECORD 的 (tdtypeid, tdtypmod) 判断，失效后自动重查——因此不能只在
 *      表达式初始化时查一次就假定永远有效。
 *   2. 命名类型路径：rowcache->cacheptr 保存 TypeCacheEntry*；用
 *      "tupdesc_id == 0" 来防御上次调用是 RECORD 类型时 cacheptr 指向
 *      TupleDesc 而非 TypeCacheEntry 的错位（理论情形，防御便宜）。
 *   3. RECORD 类型路径：一旦注册（lookup_rowtype_tupdesc）在会话期内不变，
 *      无需 typcache 条目；lookup 返回的 pin 立即释放，仅保留引用计数。
 *      两个路径都把"新找到的描述符"存入 rowcache，实现跨行复用。
 * ============================================================================
 */
static TupleDesc
get_cached_rowtype(Oid type_id, int32 typmod,
				   ExprEvalRowtypeCache *rowcache,
				   bool *changed)
{
	if (type_id != RECORDOID)
	{
		/*
		 * It's a named composite type, so use the regular typcache.  Do a
		 * lookup first time through, or if the composite type changed.  Note:
		 * "tupdesc_id == 0" may look redundant, but it protects against the
		 * admittedly-theoretical possibility that type_id was RECORDOID the
		 * last time through, so that the cacheptr isn't TypeCacheEntry *.
		 */
		TypeCacheEntry *typentry = (TypeCacheEntry *) rowcache->cacheptr;

		if (unlikely(typentry == NULL ||
					 rowcache->tupdesc_id == 0 ||
					 typentry->tupDesc_identifier != rowcache->tupdesc_id))
		{
			typentry = lookup_type_cache(type_id, TYPECACHE_TUPDESC);
			if (typentry->tupDesc == NULL)
				ereport(ERROR,
						(errcode(ERRCODE_WRONG_OBJECT_TYPE),
						 errmsg("type %s is not composite",
								format_type_be(type_id))));
			rowcache->cacheptr = typentry;
			rowcache->tupdesc_id = typentry->tupDesc_identifier;
			if (changed)
				*changed = true;
		}
		return typentry->tupDesc;
	}
	else
	{
		/*
		 * A RECORD type, once registered, doesn't change for the life of the
		 * backend.  So we don't need a typcache entry as such, which is good
		 * because there isn't one.  It's possible that the caller is asking
		 * about a different type than before, though.
		 */
		TupleDesc	tupDesc = (TupleDesc) rowcache->cacheptr;

		if (unlikely(tupDesc == NULL ||
					 rowcache->tupdesc_id != 0 ||
					 type_id != tupDesc->tdtypeid ||
					 typmod != tupDesc->tdtypmod))
		{
			tupDesc = lookup_rowtype_tupdesc(type_id, typmod);
			/* Drop pin acquired by lookup_rowtype_tupdesc */
			ReleaseTupleDesc(tupDesc);
			rowcache->cacheptr = tupDesc;
			rowcache->tupdesc_id = 0;	/* not a valid value for non-RECORD */
			if (changed)
				*changed = true;
		}
		return tupDesc;
	}
}


/*
 * ============================================================================
 * 【中文注释】ExecJust* 快速路径函数族 —— 极简单表达式的专用执行器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   由 ExecReadyInterpretedExpr 按 steps_len 与 opcode 模式匹配选中的专用
 *   求值函数：它们针对"FETCHSOME+VAR"、"CONST"、"CASE_TESTVAL+严格函数"
 *   等少数固定 step 形态手写最短路径，直接返回结果而非进入解释器主循环。
 *
 * 设计思想：
 *   完整解释器的"启动"开销（哪怕很小）对极简单表达式是可见的；这些形态
 *   （如 SELECT 里的裸列引用）又极其常见，值得为每种形态特化一个函数。
 *   每个特化函数对 step 布局有硬编码假设（如 ExecJustVarImpl 假定
 *   steps[0]=FETCHSOME、steps[1]=VAR），因此 ExecReadyInterpretedExpr 的
 *   模式匹配必须与这里的布局严格同步——改一边必须改另一边。
 *   虚拟槽变体（Virt）：假定槽已固定为虚拟槽且无需变形（编译期因此不发
 *   FETCHSOME），直接读 tts_values/tts_isnull。
 *   哈希变体：服务 Hash 连接/聚合的键列直接哈希（省去把列值经结果寄存器
 *   中转），是哈希表构建路径的热点。
 * ============================================================================
 */

/* 【中文注释】ExecJustVarImpl —— (Inner|Outer|Scan)Var 快速路径公共实现：
		 * 直接用 slot_getattr 取第 attnum 列（slot_getattr 内部自带按需
		 * 变形，因此无需显式 FETCHSOME，也不需要 Assert 列号范围）。
		 * 三个包装 ExecJustInnerVar/OuterVar/ScanVar 仅槽来源不同。 */
static pg_always_inline Datum
ExecJustVarImpl(ExprState *state, TupleTableSlot *slot, bool *isnull)
{
	ExprEvalStep *op = &state->steps[1];
	int			attnum = op->d.var.attnum + 1;

	CheckOpSlotCompatibility(&state->steps[0], slot);

	/*
	 * Since we use slot_getattr(), we don't need to implement the FETCHSOME
	 * step explicitly, and we also needn't Assert that the attnum is in range
	 * --- slot_getattr() will take care of any problems.
	 */
	return slot_getattr(slot, attnum, isnull);
}

/* 快速路径：直接引用 inner 关系（连接内表）的一列，委托 ExecJustVarImpl */
static Datum
ExecJustInnerVar(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustVarImpl(state, econtext->ecxt_innertuple, isnull);
}

/* 快速路径：直接引用 outer 关系（连接外表）的一列，委托 ExecJustVarImpl */
static Datum
ExecJustOuterVar(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustVarImpl(state, econtext->ecxt_outertuple, isnull);
}

/* 快速路径：直接引用当前扫描关系的一列，委托 ExecJustVarImpl */
static Datum
ExecJustScanVar(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustVarImpl(state, econtext->ecxt_scantuple, isnull);
}

/* 【中文注释】ExecJustAssignVarImpl —— AssignVar 快速路径公共实现：把
		 * 输入槽第 attnum 列的值（slot_getattr 自带按需变形）直接写入
		 * 结果槽第 resultnum 列。三个包装 ExecJustAssignInnerVar/OuterVar/
		 * ScanVar 仅输入槽来源不同。 */
static pg_always_inline Datum
ExecJustAssignVarImpl(ExprState *state, TupleTableSlot *inslot, bool *isnull)
{
	ExprEvalStep *op = &state->steps[1];
	int			attnum = op->d.assign_var.attnum + 1;
	int			resultnum = op->d.assign_var.resultnum;
	TupleTableSlot *outslot = state->resultslot;

	CheckOpSlotCompatibility(&state->steps[0], inslot);

	/*
	 * We do not need CheckVarSlotCompatibility here; that was taken care of
	 * at compilation time.
	 *
	 * Since we use slot_getattr(), we don't need to implement the FETCHSOME
	 * step explicitly, and we also needn't Assert that the attnum is in range
	 * --- slot_getattr() will take care of any problems.  Nonetheless, check
	 * that resultnum is in range.
	 */
	Assert(resultnum >= 0 && resultnum < outslot->tts_tupleDescriptor->natts);
	outslot->tts_values[resultnum] =
		slot_getattr(inslot, attnum, &outslot->tts_isnull[resultnum]);
	return 0;
}

/* 快速路径：求内表 Var 并写入结果元组对应列 */
static Datum
ExecJustAssignInnerVar(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustAssignVarImpl(state, econtext->ecxt_innertuple, isnull);
}

/* 快速路径：求外表 Var 并写入结果元组对应列 */
static Datum
ExecJustAssignOuterVar(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustAssignVarImpl(state, econtext->ecxt_outertuple, isnull);
}

/* 快速路径：求扫描 Var 并写入结果元组对应列 */
static Datum
ExecJustAssignScanVar(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustAssignVarImpl(state, econtext->ecxt_scantuple, isnull);
}

/*
 * ============================================================================
 * 【中文注释】ExecJustApplyFuncToCase —— CASE_TESTVAL + 严格函数的快速路径
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   特化模式 [EEOP_CASE_TESTVAL, EEOP_FUNCEXPR_STRICT*]：先把 CASE 基值
 *   拷入 step0 的结果寄存器（即被作为第一个实参），再对严格的函数调用做
 *   判空与调用。典型场景：CASE 的简单 CASE 表达式——WHEN 子句形如
 *   caseval = const 且比较运算符底层是严格函数。
 *
 * 设计思想：
 *   1. 省掉的启动：两个 step 的表达式不用进解释器主循环，直接手工串起来。
 *   2. 数据搬移的来历：CASE_TESTVAL 的结果写入其自身 step 的结果寄存器，
 *      编译期把该寄存器布局成函数调用的 args[0] 指向的位置，因此这里先
 *      "物化"基值再让 fn_addr 直接消费。
 *   3. 严格性：任一步骤的判空不通过则整个表达式结果为 NULL（与解释器
 *      中 EEOP_FUNCEXPR_STRICT 的 goto strictfail 语义一致）。
 *   4. 代码中的 XXX 注释提示：若重新设计 CaseTestExpr 机制，这个数据
 *      搬移也许能消除——属已知的小优化空间。
 * ============================================================================
 */
static Datum
ExecJustApplyFuncToCase(ExprState *state, ExprContext *econtext, bool *isnull)
{
	ExprEvalStep *op = &state->steps[0];
	FunctionCallInfo fcinfo;
	NullableDatum *args;
	int			nargs;
	Datum		d;

	/*
	 * XXX with some redesign of the CaseTestExpr mechanism, maybe we could
	 * get rid of this data shuffling?
	 */
	*op->resvalue = *op->d.casetest.value;
	*op->resnull = *op->d.casetest.isnull;

	op++;

	nargs = op->d.func.nargs;
	fcinfo = op->d.func.fcinfo_data;
	args = fcinfo->args;

	/* strict function, so check for NULL args */
	for (int argno = 0; argno < nargs; argno++)
	{
		if (args[argno].isnull)
		{
			*isnull = true;
			return (Datum) 0;
		}
	}
	fcinfo->isnull = false;
	d = op->d.func.fn_addr(fcinfo);
	*isnull = fcinfo->isnull;
	return d;
}

/* 【中文注释】ExecJustConst —— 常量的快速路径：常量值与 NULL 标志在
		 * 编译期已内嵌进 step，这里只需一次拷贝即可返回。 */
static Datum
ExecJustConst(ExprState *state, ExprContext *econtext, bool *isnull)
{
	ExprEvalStep *op = &state->steps[0];

	*isnull = op->d.constval.isnull;
	return op->d.constval.value;
}

/* 【中文注释】ExecJustVarVirtImpl —— 虚拟槽版 VAR 快速路径公共实现：
		 * 编译期已确认槽必为"已固定的虚拟槽"（因而无需也不能变形、没有
		 * FETCHSOME 步），直接读 tts_values/tts_isnull 数组返回；三个
		 * Assert 验证编译期判断与运行期事实一致。三个包装（Inner/Outer/
		 * Scan）仅槽来源不同。 */
static pg_always_inline Datum
ExecJustVarVirtImpl(ExprState *state, TupleTableSlot *slot, bool *isnull)
{
	ExprEvalStep *op = &state->steps[0];
	int			attnum = op->d.var.attnum;

	/*
	 * As it is guaranteed that a virtual slot is used, there never is a need
	 * to perform tuple deforming (nor would it be possible). Therefore
	 * execExpr.c has not emitted an EEOP_*_FETCHSOME step. Verify, as much as
	 * possible, that that determination was accurate.
	 */
	Assert(TTS_IS_VIRTUAL(slot));
	Assert(TTS_FIXED(slot));
	Assert(attnum >= 0 && attnum < slot->tts_nvalid);

	*isnull = slot->tts_isnull[attnum];

	return slot->tts_values[attnum];
}

/* 虚拟槽版：读内表 Var */
static Datum
ExecJustInnerVarVirt(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustVarVirtImpl(state, econtext->ecxt_innertuple, isnull);
}

/* 虚拟槽版：读外表 Var */
static Datum
ExecJustOuterVarVirt(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustVarVirtImpl(state, econtext->ecxt_outertuple, isnull);
}

/* 虚拟槽版：读扫描 Var */
static Datum
ExecJustScanVarVirt(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustVarVirtImpl(state, econtext->ecxt_scantuple, isnull);
}

/* 【中文注释】ExecJustAssignVarVirtImpl —— 虚拟槽版 ASSIGN 快速路径：
		 * 见 ExecJustAssignVarImpl 注释（槽为虚拟槽，零变形直接搬数组）。
		 * 三个包装（Inner/Outer/Scan）仅输入槽来源不同。 */
static pg_always_inline Datum
ExecJustAssignVarVirtImpl(ExprState *state, TupleTableSlot *inslot, bool *isnull)
{
	ExprEvalStep *op = &state->steps[0];
	int			attnum = op->d.assign_var.attnum;
	int			resultnum = op->d.assign_var.resultnum;
	TupleTableSlot *outslot = state->resultslot;

	/* see ExecJustVarVirtImpl for comments */

	Assert(TTS_IS_VIRTUAL(inslot));
	Assert(TTS_FIXED(inslot));
	Assert(attnum >= 0 && attnum < inslot->tts_nvalid);
	Assert(resultnum >= 0 && resultnum < outslot->tts_tupleDescriptor->natts);

	outslot->tts_values[resultnum] = inslot->tts_values[attnum];
	outslot->tts_isnull[resultnum] = inslot->tts_isnull[attnum];

	return 0;
}

/* 虚拟槽版：内表 Var 写入结果元组对应列 */
static Datum
ExecJustAssignInnerVarVirt(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustAssignVarVirtImpl(state, econtext->ecxt_innertuple, isnull);
}

/* 虚拟槽版：外表 Var 写入结果元组对应列 */
static Datum
ExecJustAssignOuterVarVirt(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustAssignVarVirtImpl(state, econtext->ecxt_outertuple, isnull);
}

/* 虚拟槽版：扫描 Var 写入结果元组对应列 */
static Datum
ExecJustAssignScanVarVirt(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustAssignVarVirtImpl(state, econtext->ecxt_scantuple, isnull);
}

/*
 * ============================================================================
 * 【中文注释】ExecJustHashInnerVarWithIV —— 带种子初值的哈希键快速路径
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   特化模式 [FETCHSOME, HASHDATUM_SET_INITVAL, INNER_VAR, HASHDATUM_NEXT32]
 *   （5 个 step）：把内表 Var 的哈希与指定初值合并。典型调用方是 Hash
 *   连接的"哈希内表前先对连接键做哈希"路径，其中初值用作哈希种子。
 *
 * 设计思想：
 *   1. 合并步骤在解释器里要四次派发（SET_INITVAL、FETCHSOME、VAR、
 *      NEXT32），这里手写为一个函数：变形（slot_getsomeattrs）+ 取列 +
 *      初值左旋一位 + 与列哈希异或（非 NULL 才哈希列；NULL 列保持初值
 *      参与合并，NULL 键与非 NULL 键仍能同桶，交由相等函数鉴别）。
 *   2. 与解释器 EEOP_HASHDATUM_NEXT32 的合并公式完全一致
 *      （hash = rotate_left(hash, 1) ^ value），保证同键两种路径
 *      产出一致哈希，这是哈希表可互换性的前提。
 * ============================================================================
 */
static Datum
ExecJustHashInnerVarWithIV(ExprState *state, ExprContext *econtext,
						   bool *isnull)
{
	ExprEvalStep *fetchop = &state->steps[0];
	ExprEvalStep *setivop = &state->steps[1];
	ExprEvalStep *innervar = &state->steps[2];
	ExprEvalStep *hashop = &state->steps[3];
	FunctionCallInfo fcinfo = hashop->d.hashdatum.fcinfo_data;
	int			attnum = innervar->d.var.attnum;
	uint32		hashkey;

	CheckOpSlotCompatibility(fetchop, econtext->ecxt_innertuple);
	slot_getsomeattrs(econtext->ecxt_innertuple, fetchop->d.fetch.last_var);

	fcinfo->args[0].value = econtext->ecxt_innertuple->tts_values[attnum];
	fcinfo->args[0].isnull = econtext->ecxt_innertuple->tts_isnull[attnum];

	hashkey = DatumGetUInt32(setivop->d.hashdatum_initvalue.init_value);
	hashkey = pg_rotate_left32(hashkey, 1);

	if (!fcinfo->args[0].isnull)
	{
		uint32		hashvalue;

		hashvalue = DatumGetUInt32(hashop->d.hashdatum.fn_addr(fcinfo));
		hashkey = hashkey ^ hashvalue;
	}

	*isnull = false;
	return UInt32GetDatum(hashkey);
}

/* 【中文注释】ExecJustHashVarImpl —— 单列哈希键快速路径公共实现：
		 * 模式 [FETCHSOME, VAR, HASHDATUM_FIRST]：变形后取列，非 NULL
		 * 则返回列哈希值（单列键不需要合并旋转），NULL 返回 0 作为
		 * 占位（NULL 键同桶语义由相等函数处理）。包装 ExecJustHashOuterVar
		 * / ExecJustHashInnerVar 仅槽来源不同。 */
static pg_always_inline Datum
ExecJustHashVarImpl(ExprState *state, TupleTableSlot *slot, bool *isnull)
{
	ExprEvalStep *fetchop = &state->steps[0];
	ExprEvalStep *var = &state->steps[1];
	ExprEvalStep *hashop = &state->steps[2];
	FunctionCallInfo fcinfo = hashop->d.hashdatum.fcinfo_data;
	int			attnum = var->d.var.attnum;

	CheckOpSlotCompatibility(fetchop, slot);
	slot_getsomeattrs(slot, fetchop->d.fetch.last_var);

	fcinfo->args[0].value = slot->tts_values[attnum];
	fcinfo->args[0].isnull = slot->tts_isnull[attnum];

	*isnull = false;

	if (!fcinfo->args[0].isnull)
		return hashop->d.hashdatum.fn_addr(fcinfo);
	else
		return (Datum) 0;
}

/* 快速路径：哈希外表 Var（Hash 连接探测侧键） */
static Datum
ExecJustHashOuterVar(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustHashVarImpl(state, econtext->ecxt_outertuple, isnull);
}

/* 快速路径：哈希内表 Var（Hash 连接构建侧键） */
static Datum
ExecJustHashInnerVar(ExprState *state, ExprContext *econtext, bool *isnull)
{
	return ExecJustHashVarImpl(state, econtext->ecxt_innertuple, isnull);
}

/* 【中文注释】ExecJustHashVarVirtImpl —— 虚拟槽版哈希键快速路径：
		 * 模式 [VAR, HASHDATUM_FIRST]（无 FETCHSOME）。见 ExecJustHashVarImpl
		 * 注释；虚拟槽免变形直接读数组。包装 ExecJustHashInnerVarVirt 与
		 * ExecJustHashOuterVarVirt 仅槽来源不同。 */
static pg_always_inline Datum
ExecJustHashVarVirtImpl(ExprState *state, TupleTableSlot *slot, bool *isnull)
{
	ExprEvalStep *var = &state->steps[0];
	ExprEvalStep *hashop = &state->steps[1];
	FunctionCallInfo fcinfo = hashop->d.hashdatum.fcinfo_data;
	int			attnum = var->d.var.attnum;

	fcinfo->args[0].value = slot->tts_values[attnum];
	fcinfo->args[0].isnull = slot->tts_isnull[attnum];

	*isnull = false;

	if (!fcinfo->args[0].isnull)
		return hashop->d.hashdatum.fn_addr(fcinfo);
	else
		return (Datum) 0;
}

/* 虚拟槽版：哈希内表 Var */
static Datum
ExecJustHashInnerVarVirt(ExprState *state, ExprContext *econtext,
						 bool *isnull)
{
	return ExecJustHashVarVirtImpl(state, econtext->ecxt_innertuple, isnull);
}

/* 虚拟槽版：哈希外表 Var */
static Datum
ExecJustHashOuterVarVirt(ExprState *state, ExprContext *econtext,
						 bool *isnull)
{
	return ExecJustHashVarVirtImpl(state, econtext->ecxt_outertuple, isnull);
}

/*
 * ============================================================================
 * 【中文注释】ExecJustHashOuterVarStrict —— 严格版外表哈希键快速路径
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   特化模式 [FETCHSOME, OUTER_VAR, HASHDATUM_FIRST_STRICT]：与
 *   ExecJustHashOuterVar 相同，但键列为 NULL 时直接返回 NULL 结果
 *   （*isnull = true），而不是用 0 占位。
 *
 * 设计思想：
 *   非严格版用 0 占位意味着"NULL 键也能算出哈希进入哈希表"，适合
 *   Hash Join 这类在相等性判定阶段再处理 NULL 的场景；严格版则让整
 *   个表达式的结果为 NULL，供"键为 NULL 时必须跳过/特殊处理"的调用方
 *   （比如某些 Hash 连接的过滤语义或聚合取键）使用——两种语义都要
 *   足够快，因此各配一个特化函数。
 * ============================================================================
 */
static Datum
ExecJustHashOuterVarStrict(ExprState *state, ExprContext *econtext,
						   bool *isnull)
{
	ExprEvalStep *fetchop = &state->steps[0];
	ExprEvalStep *var = &state->steps[1];
	ExprEvalStep *hashop = &state->steps[2];
	FunctionCallInfo fcinfo = hashop->d.hashdatum.fcinfo_data;
	int			attnum = var->d.var.attnum;

	CheckOpSlotCompatibility(fetchop, econtext->ecxt_outertuple);
	slot_getsomeattrs(econtext->ecxt_outertuple, fetchop->d.fetch.last_var);

	fcinfo->args[0].value = econtext->ecxt_outertuple->tts_values[attnum];
	fcinfo->args[0].isnull = econtext->ecxt_outertuple->tts_isnull[attnum];

	if (!fcinfo->args[0].isnull)
	{
		*isnull = false;
		return hashop->d.hashdatum.fn_addr(fcinfo);
	}
	else
	{
		/* return NULL on NULL input */
		*isnull = true;
		return (Datum) 0;
	}
}

#if defined(EEO_USE_COMPUTED_GOTO)
/*
 * ============================================================================
 * 【中文注释】dispatch_compare_ptr —— 跳转目标地址->opcode 反查表的排序比较器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按 opcode（代码块地址）大小比较两个 ExprEvalOpLookup 条目，供
 *   qsort（构建 reverse_dispatch_table）与 bsearch（ExecEvalStepOp 反查）
 *   使用。
 *
 * 设计思想：
 *   direct-threaded 方式下，step 的 opcode 域被替换为代码块地址，运行时
 *   需要"由地址还原枚举 opcode"（如 ExecInterpExprStillValid 校验时）。
 *   由于地址不是按枚举顺序递增的，先把 (地址, opcode) 对建成表并按地址
 *   排序，之后 O(log N) 二分即可反查。地址可以直接比较大小即比较器
 *   只是数值大小比较——比较语义正确即可，无需关心地址本身含义。
 * ============================================================================
 */
static int
dispatch_compare_ptr(const void *a, const void *b)
{
	const ExprEvalOpLookup *la = (const ExprEvalOpLookup *) a;
	const ExprEvalOpLookup *lb = (const ExprEvalOpLookup *) b;

	if (la->opcode < lb->opcode)
		return -1;
	else if (la->opcode > lb->opcode)
		return 1;
	return 0;
}
#endif

/*
 * ============================================================================
 * 【中文注释】ExecInitInterpreter —— 解释器的全局一次性初始化
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   只做一次：在 direct-threaded 方式下，把 ExecInterpExpr 内置的
 *   dispatch_table 静态数组地址取出来存到文件级全局 dispatch_table，
 *   并构建反向查找表 reverse_dispatch_table（保持有序以便二分）。
 *
 * 设计思想：
 *   1. dispatch_table 是 ExecInterpExpr 内部的 static 局部数组（与枚举
 *      ExprEvalOp 顺序一致，StaticAssertDecl 保证长度）；为让 ExecInterpExpr
 *      之外的代码（ExecReadyInterpretedExpr 的 EEO_OPCODE、ExecEvalStepOp
 *      的反查）也能访问，用"state == NULL 调用 ExecInterpExpr 返回表地址"
 *      的技巧把它导出到全局。开关方式下不编译 dispatch_table，本函数为空。
 *   2. 反查表：直接线程化后 step->opcode 是代码块地址，需要还原成
 *      枚举值时按地址二分查找——这正是 CheckExprStillValid /
 *      ExecEvalStepOp 的用法。地址对应关系在编译期内稳定（每个 CASE_ 标签
 *      地址固定），因此一次构建全局复用。
 *   3. 由 ExecReadyInterpretedExpr 在每个 ExprState 准备时调用，利用
 *      dispatch_table == NULL 判空保证只初始化一次。
 * ============================================================================
 */
static void
ExecInitInterpreter(void)
{
#if defined(EEO_USE_COMPUTED_GOTO)
	/* Set up externally-visible pointer to dispatch table */
	if (dispatch_table == NULL)
	{
		dispatch_table = (const void **)
			DatumGetPointer(ExecInterpExpr(NULL, NULL, NULL));

		/* build reverse lookup table */
		for (int i = 0; i < EEOP_LAST; i++)
		{
			reverse_dispatch_table[i].opcode = dispatch_table[i];
			reverse_dispatch_table[i].op = (ExprEvalOp) i;
		}

		/* make it bsearch()able */
		qsort(reverse_dispatch_table,
			  EEOP_LAST /* nmembers */ ,
			  sizeof(ExprEvalOpLookup),
			  dispatch_compare_ptr);
	}
#endif
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalStepOp —— 返回表达式 step 的原始 opcode 枚举值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   读取 step 的 opcode 域并还原为 ExprEvalOp 枚举。直接线程化的
 *   ExprState 里 opcode 域存的是代码块地址而不是枚举，需要时用反查表
 *   换回枚举；普通状态下直接转型返回。
 *
 * 参数：
 *   state - ExprState（查 EEO_FLAG_DIRECT_THREADED 决定是否反查）。
 *   op    - 目标 step。
 *
 * 设计思想：
 *   解释器执行路径本身用不到这个函数（它直接以地址/枚举 dispatch），
 *   但"需要审视 step 内容的代码"（如 CheckExprStillValid 的逐步校验、
 *   JIT 代码生成对 step 分类）必须以枚举为准，因此提供统一入口。
 *   直接线程化时的反查是 bsearch 二分，O(log EEOP_LAST)，只在非热点
 *   路径使用；未知地址会触发 Assert（说明 dispatch 表与枚举失配，
 *   属于内部错误）。本函数也被 execExpr.c / exprjit 等模块使用（extern）。
 * ============================================================================
 */
ExprEvalOp
ExecEvalStepOp(ExprState *state, ExprEvalStep *op)
{
#if defined(EEO_USE_COMPUTED_GOTO)
	if (state->flags & EEO_FLAG_DIRECT_THREADED)
	{
		ExprEvalOpLookup key;
		ExprEvalOpLookup *res;

		key.opcode = (void *) op->opcode;
		res = bsearch(&key,
					  reverse_dispatch_table,
					  EEOP_LAST /* nmembers */ ,
					  sizeof(ExprEvalOpLookup),
					  dispatch_compare_ptr);
		Assert(res);			/* unknown ops shouldn't get looked up */
		return res->op;
	}
#endif
	return (ExprEvalOp) op->opcode;
}


/*
 * ============================================================================
 * 【中文注释】out-of-line 辅助函数区 —— 复杂指令的执行器（对外暴露共享）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   执行解释器主循环中"过于复杂/罕见、不值得内联"的 EEOP_* opcode 的
 *   辅助函数：数组、行、XML/JSON、域约束、参数、聚合转移、子计划、
 *   整行 Var 等。它们全部导出（非 static），并与解释器本体共享同一套
 *   ExprEvalStep/ExprEvalOp 数据结构约定。
 *
 * 设计思想：
 *   1. 内联取舍：主循环 EEO_CASE 里只有"每次执行都走、且代码量小"的
 *      指令才手写；复杂指令内联既难写出高效代码也会撑爆指令缓存，
 *      因此一条 EEO_CASE 一行函数调用。
 *   2. 共享契约：这些函数被多种"执行方式"共用——解释器（本文件）调用、
 *      JIT 编译（exprjit.c）直接生成对它们的原生调用、以及少量 fast-path
 *      特化；正因为如此它们必须导出，这是它们能被 JIT 复用的关键。
 *   3. 状态持久化：凡涉及跨行缓存（行类型缓存 rowcache、哈希表
 *      elements_tab、属性映射 map 等）都挂在 step 的 d.* 联合体中，
 *      由这些函数在第一行访问时初始化、后续行直接复用。
 * ============================================================================
 */

/*
 * ============================================================================
 * 【中文注释】ExecEvalFuncExprFusage / ExecEvalFuncExprStrictFusage ——
 *              带 pg_stat 函数调用统计的（严格）函数调用
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与内联的 EEOP_FUNCEXPR[_STRICT] 等价的函数调用执行，额外用
 *   pgstat_init_function_usage / pgstat_end_function_usage 统计函数调用
 *   次数与耗时（pg_stat_user_functions 的数据来源）。Fusage 版不判严格，
 *   StrictFusage 版先逐个参数判空、有 NULL 时直接返回 NULL 结果。
 *
 * 参数：
 *   state   - ExprState（执行上下文）。
 *   op      - FUNCEXPR_FUSAGE / FUNCEXPR_STRICT_FUSAGE 步，实参已由前置
 *             step 求值填入 fcinfo->args。
 *   econtext- 未使用（保留签名一致性）。
 *
 * 设计思想：
 *   函数调用统计不是默认开启的（track_functions 关闭时这些 opcode 不会
 *   被编译出来），因而不常见——这就是它们不进主循环内联的原因。统计
 *   的开启/关闭由 execExpr.c 编译期根据 GUC 决定发不发 FUSAGE 变体，
 *   运行时零判断。strict 变体与 EEOP_FUNCEXPR_STRICT 语义一致
 *   （NULL 输入不调用函数）。
 * ============================================================================
 */
void
ExecEvalFuncExprFusage(ExprState *state, ExprEvalStep *op,
					   ExprContext *econtext)
{
	FunctionCallInfo fcinfo = op->d.func.fcinfo_data;
	PgStat_FunctionCallUsage fcusage;
	Datum		d;

	pgstat_init_function_usage(fcinfo, &fcusage);

	fcinfo->isnull = false;
	d = op->d.func.fn_addr(fcinfo);
	*op->resvalue = d;
	*op->resnull = fcinfo->isnull;

	pgstat_end_function_usage(&fcusage, true);
}

/*
 * 严格版 Fusage 调用：实参任一为 NULL 即短路，不调用函数也不做统计
 */
void
ExecEvalFuncExprStrictFusage(ExprState *state, ExprEvalStep *op,
							 ExprContext *econtext)
{

	FunctionCallInfo fcinfo = op->d.func.fcinfo_data;
	PgStat_FunctionCallUsage fcusage;
	NullableDatum *args = fcinfo->args;
	int			nargs = op->d.func.nargs;
	Datum		d;

	/* strict function, so check for NULL args */
	for (int argno = 0; argno < nargs; argno++)
	{
		if (args[argno].isnull)
		{
			*op->resnull = true;
			return;
		}
	}

	pgstat_init_function_usage(fcinfo, &fcusage);

	fcinfo->isnull = false;
	d = op->d.func.fn_addr(fcinfo);
	*op->resvalue = d;
	*op->resnull = fcinfo->isnull;

	pgstat_end_function_usage(&fcusage, true);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalParamExec —— 读取内部执行参数（PARAM_EXEC）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按 op->d.param.paramid 从 econtext->ecxt_param_exec_vals 数组取值写入
 *   结果寄存器。PARAM_EXEC 是"执行器内部参数"：InitPlan / 子查询结果、
 *   被下推的参数化表达式等都通过它传递。
 *
 * 设计思想：
 *   1. 惰性求值：若参数还挂着 execPlan（首次访问的 InitPlan 结果参数），
 *      先调用 ExecSetParamPlan 执行子计划把值填好——从而保证"引用子计划
 *      结果的表达式"在任意访问顺序下都得到正确值，且子计划只执行一次。
 *   2. 校验：barrier 语义上，ExecSetParamPlan 完成后必须清掉 execPlan
 *      （Assert 验证），防止同一 InitPlan 被重复执行。
 *   3. 数组直取零拷贝：值的生命周期由参数槽管理（通常跨元组稳定或用
 *      一次就拷贝），这里不做任何拷贝。
 * ============================================================================
 */
void
ExecEvalParamExec(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	ParamExecData *prm;

	prm = &(econtext->ecxt_param_exec_vals[op->d.param.paramid]);
	if (unlikely(prm->execPlan != NULL))
	{
		/* Parameter not evaluated yet, so go do it */
		ExecSetParamPlan(prm->execPlan, econtext);
		/* ExecSetParamPlan should have processed this param... */
		Assert(prm->execPlan == NULL);
	}
	*op->resvalue = prm->value;
	*op->resnull = prm->isnull;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalParamExtern —— 读取外部参数（PARAM_EXTERN）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从 econtext->ecxt_param_list_info（调用方传入的 ParamListInfo）按
 *   paramId 取 $1/$2... 之类的客户端参数值，写入结果寄存器；参数类型与
 *   编译期记录不符时报 DATATYPE_MISMATCH，找不到参数报 UNDEFINED_OBJECT。
 *
 * 设计思想：
 *   1. 动态参数钩子：ParamListInfo->paramFetch 允许调用方（如某些 FDW、
 *      扩展、PL/pgSQL 的动态绑定）按需现场生成参数值，回调返回的临时
 *      条目先拷到栈上 prmdata 再使用，避免悬垂指针。
 *   2. 类型校验：计划编译时记录 paramtype，运行时与 paramFetch/数组提供
 *      ptype 比对——不同则说明调用方改变了参数类型（典型如 JDBC 驱动
 *      类型推断变化），必须报错而不是静默错值。
 *   3. 热路径友好：常规路径（paramInfo 有效 + paramId 在范围 + ptype 有效）
 *      全部标 likely，跳过错误分支；只有在失败时才进入报错路径。
 * ============================================================================
 */
void
ExecEvalParamExtern(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	ParamListInfo paramInfo = econtext->ecxt_param_list_info;
	int			paramId = op->d.param.paramid;

	if (likely(paramInfo &&
			   paramId > 0 && paramId <= paramInfo->numParams))
	{
		ParamExternData *prm;
		ParamExternData prmdata;

		/* give hook a chance in case parameter is dynamic */
		if (paramInfo->paramFetch != NULL)
			prm = paramInfo->paramFetch(paramInfo, paramId, false, &prmdata);
		else
			prm = &paramInfo->params[paramId - 1];

		if (likely(OidIsValid(prm->ptype)))
		{
			/* safety check in case hook did something unexpected */
			if (unlikely(prm->ptype != op->d.param.paramtype))
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("type of parameter %d (%s) does not match that when preparing the plan (%s)",
								paramId,
								format_type_be(prm->ptype),
								format_type_be(op->d.param.paramtype))));
			*op->resvalue = prm->value;
			*op->resnull = prm->isnull;
			return;
		}
	}

	ereport(ERROR,
			(errcode(ERRCODE_UNDEFINED_OBJECT),
			 errmsg("no value found for parameter %d", paramId)));
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalParamSet —— 反向设置 PARAM_EXEC 参数的值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把当前结果寄存器（*op->resvalue / *op->resnull）写入
 *   econtext->ecxt_param_exec_vals[paramid]，即把刚求出的表达式结果
 *   存入某内部参数。
 *
 * 设计思想：
 *   与 ExecEvalParamExec 是读写对偶：编译期把"InitPlan 结果参数"的写入
 *   点编译为 PARAM_SET step（如 UNION 子计划结果的回填、参数化扫描的
 *   参数装载），随后引用方用 PARAM_EXEC 读取。执行期间该参数可能被
 *   多次写入（每行改写），读取方总是看到最新值。Assert 确保写入前该
 *   参数没有挂起的求值计划（PARAM_SET 与 InitPlan 首次求值互斥）。
 * ============================================================================
 */
void
ExecEvalParamSet(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	ParamExecData *prm;

	prm = &(econtext->ecxt_param_exec_vals[op->d.param.paramid]);

	/* Shouldn't have a pending evaluation anymore */
	Assert(prm->execPlan == NULL);

	prm->value = *op->resvalue;
	prm->isnull = *op->resnull;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalCoerceViaIOSafe —— 软错误模式的 CoerceViaIO
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与内联 EEOP_IOCOERCE 等价但"出错不抛异常"：输入函数调用通过
 *   ErrorSaveContext 捕获错误（fcinfo_in->context 必须是 ErrorSaveContext），
 *   出错时结果置 NULL 返回；供 JSON 等需要把转换失败转为 NULL/走
 *   ON ERROR 语义的场景使用。
 *
 * 参数：
 *   state - ExprState（未直接使用，保留签名一致性）。
 *   op    - IOCOERCE_SAFE 步；源值在 *op->resvalue，输出/输入函数的
 *           fcinfo 与 typmod 等参数已由编译期备好。
 *
 * 设计思想：
 *   1. 流程与 EEOP_IOCOERCE 完全平行：NULL 源值不调用输出函数，直接
 *      以 NULL 进入输入函数判定（严格输入函数且 str 为 NULL 时不再调用）；
 *      成功路径的 null 结果一致性用 Assert 保持。
 *   2. 与内联版的双向维护约定：注释显式要求修改任一方时必须同步审查
 *      另一方（JIT 直接复用内联版代码，SAFE 版专供软错误路径）。
 *   3. 软错误的落地：InputFunctionCallSafe 在失败时把错误记录进
 *      ErrorSaveContext 而非抛异常；这里检查 SOFT_ERROR_OCCURRED 后把
 *      结果置 NULL——由上层 step（如 JSONEXPR_COERCION_FINISH）决定
 *      是走 ON ERROR 分支还是保持 NULL。
 * ============================================================================
 */
void
ExecEvalCoerceViaIOSafe(ExprState *state, ExprEvalStep *op)
{
	char	   *str;

	/* call output function (similar to OutputFunctionCall) */
	if (*op->resnull)
	{
		/* output functions are not called on nulls */
		str = NULL;
	}
	else
	{
		FunctionCallInfo fcinfo_out;

		fcinfo_out = op->d.iocoerce.fcinfo_data_out;
		fcinfo_out->args[0].value = *op->resvalue;
		fcinfo_out->args[0].isnull = false;

		fcinfo_out->isnull = false;
		str = DatumGetCString(FunctionCallInvoke(fcinfo_out));

		/* OutputFunctionCall assumes result isn't null */
		Assert(!fcinfo_out->isnull);
	}

	/* call input function (similar to InputFunctionCallSafe) */
	if (!op->d.iocoerce.finfo_in->fn_strict || str != NULL)
	{
		FunctionCallInfo fcinfo_in;

		fcinfo_in = op->d.iocoerce.fcinfo_data_in;
		fcinfo_in->args[0].value = PointerGetDatum(str);
		fcinfo_in->args[0].isnull = *op->resnull;
		/* second and third arguments are already set up */

		/* ErrorSaveContext must be present. */
		Assert(IsA(fcinfo_in->context, ErrorSaveContext));

		fcinfo_in->isnull = false;
		*op->resvalue = FunctionCallInvoke(fcinfo_in);

		if (SOFT_ERROR_OCCURRED(fcinfo_in->context))
		{
			*op->resnull = true;
			*op->resvalue = (Datum) 0;
			return;
		}

		/* Should get null result if and only if str is NULL */
		if (str == NULL)
			Assert(*op->resnull);
		else
			Assert(!*op->resnull);
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalSQLValueFunction —— SQL 值函数（CURRENT_DATE 等）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   计算 SQLValueFunction 节点：CURRENT_DATE/CURRENT_TIME(_N)/
 *   CURRENT_TIMESTAMP(_N)/LOCALTIME(_N)/LOCALTIMESTAMP(_N)/CURRENT_ROLE/
 *   CURRENT_USER/USER/SESSION_USER/CURRENT_CATALOG/CURRENT_SCHEMA，结果
 *   写入结果寄存器。
 *
 * 设计思想：
 *   1. 这些函数值在事务内多次求值也必须一致（如 CURRENT_TIMESTAMP 在
 *      START TRANSACTION 时冻结），因此底层 GetSQLCurrent* 都基于
 *      transaction timestamp 的快照语义，本函数只是分派+取结果。
 *   2. 带精度后缀的形态（_N）由 svf->typmod 控制小数位数。
 *   3. 大部分形态结果恒非 NULL（resnull 预置 false），仅 current_schema()
 *      可能返回 NULL（未设置 search_path 前），其余形态也统一按可空
 *      编码以防将来语义变化。
 *   4. 用户相关形态直接调用内置函数（current_user 等），保持与函数
 *      调用一致的语义（如 SET ROLE 影响）。
 * ============================================================================
 */
void
ExecEvalSQLValueFunction(ExprState *state, ExprEvalStep *op)
{
	LOCAL_FCINFO(fcinfo, 0);
	SQLValueFunction *svf = op->d.sqlvaluefunction.svf;

	*op->resnull = false;

	/*
	 * Note: current_schema() can return NULL.  current_user() etc currently
	 * cannot, but might as well code those cases the same way for safety.
	 */
	switch (svf->op)
	{
		case SVFOP_CURRENT_DATE:
			*op->resvalue = DateADTGetDatum(GetSQLCurrentDate());
			break;
		case SVFOP_CURRENT_TIME:
		case SVFOP_CURRENT_TIME_N:
			*op->resvalue = TimeTzADTPGetDatum(GetSQLCurrentTime(svf->typmod));
			break;
		case SVFOP_CURRENT_TIMESTAMP:
		case SVFOP_CURRENT_TIMESTAMP_N:
			*op->resvalue = TimestampTzGetDatum(GetSQLCurrentTimestamp(svf->typmod));
			break;
		case SVFOP_LOCALTIME:
		case SVFOP_LOCALTIME_N:
			*op->resvalue = TimeADTGetDatum(GetSQLLocalTime(svf->typmod));
			break;
		case SVFOP_LOCALTIMESTAMP:
		case SVFOP_LOCALTIMESTAMP_N:
			*op->resvalue = TimestampGetDatum(GetSQLLocalTimestamp(svf->typmod));
			break;
		case SVFOP_CURRENT_ROLE:
		case SVFOP_CURRENT_USER:
		case SVFOP_USER:
			InitFunctionCallInfoData(*fcinfo, NULL, 0, InvalidOid, NULL, NULL);
			*op->resvalue = current_user(fcinfo);
			*op->resnull = fcinfo->isnull;
			break;
		case SVFOP_SESSION_USER:
			InitFunctionCallInfoData(*fcinfo, NULL, 0, InvalidOid, NULL, NULL);
			*op->resvalue = session_user(fcinfo);
			*op->resnull = fcinfo->isnull;
			break;
		case SVFOP_CURRENT_CATALOG:
			InitFunctionCallInfoData(*fcinfo, NULL, 0, InvalidOid, NULL, NULL);
			*op->resvalue = current_database(fcinfo);
			*op->resnull = fcinfo->isnull;
			break;
		case SVFOP_CURRENT_SCHEMA:
			InitFunctionCallInfoData(*fcinfo, NULL, 0, InvalidOid, NULL, NULL);
			*op->resvalue = current_schema(fcinfo);
			*op->resnull = fcinfo->isnull;
			break;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalCurrentOfExpr —— CURRENT OF 不支持时的错误落点
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   执行到 EEOP_CURRENTOFEXPR 时必然报"不支持"错误。
 *
 * 设计思想：
 *   正常流程中，规划器应把 WHERE CURRENT OF 转换为 TidScan 的定位条件
 *   （或由 ForeignScan 的 FDW 特殊处理），因此 ExecInitExpr 必须能编译
 *   CurrentOfExpr 节点（保持接口完整），但解释执行永远不应该走到这里。
 *   走到这里即意味着：该查询针对的是不处理 CURRENT OF 的表类型
 *   （如不支持的外表），此时给出清晰的 FEATURE_NOT_SUPPORTED 错误，
 *   而不是让查询静默返回空结果。
 * ============================================================================
 */
void
ExecEvalCurrentOfExpr(ExprState *state, ExprEvalStep *op)
{
	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("WHERE CURRENT OF is not supported for this table type")));
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalNextValueExpr —— 序列 nextval 求值（NextValueExpr）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   调用 nextval_internal 推进序列并取新值，按序列声明类型（int2/int4/int8）
 *   转换为对应 Datum 写入结果寄存器。
 *
 * 设计思想：
 *   1. NextValueExpr 在 DEFAULT 表达式/序列默认值场景下由执行器直接求值
 *      （相对普通函数调用省去 fmgr 包装），是 INSERT 走序列默认值的
 *      主路径。
 *   2. 序列推进是全局副作用：每行调用一次必取到互不相同的新值；
 *      nextval_internal 内部处理序列缓存与 WAL。
 *   3. 结果非 NULL（预置 resnull=false）；序列类型只允许三种整数类型，
 *      其它是编译期不可达，运行时撞上按内部错误 elog 处理。
 * ============================================================================
 */
void
ExecEvalNextValueExpr(ExprState *state, ExprEvalStep *op)
{
	int64		newval = nextval_internal(op->d.nextvalueexpr.seqid, false);

	switch (op->d.nextvalueexpr.seqtypid)
	{
		case INT2OID:
			*op->resvalue = Int16GetDatum((int16) newval);
			break;
		case INT4OID:
			*op->resvalue = Int32GetDatum((int32) newval);
			break;
		case INT8OID:
			*op->resvalue = Int64GetDatum(newval);
			break;
		default:
			elog(ERROR, "unsupported sequence type %u",
				 op->d.nextvalueexpr.seqtypid);
	}
	*op->resnull = false;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalRowNull / ExecEvalRowNotNull —— 行值的 IS [NOT] NULL
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   求值 "行变量 IS NULL" / "行变量 IS NOT NULL"：两个薄包装分别把
 *   checkisnull 置 true/false 后委托公共实现 ExecEvalRowNullInt。
 *
 * 设计思想：
 *   1. 委托结构：真正的实现只有一份（ExecEvalRowNullInt），两个入口
 *      只差"判空方向"，避免复制代码。
 *   2. SQL 标准语义（在 ExecEvalRowNullInt 中实现）：
 *      - R IS NULL 当且仅当 R 的每个字段都是 NULL；
 *      - R IS NOT NULL 当且仅当 R 没有任何字段为 NULL；
 *      - 判定是"原始 attisnull"层面的，不做递归（字段本身若是行类型，
 *        不递归检查其字段）；
 *      - 零字段的行（空行类型）两者都空洞满足（返回 true）。
 *      注意这与"行是否等于 NULL 复合值"完全不同——NULL 复合 Datum
 *      直接当作标量 NULL 处理。
 * ============================================================================
 */
void
ExecEvalRowNull(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	ExecEvalRowNullInt(state, op, econtext, true);
}

/* 行值 IS NOT NULL：同 ExecEvalRowNull 中文注释，checkisnull=false */
void
ExecEvalRowNotNull(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	ExecEvalRowNullInt(state, op, econtext, false);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalRowNullInt —— 行 IS [NOT] NULL 的公共实现（核心）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对结果寄存器中的行 Datum（HeapTupleHeader 复合值）逐字段执行
 *   attisnull 检查，按 checkisnull 方向汇总出 IS NULL / IS NOT NULL 的
 *   布尔结果；源值为 NULL 时退化为标量 NULL 判定。
 *
 * 参数：
 *   checkisnull - true 表示求 IS NULL；false 表示求 IS NOT NULL。
 *
 * 设计思想：
 *   1. 槽位约定：输入在 *op->resvalue（前一步求值的行值），输出覆写
 *      同一寄存器，不额外分配。
 *   2. NULL 复合值等价于标量 NULL：直接返回 checkisnull，不进入逐字段
 *      逻辑（与 SQL 语义一致：一个 NULL 的行变量就是"值未知"）。
 *   3. 行类型缓存：通过 get_cached_rowtype 按 (tupType, tupTypmod) 取
 *      描述符并缓存于 step 的 rowcache；描述符可能在执行期间因 DDL
 *      失效，该函数自动重查。
 *   4. 逐字段判定采用 heap_attisnull（直接用 null bitmap/无位图优化，
 *      比 heap_getattr 轻）并跳过已丢弃列；一旦出现"反例字段"立即
 *      返回 false 短路——行通常只有少数字段，最坏 O(natts)。
 * ============================================================================
 */
static void
ExecEvalRowNullInt(ExprState *state, ExprEvalStep *op,
				   ExprContext *econtext, bool checkisnull)
{
	Datum		value = *op->resvalue;
	bool		isnull = *op->resnull;
	HeapTupleHeader tuple;
	Oid			tupType;
	int32		tupTypmod;
	TupleDesc	tupDesc;
	HeapTupleData tmptup;

	*op->resnull = false;

	/* NULL row variables are treated just as NULL scalar columns */
	if (isnull)
	{
		*op->resvalue = BoolGetDatum(checkisnull);
		return;
	}

	/*
	 * The SQL standard defines IS [NOT] NULL for a non-null rowtype argument
	 * as:
	 *
	 * "R IS NULL" is true if every field is the null value.
	 *
	 * "R IS NOT NULL" is true if no field is the null value.
	 *
	 * This definition is (apparently intentionally) not recursive; so our
	 * tests on the fields are primitive attisnull tests, not recursive checks
	 * to see if they are all-nulls or no-nulls rowtypes.
	 *
	 * The standard does not consider the possibility of zero-field rows, but
	 * here we consider them to vacuously satisfy both predicates.
	 */

	tuple = DatumGetHeapTupleHeader(value);

	tupType = HeapTupleHeaderGetTypeId(tuple);
	tupTypmod = HeapTupleHeaderGetTypMod(tuple);

	/* Lookup tupdesc if first time through or if type changes */
	tupDesc = get_cached_rowtype(tupType, tupTypmod,
								 &op->d.nulltest_row.rowcache, NULL);

	/*
	 * heap_attisnull needs a HeapTuple not a bare HeapTupleHeader.
	 */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
	tmptup.t_data = tuple;

	for (int att = 1; att <= tupDesc->natts; att++)
	{
		/* ignore dropped columns */
		if (TupleDescCompactAttr(tupDesc, att - 1)->attisdropped)
			continue;
		if (heap_attisnull(&tmptup, att, tupDesc))
		{
			/* null field disproves IS NOT NULL */
			if (!checkisnull)
			{
				*op->resvalue = BoolGetDatum(false);
				return;
			}
		}
		else
		{
			/* non-null field disproves IS NULL */
			if (checkisnull)
			{
				*op->resvalue = BoolGetDatum(false);
				return;
			}
		}
	}

	*op->resvalue = BoolGetDatum(true);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalArrayExpr —— ARRAY[...] 数组构造（核心）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把编译期预分配的 elemvalues/elemnulls 中的各元素组装成 ArrayType：
 *   一维数组直接 construct_md_array；多维数组（元素本身是子数组）需
 *   校验各子数组维度一致、合并数据区与 NULL 位图，并做溢出/维度检查。
 *
 * 参数：
 *   state - ExprState（保留，未直接使用）。
 *   op    - ARRAYEXPR 步：d.arrayexpr 提供 elemtype、nelems、multidims、
 *           elemvalues/elemnulls 及元素类型物理属性。
 *
 * 设计思想：
 *   1. 两种形态：
 *      - 非多维（multidims=false）：元素是标量，一维、下界 1 构造；
 *      - 多维（multidims=true）：元素应是数组，结果维度 = 子数组维度+1。
 *   2. 多维合并细节：以第一个非空子数组的维度/下界为基准，其余子数组
 *      必须完全一致（含下界），否则按 SQL 报 ARRAY_SUBSCRIPT_ERROR；
 *      运行时还会复核元素类型（编译期推断可能与实际运行类型不同）。
 *      NULL 子数组与 0 维空数组都标记 haveempty：全部为空时返回空数组，
 *      部分为空时报维度不一致错误。
 *   3. 内存规划：先累加各子数组数据字节数与 NULL 位图需要，统一 palloc
 *      一次并逐块 memcpy（含 64 位对齐安全；位图用 array_bitmap_copy），
 *      避免逐元素插入的开销与碎片。
 *   4. 总大小按 AllocSizeIsValid 防溢出（MaxAllocSize 上限），下标乘积
 *      ArrayCheckBounds 防整型溢出。
 * ============================================================================
 */
void
ExecEvalArrayExpr(ExprState *state, ExprEvalStep *op)
{
	ArrayType  *result;
	Oid			element_type = op->d.arrayexpr.elemtype;
	int			nelems = op->d.arrayexpr.nelems;
	int			ndims = 0;
	int			dims[MAXDIM];
	int			lbs[MAXDIM];

	/* Set non-null as default */
	*op->resnull = false;

	if (!op->d.arrayexpr.multidims)
	{
		/* Elements are presumably of scalar type */
		Datum	   *dvalues = op->d.arrayexpr.elemvalues;
		bool	   *dnulls = op->d.arrayexpr.elemnulls;

		/* setup for 1-D array of the given length */
		ndims = 1;
		dims[0] = nelems;
		lbs[0] = 1;

		result = construct_md_array(dvalues, dnulls, ndims, dims, lbs,
									element_type,
									op->d.arrayexpr.elemlength,
									op->d.arrayexpr.elembyval,
									op->d.arrayexpr.elemalign);
	}
	else
	{
		/* Must be nested array expressions */
		int			nbytes = 0;
		int			nitems;
		int			outer_nelems = 0;
		int			elem_ndims = 0;
		int		   *elem_dims = NULL;
		int		   *elem_lbs = NULL;
		bool		firstone = true;
		bool		havenulls = false;
		bool		haveempty = false;
		char	  **subdata;
		uint8	  **subbitmaps;
		int		   *subbytes;
		int		   *subnitems;
		int32		dataoffset;
		char	   *dat;
		int			iitem;

		subdata = (char **) palloc(nelems * sizeof(char *));
		subbitmaps = (uint8 **) palloc(nelems * sizeof(uint8 *));
		subbytes = (int *) palloc(nelems * sizeof(int));
		subnitems = (int *) palloc(nelems * sizeof(int));

		/* loop through and get data area from each element */
		for (int elemoff = 0; elemoff < nelems; elemoff++)
		{
			Datum		arraydatum;
			bool		eisnull;
			ArrayType  *array;
			int			this_ndims;

			arraydatum = op->d.arrayexpr.elemvalues[elemoff];
			eisnull = op->d.arrayexpr.elemnulls[elemoff];

			/* temporarily ignore null subarrays */
			if (eisnull)
			{
				haveempty = true;
				continue;
			}

			array = DatumGetArrayTypeP(arraydatum);

			/* run-time double-check on element type */
			if (element_type != ARR_ELEMTYPE(array))
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("cannot merge incompatible arrays"),
						 errdetail("Array with element type %s cannot be "
								   "included in ARRAY construct with element type %s.",
								   format_type_be(ARR_ELEMTYPE(array)),
								   format_type_be(element_type))));

			this_ndims = ARR_NDIM(array);
			/* temporarily ignore zero-dimensional subarrays */
			if (this_ndims <= 0)
			{
				haveempty = true;
				continue;
			}

			if (firstone)
			{
				/* Get sub-array details from first member */
				elem_ndims = this_ndims;
				ndims = elem_ndims + 1;
				if (ndims <= 0 || ndims > MAXDIM)
					ereport(ERROR,
							(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
							 errmsg("number of array dimensions (%d) exceeds the maximum allowed (%d)",
									ndims, MAXDIM)));

				elem_dims = (int *) palloc(elem_ndims * sizeof(int));
				memcpy(elem_dims, ARR_DIMS(array), elem_ndims * sizeof(int));
				elem_lbs = (int *) palloc(elem_ndims * sizeof(int));
				memcpy(elem_lbs, ARR_LBOUND(array), elem_ndims * sizeof(int));

				firstone = false;
			}
			else
			{
				/* Check other sub-arrays are compatible */
				if (elem_ndims != this_ndims ||
					memcmp(elem_dims, ARR_DIMS(array),
						   elem_ndims * sizeof(int)) != 0 ||
					memcmp(elem_lbs, ARR_LBOUND(array),
						   elem_ndims * sizeof(int)) != 0)
					ereport(ERROR,
							(errcode(ERRCODE_ARRAY_SUBSCRIPT_ERROR),
							 errmsg("multidimensional arrays must have array "
									"expressions with matching dimensions")));
			}

			subdata[outer_nelems] = ARR_DATA_PTR(array);
			subbitmaps[outer_nelems] = ARR_NULLBITMAP(array);
			subbytes[outer_nelems] = ARR_SIZE(array) - ARR_DATA_OFFSET(array);
			nbytes += subbytes[outer_nelems];
			/* check for overflow of total request */
			if (!AllocSizeIsValid(nbytes))
				ereport(ERROR,
						(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
						 errmsg("array size exceeds the maximum allowed (%d)",
								(int) MaxAllocSize)));
			subnitems[outer_nelems] = ArrayGetNItems(this_ndims,
													 ARR_DIMS(array));
			havenulls |= ARR_HASNULL(array);
			outer_nelems++;
		}

		/*
		 * If all items were null or empty arrays, return an empty array;
		 * otherwise, if some were and some weren't, raise error.  (Note: we
		 * must special-case this somehow to avoid trying to generate a 1-D
		 * array formed from empty arrays.  It's not ideal...)
		 */
		if (haveempty)
		{
			if (ndims == 0)		/* didn't find any nonempty array */
			{
				*op->resvalue = PointerGetDatum(construct_empty_array(element_type));
				return;
			}
			ereport(ERROR,
					(errcode(ERRCODE_ARRAY_SUBSCRIPT_ERROR),
					 errmsg("multidimensional arrays must have array "
							"expressions with matching dimensions")));
		}

		/* setup for multi-D array */
		dims[0] = outer_nelems;
		lbs[0] = 1;
		for (int i = 1; i < ndims; i++)
		{
			dims[i] = elem_dims[i - 1];
			lbs[i] = elem_lbs[i - 1];
		}

		/* check for subscript overflow */
		nitems = ArrayGetNItems(ndims, dims);
		ArrayCheckBounds(ndims, dims, lbs);

		if (havenulls)
		{
			dataoffset = ARR_OVERHEAD_WITHNULLS(ndims, nitems);
			nbytes += dataoffset;
		}
		else
		{
			dataoffset = 0;		/* marker for no null bitmap */
			nbytes += ARR_OVERHEAD_NONULLS(ndims);
		}

		result = (ArrayType *) palloc0(nbytes);
		SET_VARSIZE(result, nbytes);
		result->ndim = ndims;
		result->dataoffset = dataoffset;
		result->elemtype = element_type;
		memcpy(ARR_DIMS(result), dims, ndims * sizeof(int));
		memcpy(ARR_LBOUND(result), lbs, ndims * sizeof(int));

		dat = ARR_DATA_PTR(result);
		iitem = 0;
		for (int i = 0; i < outer_nelems; i++)
		{
			memcpy(dat, subdata[i], subbytes[i]);
			dat += subbytes[i];
			if (havenulls)
				array_bitmap_copy(ARR_NULLBITMAP(result), iitem,
								  subbitmaps[i], 0,
								  subnitems[i]);
			iitem += subnitems[i];
		}
	}

	*op->resvalue = PointerGetDatum(result);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalArrayCoerce —— 数组类型转换（ArrayCoerceExpr）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对源数组（在 *op->resvalue）执行元素级类型转换：二进制兼容时仅改写
 *   数组头部的元素类型 OID；否则用 array_map 对每个元素应用元素转换
 *   表达式（elemexprstate）。
 *
 * 设计思想：
 *   1. 两条路径的选择由编译期决定（elemexprstate 是否生成）：
 *      - NULL（二进制兼容）：转换只涉及"类型标记"，物理布局不变——
 *        只 detoast+拷贝（DatumGetArrayTypePCopy 保证后续改写头部不污染
 *        原 datum）后改 ARR_ELEMTYPE；
 *      - 非 NULL：需要真正的逐元素转换，array_map 复用元素表达式
 *        状态（elemexprstate 已在 ExecInitExpr 编译好，amstate 为
 *        ArrayMapState 缓存），避免为每个数组重新初始化。
 *   2. NULL 数组原样返回 NULL（resnull 已置位，直接 return）。
 *   3. 典型场景：隐式/显式的元素类型提升（如 int[] -> bigint[]、
 *      varchar[] -> text[]），以及聚合函数中对数组参数的归并转换。
 * ============================================================================
 */
void
ExecEvalArrayCoerce(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	Datum		arraydatum;

	/* NULL array -> NULL result */
	if (*op->resnull)
		return;

	arraydatum = *op->resvalue;

	/*
	 * If it's binary-compatible, modify the element type in the array header,
	 * but otherwise leave the array as we received it.
	 */
	if (op->d.arraycoerce.elemexprstate == NULL)
	{
		/* Detoast input array if necessary, and copy in any case */
		ArrayType  *array = DatumGetArrayTypePCopy(arraydatum);

		ARR_ELEMTYPE(array) = op->d.arraycoerce.resultelemtype;
		*op->resvalue = PointerGetDatum(array);
		return;
	}

	/*
	 * Use array_map to apply the sub-expression to each array element.
	 */
	*op->resvalue = array_map(arraydatum,
							  op->d.arraycoerce.elemexprstate,
							  econtext,
							  op->d.arraycoerce.resultelemtype,
							  op->d.arraycoerce.amstate);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalRow —— ROW(...) 行构造
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   用编译期备好的行描述符（op->d.row.tupdesc）把已求值字段
 *   （elemvalues/elemnulls，前置 step 逐字段写入）经 heap_form_tuple
 *   组装为复合类型 Datum。
 *
 * 设计思想：
 *   1. 列值已在解释器主循环中逐个求值并写入预分配数组，本函数只做
 *      一次"打包"，因此体积极小、语义清晰。
 *   2. heap_form_tuple 负责按描述符的物理属性（typbyval/typlen/对齐）
 *      布置元组并生成 NULL 位图；结果是非 NULL 复合值（resnull=false）。
 *   3. 典型场景：SELECT ROW(a, b)、行比较/行 IN 的操作数、INSERT 的
 *      行值构造、把若干列当复合参数传给函数等。
 * ============================================================================
 */
void
ExecEvalRow(ExprState *state, ExprEvalStep *op)
{
	HeapTuple	tuple;

	/* build tuple from evaluated field values */
	tuple = heap_form_tuple(op->d.row.tupdesc,
							op->d.row.elemvalues,
							op->d.row.elemnulls);

	*op->resvalue = HeapTupleGetDatum(tuple);
	*op->resnull = false;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalMinMax —— GREATEST / LEAST 多值极值（注意非聚合）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对全部已求值输入（values/nulls 数组）用类型比较函数两两比较，
 *   挑选最大（GREATEST）或最小（LEAST）值；NULL 输入被忽略，全部为
 *   NULL 时结果为 NULL。
 *
 * 设计思想：
 *   1. 与聚合 MIN/MAX 的区别：这里是"标量值集合的极值"语义——NULL
 *      直接跳过（不是"未知"参与排序），只从非 NULL 值中选；全部为
 *      NULL 才返回 NULL。
 *   2. 性能：结果寄存器先置 NULL（作为"尚无候选"标志），首个非 NULL
 *      输入直接采纳，之后每来一个输入与当前极值比较并替换——单遍
 *      O(n)，比较函数复用编译期备好的 fcinfo（两参数槽复用）。
 *   3. 比较函数返回 NULL 被视为"不应发生"的防御：跳过该输入继续。
 * ============================================================================
 */
void
ExecEvalMinMax(ExprState *state, ExprEvalStep *op)
{
	Datum	   *values = op->d.minmax.values;
	bool	   *nulls = op->d.minmax.nulls;
	FunctionCallInfo fcinfo = op->d.minmax.fcinfo_data;
	MinMaxOp	operator = op->d.minmax.op;

	/* set at initialization */
	Assert(fcinfo->args[0].isnull == false);
	Assert(fcinfo->args[1].isnull == false);

	/* default to null result */
	*op->resnull = true;

	for (int off = 0; off < op->d.minmax.nelems; off++)
	{
		/* ignore NULL inputs */
		if (nulls[off])
			continue;

		if (*op->resnull)
		{
			/* first nonnull input, adopt value */
			*op->resvalue = values[off];
			*op->resnull = false;
		}
		else
		{
			int			cmpresult;

			/* apply comparison function */
			fcinfo->args[0].value = *op->resvalue;
			fcinfo->args[1].value = values[off];

			fcinfo->isnull = false;
			cmpresult = DatumGetInt32(FunctionCallInvoke(fcinfo));
			if (fcinfo->isnull) /* probably should not happen */
				continue;

			if (cmpresult > 0 && operator == IS_LEAST)
				*op->resvalue = values[off];
			else if (cmpresult < 0 && operator == IS_GREATEST)
				*op->resvalue = values[off];
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalFieldSelect —— 复合类型取字段（(row_expr).col）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从结果寄存器中的复合 Datum 取出 fieldnum 指定字段并覆写回结果
 *   寄存器；支持普通堆元组复合值与被 detoast 的展开记录（expanded
 *   record）两种形态。
 *
 * 设计思想：
 *   1. NULL 复合值 → NULL 字段结果，直接返回。
 *   2. 展开记录快速路径：VARATT_IS_EXTERNAL_EXPANDED 检测后直接
 *      expanded_record_get_field，零拷贝取字段（避免先物化为堆元组）。
 *   3. 普通路径：HeapTupleHeader 上按行类型描述符用 heap_getattr 取，
 *      描述符经 get_cached_rowtype 缓存（DDL 后自动重查）。
 *   4. 防御检查：不支持系统列（复合 Datum 里多数系统列无意义）；
 *      被 DROP 的列返回 NULL（不是错误——编译期就允许引用丢弃列，
 *      运行期遇到按"该列值视为 NULL"处理）；类型漂移
 *      （ALTER COLUMN TYPE 后）报 DATATYPE_MISMATCH；typmod 有意不查
 *      （与 CheckVarSlotCompatibility 同理）。
 * ============================================================================
 */
void
ExecEvalFieldSelect(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	AttrNumber	fieldnum = op->d.fieldselect.fieldnum;
	Datum		tupDatum;
	HeapTupleHeader tuple;
	Oid			tupType;
	int32		tupTypmod;
	TupleDesc	tupDesc;
	Form_pg_attribute attr;
	HeapTupleData tmptup;

	/* NULL record -> NULL result */
	if (*op->resnull)
		return;

	tupDatum = *op->resvalue;

	/* We can special-case expanded records for speed */
	if (VARATT_IS_EXTERNAL_EXPANDED(DatumGetPointer(tupDatum)))
	{
		ExpandedRecordHeader *erh = (ExpandedRecordHeader *) DatumGetEOHP(tupDatum);

		Assert(erh->er_magic == ER_MAGIC);

		/* Extract record's TupleDesc */
		tupDesc = expanded_record_get_tupdesc(erh);

		/*
		 * Find field's attr record.  Note we don't support system columns
		 * here: a datum tuple doesn't have valid values for most of the
		 * interesting system columns anyway.
		 */
		if (fieldnum <= 0)		/* should never happen */
			elog(ERROR, "unsupported reference to system column %d in FieldSelect",
				 fieldnum);
		if (fieldnum > tupDesc->natts)	/* should never happen */
			elog(ERROR, "attribute number %d exceeds number of columns %d",
				 fieldnum, tupDesc->natts);
		attr = TupleDescAttr(tupDesc, fieldnum - 1);

		/* Check for dropped column, and force a NULL result if so */
		if (attr->attisdropped)
		{
			*op->resnull = true;
			return;
		}

		/* Check for type mismatch --- possible after ALTER COLUMN TYPE? */
		/* As in CheckVarSlotCompatibility, we should but can't check typmod */
		if (op->d.fieldselect.resulttype != attr->atttypid)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("attribute %d has wrong type", fieldnum),
					 errdetail("Table has type %s, but query expects %s.",
							   format_type_be(attr->atttypid),
							   format_type_be(op->d.fieldselect.resulttype))));

		/* extract the field */
		*op->resvalue = expanded_record_get_field(erh, fieldnum,
												  op->resnull);
	}
	else
	{
		/* Get the composite datum and extract its type fields */
		tuple = DatumGetHeapTupleHeader(tupDatum);

		tupType = HeapTupleHeaderGetTypeId(tuple);
		tupTypmod = HeapTupleHeaderGetTypMod(tuple);

		/* Lookup tupdesc if first time through or if type changes */
		tupDesc = get_cached_rowtype(tupType, tupTypmod,
									 &op->d.fieldselect.rowcache, NULL);

		/*
		 * Find field's attr record.  Note we don't support system columns
		 * here: a datum tuple doesn't have valid values for most of the
		 * interesting system columns anyway.
		 */
		if (fieldnum <= 0)		/* should never happen */
			elog(ERROR, "unsupported reference to system column %d in FieldSelect",
				 fieldnum);
		if (fieldnum > tupDesc->natts)	/* should never happen */
			elog(ERROR, "attribute number %d exceeds number of columns %d",
				 fieldnum, tupDesc->natts);
		attr = TupleDescAttr(tupDesc, fieldnum - 1);

		/* Check for dropped column, and force a NULL result if so */
		if (attr->attisdropped)
		{
			*op->resnull = true;
			return;
		}

		/* Check for type mismatch --- possible after ALTER COLUMN TYPE? */
		/* As in CheckVarSlotCompatibility, we should but can't check typmod */
		if (op->d.fieldselect.resulttype != attr->atttypid)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("attribute %d has wrong type", fieldnum),
					 errdetail("Table has type %s, but query expects %s.",
							   format_type_be(attr->atttypid),
							   format_type_be(op->d.fieldselect.resulttype))));

		/* heap_getattr needs a HeapTuple not a bare HeapTupleHeader */
		tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
		tmptup.t_data = tuple;

		/* extract the field */
		*op->resvalue = heap_getattr(&tmptup,
									 fieldnum,
									 tupDesc,
									 op->resnull);
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalFieldStoreDeForm —— FieldStore 前半步：源行变形到数组
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把结果寄存器中的源复合值变形（deform）到 step 的
 *   d.fieldstore.values/nulls 数组中，为后续"逐字段求新值并覆写"做
 *   准备；源值为 NULL 时直接把整个数组置为全 NULL（等价于"由 NULL
 *   行改写各字段"）。
 *
 * 设计思想：
 *   1. FieldStore 是两步流水线（与 ROW 构造配合实现复合列赋值）：
 *      DEFORM 展开旧值 → 中间的 FIELD_* step 求新字段值并覆写数组
 *      元素 → FORMAT 阶段 heap_form_tuple 重装（见 ExecEvalFieldStoreForm）。
 *   2. 行类型描述符经 get_cached_rowtype 按结果类型缓存；DESCRIPTOR
 *      列数超过编译期分配上限时 elog 内部错误（DDL 增列但计划未失效
 *      的兜底，正常情况下不会发生）。
 *   3. detoast 顺序注意：先 DatumGetHeapTupleHeader 再查描述符——查
 *      描述符可能触发缓存失效导致数据库访问，而 detoast 也可能访问
 *      数据库；注释明确要求不得颠倒这两步。
 * ============================================================================
 */
void
ExecEvalFieldStoreDeForm(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	if (*op->resnull)
	{
		/* Convert null input tuple into an all-nulls row */
		memset(op->d.fieldstore.nulls, true,
			   op->d.fieldstore.ncolumns * sizeof(bool));
	}
	else
	{
		/*
		 * heap_deform_tuple needs a HeapTuple not a bare HeapTupleHeader. We
		 * set all the fields in the struct just in case.
		 */
		Datum		tupDatum = *op->resvalue;
		HeapTupleHeader tuphdr;
		HeapTupleData tmptup;
		TupleDesc	tupDesc;

		tuphdr = DatumGetHeapTupleHeader(tupDatum);
		tmptup.t_len = HeapTupleHeaderGetDatumLength(tuphdr);
		ItemPointerSetInvalid(&(tmptup.t_self));
		tmptup.t_tableOid = InvalidOid;
		tmptup.t_data = tuphdr;

		/*
		 * Lookup tupdesc if first time through or if type changes.  Because
		 * we don't pin the tupdesc, we must not do this lookup until after
		 * doing DatumGetHeapTupleHeader: that could do database access while
		 * detoasting the datum.
		 */
		tupDesc = get_cached_rowtype(op->d.fieldstore.fstore->resulttype, -1,
									 op->d.fieldstore.rowcache, NULL);

		/* Check that current tupdesc doesn't have more fields than allocated */
		if (unlikely(tupDesc->natts > op->d.fieldstore.ncolumns))
			elog(ERROR, "too many columns in composite type %u",
				 op->d.fieldstore.fstore->resulttype);

		heap_deform_tuple(&tmptup, tupDesc,
						  op->d.fieldstore.values,
						  op->d.fieldstore.nulls);
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalFieldStoreForm —— FieldStore 后半步：重装新复合值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在 DEFORM 展开的数组被各字段新值覆写完成后，用 heap_form_tuple
 *   按结果类型描述符重新组装复合 Datum 并写回结果寄存器。
 *
 * 设计思想：
 *   与 ExecEvalFieldStoreDeForm 严格配对（共用同一 rowcache、同一
 *   values/nulls 数组）；描述符此时应已在 DEFORM 阶段缓存过
 *   （"should be valid already"），这里再查一次是廉价防御。组装结果
 *   恒非 NULL。典型场景：UPDATE 语句对复合列（如 whole-row 字段、
 *   域上复合）的部分字段赋值。
 * ============================================================================
 */
void
ExecEvalFieldStoreForm(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	TupleDesc	tupDesc;
	HeapTuple	tuple;

	/* Lookup tupdesc (should be valid already) */
	tupDesc = get_cached_rowtype(op->d.fieldstore.fstore->resulttype, -1,
								 op->d.fieldstore.rowcache, NULL);

	tuple = heap_form_tuple(tupDesc,
							op->d.fieldstore.values,
							op->d.fieldstore.nulls);

	*op->resvalue = HeapTupleGetDatum(tuple);
	*op->resnull = false;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalConvertRowtype —— 行类型转换（ConvertRowtypeExpr）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把结果寄存器中的行 Datum 从 inputtype 转为 outputtype：按属性名
 *   建立映射重排字段（execute_attr_map_tuple），或物理布局兼容时仅重打
 *   复合头类型标记；结果写回结果寄存器。
 *
 * 设计思想：
 *   1. 使用场景：显式 ::rowtype 转换、继承/分区子父表行互转、以及
 *      planner 为整行传参插的类型转换。
 *   2. 懒构建映射：convert_tuples_by_name 在首次（或类型缓存失效后）
 *      才构建，缓存在 step 的 map 字段（分配在 per-query 内存，跨行
 *      复用）；描述符每次用 get_cached_rowtype 取，返回前
 *      IncrTupleDescRefCount 加 pin（转换函数可能做目录查询触发缓存
 *      失效），用完后 DecrTupleDescRefCount 释放。
 *   3. 双路径：map 非 NULL → 完整重排拷贝；map 为 NULL（按名即按物理
 *      顺序兼容）→ heap_copy_tuple_as_datum 拷贝并重打正确的行类型头
 *      （复合头里必须含目标类型 OID，因此物理兼容也必须拷贝）。
 *   4. 弱化断言：输入行可能是 RECORDOID（整行 Var 别名化后），因此只
 *      断言"输入类型 == 期望或 RECORD"。
 * ============================================================================
 */
void
ExecEvalConvertRowtype(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	HeapTuple	result;
	Datum		tupDatum;
	HeapTupleHeader tuple;
	HeapTupleData tmptup;
	TupleDesc	indesc,
				outdesc;
	bool		changed = false;

	/* NULL in -> NULL out */
	if (*op->resnull)
		return;

	tupDatum = *op->resvalue;
	tuple = DatumGetHeapTupleHeader(tupDatum);

	/*
	 * Lookup tupdescs if first time through or if type changes.  We'd better
	 * pin them since type conversion functions could do catalog lookups and
	 * hence cause cache invalidation.
	 */
	indesc = get_cached_rowtype(op->d.convert_rowtype.inputtype, -1,
								op->d.convert_rowtype.incache,
								&changed);
	IncrTupleDescRefCount(indesc);
	outdesc = get_cached_rowtype(op->d.convert_rowtype.outputtype, -1,
								 op->d.convert_rowtype.outcache,
								 &changed);
	IncrTupleDescRefCount(outdesc);

	/*
	 * We used to be able to assert that incoming tuples are marked with
	 * exactly the rowtype of indesc.  However, now that ExecEvalWholeRowVar
	 * might change the tuples' marking to plain RECORD due to inserting
	 * aliases, we can only make this weak test:
	 */
	Assert(HeapTupleHeaderGetTypeId(tuple) == indesc->tdtypeid ||
		   HeapTupleHeaderGetTypeId(tuple) == RECORDOID);

	/* if first time through, or after change, initialize conversion map */
	if (changed)
	{
		MemoryContext old_cxt;

		/* allocate map in long-lived memory context */
		old_cxt = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);

		/* prepare map from old to new attribute numbers */
		op->d.convert_rowtype.map = convert_tuples_by_name(indesc, outdesc);

		MemoryContextSwitchTo(old_cxt);
	}

	/* Following steps need a HeapTuple not a bare HeapTupleHeader */
	tmptup.t_len = HeapTupleHeaderGetDatumLength(tuple);
	tmptup.t_data = tuple;

	if (op->d.convert_rowtype.map != NULL)
	{
		/* Full conversion with attribute rearrangement needed */
		result = execute_attr_map_tuple(&tmptup, op->d.convert_rowtype.map);
		/* Result already has appropriate composite-datum header fields */
		*op->resvalue = HeapTupleGetDatum(result);
	}
	else
	{
		/*
		 * The tuple is physically compatible as-is, but we need to insert the
		 * destination rowtype OID in its composite-datum header field, so we
		 * have to copy it anyway.  heap_copy_tuple_as_datum() is convenient
		 * for this since it will both make the physical copy and insert the
		 * correct composite header fields.  Note that we aren't expecting to
		 * have to flatten any toasted fields: the input was a composite
		 * datum, so it shouldn't contain any.  So heap_copy_tuple_as_datum()
		 * is overkill here, but its check for external fields is cheap.
		 */
		*op->resvalue = heap_copy_tuple_as_datum(&tmptup, outdesc);
	}

	DecrTupleDescRefCount(indesc);
	DecrTupleDescRefCount(outdesc);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalScalarArrayOp —— 标量 op ANY/ALL（数组）求值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对数组的每个元素应用二元操作符（fcinfo->args[0] 为标量、args[1]
 *   逐元素填入），结果恒为布尔：ANY 用 OR 合并、ALL 用 AND 合并，
 *   可中途短路。
 *
 * 设计思想：
 *   1. 快捷路径：数组为 NULL → 结果 NULL（哪怕操作符非严格）；空数组
 *      → ANY 为 FALSE、ALL 为 TRUE（对零个元素"存在性"的空洞结论，
 *      即使标量为 NULL 也不影响）；严格操作符且标量为 NULL → NULL
 *      （免去空转循环）。
 *   2. 元素遍历（ExecEvalArrayCompareInternal）：手动按 typlen/typbyval/
 *      typalign 行走数据区 + NULL 位图（fetch_att 式），避免把元素
 *      逐一出队为 Datum 数组；元素类型信息首次遇到时
 *      get_typlenbyvalalign 缓存（元素类型运行期漂移自动重查）。
 *   3. 短路：OR 一旦得到 TRUE、ALL 一旦得到 FALSE 立即退出循环；
 *      元素比较返回 NULL 时置 resultnull（三值逻辑：只有出现反例或
 *      全部定论才覆盖 NULL）。
 * ============================================================================
 */
void
ExecEvalScalarArrayOp(ExprState *state, ExprEvalStep *op)
{
	FunctionCallInfo fcinfo = op->d.scalararrayop.fcinfo_data;
	bool		useOr = op->d.scalararrayop.useOr;
	bool		strictfunc = op->d.scalararrayop.finfo->fn_strict;
	ArrayType  *arr;
	int			nitems;
	Datum		result;
	bool		resultnull;

	/*
	 * If the array is NULL then we return NULL --- it's not very meaningful
	 * to do anything else, even if the operator isn't strict.
	 */
	if (*op->resnull)
		return;

	/* Else okay to fetch and detoast the array */
	arr = DatumGetArrayTypeP(*op->resvalue);

	/*
	 * If the array is empty, we return either FALSE or TRUE per the useOr
	 * flag.  This is correct even if the scalar is NULL; since we would
	 * evaluate the operator zero times, it matters not whether it would want
	 * to return NULL.
	 */
	nitems = ArrayGetNItems(ARR_NDIM(arr), ARR_DIMS(arr));
	if (nitems <= 0)
	{
		*op->resvalue = BoolGetDatum(!useOr);
		*op->resnull = false;
		return;
	}

	/*
	 * If the scalar is NULL, and the function is strict, return NULL; no
	 * point in iterating the loop.
	 */
	if (fcinfo->args[0].isnull && strictfunc)
	{
		*op->resnull = true;
		return;
	}

	/*
	 * We arrange to look up info about the element type only once per series
	 * of calls, assuming the element type doesn't change underneath us.
	 */
	if (op->d.scalararrayop.element_type != ARR_ELEMTYPE(arr))
	{
		get_typlenbyvalalign(ARR_ELEMTYPE(arr),
							 &op->d.scalararrayop.typlen,
							 &op->d.scalararrayop.typbyval,
							 &op->d.scalararrayop.typalign);
		op->d.scalararrayop.element_type = ARR_ELEMTYPE(arr);
	}

	ExecEvalArrayCompareInternal(fcinfo,
								 arr,
								 op->d.scalararrayop.typlen,
								 op->d.scalararrayop.typbyval,
								 op->d.scalararrayop.typalign,
								 useOr,
								 &result,
								 &resultnull);

	*op->resvalue = result;
	*op->resnull = resultnull;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalArrayCompareInternal —— 数组逐元素比较的公共内联实现
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   在数组数据区上直接遍历元素，逐个调用比较函数并按 useOr（OR=ANY /
 *   AND=ALL）合并结果到 *result 与 *resultnull，支持短路。
 *
 * 参数：
 *   fcinfo     - 比较函数调用信息（args[0]=标量，args[1] 每轮填元素）。
 *   arr        - 源数组（已 detoast）。
 *   typlen/typbyval/typalign - 元素类型的物理属性（调用方已按元素类型备好）。
 *   useOr      - true=ANY(OR) / false=ALL(AND)。
 *   result/resultnull - 输出：合并后的布尔结果与 NULL 标志。
 *
 * 设计思想：
 *   1. 双调用方共享：ExecEvalScalarArrayOp（常规 ANY/ALL）与
 *      ExecEvalHashedScalarArrayOp 构建哈希表时对 NULL 左值的预扫描。
 *      调用方必须已处理"严格函数 + 标量 NULL"的快路径。
 *   2. 零装箱遍历：直接在数组数据区按对齐步长行走（fetch_att +
 *      att_nominal_alignby），NULL 元素从位图判定；避免构造元素数组，
 *      是解释器里极少数"手写内存行走"的热路径之一。
 *   3. 三值合并：任何一次比较返回 NULL → 记 resultnull；一旦出现与
 *      useOr 矛盾的确定结果（OR 得 TRUE / AND 得 FALSE）即短路返回；
 *      全循环无矛盾时 *result 保持初值（OR 初 FALSE、AND 初 TRUE），
 *      仅当存在 NULL 结果时才输出 NULL。
 *   4. 严格性：元素为 NULL 且函数严格时跳过调用直接视为 NULL 结果。
 * ============================================================================
 */
static pg_always_inline void
ExecEvalArrayCompareInternal(FunctionCallInfo fcinfo, ArrayType *arr,
							 int16 typlen, bool typbyval, char typalign,
							 bool useOr, Datum *result, bool *resultnull)
{
	uint8		typalignby = typalign_to_alignby(typalign);
	int			nitems;
	char	   *s;
	uint8	   *bitmap;
	int			bitmask;
	bool		strictfunc = fcinfo->flinfo->fn_strict;

	nitems = ArrayGetNItems(ARR_NDIM(arr), ARR_DIMS(arr));

	/* Initialize result appropriately depending on useOr */
	*result = BoolGetDatum(!useOr);
	*resultnull = false;

	/* Loop over the array elements */
	s = (char *) ARR_DATA_PTR(arr);
	bitmap = ARR_NULLBITMAP(arr);
	bitmask = 1;

	for (int i = 0; i < nitems; i++)
	{
		Datum		elt;
		Datum		thisresult;

		/* Get array element, checking for NULL */
		if (bitmap && (*bitmap & bitmask) == 0)
		{
			fcinfo->args[1].value = (Datum) 0;
			fcinfo->args[1].isnull = true;
		}
		else
		{
			elt = fetch_att(s, typbyval, typlen);
			s = att_addlength_pointer(s, typlen, s);
			s = (char *) att_nominal_alignby(s, typalignby);
			fcinfo->args[1].value = elt;
			fcinfo->args[1].isnull = false;
		}

		/* Call comparison function */
		if (fcinfo->args[1].isnull && strictfunc)
		{
			fcinfo->isnull = true;
			thisresult = (Datum) 0;
		}
		else
		{
			fcinfo->isnull = false;
			thisresult = fcinfo->flinfo->fn_addr(fcinfo);
		}

		/* Combine results per OR or AND semantics */
		if (fcinfo->isnull)
			*resultnull = true;
		else if (useOr)
		{
			if (DatumGetBool(thisresult))
			{
				*result = BoolGetDatum(true);
				*resultnull = false;
				break;			/* needn't look at any more elements */
			}
		}
		else
		{
			if (!DatumGetBool(thisresult))
			{
				*result = BoolGetDatum(false);
				*resultnull = false;
				break;			/* needn't look at any more elements */
			}
		}

		/* advance bitmap pointer if any */
		if (bitmap)
		{
			bitmask <<= 1;
			if (bitmask == 0x100)
			{
				bitmap++;
				bitmask = 1;
			}
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】saop_element_hash / saop_hash_element_match —— 哈希标量数组
 *              操作的元素哈希与相等回调
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   供 simplehash 哈希表使用的两个回调：
 *   saop_element_hash 用元素类型默认哈希函数（含 collation 敏感列的
 *   列排序规则）计算数组元素哈希；saop_hash_element_match 用相等函数
 *   判定两个元素是否相等。
 *
 * 设计思想：
 *   1. 二者通过 tb->private_data 取回 ScalarArrayOpExprHashTable，其内含
 *      编译期备好的 hash_finfo/hash_fcinfo_data（哈希）与 op->d.
 *      hashedscalararrayop.fcinfo_data/finfo（相等），避免每次回调重建
 *      调用上下文。
 *   2. 哈希表元素只存 Datum（不存 NULL），NULL 用 has_nulls 标志单独
 *      处理（见 ExecEvalHashedScalarArrayOp）——因此回调里从不出现
 *      NULL 键，isnull 恒置 false。
 *   3. 相等回调与 SQL IN 语义完全一致：数组元素与标量用运算符相等性
 *      判定，结果即 IN/NOT IN 的查表依据。
 * ============================================================================
 */
static uint32
saop_element_hash(struct saophash_hash *tb, Datum key)
{
	ScalarArrayOpExprHashTable *elements_tab = (ScalarArrayOpExprHashTable *) tb->private_data;
	FunctionCallInfo fcinfo = &elements_tab->hash_fcinfo_data;
	Datum		hash;

	fcinfo->args[0].value = key;
	fcinfo->args[0].isnull = false;

	hash = elements_tab->hash_finfo.fn_addr(fcinfo);

	return DatumGetUInt32(hash);
}

/* 同 saop_element_hash 中文注释：相等回调（哈希表查表用） */
static bool
saop_hash_element_match(struct saophash_hash *tb, Datum key1, Datum key2)
{
	Datum		result;

	ScalarArrayOpExprHashTable *elements_tab = (ScalarArrayOpExprHashTable *) tb->private_data;
	FunctionCallInfo fcinfo = elements_tab->op->d.hashedscalararrayop.fcinfo_data;

	fcinfo->args[0].value = key1;
	fcinfo->args[0].isnull = false;
	fcinfo->args[1].value = key2;
	fcinfo->args[1].isnull = false;

	result = elements_tab->op->d.hashedscalararrayop.finfo->fn_addr(fcinfo);

	return DatumGetBool(result);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalHashedScalarArrayOp —— 常量数组的 IN/NOT IN 哈希化求值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   求值 "标量 op ANY（常量数组）"（编译器保证数组是常量且非 NULL）：
 *   首次求值时把数组元素建成哈希表（per-query 内存，后续行复用），
 *   之后每行 O(1) 查表得到 IN/NOT IN 布尔结果；NULL 与严格性语义单独
 *   处理。
 *
 * 设计思想：
 *   1. 与 ExecEvalScalarArrayOp 的分工：后者对任意数组逐元素比较
 *      （每行 O(n)）；本函数针对"同一常量数组作用于每行"的形态
 *      （典型如 x IN (1,2,3)），用哈希把每行代价降到 O(1)。
 *   2. 建表细节（首行）：
 *      - 数组元素逐个 fetch_att 行走插入 simplehash，NULL 不进表而是
 *        记 has_nulls 标志；
 *      - 哈希/相等函数信息与调用上下文在 per-query 内存一次性建好
 *        （fmgr_info + InitFunctionCallInfoData），跨行复用；
 *      - 容量按元素数预分配（假定无重复，重复只会让表略大）。
 *   3. NULL 语义（三路）：
 *      - 严格函数 + 标量 NULL → 结果 NULL（不查表）；
 *      - 非严格函数 + 标量 NULL：用缓存的 null_lhs_result（建表时用
 *        线性扫描 ExecEvalArrayCompareInternal 对"NULL 左值"预评估
 *        并缓存——非严格函数可能把 NULL 当作与某些值相等！）；
 *      - 标量非 NULL、查表未命中但数组含 NULL：严格 → NULL（SQL 三值
 *        语义：元素 NULL 与标量的比较结果未知）；非严格 → 以 NULL 右值
 *        再调一次函数（结果按 NOT IN 翻转）。
 *   4. 结果翻转：NOT IN 是 IN 的布尔取反（hashfound 取反；函数比较
 *      路径再翻转一次相等结果）。
 * ============================================================================
 */
void
ExecEvalHashedScalarArrayOp(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	ScalarArrayOpExprHashTable *elements_tab = op->d.hashedscalararrayop.elements_tab;
	FunctionCallInfo fcinfo = op->d.hashedscalararrayop.fcinfo_data;
	bool		inclause = op->d.hashedscalararrayop.inclause;
	bool		strictfunc = op->d.hashedscalararrayop.finfo->fn_strict;
	Datum		scalar = fcinfo->args[0].value;
	bool		scalar_isnull = fcinfo->args[0].isnull;
	Datum		result;
	bool		resultnull;
	bool		hashfound;

	/* We don't setup a hashed scalar array op if the array const is null. */
	Assert(!*op->resnull);

	/*
	 * If the scalar is NULL, and the function is strict, return NULL; no
	 * point in executing the search.
	 */
	if (scalar_isnull && strictfunc)
	{
		*op->resnull = true;
		return;
	}

	/* Build the hash table on first evaluation */
	if (elements_tab == NULL)
	{
		ScalarArrayOpExpr *saop;
		int16		typlen;
		bool		typbyval;
		char		typalign;
		uint8		typalignby;
		int			nitems;
		bool		has_nulls = false;
		char	   *s;
		uint8	   *bitmap;
		int			bitmask;
		MemoryContext oldcontext;
		ArrayType  *arr;

		saop = op->d.hashedscalararrayop.saop;

		arr = DatumGetArrayTypeP(*op->resvalue);
		nitems = ArrayGetNItems(ARR_NDIM(arr), ARR_DIMS(arr));

		get_typlenbyvalalign(ARR_ELEMTYPE(arr),
							 &typlen,
							 &typbyval,
							 &typalign);
		typalignby = typalign_to_alignby(typalign);

		oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);

		elements_tab = (ScalarArrayOpExprHashTable *)
			palloc0(offsetof(ScalarArrayOpExprHashTable, hash_fcinfo_data) +
					SizeForFunctionCallInfo(1));
		op->d.hashedscalararrayop.elements_tab = elements_tab;
		elements_tab->op = op;

		fmgr_info(saop->hashfuncid, &elements_tab->hash_finfo);
		fmgr_info_set_expr((Node *) saop, &elements_tab->hash_finfo);

		InitFunctionCallInfoData(elements_tab->hash_fcinfo_data,
								 &elements_tab->hash_finfo,
								 1,
								 saop->inputcollid,
								 NULL,
								 NULL);

		/*
		 * Create the hash table sizing it according to the number of elements
		 * in the array.  This does assume that the array has no duplicates.
		 * If the array happens to contain many duplicate values then it'll
		 * just mean that we sized the table a bit on the large side.
		 */
		elements_tab->hashtab = saophash_create(CurrentMemoryContext, nitems,
												elements_tab);

		MemoryContextSwitchTo(oldcontext);

		s = (char *) ARR_DATA_PTR(arr);
		bitmap = ARR_NULLBITMAP(arr);
		bitmask = 1;
		for (int i = 0; i < nitems; i++)
		{
			/* Get array element, checking for NULL. */
			if (bitmap && (*bitmap & bitmask) == 0)
			{
				has_nulls = true;
			}
			else
			{
				Datum		element;

				element = fetch_att(s, typbyval, typlen);
				s = att_addlength_pointer(s, typlen, s);
				s = (char *) att_nominal_alignby(s, typalignby);

				saophash_insert(elements_tab->hashtab, element, &hashfound);
			}

			/* Advance bitmap pointer if any. */
			if (bitmap)
			{
				bitmask <<= 1;
				if (bitmask == 0x100)
				{
					bitmap++;
					bitmask = 1;
				}
			}
		}

		/*
		 * Remember if we had any nulls so that we know if we need to execute
		 * non-strict functions with a null lhs value if no match is found.
		 */
		op->d.hashedscalararrayop.has_nulls = has_nulls;

		/*
		 * When we have a non-strict equality function, check and cache the
		 * result from looking up a NULL.  Non-strict functions are free to
		 * treat a NULL as equal to any other value, e.g. a 0 or an empty
		 * string.  Here we perform a linear search over the array and cache
		 * the outcome so that we can use that result any time we receive a
		 * NULL.
		 */
		if (!strictfunc)
		{
			bool		null_lhs_result;

			fcinfo->args[0].value = (Datum) 0;
			fcinfo->args[0].isnull = true;

			ExecEvalArrayCompareInternal(fcinfo, arr, typlen, typbyval,
										 typalign, true, &result,
										 &resultnull);

			null_lhs_result = DatumGetBool(result);

			/* invert non-NULL results for NOT IN */
			if (!resultnull && !inclause)
				null_lhs_result = !null_lhs_result;

			op->d.hashedscalararrayop.null_lhs_isnull = resultnull;
			op->d.hashedscalararrayop.null_lhs_result = null_lhs_result;
		}
	}

	/*
	 * When looking up an SQL NULL value with non-strict functions, we defer
	 * to the value we cached when building the hash table.
	 */
	if (scalar_isnull)
	{
		Assert(!strictfunc);

		*op->resnull = op->d.hashedscalararrayop.null_lhs_isnull;
		*op->resvalue = BoolGetDatum(op->d.hashedscalararrayop.null_lhs_result);
		return;
	}


	/* Check the hash to see if we have a match. */
	hashfound = NULL != saophash_lookup(elements_tab->hashtab, scalar);

	/* the result depends on if the clause is an IN or NOT IN clause */
	if (inclause)
		result = BoolGetDatum(hashfound);	/* IN */
	else
		result = BoolGetDatum(!hashfound);	/* NOT IN */

	resultnull = false;

	/*
	 * If we didn't find a match in the array, we still might need to handle
	 * the possibility of null values.  We didn't put any NULLs into the
	 * hashtable, but instead marked if we found any when building the table
	 * in has_nulls.
	 */
	if (!hashfound && op->d.hashedscalararrayop.has_nulls)
	{
		if (strictfunc)
		{

			/*
			 * We have nulls in the array so a non-null lhs and no match must
			 * yield NULL.
			 */
			result = (Datum) 0;
			resultnull = true;
		}
		else
		{
			/*
			 * Execute function will null rhs just once.
			 *
			 * The hash lookup path will have scribbled on the lhs argument so
			 * we need to set it up also (even though we entered this function
			 * with it already set).
			 */
			fcinfo->args[0].value = scalar;
			fcinfo->args[0].isnull = scalar_isnull;
			fcinfo->args[1].value = (Datum) 0;
			fcinfo->args[1].isnull = true;

			result = op->d.hashedscalararrayop.finfo->fn_addr(fcinfo);
			resultnull = fcinfo->isnull;

			/*
			 * Reverse the result for NOT IN clauses since the above function
			 * is the equality function and we need not-equals.
			 */
			if (!inclause)
				result = BoolGetDatum(!DatumGetBool(result));
		}
	}

	*op->resvalue = result;
	*op->resnull = resultnull;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalConstraintNotNull —— 域（domain）NOT NULL 约束检查
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查结果寄存器中的域值是否为 NULL：若是，则按错误上下文
 *   （escontext）抛出 NOT NULL_VIOLATION 错误（硬错误或软错误，
 *   取决于调用方设置的 ErrorSaveContext）。
 *
 * 设计思想：
 *   1. 这是域类型检查流水线的一环：compile-time 已把域约束翻译成
 *      "计算约束表达式 + 本检查 step"；constraint/not null 检查以
 *      step 形式插入到 CAST 目标域类型的值之后。
 *   2. 使用 errsave() 走错误上下文：普通求值路径会抛 ERROR；
 *      而在 UPDATE 的软错误（soft error）场景（如 RETURNING 里触发的
 *      域约束失败仅需记录）可通过 escontext 捕获，配合 errdatatype
 *      给出域类型信息（hint 链）。
 * ============================================================================
 */
void
ExecEvalConstraintNotNull(ExprState *state, ExprEvalStep *op)
{
	if (*op->resnull)
		errsave((Node *) op->d.domaincheck.escontext,
				(errcode(ERRCODE_NOT_NULL_VIOLATION),
				 errmsg("domain %s does not allow null values",
						format_type_be(op->d.domaincheck.resulttype)),
				 errdatatype(op->d.domaincheck.resulttype)));
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalConstraintCheck —— 域（domain）CHECK 约束检查
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   前置 step 已把域 CHECK 约束表达式的值求入
 *   d.domaincheck.checkvalue/checknull；本函数判定失败条件：
 *   "约束表达式结果为 FALSE（且非 NULL）"即违反，通过 errsave()
 *   按 escontext 抛出 CHECK_VIOLATION（附约束名与域类型）。
 *
 * 设计思想：
 *   1. SQL 语义：约束表达式为 NULL 或 TRUE 均视为通过；只有显式
 *      FALSE 才违规（对应 CHECK 约束"未知不拒绝"的三值逻辑）。
 *   2. 配合 ExecEvalConstraintNotNull 构成域检查的两种 step；
 *      errdomainconstraint 提供 SQLSTATE/errdetail 的约束链信息。
 *   3. 软错误路径：由调用方（如 ExecEvalCoerceToDomain 场景下的
 *      赋值目标）决定是否捕获，实现 RETURNING 等场景的延迟报错。
 * ============================================================================
 */
void
ExecEvalConstraintCheck(ExprState *state, ExprEvalStep *op)
{
	if (!*op->d.domaincheck.checknull &&
		!DatumGetBool(*op->d.domaincheck.checkvalue))
		errsave((Node *) op->d.domaincheck.escontext,
				(errcode(ERRCODE_CHECK_VIOLATION),
				 errmsg("value for domain %s violates check constraint \"%s\"",
						format_type_be(op->d.domaincheck.resulttype),
						op->d.domaincheck.constraintname),
				 errdomainconstraint(op->d.domaincheck.resulttype,
									 op->d.domaincheck.constraintname)));
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalXmlExpr —— 各形态 XmlExpr（XML 构造/序列化/解析）求值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按 xexpr->op 分发执行 XML 语义：XMLCONCAT（拼接）、XMLFOREST
 *   （命名列转 XML 片段）、XMLELEMENT（构造元素）、XMLPARSE（文本
 *   解析为 xml）、XMLPI（处理指令）、XMLROOT（改根属性）、XMLSERIALIZE
 *   （序列化为文本）、IS_DOCUMENT（判定文档）。所有参数已由前置 step
 *   求值到 argvalue/argnull（无名）与 named_argvalue/named_argnull
 *   （命名）数组，结果写回结果寄存器。
 *
 * 设计思想：
 *   1. 这是"编译期翻译 + 运行期分派"的典型：XmlExpr 树解析于
 *      execExpr.c（命名参数与位置参数按名/序分类装入数组），本函数
 *      只做最终的语义化组装。
 *   2. NULL 传播遵循各形态规则：XMLFOREST/XMLELEMENT 遇 NULL 参数
 *      时跳过该列/子元素（保留其余）；XMLPARSE/XMLROOT/XMLSERIALIZE/
 *      IS_DOCUMENT 的参数为 NULL 时整个表达式结果为 NULL（return）。
 *   3. 安全细节：XMLFOREST 用 map_sql_value_to_xml_value 对每个值做
 *      类型化的 XML 转义；XMLSERIALIZE/XMLPARSE 用 xexpr 里编译期
 *      固化好的 xmloption（DOCUMENT/CONTENT）与 indent 开关。
 * ============================================================================
 */
void
ExecEvalXmlExpr(ExprState *state, ExprEvalStep *op)
{
	XmlExpr    *xexpr = op->d.xmlexpr.xexpr;
	Datum		value;

	*op->resnull = true;		/* until we get a result */
	*op->resvalue = (Datum) 0;

	switch (xexpr->op)
	{
		case IS_XMLCONCAT:
			{
				Datum	   *argvalue = op->d.xmlexpr.argvalue;
				bool	   *argnull = op->d.xmlexpr.argnull;
				List	   *values = NIL;

				for (int i = 0; i < list_length(xexpr->args); i++)
				{
					if (!argnull[i])
						values = lappend(values, DatumGetPointer(argvalue[i]));
				}

				if (values != NIL)
				{
					*op->resvalue = PointerGetDatum(xmlconcat(values));
					*op->resnull = false;
				}
			}
			break;

		case IS_XMLFOREST:
			{
				Datum	   *argvalue = op->d.xmlexpr.named_argvalue;
				bool	   *argnull = op->d.xmlexpr.named_argnull;
				StringInfoData buf;
				ListCell   *lc;
				ListCell   *lc2;
				int			i;

				initStringInfo(&buf);

				i = 0;
				forboth(lc, xexpr->named_args, lc2, xexpr->arg_names)
				{
					Expr	   *e = (Expr *) lfirst(lc);
					char	   *argname = strVal(lfirst(lc2));

					if (!argnull[i])
					{
						value = argvalue[i];
						appendStringInfo(&buf, "<%s>%s</%s>",
										 argname,
										 map_sql_value_to_xml_value(value,
																	exprType((Node *) e), true),
										 argname);
						*op->resnull = false;
					}
					i++;
				}

				if (!*op->resnull)
				{
					text	   *result;

					result = cstring_to_text_with_len(buf.data, buf.len);
					*op->resvalue = PointerGetDatum(result);
				}

				pfree(buf.data);
			}
			break;

		case IS_XMLELEMENT:
			*op->resvalue = PointerGetDatum(xmlelement(xexpr,
													   op->d.xmlexpr.named_argvalue,
													   op->d.xmlexpr.named_argnull,
													   op->d.xmlexpr.argvalue,
													   op->d.xmlexpr.argnull));
			*op->resnull = false;
			break;

		case IS_XMLPARSE:
			{
				Datum	   *argvalue = op->d.xmlexpr.argvalue;
				bool	   *argnull = op->d.xmlexpr.argnull;
				text	   *data;
				bool		preserve_whitespace;

				/* arguments are known to be text, bool */
				Assert(list_length(xexpr->args) == 2);

				if (argnull[0])
					return;
				value = argvalue[0];
				data = DatumGetTextPP(value);

				if (argnull[1]) /* probably can't happen */
					return;
				value = argvalue[1];
				preserve_whitespace = DatumGetBool(value);

				*op->resvalue = PointerGetDatum(xmlparse(data,
														 xexpr->xmloption,
														 preserve_whitespace, NULL));
				*op->resnull = false;
			}
			break;

		case IS_XMLPI:
			{
				text	   *arg;
				bool		isnull;

				/* optional argument is known to be text */
				Assert(list_length(xexpr->args) <= 1);

				if (xexpr->args)
				{
					isnull = op->d.xmlexpr.argnull[0];
					if (isnull)
						arg = NULL;
					else
						arg = DatumGetTextPP(op->d.xmlexpr.argvalue[0]);
				}
				else
				{
					arg = NULL;
					isnull = false;
				}

				*op->resvalue = PointerGetDatum(xmlpi(xexpr->name,
													  arg,
													  isnull,
													  op->resnull));
			}
			break;

		case IS_XMLROOT:
			{
				Datum	   *argvalue = op->d.xmlexpr.argvalue;
				bool	   *argnull = op->d.xmlexpr.argnull;
				xmltype    *data;
				text	   *version;
				int			standalone;

				/* arguments are known to be xml, text, int */
				Assert(list_length(xexpr->args) == 3);

				if (argnull[0])
					return;
				data = DatumGetXmlP(argvalue[0]);

				if (argnull[1])
					version = NULL;
				else
					version = DatumGetTextPP(argvalue[1]);

				Assert(!argnull[2]);	/* always present */
				standalone = DatumGetInt32(argvalue[2]);

				*op->resvalue = PointerGetDatum(xmlroot(data,
														version,
														standalone));
				*op->resnull = false;
			}
			break;

		case IS_XMLSERIALIZE:
			{
				Datum	   *argvalue = op->d.xmlexpr.argvalue;
				bool	   *argnull = op->d.xmlexpr.argnull;

				/* argument type is known to be xml */
				Assert(list_length(xexpr->args) == 1);

				if (argnull[0])
					return;
				value = argvalue[0];

				*op->resvalue =
					PointerGetDatum(xmltotext_with_options(DatumGetXmlP(value),
														   xexpr->xmloption,
														   xexpr->indent));
				*op->resnull = false;
			}
			break;

		case IS_DOCUMENT:
			{
				Datum	   *argvalue = op->d.xmlexpr.argvalue;
				bool	   *argnull = op->d.xmlexpr.argnull;

				/* optional argument is known to be xml */
				Assert(list_length(xexpr->args) == 1);

				if (argnull[0])
					return;
				value = argvalue[0];

				*op->resvalue =
					BoolGetDatum(xml_is_document(DatumGetXmlP(value)));
				*op->resnull = false;
			}
			break;

		default:
			elog(ERROR, "unrecognized XML operation");
			break;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalJsonConstructor —— JSON_ARRAY / JSON_OBJECT /
 *              JSON / JSON_SCALAR 构造表达式求值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按构造器类型（JSCTOR_JSON_ARRAY/OBJECT/SCALAR/PARSE）把已求值的
 *   参数数组（jcstate->arg_values/arg_nulls/arg_types）组装为 json 或
 *   jsonb 值，结果写回结果寄存器。
 *
 * 设计思想：
 *   1. 双格式统一：依据 RETURNING 子句的 format_type 选择 json_* 还是
 *      jsonb_* 系列 worker（如 jsonb_build_array_worker），编译期已在
 *      jcstate 备好输出函数（outfuncid）与类型分类（category）。
 *   2. 语义开关在构造器里固化：absent_on_null（NULL 参数在 ARRAY/
 *      OBJECT 中是否省略）与 unique（OBJECT 键唯一性校验）。
 *   3. JSON_SCALAR：把单个标量值经 datum_to_json(b) 序列化；参数为
 *      NULL 时结果为 SQL NULL。JSON_PARSE（即 JSON(...) 语法）：对
 *      text 输入做解析（jsonb 直接 jsonb_from_text；json 类型先
 *      json_validate 校验文本合法性，通过则原值返回）。
 * ============================================================================
 */
void
ExecEvalJsonConstructor(ExprState *state, ExprEvalStep *op,
						ExprContext *econtext)
{
	Datum		res;
	JsonConstructorExprState *jcstate = op->d.json_constructor.jcstate;
	JsonConstructorExpr *ctor = jcstate->constructor;
	bool		is_jsonb = ctor->returning->format->format_type == JS_FORMAT_JSONB;
	bool		isnull = false;

	if (ctor->type == JSCTOR_JSON_ARRAY)
		res = (is_jsonb ?
			   jsonb_build_array_worker :
			   json_build_array_worker) (jcstate->nargs,
										 jcstate->arg_values,
										 jcstate->arg_nulls,
										 jcstate->arg_types,
										 jcstate->constructor->absent_on_null);
	else if (ctor->type == JSCTOR_JSON_OBJECT)
		res = (is_jsonb ?
			   jsonb_build_object_worker :
			   json_build_object_worker) (jcstate->nargs,
										  jcstate->arg_values,
										  jcstate->arg_nulls,
										  jcstate->arg_types,
										  jcstate->constructor->absent_on_null,
										  jcstate->constructor->unique);
	else if (ctor->type == JSCTOR_JSON_SCALAR)
	{
		if (jcstate->arg_nulls[0])
		{
			res = (Datum) 0;
			isnull = true;
		}
		else
		{
			Datum		value = jcstate->arg_values[0];
			Oid			outfuncid = jcstate->arg_type_cache[0].outfuncid;
			JsonTypeCategory category = (JsonTypeCategory)
				jcstate->arg_type_cache[0].category;

			if (is_jsonb)
				res = datum_to_jsonb(value, category, outfuncid);
			else
				res = datum_to_json(value, category, outfuncid);
		}
	}
	else if (ctor->type == JSCTOR_JSON_PARSE)
	{
		if (jcstate->arg_nulls[0])
		{
			res = (Datum) 0;
			isnull = true;
		}
		else
		{
			Datum		value = jcstate->arg_values[0];
			text	   *js = DatumGetTextP(value);

			if (is_jsonb)
				res = jsonb_from_text(js, true);
			else
			{
				(void) json_validate(js, true, true);
				res = value;
			}
		}
	}
	else
		elog(ERROR, "invalid JsonConstructorExpr type %d", ctor->type);

	*op->resvalue = res;
	*op->resnull = isnull;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalJsonIsPredicate —— "IS JSON" 谓词求值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   判定结果寄存器中的值是否满足 "IS [NOT] JSON [OBJECT|ARRAY|SCALAR
 *   [WITH UNIQUE KEYS]]" 的指定类型与键唯一性要求，结果为布尔写回
 *   结果寄存器（原值已被本 step 结果覆盖）。
 *
 * 设计思想：
 *   1. 输入为 NULL → 结果 FALSE（SQL 谓词对 NULL 输入不返回 NULL，
 *      而是"不是 JSON"为假）。
 *   2. 按表达式基类型分流：text/json 走文本扫描
 *      （json_get_first_token 看首 token 定根类型，必要时再做一次
 *      json_validate 全量解析以支持 WITH UNIQUE KEYS 或 text 合法性）；
 *      jsonb 直接查根容器位（JB_ROOT_IS_*），键唯一性对 jsonb 是
 *      结构上恒成立的（构建时已保证），无需再校验。
 *   3. IS JSON ANY 是恒真快速路径（只要输入非 NULL 且类型为 JSON
 *      兼容类型）；不支持的类型一律 FALSE。
 * ============================================================================
 */
void
ExecEvalJsonIsPredicate(ExprState *state, ExprEvalStep *op)
{
	JsonIsPredicate *pred = op->d.is_json.pred;
	Datum		js = *op->resvalue;
	Oid			exprtype = pred->exprBaseType;
	bool		res;

	if (*op->resnull)
	{
		*op->resvalue = BoolGetDatum(false);
		return;
	}

	if (exprtype == TEXTOID || exprtype == JSONOID)
	{
		text	   *json = DatumGetTextP(js);

		if (pred->item_type == JS_TYPE_ANY)
			res = true;
		else
		{
			switch (json_get_first_token(json, false))
			{
				case JSON_TOKEN_OBJECT_START:
					res = pred->item_type == JS_TYPE_OBJECT;
					break;
				case JSON_TOKEN_ARRAY_START:
					res = pred->item_type == JS_TYPE_ARRAY;
					break;
				case JSON_TOKEN_STRING:
				case JSON_TOKEN_NUMBER:
				case JSON_TOKEN_TRUE:
				case JSON_TOKEN_FALSE:
				case JSON_TOKEN_NULL:
					res = pred->item_type == JS_TYPE_SCALAR;
					break;
				default:
					res = false;
					break;
			}
		}

		/*
		 * Do full parsing pass only for uniqueness check or for JSON text
		 * validation.
		 */
		if (res && (pred->unique_keys || exprtype == TEXTOID))
			res = json_validate(json, pred->unique_keys, false);
	}
	else if (exprtype == JSONBOID)
	{
		if (pred->item_type == JS_TYPE_ANY)
			res = true;
		else
		{
			Jsonb	   *jb = DatumGetJsonbP(js);

			switch (pred->item_type)
			{
				case JS_TYPE_OBJECT:
					res = JB_ROOT_IS_OBJECT(jb);
					break;
				case JS_TYPE_ARRAY:
					res = JB_ROOT_IS_ARRAY(jb) && !JB_ROOT_IS_SCALAR(jb);
					break;
				case JS_TYPE_SCALAR:
					res = JB_ROOT_IS_ARRAY(jb) && JB_ROOT_IS_SCALAR(jb);
					break;
				default:
					res = false;
					break;
			}
		}

		/* Key uniqueness check is redundant for jsonb */
	}
	else
		res = false;

	*op->resvalue = BoolGetDatum(res);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalJsonExprPath —— SQL/JSON 路径表达式核心求值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对已格式化的文档（jsestate->formatted_expr.value）执行
 *   jsonpath 查询，实现 JSON_EXISTS / JSON_QUERY / JSON_VALUE 三种
 *   操作；必要时用输入函数把结果强转成 RETURNING 类型；随后按
 *   ON EMPTY / ON ERROR 行为决定返回值或跳转目标。
 *
 * 返回值：
 *   下一个 step 的下标：jump_error、jump_empty、jump_eval_coercion
 *   或 jump_end（全部存于 op->d.jsonexpr.jsestate）；-1 语义为
 *   "顺序执行下一 step"。
 *
 * 设计思想：
 *   1. 软错误管道：throw_error=false 时 JsonPath 求值错误与强转错误
 *      不直接抛 ERROR，而是置 jsestate->error（NullableDatum）；
 *      后续 step（如 ExecEvalJsonCoercion）检查该标志决定返回
 *      ON ERROR 表达式的结果。
 *   2. ON EMPTY/ON ERROR 统一编排：empty/error 置位后，若配置了
 *      相应行为表达式则设置 ErrorSaveContext（details_wanted 以便
 *      报错信息带 DETAIL），跳转到行为表达式 step（jump_empty/
 *      jump_error）；行为为 NULL 时直接跳到 jump_end；行为为 ERROR
 *      或未配置则这里直接抛 NO_SQL_JSON_ITEM。
 *   3. 结果产出路径多样：JSON_VALUE 里，按 RETURNING 类型与
 *      是否 use_json_coercion/use_io_coercion 决定直接给 Jsonb、
 *      给序列化字符串、或留待 io 输入函数强转；每行开始时
 *      memset 复位 error/empty/escontext，保证行间不串状态。
 *   4. 每次调用都返回显式跳转下标，不依赖解释器顺序执行——这是
 *      少数需要"运行期决定控制流"的 step。
 * ============================================================================
 */
int
ExecEvalJsonExprPath(ExprState *state, ExprEvalStep *op,
					 ExprContext *econtext)
{
	JsonExprState *jsestate = op->d.jsonexpr.jsestate;
	JsonExpr   *jsexpr = jsestate->jsexpr;
	Datum		item;
	JsonPath   *path;
	bool		throw_error = jsexpr->on_error->btype == JSON_BEHAVIOR_ERROR;
	bool		error = false,
				empty = false;
	int			jump_eval_coercion = jsestate->jump_eval_coercion;
	char	   *val_string = NULL;

	item = jsestate->formatted_expr.value;
	path = DatumGetJsonPathP(jsestate->pathspec.value);

	/* Set error/empty to false. */
	memset(&jsestate->error, 0, sizeof(NullableDatum));
	memset(&jsestate->empty, 0, sizeof(NullableDatum));

	/* Also reset ErrorSaveContext contents for the next row. */
	if (jsestate->escontext.details_wanted)
	{
		jsestate->escontext.error_data = NULL;
		jsestate->escontext.details_wanted = false;
	}
	jsestate->escontext.error_occurred = false;

	switch (jsexpr->op)
	{
		case JSON_EXISTS_OP:
			{
				bool		exists = JsonPathExists(item, path,
													!throw_error ? &error : NULL,
													jsestate->args);

				if (!error)
				{
					*op->resnull = false;
					*op->resvalue = BoolGetDatum(exists);
				}
			}
			break;

		case JSON_QUERY_OP:
			*op->resvalue = JsonPathQuery(item, path, jsexpr->wrapper, &empty,
										  !throw_error ? &error : NULL,
										  jsestate->args,
										  jsexpr->column_name);

			*op->resnull = (DatumGetPointer(*op->resvalue) == NULL);
			break;

		case JSON_VALUE_OP:
			{
				JsonbValue *jbv = JsonPathValue(item, path, &empty,
												!throw_error ? &error : NULL,
												jsestate->args,
												jsexpr->column_name);

				if (jbv == NULL)
				{
					/* Will be coerced with json_populate_type(), if needed. */
					*op->resvalue = (Datum) 0;
					*op->resnull = true;
				}
				else if (!error && !empty)
				{
					if (jsexpr->returning->typid == JSONOID ||
						jsexpr->returning->typid == JSONBOID)
					{
						val_string = DatumGetCString(DirectFunctionCall1(jsonb_out,
																		 JsonbPGetDatum(JsonbValueToJsonb(jbv))));
					}
					else if (jsexpr->use_json_coercion)
					{
						*op->resvalue = JsonbPGetDatum(JsonbValueToJsonb(jbv));
						*op->resnull = false;
					}
					else
					{
						val_string = ExecGetJsonValueItemString(jbv, op->resnull);

						/*
						 * Simply convert to the default RETURNING type (text)
						 * if no coercion needed.
						 */
						if (!jsexpr->use_io_coercion)
							*op->resvalue = DirectFunctionCall1(textin,
																CStringGetDatum(val_string));
					}
				}
				break;
			}

			/* JSON_TABLE_OP can't happen here */

		default:
			elog(ERROR, "unrecognized SQL/JSON expression op %d",
				 (int) jsexpr->op);
			return false;
	}

	/*
	 * Coerce the result value to the RETURNING type by calling its input
	 * function.
	 */
	if (!*op->resnull && jsexpr->use_io_coercion)
	{
		FunctionCallInfo fcinfo;

		Assert(jump_eval_coercion == -1);
		fcinfo = jsestate->input_fcinfo;
		Assert(fcinfo != NULL);
		Assert(val_string != NULL);
		fcinfo->args[0].value = PointerGetDatum(val_string);
		fcinfo->args[0].isnull = *op->resnull;

		/*
		 * Second and third arguments are already set up in
		 * ExecInitJsonExpr().
		 */

		fcinfo->isnull = false;
		*op->resvalue = FunctionCallInvoke(fcinfo);
		if (SOFT_ERROR_OCCURRED(&jsestate->escontext))
			error = true;
	}

	/*
	 * When setting up the ErrorSaveContext (if needed) for capturing the
	 * errors that occur when coercing the JsonBehavior expression, set
	 * details_wanted to be able to show the actual error message as the
	 * DETAIL of the error message that tells that it is the JsonBehavior
	 * expression that caused the error; see ExecEvalJsonCoercionFinish().
	 */

	/* Handle ON EMPTY. */
	if (empty)
	{
		*op->resvalue = (Datum) 0;
		*op->resnull = true;
		if (jsexpr->on_empty)
		{
			if (jsexpr->on_empty->btype != JSON_BEHAVIOR_ERROR)
			{
				jsestate->empty.value = BoolGetDatum(true);
				/* Set up to catch coercion errors of the ON EMPTY value. */
				jsestate->escontext.error_occurred = false;
				jsestate->escontext.details_wanted = true;
				/* Jump to end if the ON EMPTY behavior is to return NULL */
				return jsestate->jump_empty >= 0 ? jsestate->jump_empty : jsestate->jump_end;
			}
		}
		else if (jsexpr->on_error->btype != JSON_BEHAVIOR_ERROR)
		{
			jsestate->error.value = BoolGetDatum(true);
			/* Set up to catch coercion errors of the ON ERROR value. */
			jsestate->escontext.error_occurred = false;
			jsestate->escontext.details_wanted = true;
			Assert(!throw_error);
			/* Jump to end if the ON ERROR behavior is to return NULL */
			return jsestate->jump_error >= 0 ? jsestate->jump_error : jsestate->jump_end;
		}

		if (jsexpr->column_name)
			ereport(ERROR,
					errcode(ERRCODE_NO_SQL_JSON_ITEM),
					errmsg("no SQL/JSON item found for specified path of column \"%s\"",
						   jsexpr->column_name));
		else
			ereport(ERROR,
					errcode(ERRCODE_NO_SQL_JSON_ITEM),
					errmsg("no SQL/JSON item found for specified path"));
	}

	/*
	 * ON ERROR. Wouldn't get here if the behavior is ERROR, because they
	 * would have already been thrown.
	 */
	if (error)
	{
		Assert(!throw_error);
		*op->resvalue = (Datum) 0;
		*op->resnull = true;
		jsestate->error.value = BoolGetDatum(true);
		/* Set up to catch coercion errors of the ON ERROR value. */
		jsestate->escontext.error_occurred = false;
		jsestate->escontext.details_wanted = true;
		/* Jump to end if the ON ERROR behavior is to return NULL */
		return jsestate->jump_error >= 0 ? jsestate->jump_error : jsestate->jump_end;
	}

	return jump_eval_coercion >= 0 ? jump_eval_coercion : jsestate->jump_end;
}

/*
 * ============================================================================
 * 【中文注释】ExecGetJsonValueItemString —— JsonbValue 转 C 字符串
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 JSON_VALUE 取出的 JsonbValue 转成其 C 字符串表示（供 RETURNING
 *   类型为标量时调用输入函数强转），jbvNull 通过 *resnull 标记。
 *
 * 设计思想：
 *   各 jsonb 值类型分别走专用输出：字符串直接拷贝、numeric/bool/
 *   datetime 调对应类型的 *_out 函数（datetime 需携带 typid 分派）、
 *   数组/对象序列化为 jsonb 文本；出错即内部错误。
 * ============================================================================
 */
static char *
ExecGetJsonValueItemString(JsonbValue *item, bool *resnull)
{
	*resnull = false;

	/* get coercion state reference and datum of the corresponding SQL type */
	switch (item->type)
	{
		case jbvNull:
			*resnull = true;
			return NULL;

		case jbvString:
			{
				char	   *str = palloc(item->val.string.len + 1);

				memcpy(str, item->val.string.val, item->val.string.len);
				str[item->val.string.len] = '\0';
				return str;
			}

		case jbvNumeric:
			return DatumGetCString(DirectFunctionCall1(numeric_out,
													   NumericGetDatum(item->val.numeric)));

		case jbvBool:
			return DatumGetCString(DirectFunctionCall1(boolout,
													   BoolGetDatum(item->val.boolean)));

		case jbvDatetime:
			switch (item->val.datetime.typid)
			{
				case DATEOID:
					return DatumGetCString(DirectFunctionCall1(date_out,
															   item->val.datetime.value));
				case TIMEOID:
					return DatumGetCString(DirectFunctionCall1(time_out,
															   item->val.datetime.value));
				case TIMETZOID:
					return DatumGetCString(DirectFunctionCall1(timetz_out,
															   item->val.datetime.value));
				case TIMESTAMPOID:
					return DatumGetCString(DirectFunctionCall1(timestamp_out,
															   item->val.datetime.value));
				case TIMESTAMPTZOID:
					return DatumGetCString(DirectFunctionCall1(timestamptz_out,
															   item->val.datetime.value));
				default:
					elog(ERROR, "unexpected jsonb datetime type oid %u",
						 item->val.datetime.typid);
			}
			break;

		case jbvArray:
		case jbvObject:
		case jbvBinary:
			return DatumGetCString(DirectFunctionCall1(jsonb_out,
													   JsonbPGetDatum(JsonbValueToJsonb(item))));

		default:
			elog(ERROR, "unexpected jsonb value type %d", item->type);
	}

	Assert(false);
	*resnull = true;
	return NULL;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalJsonCoercion —— 把 jsonb 结果强转为 RETURNING 类型
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 ExecEvalJsonExprPath() 或 ON ERROR / ON EMPTY 行为表达式产出的
 *   jsonb 值，经 json_populate_type() 强转为目标类型（含 typmod 与
 *   域约束检查），结果写回结果寄存器。
 *
 * 设计思想：
 *   1. JSON_EXISTS 特例（exists_coerce）：结果为布尔；目标为整型或其
 *      域时用 bool_int4 直接转换（整型的输入函数不接受布尔字面量），
 *      并顺带做域约束检查（domain_check_safe）；否则把布尔编码成
 *      jsonb 的 true/false 再走统一路径。
 *   2. 转换期间的软错误（如类型不匹配）被捕获进 escontext，由紧随的
 *      EEOP_JSONEXPR_COERCION_FINISH step（ExecEvalJsonCoercionFinish）
 *      检查并转成 ON ERROR 处理或真实报错。
 *   3. omit_quotes 控制标量目标类型对字符串/数字引号的取舍，编译期
 *      依 RETURNING 子句固化。
 * ============================================================================
 */
void
ExecEvalJsonCoercion(ExprState *state, ExprEvalStep *op,
					 ExprContext *econtext)
{
	ErrorSaveContext *escontext = op->d.jsonexpr_coercion.escontext;

	/*
	 * Prepare to call json_populate_type() to coerce the boolean result of
	 * JSON_EXISTS_OP to the target type.  If the target type is integer or a
	 * domain over integer, call the boolean-to-integer cast function instead,
	 * because the integer's input function (which is what
	 * json_populate_type() calls to coerce to scalar target types) doesn't
	 * accept boolean literals as valid input.  We only have a special case
	 * for integer and domains thereof as it seems common to use those types
	 * for EXISTS columns in JSON_TABLE().
	 */
	if (op->d.jsonexpr_coercion.exists_coerce)
	{
		if (op->d.jsonexpr_coercion.exists_cast_to_int)
		{
			/* Check domain constraints if any. */
			if (op->d.jsonexpr_coercion.exists_check_domain &&
				!domain_check_safe(*op->resvalue, *op->resnull,
								   op->d.jsonexpr_coercion.targettype,
								   &op->d.jsonexpr_coercion.json_coercion_cache,
								   econtext->ecxt_per_query_memory,
								   (Node *) escontext))
			{
				*op->resnull = true;
				*op->resvalue = (Datum) 0;
			}
			else
				*op->resvalue = DirectFunctionCall1(bool_int4, *op->resvalue);
			return;
		}

		*op->resvalue = DirectFunctionCall1(jsonb_in,
											DatumGetBool(*op->resvalue) ?
											CStringGetDatum("true") :
											CStringGetDatum("false"));
	}

	*op->resvalue = json_populate_type(*op->resvalue, JSONBOID,
									   op->d.jsonexpr_coercion.targettype,
									   op->d.jsonexpr_coercion.targettypmod,
									   &op->d.jsonexpr_coercion.json_coercion_cache,
									   econtext->ecxt_per_query_memory,
									   op->resnull,
									   op->d.jsonexpr_coercion.omit_quotes,
									   (Node *) escontext);
}

/*
 * ============================================================================
 * 【中文注释】GetJsonBehaviorValueString —— 把 ON ERROR / ON EMPTY 行为
 *              类型转成可读字符串（用于错误信息）
 * ----------------------------------------------------------------------------
 * 设计思想：
 *   数组顺序必须与 JsonBehaviorType 枚举定义一一对应（注释已强调），
 *   只服务于 ExecEvalJsonCoercionFinish 的报错信息。
 * ============================================================================
 */
static char *
GetJsonBehaviorValueString(JsonBehavior *behavior)
{
	/*
	 * The order of array elements must correspond to the order of
	 * JsonBehaviorType members.
	 */
	const char *behavior_names[] =
	{
		"NULL",
		"ERROR",
		"EMPTY",
		"TRUE",
		"FALSE",
		"UNKNOWN",
		"EMPTY ARRAY",
		"EMPTY OBJECT",
		"DEFAULT"
	};

	return pstrdup(behavior_names[behavior->btype]);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalJsonCoercionFinish —— 检查强转软错误并编排
 *              ON ERROR / ON EMPTY
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   检查 ExecEvalJsonCoercion() 期间是否发生了软错误（SOFT_ERROR_-
 *   OCCURRED）。若发生：若 jsestate->error/empty 标志表明错误发生在
 *   ON ERROR / ON EMPTY 行为表达式值的强转中，则直接把该强转错误
 *   抛为真实 ERROR（错误细节经 errdetail 展示）；否则把结果置 NULL
 *   并置 jsestate->error，触发后续 ON ERROR 处理 step。
 *
 * 设计思想：
 *   soft-error 两段式：coercion step 用 escontext 捕获一切强转错误，
 *   本 finish step 判定"错误来自主结果还是行为表达式"——前者走
 *   ON ERROR 行为编排，后者按 SQL 标准应直接报错（行为值本身非法）；
 *   处理完复位 escontext 供下一行复用。
 * ============================================================================
 */
void
ExecEvalJsonCoercionFinish(ExprState *state, ExprEvalStep *op)
{
	JsonExprState *jsestate = op->d.jsonexpr.jsestate;

	if (SOFT_ERROR_OCCURRED(&jsestate->escontext))
	{
		/*
		 * jsestate->error or jsestate->empty being set means that the error
		 * occurred when coercing the JsonBehavior value.  Throw the error in
		 * that case with the actual coercion error message shown in the
		 * DETAIL part.
		 */
		if (DatumGetBool(jsestate->error.value))
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
			/*- translator: first %s is a SQL/JSON clause (e.g. ON ERROR) */
					 errmsg("could not coerce %s expression (%s) to the RETURNING type",
							"ON ERROR",
							GetJsonBehaviorValueString(jsestate->jsexpr->on_error)),
					 errdetail("%s", jsestate->escontext.error_data->message)));
		else if (DatumGetBool(jsestate->empty.value))
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
			/*- translator: first %s is a SQL/JSON clause (e.g. ON ERROR) */
					 errmsg("could not coerce %s expression (%s) to the RETURNING type",
							"ON EMPTY",
							GetJsonBehaviorValueString(jsestate->jsexpr->on_empty)),
					 errdetail("%s", jsestate->escontext.error_data->message)));

		*op->resvalue = (Datum) 0;
		*op->resnull = true;

		jsestate->error.value = BoolGetDatum(true);

		/*
		 * Reset for next use such as for catching errors when coercing a
		 * JsonBehavior expression.
		 */
		jsestate->escontext.error_occurred = false;
		jsestate->escontext.details_wanted = true;
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalGroupingFunc —— GROUPING() 分组集判定函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   计算 GROUPING(expr...) 的位掩码结果：从右到左为每个参数表达式
 *   置 1 个 bit（最右侧参数是最低位），某参数不在当前分组集的
 *   grouping 表达式集合中则对应 bit=1。
 *
 * 设计思想：
 *   1. 语义：分组集聚合（GROUP BY GROUPING SETS/CUBE/ROLLUP）中，
 *      某列在"当前分组集"里没有参与分组时其值应为 NULL，GROUPING()
 *      用它区分"真 NULL"与"分组产生的 NULL"。
 *   2. 实现直取 aggstate->grouped_cols（当前分组集实际参与分组的
 *      属性位图）与编译期记录的参数 attnum 列表逐位构造掩码；
 *      结果恒非 NULL 的 int4。
 * ============================================================================
 */
void
ExecEvalGroupingFunc(ExprState *state, ExprEvalStep *op)
{
	AggState   *aggstate = castNode(AggState, state->parent);
	int			result = 0;
	Bitmapset  *grouped_cols = aggstate->grouped_cols;
	ListCell   *lc;

	foreach(lc, op->d.grouping_func.clauses)
	{
		int			attnum = lfirst_int(lc);

		result <<= 1;

		if (!bms_is_member(attnum, grouped_cols))
			result |= 1;
	}

	*op->resvalue = Int32GetDatum(result);
	*op->resnull = false;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalMergeSupportFunc —— MERGE 的 RETURNING 辅助函数
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   返回当前正在执行的 MERGE action 名称（"INSERT"/"UPDATE"/"DELETE"
 *   的 text 值），供 MERGE 语句 RETURNING 列表使用。
 *
 * 设计思想：
 *   直取 parent ModifyTableState 的 mt_merge_action 当前 action 的
 *   commandType 映射为字符串；无进行中的 action 属非法状态直接报错
 *   （DO NOTHING 分支不该走到求值）。文本用 cstring_to_text_with_len
 *   常量字符串零拷贝组装。
 * ============================================================================
 */
void
ExecEvalMergeSupportFunc(ExprState *state, ExprEvalStep *op,
						 ExprContext *econtext)
{
	ModifyTableState *mtstate = castNode(ModifyTableState, state->parent);
	MergeActionState *relaction = mtstate->mt_merge_action;

	if (!relaction)
		elog(ERROR, "no merge action in progress");

	/* Return the MERGE action ("INSERT", "UPDATE", or "DELETE") */
	switch (relaction->mas_action->commandType)
	{
		case CMD_INSERT:
			*op->resvalue = PointerGetDatum(cstring_to_text_with_len("INSERT", 6));
			*op->resnull = false;
			break;
		case CMD_UPDATE:
			*op->resvalue = PointerGetDatum(cstring_to_text_with_len("UPDATE", 6));
			*op->resnull = false;
			break;
		case CMD_DELETE:
			*op->resvalue = PointerGetDatum(cstring_to_text_with_len("DELETE", 6));
			*op->resnull = false;
			break;
		case CMD_NOTHING:
			elog(ERROR, "unexpected merge action: DO NOTHING");
			break;
		default:
			elog(ERROR, "unrecognized commandType: %d",
				 (int) relaction->mas_action->commandType);
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalSubPlan —— 子查询（SubPlan）求值转交
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把子查询求值交给 nodeSubplan.c 的 ExecSubPlan()：按子查询类型
 *   （标量/EXISTS/IN/ANY/ALL 等）驱动下层执行、缓存结果并做相关化
 *   参数处理，结果写回结果寄存器。
 *
 * 设计思想：
 *   1. 本文件只做"交接"：sstate 在编译期由 ExecInitSubPlan 建好，
 *      执行细节（物化、重复执行策略、参数重新扫描）都在 nodeSubplan.c。
 *   2. check_stack_depth：子查询可嵌套任意深，防止深层递归耗尽栈。
 * ============================================================================
 */
void
ExecEvalSubPlan(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	SubPlanState *sstate = op->d.subplan.sstate;

	/* could potentially be nested, so make sure there's enough stack */
	check_stack_depth();

	*op->resvalue = ExecSubPlan(sstate, econtext, op->resnull);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalWholeRowVar —— 整行 Var 求值（表名.* / whole-row）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从表达式上下文取到整行 slot，经可选 junkfilter 过滤后组装为
 *   复合 Datum 返回；首次执行时校验行类型与 Var 声明类型兼容并缓存
 *   输出描述符（命名复合类型按声明描述符、RECORD 按输入槽描述符）。
 *
 * 设计思想：
 *   1. 取槽分流：INNER/OUTER 取内/外表元组；默认（扫描）路径按
 *      varreturningtype 取扫描槽或 RETURNING 的 OLD/NEW 槽——OLD/NEW
 *      行不存在（INSERT 的 OLD / DELETE 的 NEW）时按标志直接返回 NULL。
 *   2. 类型兼容性首行检查：对命名复合类型，比较属性数、逐列类型；
 *      仅当源列是 dropped 列时允许类型不同，但物理存储（len/align）
 *      不同则必须走 slow 路径——每行再检查 dropped 列是否恰好为
 *      NULL（如过期的缓存计划插入含 dropped 列的表：planner 常产生
 *      INT4 NULL 而不管 dropped 列原类型）。域上复合先剥到基类型。
 *   3. 输出描述符：命名类型取声明（必须吸收 attisdropped 标记），
 *      RECORD 类型取输入槽描述符并尽力从 RTE 的 eref 采列名；均拷贝
 *      到 per-query 内存并 BlessTupleDesc 后缓存，此后跨行复用。
 *   4. 组装：toast_build_flattened_tuple 保证 toasted 字段被展开
 *      （复合 Datum 内不允许存在外部 toast 指针），再打上输出行类型
 *      的 typeid/typmod 标签。
 *   5. 为什么不在编译期做描述符检查：整行值经 slot 获取，slot 描述
 *      符要到运行期才有（见函数内 XXX 注释）。
 * ============================================================================
 */
void
ExecEvalWholeRowVar(ExprState *state, ExprEvalStep *op, ExprContext *econtext)
{
	Var		   *variable = op->d.wholerow.var;
	TupleTableSlot *slot = NULL;
	TupleDesc	output_tupdesc;
	MemoryContext oldcontext;
	HeapTupleHeader dtuple;
	HeapTuple	tuple;

	/* This was checked by ExecInitExpr */
	Assert(variable->varattno == InvalidAttrNumber);

	/* Get the input slot we want */
	switch (variable->varno)
	{
		case INNER_VAR:
			/* get the tuple from the inner node */
			slot = econtext->ecxt_innertuple;
			break;

		case OUTER_VAR:
			/* get the tuple from the outer node */
			slot = econtext->ecxt_outertuple;
			break;

			/* INDEX_VAR is handled by default case */

		default:

			/*
			 * Get the tuple from the relation being scanned.
			 *
			 * By default, this uses the "scan" tuple slot, but a wholerow Var
			 * in the RETURNING list may explicitly refer to OLD/NEW.  If the
			 * OLD/NEW row doesn't exist, we just return NULL.
			 */
			switch (variable->varreturningtype)
			{
				case VAR_RETURNING_DEFAULT:
					slot = econtext->ecxt_scantuple;
					break;

				case VAR_RETURNING_OLD:
					if (state->flags & EEO_FLAG_OLD_IS_NULL)
					{
						*op->resvalue = (Datum) 0;
						*op->resnull = true;
						return;
					}
					slot = econtext->ecxt_oldtuple;
					break;

				case VAR_RETURNING_NEW:
					if (state->flags & EEO_FLAG_NEW_IS_NULL)
					{
						*op->resvalue = (Datum) 0;
						*op->resnull = true;
						return;
					}
					slot = econtext->ecxt_newtuple;
					break;
			}
			break;
	}

	/* Apply the junkfilter if any */
	if (op->d.wholerow.junkFilter != NULL)
		slot = ExecFilterJunk(op->d.wholerow.junkFilter, slot);

	/*
	 * If first time through, obtain tuple descriptor and check compatibility.
	 *
	 * XXX: It'd be great if this could be moved to the expression
	 * initialization phase, but due to using slots that's currently not
	 * feasible.
	 */
	if (op->d.wholerow.first)
	{
		/* optimistically assume we don't need slow path */
		op->d.wholerow.slow = false;

		/*
		 * If the Var identifies a named composite type, we must check that
		 * the actual tuple type is compatible with it.
		 */
		if (variable->vartype != RECORDOID)
		{
			TupleDesc	var_tupdesc;
			TupleDesc	slot_tupdesc;

			/*
			 * We really only care about numbers of attributes and data types.
			 * Also, we can ignore type mismatch on columns that are dropped
			 * in the destination type, so long as (1) the physical storage
			 * matches or (2) the actual column value is NULL.  Case (1) is
			 * helpful in some cases involving out-of-date cached plans, while
			 * case (2) is expected behavior in situations such as an INSERT
			 * into a table with dropped columns (the planner typically
			 * generates an INT4 NULL regardless of the dropped column type).
			 * If we find a dropped column and cannot verify that case (1)
			 * holds, we have to use the slow path to check (2) for each row.
			 *
			 * If vartype is a domain over composite, just look through that
			 * to the base composite type.
			 */
			var_tupdesc = lookup_rowtype_tupdesc_domain(variable->vartype,
														-1, false);

			slot_tupdesc = slot->tts_tupleDescriptor;

			if (var_tupdesc->natts != slot_tupdesc->natts)
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("table row type and query-specified row type do not match"),
						 errdetail_plural("Table row contains %d attribute, but query expects %d.",
										  "Table row contains %d attributes, but query expects %d.",
										  slot_tupdesc->natts,
										  slot_tupdesc->natts,
										  var_tupdesc->natts)));

			for (int i = 0; i < var_tupdesc->natts; i++)
			{
				Form_pg_attribute vattr = TupleDescAttr(var_tupdesc, i);
				Form_pg_attribute sattr = TupleDescAttr(slot_tupdesc, i);

				if (vattr->atttypid == sattr->atttypid)
					continue;	/* no worries */
				if (!vattr->attisdropped)
					ereport(ERROR,
							(errcode(ERRCODE_DATATYPE_MISMATCH),
							 errmsg("table row type and query-specified row type do not match"),
							 errdetail("Table has type %s at ordinal position %d, but query expects %s.",
									   format_type_be(sattr->atttypid),
									   i + 1,
									   format_type_be(vattr->atttypid))));

				if (vattr->attlen != sattr->attlen ||
					vattr->attalign != sattr->attalign)
					op->d.wholerow.slow = true; /* need to check for nulls */
			}

			/*
			 * Use the variable's declared rowtype as the descriptor for the
			 * output values.  In particular, we *must* absorb any
			 * attisdropped markings.
			 */
			oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
			output_tupdesc = CreateTupleDescCopy(var_tupdesc);
			MemoryContextSwitchTo(oldcontext);

			ReleaseTupleDesc(var_tupdesc);
		}
		else
		{
			/*
			 * In the RECORD case, we use the input slot's rowtype as the
			 * descriptor for the output values, modulo possibly assigning new
			 * column names below.
			 */
			oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
			output_tupdesc = CreateTupleDescCopy(slot->tts_tupleDescriptor);
			MemoryContextSwitchTo(oldcontext);

			/*
			 * It's possible that the input slot is a relation scan slot and
			 * so is marked with that relation's rowtype.  But we're supposed
			 * to be returning RECORD, so reset to that.
			 */
			output_tupdesc->tdtypeid = RECORDOID;
			output_tupdesc->tdtypmod = -1;

			/*
			 * We already got the correct physical datatype info above, but
			 * now we should try to find the source RTE and adopt its column
			 * aliases, since it's unlikely that the input slot has the
			 * desired names.
			 *
			 * If we can't locate the RTE, assume the column names we've got
			 * are OK.  (As of this writing, the only cases where we can't
			 * locate the RTE are in execution of trigger WHEN clauses, and
			 * then the Var will have the trigger's relation's rowtype, so its
			 * names are fine.)  Also, if the creator of the RTE didn't bother
			 * to fill in an eref field, assume our column names are OK. (This
			 * happens in COPY, and perhaps other places.)
			 */
			if (econtext->ecxt_estate &&
				variable->varno <= econtext->ecxt_estate->es_range_table_size)
			{
				RangeTblEntry *rte = exec_rt_fetch(variable->varno,
												   econtext->ecxt_estate);

				if (rte->eref)
					ExecTypeSetColNames(output_tupdesc, rte->eref->colnames);
			}
		}

		/* Bless the tupdesc if needed, and save it in the execution state */
		op->d.wholerow.tupdesc = BlessTupleDesc(output_tupdesc);

		op->d.wholerow.first = false;
	}

	/*
	 * Make sure all columns of the slot are accessible in the slot's
	 * Datum/isnull arrays.
	 */
	slot_getallattrs(slot);

	if (op->d.wholerow.slow)
	{
		/* Check to see if any dropped attributes are non-null */
		TupleDesc	tupleDesc = slot->tts_tupleDescriptor;
		TupleDesc	var_tupdesc = op->d.wholerow.tupdesc;

		Assert(var_tupdesc->natts == tupleDesc->natts);

		for (int i = 0; i < var_tupdesc->natts; i++)
		{
			CompactAttribute *vattr = TupleDescCompactAttr(var_tupdesc, i);
			CompactAttribute *sattr = TupleDescCompactAttr(tupleDesc, i);

			if (!vattr->attisdropped)
				continue;		/* already checked non-dropped cols */
			if (slot->tts_isnull[i])
				continue;		/* null is always okay */
			if (vattr->attlen != sattr->attlen ||
				vattr->attalignby != sattr->attalignby)
				ereport(ERROR,
						(errcode(ERRCODE_DATATYPE_MISMATCH),
						 errmsg("table row type and query-specified row type do not match"),
						 errdetail("Physical storage mismatch on dropped attribute at ordinal position %d.",
								   i + 1)));
		}
	}

	/*
	 * Build a composite datum, making sure any toasted fields get detoasted.
	 *
	 * (Note: it is critical that we not change the slot's state here.)
	 */
	tuple = toast_build_flattened_tuple(slot->tts_tupleDescriptor,
										slot->tts_values,
										slot->tts_isnull);
	dtuple = tuple->t_data;

	/*
	 * Label the datum with the composite type info we identified before.
	 *
	 * (Note: we could skip doing this by passing op->d.wholerow.tupdesc to
	 * the tuple build step; but that seems a tad risky so let's not.)
	 */
	HeapTupleHeaderSetTypeId(dtuple, op->d.wholerow.tupdesc->tdtypeid);
	HeapTupleHeaderSetTypMod(dtuple, op->d.wholerow.tupdesc->tdtypmod);

	*op->resvalue = PointerGetDatum(dtuple);
	*op->resnull = false;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalSysVar —— 系统列（ctid/xmin/tableoid/…）求值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从指定 slot 取 Var 指定的系统属性值（attnum 为负的系统列号），
 *   结果写回结果寄存器；RETURNING 语境下 OLD/NEW 行整体为 NULL 时
 *   直接返回 NULL。
 *
 * 设计思想：
 *   1. OLD/NEW 防护：与整行 Var 同理，标志位 EEO_FLAG_OLD/NEW_IS_NULL
 *      存在时系统列无意义，返回 NULL。
 *   2. slot_getsysattr 统一处理各类系统列的派生计算（ctid 定位、
 *      tableoid 取 OID 等），对非法 attnum 自带防御；命中 NULL 属
 *      "不应发生"，用 unlikely 低成本防御报错。
 * ============================================================================
 */
void
ExecEvalSysVar(ExprState *state, ExprEvalStep *op, ExprContext *econtext,
			   TupleTableSlot *slot)
{
	Datum		d;

	/* OLD/NEW system attribute is NULL if OLD/NEW row is NULL */
	if ((op->d.var.varreturningtype == VAR_RETURNING_OLD &&
		 state->flags & EEO_FLAG_OLD_IS_NULL) ||
		(op->d.var.varreturningtype == VAR_RETURNING_NEW &&
		 state->flags & EEO_FLAG_NEW_IS_NULL))
	{
		*op->resvalue = (Datum) 0;
		*op->resnull = true;
		return;
	}

	/* slot_getsysattr has sufficient defenses against bad attnums */
	d = slot_getsysattr(slot,
						op->d.var.attnum,
						op->resnull);
	*op->resvalue = d;
	/* this ought to be unreachable, but it's cheap enough to check */
	if (unlikely(*op->resnull))
		elog(ERROR, "failed to fetch attribute from slot");
}

/*
 * ============================================================================
 * 【中文注释】ExecAggInitGroup —— 组的首个非 NULL 输入作为初始转移值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   当某组还没有初始化转移值时（这是该组的第一个非 NULL 输入），
 *   直接把这个输入值（fcinfo->args[1]）拷贝进 per-tuple 上下文作为
 *   transValue，并置位 transValueIsNull=false、noTransValue=false。
 *
 * 设计思想：
 *   1. 这是聚合转移的"零调用"优化：min/max/sum 等简单聚合在
 *      EEOP_AGG_PLAIN_TRANS_* 指令里先查 noTransValue，命中则直接
 *      采纳输入，跳过对 transfn 的第一次调用。
 *   2. 拷贝进 aggcontext 的 per-tuple 内存（按 per-tuple 生命周期，
 *      由聚合框架在组间换 context 释放）；pass-by-ref 才真正拷贝，
 *      输入类型与 transtype 已被编译期保证二进制兼容，故可直接拷贝。
 * ============================================================================
 */
void
ExecAggInitGroup(AggState *aggstate, AggStatePerTrans pertrans, AggStatePerGroup pergroup,
				 ExprContext *aggcontext)
{
	FunctionCallInfo fcinfo = pertrans->transfn_fcinfo;
	MemoryContext oldContext;

	/*
	 * We must copy the datum into aggcontext if it is pass-by-ref. We do not
	 * need to pfree the old transValue, since it's NULL.  (We already checked
	 * that the agg's input type is binary-compatible with its transtype, so
	 * straight copy here is OK.)
	 */
	oldContext = MemoryContextSwitchTo(aggcontext->ecxt_per_tuple_memory);
	pergroup->transValue = datumCopy(fcinfo->args[1].value,
									 pertrans->transtypeByVal,
									 pertrans->transtypeLen);
	pergroup->transValueIsNull = false;
	pergroup->noTransValue = false;
	MemoryContextSwitchTo(oldContext);
}

/*
 * ============================================================================
 * 【中文注释】ExecAggCopyTransValue —— 把新转移值落位到 aggcontext 并
 *              释放旧值
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   保证 pass-by-ref 的转移值存储在 aggcontext 的 per-tuple 上下文
 *   中（而非 per-tuple 求值上下文），并释放旧转移值。仅当已知新值与
 *   旧值不同（指针不同）时被调用。
 *
 * 注意：本函数会切换当前内存上下文（调用方须负责恢复）。
 *
 * 设计思想：
 *   1. 拷贝豁免：newValue 若是已经是 aggcontext 子上下文的可写
 *      expanded 对象则无需拷贝（聚合感知的 transfn 首调应直接返回
 *      落位好的对象，此后原地修改并返回同一指针——这样根本走不到
 *      这里）。
 *   2. 不 reparent 的理由：若把 generic transfn 返回的可写 expanded
 *      对象 reparent 到 aggcontext，下一次调用可能删除它，随后我们
 *      再删旧值会双重释放——因此存储的转移值恒为扁平非 expanded
 *      对象，除非 transfn 明确做聚合感知的内存管理（这在文档化的
 *      记忆管理中是被接受的折中）。
 *   3. NULL 的规范化：新值为 NULL 时置 (Datum) 0，使调用方可以安全
 *      用指针比较判定新旧是否同一，而不必再判 NULL。
 *   4. 旧值释放：expanded 用 DeleteExpandedObject，否则 pfree。
 * ============================================================================
 */
Datum
ExecAggCopyTransValue(AggState *aggstate, AggStatePerTrans pertrans,
					  Datum newValue, bool newValueIsNull,
					  Datum oldValue, bool oldValueIsNull)
{
	Assert(newValue != oldValue);

	if (!newValueIsNull)
	{
		MemoryContextSwitchTo(aggstate->curaggcontext->ecxt_per_tuple_memory);
		if (DatumIsReadWriteExpandedObject(newValue,
										   false,
										   pertrans->transtypeLen) &&
			MemoryContextGetParent(DatumGetEOHP(newValue)->eoh_context) == CurrentMemoryContext)
			 /* do nothing */ ;
		else
			newValue = datumCopy(newValue,
								 pertrans->transtypeByVal,
								 pertrans->transtypeLen);
	}
	else
	{
		/*
		 * Ensure that AggStatePerGroup->transValue ends up being 0, so
		 * callers can safely compare newValue/oldValue without having to
		 * check their respective nullness.
		 */
		newValue = (Datum) 0;
	}

	if (!oldValueIsNull)
	{
		if (DatumIsReadWriteExpandedObject(oldValue,
										   false,
										   pertrans->transtypeLen))
			DeleteExpandedObject(oldValue);
		else
			pfree(DatumGetPointer(oldValue));
	}

	return newValue;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalPreOrderedDistinctSingle —— 单输入有序聚合的去重
 *              前判定（按值比较）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对"预先排好序"的单输入聚合（如 DISTINCT 的 ORDERED SET 聚合/
 *   ORDER BY 排序流），比较当前输入与上一个输入：不同返回 true
 *   （应开始/继续新值的转移），相同返回 false（跳过转移）。
 *
 * 设计思想：
 *   1. 依赖排序输入流：值相同必相邻，故只需记忆"上一个输入"
 *      （haslast/lastdatum/lastisnull 挂在 pertrans 上跨行复用）。
 *   2. 三要素判重：无上一个、NULL 性不同、或非 NULL 且等值函数
 *      （equalfnOne，编译期选定的默认等值操作符）判不等——任一命中
 *      即视为新值；换新值时拷贝新 datum 到 aggcontext per-tuple
 *      内存（先释放旧的 pass-by-ref lastdatum 防泄漏）。
 *   3. 语义约定：NULL 输入本身参与去重（NULL 与 NULL 视为相等），
 *      与 SQL DISTINCT 的 NULL 处理一致（由聚合语义决定）。
 * ============================================================================
 */
bool
ExecEvalPreOrderedDistinctSingle(AggState *aggstate, AggStatePerTrans pertrans)
{
	Datum		value = pertrans->transfn_fcinfo->args[1].value;
	bool		isnull = pertrans->transfn_fcinfo->args[1].isnull;

	if (!pertrans->haslast ||
		pertrans->lastisnull != isnull ||
		(!isnull && !DatumGetBool(FunctionCall2Coll(&pertrans->equalfnOne,
													pertrans->aggCollation,
													pertrans->lastdatum, value))))
	{
		if (pertrans->haslast && !pertrans->inputtypeByVal &&
			!pertrans->lastisnull)
			pfree(DatumGetPointer(pertrans->lastdatum));

		pertrans->haslast = true;
		if (!isnull)
		{
			MemoryContext oldContext;

			oldContext = MemoryContextSwitchTo(aggstate->curaggcontext->ecxt_per_tuple_memory);

			pertrans->lastdatum = datumCopy(value, pertrans->inputtypeByVal,
											pertrans->inputtypeLen);

			MemoryContextSwitchTo(oldContext);
		}
		else
			pertrans->lastdatum = (Datum) 0;
		pertrans->lastisnull = isnull;
		return true;
	}

	return false;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalPreOrderedDistinctMulti —— 多输入有序聚合的去重
 *              前判定（按整行比较）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   与 ExecEvalPreOrderedDistinctSingle 同构，但用
 *   pertrans->equalfnMulti（编译期生成的等值 Qual 表达式）对整组
 *   输入做行级比较：与上一个输入行不同返回 true，相同或没有上一个
 *   输入返回 false。
 *
 * 设计思想：
 *   1. 把当前所有输入值装载进 sortslot 虚拟槽，用 tmpcontext 临时
 *      把 outer/inner 槽换成 sortslot/uniqslot 后直接 ExecQual 走
 *      普通表达式求值做行比较——复用通用 ExecQual 免去逐值比较的
 *      手写逻辑。
 *   2. 换新行时用 ExecCopySlot 把 sortslot 拷进 uniqslot 留存为
 *      "上一个输入"；调用前后必须恢复 tmpcontext 的原外/内槽。
 *   3. 注意 sortslot 装载后 ExecClearTuple + tts_nvalid 手动设置
 *      标记虚拟槽为已有效，与 ExecStoreVirtualTuple 配合正确初始化
 *      槽状态。
 * ============================================================================
 */
bool
ExecEvalPreOrderedDistinctMulti(AggState *aggstate, AggStatePerTrans pertrans)
{
	ExprContext *tmpcontext = aggstate->tmpcontext;
	bool		isdistinct = false; /* for now */
	TupleTableSlot *save_outer;
	TupleTableSlot *save_inner;

	for (int i = 0; i < pertrans->numTransInputs; i++)
	{
		pertrans->sortslot->tts_values[i] = pertrans->transfn_fcinfo->args[i + 1].value;
		pertrans->sortslot->tts_isnull[i] = pertrans->transfn_fcinfo->args[i + 1].isnull;
	}

	ExecClearTuple(pertrans->sortslot);
	pertrans->sortslot->tts_nvalid = pertrans->numInputs;
	ExecStoreVirtualTuple(pertrans->sortslot);

	/* save the previous slots before we overwrite them */
	save_outer = tmpcontext->ecxt_outertuple;
	save_inner = tmpcontext->ecxt_innertuple;

	tmpcontext->ecxt_outertuple = pertrans->sortslot;
	tmpcontext->ecxt_innertuple = pertrans->uniqslot;

	if (!pertrans->haslast ||
		!ExecQual(pertrans->equalfnMulti, tmpcontext))
	{
		if (pertrans->haslast)
			ExecClearTuple(pertrans->uniqslot);

		pertrans->haslast = true;
		ExecCopySlot(pertrans->uniqslot, pertrans->sortslot);

		isdistinct = true;
	}

	/* restore the original slots */
	tmpcontext->ecxt_outertuple = save_outer;
	tmpcontext->ecxt_innertuple = save_inner;

	return isdistinct;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalAggOrderedTransDatum —— 有序聚合：以 datum 形式
 *              喂给排序器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把当前行的输入值（已在结果寄存器）写入 pertrans->sortstates[setno]
 *   对应的 tuplesort 实例（tuplesort_putdatum）——有序聚合
 *   （ORDERED SET 聚合 / DISTINCT + ORDER BY 聚合）运行期先排序再
 *   顺序喂转移函数的流水线第一环。
 *
 * 设计思想：
 *   datum 形式适用于单输入有序聚合：排序键与有效值合一；排序器在
 *   编译期已按聚合的比较语义（collation、排序方向）配置好。
 * ============================================================================
 */
void
ExecEvalAggOrderedTransDatum(ExprState *state, ExprEvalStep *op,
							 ExprContext *econtext)
{
	AggStatePerTrans pertrans = op->d.agg_trans.pertrans;
	int			setno = op->d.agg_trans.setno;

	tuplesort_putdatum(pertrans->sortstates[setno],
					   *op->resvalue, *op->resnull);
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalAggOrderedTransTuple —— 有序聚合：以元组形式喂给
 *              排序器
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   多输入有序聚合版本：把当前行的各输入列装载进 pertrans->sortslot
 *   虚拟槽（ts_values/ts_isnull 已由前置 FETCH 写入），再以
 *   tuplesort_puttupleslot 存入对应 setno 的 tuplesort。
 *
 * 设计思想：
 *   与 datum 版互补：排序键为整行（首列或指定列序），后续 final 阶段
 *   按排序顺序取行喂转移函数；装载后手动置 tts_nvalid 并
 *   ExecStoreVirtualTuple 完成槽状态标记。
 * ============================================================================
 */
void
ExecEvalAggOrderedTransTuple(ExprState *state, ExprEvalStep *op,
							 ExprContext *econtext)
{
	AggStatePerTrans pertrans = op->d.agg_trans.pertrans;
	int			setno = op->d.agg_trans.setno;

	ExecClearTuple(pertrans->sortslot);
	pertrans->sortslot->tts_nvalid = pertrans->numInputs;
	ExecStoreVirtualTuple(pertrans->sortslot);
	tuplesort_puttupleslot(pertrans->sortstates[setno], pertrans->sortslot);
}

/* 【中文注释】byval 转移类型的普通（plain）转移函数调用实现 */
static pg_always_inline void
ExecAggPlainTransByVal(AggState *aggstate, AggStatePerTrans pertrans,
					   AggStatePerGroup pergroup,
					   ExprContext *aggcontext, int setno)
{
	FunctionCallInfo fcinfo = pertrans->transfn_fcinfo;
	MemoryContext oldContext;
	Datum		newVal;

	/* cf. select_current_set() */
	aggstate->curaggcontext = aggcontext;
	aggstate->current_set = setno;

	/* set up aggstate->curpertrans for AggGetAggref() */
	aggstate->curpertrans = pertrans;

	/* invoke transition function in per-tuple context */
	oldContext = MemoryContextSwitchTo(aggstate->tmpcontext->ecxt_per_tuple_memory);

	fcinfo->args[0].value = pergroup->transValue;
	fcinfo->args[0].isnull = pergroup->transValueIsNull;
	fcinfo->isnull = false;		/* just in case transfn doesn't set it */

	newVal = FunctionCallInvoke(fcinfo);

	pergroup->transValue = newVal;
	pergroup->transValueIsNull = fcinfo->isnull;

	MemoryContextSwitchTo(oldContext);
}

/*
 * ============================================================================
 * 【中文注释】ExecAggPlainTransByRef —— byref 转移类型的普通转移函数
 *              调用实现
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   对 pass-by-ref 转移类型：在 per-tuple 上下文里调用转移函数
 *   （args[0]=旧 transValue、args[1]=当前输入），新值若不是同一指针
 *   则经 ExecAggCopyTransValue 拷贝到 aggcontext 并释放旧值。
 *
 * 设计思想：
 *   1. 调用前设置 aggstate->curaggcontext/current_set/curpertrans，
 *      供转移函数内 AggGetAggref()/选择当前分组集等反射 API 使用。
 *   2. 指针判等的免拷贝优化：若 transfn 就地修改并返回第一个参数
 *      （通用内存感知 transfn 的惯例），指针相同则跳过拷贝/释放。
 *   3. NULL 归一化细节（见 ExecAggCopyTransValue 注释）：transValue
 *      为 NULL 时保证是 (Datum) 0，使指针比较不受数值相等干扰——
 *      这是热路径，避免为此再加分支。
 * ============================================================================
 */
static pg_always_inline void
ExecAggPlainTransByRef(AggState *aggstate, AggStatePerTrans pertrans,
					   AggStatePerGroup pergroup,
					   ExprContext *aggcontext, int setno)
{
	FunctionCallInfo fcinfo = pertrans->transfn_fcinfo;
	MemoryContext oldContext;
	Datum		newVal;

	/* cf. select_current_set() */
	aggstate->curaggcontext = aggcontext;
	aggstate->current_set = setno;

	/* set up aggstate->curpertrans for AggGetAggref() */
	aggstate->curpertrans = pertrans;

	/* invoke transition function in per-tuple context */
	oldContext = MemoryContextSwitchTo(aggstate->tmpcontext->ecxt_per_tuple_memory);

	fcinfo->args[0].value = pergroup->transValue;
	fcinfo->args[0].isnull = pergroup->transValueIsNull;
	fcinfo->isnull = false;		/* just in case transfn doesn't set it */

	newVal = FunctionCallInvoke(fcinfo);

	/*
	 * For pass-by-ref datatype, must copy the new value into aggcontext and
	 * free the prior transValue.  But if transfn returned a pointer to its
	 * first input, we don't need to do anything.
	 *
	 * It's safe to compare newVal with pergroup->transValue without regard
	 * for either being NULL, because ExecAggCopyTransValue takes care to set
	 * transValue to 0 when NULL. Otherwise we could end up accidentally not
	 * reparenting, when the transValue has the same numerical value as
	 * newValue, despite being NULL.  This is a somewhat hot path, making it
	 * undesirable to instead solve this with another branch for the common
	 * case of the transition function returning its (modified) input
	 * argument.
	 */
	if (DatumGetPointer(newVal) != DatumGetPointer(pergroup->transValue))
		newVal = ExecAggCopyTransValue(aggstate, pertrans,
									   newVal, fcinfo->isnull,
									   pergroup->transValue,
									   pergroup->transValueIsNull);

	pergroup->transValue = newVal;
	pergroup->transValueIsNull = fcinfo->isnull;

	MemoryContextSwitchTo(oldContext);
}
