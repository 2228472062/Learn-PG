/*-------------------------------------------------------------------------
 *
 * execSRF.c
 *	  Routines implementing the API for set-returning functions
 *
 * This file serves nodeFunctionscan.c and nodeProjectSet.c, providing
 * common code for calling set-returning functions according to the
 * ReturnSetInfo API.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execSRF.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * ============================================================================
 * 【中文注释】execSRF.c —— 集合返回函数（SRF）执行 API
 * ----------------------------------------------------------------------------
 * 文件定位：
 *   为 nodeFunctionscan.c（FROM ROWS FROM 表函数/ROWS FROM）与
 *   nodeProjectSet.c（targetlist 中的 SRF 投影）提供公共支撑：
 *   按 ReturnSetInfo 协议调用集合返回函数并消费其输出。
 *
 * 核心概念（ReturnSetInfo 协议，三个 returnMode）：
 *   1. SFRM_ValuePerCall：每调用一次函数返回一行（isDone 区分
 *      ExprSingleResult 一行即止 / ExprMultipleResult 还能再要 /
 *      ExprEndResult 结束）。这是最常用模式（大部分 SRF 语言函数、
 *      C 函数等）。
 *   2. SFRM_Materialize：函数一次性把结果写进 tuplestore 并回填
 *      setResult/setDesc；执行器随后从 tuplestore 逐行读出。
 *      SFRM_Materialize_Preferred/Random 变体表示"更希望/允许物化"。
 *   3. 协议违规（SRF 在上下文中乱换模式、非 SRF 返回多行等）报
 *      ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED。
 *
 * 关键机制：
 *   - SetExprState 缓存函数元数据（fmgr_info）、参数表达式列表、fcinfo
 *     及"结果存储"（funcResultStore/ funcResultSlot）；首次调用时初始化
 *     （init_sexpr：权限检查 + 元数据 + 结果行类型推导 funcResultDesc）；
 *   - 参数粘性（setArgsValid）：ValuePerCall 多行模式下参数只需求值一次，
 *     后续调用复用（值保存在 argContext，跨 per-tuple 上下文存活）；
 *   - 清理回调（RegisterExprContextCallback → ShutdownSetExpr）：未跑完
 *     就被丢弃时释放 tuplestore/槽。
 * ============================================================================
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "catalog/objectaccess.h"
#include "catalog/pg_proc.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "parser/parse_coerce.h"
#include "pgstat.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/tuplestore.h"
#include "utils/typcache.h"


/* static function decls */
static void init_sexpr(Oid foid, Oid input_collation, Expr *node,
					   SetExprState *sexpr, PlanState *parent,
					   MemoryContext sexprCxt, bool allowSRF, bool needDescForSRF);
static void ShutdownSetExpr(Datum arg);
static void ExecEvalFuncArgs(FunctionCallInfo fcinfo,
							 List *argList, ExprContext *econtext);
static void ExecPrepareTuplestoreResult(SetExprState *sexpr,
										ExprContext *econtext,
										Tuplestorestate *resultStore,
										TupleDesc resultDesc);
static void tupledesc_match(TupleDesc dst_tupdesc, TupleDesc src_tupdesc);


/*
 * ============================================================================
 * 【中文注释】ExecInitTableFunctionResult —— 准备 FROM 子句表函数调用
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为表函数（FROM 位置的 ROWS FROM 项）构建 SetExprState。若表达式是
 *   FuncExpr 则按其声明初始化（参数列表编译 + init_sexpr 完成权限/元数据）；
 *   否则（规划器常量折叠/内联把函数调用替换成了别的表达式）退化为通用
 *   表达式路径——elidedFuncState 走 ExecEvalExpr，代价是嵌套在表达式里
 *   的 SRF 不再受支持。
 *
 * 上下文选择：per-query 内存（函数元数据跨整查询存活）。
 * ============================================================================
 */
SetExprState *
ExecInitTableFunctionResult(Expr *expr,
							ExprContext *econtext, PlanState *parent)
{
	SetExprState *state = makeNode(SetExprState);

	state->funcReturnsSet = false;
	state->expr = expr;
	state->func.fn_oid = InvalidOid;

	/*
	 * Normally the passed expression tree will be a FuncExpr, since the
	 * grammar only allows a function call at the top level of a table
	 * function reference.  However, if the function doesn't return set then
	 * the planner might have replaced the function call via constant-folding
	 * or inlining.  So if we see any other kind of expression node, execute
	 * it via the general ExecEvalExpr() code.  That code path will not
	 * support set-returning functions buried in the expression, though.
	 */
	if (IsA(expr, FuncExpr))
	{
		FuncExpr   *func = (FuncExpr *) expr;

		state->funcReturnsSet = func->funcretset;
		state->args = ExecInitExprList(func->args, parent);

		init_sexpr(func->funcid, func->inputcollid, expr, state, parent,
				   econtext->ecxt_per_query_memory, func->funcretset, false);
	}
	else
	{
		state->elidedFuncState = ExecInitExpr(expr, parent);
	}

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecMakeTableFunctionResult —— 求值表函数并物化为 tuplestore
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   调用表函数，把结果全部收集进 Tuplestore 返回（nodeFunctionscan 逐行
 *   读取）。两种输入形态：
 *   - 真正的 SRF：按 ReturnSetInfo 协议驱动（ValuePerCall 循环收集 /
 *     Materialize 直接接住 tuplestore）；strict 且含 NULL 参数时跳过函数
 *     视作空集；
 *   - 被折叠成普通表达式的：每轮 ExecEvalExpr 求值一次（isDone 恒为
 *     SingleResult，即函数式 SRF 已无从谈起）。
 *
 * 内存层次（重要）：
 *   - 参数/函数调用信息分配在调用方提供的 argContext（长生命周期，循环
 *     内每轮 Reset 防膨胀）；ValuePerCall 多次调用间参数必须存活；
 *   - 函数每轮调用切换进 per-tuple 上下文（ResetExprContext 清理函数
 *     泄漏的中间内存）；
 *   - tuplestore 与行类型描述符建立在 per-query 上下文。
 *
 * 结果行类型处理：返回复合类型时从行 Datum 里取类型信息查描述符
 * （记录类型逐行校验 tdtypeid/tdtypmod 一致性，不一致报错）；标量类型
 * 造单列 "column" 描述符；NULL 行展开为全 NULL 行（用 expectedDesc）。
 * 结束后 tupledesc_match 与期望描述符交叉校验，动态描述符释放防泄漏。
 * ============================================================================
 */
Tuplestorestate *
ExecMakeTableFunctionResult(SetExprState *setexpr,
							ExprContext *econtext,
							MemoryContext argContext,
							TupleDesc expectedDesc,
							bool randomAccess)
{
	Tuplestorestate *tupstore = NULL;
	TupleDesc	tupdesc = NULL;
	Oid			funcrettype;
	bool		returnsTuple;
	bool		returnsSet = false;
	FunctionCallInfo fcinfo;
	PgStat_FunctionCallUsage fcusage;
	ReturnSetInfo rsinfo;
	HeapTupleData tmptup;
	MemoryContext callerContext;
	bool		first_time = true;

	/*
	 * Execute per-tablefunc actions in appropriate context.
	 *
	 * The FunctionCallInfo needs to live across all the calls to a
	 * ValuePerCall function, so it can't be allocated in the per-tuple
	 * context. Similarly, the function arguments need to be evaluated in a
	 * context that is longer lived than the per-tuple context: The argument
	 * values would otherwise disappear when we reset that context in the
	 * inner loop.  As the caller's CurrentMemoryContext is typically a
	 * query-lifespan context, we don't want to leak memory there.  We require
	 * the caller to pass a separate memory context that can be used for this,
	 * and can be reset each time through to avoid bloat.
	 */
	MemoryContextReset(argContext);
	callerContext = MemoryContextSwitchTo(argContext);

	funcrettype = exprType((Node *) setexpr->expr);

	returnsTuple = type_is_rowtype(funcrettype);

	/*
	 * Prepare a resultinfo node for communication.  We always do this even if
	 * not expecting a set result, so that we can pass expectedDesc.  In the
	 * generic-expression case, the expression doesn't actually get to see the
	 * resultinfo, but set it up anyway because we use some of the fields as
	 * our own state variables.
	 */
	rsinfo.type = T_ReturnSetInfo;
	rsinfo.econtext = econtext;
	rsinfo.expectedDesc = expectedDesc;
	rsinfo.allowedModes = (int) (SFRM_ValuePerCall | SFRM_Materialize | SFRM_Materialize_Preferred);
	if (randomAccess)
		rsinfo.allowedModes |= (int) SFRM_Materialize_Random;
	rsinfo.returnMode = SFRM_ValuePerCall;
	/* isDone is filled below */
	rsinfo.setResult = NULL;
	rsinfo.setDesc = NULL;

	fcinfo = palloc(SizeForFunctionCallInfo(list_length(setexpr->args)));

	/*
	 * Normally the passed expression tree will be a SetExprState, since the
	 * grammar only allows a function call at the top level of a table
	 * function reference.  However, if the function doesn't return set then
	 * the planner might have replaced the function call via constant-folding
	 * or inlining.  So if we see any other kind of expression node, execute
	 * it via the general ExecEvalExpr() code; the only difference is that we
	 * don't get a chance to pass a special ReturnSetInfo to any functions
	 * buried in the expression.
	 */
	if (!setexpr->elidedFuncState)
	{
		/*
		 * This path is similar to ExecMakeFunctionResultSet.
		 */
		returnsSet = setexpr->funcReturnsSet;
		InitFunctionCallInfoData(*fcinfo, &(setexpr->func),
								 list_length(setexpr->args),
								 setexpr->fcinfo->fncollation,
								 NULL, (Node *) &rsinfo);
		/* evaluate the function's argument list */
		Assert(CurrentMemoryContext == argContext);
		ExecEvalFuncArgs(fcinfo, setexpr->args, econtext);

		/*
		 * If function is strict, and there are any NULL arguments, skip
		 * calling the function and act like it returned NULL (or an empty
		 * set, in the returns-set case).
		 */
		if (setexpr->func.fn_strict)
		{
			int			i;

			for (i = 0; i < fcinfo->nargs; i++)
			{
				if (fcinfo->args[i].isnull)
					goto no_function_result;
			}
		}
	}
	else
	{
		/* Treat setexpr as a generic expression */
		InitFunctionCallInfoData(*fcinfo, NULL, 0, InvalidOid, NULL, NULL);
	}

	/*
	 * Switch to short-lived context for calling the function or expression.
	 */
	MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

	/*
	 * Loop to handle the ValuePerCall protocol (which is also the same
	 * behavior needed in the generic ExecEvalExpr path).
	 */
	for (;;)
	{
		Datum		result;

		CHECK_FOR_INTERRUPTS();

		/*
		 * Reset per-tuple memory context before each call of the function or
		 * expression. This cleans up any local memory the function may leak
		 * when called.
		 */
		ResetExprContext(econtext);

		/* Call the function or expression one time */
		if (!setexpr->elidedFuncState)
		{
			pgstat_init_function_usage(fcinfo, &fcusage);

			fcinfo->isnull = false;
			rsinfo.isDone = ExprSingleResult;
			result = FunctionCallInvoke(fcinfo);

			pgstat_end_function_usage(&fcusage,
									  rsinfo.isDone != ExprMultipleResult);
		}
		else
		{
			result =
				ExecEvalExpr(setexpr->elidedFuncState, econtext, &fcinfo->isnull);
			rsinfo.isDone = ExprSingleResult;
		}

		/* Which protocol does function want to use? */
		if (rsinfo.returnMode == SFRM_ValuePerCall)
		{
			/*
			 * Check for end of result set.
			 */
			if (rsinfo.isDone == ExprEndResult)
				break;

			/*
			 * If first time through, build tuplestore for result.  For a
			 * scalar function result type, also make a suitable tupdesc.
			 */
			if (first_time)
			{
				MemoryContext oldcontext =
					MemoryContextSwitchTo(econtext->ecxt_per_query_memory);

				tupstore = tuplestore_begin_heap(randomAccess, false, work_mem);
				rsinfo.setResult = tupstore;
				if (!returnsTuple)
				{
					tupdesc = CreateTemplateTupleDesc(1);
					TupleDescInitEntry(tupdesc,
									   (AttrNumber) 1,
									   "column",
									   funcrettype,
									   -1,
									   0);
					TupleDescFinalize(tupdesc);
					rsinfo.setDesc = tupdesc;
				}
				MemoryContextSwitchTo(oldcontext);
			}

			/*
			 * Store current resultset item.
			 */
			if (returnsTuple)
			{
				if (!fcinfo->isnull)
				{
					HeapTupleHeader td = DatumGetHeapTupleHeader(result);

					if (tupdesc == NULL)
					{
						MemoryContext oldcontext =
							MemoryContextSwitchTo(econtext->ecxt_per_query_memory);

						/*
						 * This is the first non-NULL result from the
						 * function.  Use the type info embedded in the
						 * rowtype Datum to look up the needed tupdesc.  Make
						 * a copy for the query.
						 */
						tupdesc = lookup_rowtype_tupdesc_copy(HeapTupleHeaderGetTypeId(td),
															  HeapTupleHeaderGetTypMod(td));
						rsinfo.setDesc = tupdesc;
						MemoryContextSwitchTo(oldcontext);
					}
					else
					{
						/*
						 * Verify all later returned rows have same subtype;
						 * necessary in case the type is RECORD.
						 */
						if (HeapTupleHeaderGetTypeId(td) != tupdesc->tdtypeid ||
							HeapTupleHeaderGetTypMod(td) != tupdesc->tdtypmod)
							ereport(ERROR,
									(errcode(ERRCODE_DATATYPE_MISMATCH),
									 errmsg("rows returned by function are not all of the same row type")));
					}

					/*
					 * tuplestore_puttuple needs a HeapTuple not a bare
					 * HeapTupleHeader, but it doesn't need all the fields.
					 */
					tmptup.t_len = HeapTupleHeaderGetDatumLength(td);
					tmptup.t_data = td;

					tuplestore_puttuple(tupstore, &tmptup);
				}
				else
				{
					/*
					 * NULL result from a tuple-returning function; expand it
					 * to a row of all nulls.  We rely on the expectedDesc to
					 * form such rows.  (Note: this would be problematic if
					 * tuplestore_putvalues saved the tdtypeid/tdtypmod from
					 * the provided descriptor, since that might not match
					 * what we get from the function itself.  But it doesn't.)
					 */
					int			natts = expectedDesc->natts;
					bool	   *nullflags;

					nullflags = (bool *) palloc(natts * sizeof(bool));
					memset(nullflags, true, natts * sizeof(bool));
					tuplestore_putvalues(tupstore, expectedDesc, NULL, nullflags);
				}
			}
			else
			{
				/* Scalar-type case: just store the function result */
				tuplestore_putvalues(tupstore, tupdesc, &result, &fcinfo->isnull);
			}

			/*
			 * Are we done?
			 */
			if (rsinfo.isDone != ExprMultipleResult)
				break;

			/*
			 * Check that set-returning functions were properly declared.
			 * (Note: for historical reasons, we don't complain if a non-SRF
			 * returns ExprEndResult; that's treated as returning NULL.)
			 */
			if (!returnsSet)
				ereport(ERROR,
						(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
						 errmsg("table-function protocol for value-per-call mode was not followed")));
		}
		else if (rsinfo.returnMode == SFRM_Materialize)
		{
			/* check we're on the same page as the function author */
			if (!first_time || rsinfo.isDone != ExprSingleResult || !returnsSet)
				ereport(ERROR,
						(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
						 errmsg("table-function protocol for materialize mode was not followed")));
			/* Done evaluating the set result */
			break;
		}
		else
			ereport(ERROR,
					(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
					 errmsg("unrecognized table-function returnMode: %d",
							(int) rsinfo.returnMode)));

		first_time = false;
	}

no_function_result:

	/*
	 * If we got nothing from the function (ie, an empty-set or NULL result),
	 * we have to create the tuplestore to return, and if it's a
	 * non-set-returning function then insert a single all-nulls row.  As
	 * above, we depend on the expectedDesc to manufacture the dummy row.
	 */
	if (rsinfo.setResult == NULL)
	{
		MemoryContext oldcontext =
			MemoryContextSwitchTo(econtext->ecxt_per_query_memory);

		tupstore = tuplestore_begin_heap(randomAccess, false, work_mem);
		rsinfo.setResult = tupstore;
		MemoryContextSwitchTo(oldcontext);

		if (!returnsSet)
		{
			int			natts = expectedDesc->natts;
			bool	   *nullflags;

			nullflags = (bool *) palloc(natts * sizeof(bool));
			memset(nullflags, true, natts * sizeof(bool));
			tuplestore_putvalues(tupstore, expectedDesc, NULL, nullflags);
		}
	}

	/*
	 * If function provided a tupdesc, cross-check it.  We only really need to
	 * do this for functions returning RECORD, but might as well do it always.
	 */
	if (rsinfo.setDesc)
	{
		tupledesc_match(expectedDesc, rsinfo.setDesc);

		/*
		 * If it is a dynamically-allocated TupleDesc, free it: it is
		 * typically allocated in a per-query context, so we must avoid
		 * leaking it across multiple usages.
		 */
		if (rsinfo.setDesc->tdrefcount == -1)
			FreeTupleDesc(rsinfo.setDesc);
	}

	MemoryContextSwitchTo(callerContext);

	/* All done, pass back the tuplestore */
	return rsinfo.setResult;
}


/*
 * ============================================================================
 * 【中文注释】ExecInitFunctionResultSet —— 准备 targetlist 中的 SRF
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为投影表达式里的集合返回函数（FuncExpr 或运算符 OpExpr 形态）构建
 *   SetExprState，供 nodeProjectSet 的"每行 N 行输出"语义使用。
 * 差异：强制允许 SRF（allowSRF=true）/ 需要结果描述符（needDescForSRF=
 * true，ProjectSet 逐行检查结果类型），并断言最终确实选中了返回集的函数。
 * ============================================================================
 */
SetExprState *
ExecInitFunctionResultSet(Expr *expr,
						  ExprContext *econtext, PlanState *parent)
{
	SetExprState *state = makeNode(SetExprState);

	state->funcReturnsSet = true;
	state->expr = expr;
	state->func.fn_oid = InvalidOid;

	/*
	 * Initialize metadata.  The expression node could be either a FuncExpr or
	 * an OpExpr.
	 */
	if (IsA(expr, FuncExpr))
	{
		FuncExpr   *func = (FuncExpr *) expr;

		state->args = ExecInitExprList(func->args, parent);
		init_sexpr(func->funcid, func->inputcollid, expr, state, parent,
				   econtext->ecxt_per_query_memory, true, true);
	}
	else if (IsA(expr, OpExpr))
	{
		OpExpr	   *op = (OpExpr *) expr;

		state->args = ExecInitExprList(op->args, parent);
		init_sexpr(op->opfuncid, op->inputcollid, expr, state, parent,
				   econtext->ecxt_per_query_memory, true, true);
	}
	else
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(expr));

	/* shouldn't get here unless the selected function returns set */
	Assert(state->func.fn_retset);

	return state;
}

/*
 * ============================================================================
 * 【中文注释】ExecMakeFunctionResultSet —— 求值 SRF 参数并调用（逐行协议）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   nodeProjectSet 的核心：每次调用产出目标列展开的一行（或一行结束）。
 *   三种输入阶段（restart 标签协同）：
 *   1. 若上轮 Materialize 结果还没取完——从 funcResultStore 逐行读：
 *      复合结果整体打包成行 Datum 返回；标量结果取第一列；
 *   2. 参数未缓存（setArgsValid=false）时求值参数（在 argContext 中，
 *      保证多行模式下参数值不随 per-tuple 重置消失）后调用函数；
 *      strict+NULL 参数 → 空集；
 *   3. 函数选择 ValuePerCall 且返回 ExprMultipleResult：缓存参数
 *     （setArgsValid=true）并注册清理回调，下次调用跳过参数求值直接
 *      再要一行；
 *   4. 函数选择 Materialize：校验协议后把 tuplestore 收编
 *     （ExecPrepareTuplestoreResult），goto restart 从第 1 阶段逐行吐出。
 *
 * 输出约束：*isDone 指示行流状态（Single=此行即终 / Multiple=可续 /
 * End=结束）；调用方在 per-tuple 上下文调用，argContext 须存活到
 * 结果取尽（isDone 非 Multiple）。
 * ============================================================================
 */
Datum
ExecMakeFunctionResultSet(SetExprState *fcache,
						  ExprContext *econtext,
						  MemoryContext argContext,
						  bool *isNull,
						  ExprDoneCond *isDone)
{
	List	   *arguments;
	Datum		result;
	FunctionCallInfo fcinfo;
	PgStat_FunctionCallUsage fcusage;
	ReturnSetInfo rsinfo;
	bool		callit;
	int			i;

restart:

	/* Guard against stack overflow due to overly complex expressions */
	check_stack_depth();

	/*
	 * If a previous call of the function returned a set result in the form of
	 * a tuplestore, continue reading rows from the tuplestore until it's
	 * empty.
	 */
	if (fcache->funcResultStore)
	{
		TupleTableSlot *slot = fcache->funcResultSlot;
		MemoryContext oldContext;
		bool		foundTup;

		/*
		 * Have to make sure tuple in slot lives long enough, otherwise
		 * clearing the slot could end up trying to free something already
		 * freed.
		 */
		oldContext = MemoryContextSwitchTo(slot->tts_mcxt);
		foundTup = tuplestore_gettupleslot(fcache->funcResultStore, true, false,
										   fcache->funcResultSlot);
		MemoryContextSwitchTo(oldContext);

		if (foundTup)
		{
			*isDone = ExprMultipleResult;
			if (fcache->funcReturnsTuple)
			{
				/* We must return the whole tuple as a Datum. */
				*isNull = false;
				return ExecFetchSlotHeapTupleDatum(fcache->funcResultSlot);
			}
			else
			{
				/* Extract the first column and return it as a scalar. */
				return slot_getattr(fcache->funcResultSlot, 1, isNull);
			}
		}
		/* Exhausted the tuplestore, so clean up */
		tuplestore_end(fcache->funcResultStore);
		fcache->funcResultStore = NULL;
		*isDone = ExprEndResult;
		*isNull = true;
		return (Datum) 0;
	}

	/*
	 * arguments is a list of expressions to evaluate before passing to the
	 * function manager.  We skip the evaluation if it was already done in the
	 * previous call (ie, we are continuing the evaluation of a set-valued
	 * function).  Otherwise, collect the current argument values into fcinfo.
	 *
	 * The arguments have to live in a context that lives at least until all
	 * rows from this SRF have been returned, otherwise ValuePerCall SRFs
	 * would reference freed memory after the first returned row.
	 */
	fcinfo = fcache->fcinfo;
	arguments = fcache->args;
	if (!fcache->setArgsValid)
	{
		MemoryContext oldContext = MemoryContextSwitchTo(argContext);

		ExecEvalFuncArgs(fcinfo, arguments, econtext);
		MemoryContextSwitchTo(oldContext);
	}
	else
	{
		/* Reset flag (we may set it again below) */
		fcache->setArgsValid = false;
	}

	/*
	 * Now call the function, passing the evaluated parameter values.
	 */

	/* Prepare a resultinfo node for communication. */
	fcinfo->resultinfo = (Node *) &rsinfo;
	rsinfo.type = T_ReturnSetInfo;
	rsinfo.econtext = econtext;
	rsinfo.expectedDesc = fcache->funcResultDesc;
	rsinfo.allowedModes = (int) (SFRM_ValuePerCall | SFRM_Materialize);
	/* note we do not set SFRM_Materialize_Random or _Preferred */
	rsinfo.returnMode = SFRM_ValuePerCall;
	/* isDone is filled below */
	rsinfo.setResult = NULL;
	rsinfo.setDesc = NULL;

	/*
	 * If function is strict, and there are any NULL arguments, skip calling
	 * the function.
	 */
	callit = true;
	if (fcache->func.fn_strict)
	{
		for (i = 0; i < fcinfo->nargs; i++)
		{
			if (fcinfo->args[i].isnull)
			{
				callit = false;
				break;
			}
		}
	}

	if (callit)
	{
		pgstat_init_function_usage(fcinfo, &fcusage);

		fcinfo->isnull = false;
		rsinfo.isDone = ExprSingleResult;
		result = FunctionCallInvoke(fcinfo);
		*isNull = fcinfo->isnull;
		*isDone = rsinfo.isDone;

		pgstat_end_function_usage(&fcusage,
								  rsinfo.isDone != ExprMultipleResult);
	}
	else
	{
		/* for a strict SRF, result for NULL is an empty set */
		result = (Datum) 0;
		*isNull = true;
		*isDone = ExprEndResult;
	}

	/* Which protocol does function want to use? */
	if (rsinfo.returnMode == SFRM_ValuePerCall)
	{
		if (*isDone != ExprEndResult)
		{
			/*
			 * Save the current argument values to re-use on the next call.
			 */
			if (*isDone == ExprMultipleResult)
			{
				fcache->setArgsValid = true;
				/* Register cleanup callback if we didn't already */
				if (!fcache->shutdown_reg)
				{
					RegisterExprContextCallback(econtext,
												ShutdownSetExpr,
												PointerGetDatum(fcache));
					fcache->shutdown_reg = true;
				}
			}
		}
	}
	else if (rsinfo.returnMode == SFRM_Materialize)
	{
		/* check we're on the same page as the function author */
		if (rsinfo.isDone != ExprSingleResult)
			ereport(ERROR,
					(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
					 errmsg("table-function protocol for materialize mode was not followed")));
		if (rsinfo.setResult != NULL)
		{
			/* prepare to return values from the tuplestore */
			ExecPrepareTuplestoreResult(fcache, econtext,
										rsinfo.setResult,
										rsinfo.setDesc);
			/* loop back to top to start returning from tuplestore */
			goto restart;
		}
		/* if setResult was left null, treat it as empty set */
		*isDone = ExprEndResult;
		*isNull = true;
		result = (Datum) 0;
	}
	else
		ereport(ERROR,
				(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
				 errmsg("unrecognized table-function returnMode: %d",
						(int) rsinfo.returnMode)));

	return result;
}


/*
 * ============================================================================
 * 【中文注释】init_sexpr —— SetExprState 一次性初始化
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   首次调用前填充 SetExprState 的运行时元数据：
 *   1. 权限：EXECUTE 权限检查 + 函数执行钩子（对象访问钩子）；
 *   2. fmgr：fmgr_info_cxt 绑定函数（信息存到 sexprCxt，防跨查询泄漏）、
 *      绑定表达式（fmgr_info_set_expr，支持返回 RECORD 的函数 ID 动态化）、
 *      预分配 fcinfo（nargs 超 PROC_MAX_ARGS 报错防御）；
 *   3. SRF 契约：函数返回集但调用方不允许（allowSRF=false）时报
 *      "set-valued function called in context that cannot accept a set"；
 *   4. 结果行类型推导（needDescForSRF=true 时）：按函数返回类型分类——
 *      复合类型（查得描述符拷贝进 sexprCxt，funcReturnsTuple=true）、
 *      标量（造单列描述符）、RECORD（描述符留空，靠运行时 expectedDesc）、
 *      其他（留 NULL，用到时失败报"cannot accept type record"）。
 * ============================================================================
 */
static void
init_sexpr(Oid foid, Oid input_collation, Expr *node,
		   SetExprState *sexpr, PlanState *parent,
		   MemoryContext sexprCxt, bool allowSRF, bool needDescForSRF)
{
	AclResult	aclresult;
	size_t		numargs = list_length(sexpr->args);

	/* Check permission to call function */
	aclresult = object_aclcheck(ProcedureRelationId, foid, GetUserId(), ACL_EXECUTE);
	if (aclresult != ACLCHECK_OK)
		aclcheck_error(aclresult, OBJECT_FUNCTION, get_func_name(foid));
	InvokeFunctionExecuteHook(foid);

	/*
	 * Safety check on nargs.  Under normal circumstances this should never
	 * fail, as parser should check sooner.  But possibly it might fail if
	 * server has been compiled with FUNC_MAX_ARGS smaller than some functions
	 * declared in pg_proc?
	 */
	if (list_length(sexpr->args) > FUNC_MAX_ARGS)
		ereport(ERROR,
				(errcode(ERRCODE_TOO_MANY_ARGUMENTS),
				 errmsg_plural("cannot pass more than %d argument to a function",
							   "cannot pass more than %d arguments to a function",
							   FUNC_MAX_ARGS,
							   FUNC_MAX_ARGS)));

	/* Set up the primary fmgr lookup information */
	fmgr_info_cxt(foid, &(sexpr->func), sexprCxt);
	fmgr_info_set_expr((Node *) sexpr->expr, &(sexpr->func));

	/* Initialize the function call parameter struct as well */
	sexpr->fcinfo =
		(FunctionCallInfo) palloc(SizeForFunctionCallInfo(numargs));
	InitFunctionCallInfoData(*sexpr->fcinfo, &(sexpr->func),
							 numargs,
							 input_collation, NULL, NULL);

	/* If function returns set, check if that's allowed by caller */
	if (sexpr->func.fn_retset && !allowSRF)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("set-valued function called in context that cannot accept a set"),
				 parent ? executor_errposition(parent->state,
											   exprLocation((Node *) node)) : 0));

	/* Otherwise, caller should have marked the sexpr correctly */
	Assert(sexpr->func.fn_retset == sexpr->funcReturnsSet);

	/* If function returns set, prepare expected tuple descriptor */
	if (sexpr->func.fn_retset && needDescForSRF)
	{
		TypeFuncClass functypclass;
		Oid			funcrettype;
		TupleDesc	tupdesc;
		MemoryContext oldcontext;

		functypclass = get_expr_result_type(sexpr->func.fn_expr,
											&funcrettype,
											&tupdesc);

		/* Must save tupdesc in sexpr's context */
		oldcontext = MemoryContextSwitchTo(sexprCxt);

		if (functypclass == TYPEFUNC_COMPOSITE ||
			functypclass == TYPEFUNC_COMPOSITE_DOMAIN)
		{
			/* Composite data type, e.g. a table's row type */
			Assert(tupdesc);
			/* Must copy it out of typcache for safety */
			sexpr->funcResultDesc = CreateTupleDescCopy(tupdesc);
			sexpr->funcReturnsTuple = true;
		}
		else if (functypclass == TYPEFUNC_SCALAR)
		{
			/* Base data type, i.e. scalar */
			tupdesc = CreateTemplateTupleDesc(1);
			TupleDescInitEntry(tupdesc,
							   (AttrNumber) 1,
							   NULL,
							   funcrettype,
							   -1,
							   0);
			TupleDescFinalize(tupdesc);
			sexpr->funcResultDesc = tupdesc;
			sexpr->funcReturnsTuple = false;
		}
		else if (functypclass == TYPEFUNC_RECORD)
		{
			/* This will work if function doesn't need an expectedDesc */
			sexpr->funcResultDesc = NULL;
			sexpr->funcReturnsTuple = true;
		}
		else
		{
			/* Else, we will fail if function needs an expectedDesc */
			sexpr->funcResultDesc = NULL;
		}

		MemoryContextSwitchTo(oldcontext);
	}
	else
		sexpr->funcResultDesc = NULL;

	/* Initialize additional state */
	sexpr->funcResultStore = NULL;
	sexpr->funcResultSlot = NULL;
	sexpr->shutdown_reg = false;
}

/*
 * ============================================================================
 * 【中文注释】ShutdownSetExpr —— SRF 提前终止清理回调
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   经 RegisterExprContextCallback 挂到表达式上下文上，在查询/上下文
 *   注销（或 SRF 未放完就被弃用）时释放残留资源：清结果槽、关
 *   tuplestore、复位参数缓存标志。防"槽还指着已释放的 tuplestore"。
 * 注意：回调的注销由 execUtils 的上下文清理流程统一完成。
 * ============================================================================
 */
static void
ShutdownSetExpr(Datum arg)
{
	SetExprState *sexpr = castNode(SetExprState, DatumGetPointer(arg));

	/* If we have a slot, make sure it's let go of any tuplestore pointer */
	if (sexpr->funcResultSlot)
		ExecClearTuple(sexpr->funcResultSlot);

	/* Release any open tuplestore */
	if (sexpr->funcResultStore)
		tuplestore_end(sexpr->funcResultStore);
	sexpr->funcResultStore = NULL;

	/* Clear any active set-argument state */
	sexpr->setArgsValid = false;

	/* execUtils will deregister the callback... */
	sexpr->shutdown_reg = false;
}

/*
 * ============================================================================
 * 【中文注释】ExecEvalFuncArgs —— 批量求值函数实参
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把参数表达式列表逐项 ExecEvalExpr 求值，写进 fcinfo->args
 *   （value/isnull 对），数量必须与函数声明一致（断言）。
 * 注意：值分配在当前内存上下文，调用方须保证存活期覆盖全部 SRF 调用
 * （典型是 argContext，见 ExecMakeFunctionResultSet 的用法）。
 * ============================================================================
 */
static void
ExecEvalFuncArgs(FunctionCallInfo fcinfo,
				 List *argList,
				 ExprContext *econtext)
{
	int			i;
	ListCell   *arg;

	i = 0;
	foreach(arg, argList)
	{
		ExprState  *argstate = (ExprState *) lfirst(arg);

		fcinfo->args[i].value = ExecEvalExpr(argstate,
											 econtext,
											 &fcinfo->args[i].isnull);
		i++;
	}

	Assert(i == fcinfo->nargs);
}

/*
 * ============================================================================
 * 【中文注释】ExecPrepareTuplestoreResult —— 收编 Materialize 模式的 tuplestore
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   函数用 SFRM_Materialize 交出结果后，为逐行消费做准备：
 *   1. 缓存 ResultStore；首次收编时创建结果槽（行类型：优先
 *      funcResultDesc，其次拷贝 resultDesc——不假定其长命，再次为空则
 *      报"cannot accept type record"）；
 *   2. resultDesc 与期望描述符交叉校验（tupledesc_match），动态描述符
 *      立即释放（防跨查询泄漏）；
 *   3. 注册 ShutdownSetExpr 兜底清理（防循环内提前放弃）。
 * ============================================================================
 */
static void
ExecPrepareTuplestoreResult(SetExprState *sexpr,
							ExprContext *econtext,
							Tuplestorestate *resultStore,
							TupleDesc resultDesc)
{
	sexpr->funcResultStore = resultStore;

	if (sexpr->funcResultSlot == NULL)
	{
		/* Create a slot so we can read data out of the tuplestore */
		TupleDesc	slotDesc;
		MemoryContext oldcontext;

		oldcontext = MemoryContextSwitchTo(sexpr->func.fn_mcxt);

		/*
		 * If we were not able to determine the result rowtype from context,
		 * and the function didn't return a tupdesc, we have to fail.
		 */
		if (sexpr->funcResultDesc)
			slotDesc = sexpr->funcResultDesc;
		else if (resultDesc)
		{
			/* don't assume resultDesc is long-lived */
			slotDesc = CreateTupleDescCopy(resultDesc);
		}
		else
		{
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("function returning setof record called in "
							"context that cannot accept type record")));
			slotDesc = NULL;	/* keep compiler quiet */
		}

		sexpr->funcResultSlot = MakeSingleTupleTableSlot(slotDesc,
														 &TTSOpsMinimalTuple);
		MemoryContextSwitchTo(oldcontext);
	}

	/*
	 * If function provided a tupdesc, cross-check it.  We only really need to
	 * do this for functions returning RECORD, but might as well do it always.
	 */
	if (resultDesc)
	{
		if (sexpr->funcResultDesc)
			tupledesc_match(sexpr->funcResultDesc, resultDesc);

		/*
		 * If it is a dynamically-allocated TupleDesc, free it: it is
		 * typically allocated in a per-query context, so we must avoid
		 * leaking it across multiple usages.
		 */
		if (resultDesc->tdrefcount == -1)
			FreeTupleDesc(resultDesc);
	}

	/* Register cleanup callback if we didn't already */
	if (!sexpr->shutdown_reg)
	{
		RegisterExprContextCallback(econtext,
									ShutdownSetExpr,
									PointerGetDatum(sexpr));
		sexpr->shutdown_reg = true;
	}
}

/*
 * ============================================================================
 * 【中文注释】tupledesc_match —— 校验函数返回行类型与查询期望一致
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   逐属性比对 dst（查询期望）与 src（函数实际返回）描述符：列数必须
 *   相同（errdetail_plural 报数）；每列类型可按二进制强制转换（一个
 *   例外来自缓存计划的陈旧描述符）则不追究；其余必须一致——但 dst 列
 *   已删除（attisdropped）时允许类型不符，只要物理存储（长度/对齐）
 *   一致即可（历史遗留的行布局兼容）。
 * ============================================================================
 */
static void
tupledesc_match(TupleDesc dst_tupdesc, TupleDesc src_tupdesc)
{
	int			i;

	if (dst_tupdesc->natts != src_tupdesc->natts)
		ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("function return row and query-specified return row do not match"),
				 errdetail_plural("Returned row contains %d attribute, but query expects %d.",
								  "Returned row contains %d attributes, but query expects %d.",
								  src_tupdesc->natts,
								  src_tupdesc->natts, dst_tupdesc->natts)));

	for (i = 0; i < dst_tupdesc->natts; i++)
	{
		Form_pg_attribute dattr = TupleDescAttr(dst_tupdesc, i);
		Form_pg_attribute sattr = TupleDescAttr(src_tupdesc, i);

		if (IsBinaryCoercible(sattr->atttypid, dattr->atttypid))
			continue;			/* no worries */
		if (!dattr->attisdropped)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("function return row and query-specified return row do not match"),
					 errdetail("Returned type %s at ordinal position %d, but query expects %s.",
							   format_type_be(sattr->atttypid),
							   i + 1,
							   format_type_be(dattr->atttypid))));

		if (dattr->attlen != sattr->attlen ||
			dattr->attalign != sattr->attalign)
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("function return row and query-specified return row do not match"),
					 errdetail("Physical storage mismatch on dropped attribute at ordinal position %d.",
							   i + 1)));
	}
}
