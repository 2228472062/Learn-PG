/*-------------------------------------------------------------------------
 *
 * parse_param.c
 *	  handle parameters in parser
 *
 * This code covers two cases that are used within the core backend:
 *		* a fixed list of parameters with known types
 *		* an expandable list of parameters whose types can optionally
 *		  be determined from context
 * In both cases, only explicit $n references (ParamRef nodes) are supported.
 *
 * Note that other approaches to parameters are possible using the parser
 * hooks defined in ParseState.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/parser/parse_param.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <limits.h>

#include "catalog/pg_type.h"
#include "nodes/nodeFuncs.h"
#include "parser/parse_param.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"


typedef struct FixedParamState
{
	const Oid  *paramTypes;		/* array of parameter type OIDs */
	int			numParams;		/* number of array entries */
} FixedParamState;

/*
 * In the varparams case, the caller-supplied OID array (if any) can be
 * re-palloc'd larger at need.  A zero array entry means that parameter number
 * hasn't been seen, while UNKNOWNOID means the parameter has been used but
 * its type is not yet known.
 */
typedef struct VarParamState
{
	Oid		  **paramTypes;		/* array of parameter type OIDs */
	int		   *numParams;		/* number of array entries */
} VarParamState;

static Node *fixed_paramref_hook(ParseState *pstate, ParamRef *pref);
static Node *variable_paramref_hook(ParseState *pstate, ParamRef *pref);
static Node *variable_coerce_param_hook(ParseState *pstate, Param *param,
										Oid targetTypeId, int32 targetTypeMod,
										int location);
static bool check_parameter_resolution_walker(Node *node, ParseState *pstate);
static bool query_contains_extern_params_walker(Node *node, void *context);


/*
 * Set up to process a query containing references to fixed parameters.
 *
 * 【中文总述】设置固定参数解析状态：参数类型在编译时已知（Oid 数组），
 * 解析 $n 时直接查表映射到 Param 节点，无需类型推断。
 * 【调用链】由 raw_parser() → analyze.c 中的 parse_analyze() 调用，
 * 用于预处理含固定参数的查询。
 */
void
setup_parse_fixed_parameters(ParseState *pstate,
							 const Oid *paramTypes, int numParams)
{
	FixedParamState *parstate = palloc_object(FixedParamState);

	parstate->paramTypes = paramTypes;
	parstate->numParams = numParams;
	pstate->p_ref_hook_state = parstate;
	pstate->p_paramref_hook = fixed_paramref_hook;
	/* no need to use p_coerce_param_hook */
}

/*
 * Set up to process a query containing references to variable parameters.
 *
 * 【中文总述】设置可变参数解析状态：参数类型初始为 UNKNOWN，
 * 解析时根据上下文推断具体类型，参数数组可动态扩容。
 * 【调用链】由 raw_parser() → analyze.c 中的 parse_analyze() 调用，
 * 用于预处理含可变参数（$1, $2...）的查询。
 */
void
setup_parse_variable_parameters(ParseState *pstate,
								Oid **paramTypes, int *numParams)
{
	VarParamState *parstate = palloc_object(VarParamState);

	parstate->paramTypes = paramTypes;
	parstate->numParams = numParams;
	pstate->p_ref_hook_state = parstate;
	pstate->p_paramref_hook = variable_paramref_hook;
	pstate->p_coerce_param_hook = variable_coerce_param_hook;
}

/*
 * Transform a ParamRef using fixed parameter types.
 *
 * 【中文总述】处理固定参数 $n 的引用：检查参数编号有效性，
 * 从预定义类型数组中查找类型，创建 Param 节点。
 * 【调用链】被 p_paramref_hook 回调调用（由 parse_expr.c 中的
 * transformParamRef 触发），解析 SQL 中的 $n 参数引用。
 */
static Node *
fixed_paramref_hook(ParseState *pstate, ParamRef *pref)
{
	FixedParamState *parstate = (FixedParamState *) pstate->p_ref_hook_state;
	int			paramno = pref->number;
	Param	   *param;

	/* Check parameter number is valid */
	if (paramno <= 0 || paramno > parstate->numParams ||
		!OidIsValid(parstate->paramTypes[paramno - 1]))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_PARAMETER),
				 errmsg("there is no parameter $%d", paramno),
				 parser_errposition(pstate, pref->location)));

	param = makeNode(Param);
	param->paramkind = PARAM_EXTERN;
	param->paramid = paramno;
	param->paramtype = parstate->paramTypes[paramno - 1];
	param->paramtypmod = -1;
	param->paramcollid = get_typcollation(param->paramtype);
	param->location = pref->location;

	return (Node *) param;
}

/*
 * Transform a ParamRef using variable parameter types.
 *
 * The only difference here is we must enlarge the parameter type array
 * as needed.
 *
 * 【中文总述】处理可变参数 $n 的引用：若参数编号超出当前数组则扩容，
 * 初始化未见过的参数为 UNKNOWN 类型，对 void 类型参数做特殊处理
 *（允许 JDBC 驱动不区分函数与过程调用）。
 * 【调用链】被 p_paramref_hook 回调调用，在解析含可变参数的 SQL 时触发；
 * 参数类型后续由 variable_coerce_param_hook 在类型推断阶段确定。
 */
static Node *
variable_paramref_hook(ParseState *pstate, ParamRef *pref)
{
	VarParamState *parstate = (VarParamState *) pstate->p_ref_hook_state;
	int			paramno = pref->number;
	Oid		   *pptype;
	Param	   *param;

	/* Check parameter number is in range */
	if (paramno <= 0 || paramno > MaxAllocSize / sizeof(Oid))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_PARAMETER),
				 errmsg("there is no parameter $%d", paramno),
				 parser_errposition(pstate, pref->location)));
	if (paramno > *parstate->numParams)
	{
		/* Need to enlarge param array */
		if (*parstate->paramTypes)
			*parstate->paramTypes = repalloc0_array(*parstate->paramTypes, Oid,
													*parstate->numParams, paramno);
		else
			*parstate->paramTypes = palloc0_array(Oid, paramno);
		*parstate->numParams = paramno;
	}

	/* Locate param's slot in array */
	pptype = &(*parstate->paramTypes)[paramno - 1];

	/* If not seen before, initialize to UNKNOWN type */
	if (*pptype == InvalidOid)
		*pptype = UNKNOWNOID;

	/*
	 * If the argument is of type void and it's procedure call, interpret it
	 * as unknown.  This allows the JDBC driver to not have to distinguish
	 * function and procedure calls.  See also another component of this hack
	 * in ParseFuncOrColumn().
	 */
	if (*pptype == VOIDOID && pstate->p_expr_kind == EXPR_KIND_CALL_ARGUMENT)
		*pptype = UNKNOWNOID;

	param = makeNode(Param);
	param->paramkind = PARAM_EXTERN;
	param->paramid = paramno;
	param->paramtype = *pptype;
	param->paramtypmod = -1;
	param->paramcollid = get_typcollation(param->paramtype);
	param->location = pref->location;

	return (Node *) param;
}

/*
 * Coerce a Param to a query-requested datatype, in the varparams case.
 *
 * 【中文总述】在可变参数场景下，将 Param 从 UNKNOWN 类型强制转换
 * 为查询请求的目标类型，并记录类型信息。若类型已确定且匹配则跳过，
 * 若前后推断不一致则报错。
 * 【调用链】被 p_coerce_param_hook 回调调用（由 transformExpr /
 * coerce_to_target_type 触发），在表达式类型推断阶段对 UNKNOWN
 * 类型参数进行类型解析。
 */
static Node *
variable_coerce_param_hook(ParseState *pstate, Param *param,
						   Oid targetTypeId, int32 targetTypeMod,
						   int location)
{
	if (param->paramkind == PARAM_EXTERN && param->paramtype == UNKNOWNOID)
	{
		/*
		 * Input is a Param of previously undetermined type, and we want to
		 * update our knowledge of the Param's type.
		 */
		VarParamState *parstate = (VarParamState *) pstate->p_ref_hook_state;
		Oid		   *paramTypes = *parstate->paramTypes;
		int			paramno = param->paramid;

		if (paramno <= 0 ||		/* shouldn't happen, but... */
			paramno > *parstate->numParams)
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_PARAMETER),
					 errmsg("there is no parameter $%d", paramno),
					 parser_errposition(pstate, param->location)));

		if (paramTypes[paramno - 1] == UNKNOWNOID)
		{
			/* We've successfully resolved the type */
			paramTypes[paramno - 1] = targetTypeId;
		}
		else if (paramTypes[paramno - 1] == targetTypeId)
		{
			/* We previously resolved the type, and it matches */
		}
		else
		{
			/* Oops */
			ereport(ERROR,
					(errcode(ERRCODE_AMBIGUOUS_PARAMETER),
					 errmsg("inconsistent types deduced for parameter $%d",
							paramno),
					 errdetail("%s versus %s",
							   format_type_be(paramTypes[paramno - 1]),
							   format_type_be(targetTypeId)),
					 parser_errposition(pstate, param->location)));
		}

		param->paramtype = targetTypeId;

		/*
		 * Note: it is tempting here to set the Param's paramtypmod to
		 * targetTypeMod, but that is probably unwise because we have no
		 * infrastructure that enforces that the value delivered for a Param
		 * will match any particular typmod.  Leaving it -1 ensures that a
		 * run-time length check/coercion will occur if needed.
		 */
		param->paramtypmod = -1;

		/*
		 * This module always sets a Param's collation to be the default for
		 * its datatype.  If that's not what you want, you should be using the
		 * more general parser substitution hooks.
		 */
		param->paramcollid = get_typcollation(param->paramtype);

		/* Use the leftmost of the param's and coercion's locations */
		if (location >= 0 &&
			(param->location < 0 || location < param->location))
			param->location = location;

		return (Node *) param;
	}

	/* Else signal to proceed with normal coercion */
	return NULL;
}

/*
 * Check for consistent assignment of variable parameters after completion
 * of parsing with parse_variable_parameters.
 *
 * Note: this code intentionally does not check that all parameter positions
 * were used, nor that all got non-UNKNOWN types assigned.  Caller of parser
 * should enforce that if it's important.
 *
 * 【中文总述】在可变参数解析完成后，遍历查询树检查参数类型
 * 是否一致解析（防止同一 $n 在不同位置被推断为不同类型）。
 * 【调用链】由 parse_analyze() 在 parse_variable_parameters()
 * 之后调用，确保参数类型推断的完整性。
 */
void
check_variable_parameters(ParseState *pstate, Query *query)
{
	VarParamState *parstate = (VarParamState *) pstate->p_ref_hook_state;

	/* If numParams is zero then no Params were generated, so no work */
	if (*parstate->numParams > 0)
		(void) query_tree_walker(query,
								 check_parameter_resolution_walker,
								 pstate, 0);
}

/*
 * Traverse a fully-analyzed tree to verify that parameter symbols
 * match their types. We need this because some Params might still
 * be UNKNOWN, if there wasn't anything to force their coercion,
 * and yet other instances seen later might have gotten coerced.
 *
 * 【中文总述】递归遍历已分析的查询树，验证所有 PARAM_EXTERN
 * 参数是否都获得了确定的类型（不能仍为 UNKNOWN）。
 * 【调用链】被 check_variable_parameters() 通过 query_tree_walker 调用；
 * 内部递归调用自身处理子查询和表达式树。
 */
static bool
check_parameter_resolution_walker(Node *node, ParseState *pstate)
{
	if (node == NULL)
		return false;
	if (IsA(node, Param))
	{
		Param	   *param = (Param *) node;

		if (param->paramkind == PARAM_EXTERN)
		{
			VarParamState *parstate = (VarParamState *) pstate->p_ref_hook_state;
			int			paramno = param->paramid;

			if (paramno <= 0 || /* shouldn't happen, but... */
				paramno > *parstate->numParams)
				ereport(ERROR,
						(errcode(ERRCODE_UNDEFINED_PARAMETER),
						 errmsg("there is no parameter $%d", paramno),
						 parser_errposition(pstate, param->location)));

			if (param->paramtype != (*parstate->paramTypes)[paramno - 1])
				ereport(ERROR,
						(errcode(ERRCODE_AMBIGUOUS_PARAMETER),
						 errmsg("could not determine data type of parameter $%d",
								paramno),
						 parser_errposition(pstate, param->location)));
		}
		return false;
	}
	if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		return query_tree_walker((Query *) node,
								 check_parameter_resolution_walker,
								 pstate, 0);
	}
	return expression_tree_walker(node, check_parameter_resolution_walker,
								  pstate);
}

/*
 * Check to see if a fully-parsed query tree contains any PARAM_EXTERN Params.
 *
 * 【中文总述】检查一个已解析的查询树中是否包含任何
 * PARAM_EXTERN 类型的参数引用。
 * 【调用链】被 analyze.c 或其他分析阶段调用，
 * 用于判断查询是否依赖外部参数。
 */
bool
query_contains_extern_params(Query *query)
{
	return query_tree_walker(query,
							 query_contains_extern_params_walker,
							 NULL, 0);
}

/*
 * 【中文总述】递归遍历查询树，查找 PARAM_EXTERN 类型的
 * Param 节点，找到即返回 true。
 * 【调用链】被 query_contains_extern_params() 通过
 * query_tree_walker 调用；内部递归调用自身处理子查询
 * 和表达式树。
 */
static bool
query_contains_extern_params_walker(Node *node, void *context)
{
		return false;
	if (IsA(node, Param))
	{
		Param	   *param = (Param *) node;

		if (param->paramkind == PARAM_EXTERN)
			return true;
		return false;
	}
	if (IsA(node, Query))
	{
		/* Recurse into RTE subquery or not-yet-planned sublink subquery */
		return query_tree_walker((Query *) node,
								 query_contains_extern_params_walker,
								 context, 0);
	}
	return expression_tree_walker(node, query_contains_extern_params_walker,
								  context);
}
