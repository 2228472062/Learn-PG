/*
 * gramparse.h
 *		Shared definitions for the "raw" parser (flex and bison phases only)
 *
 * NOTE: this file is only meant to be included in the core parsing files,
 * i.e., parser.c, gram.y, and scan.l.
 * Definitions that are needed outside the core parser should be in parser.h.
 *
 * 【中文总述】
 * 原始解析器（raw parser）的共享定义头文件。
 * 供 flex（scan.l）和 bison（gram.y）以及 parser.c 使用。
 * 包含：
 *   1. base_yy_extra_type 结构体：flex 扫描器的扩展状态，
 *      包含核心词法分析器状态、前瞻 token信息和最终解析树结果
 *   2. pg_yyget_extra() 宏：快速访问 yyscanner 中的 yyextra 字段
 *   3. 外部函数声明：base_yylex（词法分析过滤器）、
 *      parser_init 和 base_yyparse（语法分析器）
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/parser/gramparse.h
 *
 *-------------------------------------------------------------------------
 */

#ifndef GRAMPARSE_H
#define GRAMPARSE_H

#include "nodes/parsenodes.h"
#include "parser/scanner.h"

/*
 * NB: include gram.h only AFTER including scanner.h, because scanner.h
 * is what #defines YYLTYPE.
 */
#include "gram.h"

/*
 * The YY_EXTRA data that a flex scanner allows us to pass around.  Private
 * state needed for raw parsing/lexing goes here.
 *
 * 【中文】YY_EXTRA 是 flex 允许用户传入的私有状态结构体，
 * 这里存放原始解析/词法分析阶段需要的所有上下文数据。
 */
typedef struct base_yy_extra_type
{
	/*
	 * Fields used by the core scanner.
	 */
	core_yy_extra_type core_yy_extra;

	/*
	 * State variables for base_yylex().
	 */
	bool		have_lookahead; /* is lookahead info valid? */
	int			lookahead_token;	/* one-token lookahead */
	core_YYSTYPE lookahead_yylval;	/* yylval for lookahead token */
	YYLTYPE		lookahead_yylloc;	/* yylloc for lookahead token */
	char	   *lookahead_end;	/* end of current token */
	char		lookahead_hold_char;	/* to be put back at *lookahead_end */

	/*
	 * State variables that belong to the grammar.
	 */
	List	   *parsetree;		/* final parse result is delivered here */
} base_yy_extra_type;

/*
 * In principle we should use yyget_extra() to fetch the yyextra field
 * from a yyscanner struct.  However, flex always puts that field first,
 * and this is sufficiently performance-critical to make it seem worth
 * cheating a bit to use an inline macro.
 *
 * 【中文】通过内联宏直接访问 yyscanner 内部的 yyextra 指针，
 * 避免 yyget_extra() 的函数调用开销。flex 保证 yyextra
 * 字段在 yyscanner 结构体的最前面，所以可以用强制类型转换
 * 直接取地址。
 */
#define pg_yyget_extra(yyscanner) (*((base_yy_extra_type **) (yyscanner)))


/* from parser.c */
extern int	base_yylex(YYSTYPE *lvalp, YYLTYPE *llocp,
					   core_yyscan_t yyscanner);

/* from gram.y */
extern void parser_init(base_yy_extra_type *yyext);
extern int	base_yyparse(core_yyscan_t yyscanner);

#endif							/* GRAMPARSE_H */
