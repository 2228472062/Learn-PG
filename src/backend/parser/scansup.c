/*-------------------------------------------------------------------------
 *
 * scansup.c
 *	  scanner support routines used by the core lexer
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/parser/scansup.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <ctype.h>

#include "mb/pg_wchar.h"
#include "parser/scansup.h"
#include "utils/pg_locale.h"


/*
 * downcase_truncate_identifier() --- do appropriate downcasing and
 * truncation of an unquoted identifier.  Optionally warn of truncation.
 *
 * Returns a palloc'd string containing the adjusted identifier.
 *
 * Note: in some usages the passed string is not null-terminated.
 *
 * Note: the API of this function is designed to allow for downcasing
 * transformations that increase the string length, but we don't yet
 * support that.  If you want to implement it, you'll need to fix
 * SplitIdentifierString() in utils/adt/varlena.c.
 *
 * 【中文总述】
 * 对未加引号的标识符进行小写转换和截断处理。
 * 这是 downcase_identifier() 的简单封装，始终启用截断。
 * 【调用链】scanner/gram.y → downcase_truncate_identifier()
 *   → downcase_identifier() → pg_downcase_ident() + truncate_identifier()
 */
char *
downcase_truncate_identifier(const char *ident, int len, bool warn)
{
	return downcase_identifier(ident, len, warn, true);
}

/*
 * a workhorse for downcase_truncate_identifier
 *
 * 【中文总述】
 * downcase_truncate_identifier() 的核心工作函数。
 * 执行实际的小写转换（pg_downcase_ident），然后根据需要截断到 NAMEDATALEN-1。
 * 注意：如果未来需要支持 Unicode 感知的标识符大小写转换，
 * 需要同时修改 pg_downcase_ident 和 SplitIdentifierString。
 * 【调用链】downcase_truncate_identifier() → downcase_identifier()
 *   → pg_downcase_ident() + truncate_identifier()
 */
char *
downcase_identifier(const char *ident, int len, bool warn, bool truncate)
{
	char	   *result;
	size_t		needed pg_attribute_unused();

	/*
	 * Preserves string length.
	 *
	 * NB: if we decide to support Unicode-aware identifier case folding, then
	 * we need to account for a change in string length.
	 */
	result = palloc(len + 1);

	needed = pg_downcase_ident(result, len + 1, ident, len);
	Assert(needed == len);
	Assert(result[len] == '\0');

	if (len >= NAMEDATALEN && truncate)
		truncate_identifier(result, len, warn);

	return result;
}


/*
 * truncate_identifier() --- truncate an identifier to NAMEDATALEN-1 bytes.
 *
 * The given string is modified in-place, if necessary.  A warning is
 * issued if requested.
 *
 * We require the caller to pass in the string length since this saves a
 * strlen() call in some common usages.
 *
 * 【中文总述】
 * 将标识符截断到 NAMEDATALEN-1 字节。
 * 如果标识符长度超过限制，先用 pg_mbcliplen 按字符边界截断，
 * 然后发出 NOTICE 警告（如果 warn 为 true），最后补 '\0'。
 * 【调用链】downcase_identifier() → truncate_identifier()
 */
void
truncate_identifier(char *ident, int len, bool warn)
{
	if (len >= NAMEDATALEN)
	{
		len = pg_mbcliplen(ident, len, NAMEDATALEN - 1);
		if (warn)
			ereport(NOTICE,
					(errcode(ERRCODE_NAME_TOO_LONG),
					 errmsg("identifier \"%s\" will be truncated to \"%.*s\"",
							ident, len, ident)));
		ident[len] = '\0';
	}
}

/*
 * scanner_isspace() --- return true if flex scanner considers char whitespace
 *
 * This should be used instead of the potentially locale-dependent isspace()
 * function when it's important to match the lexer's behavior.
 *
 * In principle we might need similar functions for isalnum etc, but for the
 * moment only isspace seems needed.
 *
 * 【中文总述】
 * 检查字符是否被 flex 词法分析器视为空白符。
 * 必须与 scan.l 中的 {space} 字符列表保持一致，避免因本地化
 * 设置不同而与词法分析器行为不一致。
 * 【调用链】scan.l / base_yylex() → scanner_isspace() → 判断空白符 */
bool
scanner_isspace(char ch)
{
	/* This must match scan.l's list of {space} characters */
	if (ch == ' ' ||
		ch == '\t' ||
		ch == '\n' ||
		ch == '\r' ||
		ch == '\v' ||
		ch == '\f')
		return true;
	return false;
}
