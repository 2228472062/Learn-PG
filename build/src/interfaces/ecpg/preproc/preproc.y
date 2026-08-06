/* header */
/* src/interfaces/ecpg/preproc/ecpg.header */

/* Copyright comment */
%{
#include "postgres_fe.h"

#include "preproc_extern.h"
#include "preproc.h"
#include "ecpg_config.h"
#include <unistd.h>

/* silence -Wmissing-variable-declarations */
extern int base_yychar;
extern int base_yynerrs;


/*
 * The %name-prefix option below will make bison call base_yylex, but we
 * really want it to call filtered_base_yylex (see parser.c).
 */
#define base_yylex filtered_base_yylex

/*
 * This is only here so the string gets into the POT.  Bison uses it
 * internally.
 */
#define bison_gettext_dummy gettext_noop("syntax error")

/*
 * Variables containing simple states.
 */
int			struct_level = 0;
int			braces_open;		/* brace level counter */
char	   *current_function;
int			ecpg_internal_var = 0;
char	   *connection = NULL;
char	   *input_filename = NULL;

static int	FoundInto = 0;
static int	initializer = 0;
static int	pacounter = 1;
static struct this_type actual_type[STRUCT_DEPTH];
static char *actual_startline[STRUCT_DEPTH];
static int	varchar_counter = 1;
static int	bytea_counter = 1;

/*
 * We temporarily store struct members here while parsing struct declarations.
 * The struct_member_list (at a given nesting depth) is constructed while
 * scanning the fields within "struct { .... }", but we can't remove it upon
 * seeing the right brace.  It's kept around and copied into the variables
 * or typedefs that follow, in order to handle cases like
 * "struct foo { ... } foovar1, foovar2;".  We recycle the storage only
 * upon closing the current nesting level or starting the next struct
 * declaration within the same nesting level.
 * For cases like "struct foo foovar1, foovar2;", we copy the saved struct
 * field list for the typedef or struct tag into the struct_member_list
 * global variable, and then copy it again to the newly-declared variables.
 */
struct ECPGstruct_member *struct_member_list[STRUCT_DEPTH] = {NULL};

/* also store struct type so we can do a sizeof() later */
static char *ECPGstruct_sizeof = NULL;

/* for forward declarations we have to store some data as well */
static char *forward_name = NULL;

struct ECPGtype ecpg_no_indicator = {ECPGt_NO_INDICATOR, NULL, NULL, NULL, {NULL}, 0};
struct variable no_indicator = {"no_indicator", &ecpg_no_indicator, 0, NULL};

static struct ECPGtype ecpg_query = {ECPGt_char_variable, NULL, NULL, NULL, {NULL}, 0};

static bool check_declared_list(const char *name);
static void update_connection(const char *newconn);


/*
 * "Location tracking" support.  We commandeer Bison's location tracking
 * mechanism to manage the output string for productions that ordinarily would
 * return a <str> result.  This allows the majority of those productions to
 * have default semantic actions, reducing the size of the parser, and also
 * greatly reducing its compilation time on some versions of clang.
 *
 * To do this, we make YYLTYPE be a pointer to a malloc'd string, and then
 * merge the location strings of the input tokens in the default YYLLOC
 * computation.  Productions that are okay with the standard merge need not
 * do anything more; otherwise, they can override it by assigning to @$.
 */
#define YYLLOC_DEFAULT(Current, Rhs, N) yylloc_default(&(Current), Rhs, N)

static void
yylloc_default(YYLTYPE *target, YYLTYPE *rhs, int N)
{
	if (N > 1)
	{
		/* Concatenate non-empty inputs with one space between them */
		char	   *result,
				   *ptr;
		size_t		needed = 0;

		for (int i = 1; i <= N; i++)
		{
			size_t		thislen = strlen(rhs[i]);

			if (needed > 0 && thislen > 0)
				needed++;
			needed += thislen;
		}
		result = (char *) loc_alloc(needed + 1);
		ptr = result;
		for (int i = 1; i <= N; i++)
		{
			size_t		thislen = strlen(rhs[i]);

			if (ptr > result && thislen > 0)
				*ptr++ = ' ';
			memcpy(ptr, rhs[i], thislen);
			ptr += thislen;
		}
		*ptr = '\0';
		*target = result;
	}
	else if (N == 1)
	{
		/* Just re-use the single input */
		*target = rhs[1];
	}
	else
	{
		/* No need to allocate any space */
		*target = "";
	}
}

/* and the rest */
static char *
create_questionmarks(const char *name, bool array)
{
	struct variable *p = find_variable(name);
	int			count;
	char	   *result = "";

	/*
	 * In case we have a struct, we have to print as many "?" as there are
	 * attributes in the struct
	 *
	 * An array is only allowed together with an element argument
	 *
	 * This is essentially only used for inserts, but using a struct as input
	 * parameter is an error anywhere else so we don't have to worry here.
	 */

	if (p->type->type == ECPGt_struct || (array && p->type->type == ECPGt_array && p->type->u.element->type == ECPGt_struct))
	{
		struct ECPGstruct_member *m;

		if (p->type->type == ECPGt_struct)
			m = p->type->u.members;
		else
			m = p->type->u.element->u.members;

		for (count = 0; m != NULL; m = m->next, count++);
	}
	else
		count = 1;

	for (; count > 0; count--)
	{
		char	buf[32];

		snprintf(buf, sizeof(buf), "$%d", pacounter++);
		result = cat_str(3, result, buf, " , ");
	}

	/* remove the trailing " ," */
	result[strlen(result) - 3] = '\0';
	return result;
}

static char *
adjust_outofscope_cursor_vars(struct cursor *cur)
{
	/*
	 * Informix accepts DECLARE with variables that are out of scope when OPEN
	 * is called. For instance you can DECLARE a cursor in one function, and
	 * OPEN/FETCH/CLOSE it in another functions. This is very useful for e.g.
	 * event-driver programming, but may also lead to dangerous programming.
	 * The limitation when this is allowed and doesn't cause problems have to
	 * be documented, like the allocated variables must not be realloc()'ed.
	 *
	 * We have to change the variables to our own struct and just store the
	 * pointer instead of the variable. Do it only for local variables, not
	 * for globals.
	 */
	char	   *result = "";
	int			insert;

	for (insert = 1; insert >= 0; insert--)
	{
		struct arguments *list;
		struct arguments *ptr;
		struct arguments *newlist = NULL;
		struct variable *newvar,
				   *newind;

		list = (insert ? cur->argsinsert : cur->argsresult);

		for (ptr = list; ptr != NULL; ptr = ptr->next)
		{
			char		var_text[20];
			char	   *original_var;
			bool		skip_set_var = false;
			bool		var_ptr = false;

			/* change variable name to "ECPGget_var(<counter>)" */
			original_var = ptr->variable->name;
			snprintf(var_text, sizeof(var_text), "%d))", ecpg_internal_var);

			/* Don't emit ECPGset_var() calls for global variables */
			if (ptr->variable->brace_level == 0)
			{
				newvar = ptr->variable;
				skip_set_var = true;
			}
			else if ((ptr->variable->type->type == ECPGt_char_variable)
					 && (strncmp(ptr->variable->name, "ECPGprepared_statement", strlen("ECPGprepared_statement")) == 0))
			{
				newvar = ptr->variable;
				skip_set_var = true;
			}
			else if ((ptr->variable->type->type != ECPGt_varchar
					  && ptr->variable->type->type != ECPGt_char
					  && ptr->variable->type->type != ECPGt_unsigned_char
					  && ptr->variable->type->type != ECPGt_string
					  && ptr->variable->type->type != ECPGt_bytea)
					 && atoi(ptr->variable->type->size) > 1)
			{
				newvar = new_variable(cat_str(4, "(",
											  ecpg_type_name(ptr->variable->type->u.element->type),
											  " *)(ECPGget_var(",
											  var_text),
									  ECPGmake_array_type(ECPGmake_simple_type(ptr->variable->type->u.element->type,
																			   "1",
																			   ptr->variable->type->u.element->counter),
														  ptr->variable->type->size),
									  0);
			}
			else if ((ptr->variable->type->type == ECPGt_varchar
					  || ptr->variable->type->type == ECPGt_char
					  || ptr->variable->type->type == ECPGt_unsigned_char
					  || ptr->variable->type->type == ECPGt_string
					  || ptr->variable->type->type == ECPGt_bytea)
					 && atoi(ptr->variable->type->size) > 1)
			{
				newvar = new_variable(cat_str(4, "(",
											  ecpg_type_name(ptr->variable->type->type),
											  " *)(ECPGget_var(",
											  var_text),
									  ECPGmake_simple_type(ptr->variable->type->type,
														   ptr->variable->type->size,
														   ptr->variable->type->counter),
									  0);
				if (ptr->variable->type->type == ECPGt_varchar ||
					ptr->variable->type->type == ECPGt_bytea)
					var_ptr = true;
			}
			else if (ptr->variable->type->type == ECPGt_struct
					 || ptr->variable->type->type == ECPGt_union)
			{
				newvar = new_variable(cat_str(5, "(*(",
											  ptr->variable->type->type_name,
											  " *)(ECPGget_var(",
											  var_text,
											  ")"),
									  ECPGmake_struct_type(ptr->variable->type->u.members,
														   ptr->variable->type->type,
														   ptr->variable->type->type_name,
														   ptr->variable->type->struct_sizeof),
									  0);
				var_ptr = true;
			}
			else if (ptr->variable->type->type == ECPGt_array)
			{
				if (ptr->variable->type->u.element->type == ECPGt_struct
					|| ptr->variable->type->u.element->type == ECPGt_union)
				{
					newvar = new_variable(cat_str(5, "(*(",
												  ptr->variable->type->u.element->type_name,
												  " *)(ECPGget_var(",
												  var_text,
												  ")"),
										  ECPGmake_struct_type(ptr->variable->type->u.element->u.members,
															   ptr->variable->type->u.element->type,
															   ptr->variable->type->u.element->type_name,
															   ptr->variable->type->u.element->struct_sizeof),
										  0);
				}
				else
				{
					newvar = new_variable(cat_str(4, "(",
												  ecpg_type_name(ptr->variable->type->u.element->type),
												  " *)(ECPGget_var(",
												  var_text),
										  ECPGmake_array_type(ECPGmake_simple_type(ptr->variable->type->u.element->type,
																				   ptr->variable->type->u.element->size,
																				   ptr->variable->type->u.element->counter),
															  ptr->variable->type->size),
										  0);
					var_ptr = true;
				}
			}
			else
			{
				newvar = new_variable(cat_str(4, "*(",
											  ecpg_type_name(ptr->variable->type->type),
											  " *)(ECPGget_var(",
											  var_text),
									  ECPGmake_simple_type(ptr->variable->type->type,
														   ptr->variable->type->size,
														   ptr->variable->type->counter),
									  0);
				var_ptr = true;
			}

			/*
			 * create call to "ECPGset_var(<counter>, <connection>, <pointer>.
			 * <line number>)"
			 */
			if (!skip_set_var)
			{
				snprintf(var_text, sizeof(var_text), "%d, %s",
						 ecpg_internal_var++, var_ptr ? "&(" : "(");
				result = cat_str(5, result, "ECPGset_var(",
								 var_text, original_var,
								 "), __LINE__);\n");
			}

			/*
			 * now the indicator if there is one and it's not a global
			 * variable
			 */
			if ((ptr->indicator->type->type == ECPGt_NO_INDICATOR) || (ptr->indicator->brace_level == 0))
			{
				newind = ptr->indicator;
			}
			else
			{
				/* change variable name to "ECPGget_var(<counter>)" */
				original_var = ptr->indicator->name;
				snprintf(var_text, sizeof(var_text), "%d))", ecpg_internal_var);
				var_ptr = false;

				if (ptr->indicator->type->type == ECPGt_struct
					|| ptr->indicator->type->type == ECPGt_union)
				{
					newind = new_variable(cat_str(5, "(*(",
												  ptr->indicator->type->type_name,
												  " *)(ECPGget_var(",
												  var_text,
												  ")"),
										  ECPGmake_struct_type(ptr->indicator->type->u.members,
															   ptr->indicator->type->type,
															   ptr->indicator->type->type_name,
															   ptr->indicator->type->struct_sizeof),
										  0);
					var_ptr = true;
				}
				else if (ptr->indicator->type->type == ECPGt_array)
				{
					if (ptr->indicator->type->u.element->type == ECPGt_struct
						|| ptr->indicator->type->u.element->type == ECPGt_union)
					{
						newind = new_variable(cat_str(5, "(*(",
													  ptr->indicator->type->u.element->type_name,
													  " *)(ECPGget_var(",
													  var_text,
													  ")"),
											  ECPGmake_struct_type(ptr->indicator->type->u.element->u.members,
																   ptr->indicator->type->u.element->type,
																   ptr->indicator->type->u.element->type_name,
																   ptr->indicator->type->u.element->struct_sizeof),
											  0);
					}
					else
					{
						newind = new_variable(cat_str(4, "(",
													  ecpg_type_name(ptr->indicator->type->u.element->type),
													  " *)(ECPGget_var(",
													  var_text),
											  ECPGmake_array_type(ECPGmake_simple_type(ptr->indicator->type->u.element->type,
																					   ptr->indicator->type->u.element->size,
																					   ptr->indicator->type->u.element->counter),
																  ptr->indicator->type->size),
											  0);
						var_ptr = true;
					}
				}
				else if (atoi(ptr->indicator->type->size) > 1)
				{
					newind = new_variable(cat_str(4, "(",
												  ecpg_type_name(ptr->indicator->type->type),
												  " *)(ECPGget_var(",
												  var_text),
										  ECPGmake_simple_type(ptr->indicator->type->type,
															   ptr->indicator->type->size,
															   ptr->variable->type->counter),
										  0);
				}
				else
				{
					newind = new_variable(cat_str(4, "*(",
												  ecpg_type_name(ptr->indicator->type->type),
												  " *)(ECPGget_var(",
												  var_text),
										  ECPGmake_simple_type(ptr->indicator->type->type,
															   ptr->indicator->type->size,
															   ptr->variable->type->counter),
										  0);
					var_ptr = true;
				}

				/*
				 * create call to "ECPGset_var(<counter>, <pointer>. <line
				 * number>)"
				 */
				snprintf(var_text, sizeof(var_text), "%d, %s",
						 ecpg_internal_var++, var_ptr ? "&(" : "(");
				result = cat_str(5, result, "ECPGset_var(",
								 var_text, original_var,
								 "), __LINE__);\n");
			}

			add_variable_to_tail(&newlist, newvar, newind);
		}

		if (insert)
			cur->argsinsert_oos = newlist;
		else
			cur->argsresult_oos = newlist;
	}

	return result;
}

/* This tests whether the cursor was declared and opened in the same function. */
#define SAMEFUNC(cur)	\
	((cur->function == NULL) ||		\
	 (cur->function != NULL && current_function != NULL && \
	  strcmp(cur->function, current_function) == 0))

static struct cursor *
add_additional_variables(const char *name, bool insert)
{
	struct cursor *ptr;
	struct arguments *p;
	int			(*strcmp_fn) (const char *, const char *) = ((name[0] == ':' || name[0] == '"') ? strcmp : pg_strcasecmp);

	for (ptr = cur; ptr != NULL; ptr = ptr->next)
	{
		if (strcmp_fn(ptr->name, name) == 0)
			break;
	}

	if (ptr == NULL)
	{
		mmerror(PARSE_ERROR, ET_ERROR, "cursor \"%s\" does not exist", name);
		return NULL;
	}

	if (insert)
	{
		/*
		 * add all those input variables that were given earlier
		 *
		 * note that we have to append here but have to keep the existing
		 * order
		 */
		for (p = (SAMEFUNC(ptr) ? ptr->argsinsert : ptr->argsinsert_oos); p; p = p->next)
			add_variable_to_tail(&argsinsert, p->variable, p->indicator);
	}

	/* add all those output variables that were given earlier */
	for (p = (SAMEFUNC(ptr) ? ptr->argsresult : ptr->argsresult_oos); p; p = p->next)
		add_variable_to_tail(&argsresult, p->variable, p->indicator);

	return ptr;
}

static void
add_typedef(const char *name, const char *dimension, const char *length,
			enum ECPGttype type_enum,
			const char *type_dimension, const char *type_index,
			int initializer, int array)
{
	/* add entry to list */
	struct typedefs *ptr,
			   *this;

	if ((type_enum == ECPGt_struct ||
		 type_enum == ECPGt_union) &&
		initializer == 1)
		mmerror(PARSE_ERROR, ET_ERROR, "initializer not allowed in type definition");
	else if (INFORMIX_MODE && strcmp(name, "string") == 0)
		mmerror(PARSE_ERROR, ET_ERROR, "type name \"string\" is reserved in Informix mode");
	else
	{
		for (ptr = types; ptr != NULL; ptr = ptr->next)
		{
			if (strcmp(name, ptr->name) == 0)
				/* re-definition is a bug */
				mmerror(PARSE_ERROR, ET_ERROR, "type \"%s\" is already defined", name);
		}
		adjust_array(type_enum, &dimension, &length,
					 type_dimension, type_index, array, true);

		this = (struct typedefs *) mm_alloc(sizeof(struct typedefs));

		/* initial definition */
		this->next = types;
		this->name = mm_strdup(name);
		this->brace_level = braces_open;
		this->type = (struct this_type *) mm_alloc(sizeof(struct this_type));
		this->type->type_storage = NULL;
		this->type->type_enum = type_enum;
		this->type->type_str = mm_strdup(name);
		this->type->type_dimension = mm_strdup(dimension); /* dimension of array */
		this->type->type_index = mm_strdup(length);	/* length of string */
		this->type->type_sizeof = ECPGstruct_sizeof ? mm_strdup(ECPGstruct_sizeof) : NULL;
		this->struct_member_list = (type_enum == ECPGt_struct || type_enum == ECPGt_union) ?
			ECPGstruct_member_dup(struct_member_list[struct_level]) : NULL;

		if (type_enum != ECPGt_varchar &&
			type_enum != ECPGt_bytea &&
			type_enum != ECPGt_char &&
			type_enum != ECPGt_unsigned_char &&
			type_enum != ECPGt_string &&
			atoi(this->type->type_index) >= 0)
			mmerror(PARSE_ERROR, ET_ERROR, "multidimensional arrays for simple data types are not supported");

		types = this;
	}
}

/*
 * check an SQL identifier is declared or not.
 * If it is already declared, the global variable
 * connection will be changed to the related connection.
 */
static bool
check_declared_list(const char *name)
{
	struct declared_list *ptr = NULL;

	for (ptr = g_declared_list; ptr != NULL; ptr = ptr->next)
	{
		if (!ptr->connection)
			continue;
		if (strcmp(name, ptr->name) == 0)
		{
			if (connection && strcmp(ptr->connection, connection) != 0)
				mmerror(PARSE_ERROR, ET_WARNING, "connection %s is overwritten with %s by DECLARE statement %s", connection, ptr->connection, name);
			update_connection(ptr->connection);
			return true;
		}
	}
	return false;
}

/*
 * If newconn isn't NULL, update the global "connection" variable to that;
 * otherwise do nothing.
 */
static void
update_connection(const char *newconn)
{
	if (newconn)
	{
		free(connection);
		connection = mm_strdup(newconn);
	}
}
%}

%expect 0
%name-prefix="base_yy"
%locations

%union {
	double		dval;
	char	   *str;
	int			ival;
	struct when action;
	struct index index;
	int			tagname;
	struct this_type type;
	enum ECPGttype type_enum;
	enum ECPGdtype dtype_enum;
	struct fetch_desc descriptor;
	struct su_symbol struct_union;
	struct prep prep;
	struct exec exec;
	struct describe describe;
}
/* tokens */
/* src/interfaces/ecpg/preproc/ecpg.tokens */

/* special embedded SQL tokens */
%token  SQL_ALLOCATE SQL_AUTOCOMMIT SQL_BOOL SQL_BREAK
                SQL_CARDINALITY SQL_CONNECT
                SQL_COUNT
                SQL_DATETIME_INTERVAL_CODE
                SQL_DATETIME_INTERVAL_PRECISION SQL_DESCRIBE
                SQL_DESCRIPTOR SQL_DISCONNECT SQL_FOUND
                SQL_FREE SQL_GET SQL_GO SQL_GOTO SQL_IDENTIFIED
                SQL_INDICATOR SQL_KEY_MEMBER SQL_LENGTH
                SQL_LONG SQL_NULLABLE SQL_OCTET_LENGTH
                SQL_OPEN SQL_OUTPUT SQL_REFERENCE
                SQL_RETURNED_LENGTH SQL_RETURNED_OCTET_LENGTH SQL_SCALE
                SQL_SECTION SQL_SHORT SQL_SIGNED SQL_SQLERROR
                SQL_SQLPRINT SQL_SQLWARNING SQL_START SQL_STOP
                SQL_STRUCT SQL_UNSIGNED SQL_VAR SQL_WHENEVER

/* C tokens */
%token  S_ADD S_AND S_ANYTHING S_AUTO S_CONST S_DEC S_DIV
                S_DOTPOINT S_EQUAL S_EXTERN S_INC S_LSHIFT S_MEMPOINT
                S_MEMBER S_MOD S_MUL S_NEQUAL S_OR S_REGISTER S_RSHIFT
                S_STATIC S_SUB S_VOLATILE
                S_TYPEDEF

%token CSTRING CVARIABLE CPP_LINE IP
/* types */
%type <prep> PrepareStmt
%type <exec> ExecuteStmt
%type <index> opt_array_bounds
/* ecpgtype */
/* src/interfaces/ecpg/preproc/ecpg.type */
%type  <struct_union> s_struct_union_symbol

%type  <descriptor> ECPGGetDescriptor
%type  <descriptor> ECPGSetDescriptor

%type  <type_enum> simple_type
%type  <type_enum> signed_type
%type  <type_enum> unsigned_type

%type  <dtype_enum> descriptor_item
%type  <dtype_enum> desc_header_item

%type  <type>   var_type

%type  <action> action

%type  <describe> ECPGDescribe
/* orig_tokens */
 %token IDENT UIDENT FCONST SCONST USCONST BCONST XCONST Op
 %token ICONST PARAM
 %token TYPECAST DOT_DOT COLON_EQUALS EQUALS_GREATER
 %token LESS_EQUALS GREATER_EQUALS NOT_EQUALS







 %token ABORT_P ABSENT ABSOLUTE_P ACCESS ACTION ADD_P ADMIN AFTER
 AGGREGATE ALL ALSO ALTER ALWAYS ANALYSE ANALYZE AND ANY ARRAY AS ASC
 ASENSITIVE ASSERTION ASSIGNMENT ASYMMETRIC ATOMIC AT ATTACH ATTRIBUTE AUTHORIZATION
 BACKWARD BEFORE BEGIN_P BETWEEN BIGINT BINARY BIT
 BOOLEAN_P BOTH BREADTH BY
 CACHE CALL CALLED CASCADE CASCADED CASE CAST CATALOG_P CHAIN CHAR_P
 CHARACTER CHARACTERISTICS CHECK CHECKPOINT CLASS CLOSE
 CLUSTER COALESCE COLLATE COLLATION COLUMN COLUMNS COMMENT COMMENTS COMMIT
 COMMITTED COMPRESSION CONCURRENTLY CONDITIONAL CONFIGURATION CONFLICT
 CONNECTION CONSTRAINT CONSTRAINTS CONTENT_P CONTINUE_P CONVERSION_P COPY
 COST CREATE CROSS CSV CUBE CURRENT_P
 CURRENT_CATALOG CURRENT_DATE CURRENT_ROLE CURRENT_SCHEMA
 CURRENT_TIME CURRENT_TIMESTAMP CURRENT_USER CURSOR CYCLE
 DATA_P DATABASE DAY_P DEALLOCATE DEC DECIMAL_P DECLARE DEFAULT DEFAULTS
 DEFERRABLE DEFERRED DEFINER DELETE_P DELIMITER DELIMITERS DEPENDS DEPTH DESC DESTINATION
 DETACH DICTIONARY DISABLE_P DISCARD DISTINCT DO DOCUMENT_P DOMAIN_P
 DOUBLE_P DROP
 EACH EDGE ELSE EMPTY_P ENABLE_P ENCODING ENCRYPTED END_P ENFORCED ENUM_P
 ERROR_P ESCAPE EVENT EXCEPT EXCLUDE EXCLUDING EXCLUSIVE EXECUTE EXISTS
 EXPLAIN EXPRESSION EXTENSION EXTERNAL EXTRACT
 FALSE_P FAMILY FETCH FILTER FINALIZE FIRST_P FLOAT_P FOLLOWING FOR
 FORCE FOREIGN FORMAT FORWARD FREEZE FROM FULL FUNCTION FUNCTIONS
 GENERATED GLOBAL GRANT GRANTED GRAPH GRAPH_TABLE GREATEST GROUP_P GROUPING GROUPS
 HANDLER HAVING HEADER_P HOLD HOUR_P
 IDENTITY_P IF_P IGNORE_P ILIKE IMMEDIATE IMMUTABLE IMPLICIT_P IMPORT_P IN_P INCLUDE
 INCLUDING INCREMENT INDENT INDEX INDEXES INHERIT INHERITS INITIALLY INLINE_P
 INNER_P INOUT INPUT_P INSENSITIVE INSERT INSTEAD INT_P INTEGER
 INTERSECT INTERVAL INTO INVOKER IS ISNULL ISOLATION
 JOIN JSON JSON_ARRAY JSON_ARRAYAGG JSON_EXISTS JSON_OBJECT JSON_OBJECTAGG
 JSON_QUERY JSON_SCALAR JSON_SERIALIZE JSON_TABLE JSON_VALUE
 KEEP KEY KEYS
 LABEL LANGUAGE LARGE_P LAST_P LATERAL_P
 LEADING LEAKPROOF LEAST LEFT LEVEL LIKE LIMIT LISTEN LOAD LOCAL
 LOCALTIME LOCALTIMESTAMP LOCATION LOCK_P LOCKED LOGGED LSN_P
 MAPPING MATCH MATCHED MATERIALIZED MAXVALUE MERGE MERGE_ACTION METHOD
 MINUTE_P MINVALUE MODE MONTH_P MOVE
 NAME_P NAMES NATIONAL NATURAL NCHAR NESTED NEW NEXT NFC NFD NFKC NFKD NO NODE
 NONE NORMALIZE NORMALIZED
 NOT NOTHING NOTIFY NOTNULL NOWAIT NULL_P NULLIF
 NULLS_P NUMERIC
 OBJECT_P OBJECTS_P OF OFF OFFSET OIDS OLD OMIT ON ONLY OPERATOR OPTION OPTIONS OR
 ORDER ORDINALITY OTHERS OUT_P OUTER_P
 OVER OVERLAPS OVERLAY OVERRIDING OWNED OWNER
 PARALLEL PARAMETER PARSER PARTIAL PARTITION PARTITIONS PASSING PASSWORD PATH
 PERIOD PLACING PLAN PLANS POLICY PORTION
 POSITION PRECEDING PRECISION PRESERVE PREPARE PREPARED PRIMARY
 PRIOR PRIVILEGES PROCEDURAL PROCEDURE PROCEDURES PROGRAM PROPERTIES PROPERTY PUBLICATION
 QUOTE QUOTES
 RANGE READ REAL REASSIGN RECURSIVE REF_P REFERENCES REFERENCING
 REFRESH REINDEX RELATIONSHIP RELATIVE_P RELEASE RENAME REPACK REPEATABLE REPLACE REPLICA
 RESET RESPECT_P RESTART RESTRICT RETURN RETURNING RETURNS REVOKE RIGHT ROLE ROLLBACK ROLLUP
 ROUTINE ROUTINES ROW ROWS RULE
 SAVEPOINT SCALAR SCHEMA SCHEMAS SCROLL SEARCH SECOND_P SECURITY SELECT
 SEQUENCE SEQUENCES
 SERIALIZABLE SERVER SESSION SESSION_USER SET SETS SETOF SHARE SHOW
 SIMILAR SIMPLE SKIP SMALLINT SNAPSHOT SOME SPLIT SOURCE SQL_P STABLE STANDALONE_P
 START STATEMENT STATISTICS STDIN STDOUT STORAGE STORED STRICT_P STRING_P STRIP_P
 SUBSCRIPTION SUBSTRING SUPPORT SYMMETRIC SYSID SYSTEM_P SYSTEM_USER
 TABLE TABLES TABLESAMPLE TABLESPACE TARGET TEMP TEMPLATE TEMPORARY TEXT_P THEN
 TIES TIME TIMESTAMP TO TRAILING TRANSACTION TRANSFORM
 TREAT TRIGGER TRIM TRUE_P
 TRUNCATE TRUSTED TYPE_P TYPES_P
 UESCAPE UNBOUNDED UNCONDITIONAL UNCOMMITTED UNENCRYPTED UNION UNIQUE UNKNOWN
 UNLISTEN UNLOGGED UNTIL UPDATE USER USING
 VACUUM VALID VALIDATE VALIDATOR VALUE_P VALUES VARCHAR VARIADIC VARYING
 VERBOSE VERSION_P VERTEX VIEW VIEWS VIRTUAL VOLATILE
 WAIT WHEN WHERE WHITESPACE_P WINDOW WITH WITHIN WITHOUT WORK WRAPPER WRITE
 XML_P XMLATTRIBUTES XMLCONCAT XMLELEMENT XMLEXISTS XMLFOREST XMLNAMESPACES
 XMLPARSE XMLPI XMLROOT XMLSERIALIZE XMLTABLE
 YEAR_P YES_P
 ZONE











 %token FORMAT_LA NOT_LA NULLS_LA WITH_LA WITHOUT_LA







 %token MODE_TYPE_NAME
 %token MODE_PLPGSQL_EXPR
 %token MODE_PLPGSQL_ASSIGN1
 %token MODE_PLPGSQL_ASSIGN2
 %token MODE_PLPGSQL_ASSIGN3

 %left UNION EXCEPT
 %left INTERSECT
 %left OR
 %left AND
 %right NOT
 %nonassoc IS ISNULL NOTNULL
 %nonassoc '<' '>' '=' LESS_EQUALS GREATER_EQUALS NOT_EQUALS
 %nonassoc BETWEEN IN_P LIKE ILIKE SIMILAR NOT_LA
 %nonassoc ESCAPE

















































 %nonassoc UNBOUNDED NESTED
 %nonassoc IDENT CSTRING PARTITION RANGE ROWS GROUPS PRECEDING FOLLOWING CUBE ROLLUP
 SET KEYS OBJECT_P SCALAR TO USING VALUE_P WITH WITHOUT PATH
 %left Op OPERATOR RIGHT_ARROW '|'
 %left '+' '-'
 %left '*' '/' '%'
 %left '^'

 %left AT
 %left COLLATE
 %right UMINUS
 %left '[' ']'
 %left '(' ')'
 %left TYPECAST
 %left '.'







 %left JOIN CROSS LEFT FULL RIGHT INNER_P NATURAL
%%
prog: statements;
/* rules */
 toplevel_stmt:
 stmt
|  TransactionStmtLegacy
	{
		fprintf(base_yyout, "{ ECPGtrans(__LINE__, %s, \"%s\");", connection ? connection : "NULL", @1);
		whenever_action(2);
	}
;


 stmt:
 AlterEventTrigStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterCollationStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterDatabaseStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterDatabaseSetStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterDefaultPrivilegesStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterDomainStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterEnumStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterExtensionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterExtensionContentsStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterFdwStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterForeignServerStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterFunctionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterGroupStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterObjectDependsStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterObjectSchemaStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterOwnerStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterOperatorStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterTypeStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterPolicyStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterPropGraphStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterSeqStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterSystemStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterTableStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterTblSpcStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterCompositeTypeStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterPublicationStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterRoleSetStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterRoleStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterSubscriptionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterStatsStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterTSConfigurationStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterTSDictionaryStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterUserMappingStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AnalyzeStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CallStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CheckPointStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  ClosePortalStmt
	{
		if (INFORMIX_MODE)
		{
			if (pg_strcasecmp(@1 + strlen("close "), "database") == 0)
			{
				if (connection)
					mmerror(PARSE_ERROR, ET_ERROR, "AT option not allowed in CLOSE DATABASE statement");

				fprintf(base_yyout, "{ ECPGdisconnect(__LINE__, \"CURRENT\");");
				whenever_action(2);
				break;
			}
		}

		output_statement(@1, 0, ECPGst_normal);
	}
|  CommentStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  ConstraintsSetStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CopyStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateAmStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateAsStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateAssertionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateCastStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateConversionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateDomainStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateExtensionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateFdwStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateForeignServerStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateForeignTableStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateFunctionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateGroupStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateMatViewStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateOpClassStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateOpFamilyStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreatePublicationStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  AlterOpFamilyStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreatePolicyStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreatePLangStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreatePropGraphStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateSchemaStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateSeqStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateSubscriptionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateStatsStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateTableSpaceStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateTransformStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateTrigStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateEventTrigStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateRoleStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateUserStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreateUserMappingStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  CreatedbStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DeallocateStmt
	{
		output_deallocate_prepare_statement(@1);
	}
|  DeclareCursorStmt
	{
		output_simple_statement(@1, (strncmp(@1, "ECPGset_var", strlen("ECPGset_var")) == 0) ? 4 : 0);
	}
|  DefineStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DeleteStmt
	{ output_statement(@1, 1, ECPGst_prepnormal); }
|  DiscardStmt
	{ output_statement(@1, 1, ECPGst_normal); }
|  DoStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropCastStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropOpClassStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropOpFamilyStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropOwnedStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropSubscriptionStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropTableSpaceStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropTransformStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropRoleStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropUserMappingStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  DropdbStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  ExecuteStmt
	{
		check_declared_list($1.name);
		if ($1.type == NULL || strlen($1.type) == 0)
			output_statement($1.name, 1, ECPGst_execute);
		else
		{
			if ($1.name[0] != '"')
				/* case of char_variable */
				add_variable_to_tail(&argsinsert, find_variable($1.name), &no_indicator);
			else
			{
				/* case of ecpg_ident or CSTRING */
				char		length[32];
				char	   *str;

				/* Remove double quotes from name */
				str = loc_strdup($1.name + 1);
				str[strlen(str) - 1] = '\0';
				snprintf(length, sizeof(length), "%zu", strlen(str));
				add_variable_to_tail(&argsinsert, new_variable(str, ECPGmake_simple_type(ECPGt_const, length, 0), 0), &no_indicator);
			}
			output_statement(cat_str(3, "execute", "$0", $1.type), 0, ECPGst_exec_with_exprlist);
		}
	}
|  ExplainStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  FetchStmt
	{ output_statement(@1, 1, ECPGst_normal); }
|  GrantStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  GrantRoleStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  ImportForeignSchemaStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  IndexStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  InsertStmt
	{ output_statement(@1, 1, ECPGst_prepnormal); }
|  ListenStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RefreshMatViewStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  LoadStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  LockStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  MergeStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  NotifyStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  PrepareStmt
	{
		check_declared_list($1.name);
		if ($1.type == NULL)
			output_prepare_statement($1.name, $1.stmt);
		else if (strlen($1.type) == 0)
		{
			char	   *stmt = cat_str(3, "\"", $1.stmt, "\"");

			output_prepare_statement($1.name, stmt);
		}
		else
		{
			if ($1.name[0] != '"')
				/* case of char_variable */
				add_variable_to_tail(&argsinsert, find_variable($1.name), &no_indicator);
			else
			{
				char		length[32];
				char	   *str;

				/* Remove double quotes from name */
				str = loc_strdup($1.name + 1);
				str[strlen(str) - 1] = '\0';
				snprintf(length, sizeof(length), "%zu", strlen(str));
				add_variable_to_tail(&argsinsert, new_variable(str, ECPGmake_simple_type(ECPGt_const, length, 0), 0), &no_indicator);
			}
			output_statement(cat_str(5, "prepare", "$0", $1.type, "as", $1.stmt), 0, ECPGst_prepare);
		}
	}
|  ReassignOwnedStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  ReindexStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RemoveAggrStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RemoveFuncStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RemoveOperStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RenameStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RepackStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RevokeStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RevokeRoleStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  RuleStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  SecLabelStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  SelectStmt
	{ output_statement(@1, 1, ECPGst_prepnormal); }
|  TransactionStmt
	{
		fprintf(base_yyout, "{ ECPGtrans(__LINE__, %s, \"%s\");", connection ? connection : "NULL", @1);
		whenever_action(2);
	}
|  TruncateStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  UnlistenStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  UpdateStmt
	{ output_statement(@1, 1, ECPGst_prepnormal); }
|  VacuumStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  VariableResetStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  VariableSetStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  VariableShowStmt
 { output_statement(@1, 0, ECPGst_normal); }
|  ViewStmt
 { output_statement(@1, 0, ECPGst_normal); }
	| ECPGAllocateDescr
	{
		fprintf(base_yyout, "ECPGallocate_desc(__LINE__, %s);", @1);
		whenever_action(0);
	}
	| ECPGConnect
	{
		if (connection)
			mmerror(PARSE_ERROR, ET_ERROR, "AT option not allowed in CONNECT statement");

		fprintf(base_yyout, "{ ECPGconnect(__LINE__, %d, %s, %d); ", compat, @1, autocommit);
		reset_variables();
		whenever_action(2);
	}
	| ECPGDeclareStmt
	{
		output_simple_statement(@1, 0);
	}
	| ECPGCursorStmt
	{
		output_simple_statement(@1, (strncmp(@1, "ECPGset_var", strlen("ECPGset_var")) == 0) ? 4 : 0);
	}
	| ECPGDeallocateDescr
	{
		fprintf(base_yyout, "ECPGdeallocate_desc(__LINE__, %s);", @1);
		whenever_action(0);
	}
	| ECPGDeclare
	{
		output_simple_statement(@1, 0);
	}
	| ECPGDescribe
	{
		check_declared_list($1.stmt_name);

		fprintf(base_yyout, "{ ECPGdescribe(__LINE__, %d, %d, %s, %s,", compat, $1.input, connection ? connection : "NULL", $1.stmt_name);
		dump_variables(argsresult, 1);
		argsresult = NULL;
		fputs("ECPGt_EORT);", base_yyout);
		fprintf(base_yyout, "}");
		output_line_number();
	}
	| ECPGDisconnect
	{
		if (connection)
			mmerror(PARSE_ERROR, ET_ERROR, "AT option not allowed in DISCONNECT statement");

		fprintf(base_yyout, "{ ECPGdisconnect(__LINE__, %s);",
				@1 ? @1 : "\"CURRENT\"");
		whenever_action(2);
	}
	| ECPGExecuteImmediateStmt
	{
		output_statement(@1, 0, ECPGst_exec_immediate);
	}
	| ECPGFree
	{
		const char *con = connection ? connection : "NULL";

		if (strcmp(@1, "all") == 0)
			fprintf(base_yyout, "{ ECPGdeallocate_all(__LINE__, %d, %s);", compat, con);
		else if (@1[0] == ':')
			fprintf(base_yyout, "{ ECPGdeallocate(__LINE__, %d, %s, %s);", compat, con, @1 + 1);
		else
			fprintf(base_yyout, "{ ECPGdeallocate(__LINE__, %d, %s, \"%s\");", compat, con, @1);

		whenever_action(2);
	}
	| ECPGGetDescriptor
	{
		lookup_descriptor($1.name, connection);
		output_get_descr($1.name, $1.str);
	}
	| ECPGGetDescriptorHeader
	{
		lookup_descriptor(@1, connection);
		output_get_descr_header(@1);
	}
	| ECPGOpen
	{
		struct cursor *ptr;

		if ((ptr = add_additional_variables(@1, true)) != NULL)
		{
			free(connection);
			connection = ptr->connection ? mm_strdup(ptr->connection) : NULL;
			output_statement(ptr->command, 0, ECPGst_normal);
			ptr->opened = true;
		}
	}
	| ECPGSetAutocommit
	{
		fprintf(base_yyout, "{ ECPGsetcommit(__LINE__, \"%s\", %s);", @1, connection ? connection : "NULL");
		whenever_action(2);
	}
	| ECPGSetConnection
	{
		if (connection)
			mmerror(PARSE_ERROR, ET_ERROR, "AT option not allowed in SET CONNECTION statement");

		fprintf(base_yyout, "{ ECPGsetconn(__LINE__, %s);", @1);
		whenever_action(2);
	}
	| ECPGSetDescriptor
	{
		lookup_descriptor($1.name, connection);
		output_set_descr($1.name, $1.str);
	}
	| ECPGSetDescriptorHeader
	{
		lookup_descriptor(@1, connection);
		output_set_descr_header(@1);
	}
	| ECPGTypedef
	{
		if (connection)
			mmerror(PARSE_ERROR, ET_ERROR, "AT option not allowed in TYPE statement");

		fprintf(base_yyout, "%s", @1);
		output_line_number();
	}
	| ECPGVar
	{
		if (connection)
			mmerror(PARSE_ERROR, ET_ERROR, "AT option not allowed in VAR statement");

		output_simple_statement(@1, 0);
	}
	| ECPGWhenever
	{
		if (connection)
			mmerror(PARSE_ERROR, ET_ERROR, "AT option not allowed in WHENEVER statement");

		output_simple_statement(@1, 0);
	}
|  WaitStmt
 { output_statement(@1, 0, ECPGst_normal); }
| 
;


 opt_single_name:
 ColId
| 
;


 opt_qualified_name:
 any_name
| 
;


 opt_concurrently:
 CONCURRENTLY
| 
;


 opt_usingindex:
 USING INDEX
| 
;


 opt_drop_behavior:
 CASCADE
|  RESTRICT
| 
;


 opt_utility_option_list:
 '(' utility_option_list ')'
| 
;


 utility_option_list:
 utility_option_elem
|  utility_option_list ',' utility_option_elem
;


 utility_option_elem:
 utility_option_name utility_option_arg
;


 utility_option_name:
 NonReservedWord
|  analyze_keyword
|  FORMAT_LA
;


 utility_option_arg:
 opt_boolean_or_string
|  NumericOnly
| 
;


 CallStmt:
 CALL func_application
;


 CreateRoleStmt:
 CREATE ROLE RoleId opt_with OptRoleList
;


 opt_with:
 WITH
|  WITH_LA
| 
;


 OptRoleList:
 OptRoleList CreateOptRoleElem
| 
;


 AlterOptRoleList:
 AlterOptRoleList AlterOptRoleElem
| 
;


 AlterOptRoleElem:
 PASSWORD ecpg_sconst
|  PASSWORD NULL_P
|  ENCRYPTED PASSWORD ecpg_sconst
|  UNENCRYPTED PASSWORD ecpg_sconst
 { 
mmerror(PARSE_ERROR, ET_WARNING, "unsupported feature will be passed to server");
}
|  INHERIT
|  CONNECTION LIMIT SignedIconst
|  VALID UNTIL ecpg_sconst
|  USER role_list
|  ecpg_ident
;


 CreateOptRoleElem:
 AlterOptRoleElem
|  SYSID Iconst
|  ADMIN role_list
|  ROLE role_list
|  IN_P ROLE role_list
|  IN_P GROUP_P role_list
;


 CreateUserStmt:
 CREATE USER RoleId opt_with OptRoleList
;


 AlterRoleStmt:
 ALTER ROLE RoleSpec opt_with AlterOptRoleList
|  ALTER USER RoleSpec opt_with AlterOptRoleList
;


 opt_in_database:

|  IN_P DATABASE name
;


 AlterRoleSetStmt:
 ALTER ROLE RoleSpec opt_in_database SetResetClause
|  ALTER ROLE ALL opt_in_database SetResetClause
|  ALTER USER RoleSpec opt_in_database SetResetClause
|  ALTER USER ALL opt_in_database SetResetClause
;


 DropRoleStmt:
 DROP ROLE role_list
|  DROP ROLE IF_P EXISTS role_list
|  DROP USER role_list
|  DROP USER IF_P EXISTS role_list
|  DROP GROUP_P role_list
|  DROP GROUP_P IF_P EXISTS role_list
;


 CreateGroupStmt:
 CREATE GROUP_P RoleId opt_with OptRoleList
;


 AlterGroupStmt:
 ALTER GROUP_P RoleSpec add_drop USER role_list
;


 add_drop:
 ADD_P
|  DROP
;


 CreateSchemaStmt:
 CREATE SCHEMA opt_single_name AUTHORIZATION RoleSpec OptSchemaEltList
|  CREATE SCHEMA ColId OptSchemaEltList
|  CREATE SCHEMA IF_P NOT EXISTS opt_single_name AUTHORIZATION RoleSpec OptSchemaEltList
|  CREATE SCHEMA IF_P NOT EXISTS ColId OptSchemaEltList
;


 OptSchemaEltList:
 OptSchemaEltList schema_stmt
| 
;


 schema_stmt:
 CreateStmt
|  IndexStmt
|  CreateDomainStmt
|  CreateFunctionStmt
|  CreateSeqStmt
|  CreateTrigStmt
|  DefineStmt
|  GrantStmt
|  ViewStmt
;


 VariableSetStmt:
 SET set_rest
|  SET LOCAL set_rest
|  SET SESSION set_rest
;


 set_rest:
 TRANSACTION transaction_mode_list
|  SESSION CHARACTERISTICS AS TRANSACTION transaction_mode_list
|  set_rest_more
;


 generic_set:
 var_name TO var_list
|  var_name '=' var_list
|  var_name TO NULL_P
|  var_name '=' NULL_P
|  var_name TO DEFAULT
|  var_name '=' DEFAULT
;


 set_rest_more:
 generic_set
|  var_name FROM CURRENT_P
|  TIME ZONE zone_value
|  CATALOG_P ecpg_sconst
 { 
mmerror(PARSE_ERROR, ET_WARNING, "unsupported feature will be passed to server");
}
|  SCHEMA ecpg_sconst
|  NAMES opt_encoding
|  ROLE NonReservedWord_or_Sconst
|  SESSION AUTHORIZATION NonReservedWord_or_Sconst
|  SESSION AUTHORIZATION DEFAULT
|  XML_P OPTION document_or_content
|  TRANSACTION SNAPSHOT ecpg_sconst
;


 var_name:
ECPGColId
|  var_name '.' ColId
;


 var_list:
 var_value
|  var_list ',' var_value
;


 var_value:
 opt_boolean_or_string
|  NumericOnly
 { 
		if (@1[0] == '$')
			@$ = "$0";
}
;


 iso_level:
 READ UNCOMMITTED
|  READ COMMITTED
|  REPEATABLE READ
|  SERIALIZABLE
;


 opt_boolean_or_string:
 TRUE_P
|  FALSE_P
|  ON
|  NonReservedWord_or_Sconst
;


 zone_value:
 ecpg_sconst
|  ecpg_ident
|  ConstInterval ecpg_sconst opt_interval
|  ConstInterval '(' Iconst ')' ecpg_sconst
|  NumericOnly
|  DEFAULT
|  LOCAL
;


 opt_encoding:
 ecpg_sconst
|  DEFAULT
| 
;


 NonReservedWord_or_Sconst:
 NonReservedWord
|  ecpg_sconst
;


 VariableResetStmt:
 RESET reset_rest
;


 reset_rest:
 generic_reset
|  TIME ZONE
|  TRANSACTION ISOLATION LEVEL
|  SESSION AUTHORIZATION
;


 generic_reset:
 var_name
|  ALL
;


 SetResetClause:
 SET set_rest
|  VariableResetStmt
;


 FunctionSetResetClause:
 SET set_rest_more
|  VariableResetStmt
;


 VariableShowStmt:
SHOW var_name ecpg_into
| SHOW TIME ZONE ecpg_into
| SHOW TRANSACTION ISOLATION LEVEL ecpg_into
| SHOW SESSION AUTHORIZATION ecpg_into
|  SHOW ALL
	{
		mmerror(PARSE_ERROR, ET_ERROR, "SHOW ALL is not implemented");
	}
;


 ConstraintsSetStmt:
 SET CONSTRAINTS constraints_set_list constraints_set_mode
;


 constraints_set_list:
 ALL
|  qualified_name_list
;


 constraints_set_mode:
 DEFERRED
|  IMMEDIATE
;


 CheckPointStmt:
 CHECKPOINT opt_utility_option_list
;


 DiscardStmt:
 DISCARD ALL
|  DISCARD TEMP
|  DISCARD TEMPORARY
|  DISCARD PLANS
|  DISCARD SEQUENCES
;


 AlterTableStmt:
 ALTER TABLE relation_expr alter_table_cmds
|  ALTER TABLE IF_P EXISTS relation_expr alter_table_cmds
|  ALTER TABLE relation_expr partition_cmd
|  ALTER TABLE IF_P EXISTS relation_expr partition_cmd
|  ALTER TABLE ALL IN_P TABLESPACE name SET TABLESPACE name opt_nowait
|  ALTER TABLE ALL IN_P TABLESPACE name OWNED BY role_list SET TABLESPACE name opt_nowait
|  ALTER INDEX qualified_name alter_table_cmds
|  ALTER INDEX IF_P EXISTS qualified_name alter_table_cmds
|  ALTER INDEX qualified_name index_partition_cmd
|  ALTER INDEX ALL IN_P TABLESPACE name SET TABLESPACE name opt_nowait
|  ALTER INDEX ALL IN_P TABLESPACE name OWNED BY role_list SET TABLESPACE name opt_nowait
|  ALTER SEQUENCE qualified_name alter_table_cmds
|  ALTER SEQUENCE IF_P EXISTS qualified_name alter_table_cmds
|  ALTER VIEW qualified_name alter_table_cmds
|  ALTER VIEW IF_P EXISTS qualified_name alter_table_cmds
|  ALTER MATERIALIZED VIEW qualified_name alter_table_cmds
|  ALTER MATERIALIZED VIEW IF_P EXISTS qualified_name alter_table_cmds
|  ALTER MATERIALIZED VIEW ALL IN_P TABLESPACE name SET TABLESPACE name opt_nowait
|  ALTER MATERIALIZED VIEW ALL IN_P TABLESPACE name OWNED BY role_list SET TABLESPACE name opt_nowait
|  ALTER FOREIGN TABLE relation_expr alter_table_cmds
|  ALTER FOREIGN TABLE IF_P EXISTS relation_expr alter_table_cmds
;


 alter_table_cmds:
 alter_table_cmd
|  alter_table_cmds ',' alter_table_cmd
;


 partitions_list:
 SinglePartitionSpec
|  partitions_list ',' SinglePartitionSpec
;


 SinglePartitionSpec:
 PARTITION qualified_name PartitionBoundSpec
;


 partition_cmd:
 ATTACH PARTITION qualified_name PartitionBoundSpec
|  DETACH PARTITION qualified_name opt_concurrently
|  DETACH PARTITION qualified_name FINALIZE
|  SPLIT PARTITION qualified_name INTO '(' partitions_list ')'
|  MERGE PARTITIONS '(' qualified_name_list ')' INTO qualified_name
;


 index_partition_cmd:
 ATTACH PARTITION qualified_name
;


 alter_table_cmd:
 ADD_P columnDef
|  ADD_P IF_P NOT EXISTS columnDef
|  ADD_P COLUMN columnDef
|  ADD_P COLUMN IF_P NOT EXISTS columnDef
|  ALTER opt_column ColId alter_column_default
|  ALTER opt_column ColId DROP NOT NULL_P
|  ALTER opt_column ColId SET NOT NULL_P
|  ALTER opt_column ColId SET EXPRESSION AS '(' a_expr ')'
|  ALTER opt_column ColId DROP EXPRESSION
|  ALTER opt_column ColId DROP EXPRESSION IF_P EXISTS
|  ALTER opt_column ColId SET STATISTICS set_statistics_value
|  ALTER opt_column Iconst SET STATISTICS set_statistics_value
|  ALTER opt_column ColId SET reloptions
|  ALTER opt_column ColId RESET reloptions
|  ALTER opt_column ColId SET column_storage
|  ALTER opt_column ColId SET column_compression
|  ALTER opt_column ColId ADD_P GENERATED generated_when AS IDENTITY_P OptParenthesizedSeqOptList
|  ALTER opt_column ColId alter_identity_column_option_list
|  ALTER opt_column ColId DROP IDENTITY_P
|  ALTER opt_column ColId DROP IDENTITY_P IF_P EXISTS
|  DROP opt_column IF_P EXISTS ColId opt_drop_behavior
|  DROP opt_column ColId opt_drop_behavior
|  ALTER opt_column ColId opt_set_data TYPE_P Typename opt_collate_clause alter_using
|  ALTER opt_column ColId alter_generic_options
|  ADD_P TableConstraint
|  ALTER CONSTRAINT name ConstraintAttributeSpec
|  ALTER CONSTRAINT name INHERIT
|  VALIDATE CONSTRAINT name
|  DROP CONSTRAINT IF_P EXISTS name opt_drop_behavior
|  DROP CONSTRAINT name opt_drop_behavior
|  SET WITHOUT OIDS
|  CLUSTER ON name
|  SET WITHOUT CLUSTER
|  SET LOGGED
|  SET UNLOGGED
|  ENABLE_P TRIGGER name
|  ENABLE_P ALWAYS TRIGGER name
|  ENABLE_P REPLICA TRIGGER name
|  ENABLE_P TRIGGER ALL
|  ENABLE_P TRIGGER USER
|  DISABLE_P TRIGGER name
|  DISABLE_P TRIGGER ALL
|  DISABLE_P TRIGGER USER
|  ENABLE_P RULE name
|  ENABLE_P ALWAYS RULE name
|  ENABLE_P REPLICA RULE name
|  DISABLE_P RULE name
|  INHERIT qualified_name
|  NO INHERIT qualified_name
|  OF any_name
|  NOT OF
|  OWNER TO RoleSpec
|  SET ACCESS METHOD set_access_method_name
|  SET TABLESPACE name
|  SET reloptions
|  RESET reloptions
|  REPLICA IDENTITY_P replica_identity
|  ENABLE_P ROW LEVEL SECURITY
|  DISABLE_P ROW LEVEL SECURITY
|  FORCE ROW LEVEL SECURITY
|  NO FORCE ROW LEVEL SECURITY
|  alter_generic_options
;


 alter_column_default:
 SET DEFAULT a_expr
|  DROP DEFAULT
;


 opt_collate_clause:
 COLLATE any_name
| 
;


 alter_using:
 USING a_expr
| 
;


 replica_identity:
 NOTHING
|  FULL
|  DEFAULT
|  USING INDEX name
;


 reloptions:
 '(' reloption_list ')'
;


 opt_reloptions:
 WITH reloptions
| 
;


 reloption_list:
 reloption_elem
|  reloption_list ',' reloption_elem
;


 reloption_elem:
 ColLabel '=' def_arg
|  ColLabel
|  ColLabel '.' ColLabel '=' def_arg
|  ColLabel '.' ColLabel
;


 alter_identity_column_option_list:
 alter_identity_column_option
|  alter_identity_column_option_list alter_identity_column_option
;


 alter_identity_column_option:
 RESTART
|  RESTART opt_with NumericOnly
|  SET SeqOptElem
|  SET GENERATED generated_when
;


 set_statistics_value:
 SignedIconst
|  DEFAULT
;


 set_access_method_name:
 ColId
|  DEFAULT
;


 PartitionBoundSpec:
 FOR VALUES WITH '(' hash_partbound ')'
|  FOR VALUES IN_P '(' expr_list ')'
|  FOR VALUES FROM '(' expr_list ')' TO '(' expr_list ')'
|  DEFAULT
;


 hash_partbound_elem:
 NonReservedWord Iconst
;


 hash_partbound:
 hash_partbound_elem
|  hash_partbound ',' hash_partbound_elem
;


 AlterCompositeTypeStmt:
 ALTER TYPE_P any_name alter_type_cmds
;


 alter_type_cmds:
 alter_type_cmd
|  alter_type_cmds ',' alter_type_cmd
;


 alter_type_cmd:
 ADD_P ATTRIBUTE TableFuncElement opt_drop_behavior
|  DROP ATTRIBUTE IF_P EXISTS ColId opt_drop_behavior
|  DROP ATTRIBUTE ColId opt_drop_behavior
|  ALTER ATTRIBUTE ColId opt_set_data TYPE_P Typename opt_collate_clause opt_drop_behavior
;


 ClosePortalStmt:
 CLOSE cursor_name
	{
		const char *cursor_marker = @2[0] == ':' ? "$0" : @2;
		struct cursor *ptr = NULL;

		for (ptr = cur; ptr != NULL; ptr = ptr->next)
		{
			if (strcmp(@2, ptr->name) == 0)
			{
				update_connection(ptr->connection);
				break;
			}
		}
		@$ = cat2_str("close", cursor_marker);
	}
|  CLOSE ALL
;


 CopyStmt:
 COPY opt_binary qualified_name opt_column_list copy_from opt_program copy_file_name copy_delimiter opt_with copy_options where_clause
 { 
		if (strcmp(@5, "from") == 0 &&
			(strcmp(@7, "stdin") == 0 || strcmp(@7, "stdout") == 0))
			mmerror(PARSE_ERROR, ET_WARNING, "COPY FROM STDIN is not implemented");
}
|  COPY '(' PreparableStmt ')' TO opt_program copy_file_name opt_with copy_options
;


 copy_from:
 FROM
|  TO
;


 opt_program:
 PROGRAM
| 
;


 copy_file_name:
 ecpg_sconst
|  STDIN
|  STDOUT
;


 copy_options:
 copy_opt_list
|  '(' copy_generic_opt_list ')'
;


 copy_opt_list:
 copy_opt_list copy_opt_item
| 
;


 copy_opt_item:
 BINARY
|  FREEZE
|  DELIMITER opt_as ecpg_sconst
|  NULL_P opt_as ecpg_sconst
|  CSV
|  JSON
|  HEADER_P
|  QUOTE opt_as ecpg_sconst
|  ESCAPE opt_as ecpg_sconst
|  FORCE QUOTE columnList
|  FORCE QUOTE '*'
|  FORCE NOT NULL_P columnList
|  FORCE NOT NULL_P '*'
|  FORCE NULL_P columnList
|  FORCE NULL_P '*'
|  ENCODING ecpg_sconst
;


 opt_binary:
 BINARY
| 
;


 copy_delimiter:
 opt_using DELIMITERS ecpg_sconst
| 
;


 opt_using:
 USING
| 
;


 copy_generic_opt_list:
 copy_generic_opt_elem
|  copy_generic_opt_list ',' copy_generic_opt_elem
;


 copy_generic_opt_elem:
 ColLabel copy_generic_opt_arg
|  FORMAT_LA copy_generic_opt_arg
;


 copy_generic_opt_arg:
 opt_boolean_or_string
|  NumericOnly
|  '*'
|  DEFAULT
|  '(' copy_generic_opt_arg_list ')'
| 
;


 copy_generic_opt_arg_list:
 copy_generic_opt_arg_list_item
|  copy_generic_opt_arg_list ',' copy_generic_opt_arg_list_item
;


 copy_generic_opt_arg_list_item:
 opt_boolean_or_string
;


 CreateStmt:
 CREATE OptTemp TABLE qualified_name '(' OptTableElementList ')' OptInherit OptPartitionSpec table_access_method_clause OptWith OnCommitOption OptTableSpace
|  CREATE OptTemp TABLE IF_P NOT EXISTS qualified_name '(' OptTableElementList ')' OptInherit OptPartitionSpec table_access_method_clause OptWith OnCommitOption OptTableSpace
|  CREATE OptTemp TABLE qualified_name OF any_name OptTypedTableElementList OptPartitionSpec table_access_method_clause OptWith OnCommitOption OptTableSpace
|  CREATE OptTemp TABLE IF_P NOT EXISTS qualified_name OF any_name OptTypedTableElementList OptPartitionSpec table_access_method_clause OptWith OnCommitOption OptTableSpace
|  CREATE OptTemp TABLE qualified_name PARTITION OF qualified_name OptTypedTableElementList PartitionBoundSpec OptPartitionSpec table_access_method_clause OptWith OnCommitOption OptTableSpace
|  CREATE OptTemp TABLE IF_P NOT EXISTS qualified_name PARTITION OF qualified_name OptTypedTableElementList PartitionBoundSpec OptPartitionSpec table_access_method_clause OptWith OnCommitOption OptTableSpace
;


 OptTemp:
 TEMPORARY
|  TEMP
|  LOCAL TEMPORARY
|  LOCAL TEMP
|  GLOBAL TEMPORARY
|  GLOBAL TEMP
|  UNLOGGED
| 
;


 OptTableElementList:
 TableElementList
| 
;


 OptTypedTableElementList:
 '(' TypedTableElementList ')'
| 
;


 TableElementList:
 TableElement
|  TableElementList ',' TableElement
;


 TypedTableElementList:
 TypedTableElement
|  TypedTableElementList ',' TypedTableElement
;


 TableElement:
 columnDef
|  TableLikeClause
|  TableConstraint
;


 TypedTableElement:
 columnOptions
|  TableConstraint
;


 columnDef:
 ColId Typename opt_column_storage opt_column_compression create_generic_options ColQualList
;


 columnOptions:
 ColId ColQualList
|  ColId WITH OPTIONS ColQualList
;


 column_compression:
 COMPRESSION ColId
|  COMPRESSION DEFAULT
;


 opt_column_compression:
 column_compression
| 
;


 column_storage:
 STORAGE ColId
|  STORAGE DEFAULT
;


 opt_column_storage:
 column_storage
| 
;


 ColQualList:
 ColQualList ColConstraint
| 
;


 ColConstraint:
 CONSTRAINT name ColConstraintElem
|  ColConstraintElem
|  ConstraintAttr
|  COLLATE any_name
;


 ColConstraintElem:
 NOT NULL_P opt_no_inherit
|  NULL_P
|  UNIQUE opt_unique_null_treatment opt_definition OptConsTableSpace
|  PRIMARY KEY opt_definition OptConsTableSpace
|  CHECK '(' a_expr ')' opt_no_inherit
|  DEFAULT b_expr
|  GENERATED generated_when AS IDENTITY_P OptParenthesizedSeqOptList
|  GENERATED generated_when AS '(' a_expr ')' opt_virtual_or_stored
|  REFERENCES qualified_name opt_column_list key_match key_actions
;


 opt_unique_null_treatment:
 NULLS_P DISTINCT
|  NULLS_P NOT DISTINCT
| 
;


 generated_when:
 ALWAYS
|  BY DEFAULT
;


 opt_virtual_or_stored:
 STORED
|  VIRTUAL
| 
;


 ConstraintAttr:
 DEFERRABLE
|  NOT DEFERRABLE
|  INITIALLY DEFERRED
|  INITIALLY IMMEDIATE
|  ENFORCED
|  NOT ENFORCED
;


 TableLikeClause:
 LIKE qualified_name TableLikeOptionList
;


 TableLikeOptionList:
 TableLikeOptionList INCLUDING TableLikeOption
|  TableLikeOptionList EXCLUDING TableLikeOption
| 
;


 TableLikeOption:
 COMMENTS
|  COMPRESSION
|  CONSTRAINTS
|  DEFAULTS
|  IDENTITY_P
|  GENERATED
|  INDEXES
|  STATISTICS
|  STORAGE
|  ALL
;


 TableConstraint:
 CONSTRAINT name ConstraintElem
|  ConstraintElem
;


 ConstraintElem:
 CHECK '(' a_expr ')' ConstraintAttributeSpec
|  NOT NULL_P ColId ConstraintAttributeSpec
|  UNIQUE opt_unique_null_treatment '(' columnList opt_without_overlaps ')' opt_c_include opt_definition OptConsTableSpace ConstraintAttributeSpec
|  UNIQUE ExistingIndex ConstraintAttributeSpec
|  PRIMARY KEY '(' columnList opt_without_overlaps ')' opt_c_include opt_definition OptConsTableSpace ConstraintAttributeSpec
|  PRIMARY KEY ExistingIndex ConstraintAttributeSpec
|  EXCLUDE access_method_clause '(' ExclusionConstraintList ')' opt_c_include opt_definition OptConsTableSpace OptWhereClause ConstraintAttributeSpec
|  FOREIGN KEY '(' columnList optionalPeriodName ')' REFERENCES qualified_name opt_column_and_period_list key_match key_actions ConstraintAttributeSpec
;


 DomainConstraint:
 CONSTRAINT name DomainConstraintElem
|  DomainConstraintElem
;


 DomainConstraintElem:
 CHECK '(' a_expr ')' ConstraintAttributeSpec
|  NOT NULL_P ConstraintAttributeSpec
;


 opt_no_inherit:
 NO INHERIT
| 
;


 opt_without_overlaps:
 WITHOUT OVERLAPS
| 
;


 opt_column_list:
 '(' columnList ')'
| 
;


 columnList:
 columnElem
|  columnList ',' columnElem
;


 optionalPeriodName:
 ',' PERIOD columnElem
| 
;


 opt_column_and_period_list:
 '(' columnList optionalPeriodName ')'
| 
;


 columnElem:
 ColId
;


 opt_c_include:
 INCLUDE '(' columnList ')'
| 
;


 key_match:
 MATCH FULL
|  MATCH PARTIAL
 { 
mmerror(PARSE_ERROR, ET_WARNING, "unsupported feature will be passed to server");
}
|  MATCH SIMPLE
| 
;


 ExclusionConstraintList:
 ExclusionConstraintElem
|  ExclusionConstraintList ',' ExclusionConstraintElem
;


 ExclusionConstraintElem:
 index_elem WITH any_operator
|  index_elem WITH OPERATOR '(' any_operator ')'
;


 OptWhereClause:
 WHERE '(' a_expr ')'
| 
;


 key_actions:
 key_update
|  key_delete
|  key_update key_delete
|  key_delete key_update
| 
;


 key_update:
 ON UPDATE key_action
;


 key_delete:
 ON DELETE_P key_action
;


 key_action:
 NO ACTION
|  RESTRICT
|  CASCADE
|  SET NULL_P opt_column_list
|  SET DEFAULT opt_column_list
;


 OptInherit:
 INHERITS '(' qualified_name_list ')'
| 
;


 OptPartitionSpec:
 PartitionSpec
| 
;


 PartitionSpec:
 PARTITION BY ColId '(' part_params ')'
;


 part_params:
 part_elem
|  part_params ',' part_elem
;


 part_elem:
 ColId opt_collate opt_qualified_name
|  func_expr_windowless opt_collate opt_qualified_name
|  '(' a_expr ')' opt_collate opt_qualified_name
;


 table_access_method_clause:
 USING name
| 
;


 OptWith:
 WITH reloptions
|  WITHOUT OIDS
| 
;


 OnCommitOption:
 ON COMMIT DROP
|  ON COMMIT DELETE_P ROWS
|  ON COMMIT PRESERVE ROWS
| 
;


 OptTableSpace:
 TABLESPACE name
| 
;


 OptConsTableSpace:
 USING INDEX TABLESPACE name
| 
;


 ExistingIndex:
 USING INDEX name
;


 CreateStatsStmt:
 CREATE STATISTICS opt_qualified_name opt_name_list ON stats_params FROM from_list
|  CREATE STATISTICS IF_P NOT EXISTS any_name opt_name_list ON stats_params FROM from_list
;


 stats_params:
 stats_param
|  stats_params ',' stats_param
;


 stats_param:
 ColId
|  func_expr_windowless
|  '(' a_expr ')'
;


 AlterStatsStmt:
 ALTER STATISTICS any_name SET STATISTICS set_statistics_value
|  ALTER STATISTICS IF_P EXISTS any_name SET STATISTICS set_statistics_value
;


 create_as_target:
 qualified_name opt_column_list table_access_method_clause OptWith OnCommitOption OptTableSpace
;


 opt_with_data:
 WITH DATA_P
|  WITH NO DATA_P
| 
;


 CreateMatViewStmt:
 CREATE OptNoLog MATERIALIZED VIEW create_mv_target AS SelectStmt opt_with_data
|  CREATE OptNoLog MATERIALIZED VIEW IF_P NOT EXISTS create_mv_target AS SelectStmt opt_with_data
;


 create_mv_target:
 qualified_name opt_column_list table_access_method_clause opt_reloptions OptTableSpace
;


 OptNoLog:
 UNLOGGED
| 
;


 RefreshMatViewStmt:
 REFRESH MATERIALIZED VIEW opt_concurrently qualified_name opt_with_data
;


 CreateSeqStmt:
 CREATE OptTemp SEQUENCE qualified_name OptSeqOptList
|  CREATE OptTemp SEQUENCE IF_P NOT EXISTS qualified_name OptSeqOptList
;


 AlterSeqStmt:
 ALTER SEQUENCE qualified_name SeqOptList
|  ALTER SEQUENCE IF_P EXISTS qualified_name SeqOptList
;


 OptSeqOptList:
 SeqOptList
| 
;


 OptParenthesizedSeqOptList:
 '(' SeqOptList ')'
| 
;


 SeqOptList:
 SeqOptElem
|  SeqOptList SeqOptElem
;


 SeqOptElem:
 AS SimpleTypename
|  CACHE NumericOnly
|  CYCLE
|  NO CYCLE
|  INCREMENT opt_by NumericOnly
|  LOGGED
|  MAXVALUE NumericOnly
|  MINVALUE NumericOnly
|  NO MAXVALUE
|  NO MINVALUE
|  OWNED BY any_name
|  SEQUENCE NAME_P any_name
|  START opt_with NumericOnly
|  RESTART
|  RESTART opt_with NumericOnly
|  UNLOGGED
;


 opt_by:
 BY
| 
;


 NumericOnly:
 ecpg_fconst
|  '+' ecpg_fconst
|  '-' ecpg_fconst
|  SignedIconst
;


 NumericOnly_list:
 NumericOnly
|  NumericOnly_list ',' NumericOnly
;


 CreatePLangStmt:
 CREATE opt_or_replace opt_trusted opt_procedural LANGUAGE name
|  CREATE opt_or_replace opt_trusted opt_procedural LANGUAGE name HANDLER handler_name opt_inline_handler opt_validator
;


 opt_trusted:
 TRUSTED
| 
;


 handler_name:
 name
|  name attrs
;


 opt_inline_handler:
 INLINE_P handler_name
| 
;


 validator_clause:
 VALIDATOR handler_name
|  NO VALIDATOR
;


 opt_validator:
 validator_clause
| 
;


 opt_procedural:
 PROCEDURAL
| 
;


 CreateTableSpaceStmt:
 CREATE TABLESPACE name OptTableSpaceOwner LOCATION ecpg_sconst opt_reloptions
;


 OptTableSpaceOwner:
 OWNER RoleSpec
| 
;


 DropTableSpaceStmt:
 DROP TABLESPACE name
|  DROP TABLESPACE IF_P EXISTS name
;


 CreateExtensionStmt:
 CREATE EXTENSION name opt_with create_extension_opt_list
|  CREATE EXTENSION IF_P NOT EXISTS name opt_with create_extension_opt_list
;


 create_extension_opt_list:
 create_extension_opt_list create_extension_opt_item
| 
;


 create_extension_opt_item:
 SCHEMA name
|  VERSION_P NonReservedWord_or_Sconst
|  FROM NonReservedWord_or_Sconst
 { 
mmerror(PARSE_ERROR, ET_WARNING, "unsupported feature will be passed to server");
}
|  CASCADE
;


 AlterExtensionStmt:
 ALTER EXTENSION name UPDATE alter_extension_opt_list
;


 alter_extension_opt_list:
 alter_extension_opt_list alter_extension_opt_item
| 
;


 alter_extension_opt_item:
 TO NonReservedWord_or_Sconst
;


 AlterExtensionContentsStmt:
 ALTER EXTENSION name add_drop object_type_name name
|  ALTER EXTENSION name add_drop object_type_any_name any_name
|  ALTER EXTENSION name add_drop AGGREGATE aggregate_with_argtypes
|  ALTER EXTENSION name add_drop CAST '(' Typename AS Typename ')'
|  ALTER EXTENSION name add_drop DOMAIN_P Typename
|  ALTER EXTENSION name add_drop FUNCTION function_with_argtypes
|  ALTER EXTENSION name add_drop OPERATOR operator_with_argtypes
|  ALTER EXTENSION name add_drop OPERATOR CLASS any_name USING name
|  ALTER EXTENSION name add_drop OPERATOR FAMILY any_name USING name
|  ALTER EXTENSION name add_drop PROCEDURE function_with_argtypes
|  ALTER EXTENSION name add_drop ROUTINE function_with_argtypes
|  ALTER EXTENSION name add_drop TRANSFORM FOR Typename LANGUAGE name
|  ALTER EXTENSION name add_drop TYPE_P Typename
;


 CreateFdwStmt:
 CREATE FOREIGN DATA_P WRAPPER name opt_fdw_options create_generic_options
;


 fdw_option:
 HANDLER handler_name
|  NO HANDLER
|  VALIDATOR handler_name
|  NO VALIDATOR
|  CONNECTION handler_name
|  NO CONNECTION
;


 fdw_options:
 fdw_option
|  fdw_options fdw_option
;


 opt_fdw_options:
 fdw_options
| 
;


 AlterFdwStmt:
 ALTER FOREIGN DATA_P WRAPPER name opt_fdw_options alter_generic_options
|  ALTER FOREIGN DATA_P WRAPPER name fdw_options
;


 create_generic_options:
 OPTIONS '(' generic_option_list ')'
| 
;


 generic_option_list:
 generic_option_elem
|  generic_option_list ',' generic_option_elem
;


 alter_generic_options:
 OPTIONS '(' alter_generic_option_list ')'
;


 alter_generic_option_list:
 alter_generic_option_elem
|  alter_generic_option_list ',' alter_generic_option_elem
;


 alter_generic_option_elem:
 generic_option_elem
|  SET generic_option_elem
|  ADD_P generic_option_elem
|  DROP generic_option_name
;


 generic_option_elem:
 generic_option_name generic_option_arg
;


 generic_option_name:
 ColLabel
;


 generic_option_arg:
 ecpg_sconst
;


 CreateForeignServerStmt:
 CREATE SERVER name opt_type opt_foreign_server_version FOREIGN DATA_P WRAPPER name create_generic_options
|  CREATE SERVER IF_P NOT EXISTS name opt_type opt_foreign_server_version FOREIGN DATA_P WRAPPER name create_generic_options
;


 opt_type:
 TYPE_P ecpg_sconst
| 
;


 foreign_server_version:
 VERSION_P ecpg_sconst
|  VERSION_P NULL_P
;


 opt_foreign_server_version:
 foreign_server_version
| 
;


 AlterForeignServerStmt:
 ALTER SERVER name foreign_server_version alter_generic_options
|  ALTER SERVER name foreign_server_version
|  ALTER SERVER name alter_generic_options
;


 CreateForeignTableStmt:
 CREATE FOREIGN TABLE qualified_name '(' OptTableElementList ')' OptInherit SERVER name create_generic_options
|  CREATE FOREIGN TABLE IF_P NOT EXISTS qualified_name '(' OptTableElementList ')' OptInherit SERVER name create_generic_options
|  CREATE FOREIGN TABLE qualified_name PARTITION OF qualified_name OptTypedTableElementList PartitionBoundSpec SERVER name create_generic_options
|  CREATE FOREIGN TABLE IF_P NOT EXISTS qualified_name PARTITION OF qualified_name OptTypedTableElementList PartitionBoundSpec SERVER name create_generic_options
;


 ImportForeignSchemaStmt:
 IMPORT_P FOREIGN SCHEMA name import_qualification FROM SERVER name INTO name create_generic_options
;


 import_qualification_type:
 LIMIT TO
|  EXCEPT
;


 import_qualification:
 import_qualification_type '(' relation_expr_list ')'
| 
;


 CreateUserMappingStmt:
 CREATE USER MAPPING FOR auth_ident SERVER name create_generic_options
|  CREATE USER MAPPING IF_P NOT EXISTS FOR auth_ident SERVER name create_generic_options
;


 auth_ident:
 RoleSpec
|  USER
;


 DropUserMappingStmt:
 DROP USER MAPPING FOR auth_ident SERVER name
|  DROP USER MAPPING IF_P EXISTS FOR auth_ident SERVER name
;


 AlterUserMappingStmt:
 ALTER USER MAPPING FOR auth_ident SERVER name alter_generic_options
;


 CreatePolicyStmt:
 CREATE POLICY name ON qualified_name RowSecurityDefaultPermissive RowSecurityDefaultForCmd RowSecurityDefaultToRole RowSecurityOptionalExpr RowSecurityOptionalWithCheck
;


 AlterPolicyStmt:
 ALTER POLICY name ON qualified_name RowSecurityOptionalToRole RowSecurityOptionalExpr RowSecurityOptionalWithCheck
;


 RowSecurityOptionalExpr:
 USING '(' a_expr ')'
| 
;


 RowSecurityOptionalWithCheck:
 WITH CHECK '(' a_expr ')'
| 
;


 RowSecurityDefaultToRole:
 TO role_list
| 
;


 RowSecurityOptionalToRole:
 TO role_list
| 
;


 RowSecurityDefaultPermissive:
 AS ecpg_ident
| 
;


 RowSecurityDefaultForCmd:
 FOR row_security_cmd
| 
;


 row_security_cmd:
 ALL
|  SELECT
|  INSERT
|  UPDATE
|  DELETE_P
;


 CreateAmStmt:
 CREATE ACCESS METHOD name TYPE_P am_type HANDLER handler_name
;


 am_type:
 INDEX
|  TABLE
;


 CreateTrigStmt:
 CREATE opt_or_replace TRIGGER name TriggerActionTime TriggerEvents ON qualified_name TriggerReferencing TriggerForSpec TriggerWhen EXECUTE FUNCTION_or_PROCEDURE func_name '(' TriggerFuncArgs ')'
|  CREATE opt_or_replace CONSTRAINT TRIGGER name AFTER TriggerEvents ON qualified_name OptConstrFromTable ConstraintAttributeSpec FOR EACH ROW TriggerWhen EXECUTE FUNCTION_or_PROCEDURE func_name '(' TriggerFuncArgs ')'
;


 TriggerActionTime:
 BEFORE
|  AFTER
|  INSTEAD OF
;


 TriggerEvents:
 TriggerOneEvent
|  TriggerEvents OR TriggerOneEvent
;


 TriggerOneEvent:
 INSERT
|  DELETE_P
|  UPDATE
|  UPDATE OF columnList
|  TRUNCATE
;


 TriggerReferencing:
 REFERENCING TriggerTransitions
| 
;


 TriggerTransitions:
 TriggerTransition
|  TriggerTransitions TriggerTransition
;


 TriggerTransition:
 TransitionOldOrNew TransitionRowOrTable opt_as TransitionRelName
;


 TransitionOldOrNew:
 NEW
|  OLD
;


 TransitionRowOrTable:
 TABLE
|  ROW
;


 TransitionRelName:
 ColId
;


 TriggerForSpec:
 FOR TriggerForOptEach TriggerForType
| 
;


 TriggerForOptEach:
 EACH
| 
;


 TriggerForType:
 ROW
|  STATEMENT
;


 TriggerWhen:
 WHEN '(' a_expr ')'
| 
;


 FUNCTION_or_PROCEDURE:
 FUNCTION
|  PROCEDURE
;


 TriggerFuncArgs:
 TriggerFuncArg
|  TriggerFuncArgs ',' TriggerFuncArg
| 
;


 TriggerFuncArg:
 Iconst
|  ecpg_fconst
|  ecpg_sconst
|  ColLabel
;


 OptConstrFromTable:
 FROM qualified_name
| 
;


 ConstraintAttributeSpec:

|  ConstraintAttributeSpec ConstraintAttributeElem
;


 ConstraintAttributeElem:
 NOT DEFERRABLE
|  DEFERRABLE
|  INITIALLY IMMEDIATE
|  INITIALLY DEFERRED
|  NOT VALID
|  NO INHERIT
|  NOT ENFORCED
|  ENFORCED
;


 CreateEventTrigStmt:
 CREATE EVENT TRIGGER name ON ColLabel EXECUTE FUNCTION_or_PROCEDURE func_name '(' ')'
|  CREATE EVENT TRIGGER name ON ColLabel WHEN event_trigger_when_list EXECUTE FUNCTION_or_PROCEDURE func_name '(' ')'
;


 event_trigger_when_list:
 event_trigger_when_item
|  event_trigger_when_list AND event_trigger_when_item
;


 event_trigger_when_item:
 ColId IN_P '(' event_trigger_value_list ')'
;


 event_trigger_value_list:
 SCONST
|  event_trigger_value_list ',' SCONST
;


 AlterEventTrigStmt:
 ALTER EVENT TRIGGER name enable_trigger
;


 enable_trigger:
 ENABLE_P
|  ENABLE_P REPLICA
|  ENABLE_P ALWAYS
|  DISABLE_P
;


 CreateAssertionStmt:
 CREATE ASSERTION any_name CHECK '(' a_expr ')' ConstraintAttributeSpec
 { 
mmerror(PARSE_ERROR, ET_WARNING, "unsupported feature will be passed to server");
}
;


 DefineStmt:
 CREATE opt_or_replace AGGREGATE func_name aggr_args definition
|  CREATE opt_or_replace AGGREGATE func_name old_aggr_definition
|  CREATE OPERATOR any_operator definition
|  CREATE TYPE_P any_name definition
|  CREATE TYPE_P any_name
|  CREATE TYPE_P any_name AS '(' OptTableFuncElementList ')'
|  CREATE TYPE_P any_name AS ENUM_P '(' opt_enum_val_list ')'
|  CREATE TYPE_P any_name AS RANGE definition
|  CREATE TEXT_P SEARCH PARSER any_name definition
|  CREATE TEXT_P SEARCH DICTIONARY any_name definition
|  CREATE TEXT_P SEARCH TEMPLATE any_name definition
|  CREATE TEXT_P SEARCH CONFIGURATION any_name definition
|  CREATE COLLATION any_name definition
|  CREATE COLLATION IF_P NOT EXISTS any_name definition
|  CREATE COLLATION any_name FROM any_name
|  CREATE COLLATION IF_P NOT EXISTS any_name FROM any_name
;


 definition:
 '(' def_list ')'
;


 def_list:
 def_elem
|  def_list ',' def_elem
;


 def_elem:
 ColLabel '=' def_arg
|  ColLabel
;


 def_arg:
 func_type
|  reserved_keyword
|  qual_all_Op
|  NumericOnly
|  ecpg_sconst
|  NONE
;


 old_aggr_definition:
 '(' old_aggr_list ')'
;


 old_aggr_list:
 old_aggr_elem
|  old_aggr_list ',' old_aggr_elem
;


 old_aggr_elem:
 ecpg_ident '=' def_arg
;


 opt_enum_val_list:
 enum_val_list
| 
;


 enum_val_list:
 ecpg_sconst
|  enum_val_list ',' ecpg_sconst
;


 AlterEnumStmt:
 ALTER TYPE_P any_name ADD_P VALUE_P opt_if_not_exists ecpg_sconst
|  ALTER TYPE_P any_name ADD_P VALUE_P opt_if_not_exists ecpg_sconst BEFORE ecpg_sconst
|  ALTER TYPE_P any_name ADD_P VALUE_P opt_if_not_exists ecpg_sconst AFTER ecpg_sconst
|  ALTER TYPE_P any_name RENAME VALUE_P ecpg_sconst TO ecpg_sconst
|  ALTER TYPE_P any_name DROP VALUE_P ecpg_sconst
 { 
mmerror(PARSE_ERROR, ET_WARNING, "unsupported feature will be passed to server");
}
;


 opt_if_not_exists:
 IF_P NOT EXISTS
| 
;


 CreateOpClassStmt:
 CREATE OPERATOR CLASS any_name opt_default FOR TYPE_P Typename USING name opt_opfamily AS opclass_item_list
;


 opclass_item_list:
 opclass_item
|  opclass_item_list ',' opclass_item
;


 opclass_item:
 OPERATOR Iconst any_operator opclass_purpose
|  OPERATOR Iconst operator_with_argtypes opclass_purpose
|  FUNCTION Iconst function_with_argtypes
|  FUNCTION Iconst '(' type_list ')' function_with_argtypes
|  STORAGE Typename
;


 opt_default:
 DEFAULT
| 
;


 opt_opfamily:
 FAMILY any_name
| 
;


 opclass_purpose:
 FOR SEARCH
|  FOR ORDER BY any_name
| 
;


 CreateOpFamilyStmt:
 CREATE OPERATOR FAMILY any_name USING name
;


 AlterOpFamilyStmt:
 ALTER OPERATOR FAMILY any_name USING name ADD_P opclass_item_list
|  ALTER OPERATOR FAMILY any_name USING name DROP opclass_drop_list
;


 opclass_drop_list:
 opclass_drop
|  opclass_drop_list ',' opclass_drop
;


 opclass_drop:
 OPERATOR Iconst '(' type_list ')'
|  FUNCTION Iconst '(' type_list ')'
;


 DropOpClassStmt:
 DROP OPERATOR CLASS any_name USING name opt_drop_behavior
|  DROP OPERATOR CLASS IF_P EXISTS any_name USING name opt_drop_behavior
;


 DropOpFamilyStmt:
 DROP OPERATOR FAMILY any_name USING name opt_drop_behavior
|  DROP OPERATOR FAMILY IF_P EXISTS any_name USING name opt_drop_behavior
;


 DropOwnedStmt:
 DROP OWNED BY role_list opt_drop_behavior
;


 ReassignOwnedStmt:
 REASSIGN OWNED BY role_list TO RoleSpec
;


 DropStmt:
 DROP object_type_any_name IF_P EXISTS any_name_list opt_drop_behavior
|  DROP object_type_any_name any_name_list opt_drop_behavior
|  DROP drop_type_name IF_P EXISTS name_list opt_drop_behavior
|  DROP drop_type_name name_list opt_drop_behavior
|  DROP object_type_name_on_any_name name ON any_name opt_drop_behavior
|  DROP object_type_name_on_any_name IF_P EXISTS name ON any_name opt_drop_behavior
|  DROP TYPE_P type_name_list opt_drop_behavior
|  DROP TYPE_P IF_P EXISTS type_name_list opt_drop_behavior
|  DROP DOMAIN_P type_name_list opt_drop_behavior
|  DROP DOMAIN_P IF_P EXISTS type_name_list opt_drop_behavior
|  DROP INDEX CONCURRENTLY any_name_list opt_drop_behavior
|  DROP INDEX CONCURRENTLY IF_P EXISTS any_name_list opt_drop_behavior
;


 object_type_any_name:
 TABLE
|  SEQUENCE
|  VIEW
|  MATERIALIZED VIEW
|  INDEX
|  FOREIGN TABLE
|  PROPERTY GRAPH
|  COLLATION
|  CONVERSION_P
|  STATISTICS
|  TEXT_P SEARCH PARSER
|  TEXT_P SEARCH DICTIONARY
|  TEXT_P SEARCH TEMPLATE
|  TEXT_P SEARCH CONFIGURATION
;


 object_type_name:
 drop_type_name
|  DATABASE
|  ROLE
|  SUBSCRIPTION
|  TABLESPACE
;


 drop_type_name:
 ACCESS METHOD
|  EVENT TRIGGER
|  EXTENSION
|  FOREIGN DATA_P WRAPPER
|  opt_procedural LANGUAGE
|  PUBLICATION
|  SCHEMA
|  SERVER
;


 object_type_name_on_any_name:
 POLICY
|  RULE
|  TRIGGER
;


 any_name_list:
 any_name
|  any_name_list ',' any_name
;


 any_name:
 ColId
|  ColId attrs
;


 attrs:
 '.' attr_name
|  attrs '.' attr_name
;


 type_name_list:
 Typename
|  type_name_list ',' Typename
;


 TruncateStmt:
 TRUNCATE opt_table relation_expr_list opt_restart_seqs opt_drop_behavior
;


 opt_restart_seqs:
 CONTINUE_P IDENTITY_P
|  RESTART IDENTITY_P
| 
;


 CommentStmt:
 COMMENT ON object_type_any_name any_name IS comment_text
|  COMMENT ON COLUMN any_name IS comment_text
|  COMMENT ON object_type_name name IS comment_text
|  COMMENT ON TYPE_P Typename IS comment_text
|  COMMENT ON DOMAIN_P Typename IS comment_text
|  COMMENT ON AGGREGATE aggregate_with_argtypes IS comment_text
|  COMMENT ON FUNCTION function_with_argtypes IS comment_text
|  COMMENT ON OPERATOR operator_with_argtypes IS comment_text
|  COMMENT ON CONSTRAINT name ON any_name IS comment_text
|  COMMENT ON CONSTRAINT name ON DOMAIN_P any_name IS comment_text
|  COMMENT ON object_type_name_on_any_name name ON any_name IS comment_text
|  COMMENT ON PROCEDURE function_with_argtypes IS comment_text
|  COMMENT ON ROUTINE function_with_argtypes IS comment_text
|  COMMENT ON TRANSFORM FOR Typename LANGUAGE name IS comment_text
|  COMMENT ON OPERATOR CLASS any_name USING name IS comment_text
|  COMMENT ON OPERATOR FAMILY any_name USING name IS comment_text
|  COMMENT ON LARGE_P OBJECT_P NumericOnly IS comment_text
|  COMMENT ON CAST '(' Typename AS Typename ')' IS comment_text
;


 comment_text:
 ecpg_sconst
|  NULL_P
;


 SecLabelStmt:
 SECURITY LABEL opt_provider ON object_type_any_name any_name IS security_label
|  SECURITY LABEL opt_provider ON COLUMN any_name IS security_label
|  SECURITY LABEL opt_provider ON object_type_name name IS security_label
|  SECURITY LABEL opt_provider ON TYPE_P Typename IS security_label
|  SECURITY LABEL opt_provider ON DOMAIN_P Typename IS security_label
|  SECURITY LABEL opt_provider ON AGGREGATE aggregate_with_argtypes IS security_label
|  SECURITY LABEL opt_provider ON FUNCTION function_with_argtypes IS security_label
|  SECURITY LABEL opt_provider ON LARGE_P OBJECT_P NumericOnly IS security_label
|  SECURITY LABEL opt_provider ON PROCEDURE function_with_argtypes IS security_label
|  SECURITY LABEL opt_provider ON ROUTINE function_with_argtypes IS security_label
;


 opt_provider:
 FOR NonReservedWord_or_Sconst
| 
;


 security_label:
 ecpg_sconst
|  NULL_P
;


 FetchStmt:
 FETCH fetch_args
|  MOVE fetch_args
	| FETCH fetch_args ecpg_fetch_into
	| FETCH FORWARD cursor_name opt_ecpg_fetch_into
	{
		const char *cursor_marker = @3[0] == ':' ? "$0" : @3;
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);

		@$ = cat_str(2, "fetch forward", cursor_marker);
	}
	| FETCH FORWARD from_in cursor_name opt_ecpg_fetch_into
	{
		const char *cursor_marker = @4[0] == ':' ? "$0" : @4;
		struct cursor *ptr = add_additional_variables(@4, false);

		update_connection(ptr->connection);

		@$ = cat_str(2, "fetch forward from", cursor_marker);
	}
	| FETCH BACKWARD cursor_name opt_ecpg_fetch_into
	{
		const char *cursor_marker = @3[0] == ':' ? "$0" : @3;
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);

		@$ = cat_str(2, "fetch backward", cursor_marker);
	}
	| FETCH BACKWARD from_in cursor_name opt_ecpg_fetch_into
	{
		const char *cursor_marker = @4[0] == ':' ? "$0" : @4;
		struct cursor *ptr = add_additional_variables(@4, false);

		update_connection(ptr->connection);

		@$ = cat_str(2, "fetch backward from", cursor_marker);
	}
	| MOVE FORWARD cursor_name
	{
		const char *cursor_marker = @3[0] == ':' ? "$0" : @3;
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);

		@$ = cat_str(2, "move forward", cursor_marker);
	}
	| MOVE FORWARD from_in cursor_name
	{
		const char *cursor_marker = @4[0] == ':' ? "$0" : @4;
		struct cursor *ptr = add_additional_variables(@4, false);

		update_connection(ptr->connection);

		@$ = cat_str(2, "move forward from", cursor_marker);
	}
	| MOVE BACKWARD cursor_name
	{
		const char *cursor_marker = @3[0] == ':' ? "$0" : @3;
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);

		@$ = cat_str(2, "move backward", cursor_marker);
	}
	| MOVE BACKWARD from_in cursor_name
	{
		const char *cursor_marker = @4[0] == ':' ? "$0" : @4;
		struct cursor *ptr = add_additional_variables(@4, false);

		update_connection(ptr->connection);

		@$ = cat_str(2, "move backward from", cursor_marker);
	}
;


 fetch_args:
 cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@1, false);

		update_connection(ptr->connection);
		if (@1[0] == ':')
			@$ = "$0";
}
|  from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@2, false);

		update_connection(ptr->connection);
		if (@2[0] == ':')
			@$ = cat2_str(@1, "$0");
}
|  SignedIconst opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@3, false);
		bool	replace = false;

		update_connection(ptr->connection);
		if (@3[0] == ':')
		{
			@3 = "$0";
			replace = true;
		}
		if (@1[0] == '$')
		{
			@1 = "$0";
			replace = true;
		}
		if (replace)
			@$ = cat_str(3, @1, @2, @3);
}
|  NEXT opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);
		if (@3[0] == ':')
			@$ = cat_str(3, @1, @2, "$0");
}
|  PRIOR opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);
		if (@3[0] == ':')
			@$ = cat_str(3, @1, @2, "$0");
}
|  FIRST_P opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);
		if (@3[0] == ':')
			@$ = cat_str(3, @1, @2, "$0");
}
|  LAST_P opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);
		if (@3[0] == ':')
			@$ = cat_str(3, @1, @2, "$0");
}
|  ABSOLUTE_P SignedIconst opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@4, false);
		bool	replace = false;

		update_connection(ptr->connection);
		if (@4[0] == ':')
		{
			@4 = "$0";
			replace = true;
		}
		if (@2[0] == '$')
		{
			@2 = "$0";
			replace = true;
		}
		if (replace)
			@$ = cat_str(4, @1, @2, @3, @4);
}
|  RELATIVE_P SignedIconst opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@4, false);
		bool	replace = false;

		update_connection(ptr->connection);
		if (@4[0] == ':')
		{
			@4 = "$0";
			replace = true;
		}
		if (@2[0] == '$')
		{
			@2 = "$0";
			replace = true;
		}
		if (replace)
			@$ = cat_str(4, @1, @2, @3, @4);
}
|  ALL opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@3, false);

		update_connection(ptr->connection);
		if (@3[0] == ':')
			@$ = cat_str(3, @1, @2, "$0");
}
|  FORWARD SignedIconst opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@4, false);
		bool	replace = false;

		update_connection(ptr->connection);
		if (@4[0] == ':')
		{
			@4 = "$0";
			replace = true;
		}
		if (@2[0] == '$')
		{
			@2 = "$0";
			replace = true;
		}
		if (replace)
			@$ = cat_str(4, @1, @2, @3, @4);
}
|  FORWARD ALL opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@4, false);

		update_connection(ptr->connection);
		if (@4[0] == ':')
			@$ = cat_str(4, @1, @2, @3, "$0");
}
|  BACKWARD SignedIconst opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@4, false);
		bool	replace = false;

		update_connection(ptr->connection);
		if (@4[0] == ':')
		{
			@4 = "$0";
			replace = true;
		}
		if (@2[0] == '$')
		{
			@2 = "$0";
			replace = true;
		}
		if (replace)
			@$ = cat_str(4, @1, @2, @3, @4);
}
|  BACKWARD ALL opt_from_in cursor_name
 { 
		struct cursor *ptr = add_additional_variables(@4, false);

		update_connection(ptr->connection);
		if (@4[0] == ':')
			@$ = cat_str(4, @1, @2, @3, "$0");
}
;


 from_in:
 FROM
|  IN_P
;


 opt_from_in:
 from_in
| 
;


 GrantStmt:
 GRANT privileges ON privilege_target TO grantee_list opt_grant_grant_option opt_granted_by
;


 RevokeStmt:
 REVOKE privileges ON privilege_target FROM grantee_list opt_granted_by opt_drop_behavior
|  REVOKE GRANT OPTION FOR privileges ON privilege_target FROM grantee_list opt_granted_by opt_drop_behavior
;


 privileges:
 privilege_list
|  ALL
|  ALL PRIVILEGES
|  ALL '(' columnList ')'
|  ALL PRIVILEGES '(' columnList ')'
;


 privilege_list:
 privilege
|  privilege_list ',' privilege
;


 privilege:
 SELECT opt_column_list
|  REFERENCES opt_column_list
|  CREATE opt_column_list
|  ALTER SYSTEM_P
|  ColId opt_column_list
;


 parameter_name_list:
 parameter_name
|  parameter_name_list ',' parameter_name
;


 parameter_name:
 ColId
|  parameter_name '.' ColId
;


 privilege_target:
 qualified_name_list
|  TABLE qualified_name_list
|  SEQUENCE qualified_name_list
|  FOREIGN DATA_P WRAPPER name_list
|  FOREIGN SERVER name_list
|  FUNCTION function_with_argtypes_list
|  PROCEDURE function_with_argtypes_list
|  ROUTINE function_with_argtypes_list
|  DATABASE name_list
|  DOMAIN_P any_name_list
|  LANGUAGE name_list
|  LARGE_P OBJECT_P NumericOnly_list
|  PARAMETER parameter_name_list
|  PROPERTY GRAPH qualified_name_list
|  SCHEMA name_list
|  TABLESPACE name_list
|  TYPE_P any_name_list
|  ALL TABLES IN_P SCHEMA name_list
|  ALL SEQUENCES IN_P SCHEMA name_list
|  ALL FUNCTIONS IN_P SCHEMA name_list
|  ALL PROCEDURES IN_P SCHEMA name_list
|  ALL ROUTINES IN_P SCHEMA name_list
;


 grantee_list:
 grantee
|  grantee_list ',' grantee
;


 grantee:
 RoleSpec
|  GROUP_P RoleSpec
;


 opt_grant_grant_option:
 WITH GRANT OPTION
| 
;


 GrantRoleStmt:
 GRANT privilege_list TO role_list opt_granted_by
|  GRANT privilege_list TO role_list WITH grant_role_opt_list opt_granted_by
;


 RevokeRoleStmt:
 REVOKE privilege_list FROM role_list opt_granted_by opt_drop_behavior
|  REVOKE ColId OPTION FOR privilege_list FROM role_list opt_granted_by opt_drop_behavior
;


 grant_role_opt_list:
 grant_role_opt_list ',' grant_role_opt
|  grant_role_opt
;


 grant_role_opt:
 ColLabel grant_role_opt_value
;


 grant_role_opt_value:
 OPTION
|  TRUE_P
|  FALSE_P
;


 opt_granted_by:
 GRANTED BY RoleSpec
| 
;


 AlterDefaultPrivilegesStmt:
 ALTER DEFAULT PRIVILEGES DefACLOptionList DefACLAction
;


 DefACLOptionList:
 DefACLOptionList DefACLOption
| 
;


 DefACLOption:
 IN_P SCHEMA name_list
|  FOR ROLE role_list
|  FOR USER role_list
;


 DefACLAction:
 GRANT privileges ON defacl_privilege_target TO grantee_list opt_grant_grant_option
|  REVOKE privileges ON defacl_privilege_target FROM grantee_list opt_drop_behavior
|  REVOKE GRANT OPTION FOR privileges ON defacl_privilege_target FROM grantee_list opt_drop_behavior
;


 defacl_privilege_target:
 TABLES
|  FUNCTIONS
|  ROUTINES
|  SEQUENCES
|  TYPES_P
|  SCHEMAS
|  LARGE_P OBJECTS_P
;


 IndexStmt:
 CREATE opt_unique INDEX opt_concurrently opt_single_name ON relation_expr access_method_clause '(' index_params ')' opt_include opt_unique_null_treatment opt_reloptions OptTableSpace where_clause
|  CREATE opt_unique INDEX opt_concurrently IF_P NOT EXISTS name ON relation_expr access_method_clause '(' index_params ')' opt_include opt_unique_null_treatment opt_reloptions OptTableSpace where_clause
;


 opt_unique:
 UNIQUE
| 
;


 access_method_clause:
 USING name
| 
;


 index_params:
 index_elem
|  index_params ',' index_elem
;


 index_elem_options:
 opt_collate opt_qualified_name opt_asc_desc opt_nulls_order
|  opt_collate any_name reloptions opt_asc_desc opt_nulls_order
;


 index_elem:
 ColId index_elem_options
|  func_expr_windowless index_elem_options
|  '(' a_expr ')' index_elem_options
;


 opt_include:
 INCLUDE '(' index_including_params ')'
| 
;


 index_including_params:
 index_elem
|  index_including_params ',' index_elem
;


 opt_collate:
 COLLATE any_name
| 
;


 opt_asc_desc:
 ASC
|  DESC
| 
;


 opt_nulls_order:
 NULLS_LA FIRST_P
|  NULLS_LA LAST_P
| 
;


 CreateFunctionStmt:
 CREATE opt_or_replace FUNCTION func_name func_args_with_defaults RETURNS func_return opt_createfunc_opt_list opt_routine_body
|  CREATE opt_or_replace FUNCTION func_name func_args_with_defaults RETURNS TABLE '(' table_func_column_list ')' opt_createfunc_opt_list opt_routine_body
|  CREATE opt_or_replace FUNCTION func_name func_args_with_defaults opt_createfunc_opt_list opt_routine_body
|  CREATE opt_or_replace PROCEDURE func_name func_args_with_defaults opt_createfunc_opt_list opt_routine_body
;


 opt_or_replace:
 OR REPLACE
| 
;


 func_args:
 '(' func_args_list ')'
|  '(' ')'
;


 func_args_list:
 func_arg
|  func_args_list ',' func_arg
;


 function_with_argtypes_list:
 function_with_argtypes
|  function_with_argtypes_list ',' function_with_argtypes
;


 function_with_argtypes:
 func_name func_args
|  type_func_name_keyword
|  ColId
|  ColId indirection
;


 func_args_with_defaults:
 '(' func_args_with_defaults_list ')'
|  '(' ')'
;


 func_args_with_defaults_list:
 func_arg_with_default
|  func_args_with_defaults_list ',' func_arg_with_default
;


 func_arg:
 arg_class param_name func_type
|  param_name arg_class func_type
|  param_name func_type
|  arg_class func_type
|  func_type
;


 arg_class:
 IN_P
|  OUT_P
|  INOUT
|  IN_P OUT_P
|  VARIADIC
;


 param_name:
 type_function_name
;


 func_return:
 func_type
;


 func_type:
 Typename
|  type_function_name attrs '%' TYPE_P
|  SETOF type_function_name attrs '%' TYPE_P
;


 func_arg_with_default:
 func_arg
|  func_arg DEFAULT a_expr
|  func_arg '=' a_expr
;


 aggr_arg:
 func_arg
;


 aggr_args:
 '(' '*' ')'
|  '(' aggr_args_list ')'
|  '(' ORDER BY aggr_args_list ')'
|  '(' aggr_args_list ORDER BY aggr_args_list ')'
;


 aggr_args_list:
 aggr_arg
|  aggr_args_list ',' aggr_arg
;


 aggregate_with_argtypes:
 func_name aggr_args
;


 aggregate_with_argtypes_list:
 aggregate_with_argtypes
|  aggregate_with_argtypes_list ',' aggregate_with_argtypes
;


 opt_createfunc_opt_list:
 createfunc_opt_list
| 
;


 createfunc_opt_list:
 createfunc_opt_item
|  createfunc_opt_list createfunc_opt_item
;


 common_func_opt_item:
 CALLED ON NULL_P INPUT_P
|  RETURNS NULL_P ON NULL_P INPUT_P
|  STRICT_P
|  IMMUTABLE
|  STABLE
|  VOLATILE
|  EXTERNAL SECURITY DEFINER
|  EXTERNAL SECURITY INVOKER
|  SECURITY DEFINER
|  SECURITY INVOKER
|  LEAKPROOF
|  NOT LEAKPROOF
|  COST NumericOnly
|  ROWS NumericOnly
|  SUPPORT any_name
|  FunctionSetResetClause
|  PARALLEL ColId
;


 createfunc_opt_item:
 AS func_as
|  LANGUAGE NonReservedWord_or_Sconst
|  TRANSFORM transform_type_list
|  WINDOW
|  common_func_opt_item
;


 func_as:
 ecpg_sconst
|  ecpg_sconst ',' ecpg_sconst
;


 ReturnStmt:
 RETURN a_expr
;


 opt_routine_body:
 ReturnStmt
|  BEGIN_P ATOMIC routine_body_stmt_list END_P
| 
;


 routine_body_stmt_list:
 routine_body_stmt_list routine_body_stmt ';'
| 
;


 routine_body_stmt:
 stmt
|  ReturnStmt
;


 transform_type_list:
 FOR TYPE_P Typename
|  transform_type_list ',' FOR TYPE_P Typename
;


 opt_definition:
 WITH definition
| 
;


 table_func_column:
 param_name func_type
;


 table_func_column_list:
 table_func_column
|  table_func_column_list ',' table_func_column
;


 AlterFunctionStmt:
 ALTER FUNCTION function_with_argtypes alterfunc_opt_list opt_restrict
|  ALTER PROCEDURE function_with_argtypes alterfunc_opt_list opt_restrict
|  ALTER ROUTINE function_with_argtypes alterfunc_opt_list opt_restrict
;


 alterfunc_opt_list:
 common_func_opt_item
|  alterfunc_opt_list common_func_opt_item
;


 opt_restrict:
 RESTRICT
| 
;


 RemoveFuncStmt:
 DROP FUNCTION function_with_argtypes_list opt_drop_behavior
|  DROP FUNCTION IF_P EXISTS function_with_argtypes_list opt_drop_behavior
|  DROP PROCEDURE function_with_argtypes_list opt_drop_behavior
|  DROP PROCEDURE IF_P EXISTS function_with_argtypes_list opt_drop_behavior
|  DROP ROUTINE function_with_argtypes_list opt_drop_behavior
|  DROP ROUTINE IF_P EXISTS function_with_argtypes_list opt_drop_behavior
;


 RemoveAggrStmt:
 DROP AGGREGATE aggregate_with_argtypes_list opt_drop_behavior
|  DROP AGGREGATE IF_P EXISTS aggregate_with_argtypes_list opt_drop_behavior
;


 RemoveOperStmt:
 DROP OPERATOR operator_with_argtypes_list opt_drop_behavior
|  DROP OPERATOR IF_P EXISTS operator_with_argtypes_list opt_drop_behavior
;


 oper_argtypes:
 '(' Typename ')'
|  '(' Typename ',' Typename ')'
|  '(' NONE ',' Typename ')'
|  '(' Typename ',' NONE ')'
;


 any_operator:
 all_Op
|  ColId '.' any_operator
;


 operator_with_argtypes_list:
 operator_with_argtypes
|  operator_with_argtypes_list ',' operator_with_argtypes
;


 operator_with_argtypes:
 any_operator oper_argtypes
;


 DoStmt:
 DO dostmt_opt_list
;


 dostmt_opt_list:
 dostmt_opt_item
|  dostmt_opt_list dostmt_opt_item
;


 dostmt_opt_item:
 ecpg_sconst
|  LANGUAGE NonReservedWord_or_Sconst
;


 CreateCastStmt:
 CREATE CAST '(' Typename AS Typename ')' WITH FUNCTION function_with_argtypes cast_context
|  CREATE CAST '(' Typename AS Typename ')' WITHOUT FUNCTION cast_context
|  CREATE CAST '(' Typename AS Typename ')' WITH INOUT cast_context
;


 cast_context:
 AS IMPLICIT_P
|  AS ASSIGNMENT
| 
;


 DropCastStmt:
 DROP CAST opt_if_exists '(' Typename AS Typename ')' opt_drop_behavior
;


 opt_if_exists:
 IF_P EXISTS
| 
;


 CreatePropGraphStmt:
 CREATE OptTemp PROPERTY GRAPH qualified_name opt_vertex_tables_clause opt_edge_tables_clause
;


 opt_vertex_tables_clause:
 vertex_tables_clause
| 
;


 vertex_tables_clause:
 vertex_synonym TABLES '(' vertex_table_list ')'
;


 vertex_synonym:
 NODE
|  VERTEX
;


 vertex_table_list:
 vertex_table_definition
|  vertex_table_list ',' vertex_table_definition
;


 vertex_table_definition:
 qualified_name opt_propgraph_table_alias opt_graph_table_key_clause opt_element_table_label_and_properties
;


 opt_propgraph_table_alias:
 AS name
| 
;


 opt_graph_table_key_clause:
 KEY '(' columnList ')'
| 
;


 opt_edge_tables_clause:
 edge_tables_clause
| 
;


 edge_tables_clause:
 edge_synonym TABLES '(' edge_table_list ')'
;


 edge_synonym:
 EDGE
|  RELATIONSHIP
;


 edge_table_list:
 edge_table_definition
|  edge_table_list ',' edge_table_definition
;


 edge_table_definition:
 qualified_name opt_propgraph_table_alias opt_graph_table_key_clause source_vertex_table destination_vertex_table opt_element_table_label_and_properties
;


 source_vertex_table:
 SOURCE name
|  SOURCE KEY '(' columnList ')' REFERENCES name '(' columnList ')'
;


 destination_vertex_table:
 DESTINATION name
|  DESTINATION KEY '(' columnList ')' REFERENCES name '(' columnList ')'
;


 opt_element_table_label_and_properties:
 element_table_properties
|  label_and_properties_list
| 
;


 element_table_properties:
 NO PROPERTIES
|  PROPERTIES ALL COLUMNS
|  PROPERTIES '(' labeled_expr_list ')'
;


 label_and_properties_list:
 label_and_properties
|  label_and_properties_list label_and_properties
;


 label_and_properties:
 element_table_label_clause
|  element_table_label_clause element_table_properties
;


 element_table_label_clause:
 LABEL name
|  DEFAULT LABEL
;


 AlterPropGraphStmt:
 ALTER PROPERTY GRAPH qualified_name ADD_P vertex_tables_clause
|  ALTER PROPERTY GRAPH qualified_name ADD_P vertex_tables_clause ADD_P edge_tables_clause
|  ALTER PROPERTY GRAPH qualified_name ADD_P edge_tables_clause
|  ALTER PROPERTY GRAPH qualified_name DROP vertex_synonym TABLES '(' name_list ')' opt_drop_behavior
|  ALTER PROPERTY GRAPH qualified_name DROP edge_synonym TABLES '(' name_list ')' opt_drop_behavior
|  ALTER PROPERTY GRAPH qualified_name ALTER vertex_or_edge TABLE name add_label_list
|  ALTER PROPERTY GRAPH qualified_name ALTER vertex_or_edge TABLE name DROP LABEL name opt_drop_behavior
|  ALTER PROPERTY GRAPH qualified_name ALTER vertex_or_edge TABLE name ALTER LABEL name ADD_P PROPERTIES '(' labeled_expr_list ')'
|  ALTER PROPERTY GRAPH qualified_name ALTER vertex_or_edge TABLE name ALTER LABEL name DROP PROPERTIES '(' name_list ')' opt_drop_behavior
;


 vertex_or_edge:
 vertex_synonym
|  edge_synonym
;


 add_label_list:
 add_label
|  add_label_list add_label
;


 add_label:
 ADD_P LABEL name element_table_properties
;


 CreateTransformStmt:
 CREATE opt_or_replace TRANSFORM FOR Typename LANGUAGE name '(' transform_element_list ')'
;


 transform_element_list:
 FROM SQL_P WITH FUNCTION function_with_argtypes ',' TO SQL_P WITH FUNCTION function_with_argtypes
|  TO SQL_P WITH FUNCTION function_with_argtypes ',' FROM SQL_P WITH FUNCTION function_with_argtypes
|  FROM SQL_P WITH FUNCTION function_with_argtypes
|  TO SQL_P WITH FUNCTION function_with_argtypes
;


 DropTransformStmt:
 DROP TRANSFORM opt_if_exists FOR Typename LANGUAGE name opt_drop_behavior
;


 ReindexStmt:
 REINDEX opt_utility_option_list reindex_target_relation opt_concurrently qualified_name
|  REINDEX opt_utility_option_list SCHEMA opt_concurrently name
|  REINDEX opt_utility_option_list reindex_target_all opt_concurrently opt_single_name
;


 reindex_target_relation:
 INDEX
|  TABLE
;


 reindex_target_all:
 SYSTEM_P
|  DATABASE
;


 AlterTblSpcStmt:
 ALTER TABLESPACE name SET reloptions
|  ALTER TABLESPACE name RESET reloptions
;


 RenameStmt:
 ALTER AGGREGATE aggregate_with_argtypes RENAME TO name
|  ALTER COLLATION any_name RENAME TO name
|  ALTER CONVERSION_P any_name RENAME TO name
|  ALTER DATABASE name RENAME TO name
|  ALTER DOMAIN_P any_name RENAME TO name
|  ALTER DOMAIN_P any_name RENAME CONSTRAINT name TO name
|  ALTER FOREIGN DATA_P WRAPPER name RENAME TO name
|  ALTER FUNCTION function_with_argtypes RENAME TO name
|  ALTER GROUP_P RoleId RENAME TO RoleId
|  ALTER opt_procedural LANGUAGE name RENAME TO name
|  ALTER OPERATOR CLASS any_name USING name RENAME TO name
|  ALTER OPERATOR FAMILY any_name USING name RENAME TO name
|  ALTER POLICY name ON qualified_name RENAME TO name
|  ALTER POLICY IF_P EXISTS name ON qualified_name RENAME TO name
|  ALTER PROCEDURE function_with_argtypes RENAME TO name
|  ALTER PROPERTY GRAPH qualified_name RENAME TO name
|  ALTER PUBLICATION name RENAME TO name
|  ALTER ROUTINE function_with_argtypes RENAME TO name
|  ALTER SCHEMA name RENAME TO name
|  ALTER SERVER name RENAME TO name
|  ALTER SUBSCRIPTION name RENAME TO name
|  ALTER TABLE relation_expr RENAME TO name
|  ALTER TABLE IF_P EXISTS relation_expr RENAME TO name
|  ALTER SEQUENCE qualified_name RENAME TO name
|  ALTER SEQUENCE IF_P EXISTS qualified_name RENAME TO name
|  ALTER VIEW qualified_name RENAME TO name
|  ALTER VIEW IF_P EXISTS qualified_name RENAME TO name
|  ALTER MATERIALIZED VIEW qualified_name RENAME TO name
|  ALTER MATERIALIZED VIEW IF_P EXISTS qualified_name RENAME TO name
|  ALTER INDEX qualified_name RENAME TO name
|  ALTER INDEX IF_P EXISTS qualified_name RENAME TO name
|  ALTER FOREIGN TABLE relation_expr RENAME TO name
|  ALTER FOREIGN TABLE IF_P EXISTS relation_expr RENAME TO name
|  ALTER TABLE relation_expr RENAME opt_column name TO name
|  ALTER TABLE IF_P EXISTS relation_expr RENAME opt_column name TO name
|  ALTER VIEW qualified_name RENAME opt_column name TO name
|  ALTER VIEW IF_P EXISTS qualified_name RENAME opt_column name TO name
|  ALTER MATERIALIZED VIEW qualified_name RENAME opt_column name TO name
|  ALTER MATERIALIZED VIEW IF_P EXISTS qualified_name RENAME opt_column name TO name
|  ALTER TABLE relation_expr RENAME CONSTRAINT name TO name
|  ALTER TABLE IF_P EXISTS relation_expr RENAME CONSTRAINT name TO name
|  ALTER FOREIGN TABLE relation_expr RENAME opt_column name TO name
|  ALTER FOREIGN TABLE IF_P EXISTS relation_expr RENAME opt_column name TO name
|  ALTER RULE name ON qualified_name RENAME TO name
|  ALTER TRIGGER name ON qualified_name RENAME TO name
|  ALTER EVENT TRIGGER name RENAME TO name
|  ALTER ROLE RoleId RENAME TO RoleId
|  ALTER USER RoleId RENAME TO RoleId
|  ALTER TABLESPACE name RENAME TO name
|  ALTER STATISTICS any_name RENAME TO name
|  ALTER TEXT_P SEARCH PARSER any_name RENAME TO name
|  ALTER TEXT_P SEARCH DICTIONARY any_name RENAME TO name
|  ALTER TEXT_P SEARCH TEMPLATE any_name RENAME TO name
|  ALTER TEXT_P SEARCH CONFIGURATION any_name RENAME TO name
|  ALTER TYPE_P any_name RENAME TO name
|  ALTER TYPE_P any_name RENAME ATTRIBUTE name TO name opt_drop_behavior
;


 opt_column:
 COLUMN
| 
;


 opt_set_data:
 SET DATA_P
| 
;


 AlterObjectDependsStmt:
 ALTER FUNCTION function_with_argtypes opt_no DEPENDS ON EXTENSION name
|  ALTER PROCEDURE function_with_argtypes opt_no DEPENDS ON EXTENSION name
|  ALTER ROUTINE function_with_argtypes opt_no DEPENDS ON EXTENSION name
|  ALTER TRIGGER name ON qualified_name opt_no DEPENDS ON EXTENSION name
|  ALTER MATERIALIZED VIEW qualified_name opt_no DEPENDS ON EXTENSION name
|  ALTER INDEX qualified_name opt_no DEPENDS ON EXTENSION name
;


 opt_no:
 NO
| 
;


 AlterObjectSchemaStmt:
 ALTER AGGREGATE aggregate_with_argtypes SET SCHEMA name
|  ALTER COLLATION any_name SET SCHEMA name
|  ALTER CONVERSION_P any_name SET SCHEMA name
|  ALTER DOMAIN_P any_name SET SCHEMA name
|  ALTER EXTENSION name SET SCHEMA name
|  ALTER FUNCTION function_with_argtypes SET SCHEMA name
|  ALTER OPERATOR operator_with_argtypes SET SCHEMA name
|  ALTER OPERATOR CLASS any_name USING name SET SCHEMA name
|  ALTER OPERATOR FAMILY any_name USING name SET SCHEMA name
|  ALTER PROCEDURE function_with_argtypes SET SCHEMA name
|  ALTER PROPERTY GRAPH qualified_name SET SCHEMA name
|  ALTER PROPERTY GRAPH IF_P EXISTS qualified_name SET SCHEMA name
|  ALTER ROUTINE function_with_argtypes SET SCHEMA name
|  ALTER TABLE relation_expr SET SCHEMA name
|  ALTER TABLE IF_P EXISTS relation_expr SET SCHEMA name
|  ALTER STATISTICS any_name SET SCHEMA name
|  ALTER TEXT_P SEARCH PARSER any_name SET SCHEMA name
|  ALTER TEXT_P SEARCH DICTIONARY any_name SET SCHEMA name
|  ALTER TEXT_P SEARCH TEMPLATE any_name SET SCHEMA name
|  ALTER TEXT_P SEARCH CONFIGURATION any_name SET SCHEMA name
|  ALTER SEQUENCE qualified_name SET SCHEMA name
|  ALTER SEQUENCE IF_P EXISTS qualified_name SET SCHEMA name
|  ALTER VIEW qualified_name SET SCHEMA name
|  ALTER VIEW IF_P EXISTS qualified_name SET SCHEMA name
|  ALTER MATERIALIZED VIEW qualified_name SET SCHEMA name
|  ALTER MATERIALIZED VIEW IF_P EXISTS qualified_name SET SCHEMA name
|  ALTER FOREIGN TABLE relation_expr SET SCHEMA name
|  ALTER FOREIGN TABLE IF_P EXISTS relation_expr SET SCHEMA name
|  ALTER TYPE_P any_name SET SCHEMA name
;


 AlterOperatorStmt:
 ALTER OPERATOR operator_with_argtypes SET '(' operator_def_list ')'
;


 operator_def_list:
 operator_def_elem
|  operator_def_list ',' operator_def_elem
;


 operator_def_elem:
 ColLabel '=' NONE
|  ColLabel '=' operator_def_arg
|  ColLabel
;


 operator_def_arg:
 func_type
|  reserved_keyword
|  qual_all_Op
|  NumericOnly
|  ecpg_sconst
;


 AlterTypeStmt:
 ALTER TYPE_P any_name SET '(' operator_def_list ')'
;


 AlterOwnerStmt:
 ALTER AGGREGATE aggregate_with_argtypes OWNER TO RoleSpec
|  ALTER COLLATION any_name OWNER TO RoleSpec
|  ALTER CONVERSION_P any_name OWNER TO RoleSpec
|  ALTER DATABASE name OWNER TO RoleSpec
|  ALTER DOMAIN_P any_name OWNER TO RoleSpec
|  ALTER FUNCTION function_with_argtypes OWNER TO RoleSpec
|  ALTER opt_procedural LANGUAGE name OWNER TO RoleSpec
|  ALTER LARGE_P OBJECT_P NumericOnly OWNER TO RoleSpec
|  ALTER OPERATOR operator_with_argtypes OWNER TO RoleSpec
|  ALTER OPERATOR CLASS any_name USING name OWNER TO RoleSpec
|  ALTER OPERATOR FAMILY any_name USING name OWNER TO RoleSpec
|  ALTER PROCEDURE function_with_argtypes OWNER TO RoleSpec
|  ALTER PROPERTY GRAPH qualified_name OWNER TO RoleSpec
|  ALTER ROUTINE function_with_argtypes OWNER TO RoleSpec
|  ALTER SCHEMA name OWNER TO RoleSpec
|  ALTER TYPE_P any_name OWNER TO RoleSpec
|  ALTER TABLESPACE name OWNER TO RoleSpec
|  ALTER STATISTICS any_name OWNER TO RoleSpec
|  ALTER TEXT_P SEARCH DICTIONARY any_name OWNER TO RoleSpec
|  ALTER TEXT_P SEARCH CONFIGURATION any_name OWNER TO RoleSpec
|  ALTER FOREIGN DATA_P WRAPPER name OWNER TO RoleSpec
|  ALTER SERVER name OWNER TO RoleSpec
|  ALTER EVENT TRIGGER name OWNER TO RoleSpec
|  ALTER PUBLICATION name OWNER TO RoleSpec
|  ALTER SUBSCRIPTION name OWNER TO RoleSpec
;


 CreatePublicationStmt:
 CREATE PUBLICATION name opt_definition
|  CREATE PUBLICATION name FOR pub_all_obj_type_list opt_definition
|  CREATE PUBLICATION name FOR pub_obj_list opt_definition
;


 PublicationObjSpec:
 TABLE relation_expr opt_column_list OptWhereClause
|  TABLES IN_P SCHEMA ColId
|  TABLES IN_P SCHEMA CURRENT_SCHEMA
|  ColId opt_column_list OptWhereClause
|  ColId indirection opt_column_list OptWhereClause
|  extended_relation_expr opt_column_list OptWhereClause
|  CURRENT_SCHEMA
;


 pub_obj_list:
 PublicationObjSpec
|  pub_obj_list ',' PublicationObjSpec
;


 opt_pub_except_clause:
 EXCEPT '(' TABLE pub_except_obj_list ')'
| 
;


 PublicationAllObjSpec:
 ALL TABLES opt_pub_except_clause
|  ALL SEQUENCES
;


 pub_all_obj_type_list:
 PublicationAllObjSpec
|  pub_all_obj_type_list ',' PublicationAllObjSpec
;


 PublicationExceptObjSpec:
 relation_expr
;


 pub_except_obj_list:
 PublicationExceptObjSpec
|  pub_except_obj_list ',' opt_table PublicationExceptObjSpec
;


 AlterPublicationStmt:
 ALTER PUBLICATION name SET definition
|  ALTER PUBLICATION name ADD_P pub_obj_list
|  ALTER PUBLICATION name SET pub_obj_list
|  ALTER PUBLICATION name SET pub_all_obj_type_list
|  ALTER PUBLICATION name DROP pub_obj_list
;


 CreateSubscriptionStmt:
 CREATE SUBSCRIPTION name CONNECTION ecpg_sconst PUBLICATION name_list opt_definition
|  CREATE SUBSCRIPTION name SERVER name PUBLICATION name_list opt_definition
;


 AlterSubscriptionStmt:
 ALTER SUBSCRIPTION name SET definition
|  ALTER SUBSCRIPTION name CONNECTION ecpg_sconst
|  ALTER SUBSCRIPTION name SERVER name
|  ALTER SUBSCRIPTION name REFRESH PUBLICATION opt_definition
|  ALTER SUBSCRIPTION name REFRESH SEQUENCES
|  ALTER SUBSCRIPTION name ADD_P PUBLICATION name_list opt_definition
|  ALTER SUBSCRIPTION name DROP PUBLICATION name_list opt_definition
|  ALTER SUBSCRIPTION name SET PUBLICATION name_list opt_definition
|  ALTER SUBSCRIPTION name ENABLE_P
|  ALTER SUBSCRIPTION name DISABLE_P
|  ALTER SUBSCRIPTION name SKIP definition
;


 DropSubscriptionStmt:
 DROP SUBSCRIPTION name opt_drop_behavior
|  DROP SUBSCRIPTION IF_P EXISTS name opt_drop_behavior
;


 RuleStmt:
 CREATE opt_or_replace RULE name AS ON event TO qualified_name where_clause DO opt_instead RuleActionList
;


 RuleActionList:
 NOTHING
|  RuleActionStmt
|  '(' RuleActionMulti ')'
;


 RuleActionMulti:
 RuleActionMulti ';' RuleActionStmtOrEmpty
|  RuleActionStmtOrEmpty
;


 RuleActionStmt:
 SelectStmt
|  InsertStmt
|  UpdateStmt
|  DeleteStmt
|  NotifyStmt
;


 RuleActionStmtOrEmpty:
 RuleActionStmt
| 
;


 event:
 SELECT
|  UPDATE
|  DELETE_P
|  INSERT
;


 opt_instead:
 INSTEAD
|  ALSO
| 
;


 NotifyStmt:
 NOTIFY ColId notify_payload
;


 notify_payload:
 ',' ecpg_sconst
| 
;


 ListenStmt:
 LISTEN ColId
;


 UnlistenStmt:
 UNLISTEN ColId
|  UNLISTEN '*'
;


 TransactionStmt:
 ABORT_P opt_transaction opt_transaction_chain
|  START TRANSACTION transaction_mode_list_or_empty
|  COMMIT opt_transaction opt_transaction_chain
|  ROLLBACK opt_transaction opt_transaction_chain
|  SAVEPOINT ColId
|  RELEASE SAVEPOINT ColId
|  RELEASE ColId
|  ROLLBACK opt_transaction TO SAVEPOINT ColId
|  ROLLBACK opt_transaction TO ColId
|  PREPARE TRANSACTION ecpg_sconst
|  COMMIT PREPARED ecpg_sconst
|  ROLLBACK PREPARED ecpg_sconst
;


 TransactionStmtLegacy:
 BEGIN_P opt_transaction transaction_mode_list_or_empty
|  END_P opt_transaction opt_transaction_chain
;


 opt_transaction:
 WORK
|  TRANSACTION
| 
;


 transaction_mode_item:
 ISOLATION LEVEL iso_level
|  READ ONLY
|  READ WRITE
|  DEFERRABLE
|  NOT DEFERRABLE
;


 transaction_mode_list:
 transaction_mode_item
|  transaction_mode_list ',' transaction_mode_item
|  transaction_mode_list transaction_mode_item
;


 transaction_mode_list_or_empty:
 transaction_mode_list
| 
;


 opt_transaction_chain:
 AND CHAIN
|  AND NO CHAIN
| 
;


 ViewStmt:
 CREATE OptTemp VIEW qualified_name opt_column_list opt_reloptions AS SelectStmt opt_check_option
|  CREATE OR REPLACE OptTemp VIEW qualified_name opt_column_list opt_reloptions AS SelectStmt opt_check_option
|  CREATE OptTemp RECURSIVE VIEW qualified_name '(' columnList ')' opt_reloptions AS SelectStmt opt_check_option
|  CREATE OR REPLACE OptTemp RECURSIVE VIEW qualified_name '(' columnList ')' opt_reloptions AS SelectStmt opt_check_option
;


 opt_check_option:
 WITH CHECK OPTION
|  WITH CASCADED CHECK OPTION
|  WITH LOCAL CHECK OPTION
| 
;


 LoadStmt:
 LOAD file_name
;


 CreatedbStmt:
 CREATE DATABASE name opt_with createdb_opt_list
;


 createdb_opt_list:
 createdb_opt_items
| 
;


 createdb_opt_items:
 createdb_opt_item
|  createdb_opt_items createdb_opt_item
;


 createdb_opt_item:
 createdb_opt_name opt_equal NumericOnly
|  createdb_opt_name opt_equal opt_boolean_or_string
|  createdb_opt_name opt_equal DEFAULT
;


 createdb_opt_name:
 ecpg_ident
|  CONNECTION LIMIT
|  ENCODING
|  LOCATION
|  OWNER
|  TABLESPACE
|  TEMPLATE
;


 opt_equal:
 '='
| 
;


 AlterDatabaseStmt:
 ALTER DATABASE name WITH createdb_opt_list
|  ALTER DATABASE name createdb_opt_list
|  ALTER DATABASE name SET TABLESPACE name
|  ALTER DATABASE name REFRESH COLLATION VERSION_P
;


 AlterDatabaseSetStmt:
 ALTER DATABASE name SetResetClause
;


 DropdbStmt:
 DROP DATABASE name
|  DROP DATABASE IF_P EXISTS name
|  DROP DATABASE name opt_with '(' drop_option_list ')'
|  DROP DATABASE IF_P EXISTS name opt_with '(' drop_option_list ')'
;


 drop_option_list:
 drop_option
|  drop_option_list ',' drop_option
;


 drop_option:
 FORCE
;


 AlterCollationStmt:
 ALTER COLLATION any_name REFRESH VERSION_P
;


 AlterSystemStmt:
 ALTER SYSTEM_P SET generic_set
|  ALTER SYSTEM_P RESET generic_reset
;


 CreateDomainStmt:
 CREATE DOMAIN_P any_name opt_as Typename ColQualList
;


 AlterDomainStmt:
 ALTER DOMAIN_P any_name alter_column_default
|  ALTER DOMAIN_P any_name DROP NOT NULL_P
|  ALTER DOMAIN_P any_name SET NOT NULL_P
|  ALTER DOMAIN_P any_name ADD_P DomainConstraint
|  ALTER DOMAIN_P any_name DROP CONSTRAINT name opt_drop_behavior
|  ALTER DOMAIN_P any_name DROP CONSTRAINT IF_P EXISTS name opt_drop_behavior
|  ALTER DOMAIN_P any_name VALIDATE CONSTRAINT name
;


 opt_as:
 AS
| 
;


 AlterTSDictionaryStmt:
 ALTER TEXT_P SEARCH DICTIONARY any_name definition
;


 AlterTSConfigurationStmt:
 ALTER TEXT_P SEARCH CONFIGURATION any_name ADD_P MAPPING FOR name_list any_with any_name_list
|  ALTER TEXT_P SEARCH CONFIGURATION any_name ALTER MAPPING FOR name_list any_with any_name_list
|  ALTER TEXT_P SEARCH CONFIGURATION any_name ALTER MAPPING REPLACE any_name any_with any_name
|  ALTER TEXT_P SEARCH CONFIGURATION any_name ALTER MAPPING FOR name_list REPLACE any_name any_with any_name
|  ALTER TEXT_P SEARCH CONFIGURATION any_name DROP MAPPING FOR name_list
|  ALTER TEXT_P SEARCH CONFIGURATION any_name DROP MAPPING IF_P EXISTS FOR name_list
;


 any_with:
 WITH
|  WITH_LA
;


 CreateConversionStmt:
 CREATE opt_default CONVERSION_P any_name FOR ecpg_sconst TO ecpg_sconst FROM any_name
;


 RepackStmt:
 REPACK opt_utility_option_list vacuum_relation USING INDEX name
|  REPACK opt_utility_option_list vacuum_relation opt_usingindex
|  REPACK opt_utility_option_list opt_usingindex
|  CLUSTER '(' utility_option_list ')' qualified_name cluster_index_specification
|  CLUSTER opt_utility_option_list
|  CLUSTER opt_verbose qualified_name cluster_index_specification
|  CLUSTER VERBOSE
|  CLUSTER opt_verbose name ON qualified_name
;


 cluster_index_specification:
 USING name
| 
;


 VacuumStmt:
 VACUUM opt_full opt_freeze opt_verbose opt_analyze opt_vacuum_relation_list
|  VACUUM '(' utility_option_list ')' opt_vacuum_relation_list
;


 AnalyzeStmt:
 analyze_keyword opt_utility_option_list opt_vacuum_relation_list
|  analyze_keyword VERBOSE opt_vacuum_relation_list
;


 analyze_keyword:
 ANALYZE
|  ANALYSE
;


 opt_analyze:
 analyze_keyword
| 
;


 opt_verbose:
 VERBOSE
| 
;


 opt_full:
 FULL
| 
;


 opt_freeze:
 FREEZE
| 
;


 opt_name_list:
 '(' name_list ')'
| 
;


 vacuum_relation:
 relation_expr opt_name_list
;


 vacuum_relation_list:
 vacuum_relation
|  vacuum_relation_list ',' vacuum_relation
;


 opt_vacuum_relation_list:
 vacuum_relation_list
| 
;


 ExplainStmt:
 EXPLAIN ExplainableStmt
|  EXPLAIN analyze_keyword opt_verbose ExplainableStmt
|  EXPLAIN VERBOSE ExplainableStmt
|  EXPLAIN '(' utility_option_list ')' ExplainableStmt
;


 ExplainableStmt:
 SelectStmt
|  InsertStmt
|  UpdateStmt
|  DeleteStmt
|  MergeStmt
|  DeclareCursorStmt
|  CreateAsStmt
|  CreateMatViewStmt
|  RefreshMatViewStmt
|  ExecuteStmt
	{
		@$ = $1.name;
	}
;


 PrepareStmt:
PREPARE prepared_name prep_type_clause AS PreparableStmt
	{
		$$.name = @2;
		$$.type = @3;
		$$.stmt = @5;
	}
	| PREPARE prepared_name FROM execstring
	{
		$$.name = @2;
		$$.type = NULL;
		$$.stmt = @4;
	}
;


 prep_type_clause:
 '(' type_list ')'
| 
;


 PreparableStmt:
 SelectStmt
|  InsertStmt
|  UpdateStmt
|  DeleteStmt
|  MergeStmt
;


 ExecuteStmt:
EXECUTE prepared_name execute_param_clause execute_rest
	{
		$$.name = @2;
		$$.type = @3;
	}
| CREATE OptTemp TABLE create_as_target AS EXECUTE prepared_name execute_param_clause opt_with_data execute_rest
	{
		$$.name = @$;
	}
| CREATE OptTemp TABLE IF_P NOT EXISTS create_as_target AS EXECUTE prepared_name execute_param_clause opt_with_data execute_rest
	{
		$$.name = @$;
	}
;


 execute_param_clause:
 '(' expr_list ')'
| 
;


 InsertStmt:
 opt_with_clause INSERT INTO insert_target insert_rest opt_on_conflict returning_clause
;


 insert_target:
 qualified_name
|  qualified_name AS ColId
;


 insert_rest:
 SelectStmt
|  OVERRIDING override_kind VALUE_P SelectStmt
|  '(' insert_column_list ')' SelectStmt
|  '(' insert_column_list ')' OVERRIDING override_kind VALUE_P SelectStmt
|  DEFAULT VALUES
;


 override_kind:
 USER
|  SYSTEM_P
;


 insert_column_list:
 insert_column_item
|  insert_column_list ',' insert_column_item
;


 insert_column_item:
 ColId opt_indirection
;


 opt_on_conflict:
 ON CONFLICT opt_conf_expr DO SELECT opt_for_locking_strength where_clause
|  ON CONFLICT opt_conf_expr DO UPDATE SET set_clause_list where_clause
|  ON CONFLICT opt_conf_expr DO NOTHING
| 
;


 opt_conf_expr:
 '(' index_params ')' where_clause
|  ON CONSTRAINT name
| 
;


 returning_clause:
RETURNING returning_with_clause target_list opt_ecpg_into
| 
;


 returning_with_clause:
 WITH '(' returning_options ')'
| 
;


 returning_options:
 returning_option
|  returning_options ',' returning_option
;


 returning_option:
 returning_option_kind AS ColId
;


 returning_option_kind:
 OLD
|  NEW
;


 DeleteStmt:
 opt_with_clause DELETE_P FROM relation_expr_opt_alias using_clause where_or_current_clause returning_clause
|  opt_with_clause DELETE_P FROM relation_expr for_portion_of_clause for_portion_of_opt_alias using_clause where_or_current_clause returning_clause
;


 using_clause:
 USING from_list
| 
;


 LockStmt:
 LOCK_P opt_table relation_expr_list opt_lock opt_nowait
;


 opt_lock:
 IN_P lock_type MODE
| 
;


 lock_type:
 ACCESS SHARE
|  ROW SHARE
|  ROW EXCLUSIVE
|  SHARE UPDATE EXCLUSIVE
|  SHARE
|  SHARE ROW EXCLUSIVE
|  EXCLUSIVE
|  ACCESS EXCLUSIVE
;


 opt_nowait:
 NOWAIT
| 
;


 opt_nowait_or_skip:
 NOWAIT
|  SKIP LOCKED
| 
;


 UpdateStmt:
 opt_with_clause UPDATE relation_expr_opt_alias SET set_clause_list from_clause where_or_current_clause returning_clause
|  opt_with_clause UPDATE relation_expr for_portion_of_clause for_portion_of_opt_alias SET set_clause_list from_clause where_or_current_clause returning_clause
;


 set_clause_list:
 set_clause
|  set_clause_list ',' set_clause
;


 set_clause:
 set_target '=' a_expr
|  '(' set_target_list ')' '=' a_expr
;


 set_target:
 ColId opt_indirection
;


 set_target_list:
 set_target
|  set_target_list ',' set_target
;


 MergeStmt:
 opt_with_clause MERGE INTO relation_expr_opt_alias USING table_ref ON a_expr merge_when_list returning_clause
;


 merge_when_list:
 merge_when_clause
|  merge_when_list merge_when_clause
;


 merge_when_clause:
 merge_when_tgt_matched opt_merge_when_condition THEN merge_update
|  merge_when_tgt_matched opt_merge_when_condition THEN merge_delete
|  merge_when_tgt_not_matched opt_merge_when_condition THEN merge_insert
|  merge_when_tgt_matched opt_merge_when_condition THEN DO NOTHING
|  merge_when_tgt_not_matched opt_merge_when_condition THEN DO NOTHING
;


 merge_when_tgt_matched:
 WHEN MATCHED
|  WHEN NOT MATCHED BY SOURCE
;


 merge_when_tgt_not_matched:
 WHEN NOT MATCHED
|  WHEN NOT MATCHED BY TARGET
;


 opt_merge_when_condition:
 AND a_expr
| 
;


 merge_update:
 UPDATE SET set_clause_list
;


 merge_delete:
 DELETE_P
;


 merge_insert:
 INSERT merge_values_clause
|  INSERT OVERRIDING override_kind VALUE_P merge_values_clause
|  INSERT '(' insert_column_list ')' merge_values_clause
|  INSERT '(' insert_column_list ')' OVERRIDING override_kind VALUE_P merge_values_clause
|  INSERT DEFAULT VALUES
;


 merge_values_clause:
 VALUES '(' expr_list ')'
;


 DeclareCursorStmt:
 DECLARE cursor_name cursor_options CURSOR opt_hold FOR SelectStmt
	{
		struct cursor *ptr,
				   *this;
		const char *cursor_marker = @2[0] == ':' ? "$0" : @2;
		char	   *comment,
				   *c1,
				   *c2;
		int			(*strcmp_fn) (const char *, const char *) = ((@2[0] == ':' || @2[0] == '"') ? strcmp : pg_strcasecmp);

		if (INFORMIX_MODE && pg_strcasecmp(@2, "database") == 0)
			mmfatal(PARSE_ERROR, "\"database\" cannot be used as cursor name in INFORMIX mode");

		for (ptr = cur; ptr != NULL; ptr = ptr->next)
		{
			if (strcmp_fn(@2, ptr->name) == 0)
			{
				if (@2[0] == ':')
					mmerror(PARSE_ERROR, ET_ERROR, "using variable \"%s\" in different declare statements is not supported", @2 + 1);
				else
					mmerror(PARSE_ERROR, ET_ERROR, "cursor \"%s\" is already defined", @2);
			}
		}

		this = (struct cursor *) mm_alloc(sizeof(struct cursor));

		this->next = cur;
		this->name = mm_strdup(@2);
		this->function = (current_function ? mm_strdup(current_function) : NULL);
		this->connection = connection ? mm_strdup(connection) : NULL;
		this->opened = false;
		this->command = mm_strdup(cat_str(7, "declare", cursor_marker, @3, "cursor", @5, "for", @7));
		this->argsinsert = argsinsert;
		this->argsinsert_oos = NULL;
		this->argsresult = argsresult;
		this->argsresult_oos = NULL;
		argsinsert = argsresult = NULL;
		cur = this;

		c1 = loc_strdup(this->command);
		while ((c2 = strstr(c1, "*/")) != NULL)
		{
			/* We put this text into a comment, so we better remove [*][/]. */
			c2[0] = '.';
			c2[1] = '.';
		}
		comment = cat_str(3, "/*", c1, "*/");

		@$ = cat2_str(adjust_outofscope_cursor_vars(this), comment);
	}
;


 cursor_name:
 name
	| char_civar
	{
		char	   *curname = loc_alloc(strlen(@1) + 2);

		sprintf(curname, ":%s", @1);
		@$ = curname;
	}
;


 cursor_options:

|  cursor_options NO SCROLL
|  cursor_options SCROLL
|  cursor_options BINARY
|  cursor_options ASENSITIVE
|  cursor_options INSENSITIVE
;


 opt_hold:

	{
		if (compat == ECPG_COMPAT_INFORMIX_SE && autocommit)
			@$ = "with hold";
		else
			@$ = "";
	}
|  WITH HOLD
|  WITHOUT HOLD
;


 SelectStmt:
 select_no_parens %prec UMINUS
|  select_with_parens %prec UMINUS
;


 select_with_parens:
 '(' select_no_parens ')'
|  '(' select_with_parens ')'
;


 select_no_parens:
 simple_select
|  select_clause sort_clause
|  select_clause opt_sort_clause for_locking_clause opt_select_limit
|  select_clause opt_sort_clause select_limit opt_for_locking_clause
|  with_clause select_clause
|  with_clause select_clause sort_clause
|  with_clause select_clause opt_sort_clause for_locking_clause opt_select_limit
|  with_clause select_clause opt_sort_clause select_limit opt_for_locking_clause
;


 select_clause:
 simple_select
|  select_with_parens
;


 simple_select:
 SELECT opt_all_clause opt_target_list into_clause from_clause where_clause group_clause having_clause window_clause
|  SELECT distinct_clause target_list into_clause from_clause where_clause group_clause having_clause window_clause
|  values_clause
|  TABLE relation_expr
|  select_clause UNION set_quantifier select_clause
|  select_clause INTERSECT set_quantifier select_clause
|  select_clause EXCEPT set_quantifier select_clause
;


 with_clause:
 WITH cte_list
|  WITH_LA cte_list
|  WITH RECURSIVE cte_list
;


 cte_list:
 common_table_expr
|  cte_list ',' common_table_expr
;


 common_table_expr:
 name opt_name_list AS opt_materialized '(' PreparableStmt ')' opt_search_clause opt_cycle_clause
;


 opt_materialized:
 MATERIALIZED
|  NOT MATERIALIZED
| 
;


 opt_search_clause:
 SEARCH DEPTH FIRST_P BY columnList SET ColId
|  SEARCH BREADTH FIRST_P BY columnList SET ColId
| 
;


 opt_cycle_clause:
 CYCLE columnList SET ColId TO AexprConst DEFAULT AexprConst USING ColId
|  CYCLE columnList SET ColId USING ColId
| 
;


 opt_with_clause:
 with_clause
| 
;


 into_clause:
 INTO OptTempTableName
	{
		FoundInto = 1;
		@$ = cat2_str("into", @2);
	}
	| ecpg_into
	{
		@$ = "";
	}
| 
;


 OptTempTableName:
 TEMPORARY opt_table qualified_name
|  TEMP opt_table qualified_name
|  LOCAL TEMPORARY opt_table qualified_name
|  LOCAL TEMP opt_table qualified_name
|  GLOBAL TEMPORARY opt_table qualified_name
|  GLOBAL TEMP opt_table qualified_name
|  UNLOGGED opt_table qualified_name
|  TABLE qualified_name
|  qualified_name
;


 opt_table:
 TABLE
| 
;


 set_quantifier:
 ALL
|  DISTINCT
| 
;


 distinct_clause:
 DISTINCT
|  DISTINCT ON '(' expr_list ')'
;


 opt_all_clause:
 ALL
| 
;


 opt_sort_clause:
 sort_clause
| 
;


 sort_clause:
 ORDER BY sortby_list
;


 sortby_list:
 sortby
|  sortby_list ',' sortby
;


 sortby:
 a_expr USING qual_all_Op opt_nulls_order
|  a_expr opt_asc_desc opt_nulls_order
;


 select_limit:
 limit_clause offset_clause
|  offset_clause limit_clause
|  limit_clause
|  offset_clause
;


 opt_select_limit:
 select_limit
| 
;


 limit_clause:
 LIMIT select_limit_value
|  LIMIT select_limit_value ',' select_offset_value
	{
		mmerror(PARSE_ERROR, ET_WARNING, "no longer supported LIMIT #,# syntax passed to server");
	}
|  FETCH first_or_next select_fetch_first_value row_or_rows ONLY
|  FETCH first_or_next select_fetch_first_value row_or_rows WITH TIES
|  FETCH first_or_next row_or_rows ONLY
|  FETCH first_or_next row_or_rows WITH TIES
;


 offset_clause:
 OFFSET select_offset_value
|  OFFSET select_fetch_first_value row_or_rows
;


 select_limit_value:
 a_expr
|  ALL
;


 select_offset_value:
 a_expr
;


 select_fetch_first_value:
 c_expr
|  '+' I_or_F_const
|  '-' I_or_F_const
;


 I_or_F_const:
 Iconst
|  ecpg_fconst
;


 row_or_rows:
 ROW
|  ROWS
;


 first_or_next:
 FIRST_P
|  NEXT
;


 group_clause:
 GROUP_P BY set_quantifier group_by_list
| 
;


 group_by_list:
 group_by_item
|  group_by_list ',' group_by_item
;


 group_by_item:
 a_expr
|  empty_grouping_set
|  cube_clause
|  rollup_clause
|  grouping_sets_clause
;


 empty_grouping_set:
 '(' ')'
;


 rollup_clause:
 ROLLUP '(' expr_list ')'
;


 cube_clause:
 CUBE '(' expr_list ')'
;


 grouping_sets_clause:
 GROUPING SETS '(' group_by_list ')'
;


 having_clause:
 HAVING a_expr
| 
;


 for_locking_clause:
 for_locking_items
|  FOR READ ONLY
;


 opt_for_locking_clause:
 for_locking_clause
| 
;


 for_locking_items:
 for_locking_item
|  for_locking_items for_locking_item
;


 for_locking_item:
 for_locking_strength locked_rels_list opt_nowait_or_skip
;


 for_locking_strength:
 FOR UPDATE
|  FOR NO KEY UPDATE
|  FOR SHARE
|  FOR KEY SHARE
;


 opt_for_locking_strength:
 for_locking_strength
| 
;


 locked_rels_list:
 OF qualified_name_list
| 
;


 values_clause:
 VALUES '(' expr_list ')'
|  values_clause ',' '(' expr_list ')'
;


 from_clause:
 FROM from_list
| 
;


 from_list:
 table_ref
|  from_list ',' table_ref
;


 table_ref:
 relation_expr opt_alias_clause
|  relation_expr opt_alias_clause tablesample_clause
|  func_table func_alias_clause
|  LATERAL_P func_table func_alias_clause
|  xmltable opt_alias_clause
|  LATERAL_P xmltable opt_alias_clause
|  GRAPH_TABLE '(' qualified_name MATCH graph_pattern COLUMNS '(' labeled_expr_list ')' ')' opt_alias_clause
|  select_with_parens opt_alias_clause
|  LATERAL_P select_with_parens opt_alias_clause
|  joined_table
|  '(' joined_table ')' alias_clause
|  json_table opt_alias_clause
|  LATERAL_P json_table opt_alias_clause
;


 joined_table:
 '(' joined_table ')'
|  table_ref CROSS JOIN table_ref
|  table_ref join_type JOIN table_ref join_qual
|  table_ref JOIN table_ref join_qual
|  table_ref NATURAL join_type JOIN table_ref
|  table_ref NATURAL JOIN table_ref
;


 alias_clause:
 AS ColId '(' name_list ')'
|  AS ColId
|  ColId '(' name_list ')'
|  ColId
;


 opt_alias_clause:
 alias_clause
| 
;


 opt_alias_clause_for_join_using:
 AS ColId
| 
;


 func_alias_clause:
 alias_clause
|  AS '(' TableFuncElementList ')'
|  AS ColId '(' TableFuncElementList ')'
|  ColId '(' TableFuncElementList ')'
| 
;


 join_type:
 FULL opt_outer
|  LEFT opt_outer
|  RIGHT opt_outer
|  INNER_P
;


 opt_outer:
 OUTER_P
| 
;


 join_qual:
 USING '(' name_list ')' opt_alias_clause_for_join_using
|  ON a_expr
;


 relation_expr:
 qualified_name
|  extended_relation_expr
;


 extended_relation_expr:
 qualified_name '*'
|  ONLY qualified_name
|  ONLY '(' qualified_name ')'
;


 relation_expr_list:
 relation_expr
|  relation_expr_list ',' relation_expr
;


 relation_expr_opt_alias:
 relation_expr %prec UMINUS
|  relation_expr ColId
|  relation_expr AS ColId
;


 for_portion_of_opt_alias:
 AS ColId
|  BareColLabel
|  %prec UMINUS
;


 for_portion_of_clause:
 FOR PORTION OF ColId '(' a_expr ')'
|  FOR PORTION OF ColId FROM a_expr TO a_expr
;


 tablesample_clause:
 TABLESAMPLE func_name '(' expr_list ')' opt_repeatable_clause
;


 opt_repeatable_clause:
 REPEATABLE '(' a_expr ')'
| 
;


 func_table:
 func_expr_windowless opt_ordinality
|  ROWS FROM '(' rowsfrom_list ')' opt_ordinality
;


 rowsfrom_item:
 func_expr_windowless opt_col_def_list
;


 rowsfrom_list:
 rowsfrom_item
|  rowsfrom_list ',' rowsfrom_item
;


 opt_col_def_list:
 AS '(' TableFuncElementList ')'
| 
;


 opt_ordinality:
 WITH_LA ORDINALITY
| 
;


 where_clause:
 WHERE a_expr
| 
;


 where_or_current_clause:
 WHERE a_expr
|  WHERE CURRENT_P OF cursor_name
	{
		const char *cursor_marker = @4[0] == ':' ? "$0" : @4;

		@$ = cat_str(2, "where current of", cursor_marker);
	}
| 
;


 OptTableFuncElementList:
 TableFuncElementList
| 
;


 TableFuncElementList:
 TableFuncElement
|  TableFuncElementList ',' TableFuncElement
;


 TableFuncElement:
 ColId Typename opt_collate_clause
;


 xmltable:
 XMLTABLE '(' c_expr xmlexists_argument COLUMNS xmltable_column_list ')'
|  XMLTABLE '(' XMLNAMESPACES '(' xml_namespace_list ')' ',' c_expr xmlexists_argument COLUMNS xmltable_column_list ')'
;


 xmltable_column_list:
 xmltable_column_el
|  xmltable_column_list ',' xmltable_column_el
;


 xmltable_column_el:
 ColId Typename
|  ColId Typename xmltable_column_option_list
|  ColId FOR ORDINALITY
;


 xmltable_column_option_list:
 xmltable_column_option_el
|  xmltable_column_option_list xmltable_column_option_el
;


 xmltable_column_option_el:
 ecpg_ident b_expr
|  DEFAULT b_expr
|  NOT NULL_P
|  NULL_P
|  PATH b_expr
;


 xml_namespace_list:
 xml_namespace_el
|  xml_namespace_list ',' xml_namespace_el
;


 xml_namespace_el:
 b_expr AS ColLabel
|  DEFAULT b_expr
;


 json_table:
 JSON_TABLE '(' json_value_expr ',' a_expr json_table_path_name_opt json_passing_clause_opt COLUMNS '(' json_table_column_definition_list ')' json_table_plan_clause_opt json_on_error_clause_opt ')'
;


 json_table_path_name_opt:
 AS name
| 
;


 json_table_column_definition_list:
 json_table_column_definition
|  json_table_column_definition_list ',' json_table_column_definition
;


 json_table_column_definition:
 ColId FOR ORDINALITY
|  ColId Typename json_table_column_path_clause_opt json_wrapper_behavior json_quotes_clause_opt json_behavior_clause_opt
|  ColId Typename json_format_clause json_table_column_path_clause_opt json_wrapper_behavior json_quotes_clause_opt json_behavior_clause_opt
|  ColId Typename EXISTS json_table_column_path_clause_opt json_on_error_clause_opt
|  NESTED path_opt ecpg_sconst COLUMNS '(' json_table_column_definition_list ')'
|  NESTED path_opt ecpg_sconst AS name COLUMNS '(' json_table_column_definition_list ')'
;


 path_opt:
 PATH
| 
;


 json_table_column_path_clause_opt:
 PATH ecpg_sconst
| 
;


 json_table_plan_clause_opt:
 PLAN '(' json_table_plan ')'
|  PLAN DEFAULT '(' json_table_default_plan_choices ')'
| 
;


 json_table_plan:
 json_table_plan_simple
|  json_table_plan_outer
|  json_table_plan_inner
|  json_table_plan_union
|  json_table_plan_cross
;


 json_table_plan_simple:
 name
;


 json_table_plan_outer:
 json_table_plan_simple OUTER_P json_table_plan_primary
;


 json_table_plan_inner:
 json_table_plan_simple INNER_P json_table_plan_primary
;


 json_table_plan_union:
 json_table_plan_primary UNION json_table_plan_primary
|  json_table_plan_union UNION json_table_plan_primary
;


 json_table_plan_cross:
 json_table_plan_primary CROSS json_table_plan_primary
|  json_table_plan_cross CROSS json_table_plan_primary
;


 json_table_plan_primary:
 json_table_plan_simple
|  '(' json_table_plan ')'
;


 json_table_default_plan_choices:
 json_table_default_plan_inner_outer
|  json_table_default_plan_union_cross
|  json_table_default_plan_inner_outer ',' json_table_default_plan_union_cross
|  json_table_default_plan_union_cross ',' json_table_default_plan_inner_outer
;


 json_table_default_plan_inner_outer:
 INNER_P
|  OUTER_P
;


 json_table_default_plan_union_cross:
 UNION
|  CROSS
;


 Typename:
 SimpleTypename opt_array_bounds
	{
		@$ = cat2_str(@1, $2.str);
	}
|  SETOF SimpleTypename opt_array_bounds
	{
		@$ = cat_str(3, "setof", @2, $3.str);
	}
|  SimpleTypename ARRAY '[' Iconst ']'
|  SETOF SimpleTypename ARRAY '[' Iconst ']'
|  SimpleTypename ARRAY
|  SETOF SimpleTypename ARRAY
;


 opt_array_bounds:
 opt_array_bounds '[' ']'
	{
		$$.index1 = $1.index1;
		$$.index2 = $1.index2;
		if (strcmp($$.index1, "-1") == 0)
			$$.index1 = "0";
		else if (strcmp($1.index2, "-1") == 0)
			$$.index2 = "0";
		$$.str = cat_str(2, $1.str, "[]");
	}
	| opt_array_bounds '[' Iresult ']'
	{
		$$.index1 = $1.index1;
		$$.index2 = $1.index2;
		if (strcmp($1.index1, "-1") == 0)
			$$.index1 = @3;
		else if (strcmp($1.index2, "-1") == 0)
			$$.index2 = @3;
		$$.str = cat_str(4, $1.str, "[", @3, "]");
	}
| 
	{
		$$.index1 = "-1";
		$$.index2 = "-1";
		$$.str = "";
	}
;


 SimpleTypename:
 GenericType
|  Numeric
|  Bit
|  Character
|  ConstDatetime
|  ConstInterval opt_interval
|  ConstInterval '(' Iconst ')'
|  JsonType
;


 ConstTypename:
 Numeric
|  ConstBit
|  ConstCharacter
|  ConstDatetime
|  JsonType
;


 GenericType:
 type_function_name opt_type_modifiers
|  type_function_name attrs opt_type_modifiers
;


 opt_type_modifiers:
 '(' expr_list ')'
| 
;


 Numeric:
 INT_P
|  INTEGER
|  SMALLINT
|  BIGINT
|  REAL
|  FLOAT_P opt_float
|  DOUBLE_P PRECISION
|  DECIMAL_P opt_type_modifiers
|  DEC opt_type_modifiers
|  NUMERIC opt_type_modifiers
|  BOOLEAN_P
;


 opt_float:
 '(' Iconst ')'
| 
;


 Bit:
 BitWithLength
|  BitWithoutLength
;


 ConstBit:
 BitWithLength
|  BitWithoutLength
;


 BitWithLength:
 BIT opt_varying '(' expr_list ')'
;


 BitWithoutLength:
 BIT opt_varying
;


 Character:
 CharacterWithLength
|  CharacterWithoutLength
;


 ConstCharacter:
 CharacterWithLength
|  CharacterWithoutLength
;


 CharacterWithLength:
 character '(' Iconst ')'
;


 CharacterWithoutLength:
 character
;


 character:
 CHARACTER opt_varying
|  CHAR_P opt_varying
|  VARCHAR
|  NATIONAL CHARACTER opt_varying
|  NATIONAL CHAR_P opt_varying
|  NCHAR opt_varying
;


 opt_varying:
 VARYING
| 
;


 ConstDatetime:
 TIMESTAMP '(' Iconst ')' opt_timezone
|  TIMESTAMP opt_timezone
|  TIME '(' Iconst ')' opt_timezone
|  TIME opt_timezone
;


 ConstInterval:
 INTERVAL
;


 opt_timezone:
 WITH_LA TIME ZONE
|  WITHOUT_LA TIME ZONE
| 
;


 opt_interval:
 YEAR_P %prec IS
|  MONTH_P
|  DAY_P %prec IS
|  HOUR_P %prec IS
|  MINUTE_P %prec IS
|  interval_second
|  YEAR_P TO MONTH_P
|  DAY_P TO HOUR_P
|  DAY_P TO MINUTE_P
|  DAY_P TO interval_second
|  HOUR_P TO MINUTE_P
|  HOUR_P TO interval_second
|  MINUTE_P TO interval_second
| 
;


 interval_second:
 SECOND_P
|  SECOND_P '(' Iconst ')'
;


 JsonType:
 JSON
;


 a_expr:
 c_expr
|  a_expr TYPECAST Typename
|  a_expr COLLATE any_name
|  a_expr AT TIME ZONE a_expr %prec AT
|  a_expr AT LOCAL %prec AT
|  '+' a_expr %prec UMINUS
|  '-' a_expr %prec UMINUS
|  a_expr '+' a_expr
|  a_expr '-' a_expr
|  a_expr '*' a_expr
|  a_expr '/' a_expr
|  a_expr '%' a_expr
|  a_expr '^' a_expr
|  a_expr '<' a_expr
|  a_expr '>' a_expr
|  a_expr '=' a_expr
|  a_expr LESS_EQUALS a_expr
|  a_expr GREATER_EQUALS a_expr
|  a_expr NOT_EQUALS a_expr
|  RIGHT_ARROW a_expr
|  '|' a_expr
|  a_expr RIGHT_ARROW a_expr
|  a_expr '|' a_expr
|  a_expr qual_Op a_expr %prec Op
|  qual_Op a_expr %prec Op
|  a_expr AND a_expr
|  a_expr OR a_expr
|  NOT a_expr
|  NOT_LA a_expr %prec NOT
|  a_expr LIKE a_expr
|  a_expr LIKE a_expr ESCAPE a_expr %prec LIKE
|  a_expr NOT_LA LIKE a_expr %prec NOT_LA
|  a_expr NOT_LA LIKE a_expr ESCAPE a_expr %prec NOT_LA
|  a_expr ILIKE a_expr
|  a_expr ILIKE a_expr ESCAPE a_expr %prec ILIKE
|  a_expr NOT_LA ILIKE a_expr %prec NOT_LA
|  a_expr NOT_LA ILIKE a_expr ESCAPE a_expr %prec NOT_LA
|  a_expr SIMILAR TO a_expr %prec SIMILAR
|  a_expr SIMILAR TO a_expr ESCAPE a_expr %prec SIMILAR
|  a_expr NOT_LA SIMILAR TO a_expr %prec NOT_LA
|  a_expr NOT_LA SIMILAR TO a_expr ESCAPE a_expr %prec NOT_LA
|  a_expr IS NULL_P %prec IS
|  a_expr ISNULL
|  a_expr IS NOT NULL_P %prec IS
|  a_expr NOTNULL
|  row OVERLAPS row
|  a_expr IS TRUE_P %prec IS
|  a_expr IS NOT TRUE_P %prec IS
|  a_expr IS FALSE_P %prec IS
|  a_expr IS NOT FALSE_P %prec IS
|  a_expr IS UNKNOWN %prec IS
|  a_expr IS NOT UNKNOWN %prec IS
|  a_expr IS DISTINCT FROM a_expr %prec IS
|  a_expr IS NOT DISTINCT FROM a_expr %prec IS
|  a_expr BETWEEN opt_asymmetric b_expr AND a_expr %prec BETWEEN
|  a_expr NOT_LA BETWEEN opt_asymmetric b_expr AND a_expr %prec NOT_LA
|  a_expr BETWEEN SYMMETRIC b_expr AND a_expr %prec BETWEEN
|  a_expr NOT_LA BETWEEN SYMMETRIC b_expr AND a_expr %prec NOT_LA
|  a_expr IN_P select_with_parens
|  a_expr IN_P '(' expr_list ')'
|  a_expr NOT_LA IN_P select_with_parens %prec NOT_LA
|  a_expr NOT_LA IN_P '(' expr_list ')'
|  a_expr subquery_Op sub_type select_with_parens %prec Op
|  a_expr subquery_Op sub_type '(' a_expr ')' %prec Op
|  UNIQUE opt_unique_null_treatment select_with_parens
 { 
mmerror(PARSE_ERROR, ET_WARNING, "unsupported feature will be passed to server");
}
|  a_expr IS DOCUMENT_P %prec IS
|  a_expr IS NOT DOCUMENT_P %prec IS
|  a_expr IS NORMALIZED %prec IS
|  a_expr IS unicode_normal_form NORMALIZED %prec IS
|  a_expr IS NOT NORMALIZED %prec IS
|  a_expr IS NOT unicode_normal_form NORMALIZED %prec IS
|  a_expr IS json_predicate_type_constraint json_key_uniqueness_constraint_opt %prec IS
|  a_expr IS NOT json_predicate_type_constraint json_key_uniqueness_constraint_opt %prec IS
|  DEFAULT
;


 b_expr:
 c_expr
|  b_expr TYPECAST Typename
|  '+' b_expr %prec UMINUS
|  '-' b_expr %prec UMINUS
|  b_expr '+' b_expr
|  b_expr '-' b_expr
|  b_expr '*' b_expr
|  b_expr '/' b_expr
|  b_expr '%' b_expr
|  b_expr '^' b_expr
|  b_expr '<' b_expr
|  b_expr '>' b_expr
|  b_expr '=' b_expr
|  b_expr LESS_EQUALS b_expr
|  b_expr GREATER_EQUALS b_expr
|  b_expr NOT_EQUALS b_expr
|  RIGHT_ARROW b_expr
|  '|' b_expr
|  b_expr RIGHT_ARROW b_expr
|  b_expr '|' b_expr
|  b_expr qual_Op b_expr %prec Op
|  qual_Op b_expr %prec Op
|  b_expr IS DISTINCT FROM b_expr %prec IS
|  b_expr IS NOT DISTINCT FROM b_expr %prec IS
|  b_expr IS DOCUMENT_P %prec IS
|  b_expr IS NOT DOCUMENT_P %prec IS
;


 c_expr:
 columnref
|  AexprConst
|  ecpg_param opt_indirection
|  '(' a_expr ')' opt_indirection
|  case_expr
|  func_expr
|  select_with_parens %prec UMINUS
|  select_with_parens indirection
|  EXISTS select_with_parens
|  ARRAY select_with_parens
|  ARRAY array_expr
|  explicit_row
|  implicit_row
|  GROUPING '(' expr_list ')'
;


 func_application:
 func_name '(' ')'
|  func_name '(' func_arg_list opt_sort_clause ')'
|  func_name '(' VARIADIC func_arg_expr opt_sort_clause ')'
|  func_name '(' func_arg_list ',' VARIADIC func_arg_expr opt_sort_clause ')'
|  func_name '(' ALL func_arg_list opt_sort_clause ')'
|  func_name '(' DISTINCT func_arg_list opt_sort_clause ')'
|  func_name '(' '*' ')'
;


 func_expr:
 func_application within_group_clause filter_clause null_treatment over_clause
|  json_aggregate_func filter_clause over_clause
|  func_expr_common_subexpr
;


 func_expr_windowless:
 func_application
|  func_expr_common_subexpr
|  json_aggregate_func
;


 func_expr_common_subexpr:
 COLLATION FOR '(' a_expr ')'
|  CURRENT_DATE
|  CURRENT_TIME
|  CURRENT_TIME '(' Iconst ')'
|  CURRENT_TIMESTAMP
|  CURRENT_TIMESTAMP '(' Iconst ')'
|  LOCALTIME
|  LOCALTIME '(' Iconst ')'
|  LOCALTIMESTAMP
|  LOCALTIMESTAMP '(' Iconst ')'
|  CURRENT_ROLE
|  CURRENT_USER
|  SESSION_USER
|  SYSTEM_USER
|  USER
|  CURRENT_CATALOG
|  CURRENT_SCHEMA
|  CAST '(' a_expr AS Typename ')'
|  EXTRACT '(' extract_list ')'
|  NORMALIZE '(' a_expr ')'
|  NORMALIZE '(' a_expr ',' unicode_normal_form ')'
|  OVERLAY '(' overlay_list ')'
|  OVERLAY '(' func_arg_list_opt ')'
|  POSITION '(' position_list ')'
|  SUBSTRING '(' substr_list ')'
|  SUBSTRING '(' func_arg_list_opt ')'
|  TREAT '(' a_expr AS Typename ')'
|  TRIM '(' BOTH trim_list ')'
|  TRIM '(' LEADING trim_list ')'
|  TRIM '(' TRAILING trim_list ')'
|  TRIM '(' trim_list ')'
|  NULLIF '(' a_expr ',' a_expr ')'
|  COALESCE '(' expr_list ')'
|  GREATEST '(' expr_list ')'
|  LEAST '(' expr_list ')'
|  XMLCONCAT '(' expr_list ')'
|  XMLELEMENT '(' NAME_P ColLabel ')'
|  XMLELEMENT '(' NAME_P ColLabel ',' xml_attributes ')'
|  XMLELEMENT '(' NAME_P ColLabel ',' expr_list ')'
|  XMLELEMENT '(' NAME_P ColLabel ',' xml_attributes ',' expr_list ')'
|  XMLEXISTS '(' c_expr xmlexists_argument ')'
|  XMLFOREST '(' labeled_expr_list ')'
|  XMLPARSE '(' document_or_content a_expr xml_whitespace_option ')'
|  XMLPI '(' NAME_P ColLabel ')'
|  XMLPI '(' NAME_P ColLabel ',' a_expr ')'
|  XMLROOT '(' a_expr ',' xml_root_version opt_xml_root_standalone ')'
|  XMLSERIALIZE '(' document_or_content a_expr AS SimpleTypename xml_indent_option ')'
|  JSON_OBJECT '(' func_arg_list ')'
|  JSON_OBJECT '(' json_name_and_value_list json_object_constructor_null_clause_opt json_key_uniqueness_constraint_opt json_returning_clause_opt ')'
|  JSON_OBJECT '(' json_returning_clause_opt ')'
|  JSON_ARRAY '(' json_value_expr_list json_array_constructor_null_clause_opt json_returning_clause_opt ')'
|  JSON_ARRAY '(' select_no_parens json_format_clause_opt json_returning_clause_opt ')'
|  JSON_ARRAY '(' json_returning_clause_opt ')'
|  JSON '(' json_value_expr json_key_uniqueness_constraint_opt ')'
|  JSON_SCALAR '(' a_expr ')'
|  JSON_SERIALIZE '(' json_value_expr json_returning_clause_opt ')'
|  MERGE_ACTION '(' ')'
|  JSON_QUERY '(' json_value_expr ',' a_expr json_passing_clause_opt json_returning_clause_opt json_wrapper_behavior json_quotes_clause_opt json_behavior_clause_opt ')'
|  JSON_EXISTS '(' json_value_expr ',' a_expr json_passing_clause_opt json_on_error_clause_opt ')'
|  JSON_VALUE '(' json_value_expr ',' a_expr json_passing_clause_opt json_returning_clause_opt json_behavior_clause_opt ')'
;


 xml_root_version:
 VERSION_P a_expr
|  VERSION_P NO VALUE_P
;


 opt_xml_root_standalone:
 ',' STANDALONE_P YES_P
|  ',' STANDALONE_P NO
|  ',' STANDALONE_P NO VALUE_P
| 
;


 xml_attributes:
 XMLATTRIBUTES '(' labeled_expr_list ')'
;


 labeled_expr_list:
 labeled_expr
|  labeled_expr_list ',' labeled_expr
;


 labeled_expr:
 a_expr AS ColLabel
|  a_expr
;


 document_or_content:
 DOCUMENT_P
|  CONTENT_P
;


 xml_indent_option:
 INDENT
|  NO INDENT
| 
;


 xml_whitespace_option:
 PRESERVE WHITESPACE_P
|  STRIP_P WHITESPACE_P
| 
;


 xmlexists_argument:
 PASSING c_expr
|  PASSING c_expr xml_passing_mech
|  PASSING xml_passing_mech c_expr
|  PASSING xml_passing_mech c_expr xml_passing_mech
;


 xml_passing_mech:
 BY REF_P
|  BY VALUE_P
;


 WaitStmt:
 WAIT FOR LSN_P ecpg_sconst opt_wait_with_clause
;


 opt_wait_with_clause:
 WITH '(' utility_option_list ')'
| 
;


 within_group_clause:
 WITHIN GROUP_P '(' sort_clause ')'
| 
;


 filter_clause:
 FILTER '(' WHERE a_expr ')'
| 
;


 null_treatment:
 IGNORE_P NULLS_P
|  RESPECT_P NULLS_P
| 
;


 window_clause:
 WINDOW window_definition_list
| 
;


 window_definition_list:
 window_definition
|  window_definition_list ',' window_definition
;


 window_definition:
 ColId AS window_specification
;


 over_clause:
 OVER window_specification
|  OVER ColId
| 
;


 window_specification:
 '(' opt_existing_window_name opt_partition_clause opt_sort_clause opt_frame_clause ')'
;


 opt_existing_window_name:
 ColId
|  %prec Op
;


 opt_partition_clause:
 PARTITION BY expr_list
| 
;


 opt_frame_clause:
 RANGE frame_extent opt_window_exclusion_clause
|  ROWS frame_extent opt_window_exclusion_clause
|  GROUPS frame_extent opt_window_exclusion_clause
| 
;


 frame_extent:
 frame_bound
|  BETWEEN frame_bound AND frame_bound
;


 frame_bound:
 UNBOUNDED PRECEDING
|  UNBOUNDED FOLLOWING
|  CURRENT_P ROW
|  a_expr PRECEDING
|  a_expr FOLLOWING
;


 opt_window_exclusion_clause:
 EXCLUDE CURRENT_P ROW
|  EXCLUDE GROUP_P
|  EXCLUDE TIES
|  EXCLUDE NO OTHERS
| 
;


 row:
 ROW '(' expr_list ')'
|  ROW '(' ')'
|  '(' expr_list ',' a_expr ')'
;


 explicit_row:
 ROW '(' expr_list ')'
|  ROW '(' ')'
;


 implicit_row:
 '(' expr_list ',' a_expr ')'
;


 sub_type:
 ANY
|  SOME
|  ALL
;


 all_Op:
 Op
|  MathOp
;


 MathOp:
 '+'
|  '-'
|  '*'
|  '/'
|  '%'
|  '^'
|  '<'
|  '>'
|  '='
|  LESS_EQUALS
|  GREATER_EQUALS
|  NOT_EQUALS
|  RIGHT_ARROW
|  '|'
;


 qual_Op:
 Op
|  OPERATOR '(' any_operator ')'
;


 qual_all_Op:
 all_Op
|  OPERATOR '(' any_operator ')'
;


 subquery_Op:
 all_Op
|  OPERATOR '(' any_operator ')'
|  LIKE
|  NOT_LA LIKE
|  ILIKE
|  NOT_LA ILIKE
;


 expr_list:
 a_expr
|  expr_list ',' a_expr
;


 func_arg_list:
 func_arg_expr
|  func_arg_list ',' func_arg_expr
;


 func_arg_expr:
 a_expr
|  param_name COLON_EQUALS a_expr
|  param_name EQUALS_GREATER a_expr
;


 func_arg_list_opt:
 func_arg_list
| 
;


 type_list:
 Typename
|  type_list ',' Typename
;


 array_expr:
 '[' expr_list ']'
|  '[' array_expr_list ']'
|  '[' ']'
;


 array_expr_list:
 array_expr
|  array_expr_list ',' array_expr
;


 extract_list:
 extract_arg FROM a_expr
;


 extract_arg:
 ecpg_ident
|  YEAR_P
|  MONTH_P
|  DAY_P
|  HOUR_P
|  MINUTE_P
|  SECOND_P
|  ecpg_sconst
;


 unicode_normal_form:
 NFC
|  NFD
|  NFKC
|  NFKD
;


 overlay_list:
 a_expr PLACING a_expr FROM a_expr FOR a_expr
|  a_expr PLACING a_expr FROM a_expr
;


 position_list:
 b_expr IN_P b_expr
;


 substr_list:
 a_expr FROM a_expr FOR a_expr
|  a_expr FOR a_expr FROM a_expr
|  a_expr FROM a_expr
|  a_expr FOR a_expr
|  a_expr SIMILAR a_expr ESCAPE a_expr
;


 trim_list:
 a_expr FROM expr_list
|  FROM expr_list
|  expr_list
;


 case_expr:
 CASE case_arg when_clause_list case_default END_P
;


 when_clause_list:
 when_clause
|  when_clause_list when_clause
;


 when_clause:
 WHEN a_expr THEN a_expr
;


 case_default:
 ELSE a_expr
| 
;


 case_arg:
 a_expr
| 
;


 columnref:
 ColId
|  ColId indirection
;


 indirection_el:
 '.' attr_name
|  '.' '*'
|  '[' a_expr ']'
|  '[' opt_slice_bound ':' opt_slice_bound ']'
;


 opt_slice_bound:
 a_expr
| 
;


 indirection:
 indirection_el
|  indirection indirection_el
;


 opt_indirection:

|  opt_indirection indirection_el
;


 opt_asymmetric:
 ASYMMETRIC
| 
;


 json_passing_clause_opt:
 PASSING json_arguments
| 
;


 json_arguments:
 json_argument
|  json_arguments ',' json_argument
;


 json_argument:
 json_value_expr AS ColLabel
;


 json_wrapper_behavior:
 WITHOUT WRAPPER
|  WITHOUT ARRAY WRAPPER
|  WITH WRAPPER
|  WITH ARRAY WRAPPER
|  WITH CONDITIONAL ARRAY WRAPPER
|  WITH UNCONDITIONAL ARRAY WRAPPER
|  WITH CONDITIONAL WRAPPER
|  WITH UNCONDITIONAL WRAPPER
| 
;


 json_behavior:
 DEFAULT a_expr
|  json_behavior_type
;


 json_behavior_type:
 ERROR_P
|  NULL_P
|  TRUE_P
|  FALSE_P
|  UNKNOWN
|  EMPTY_P ARRAY
|  EMPTY_P OBJECT_P
|  EMPTY_P
;


 json_behavior_clause_opt:
 json_behavior ON EMPTY_P
|  json_behavior ON ERROR_P
|  json_behavior ON EMPTY_P json_behavior ON ERROR_P
| 
;


 json_on_error_clause_opt:
 json_behavior ON ERROR_P
| 
;


 json_value_expr:
 a_expr json_format_clause_opt
;


 json_format_clause:
 FORMAT_LA JSON ENCODING name
|  FORMAT_LA JSON
;


 json_format_clause_opt:
 json_format_clause
| 
;


 json_quotes_clause_opt:
 KEEP QUOTES ON SCALAR STRING_P
|  KEEP QUOTES
|  OMIT QUOTES ON SCALAR STRING_P
|  OMIT QUOTES
| 
;


 json_returning_clause_opt:
 RETURNING Typename json_format_clause_opt
| 
;


 json_predicate_type_constraint:
 JSON %prec UNBOUNDED
|  JSON VALUE_P
|  JSON ARRAY
|  JSON OBJECT_P
|  JSON SCALAR
;


 json_key_uniqueness_constraint_opt:
 WITH UNIQUE KEYS
|  WITH UNIQUE %prec UNBOUNDED
|  WITHOUT UNIQUE KEYS
|  WITHOUT UNIQUE %prec UNBOUNDED
|  %prec UNBOUNDED
;


 json_name_and_value_list:
 json_name_and_value
|  json_name_and_value_list ',' json_name_and_value
;


 json_name_and_value:
 c_expr VALUE_P json_value_expr
|  a_expr ':' json_value_expr
;


 json_object_constructor_null_clause_opt:
 NULL_P ON NULL_P
|  ABSENT ON NULL_P
| 
;


 json_array_constructor_null_clause_opt:
 NULL_P ON NULL_P
|  ABSENT ON NULL_P
| 
;


 json_value_expr_list:
 json_value_expr
|  json_value_expr_list ',' json_value_expr
;


 json_aggregate_func:
 JSON_OBJECTAGG '(' json_name_and_value json_object_constructor_null_clause_opt json_key_uniqueness_constraint_opt json_returning_clause_opt ')'
|  JSON_ARRAYAGG '(' json_value_expr json_array_aggregate_order_by_clause_opt json_array_constructor_null_clause_opt json_returning_clause_opt ')'
;


 json_array_aggregate_order_by_clause_opt:
 ORDER BY sortby_list
| 
;


 graph_pattern:
 path_pattern_list where_clause
;


 path_pattern_list:
 path_pattern
|  path_pattern_list ',' path_pattern
;


 path_pattern:
 path_pattern_expression
;


 path_pattern_expression:
 path_term
;


 path_term:
 path_factor
|  path_term path_factor
;


 path_factor:
 path_primary opt_graph_pattern_quantifier
;


 path_primary:
 '(' opt_colid opt_is_label_expression where_clause ')'
|  '<' '-' '[' opt_colid opt_is_label_expression where_clause ']' '-'
|  '-' '[' opt_colid opt_is_label_expression where_clause ']' '-' '>'
|  '-' '[' opt_colid opt_is_label_expression where_clause ']' RIGHT_ARROW
|  '-' '[' opt_colid opt_is_label_expression where_clause ']' '-'
|  '<' '-'
|  '-' '>'
|  RIGHT_ARROW
|  '-'
|  '(' path_pattern_expression where_clause ')'
;


 opt_colid:
 ColId
| 
;


 opt_is_label_expression:
 IS label_expression
| 
;


 opt_graph_pattern_quantifier:
 '{' Iconst '}'
|  '{' ',' Iconst '}'
|  '{' Iconst ',' Iconst '}'
| 
;


 label_expression:
 label_term
|  label_disjunction
;


 label_disjunction:
 label_expression '|' label_term
;


 label_term:
 name
;


 opt_target_list:
 target_list
| 
;


 target_list:
 target_el
|  target_list ',' target_el
;


 target_el:
 a_expr AS ColLabel
|  a_expr BareColLabel
|  a_expr
|  '*'
;


 qualified_name_list:
 qualified_name
|  qualified_name_list ',' qualified_name
;


 qualified_name:
 ColId
|  ColId indirection
;


 name_list:
 name
|  name_list ',' name
;


 name:
 ColId
;


 attr_name:
 ColLabel
;


 file_name:
 ecpg_sconst
;


 func_name:
 type_function_name
|  ColId indirection
;


 AexprConst:
 Iconst
|  ecpg_fconst
|  ecpg_sconst
|  ecpg_bconst
|  ecpg_xconst
|  func_name ecpg_sconst
|  func_name '(' func_arg_list opt_sort_clause ')' ecpg_sconst
|  ConstTypename ecpg_sconst
|  ConstInterval ecpg_sconst opt_interval
|  ConstInterval '(' Iconst ')' ecpg_sconst
|  TRUE_P
|  FALSE_P
|  NULL_P
	| civar
	| civarind
;


 Iconst:
 ICONST
;


 SignedIconst:
 Iconst
	| civar
|  '+' Iconst
|  '-' Iconst
;


 RoleId:
 RoleSpec
;


 RoleSpec:
 NonReservedWord
|  CURRENT_ROLE
|  CURRENT_USER
|  SESSION_USER
;


 role_list:
 RoleSpec
|  role_list ',' RoleSpec
;


 NonReservedWord:
 ecpg_ident
|  unreserved_keyword
|  col_name_keyword
|  type_func_name_keyword
;


 BareColLabel:
 ecpg_ident
|  bare_label_keyword
;


 unreserved_keyword:
 ABORT_P
|  ABSENT
|  ABSOLUTE_P
|  ACCESS
|  ACTION
|  ADD_P
|  ADMIN
|  AFTER
|  AGGREGATE
|  ALSO
|  ALTER
|  ALWAYS
|  ASENSITIVE
|  ASSERTION
|  ASSIGNMENT
|  AT
|  ATOMIC
|  ATTACH
|  ATTRIBUTE
|  BACKWARD
|  BEFORE
|  BEGIN_P
|  BREADTH
|  BY
|  CACHE
|  CALL
|  CALLED
|  CASCADE
|  CASCADED
|  CATALOG_P
|  CHAIN
|  CHARACTERISTICS
|  CHECKPOINT
|  CLASS
|  CLOSE
|  CLUSTER
|  COLUMNS
|  COMMENT
|  COMMENTS
|  COMMIT
|  COMMITTED
|  COMPRESSION
|  CONDITIONAL
|  CONFIGURATION
|  CONFLICT
|  CONSTRAINTS
|  CONTENT_P
|  CONTINUE_P
|  CONVERSION_P
|  COPY
|  COST
|  CSV
|  CUBE
|  CURSOR
|  CYCLE
|  DATA_P
|  DATABASE
|  DEALLOCATE
|  DECLARE
|  DEFAULTS
|  DEFERRED
|  DEFINER
|  DELETE_P
|  DELIMITER
|  DELIMITERS
|  DEPENDS
|  DEPTH
|  DESTINATION
|  DETACH
|  DICTIONARY
|  DISABLE_P
|  DISCARD
|  DOCUMENT_P
|  DOMAIN_P
|  DOUBLE_P
|  DROP
|  EACH
|  EDGE
|  EMPTY_P
|  ENABLE_P
|  ENCODING
|  ENCRYPTED
|  ENFORCED
|  ENUM_P
|  ERROR_P
|  ESCAPE
|  EVENT
|  EXCLUDE
|  EXCLUDING
|  EXCLUSIVE
|  EXECUTE
|  EXPLAIN
|  EXPRESSION
|  EXTENSION
|  EXTERNAL
|  FAMILY
|  FILTER
|  FINALIZE
|  FIRST_P
|  FOLLOWING
|  FORCE
|  FORMAT
|  FORWARD
|  FUNCTION
|  FUNCTIONS
|  GENERATED
|  GLOBAL
|  GRANTED
|  GRAPH
|  GROUPS
|  HANDLER
|  HEADER_P
|  HOLD
|  IDENTITY_P
|  IF_P
|  IGNORE_P
|  IMMEDIATE
|  IMMUTABLE
|  IMPLICIT_P
|  IMPORT_P
|  INCLUDE
|  INCLUDING
|  INCREMENT
|  INDENT
|  INDEX
|  INDEXES
|  INHERIT
|  INHERITS
|  INLINE_P
|  INSENSITIVE
|  INSERT
|  INSTEAD
|  INVOKER
|  ISOLATION
|  KEEP
|  KEY
|  KEYS
|  LABEL
|  LANGUAGE
|  LARGE_P
|  LAST_P
|  LEAKPROOF
|  LEVEL
|  LISTEN
|  LOAD
|  LOCAL
|  LOCATION
|  LOCK_P
|  LOCKED
|  LOGGED
|  LSN_P
|  MAPPING
|  MATCH
|  MATCHED
|  MATERIALIZED
|  MAXVALUE
|  MERGE
|  METHOD
|  MINVALUE
|  MODE
|  MOVE
|  NAME_P
|  NAMES
|  NESTED
|  NEW
|  NEXT
|  NFC
|  NFD
|  NFKC
|  NFKD
|  NO
|  NODE
|  NORMALIZED
|  NOTHING
|  NOTIFY
|  NOWAIT
|  NULLS_P
|  OBJECT_P
|  OBJECTS_P
|  OF
|  OFF
|  OIDS
|  OLD
|  OMIT
|  OPERATOR
|  OPTION
|  OPTIONS
|  ORDINALITY
|  OTHERS
|  OVER
|  OVERRIDING
|  OWNED
|  OWNER
|  PARALLEL
|  PARAMETER
|  PARSER
|  PARTIAL
|  PARTITION
|  PARTITIONS
|  PASSING
|  PASSWORD
|  PATH
|  PERIOD
|  PLAN
|  PLANS
|  POLICY
|  PORTION
|  PRECEDING
|  PREPARE
|  PREPARED
|  PRESERVE
|  PRIOR
|  PRIVILEGES
|  PROCEDURAL
|  PROCEDURE
|  PROCEDURES
|  PROGRAM
|  PROPERTIES
|  PROPERTY
|  PUBLICATION
|  QUOTE
|  QUOTES
|  RANGE
|  READ
|  REASSIGN
|  RECURSIVE
|  REF_P
|  REFERENCING
|  REFRESH
|  REINDEX
|  RELATIONSHIP
|  RELATIVE_P
|  RELEASE
|  RENAME
|  REPACK
|  REPEATABLE
|  REPLACE
|  REPLICA
|  RESET
|  RESPECT_P
|  RESTART
|  RESTRICT
|  RETURN
|  RETURNS
|  REVOKE
|  ROLE
|  ROLLBACK
|  ROLLUP
|  ROUTINE
|  ROUTINES
|  ROWS
|  RULE
|  SAVEPOINT
|  SCALAR
|  SCHEMA
|  SCHEMAS
|  SCROLL
|  SEARCH
|  SECURITY
|  SEQUENCE
|  SEQUENCES
|  SERIALIZABLE
|  SERVER
|  SESSION
|  SET
|  SETS
|  SHARE
|  SHOW
|  SIMPLE
|  SKIP
|  SNAPSHOT
|  SOURCE
|  SPLIT
|  SQL_P
|  STABLE
|  STANDALONE_P
|  START
|  STATEMENT
|  STATISTICS
|  STDIN
|  STDOUT
|  STORAGE
|  STORED
|  STRICT_P
|  STRING_P
|  STRIP_P
|  SUBSCRIPTION
|  SUPPORT
|  SYSID
|  SYSTEM_P
|  TABLES
|  TABLESPACE
|  TARGET
|  TEMP
|  TEMPLATE
|  TEMPORARY
|  TEXT_P
|  TIES
|  TRANSACTION
|  TRANSFORM
|  TRIGGER
|  TRUNCATE
|  TRUSTED
|  TYPE_P
|  TYPES_P
|  UESCAPE
|  UNBOUNDED
|  UNCOMMITTED
|  UNCONDITIONAL
|  UNENCRYPTED
|  UNKNOWN
|  UNLISTEN
|  UNLOGGED
|  UNTIL
|  UPDATE
|  VACUUM
|  VALID
|  VALIDATE
|  VALIDATOR
|  VALUE_P
|  VARYING
|  VERSION_P
|  VERTEX
|  VIEW
|  VIEWS
|  VIRTUAL
|  VOLATILE
|  WAIT
|  WHITESPACE_P
|  WITHIN
|  WITHOUT
|  WORK
|  WRAPPER
|  WRITE
|  XML_P
|  YES_P
|  ZONE
;


 col_name_keyword:
 BETWEEN
|  BIGINT
|  BIT
|  BOOLEAN_P
|  CHARACTER
|  COALESCE
|  DEC
|  DECIMAL_P
|  EXISTS
|  EXTRACT
|  FLOAT_P
|  GRAPH_TABLE
|  GREATEST
|  GROUPING
|  INOUT
|  INTEGER
|  INTERVAL
|  JSON
|  JSON_ARRAY
|  JSON_ARRAYAGG
|  JSON_EXISTS
|  JSON_OBJECT
|  JSON_OBJECTAGG
|  JSON_QUERY
|  JSON_SCALAR
|  JSON_SERIALIZE
|  JSON_TABLE
|  JSON_VALUE
|  LEAST
|  MERGE_ACTION
|  NATIONAL
|  NCHAR
|  NONE
|  NORMALIZE
|  NULLIF
|  NUMERIC
|  OUT_P
|  OVERLAY
|  POSITION
|  PRECISION
|  REAL
|  ROW
|  SETOF
|  SMALLINT
|  SUBSTRING
|  TIME
|  TIMESTAMP
|  TREAT
|  TRIM
|  VARCHAR
|  XMLATTRIBUTES
|  XMLCONCAT
|  XMLELEMENT
|  XMLEXISTS
|  XMLFOREST
|  XMLNAMESPACES
|  XMLPARSE
|  XMLPI
|  XMLROOT
|  XMLSERIALIZE
|  XMLTABLE
;


 type_func_name_keyword:
 AUTHORIZATION
|  BINARY
|  COLLATION
|  CONCURRENTLY
|  CROSS
|  CURRENT_SCHEMA
|  FREEZE
|  FULL
|  ILIKE
|  INNER_P
|  IS
|  ISNULL
|  JOIN
|  LEFT
|  LIKE
|  NATURAL
|  NOTNULL
|  OUTER_P
|  OVERLAPS
|  RIGHT
|  SIMILAR
|  TABLESAMPLE
|  VERBOSE
;


 reserved_keyword:
 ALL
|  ANALYSE
|  ANALYZE
|  AND
|  ANY
|  ARRAY
|  AS
|  ASC
|  ASYMMETRIC
|  BOTH
|  CASE
|  CAST
|  CHECK
|  COLLATE
|  COLUMN
|  CONSTRAINT
|  CREATE
|  CURRENT_CATALOG
|  CURRENT_DATE
|  CURRENT_ROLE
|  CURRENT_TIME
|  CURRENT_TIMESTAMP
|  CURRENT_USER
|  DEFAULT
|  DEFERRABLE
|  DESC
|  DISTINCT
|  DO
|  ELSE
|  END_P
|  EXCEPT
|  FALSE_P
|  FETCH
|  FOR
|  FOREIGN
|  FROM
|  GRANT
|  GROUP_P
|  HAVING
|  IN_P
|  INITIALLY
|  INTERSECT
|  INTO
|  LATERAL_P
|  LEADING
|  LIMIT
|  LOCALTIME
|  LOCALTIMESTAMP
|  NOT
|  NULL_P
|  OFFSET
|  ON
|  ONLY
|  OR
|  ORDER
|  PLACING
|  PRIMARY
|  REFERENCES
|  RETURNING
|  SELECT
|  SESSION_USER
|  SOME
|  SYMMETRIC
|  SYSTEM_USER
|  TABLE
|  THEN
|  TRAILING
|  TRUE_P
|  UNIQUE
|  USER
|  USING
|  VARIADIC
|  WHEN
|  WHERE
|  WINDOW
|  WITH
;


 bare_label_keyword:
 ABORT_P
|  ABSENT
|  ABSOLUTE_P
|  ACCESS
|  ACTION
|  ADD_P
|  ADMIN
|  AFTER
|  AGGREGATE
|  ALL
|  ALSO
|  ALTER
|  ALWAYS
|  ANALYSE
|  ANALYZE
|  AND
|  ANY
|  ASC
|  ASENSITIVE
|  ASSERTION
|  ASSIGNMENT
|  ASYMMETRIC
|  AT
|  ATOMIC
|  ATTACH
|  ATTRIBUTE
|  AUTHORIZATION
|  BACKWARD
|  BEFORE
|  BEGIN_P
|  BETWEEN
|  BIGINT
|  BINARY
|  BIT
|  BOOLEAN_P
|  BOTH
|  BREADTH
|  BY
|  CACHE
|  CALL
|  CALLED
|  CASCADE
|  CASCADED
|  CASE
|  CAST
|  CATALOG_P
|  CHAIN
|  CHARACTERISTICS
|  CHECK
|  CHECKPOINT
|  CLASS
|  CLOSE
|  CLUSTER
|  COALESCE
|  COLLATE
|  COLLATION
|  COLUMN
|  COLUMNS
|  COMMENT
|  COMMENTS
|  COMMIT
|  COMMITTED
|  COMPRESSION
|  CONCURRENTLY
|  CONDITIONAL
|  CONFIGURATION
|  CONFLICT
|  CONNECTION
|  CONSTRAINT
|  CONSTRAINTS
|  CONTENT_P
|  CONTINUE_P
|  CONVERSION_P
|  COPY
|  COST
|  CROSS
|  CSV
|  CUBE
|  CURRENT_P
|  CURRENT_CATALOG
|  CURRENT_DATE
|  CURRENT_ROLE
|  CURRENT_SCHEMA
|  CURRENT_TIME
|  CURRENT_TIMESTAMP
|  CURRENT_USER
|  CURSOR
|  CYCLE
|  DATA_P
|  DATABASE
|  DEALLOCATE
|  DEC
|  DECIMAL_P
|  DECLARE
|  DEFAULT
|  DEFAULTS
|  DEFERRABLE
|  DEFERRED
|  DEFINER
|  DELETE_P
|  DELIMITER
|  DELIMITERS
|  DEPENDS
|  DEPTH
|  DESC
|  DESTINATION
|  DETACH
|  DICTIONARY
|  DISABLE_P
|  DISCARD
|  DISTINCT
|  DO
|  DOCUMENT_P
|  DOMAIN_P
|  DOUBLE_P
|  DROP
|  EACH
|  EDGE
|  ELSE
|  EMPTY_P
|  ENABLE_P
|  ENCODING
|  ENCRYPTED
|  END_P
|  ENFORCED
|  ENUM_P
|  ERROR_P
|  ESCAPE
|  EVENT
|  EXCLUDE
|  EXCLUDING
|  EXCLUSIVE
|  EXECUTE
|  EXISTS
|  EXPLAIN
|  EXPRESSION
|  EXTENSION
|  EXTERNAL
|  EXTRACT
|  FALSE_P
|  FAMILY
|  FINALIZE
|  FIRST_P
|  FLOAT_P
|  FOLLOWING
|  FORCE
|  FOREIGN
|  FORMAT
|  FORWARD
|  FREEZE
|  FULL
|  FUNCTION
|  FUNCTIONS
|  GENERATED
|  GLOBAL
|  GRANTED
|  GRAPH
|  GRAPH_TABLE
|  GREATEST
|  GROUPING
|  GROUPS
|  HANDLER
|  HEADER_P
|  HOLD
|  IDENTITY_P
|  IF_P
|  ILIKE
|  IMMEDIATE
|  IMMUTABLE
|  IMPLICIT_P
|  IMPORT_P
|  IN_P
|  INCLUDE
|  INCLUDING
|  INCREMENT
|  INDENT
|  INDEX
|  INDEXES
|  INHERIT
|  INHERITS
|  INITIALLY
|  INLINE_P
|  INNER_P
|  INOUT
|  INPUT_P
|  INSENSITIVE
|  INSERT
|  INSTEAD
|  INT_P
|  INTEGER
|  INTERVAL
|  INVOKER
|  IS
|  ISOLATION
|  JOIN
|  JSON
|  JSON_ARRAY
|  JSON_ARRAYAGG
|  JSON_EXISTS
|  JSON_OBJECT
|  JSON_OBJECTAGG
|  JSON_QUERY
|  JSON_SCALAR
|  JSON_SERIALIZE
|  JSON_TABLE
|  JSON_VALUE
|  KEEP
|  KEY
|  KEYS
|  LABEL
|  LANGUAGE
|  LARGE_P
|  LAST_P
|  LATERAL_P
|  LEADING
|  LEAKPROOF
|  LEAST
|  LEFT
|  LEVEL
|  LIKE
|  LISTEN
|  LOAD
|  LOCAL
|  LOCALTIME
|  LOCALTIMESTAMP
|  LOCATION
|  LOCK_P
|  LOCKED
|  LOGGED
|  LSN_P
|  MAPPING
|  MATCH
|  MATCHED
|  MATERIALIZED
|  MAXVALUE
|  MERGE
|  MERGE_ACTION
|  METHOD
|  MINVALUE
|  MODE
|  MOVE
|  NAME_P
|  NAMES
|  NATIONAL
|  NATURAL
|  NCHAR
|  NESTED
|  NEW
|  NEXT
|  NFC
|  NFD
|  NFKC
|  NFKD
|  NO
|  NODE
|  NONE
|  NORMALIZE
|  NORMALIZED
|  NOT
|  NOTHING
|  NOTIFY
|  NOWAIT
|  NULL_P
|  NULLIF
|  NULLS_P
|  NUMERIC
|  OBJECT_P
|  OBJECTS_P
|  OF
|  OFF
|  OIDS
|  OLD
|  OMIT
|  ONLY
|  OPERATOR
|  OPTION
|  OPTIONS
|  OR
|  ORDINALITY
|  OTHERS
|  OUT_P
|  OUTER_P
|  OVERLAY
|  OVERRIDING
|  OWNED
|  OWNER
|  PARALLEL
|  PARAMETER
|  PARSER
|  PARTIAL
|  PARTITION
|  PARTITIONS
|  PASSING
|  PASSWORD
|  PATH
|  PERIOD
|  PLACING
|  PLAN
|  PLANS
|  POLICY
|  PORTION
|  POSITION
|  PRECEDING
|  PREPARE
|  PREPARED
|  PRESERVE
|  PRIMARY
|  PRIOR
|  PRIVILEGES
|  PROCEDURAL
|  PROCEDURE
|  PROCEDURES
|  PROGRAM
|  PROPERTIES
|  PROPERTY
|  PUBLICATION
|  QUOTE
|  QUOTES
|  RANGE
|  READ
|  REAL
|  REASSIGN
|  RECURSIVE
|  REF_P
|  REFERENCES
|  REFERENCING
|  REFRESH
|  REINDEX
|  RELATIONSHIP
|  RELATIVE_P
|  RELEASE
|  RENAME
|  REPACK
|  REPEATABLE
|  REPLACE
|  REPLICA
|  RESET
|  RESTART
|  RESTRICT
|  RETURN
|  RETURNS
|  REVOKE
|  RIGHT
|  ROLE
|  ROLLBACK
|  ROLLUP
|  ROUTINE
|  ROUTINES
|  ROW
|  ROWS
|  RULE
|  SAVEPOINT
|  SCALAR
|  SCHEMA
|  SCHEMAS
|  SCROLL
|  SEARCH
|  SECURITY
|  SELECT
|  SEQUENCE
|  SEQUENCES
|  SERIALIZABLE
|  SERVER
|  SESSION
|  SESSION_USER
|  SET
|  SETOF
|  SETS
|  SHARE
|  SHOW
|  SIMILAR
|  SIMPLE
|  SKIP
|  SMALLINT
|  SNAPSHOT
|  SOME
|  SOURCE
|  SPLIT
|  SQL_P
|  STABLE
|  STANDALONE_P
|  START
|  STATEMENT
|  STATISTICS
|  STDIN
|  STDOUT
|  STORAGE
|  STORED
|  STRICT_P
|  STRING_P
|  STRIP_P
|  SUBSCRIPTION
|  SUBSTRING
|  SUPPORT
|  SYMMETRIC
|  SYSID
|  SYSTEM_P
|  SYSTEM_USER
|  TABLE
|  TABLES
|  TABLESAMPLE
|  TABLESPACE
|  TARGET
|  TEMP
|  TEMPLATE
|  TEMPORARY
|  TEXT_P
|  THEN
|  TIES
|  TIME
|  TIMESTAMP
|  TRAILING
|  TRANSACTION
|  TRANSFORM
|  TREAT
|  TRIGGER
|  TRIM
|  TRUE_P
|  TRUNCATE
|  TRUSTED
|  TYPE_P
|  TYPES_P
|  UESCAPE
|  UNBOUNDED
|  UNCOMMITTED
|  UNCONDITIONAL
|  UNENCRYPTED
|  UNIQUE
|  UNKNOWN
|  UNLISTEN
|  UNLOGGED
|  UNTIL
|  UPDATE
|  USER
|  USING
|  VACUUM
|  VALID
|  VALIDATE
|  VALIDATOR
|  VALUE_P
|  VALUES
|  VARCHAR
|  VARIADIC
|  VERBOSE
|  VERSION_P
|  VERTEX
|  VIEW
|  VIEWS
|  VIRTUAL
|  VOLATILE
|  WAIT
|  WHEN
|  WHITESPACE_P
|  WORK
|  WRAPPER
|  WRITE
|  XML_P
|  XMLATTRIBUTES
|  XMLCONCAT
|  XMLELEMENT
|  XMLEXISTS
|  XMLFOREST
|  XMLNAMESPACES
|  XMLPARSE
|  XMLPI
|  XMLROOT
|  XMLSERIALIZE
|  XMLTABLE
|  YES_P
|  ZONE
;


/* trailer */
/* src/interfaces/ecpg/preproc/ecpg.trailer */

statements: /* EMPTY */
	| statements statement
	{
		/* Reclaim local storage used while processing statement */
		reclaim_local_storage();
		/* Clean up now-dangling location pointer */
		@$ = "";
	}
	;

statement: ecpgstart at toplevel_stmt ';'
	{
		if (connection)
			free(connection);
		connection = NULL;
	}
	| ecpgstart toplevel_stmt ';'
	{
		if (connection)
			free(connection);
		connection = NULL;
	}
	| ecpgstart ECPGVarDeclaration
	{
		fprintf(base_yyout, "%s", @$);
		output_line_number();
	}
	| ECPGDeclaration
	| c_thing
	{
		fprintf(base_yyout, "%s", @$);
	}
	| CPP_LINE
	{
		fprintf(base_yyout, "%s", @$);
	}
	| '{'
	{
		braces_open++;
		fputs("{", base_yyout);
	}
	| '}'
	{
		if (braces_open > 0)
		{
			remove_typedefs(braces_open);
			remove_variables(braces_open);
			if (--braces_open == 0)
			{
				free(current_function);
				current_function = NULL;
			}
		}
		fputs("}", base_yyout);
	}
	;

CreateAsStmt: CREATE OptTemp TABLE create_as_target AS
	{
		FoundInto = 0;
	} SelectStmt opt_with_data
	{
		if (FoundInto == 1)
			mmerror(PARSE_ERROR, ET_ERROR, "CREATE TABLE AS cannot specify INTO");
	}
	| CREATE OptTemp TABLE IF_P NOT EXISTS create_as_target AS
	{
		FoundInto = 0;
	} SelectStmt opt_with_data
	{
		if (FoundInto == 1)
			mmerror(PARSE_ERROR, ET_ERROR, "CREATE TABLE AS cannot specify INTO");
	}
	;

at: AT connection_object
	{
		if (connection)
			free(connection);
		connection = mm_strdup(@2);

		/*
		 * Do we have a variable as connection target?  Remove the variable
		 * from the variable list or else it will be used twice.
		 */
		if (argsinsert != NULL)
			argsinsert = NULL;
	}
	;

/*
 * the exec sql connect statement: connect to the given database
 */
ECPGConnect: SQL_CONNECT TO connection_target opt_connection_name opt_user
	{
		@$ = cat_str(5, @3, ",", @5, ",", @4);
	}
	| SQL_CONNECT TO DEFAULT
	{
		@$ = "NULL, NULL, NULL, \"DEFAULT\"";
	}
	/* also allow ORACLE syntax */
	| SQL_CONNECT ora_user
	{
		@$ = cat_str(3, "NULL,", @2, ", NULL");
	}
	| DATABASE connection_target
	{
		@$ = cat2_str(@2, ", NULL, NULL, NULL");
	}
	;

connection_target: opt_database_name opt_server opt_port
	{
		/* old style: dbname[@server][:port] */
		if (strlen(@2) > 0 && *(@2) != '@')
			mmerror(PARSE_ERROR, ET_ERROR, "expected \"@\", found \"%s\"", @2);

		/* C strings need to be handled differently */
		if (@1[0] == '\"')
			@$ = @1;
		else
			@$ = make3_str("\"", make3_str(@1, @2, @3), "\"");
	}
	| db_prefix ':' server opt_port '/' opt_database_name opt_options
	{
		/* new style: <tcp|unix>:postgresql://server[:port][/dbname] */
		if (strncmp(@1, "unix:postgresql", strlen("unix:postgresql")) != 0 && strncmp(@1, "tcp:postgresql", strlen("tcp:postgresql")) != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "only protocols \"tcp\" and \"unix\" and database type \"postgresql\" are supported");

		if (strncmp(@3, "//", strlen("//")) != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "expected \"://\", found \"%s\"", @3);

		if (strncmp(@1, "unix", strlen("unix")) == 0 &&
			strncmp(@3 + strlen("//"), "localhost", strlen("localhost")) != 0 &&
			strncmp(@3 + strlen("//"), "127.0.0.1", strlen("127.0.0.1")) != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "Unix-domain sockets only work on \"localhost\" but not on \"%s\"", @3 + strlen("//"));

		@$ = make3_str(make3_str("\"", @1, ":"), @3, make3_str(make3_str(@4, "/", @6), @7, "\""));
	}
	| char_variable
	| ecpg_sconst
	{
		/*
		 * We can only process double quoted strings not single quoted ones,
		 * so we change the quotes. Note that the rule for ecpg_sconst adds
		 * these single quotes.
		 */
		char   *str = loc_strdup(@1);

		str[0] = '\"';
		str[strlen(str) - 1] = '\"';
		@$ = str;
	}
	;

opt_database_name: name
	| /* EMPTY */
	;

db_prefix: ecpg_ident cvariable
	{
		if (strcmp(@2, "postgresql") != 0 && strcmp(@2, "postgres") != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "expected \"postgresql\", found \"%s\"", @2);

		if (strcmp(@1, "tcp") != 0 && strcmp(@1, "unix") != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "invalid connection type: %s", @1);

		@$ = make3_str(@1, ":", @2);
	}
	;

server: Op server_name
	{
		if (strcmp(@1, "@") != 0 && strcmp(@1, "//") != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "expected \"@\" or \"://\", found \"%s\"", @1);

		@$ = make2_str(@1, @2);
	}
	;

opt_server: server
	| /* EMPTY */
	;

server_name: ColId
	| ColId '.' server_name
	| IP
	;

opt_port: ':' Iconst
	{
		@$ = make2_str(":", @2);
	}
	| /* EMPTY */
	;

opt_connection_name: AS connection_object
	{
		@$ = @2;
	}
	| /* EMPTY */
	{
		@$ = "NULL";
	}
	;

opt_user: USER ora_user
	{
		@$ = @2;
	}
	| /* EMPTY */
	{
		@$ = "NULL, NULL";
	}
	;

ora_user: user_name
	{
		@$ = cat2_str(@1, ", NULL");
	}
	| user_name '/' user_name
	{
		@$ = cat_str(3, @1, ",", @3);
	}
	| user_name SQL_IDENTIFIED BY user_name
	{
		@$ = cat_str(3, @1, ",", @4);
	}
	| user_name USING user_name
	{
		@$ = cat_str(3, @1, ",", @3);
	}
	;

user_name: RoleId
	{
		if (@1[0] == '\"')
			@$ = @1;
		else
			@$ = make3_str("\"", @1, "\"");
	}
	| ecpg_sconst
	{
		if (@1[0] == '\"')
			@$ = @1;
		else
			@$ = make3_str("\"", @1, "\"");
	}
	| civar
	{
		enum ECPGttype type = argsinsert->variable->type->type;

		/* if array see what's inside */
		if (type == ECPGt_array)
			type = argsinsert->variable->type->u.element->type;

		/* handle varchars */
		if (type == ECPGt_varchar)
			@$ = make2_str(argsinsert->variable->name, ".arr");
		else
			@$ = argsinsert->variable->name;
	}
	;

char_variable: cvariable
	{
		/* check if we have a string variable */
		struct variable *p = find_variable(@1);
		enum ECPGttype type = p->type->type;

		/* If we have just one character this is not a string */
		if (atol(p->type->size) == 1)
			mmerror(PARSE_ERROR, ET_ERROR, "invalid data type");
		else
		{
			/* if array see what's inside */
			if (type == ECPGt_array)
				type = p->type->u.element->type;

			switch (type)
			{
				case ECPGt_char:
				case ECPGt_unsigned_char:
				case ECPGt_string:
					@$ = @1;
					break;
				case ECPGt_varchar:
					@$ = make2_str(@1, ".arr");
					break;
				default:
					mmerror(PARSE_ERROR, ET_ERROR, "invalid data type");
					@$ = @1;
					break;
			}
		}
	}
	;

opt_options: Op connect_options
	{
		if (strlen(@1) == 0)
			mmerror(PARSE_ERROR, ET_ERROR, "incomplete statement");

		if (strcmp(@1, "?") != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "unrecognized token \"%s\"", @1);

		@$ = make2_str("?", @2);
	}
	| /* EMPTY */
	;

connect_options: ColId opt_opt_value
	{
		@$ = make2_str(@1, @2);
	}
	| ColId opt_opt_value Op connect_options
	{
		if (strlen(@3) == 0)
			mmerror(PARSE_ERROR, ET_ERROR, "incomplete statement");

		if (strcmp(@3, "&") != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "unrecognized token \"%s\"", @3);

		@$ = make3_str(make2_str(@1, @2), @3, @4);
	}
	;

opt_opt_value: /* EMPTY */
	| '=' Iconst
	{
		@$ = make2_str("=", @2);
	}
	| '=' ecpg_ident
	{
		@$ = make2_str("=", @2);
	}
	| '=' civar
	{
		@$ = make2_str("=", @2);
	}
	;

prepared_name: name
	{
		size_t		slen = strlen(@1);

		if (@1[0] == '\"' && @1[slen - 1] == '\"')	/* already quoted? */
			@$ = @1;
		else					/* not quoted => convert to lowercase */
		{
			char	   *str = loc_alloc(slen + 3);

			str[0] = '\"';
			for (size_t i = 0; i < slen; i++)
				str[i + 1] = tolower((unsigned char) @1[i]);
			str[slen + 1] = '\"';
			str[slen + 2] = '\0';
			@$ = str;
		}
	}
	| char_variable
	;

/*
 * Declare Statement
 */
ECPGDeclareStmt: DECLARE prepared_name STATEMENT
	{
		struct declared_list *ptr;

		/* Check whether the declared name has been defined or not */
		for (ptr = g_declared_list; ptr != NULL; ptr = ptr->next)
		{
			if (strcmp(@2, ptr->name) == 0)
			{
				/* re-definition is not allowed */
				mmerror(PARSE_ERROR, ET_ERROR, "name \"%s\" is already declared", ptr->name);
			}
		}

		/* Add a new declared name into the g_declared_list */
		ptr = (struct declared_list *) mm_alloc(sizeof(struct declared_list));
		if (ptr)
		{
			/* initial definition */
			ptr->name = mm_strdup(@2);
			if (connection)
				ptr->connection = mm_strdup(connection);
			else
				ptr->connection = NULL;

			ptr->next = g_declared_list;
			g_declared_list = ptr;
		}

		@$ = cat_str(3, "/* declare ", @2, " as an SQL identifier */");
	}
	;

/*
 * Declare a prepared cursor. The syntax is different from the standard
 * declare statement, so we create a new rule.
 */
ECPGCursorStmt: DECLARE cursor_name cursor_options CURSOR opt_hold FOR prepared_name
	{
		struct cursor *ptr,
				   *this;
		const char *cursor_marker = @2[0] == ':' ? "$0" : @2;
		int			(*strcmp_fn) (const char *, const char *) = ((@2[0] == ':' || @2[0] == '"') ? strcmp : pg_strcasecmp);
		struct variable *thisquery = (struct variable *) mm_alloc(sizeof(struct variable));
		char	   *comment;
		char	   *con;

		if (INFORMIX_MODE && pg_strcasecmp(@2, "database") == 0)
			mmfatal(PARSE_ERROR, "\"database\" cannot be used as cursor name in INFORMIX mode");

		check_declared_list(@7);
		con = connection ? connection : "NULL";
		for (ptr = cur; ptr != NULL; ptr = ptr->next)
		{
			if (strcmp_fn(@2, ptr->name) == 0)
			{
				/* re-definition is a bug */
				if (@2[0] == ':')
					mmerror(PARSE_ERROR, ET_ERROR, "using variable \"%s\" in different declare statements is not supported", @2 + 1);
				else
					mmerror(PARSE_ERROR, ET_ERROR, "cursor \"%s\" is already defined", @2);
			}
		}

		this = (struct cursor *) mm_alloc(sizeof(struct cursor));

		/* initial definition */
		this->next = cur;
		this->name = mm_strdup(@2);
		this->function = (current_function ? mm_strdup(current_function) : NULL);
		this->connection = connection ? mm_strdup(connection) : NULL;
		this->opened = false;
		this->command = mm_strdup(cat_str(6, "declare", cursor_marker, @3, "cursor", @5, "for $1"));
		this->argsresult = NULL;
		this->argsresult_oos = NULL;

		thisquery->type = &ecpg_query;
		thisquery->brace_level = 0;
		thisquery->next = NULL;
		thisquery->name = (char *) mm_alloc(sizeof("ECPGprepared_statement(, , __LINE__)") + strlen(con) + strlen(@7));
		sprintf(thisquery->name, "ECPGprepared_statement(%s, %s, __LINE__)", con, @7);

		this->argsinsert = NULL;
		this->argsinsert_oos = NULL;
		if (@2[0] == ':')
		{
			struct variable *var = find_variable(@2 + 1);

			remove_variable_from_list(&argsinsert, var);
			add_variable_to_head(&(this->argsinsert), var, &no_indicator);
		}
		add_variable_to_head(&(this->argsinsert), thisquery, &no_indicator);

		cur = this;

		comment = cat_str(3, "/*", this->command, "*/");

		@$ = cat_str(2, adjust_outofscope_cursor_vars(this),
					 comment);
	}
	;

ECPGExecuteImmediateStmt: EXECUTE IMMEDIATE execstring
	{
		/*
		 * execute immediate means prepare the statement and immediately
		 * execute it
		 */
		@$ = @3;
	}
	;

/*
 * variable declaration outside exec sql declare block
 */
ECPGVarDeclaration: single_vt_declaration;

single_vt_declaration: type_declaration
	| var_declaration
	;

precision: NumericOnly
	;

opt_scale: ',' NumericOnly
	{
		@$ = @2;
	}
	| /* EMPTY */
	;

ecpg_interval: opt_interval
	| YEAR_P TO MINUTE_P
	| YEAR_P TO SECOND_P
	| DAY_P TO DAY_P
	| MONTH_P TO MONTH_P
	;

/*
 * variable declaration inside exec sql declare block
 */
ECPGDeclaration: sql_startdeclare
	{
		fputs("/* exec sql begin declare section */", base_yyout);
	}
	var_type_declarations sql_enddeclare
	{
		fprintf(base_yyout, "%s/* exec sql end declare section */", @3);
		output_line_number();
	}
	;

sql_startdeclare: ecpgstart BEGIN_P DECLARE SQL_SECTION ';'
	{
	}
	;

sql_enddeclare: ecpgstart END_P DECLARE SQL_SECTION ';'
	{
	}
	;

var_type_declarations: /* EMPTY */
	| vt_declarations
	;

vt_declarations: single_vt_declaration
	| CPP_LINE
	| vt_declarations single_vt_declaration
	| vt_declarations CPP_LINE
	;

variable_declarations: var_declaration
	| variable_declarations var_declaration
	;

type_declaration: S_TYPEDEF
	{
		/* reset this variable so we see if there was */
		/* an initializer specified */
		initializer = 0;
	}
	var_type	opt_pointer ECPGColLabel opt_array_bounds ';'
	{
		add_typedef(@5, $6.index1, $6.index2, $3.type_enum, $3.type_dimension, $3.type_index, initializer, *@4 ? 1 : 0);

		fprintf(base_yyout, "typedef %s %s %s %s;\n", $3.type_str, *@4 ? "*" : "", @5, $6.str);
		output_line_number();
		@$ = "";
	}
	;

var_declaration:
	storage_declaration var_type
	{
		actual_type[struct_level].type_storage = loc_strdup(@1);
		actual_type[struct_level].type_enum = $2.type_enum;
		actual_type[struct_level].type_str = $2.type_str;
		actual_type[struct_level].type_dimension = $2.type_dimension;
		actual_type[struct_level].type_index = $2.type_index;
		actual_type[struct_level].type_sizeof = $2.type_sizeof;

		actual_startline[struct_level] = hashline_number();
	}
	variable_list ';'
	{
		@$ = cat_str(5, actual_startline[struct_level], @1, $2.type_str, @4, ";\n");
	}
	| var_type
	{
		actual_type[struct_level].type_storage = loc_strdup("");
		actual_type[struct_level].type_enum = $1.type_enum;
		actual_type[struct_level].type_str = $1.type_str;
		actual_type[struct_level].type_dimension = $1.type_dimension;
		actual_type[struct_level].type_index = $1.type_index;
		actual_type[struct_level].type_sizeof = $1.type_sizeof;

		actual_startline[struct_level] = hashline_number();
	}
	variable_list ';'
	{
		@$ = cat_str(4, actual_startline[struct_level], $1.type_str, @3, ";\n");
	}
	| struct_union_type_with_symbol ';'
	;

opt_bit_field: ':' Iconst
	| /* EMPTY */
	;

storage_declaration: storage_clause storage_modifier
	| storage_clause
	| storage_modifier
	;

storage_clause: S_EXTERN
	| S_STATIC
	| S_REGISTER
	| S_AUTO
	;

storage_modifier: S_CONST
	| S_VOLATILE
	;

var_type: simple_type
	{
		$$.type_enum = $1;
		$$.type_str = loc_strdup(ecpg_type_name($1));
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| struct_union_type
	{
		$$.type_str = loc_strdup(@1);
		$$.type_dimension = "-1";
		$$.type_index = "-1";

		if (strncmp(@1, "struct", sizeof("struct") - 1) == 0)
		{
			$$.type_enum = ECPGt_struct;
			$$.type_sizeof = ECPGstruct_sizeof;
		}
		else
		{
			$$.type_enum = ECPGt_union;
			$$.type_sizeof = NULL;
		}
	}
	| enum_type
	{
		$$.type_str = loc_strdup(@1);
		$$.type_enum = ECPGt_int;
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| NUMERIC '(' precision opt_scale ')'
	{
		$$.type_enum = ECPGt_numeric;
		$$.type_str = "numeric";
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| DECIMAL_P '(' precision opt_scale ')'
	{
		$$.type_enum = ECPGt_decimal;
		$$.type_str = "decimal";
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| IDENT '(' precision opt_scale ')'
	{
		/*
		 * In C parsing mode, NUMERIC and DECIMAL are not keywords, so they
		 * will show up here as a plain identifier, and we need this duplicate
		 * code to recognize them.
		 */
		if (strcmp(@1, "numeric") == 0)
		{
			$$.type_enum = ECPGt_numeric;
			$$.type_str = "numeric";
		}
		else if (strcmp(@1, "decimal") == 0)
		{
			$$.type_enum = ECPGt_decimal;
			$$.type_str = "decimal";
		}
		else
		{
			mmerror(PARSE_ERROR, ET_ERROR, "only data types numeric and decimal have precision/scale argument");
			$$.type_enum = ECPGt_numeric;
			$$.type_str = "numeric";
		}

		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| VARCHAR
	{
		$$.type_enum = ECPGt_varchar;
		$$.type_str = "";	/* "varchar"; */
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| FLOAT_P
	{
		/* Note: DOUBLE is handled in simple_type */
		$$.type_enum = ECPGt_float;
		$$.type_str = "float";
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| NUMERIC
	{
		$$.type_enum = ECPGt_numeric;
		$$.type_str = "numeric";
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| DECIMAL_P
	{
		$$.type_enum = ECPGt_decimal;
		$$.type_str = "decimal";
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| TIMESTAMP
	{
		$$.type_enum = ECPGt_timestamp;
		$$.type_str = "timestamp";
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| STRING_P
	{
		if (INFORMIX_MODE)
		{
			/* In Informix mode, "string" is automatically a typedef */
			$$.type_enum = ECPGt_string;
			$$.type_str = "char";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else
		{
			/* Otherwise, legal only if user typedef'ed it */
			struct typedefs *this = get_typedef("string", false);

			$$.type_str = (this->type->type_enum == ECPGt_varchar || this->type->type_enum == ECPGt_bytea) ? mm_strdup("") : mm_strdup(this->name);
			$$.type_enum = this->type->type_enum;
			$$.type_dimension = this->type->type_dimension;
			$$.type_index = this->type->type_index;
			if (this->type->type_sizeof && strlen(this->type->type_sizeof) != 0)
				$$.type_sizeof = this->type->type_sizeof;
			else
				$$.type_sizeof = cat_str(3, "sizeof(", this->name, ")");

			ECPGfree_struct_member(struct_member_list[struct_level]);
			struct_member_list[struct_level] = ECPGstruct_member_dup(this->struct_member_list);
		}
	}
	| INTERVAL ecpg_interval
	{
		$$.type_enum = ECPGt_interval;
		$$.type_str = "interval";
		$$.type_dimension = "-1";
		$$.type_index = "-1";
		$$.type_sizeof = NULL;
	}
	| IDENT ecpg_interval
	{
		/*
		 * In C parsing mode, the above SQL type names are not keywords, so
		 * they will show up here as a plain identifier, and we need this
		 * duplicate code to recognize them.
		 *
		 * Note that we also handle the type names bytea, date, and datetime
		 * here, but not above because those are not currently SQL keywords.
		 * If they ever become so, they must gain duplicate productions above.
		 */
		if (strlen(@2) != 0 && strcmp(@1, "datetime") != 0 && strcmp(@1, "interval") != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "interval specification not allowed here");

		if (strcmp(@1, "varchar") == 0)
		{
			$$.type_enum = ECPGt_varchar;
			$$.type_str = "";	/* "varchar"; */
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "bytea") == 0)
		{
			$$.type_enum = ECPGt_bytea;
			$$.type_str = "";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "float") == 0)
		{
			$$.type_enum = ECPGt_float;
			$$.type_str = "float";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "double") == 0)
		{
			$$.type_enum = ECPGt_double;
			$$.type_str = "double";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "numeric") == 0)
		{
			$$.type_enum = ECPGt_numeric;
			$$.type_str = "numeric";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "decimal") == 0)
		{
			$$.type_enum = ECPGt_decimal;
			$$.type_str = "decimal";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "date") == 0)
		{
			$$.type_enum = ECPGt_date;
			$$.type_str = "date";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "timestamp") == 0)
		{
			$$.type_enum = ECPGt_timestamp;
			$$.type_str = "timestamp";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "interval") == 0)
		{
			$$.type_enum = ECPGt_interval;
			$$.type_str = "interval";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if (strcmp(@1, "datetime") == 0)
		{
			$$.type_enum = ECPGt_timestamp;
			$$.type_str = "timestamp";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else if ((strcmp(@1, "string") == 0) && INFORMIX_MODE)
		{
			$$.type_enum = ECPGt_string;
			$$.type_str = "char";
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = NULL;
		}
		else
		{
			/* Otherwise, it must be a user-defined typedef name */
			struct typedefs *this = get_typedef(@1, false);

			$$.type_str = (this->type->type_enum == ECPGt_varchar || this->type->type_enum == ECPGt_bytea) ? "" : this->name;
			$$.type_enum = this->type->type_enum;
			$$.type_dimension = this->type->type_dimension;
			$$.type_index = this->type->type_index;
			if (this->type->type_sizeof && strlen(this->type->type_sizeof) != 0)
				$$.type_sizeof = this->type->type_sizeof;
			else
				$$.type_sizeof = cat_str(3, "sizeof(", this->name, ")");

			ECPGfree_struct_member(struct_member_list[struct_level]);
			struct_member_list[struct_level] = ECPGstruct_member_dup(this->struct_member_list);
		}
	}
	| s_struct_union_symbol
	{
		/* this is for named structs/unions */
		char	   *name;
		struct typedefs *this;
		bool		forward = (forward_name != NULL && strcmp($1.symbol, forward_name) == 0 && strcmp($1.su, "struct") == 0);

		name = cat2_str($1.su, $1.symbol);
		/* Do we have a forward definition? */
		if (!forward)
		{
			/* No */

			this = get_typedef(name, false);
			$$.type_str = this->name;
			$$.type_enum = this->type->type_enum;
			$$.type_dimension = this->type->type_dimension;
			$$.type_index = this->type->type_index;
			$$.type_sizeof = this->type->type_sizeof;
			ECPGfree_struct_member(struct_member_list[struct_level]);
			struct_member_list[struct_level] = ECPGstruct_member_dup(this->struct_member_list);
		}
		else
		{
			$$.type_str = name;
			$$.type_enum = ECPGt_long;
			$$.type_dimension = "-1";
			$$.type_index = "-1";
			$$.type_sizeof = "";
			ECPGfree_struct_member(struct_member_list[struct_level]);
			struct_member_list[struct_level] = NULL;
		}
	}
	;

enum_type: ENUM_P symbol enum_definition
	| ENUM_P enum_definition
	| ENUM_P symbol
	;

enum_definition: '{' c_list '}'
	;

struct_union_type_with_symbol: s_struct_union_symbol
	{
		ECPGfree_struct_member(struct_member_list[struct_level]);
		struct_member_list[struct_level++] = NULL;
		if (struct_level >= STRUCT_DEPTH)
			mmerror(PARSE_ERROR, ET_ERROR, "too many levels in nested structure/union definition");
		forward_name = mm_strdup($1.symbol);
	}
	'{' variable_declarations '}'
	{
		struct typedefs *ptr,
				   *this;
		struct this_type su_type;

		ECPGfree_struct_member(struct_member_list[struct_level]);
		struct_member_list[struct_level] = NULL;
		struct_level--;
		if (strcmp($1.su, "struct") == 0)
			su_type.type_enum = ECPGt_struct;
		else
			su_type.type_enum = ECPGt_union;
		su_type.type_str = cat2_str($1.su, $1.symbol);
		free(forward_name);
		forward_name = NULL;

		/*
		 * This is essentially a typedef but needs the keyword struct/union as
		 * well. So we create the typedef for each struct definition with
		 * symbol
		 */
		for (ptr = types; ptr != NULL; ptr = ptr->next)
		{
			if (strcmp(su_type.type_str, ptr->name) == 0)
				/* re-definition is a bug */
				mmerror(PARSE_ERROR, ET_ERROR, "type \"%s\" is already defined", su_type.type_str);
		}

		this = (struct typedefs *) mm_alloc(sizeof(struct typedefs));

		/* initial definition */
		this->next = types;
		this->name = mm_strdup(su_type.type_str);
		this->brace_level = braces_open;
		this->type = (struct this_type *) mm_alloc(sizeof(struct this_type));
		this->type->type_storage = NULL;
		this->type->type_enum = su_type.type_enum;
		this->type->type_str = mm_strdup(su_type.type_str);
		this->type->type_dimension = mm_strdup("-1");	/* dimension of array */
		this->type->type_index = mm_strdup("-1");	/* length of string */
		this->type->type_sizeof = ECPGstruct_sizeof ? mm_strdup(ECPGstruct_sizeof) : NULL;
		this->struct_member_list = ECPGstruct_member_dup(struct_member_list[struct_level]);

		types = this;
		@$ = cat_str(4, su_type.type_str, "{", @4, "}");
	}
	;

struct_union_type: struct_union_type_with_symbol
	| s_struct_union
	{
		ECPGfree_struct_member(struct_member_list[struct_level]);
		struct_member_list[struct_level++] = NULL;
		if (struct_level >= STRUCT_DEPTH)
			mmerror(PARSE_ERROR, ET_ERROR, "too many levels in nested structure/union definition");
	}
	'{' variable_declarations '}'
	{
		ECPGfree_struct_member(struct_member_list[struct_level]);
		struct_member_list[struct_level] = NULL;
		struct_level--;
		@$ = cat_str(4, @1, "{", @4, "}");
	}
	;

s_struct_union_symbol: SQL_STRUCT symbol
	{
		$$.su = "struct";
		$$.symbol = @2;
		free(ECPGstruct_sizeof);
		ECPGstruct_sizeof = mm_strdup(cat_str(3, "sizeof(",
											  cat2_str($$.su, $$.symbol),
											  ")"));
	}
	| UNION symbol
	{
		$$.su = "union";
		$$.symbol = @2;
	}
	;

s_struct_union: SQL_STRUCT
	{
		free(ECPGstruct_sizeof);
		ECPGstruct_sizeof = mm_strdup("");	/* This must not be NULL to
											 * distinguish from simple types. */
		@$ = "struct";
	}
	| UNION
	{
		@$ = "union";
	}
	;

simple_type: unsigned_type
	| opt_signed signed_type			{ $$ = $2; }
	;

unsigned_type: SQL_UNSIGNED SQL_SHORT	{ $$ = ECPGt_unsigned_short; }
	| SQL_UNSIGNED SQL_SHORT INT_P		{ $$ = ECPGt_unsigned_short; }
	| SQL_UNSIGNED						{ $$ = ECPGt_unsigned_int; }
	| SQL_UNSIGNED INT_P				{ $$ = ECPGt_unsigned_int; }
	| SQL_UNSIGNED SQL_LONG				{ $$ = ECPGt_unsigned_long; }
	| SQL_UNSIGNED SQL_LONG INT_P		{ $$ = ECPGt_unsigned_long; }
	| SQL_UNSIGNED SQL_LONG SQL_LONG	{ $$ = ECPGt_unsigned_long_long; }
	| SQL_UNSIGNED SQL_LONG SQL_LONG INT_P	{ $$ = ECPGt_unsigned_long_long; }
	| SQL_UNSIGNED CHAR_P				{ $$ = ECPGt_unsigned_char; }
	;

signed_type: SQL_SHORT					{ $$ = ECPGt_short; }
	| SQL_SHORT INT_P					{ $$ = ECPGt_short; }
	| INT_P								{ $$ = ECPGt_int; }
	| SQL_LONG							{ $$ = ECPGt_long; }
	| SQL_LONG INT_P					{ $$ = ECPGt_long; }
	| SQL_LONG SQL_LONG					{ $$ = ECPGt_long_long; }
	| SQL_LONG SQL_LONG INT_P			{ $$ = ECPGt_long_long; }
	| SQL_BOOL							{ $$ = ECPGt_bool; }
	| CHAR_P							{ $$ = ECPGt_char; }
	| DOUBLE_P							{ $$ = ECPGt_double; }
	;

opt_signed: SQL_SIGNED
	| /* EMPTY */
	;

variable_list: variable
	| variable_list ',' variable
	{
		if (actual_type[struct_level].type_enum == ECPGt_varchar || actual_type[struct_level].type_enum == ECPGt_bytea)
			@$ = cat_str(4, @1, ";", actual_type[struct_level].type_storage, @3);
		else
			@$ = cat_str(3, @1, ",", @3);
	}
	;

variable: opt_pointer ECPGColLabel opt_array_bounds opt_bit_field opt_initializer
	{
		struct ECPGtype *type;
		const char *dimension = $3.index1;	/* dimension of array */
		const char *length = $3.index2; /* length of string */
		char	   *dim_str;
		char		vcn[32];
		int		   *varlen_type_counter;
		char	   *struct_name;

		adjust_array(actual_type[struct_level].type_enum,
					 &dimension, &length,
					 actual_type[struct_level].type_dimension,
					 actual_type[struct_level].type_index,
					 strlen(@1), false);
		switch (actual_type[struct_level].type_enum)
		{
			case ECPGt_struct:
			case ECPGt_union:
				if (atoi(dimension) < 0)
					type = ECPGmake_struct_type(struct_member_list[struct_level], actual_type[struct_level].type_enum, actual_type[struct_level].type_str, actual_type[struct_level].type_sizeof);
				else
					type = ECPGmake_array_type(ECPGmake_struct_type(struct_member_list[struct_level], actual_type[struct_level].type_enum, actual_type[struct_level].type_str, actual_type[struct_level].type_sizeof), dimension);

				@$ = cat_str(5, @1, @2, $3.str, @4, @5);
				break;

			case ECPGt_varchar:
			case ECPGt_bytea:
				if (actual_type[struct_level].type_enum == ECPGt_varchar)
				{
					varlen_type_counter = &varchar_counter;
					struct_name = " struct varchar_";
				}
				else
				{
					varlen_type_counter = &bytea_counter;
					struct_name = " struct bytea_";
				}
				if (atoi(dimension) < 0)
					type = ECPGmake_simple_type(actual_type[struct_level].type_enum, length, *varlen_type_counter);
				else
					type = ECPGmake_array_type(ECPGmake_simple_type(actual_type[struct_level].type_enum, length, *varlen_type_counter), dimension);

				if (strcmp(dimension, "0") == 0 || abs(atoi(dimension)) == 1)
					dim_str = "";
				else
					dim_str = cat_str(3, "[", dimension, "]");

				/*
				 * cannot check for atoi <= 0 because a defined constant will
				 * yield 0 here as well
				 */
				if (atoi(length) < 0 || strcmp(length, "0") == 0)
					mmerror(PARSE_ERROR, ET_ERROR, "pointers to varchar are not implemented");

				/*
				 * make sure varchar struct name is unique by adding a unique
				 * counter to its definition
				 */
				snprintf(vcn, sizeof(vcn), "%d", *varlen_type_counter);
				if (strcmp(dimension, "0") == 0)
					@$ = cat_str(7, make2_str(struct_name, vcn), " { int len; char arr[", length, "]; } *", @2, @4, @5);
				else
					@$ = cat_str(8, make2_str(struct_name, vcn), " { int len; char arr[", length, "]; } ", @2, dim_str, @4, @5);
				(*varlen_type_counter)++;
				break;

			case ECPGt_char:
			case ECPGt_unsigned_char:
			case ECPGt_string:
				if (atoi(dimension) == -1)
				{
					int			i = strlen(@5);

					if (atoi(length) == -1 && i > 0)	/* char <var>[] =
														 * "string" */
					{
						/*
						 * if we have an initializer but no string size set,
						 * let's use the initializer's length
						 */
						char   *buf = loc_alloc(32);

						snprintf(buf, 32, "sizeof(%s)", @5 + 2);
						length = buf;
					}
					type = ECPGmake_simple_type(actual_type[struct_level].type_enum, length, 0);
				}
				else
					type = ECPGmake_array_type(ECPGmake_simple_type(actual_type[struct_level].type_enum, length, 0), dimension);

				@$ = cat_str(5, @1, @2, $3.str, @4, @5);
				break;

			default:
				if (atoi(dimension) < 0)
					type = ECPGmake_simple_type(actual_type[struct_level].type_enum, "1", 0);
				else
					type = ECPGmake_array_type(ECPGmake_simple_type(actual_type[struct_level].type_enum, "1", 0), dimension);

				@$ = cat_str(5, @1, @2, $3.str, @4, @5);
				break;
		}

		if (struct_level == 0)
			new_variable(@2, type, braces_open);
		else
			ECPGmake_struct_member(@2, type, &(struct_member_list[struct_level - 1]));
	}
	;

opt_initializer: /* EMPTY */
	| '=' c_term
	{
		initializer = 1;
	}
	;

opt_pointer: /* EMPTY */
	| '*'
	| '*' '*'
	{
		@$ = "**";
	}
	;

/*
 * We try to simulate the correct DECLARE syntax here so we get dynamic SQL
 */
ECPGDeclare: DECLARE STATEMENT ecpg_ident
	{
		/* this is only supported for compatibility */
		@$ = cat_str(3, "/* declare statement", @3, "*/");
	}
	;
/*
 * the exec sql disconnect statement: disconnect from the given database
 */
ECPGDisconnect: SQL_DISCONNECT dis_name
	{
		@$ = @2;
	}
	;

dis_name: connection_object
	| CURRENT_P
	{
		@$ = "\"CURRENT\"";
	}
	| ALL
	{
		@$ = "\"ALL\"";
	}
	| /* EMPTY */
	{
		@$ = "\"CURRENT\"";
	}
	;

connection_object: name
	{
		@$ = make3_str("\"", @1, "\"");
	}
	| DEFAULT
	{
		@$ = "\"DEFAULT\"";
	}
	| char_variable
	;

execstring: char_variable
	| CSTRING
	{
		@$ = make3_str("\"", @1, "\"");
	}
	;

/*
 * the exec sql free command to deallocate a previously
 * prepared statement
 */
ECPGFree: SQL_FREE cursor_name
	{
		@$ = @2;
	}
	| SQL_FREE ALL
	{
		@$ = "all";
	}
	;

/*
 * open is an open cursor, at the moment this has to be removed
 */
ECPGOpen: SQL_OPEN cursor_name opt_ecpg_using
	{
		if (@2[0] == ':')
			remove_variable_from_list(&argsinsert, find_variable(@2 + 1));
		@$ = @2;
	}
	;

opt_ecpg_using: /* EMPTY */
	| ecpg_using
	;

ecpg_using: USING using_list
	{
		@$ = "";
	}
	| using_descriptor
	;

using_descriptor: USING SQL_P SQL_DESCRIPTOR quoted_ident_stringvar
	{
		add_variable_to_head(&argsinsert, descriptor_variable(@4, 0), &no_indicator);
		@$ = "";
	}
	| USING SQL_DESCRIPTOR name
	{
		add_variable_to_head(&argsinsert, sqlda_variable(@3), &no_indicator);
		@$ = "";
	}
	;

into_descriptor: INTO SQL_P SQL_DESCRIPTOR quoted_ident_stringvar
	{
		add_variable_to_head(&argsresult, descriptor_variable(@4, 1), &no_indicator);
		@$ = "";
	}
	| INTO SQL_DESCRIPTOR name
	{
		add_variable_to_head(&argsresult, sqlda_variable(@3), &no_indicator);
		@$ = "";
	}
	;

into_sqlda: INTO name
	{
		add_variable_to_head(&argsresult, sqlda_variable(@2), &no_indicator);
		@$ = "";
	}
	;

using_list: UsingValue | UsingValue ',' using_list
	;

UsingValue: UsingConst
	{
		char		length[32];

		snprintf(length, sizeof(length), "%zu", strlen(@1));
		add_variable_to_head(&argsinsert, new_variable(@1, ECPGmake_simple_type(ECPGt_const, length, 0), 0), &no_indicator);
	}
	| civar
	{
		@$ = "";
	}
	| civarind
	{
		@$ = "";
	}
	;

UsingConst: Iconst
	| '+' Iconst
	| '-' Iconst
	| ecpg_fconst
	| '+' ecpg_fconst
	| '-' ecpg_fconst
	| ecpg_sconst
	| ecpg_bconst
	| ecpg_xconst
	;

/*
 * We accept DESCRIBE [OUTPUT] but do nothing with DESCRIBE INPUT so far.
 */
ECPGDescribe: SQL_DESCRIBE INPUT_P prepared_name using_descriptor
	{
		$$.input = 1;
		$$.stmt_name = @3;
	}
	| SQL_DESCRIBE opt_output prepared_name using_descriptor
	{
		struct variable *var;

		var = argsinsert->variable;
		remove_variable_from_list(&argsinsert, var);
		add_variable_to_head(&argsresult, var, &no_indicator);

		$$.input = 0;
		$$.stmt_name = @3;
	}
	| SQL_DESCRIBE opt_output prepared_name into_descriptor
	{
		$$.input = 0;
		$$.stmt_name = @3;
	}
	| SQL_DESCRIBE INPUT_P prepared_name into_sqlda
	{
		$$.input = 1;
		$$.stmt_name = @3;
	}
	| SQL_DESCRIBE opt_output prepared_name into_sqlda
	{
		$$.input = 0;
		$$.stmt_name = @3;
	}
	;

opt_output: SQL_OUTPUT
	| /* EMPTY */
	;

/*
 * dynamic SQL: descriptor based access
 *	originally written by Christof Petig <christof.petig@wtal.de>
 *			and Peter Eisentraut <peter.eisentraut@credativ.de>
 */

/*
 * allocate a descriptor
 */
ECPGAllocateDescr: SQL_ALLOCATE SQL_DESCRIPTOR quoted_ident_stringvar
	{
		add_descriptor(@3, connection);
		@$ = @3;
	}
	;


/*
 * deallocate a descriptor
 */
ECPGDeallocateDescr: DEALLOCATE SQL_DESCRIPTOR quoted_ident_stringvar
	{
		drop_descriptor(@3, connection);
		@$ = @3;
	}
	;

/*
 * manipulate a descriptor header
 */

ECPGGetDescriptorHeader: SQL_GET SQL_DESCRIPTOR quoted_ident_stringvar ECPGGetDescHeaderItem
	{
		@$ = @3;
	}
	;

ECPGGetDescHeaderItem: cvariable '=' desc_header_item
	{
		push_assignment(@1, $3);
	}
	;

ECPGSetDescriptorHeader: SET SQL_DESCRIPTOR quoted_ident_stringvar ECPGSetDescHeaderItem
	{
		@$ = @3;
	}
	;

ECPGSetDescHeaderItem: desc_header_item '=' IntConstVar
	{
		push_assignment(@3, $1);
	}
	;

IntConstVar: Iconst
	{
		char		length[32];

		snprintf(length, sizeof(length), "%zu", strlen(@1));
		new_variable(@1, ECPGmake_simple_type(ECPGt_const, length, 0), 0);
	}
	| cvariable
	;

desc_header_item: SQL_COUNT
	{
		$$ = ECPGd_count;
	}
	;

/*
 * manipulate a descriptor
 */

ECPGGetDescriptor: SQL_GET SQL_DESCRIPTOR quoted_ident_stringvar VALUE_P IntConstVar ECPGGetDescItems
	{
		$$.str = @5;
		$$.name = @3;
	}
	;

ECPGGetDescItems: ECPGGetDescItem
	| ECPGGetDescItems ',' ECPGGetDescItem
	;

ECPGGetDescItem: cvariable '=' descriptor_item
	{
		push_assignment(@1, $3);
	}
	;

ECPGSetDescriptor: SET SQL_DESCRIPTOR quoted_ident_stringvar VALUE_P IntConstVar ECPGSetDescItems
	{
		$$.str = @5;
		$$.name = @3;
	}
	;

ECPGSetDescItems: ECPGSetDescItem
	| ECPGSetDescItems ',' ECPGSetDescItem
	;

ECPGSetDescItem: descriptor_item '=' AllConstVar
	{
		push_assignment(@3, $1);
	}
	;

AllConstVar: ecpg_fconst
	{
		char		length[32];

		snprintf(length, sizeof(length), "%zu", strlen(@1));
		new_variable(@1, ECPGmake_simple_type(ECPGt_const, length, 0), 0);
	}
	| IntConstVar
	| '-' ecpg_fconst
	{
		char		length[32];
		char	   *var = cat2_str("-", @2);

		snprintf(length, sizeof(length), "%zu", strlen(var));
		new_variable(var, ECPGmake_simple_type(ECPGt_const, length, 0), 0);
		@$ = var;
	}
	| '-' Iconst
	{
		char		length[32];
		char	   *var = cat2_str("-", @2);

		snprintf(length, sizeof(length), "%zu", strlen(var));
		new_variable(var, ECPGmake_simple_type(ECPGt_const, length, 0), 0);
		@$ = var;
	}
	| ecpg_sconst
	{
		char		length[32];
		char	   *var;

		/* Strip single quotes from ecpg_sconst */
		var = loc_strdup(@1 + 1);
		var[strlen(var) - 1] = '\0';
		snprintf(length, sizeof(length), "%zu", strlen(var));
		new_variable(var, ECPGmake_simple_type(ECPGt_const, length, 0), 0);
		@$ = var;
	}
	;

descriptor_item: SQL_CARDINALITY		{ $$ = ECPGd_cardinality; }
	| DATA_P							{ $$ = ECPGd_data; }
	| SQL_DATETIME_INTERVAL_CODE		{ $$ = ECPGd_di_code; }
	| SQL_DATETIME_INTERVAL_PRECISION	{ $$ = ECPGd_di_precision; }
	| SQL_INDICATOR						{ $$ = ECPGd_indicator; }
	| SQL_KEY_MEMBER					{ $$ = ECPGd_key_member; }
	| SQL_LENGTH						{ $$ = ECPGd_length; }
	| NAME_P							{ $$ = ECPGd_name; }
	| SQL_NULLABLE						{ $$ = ECPGd_nullable; }
	| SQL_OCTET_LENGTH					{ $$ = ECPGd_octet; }
	| PRECISION							{ $$ = ECPGd_precision; }
	| SQL_RETURNED_LENGTH				{ $$ = ECPGd_length; }
	| SQL_RETURNED_OCTET_LENGTH			{ $$ = ECPGd_ret_octet; }
	| SQL_SCALE							{ $$ = ECPGd_scale; }
	| TYPE_P							{ $$ = ECPGd_type; }
	;

/*
 * set/reset the automatic transaction mode, this needs a different handling
 * as the other set commands
 */
ECPGSetAutocommit: SET SQL_AUTOCOMMIT '=' on_off
	{
		@$ = @4;
	}
	| SET SQL_AUTOCOMMIT TO on_off
	{
		@$ = @4;
	}
	;

on_off: ON
	| OFF
	;

/*
 * set the actual connection, this needs a different handling as the other
 * set commands
 */
ECPGSetConnection: SET CONNECTION TO connection_object
	{
		@$ = @4;
	}
	| SET CONNECTION '=' connection_object
	{
		@$ = @4;
	}
	| SET CONNECTION connection_object
	{
		@$ = @3;
	}
	;

/*
 * define a new type for embedded SQL
 */
ECPGTypedef: TYPE_P
	{
		/* reset this variable so we see if there was */
		/* an initializer specified */
		initializer = 0;
	}
	ECPGColLabel IS var_type opt_array_bounds opt_reference
	{
		add_typedef(@3, $6.index1, $6.index2, $5.type_enum, $5.type_dimension, $5.type_index, initializer, *@7 ? 1 : 0);

		if (auto_create_c == false)
			@$ = cat_str(7, "/* exec sql type", @3, "is", $5.type_str, $6.str, @7, "*/");
		else
			@$ = cat_str(6, "typedef ", $5.type_str, *@7 ? "*" : "", @3, $6.str, ";");
	}
	;

opt_reference: SQL_REFERENCE
	| /* EMPTY */
	;

/*
 * define the type of one variable for embedded SQL
 */
ECPGVar: SQL_VAR
	{
		/* reset this variable so we see if there was */
		/* an initializer specified */
		initializer = 0;
	}
	ColLabel	IS var_type opt_array_bounds opt_reference
	{
		struct variable *p = find_variable(@3);
		const char *dimension = $6.index1;
		const char *length = $6.index2;
		struct ECPGtype *type;

		if			(($5.type_enum == ECPGt_struct ||
					  $5.type_enum == ECPGt_union) &&
					 initializer == 1)
			mmerror(PARSE_ERROR, ET_ERROR, "initializer not allowed in EXEC SQL VAR command");
		else
		{
			adjust_array($5.type_enum, &dimension, &length,
						 $5.type_dimension, $5.type_index, *@7 ? 1 : 0, false);

			switch ($5.type_enum)
			{
					case ECPGt_struct:
					case ECPGt_union:
					if (atoi(dimension) < 0)
						type = ECPGmake_struct_type(struct_member_list[struct_level], $5.type_enum, $5.type_str, $5.type_sizeof);
					else
						type = ECPGmake_array_type(ECPGmake_struct_type(struct_member_list[struct_level], $5.type_enum, $5.type_str, $5.type_sizeof), dimension);
					break;

					case ECPGt_varchar:
					case ECPGt_bytea:
					if (atoi(dimension) == -1)
						type = ECPGmake_simple_type($5.type_enum, length, 0);
					else
						type = ECPGmake_array_type(ECPGmake_simple_type($5.type_enum, length, 0), dimension);
					break;

					case ECPGt_char:
					case ECPGt_unsigned_char:
					case ECPGt_string:
					if (atoi(dimension) == -1)
						type = ECPGmake_simple_type($5.type_enum, length, 0);
					else
						type = ECPGmake_array_type(ECPGmake_simple_type($5.type_enum, length, 0), dimension);
					break;

					default:
					if (atoi(length) >= 0)
						mmerror(PARSE_ERROR, ET_ERROR, "multidimensional arrays for simple data types are not supported");

					if (atoi(dimension) < 0)
						type = ECPGmake_simple_type($5.type_enum, "1", 0);
					else
						type = ECPGmake_array_type(ECPGmake_simple_type($5.type_enum, "1", 0), dimension);
					break;
			}

			ECPGfree_type(p->type);
			p->type = type;
		}

					@$ = cat_str(7, "/* exec sql var", @3, "is", $5.type_str, $6.str, @7, "*/");
	}
	;

/*
 * whenever statement: decide what to do in case of error/no data found
 * according to SQL standards we lack: SQLSTATE, CONSTRAINT and SQLEXCEPTION
 */
ECPGWhenever: SQL_WHENEVER SQL_SQLERROR action
	{
		when_error.code = $3.code;
		free(when_error.command);
		when_error.command = $3.command ? mm_strdup($3.command) : NULL;
		@$ = cat_str(3, "/* exec sql whenever sqlerror ", $3.str, "; */");
	}
	| SQL_WHENEVER NOT SQL_FOUND action
	{
		when_nf.code = $4.code;
		free(when_nf.command);
		when_nf.command = $4.command ? mm_strdup($4.command) : NULL;
		@$ = cat_str(3, "/* exec sql whenever not found ", $4.str, "; */");
	}
	| SQL_WHENEVER SQL_SQLWARNING action
	{
		when_warn.code = $3.code;
		free(when_warn.command);
		when_warn.command = $3.command ? mm_strdup($3.command) : NULL;
		@$ = cat_str(3, "/* exec sql whenever sql_warning ", $3.str, "; */");
	}
	;

action: CONTINUE_P
	{
		$$.code = W_NOTHING;
		$$.command = NULL;
		$$.str = "continue";
	}
	| SQL_SQLPRINT
	{
		$$.code = W_SQLPRINT;
		$$.command = NULL;
		$$.str = "sqlprint";
	}
	| SQL_STOP
	{
		$$.code = W_STOP;
		$$.command = NULL;
		$$.str = "stop";
	}
	| SQL_GOTO name
	{
		$$.code = W_GOTO;
		$$.command = loc_strdup(@2);
		$$.str = cat2_str("goto ", @2);
	}
	| SQL_GO TO name
	{
		$$.code = W_GOTO;
		$$.command = loc_strdup(@3);
		$$.str = cat2_str("goto ", @3);
	}
	| DO name '(' c_args ')'
	{
		$$.code = W_DO;
		$$.command = cat_str(4, @2, "(", @4, ")");
		$$.str = cat2_str("do", $$.command);
	}
	| DO SQL_BREAK
	{
		$$.code = W_BREAK;
		$$.command = NULL;
		$$.str = "break";
	}
	| DO CONTINUE_P
	{
		$$.code = W_CONTINUE;
		$$.command = NULL;
		$$.str = "continue";
	}
	| CALL name '(' c_args ')'
	{
		$$.code = W_DO;
		$$.command = cat_str(4, @2, "(", @4, ")");
		$$.str = cat2_str("call", $$.command);
	}
	| CALL name
	{
		$$.code = W_DO;
		$$.command = cat2_str(@2, "()");
		$$.str = cat2_str("call", $$.command);
	}
	;

/* some other stuff for ecpg */

/* additional unreserved keywords */
ECPGKeywords: ECPGKeywords_vanames
	| ECPGKeywords_rest
	;

ECPGKeywords_vanames: SQL_BREAK
	| SQL_CARDINALITY
	| SQL_COUNT
	| SQL_DATETIME_INTERVAL_CODE
	| SQL_DATETIME_INTERVAL_PRECISION
	| SQL_FOUND
	| SQL_GO
	| SQL_GOTO
	| SQL_IDENTIFIED
	| SQL_INDICATOR
	| SQL_KEY_MEMBER
	| SQL_LENGTH
	| SQL_NULLABLE
	| SQL_OCTET_LENGTH
	| SQL_RETURNED_LENGTH
	| SQL_RETURNED_OCTET_LENGTH
	| SQL_SCALE
	| SQL_SECTION
	| SQL_SQLERROR
	| SQL_SQLPRINT
	| SQL_SQLWARNING
	| SQL_STOP
	;

ECPGKeywords_rest: SQL_CONNECT
	| SQL_DESCRIBE
	| SQL_DISCONNECT
	| SQL_OPEN
	| SQL_VAR
	| SQL_WHENEVER
	;

/* additional keywords that can be SQL type names (but not ECPGColLabels) */
ECPGTypeName: SQL_BOOL
	| SQL_LONG
	| SQL_OUTPUT
	| SQL_SHORT
	| SQL_STRUCT
	| SQL_SIGNED
	| SQL_UNSIGNED
	;

symbol: ColLabel
	;

ECPGColId: ecpg_ident
	| unreserved_keyword
	| col_name_keyword
	| ECPGunreserved_interval
	| ECPGKeywords
	| ECPGCKeywords
	| CHAR_P
	| VALUES
	;

/*
 * Name classification hierarchy.
 *
 * These productions should match those in the core grammar, except that
 * we use all_unreserved_keyword instead of unreserved_keyword, and
 * where possible include ECPG keywords as well as core keywords.
 */

/* Column identifier --- names that can be column, table, etc names.
 */
ColId: ecpg_ident
	| all_unreserved_keyword
	| col_name_keyword
	| ECPGKeywords
	| ECPGCKeywords
	| CHAR_P
	| VALUES
	;

/* Type/function identifier --- names that can be type or function names.
 */
type_function_name: ecpg_ident
	| all_unreserved_keyword
	| type_func_name_keyword
	| ECPGKeywords
	| ECPGCKeywords
	| ECPGTypeName
	;

/* Column label --- allowed labels in "AS" clauses.
 * This presently includes *all* Postgres keywords.
 */
ColLabel: ECPGColLabel
	| ECPGTypeName
	| CHAR_P
	| CURRENT_P
	| INPUT_P
	| INT_P
	| TO
	| UNION
	| VALUES
	| ECPGCKeywords
	| ECPGunreserved_interval
	;

ECPGColLabel: ecpg_ident
	| unreserved_keyword
	| col_name_keyword
	| type_func_name_keyword
	| reserved_keyword
	| ECPGKeywords_vanames
	| ECPGKeywords_rest
	| CONNECTION
	;

ECPGCKeywords: S_AUTO
	| S_CONST
	| S_EXTERN
	| S_REGISTER
	| S_STATIC
	| S_TYPEDEF
	| S_VOLATILE
	;

/* "Unreserved" keywords --- available for use as any kind of name.
 */

/*
 * The following symbols must be excluded from ECPGColLabel and directly
 * included into ColLabel to enable C variables to get names from ECPGColLabel:
 * DAY_P, HOUR_P, MINUTE_P, MONTH_P, SECOND_P, YEAR_P.
 *
 * We also have to exclude CONNECTION, CURRENT, and INPUT for various reasons.
 * CONNECTION can be added back in all_unreserved_keyword, but CURRENT and
 * INPUT are reserved for ecpg purposes.
 *
 * The mentioned exclusions are done by $replace_line settings in parse.pl.
 */
all_unreserved_keyword: unreserved_keyword
	| ECPGunreserved_interval
	| CONNECTION
	;

ECPGunreserved_interval: DAY_P
	| HOUR_P
	| MINUTE_P
	| MONTH_P
	| SECOND_P
	| YEAR_P
	;

into_list: coutputvariable | into_list ',' coutputvariable
	;

ecpgstart: SQL_START
	{
		reset_variables();
		pacounter = 1;
		@$ = "";
	}
	;

c_args: /* EMPTY */
	| c_list
	;

coutputvariable: cvariable indicator
	{
		add_variable_to_head(&argsresult, find_variable(@1), find_variable(@2));
	}
	| cvariable
	{
		add_variable_to_head(&argsresult, find_variable(@1), &no_indicator);
	}
	;


civarind: cvariable indicator
	{
		if (find_variable(@2)->type->type == ECPGt_array)
			mmerror(PARSE_ERROR, ET_ERROR, "arrays of indicators are not allowed on input");

		add_variable_to_head(&argsinsert, find_variable(@1), find_variable(@2));
		@$ = create_questionmarks(@1, false);
	}
	;

char_civar: char_variable
	{
		char	   *var = loc_strdup(@1);
		char	   *ptr = strstr(var, ".arr");

		if (ptr)				/* varchar, we need the struct name here, not
								 * the struct element */
			*ptr = '\0';
		add_variable_to_head(&argsinsert, find_variable(var), &no_indicator);
		@$ = var;
	}
	;

civar: cvariable
	{
		add_variable_to_head(&argsinsert, find_variable(@1), &no_indicator);
		@$ = create_questionmarks(@1, false);
	}
	;

indicator: cvariable
	{
		check_indicator((find_variable(@1))->type);
	}
	| SQL_INDICATOR cvariable
	{
		check_indicator((find_variable(@2))->type);
		@$ = @2;
	}
	| SQL_INDICATOR name
	{
		check_indicator((find_variable(@2))->type);
		@$ = @2;
	}
	;

cvariable: CVARIABLE
	{
		/*
		 * As long as multidimensional arrays are not implemented we have to
		 * check for those here
		 */
		const char *ptr = @1;
		int			brace_open = 0,
					brace = false;

		for (; *ptr; ptr++)
		{
			switch (*ptr)
			{
				case '[':
					if (brace)
						mmfatal(PARSE_ERROR, "multidimensional arrays for simple data types are not supported");
					brace_open++;
					break;
				case ']':
					brace_open--;
					if (brace_open == 0)
						brace = true;
					break;
				case '\t':
				case ' ':
					break;
				default:
					if (brace_open == 0)
						brace = false;
					break;
			}
		}
	}
	;

ecpg_param: PARAM
	;

ecpg_bconst: BCONST
	;

ecpg_fconst: FCONST
	;

ecpg_sconst: SCONST
	;

ecpg_xconst: XCONST
	;

ecpg_ident: IDENT
	| CSTRING
	{
		@$ = make3_str("\"", @1, "\"");
	}
	;

quoted_ident_stringvar: name
	{
		@$ = make3_str("\"", @1, "\"");
	}
	| char_variable
	{
		@$ = make3_str("(", @1, ")");
	}
	;

/*
 * C stuff
 */

c_stuff_item: c_anything
	| '(' ')'
	{
		@$ = "()";
	}
	| '(' c_stuff ')'
	;

c_stuff: c_stuff_item
	| c_stuff c_stuff_item
	;

c_list: c_term
	| c_list ',' c_term
	;

c_term: c_stuff
	| '{' c_list '}'
	;

c_thing: c_anything
	| '('
	| ')'
	| ','
	| ';'
	;

/*
 * Note: NULL_P is treated specially to force it to be output in upper case,
 * since it's likely meant as a reference to the standard C macro NULL.
 */
c_anything: ecpg_ident
	| Iconst
	| ecpg_fconst
	| ecpg_sconst
	| '*'
	| '+'
	| '-'
	| '/'
	| '%'
	| NULL_P						{ @$ = "NULL"; }
	| S_ADD
	| S_AND
	| S_ANYTHING
	| S_AUTO
	| S_CONST
	| S_DEC
	| S_DIV
	| S_DOTPOINT
	| S_EQUAL
	| S_EXTERN
	| S_INC
	| S_LSHIFT
	| S_MEMBER
	| S_MEMPOINT
	| S_MOD
	| S_MUL
	| S_NEQUAL
	| S_OR
	| S_REGISTER
	| S_RSHIFT
	| S_STATIC
	| S_SUB
	| S_TYPEDEF
	| S_VOLATILE
	| SQL_BOOL
	| ENUM_P
	| HOUR_P
	| INT_P
	| SQL_LONG
	| MINUTE_P
	| MONTH_P
	| SECOND_P
	| SQL_SHORT
	| SQL_SIGNED
	| SQL_STRUCT
	| SQL_UNSIGNED
	| YEAR_P
	| CHAR_P
	| FLOAT_P
	| TO
	| UNION
	| VARCHAR
	| '['
	| ']'
	| '='
	| ':'
	;

DeallocateStmt: DEALLOCATE prepared_name
	{
		check_declared_list(@2);
		@$ = @2;
	}
	| DEALLOCATE PREPARE prepared_name
	{
		check_declared_list(@3);
		@$ = @3;
	}
	| DEALLOCATE ALL
	{
		@$ = "all";
	}
	| DEALLOCATE PREPARE ALL
	{
		@$ = "all";
	}
	;

Iresult: Iconst
	| '(' Iresult ')'
	| Iresult '+' Iresult
	| Iresult '-' Iresult
	| Iresult '*' Iresult
	| Iresult '/' Iresult
	| Iresult '%' Iresult
	| ecpg_sconst
	| ColId
	| ColId '(' var_type ')'
	{
		if (pg_strcasecmp(@1, "sizeof") != 0)
			mmerror(PARSE_ERROR, ET_ERROR, "operator not allowed in variable definition");
		else
			@$ = cat_str(4, @1, "(", $3.type_str, ")");
	}
	;

execute_rest: /* EMPTY */
	| ecpg_using opt_ecpg_into
	| ecpg_into ecpg_using
	| ecpg_into
	;

ecpg_into: INTO into_list
	{
		/* always suppress this from the constructed string */
		@$ = "";
	}
	| into_descriptor
	;

opt_ecpg_into: /* EMPTY */
	| ecpg_into
	;

ecpg_fetch_into: ecpg_into
	| using_descriptor
	{
		struct variable *var;

		var = argsinsert->variable;
		remove_variable_from_list(&argsinsert, var);
		add_variable_to_head(&argsresult, var, &no_indicator);
	}
	;

opt_ecpg_fetch_into: /* EMPTY */
	| ecpg_fetch_into
	;

%%

void
base_yyerror(const char *error)
{
	/* translator: %s is typically the translation of "syntax error" */
	mmerror(PARSE_ERROR, ET_ERROR, "%s at or near \"%s\"",
			_(error), token_start ? token_start : base_yytext);
}

void
parser_init(void)
{
	/*
	 * This function is empty. It only exists for compatibility with the
	 * backend parser right now.
	 */
}
