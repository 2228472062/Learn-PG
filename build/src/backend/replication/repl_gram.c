/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1


/* Substitute the variable and function names.  */
#define yyparse         replication_yyparse
#define yylex           replication_yylex
#define yyerror         replication_yyerror
#define yydebug         replication_yydebug
#define yynerrs         replication_yynerrs

/* First part of user prologue.  */
#line 1 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"

/*-------------------------------------------------------------------------
 *
 * repl_gram.y				- Parser for the replication commands
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/replication/repl_gram.y
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/xlogdefs.h"
#include "nodes/makefuncs.h"
#include "nodes/parsenodes.h"
#include "nodes/replnodes.h"
#include "replication/walsender.h"
#include "replication/walsender_private.h"

#include "repl_gram.h"


/*
 * Bison doesn't allocate anything that needs to live across parser calls,
 * so we can easily have it use palloc instead of malloc.  This prevents
 * memory leaks if we error out during parsing.
 */
#define YYMALLOC palloc
#define YYFREE   pfree


#line 113 "repl_gram.c"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "repl_gram.h"
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_SCONST = 3,                     /* SCONST  */
  YYSYMBOL_IDENT = 4,                      /* IDENT  */
  YYSYMBOL_UCONST = 5,                     /* UCONST  */
  YYSYMBOL_RECPTR = 6,                     /* RECPTR  */
  YYSYMBOL_K_BASE_BACKUP = 7,              /* K_BASE_BACKUP  */
  YYSYMBOL_K_IDENTIFY_SYSTEM = 8,          /* K_IDENTIFY_SYSTEM  */
  YYSYMBOL_K_READ_REPLICATION_SLOT = 9,    /* K_READ_REPLICATION_SLOT  */
  YYSYMBOL_K_SHOW = 10,                    /* K_SHOW  */
  YYSYMBOL_K_START_REPLICATION = 11,       /* K_START_REPLICATION  */
  YYSYMBOL_K_CREATE_REPLICATION_SLOT = 12, /* K_CREATE_REPLICATION_SLOT  */
  YYSYMBOL_K_DROP_REPLICATION_SLOT = 13,   /* K_DROP_REPLICATION_SLOT  */
  YYSYMBOL_K_ALTER_REPLICATION_SLOT = 14,  /* K_ALTER_REPLICATION_SLOT  */
  YYSYMBOL_K_TIMELINE_HISTORY = 15,        /* K_TIMELINE_HISTORY  */
  YYSYMBOL_K_WAIT = 16,                    /* K_WAIT  */
  YYSYMBOL_K_TIMELINE = 17,                /* K_TIMELINE  */
  YYSYMBOL_K_PHYSICAL = 18,                /* K_PHYSICAL  */
  YYSYMBOL_K_LOGICAL = 19,                 /* K_LOGICAL  */
  YYSYMBOL_K_SLOT = 20,                    /* K_SLOT  */
  YYSYMBOL_K_RESERVE_WAL = 21,             /* K_RESERVE_WAL  */
  YYSYMBOL_K_TEMPORARY = 22,               /* K_TEMPORARY  */
  YYSYMBOL_K_TWO_PHASE = 23,               /* K_TWO_PHASE  */
  YYSYMBOL_K_EXPORT_SNAPSHOT = 24,         /* K_EXPORT_SNAPSHOT  */
  YYSYMBOL_K_NOEXPORT_SNAPSHOT = 25,       /* K_NOEXPORT_SNAPSHOT  */
  YYSYMBOL_K_USE_SNAPSHOT = 26,            /* K_USE_SNAPSHOT  */
  YYSYMBOL_K_UPLOAD_MANIFEST = 27,         /* K_UPLOAD_MANIFEST  */
  YYSYMBOL_28_ = 28,                       /* ';'  */
  YYSYMBOL_29_ = 29,                       /* '.'  */
  YYSYMBOL_30_ = 30,                       /* '('  */
  YYSYMBOL_31_ = 31,                       /* ')'  */
  YYSYMBOL_32_ = 32,                       /* ','  */
  YYSYMBOL_YYACCEPT = 33,                  /* $accept  */
  YYSYMBOL_firstcmd = 34,                  /* firstcmd  */
  YYSYMBOL_opt_semicolon = 35,             /* opt_semicolon  */
  YYSYMBOL_command = 36,                   /* command  */
  YYSYMBOL_identify_system = 37,           /* identify_system  */
  YYSYMBOL_read_replication_slot = 38,     /* read_replication_slot  */
  YYSYMBOL_show = 39,                      /* show  */
  YYSYMBOL_var_name = 40,                  /* var_name  */
  YYSYMBOL_base_backup = 41,               /* base_backup  */
  YYSYMBOL_create_replication_slot = 42,   /* create_replication_slot  */
  YYSYMBOL_create_slot_options = 43,       /* create_slot_options  */
  YYSYMBOL_create_slot_legacy_opt_list = 44, /* create_slot_legacy_opt_list  */
  YYSYMBOL_create_slot_legacy_opt = 45,    /* create_slot_legacy_opt  */
  YYSYMBOL_drop_replication_slot = 46,     /* drop_replication_slot  */
  YYSYMBOL_alter_replication_slot = 47,    /* alter_replication_slot  */
  YYSYMBOL_start_replication = 48,         /* start_replication  */
  YYSYMBOL_start_logical_replication = 49, /* start_logical_replication  */
  YYSYMBOL_timeline_history = 50,          /* timeline_history  */
  YYSYMBOL_upload_manifest = 51,           /* upload_manifest  */
  YYSYMBOL_opt_physical = 52,              /* opt_physical  */
  YYSYMBOL_opt_temporary = 53,             /* opt_temporary  */
  YYSYMBOL_opt_slot = 54,                  /* opt_slot  */
  YYSYMBOL_opt_timeline = 55,              /* opt_timeline  */
  YYSYMBOL_plugin_options = 56,            /* plugin_options  */
  YYSYMBOL_plugin_opt_list = 57,           /* plugin_opt_list  */
  YYSYMBOL_plugin_opt_elem = 58,           /* plugin_opt_elem  */
  YYSYMBOL_plugin_opt_arg = 59,            /* plugin_opt_arg  */
  YYSYMBOL_generic_option_list = 60,       /* generic_option_list  */
  YYSYMBOL_generic_option = 61,            /* generic_option  */
  YYSYMBOL_ident_or_keyword = 62           /* ident_or_keyword  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_int8 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if !defined yyoverflow

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* !defined yyoverflow */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  34
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   80

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  33
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  30
/* YYNRULES -- Number of rules.  */
#define YYNRULES  82
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  109

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   282


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      30,    31,     2,     2,    32,     2,    29,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,    28,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   102,   102,   110,   111,   115,   116,   117,   118,   119,
     120,   121,   122,   123,   124,   125,   132,   142,   154,   161,
     162,   170,   176,   185,   196,   210,   211,   215,   218,   222,
     227,   232,   237,   242,   251,   259,   271,   285,   300,   315,
     333,   341,   342,   346,   347,   351,   354,   358,   366,   371,
     372,   376,   380,   387,   394,   395,   399,   401,   406,   410,
     414,   418,   425,   426,   427,   428,   429,   430,   431,   432,
     433,   434,   435,   436,   437,   438,   439,   440,   441,   442,
     443,   444,   445
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if YYDEBUG || 0
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "SCONST", "IDENT",
  "UCONST", "RECPTR", "K_BASE_BACKUP", "K_IDENTIFY_SYSTEM",
  "K_READ_REPLICATION_SLOT", "K_SHOW", "K_START_REPLICATION",
  "K_CREATE_REPLICATION_SLOT", "K_DROP_REPLICATION_SLOT",
  "K_ALTER_REPLICATION_SLOT", "K_TIMELINE_HISTORY", "K_WAIT", "K_TIMELINE",
  "K_PHYSICAL", "K_LOGICAL", "K_SLOT", "K_RESERVE_WAL", "K_TEMPORARY",
  "K_TWO_PHASE", "K_EXPORT_SNAPSHOT", "K_NOEXPORT_SNAPSHOT",
  "K_USE_SNAPSHOT", "K_UPLOAD_MANIFEST", "';'", "'.'", "'('", "')'", "','",
  "$accept", "firstcmd", "opt_semicolon", "command", "identify_system",
  "read_replication_slot", "show", "var_name", "base_backup",
  "create_replication_slot", "create_slot_options",
  "create_slot_legacy_opt_list", "create_slot_legacy_opt",
  "drop_replication_slot", "alter_replication_slot", "start_replication",
  "start_logical_replication", "timeline_history", "upload_manifest",
  "opt_physical", "opt_temporary", "opt_slot", "opt_timeline",
  "plugin_options", "plugin_opt_list", "plugin_opt_elem", "plugin_opt_arg",
  "generic_option_list", "generic_option", "ident_or_keyword", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-36)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-1)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int8 yypact[] =
{
      17,   -25,   -36,    31,    31,    23,    50,    51,    52,    53,
     -36,    57,    32,   -36,   -36,   -36,   -36,   -36,   -36,   -36,
     -36,   -36,   -36,   -36,    -4,   -36,    30,    30,    58,    43,
      41,    48,    35,   -36,   -36,   -36,   -36,   -36,   -36,   -36,
     -36,   -36,   -36,   -36,   -36,   -36,   -36,   -36,   -36,   -36,
     -36,   -36,   -36,   -36,   -36,   -36,   -36,   -36,   -30,   -36,
      37,    62,    49,   -36,    61,   -36,    27,   -36,    -4,   -36,
      -4,   -36,   -36,   -36,   -36,    63,    54,    40,    68,    16,
     -36,    44,    70,   -36,    -4,   -36,    13,    40,   -36,    69,
     -36,   -36,    19,   -36,   -36,   -36,   -36,   -36,   -36,   -36,
      73,    21,   -36,   -36,   -36,   -36,   -36,    69,   -36
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       0,    22,    16,     0,     0,    46,     0,     0,     0,     0,
      40,     0,     4,     5,    12,    14,     6,     9,    10,    11,
       7,     8,    13,    15,     0,    19,    17,    18,     0,    42,
      44,    34,     0,    39,     1,     3,     2,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,     0,    57,
      58,     0,    45,    41,     0,    43,     0,    35,     0,    21,
       0,    60,    59,    61,    20,     0,    48,    28,     0,     0,
      56,    50,     0,    37,     0,    23,    26,    28,    36,     0,
      38,    47,     0,    32,    33,    29,    30,    31,    27,    24,
      55,     0,    51,    25,    54,    53,    49,     0,    52
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] =
{
     -36,   -36,   -36,   -36,   -36,   -36,   -36,    74,   -36,   -36,
     -10,   -36,   -36,   -36,   -36,   -36,   -36,   -36,   -36,   -36,
     -36,   -36,   -36,   -36,   -36,   -28,   -36,   -35,    10,   -36
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] =
{
       0,    11,    36,    12,    13,    14,    15,    26,    16,    17,
      85,    86,    98,    18,    19,    20,    21,    22,    23,    64,
      66,    29,    83,    90,   101,   102,   105,    58,    59,    60
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int8 yytable[] =
{
      37,    69,    70,    38,    39,    24,    40,    41,    42,    43,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,     1,     2,     3,     4,     5,     6,
       7,     8,     9,    79,    93,    25,    94,    95,    96,    97,
      71,    72,    73,    28,    10,    77,    78,    88,    70,    92,
     103,    70,   106,   107,    30,    31,    32,    34,    33,    61,
      35,    63,    62,    65,    67,    68,    74,    76,    75,    81,
      84,    82,    87,   100,    89,    91,   104,    99,    27,   108,
      80
};

static const yytype_int8 yycheck[] =
{
       4,    31,    32,     7,     8,    30,    10,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    68,    21,     4,    23,    24,    25,    26,
       3,     4,     5,    20,    27,    18,    19,    31,    32,    84,
      31,    32,    31,    32,     4,     4,     4,     0,     5,    29,
      28,    18,     4,    22,    16,    30,     4,     6,    19,     6,
      30,    17,     4,     4,    30,     5,     3,    87,     4,   107,
      70
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      27,    34,    36,    37,    38,    39,    41,    42,    46,    47,
      48,    49,    50,    51,    30,     4,    40,    40,    20,    54,
       4,     4,     4,     5,     0,    28,    35,     4,     7,     8,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,    25,    26,    27,    60,    61,
      62,    29,     4,    18,    52,    22,    53,    16,    30,    31,
      32,     3,     4,     5,     4,    19,     6,    18,    19,    60,
      61,     6,    17,    55,    30,    43,    44,     4,    31,    30,
      56,     5,    60,    21,    23,    24,    25,    26,    45,    43,
       4,    57,    58,    31,     3,    59,    31,    32,    58
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr1[] =
{
       0,    33,    34,    35,    35,    36,    36,    36,    36,    36,
      36,    36,    36,    36,    36,    36,    37,    38,    39,    40,
      40,    41,    41,    42,    42,    43,    43,    44,    44,    45,
      45,    45,    45,    45,    46,    46,    47,    48,    49,    50,
      51,    52,    52,    53,    53,    54,    54,    55,    55,    56,
      56,    57,    57,    58,    59,    59,    60,    60,    61,    61,
      61,    61,    62,    62,    62,    62,    62,    62,    62,    62,
      62,    62,    62,    62,    62,    62,    62,    62,    62,    62,
      62,    62,    62
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     2,     1,     0,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     2,     2,     1,
       3,     4,     1,     5,     6,     3,     1,     2,     0,     1,
       1,     1,     1,     1,     2,     3,     5,     5,     6,     2,
       1,     1,     0,     1,     0,     2,     0,     2,     0,     3,
       0,     1,     3,     2,     1,     0,     3,     1,     1,     2,
       2,     2,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (replication_parse_result_p, yyscanner, YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)




# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value, replication_parse_result_p, yyscanner); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, Node **replication_parse_result_p, yyscan_t yyscanner)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  YY_USE (replication_parse_result_p);
  YY_USE (yyscanner);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, Node **replication_parse_result_p, yyscan_t yyscanner)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  yy_symbol_value_print (yyo, yykind, yyvaluep, replication_parse_result_p, yyscanner);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp,
                 int yyrule, Node **replication_parse_result_p, yyscan_t yyscanner)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)], replication_parse_result_p, yyscanner);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule, replication_parse_result_p, yyscanner); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif






/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep, Node **replication_parse_result_p, yyscan_t yyscanner)
{
  YY_USE (yyvaluep);
  YY_USE (replication_parse_result_p);
  YY_USE (yyscanner);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}






/*----------.
| yyparse.  |
`----------*/

int
yyparse (Node **replication_parse_result_p, yyscan_t yyscanner)
{
/* Lookahead token kind.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

    /* Number of syntax errors so far.  */
    int yynerrs = 0;

    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex (&yylval, yyscanner);
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 2: /* firstcmd: command opt_semicolon  */
#line 103 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					*replication_parse_result_p = (yyvsp[-1].node);

					(void) yynerrs; /* suppress compiler warning */
				}
#line 1254 "repl_gram.c"
    break;

  case 16: /* identify_system: K_IDENTIFY_SYSTEM  */
#line 133 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					(yyval.node) = (Node *) makeNode(IdentifySystemCmd);
				}
#line 1262 "repl_gram.c"
    break;

  case 17: /* read_replication_slot: K_READ_REPLICATION_SLOT var_name  */
#line 143 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					ReadReplicationSlotCmd *n = makeNode(ReadReplicationSlotCmd);
					n->slotname = (yyvsp[0].str);
					(yyval.node) = (Node *) n;
				}
#line 1272 "repl_gram.c"
    break;

  case 18: /* show: K_SHOW var_name  */
#line 155 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					VariableShowStmt *n = makeNode(VariableShowStmt);
					n->name = (yyvsp[0].str);
					(yyval.node) = (Node *) n;
				}
#line 1282 "repl_gram.c"
    break;

  case 19: /* var_name: IDENT  */
#line 161 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                        { (yyval.str) = (yyvsp[0].str); }
#line 1288 "repl_gram.c"
    break;

  case 20: /* var_name: var_name '.' IDENT  */
#line 163 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                { (yyval.str) = psprintf("%s.%s", (yyvsp[-2].str), (yyvsp[0].str)); }
#line 1294 "repl_gram.c"
    break;

  case 21: /* base_backup: K_BASE_BACKUP '(' generic_option_list ')'  */
#line 171 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					BaseBackupCmd *cmd = makeNode(BaseBackupCmd);
					cmd->options = (yyvsp[-1].list);
					(yyval.node) = (Node *) cmd;
				}
#line 1304 "repl_gram.c"
    break;

  case 22: /* base_backup: K_BASE_BACKUP  */
#line 177 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					BaseBackupCmd *cmd = makeNode(BaseBackupCmd);
					(yyval.node) = (Node *) cmd;
				}
#line 1313 "repl_gram.c"
    break;

  case 23: /* create_replication_slot: K_CREATE_REPLICATION_SLOT IDENT opt_temporary K_PHYSICAL create_slot_options  */
#line 186 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					CreateReplicationSlotCmd *cmd;
					cmd = makeNode(CreateReplicationSlotCmd);
					cmd->kind = REPLICATION_KIND_PHYSICAL;
					cmd->slotname = (yyvsp[-3].str);
					cmd->temporary = (yyvsp[-2].boolval);
					cmd->options = (yyvsp[0].list);
					(yyval.node) = (Node *) cmd;
				}
#line 1327 "repl_gram.c"
    break;

  case 24: /* create_replication_slot: K_CREATE_REPLICATION_SLOT IDENT opt_temporary K_LOGICAL IDENT create_slot_options  */
#line 197 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					CreateReplicationSlotCmd *cmd;
					cmd = makeNode(CreateReplicationSlotCmd);
					cmd->kind = REPLICATION_KIND_LOGICAL;
					cmd->slotname = (yyvsp[-4].str);
					cmd->temporary = (yyvsp[-3].boolval);
					cmd->plugin = (yyvsp[-1].str);
					cmd->options = (yyvsp[0].list);
					(yyval.node) = (Node *) cmd;
				}
#line 1342 "repl_gram.c"
    break;

  case 25: /* create_slot_options: '(' generic_option_list ')'  */
#line 210 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.list) = (yyvsp[-1].list); }
#line 1348 "repl_gram.c"
    break;

  case 26: /* create_slot_options: create_slot_legacy_opt_list  */
#line 211 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                { (yyval.list) = (yyvsp[0].list); }
#line 1354 "repl_gram.c"
    break;

  case 27: /* create_slot_legacy_opt_list: create_slot_legacy_opt_list create_slot_legacy_opt  */
#line 216 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                { (yyval.list) = lappend((yyvsp[-1].list), (yyvsp[0].defelt)); }
#line 1360 "repl_gram.c"
    break;

  case 28: /* create_slot_legacy_opt_list: %empty  */
#line 218 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                { (yyval.list) = NIL; }
#line 1366 "repl_gram.c"
    break;

  case 29: /* create_slot_legacy_opt: K_EXPORT_SNAPSHOT  */
#line 223 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
				  (yyval.defelt) = makeDefElem("snapshot",
								   (Node *) makeString("export"), -1);
				}
#line 1375 "repl_gram.c"
    break;

  case 30: /* create_slot_legacy_opt: K_NOEXPORT_SNAPSHOT  */
#line 228 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
				  (yyval.defelt) = makeDefElem("snapshot",
								   (Node *) makeString("nothing"), -1);
				}
#line 1384 "repl_gram.c"
    break;

  case 31: /* create_slot_legacy_opt: K_USE_SNAPSHOT  */
#line 233 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
				  (yyval.defelt) = makeDefElem("snapshot",
								   (Node *) makeString("use"), -1);
				}
#line 1393 "repl_gram.c"
    break;

  case 32: /* create_slot_legacy_opt: K_RESERVE_WAL  */
#line 238 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
				  (yyval.defelt) = makeDefElem("reserve_wal",
								   (Node *) makeBoolean(true), -1);
				}
#line 1402 "repl_gram.c"
    break;

  case 33: /* create_slot_legacy_opt: K_TWO_PHASE  */
#line 243 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
				  (yyval.defelt) = makeDefElem("two_phase",
								   (Node *) makeBoolean(true), -1);
				}
#line 1411 "repl_gram.c"
    break;

  case 34: /* drop_replication_slot: K_DROP_REPLICATION_SLOT IDENT  */
#line 252 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					DropReplicationSlotCmd *cmd;
					cmd = makeNode(DropReplicationSlotCmd);
					cmd->slotname = (yyvsp[0].str);
					cmd->wait = false;
					(yyval.node) = (Node *) cmd;
				}
#line 1423 "repl_gram.c"
    break;

  case 35: /* drop_replication_slot: K_DROP_REPLICATION_SLOT IDENT K_WAIT  */
#line 260 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					DropReplicationSlotCmd *cmd;
					cmd = makeNode(DropReplicationSlotCmd);
					cmd->slotname = (yyvsp[-1].str);
					cmd->wait = true;
					(yyval.node) = (Node *) cmd;
				}
#line 1435 "repl_gram.c"
    break;

  case 36: /* alter_replication_slot: K_ALTER_REPLICATION_SLOT IDENT '(' generic_option_list ')'  */
#line 272 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					AlterReplicationSlotCmd *cmd;
					cmd = makeNode(AlterReplicationSlotCmd);
					cmd->slotname = (yyvsp[-3].str);
					cmd->options = (yyvsp[-1].list);
					(yyval.node) = (Node *) cmd;
				}
#line 1447 "repl_gram.c"
    break;

  case 37: /* start_replication: K_START_REPLICATION opt_slot opt_physical RECPTR opt_timeline  */
#line 286 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					StartReplicationCmd *cmd;

					cmd = makeNode(StartReplicationCmd);
					cmd->kind = REPLICATION_KIND_PHYSICAL;
					cmd->slotname = (yyvsp[-3].str);
					cmd->startpoint = (yyvsp[-1].recptr);
					cmd->timeline = (yyvsp[0].uintval);
					(yyval.node) = (Node *) cmd;
				}
#line 1462 "repl_gram.c"
    break;

  case 38: /* start_logical_replication: K_START_REPLICATION K_SLOT IDENT K_LOGICAL RECPTR plugin_options  */
#line 301 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					StartReplicationCmd *cmd;
					cmd = makeNode(StartReplicationCmd);
					cmd->kind = REPLICATION_KIND_LOGICAL;
					cmd->slotname = (yyvsp[-3].str);
					cmd->startpoint = (yyvsp[-1].recptr);
					cmd->options = (yyvsp[0].list);
					(yyval.node) = (Node *) cmd;
				}
#line 1476 "repl_gram.c"
    break;

  case 39: /* timeline_history: K_TIMELINE_HISTORY UCONST  */
#line 316 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					TimeLineHistoryCmd *cmd;

					if ((yyvsp[0].uintval) <= 0)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("invalid timeline %u", (yyvsp[0].uintval))));

					cmd = makeNode(TimeLineHistoryCmd);
					cmd->timeline = (yyvsp[0].uintval);

					(yyval.node) = (Node *) cmd;
				}
#line 1494 "repl_gram.c"
    break;

  case 40: /* upload_manifest: K_UPLOAD_MANIFEST  */
#line 334 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					UploadManifestCmd *cmd = makeNode(UploadManifestCmd);

					(yyval.node) = (Node *) cmd;
				}
#line 1504 "repl_gram.c"
    break;

  case 43: /* opt_temporary: K_TEMPORARY  */
#line 346 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                                { (yyval.boolval) = true; }
#line 1510 "repl_gram.c"
    break;

  case 44: /* opt_temporary: %empty  */
#line 347 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.boolval) = false; }
#line 1516 "repl_gram.c"
    break;

  case 45: /* opt_slot: K_SLOT IDENT  */
#line 352 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                { (yyval.str) = (yyvsp[0].str); }
#line 1522 "repl_gram.c"
    break;

  case 46: /* opt_slot: %empty  */
#line 354 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                { (yyval.str) = NULL; }
#line 1528 "repl_gram.c"
    break;

  case 47: /* opt_timeline: K_TIMELINE UCONST  */
#line 359 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					if ((yyvsp[0].uintval) <= 0)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("invalid timeline %u", (yyvsp[0].uintval))));
					(yyval.uintval) = (yyvsp[0].uintval);
				}
#line 1540 "repl_gram.c"
    break;

  case 48: /* opt_timeline: %empty  */
#line 366 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                { (yyval.uintval) = 0; }
#line 1546 "repl_gram.c"
    break;

  case 49: /* plugin_options: '(' plugin_opt_list ')'  */
#line 371 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                { (yyval.list) = (yyvsp[-1].list); }
#line 1552 "repl_gram.c"
    break;

  case 50: /* plugin_options: %empty  */
#line 372 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.list) = NIL; }
#line 1558 "repl_gram.c"
    break;

  case 51: /* plugin_opt_list: plugin_opt_elem  */
#line 377 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					(yyval.list) = list_make1((yyvsp[0].defelt));
				}
#line 1566 "repl_gram.c"
    break;

  case 52: /* plugin_opt_list: plugin_opt_list ',' plugin_opt_elem  */
#line 381 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					(yyval.list) = lappend((yyvsp[-2].list), (yyvsp[0].defelt));
				}
#line 1574 "repl_gram.c"
    break;

  case 53: /* plugin_opt_elem: IDENT plugin_opt_arg  */
#line 388 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					(yyval.defelt) = makeDefElem((yyvsp[-1].str), (yyvsp[0].node), -1);
				}
#line 1582 "repl_gram.c"
    break;

  case 54: /* plugin_opt_arg: SCONST  */
#line 394 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                                { (yyval.node) = (Node *) makeString((yyvsp[0].str)); }
#line 1588 "repl_gram.c"
    break;

  case 55: /* plugin_opt_arg: %empty  */
#line 395 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.node) = NULL; }
#line 1594 "repl_gram.c"
    break;

  case 56: /* generic_option_list: generic_option_list ',' generic_option  */
#line 400 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                { (yyval.list) = lappend((yyvsp[-2].list), (yyvsp[0].defelt)); }
#line 1600 "repl_gram.c"
    break;

  case 57: /* generic_option_list: generic_option  */
#line 402 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                { (yyval.list) = list_make1((yyvsp[0].defelt)); }
#line 1606 "repl_gram.c"
    break;

  case 58: /* generic_option: ident_or_keyword  */
#line 407 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					(yyval.defelt) = makeDefElem((yyvsp[0].str), NULL, -1);
				}
#line 1614 "repl_gram.c"
    break;

  case 59: /* generic_option: ident_or_keyword IDENT  */
#line 411 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					(yyval.defelt) = makeDefElem((yyvsp[-1].str), (Node *) makeString((yyvsp[0].str)), -1);
				}
#line 1622 "repl_gram.c"
    break;

  case 60: /* generic_option: ident_or_keyword SCONST  */
#line 415 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					(yyval.defelt) = makeDefElem((yyvsp[-1].str), (Node *) makeString((yyvsp[0].str)), -1);
				}
#line 1630 "repl_gram.c"
    break;

  case 61: /* generic_option: ident_or_keyword UCONST  */
#line 419 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                {
					(yyval.defelt) = makeDefElem((yyvsp[-1].str), (Node *) makeInteger((yyvsp[0].uintval)), -1);
				}
#line 1638 "repl_gram.c"
    break;

  case 62: /* ident_or_keyword: IDENT  */
#line 425 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                                { (yyval.str) = (yyvsp[0].str); }
#line 1644 "repl_gram.c"
    break;

  case 63: /* ident_or_keyword: K_BASE_BACKUP  */
#line 426 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "base_backup"; }
#line 1650 "repl_gram.c"
    break;

  case 64: /* ident_or_keyword: K_IDENTIFY_SYSTEM  */
#line 427 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "identify_system"; }
#line 1656 "repl_gram.c"
    break;

  case 65: /* ident_or_keyword: K_SHOW  */
#line 428 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                                { (yyval.str) = "show"; }
#line 1662 "repl_gram.c"
    break;

  case 66: /* ident_or_keyword: K_START_REPLICATION  */
#line 429 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                { (yyval.str) = "start_replication"; }
#line 1668 "repl_gram.c"
    break;

  case 67: /* ident_or_keyword: K_CREATE_REPLICATION_SLOT  */
#line 430 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                        { (yyval.str) = "create_replication_slot"; }
#line 1674 "repl_gram.c"
    break;

  case 68: /* ident_or_keyword: K_DROP_REPLICATION_SLOT  */
#line 431 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                { (yyval.str) = "drop_replication_slot"; }
#line 1680 "repl_gram.c"
    break;

  case 69: /* ident_or_keyword: K_ALTER_REPLICATION_SLOT  */
#line 432 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                { (yyval.str) = "alter_replication_slot"; }
#line 1686 "repl_gram.c"
    break;

  case 70: /* ident_or_keyword: K_TIMELINE_HISTORY  */
#line 433 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                { (yyval.str) = "timeline_history"; }
#line 1692 "repl_gram.c"
    break;

  case 71: /* ident_or_keyword: K_WAIT  */
#line 434 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                                { (yyval.str) = "wait"; }
#line 1698 "repl_gram.c"
    break;

  case 72: /* ident_or_keyword: K_TIMELINE  */
#line 435 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "timeline"; }
#line 1704 "repl_gram.c"
    break;

  case 73: /* ident_or_keyword: K_PHYSICAL  */
#line 436 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "physical"; }
#line 1710 "repl_gram.c"
    break;

  case 74: /* ident_or_keyword: K_LOGICAL  */
#line 437 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                                { (yyval.str) = "logical"; }
#line 1716 "repl_gram.c"
    break;

  case 75: /* ident_or_keyword: K_SLOT  */
#line 438 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                                { (yyval.str) = "slot"; }
#line 1722 "repl_gram.c"
    break;

  case 76: /* ident_or_keyword: K_RESERVE_WAL  */
#line 439 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "reserve_wal"; }
#line 1728 "repl_gram.c"
    break;

  case 77: /* ident_or_keyword: K_TEMPORARY  */
#line 440 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "temporary"; }
#line 1734 "repl_gram.c"
    break;

  case 78: /* ident_or_keyword: K_TWO_PHASE  */
#line 441 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "two_phase"; }
#line 1740 "repl_gram.c"
    break;

  case 79: /* ident_or_keyword: K_EXPORT_SNAPSHOT  */
#line 442 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "export_snapshot"; }
#line 1746 "repl_gram.c"
    break;

  case 80: /* ident_or_keyword: K_NOEXPORT_SNAPSHOT  */
#line 443 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                { (yyval.str) = "noexport_snapshot"; }
#line 1752 "repl_gram.c"
    break;

  case 81: /* ident_or_keyword: K_USE_SNAPSHOT  */
#line 444 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "use_snapshot"; }
#line 1758 "repl_gram.c"
    break;

  case 82: /* ident_or_keyword: K_UPLOAD_MANIFEST  */
#line 445 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"
                                                                        { (yyval.str) = "upload_manifest"; }
#line 1764 "repl_gram.c"
    break;


#line 1768 "repl_gram.c"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      yyerror (replication_parse_result_p, yyscanner, YY_("syntax error"));
    }

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, replication_parse_result_p, yyscanner);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp, replication_parse_result_p, yyscanner);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (replication_parse_result_p, yyscanner, YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, replication_parse_result_p, yyscanner);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp, replication_parse_result_p, yyscanner);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif

  return yyresult;
}

#line 448 "/home/postgres/Learn-PG/build/../src/backend/replication/repl_gram.y"

