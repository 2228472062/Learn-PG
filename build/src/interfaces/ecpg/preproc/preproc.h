/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

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

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_BASE_YY_PREPROC_H_INCLUDED
# define YY_BASE_YY_PREPROC_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int base_yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    SQL_ALLOCATE = 258,            /* SQL_ALLOCATE  */
    SQL_AUTOCOMMIT = 259,          /* SQL_AUTOCOMMIT  */
    SQL_BOOL = 260,                /* SQL_BOOL  */
    SQL_BREAK = 261,               /* SQL_BREAK  */
    SQL_CARDINALITY = 262,         /* SQL_CARDINALITY  */
    SQL_CONNECT = 263,             /* SQL_CONNECT  */
    SQL_COUNT = 264,               /* SQL_COUNT  */
    SQL_DATETIME_INTERVAL_CODE = 265, /* SQL_DATETIME_INTERVAL_CODE  */
    SQL_DATETIME_INTERVAL_PRECISION = 266, /* SQL_DATETIME_INTERVAL_PRECISION  */
    SQL_DESCRIBE = 267,            /* SQL_DESCRIBE  */
    SQL_DESCRIPTOR = 268,          /* SQL_DESCRIPTOR  */
    SQL_DISCONNECT = 269,          /* SQL_DISCONNECT  */
    SQL_FOUND = 270,               /* SQL_FOUND  */
    SQL_FREE = 271,                /* SQL_FREE  */
    SQL_GET = 272,                 /* SQL_GET  */
    SQL_GO = 273,                  /* SQL_GO  */
    SQL_GOTO = 274,                /* SQL_GOTO  */
    SQL_IDENTIFIED = 275,          /* SQL_IDENTIFIED  */
    SQL_INDICATOR = 276,           /* SQL_INDICATOR  */
    SQL_KEY_MEMBER = 277,          /* SQL_KEY_MEMBER  */
    SQL_LENGTH = 278,              /* SQL_LENGTH  */
    SQL_LONG = 279,                /* SQL_LONG  */
    SQL_NULLABLE = 280,            /* SQL_NULLABLE  */
    SQL_OCTET_LENGTH = 281,        /* SQL_OCTET_LENGTH  */
    SQL_OPEN = 282,                /* SQL_OPEN  */
    SQL_OUTPUT = 283,              /* SQL_OUTPUT  */
    SQL_REFERENCE = 284,           /* SQL_REFERENCE  */
    SQL_RETURNED_LENGTH = 285,     /* SQL_RETURNED_LENGTH  */
    SQL_RETURNED_OCTET_LENGTH = 286, /* SQL_RETURNED_OCTET_LENGTH  */
    SQL_SCALE = 287,               /* SQL_SCALE  */
    SQL_SECTION = 288,             /* SQL_SECTION  */
    SQL_SHORT = 289,               /* SQL_SHORT  */
    SQL_SIGNED = 290,              /* SQL_SIGNED  */
    SQL_SQLERROR = 291,            /* SQL_SQLERROR  */
    SQL_SQLPRINT = 292,            /* SQL_SQLPRINT  */
    SQL_SQLWARNING = 293,          /* SQL_SQLWARNING  */
    SQL_START = 294,               /* SQL_START  */
    SQL_STOP = 295,                /* SQL_STOP  */
    SQL_STRUCT = 296,              /* SQL_STRUCT  */
    SQL_UNSIGNED = 297,            /* SQL_UNSIGNED  */
    SQL_VAR = 298,                 /* SQL_VAR  */
    SQL_WHENEVER = 299,            /* SQL_WHENEVER  */
    S_ADD = 300,                   /* S_ADD  */
    S_AND = 301,                   /* S_AND  */
    S_ANYTHING = 302,              /* S_ANYTHING  */
    S_AUTO = 303,                  /* S_AUTO  */
    S_CONST = 304,                 /* S_CONST  */
    S_DEC = 305,                   /* S_DEC  */
    S_DIV = 306,                   /* S_DIV  */
    S_DOTPOINT = 307,              /* S_DOTPOINT  */
    S_EQUAL = 308,                 /* S_EQUAL  */
    S_EXTERN = 309,                /* S_EXTERN  */
    S_INC = 310,                   /* S_INC  */
    S_LSHIFT = 311,                /* S_LSHIFT  */
    S_MEMPOINT = 312,              /* S_MEMPOINT  */
    S_MEMBER = 313,                /* S_MEMBER  */
    S_MOD = 314,                   /* S_MOD  */
    S_MUL = 315,                   /* S_MUL  */
    S_NEQUAL = 316,                /* S_NEQUAL  */
    S_OR = 317,                    /* S_OR  */
    S_REGISTER = 318,              /* S_REGISTER  */
    S_RSHIFT = 319,                /* S_RSHIFT  */
    S_STATIC = 320,                /* S_STATIC  */
    S_SUB = 321,                   /* S_SUB  */
    S_VOLATILE = 322,              /* S_VOLATILE  */
    S_TYPEDEF = 323,               /* S_TYPEDEF  */
    CSTRING = 324,                 /* CSTRING  */
    CVARIABLE = 325,               /* CVARIABLE  */
    CPP_LINE = 326,                /* CPP_LINE  */
    IP = 327,                      /* IP  */
    IDENT = 328,                   /* IDENT  */
    UIDENT = 329,                  /* UIDENT  */
    FCONST = 330,                  /* FCONST  */
    SCONST = 331,                  /* SCONST  */
    USCONST = 332,                 /* USCONST  */
    BCONST = 333,                  /* BCONST  */
    XCONST = 334,                  /* XCONST  */
    Op = 335,                      /* Op  */
    ICONST = 336,                  /* ICONST  */
    PARAM = 337,                   /* PARAM  */
    TYPECAST = 338,                /* TYPECAST  */
    DOT_DOT = 339,                 /* DOT_DOT  */
    COLON_EQUALS = 340,            /* COLON_EQUALS  */
    EQUALS_GREATER = 341,          /* EQUALS_GREATER  */
    LESS_EQUALS = 342,             /* LESS_EQUALS  */
    GREATER_EQUALS = 343,          /* GREATER_EQUALS  */
    NOT_EQUALS = 344,              /* NOT_EQUALS  */
    ABORT_P = 345,                 /* ABORT_P  */
    ABSENT = 346,                  /* ABSENT  */
    ABSOLUTE_P = 347,              /* ABSOLUTE_P  */
    ACCESS = 348,                  /* ACCESS  */
    ACTION = 349,                  /* ACTION  */
    ADD_P = 350,                   /* ADD_P  */
    ADMIN = 351,                   /* ADMIN  */
    AFTER = 352,                   /* AFTER  */
    AGGREGATE = 353,               /* AGGREGATE  */
    ALL = 354,                     /* ALL  */
    ALSO = 355,                    /* ALSO  */
    ALTER = 356,                   /* ALTER  */
    ALWAYS = 357,                  /* ALWAYS  */
    ANALYSE = 358,                 /* ANALYSE  */
    ANALYZE = 359,                 /* ANALYZE  */
    AND = 360,                     /* AND  */
    ANY = 361,                     /* ANY  */
    ARRAY = 362,                   /* ARRAY  */
    AS = 363,                      /* AS  */
    ASC = 364,                     /* ASC  */
    ASENSITIVE = 365,              /* ASENSITIVE  */
    ASSERTION = 366,               /* ASSERTION  */
    ASSIGNMENT = 367,              /* ASSIGNMENT  */
    ASYMMETRIC = 368,              /* ASYMMETRIC  */
    ATOMIC = 369,                  /* ATOMIC  */
    AT = 370,                      /* AT  */
    ATTACH = 371,                  /* ATTACH  */
    ATTRIBUTE = 372,               /* ATTRIBUTE  */
    AUTHORIZATION = 373,           /* AUTHORIZATION  */
    BACKWARD = 374,                /* BACKWARD  */
    BEFORE = 375,                  /* BEFORE  */
    BEGIN_P = 376,                 /* BEGIN_P  */
    BETWEEN = 377,                 /* BETWEEN  */
    BIGINT = 378,                  /* BIGINT  */
    BINARY = 379,                  /* BINARY  */
    BIT = 380,                     /* BIT  */
    BOOLEAN_P = 381,               /* BOOLEAN_P  */
    BOTH = 382,                    /* BOTH  */
    BREADTH = 383,                 /* BREADTH  */
    BY = 384,                      /* BY  */
    CACHE = 385,                   /* CACHE  */
    CALL = 386,                    /* CALL  */
    CALLED = 387,                  /* CALLED  */
    CASCADE = 388,                 /* CASCADE  */
    CASCADED = 389,                /* CASCADED  */
    CASE = 390,                    /* CASE  */
    CAST = 391,                    /* CAST  */
    CATALOG_P = 392,               /* CATALOG_P  */
    CHAIN = 393,                   /* CHAIN  */
    CHAR_P = 394,                  /* CHAR_P  */
    CHARACTER = 395,               /* CHARACTER  */
    CHARACTERISTICS = 396,         /* CHARACTERISTICS  */
    CHECK = 397,                   /* CHECK  */
    CHECKPOINT = 398,              /* CHECKPOINT  */
    CLASS = 399,                   /* CLASS  */
    CLOSE = 400,                   /* CLOSE  */
    CLUSTER = 401,                 /* CLUSTER  */
    COALESCE = 402,                /* COALESCE  */
    COLLATE = 403,                 /* COLLATE  */
    COLLATION = 404,               /* COLLATION  */
    COLUMN = 405,                  /* COLUMN  */
    COLUMNS = 406,                 /* COLUMNS  */
    COMMENT = 407,                 /* COMMENT  */
    COMMENTS = 408,                /* COMMENTS  */
    COMMIT = 409,                  /* COMMIT  */
    COMMITTED = 410,               /* COMMITTED  */
    COMPRESSION = 411,             /* COMPRESSION  */
    CONCURRENTLY = 412,            /* CONCURRENTLY  */
    CONDITIONAL = 413,             /* CONDITIONAL  */
    CONFIGURATION = 414,           /* CONFIGURATION  */
    CONFLICT = 415,                /* CONFLICT  */
    CONNECTION = 416,              /* CONNECTION  */
    CONSTRAINT = 417,              /* CONSTRAINT  */
    CONSTRAINTS = 418,             /* CONSTRAINTS  */
    CONTENT_P = 419,               /* CONTENT_P  */
    CONTINUE_P = 420,              /* CONTINUE_P  */
    CONVERSION_P = 421,            /* CONVERSION_P  */
    COPY = 422,                    /* COPY  */
    COST = 423,                    /* COST  */
    CREATE = 424,                  /* CREATE  */
    CROSS = 425,                   /* CROSS  */
    CSV = 426,                     /* CSV  */
    CUBE = 427,                    /* CUBE  */
    CURRENT_P = 428,               /* CURRENT_P  */
    CURRENT_CATALOG = 429,         /* CURRENT_CATALOG  */
    CURRENT_DATE = 430,            /* CURRENT_DATE  */
    CURRENT_ROLE = 431,            /* CURRENT_ROLE  */
    CURRENT_SCHEMA = 432,          /* CURRENT_SCHEMA  */
    CURRENT_TIME = 433,            /* CURRENT_TIME  */
    CURRENT_TIMESTAMP = 434,       /* CURRENT_TIMESTAMP  */
    CURRENT_USER = 435,            /* CURRENT_USER  */
    CURSOR = 436,                  /* CURSOR  */
    CYCLE = 437,                   /* CYCLE  */
    DATA_P = 438,                  /* DATA_P  */
    DATABASE = 439,                /* DATABASE  */
    DAY_P = 440,                   /* DAY_P  */
    DEALLOCATE = 441,              /* DEALLOCATE  */
    DEC = 442,                     /* DEC  */
    DECIMAL_P = 443,               /* DECIMAL_P  */
    DECLARE = 444,                 /* DECLARE  */
    DEFAULT = 445,                 /* DEFAULT  */
    DEFAULTS = 446,                /* DEFAULTS  */
    DEFERRABLE = 447,              /* DEFERRABLE  */
    DEFERRED = 448,                /* DEFERRED  */
    DEFINER = 449,                 /* DEFINER  */
    DELETE_P = 450,                /* DELETE_P  */
    DELIMITER = 451,               /* DELIMITER  */
    DELIMITERS = 452,              /* DELIMITERS  */
    DEPENDS = 453,                 /* DEPENDS  */
    DEPTH = 454,                   /* DEPTH  */
    DESC = 455,                    /* DESC  */
    DESTINATION = 456,             /* DESTINATION  */
    DETACH = 457,                  /* DETACH  */
    DICTIONARY = 458,              /* DICTIONARY  */
    DISABLE_P = 459,               /* DISABLE_P  */
    DISCARD = 460,                 /* DISCARD  */
    DISTINCT = 461,                /* DISTINCT  */
    DO = 462,                      /* DO  */
    DOCUMENT_P = 463,              /* DOCUMENT_P  */
    DOMAIN_P = 464,                /* DOMAIN_P  */
    DOUBLE_P = 465,                /* DOUBLE_P  */
    DROP = 466,                    /* DROP  */
    EACH = 467,                    /* EACH  */
    EDGE = 468,                    /* EDGE  */
    ELSE = 469,                    /* ELSE  */
    EMPTY_P = 470,                 /* EMPTY_P  */
    ENABLE_P = 471,                /* ENABLE_P  */
    ENCODING = 472,                /* ENCODING  */
    ENCRYPTED = 473,               /* ENCRYPTED  */
    END_P = 474,                   /* END_P  */
    ENFORCED = 475,                /* ENFORCED  */
    ENUM_P = 476,                  /* ENUM_P  */
    ERROR_P = 477,                 /* ERROR_P  */
    ESCAPE = 478,                  /* ESCAPE  */
    EVENT = 479,                   /* EVENT  */
    EXCEPT = 480,                  /* EXCEPT  */
    EXCLUDE = 481,                 /* EXCLUDE  */
    EXCLUDING = 482,               /* EXCLUDING  */
    EXCLUSIVE = 483,               /* EXCLUSIVE  */
    EXECUTE = 484,                 /* EXECUTE  */
    EXISTS = 485,                  /* EXISTS  */
    EXPLAIN = 486,                 /* EXPLAIN  */
    EXPRESSION = 487,              /* EXPRESSION  */
    EXTENSION = 488,               /* EXTENSION  */
    EXTERNAL = 489,                /* EXTERNAL  */
    EXTRACT = 490,                 /* EXTRACT  */
    FALSE_P = 491,                 /* FALSE_P  */
    FAMILY = 492,                  /* FAMILY  */
    FETCH = 493,                   /* FETCH  */
    FILTER = 494,                  /* FILTER  */
    FINALIZE = 495,                /* FINALIZE  */
    FIRST_P = 496,                 /* FIRST_P  */
    FLOAT_P = 497,                 /* FLOAT_P  */
    FOLLOWING = 498,               /* FOLLOWING  */
    FOR = 499,                     /* FOR  */
    FORCE = 500,                   /* FORCE  */
    FOREIGN = 501,                 /* FOREIGN  */
    FORMAT = 502,                  /* FORMAT  */
    FORWARD = 503,                 /* FORWARD  */
    FREEZE = 504,                  /* FREEZE  */
    FROM = 505,                    /* FROM  */
    FULL = 506,                    /* FULL  */
    FUNCTION = 507,                /* FUNCTION  */
    FUNCTIONS = 508,               /* FUNCTIONS  */
    GENERATED = 509,               /* GENERATED  */
    GLOBAL = 510,                  /* GLOBAL  */
    GRANT = 511,                   /* GRANT  */
    GRANTED = 512,                 /* GRANTED  */
    GRAPH = 513,                   /* GRAPH  */
    GRAPH_TABLE = 514,             /* GRAPH_TABLE  */
    GREATEST = 515,                /* GREATEST  */
    GROUP_P = 516,                 /* GROUP_P  */
    GROUPING = 517,                /* GROUPING  */
    GROUPS = 518,                  /* GROUPS  */
    HANDLER = 519,                 /* HANDLER  */
    HAVING = 520,                  /* HAVING  */
    HEADER_P = 521,                /* HEADER_P  */
    HOLD = 522,                    /* HOLD  */
    HOUR_P = 523,                  /* HOUR_P  */
    IDENTITY_P = 524,              /* IDENTITY_P  */
    IF_P = 525,                    /* IF_P  */
    IGNORE_P = 526,                /* IGNORE_P  */
    ILIKE = 527,                   /* ILIKE  */
    IMMEDIATE = 528,               /* IMMEDIATE  */
    IMMUTABLE = 529,               /* IMMUTABLE  */
    IMPLICIT_P = 530,              /* IMPLICIT_P  */
    IMPORT_P = 531,                /* IMPORT_P  */
    IN_P = 532,                    /* IN_P  */
    INCLUDE = 533,                 /* INCLUDE  */
    INCLUDING = 534,               /* INCLUDING  */
    INCREMENT = 535,               /* INCREMENT  */
    INDENT = 536,                  /* INDENT  */
    INDEX = 537,                   /* INDEX  */
    INDEXES = 538,                 /* INDEXES  */
    INHERIT = 539,                 /* INHERIT  */
    INHERITS = 540,                /* INHERITS  */
    INITIALLY = 541,               /* INITIALLY  */
    INLINE_P = 542,                /* INLINE_P  */
    INNER_P = 543,                 /* INNER_P  */
    INOUT = 544,                   /* INOUT  */
    INPUT_P = 545,                 /* INPUT_P  */
    INSENSITIVE = 546,             /* INSENSITIVE  */
    INSERT = 547,                  /* INSERT  */
    INSTEAD = 548,                 /* INSTEAD  */
    INT_P = 549,                   /* INT_P  */
    INTEGER = 550,                 /* INTEGER  */
    INTERSECT = 551,               /* INTERSECT  */
    INTERVAL = 552,                /* INTERVAL  */
    INTO = 553,                    /* INTO  */
    INVOKER = 554,                 /* INVOKER  */
    IS = 555,                      /* IS  */
    ISNULL = 556,                  /* ISNULL  */
    ISOLATION = 557,               /* ISOLATION  */
    JOIN = 558,                    /* JOIN  */
    JSON = 559,                    /* JSON  */
    JSON_ARRAY = 560,              /* JSON_ARRAY  */
    JSON_ARRAYAGG = 561,           /* JSON_ARRAYAGG  */
    JSON_EXISTS = 562,             /* JSON_EXISTS  */
    JSON_OBJECT = 563,             /* JSON_OBJECT  */
    JSON_OBJECTAGG = 564,          /* JSON_OBJECTAGG  */
    JSON_QUERY = 565,              /* JSON_QUERY  */
    JSON_SCALAR = 566,             /* JSON_SCALAR  */
    JSON_SERIALIZE = 567,          /* JSON_SERIALIZE  */
    JSON_TABLE = 568,              /* JSON_TABLE  */
    JSON_VALUE = 569,              /* JSON_VALUE  */
    KEEP = 570,                    /* KEEP  */
    KEY = 571,                     /* KEY  */
    KEYS = 572,                    /* KEYS  */
    LABEL = 573,                   /* LABEL  */
    LANGUAGE = 574,                /* LANGUAGE  */
    LARGE_P = 575,                 /* LARGE_P  */
    LAST_P = 576,                  /* LAST_P  */
    LATERAL_P = 577,               /* LATERAL_P  */
    LEADING = 578,                 /* LEADING  */
    LEAKPROOF = 579,               /* LEAKPROOF  */
    LEAST = 580,                   /* LEAST  */
    LEFT = 581,                    /* LEFT  */
    LEVEL = 582,                   /* LEVEL  */
    LIKE = 583,                    /* LIKE  */
    LIMIT = 584,                   /* LIMIT  */
    LISTEN = 585,                  /* LISTEN  */
    LOAD = 586,                    /* LOAD  */
    LOCAL = 587,                   /* LOCAL  */
    LOCALTIME = 588,               /* LOCALTIME  */
    LOCALTIMESTAMP = 589,          /* LOCALTIMESTAMP  */
    LOCATION = 590,                /* LOCATION  */
    LOCK_P = 591,                  /* LOCK_P  */
    LOCKED = 592,                  /* LOCKED  */
    LOGGED = 593,                  /* LOGGED  */
    LSN_P = 594,                   /* LSN_P  */
    MAPPING = 595,                 /* MAPPING  */
    MATCH = 596,                   /* MATCH  */
    MATCHED = 597,                 /* MATCHED  */
    MATERIALIZED = 598,            /* MATERIALIZED  */
    MAXVALUE = 599,                /* MAXVALUE  */
    MERGE = 600,                   /* MERGE  */
    MERGE_ACTION = 601,            /* MERGE_ACTION  */
    METHOD = 602,                  /* METHOD  */
    MINUTE_P = 603,                /* MINUTE_P  */
    MINVALUE = 604,                /* MINVALUE  */
    MODE = 605,                    /* MODE  */
    MONTH_P = 606,                 /* MONTH_P  */
    MOVE = 607,                    /* MOVE  */
    NAME_P = 608,                  /* NAME_P  */
    NAMES = 609,                   /* NAMES  */
    NATIONAL = 610,                /* NATIONAL  */
    NATURAL = 611,                 /* NATURAL  */
    NCHAR = 612,                   /* NCHAR  */
    NESTED = 613,                  /* NESTED  */
    NEW = 614,                     /* NEW  */
    NEXT = 615,                    /* NEXT  */
    NFC = 616,                     /* NFC  */
    NFD = 617,                     /* NFD  */
    NFKC = 618,                    /* NFKC  */
    NFKD = 619,                    /* NFKD  */
    NO = 620,                      /* NO  */
    NODE = 621,                    /* NODE  */
    NONE = 622,                    /* NONE  */
    NORMALIZE = 623,               /* NORMALIZE  */
    NORMALIZED = 624,              /* NORMALIZED  */
    NOT = 625,                     /* NOT  */
    NOTHING = 626,                 /* NOTHING  */
    NOTIFY = 627,                  /* NOTIFY  */
    NOTNULL = 628,                 /* NOTNULL  */
    NOWAIT = 629,                  /* NOWAIT  */
    NULL_P = 630,                  /* NULL_P  */
    NULLIF = 631,                  /* NULLIF  */
    NULLS_P = 632,                 /* NULLS_P  */
    NUMERIC = 633,                 /* NUMERIC  */
    OBJECT_P = 634,                /* OBJECT_P  */
    OBJECTS_P = 635,               /* OBJECTS_P  */
    OF = 636,                      /* OF  */
    OFF = 637,                     /* OFF  */
    OFFSET = 638,                  /* OFFSET  */
    OIDS = 639,                    /* OIDS  */
    OLD = 640,                     /* OLD  */
    OMIT = 641,                    /* OMIT  */
    ON = 642,                      /* ON  */
    ONLY = 643,                    /* ONLY  */
    OPERATOR = 644,                /* OPERATOR  */
    OPTION = 645,                  /* OPTION  */
    OPTIONS = 646,                 /* OPTIONS  */
    OR = 647,                      /* OR  */
    ORDER = 648,                   /* ORDER  */
    ORDINALITY = 649,              /* ORDINALITY  */
    OTHERS = 650,                  /* OTHERS  */
    OUT_P = 651,                   /* OUT_P  */
    OUTER_P = 652,                 /* OUTER_P  */
    OVER = 653,                    /* OVER  */
    OVERLAPS = 654,                /* OVERLAPS  */
    OVERLAY = 655,                 /* OVERLAY  */
    OVERRIDING = 656,              /* OVERRIDING  */
    OWNED = 657,                   /* OWNED  */
    OWNER = 658,                   /* OWNER  */
    PARALLEL = 659,                /* PARALLEL  */
    PARAMETER = 660,               /* PARAMETER  */
    PARSER = 661,                  /* PARSER  */
    PARTIAL = 662,                 /* PARTIAL  */
    PARTITION = 663,               /* PARTITION  */
    PARTITIONS = 664,              /* PARTITIONS  */
    PASSING = 665,                 /* PASSING  */
    PASSWORD = 666,                /* PASSWORD  */
    PATH = 667,                    /* PATH  */
    PERIOD = 668,                  /* PERIOD  */
    PLACING = 669,                 /* PLACING  */
    PLAN = 670,                    /* PLAN  */
    PLANS = 671,                   /* PLANS  */
    POLICY = 672,                  /* POLICY  */
    PORTION = 673,                 /* PORTION  */
    POSITION = 674,                /* POSITION  */
    PRECEDING = 675,               /* PRECEDING  */
    PRECISION = 676,               /* PRECISION  */
    PRESERVE = 677,                /* PRESERVE  */
    PREPARE = 678,                 /* PREPARE  */
    PREPARED = 679,                /* PREPARED  */
    PRIMARY = 680,                 /* PRIMARY  */
    PRIOR = 681,                   /* PRIOR  */
    PRIVILEGES = 682,              /* PRIVILEGES  */
    PROCEDURAL = 683,              /* PROCEDURAL  */
    PROCEDURE = 684,               /* PROCEDURE  */
    PROCEDURES = 685,              /* PROCEDURES  */
    PROGRAM = 686,                 /* PROGRAM  */
    PROPERTIES = 687,              /* PROPERTIES  */
    PROPERTY = 688,                /* PROPERTY  */
    PUBLICATION = 689,             /* PUBLICATION  */
    QUOTE = 690,                   /* QUOTE  */
    QUOTES = 691,                  /* QUOTES  */
    RANGE = 692,                   /* RANGE  */
    READ = 693,                    /* READ  */
    REAL = 694,                    /* REAL  */
    REASSIGN = 695,                /* REASSIGN  */
    RECURSIVE = 696,               /* RECURSIVE  */
    REF_P = 697,                   /* REF_P  */
    REFERENCES = 698,              /* REFERENCES  */
    REFERENCING = 699,             /* REFERENCING  */
    REFRESH = 700,                 /* REFRESH  */
    REINDEX = 701,                 /* REINDEX  */
    RELATIONSHIP = 702,            /* RELATIONSHIP  */
    RELATIVE_P = 703,              /* RELATIVE_P  */
    RELEASE = 704,                 /* RELEASE  */
    RENAME = 705,                  /* RENAME  */
    REPACK = 706,                  /* REPACK  */
    REPEATABLE = 707,              /* REPEATABLE  */
    REPLACE = 708,                 /* REPLACE  */
    REPLICA = 709,                 /* REPLICA  */
    RESET = 710,                   /* RESET  */
    RESPECT_P = 711,               /* RESPECT_P  */
    RESTART = 712,                 /* RESTART  */
    RESTRICT = 713,                /* RESTRICT  */
    RETURN = 714,                  /* RETURN  */
    RETURNING = 715,               /* RETURNING  */
    RETURNS = 716,                 /* RETURNS  */
    REVOKE = 717,                  /* REVOKE  */
    RIGHT = 718,                   /* RIGHT  */
    ROLE = 719,                    /* ROLE  */
    ROLLBACK = 720,                /* ROLLBACK  */
    ROLLUP = 721,                  /* ROLLUP  */
    ROUTINE = 722,                 /* ROUTINE  */
    ROUTINES = 723,                /* ROUTINES  */
    ROW = 724,                     /* ROW  */
    ROWS = 725,                    /* ROWS  */
    RULE = 726,                    /* RULE  */
    SAVEPOINT = 727,               /* SAVEPOINT  */
    SCALAR = 728,                  /* SCALAR  */
    SCHEMA = 729,                  /* SCHEMA  */
    SCHEMAS = 730,                 /* SCHEMAS  */
    SCROLL = 731,                  /* SCROLL  */
    SEARCH = 732,                  /* SEARCH  */
    SECOND_P = 733,                /* SECOND_P  */
    SECURITY = 734,                /* SECURITY  */
    SELECT = 735,                  /* SELECT  */
    SEQUENCE = 736,                /* SEQUENCE  */
    SEQUENCES = 737,               /* SEQUENCES  */
    SERIALIZABLE = 738,            /* SERIALIZABLE  */
    SERVER = 739,                  /* SERVER  */
    SESSION = 740,                 /* SESSION  */
    SESSION_USER = 741,            /* SESSION_USER  */
    SET = 742,                     /* SET  */
    SETS = 743,                    /* SETS  */
    SETOF = 744,                   /* SETOF  */
    SHARE = 745,                   /* SHARE  */
    SHOW = 746,                    /* SHOW  */
    SIMILAR = 747,                 /* SIMILAR  */
    SIMPLE = 748,                  /* SIMPLE  */
    SKIP = 749,                    /* SKIP  */
    SMALLINT = 750,                /* SMALLINT  */
    SNAPSHOT = 751,                /* SNAPSHOT  */
    SOME = 752,                    /* SOME  */
    SPLIT = 753,                   /* SPLIT  */
    SOURCE = 754,                  /* SOURCE  */
    SQL_P = 755,                   /* SQL_P  */
    STABLE = 756,                  /* STABLE  */
    STANDALONE_P = 757,            /* STANDALONE_P  */
    START = 758,                   /* START  */
    STATEMENT = 759,               /* STATEMENT  */
    STATISTICS = 760,              /* STATISTICS  */
    STDIN = 761,                   /* STDIN  */
    STDOUT = 762,                  /* STDOUT  */
    STORAGE = 763,                 /* STORAGE  */
    STORED = 764,                  /* STORED  */
    STRICT_P = 765,                /* STRICT_P  */
    STRING_P = 766,                /* STRING_P  */
    STRIP_P = 767,                 /* STRIP_P  */
    SUBSCRIPTION = 768,            /* SUBSCRIPTION  */
    SUBSTRING = 769,               /* SUBSTRING  */
    SUPPORT = 770,                 /* SUPPORT  */
    SYMMETRIC = 771,               /* SYMMETRIC  */
    SYSID = 772,                   /* SYSID  */
    SYSTEM_P = 773,                /* SYSTEM_P  */
    SYSTEM_USER = 774,             /* SYSTEM_USER  */
    TABLE = 775,                   /* TABLE  */
    TABLES = 776,                  /* TABLES  */
    TABLESAMPLE = 777,             /* TABLESAMPLE  */
    TABLESPACE = 778,              /* TABLESPACE  */
    TARGET = 779,                  /* TARGET  */
    TEMP = 780,                    /* TEMP  */
    TEMPLATE = 781,                /* TEMPLATE  */
    TEMPORARY = 782,               /* TEMPORARY  */
    TEXT_P = 783,                  /* TEXT_P  */
    THEN = 784,                    /* THEN  */
    TIES = 785,                    /* TIES  */
    TIME = 786,                    /* TIME  */
    TIMESTAMP = 787,               /* TIMESTAMP  */
    TO = 788,                      /* TO  */
    TRAILING = 789,                /* TRAILING  */
    TRANSACTION = 790,             /* TRANSACTION  */
    TRANSFORM = 791,               /* TRANSFORM  */
    TREAT = 792,                   /* TREAT  */
    TRIGGER = 793,                 /* TRIGGER  */
    TRIM = 794,                    /* TRIM  */
    TRUE_P = 795,                  /* TRUE_P  */
    TRUNCATE = 796,                /* TRUNCATE  */
    TRUSTED = 797,                 /* TRUSTED  */
    TYPE_P = 798,                  /* TYPE_P  */
    TYPES_P = 799,                 /* TYPES_P  */
    UESCAPE = 800,                 /* UESCAPE  */
    UNBOUNDED = 801,               /* UNBOUNDED  */
    UNCONDITIONAL = 802,           /* UNCONDITIONAL  */
    UNCOMMITTED = 803,             /* UNCOMMITTED  */
    UNENCRYPTED = 804,             /* UNENCRYPTED  */
    UNION = 805,                   /* UNION  */
    UNIQUE = 806,                  /* UNIQUE  */
    UNKNOWN = 807,                 /* UNKNOWN  */
    UNLISTEN = 808,                /* UNLISTEN  */
    UNLOGGED = 809,                /* UNLOGGED  */
    UNTIL = 810,                   /* UNTIL  */
    UPDATE = 811,                  /* UPDATE  */
    USER = 812,                    /* USER  */
    USING = 813,                   /* USING  */
    VACUUM = 814,                  /* VACUUM  */
    VALID = 815,                   /* VALID  */
    VALIDATE = 816,                /* VALIDATE  */
    VALIDATOR = 817,               /* VALIDATOR  */
    VALUE_P = 818,                 /* VALUE_P  */
    VALUES = 819,                  /* VALUES  */
    VARCHAR = 820,                 /* VARCHAR  */
    VARIADIC = 821,                /* VARIADIC  */
    VARYING = 822,                 /* VARYING  */
    VERBOSE = 823,                 /* VERBOSE  */
    VERSION_P = 824,               /* VERSION_P  */
    VERTEX = 825,                  /* VERTEX  */
    VIEW = 826,                    /* VIEW  */
    VIEWS = 827,                   /* VIEWS  */
    VIRTUAL = 828,                 /* VIRTUAL  */
    VOLATILE = 829,                /* VOLATILE  */
    WAIT = 830,                    /* WAIT  */
    WHEN = 831,                    /* WHEN  */
    WHERE = 832,                   /* WHERE  */
    WHITESPACE_P = 833,            /* WHITESPACE_P  */
    WINDOW = 834,                  /* WINDOW  */
    WITH = 835,                    /* WITH  */
    WITHIN = 836,                  /* WITHIN  */
    WITHOUT = 837,                 /* WITHOUT  */
    WORK = 838,                    /* WORK  */
    WRAPPER = 839,                 /* WRAPPER  */
    WRITE = 840,                   /* WRITE  */
    XML_P = 841,                   /* XML_P  */
    XMLATTRIBUTES = 842,           /* XMLATTRIBUTES  */
    XMLCONCAT = 843,               /* XMLCONCAT  */
    XMLELEMENT = 844,              /* XMLELEMENT  */
    XMLEXISTS = 845,               /* XMLEXISTS  */
    XMLFOREST = 846,               /* XMLFOREST  */
    XMLNAMESPACES = 847,           /* XMLNAMESPACES  */
    XMLPARSE = 848,                /* XMLPARSE  */
    XMLPI = 849,                   /* XMLPI  */
    XMLROOT = 850,                 /* XMLROOT  */
    XMLSERIALIZE = 851,            /* XMLSERIALIZE  */
    XMLTABLE = 852,                /* XMLTABLE  */
    YEAR_P = 853,                  /* YEAR_P  */
    YES_P = 854,                   /* YES_P  */
    ZONE = 855,                    /* ZONE  */
    FORMAT_LA = 856,               /* FORMAT_LA  */
    NOT_LA = 857,                  /* NOT_LA  */
    NULLS_LA = 858,                /* NULLS_LA  */
    WITH_LA = 859,                 /* WITH_LA  */
    WITHOUT_LA = 860,              /* WITHOUT_LA  */
    MODE_TYPE_NAME = 861,          /* MODE_TYPE_NAME  */
    MODE_PLPGSQL_EXPR = 862,       /* MODE_PLPGSQL_EXPR  */
    MODE_PLPGSQL_ASSIGN1 = 863,    /* MODE_PLPGSQL_ASSIGN1  */
    MODE_PLPGSQL_ASSIGN2 = 864,    /* MODE_PLPGSQL_ASSIGN2  */
    MODE_PLPGSQL_ASSIGN3 = 865,    /* MODE_PLPGSQL_ASSIGN3  */
    RIGHT_ARROW = 866,             /* RIGHT_ARROW  */
    UMINUS = 867                   /* UMINUS  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 589 "preproc.y"

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

#line 693 "preproc.h"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif


extern YYSTYPE base_yylval;
extern YYLTYPE base_yylloc;

int base_yyparse (void);


#endif /* !YY_BASE_YY_PREPROC_H_INCLUDED  */
