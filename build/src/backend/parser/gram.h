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

#ifndef YY_BASE_YY_GRAM_H_INCLUDED
# define YY_BASE_YY_GRAM_H_INCLUDED
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
    IDENT = 258,                   /* IDENT  */
    UIDENT = 259,                  /* UIDENT  */
    FCONST = 260,                  /* FCONST  */
    SCONST = 261,                  /* SCONST  */
    USCONST = 262,                 /* USCONST  */
    BCONST = 263,                  /* BCONST  */
    XCONST = 264,                  /* XCONST  */
    Op = 265,                      /* Op  */
    ICONST = 266,                  /* ICONST  */
    PARAM = 267,                   /* PARAM  */
    TYPECAST = 268,                /* TYPECAST  */
    DOT_DOT = 269,                 /* DOT_DOT  */
    COLON_EQUALS = 270,            /* COLON_EQUALS  */
    EQUALS_GREATER = 271,          /* EQUALS_GREATER  */
    LESS_EQUALS = 272,             /* LESS_EQUALS  */
    GREATER_EQUALS = 273,          /* GREATER_EQUALS  */
    NOT_EQUALS = 274,              /* NOT_EQUALS  */
    ABORT_P = 275,                 /* ABORT_P  */
    ABSENT = 276,                  /* ABSENT  */
    ABSOLUTE_P = 277,              /* ABSOLUTE_P  */
    ACCESS = 278,                  /* ACCESS  */
    ACTION = 279,                  /* ACTION  */
    ADD_P = 280,                   /* ADD_P  */
    ADMIN = 281,                   /* ADMIN  */
    AFTER = 282,                   /* AFTER  */
    AGGREGATE = 283,               /* AGGREGATE  */
    ALL = 284,                     /* ALL  */
    ALSO = 285,                    /* ALSO  */
    ALTER = 286,                   /* ALTER  */
    ALWAYS = 287,                  /* ALWAYS  */
    ANALYSE = 288,                 /* ANALYSE  */
    ANALYZE = 289,                 /* ANALYZE  */
    AND = 290,                     /* AND  */
    ANY = 291,                     /* ANY  */
    ARRAY = 292,                   /* ARRAY  */
    AS = 293,                      /* AS  */
    ASC = 294,                     /* ASC  */
    ASENSITIVE = 295,              /* ASENSITIVE  */
    ASSERTION = 296,               /* ASSERTION  */
    ASSIGNMENT = 297,              /* ASSIGNMENT  */
    ASYMMETRIC = 298,              /* ASYMMETRIC  */
    ATOMIC = 299,                  /* ATOMIC  */
    AT = 300,                      /* AT  */
    ATTACH = 301,                  /* ATTACH  */
    ATTRIBUTE = 302,               /* ATTRIBUTE  */
    AUTHORIZATION = 303,           /* AUTHORIZATION  */
    BACKWARD = 304,                /* BACKWARD  */
    BEFORE = 305,                  /* BEFORE  */
    BEGIN_P = 306,                 /* BEGIN_P  */
    BETWEEN = 307,                 /* BETWEEN  */
    BIGINT = 308,                  /* BIGINT  */
    BINARY = 309,                  /* BINARY  */
    BIT = 310,                     /* BIT  */
    BOOLEAN_P = 311,               /* BOOLEAN_P  */
    BOTH = 312,                    /* BOTH  */
    BREADTH = 313,                 /* BREADTH  */
    BY = 314,                      /* BY  */
    CACHE = 315,                   /* CACHE  */
    CALL = 316,                    /* CALL  */
    CALLED = 317,                  /* CALLED  */
    CASCADE = 318,                 /* CASCADE  */
    CASCADED = 319,                /* CASCADED  */
    CASE = 320,                    /* CASE  */
    CAST = 321,                    /* CAST  */
    CATALOG_P = 322,               /* CATALOG_P  */
    CHAIN = 323,                   /* CHAIN  */
    CHAR_P = 324,                  /* CHAR_P  */
    CHARACTER = 325,               /* CHARACTER  */
    CHARACTERISTICS = 326,         /* CHARACTERISTICS  */
    CHECK = 327,                   /* CHECK  */
    CHECKPOINT = 328,              /* CHECKPOINT  */
    CLASS = 329,                   /* CLASS  */
    CLOSE = 330,                   /* CLOSE  */
    CLUSTER = 331,                 /* CLUSTER  */
    COALESCE = 332,                /* COALESCE  */
    COLLATE = 333,                 /* COLLATE  */
    COLLATION = 334,               /* COLLATION  */
    COLUMN = 335,                  /* COLUMN  */
    COLUMNS = 336,                 /* COLUMNS  */
    COMMENT = 337,                 /* COMMENT  */
    COMMENTS = 338,                /* COMMENTS  */
    COMMIT = 339,                  /* COMMIT  */
    COMMITTED = 340,               /* COMMITTED  */
    COMPRESSION = 341,             /* COMPRESSION  */
    CONCURRENTLY = 342,            /* CONCURRENTLY  */
    CONDITIONAL = 343,             /* CONDITIONAL  */
    CONFIGURATION = 344,           /* CONFIGURATION  */
    CONFLICT = 345,                /* CONFLICT  */
    CONNECTION = 346,              /* CONNECTION  */
    CONSTRAINT = 347,              /* CONSTRAINT  */
    CONSTRAINTS = 348,             /* CONSTRAINTS  */
    CONTENT_P = 349,               /* CONTENT_P  */
    CONTINUE_P = 350,              /* CONTINUE_P  */
    CONVERSION_P = 351,            /* CONVERSION_P  */
    COPY = 352,                    /* COPY  */
    COST = 353,                    /* COST  */
    CREATE = 354,                  /* CREATE  */
    CROSS = 355,                   /* CROSS  */
    CSV = 356,                     /* CSV  */
    CUBE = 357,                    /* CUBE  */
    CURRENT_P = 358,               /* CURRENT_P  */
    CURRENT_CATALOG = 359,         /* CURRENT_CATALOG  */
    CURRENT_DATE = 360,            /* CURRENT_DATE  */
    CURRENT_ROLE = 361,            /* CURRENT_ROLE  */
    CURRENT_SCHEMA = 362,          /* CURRENT_SCHEMA  */
    CURRENT_TIME = 363,            /* CURRENT_TIME  */
    CURRENT_TIMESTAMP = 364,       /* CURRENT_TIMESTAMP  */
    CURRENT_USER = 365,            /* CURRENT_USER  */
    CURSOR = 366,                  /* CURSOR  */
    CYCLE = 367,                   /* CYCLE  */
    DATA_P = 368,                  /* DATA_P  */
    DATABASE = 369,                /* DATABASE  */
    DAY_P = 370,                   /* DAY_P  */
    DEALLOCATE = 371,              /* DEALLOCATE  */
    DEC = 372,                     /* DEC  */
    DECIMAL_P = 373,               /* DECIMAL_P  */
    DECLARE = 374,                 /* DECLARE  */
    DEFAULT = 375,                 /* DEFAULT  */
    DEFAULTS = 376,                /* DEFAULTS  */
    DEFERRABLE = 377,              /* DEFERRABLE  */
    DEFERRED = 378,                /* DEFERRED  */
    DEFINER = 379,                 /* DEFINER  */
    DELETE_P = 380,                /* DELETE_P  */
    DELIMITER = 381,               /* DELIMITER  */
    DELIMITERS = 382,              /* DELIMITERS  */
    DEPENDS = 383,                 /* DEPENDS  */
    DEPTH = 384,                   /* DEPTH  */
    DESC = 385,                    /* DESC  */
    DESTINATION = 386,             /* DESTINATION  */
    DETACH = 387,                  /* DETACH  */
    DICTIONARY = 388,              /* DICTIONARY  */
    DISABLE_P = 389,               /* DISABLE_P  */
    DISCARD = 390,                 /* DISCARD  */
    DISTINCT = 391,                /* DISTINCT  */
    DO = 392,                      /* DO  */
    DOCUMENT_P = 393,              /* DOCUMENT_P  */
    DOMAIN_P = 394,                /* DOMAIN_P  */
    DOUBLE_P = 395,                /* DOUBLE_P  */
    DROP = 396,                    /* DROP  */
    EACH = 397,                    /* EACH  */
    EDGE = 398,                    /* EDGE  */
    ELSE = 399,                    /* ELSE  */
    EMPTY_P = 400,                 /* EMPTY_P  */
    ENABLE_P = 401,                /* ENABLE_P  */
    ENCODING = 402,                /* ENCODING  */
    ENCRYPTED = 403,               /* ENCRYPTED  */
    END_P = 404,                   /* END_P  */
    ENFORCED = 405,                /* ENFORCED  */
    ENUM_P = 406,                  /* ENUM_P  */
    ERROR_P = 407,                 /* ERROR_P  */
    ESCAPE = 408,                  /* ESCAPE  */
    EVENT = 409,                   /* EVENT  */
    EXCEPT = 410,                  /* EXCEPT  */
    EXCLUDE = 411,                 /* EXCLUDE  */
    EXCLUDING = 412,               /* EXCLUDING  */
    EXCLUSIVE = 413,               /* EXCLUSIVE  */
    EXECUTE = 414,                 /* EXECUTE  */
    EXISTS = 415,                  /* EXISTS  */
    EXPLAIN = 416,                 /* EXPLAIN  */
    EXPRESSION = 417,              /* EXPRESSION  */
    EXTENSION = 418,               /* EXTENSION  */
    EXTERNAL = 419,                /* EXTERNAL  */
    EXTRACT = 420,                 /* EXTRACT  */
    FALSE_P = 421,                 /* FALSE_P  */
    FAMILY = 422,                  /* FAMILY  */
    FETCH = 423,                   /* FETCH  */
    FILTER = 424,                  /* FILTER  */
    FINALIZE = 425,                /* FINALIZE  */
    FIRST_P = 426,                 /* FIRST_P  */
    FLOAT_P = 427,                 /* FLOAT_P  */
    FOLLOWING = 428,               /* FOLLOWING  */
    FOR = 429,                     /* FOR  */
    FORCE = 430,                   /* FORCE  */
    FOREIGN = 431,                 /* FOREIGN  */
    FORMAT = 432,                  /* FORMAT  */
    FORWARD = 433,                 /* FORWARD  */
    FREEZE = 434,                  /* FREEZE  */
    FROM = 435,                    /* FROM  */
    FULL = 436,                    /* FULL  */
    FUNCTION = 437,                /* FUNCTION  */
    FUNCTIONS = 438,               /* FUNCTIONS  */
    GENERATED = 439,               /* GENERATED  */
    GLOBAL = 440,                  /* GLOBAL  */
    GRANT = 441,                   /* GRANT  */
    GRANTED = 442,                 /* GRANTED  */
    GRAPH = 443,                   /* GRAPH  */
    GRAPH_TABLE = 444,             /* GRAPH_TABLE  */
    GREATEST = 445,                /* GREATEST  */
    GROUP_P = 446,                 /* GROUP_P  */
    GROUPING = 447,                /* GROUPING  */
    GROUPS = 448,                  /* GROUPS  */
    HANDLER = 449,                 /* HANDLER  */
    HAVING = 450,                  /* HAVING  */
    HEADER_P = 451,                /* HEADER_P  */
    HOLD = 452,                    /* HOLD  */
    HOUR_P = 453,                  /* HOUR_P  */
    IDENTITY_P = 454,              /* IDENTITY_P  */
    IF_P = 455,                    /* IF_P  */
    IGNORE_P = 456,                /* IGNORE_P  */
    ILIKE = 457,                   /* ILIKE  */
    IMMEDIATE = 458,               /* IMMEDIATE  */
    IMMUTABLE = 459,               /* IMMUTABLE  */
    IMPLICIT_P = 460,              /* IMPLICIT_P  */
    IMPORT_P = 461,                /* IMPORT_P  */
    IN_P = 462,                    /* IN_P  */
    INCLUDE = 463,                 /* INCLUDE  */
    INCLUDING = 464,               /* INCLUDING  */
    INCREMENT = 465,               /* INCREMENT  */
    INDENT = 466,                  /* INDENT  */
    INDEX = 467,                   /* INDEX  */
    INDEXES = 468,                 /* INDEXES  */
    INHERIT = 469,                 /* INHERIT  */
    INHERITS = 470,                /* INHERITS  */
    INITIALLY = 471,               /* INITIALLY  */
    INLINE_P = 472,                /* INLINE_P  */
    INNER_P = 473,                 /* INNER_P  */
    INOUT = 474,                   /* INOUT  */
    INPUT_P = 475,                 /* INPUT_P  */
    INSENSITIVE = 476,             /* INSENSITIVE  */
    INSERT = 477,                  /* INSERT  */
    INSTEAD = 478,                 /* INSTEAD  */
    INT_P = 479,                   /* INT_P  */
    INTEGER = 480,                 /* INTEGER  */
    INTERSECT = 481,               /* INTERSECT  */
    INTERVAL = 482,                /* INTERVAL  */
    INTO = 483,                    /* INTO  */
    INVOKER = 484,                 /* INVOKER  */
    IS = 485,                      /* IS  */
    ISNULL = 486,                  /* ISNULL  */
    ISOLATION = 487,               /* ISOLATION  */
    JOIN = 488,                    /* JOIN  */
    JSON = 489,                    /* JSON  */
    JSON_ARRAY = 490,              /* JSON_ARRAY  */
    JSON_ARRAYAGG = 491,           /* JSON_ARRAYAGG  */
    JSON_EXISTS = 492,             /* JSON_EXISTS  */
    JSON_OBJECT = 493,             /* JSON_OBJECT  */
    JSON_OBJECTAGG = 494,          /* JSON_OBJECTAGG  */
    JSON_QUERY = 495,              /* JSON_QUERY  */
    JSON_SCALAR = 496,             /* JSON_SCALAR  */
    JSON_SERIALIZE = 497,          /* JSON_SERIALIZE  */
    JSON_TABLE = 498,              /* JSON_TABLE  */
    JSON_VALUE = 499,              /* JSON_VALUE  */
    KEEP = 500,                    /* KEEP  */
    KEY = 501,                     /* KEY  */
    KEYS = 502,                    /* KEYS  */
    LABEL = 503,                   /* LABEL  */
    LANGUAGE = 504,                /* LANGUAGE  */
    LARGE_P = 505,                 /* LARGE_P  */
    LAST_P = 506,                  /* LAST_P  */
    LATERAL_P = 507,               /* LATERAL_P  */
    LEADING = 508,                 /* LEADING  */
    LEAKPROOF = 509,               /* LEAKPROOF  */
    LEAST = 510,                   /* LEAST  */
    LEFT = 511,                    /* LEFT  */
    LEVEL = 512,                   /* LEVEL  */
    LIKE = 513,                    /* LIKE  */
    LIMIT = 514,                   /* LIMIT  */
    LISTEN = 515,                  /* LISTEN  */
    LOAD = 516,                    /* LOAD  */
    LOCAL = 517,                   /* LOCAL  */
    LOCALTIME = 518,               /* LOCALTIME  */
    LOCALTIMESTAMP = 519,          /* LOCALTIMESTAMP  */
    LOCATION = 520,                /* LOCATION  */
    LOCK_P = 521,                  /* LOCK_P  */
    LOCKED = 522,                  /* LOCKED  */
    LOGGED = 523,                  /* LOGGED  */
    LSN_P = 524,                   /* LSN_P  */
    MAPPING = 525,                 /* MAPPING  */
    MATCH = 526,                   /* MATCH  */
    MATCHED = 527,                 /* MATCHED  */
    MATERIALIZED = 528,            /* MATERIALIZED  */
    MAXVALUE = 529,                /* MAXVALUE  */
    MERGE = 530,                   /* MERGE  */
    MERGE_ACTION = 531,            /* MERGE_ACTION  */
    METHOD = 532,                  /* METHOD  */
    MINUTE_P = 533,                /* MINUTE_P  */
    MINVALUE = 534,                /* MINVALUE  */
    MODE = 535,                    /* MODE  */
    MONTH_P = 536,                 /* MONTH_P  */
    MOVE = 537,                    /* MOVE  */
    NAME_P = 538,                  /* NAME_P  */
    NAMES = 539,                   /* NAMES  */
    NATIONAL = 540,                /* NATIONAL  */
    NATURAL = 541,                 /* NATURAL  */
    NCHAR = 542,                   /* NCHAR  */
    NESTED = 543,                  /* NESTED  */
    NEW = 544,                     /* NEW  */
    NEXT = 545,                    /* NEXT  */
    NFC = 546,                     /* NFC  */
    NFD = 547,                     /* NFD  */
    NFKC = 548,                    /* NFKC  */
    NFKD = 549,                    /* NFKD  */
    NO = 550,                      /* NO  */
    NODE = 551,                    /* NODE  */
    NONE = 552,                    /* NONE  */
    NORMALIZE = 553,               /* NORMALIZE  */
    NORMALIZED = 554,              /* NORMALIZED  */
    NOT = 555,                     /* NOT  */
    NOTHING = 556,                 /* NOTHING  */
    NOTIFY = 557,                  /* NOTIFY  */
    NOTNULL = 558,                 /* NOTNULL  */
    NOWAIT = 559,                  /* NOWAIT  */
    NULL_P = 560,                  /* NULL_P  */
    NULLIF = 561,                  /* NULLIF  */
    NULLS_P = 562,                 /* NULLS_P  */
    NUMERIC = 563,                 /* NUMERIC  */
    OBJECT_P = 564,                /* OBJECT_P  */
    OBJECTS_P = 565,               /* OBJECTS_P  */
    OF = 566,                      /* OF  */
    OFF = 567,                     /* OFF  */
    OFFSET = 568,                  /* OFFSET  */
    OIDS = 569,                    /* OIDS  */
    OLD = 570,                     /* OLD  */
    OMIT = 571,                    /* OMIT  */
    ON = 572,                      /* ON  */
    ONLY = 573,                    /* ONLY  */
    OPERATOR = 574,                /* OPERATOR  */
    OPTION = 575,                  /* OPTION  */
    OPTIONS = 576,                 /* OPTIONS  */
    OR = 577,                      /* OR  */
    ORDER = 578,                   /* ORDER  */
    ORDINALITY = 579,              /* ORDINALITY  */
    OTHERS = 580,                  /* OTHERS  */
    OUT_P = 581,                   /* OUT_P  */
    OUTER_P = 582,                 /* OUTER_P  */
    OVER = 583,                    /* OVER  */
    OVERLAPS = 584,                /* OVERLAPS  */
    OVERLAY = 585,                 /* OVERLAY  */
    OVERRIDING = 586,              /* OVERRIDING  */
    OWNED = 587,                   /* OWNED  */
    OWNER = 588,                   /* OWNER  */
    PARALLEL = 589,                /* PARALLEL  */
    PARAMETER = 590,               /* PARAMETER  */
    PARSER = 591,                  /* PARSER  */
    PARTIAL = 592,                 /* PARTIAL  */
    PARTITION = 593,               /* PARTITION  */
    PARTITIONS = 594,              /* PARTITIONS  */
    PASSING = 595,                 /* PASSING  */
    PASSWORD = 596,                /* PASSWORD  */
    PATH = 597,                    /* PATH  */
    PERIOD = 598,                  /* PERIOD  */
    PLACING = 599,                 /* PLACING  */
    PLAN = 600,                    /* PLAN  */
    PLANS = 601,                   /* PLANS  */
    POLICY = 602,                  /* POLICY  */
    PORTION = 603,                 /* PORTION  */
    POSITION = 604,                /* POSITION  */
    PRECEDING = 605,               /* PRECEDING  */
    PRECISION = 606,               /* PRECISION  */
    PRESERVE = 607,                /* PRESERVE  */
    PREPARE = 608,                 /* PREPARE  */
    PREPARED = 609,                /* PREPARED  */
    PRIMARY = 610,                 /* PRIMARY  */
    PRIOR = 611,                   /* PRIOR  */
    PRIVILEGES = 612,              /* PRIVILEGES  */
    PROCEDURAL = 613,              /* PROCEDURAL  */
    PROCEDURE = 614,               /* PROCEDURE  */
    PROCEDURES = 615,              /* PROCEDURES  */
    PROGRAM = 616,                 /* PROGRAM  */
    PROPERTIES = 617,              /* PROPERTIES  */
    PROPERTY = 618,                /* PROPERTY  */
    PUBLICATION = 619,             /* PUBLICATION  */
    QUOTE = 620,                   /* QUOTE  */
    QUOTES = 621,                  /* QUOTES  */
    RANGE = 622,                   /* RANGE  */
    READ = 623,                    /* READ  */
    REAL = 624,                    /* REAL  */
    REASSIGN = 625,                /* REASSIGN  */
    RECURSIVE = 626,               /* RECURSIVE  */
    REF_P = 627,                   /* REF_P  */
    REFERENCES = 628,              /* REFERENCES  */
    REFERENCING = 629,             /* REFERENCING  */
    REFRESH = 630,                 /* REFRESH  */
    REINDEX = 631,                 /* REINDEX  */
    RELATIONSHIP = 632,            /* RELATIONSHIP  */
    RELATIVE_P = 633,              /* RELATIVE_P  */
    RELEASE = 634,                 /* RELEASE  */
    RENAME = 635,                  /* RENAME  */
    REPACK = 636,                  /* REPACK  */
    REPEATABLE = 637,              /* REPEATABLE  */
    REPLACE = 638,                 /* REPLACE  */
    REPLICA = 639,                 /* REPLICA  */
    RESET = 640,                   /* RESET  */
    RESPECT_P = 641,               /* RESPECT_P  */
    RESTART = 642,                 /* RESTART  */
    RESTRICT = 643,                /* RESTRICT  */
    RETURN = 644,                  /* RETURN  */
    RETURNING = 645,               /* RETURNING  */
    RETURNS = 646,                 /* RETURNS  */
    REVOKE = 647,                  /* REVOKE  */
    RIGHT = 648,                   /* RIGHT  */
    ROLE = 649,                    /* ROLE  */
    ROLLBACK = 650,                /* ROLLBACK  */
    ROLLUP = 651,                  /* ROLLUP  */
    ROUTINE = 652,                 /* ROUTINE  */
    ROUTINES = 653,                /* ROUTINES  */
    ROW = 654,                     /* ROW  */
    ROWS = 655,                    /* ROWS  */
    RULE = 656,                    /* RULE  */
    SAVEPOINT = 657,               /* SAVEPOINT  */
    SCALAR = 658,                  /* SCALAR  */
    SCHEMA = 659,                  /* SCHEMA  */
    SCHEMAS = 660,                 /* SCHEMAS  */
    SCROLL = 661,                  /* SCROLL  */
    SEARCH = 662,                  /* SEARCH  */
    SECOND_P = 663,                /* SECOND_P  */
    SECURITY = 664,                /* SECURITY  */
    SELECT = 665,                  /* SELECT  */
    SEQUENCE = 666,                /* SEQUENCE  */
    SEQUENCES = 667,               /* SEQUENCES  */
    SERIALIZABLE = 668,            /* SERIALIZABLE  */
    SERVER = 669,                  /* SERVER  */
    SESSION = 670,                 /* SESSION  */
    SESSION_USER = 671,            /* SESSION_USER  */
    SET = 672,                     /* SET  */
    SETS = 673,                    /* SETS  */
    SETOF = 674,                   /* SETOF  */
    SHARE = 675,                   /* SHARE  */
    SHOW = 676,                    /* SHOW  */
    SIMILAR = 677,                 /* SIMILAR  */
    SIMPLE = 678,                  /* SIMPLE  */
    SKIP = 679,                    /* SKIP  */
    SMALLINT = 680,                /* SMALLINT  */
    SNAPSHOT = 681,                /* SNAPSHOT  */
    SOME = 682,                    /* SOME  */
    SPLIT = 683,                   /* SPLIT  */
    SOURCE = 684,                  /* SOURCE  */
    SQL_P = 685,                   /* SQL_P  */
    STABLE = 686,                  /* STABLE  */
    STANDALONE_P = 687,            /* STANDALONE_P  */
    START = 688,                   /* START  */
    STATEMENT = 689,               /* STATEMENT  */
    STATISTICS = 690,              /* STATISTICS  */
    STDIN = 691,                   /* STDIN  */
    STDOUT = 692,                  /* STDOUT  */
    STORAGE = 693,                 /* STORAGE  */
    STORED = 694,                  /* STORED  */
    STRICT_P = 695,                /* STRICT_P  */
    STRING_P = 696,                /* STRING_P  */
    STRIP_P = 697,                 /* STRIP_P  */
    SUBSCRIPTION = 698,            /* SUBSCRIPTION  */
    SUBSTRING = 699,               /* SUBSTRING  */
    SUPPORT = 700,                 /* SUPPORT  */
    SYMMETRIC = 701,               /* SYMMETRIC  */
    SYSID = 702,                   /* SYSID  */
    SYSTEM_P = 703,                /* SYSTEM_P  */
    SYSTEM_USER = 704,             /* SYSTEM_USER  */
    TABLE = 705,                   /* TABLE  */
    TABLES = 706,                  /* TABLES  */
    TABLESAMPLE = 707,             /* TABLESAMPLE  */
    TABLESPACE = 708,              /* TABLESPACE  */
    TARGET = 709,                  /* TARGET  */
    TEMP = 710,                    /* TEMP  */
    TEMPLATE = 711,                /* TEMPLATE  */
    TEMPORARY = 712,               /* TEMPORARY  */
    TEXT_P = 713,                  /* TEXT_P  */
    THEN = 714,                    /* THEN  */
    TIES = 715,                    /* TIES  */
    TIME = 716,                    /* TIME  */
    TIMESTAMP = 717,               /* TIMESTAMP  */
    TO = 718,                      /* TO  */
    TRAILING = 719,                /* TRAILING  */
    TRANSACTION = 720,             /* TRANSACTION  */
    TRANSFORM = 721,               /* TRANSFORM  */
    TREAT = 722,                   /* TREAT  */
    TRIGGER = 723,                 /* TRIGGER  */
    TRIM = 724,                    /* TRIM  */
    TRUE_P = 725,                  /* TRUE_P  */
    TRUNCATE = 726,                /* TRUNCATE  */
    TRUSTED = 727,                 /* TRUSTED  */
    TYPE_P = 728,                  /* TYPE_P  */
    TYPES_P = 729,                 /* TYPES_P  */
    UESCAPE = 730,                 /* UESCAPE  */
    UNBOUNDED = 731,               /* UNBOUNDED  */
    UNCONDITIONAL = 732,           /* UNCONDITIONAL  */
    UNCOMMITTED = 733,             /* UNCOMMITTED  */
    UNENCRYPTED = 734,             /* UNENCRYPTED  */
    UNION = 735,                   /* UNION  */
    UNIQUE = 736,                  /* UNIQUE  */
    UNKNOWN = 737,                 /* UNKNOWN  */
    UNLISTEN = 738,                /* UNLISTEN  */
    UNLOGGED = 739,                /* UNLOGGED  */
    UNTIL = 740,                   /* UNTIL  */
    UPDATE = 741,                  /* UPDATE  */
    USER = 742,                    /* USER  */
    USING = 743,                   /* USING  */
    VACUUM = 744,                  /* VACUUM  */
    VALID = 745,                   /* VALID  */
    VALIDATE = 746,                /* VALIDATE  */
    VALIDATOR = 747,               /* VALIDATOR  */
    VALUE_P = 748,                 /* VALUE_P  */
    VALUES = 749,                  /* VALUES  */
    VARCHAR = 750,                 /* VARCHAR  */
    VARIADIC = 751,                /* VARIADIC  */
    VARYING = 752,                 /* VARYING  */
    VERBOSE = 753,                 /* VERBOSE  */
    VERSION_P = 754,               /* VERSION_P  */
    VERTEX = 755,                  /* VERTEX  */
    VIEW = 756,                    /* VIEW  */
    VIEWS = 757,                   /* VIEWS  */
    VIRTUAL = 758,                 /* VIRTUAL  */
    VOLATILE = 759,                /* VOLATILE  */
    WAIT = 760,                    /* WAIT  */
    WHEN = 761,                    /* WHEN  */
    WHERE = 762,                   /* WHERE  */
    WHITESPACE_P = 763,            /* WHITESPACE_P  */
    WINDOW = 764,                  /* WINDOW  */
    WITH = 765,                    /* WITH  */
    WITHIN = 766,                  /* WITHIN  */
    WITHOUT = 767,                 /* WITHOUT  */
    WORK = 768,                    /* WORK  */
    WRAPPER = 769,                 /* WRAPPER  */
    WRITE = 770,                   /* WRITE  */
    XML_P = 771,                   /* XML_P  */
    XMLATTRIBUTES = 772,           /* XMLATTRIBUTES  */
    XMLCONCAT = 773,               /* XMLCONCAT  */
    XMLELEMENT = 774,              /* XMLELEMENT  */
    XMLEXISTS = 775,               /* XMLEXISTS  */
    XMLFOREST = 776,               /* XMLFOREST  */
    XMLNAMESPACES = 777,           /* XMLNAMESPACES  */
    XMLPARSE = 778,                /* XMLPARSE  */
    XMLPI = 779,                   /* XMLPI  */
    XMLROOT = 780,                 /* XMLROOT  */
    XMLSERIALIZE = 781,            /* XMLSERIALIZE  */
    XMLTABLE = 782,                /* XMLTABLE  */
    YEAR_P = 783,                  /* YEAR_P  */
    YES_P = 784,                   /* YES_P  */
    ZONE = 785,                    /* ZONE  */
    FORMAT_LA = 786,               /* FORMAT_LA  */
    NOT_LA = 787,                  /* NOT_LA  */
    NULLS_LA = 788,                /* NULLS_LA  */
    WITH_LA = 789,                 /* WITH_LA  */
    WITHOUT_LA = 790,              /* WITHOUT_LA  */
    MODE_TYPE_NAME = 791,          /* MODE_TYPE_NAME  */
    MODE_PLPGSQL_EXPR = 792,       /* MODE_PLPGSQL_EXPR  */
    MODE_PLPGSQL_ASSIGN1 = 793,    /* MODE_PLPGSQL_ASSIGN1  */
    MODE_PLPGSQL_ASSIGN2 = 794,    /* MODE_PLPGSQL_ASSIGN2  */
    MODE_PLPGSQL_ASSIGN3 = 795,    /* MODE_PLPGSQL_ASSIGN3  */
    RIGHT_ARROW = 796,             /* RIGHT_ARROW  */
    UMINUS = 797                   /* UMINUS  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 224 "/home/postgres/Learn-PG/build/../src/backend/parser/gram.y"

	core_YYSTYPE core_yystype;
	/* these fields must match core_YYSTYPE: */
	int			ival;
	char	   *str;
	const char *keyword;

	char		chr;
	bool		boolean;
	JoinType	jtype;
	DropBehavior dbehavior;
	OnCommitAction oncommit;
	List	   *list;
	Node	   *node;
	ObjectType	objtype;
	TypeName   *typnam;
	FunctionParameter *fun_param;
	FunctionParameterMode fun_param_mode;
	ObjectWithArgs *objwithargs;
	DefElem	   *defelt;
	SortBy	   *sortby;
	WindowDef  *windef;
	JoinExpr   *jexpr;
	IndexElem  *ielem;
	StatsElem  *selem;
	Alias	   *alias;
	RangeVar   *range;
	IntoClause *into;
	WithClause *with;
	InferClause	*infer;
	OnConflictClause *onconflict;
	A_Indices  *aind;
	ResTarget  *target;
	struct PrivTarget *privtarget;
	AccessPriv *accesspriv;
	struct ImportQual *importqual;
	InsertStmt *istmt;
	VariableSetStmt *vsetstmt;
	PartitionElem *partelem;
	PartitionSpec *partspec;
	PartitionBoundSpec *partboundspec;
	SinglePartitionSpec *singlepartspec;
	RoleSpec   *rolespec;
	PublicationObjSpec *publicationobjectspec;
	PublicationAllObjSpec *publicationallobjectspec;
	struct SelectLimit *selectlimit;
	SetQuantifier setquantifier;
	struct GroupClause *groupclause;
	MergeMatchKind mergematch;
	MergeWhenClause *mergewhen;
	struct KeyActions *keyactions;
	struct KeyAction *keyaction;
	ReturningClause *retclause;
	ReturningOptionKind retoptionkind;

#line 662 "gram.h"

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




int base_yyparse (core_yyscan_t yyscanner);


#endif /* !YY_BASE_YY_GRAM_H_INCLUDED  */
