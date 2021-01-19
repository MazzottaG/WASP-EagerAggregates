/* A Bison parser, made by GNU Bison 3.5.1.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2020 Free Software Foundation,
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
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

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

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Undocumented macros, especially those whose name start with YY_,
   are private implementation details.  Do not rely on them.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.5.1"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* First part of user prologue.  */
#line 1 "aspcore2.y"

//////////////////////////////////////////////////////////////////////////////
// aspcore2.y

//////////////////////////////////////////////////////////////////////////////
/*
This file is part of the ASPCOMP2013 ASP-Core-2 validator (validator in the following)

    The validator is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    The validator is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with the validator.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "InputDirector.h"


#line 96 "aspcore2.tab.c"

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

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif


/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    SYMBOLIC_CONSTANT = 258,
    NUMBER = 259,
    VARIABLE = 260,
    STRING = 261,
    DIRECTIVE_NAME = 262,
    DIRECTIVE_VALUE = 263,
    AGGR_COUNT = 264,
    AGGR_MAX = 265,
    AGGR_MIN = 266,
    AGGR_SUM = 267,
    ERROR = 268,
    NEWLINE = 269,
    DOT = 270,
    DDOT = 271,
    SEMICOLON = 272,
    COLON = 273,
    CONS = 274,
    QUERY_MARK = 275,
    PLUS = 276,
    TIMES = 277,
    SLASH = 278,
    ANON_VAR = 279,
    PARAM_OPEN = 280,
    PARAM_CLOSE = 281,
    SQUARE_OPEN = 282,
    SQUARE_CLOSE = 283,
    CURLY_OPEN = 284,
    CURLY_CLOSE = 285,
    EQUAL = 286,
    UNEQUAL = 287,
    LESS = 288,
    GREATER = 289,
    LESS_OR_EQ = 290,
    GREATER_OR_EQ = 291,
    DASH = 292,
    COMMA = 293,
    NAF = 294,
    AT = 295,
    WCONS = 296,
    VEL = 297,
    EXISTS = 298
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 29 "aspcore2.y"

    char* string;
    char single_char;
    int integer;

#line 195 "aspcore2.tab.c"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (DLV2::InputDirector& director);





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
typedef yytype_uint8 yy_state_t;

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
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && ! defined __ICC && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                            \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
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

#if ! defined yyoverflow || YYERROR_VERBOSE

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
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


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
#define YYFINAL  67
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   379

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  44
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  58
/* YYNRULES -- Number of rules.  */
#define YYNRULES  126
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  201

#define YYUNDEFTOK  2
#define YYMAXUTOK   298


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
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
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,    66,    66,    69,    70,    71,    72,    76,    77,    81,
      82,    86,    90,    94,    98,   102,   109,   113,   121,   128,
     133,   141,   146,   150,   160,   164,   168,   172,   179,   183,
     190,   191,   192,   193,   197,   204,   211,   212,   216,   220,
     227,   234,   238,   245,   249,   256,   260,   264,   271,   272,
     276,   283,   289,   290,   294,   299,   304,   312,   313,   317,
     318,   322,   329,   333,   340,   341,   342,   346,   347,   348,
     349,   353,   358,   363,   367,   372,   379,   383,   390,   391,
     397,   398,   402,   407,   412,   417,   425,   430,   437,   442,
     450,   451,   452,   456,   463,   473,   480,   487,   494,   495,
     499,   506,   510,   511,   515,   522,   526,   533,   540,   541,
     545,   546,   547,   548,   549,   553,   557,   564,   568,   575,
     579,   580,   585,   592,   597,   602,   607
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "SYMBOLIC_CONSTANT", "NUMBER",
  "VARIABLE", "STRING", "DIRECTIVE_NAME", "DIRECTIVE_VALUE", "AGGR_COUNT",
  "AGGR_MAX", "AGGR_MIN", "AGGR_SUM", "ERROR", "NEWLINE", "DOT", "DDOT",
  "SEMICOLON", "COLON", "CONS", "QUERY_MARK", "PLUS", "TIMES", "SLASH",
  "ANON_VAR", "PARAM_OPEN", "PARAM_CLOSE", "SQUARE_OPEN", "SQUARE_CLOSE",
  "CURLY_OPEN", "CURLY_CLOSE", "EQUAL", "UNEQUAL", "LESS", "GREATER",
  "LESS_OR_EQ", "GREATER_OR_EQ", "DASH", "COMMA", "NAF", "AT", "WCONS",
  "VEL", "EXISTS", "$accept", "HEAD_SEPARATOR", "program", "real_program",
  "rules", "rule", "head", "body", "weight_at_levels", "levels_and_terms",
  "disjunction", "conjunction", "choice_atom", "lower_guard",
  "upper_guard", "choice_elements", "choice_element",
  "choice_element_atom", "choice_elements_literals", "naf_literals",
  "naf_literal", "naf_literal_aggregate", "existential_atom",
  "classic_literal", "atom", "terms", "basic_terms", "builtin_atom",
  "compareop", "binop", "arithop", "term_", "term", "basic_term",
  "ground_term", "variable_term", "vars", "identifier", "directives",
  "query", "lower_guard_compare_aggregate",
  "upper_guard_compare_aggregate", "compare_aggregate",
  "lower_guard_leftward_left_aggregate", "leftward_left_aggregate",
  "left_aggregate", "lower_guard_rightward_left_aggregate",
  "rightward_left_aggregate", "upper_guard_leftward_right_aggregate",
  "upper_guard_rightward_right_aggregate", "right_aggregate",
  "aggregate_atom", "leftwardop", "rightwardop", "aggregate",
  "aggregate_elements", "aggregate_element", "aggregate_function", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_int16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298
};
# endif

#define YYPACT_NINF (-116)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-105)

#define yytable_value_is_error(Yyn) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     132,  -116,  -116,   -10,  -116,  -116,     9,   266,  -116,   303,
     103,   303,   266,    29,    41,  -116,   208,  -116,    73,    19,
    -116,    37,  -116,  -116,  -116,  -116,   336,   200,   181,    54,
    -116,  -116,  -116,  -116,  -116,   313,    52,    80,  -116,  -116,
    -116,  -116,   336,   131,  -116,   131,   135,  -116,   131,   142,
    -116,  -116,   343,    95,   303,    63,    45,    27,  -116,   111,
    -116,   124,  -116,     1,   147,  -116,    42,  -116,  -116,   130,
    -116,  -116,   249,  -116,    50,   103,  -116,  -116,  -116,  -116,
    -116,  -116,  -116,  -116,  -116,  -116,  -116,  -116,   303,  -116,
    -116,   122,   150,  -116,  -116,  -116,   336,  -116,  -116,   266,
     143,   303,   192,   256,  -116,  -116,  -116,   303,  -116,  -116,
     303,   303,  -116,  -116,  -116,   327,  -116,   303,   103,   343,
     276,   122,   138,   162,  -116,  -116,  -116,   156,   103,  -116,
    -116,    32,  -116,  -116,   -18,    93,  -116,  -116,  -116,  -116,
    -116,    93,    93,    93,    93,  -116,  -116,  -116,  -116,  -116,
     175,     4,  -116,  -116,  -116,    51,  -116,    14,  -116,  -116,
     303,    68,   144,  -116,   336,    25,   303,  -116,  -116,  -116,
     343,   324,   303,  -116,   276,   327,   327,  -116,  -116,    93,
     276,  -116,   274,  -116,    93,   151,  -116,  -116,  -116,  -116,
    -116,   303,   303,   153,   276,   152,    75,  -116,  -116,   303,
     152
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       0,     6,    90,    72,    92,    91,     0,     0,    73,     0,
       0,     0,     0,     0,     0,     4,     7,    10,     0,    16,
      17,     0,    26,    24,    52,    78,     0,    71,     0,     0,
      93,   123,   124,   125,   126,     0,     0,    18,    48,    28,
      45,    47,     0,     0,   112,     0,   102,   110,     0,   103,
     111,    49,     0,     0,     0,     0,    71,     0,    37,    38,
      40,    54,    53,    77,     0,    88,     0,     1,     9,    52,
       8,    11,     0,     2,     0,     0,    67,    69,    70,    62,
      63,   115,   117,   116,   118,    68,    64,    34,     0,    65,
      66,     0,     0,     5,    75,    46,     0,    50,    14,     0,
      64,     0,    65,    66,    98,   101,   113,     0,   105,   114,
       0,     0,    99,   108,   109,     0,    76,     0,     0,    32,
       0,     0,     0,     0,    51,    95,    12,     0,     0,    27,
      25,     0,    79,    56,     0,    57,    94,    96,   100,   104,
      29,    61,   106,   107,    97,    82,    84,    86,    83,    87,
       0,     0,    59,    80,    81,     0,   121,     0,    36,    33,
       0,     0,    39,    41,     0,     0,     0,    15,    89,    13,
      31,    74,     0,    85,     0,     0,     0,   119,    74,    35,
       0,    55,     0,    30,    58,   122,    43,    60,   120,    42,
      19,     0,     0,     0,     0,    23,    21,    20,    44,     0,
      22
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -116,  -116,  -116,   163,  -116,   177,  -116,    -8,  -116,  -116,
    -116,  -116,  -116,  -116,    26,   120,    81,  -116,  -116,  -116,
    -115,    99,   133,     2,    16,   -96,  -116,  -116,     8,   -25,
    -116,   121,     0,    33,  -116,  -116,  -116,     3,  -116,  -116,
    -116,  -116,  -116,  -116,  -116,  -116,  -116,  -116,   164,   169,
    -116,   188,   -13,    -6,    74,  -116,    53,  -116
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    74,    14,    15,    16,    17,    18,    36,   167,   193,
      19,    37,    20,    21,   159,    57,    58,    59,   162,   185,
      38,    39,    22,    40,    24,   134,   151,    41,    86,   101,
      88,    25,   135,   152,   153,   154,    66,    56,    28,    70,
      43,   112,    44,    45,    46,    47,    48,    49,   106,   109,
      50,    51,    89,    90,    52,   155,   156,    53
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      26,    87,    23,    27,    64,   163,    29,    42,   171,    55,
      27,    63,    42,    61,    27,    27,    26,    30,    23,    27,
     172,   157,   174,    77,    78,   165,    60,    62,    26,   102,
      23,    27,    69,   107,    65,    96,   103,    95,    27,   107,
     178,    67,   175,   110,   118,     2,   110,     4,     5,   118,
     100,   181,   172,     2,    63,     4,     5,   119,    94,   186,
     111,    73,   170,   172,   127,   189,    75,    98,   176,    61,
     117,     2,    42,     4,     5,    27,   130,    61,    61,   198,
     123,   177,   124,   138,    76,    77,    78,   128,    71,   116,
     139,    60,    72,    13,   160,   195,    76,    77,    78,    42,
      85,   141,    27,   200,   137,   128,     2,   142,     4,     5,
     143,   144,    85,   199,    76,    77,    78,   104,    99,   105,
     164,    61,   108,    27,   115,     2,     3,     4,     5,   120,
      85,    61,    -3,     1,    60,     2,     3,     4,     5,     6,
      31,    32,    33,    34,    62,   160,     8,     9,   133,   121,
     125,     7,   -96,   -96,   -96,   -96,     8,     9,   136,    54,
     179,    10,   122,    95,    61,   166,   182,   168,    81,    11,
      83,   169,   184,    12,   164,    13,    82,    27,    84,   173,
     164,   197,   180,    27,     2,     3,     4,     5,    92,   194,
     172,    93,   196,    68,   164,   131,   183,    27,   140,   158,
       7,  -100,  -100,  -100,  -100,     8,     9,   129,   187,   132,
      10,     2,     3,     4,     5,   -54,   113,   -54,    11,   -54,
     -54,   114,    12,    97,    13,    91,     0,     7,     0,   188,
     -54,     0,     8,     9,     0,     0,     0,    10,   -54,     0,
       0,     0,   -54,     0,     0,    11,     0,     0,     0,    12,
       0,    13,     2,     3,     4,     5,     0,     0,    31,    32,
      33,    34,     0,     0,   126,  -104,  -104,  -104,  -104,     2,
       3,     4,     5,     8,     9,    31,    32,    33,    34,     2,
       3,     4,     5,     0,     0,     0,    11,     0,    35,     0,
       8,     9,     0,     0,     0,    76,    77,    78,     0,     0,
       8,     9,   190,    11,     0,    35,     2,     3,     4,     5,
       0,    85,   191,    11,   192,   161,     2,     3,     4,     5,
       0,     0,    31,    32,    33,    34,     0,     8,     9,     0,
     145,   146,   147,   148,     0,     0,     0,     8,     9,   -55,
      54,   -55,     0,   -55,   -55,     0,     0,     0,     0,     0,
      11,   149,     0,     0,   -55,     0,     0,    76,    77,    78,
       0,     0,   -55,     0,   150,     0,   -55,    79,    80,    81,
      82,    83,    84,    85,    79,    80,    81,    82,    83,    84
};

static const yytype_int16 yycheck[] =
{
       0,    26,     0,     0,    12,   120,    16,     7,    26,     9,
       7,    11,    12,    10,    11,    12,    16,     8,    16,    16,
      38,   117,    18,    22,    23,   121,    10,    11,    28,    42,
      28,    28,    16,    46,     5,    35,    42,    35,    35,    52,
      26,     0,    38,    49,    17,     3,    52,     5,     6,    17,
      42,    26,    38,     3,    54,     5,     6,    30,     4,   174,
      52,    42,    30,    38,    72,   180,    29,    15,    17,    66,
      25,     3,    72,     5,     6,    72,    74,    74,    75,   194,
      38,    30,    66,    96,    21,    22,    23,    37,    15,    26,
      96,    75,    19,    43,   119,   191,    21,    22,    23,    99,
      37,   101,    99,   199,    96,    37,     3,   107,     5,     6,
     110,   111,    37,    38,    21,    22,    23,    43,    38,    45,
     120,   118,    48,   120,    29,     3,     4,     5,     6,    18,
      37,   128,     0,     1,   118,     3,     4,     5,     6,     7,
       9,    10,    11,    12,   128,   170,    24,    25,    26,    25,
      20,    19,     9,    10,    11,    12,    24,    25,     8,    37,
     160,    29,    15,   161,   161,    27,   166,     5,    33,    37,
      35,    15,   172,    41,   174,    43,    34,   174,    36,     4,
     180,    28,    38,   180,     3,     4,     5,     6,     7,    38,
      38,    28,   192,    16,   194,    75,   170,   194,    99,   118,
      19,     9,    10,    11,    12,    24,    25,    74,   175,    88,
      29,     3,     4,     5,     6,    15,    52,    17,    37,    19,
      20,    52,    41,    35,    43,    25,    -1,    19,    -1,   176,
      30,    -1,    24,    25,    -1,    -1,    -1,    29,    38,    -1,
      -1,    -1,    42,    -1,    -1,    37,    -1,    -1,    -1,    41,
      -1,    43,     3,     4,     5,     6,    -1,    -1,     9,    10,
      11,    12,    -1,    -1,    15,     9,    10,    11,    12,     3,
       4,     5,     6,    24,    25,     9,    10,    11,    12,     3,
       4,     5,     6,    -1,    -1,    -1,    37,    -1,    39,    -1,
      24,    25,    -1,    -1,    -1,    21,    22,    23,    -1,    -1,
      24,    25,    28,    37,    -1,    39,     3,     4,     5,     6,
      -1,    37,    38,    37,    40,    39,     3,     4,     5,     6,
      -1,    -1,     9,    10,    11,    12,    -1,    24,    25,    -1,
       3,     4,     5,     6,    -1,    -1,    -1,    24,    25,    15,
      37,    17,    -1,    19,    20,    -1,    -1,    -1,    -1,    -1,
      37,    24,    -1,    -1,    30,    -1,    -1,    21,    22,    23,
      -1,    -1,    38,    -1,    37,    -1,    42,    31,    32,    33,
      34,    35,    36,    37,    31,    32,    33,    34,    35,    36
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,     1,     3,     4,     5,     6,     7,    19,    24,    25,
      29,    37,    41,    43,    46,    47,    48,    49,    50,    54,
      56,    57,    66,    67,    68,    75,    76,    81,    82,    16,
       8,     9,    10,    11,    12,    39,    51,    55,    64,    65,
      67,    71,    76,    84,    86,    87,    88,    89,    90,    91,
      94,    95,    98,   101,    37,    76,    81,    59,    60,    61,
      68,    81,    68,    76,    51,     5,    80,     0,    49,    68,
      83,    15,    19,    42,    45,    29,    21,    22,    23,    31,
      32,    33,    34,    35,    36,    37,    72,    73,    74,    96,
      97,    25,     7,    47,     4,    67,    76,    95,    15,    38,
      72,    73,    96,    97,    98,    98,    92,    96,    98,    93,
      97,    72,    85,    92,    93,    29,    26,    25,    17,    30,
      18,    25,    15,    38,    68,    20,    15,    51,    37,    66,
      67,    59,    75,    26,    69,    76,     8,    72,    96,    97,
      65,    76,    76,    76,    76,     3,     4,     5,     6,    24,
      37,    70,    77,    78,    79,    99,   100,    69,    60,    58,
      73,    39,    62,    64,    76,    69,    27,    52,     5,    15,
      30,    26,    38,     4,    18,    38,    17,    30,    26,    76,
      38,    26,    76,    58,    76,    63,    64,    77,   100,    64,
      28,    38,    40,    53,    38,    69,    76,    28,    64,    38,
      69
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_int8 yyr1[] =
{
       0,    44,    45,    46,    46,    46,    46,    47,    47,    48,
      48,    49,    49,    49,    49,    49,    50,    50,    51,    52,
      52,    53,    53,    53,    54,    54,    54,    54,    55,    55,
      56,    56,    56,    56,    57,    58,    59,    59,    60,    60,
      61,    62,    62,    63,    63,    64,    64,    64,    65,    65,
      65,    66,    67,    67,    68,    68,    68,    69,    69,    70,
      70,    71,    72,    72,    73,    73,    73,    74,    74,    74,
      74,    75,    75,    75,    75,    75,    75,    75,    76,    76,
      77,    77,    78,    78,    78,    78,    79,    79,    80,    80,
      81,    81,    81,    82,    82,    83,    84,    85,    86,    86,
      87,    88,    89,    89,    90,    91,    92,    93,    94,    94,
      95,    95,    95,    95,    95,    96,    96,    97,    97,    98,
      99,    99,   100,   101,   101,   101,   101
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     1,     0,     1,     2,     1,     1,     2,     2,
       1,     2,     3,     4,     3,     4,     1,     1,     1,     3,
       4,     2,     4,     2,     1,     3,     1,     3,     1,     3,
       5,     4,     3,     4,     2,     2,     3,     1,     1,     3,
       1,     1,     3,     1,     3,     1,     2,     1,     1,     1,
       2,     3,     1,     2,     1,     4,     3,     1,     3,     1,
       3,     3,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     4,     3,     3,     2,     1,     3,
       1,     1,     1,     1,     1,     2,     1,     1,     1,     3,
       1,     1,     1,     2,     3,     2,     2,     2,     2,     2,
       2,     2,     1,     1,     2,     2,     2,     2,     2,     2,
       1,     1,     1,     2,     2,     1,     1,     1,     1,     4,
       3,     1,     3,     1,     1,     1,     1
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


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
        yyerror (director, YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



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

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value, director); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo, int yytype, YYSTYPE const * const yyvaluep, DLV2::InputDirector& director)
{
  FILE *yyoutput = yyo;
  YYUSE (yyoutput);
  YYUSE (director);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyo, yytoknum[yytype], *yyvaluep);
# endif
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo, int yytype, YYSTYPE const * const yyvaluep, DLV2::InputDirector& director)
{
  YYFPRINTF (yyo, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyo, yytype, yyvaluep, director);
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
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp, int yyrule, DLV2::InputDirector& director)
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
                       yystos[+yyssp[yyi + 1 - yynrhs]],
                       &yyvsp[(yyi + 1) - (yynrhs)]
                                              , director);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule, director); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
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


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
#  else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            else
              goto append;

          append:
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                yy_state_t *yyssp, int yytoken)
{
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Actual size of YYARG. */
  int yycount = 0;
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[+*yyssp];
      YYPTRDIFF_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
      yysize = yysize0;
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYPTRDIFF_T yysize1
                    = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
                    yysize = yysize1;
                  else
                    return 2;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    /* Don't count the "%s"s in the final size, but reserve room for
       the terminator.  */
    YYPTRDIFF_T yysize1 = yysize + (yystrlen (yyformat) - 2 * yycount) + 1;
    if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
      yysize = yysize1;
    else
      return 2;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, DLV2::InputDirector& director)
{
  YYUSE (yyvaluep);
  YYUSE (director);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (DLV2::InputDirector& director)
{
    yy_state_fast_t yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss;
    yy_state_t *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYPTRDIFF_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
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

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    goto yyexhaustedlab;
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
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
# undef YYSTACK_RELOCATE
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

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex (director);
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
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
  case 6:
#line 72 "aspcore2.y"
            { yyerror(director,"Generic error"); }
#line 1569 "aspcore2.tab.c"
    break;

  case 8:
#line 77 "aspcore2.y"
                  { director.getBuilder()->onQuery(); }
#line 1575 "aspcore2.tab.c"
    break;

  case 11:
#line 87 "aspcore2.y"
        { 
            director.getBuilder()->onRule(); 
        }
#line 1583 "aspcore2.tab.c"
    break;

  case 12:
#line 91 "aspcore2.y"
        {
            director.getBuilder()->onRule(); 
        }
#line 1591 "aspcore2.tab.c"
    break;

  case 13:
#line 95 "aspcore2.y"
        { 
            director.getBuilder()->onRule(); 
        }
#line 1599 "aspcore2.tab.c"
    break;

  case 14:
#line 99 "aspcore2.y"
        { 
            director.getBuilder()->onConstraint(); 
        }
#line 1607 "aspcore2.tab.c"
    break;

  case 15:
#line 103 "aspcore2.y"
        { 
            director.getBuilder()->onWeakConstraint(); 
        }
#line 1615 "aspcore2.tab.c"
    break;

  case 16:
#line 110 "aspcore2.y"
        {
            director.getBuilder()->onHead();
        }
#line 1623 "aspcore2.tab.c"
    break;

  case 17:
#line 114 "aspcore2.y"
        {
            director.getBuilder()->onChoiceAtom();
            director.getBuilder()->onHead();
        }
#line 1632 "aspcore2.tab.c"
    break;

  case 18:
#line 122 "aspcore2.y"
        {
            director.getBuilder()->onBody();
        }
#line 1640 "aspcore2.tab.c"
    break;

  case 19:
#line 129 "aspcore2.y"
        {
            // There is only the weight. No level and terms.
            director.getBuilder()->onWeightAtLevels(1,0,0); 
        }
#line 1649 "aspcore2.tab.c"
    break;

  case 20:
#line 134 "aspcore2.y"
        {
            // There are also a level and/or some terms.
            // The finalization has been postponed to "level_and_terms".
        }
#line 1658 "aspcore2.tab.c"
    break;

  case 21:
#line 142 "aspcore2.y"
        {
            // There is no terms following the level.
            director.getBuilder()->onWeightAtLevels(1,1,0); 
        }
#line 1667 "aspcore2.tab.c"
    break;

  case 22:
#line 147 "aspcore2.y"
        { 
            director.getBuilder()->onWeightAtLevels(1,1,(yyvsp[0].integer)); 
        }
#line 1675 "aspcore2.tab.c"
    break;

  case 23:
#line 151 "aspcore2.y"
        { 
            // The level is omitted.
            // Thus, the first term, recognized as the
            // weight, should be a term of this list.
            director.getBuilder()->onWeightAtLevels(0,0,(yyvsp[0].integer)+1); 
        }
#line 1686 "aspcore2.tab.c"
    break;

  case 24:
#line 161 "aspcore2.y"
        { 
            director.getBuilder()->onHeadAtom(); 
        }
#line 1694 "aspcore2.tab.c"
    break;

  case 25:
#line 165 "aspcore2.y"
        { 
            director.getBuilder()->onHeadAtom(); 
        }
#line 1702 "aspcore2.tab.c"
    break;

  case 26:
#line 169 "aspcore2.y"
        { 
            director.getBuilder()->onHeadAtom(); 
        }
#line 1710 "aspcore2.tab.c"
    break;

  case 27:
#line 173 "aspcore2.y"
        { 
            director.getBuilder()->onHeadAtom(); 
        }
#line 1718 "aspcore2.tab.c"
    break;

  case 28:
#line 180 "aspcore2.y"
        { 
            director.getBuilder()->onBodyLiteral(); 
        }
#line 1726 "aspcore2.tab.c"
    break;

  case 29:
#line 184 "aspcore2.y"
        { 
            director.getBuilder()->onBodyLiteral(); 
        }
#line 1734 "aspcore2.tab.c"
    break;

  case 34:
#line 198 "aspcore2.y"
        { 
            director.getBuilder()->onChoiceLowerGuard();
        }
#line 1742 "aspcore2.tab.c"
    break;

  case 35:
#line 205 "aspcore2.y"
        { 
            director.getBuilder()->onChoiceUpperGuard();
        }
#line 1750 "aspcore2.tab.c"
    break;

  case 38:
#line 217 "aspcore2.y"
        {
            director.getBuilder()->onChoiceElement(); 
        }
#line 1758 "aspcore2.tab.c"
    break;

  case 39:
#line 221 "aspcore2.y"
        {
            director.getBuilder()->onChoiceElement(); 
        }
#line 1766 "aspcore2.tab.c"
    break;

  case 40:
#line 228 "aspcore2.y"
        {
            director.getBuilder()->onChoiceElementAtom(); 
        }
#line 1774 "aspcore2.tab.c"
    break;

  case 41:
#line 235 "aspcore2.y"
        { 
            director.getBuilder()->onChoiceElementLiteral(); 
        }
#line 1782 "aspcore2.tab.c"
    break;

  case 42:
#line 239 "aspcore2.y"
        {
            director.getBuilder()->onChoiceElementLiteral();
        }
#line 1790 "aspcore2.tab.c"
    break;

  case 43:
#line 246 "aspcore2.y"
        {
            director.getBuilder()->onAggregateNafLiteral();
        }
#line 1798 "aspcore2.tab.c"
    break;

  case 44:
#line 250 "aspcore2.y"
        {
            director.getBuilder()->onAggregateNafLiteral();
        }
#line 1806 "aspcore2.tab.c"
    break;

  case 45:
#line 257 "aspcore2.y"
        { 
            director.getBuilder()->onNafLiteral();
        }
#line 1814 "aspcore2.tab.c"
    break;

  case 46:
#line 261 "aspcore2.y"
        { 
            director.getBuilder()->onNafLiteral(true);
        }
#line 1822 "aspcore2.tab.c"
    break;

  case 47:
#line 265 "aspcore2.y"
        {
            director.getBuilder()->onNafLiteral();
        }
#line 1830 "aspcore2.tab.c"
    break;

  case 49:
#line 273 "aspcore2.y"
        {
            director.getBuilder()->onAggregate();
        }
#line 1838 "aspcore2.tab.c"
    break;

  case 50:
#line 277 "aspcore2.y"
        {
            director.getBuilder()->onAggregate(true);
        }
#line 1846 "aspcore2.tab.c"
    break;

  case 51:
#line 284 "aspcore2.y"
        { 
            director.getBuilder()->onExistentialAtom(); 
        }
#line 1854 "aspcore2.tab.c"
    break;

  case 52:
#line 289 "aspcore2.y"
           { director.getBuilder()->onAtom(); }
#line 1860 "aspcore2.tab.c"
    break;

  case 53:
#line 290 "aspcore2.y"
                { director.getBuilder()->onAtom(true); }
#line 1866 "aspcore2.tab.c"
    break;

  case 54:
#line 295 "aspcore2.y"
        { 
            director.getBuilder()->onPredicateName((yyvsp[0].string)); 
            delete[] (yyvsp[0].string);
        }
#line 1875 "aspcore2.tab.c"
    break;

  case 55:
#line 300 "aspcore2.y"
        { 
            director.getBuilder()->onPredicateName((yyvsp[-3].string)); 
            delete[] (yyvsp[-3].string);
        }
#line 1884 "aspcore2.tab.c"
    break;

  case 56:
#line 305 "aspcore2.y"
        { 
            director.getBuilder()->onPredicateName((yyvsp[-2].string)); 
            delete[] (yyvsp[-2].string);
        }
#line 1893 "aspcore2.tab.c"
    break;

  case 57:
#line 312 "aspcore2.y"
           { (yyval.integer) = 1; }
#line 1899 "aspcore2.tab.c"
    break;

  case 58:
#line 313 "aspcore2.y"
                       { (yyval.integer) = (yyvsp[-2].integer) + 1; }
#line 1905 "aspcore2.tab.c"
    break;

  case 61:
#line 323 "aspcore2.y"
        {
            director.getBuilder()->onBuiltinAtom();
        }
#line 1913 "aspcore2.tab.c"
    break;

  case 62:
#line 330 "aspcore2.y"
        {
            director.getBuilder()->onEqualOperator();
        }
#line 1921 "aspcore2.tab.c"
    break;

  case 63:
#line 334 "aspcore2.y"
        {
            director.getBuilder()->onUnequalOperator(); 
        }
#line 1929 "aspcore2.tab.c"
    break;

  case 67:
#line 346 "aspcore2.y"
            { (yyval.single_char) = '+'; }
#line 1935 "aspcore2.tab.c"
    break;

  case 68:
#line 347 "aspcore2.y"
            { (yyval.single_char) = '-'; }
#line 1941 "aspcore2.tab.c"
    break;

  case 69:
#line 348 "aspcore2.y"
            { (yyval.single_char) = '*'; }
#line 1947 "aspcore2.tab.c"
    break;

  case 70:
#line 349 "aspcore2.y"
            { (yyval.single_char) = '/'; }
#line 1953 "aspcore2.tab.c"
    break;

  case 71:
#line 354 "aspcore2.y"
        { 
            director.getBuilder()->onTerm((yyvsp[0].string)); 
            delete[] (yyvsp[0].string);
        }
#line 1962 "aspcore2.tab.c"
    break;

  case 72:
#line 359 "aspcore2.y"
        { 
//            director.getBuilder()->onTerm($1); 
//            delete[] $1;
        }
#line 1971 "aspcore2.tab.c"
    break;

  case 73:
#line 364 "aspcore2.y"
        { 
            director.getBuilder()->onUnknownVariable(); 
        }
#line 1979 "aspcore2.tab.c"
    break;

  case 74:
#line 368 "aspcore2.y"
        { 
            director.getBuilder()->onFunction((yyvsp[-3].string), (yyvsp[-1].integer)); 
            delete[] (yyvsp[-3].string);
        }
#line 1988 "aspcore2.tab.c"
    break;

  case 75:
#line 373 "aspcore2.y"
        {
            director.getParserConstraint()->rangeFacts();
            director.getBuilder()->onTermRange((yyvsp[-2].string), (yyvsp[0].string));
            delete[] (yyvsp[-2].string);
            delete[] (yyvsp[0].string);
        }
#line 1999 "aspcore2.tab.c"
    break;

  case 76:
#line 380 "aspcore2.y"
        { 
            director.getBuilder()->onTermParams(); 
        }
#line 2007 "aspcore2.tab.c"
    break;

  case 77:
#line 384 "aspcore2.y"
        { 
            director.getBuilder()->onTermDash(); 
        }
#line 2015 "aspcore2.tab.c"
    break;

  case 78:
#line 390 "aspcore2.y"
            {}
#line 2021 "aspcore2.tab.c"
    break;

  case 79:
#line 392 "aspcore2.y"
        { 
            director.getBuilder()->onArithmeticOperation((yyvsp[-1].single_char)); 
        }
#line 2029 "aspcore2.tab.c"
    break;

  case 80:
#line 397 "aspcore2.y"
                         {}
#line 2035 "aspcore2.tab.c"
    break;

  case 81:
#line 398 "aspcore2.y"
                       {}
#line 2041 "aspcore2.tab.c"
    break;

  case 82:
#line 403 "aspcore2.y"
        {
            director.getBuilder()->onAggregateGroundTerm((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2050 "aspcore2.tab.c"
    break;

  case 83:
#line 408 "aspcore2.y"
        {
            director.getBuilder()->onAggregateGroundTerm((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2059 "aspcore2.tab.c"
    break;

  case 84:
#line 413 "aspcore2.y"
        {
            director.getBuilder()->onAggregateGroundTerm((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2068 "aspcore2.tab.c"
    break;

  case 85:
#line 418 "aspcore2.y"
        {
            director.getBuilder()->onAggregateGroundTerm((yyvsp[0].string),true);
            delete[] (yyvsp[0].string);
        }
#line 2077 "aspcore2.tab.c"
    break;

  case 86:
#line 426 "aspcore2.y"
        { 
            director.getBuilder()->onAggregateVariableTerm((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2086 "aspcore2.tab.c"
    break;

  case 87:
#line 431 "aspcore2.y"
        {
            director.getBuilder()->onAggregateUnknownVariable();
        }
#line 2094 "aspcore2.tab.c"
    break;

  case 88:
#line 438 "aspcore2.y"
        { 
            director.getBuilder()->onExistentialVariable((yyvsp[0].string)); 
            delete[] (yyvsp[0].string);
        }
#line 2103 "aspcore2.tab.c"
    break;

  case 89:
#line 443 "aspcore2.y"
        { 
            director.getBuilder()->onExistentialVariable((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2112 "aspcore2.tab.c"
    break;

  case 90:
#line 450 "aspcore2.y"
                        { (yyval.string) = (yyvsp[0].string); }
#line 2118 "aspcore2.tab.c"
    break;

  case 91:
#line 451 "aspcore2.y"
             { (yyval.string) = (yyvsp[0].string); }
#line 2124 "aspcore2.tab.c"
    break;

  case 92:
#line 452 "aspcore2.y"
               { (yyval.string) = (yyvsp[0].string); }
#line 2130 "aspcore2.tab.c"
    break;

  case 93:
#line 457 "aspcore2.y"
        {
            director.getParserConstraint()->directives();
            director.getBuilder()->onDirective((yyvsp[-1].string),(yyvsp[0].string));
            delete[] (yyvsp[-1].string);
            delete[] (yyvsp[0].string);
        }
#line 2141 "aspcore2.tab.c"
    break;

  case 94:
#line 464 "aspcore2.y"
        {
            director.getParserConstraint()->directives();
            director.getBuilder()->onDirective((yyvsp[-1].string),(yyvsp[0].string));
            delete[] (yyvsp[-1].string);
            delete[] (yyvsp[0].string);
        }
#line 2152 "aspcore2.tab.c"
    break;

  case 95:
#line 474 "aspcore2.y"
        { 
            director.getBuilder()->onAtom(); 
        }
#line 2160 "aspcore2.tab.c"
    break;

  case 96:
#line 481 "aspcore2.y"
        {
            director.getBuilder()->onAggregateLowerGuard();
        }
#line 2168 "aspcore2.tab.c"
    break;

  case 97:
#line 488 "aspcore2.y"
        {
            director.getBuilder()->onAggregateUpperGuard();
        }
#line 2176 "aspcore2.tab.c"
    break;

  case 100:
#line 500 "aspcore2.y"
        {
            director.getBuilder()->onAggregateLowerGuard();
        }
#line 2184 "aspcore2.tab.c"
    break;

  case 104:
#line 516 "aspcore2.y"
        {
            director.getBuilder()->onAggregateLowerGuard();
        }
#line 2192 "aspcore2.tab.c"
    break;

  case 106:
#line 527 "aspcore2.y"
        {
            director.getBuilder()->onAggregateUpperGuard();
        }
#line 2200 "aspcore2.tab.c"
    break;

  case 107:
#line 534 "aspcore2.y"
        {
            director.getBuilder()->onAggregateUpperGuard();
        }
#line 2208 "aspcore2.tab.c"
    break;

  case 115:
#line 554 "aspcore2.y"
        {
            director.getBuilder()->onLessOperator(); 
        }
#line 2216 "aspcore2.tab.c"
    break;

  case 116:
#line 558 "aspcore2.y"
        {
            director.getBuilder()->onLessOrEqualOperator(); 
        }
#line 2224 "aspcore2.tab.c"
    break;

  case 117:
#line 565 "aspcore2.y"
        {
            director.getBuilder()->onGreaterOperator();
        }
#line 2232 "aspcore2.tab.c"
    break;

  case 118:
#line 569 "aspcore2.y"
        {
            director.getBuilder()->onGreaterOrEqualOperator();
        }
#line 2240 "aspcore2.tab.c"
    break;

  case 122:
#line 586 "aspcore2.y"
        {
            director.getBuilder()->onAggregateElement();
        }
#line 2248 "aspcore2.tab.c"
    break;

  case 123:
#line 593 "aspcore2.y"
        {
            director.getBuilder()->onAggregateFunction((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2257 "aspcore2.tab.c"
    break;

  case 124:
#line 598 "aspcore2.y"
        {
            director.getBuilder()->onAggregateFunction((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2266 "aspcore2.tab.c"
    break;

  case 125:
#line 603 "aspcore2.y"
        {
            director.getBuilder()->onAggregateFunction((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2275 "aspcore2.tab.c"
    break;

  case 126:
#line 608 "aspcore2.y"
        {
            director.getBuilder()->onAggregateFunction((yyvsp[0].string));
            delete[] (yyvsp[0].string);
        }
#line 2284 "aspcore2.tab.c"
    break;


#line 2288 "aspcore2.tab.c"

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
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

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
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (director, YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *, YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (director, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
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
                      yytoken, &yylval, director);
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

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
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
                  yystos[yystate], yyvsp, director);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;


#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (director, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif


/*-----------------------------------------------------.
| yyreturn -- parsing is finished, return the result.  |
`-----------------------------------------------------*/
yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, director);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[+*yyssp], yyvsp, director);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
