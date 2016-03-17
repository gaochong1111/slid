/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

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

#ifndef YY_YY_HOME_JACK_SPACE_SLIB_SLID_LIBVATA_BUILD_SRC_TIMBUK_Y_HH_INCLUDED
# define YY_YY_HOME_JACK_SPACE_SLIB_SLID_LIBVATA_BUILD_SRC_TIMBUK_Y_HH_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif
/* "%code requires" blocks.  */
#line 13 "timbuk.y" /* yacc.c:1909  */

// VATA headers
#include <vata/parsing/timbuk_parser.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/convert.hh>

// standard library headers
#include <algorithm>

GCC_DIAG_OFF(write-strings)

//#define YYDEBUG 1

int yylex();
extern int yylineno;

using VATA::Util::Convert;
using VATA::Util::AutDescription;

inline void yyerror(AutDescription&, const char* msg)
{
  throw std::runtime_error("Parser error at line " +
    Convert::ToString(yylineno) + ": " + std::string(msg));
}

static AutDescription::StateTuple global_tuple;

#line 72 "/home/jack/space/slib/slid/libvata/build/src/timbuk.y.hh" /* yacc.c:1909  */

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    END_OF_FILE = 0,
    OPERATIONS = 258,
    AUTOMATON = 259,
    STATES = 260,
    FINAL_STATES = 261,
    TRANSITIONS = 262,
    NUMBER = 263,
    IDENTIFIER = 264,
    COLON = 265,
    LPAR = 266,
    RPAR = 267,
    ARROW = 268,
    COMMA = 269
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

union YYSTYPE
{
#line 64 "timbuk.y" /* yacc.c:1909  */

  char* svalue;

#line 104 "/home/jack/space/slib/slid/libvata/build/src/timbuk.y.hh" /* yacc.c:1909  */
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


extern YYSTYPE yylval;
extern YYLTYPE yylloc;
int yyparse (AutDescription& timbukParse);

#endif /* !YY_YY_HOME_JACK_SPACE_SLIB_SLID_LIBVATA_BUILD_SRC_TIMBUK_Y_HH_INCLUDED  */
