/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

%{

#include <cstdio>
#include <cstdlib>
/* Keep the following headers in their original order */
#include "egraph/Egraph.h"
#include "dopparser.hh"

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-register"
#pragma clang diagnostic ignored "-Wnull-conversion"
#pragma clang diagnostic ignored "-Wunneeded-internal-declaration"
#endif
%}

%x start_comment
%option noyywrap
%option yylineno
%option nounput

%%

[ \t\n\r]                    { }
"#".*                        { }
"var"                        { return TK_VAR; }
"cost"                       { return TK_COST; }
"prec"                       { return TK_PREC; }
"ctr"                        { return TK_CTR; }

","                          { return TK_COMMA; }
":"                          { return TK_COLON; }
";"                          { return TK_SEMICOLON; }
"+"                          { return TK_PLUS; }
"-"                          { return TK_MINUS; }
"*"                          { return TK_TIMES; }
"/"                          { return TK_DIV; }
"="                          { return TK_EQ; }
"!="                         { return TK_NEQ; }
"<="                         { return TK_LEQ; }
">="                         { return TK_GEQ; }
"<"                          { return TK_LT; }
">"                          { return TK_GT; }
"("                          { return TK_LP; }
")"                          { return TK_RP; }
"{"                          { return TK_LC; }
"}"                          { return TK_RC; }
"["                          { return TK_LB; }
"]"                          { return TK_RB; }
"||"                         { return TK_OR; }
"&&"                         { return TK_AND; }
"sin"                        { return TK_SIN; }
"cos"                        { return TK_COS; }
"tan"                        { return TK_TAN; }
"exp"                        { return TK_EXP; }
"log"                        { return TK_LOG; }
"abs"                        { return TK_ABS; }
"asin"|"arcsin"              { return TK_ASIN; }
"acos"|"arccos"              { return TK_ACOS; }
"atan"|"arctan"              { return TK_ATAN; }
"sinh"                       { return TK_SINH; }
"cosh"                       { return TK_COSH; }
"tanh"                       { return TK_TANH; }
"min"                        { return TK_MIN; }
"max"                        { return TK_MAX; }
"atan2"|"arctan2"            { return TK_ATAN2; }
"matan"|"marctan"            { return TK_MATAN; }
"sqrt"                       { return TK_SQRT; }
"safesqrt"                   { return TK_SAFESQRT; }
"^"|"pow"                    { return TK_POW; }

((([0-9]+)|([0-9]*\.?[0-9]+))([eE][-+]?[0-9]+)?)   { doplval.str = strdup(yytext); return TK_NUM; }
((([0-9]+)|([0-9]+\.)))                            { doplval.str = strdup(yytext); return TK_NUM; }
[a-zA-Z]([a-zA-Z0-9_])*                            { doplval.str = strdup(yytext); return TK_ID; }

\".*\"          { doplval.str = strdup( yytext ); return TK_STR; }
.               { printf( "Syntax error at line %d near %s\n", yylineno, yytext ); exit( 1 ); }

%%

#ifdef __clang__
#pragma clang diagnostic pop
#endif
