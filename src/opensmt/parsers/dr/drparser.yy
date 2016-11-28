/*********************************************************************
Author: Sicun Gao <sicung@mit.edu>

dReal -- Copyright (C) 2013 - 2016, the dReal Team

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
#include <cassert>
#include <vector>
#include <utility>
#include <string>
#include <list>
#include <limits>

#include "common/Global.h"
#include "egraph/Egraph.h"
#include "egraph/Enode.h"
#include "sorts/SStore.h"
#include "api/OpenSMTContext.h"
#include "util/enode_utils.h"

using std::vector;
using std::unordered_map;
using std::string;
using std::list;
using std::stod;
using std::numeric_limits;

extern int drlineno;
extern int drlex();

extern OpenSMTContext * parser_ctx;

void drerror( const char * s )
{
  printf( "At line %d: %s\n", drlineno, s );
  exit( 1 );
}

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024
%}

%union
{
    char  *                  str;
    Enode *                  enode;
    double                   fp;
}

%error-verbose

%token TK_VAR TK_COST TK_PREC TK_CTR
%token TK_COMMA TK_COLON TK_SEMICOLON TK_PLUS TK_MINUS TK_TIMES TK_DIV TK_EQ TK_NEQ TK_LEQ TK_GEQ
%token TK_LT TK_GT TK_SIN TK_COS TK_TAN TK_EXP TK_LOG TK_ABS TK_ASIN TK_ACOS TK_ATAN TK_SINH TK_COSH TK_TANH TK_MIN
%token TK_MAX TK_ATAN2 TK_MATAN TK_SQRT TK_SAFESQRT TK_POW
%token TK_LC TK_RC TK_LP TK_RP TK_LB TK_RB TK_OR TK_AND TK_IMPLIES TK_NOT TK_FORALL
%token TK_NUM TK_STR TK_ID

%type   <str>           TK_NUM TK_ID TK_STR
%type   <enode>         exp formula var_decl ctr_decl
%type   <fp>            numeral

%left TK_AND TK_OR TK_IMPLIES
%nonassoc TK_EQ TK_NEQ TK_LT TK_LEQ TK_GT TK_GEQ
%left TK_PLUS TK_MINUS
%left TK_TIMES TK_DIV
%nonassoc UMINUS
%right TK_POW

%start script

%%

script:         opt_prec_decl_sec
                var_decl_sec
                opt_ctr_decl_sec
        ;

numeral:        TK_NUM {
                    $$ = stod($1, nullptr);
                    free($1);
        }
        |       TK_MINUS TK_NUM {
                    $$ = -stod($2, nullptr);
                    free($2);
        }
        ;

// =============================
// Variable Declaration Section
// =============================

opt_prec_decl_sec:
                /* nothing */
        {
            parser_ctx->SetLogic("QF_NRA");
        }
        |       prec_decl_sec
        ;
prec_decl_sec:  TK_PREC TK_COLON numeral {
        }
        ;

var_decl:       TK_LB numeral TK_COMMA numeral TK_RB TK_ID TK_SEMICOLON {
                    double const lb = $2;
                    double const ub = $4;
                    parser_ctx->DeclareFun($6, parser_ctx->mkSortReal());
                    Enode * e = parser_ctx->mkVar($6, true);
                    e->setDomainLowerBound(lb);
                    e->setDomainUpperBound(ub);
                    free($6);
        }
        | TK_FORALL TK_LB numeral TK_COMMA numeral TK_RB TK_ID TK_SEMICOLON {
                    double const lb = $3;
                    double const ub = $5;
                    parser_ctx->DeclareFun($7, parser_ctx->mkSortReal());
                    Enode * e = parser_ctx->mkVar($7, true);
                    e->setForallVar();
                    e->setDomainLowerBound(lb);
                    e->setDomainUpperBound(ub);
                    free($7);
        }
        |       numeral TK_ID TK_SEMICOLON {
                    double const c = $1;
                    parser_ctx->DeclareFun($2, parser_ctx->mkSortReal());
                    Enode * e = parser_ctx->mkVar($2, true);
                    e->setDomainLowerBound(c);
                    e->setDomainUpperBound(c);
                    e->setValueLowerBound(c);
                    e->setValueUpperBound(c);
                    free($2);
        }
        ;

var_decl_list:  var_decl
        |       var_decl var_decl_list
        ;

var_decl_sec:   TK_VAR TK_COLON var_decl_list
        ;

// =============================
// Constraints
// =============================

ctr_decl:        formula TK_SEMICOLON {
                     $$ = $1;
        }
        ;

ctr_decl_list:   ctr_decl {
                    Enode * const e = dreal::wrap_enode_including_forall_vars(parser_ctx, $1);
                    parser_ctx->addAssert(e);
        }
        |       ctr_decl ctr_decl_list {
                    Enode * const e = dreal::wrap_enode_including_forall_vars(parser_ctx, $1);
                    parser_ctx->addAssert(e);
        }
        ;

opt_ctr_decl_sec:
                /* nothing */
        |       ctr_decl_sec
        ;

ctr_decl_sec:
                TK_CTR TK_COLON ctr_decl_list {
          parser_ctx->addCheckSAT();
          parser_ctx->addExit();
  }
        ;

// =============================
// Expression
// =============================
exp:            TK_NUM          { $$ = parser_ctx->mkNum($1); free($1); }
        |       TK_ID           { $$ = parser_ctx->mkVar($1); free($1); }
        |       TK_LP exp TK_RP { $$ = $2; }
        |       TK_MINUS exp %prec UMINUS { $$ = parser_ctx->mkUminus(parser_ctx->mkCons($2)); }
        |       exp TK_PLUS exp {
            $$ = parser_ctx->mkPlus(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: +");
            }
        }
        |       exp TK_MINUS exp {
            $$ = parser_ctx->mkMinus(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: -");
            }
        }
        |       exp TK_TIMES exp {
            $$ = parser_ctx->mkTimes(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: *");
            }
        }
        |       exp TK_DIV exp {
            $$ = parser_ctx->mkDiv(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: /");
            }
        }
        |       exp TK_POW exp {
            $$ = parser_ctx->mkPow(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: ^(pow)");
            }
        }
        |       TK_ABS TK_LP exp TK_RP {
            $$ = parser_ctx->mkAbs(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: abs");
            }
        }
        |       TK_LOG TK_LP exp TK_RP {
            $$ = parser_ctx->mkLog(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: log");
            }
        }
        |       TK_EXP TK_LP exp TK_RP {
            $$ = parser_ctx->mkExp(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: exp");
            }
        }
        |       TK_SQRT TK_LP exp TK_RP {
            $$ = parser_ctx->mkSqrt(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sqrt");
            }
        }
        |       TK_SIN TK_LP exp TK_RP {
            $$ = parser_ctx->mkSin(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sin");
            }
                }
        |       TK_COS TK_LP exp TK_RP {
            $$ = parser_ctx->mkCos(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: cos");
            }
        }
        |       TK_TAN TK_LP exp TK_RP {
            $$ = parser_ctx->mkTan(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: tan");
            }
        }
        |       TK_SINH TK_LP exp TK_RP {
            $$ = parser_ctx->mkSinh(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sinh");
            }
        }
        |       TK_COSH TK_LP exp TK_RP {
            $$ = parser_ctx->mkCosh(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: cosh");
            }
        }
        |       TK_TANH TK_LP exp TK_RP {
            $$ = parser_ctx->mkTanh(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: tanh");
            }
        }
        |       TK_ASIN TK_LP exp TK_RP {
            $$ = parser_ctx->mkAsin(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: asin");
            }
        }
        |       TK_ACOS TK_LP exp TK_RP {
            $$ = parser_ctx->mkAcos(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: acos");
            }
        }
        |       TK_ATAN TK_LP exp TK_RP {
            $$ = parser_ctx->mkAtan(parser_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: atan");
            }
        }
        |       TK_ATAN2 TK_LP exp ',' exp TK_RP {
            $$ = parser_ctx->mkAtan2(parser_ctx->mkCons($3, parser_ctx->mkCons($5)));
            if ($$ == nullptr) {
                yyerror("Parse Error: atan2");
            }
        }
;

// =============================
// Formula
// =============================

formula:        TK_LP formula TK_RP { $$ = $2; }
        |       exp TK_EQ exp {
                    $$ = parser_ctx->mkEq(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: =");
                    }
        }
        |       exp TK_NEQ exp {
                    $$ = parser_ctx->mkEq(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    $$ = parser_ctx->mkNot(parser_ctx->mkCons($1));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: !=");
                    }        }
        |       exp TK_GT exp {
                    $$ = parser_ctx->mkGt(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: >");
                    }        }
        |       exp TK_LT exp {
                    $$ = parser_ctx->mkLt(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: <");
                    }        }
        |       exp TK_GEQ exp {
                    $$ = parser_ctx->mkGeq(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: >=");
                    }        }
        |       exp TK_LEQ exp {
                    $$ = parser_ctx->mkLeq(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: <=");
                    }        }
        |       formula TK_OR formula {
                    $$ = parser_ctx->mkOr(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: or");
                    }
        }
        |       formula TK_AND formula {
                    $$ = parser_ctx->mkAnd(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: and");
                    }
        }
      |       formula TK_IMPLIES formula {
                    $$ = parser_ctx->mkImplies(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: and");
                    }
        }
        ;
