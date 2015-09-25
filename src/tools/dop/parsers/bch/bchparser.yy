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
#include "common/Global.h"
#include "egraph/Egraph.h"
#include "sorts/SStore.h"
#include "api/OpenSMTContext.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <vector>
#include <string>
#include <unordered_map>
#include <utility>
#include <list>
#include <limits>

using std::list;
using std::pair;
using std::vector;
using std::string;
using std::unordered_map;
using std::stod;
using std::numeric_limits;

extern int bchlineno;
extern int bchlex( );

// ===========
// The result
// ===========
OpenSMTContext * bch_ctx;
bool bch_minimize; // true if minimize, false if maximize
vector<Enode*> bch_ctrs;
vector<Enode*> bch_costs;
unordered_map<string, Enode*> bch_var_map;

vector< string > * createNumeralList  ( const char * );
vector< string > * pushNumeralList    ( vector< string > *, const char * );
void               destroyNumeralList ( vector< string > * );

list< Snode * > * createSortList  ( Snode * );
list< Snode * > * pushSortList    ( list< Snode * > *, Snode * );
void              destroySortList ( list< Snode * > * );

void bcherror( const char * s )
{
  printf( "At line %d: %s\n", bchlineno, s );
  exit( 1 );
}

void bch_init_parser() {
    bch_ctx = new OpenSMTContext();
    bch_ctx->SetLogic(QF_NRA);
}

void bch_cleanup_parser() {
    delete bch_ctx;
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

%token TK_CONSTANTS TK_CONSTRAINTS TK_END TK_VARIABLES TK_IN TK_MINIMIZE TK_INFINITY TK_NINFINITY
%token TK_COMMA TK_COLON TK_SEMICOLON TK_PLUS TK_MINUS TK_TIMES TK_DIV TK_EQ TK_NEQ TK_LEQ TK_GEQ
%token TK_LT TK_GT TK_SIN TK_COS TK_TAN TK_EXP TK_LOG TK_ABS TK_ASIN TK_ACOS TK_ATAN TK_SINH TK_COSH TK_TANH TK_MIN
%token TK_MAX TK_ATAN2 TK_MATAN TK_SQRT TK_SAFESQRT TK_POW
%token TK_LC TK_RC TK_LP TK_RP TK_LB TK_RB TK_OR TK_AND
%token TK_NUM TK_STR TK_ID

%type   <str>           TK_NUM TK_ID TK_STR
%type   <enode>         exp formula var_decl ctr_decl cost_decl
%type   <fp>            numeral

%left TK_AND TK_OR
%nonassoc TK_EQ TK_NEQ TK_LT TK_LEQ TK_GT TK_GEQ
%left TK_PLUS TK_MINUS
%left TK_TIMES TK_DIV
%nonassoc UMINUS
%right TK_POW

%start script

%%

script:
                opt_constant_decl_sec
                var_decl_sec
                cost_decl_sec
                opt_ctr_decl_sec
                opt_end
        ;

opt_end:        /* nothing */
        |       TK_END
        ;

numeral:        TK_NUM {
                    $$ = stod($1, nullptr);
                    free($1);
        }
        |       TK_PLUS TK_NUM {
                    $$ = stod($2, nullptr);
                    free($2);
        }
        |       TK_MINUS TK_NUM {
                    $$ = -stod($2, nullptr);
                    free($2);
        }
        |       TK_INFINITY {
                    $$ = numeric_limits<double>::infinity();
        }
        |       TK_NINFINITY {
                    $$ = -numeric_limits<double>::infinity();
        }
        ;

// =============================
// Constants
// =============================

constant_decl:  TK_ID TK_EQ TK_LB numeral TK_COMMA numeral TK_RB TK_SEMICOLON {
                    double const lb = $4;
                    double const ub = $6;
                    bch_ctx->DeclareFun($1, bch_ctx->mkSortReal());
                    Enode * e = bch_ctx->mkVar($1, true);
                    e->setDomainLowerBound(lb);
                    e->setDomainUpperBound(ub);
                    bch_var_map.emplace($1, e);
                    free($1);
        }
        |       TK_ID TK_EQ numeral TK_SEMICOLON {
                    double const v = $3;
                    bch_ctx->DeclareFun($1, bch_ctx->mkSortReal());
                    Enode * e = bch_ctx->mkVar($1, true);
                    e->setDomainLowerBound(v);
                    e->setDomainUpperBound(v);
                    bch_var_map.emplace($1, e);
                    free($1);
        }
        ;

constant_decl_list:
                constant_decl
        |       constant_decl constant_decl_list
        ;

opt_constant_decl_sec:
                 /* nothing */
        |       constant_decl_sec
        ;

constant_decl_sec:
                TK_CONSTANTS constant_decl_list
        |       TK_CONSTANTS
        ;

// =============================
// Variable Declaration Section
// =============================
var_decl:       TK_ID TK_IN TK_LB numeral TK_COMMA numeral TK_RB TK_SEMICOLON {
                    double const lb = $4;
                    double const ub = $6;
                    bch_ctx->DeclareFun($1, bch_ctx->mkSortReal());
                    Enode * e = bch_ctx->mkVar($1, true);
                    e->setDomainLowerBound(lb);
                    e->setDomainUpperBound(ub);
                    bch_var_map.emplace($1, e);
                    free($1);
        }
        ;

var_decl_list:  var_decl
        |       var_decl var_decl_list
        ;

var_decl_sec:   TK_VARIABLES var_decl_list
        ;

// =============================
// Cost Function
// =============================
cost_decl:      exp TK_SEMICOLON {
                    bch_costs.push_back($1);
        }
        ;
cost_decl_sec:   TK_MINIMIZE cost_decl
        ;

// =============================
// Constraints
// =============================

ctr_decl:        formula TK_SEMICOLON {
                     $$ = $1;
        }
        ;

ctr_decl_list:   ctr_decl {
                    bch_ctrs.push_back($1);
        }
        |       ctr_decl ctr_decl_list {
                    bch_ctrs.push_back($1);
        }
        ;

opt_ctr_decl_sec:
                /* nothing */
        |       ctr_decl_sec
        ;

ctr_decl_sec:
                TK_CONSTRAINTS ctr_decl_list
        ;

// =============================
// Expression
// =============================
exp:            TK_NUM          { $$ = bch_ctx->mkNum($1); free($1); }
        |       TK_ID           { $$ = bch_ctx->mkVar($1); free($1); }
        |       TK_LP exp TK_RP { $$ = $2; }
        |       TK_MINUS exp %prec UMINUS { $$ = bch_ctx->mkUminus(bch_ctx->mkCons($2)); }
        |       exp TK_PLUS exp {
            $$ = bch_ctx->mkPlus(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: +");
            }
        }
        |       exp TK_MINUS exp {
            $$ = bch_ctx->mkMinus(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: -");
            }
        }
        |       exp TK_TIMES exp {
            $$ = bch_ctx->mkTimes(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: *");
            }
        }
        |       exp TK_DIV exp {
            $$ = bch_ctx->mkDiv(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: /");
            }
        }
        |       exp TK_POW exp {
            $$ = bch_ctx->mkPow(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: ^(pow)");
            }
        }
        |       TK_ABS TK_LP exp TK_RP {
            $$ = bch_ctx->mkAbs(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: abs");
            }
        }
        |       TK_LOG TK_LP exp TK_RP {
            $$ = bch_ctx->mkLog(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: log");
            }
        }
        |       TK_EXP TK_LP exp TK_RP {
            $$ = bch_ctx->mkExp(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: exp");
            }
        }
        |       TK_SQRT TK_LP exp TK_RP {
            $$ = bch_ctx->mkSqrt(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sqrt");
            }
        }
        |       TK_SIN TK_LP exp TK_RP {
            $$ = bch_ctx->mkSin(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sin");
            }
                }
        |       TK_COS TK_LP exp TK_RP {
            $$ = bch_ctx->mkCos(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: cos");
            }
        }
        |       TK_TAN TK_LP exp TK_RP {
            $$ = bch_ctx->mkTan(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: tan");
            }
        }
        |       TK_SINH TK_LP exp TK_RP {
            $$ = bch_ctx->mkSinh(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sinh");
            }
        }
        |       TK_COSH TK_LP exp TK_RP {
            $$ = bch_ctx->mkCosh(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: cosh");
            }
        }
        |       TK_TANH TK_LP exp TK_RP {
            $$ = bch_ctx->mkTanh(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: tanh");
            }
        }
        |       TK_ASIN TK_LP exp TK_RP {
            $$ = bch_ctx->mkAsin(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: asin");
            }
        }
        |       TK_ACOS TK_LP exp TK_RP {
            $$ = bch_ctx->mkAcos(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: acos");
            }
        }
        |       TK_ATAN TK_LP exp TK_RP {
            $$ = bch_ctx->mkAtan(bch_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: atan");
            }
        }
        |       TK_ATAN2 TK_LP exp ',' exp TK_RP {
            $$ = bch_ctx->mkAtan2(bch_ctx->mkCons($3, bch_ctx->mkCons($5)));
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
                    $$ = bch_ctx->mkEq(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: =");
                    }
        }
        |       exp TK_NEQ exp {
                    $$ = bch_ctx->mkEq(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
                    $$ = bch_ctx->mkNot(bch_ctx->mkCons($1));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: !=");
                    }        }
        |       exp TK_GT exp {
                    $$ = bch_ctx->mkGt(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: >");
                    }        }
        |       exp TK_LT exp {
                    $$ = bch_ctx->mkLt(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: <");
                    }        }
        |       exp TK_GEQ exp {
                    $$ = bch_ctx->mkGeq(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: >=");
                    }        }
        |       exp TK_LEQ exp {
                    $$ = bch_ctx->mkLeq(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: <=");
                    }        }
        |       formula TK_OR formula {
                    $$ = bch_ctx->mkOr(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: or");
                    }
        }
        |       formula TK_AND formula {
                    $$ = bch_ctx->mkAnd(bch_ctx->mkCons($1, bch_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: and");
                    }
        }
        ;
