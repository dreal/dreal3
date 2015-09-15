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
#include <utility>

extern int doplineno;
extern int doplex( );

// ===========
// The result
// ===========
OpenSMTContext * dop_ctx;
bool dop_minimize; // true if minimize, false if maximize
double dop_prec; // true if minimize, false if maximize
std::vector<Enode*> dop_ctrs;
std::vector<Enode*> dop_costs;
std::unordered_map<string, Enode*> dop_var_map;

vector< string > * createNumeralList  ( const char * );
vector< string > * pushNumeralList    ( vector< string > *, const char * );
void               destroyNumeralList ( vector< string > * );

list< Snode * > * createSortList  ( Snode * );
list< Snode * > * pushSortList    ( list< Snode * > *, Snode * );
void              destroySortList ( list< Snode * > * );

void doperror( const char * s )
{
  printf( "At line %d: %s\n", doplineno, s );
  exit( 1 );
}

void dop_init_parser() {
    dop_ctx = new OpenSMTContext();
    dop_ctx->SetLogic(QF_NRA);
    dop_prec = 0.0;
}

void dop_cleanup_parser() {
    delete dop_ctx;
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

script:         opt_prec_decl_sec
                var_decl_sec
                cost_decl_sec
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
        |       prec_decl_sec
        ;
prec_decl_sec:  TK_PREC TK_COLON numeral {
                    dop_prec = $3;
        }
        ;

var_decl:       TK_LB numeral TK_COMMA numeral TK_RB TK_ID TK_SEMICOLON {
                    double const lb = $2;
                    double const ub = $4;
                    dop_ctx->DeclareFun($6, dop_ctx->mkSortReal());
                    Enode * e = dop_ctx->mkVar($6, true);
                    e->setDomainLowerBound(lb);
                    e->setDomainUpperBound(ub);
                    dop_var_map.emplace($6, e);
                    free($6);
        }
        |       numeral TK_ID TK_SEMICOLON {
                    double const c = $1;
                    dop_ctx->DeclareFun($2, dop_ctx->mkSortReal());
                    Enode * e = dop_ctx->mkVar($2, true);
                    e->setDomainLowerBound(c);
                    e->setDomainUpperBound(c);
                    e->setValueLowerBound(c);
                    e->setValueUpperBound(c);
                    dop_var_map.emplace($2, e);
                    free($2);
        }
        ;

var_decl_list:  var_decl
        |       var_decl var_decl_list
        ;

var_decl_sec:   TK_VAR TK_COLON var_decl_list
        ;

// =============================
// Cost Function
// =============================
cost_decl:      exp TK_SEMICOLON {
                    $$ = $1;
        }
        ;
cost_decl_list: cost_decl {
                    dop_costs.push_back($1);
                    // TODO(soonhok): add
        }
        |       cost_decl cost_decl_list {
                    dop_costs.push_back($1);
        }
        ;
cost_decl_sec:   TK_COST TK_COLON cost_decl_list
        ;

// =============================
// Constraints
// =============================

ctr_decl:        formula TK_SEMICOLON {
                     $$ = $1;
        }
        ;

ctr_decl_list:   ctr_decl {
                    dop_ctrs.push_back($1);
        }
        |       ctr_decl ctr_decl_list {
                    dop_ctrs.push_back($1);
        }
        ;

opt_ctr_decl_sec:
                /* nothing */
        |       ctr_decl_sec
        ;

ctr_decl_sec:
                TK_CTR TK_COLON ctr_decl_list
        ;

// =============================
// Expression
// =============================
exp:            TK_NUM          { $$ = dop_ctx->mkNum($1); free($1); }
        |       TK_ID           { $$ = dop_ctx->mkVar($1); free($1); }
        |       TK_LP exp TK_RP { $$ = $2; }
        |       TK_MINUS exp %prec UMINUS { $$ = dop_ctx->mkUminus(dop_ctx->mkCons($2)); }
        |       exp TK_PLUS exp {
            $$ = dop_ctx->mkPlus(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: +");
            }
        }
        |       exp TK_MINUS exp {
            $$ = dop_ctx->mkMinus(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: -");
            }
        }
        |       exp TK_TIMES exp {
            $$ = dop_ctx->mkTimes(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: *");
            }
        }
        |       exp TK_DIV exp {
            $$ = dop_ctx->mkDiv(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: /");
            }
        }
        |       exp TK_POW exp {
            $$ = dop_ctx->mkPow(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: ^(pow)");
            }
        }
        |       TK_ABS TK_LP exp TK_RP {
            $$ = dop_ctx->mkAbs(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: abs");
            }
        }
        |       TK_LOG TK_LP exp TK_RP {
            $$ = dop_ctx->mkLog(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: log");
            }
        }
        |       TK_EXP TK_LP exp TK_RP {
            $$ = dop_ctx->mkExp(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: exp");
            }
        }
        |       TK_SQRT TK_LP exp TK_RP {
            $$ = dop_ctx->mkSqrt(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sqrt");
            }
        }
        |       TK_SIN TK_LP exp TK_RP {
            $$ = dop_ctx->mkSin(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sin");
            }
                }
        |       TK_COS TK_LP exp TK_RP {
            $$ = dop_ctx->mkCos(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: cos");
            }
        }
        |       TK_TAN TK_LP exp TK_RP {
            $$ = dop_ctx->mkTan(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: tan");
            }
        }
        |       TK_SINH TK_LP exp TK_RP {
            $$ = dop_ctx->mkSinh(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sinh");
            }
        }
        |       TK_COSH TK_LP exp TK_RP {
            $$ = dop_ctx->mkCosh(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: cosh");
            }
        }
        |       TK_TANH TK_LP exp TK_RP {
            $$ = dop_ctx->mkTanh(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: tanh");
            }
        }
        |       TK_ASIN TK_LP exp TK_RP {
            $$ = dop_ctx->mkAsin(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: asin");
            }
        }
        |       TK_ACOS TK_LP exp TK_RP {
            $$ = dop_ctx->mkAcos(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: acos");
            }
        }
        |       TK_ATAN TK_LP exp TK_RP {
            $$ = dop_ctx->mkAtan(dop_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: atan");
            }
        }
        |       TK_ATAN2 TK_LP exp ',' exp TK_RP {
            $$ = dop_ctx->mkAtan2(dop_ctx->mkCons($3, dop_ctx->mkCons($5)));
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
                    $$ = dop_ctx->mkEq(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: =");
                    }
        }
        |       exp TK_NEQ exp {
                    $$ = dop_ctx->mkEq(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
                    $$ = dop_ctx->mkNot(dop_ctx->mkCons($1));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: !=");
                    }        }
        |       exp TK_GT exp {
                    $$ = dop_ctx->mkGt(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: >");
                    }        }
        |       exp TK_LT exp {
                    $$ = dop_ctx->mkLt(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: <");
                    }        }
        |       exp TK_GEQ exp {
                    $$ = dop_ctx->mkGeq(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: >=");
                    }        }
        |       exp TK_LEQ exp {
                    $$ = dop_ctx->mkLeq(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: <=");
                    }        }
        |       formula TK_OR formula {
                    $$ = dop_ctx->mkOr(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: or");
                    }
        }
        |       formula TK_AND formula {
                    $$ = dop_ctx->mkAnd(dop_ctx->mkCons($1, dop_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: and");
                    }
        }
        ;
