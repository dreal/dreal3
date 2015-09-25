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
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/Global.h"
#include "egraph/Egraph.h"
#include "sorts/SStore.h"
#include "api/OpenSMTContext.h"

using std::vector;
using std::unordered_map;
using std::string;
using std::pair;
using std::stod;

extern int baronlineno;
extern int baronlex( );

// ===========
// The result
// ===========
OpenSMTContext * baron_ctx;
bool baron_minimize; // true if minimize, false if maximize
vector<Enode*> baron_ctrs;
Enode * baron_cost_fn;
unordered_map<string, Enode*> baron_var_map;

void baronerror( const char * s )
{
  printf( "At line %d: %s\n", baronlineno, s );
  exit( 1 );
}

void baron_init_parser() {
    baron_ctx = new OpenSMTContext();
    baron_ctx->SetLogic(QF_NRA);
}

void baron_cleanup_parser() {
    delete baron_ctx;
}

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024
%}

%union
{
    std::pair< char *, char * > * char_ptr_pair;
    std::vector< std::pair< char *, char * > > * char_ptr_pair_vec;
    char  *                  str;
    Enode *                  enode;
}

%error-verbose

%token TK_VARIABLES TK_POS_VARIABLES TK_LOWER_BOUNDS TK_UPPER_BOUNDS TK_EQUATIONS TK_OBJ TK_MINIMIZE TK_MAXIMIZE
%token TK_STARTING_POINT TK_COMMA TK_COLON TK_SEMICOLON TK_PLUS TK_MINUS TK_TIMES TK_DIV TK_EQ TK_NEQ TK_LEQ TK_GEQ
%token TK_LT TK_GT TK_SIN TK_COS TK_TAN TK_EXP TK_LOG TK_ABS TK_ASIN TK_ACOS TK_ATAN TK_SINH TK_COSH TK_TANH TK_MIN
%token TK_MAX TK_ATAN2 TK_MATAN TK_SQRT TK_SAFESQRT TK_POW
%token TK_LC TK_RC TK_LP TK_RP TK_LB TK_RB
%token TK_NUM TK_STR TK_ID

%type   <str>           TK_NUM TK_ID TK_STR
%type   <enode>         exp formula var_decl eq_decl obj_decl_sec
%type   <char_ptr_pair>  var_value_pair
%type   <char_ptr_pair_vec> var_value_pair_list

%left TK_PLUS TK_MINUS
%left TK_TIMES TK_DIV
%left UMINUS
%right TK_POW

%start script

%%

script:         var_decl_sec
                opt_pos_var_decl_sec
                opt_lb_decl_sec
                opt_ub_decl_sec
                opt_eq_decl_sec
                obj_decl_sec
                opt_starting_point_sec {
                    baron_cost_fn = $6;
        }
        ;

// =============================
// Variable Declaration Section
// =============================

var_decl:       TK_ID {
                    baron_ctx->DeclareFun($1, baron_ctx->mkSortReal());
                    Enode * e = baron_ctx->mkVar($1, true);
                    e->setDomainLowerBound(-1e51);
                    e->setDomainUpperBound(+1e51);
                    baron_var_map.emplace($1, e);
                    free($1);
        }
        ;

var_decl_list:  var_decl
        |       var_decl TK_COMMA var_decl_list
        ;

var_decl_sec:   TK_VARIABLES var_decl_list TK_SEMICOLON
        ;

// =============================
// Positive Variable Declaration Section
// =============================
pos_var_decl:       TK_ID {
                        Enode * e = baron_ctx->mkVar($1);
                        e->setDomainLowerBound(0);
                        e->setValueLowerBound(0);
                        free($1);
        }
        ;

pos_var_decl_list:  pos_var_decl
        |       pos_var_decl TK_COMMA pos_var_decl_list
        ;

opt_pos_var_decl_sec:
                /* nothing */
        |       pos_var_decl_sec
        ;

pos_var_decl_sec:   TK_POS_VARIABLES pos_var_decl_list TK_SEMICOLON
        ;


// =============================
// Lower Bounds / Upper Bounds
// =============================
var_value_pair:
                TK_ID TK_COLON TK_NUM TK_SEMICOLON {
                    $$ = new pair<char *, char *>($1, $3);
                }
        ;

var_value_pair_list:
                var_value_pair {
                    auto l = new vector<pair<char *, char *>>();
                    l->push_back(*($1));
                    delete $1;
                    $$ = l;
                }
        |       var_value_pair var_value_pair_list {
                    $2->push_back(*$1);
                    delete $1;
                    $$ = $2;
                }
opt_lb_decl_sec:
                /* nothing */
        |       lb_decl_sec
        ;

lb_decl_sec:    TK_LOWER_BOUNDS TK_LC var_value_pair_list TK_RC {
                    for (auto p : *$3) {
                        char * name = p.first;
                        char * val = p.second;
                        double const value = stod(val, nullptr);
                        Enode * e = baron_ctx->mkVar(name);
                        e->setDomainLowerBound(value);
                        e->setValueLowerBound(value);
                        free(name);
                        free(val);
                    }
                    delete $3;
                }
        ;

opt_ub_decl_sec:
                /* nothing */
        |       ub_decl_sec
        ;

ub_decl_sec:    TK_UPPER_BOUNDS TK_LC var_value_pair_list TK_RC {
                    for (auto p : *$3) {
                        char * name = p.first;
                        char * val= p.second;
                        double const value = stod(val, nullptr);
                        Enode * e = baron_ctx->mkVar(name);
                        e->setDomainUpperBound(value);
                        e->setValueUpperBound(value);
                        free(name);
                        free(val);
                    }
                    delete $3;
                }
        ;

// =============================
// Equations
// =============================

eq_decl:        TK_ID TK_COLON formula TK_SEMICOLON {
                    $$ = $3;
                    free($1);
        }
        ;

eq_decl_list:   eq_decl {
                    baron_ctrs.push_back($1);
        }
        |       eq_decl eq_decl_list {
                    baron_ctrs.push_back($1);
        }
        ;

var_list:       TK_ID { free($1); }
        |       TK_ID TK_COMMA var_list { free($1); }
        ;

opt_eq_decl_sec:
                /* nothing */
        |       eq_decl_sec
        ;

eq_decl_sec:
                TK_EQUATIONS var_list TK_SEMICOLON eq_decl_list
        ;

// =============================
// Object Function
// =============================
obj_decl_sec:   TK_OBJ TK_COLON TK_MINIMIZE exp TK_SEMICOLON {
                    baron_minimize = true;
                    $$ = $4;
        }
        |       TK_OBJ TK_COLON TK_MAXIMIZE exp TK_SEMICOLON {
                    baron_minimize = false;
                    $$ = $4;
        }
        ;

// =============================
// Starting Point
// =============================
opt_starting_point_sec:
                /* nothing */
        |       starting_point_sec
        ;
starting_point_sec: TK_STARTING_POINT TK_LC var_value_pair_list TK_RC { }

// =============================
// Expression
// =============================
exp:            TK_NUM          { $$ = baron_ctx->mkNum($1); free($1); }
        |       TK_ID           { $$ = baron_ctx->mkVar($1); free($1); }
        |       TK_LP exp TK_RP { $$ = $2; }
        |       TK_MINUS exp %prec UMINUS { $$ = baron_ctx->mkUminus(baron_ctx->mkCons($2)); }
        |       exp TK_PLUS exp {
            $$ = baron_ctx->mkPlus(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: +");
            }
        }
        |       exp TK_MINUS exp {
            $$ = baron_ctx->mkMinus(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: -");
            }
        }
        |       exp TK_TIMES exp {
            $$ = baron_ctx->mkTimes(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: *");
            }
        }
        |       exp TK_DIV exp {
            $$ = baron_ctx->mkDiv(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: /");
            }
        }
        |       exp TK_POW exp {
            $$ = baron_ctx->mkPow(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
            if ($$ == nullptr) {
                yyerror("Parse Error: ^(pow)");
            }
        }
        |       TK_ABS TK_LP exp TK_RP {
            $$ = baron_ctx->mkAbs(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: abs");
            }
        }
        |       TK_LOG TK_LP exp TK_RP {
            $$ = baron_ctx->mkLog(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: log");
            }
        }
        |       TK_EXP TK_LP exp TK_RP {
            $$ = baron_ctx->mkExp(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: exp");
            }
        }
        |       TK_SQRT TK_LP exp TK_RP {
            $$ = baron_ctx->mkSqrt(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sqrt");
            }
        }
        |       TK_SIN TK_LP exp TK_RP {
            $$ = baron_ctx->mkSin(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sin");
            }
                }
        |       TK_COS TK_LP exp TK_RP {
            $$ = baron_ctx->mkCos(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: cos");
            }
        }
        |       TK_TAN TK_LP exp TK_RP {
            $$ = baron_ctx->mkTan(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: tan");
            }
        }
        |       TK_SINH TK_LP exp TK_RP {
            $$ = baron_ctx->mkSinh(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: sinh");
            }
        }
        |       TK_COSH TK_LP exp TK_RP {
            $$ = baron_ctx->mkCosh(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: cosh");
            }
        }
        |       TK_TANH TK_LP exp TK_RP {
            $$ = baron_ctx->mkTanh(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: tanh");
            }
        }
        |       TK_ASIN TK_LP exp TK_RP {
            $$ = baron_ctx->mkAsin(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: asin");
            }
        }
        |       TK_ACOS TK_LP exp TK_RP {
            $$ = baron_ctx->mkAcos(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: acos");
            }
        }
        |       TK_ATAN TK_LP exp TK_RP {
            $$ = baron_ctx->mkAtan(baron_ctx->mkCons($3));
            if ($$ == nullptr) {
                yyerror("Parse Error: atan");
            }
        }
        |       TK_ATAN2 TK_LP exp ',' exp TK_RP {
            $$ = baron_ctx->mkAtan2(baron_ctx->mkCons($3, baron_ctx->mkCons($5)));
            if ($$ == nullptr) {
                yyerror("Parse Error: atan2");
            }
        }
;

// =============================
// Formula
// =============================

formula:        exp TK_EQ exp {
                    $$ = baron_ctx->mkEq(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: =");
                    }
        }
        |       exp TK_NEQ exp {
                    $$ = baron_ctx->mkEq(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
                    $$ = baron_ctx->mkNot(baron_ctx->mkCons($1));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: !=");
                    }        }
        |       exp TK_GT exp {
                    $$ = baron_ctx->mkGt(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: >");
                    }        }
        |       exp TK_LT exp {
                    $$ = baron_ctx->mkLt(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: <");
                    }        }
        |       exp TK_GEQ exp {
                    $$ = baron_ctx->mkGeq(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: >=");
                    }        }
        |       exp TK_LEQ exp {
                    $$ = baron_ctx->mkLeq(baron_ctx->mkCons($1, baron_ctx->mkCons($3)));
                    if ($$ == nullptr) {
                        yyerror("Parse Error: <=");
                    }        }
        ;
