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
#include "util/automaton.h"

using std::vector;
using std::unordered_map;
using std::make_pair;
using std::string;
using std::list;
using std::stod;
using std::numeric_limits;

extern int drhlineno;
extern int drhlex();
extern OpenSMTContext * parser_ctx;
extern dreal::automaton * atmp;
void drherror( const char * s ) {
  printf( "At line %d: %s\n", drhlineno, s );
  exit( 1 );
}

vector<Enode *> tmp_invt;
unordered_map<Enode *, Enode *> tmp_flow;
unordered_map<double, Enode *> tmp_guard;
unordered_map<double, Enode *> tmp_reset;

#define YYMAXDEPTH 1024 * 1024
%}

%union
{
  char *  str;
  Enode * enode;
  double  fp;
}
%error-verbose
%token TK_VAR TK_COST TK_PREC TK_CTR TK_COMMA TK_COLON TK_SEMICOLON TK_PLUS TK_MINUS TK_TIMES TK_DIV TK_EQ TK_NEQ TK_LEQ TK_GEQ TK_LT TK_GT TK_SIN TK_COS TK_TAN TK_EXP TK_LOG TK_ABS TK_ASIN TK_ACOS TK_ATAN TK_SINH TK_COSH TK_TANH TK_MIN TK_MAX TK_ATAN2 TK_MATAN TK_SQRT TK_SAFESQRT TK_POW TK_LC TK_RC TK_LP TK_RP TK_LB TK_RB TK_NOT TK_OR TK_AND TK_IMPLIES TK_NUM TK_STR TK_ID TK_GOTO TK_AT TK_DDT TK_FLOW TK_JUMP TK_INVT TK_INIT TK_GOAL TK_MODE
%type <str> TK_NUM TK_ID TK_STR
%type <enode> exp atom formula
%type <fp>  numeral mode_head
%nonassoc TK_NOT
%left TK_AND TK_OR TK_IMPLIES
%nonassoc TK_EQ TK_NEQ TK_LT TK_LEQ TK_GT TK_GEQ
%left TK_PLUS TK_MINUS
%left TK_TIMES TK_DIV
%nonassoc UMINUS
%right TK_POW

%start script
%%
script: var_decl_sec atm_decl_sec;
var_decl_sec: var_decl_list;
var_decl_list:  var_decl | var_decl var_decl_list;
var_decl: TK_LB numeral TK_COMMA numeral TK_RB TK_ID TK_SEMICOLON {
  double const lb = $2;
  double const ub = $4;
  parser_ctx->DeclareFun($6, parser_ctx->mkSortReal());
  Enode * e = parser_ctx->mkVar($6, true);
  e->setDomainLowerBound(lb);
  e->setDomainUpperBound(ub);
  //add prime variable
  string pvar($6);
  pvar = pvar + "'";
  parser_ctx->DeclareFun(pvar.c_str(), parser_ctx->mkSortReal());
  Enode * pe = parser_ctx->mkVar(pvar.c_str(), true);
  pe->setDomainLowerBound(lb);
  pe->setDomainUpperBound(ub);
  free($6);
} | numeral TK_ID TK_SEMICOLON {
  double const c = $1;
  parser_ctx->DeclareFun($2, parser_ctx->mkSortReal());
  Enode * e = parser_ctx->mkVar($2, true);
  e->setDomainLowerBound(c);
  e->setDomainUpperBound(c);
  e->setValueLowerBound(c);
  e->setValueUpperBound(c);
  free($2);
};
atm_decl_sec: mode_decl_list init_decl_sec goal_decl_sec;
mode_decl_list: mode_decl | mode_decl mode_decl_list;
mode_decl: TK_LC mode_head invt_decl_sec flow_decl_sec jump_decl_sec TK_RC {
  atmp -> add_mode($2, tmp_invt, tmp_flow, tmp_guard, tmp_reset);
  tmp_invt.clear();
  tmp_flow.clear();
  tmp_guard.clear();
  tmp_reset.clear();
};
mode_head: TK_MODE numeral TK_SEMICOLON {
  $$ = $2;
};
invt_decl_sec: TK_INVT TK_COLON invt_decl_list;
invt_decl_list: invt_decl | invt_decl invt_decl_list;
invt_decl: formula TK_SEMICOLON {
  tmp_invt.push_back($1);
};
flow_decl_sec: TK_FLOW TK_COLON flow_decl_list;
flow_decl_list: flow_decl | flow_decl flow_decl_list;
flow_decl: TK_DDT TK_LB TK_ID TK_RB TK_EQ exp TK_SEMICOLON {
  Enode * v = parser_ctx->mkVar($3);
  tmp_flow.emplace(v,$6);
};
jump_decl_sec: TK_JUMP TK_COLON jump_decl_list;
jump_decl_list: jump_decl | jump_decl jump_decl_list;
jump_decl: formula TK_GOTO TK_AT numeral formula TK_SEMICOLON {
  tmp_guard.emplace($4,$1);
  tmp_reset.emplace($4,$5);
};
init_decl_sec: TK_INIT TK_COLON init_decl_list;
init_decl_list: init_decl | init_decl init_decl_list;
init_decl: TK_AT numeral formula TK_SEMICOLON {
  atmp -> add_init($2, $3);
};
goal_decl_sec: TK_GOAL TK_COLON goal_decl_list;
goal_decl_list: goal_decl | goal_decl goal_decl_list;
goal_decl: TK_AT numeral formula TK_SEMICOLON {
  atmp -> add_goal($2, $3);
};

numeral: TK_NUM {
  $$ = stod($1, nullptr);
  free($1);
} | TK_MINUS TK_NUM {
  $$ = -stod($2, nullptr);
  free($2);
};
exp: TK_NUM {
  $$ = parser_ctx->mkNum($1);
  free($1);
} | TK_ID {
  $$ = parser_ctx->mkVar($1);
  free($1);
} | TK_LP exp TK_RP {
  $$ = $2;
} | TK_MINUS exp %prec UMINUS {
  $$ = parser_ctx->mkUminus(parser_ctx->mkCons($2));
} | exp TK_PLUS exp {
  $$ = parser_ctx->mkPlus(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: +");
  }
} | exp TK_MINUS exp {
  $$ = parser_ctx->mkMinus(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: -");
  }
} | exp TK_TIMES exp {
  $$ = parser_ctx->mkTimes(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: *");
  }
} | exp TK_DIV exp {
  $$ = parser_ctx->mkDiv(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: /");
  }
} | exp TK_POW exp {
  $$ = parser_ctx->mkPow(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: ^(pow)");
  }
} | TK_ABS TK_LP exp TK_RP {
  $$ = parser_ctx->mkAbs(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: abs");
  }
} | TK_LOG TK_LP exp TK_RP {
  $$ = parser_ctx->mkLog(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: log");
  }
} | TK_EXP TK_LP exp TK_RP {
  $$ = parser_ctx->mkExp(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: exp");
  }
} | TK_SQRT TK_LP exp TK_RP {
  $$ = parser_ctx->mkSqrt(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: sqrt");
  }
} | TK_SIN TK_LP exp TK_RP {
  $$ = parser_ctx->mkSin(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: sin");
  }
} | TK_COS TK_LP exp TK_RP {
  $$ = parser_ctx->mkCos(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: cos");
  }
} | TK_TAN TK_LP exp TK_RP {
  $$ = parser_ctx->mkTan(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: tan");
  }
} | TK_SINH TK_LP exp TK_RP {
  $$ = parser_ctx->mkSinh(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: sinh");
  }
} | TK_COSH TK_LP exp TK_RP {
  $$ = parser_ctx->mkCosh(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: cosh");
  }
} | TK_TANH TK_LP exp TK_RP {
  $$ = parser_ctx->mkTanh(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: tanh");
  }
} | TK_ASIN TK_LP exp TK_RP {
  $$ = parser_ctx->mkAsin(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: asin");
  }
} | TK_ACOS TK_LP exp TK_RP {
  $$ = parser_ctx->mkAcos(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: acos");
  }
} | TK_ATAN TK_LP exp TK_RP {
  $$ = parser_ctx->mkAtan(parser_ctx->mkCons($3));
  if ($$ == nullptr) {
    yyerror("Parse Error: atan");
  }
} | TK_ATAN2 TK_LP exp ',' exp TK_RP {
  $$ = parser_ctx->mkAtan2(parser_ctx->mkCons($3, parser_ctx->mkCons($5)));
  if ($$ == nullptr) {
    yyerror("Parse Error: atan2");
  }
};
atom: exp TK_EQ exp {
  $$ = parser_ctx->mkEq(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: =");
  }
} | exp TK_NEQ exp {
  $$ = parser_ctx->mkEq(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  $$ = parser_ctx->mkNot(parser_ctx->mkCons($1));
  if ($$ == nullptr) {
    yyerror("Parse Error: !=");
  }
} | exp TK_GT exp {
  $$ = parser_ctx->mkGt(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: >");
  }
} | exp TK_LT exp {
  $$ = parser_ctx->mkLt(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: <");
  }
} | exp TK_GEQ exp {
  $$ = parser_ctx->mkGeq(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: >=");
  }
} | exp TK_LEQ exp {
  $$ = parser_ctx->mkLeq(parser_ctx->mkCons($1, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: <=");
  }
};
formula: atom {
  $$ = $1;
} | TK_LP formula TK_RP {
  $$ = $2;
} | TK_NOT formula {
  $$ = parser_ctx->mkNot(parser_ctx->mkCons($2));
  if ($$ == nullptr) {
    yyerror("Parse Error: not");
  }
} | TK_AND formula formula {
  $$ = parser_ctx->mkAnd(parser_ctx->mkCons($2, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: and");
  }
} | TK_OR formula formula {
  $$ = parser_ctx->mkOr(parser_ctx->mkCons($2, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: or");
  }
} | TK_IMPLIES formula formula {
  $$ = parser_ctx->mkImplies(parser_ctx->mkCons($2, parser_ctx->mkCons($3)));
  if ($$ == nullptr) {
    yyerror("Parse Error: implies");
  }
};
