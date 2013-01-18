/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *
 */

%{

%}

%token AFTER BEFORE PRUNING BRANCHED IS IN ON CONFLICT DETECTED
%token PRECISION
%token LB RB COMMA COLON SEMICOLON CARET
%token LP RP PLUS MINUS AST SLASH EQ GE LE GT LT
%token INFTY
%token SIN COS TAN
%token ASIN ACOS ATAN
%token SINH COSH TANH
%token LOG EXP
%token EOF
%token <float> FNUM
%token <string> ID

%start main

%type <float * Constraint.t list * Env.t * Ptree.t> main
%type <Ptree.t> ptree
%type <Constraint.t> con
%type <Func.t> func
%type <string> branched_on

%%

main:
precision con_list init_list ptree { ($1, $2, Env.make $3, $4) }

precision: /* nothing */ { 0.001 } /* default value */
 | PRECISION COLON FNUM  { $3 }

con_list: /* */ { [] }
     | con con_list { $1::$2 }
;

con: LP EQ func func RP { (Constraint.EQ_ZERO, Func.Sub ($3, $4)) }
  |  LP LE func func RP { (Constraint.LT_ZERO, Func.Sub ($3, $4)) }
  |  LP LT func func RP { (Constraint.LT_ZERO, Func.Sub ($3, $4)) }
  |  LP GE func func RP { (Constraint.GT_ZERO, Func.Sub ($3, $4)) }
  |  LP GT func func RP { (Constraint.GT_ZERO, Func.Sub ($3, $4)) }
;

func:  FNUM                  { Func.Num $1 }
     | ID                    { Func.Var $1 }
     | LP PLUS  func func RP { Func.Add ($3, $4) }
     | LP MINUS func func RP { Func.Sub ($3, $4) }
     | LP MINUS func RP      { Func.Sub (Func.Num 0.0, $3) }
     | LP AST   func func RP { Func.Mul ($3, $4) }
     | LP SLASH func func RP { Func.Div ($3, $4) }
     | LP SIN func RP        { Func.Sin $3 }
     | LP COS func RP        { Func.Cos $3 }
     | LP TAN func RP        { Func.Tan $3 }
     | LP ASIN func RP       { Func.Asin $3 }
     | LP ACOS func RP       { Func.Acos $3 }
     | LP ATAN func RP       { Func.Atan $3 }
     | LP SINH func RP       { Func.Sinh $3 }
     | LP COSH func RP       { Func.Cosh $3 }
     | LP TANH func RP       { Func.Tanh $3 }
     | LP LOG func RP        { Func.Log $3 }
     | LP EXP func RP        { Func.Exp $3 }
     | LP CARET func FNUM RP { Func.Pow ($3, int_of_float $4) }
;

ptree: before_pruning entry_list conflict_detected
       { Ptree.Axiom (Env.make $2) }

     | before_pruning entry_list a_ptree
       { Ptree.Prune (Env.make $2, $3) }
;

a_ptree: after_pruning entry_list bptree ptree
       { Ptree.Branch (Env.make $2, $3, $4) }
     | after_pruning entry_list ptree
       { Ptree.Prune (Env.make $2, $3) }
;

bptree: branched_on entry_list ptree {$3}
;


before_pruning: LB BEFORE PRUNING RB { }
;

after_pruning: LB AFTER PRUNING RB { }
;

branched_on: LB BRANCHED ON ID RB { $4 }
;

conflict_detected: LB CONFLICT DETECTED RB { }
;

init: entry SEMICOLON { $1 }
;

init_list: init { [$1] }
         | init init_list { $1::$2 }
;

entry: ID IS IN COLON LB FNUM COMMA FNUM RB { ($1, $6, $8) }
     | ID IS IN COLON LP MINUS INFTY COMMA FNUM RB { ($1, neg_infinity, $9) }
     | ID IS IN COLON LB FNUM COMMA PLUS INFTY RP { ($1, $6, infinity) }
     | ID IS IN COLON LP MINUS INFTY COMMA PLUS INFTY RP { ($1, neg_infinity, infinity) }
     | ID IS IN COLON FNUM { ($1, $5, $5) }
;

entry_list: entry { [$1] }
     | entry SEMICOLON entry_list { $1::$3 }
;
