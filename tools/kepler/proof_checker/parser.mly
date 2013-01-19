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
%token UNSAT
%token EOF
%token <float> FNUM
%token <string> ID

%start main

%type <float * Basic.formula list * Env.t * Ptree.t option> main
%type <Ptree.t> ptree
%type <Basic.formula> con
%type <Func.t> func
%type <string> branched_on

%%

main: precision con_list init_list ptree UNSAT EOF { ($1, $2, Env.make $3, Some $4) }
 |precision con_list init_list UNSAT EOF { ($1, $2, Env.make $3, None) }

precision: /* nothing */ { 0.001 } /* default value */
 | PRECISION COLON FNUM  { $3 }

con_list: /* */ { [] }
     | con con_list { $1::$2 }
;

con: LP EQ func func RP { (Basic.Eq ($3, $4)) }
  |  LP LE func func RP { (Basic.Le ($3, $4)) }
  |  LP LT func func RP { (Basic.Le ($3, $4)) } /* ALWAYS TREAT IT AS LE */
  |  LP GE func func RP { (Basic.Ge ($3, $4)) }
  |  LP GT func func RP { (Basic.Ge ($3, $4)) } /* ALWAYS TREAT IT AS GE */
;

func:  FNUM                  { Basic.Num $1 }
     | ID                    { Basic.Var $1 }
     | LP PLUS  func func RP { Basic.Add ($3, $4) }
     | LP MINUS func func RP { Basic.Sub ($3, $4) }
     | LP MINUS func RP      { Basic.Neg ($3) }
     | LP AST   func func RP { Basic.Mul ($3, $4) }
     | LP SLASH func func RP { Basic.Div ($3, $4) }
     | LP SIN func RP        { Basic.Sin $3 }
     | LP COS func RP        { Basic.Cos $3 }
     | LP TAN func RP        { Basic.Tan $3 }
     | LP ASIN func RP       { Basic.Asin $3 }
     | LP ACOS func RP       { Basic.Acos $3 }
     | LP ATAN func RP       { Basic.Atan $3 }
     | LP SINH func RP       { Basic.Sinh $3 }
     | LP COSH func RP       { Basic.Cosh $3 }
     | LP TANH func RP       { Basic.Tanh $3 }
     | LP LOG func RP        { Basic.Log $3 }
     | LP EXP func RP        { Basic.Exp $3 }
     | LP CARET func FNUM RP { Basic.Pow ($3, $4) }
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
