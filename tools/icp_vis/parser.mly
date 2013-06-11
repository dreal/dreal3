/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *
 */

%{
  open Batteries
%}

%token AFTER BEFORE PRUNING BRANCHED IS IN ON CONFLICT DETECTED
%token PRECISION
%token LB RB COMMA COLON SEMICOLON CARET NOT
%token LP RP PLUS MINUS AST SLASH EQ GE LE GT LT
%token INFTY
%token SIN COS TAN SQRT SAFESQRT
%token ASIN ACOS ATAN ATAN2 MATAN
%token SINH COSH TANH
%token LOG EXP
%token UNSAT HOLE SATBOX
%token EOF
%token <float> FNUM
%token <string> ID
%start main

%type <float * Basic.formula list * Ptree.t> main
%type <float * Basic.formula list * Ptree.t> sp
%type <Ptree.t> ptree
%type <Basic.formula> con
%type <Basic.exp> func
%type <string> branched_on
%%

main: sp_list EOF {
  List.reduce (fun (prec, cons, t1) (_, _, t2) -> (prec, cons, Ptree.plugin t1 t2)) $1
}

sp_list: sp { [$1] }
 | sp sp_list { $1::$2 }

sp:
   precision con_list init_list ptree
     { ($1, $2, $4) }
 | precision con_list init_list
     { ($1, $2, Ptree.Axiom (Env.make $3)) }
 | precision con_list init_list conflict_detected
     { ($1, $2, Ptree.Axiom (Env.make $3)) }

precision: /* nothing */ { 0.001 } /* default value */
 | PRECISION COLON FNUM  { $3 }

con_list: con          { [$1] }
        | con con_list { $1::$2 }
;

con: LP EQ func func RP { (Basic.Eq ($3, $4)) }
  |  LP LE func func RP { (Basic.Le ($3, $4)) }
  |  LP LT func func RP { (Basic.Le ($3, $4)) } /* ALWAYS TREAT IT AS LE */
  |  LP GE func func RP { (Basic.Ge ($3, $4)) }
  |  LP GT func func RP { (Basic.Ge ($3, $4)) } /* ALWAYS TREAT IT AS GE */
  |  LP NOT LP LE func func RP RP { (Basic.Ge ($5, $6)) }
  |  LP NOT LP LT func func RP RP { (Basic.Ge ($5, $6)) } /* ALWAYS TREAT IT AS GE */
  |  LP NOT LP GE func func RP RP { (Basic.Le ($5, $6)) }
  |  LP NOT LP GT func func RP RP { (Basic.Le ($5, $6)) } /* ALWAYS TREAT IT AS LE */
;

func_list: func           { [$1] }
         | func func_list { $1::$2 }
;

func:  FNUM                  { Basic.Num $1 }
     | ID                    { Basic.Var $1 }
     | LP PLUS  func_list RP { Basic.Add $3 }
     | LP MINUS func RP      { Basic.Neg $3 }
     | LP MINUS func func_list RP { Basic.Sub ($3::$4) }
     | LP AST   func_list RP { Basic.Mul $3 }
     | LP SLASH func func RP { Basic.Div ($3, $4) }
     | LP SQRT func RP       { Basic.Sqrt $3 }
     | LP SAFESQRT func RP   { Basic.Safesqrt $3 }
     | LP SIN func RP        { Basic.Sin $3 }
     | LP COS func RP        { Basic.Cos $3 }
     | LP TAN func RP        { Basic.Tan $3 }
     | LP ASIN func RP       { Basic.Asin $3 }
     | LP ACOS func RP       { Basic.Acos $3 }
     | LP ATAN func RP       { Basic.Atan $3 }
     | LP ATAN2 func func RP { Basic.Atan2 ($3, $4) }
     | LP MATAN func RP      { Basic.Matan $3 }
     | LP SINH func RP       { Basic.Sinh $3 }
     | LP COSH func RP       { Basic.Cosh $3 }
     | LP TANH func RP       { Basic.Tanh $3 }
     | LP LOG func RP        { Basic.Log $3 }
     | LP EXP func RP        { Basic.Exp $3 }
     | LP CARET func FNUM RP { Basic.Pow ($3, Basic.Num $4) }
;

ptree: /* Axiom */
       before_pruning entry_list conflict_detected
         { Ptree.Axiom (Env.make $2) }
       /* Hole */
     | before_pruning entry_list after_pruning entry_list HOLE
         { Ptree.make_prune (Env.make $2, Ptree.Hole) }
     | SATBOX COLON entry_list
         { Ptree.SAT (Env.make $3)}
       /* Branching */
     | branched_on entry_list ptree ptree
         { Ptree.Branch (Env.make $2, $1, $3, $4) }
       /* Branching */
     | branched_on entry_list ptree
         {
           let e1 = Env.make $2 in
           let x = $1 in
           let pt = $3 in
           let e_of_pt = Ptree.extract_top pt in
           let e2 = Env.split x e1 e_of_pt in
           Ptree.Branch (e1, x, pt, Ptree.SAT e2)
         }
       /* Pruning */
     | before_pruning entry_list after_pruning entry_list ptree
         { Ptree.make_prune (Env.make $2, $5)
}
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

entry: ID COLON LB FNUM COMMA FNUM RB { ($1, Intv.make $4 $6) }
     | ID COLON LP MINUS INFTY COMMA FNUM RB { ($1, Intv.make neg_infinity $7) }
     | ID COLON LB FNUM COMMA PLUS INFTY RP { ($1, Intv.make $4 infinity) }
     | ID COLON LP MINUS INFTY COMMA PLUS INFTY RP { ($1, Intv.make neg_infinity infinity) }
     | ID COLON FNUM { ($1, Intv.make $3 $3) }
;

entry_list: entry { [$1] }
     | entry SEMICOLON entry_list { $1::$3 }
;
