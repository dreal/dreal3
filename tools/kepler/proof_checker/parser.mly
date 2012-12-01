/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *
 */

%{ 

%}

%token AFTER BEFORE PRUNING BRANCHED IS IN ON CONFLICT DETECTED
%token LB RB COMMA COLON SEMICOLON CARET
%token LP RP PLUS MINUS AST SLASH EQ
%token SIN COS TAN
%token ASIN ACOS ATAN
%token SINH COSH TANH
%token LOG EXP
%token EOF
%token <float> FNUM
%token <string> ID

%start main

%type <Func.t list * Ptree.t> main
%type <Ptree.t> ptree
%type <Func.t> func
%type <string> branched_on 

%%

main:
con_list ptree { ($1, $2) }

con_list: /* */ { [] }
     | con con_list { $1::$2 }
;
  
con: LP EQ func func RP { Func.Sub ($3, $4) }
;

func:  FNUM                  { Func.Num $1 }
     | ID                    { Func.Var $1 }
     | LP PLUS  func func RP { Func.Add ($3, $4) }
     | LP MINUS func func RP { Func.Sub ($3, $4) }
     | LP MINUS FNUM RP      { Func.Sub (Func.Num 0.0, Func.Num $3) }
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

entry1: ID IS IN COLON LB FNUM COMMA FNUM RB { ($1, $6, $8) }
entry2: ID IS IN COLON FNUM { ($1, $5, $5) }
;

entry_list:
  entry1 { [$1] }
| entry2 { [$1] }
| entry1 SEMICOLON entry_list { $1::$3 }
| entry2 SEMICOLON entry_list { $1::$3 }
;      
