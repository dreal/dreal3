/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token AT LT LE GT GE IMPLY DDT CARET DP NOT
%token SIN COS TAN
%token ASIN ACOS ATAN
%token SINH COSH TANH
%token LOG EXP SQRT ABS
%token MODE MACR INVT FLOW JUMP INIT GOAL TRUE FALSE
%token AND OR ARROW DOT
%token EOF
%token <float> FNUM
%token <string> ID

%start main

%type <Vardecl.t list * Basic.formula * Basic.formula> main
%type <Basic.formula> formula
%type <Basic.exp> exp

%%
main: varDecl_list formula formula { ($1, $2, $3) }
;

varDecl_list: varDecl { [$1] }
  | varDecl SEMICOLON varDecl_list { $1::$3 }
;

varDecl:
  LB FNUM COMMA FNUM RB var COLON FNUM { (($2, $4), $6, Some (int_of_float $8)) }
  | LB FNUM COMMA FNUM RB var { (($2, $4), $6, None) }
;

var: ID { $1 }
  | LP var RP { $2 }
  | AST var { "ptr_" ^ $2 }
  | var ARROW var { $1 ^ "_" ^ $3 }
  | var DOT var { $1 ^ "_" ^ $3 }
;

formula_list: formula { [] }
  | formula formula_list { $1::$2 }
;

formula:
    TRUE             { Basic.True }
  | FALSE            { Basic.False }
  | LP formula RP    { $2 }
  | NOT formula      { Basic.Not $2       }
  | AND formula_list { Basic.And $2       }
  | OR formula_list  { Basic.Or  $2       }
  | GT exp exp       { Basic.Gt  ($2, $3) }
  | LT exp exp       { Basic.Lt  ($2, $3) }
  | GE exp exp       { Basic.Ge  ($2, $3) }
  | LE exp exp       { Basic.Le  ($2, $3) }
  | EQ exp exp       { Basic.Eq  ($2, $3) }
;

exp:
   ID            { Basic.Var $1 }
 | FNUM          { Basic.Num $1 }
 | LP exp RP     { $2 }
 | PLUS exp exp  { Basic.Add [$2; $3] }
 | MINUS exp exp { Basic.Sub [$2; $3] }
 | AST exp exp   { Basic.Mul [$2; $3] }
 | SLASH exp exp { Basic.Div ($2, $3) }
 | CARET exp exp { Basic.Pow ($2, $3) }
 | SQRT exp      { Basic.Sqrt $2 }
 | ABS exp       { Basic.Abs $2 }
 | LOG exp       { Basic.Log $2 }
 | EXP exp       { Basic.Exp $2 }
 | SIN exp       { Basic.Sin $2 }
 | COS exp       { Basic.Cos $2 }
 | TAN exp       { Basic.Tan $2 }
 | ASIN exp      { Basic.Asin $2 }
 | ACOS exp      { Basic.Acos $2 }
 | ATAN exp      { Basic.Atan $2 }
 | SINH exp      { Basic.Sinh $2 }
 | COSH exp      { Basic.Cosh $2 }
 | TANH exp      { Basic.Tanh $2 }
;
