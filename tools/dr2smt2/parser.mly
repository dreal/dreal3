/*
 * Parser for .dr format
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token AT LT LE GT GE IMPLY DDT CARET DP NOT COMMA
%token IF THEN ELSE
%token SIN COS TAN
%token ASIN ACOS ATAN ATAN2 MATAN SAFESQRT
%token SINH COSH TANH
%token LOG EXP SQRT ABS
%token MODE MACR INVT FLOW JUMP INIT GOAL TRUE FALSE
%token AND OR ARROW DOT
%token EOF
%token <float> FNUM
%token <string> ID

%start main

%type <Vardecl.t list * (Ode.t list) option * Dr.formula> main
%type <Dr.formula> formula
%type <Dr.exp> exp

%%
main: varDecl_list ode_decls formula { ($1, $2, $3) }
;

varDecl_list: varDecl { [$1] }
  | varDecl varDecl_list { $1::$2 }
;

varDecl:
  | LB FNUM COMMA FNUM RB var SEMICOLON { (($2, $4), $6) }
;

var: ID { $1 }
  | LP var RP { $2 }
  | AST var { "ptr_" ^ $2 }
  | var ARROW var { $1 ^ "_" ^ $3 }
  | var DOT var { $1 ^ "_" ^ $3 }
;

ode_decls: /* nothing */ { None }
  | LC ode_list RC { Some $2 }

ode:
  DDT LB ID RB EQ exp SEMICOLON { ($3, $6) }
;

ode_list: /* nothing */ { [] }
  | ode ode_list { $1::$2 }
;

formula_list: formula { [$1] }
  | formula formula_list { $1::$2 }
;

formula:
    TRUE             { Dr.True }
  | FALSE            { Dr.False }
  | LP formula RP    { $2 }
  | NOT formula      { Dr.Not $2       }
  | AND formula_list { Dr.And $2       }
  | OR formula_list  { Dr.Or  $2       }
  | GT exp exp       { Dr.Gt  ($2, $3) }
  | LT exp exp       { Dr.Lt  ($2, $3) }
  | GE exp exp       { Dr.Ge  ($2, $3) }
  | LE exp exp       { Dr.Le  ($2, $3) }
  | EQ exp exp       { Dr.Eq  ($2, $3) }
  | exp EQ exp       { Dr.Eq  ($1, $3) }
;

exp:
   ID                       { Dr.Var $1 }
 | FNUM                     { Dr.Const $1 }
 | LP exp RP                { $2 }
 | PLUS exp exp             { Dr.Add ($2, $3) }
 | MINUS exp                { Dr.Neg $2 }
 | MINUS exp exp            { Dr.Sub ($2, $3) }
 | AST exp exp              { if $2 = $3 then Dr.Pow ($2, Dr.Const 2.0) else Dr.Mul ($2, $3) }
 | SLASH exp exp            { Dr.Div ($2, $3) }
 | CARET exp exp            { Dr.Pow ($2, $3) }
 | SQRT exp                 { Dr.Sqrt $2 }
 | ABS exp                  { Dr.Abs $2 }
 | LOG exp                  { Dr.Log $2 }
 | EXP exp                  { Dr.Exp $2 }
 | SIN exp                  { Dr.Sin $2 }
 | COS exp                  { Dr.Cos $2 }
 | TAN exp                  { Dr.Tan $2 }
 | ASIN exp                 { Dr.Asin $2 }
 | ACOS exp                 { Dr.Acos $2 }
 | ATAN exp                 { Dr.Atan $2 }
 | ATAN2 exp exp            { Dr.Atan2 ($2, $3) }
 | MATAN exp                { Dr.Matan $2 }
 | SAFESQRT exp             { Dr.Safesqrt $2 }
 | SINH exp                 { Dr.Sinh $2 }
 | COSH exp                 { Dr.Cosh $2 }
 | TANH exp                 { Dr.Tanh $2 }
 | IF formula THEN exp ELSE exp { Dr.Ite ($2, $4, $6) }
;
