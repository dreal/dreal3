/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token AT LT LTE GT GTE IMPLY DDT CARET DP
%token SIN COS TAN
%token ASIN ACOS ATAN
%token SINH COSH TANH
%token LOG EXP
%token MODE MACR INVT FLOW JUMP INIT GOAL TRUE FALSE
%token AND
%token EOF
%token <float> FNUM
%token <string> ID

%start main

%type <Hybrid.t> main
%type <Hybrid.formula> formula

%%

main: varDecl_list DP mode_list DP init goal { ($1, $3, $5, $6) }
;

varDecl_list: /* */ { [] }
  | varDecl varDecl_list { $1::$2 }
;

varDecl:
    LB FNUM RB ID SEMICOLON { ($4, Hybrid.Num $2) }
  | LB FNUM COMMA FNUM RB ID SEMICOLON { ($6, Hybrid.Intv ($2, $4)) }
;

mode_list: /* */ { [] }
  | mode mode_list { $1::$2 }
;

mode: LC mode_id macrs invts flows jumps RC { ($2, $3, $4, $5, $6) }
;

mode_id: MODE FNUM SEMICOLON { int_of_float $2 }
;

macrs: MACR COLON formula_list { $3 }
;

invts: INVT COLON formula_list { $3 }
;

flows: FLOW COLON ode_list { $3 }
;

jumps: JUMP COLON jump_list { $3 }
;

formula_list: /* */ { [] }
  | formula SEMICOLON formula_list { $1::$3 }
;

formula:
    TRUE                { Formula.True }
  | FALSE               { Formula.False }
  | LP formula RP       { $2 }
  | AND formula formula { Formula.And ($2, $3) }
  | EQ  exp exp         { Formula.Eq  ($2, $3) }
  | GT  exp exp         { Formula.Gt  ($2, $3) }
  | LT  exp exp         { Formula.Lt  ($2, $3) }
  | GTE exp exp         { Formula.Gte ($2, $3) }
  | LTE exp exp         { Formula.Lte ($2, $3) }
; /* TODO: add "And" and "Or". maybe "and" is unnecessary... */

exp:
   ID            { Exp.Var $1 }
 | FNUM          { Exp.Const $1 }
 | LP exp RP     { $2 }
 | PLUS exp exp  { Exp.Add ($2, $3) }
 | MINUS exp exp { Exp.Sub ($2, $3) }
 | AST exp exp   { Exp.Mul ($2, $3) }
 | SLASH exp exp { Exp.Div ($2, $3) }
 | EXP exp       { Exp.Exp $2 }
; /* TODO: support other functions such as sin, cos, ... */

ode_list: /* */ { [] }
 | ode ode_list { $1::$2 }
;

ode: DDT LB ID RB EQ exp SEMICOLON { ($3, $6) }
;

jump_list: /* */ { [] }
  | jump jump_list { $1::$2 }
;

jump:
  formula IMPLY AT FNUM formula SEMICOLON { ($1, int_of_float $4, $5) }
;

init: INIT COLON mode_formula { $3 }
;

goal: GOAL COLON mode_formula_list { $3 }
;

mode_formula_list: /* */ { [] }
  | mode_formula mode_formula_list { $1::$2 }
;

mode_formula: AT FNUM formula SEMICOLON { (int_of_float $2, $3) }
;
