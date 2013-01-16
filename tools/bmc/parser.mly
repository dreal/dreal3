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
%token AND OR
%token EOF
%token <float> FNUM
%token <string> ID

%start main

%type <Hybrid.t> main
%type <Hybrid.formula> formula

%%

main: varDecl_list DP mode_list DP init goal {
  let vardecl_list = $1 in
  let (float_list, intv_list) =
    BatList.partition
      (function (_, Value.Num _) -> true | _ -> false)
      vardecl_list
  in
  let vardeclmap = Vardeclmap.of_list intv_list in
  let macromap = Vardeclmap.of_list float_list in
  let modemap = Modemap.of_list $3 in
  let (init_mode, init_formula) = $5 in
  let goal = $6 in
  (vardeclmap, macromap, modemap, (init_mode, init_formula), goal)
}
;

varDecl_list: /* */ { [] }
  | varDecl varDecl_list { $1::$2 }
;

varDecl:
    LB FNUM RB ID SEMICOLON { ($4, Value.Num $2) }
  | LB FNUM COMMA FNUM RB ID SEMICOLON { ($6, Value.Intv ($2, $4)) }
;

mode_list: /* */ { [] }
  | mode mode_list { $1::$2 }
;

mode: LC mode_id invts_op flows jumps RC
  {
    ($2, $3, $4, Jumpmap.of_list $5)
  }
;

mode_id: MODE FNUM SEMICOLON { int_of_float $2 }
;

invts_op: /* nothing */ { None }
  | invts { Some $1 }

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
    TRUE                { Dr.True }
  | FALSE               { Dr.False }
  | LP formula RP       { $2 }
  | AND formula formula { Dr.make_and [$2; $3] }
  | OR  formula formula { Dr.make_or  [$2; $3] }
  | EQ  exp exp         { Dr.Eq  ($2, $3) }
  | GT  exp exp         { Dr.Gt  ($2, $3) }
  | LT  exp exp         { Dr.Lt  ($2, $3) }
  | GTE exp exp         { Dr.Ge ($2, $3) }
  | LTE exp exp         { Dr.Le ($2, $3) }
; /* TODO: add "And" and "Or". maybe "and" is unnecessary... */

exp:
   ID            { Dr.Var $1 }
 | FNUM          { Dr.Const $1 }
 | LP exp RP     { $2 }
 | PLUS exp exp  { Dr.Add ($2, $3) }
 | MINUS exp exp { Dr.Sub ($2, $3) }
 | AST exp exp   { Dr.Mul ($2, $3) }
 | SLASH exp exp { Dr.Div ($2, $3) }
 | EXP exp       { Dr.Exp $2 }
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
