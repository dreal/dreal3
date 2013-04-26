/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{

%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token AT LT LTE GT GTE IMPLY DDT CARET
%token SIN COS TAN
%token ASIN ACOS ATAN
%token SINH COSH TANH
%token LOG EXP
%token MODE MACR INVT FLOW JUMP INIT GOAL TRUE FALSE
%token AND OR
%token EOF
%token <float> FNUM
%token <string> ID

%left PLUS MINUS NEG
%left TIMES DIVIDE
%left NEG
%right CARET

%start main

%type <Hybrid.t> main
%type <Hybrid.formula> formula

%%

main: varDecl_list mode_list init goal {
  let vardecl_list = $1 in
  let (float_list, intv_list) =
    BatList.partition
      (function (_, Value.Num _) -> true | _ -> false)
      vardecl_list
  in
  let vardeclmap = Vardeclmap.of_list intv_list in
  let macromap = Vardeclmap.of_list float_list in
  let modemap = Modemap.of_list $2 in
  let (init_mode, init_formula) = $3 in
  let goal = $4 in
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

formulas: /* */ { [] }
  | formula formulas { $1::$2 }
;


formula:
    TRUE                { Dr.True }
  | FALSE               { Dr.False }
  | LP formula RP       { $2 }
  | AND formulas        { Dr.make_and $2 }
  | OR  formulas        { Dr.make_or  $2 }
  | exp EQ exp         { Dr.Eq  ($1, $3) }
  | exp GT exp         { Dr.Gt  ($1, $3) }
  | exp LT exp         { Dr.Lt  ($1, $3) }
  | exp GTE exp         { Dr.Ge ($1, $3) }
  | exp LTE exp         { Dr.Le ($1, $3) }
; /* TODO: add "And" and "Or". maybe "and" is unnecessary... */

exp:
   ID            { Dr.Var $1 }
 | FNUM          { Dr.Const $1 }
 | LP exp RP     { $2 }
 | exp PLUS exp  { Dr.Add ($1, $3) }
 | exp MINUS exp { Dr.Sub ($1, $3) }
 | MINUS exp %prec NEG    { Dr.Neg $2 }
 | exp AST exp   { Dr.Mul ($1, $3) }
 | exp SLASH exp { Dr.Div ($1, $3) }
 | EXP exp       { Dr.Exp $2 }
 | exp CARET exp { Dr.Pow ($1, $3) }
 | SIN exp       { Dr.Sin $2 }
 | COS exp       { Dr.Cos $2 }
 | TAN exp       { Dr.Tan $2 }
 | ASIN exp      { Dr.Asin $2 }
 | ACOS exp      { Dr.Acos $2 }
 | ATAN exp      { Dr.Atan $2 }
 | SINH exp      { Dr.Sinh $2 }
 | COSH exp      { Dr.Cosh $2 }
 | TANH exp      { Dr.Tanh $2 }
;

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
