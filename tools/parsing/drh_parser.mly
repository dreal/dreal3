/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{
open Batteries
open Type

let main_routine vardecl_list mode_list init goal ginv =
  let (float_list, intv_list) =
    List.partition
      (function (_, Value.Num _) -> true | _ -> false)
      vardecl_list
  in
  let vardeclmap = Vardeclmap.of_list intv_list in
  let macromap = Vardeclmap.of_list float_list in
  let modemap = Modemap.of_list mode_list in
  let (init_mode, init_formula) = init in
  Hybrid.preprocess (vardeclmap, macromap, modemap, init_mode, init_formula, goal, ginv, "singleton", 0, [])
  
let remove_time (singleton: Hybrid.t) = 
  let vm = Map.remove "time" (Hybrid.vardeclmap singleton) in
  let mm = Hybrid.modemap singleton in
  let init_id = Hybrid.init_id singleton in
  let init_formula = Hybrid.init_formula singleton in
  let goals = Hybrid.goals singleton in
  let ginvs = Hybrid.ginvs singleton in
  let name = Hybrid.name singleton in
  let num_id = Hybrid.numid singleton in
  let labellist = Hybrid.labellist singleton in
  Hybrid.make (vm, mm, init_id, init_formula, goals, ginvs, name, num_id, labellist)
  
let get_network (singleton: Hybrid.t) = 
  (* analyze :: [string, [(string, string)]]*)
  let base = "singleton" in
  let inst = "singleton0" in
  let subs = [] in
  let init = (Hybrid.init_id singleton, Hybrid.init_formula singleton) in
  let anal = ([(inst, base, subs, init)], ["singleton0"]) in
  let vars = Hybrid.vardeclmap singleton in
  let time = ("time", Map.find "time" vars) in
  let (mid, mfo) = List.hd (Hybrid.goals singleton) in (* [(modeid, formula)] *)
  Network.postprocess_network (Network.makep (time, [remove_time singleton], Vardeclmap.of_list [], ([(inst, mid)], mfo))) anal
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token AT LT LTE GT GTE IMPLY DDT CARET NOT
%token SIN COS TAN
%token ASIN ACOS ATAN ATAN2 MIN MAX
%token SINH COSH TANH
%token LOG EXP SQRT ABS
%token MODE MACR INVT FLOW JUMP INIT GOAL IND TRUE FALSE TIME_PRECISION
%token AND OR
%token EOF
%token <float> FNUM
%token <string> ID
/* unused*/
%token COMPONENT LABEL ANALYZE PIPE DOT

%left PLUS MINUS
%left AST SLASH
%left UNARY
%right CARET

%start main

%type <Type.Network.t> main
%type <Type.Hybrid.formula> formula

%%

main: varDecl_list mode_list init goal ind { get_network (main_routine $1 $2 $3 $4 $5) }
| varDecl_list mode_list init goal { get_network (main_routine $1 $2 $3 $4 []) }
;

varDecl_list: /* */ { [] }
  | varDecl varDecl_list { $1::$2 }
;

FFNUM: FNUM { $1 }
  | MINUS FNUM { 0.0 -. $2 }
;

varDecl:
    LB FFNUM RB ID SEMICOLON { ($4, Value.Num $2) }
  | LB FFNUM COMMA FFNUM RB ID SEMICOLON { ($6, Value.Intv ($2, $4)) }
;

mode_list: /* */ { [] }
  | mode mode_list { $1::$2 }
;

mode: LC mode_id time_precision invts_op flows jumps RC
  {
    Mode.make (string_of_int $2, $2, $3, $4, $5, $6, Jumpmap.of_list $6, 0)
  }
;

mode_id: MODE FNUM SEMICOLON { int_of_float $2 }
;

time_precision: TIME_PRECISION COLON FNUM SEMICOLON { $3 }
| { 0.0 }
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
    TRUE                { Basic.True }
  | FALSE               { Basic.False }
  | NOT formula         { Basic.Not $2 }
  | LP formula RP       { $2 }
  | AND formulas        { Basic.make_and $2 }
  | OR  formulas        { Basic.make_or  $2 }
  | exp EQ exp          { Basic.Eq  ($1, $3) }
  | exp GT exp          { Basic.Gt  ($1, $3) }
  | exp LT exp          { Basic.Lt  ($1, $3) }
  | exp GTE exp         { Basic.Ge ($1, $3) }
  | exp LTE exp         { Basic.Le ($1, $3) }
  | exp EQ precision exp          { Basic.Eqp  ($1, $4, $3) }
  | exp GT precision exp          { Basic.Gtp  ($1, $4, $3) }
  | exp LT precision exp          { Basic.Ltp  ($1, $4, $3) }
  | exp GTE precision exp         { Basic.Gep ($1, $4, $3) }
  | exp LTE precision exp         { Basic.Lep ($1, $4, $3) }
;

exp:
   ID                     { Basic.Var $1 }
 | FNUM                   { Basic.Num $1 }
 | LP exp RP              { $2 }
 | exp PLUS exp           { Basic.Add [$1; $3] }
 | exp MINUS exp          { Basic.Sub [$1; $3] }
 | PLUS exp %prec UNARY   { $2 }
 | MINUS exp %prec UNARY  {
   match $2 with
   | Basic.Num n -> Basic.Num (0.0 -. n)
   | _ -> Basic.Neg $2
 }
 | exp AST exp            { Basic.Mul [$1; $3] }
 | exp SLASH exp          { Basic.Div ($1, $3) }
 | exp CARET exp          { Basic.Pow ($1, $3) }
 | SQRT LP exp RP         { Basic.Sqrt $3 }
 | ABS LP exp RP         { Basic.Abs $3 }
 | LOG  LP exp RP         { Basic.Log  $3 }
 | EXP  LP exp RP         { Basic.Exp  $3 }
 | SIN  LP exp RP         { Basic.Sin  $3 }
 | COS  LP exp RP         { Basic.Cos  $3 }
 | TAN  LP exp RP         { Basic.Tan  $3 }
 | ASIN LP exp RP         { Basic.Asin $3 }
 | ACOS LP exp RP         { Basic.Acos $3 }
 | ATAN LP exp RP         { Basic.Atan $3 }
 | ATAN2 LP exp COMMA exp RP { Basic.Atan2 ($3, $5) }
 | MIN  LP exp COMMA exp RP  { Basic.Min ($3, $5) }
 | MAX  LP exp COMMA exp RP  { Basic.Max ($3, $5) }
 | SINH LP exp RP         { Basic.Sinh $3 }
 | COSH LP exp RP         { Basic.Cosh $3 }
 | TANH LP exp RP         { Basic.Tanh $3 }
;

precision:
 | LB FNUM RB { $2 }
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
    formula IMPLY AT FNUM formula SEMICOLON { Jump.make ($1, string_of_int (int_of_float $4), $5, []) }
  | formula IMPLY precision AT FNUM formula SEMICOLON { Jump.makep ($1, $3, string_of_int (int_of_float $5), $6, []) }
;



init: INIT COLON mode_formula { $3 }
;

goal: GOAL COLON mode_formula_list { $3 }
;

ind: IND COLON formula_list { $3 }
;

formula_list:
  | /**/ { [] }
  | formula SEMICOLON formula_list { $1 :: $3 }
;

mode_formula_list: /* */ { [] }
  | mode_formula mode_formula_list { $1::$2 }
;

mode_formula: AT FNUM formula SEMICOLON { (string_of_int (int_of_float $2), $3) }
;
