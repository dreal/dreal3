/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{
open Batteries
open Type

(* Maps to handle macros *)
(* const_macro_map : string -> Basic.exp *)
(* fun_macro_map : string -> string list * Basic.exp *)
let const_macro_map = ref (BatMap.empty)
let fun_macro_map = ref (BatMap.empty)

let main_routine vardecl_list mode_list init goal ginv =
  let (float_list, intv_list) =
    List.partition
      (function (_, Value.Num _, _) -> true | _ -> false)
      vardecl_list
  in
  let vardeclmap = Vardeclmap.of_list intv_list in
  let macromap = Vardeclmap.of_list float_list in
  let modemap = Modemap.of_list mode_list in
  let (init_mode, init_formula) = init in
  Hybrid.preprocess (vardeclmap, macromap, modemap, init_mode, init_formula, goal, ginv)
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token HASH_DEFINE
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

%left PLUS MINUS
%left AST SLASH
%left UNARY
%right CARET

%start main

%type <Type.Hybrid.t> main
%type <Type.Hybrid.formula> formula

%%

main: macro_list varDecl_list mode_list init goal ind { main_routine $2 $3 $4 $5 $6 }
| macro_list varDecl_list mode_list init goal { main_routine $2 $3 $4 $5 [] }
;

macro_list: /* */ { }
  | macro macro_list { }
;

param_list: ID { [$1] }
  | ID COMMA param_list { $1::$3 }
;

macro:
    HASH_DEFINE ID LP param_list RP exp { fun_macro_map := BatMap.add $2 ($4, $6) !fun_macro_map }
  | HASH_DEFINE ID exp { const_macro_map := BatMap.add $2 $3 !const_macro_map }
;

varDecl_list: /* */ { [] }
  | varDecl varDecl_list { $1::$2 }
;

varDecl:
  LB exp RB ID SEMICOLON { ($4, Value.Num (Basic.real_eval_noenv $2), Value.Num 0.0) }
  | LB exp COMMA exp RB ID SEMICOLON {
         ($6, Value.Intv (Basic.real_eval_noenv $2,
                          Basic.real_eval_noenv $4),
          Value.Num 0.0)
       }
  | LB exp COMMA exp RB ID LB exp RB SEMICOLON {
         ($6, Value.Intv (Basic.real_eval_noenv $2,
                          Basic.real_eval_noenv $4),
          Value.Num (Basic.real_eval_noenv $8))
       }
;

mode_list: /* */ { [] }
  | mode mode_list { $1::$2 }
;

mode: LC mode_id time_precision invts_op flows jumps RC
  {
    Mode.make ($2, $3, $4, $5, $6, Jumpmap.of_list $6)
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

exp_list: exp { [$1] }
| exp COMMA exp_list { $1::$3 }
;

exp:
   ID {
       if (Map.mem $1 !const_macro_map) then
         (Map.find $1 !const_macro_map)
       else
         Basic.Var $1
     }
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
 | ABS LP exp RP          { Basic.Abs $3 }
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
 | ID LP exp_list RP      {
        let id = $1 in
        let arg_list = $3 in
        if (Map.mem id !fun_macro_map) then
          let (param_list, body) = Map.find id !fun_macro_map in
          let replaced_body = Basic.replace_fun param_list arg_list body in
          replaced_body
        else
          raise (Failure ($1 ^ " is not defined in function-style macro."))
      }
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
    formula IMPLY AT FNUM formula SEMICOLON { Jump.make ($1, int_of_float $4, $5) }
  | formula IMPLY precision AT FNUM formula SEMICOLON { Jump.makep ($1, $3, int_of_float $5, $6) }
;

init: INIT COLON mode_formula { $3 }
;

goal: GOAL COLON mode_formula_list { $3 }
;

ind: IND COLON formula_list { $3 }
;

mode_formula_list: /* */ { [] }
  | mode_formula mode_formula_list { $1::$2 }
;

mode_formula: AT FNUM formula SEMICOLON { (int_of_float $2, $3) }
;
