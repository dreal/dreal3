/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{
open Batteries
open Type

let get_hybrid vardecl_list mode_list init goal ginv n label_list =
  let (float_list, intv_list) =
    List.partition
      (function (_, Value.Num _, _) -> true | _ -> false)
      vardecl_list
  in
  let vardeclmap = Vardeclmap.of_list intv_list in
  let macromap = Vardeclmap.of_list float_list in
  let modemap = Modemap.of_list mode_list in
  let (init_mode, init_formula) = init in
  Hybrid.preprocess (vardeclmap, macromap, modemap, init_mode, init_formula, goal, ginv, n, 0, label_list)
  
let get_network time_decl hybrid_list analyze goals_list = 
	(* analyze :: [string, [(string, string)]]*)
	let (instances, composition) = analyze in
    Network.postprocess_network (Network.makep (time_decl, hybrid_list, Vardeclmap.of_list [], goals_list)) analyze
%}

%token COMPONENT LABEL ANALYZE DOT
%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON PIPE
%token AT LT LTE GT GTE IMPLY DDT CARET NOT
%token SIN COS TAN
%token ASIN ACOS ATAN
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

%type <Type.Network.automaton> hybrid
%type <Type.Network.automata> hybrid_list
%type <Type.Hybrid.formula> formula

%type <Type.Network.t> main

%%

main: time_decl hybrid_list analyze goal_aut { get_network $1 $2 $3 $4 }
;

time_decl: varDecl { $1 }

hybrid_list : { [] } 
          | hybrid hybrid_list { $1::$2 }
;

hybrid: LP COMPONENT ID SEMICOLON varDecl_list label_list mode_list RP { get_hybrid $5 $7 ("", Basic.True) [] [] $3 $6 }
;

label_list: { [] } 
          | labelDecl label_list { $1@$2 }
;

labelDecl: LABEL label_list_ids SEMICOLON { $2 }
;

label_list_ids: { [] }
              | ID label_list_ids { $1::$2 }
              | COMMA label_list_ids { $2 }
;

varDecl_list: /* */ { [] }
  | varDecl varDecl_list { $1::$2 }
;

FFNUM: FNUM { $1 }
  | MINUS FNUM { 0.0 -. $2 }
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

analyze: ANALYZE COLON hybrid_instance_list LP hybrid_analyze_composition RP SEMICOLON { ($3, $5) } 
;

analyze_list: { [] }
            | PIPE PIPE analyze_list { $3 }
            | substitution analyze_list { $1::$2 }
;

substitution: ID LB substitution_list RB { ($1, $3) }
;

substitution_list: { [] }
                 | substitution_id substitution_list { $1::$2 }
                 | COMMA substitution_list { $2 }
;

substitution_id: ID SLASH ID { ($1, $3) }
;

hybrid_instance_analyze_list: { [] }
							| PIPE PIPE hybrid_instance_analyze_list { $3 }
							| ID hybrid_instance_analyze_list { ($1, [])::$2 }
							| ID LB substitution_list RB hybrid_instance_analyze_list { ($1, $3)::$5 }  
;

hybrid_analyze_composition: { [] }
							| PIPE PIPE  hybrid_analyze_composition { $3 }
							| ID hybrid_analyze_composition { $1::$2 }

hybrid_instance_list: { [] }
					| hybrid_instance hybrid_instance_list { $1::$2 }
;

hybrid_instance: 
	ID EQ ID 								/* 1, 2, 3 */
	LB 										/* 4 */
	hybrid_instance_substitution COMMA 		/* 5, 6 */
	mode_formula				 			/* 7 */
	RB SEMICOLON 							/* 8, 9 */
	{ ($1, $3, $5, $7) }
;

hybrid_instance_substitution: LB substitution_list RB { $2 }
;

mode_list: /* */ { [] }
  | mode mode_list { $1::$2 }
;

mode: LP mode_id_str SEMICOLON time_precision invts_op flows jumps RP
  {
    Mode.make ($2, 0, $4, $5, $6, $7, Jumpmap.of_list $7, 0)
  }
;

mode_id_str: MODE ID { $2 }
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
  | jump_str jump_list { $1::$2 }
;

jump_str: 
	jump_labels formula IMPLY AT ID formula SEMICOLON { Jump.make ($2, $5, $6, $1) }
  | jump_labels formula IMPLY precision AT ID formula SEMICOLON { Jump.makep ($2, $4, $6, $7, $1) }
;

jump_labels:
	LP label_list_ids RP COLON { $2 }
;

init: INIT COLON mode_formula SEMICOLON { $3 }
;

goal_aut: GOAL COLON goal_aut_elem { $3 }
;

goal_aut_elems: { [] }
	| goal_aut_elem goal_aut_elems { $1::$2 }
;

goal_aut_elem: LP loc_list RP COLON formula SEMICOLON { ($2, $5) }
;

loc_list: 
	| { [] }
	| AT ID DOT ID loc_list { ($2, $4)::$5 }
	| COMMA loc_list { $2 }
;

formula_list:
  |  { [] }
  | formula SEMICOLON formula_list { $1::$3 }
;

mode_formula_list: { [] }
  | mode_formula SEMICOLON mode_formula_list { $1::$3 }
;

mode_formula: AT ID formula { ($2, $3) }
;

mode_formula_aut_list: { [] }
  | mode_formula_aut mode_formula_aut_list { $1::$2 }
;

mode_formula_aut: formula { (("", ""), $1) }
                | AT ID DOT ID formula SEMICOLON { (($2, $4), $5) }
;
