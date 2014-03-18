/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 * Wei Chen (weichen1@andrew.cmu.edu)
 */

%{
open Batteries
open Type
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token LT LTE GT GTE DDT CARET
%token SIN COS TAN
%token ASIN ACOS ATAN
%token SINH COSH TANH
%token LOG EXP
%token TRUE FALSE
%token AND OR
%token EOF
%token MAINENTRY

%token IF THEN ELSE SWITCH CASE
%token DEFINE PROCESS PROCEED
%token REAL INT ASSERT
%token <float> FNUM
%token <string> ID

%left PLUS MINUS
%left AST SLASH
%left NEG
%right CARET

%start main

%type <Type.t> main

%%

main: macroDeclList mode_list main_entry {
    {macros = $1; modes = $2; main = $3}
}

macroDecl:
    | DEFINE ID ffnum { Macro ($2, $3) }
;

macroDeclList:
    | /**/ { [] }
    | macroDecl { [$1] }
    | macroDecl macroDeclList { $1::$2 }
;

ffnum:
    | FNUM { $1 }
    | MINUS FNUM { 0.0 -. $2 }
;

arg:
    | REAL ID { RealVar $2 }
    | INT ID { IntVar $2 }
;

arg_list:
    | /**/ { [] }
    | arg { [$1] }
    | arg COMMA arg_list { $1::$3 }
;

exp:
 | ID                     { Var $1 }
 | ffnum                   { Num $1 }
 | LP exp RP              { $2 }
 | exp PLUS exp           { Add [$1; $3] }
 | exp MINUS exp          { Sub [$1; $3] }
 | MINUS exp %prec NEG    {
   match $2 with
   | Num n -> Num (0.0 -. n)
   | _ -> Neg $2
 }
 | exp AST exp            { Mul [$1; $3] }
 | exp SLASH exp          { Div ($1, $3) }
 | EXP exp                { Exp $2 }
 | exp CARET exp          { Pow ($1, $3) }
 | SIN exp                { Sin $2 }
 | COS exp                { Cos $2 }
 | TAN exp                { Tan $2 }
 | ASIN exp               { Asin $2 }
 | ACOS exp               { Acos $2 }
 | ATAN exp               { Atan $2 }
 | SINH exp               { Sinh $2 }
 | COSH exp               { Cosh $2 }
 | TANH exp               { Tanh $2 }
;

/* boolean expression */
/* todo: and & or */
bexp:
  | TRUE                { B_true }
  | FALSE               { B_false }
  | ID                  { B_var $1 }
  | LP bexp RP          { $2 }
  | exp EQ exp          { B_eq  ($1, $3) }
  | exp GT exp          { B_gt  ($1, $3) }
  | exp LT exp          { B_lt  ($1, $3) }
  | exp GTE exp         { B_ge ($1, $3) }
  | exp LTE exp         { B_le ($1, $3) }
  | bexp OR bexp        { B_or ($1, $3) }
  | bexp AND bexp       { B_and ($1, $3) }
;

choice:
    | CASE ffnum COLON stmt_list { Case ($2, $4) }
;

choices:
    | /**/ { [] }
    | choice choices { $1::$2 }
;

switch:
    | SWITCH LP ID RP LC choices RC { Switch ($3, $6) }
;

params:
    | /**/ { [] }
    | exp { [$1] }
    | exp COMMA params { $1::$3 }
;

id:
    | ID { $1 }
;

ids:
    | /**/ { [] }
    | id { [$1] }
    | id COMMA ids { $1::$3 }
;

stmt:
    | DDT LB ID RB EQ exp SEMICOLON                           { [Ode ($3, $6)] }
    | ID EQ exp SEMICOLON                                     { [Assign ($1, $3)] }
    | REAL ID EQ exp SEMICOLON                                { [Vardecl (RealVar $2); Assign ($2, $4);] }
    | INT ID EQ exp SEMICOLON                                 { [Vardecl (IntVar $2); Assign ($2, $4);] }

    | REAL ids SEMICOLON                                      { List.map (fun v -> Vardecl (RealVar v)) $2 }
    | REAL LB ffnum COMMA ffnum RB ID SEMICOLON               { [Vardecl (BRealVar ($7, $3, $5))] }
    | INT ids SEMICOLON                                       { List.map (fun v -> Vardecl (IntVar v)) $2 }

    | IF bexp THEN LC stmt_list RC                            { [If ($2, $5, [])] }
    | IF bexp THEN LC stmt_list RC ELSE LC stmt_list RC       { [If ($2, $5, $9)] }

    | PROCEED LC stmt_list RC                                 { [Proceed $3] }

    | switch                                                  { [$1] }
    | ASSERT LP bexp RP SEMICOLON                             { [Assert $3] }
    | ID LP params RP SEMICOLON                               { [Invoke ($1, $3)] }
;

stmt_list:
    | /**/ { [] }
    | stmt stmt_list { $1@$2 }
;

mode: PROCESS ID LP arg_list RP LC stmt_list RC {
    {id = $2; args = $4; stmts = $7}
};

mode_list:
    | /**/ { [] }
    | mode mode_list { $1::$2 }
;

main_entry: INT MAINENTRY LP RP LC stmt_list RC {
    Main $6
};
