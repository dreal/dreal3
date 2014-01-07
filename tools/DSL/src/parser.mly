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

%token IF THEN ELSE SWITCH CASE
%token DEFINE PROCESS PROCEED
%token REAL INT
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
    Int 1
}

macroDecl: 
    DEFINE ID FNUM { Macro ($2, $3) }
;

macroDeclList: 
    | /**/ { [] }
    | macroDecl macroDeclList { $1::$2 }
;

arg:
    | REAL ID { RealVar $2 }
    | INT ID { IntVar $2 }
;

arg_list:
    | /**/ { [] }
    | arg COMMA arg_list { $1::$3 } 
;

exp:
 | ID                     { Var $1 }
 | FNUM                   { Num $1 }
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

stmt:
    | DDT LP ID RP EQ exp SEMICOLON { Ode ($3, $6) }
    /* TODO parse if else */
;

stmt_list:
    | /**/ { [] }
    | stmt stmt_list { $1::$2 }
;

mode: PROCESS ID LP arg_list RP LC stmt_list RC {
    {id = $2; args = $4; stmts = $7}
};

mode_list: 
    | /**/ { [] }
    | mode mode_list { $1::$2 }
;

main_entry: 
    /**/ { 1 }
;