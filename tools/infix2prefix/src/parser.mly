/*
 * Soonho Kong (soonhok@cs.cmu.edu)
 * Wei Chen (weichen1@andrew.cmu.edu)
 */

%{
open Batteries
open Type
open Basic
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token LT LTE GT GTE DDT CARET
%token SIN COS TAN ABS
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

%start exp

%type <Type.Basic.exp> exp

%%

ffnum:
    | FNUM { $1 }
    | MINUS FNUM { 0.0 -. $2 }
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
 | exp AST exp                  { Mul [$1; $3] }
 | exp SLASH exp                { Div ($1, $3) }
 | EXP LP exp RP                { Exp $3 }
 | exp CARET exp                { Pow ($1, $3) }
 | ABS LP exp RP                { Abs $3 }
 | SIN LP exp RP                { Sin $3 }
 | COS LP exp RP                { Cos $3 }
 | TAN LP exp RP                { Tan $3 }
 | ASIN LP exp RP               { Asin $3 }
 | ACOS LP exp RP               { Acos $3 }
 | ATAN LP exp RP               { Atan $3 }
 | SINH LP exp RP               { Sinh $3 }
 | COSH LP exp RP               { Cosh $3 }
 | TANH LP exp RP               { Tanh $3 }
;
