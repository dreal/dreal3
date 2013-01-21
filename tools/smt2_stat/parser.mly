/*
 * Parser for .smt2 format
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token AT LT LE GT GE IMPLY DDT CARET DP NOT
%token IF THEN ELSE
%token SIN COS TAN
%token ASIN ACOS ATAN
%token SINH COSH TANH
%token LOG EXP SQRT ABS
%token TRUE FALSE
%token AND OR ARROW DOT
%token EOF
%token SETLOGIC SETINFO DECLAREFUN ASSERT CHECKSAT EXIT
%token QF_NRA QF_NRA_ODE REAL INFTY
%token <float> FNUM
%token <string> ID

%start main

%type <Smt2.t> main
%type <Smt2_cmd.t> cmd
%type <Basic.formula> formula
%type <Basic.exp> exp

%%
main: cmd_list { $1 }
;

cmd_list: cmd { [$1] }
 | cmd cmd_list { $1::$2 }
;

cmd: LP SETLOGIC QF_NRA RP        { Smt2_cmd.SetLogic Smt2_cmd.QF_NRA }
 | LP SETLOGIC QF_NRA_ODE RP      { Smt2_cmd.SetLogic Smt2_cmd.QF_NRA_ODE }
 | LP SETINFO COLON ID FNUM RP    { Smt2_cmd.SetInfo (":" ^ $4, string_of_float $5) }
 | LP DECLAREFUN ID LP RP REAL RP { Smt2_cmd.DeclareFun $3 }
 | LP ASSERT formula RP           { Smt2_cmd.Assert $3 }
 | LP CHECKSAT RP                 { Smt2_cmd.CheckSAT }
 | LP EXIT RP                     { Smt2_cmd.Exit }
;

formula_list: formula { [$1] }
  | formula formula_list { $1::$2 }
;

formula:
    TRUE             { Basic.True }
  | FALSE            { Basic.False }
  | LP formula RP    { $2 }
  | NOT formula      { Basic.Not $2       }
  | AND formula_list { Basic.And $2       }
  | OR formula_list  { Basic.Or  $2       }
  | GT exp exp       { Basic.Gt  ($2, $3) }
  | LT exp exp       { Basic.Lt  ($2, $3) }
  | GE exp exp       { Basic.Ge  ($2, $3) }
  | LE exp exp       { Basic.Le  ($2, $3) }
  | EQ exp exp       { Basic.Eq  ($2, $3) }
  | exp EQ exp       { Basic.Eq  ($1, $3) }
;

exp:
   ID                           { Basic.Var $1 }
 | FNUM                         { Basic.Num $1 }
 | LP exp RP                    { $2 }
 | PLUS exp exp                 { Basic.Add ($2, $3) }
 | MINUS exp                    { Basic.Neg $2 }
 | MINUS exp exp                { Basic.Sub ($2, $3) }
 | AST exp exp                  { Basic.Mul ($2, $3) }
 | SLASH exp exp                { Basic.Div ($2, $3) }
 | CARET exp exp                { Basic.Pow ($2, $3) }
 | SQRT exp                     { Basic.Sqrt $2 }
 | ABS exp                      { Basic.Abs $2 }
 | LOG exp                      { Basic.Log $2 }
 | EXP exp                      { Basic.Exp $2 }
 | SIN exp                      { Basic.Sin $2 }
 | COS exp                      { Basic.Cos $2 }
 | TAN exp                      { Basic.Tan $2 }
 | ASIN exp                     { Basic.Asin $2 }
 | ACOS exp                     { Basic.Acos $2 }
 | ATAN exp                     { Basic.Atan $2 }
 | SINH exp                     { Basic.Sinh $2 }
 | COSH exp                     { Basic.Cosh $2 }
 | TANH exp                     { Basic.Tanh $2 }
 | IF formula THEN exp ELSE exp { Basic.Ite ($2, $4, $6) }
;
