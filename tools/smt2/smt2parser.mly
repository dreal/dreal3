/*
 * Parser for .smt2 format
 * Soonho Kong (soonhok@cs.cmu.edu)
 */

%{
open Type
%}

%token LB RB LC RC LP RP EQ PLUS MINUS AST SLASH COMMA COLON SEMICOLON
%token AT LT LE GT GE IMPLY DDT CARET DP NOT ITE
%token SIN COS TAN
%token ASIN ACOS ATAN ATAN2 MIN MAX MATAN SAFESQRT
%token SINH COSH TANH
%token LOG EXP SQRT ABS
%token TRUE FALSE
%token AND OR ARROW DOT LET
%token EOF
%token SETLOGIC SETINFO DECLAREFUN ASSERT CHECKSAT EXIT SMTLIBVERSION DECLARECONST
%token QF_NRA QF_NRA_ODE REAL INFTY BOOL
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
 | LP SETINFO COLON SMTLIBVERSION FNUM RP { Smt2_cmd.SetInfo (":" ^ "smt-lib-version", string_of_float $5) }
 | LP SETINFO COLON ID FNUM RP    { Smt2_cmd.SetInfo (":" ^ $4, string_of_float $5) }
 | LP SETINFO COLON ID ID RP      { Smt2_cmd.SetInfo (":" ^ $4, $5) }
 | LP DECLAREFUN ID LP RP REAL RP { Smt2_cmd.DeclareFun ($3, Smt2_cmd.REAL, None, None) }
 | LP DECLAREFUN ID LP RP REAL LB FNUM RB RP {
        let prec_opt = if $8 > 0.0 then Some $8 else None in
        Smt2_cmd.DeclareFun ($3, Smt2_cmd.REAL, prec_opt, None)
      }
 | LP DECLAREFUN ID LP RP REAL LB FNUM COMMA FNUM RB RP {
        let bound_opt = Some ($8, $10) in
        Smt2_cmd.DeclareFun ($3, Smt2_cmd.REAL, None, bound_opt)
      }
 | LP DECLARECONST ID REAL RP     { Smt2_cmd.DeclareConst $3 }
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
  | ID               { Basic.FVar $1 }
  | LP formula RP    { $2 }
  | NOT formula      { Basic.Not $2       }
  | AND formula_list { Basic.And $2       }
  | OR formula_list  { Basic.Or  $2       }
  | IMPLY formula formula { Basic.Imply ($2, $3) }
  | GT exp exp      { Basic.Gt  ($2, $3) }
  | LT exp exp      { Basic.Lt  ($2, $3) }
  | GE exp exp      { Basic.Ge  ($2, $3) }
  | LE exp exp      { Basic.Le  ($2, $3) }
  | EQ exp exp      { Basic.Eq  ($2, $3) }
  | GT exp exp precision      { Basic.Gtp  ($2, $3, $4) }
  | LT exp exp precision       { Basic.Ltp  ($2, $3, $4) }
  | GE exp exp precision       { Basic.Gep  ($2, $3, $4) }
  | LE exp exp precision       { Basic.Lep  ($2, $3, $4) }
  | EQ exp exp precision       { Basic.Eqp  ($2, $3, $4) }
  | exp EQ precision exp        { Basic.Eqp  ($1, $4, $3) }
  | LET LP fbinding_list RP formula   { Basic.LetF ($3, $5) }
  | LET LP ebinding_list RP formula   { Basic.LetE ($3, $5) }
;

precision:
 | LB FNUM RB { $2 }
;


fbinding_list: fbinding  { [$1] }
| fbinding fbinding_list { $1::$2 }
;

fbinding: LP ID formula RP { ($2, $3) }
;

ebinding_list: ebinding  { [$1] }
| ebinding ebinding_list { $1::$2 }
;

ebinding: LP ID exp RP { ($2, $3) }
;


exp_list: exp { [$1] }
| exp exp_list { $1::$2 }
;

exp:
   ID                           { Basic.Var $1 }
 | FNUM                         { Basic.Num $1 }
 | LP exp RP                    { $2 }
 | MINUS exp                    { Basic.Neg $2 }
 | PLUS exp_list                { Basic.Add ($2) }
 | MINUS exp exp_list           { Basic.Sub ($2::$3) }
 | AST exp_list                 { Basic.Mul ($2) }
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
 | MATAN exp                    { Basic.Matan $2 }
 | SAFESQRT exp                 { Basic.Safesqrt $2 }
 | ATAN2 exp exp                { Basic.Atan2 ($2, $3) }
 | SINH exp                     { Basic.Sinh $2 }
 | COSH exp                     { Basic.Cosh $2 }
 | TANH exp                     { Basic.Tanh $2 }
 | ITE formula exp exp { Basic.Ite ($2, $3, $4) }
 | MIN exp exp                  { Basic.Min ($2, $3) }
 | MAX exp exp                  { Basic.Max ($2, $3) }
;
