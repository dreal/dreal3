(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

{
  open Smt2parser
  open Error
  let debug_tag = false
  let verbose s =  if debug_tag then (print_string s; print_newline())
  let comment_depth = ref 0
  let keyword_tbl = Hashtbl.create 111
  let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
    [("sin", SIN);
     ("cos", COS);
     ("tan", TAN);
     ("asin", ASIN);
     ("arcsin", ASIN);
     ("acos", ACOS);
     ("arccos", ACOS);
     ("atan", ATAN);
     ("arctan", ATAN);
     ("arctan2", ATAN2);
     ("atan2", ATAN2);
     ("min", MIN);
     ("max", MAX);
     ("matan", MATAN);
     ("marctan", MATAN);
     ("safesqrt", SAFESQRT);
     ("sinh", SINH);
     ("cosh", COSH);
     ("tanh", TANH);
     ("log", LOG);
     ("exp", EXP);
     ("QF_NRA", QF_NRA);
     ("QF_NRA_ODE", QF_NRA_ODE);
     ("Real", REAL);
     ("Bool", BOOL);
     ("and", AND);
     ("or", OR);
     ("not", NOT);
     ("ite", ITE);
     ("let", LET);
     ("assert", ASSERT);
     ("exit", EXIT);
    ]
}

let blank = [' ' '\t']+
let id = ['a'-'z' 'A'-'Z'](['a'-'z' 'A'-'Z' '0'-'9' '_'])*
let float_number = ('+'|'-')? ['0'-'9']+('.'(['0'-'9']*))?('e'('+'|'-')['0'-'9']+)?
let source = '|' [^'|']* '|'
rule start =
  parse blank { start lexbuf }
    | "\r\n"  { incr_ln (); start lexbuf}
    | '\n'    { incr_ln (); start lexbuf}
    | "set-logic"   { verbose (Lexing.lexeme lexbuf); SETLOGIC }
    | "set-info"    { verbose (Lexing.lexeme lexbuf); SETINFO }
    | "declare-fun" { verbose (Lexing.lexeme lexbuf); DECLAREFUN }
    | "declare-const" { verbose (Lexing.lexeme lexbuf); DECLARECONST }
    | "check-sat"   { verbose (Lexing.lexeme lexbuf); CHECKSAT }
    | "smt-lib-version" { verbose (Lexing.lexeme lexbuf); SMTLIBVERSION }
    | "["     { verbose (Lexing.lexeme lexbuf); LB }
    | "]"     { verbose (Lexing.lexeme lexbuf); RB }
    | "("     { verbose (Lexing.lexeme lexbuf); LP }
    | ")"     { verbose (Lexing.lexeme lexbuf); RP }
    | "oo"    { verbose (Lexing.lexeme lexbuf); INFTY }
    | "="     { verbose (Lexing.lexeme lexbuf); EQ }
    | ">="    { verbose (Lexing.lexeme lexbuf); GE }
    | "<="    { verbose (Lexing.lexeme lexbuf); LE }
    | "=>"    { verbose (Lexing.lexeme lexbuf); IMPLY }
    | ">"     { verbose (Lexing.lexeme lexbuf); GT }
    | "<"     { verbose (Lexing.lexeme lexbuf); LT }
    | "+"     { verbose (Lexing.lexeme lexbuf); PLUS }
    | "-"     { verbose (Lexing.lexeme lexbuf); MINUS }
    | "*"     { verbose (Lexing.lexeme lexbuf); AST }
    | "/"     { verbose (Lexing.lexeme lexbuf); SLASH }
    | ","     { verbose (Lexing.lexeme lexbuf); COMMA }
    | ":"     { verbose (Lexing.lexeme lexbuf); COLON }
    | ";"     { verbose (Lexing.lexeme lexbuf); SEMICOLON }
    | "^"     { verbose (Lexing.lexeme lexbuf); CARET }
    | id { let id = Lexing.lexeme lexbuf
           in verbose ("ID:"^id); try Hashtbl.find keyword_tbl id
             with _ -> ID id
         }
    | float_number { verbose (Lexing.lexeme lexbuf); FNUM (float_of_string(Lexing.lexeme lexbuf)) } (* float *)
    | source       { verbose ("Source:" ^ Lexing.lexeme lexbuf); ID (Lexing.lexeme lexbuf)  }
    | eof { verbose "eof"; EOF}
    | _   { verbose (Lexing.lexeme lexbuf);raise Not_found }
