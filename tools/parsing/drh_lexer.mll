(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

{
  open Drh_parser
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
     ("acos", ACOS);
     ("atan", ATAN);
     ("sinh", SINH);
     ("cosh", COSH);
     ("tanh", TANH);
     ("sqrt", SQRT);
     ("abs", ABS);
     ("log", LOG);
     ("exp", EXP);
     ("mode", MODE);
     ("macr", MACR);
     ("timeprecision", TIME_PRECISION);
     ("invt", INVT);
     ("flow", FLOW);
     ("jump", JUMP);
     ("init", INIT);
     ("goal", GOAL);
     ("ind", IND);
     ("true", TRUE);
     ("false", FALSE);
     ("and", AND);
     ("or", OR);
     ("not", NOT);
    ]
}

let blank = [' ' '\t']+
let id = ['a'-'z' 'A'-'Z'](['a'-'z' 'A'-'Z' '0'-'9' '_' '\''])*
let float_number = ['0'-'9']+('.'(['0'-'9']*))?(('e'|'E')('+'|'-')?['0'-'9']+)?
rule start =
  parse blank { start lexbuf }
    | "\r\n"  { incr_ln (); start lexbuf}
    | '\n'    { incr_ln (); start lexbuf}
    | "//[A-Za-z0-9 ]+" { start lexbuf }                        (* Comment *)
    | "["     { verbose (Lexing.lexeme lexbuf); LB }
    | "]"     { verbose (Lexing.lexeme lexbuf); RB }
    | "{"     { verbose (Lexing.lexeme lexbuf); LC }
    | "}"     { verbose (Lexing.lexeme lexbuf); RC }
    | "("     { verbose (Lexing.lexeme lexbuf); LP }
    | ")"     { verbose (Lexing.lexeme lexbuf); RP }
    | "="     { verbose (Lexing.lexeme lexbuf); EQ }
    | "+"     { verbose (Lexing.lexeme lexbuf); PLUS }
    | "-"     { verbose (Lexing.lexeme lexbuf); MINUS }
    | "*"     { verbose (Lexing.lexeme lexbuf); AST }
    | "/"     { verbose (Lexing.lexeme lexbuf); SLASH }
    | ","     { verbose (Lexing.lexeme lexbuf); COMMA }
    | ":"     { verbose (Lexing.lexeme lexbuf); COLON }
    | ";"     { verbose (Lexing.lexeme lexbuf); SEMICOLON }
    | "@"     { verbose (Lexing.lexeme lexbuf); AT }
    | "<"     { verbose (Lexing.lexeme lexbuf); LT }
    | "<="    { verbose (Lexing.lexeme lexbuf); LTE }
    | ">"     { verbose (Lexing.lexeme lexbuf); GT }
    | ">="    { verbose (Lexing.lexeme lexbuf); GTE }
    | "==>"   { verbose (Lexing.lexeme lexbuf); IMPLY }
    | "d/dt"  { verbose (Lexing.lexeme lexbuf); DDT }
    | "^"     { verbose (Lexing.lexeme lexbuf); CARET }
    | id { let id = Lexing.lexeme lexbuf
           in verbose ("ID:"^id); try Hashtbl.find keyword_tbl id
             with _ -> ID id
         }
    | float_number { verbose (Lexing.lexeme lexbuf); FNUM (float_of_string(Lexing.lexeme lexbuf)) } (* float *)
    | eof { verbose "eof"; EOF}
    | _ { raise (Error.Lex_err (Lexing.lexeme lexbuf, !linenum)) }
