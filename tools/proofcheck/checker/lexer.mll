(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

{
  open Parser
  open Batteries
  open Error
  let debug_tag = false
  let verbose s =  if debug_tag then (print_string s; print_newline())
  let comment_depth = ref 0
  let keyword_tbl = Hashtbl.create 111
  let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
    [("after", AFTER);
     ("before", BEFORE);
     ("pruning", PRUNING);
     ("branched", BRANCHED);
     ("is", IS);
     ("in", IN);
     ("on", ON);
     ("conflict", CONFLICT);
     ("detected", DETECTED);
     ("sin", SIN);
     ("cos", COS);
     ("tan", TAN);
     ("safesqrt", SAFESQRT);
     ("asin", ASIN);
     ("acos", ACOS);
     ("atan", ATAN);
     ("arcsin", ASIN);
     ("arccos", ACOS);
     ("arctan", ATAN);
     ("atan2", ATAN2);
     ("arctan2", ATAN2);
     ("matan", MATAN);
     ("marctan", MATAN);
     ("sinh", SINH);
     ("cosh", COSH);
     ("tanh", TANH);
     ("log", LOG);
     ("exp", EXP);
     ("unsat", UNSAT);
     ("not", NOT);
     ("HOLE", HOLE);
     ("tprecision", TIME_PRECISION);
    ]
}

let blank = [' ' '\t']+
let id = ['a'-'z' 'A'-'Z'](['a'-'z' 'A'-'Z' '0'-'9' '_'])*
let dec_lit = ['0'-'9']
let hex_lit = ['0'-'9''a'-'f''A'-'F']
let hex_number = '-'?"0x" hex_lit ('.' hex_lit+)? 'p' ('+'|'-') dec_lit+
let float_number = ('+'|'-')? ['0'-'9']+('.'(['0'-'9']*))?('e'('+'|'-')['0'-'9']+)?

('+'|'-')? ['0'-'9']+('.'(['0'-'9']*))?('e'('+'|'-')['0'-'9']+)?
rule start =
  parse blank { start lexbuf }
    | "\r\n"  { incr_ln (); start lexbuf}
    | '\n'    { incr_ln (); start lexbuf}
    | "Precision" { verbose (Lexing.lexeme lexbuf); PRECISION }
    | "["     { verbose (Lexing.lexeme lexbuf); LB }
    | "]"     { verbose (Lexing.lexeme lexbuf); RB }
    | "("     { verbose (Lexing.lexeme lexbuf); LP }
    | ")"     { verbose (Lexing.lexeme lexbuf); RP }
    | "oo"    { verbose (Lexing.lexeme lexbuf); INFTY }
    | "inf"   { verbose (Lexing.lexeme lexbuf); INFTY }
    | "="     { verbose (Lexing.lexeme lexbuf); EQ }
    | ">="    { verbose (Lexing.lexeme lexbuf); GE }
    | "<="    { verbose (Lexing.lexeme lexbuf); LE }
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
    | hex_number { verbose (Lexing.lexeme lexbuf); FNUM (Float.of_string(Lexing.lexeme lexbuf)) } (* dec float *)
    | float_number { verbose (Lexing.lexeme lexbuf); FNUM (float_of_string(Lexing.lexeme lexbuf)) } (* hex float *)
    | ('-'?)('0'|['1'-'9']dec_lit*) { verbose (Lexing.lexeme lexbuf); FNUM (Float.of_string(Lexing.lexeme lexbuf)) }
    | eof { verbose "eof"; EOF}
    | _ { verbose (Lexing.lexeme lexbuf); EOF }
