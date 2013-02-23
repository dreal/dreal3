(*
 * Lexer for .dr format
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

{
  open Parser
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
     ("atn2", ATAN2);
     ("matan", MATAN);
     ("arctan", ATAN);
     ("sinh", SINH);
     ("cosh", COSH);
     ("tanh", TANH);
     ("sqrt", SQRT);
     ("safesqrt", SAFESQRT);
     ("abs", ABS);
     ("log", LOG);
     ("exp", EXP);
     ("true", TRUE);
     ("false", FALSE);
     ("and", AND);
     ("or", OR);
     ("not", NOT);
     ("if", IF);
     ("then", THEN);
     ("else", ELSE);
    ]
  type state = Normal | Comment
  let curr_state = ref Normal
}

let blank = [' ' '\t']+
let id = ['a'-'z' 'A'-'Z'](['a'-'z' 'A'-'Z' '0'-'9' '_'])*
let float_number = ('+'|'-')? ['0'-'9']+('.'(['0'-'9']*))?
let comment = '/' '/' [^ '\n']*
  rule main = parse
    blank   { main lexbuf }
  | "\r\n"  { incr_ln (); main lexbuf}
  | '\n'    { incr_ln (); main lexbuf}
  | "/*"    { c_style_comment lexbuf }
  | comment { main lexbuf } (* Comment *)
  | "d/dt"  { verbose (Lexing.lexeme lexbuf); DDT }
  | "->"    { verbose (Lexing.lexeme lexbuf); ARROW }
  | "["     { verbose (Lexing.lexeme lexbuf); LB }
  | "]"     { verbose (Lexing.lexeme lexbuf); RB }
  | "{"     { verbose (Lexing.lexeme lexbuf); LC }
  | "}"     { verbose (Lexing.lexeme lexbuf); RC }
  | "("     { verbose (Lexing.lexeme lexbuf); LP }
  | ")"     { verbose (Lexing.lexeme lexbuf); RP }
  | "="     { verbose (Lexing.lexeme lexbuf); EQ }
  | "."     { verbose (Lexing.lexeme lexbuf); DOT }
  | "+"     { verbose (Lexing.lexeme lexbuf); PLUS }
  | "-"     { verbose (Lexing.lexeme lexbuf); MINUS }
  | "*"     { verbose (Lexing.lexeme lexbuf); AST }
  | "/"     { verbose (Lexing.lexeme lexbuf); SLASH }
  | "^"     { verbose (Lexing.lexeme lexbuf); CARET }
  | ","     { verbose (Lexing.lexeme lexbuf); COMMA }
  | ":"     { verbose (Lexing.lexeme lexbuf); COLON }
  | ";"     { verbose (Lexing.lexeme lexbuf); SEMICOLON }
  | "@"     { verbose (Lexing.lexeme lexbuf); AT }
  | "<"     { verbose (Lexing.lexeme lexbuf); LT }
  | "<="    { verbose (Lexing.lexeme lexbuf); LE }
  | ">"     { verbose (Lexing.lexeme lexbuf); GT }
  | ">="    { verbose (Lexing.lexeme lexbuf); GE }
  | id { let id = Lexing.lexeme lexbuf
         in verbose ("ID:"^id); try Hashtbl.find keyword_tbl id
           with _ -> ID id
       }
  | float_number {
    verbose (Lexing.lexeme lexbuf);
    FNUM (float_of_string(Lexing.lexeme lexbuf))
  } (* float *)
  | eof { verbose "eof"; EOF}
and c_style_comment = parse
    "*/"    { main lexbuf }
  | _       { c_style_comment lexbuf }
