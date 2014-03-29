{

(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 * Wei Chen (weichen1@andrew.cmu.edu)
 *)

open Parser

let debug_tag = false
let verbose s =  if debug_tag then (print_string s; print_newline())
let keyword_tbl = Hashtbl.create 255
let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
  [
    ("abs", ABS);
    ("sin", SIN);
    ("cos", COS);
    ("tan", TAN);
    ("asin", ASIN);
    ("acos", ACOS);
    ("atan", ATAN);
    ("sinh", SINH);
    ("cosh", COSH);
    ("tanh", TANH);
    ("log", LOG);
    ("exp", EXP);
    ("true", TRUE);
    ("false", FALSE);
    ("and", AND);
    ("or", OR);

    (* types *)
    (* todo: do we need to differient thest two values ? *)
    ("int", INT);
    ("real", REAL);

    (* main loop definition *)
    ("proceed", PROCEED);
    (* ode definition *)
    ("process", PROCESS);
    ("assert", ASSERT);
    ("if", IF);
    ("then", THEN);
    ("else", ELSE);
    ("switch", SWITCH);
    ("case", CASE);
    ("main", MAINENTRY);
  ]
}

let float_number = ('+')? ['0'-'9']+('.'(['0'-'9']*))?(('e'|'E')('+'|'-')?['0'-'9']+)?
let id = ['a'-'z' 'A'-'Z'](['a'-'z' 'A'-'Z' '0'-'9' '_' '\''])*

rule token = parse
    | '{'       { verbose (Lexing.lexeme lexbuf); LC }
    | '}'       { verbose (Lexing.lexeme lexbuf); RC }
    | '('       { verbose (Lexing.lexeme lexbuf); LP }
    | ')'       { verbose (Lexing.lexeme lexbuf); RP }
    | '['       { verbose (Lexing.lexeme lexbuf); LB }
    | ']'       { verbose (Lexing.lexeme lexbuf); RB }

    | "d/dt"    { verbose (Lexing.lexeme lexbuf); DDT }

    (* operators *)
    | "="       { verbose (Lexing.lexeme lexbuf); EQ }
    | "+"       { verbose (Lexing.lexeme lexbuf); PLUS }
    | "-"       { verbose (Lexing.lexeme lexbuf); MINUS }
    | "*"       { verbose (Lexing.lexeme lexbuf); AST }
    | "/"       { verbose (Lexing.lexeme lexbuf); SLASH }
    | "//"      { verbose (Lexing.lexeme lexbuf); comment lexbuf }
    | ","       { verbose (Lexing.lexeme lexbuf); COMMA }
    | ":"       { verbose (Lexing.lexeme lexbuf); COLON }
    | ";"       { verbose (Lexing.lexeme lexbuf); SEMICOLON }
    | "<"       { verbose (Lexing.lexeme lexbuf); LT }
    | "<="      { verbose (Lexing.lexeme lexbuf); LTE }
    | ">"       { verbose (Lexing.lexeme lexbuf); GT }
    | ">="      { verbose (Lexing.lexeme lexbuf); GTE }
    | "^"       { verbose (Lexing.lexeme lexbuf); CARET }
    | "||"      { verbose (Lexing.lexeme lexbuf); OR }
    | "&&"      { verbose (Lexing.lexeme lexbuf); AND }

    (* identifier *)
    | id {
            let id = Lexing.lexeme lexbuf in

            try
              let r = Hashtbl.find keyword_tbl id in
              verbose ("Keyword: "^id);
              r
            with _ ->
              begin
              verbose ("ID: "^id);
              ID id
              end
         }
    | "#define" { verbose (Lexing.lexeme lexbuf); DEFINE }

    (* float *)
    | float_number { verbose (Lexing.lexeme lexbuf); FNUM (float_of_string(Lexing.lexeme lexbuf)) }

    (* skip blank *)
    | [' ' '\t'] { token lexbuf }

    (* end *)
    | ['\n'] { token lexbuf }
    | eof { verbose "eof"; EOF }
and comment = parse
    | ['\n'] { token lexbuf }
    | _ { comment lexbuf }
