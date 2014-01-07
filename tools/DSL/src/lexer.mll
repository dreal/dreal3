{

(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 * Wei Chen (weichen1@andrew.cmu.edu)
 *)

open Parser
let keyword_tbl = Hashtbl.create 255
let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
  [
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

    ("#define", DEFINE);

    ("if", IF);
    ("then", THEN);
    ("else", ELSE);
    ("switch", SWITCH);
    ("case", CASE);
  ]
}

let float_number = ('+')? ['0'-'9']+('.'(['0'-'9']*))?(('e'|'E')('+'|'-')?['0'-'9']+)?
let id = ['a'-'z' 'A'-'Z'](['a'-'z' 'A'-'Z' '0'-'9' '_' '\''])*

rule token = parse
    | '{'       { LC }
    | '{'       { RC }
    | '('       { LP }
    | ')'       { RP }
    | '['       { LB }
    | ']'       { RB }

    | "d/dt"    { DDT }

    (* operators *)
    | "="       { EQ }
    | "+"       { PLUS }
    | "-"       { MINUS }
    | "*"       { AST }
    | "/"       { SLASH }
    | ","       { COMMA }
    | ":"       { COLON }
    | ";"       { SEMICOLON }
    | "<"       { LT }
    | "<="      { LTE }
    | ">"       { GT }
    | ">="      { GTE }
    | "^"       { CARET }

    (* identifier *)
    | id { 
            let id = Lexing.lexeme lexbuf
            in try Hashtbl.find keyword_tbl id
            with _ -> ID id
         }

    (* float *)
    | float_number { FNUM (float_of_string(Lexing.lexeme lexbuf)) } 

    (* skip blank *)
    | [' ' '\t'] { token lexbuf }

    (* end *)
    | ['\n'] { EOF }
    | eof { EOF }