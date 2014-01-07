open Batteries
open IO

let run () =
  let lexbuf = Lexing.from_channel stdin in
  Parser.main Lexer.token lexbuf 

let _ = Printexc.catch run ()