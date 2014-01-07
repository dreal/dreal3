open Batteries
open IO

let usage = "Usage: main.native [<options>] code.dl"

let run () =
    let src = ref "" in
    let _ = Arg.parse []
            (fun x -> if Sys.file_exists x then src := x
                      else raise (Arg.Bad (x^": No such file"))) usage 
    in
    let lexbuf = Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let _ = print_string !src; print_newline () in 
    Parser.main Lexer.token lexbuf 

let _ = Printexc.catch run ()