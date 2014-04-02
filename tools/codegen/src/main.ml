open Batteries
open IO
open Type
open Codegen

let usage = "Usage: main.native [<options>] code.dl"

(* Driver *)
let run () =
    let src = ref "" in
    let _ = Arg.parse []
            (fun x -> if Sys.file_exists x then src := x
                      else raise (Arg.Bad (x^": No such file"))) usage
    in
    let lexbuf = Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let ast = Parser.main Lexer.token lexbuf in
    Codegen.emit_program ast

let _ = Printexc.catch run ()
