(*
 * Soonho Kong soonhok@cs.cmu.edu
 * Wei Chen weichen1@andrew.cmu.edu
 *)

open Batteries
open IO
open Smt2
open Inv_check

let k = ref 3

let spec = [
  ("-k",
   Arg.Int (fun n -> k := n),
   ": number of unrolling (Default: " ^ (string_of_int !k) ^ ")" );
]
let usage = "Usage: main.native [<options>] <.drh>\n<options> are: "

let run () =
  let src = ref "" in
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    let out = IO.stdout in
    let lexbuf = Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let hm = Drh_parser_networks.main Drh_lexer_networks.start lexbuf in
    let smt = Inv_check.compile (List.hd (Network.automata hm)) 0.01 in (*TODO*)
    begin
      Smt2.print out smt
    end
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()
