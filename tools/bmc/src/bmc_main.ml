(*
 * Soonho Kong soonhok@cs.cmu.edu
 * Wei Chen weichen1@andrew.cmu.edu
 *)

open Batteries
open IO
open Smt2
open Type

let k = ref 3 (* default unrolling value is 3 *)
let pathgen = ref false
let path = ref None

(* Takes in string s (ex: "[1,2,3,4,5]")
   and return int list [1;2;3;4;5]        *)
let process_path (s : string) : int list =
  match (String.starts_with s "[", String.ends_with s "]") with
    (true, true) ->
      begin
        let content = String.sub s 1 ((String.length s) - 2) in
        let items = String.nsplit content "," in
        let path = List.map Int.of_string items in
        path
      end
  | _ -> raise (Arg.Bad ("Path " ^ s ^ " is not well-formed"))

let spec = [
  ("-k",
   Arg.Int (fun n -> k := n),
   ": number of unrolling (Default: " ^ (string_of_int !k) ^ ")" );
  ("--pathgen",
   Arg.Unit (fun n -> pathgen := true),
   ": generate paths");
  ("--path",
   Arg.String (fun s -> path := Some (process_path s)),
   ": specify the path (ex: \"[1,2,1,2,1]\" to focus (Default: none)");
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
    let hm = Drh_infix_parser.main Drh_infix_lexer.start lexbuf in
    if !pathgen then
      let paths = Bmc.pathgen hm !k in
      List.print ~first:"" ~last:"\n" ~sep:"\n"
                 (fun out path ->
                  List.print ~first:"[" ~last:"]" ~sep:"," Int.print out path)
                 out
                 paths
    else
      let _ = Hybrid.check_path hm !path !k in
      let smt = Bmc.compile hm !k !path in
      Smt2.print out smt
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()
