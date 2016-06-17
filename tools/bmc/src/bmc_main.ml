(*
 * Soonho Kong soonhok@cs.cmu.edu
 * Wei Chen weichen1@andrew.cmu.edu
 *)

open Batteries
open IO
open Smt2
open Type
open Heuristic

let k = ref 3 (* default unrolling value is 3 *)
let pathgen = ref false
let bmc_heuristic_prune = ref None
let path = ref None
let new_format = ref false
let new_format_composed = ref false
let len_filter = ref false

(* Takes in string s (ex: "[1,2,3,4,5]")
   and return int list [1;2;3;4;5]        *)
let process_path (s : string) : string list =
  match (String.starts_with s "[", String.ends_with s "]") with
    (true, true) ->
      begin
        let content = String.sub s 1 ((String.length s) - 2) in
        let items = String.nsplit content "," in
        let path = items in
        path
      end
  | _ -> raise (Arg.Bad ("Path " ^ s ^ " is not well-formed"))

(*let process_path (s : string) : int list =
  match (String.starts_with s "[", String.ends_with s "]") with
    (true, true) ->
      begin
        let content = String.sub s 1 ((String.length s) - 2) in
        let items = String.nsplit content "," in
        let path = List.map Int.of_string items in
        path
      end
  | _ -> raise (Arg.Bad ("Path " ^ s ^ " is not well-formed"))*)

let spec = [
  ("-k",
   Arg.Int (fun n -> k := n),
   ": number of unrolling (Default: " ^ (string_of_int !k) ^ ")" );
  ("--pathgen",
   Arg.Unit (fun n -> pathgen := true),
   ": generate paths");
  ("--bmc_heuristic_prune",
   Arg.String (fun n -> bmc_heuristic_prune := Some(n)),
   ": generate BMC heuristic to generate a pruned encoding");
  ("--path",
   Arg.String (fun s -> path := Some (process_path s)),
   ": specify the path (ex: \"[1,2,1,2,1]\" to focus (Default: none)");
  ("--new_format",
   Arg.Unit (fun o -> new_format := true),
   ": parse file using the new file format");
  ("--new_format_composed",
   Arg.Unit (fun o -> new_format_composed := true),
   ": parse file using the new file format and encode parallel composition");

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
    let hm = match !new_format || !new_format_composed with
               | true -> Drh_parser_networks.main Drh_lexer_networks.start lexbuf 
               | false -> Drh_parser.main Drh_lexer.start lexbuf
    in
    let my_hm =  match !new_format_composed with
      | true -> Network.compose hm
      | false -> hm
    in
(*    Network.print out my_hm; *)
 (*   begin
		(*Network.print out hm;*)
		(*let paths = Bmc.pathgen hm !k in*)
		let smt = Bmc.compile hm !k None false in
		Smt2.print out smt
    end
  *)
   if !pathgen then (*TODO*)
      let paths = Bmc.pathgen hm !k in
      List.print ~first:"" ~last:"\n" ~sep:"\n"
		 (fun out path ->
		  List.print ~first:"[" ~last:"]" ~sep:"," String.print out path)
		 out
		 paths
    else
    
    if Option.is_some !bmc_heuristic_prune then
      let heuristic = Heuristic.heuristicgen my_hm !k in
      let heuristic_back = Heuristic.heuristicgen_back my_hm !k in
      let hout = open_out (Option.get !bmc_heuristic_prune) in
      let () = Heuristic.writeHeuristic heuristic my_hm !k hout in
      let () = close_out hout in      
      (*	let smt = Bmc.compile_pruned my_hm !k heuristic heuristic_back None in *)
      let smt = Bmc.compile my_hm !k !path (Some heuristic) in
      Smt2.print out smt
    else 
      let smt = Bmc.compile my_hm !k !path None in
      Smt2.print out smt
	       with v -> Error.handle_exn v
let _ = Printexc.catch run ()
