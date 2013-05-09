(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Batteries

let k = ref 3 (* default unrolling value is 3 *)
let infix = ref false
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

(**
   Given a path (ex: [1;2;3;4]), it checks the three conditions:
   1) the first mode of the path should be the init mode of the hybrid model
   2) the last mode of the path should be an element of the goals of the HM
   3) the unrolling step k, should match with the length of the given path
**)
let check_path (path : int list option) (k : int) (init : int) (goals : int list) : unit =
  match path with
    Some p ->
      begin
        let first_mode = List.first p in
        let last_mode = List.last p in
        let len = List.length p in
        let path_str =  IO.to_string (List.print ~first:"[" ~last:"]" ~sep:", " Int.print) p in
        let goal_str =  IO.to_string (List.print ~first:"[" ~last:"]" ~sep:", " Int.print) goals in
        match (first_mode = init, List.mem last_mode goals, len = k + 1) with
          (true, true, true) -> ()
        | (false, _, _) ->
          let msg = Printf.sprintf
            "The first mode of the given path %s is %d which is different from %d, the initial mode of the given hybrid system model."
            path_str first_mode init
          in
          raise (Arg.Bad msg)
        | (_, false, _) ->
          let msg = Printf.sprintf
            "The last mode of the given path %s is %d which is not an element of %s, the list of modes in the goal section of the given hybrid system model."
            path_str last_mode goal_str
          in
          raise (Arg.Bad msg)
        | (_, _, false) ->
          let msg = Printf.sprintf
            "The length of the given path %s is %d, while the given unrolling depth k is %d."
            path_str len k
          in
          raise (Arg.Bad msg)
      end
  | None -> ()

let spec = [
  ("-k",
   Arg.Int (fun n -> k := n),
   ": number of unrolling (Default: " ^ (string_of_int !k) ^ ")" );
  ("--infix",
   Arg.Unit (fun n -> infix := true),
   ": use infix syntax in drh file (Default: use prefix)");
  ("--path",
   Arg.String (fun s -> path := Some (process_path s)),
   ": specify the path (ex: \"[1,2,1,2,1]\" to focus (Default: none)");
]
let usage = "Usage: main.native [<options>] <.drh>\n<options> are: "

(* let x = [? List: 2 * x | x <- 0 -- 5 ; x * x > 3 ?] *)

let run () =
  let src = ref "" in
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let out = IO.stdout in
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let hm =
      match !infix with
        true -> Drh_infix_parser.main Drh_infix_lexer.start lexbuf
      | false -> Drh_parser.main Drh_lexer.start lexbuf
    in
    let _ = check_path !path !k (Hybrid.init_id hm) (Hybrid.goal_ids hm) in
    let (vardecls, flow_annots, formula, time_intv) = Bmc.reach !k hm !path in
    let smt2 = Bmc.make_smt2 vardecls flow_annots formula time_intv in
    begin
      Smt2.print out smt2
    end
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()
