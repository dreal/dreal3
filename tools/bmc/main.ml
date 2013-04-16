(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

let k = ref 3 (* default unrolling value is 3 *)
let infix = ref false
let spec = [
  ("-k",
   Arg.Int (fun n -> k := n),
   ": number of unrolling (Default: " ^ (string_of_int !k) ^ ")" );
  ("--infix",
   Arg.Unit (fun n -> infix := true),
   ": use infix syntax in drh file (Default: use prefix)");]
let usage = "Usage: main.native [<options>] <.drh>\n<options> are: "

let run () =
  let src = ref "" in
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let out = BatIO.stdout in
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let hm =
      match !infix with
        true -> Infix_parser.main Infix_lexer.start lexbuf
      | false -> Parser.main Lexer.start lexbuf
    in
    let hm' = Hybrid.preprocess hm in
    let (vardecls, flow_annots, formula, time_intv) = Smt2.reach !k hm' in
    let smt2 = Smt2.make_smt2 vardecls flow_annots formula time_intv in
    begin
      Smt2.print out smt2
    end
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()
