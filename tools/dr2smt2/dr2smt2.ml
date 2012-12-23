(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)
open Error

let spec = [("-i", Arg.Unit (fun () -> Dr.fop := Dr.IntRatio),
             ": print number as a ratio of two integers (Default option).");
            ("-f", Arg.Unit (fun () -> Dr.fop := Dr.Float),
             ": print number as a decimal fraction.");
           ]
let usage = "Usage: dr2smt2.native <.dr>\n"

let process out (vardecls : Vardecl.t list) (f : Dr.formula) =
  begin
    (* Set Logic *)
    BatString.println out "(set-logic QF_NLR)";

    (* Declare variables *)
    List.iter (fun (_, v) ->
      begin
        BatString.print   out "(declare-fun ";
        BatString.print   out v;
        BatString.println out " () Real)";
      end)
      vardecls;

    (* Assert *)
    BatString.println out "(assert";
    BatString.println out "(and";

    (* Variable Ranges *)
    List.iter (fun ((lb, ub), v) ->
      Dr.print_formula out
        (Dr.And
          [Dr.Le(Dr.Const lb, Dr.Var v);
          Dr.Le(Dr.Var v, Dr.Const ub)]
        ))
      vardecls;

    (* Original formula *)
    Dr.print_formula out f;
    BatString.println out ")";
    BatString.println out ")";

    (* Check-sat *)
    BatString.println out "(check-sat)";

    (* Exit *)
    BatString.println out "(exit)";
  end
let run () =
  let src = ref "" in
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let (vardecls, formula) = Parser.main Lexer.main lexbuf in
    let out = BatIO.stdout in
    process out vardecls formula
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()
