(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)
open Error
open Smt2_cmd

let spec = [("-i", Arg.Unit (fun () -> Dr.fop := Dr.IntRatio),
             ": print number as a ratio of two integers.");
            ("-f", Arg.Unit (fun () -> Dr.fop := Dr.Float),
             ": print number as a decimal fraction (Default option).");
           ]
let usage = "Usage: dr2smt2.native <.dr>\n"

let process
    (vardecls : Vardecl.t list)
    (odes_opt: (Ode.t list) option)
    (f : Dr.formula) =
  (* Set Logic *)
  let logic_cmd = SetLogic QF_NRA in
  let make_lb name v = Dr.Le (Dr.Const v,  Dr.Var name) in
  let make_ub name v = Dr.Le (Dr.Var name, Dr.Const v ) in
  let (declarefuns, asserts) =
    BatList.split
      (List.map
      (fun ((lb, ub), name) ->
        (DeclareFun name,
         [Assert (make_lb name lb);
          Assert (make_ub name ub)])
      )
      vardecls)
  in
  BatList.concat
    [[logic_cmd];
     declarefuns;
     BatList.concat asserts;
     [Assert f];
     [CheckSAT; Exit];
    ]

let run () =
  let src = ref "" in
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let (vardecls, odes_opt, formula) = Parser.main Lexer.main lexbuf in
    let out = BatIO.stdout in
    let smt2 = process vardecls odes_opt formula in
    Smt2.print out smt2
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()
