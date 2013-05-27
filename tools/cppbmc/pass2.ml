(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)
open Batteries
open Error

let print_ast = ref false
let spec = []
let usage = "Usage: pass2.native [<options>] <annotated input>\n<options> are: "

let run () =
  let src = ref "" in
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let (vardecls, trans, inv) = Parser.main Lexer.start lexbuf in
    let out = IO.stdout in
    let vardecls' = Vardecl.unfold vardecls in
    let subst_f func f = Basic.map_exp (Basic.subst_exp func) f in
    let inv_x = subst_f (fun s -> s ^ "0") inv in
    let inv_x' =
      subst_f
        (fun s ->
          let (_, _, n) = List.find (fun (_, s', _) -> s = s') vardecls in
          match n with
          | Some n' -> s ^ (string_of_int n')
          | None -> raise (Error.ShouldNotHappen ("Inv(x'): " ^ s))
        )
        inv
    in
    let final =
      (*
        final :=
            not (inv(x) /\ trans(x, x') => inv(x'))
        ==> not (not (inv(x) /\ trans(x, x') \/ inv(x'))
        ==> (inv(x) /\ trans(x, x') /\ not inv(x')
      *)
      (* Basic.make_and [inv_x; trans; Basic.Not inv_x'] *)
      Basic.Not (Basic.make_or [Basic.Not inv_x; Basic.Not trans; inv_x'])
    in
    begin
      (* Print out variable declaration with range *)
      let smt2_vardecls = List.map (fun ((lb, ub), v, _) -> Smt2_cmd.DeclareFun v) vardecls' in
      let smt2_ranges =
        List.flatten
          (List.map (fun ((lb, ub), v, _) ->
            [Smt2_cmd.make_lb v lb;
             Smt2_cmd.make_ub v ub;])
             vardecls')
      in
      let smt2 =
        List.flatten
          [[Smt2_cmd.SetLogic Smt2_cmd.QF_NRA];
           smt2_vardecls;
           smt2_ranges;
           [Smt2_cmd.Assert final];
           [Smt2_cmd.CheckSAT];
           [Smt2_cmd.Exit];] in
      Smt2.print out smt2
      (* List.print ~first:"" ~sep:"\n" ~last:"\n\n" Vardecl.print out vardecls'; *)
      (* Basic.print_formula out final; *)
      (* String.print out ";\n" *)
    end
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()
