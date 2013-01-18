open Ptree
open Func

let print_ast = ref false
let spec = [
  ("-pp", Arg.Set print_ast, "Print Python AST");
]
let usage = "Usage: main.native [<options>] <Trace File> \n<options> are: "


let run () =
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let (cs, pt) = Parser.main Lexer.start lexbuf in
    let _ =
      (BatList.print
        Constraint.print
        BatIO.stdout
        cs)
    in
    let _ = Ptree.check pt cs in
    print_endline "Success."
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()


(* let e1 = Env.make [("x1", 0.0, 15.0)] *)
(* let e2 = Env.make [("x1", 6.2666, 14.454)] *)
(* let e3 = Env.make [("x1", 6.2666, 10.36)] *)
(* let e4 = Env.make [("x1", 10.36, 14.454)] *)

(* let pt = Prune(e1, *)
(*                Branch(e2, *)
(*                       Axiom e3, *)
(*                       Axiom e4)) *)

(*
  -10 <= x1 <= 10 ->
  -10 <= x2 <= 10 ->
  (1.5   - x1 + x1*x2   )^2
  + (2.25  - x1 + x1*x2^2 )^2
  + (2.625 - x1 + x1*x2^3 )^2
*)
