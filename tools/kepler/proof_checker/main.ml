open Ptree
open Func

let print_ast = ref false
let spec = [
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
    let out = BatIO.stdout in
    let (p, cs, init, pt_op) = Parser.main Lexer.start lexbuf in
    begin
      (* Print out precision *)
      BatString.print   out "Precision: ";
      BatFloat.print    out p;
      BatString.println out "";
      BatString.println out "Formulae:";
      (* Print out Formulae *)
      (BatList.print
         Basic.print_formula
         BatIO.stdout
         cs);
      (* Print out initial box *)
      Env.print out init;
      let pt' =
        (match pt_op with
          Some pt -> pt
        | None -> Ptree.Axiom init)
      in
      Ptree.check pt' cs p;
      ()
    end
  with v ->
    Error.handle_exn v

let x = Printexc.catch run ()
