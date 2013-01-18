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
    let (p, cs, init, pt) = Parser.main Lexer.start lexbuf in
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
