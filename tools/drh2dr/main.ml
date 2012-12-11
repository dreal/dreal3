(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

let print_ast = ref false
let spec = []
let usage = "Usage: main.native [<options>] <.drh>\n<options> are: "

let run () =
  let src = ref "" in
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let hm = Parser.main Lexer.start lexbuf in
    let dr = Drh2dr.transform hm in
    begin
      Dr.print_formula BatIO.stdout dr;
      BatString.println BatIO.stdout ""
    end
  with v -> Error.handle_exn v
let _ = Printexc.catch run ()
