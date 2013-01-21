open BatGlobal

let src = empty "src"      (* trace name *)
let prec =empty "prec"
let funcs = empty

let spec = []
let usage = "Usage: main.native [<options>] <Trace File> \n<options> are: "
let run () =
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then set src x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel (if isdef src then stdin else open_in (get src)) in
    let out = BatIO.stdout in
    let (p, fs, pt) = Parser.main Lexer.start lexbuf in
    begin
      set prec p;
      Ptree.check pt fs
    end
  with v ->
    Error.handle_exn v

let x = Printexc.catch run ()
