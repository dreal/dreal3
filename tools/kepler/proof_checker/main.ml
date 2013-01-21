let spec = []
let usage = "Usage: main.native [<options>] <Trace File> \n<options> are: "
let run () =
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then BatGlobal.set Failhandler.src x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel
        (if BatGlobal.isdef Failhandler.src then
            stdin
         else open_in (BatGlobal.get Failhandler.src)) in
    let out = BatIO.stdout in
    let (p, fs, pt) = Parser.main Lexer.start lexbuf in
    begin
      BatGlobal.set Failhandler.prec p;
      Ptree.check pt fs
    end
  with v ->
    Error.handle_exn v

let x = Printexc.catch run ()
