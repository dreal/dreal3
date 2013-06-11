open Batteries

let spec = []
let usage = "Usage: main.native [<options>] <Trace File> \n<options> are: "
let src = Global.empty "filename"
let run () =
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then Global.set src x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel
        (if not (Global.isdef src) then
            stdin
         else open_in (Global.get_exn src)) in
    let out = IO.stdout in
    let (p, fs, pt) = Parser.main Lexer.start lexbuf in
    let envlist_list = Ptree.do_it pt [] in
    begin
      List.print
        ~first:"["
        ~last:"]\n"
        ~sep:",\n"
        (fun out envlist ->
          List.print
            ~first:"["
            ~last:"]\n"
            ~sep:",\n"
            Env.print
            out
            envlist
        )
        out
        envlist_list
    end
  with v ->
    Error.handle_exn v

let x = Printexc.catch run ()
