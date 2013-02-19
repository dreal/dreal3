let print_ast = ref false
let spec = []
let usage = "Usage: main.native [<options>] <.smt2> \n<options> are: "
let run () =
  let src = ref "" in
  let _ = Arg.parse spec
    (fun x -> if Sys.file_exists x then src := x
      else raise (Arg.Bad (x^": No such file"))) usage in
  try
    Error.init ();
    let lexbuf =
      Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let out = BatIO.stdout in
    let smt2 = Parser.main Lexer.start lexbuf in
    let var_count  = Smt2_stat.count_var smt2 in
    let arith_count  = Smt2_stat.count_arith smt2 in
    let mathfn_count = Smt2_stat.count_mathfn smt2 in
    begin
      (* BatString.print out "Number of Variables: "; *)
      BatString.print out (string_of_int var_count);
      BatString.print out "|";
      (* BatString.print out "Number of Arithmetic Operators: "; *)
      BatString.print out (string_of_int arith_count);
      BatString.print out "|";
      (* BatString.print out "Number of Math Functions: "; *)
      BatString.println out (string_of_int mathfn_count)
    end
  with v ->
    Error.handle_exn v

let x = Printexc.catch run ()
