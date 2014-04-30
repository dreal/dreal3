open Smt2_cmd
open Type

let count_cmd f = function
    | SetLogic _ -> 0
    | SetInfo _ -> 0
    | DeclareConst _ -> 0
    | DeclareFun _ -> 0
    | DefineODE _ -> 0
    | Assert formula -> f formula
    | CheckSAT -> 0
    | Exit -> 0

let cmd_count_var = function
    | SetLogic _ -> 0
    | SetInfo _ -> 0
    | DeclareConst _ -> 0
    | DeclareFun _ -> 1
    | DefineODE _ -> 0
    | Assert _ -> 0
    | CheckSAT -> 0
    | Exit -> 0

let count_var (smt2 : Smt2.t) : int
  =
  List.fold_left
    (fun result cmd -> result + (cmd_count_var cmd))
    0
    smt2

let count_arith (smt2 : Smt2.t) : int
  =
  List.fold_left
    (fun result cmd -> result + (count_cmd Basic.count_arith_f cmd))
    0
    smt2

let count_mathfn (smt2 : Smt2.t) : int
  =
  List.fold_left
    (fun result cmd -> result + (count_cmd Basic.count_mathfn_f cmd))
    0
    smt2

let print_ast = ref false
let delim =","
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
    let smt2 = Smt2parser.main Smt2lexer.start lexbuf in
    let var_count  = count_var smt2 in
    let arith_count  = count_arith smt2 in
    let mathfn_count = count_mathfn smt2 in
    begin
      (* BatString.print out "Number of Variables: "; *)
      BatString.print out (string_of_int var_count);
      BatString.print out delim;
      (* BatString.print out "Number of Arithmetic Operators: "; *)
      BatString.print out (string_of_int arith_count);
      BatString.print out delim;
      (* BatString.print out "Number of Math Functions: "; *)
      BatString.println out (string_of_int mathfn_count)
    end
  with v ->
    Error.handle_exn v

let x = Printexc.catch run ()
