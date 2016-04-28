open Smt2_cmd
open Type
open Batteries

let count_cmd f = function
  | SetLogic _ -> 0
  | SetInfo _ -> 0
  | DeclareConst _ -> 0
  | DeclareFun _ -> 0
  | DeclareBool _ -> 0
  | DefineODE _ -> 0
  | Assert formula -> f formula
  | CheckSAT -> 0
  | Exit -> 0

let cmd_count_var = function
  | SetLogic _ -> 0
  | SetInfo _ -> 0
  | DeclareConst _ -> 0
  | DeclareFun _ -> 1
  | DeclareBool _ -> 1
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

let rec extract_nonlinear_func (smt2 : Smt2.t) : string Set.t =
  let open Basic in
  let rec extract_nonlinear_func_from_es (es : Basic.exp list) =
    List.fold_left (fun s e -> Set.union (extract_nonlinear_func_from_e e) s) Set.empty es
  and extract_nonlinear_func_from_e : (exp -> string Set.t) = function
    | Var s            -> Set.empty
    | Vec xs           -> Set.empty
    | Num n            -> Set.empty
    | Neg e'           -> extract_nonlinear_func_from_e e'
    | Add es           -> extract_nonlinear_func_from_es es
    | Sub es           -> extract_nonlinear_func_from_es es
    | Mul es           -> extract_nonlinear_func_from_es es
    | Div (e1, e2)     -> extract_nonlinear_func_from_es [e1;e2]
    | Pow (e1, e2)     ->
        let s = extract_nonlinear_func_from_es [e1;e2] in
        if e2 = (Num 0.5) then
            Set.add "sqrt" s
        else s
    | Ite (f', e1, e2) ->
      Set.union
        (extract_nonlinear_func_from_f f')
        (extract_nonlinear_func_from_es [e1;e2])
    | Sqrt e'          -> Set.add "sqrt" (extract_nonlinear_func_from_e e')
    | Safesqrt e'      -> Set.add "safesqrt" (extract_nonlinear_func_from_e e')
    | Abs e'           -> Set.add "abs" (extract_nonlinear_func_from_e e')
    | Log e'           -> Set.add "log" (extract_nonlinear_func_from_e e')
    | Exp e'           -> Set.add "exp" (extract_nonlinear_func_from_e e')
    | Sin e'           -> Set.add "sin" (extract_nonlinear_func_from_e e')
    | Cos e'           -> Set.add "cos" (extract_nonlinear_func_from_e e')
    | Tan e'           -> Set.add "tan" (extract_nonlinear_func_from_e e')
    | Asin e'          -> Set.add "asin" (extract_nonlinear_func_from_e e')
    | Acos e'          -> Set.add "acos" (extract_nonlinear_func_from_e e')
    | Atan e'          -> Set.add "atan" (extract_nonlinear_func_from_e e')
    | Asinh e'         -> Set.add "asinh" (extract_nonlinear_func_from_e e')
    | Acosh e'         -> Set.add "acosh" (extract_nonlinear_func_from_e e')
    | Atanh e'         -> Set.add "atanh" (extract_nonlinear_func_from_e e')
    | Atan2 (e1, e2)   -> Set.add "atan2" (extract_nonlinear_func_from_es [e1;e2])
    | Min   (e1, e2)   -> Set.add "min" (extract_nonlinear_func_from_es [e1;e2])
    | Max   (e1, e2)   -> Set.add "max" (extract_nonlinear_func_from_es [e1;e2])
    | Matan e'         -> Set.add "matan" (extract_nonlinear_func_from_e e')
    | Sinh e'          -> Set.add "sinh" (extract_nonlinear_func_from_e e')
    | Cosh e'          -> Set.add "cosh" (extract_nonlinear_func_from_e e')
    | Tanh e'          -> Set.add "tanh" (extract_nonlinear_func_from_e e')
    | Integral (n, t, x0s, flow) -> failwith "extract_nonlinear_func: Not Support Integral"
  and extract_nonlinear_func_from_fs fs =
    List.fold_left (fun s f -> Set.union (extract_nonlinear_func_from_f f) s) Set.empty fs
  and extract_nonlinear_func_from_f = function
    | True           -> Set.empty
    | False          -> Set.empty
    | Not f          -> extract_nonlinear_func_from_f f
    | And fs         -> extract_nonlinear_func_from_fs fs
    | Or fs          -> extract_nonlinear_func_from_fs fs
    | Gt (e1, e2)    -> extract_nonlinear_func_from_es [e1;e2]
    | Lt (e1, e2)    -> extract_nonlinear_func_from_es [e1;e2]
    | Ge (e1, e2)    -> extract_nonlinear_func_from_es [e1;e2]
    | Le (e1, e2)    -> extract_nonlinear_func_from_es [e1;e2]
    | Eq (e1, e2)    -> extract_nonlinear_func_from_es [e1;e2]
    | Gtp (e1, e2, p) -> extract_nonlinear_func_from_es [e1;e2]
    | Ltp (e1, e2, p) -> extract_nonlinear_func_from_es [e1;e2]
    | Gep (e1, e2, p) -> extract_nonlinear_func_from_es [e1;e2]
    | Lep (e1, e2, p) -> extract_nonlinear_func_from_es [e1;e2]
    | Eqp (e1, e2, p) -> extract_nonlinear_func_from_es [e1;e2]
    | Imply (f1, f2) -> extract_nonlinear_func_from_fs [f1;f2]
    | ForallT (m, lb, ub, f) -> extract_nonlinear_func_from_f f
    | FVar x -> Set.empty
    | LetE (var_e_list, f) -> failwith "extract_nonlinear_func: Not Support LetE"
    | LetF (var_f_list, f) -> failwith "extract_nonlinear_func: Not Support LetF"
  and extract_nonlinear_func_from_cmd = function
    | SetLogic _ -> Set.empty
    | SetInfo _ -> Set.empty
    | DeclareConst _ -> Set.empty
    | DeclareFun _ -> Set.empty
    | DeclareBool _ -> Set.empty
    | DefineODE _ -> Set.empty
    | Assert f -> extract_nonlinear_func_from_f f
    | CheckSAT -> Set.empty
    | Exit -> Set.empty
  in
  List.fold_left
    (fun result cmd -> Set.union result (extract_nonlinear_func_from_cmd cmd))
    Set.empty
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
    let out = IO.stdout in
    let smt2 = Smt2parser.main Smt2lexer.start lexbuf in
    let var_count  = count_var smt2 in
    let arith_count  = count_arith smt2 in
    let mathfn_count = count_mathfn smt2 in
    let nonlinear_funcs = extract_nonlinear_func smt2 in
    begin
      (* String.print out "Number of Variables: "; *)
      String.print out (string_of_int var_count);
      String.print out delim;
      (* String.print out "Number of Arithmetic Operators: "; *)
      String.print out (string_of_int arith_count);
      String.print out delim;
      (* String.print out "Number of Math Functions: "; *)
      String.print out (string_of_int mathfn_count);
      (* String.print out "nonlinear functions: "; *)
      (if (not (Set.is_empty nonlinear_funcs)) then
         Set.print String.print ~first:"," ~last:"" ~sep:"," out nonlinear_funcs);
      String.println out "";
    end
  with v ->
    Error.handle_exn v

let x = Printexc.catch run ()
