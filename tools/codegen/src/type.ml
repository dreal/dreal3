(* Wei Chen    (weichen1@andrew.cmu.edu) *)
(* Soonho Kong (soonhok@cs.cmu.edu)      *)

(*
 * A typical program consists of 3 components:
 * 1. Macro declaration(s).

 * 2. Mode(ODE) definition(s).
 * 3. Main function.
 *)
type t =
    {
        macros: macro list;
        modes: mode list;
        main: main_entry;
    }

and macro =
    (* define g 9.8 *)
    | Macro of string * float

and anno =
    (* [unroll, 0/t, var_index], used in BMC  *)
    | VarAnno of int * string * int
    | OdeAnno of string (* the name of define-ode command *)

and var_decl =
    | RealVar  of string
    | BRealVar of string * float * float
    | IntVar   of string

and exp =
    | Var      of string * anno option
    | Num      of float
    | Neg      of exp
    | Add      of exp list
    | Sub      of exp list
    | Mul      of exp list
    | Div      of exp * exp
    | Pow      of exp * exp
    | Ite      of formula * exp * exp
    | Sqrt     of exp
    | Safesqrt of exp
    | Abs      of exp
    | Log      of exp
    | Exp      of exp
    | Sin      of exp
    | Cos      of exp
    | Tan      of exp
    | Asin     of exp
    | Acos     of exp
    | Atan     of exp
    | Atan2    of exp * exp
    | Matan    of exp
    | Sinh     of exp
    | Cosh     of exp
    | Tanh     of exp
    | Asinh    of exp
    | Acosh    of exp
    | Atanh    of exp

    (* (integral 0 time_1 [x_1_0 ... x_i_0] flow1) *)
    | Integral of float * string * string list * string
    | Invoke of string * exp list

(* math formular *)
and formula =
    | True
    | False
    | FVar of string
    | Not of formula
    | And of formula list
    | Or  of formula list
    | Imply of formula * formula
    | Gt  of exp * exp
    | Lt  of exp * exp
    | Ge  of exp * exp
    | Le  of exp * exp
    | Eq  of exp * exp
    | LetF of ((string * formula) list * formula)
    | LetE of ((string * exp) list * formula)
    | ForallT of exp * exp * exp * formula

(* boolean expression *)
and bexp =
    | B_var of string * anno option
    | B_gt  of exp * exp
    | B_lt  of exp * exp
    | B_ge  of exp * exp
    | B_le  of exp * exp
    | B_eq  of exp * exp
    | B_and of bexp * bexp
    | B_or of bexp * bexp
    | B_true
    | B_false

(* switch case *)
and choice =
    | Case of float * stmt list
and stmt =
    | Ode of string * exp * anno option
    | Assert of bexp

    (* assignment *)
    | Assign of string * exp * anno option

    (* if no else statement, the latter one is empty *)
    | If of bexp * stmt list * stmt list
    | Proceed of float option * float option * stmt list
    | Vardecl of var_decl
    | Switch of string * choice list
    | Expr of exp

and main_entry =
    | Main of (stmt list)

and mode = {
    id : string;
    args: var_decl list;
    stmts: stmt list;
};;


let rec const_fold_exp exp macros =
  match exp with
  | Var (s, anno) ->
    begin
      match List.mem_assoc s macros with
      | true -> Num (List.assoc s macros)
      | false -> exp
    end
  | Num _ -> exp
  | Neg e1 -> Neg (const_fold_exp e1 macros)
  | Add es -> Add (const_fold_exps es macros)
  | Sub es -> Sub (const_fold_exps es macros)
  | Mul es -> Mul (const_fold_exps es macros)
  | Div (e1, e2) -> Div (const_fold_exp e1 macros, const_fold_exp e2 macros)
  | Pow (e1, e2) -> Pow (const_fold_exp e1 macros, const_fold_exp e2 macros)
  | Ite (f, e1, e2) -> failwith ""
  | Sqrt e -> Sqrt (const_fold_exp e macros)
  | Safesqrt e -> Safesqrt (const_fold_exp e macros)
  | Abs e -> Abs (const_fold_exp e macros)
  | Log e -> Log (const_fold_exp e macros)
  | Exp e -> Exp (const_fold_exp e macros)
  | Sin e -> Sin (const_fold_exp e macros)
  | Cos e -> Cos (const_fold_exp e macros)
  | Tan e -> Tan (const_fold_exp e macros)
  | Asin e -> Asin (const_fold_exp e macros)
  | Acos e -> Acos (const_fold_exp e macros)
  | Atan e -> Atan (const_fold_exp e macros)
  | Atan2 (e1, e2) -> Atan2 ((const_fold_exp e1 macros), (const_fold_exp e2 macros))
  | Matan e -> Matan (const_fold_exp e macros)
  | Sinh e -> Sinh (const_fold_exp e macros)
  | Cosh e -> Cosh (const_fold_exp e macros)
  | Tanh e -> Tanh (const_fold_exp e macros)
  | Asinh e -> Asinh (const_fold_exp e macros)
  | Acosh e -> Acosh (const_fold_exp e macros)
  | Atanh e -> Atanh (const_fold_exp e macros)
  | Integral _ -> exp
  | Invoke (fn, exps) -> Invoke (fn, List.map (fun e -> const_fold_exp e macros) exps)

and const_fold_exps exps macros =
  List.map (fun e -> const_fold_exp e macros) exps

and const_fold_stmt stmt macros =
  match stmt with
  | Ode (s, e, anno) -> Ode (s, const_fold_exp e macros, anno)
  | Assert be -> Assert (const_fold_bexp be macros)
  | Assign (s, e, anno) -> Assign (s, const_fold_exp e macros, anno)
  | If (be, stmts1, stmts2) -> If (const_fold_bexp be macros, const_fold_stmts stmts1 macros, const_fold_stmts stmts2 macros)
  | Proceed (b1, b2, stmts) -> Proceed (b1, b2, const_fold_stmts stmts macros)
  | Vardecl _ -> stmt
  | Switch _ -> stmt
  | Expr e -> Expr (const_fold_exp e macros)

and const_fold_stmts stmts macros =
  List.map (fun s -> const_fold_stmt s macros) stmts

and const_fold_bexp bexp macros : bexp =
  match bexp with
  | B_var _ -> bexp
  | B_gt (e1, e2) -> B_gt (const_fold_exp e1 macros, const_fold_exp e2 macros)
  | B_lt (e1, e2) -> B_lt (const_fold_exp e1 macros, const_fold_exp e2 macros)
  | B_ge (e1, e2) -> B_ge (const_fold_exp e1 macros, const_fold_exp e2 macros)
  | B_le (e1, e2) -> B_le (const_fold_exp e1 macros, const_fold_exp e2 macros)
  | B_eq (e1, e2) -> B_eq (const_fold_exp e1 macros, const_fold_exp e2 macros)
  | B_and (e1, e2) -> B_and (const_fold_bexp e1 macros, const_fold_bexp e2 macros)
  | B_or (e1, e2) -> B_or (const_fold_bexp e1 macros, const_fold_bexp e2 macros)
  | B_true | B_false -> bexp

and const_fold_bexps bes macros =
  List.map (fun e -> const_fold_bexp e macros) bes

and const_fold_mode mode macros = {id = mode.id; args = mode.args; stmts = const_fold_stmts mode.stmts macros}

and const_fold_modes modes macros =
  List.map (fun m -> const_fold_mode m macros) modes

and const_fold_program (program:t) =
  let macros = List.map (fun (Macro(s, l)) -> (s, l)) program.macros in
  match program.main with
  | Main m ->
  {
    macros = program.macros;
    modes = const_fold_modes program.modes macros;
    main = Main m
  }


let rec subst_exp f exp =
  let transformer = subst_exps f in
  match exp with
  | Var (s, anno) ->
    f exp
  | Num _ -> f exp
  | Neg e1 -> Neg (subst_exp f e1)
  | Add es -> Add (transformer es)
  | Sub es -> Sub (transformer es)
  | Mul es -> Mul (transformer es)
  | Div (e1, e2) -> Div (subst_exp f e1, subst_exp f e2)
  | Pow (e1, e2) -> Pow (subst_exp f e1, subst_exp f e2)
  | Ite (f, e1, e2) -> failwith ""
  | Sqrt e -> Sqrt (subst_exp f e)
  | Safesqrt e -> Safesqrt (subst_exp f e)
  | Abs e -> Abs (subst_exp f e)
  | Log e -> Log (subst_exp f e)
  | Exp e -> Exp (subst_exp f e)
  | Sin e -> Sin (subst_exp f e)
  | Cos e -> Cos (subst_exp f e)
  | Tan e -> Tan (subst_exp f e)
  | Asin e -> Asin (subst_exp f e)
  | Acos e -> Acos (subst_exp f e)
  | Atan e -> Atan (subst_exp f e)
  | Atan2 (e1, e2) -> Atan2 (subst_exp f e1, subst_exp f e2)
  | Matan e -> Matan (subst_exp f e)
  | Sinh e -> Sinh (subst_exp f e)
  | Cosh e -> Cosh (subst_exp f e)
  | Tanh e -> Tanh (subst_exp f e)
  | Asinh e -> Asinh (subst_exp f e)
  | Acosh e -> Acosh (subst_exp f e)
  | Atanh e -> Atanh (subst_exp f e)
  | Integral _ -> failwith ""
  | Invoke (fn, exps) -> Invoke (fn, transformer exps)

and subst_exps f exps  =
    List.map f exps
