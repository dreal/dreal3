(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Batteries

type var = string

type vardecl = Vardecl.t

type exp =
| Var   of string
| Const of float
| Neg   of exp
| Add   of exp * exp
| Sub   of exp * exp
| Mul   of exp * exp
| Div   of exp * exp
| Pow   of exp * exp
| Ite   of formula * exp * exp
| Sqrt  of exp
| Abs   of exp
| Log   of exp
| Exp   of exp
| Sin   of exp
| Cos   of exp
| Tan   of exp
| Asin  of exp
| Acos  of exp
| Atan  of exp
| Sinh  of exp
| Cosh  of exp
| Tanh  of exp
and formula =
| True
| False
| Not of formula
| And of formula list
| Or  of formula list
| Gt  of exp * exp
| Lt  of exp * exp
| Ge  of exp * exp
| Le  of exp * exp
| Eq  of exp * exp
| ForallT of formula

type ode = var * exp

type t = vardecl list * ode list * formula

let rec collect_vars_in_formula (f : formula) : var Set.t =
  match f with
    True -> Set.empty
  | False -> Set.empty
  | Not f' -> collect_vars_in_formula f'
  | And fs -> collect_vars_in_formulas fs
  | Or  fs -> collect_vars_in_formulas fs
  | Gt (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Lt (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Ge (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Le (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Eq (e1, e2) -> collect_vars_in_exps [e1;e2]
  | ForallT f' -> collect_vars_in_formula f'
and collect_vars_in_exps (es : exp list) =
  List.reduce Set.union (List.map collect_vars_in_exp es)
and collect_vars_in_formulas (fs : formula list) =
  List.reduce Set.union (List.map collect_vars_in_formula fs)
and collect_vars_in_exp (e : exp) : var Set.t = match e with
    Var x -> Set.singleton x
  | Const _ -> Set.empty
  | Neg e' -> collect_vars_in_exp e'
  | Add (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Sub (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Mul (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Div (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Pow (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Ite (f, e1, e2) ->
    let s1 = collect_vars_in_formula f in
    let s2 = collect_vars_in_exps [e1; e2] in
    Set.union s1 s2
  | Sqrt e' -> collect_vars_in_exp e'
  | Abs  e' -> collect_vars_in_exp e'
  | Log  e' -> collect_vars_in_exp e'
  | Exp  e' -> collect_vars_in_exp e'
  | Sin  e' -> collect_vars_in_exp e'
  | Cos  e' -> collect_vars_in_exp e'
  | Tan  e' -> collect_vars_in_exp e'
  | Asin e' -> collect_vars_in_exp e'
  | Acos e' -> collect_vars_in_exp e'
  | Atan e' -> collect_vars_in_exp e'
  | Sinh e' -> collect_vars_in_exp e'
  | Cosh e' -> collect_vars_in_exp e'
  | Tanh e' -> collect_vars_in_exp e'

let make_or (fs : formula list) =
  let reduced_fs_opt = List.fold_left
    (fun fs f -> match (fs, f) with
    | (Some _, False) -> fs
    | (_, True) -> None
    | (None, _) -> None
    | (Some fs1, Or fs2) -> Some (fs1@fs2)
    | (Some fs', f) -> Some (f::fs'))
    (Some [])
    fs
  in
  match reduced_fs_opt with
  | Some [] -> False
  | Some (x::[]) -> x
  | Some fs' -> Or fs'
  | None -> True

let make_and (fs : formula list) =
  let reduced_fs_opt = List.fold_left
    (fun fs f -> match (fs, f) with
    | (Some _, True) -> fs
    | (_, False) -> None
    | (None, _) -> None
    | (Some fs1, And fs2) -> Some (fs1@fs2)
    | (Some fs', f) -> Some (f::fs'))
    (Some [])
    fs
  in
  match reduced_fs_opt with
  | Some [] -> True
  | Some (x::[]) -> x
  | Some fs' -> And fs'
  | None -> False

let rec preprocess_exp (f: string -> exp) : (exp -> exp) =
  function Var s -> f s
  | Const n -> Const n
  | Neg e'  -> Neg (preprocess_exp f e')
  | Add (e1, e2) -> Add (preprocess_exp f e1, preprocess_exp f e2)
  | Sub (e1, e2) -> Sub (preprocess_exp f e1, preprocess_exp f e2)
  | Mul (e1, e2) -> Mul (preprocess_exp f e1, preprocess_exp f e2)
  | Div (e1, e2) -> Div (preprocess_exp f e1, preprocess_exp f e2)
  | Pow (e1, e2) -> Pow (preprocess_exp f e1, preprocess_exp f e2)
  | Ite (f', e1, e2) -> Ite (preprocess_formula f f', preprocess_exp f e1, preprocess_exp f e2)
  | Sqrt e' -> Sqrt (preprocess_exp f e')
  | Abs  e' -> Abs  (preprocess_exp f e')
  | Log  e' -> Log  (preprocess_exp f e')
  | Exp  e' -> Exp  (preprocess_exp f e')
  | Sin  e' -> Sin  (preprocess_exp f e')
  | Cos  e' -> Cos  (preprocess_exp f e')
  | Tan  e' -> Tan  (preprocess_exp f e')
  | Asin e' -> Asin (preprocess_exp f e')
  | Acos e' -> Acos (preprocess_exp f e')
  | Atan e' -> Atan (preprocess_exp f e')
  | Sinh e' -> Sinh (preprocess_exp f e')
  | Cosh e' -> Cosh (preprocess_exp f e')
  | Tanh e' -> Tanh (preprocess_exp f e')
and preprocess_formula (f: string -> exp) : (formula -> formula) =
  function True -> True
  | False  -> False
  | Not f' -> Not (preprocess_formula f f')
  | And fl -> And (List.map (preprocess_formula f) fl)
  | Or fl  -> Or (List.map (preprocess_formula f) fl)
  | Gt (e1, e2) -> Gt (preprocess_exp f e1, preprocess_exp f e2)
  | Lt (e1, e2) -> Lt (preprocess_exp f e1, preprocess_exp f e2)
  | Ge (e1, e2) -> Ge (preprocess_exp f e1, preprocess_exp f e2)
  | Le (e1, e2) -> Le (preprocess_exp f e1, preprocess_exp f e2)
  | Eq (e1, e2) -> Eq (preprocess_exp f e1, preprocess_exp f e2)
  | ForallT f' -> ForallT (preprocess_formula f f')

let rec subst_exp (f: string -> string) : (exp -> exp) =
  function Var s -> Var (f s)
  | Const n -> Const n
  | Neg e'  -> Neg (subst_exp f e')
  | Add (e1, e2) -> Add (subst_exp f e1, subst_exp f e2)
  | Sub (e1, e2) -> Sub (subst_exp f e1, subst_exp f e2)
  | Mul (e1, e2) -> Mul (subst_exp f e1, subst_exp f e2)
  | Div (e1, e2) -> Div (subst_exp f e1, subst_exp f e2)
  | Pow (e1, e2) -> Pow (subst_exp f e1, subst_exp f e2)
  | Ite (f', e1, e2) -> Ite (subst_formula f f', subst_exp f e1, subst_exp f e2)
  | Sqrt e' -> Sqrt (subst_exp f e')
  | Abs  e' -> Abs  (subst_exp f e')
  | Log  e' -> Log  (subst_exp f e')
  | Exp  e' -> Exp  (subst_exp f e')
  | Sin  e' -> Sin  (subst_exp f e')
  | Cos  e' -> Cos  (subst_exp f e')
  | Tan  e' -> Tan  (subst_exp f e')
  | Asin e' -> Asin (subst_exp f e')
  | Acos e' -> Acos (subst_exp f e')
  | Atan e' -> Atan (subst_exp f e')
  | Sinh e' -> Sinh (subst_exp f e')
  | Cosh e' -> Cosh (subst_exp f e')
  | Tanh e' -> Tanh (subst_exp f e')
and subst_formula (f: string -> string) : (formula -> formula) =
  function True -> True
  | False  -> False
  | Not f' -> Not (subst_formula f f')
  | And fl -> And (List.map (subst_formula f) fl)
  | Or fl  -> Or (List.map (subst_formula f) fl)
  | Gt (e1, e2) -> Gt (subst_exp f e1, subst_exp f e2)
  | Lt (e1, e2) -> Lt (subst_exp f e1, subst_exp f e2)
  | Ge (e1, e2) -> Ge (subst_exp f e1, subst_exp f e2)
  | Le (e1, e2) -> Le (subst_exp f e1, subst_exp f e2)
  | Eq (e1, e2) -> Eq (subst_exp f e1, subst_exp f e2)
  | ForallT f' -> ForallT (subst_formula f f')
and subst_ode (f: string -> string) : (ode -> ode) =
  function (var, exp) -> (f var, subst_exp f exp)

let rec print_exp (out : 'a IO.output) : exp -> unit =
  let print_exps (op : string) (exps : exp list) =
    begin
      List.print
        ~first:("("^op^" ")
        ~sep:" "
        ~last:")"
        print_exp
        out
        exps
    end
  in
  function
  | Var x ->
    let filter str =
      (* filter out '(' and ')' *)
      let s1 = String.filter (fun c -> c != '(' && c != ')') str in
      (* replace '*' with "ptr_" *)
      let s2 = String.replace_chars (fun c -> if c == '*' then "ptr_" else String.of_char c) s1 in
      (* replace '.' with "_" *)
      let s3 = String.replace_chars (fun c -> if c == '.' then "_" else String.of_char c) s2 in
      (* replace "->" with "_" *)
      let rec replace_all (str : string) (sub : string) (by : string) =
        let (b, str') = String.replace str sub by in
        match b with
        | true -> replace_all str' sub by
        | false -> str'
      in
      replace_all s3 "->" "_"
    in
    String.print out (filter x)
  | Const n ->
    (* If n ends with ".", add "0" to make ".0" *)
    let s = Printf.sprintf "%f" n in
    let s' = match String.ends_with s "." with
      | true -> s ^ "0"
      | false -> s
    in
    String.print out s'
  | Neg e' -> print_exps "-" [e']
  | Add (e1, e2) -> print_exps "+" [e1; e2]
  | Sub (e1, e2) -> print_exps "-" [e1; e2]
  | Mul (e1, e2) -> print_exps "*" [e1; e2]
  | Div (e1, e2) -> print_exps "/" [e1; e2]
  | Pow (e1, e2) -> print_exps "^" [e1; e2]
  | Ite (f, e1, e2) ->
    begin
      String.print out "(ite ";
      print_formula out f;
      String.print out " ";
      print_exp out e1;
      String.print out " ";
      print_exp out e2;
      String.print out ")"
    end
  | Sqrt e -> (* print_exps "sqrt" [e] *)
    (* MATH HACK *)
    print_exp out (Pow(e, Const 0.5))
  | Abs  e -> (* print_exps "abs"  [e] *)
    (* MATH HACK *)
    print_exp out (Sqrt (Pow(e, Const 2.0)))
  | Log  e -> print_exps "log"  [e]
  | Exp  e -> print_exps "exp"  [e]
  | Sin  e -> print_exps "sin"  [e]
  | Cos  e -> print_exps "cos"  [e]
  | Tan  e -> print_exps "tan"  [e]
  | Asin e -> print_exps "arcsin" [e]
  | Acos e -> print_exps "arccos" [e]
  | Atan e -> print_exps "arctan" [e]
  | Sinh e -> print_exps "sinh" [e]
  | Cosh e -> print_exps "cosh" [e]
  | Tanh e -> print_exps "tanh" [e]

and print_formula (out : 'a IO.output) : formula -> unit =
  let print_lists
      (op : string)
      (out : 'a IO.output)
      f
      items =
    begin
      List.print
        ~first:("("^op^" ")
        ~sep:" "
        ~last:")"
        f
        out
        items
    end
  in
  let print_exps (op : string) (exps : exp list) : unit = print_lists op out print_exp exps in
  let print_formulas (op : string) (formulas : formula list) : unit = print_lists op out print_formula formulas in
  function
  | True -> String.print out "true"
  | False -> String.print out "false"
  | Not f -> print_formulas "not" [f]
  | And fs -> print_formulas "and" fs
  | Or  fs -> print_formulas "or"  fs
  | Gt  (e1, e2) -> print_exps ">"  [e1; e2]
  | Lt  (e1, e2) -> print_exps "<"  [e1; e2]
  | Ge  (e1, e2) -> print_exps ">=" [e1; e2]
  | Le  (e1, e2) -> print_exps "<=" [e1; e2]
  | Eq  (e1, e2) -> print_exps "="  [e1; e2]
  | ForallT f ->
    begin
      String.print out "(forall_t ";
      print_formula out f;
      String.print out ")";
    end

let print_ode out (v, e) =
  begin
    String.print out "d/dt[";
    String.print out v;
    String.print out "] = ";
    print_exp out e;
  end

let print out ((vardecls, odes, f) : t) : unit =
  begin
    (* print variable declarations *)
    List.print
      ~first:""
      ~sep:";\n"
      ~last:";\n"
      Vardecl.print
      out
      vardecls;
    (* print variable declarations *)
    List.print
      ~first:"{\n"
      ~sep:";\n"
      ~last:";\n}\n"
      print_ode out odes;
    (* print variable declarations *)
    print_formula out f
  end

let rec print_infix_exp (out : 'a IO.output) : exp -> unit =
  let print_infix_exps (op : string) (exps : exp list) =
    begin
      List.print
        ~first:"("
        ~sep: (" " ^ op ^ " ")
        ~last:")"
        print_infix_exp
        out
        exps
    end
  in
  let print_fncall (fn_name : string) (exps : exp list) =
    begin
      List.print
        ~first: (fn_name ^ "(")
        ~sep: ", "
        ~last:")"
        print_infix_exp
        out
        exps
    end
  in
  function
  | Var x ->
    let filter str =
      (* filter out '(' and ')' *)
      let s1 = String.filter (fun c -> c != '(' && c != ')') str in
      (* replace '*' with "ptr_" *)
      let s2 = String.replace_chars (fun c -> if c == '*' then "ptr_" else String.of_char c) s1 in
      (* replace '.' with "_" *)
      let s3 = String.replace_chars (fun c -> if c == '.' then "_" else String.of_char c) s2 in
      (* replace "->" with "_" *)
      let rec replace_all (str : string) (sub : string) (by : string) =
        let (b, str') = String.replace str sub by in
        match b with
        | true -> replace_all str' sub by
        | false -> str'
      in
      replace_all s3 "->" "_"
    in
    String.print out (filter x)
  | Const n ->
    (* If n ends with ".", add "0" to make ".0" *)
    let s = Printf.sprintf "%f" n in
    let s' = match String.ends_with s "." with
      | true -> s ^ "0"
      | false -> s
    in
    String.print out s'
  | Neg e' -> Printf.fprintf out "(0.0 - %s)" (IO.to_string print_infix_exp e')
  | Add (e1, e2) -> print_infix_exps "+" [e1; e2]
  | Sub (e1, e2) -> print_infix_exps "-" [e1; e2]
  | Mul (e1, e2) -> print_infix_exps "*" [e1; e2]
  | Div (e1, e2) -> print_infix_exps "/" [e1; e2]
  | Pow (e1, e2) -> print_infix_exps "^" [e1; e2]
  | Ite (f, e1, e2) ->
    begin
      String.print out "(ite ";
      print_formula out f;
      String.print out " ";
      print_infix_exp out e1;
      String.print out " ";
      print_infix_exp out e2;
      String.print out ")"
    end
  | Sqrt e -> (* print_infix_exps "sqrt" [e] *)
    (* MATH HACK *)
    print_infix_exp out (Pow(e, Const 0.5))
  | Abs  e -> (* print_infix_exps "abs"  [e] *)
    (* MATH HACK *)
    print_infix_exp out (Sqrt (Pow(e, Const 2.0)))
  | Log  e -> print_fncall "log"  [e]
  | Exp  e -> print_fncall "exp"  [e]
  | Sin  e -> print_fncall "sin"  [e]
  | Cos  e -> print_fncall "cos"  [e]
  | Tan  e -> print_fncall "tan"  [e]
  | Asin e -> print_fncall "arcsin" [e]
  | Acos e -> print_fncall "arccos" [e]
  | Atan e -> print_fncall "arctan" [e]
  | Sinh e -> print_fncall "sinh" [e]
  | Cosh e -> print_fncall "cosh" [e]
  | Tanh e -> print_fncall "tanh" [e]
