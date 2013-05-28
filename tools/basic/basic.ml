(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Batteries

exception TODO
exception DerivativeNotFound

type var = string

type exp =
| Var   of string
| Num of float
| Neg   of exp
| Add   of exp list
| Sub   of exp list
| Mul   of exp list
| Div   of exp * exp
| Pow   of exp * exp
| Ite   of formula * exp * exp
| Sqrt  of exp
| Safesqrt of exp
| Abs   of exp
| Log   of exp
| Exp   of exp
| Sin   of exp
| Cos   of exp
| Tan   of exp
| Asin  of exp
| Acos  of exp
| Atan  of exp
| Atan2 of exp * exp
| Matan  of exp
| Sinh  of exp
| Cosh  of exp
| Tanh  of exp
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
| ForallT of formula

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
  | Imply (f1, f2) -> collect_vars_in_formulas [f1;f2]
  | FVar x -> Set.singleton x
  | ForallT f' -> collect_vars_in_formula f'
  | LetF _ -> raise TODO
  | LetE _ -> raise TODO
and collect_vars_in_exps (es : exp list) =
  List.reduce Set.union (List.map collect_vars_in_exp es)
and collect_vars_in_formulas (fs : formula list) =
  List.reduce Set.union (List.map collect_vars_in_formula fs)
and collect_vars_in_exp (e : exp) : var Set.t = match e with
    Var x -> Set.singleton x
  | Num _ -> Set.empty
  | Neg e' -> collect_vars_in_exp e'
  | Add es -> collect_vars_in_exps es
  | Sub es -> collect_vars_in_exps es
  | Mul es -> collect_vars_in_exps es
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
  | Matan e' -> collect_vars_in_exp e'
  | Atan2 (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Sinh e' -> collect_vars_in_exp e'
  | Cosh e' -> collect_vars_in_exp e'
  | Tanh e' -> collect_vars_in_exp e'
  | Safesqrt e' -> collect_vars_in_exp e'

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
  | Num n -> Num n
  | Neg e'  -> Neg (preprocess_exp f e')
  | Add es -> Add (List.map (preprocess_exp f) es)
  | Sub es -> Sub (List.map (preprocess_exp f) es)
  | Mul es -> Mul (List.map (preprocess_exp f) es)
  | Div (e1, e2) -> Div (preprocess_exp f e1, preprocess_exp f e2)
  | Pow (e1, e2) -> Pow (preprocess_exp f e1, preprocess_exp f e2)
  | Ite (f', e1, e2) -> Ite (preprocess_formula f f', preprocess_exp f e1, preprocess_exp f e2)
  | Sqrt e' -> Sqrt (preprocess_exp f e')
  | Safesqrt e' -> Safesqrt (preprocess_exp f e')
  | Abs  e' -> Abs  (preprocess_exp f e')
  | Log  e' -> Log  (preprocess_exp f e')
  | Exp  e' -> Exp  (preprocess_exp f e')
  | Sin  e' -> Sin  (preprocess_exp f e')
  | Cos  e' -> Cos  (preprocess_exp f e')
  | Tan  e' -> Tan  (preprocess_exp f e')
  | Asin e' -> Asin (preprocess_exp f e')
  | Acos e' -> Acos (preprocess_exp f e')
  | Atan e' -> Atan (preprocess_exp f e')
  | Atan2 (e1, e2) -> Atan2 (preprocess_exp f e1, preprocess_exp f e2)
  | Matan e' -> Matan (preprocess_exp f e')
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
  | Imply (f1, f2) -> Imply (preprocess_formula f f1, preprocess_formula f f2)
  | ForallT f' -> ForallT (preprocess_formula f f')
  | FVar x -> FVar x
  | LetF _ -> raise TODO
  | LetE _ -> raise TODO

let rec deriv (e: exp) (x: string) : exp
    = match e with
      Var v -> if v = x then Num 1.0 else Num 0.0
    | Num _ -> Num 0.0
    | Neg e' -> Neg (deriv e' x)
    | Add es -> Add (List.map (fun e' -> deriv e' x) es)
    | Sub es -> Sub (List.map (fun e' -> deriv e' x) es)
    | Mul [] -> Num 0.0

    (** (f * g)' = f' * g +   **)
    | Mul (f::g) ->
      let f' = deriv f x in
      let g' = deriv (Mul g) x in
      Add [Mul (f'::g); Mul [f;g']]

    (** (f / g)' = (f' * g - f * g') / g^2 **)
    | Div (f, g) ->
      let f' = deriv f x in
      let g' = deriv g x in
      Div (Sub [Mul [f';g]; Mul [f;g']], Pow (g, Num 2.0))

    (** (f^n)' = n * f^(n-1) f' **)
    | Pow (f, Num n) ->
      let f' = deriv f x in
      Mul [Num n;
           Pow (f, Num (n -. 1.0));
           f']

    (** In general,
        (f^g)' = f^g (f' * g / f + g' * ln g) **)
    | Pow (f, g) ->
      let f' = deriv f x in
      let g' = deriv g x in
      Mul [Pow (f, g);
           Add [Mul [f'; Div(g, f)] ;
                Mul [g'; Log f]]]

    (** No Support **)
    | Ite _ -> raise DerivativeNotFound

    (** (sqrt(f))' = 1/2 * 1/(sqrt(f)) * f' **)
    | Sqrt f ->
      let f' = deriv f x in
      Mul [Num 0.5;
           Div (Num 1.0, Sqrt f);
           f']
    (** safesqrt = sqrt **)
    | Safesqrt f -> deriv (Safesqrt f) x

    (** No Support **)
    | Abs  f -> raise DerivativeNotFound

    (** (log f)' = f' / f **)
    | Log  f ->
      let f' = deriv f x in
      Div (f', f)

    (** (exp f)' = (cos f) * f' **)
    | Exp  f ->
      let f' = deriv f x in
      Mul [Exp f; f']

    (** (sin f)' = (cos f) * f' **)
    | Sin  f ->
      let f' = deriv f x in
      Mul [Cos f; f']

    (** (cos f)' = - (sin f) * f' **)
    | Cos  f ->
      let f' = deriv f x in
      Neg (Mul [Sin f; f'])

    (** (tan f)' = (1 + tan^2 f) * f'  **)
    | Tan  f ->
      let f' = deriv f x in
      Mul [Add [Num 1.0; Pow (Tan f, Num 2.0)];
           f']

    (** (asin f)' = (1 / sqrt(1 - f^2)) f' **)
    | Asin f ->
      let f' = deriv f x in
      Mul [Div (Num 1.0, Sqrt(Sub [Num 1.0; Pow(f, Num 2.0)]));
           f']

    (** (acos f)' = -(1 / sqrt(1 - f^2)) f' **)
    | Acos f ->
      let f' = deriv f x in
      Neg(Mul [Div (Num 1.0, Sqrt(Sub [Num 1.0; Pow(f, Num 2.0)]));
               f'])

    (** (atan f)' = (1 / (1 + f^2)) * f' **)
    | Atan f ->
      let f' = deriv f x in
      Mul [Div (Num 1.0, Add [Num 1.0; Pow(f, Num 2.0)]);
           f']

    (** TODO **)

    (** atan2(x,y)' = -y / (x^2 + y^2) dx + x / (x^2 + y^2) dy
                    = (-y dx + x dy) / (x^2 + y^2)
    **)
    | Atan2 (f, g) ->
      let f' = deriv f x in
      let g' = deriv g x in
      Div (Add [Mul [Neg g; f'];
                Mul [f; g']],
           Add [Pow (f, Num 2.0);
                Pow (g, Num 2.0)])

    | Matan f -> raise DerivativeNotFound

    (** (sinh f)' = (e^f + e^(-f))/2 * f' **)
    | Sinh f ->
      let f' = deriv f x in
      Mul [Div (Add [Exp f; Exp (Neg f)],
                Num 2.0);
           f']

    (** (cosh f)' = (e^f - e^(-f))/2 * f' **)
    | Cosh f ->
      let f' = deriv f x in
      Mul [Div (Sub [Exp f; Exp (Neg f)],
                Num 2.0);
           f']

    (** (tanh f)' = (sech^2 f) * f'
                  = ((2 * e^-f) / (1 + e^-2f)) * f'
    **)
    | Tanh f ->
      let f' = deriv f x in
      Mul [Num 2.0;
           Div(Exp (Neg f),
               Add [Num 1.0; Exp (Mul [Num (-2.0); f])]);
           f']

let rec subst_exp (f: string -> string) : (exp -> exp) =
  function Var s -> Var (f s)
  | Num n -> Num n
  | Neg e'  -> Neg (subst_exp f e')
  | Add el -> Add (List.map (subst_exp f) el)
  | Sub el -> Sub (List.map (subst_exp f) el)
  | Mul el -> Mul (List.map (subst_exp f) el)
  | Div (e1, e2) -> Div (subst_exp f e1, subst_exp f e2)
  | Pow (e1, e2) -> Pow (subst_exp f e1, subst_exp f e2)
  | Ite (f', e1, e2) -> Ite (subst_formula f f', subst_exp f e1, subst_exp f e2)
  | Sqrt e' -> Sqrt (subst_exp f e')
  | Safesqrt e' -> Safesqrt (subst_exp f e')
  | Abs  e' -> Abs  (subst_exp f e')
  | Log  e' -> Log  (subst_exp f e')
  | Exp  e' -> Exp  (subst_exp f e')
  | Sin  e' -> Sin  (subst_exp f e')
  | Cos  e' -> Cos  (subst_exp f e')
  | Tan  e' -> Tan  (subst_exp f e')
  | Asin e' -> Asin (subst_exp f e')
  | Acos e' -> Acos (subst_exp f e')
  | Atan e' -> Atan (subst_exp f e')
  | Atan2 (e1, e2) -> Atan2 (subst_exp f e1, subst_exp f e2)
  | Matan e' -> Matan (subst_exp f e')
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
  | FVar s -> FVar (f s)
  | Imply (f1, f2) -> Imply (subst_formula f f1, subst_formula f f2)
  | LetF (var_f_list, f') ->
    let var_f_list' =
      List.map
        (fun (var, formula) ->
          (var, subst_formula (fun x -> if x = var then x else f x) formula))
        var_f_list in
    let bounded_vars = List.map (fun (v, f) -> v) var_f_list' in
    LetF (var_f_list',
          subst_formula (fun x -> if List.mem x bounded_vars then x else f x) f')
  | LetE (var_e_list, f') ->
    let var_e_list' =
      List.map
        (fun (var, exp) ->
          (var, subst_exp (fun x -> if x = var then x else f x) exp))
        var_e_list in
    let bounded_vars = List.map (fun (v, f) -> v) var_e_list' in
    LetE (var_e_list',
          subst_formula (fun x -> if List.mem x bounded_vars then x else f x) f')


let rec count_mathfn_e =
  function
  | Var _ -> 0
  | Num _ -> 0
  | Neg e -> count_mathfn_e e
  | Add el ->
    List.sum (List.map count_mathfn_e el)
  | Sub (el) ->
    List.sum (List.map count_mathfn_e el)
  | Mul (el) ->
    List.sum (List.map count_mathfn_e el)
  | Div (e1, e2) ->
    let v1 = count_mathfn_e e1 in
    let v2 = count_mathfn_e e2 in
    v1 + v2
  | Pow (e1, e2) ->
    let v1 = count_mathfn_e e1 in
    let v2 = count_mathfn_e e2 in
    v1 + v2
  | Ite (f, e1, e2) ->
    let v = count_mathfn_f f in
    let v1 = count_mathfn_e e1 in
    let v2 = count_mathfn_e e2 in
    v + v1 + v2
  | Sqrt e -> (count_mathfn_e e) + 1
  | Abs  e -> (count_mathfn_e e) + 1
  | Log  e -> (count_mathfn_e e) + 1
  | Exp  e -> (count_mathfn_e e) + 1
  | Sin  e -> (count_mathfn_e e) + 1
  | Cos  e -> (count_mathfn_e e) + 1
  | Tan  e -> (count_mathfn_e e) + 1
  | Asin e -> (count_mathfn_e e) + 1
  | Acos e -> (count_mathfn_e e) + 1
  | Atan e -> (count_mathfn_e e) + 1
  | Atan2 (e1, e2) -> (count_mathfn_e e1) + (count_mathfn_e e2) + 1
  | Sinh e -> (count_mathfn_e e) + 1
  | Cosh e -> (count_mathfn_e e) + 1
  | Tanh e -> (count_mathfn_e e) + 1
  | Safesqrt e -> (count_mathfn_e e) + 1
  | Matan e -> (count_mathfn_e e) + 1

and count_mathfn_f =
  function
  | True -> 0
  | False -> 0
  | FVar _ -> 0
  | Not f -> count_mathfn_f f
  | And fl -> List.fold_left (fun result f -> result + (count_mathfn_f f)) 0 fl
  | Or fl -> List.fold_left (fun result f -> result + (count_mathfn_f f)) 0 fl
  | Imply (f1, f2) -> List.fold_left (fun result f -> result + (count_mathfn_f f)) 0 [f1;f2]
  | Gt (e1, e2) ->
    let v1 = count_mathfn_e e1 in
    let v2 = count_mathfn_e e2 in
    v1 + v2
  | Lt (e1, e2) ->
    let v1 = count_mathfn_e e1 in
    let v2 = count_mathfn_e e2 in
    v1 + v2
  | Ge (e1, e2) ->
    let v1 = count_mathfn_e e1 in
    let v2 = count_mathfn_e e2 in
    v1 + v2
  | Le (e1, e2) ->
    let v1 = count_mathfn_e e1 in
    let v2 = count_mathfn_e e2 in
    v1 + v2
  | Eq (e1, e2) ->
    let v1 = count_mathfn_e e1 in
    let v2 = count_mathfn_e e2 in
    v1 + v2
  | LetF (fbinding_list, f) ->
    List.sum (List.map (fun (id, f') -> count_mathfn_f f') fbinding_list)
    + (count_mathfn_f f)
  | LetE (ebinding_list, f) ->
    List.sum (List.map (fun (id, f') -> count_mathfn_e f') ebinding_list)
    + (count_mathfn_f f)
  | ForallT f -> count_mathfn_f f

let rec count_arith_e =
  function
  | Var _ -> 0
  | Num _ -> 0
  | Neg e -> count_arith_e e
  | Add el ->
    1 + (List.sum (List.map count_arith_e el))
  | Sub el ->
    1 + (List.sum (List.map count_arith_e el))
  | Mul el ->
    1 + (List.sum (List.map count_arith_e el))
  | Div (e1, e2) ->
    let v1 = count_arith_e e1 in
    let v2 = count_arith_e e2 in
    v1 + v2 + 1
  | Pow (e1, e2) ->
    let v1 = count_arith_e e1 in
    let v2 = count_arith_e e2 in
    v1 + v2 + 1
  | Ite (f, e1, e2) ->
    let v = count_arith_f f in
    let v1 = count_arith_e e1 in
    let v2 = count_arith_e e2 in
    v + v1 + v2
  | Sqrt e -> count_arith_e e
  | Abs  e -> count_arith_e e
  | Log  e -> count_arith_e e
  | Exp  e -> count_arith_e e
  | Sin  e -> count_arith_e e
  | Cos  e -> count_arith_e e
  | Tan  e -> count_arith_e e
  | Asin e -> count_arith_e e
  | Acos e -> count_arith_e e
  | Atan e -> count_arith_e e
  | Atan2 (e1, e2) -> (count_arith_e e1) + (count_arith_e e2)
  | Sinh e -> count_arith_e e
  | Cosh e -> count_arith_e e
  | Tanh e -> count_arith_e e
  | Matan e -> count_arith_e e
  | Safesqrt e -> count_arith_e e

and count_arith_f =
  function
  | True -> 0
  | False -> 0
  | FVar _ -> 0
  | Not f -> count_arith_f f
  | And fl -> List.fold_left (fun result f -> result + (count_arith_f f)) 0 fl
  | Or fl -> List.fold_left (fun result f -> result + (count_arith_f f)) 0 fl
  | Imply (f1, f2) -> List.fold_left (fun result f -> result + (count_arith_f f)) 0 [f1;f2]
  | Gt (e1, e2) ->
    let v1 = count_arith_e e1 in
    let v2 = count_arith_e e2 in
    v1 + v2
  | Lt (e1, e2) ->
    let v1 = count_arith_e e1 in
    let v2 = count_arith_e e2 in
    v1 + v2
  | Ge (e1, e2) ->
    let v1 = count_arith_e e1 in
    let v2 = count_arith_e e2 in
    v1 + v2
  | Le (e1, e2) ->
    let v1 = count_arith_e e1 in
    let v2 = count_arith_e e2 in
    v1 + v2
  | Eq (e1, e2) ->
    let v1 = count_arith_e e1 in
    let v2 = count_arith_e e2 in
    v1 + v2
  | LetF (fbinding_list, f) ->
    List.sum (List.map (fun (id, f') -> count_arith_f f') fbinding_list)
    + (count_arith_f f)
  | LetE (ebinding_list, f) ->
    List.sum (List.map (fun (id, e') -> count_arith_e e') ebinding_list)
    + (count_arith_f f)
  | ForallT f -> count_arith_f f

let rec collect_var_in_f f : string Set.t =
  match f with
  | True -> Set.empty
  | False -> Set.empty
  | FVar x -> Set.singleton x
  | Not f' -> collect_var_in_f f'
  | And fl ->
    List.fold_left Set.union Set.empty (List.map collect_var_in_f fl)
  | Or fl ->
    List.fold_left Set.union Set.empty (List.map collect_var_in_f fl)
  | Imply (f1, f2) ->
    Set.union (collect_var_in_f f1) (collect_var_in_f f2)
  | Gt (e1, e2) ->
    Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Lt (e1, e2) ->
    Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Ge (e1, e2) ->
    Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Le (e1, e2) ->
    Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Eq (e1, e2) ->
    Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | LetF (fbinding_list, f') ->
    let id_vars_list =
      List.map
        (fun (id, f') -> (id, collect_var_in_f f'))
        fbinding_list in
    let (id_list, vars_list) = List.split id_vars_list in
    let id_set = Set.of_list id_list in
    let bind_vars = List.fold_left Set.union Set.empty vars_list in
    let vars_in_f' = collect_var_in_f f' in
    Set.union (Set.diff vars_in_f' id_set) bind_vars
  | LetE (ebinding_list, f') ->
    let id_vars_list =
      List.map
        (fun (id, e') -> (id, collect_var_in_e e'))
        ebinding_list in
    let (id_list, vars_list) = List.split id_vars_list in
    let id_set = Set.of_list id_list in
    let bind_vars = List.fold_left Set.union Set.empty vars_list in
    let vars_in_f' = collect_var_in_f f' in
    Set.union (Set.diff vars_in_f' id_set) bind_vars
  | ForallT f -> collect_var_in_f f

and collect_var_in_e e : string Set.t =
  match e with
    Var x -> Set.singleton x
  | Num _ -> Set.empty
  | Neg e' -> collect_var_in_e e'
  | Add el ->
    List.fold_left Set.union Set.empty (List.map collect_var_in_e el)
  | Sub el ->
    List.fold_left Set.union Set.empty (List.map collect_var_in_e el)
  | Mul el ->
    List.fold_left Set.union Set.empty (List.map collect_var_in_e el)
  | Div (e1, e2) ->
    Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Pow (e1, e2 ) ->
    Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Ite (f, e1, e2) ->
    Set.union
      (collect_var_in_f f)
      (Set.union (collect_var_in_e e1) (collect_var_in_e e2))
  | Sqrt e1 -> collect_var_in_e e1
  | Abs e1 -> collect_var_in_e e1
  | Log e1 -> collect_var_in_e e1
  | Exp e1 -> collect_var_in_e e1
  | Sin e1 -> collect_var_in_e e1
  | Cos e1 -> collect_var_in_e e1
  | Tan e1 -> collect_var_in_e e1
  | Asin e1 -> collect_var_in_e e1
  | Acos e1 -> collect_var_in_e e1
  | Atan e1 -> collect_var_in_e e1
  | Atan2 (e1, e2) -> Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Sinh e1 -> collect_var_in_e e1
  | Cosh e1 -> collect_var_in_e e1
  | Tanh e1 -> collect_var_in_e e1
  | Matan e1 -> collect_var_in_e e1
  | Safesqrt e1 -> collect_var_in_e e1

let rec print_exp out =
  let print_exps op exps =
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
  | Num n ->
    let str_n = Printf.sprintf "%f" n in
    let str_n' =
      if String.ends_with str_n "." then
        str_n ^ "0"
      else
        str_n
    in
    String.print out str_n'
  | Neg e' -> print_exps "-" [Num 0.0; e']
  | Add el -> print_exps "+" el
  | Sub el -> print_exps "-" el
  | Mul el -> print_exps "*" el
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
    (* SQRT: MATH HACK
       sqrt(x) = pow(x, 0.5) *)
    print_exp out (Pow(e, Num(0.5)))
  | Abs  e -> (* print_exps "abs"  [e] *)
    (* ABS: MATH HACK
       abs(x) = sqrt(pow(x, 2)) *)
    print_exp out (Sqrt (Pow(e, Num(2.0))))
  | Log  e -> print_exps "log"  [e]
  | Exp  e -> print_exps "exp"  [e]
  | Sin  e -> print_exps "sin"  [e]
  | Cos  e -> print_exps "cos"  [e]
  | Tan  e -> print_exps "tan"  [e]
  | Asin e -> print_exps "arcsin" [e]
  | Acos e -> print_exps "arccos" [e]
  | Atan e -> print_exps "arctan" [e]
  | Atan2 (e1, e2) -> print_exps "arctan2" [e1; e2]
  | Sinh e -> print_exps "sinh" [e]
  | Cosh e -> print_exps "cosh" [e]
  | Tanh e -> print_exps "tanh" [e]
  | Matan e -> print_exps "matan" [e]
  | Safesqrt e -> print_exps "safesqrt" [e]

and print_formula out =
  let print_lists op out f items =
    begin
      List.print
        ~first:("("^op^" ")
        ~sep:" "
        ~last:")"
        f
        out
        items
    end in
  let print_fbinding out (x, f) =
    begin
      String.print out "(";
      String.print out x;
      String.print out " ";
      print_formula out f;
      String.print out ")";
    end in
  let print_ebinding out (x, e) =
    begin
      String.print out "(";
      String.print out x;
      String.print out " ";
      print_exp out e;
      String.print out ")";
    end in
  let print_exps op exps = print_lists op out print_exp exps in
  let print_formulas op formulas = print_lists op out print_formula formulas in
  function
  | True -> String.print out "true"
  | False -> String.print out "false"
  | FVar x -> String.print out "x"
  | Not f -> print_formulas "not" [f]
  | And fs -> print_formulas "and" fs
  | Or  fs -> print_formulas "or"  fs
  | Imply (f1, f2) -> print_formulas "=>" [f1;f2]
  | Gt  (e1, e2) -> print_exps ">"  [e1; e2]
  | Lt  (e1, e2) -> print_exps "<"  [e1; e2]
  | Ge  (e1, e2) -> print_exps ">=" [e1; e2]
  | Le  (e1, e2) -> print_exps "<=" [e1; e2]
  | Eq  (e1, e2) -> print_exps "="  [e1; e2]
  | LetE (ebinding_list, f) ->
    begin
      String.print out "(let ";
      List.print
        ~first:("(")
        ~sep:" "
        ~last:")"
        print_ebinding
        out
        ebinding_list;
      String.print out ")";
    end
  | LetF (fbinding_list, f) ->
    begin
      String.print out "(let ";
      List.print
        ~first:("(")
        ~sep:" "
        ~last:")"
        print_fbinding
        out
        fbinding_list;
      String.print out ")";
    end
  | ForallT f ->
    begin
      String.print out "(forall_t ";
      print_formula out f;
      String.print out ")";
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
  | Num n ->
    (* If n ends with ".", add "0" to make ".0" *)
    let s = Printf.sprintf "%f" n in
    let s' = match String.ends_with s "." with
      | true -> s ^ "0"
      | false -> s
    in
    String.print out s'
  | Neg e' -> print_infix_exps "-" [Num 0.0; e']
  | Add es -> print_infix_exps "+" es
  | Sub es -> print_infix_exps "-" es
  | Mul es -> print_infix_exps "*" es
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
  | Safesqrt e -> (* print_infix_exps "sqrt" [e] *)
    (* MATH HACK *)
    print_infix_exp out (Pow(e, Num 0.5))
  | Sqrt e -> (* print_infix_exps "sqrt" [e] *)
    (* MATH HACK *)
    print_infix_exp out (Pow(e, Num 0.5))
  | Abs  e -> (* print_infix_exps "abs"  [e] *)
    (* MATH HACK *)
    print_infix_exp out (Sqrt (Pow(e, Num 2.0)))
  | Log  e -> print_fncall "log"  [e]
  | Exp  e -> print_fncall "exp"  [e]
  | Sin  e -> print_fncall "sin"  [e]
  | Cos  e -> print_fncall "cos"  [e]
  | Tan  e -> print_fncall "tan"  [e]
  | Asin e -> print_fncall "arcsin" [e]
  | Acos e -> print_fncall "arccos" [e]
  | Atan e -> print_fncall "arctan" [e]
  | Atan2 (e1, e2) -> print_fncall "arctan2" [e1;e2]
  | Matan e -> print_fncall "marctan" [e]
  | Sinh e -> print_fncall "sinh" [e]
  | Cosh e -> print_fncall "cosh" [e]
  | Tanh e -> print_fncall "tanh" [e]

let rec map_exp (func : exp -> exp) (f : formula)
    : formula
    = match f with
    | True -> f
    | False -> f
    | Not f' -> Not (map_exp func f')
    | And fs -> And (List.map (map_exp func) fs)
    | Or fs -> Or (List.map (map_exp func) fs)
    | Gt (e1, e2) -> Gt(func e1, func e2)
    | Lt (e1, e2) -> Lt(func e1, func e2)
    | Ge (e1, e2) -> Ge(func e1, func e2)
    | Le (e1, e2) -> Le(func e1, func e2)
    | Eq (e1, e2) -> Eq(func e1, func e2)
    | FVar _ -> f
    | Imply (f1, f2) -> Imply (map_exp func f1, map_exp func f2)
    | LetF (str_formula_list, f') ->
      LetF (List.map (fun (str, f) -> (str, map_exp func f)) str_formula_list,
            map_exp func f')
    | LetE (str_exp_list, f') ->
      LetE (List.map (fun (str, e) -> (str, func e)) str_exp_list,
            map_exp func f')
    | ForallT f' -> ForallT (map_exp func f')
