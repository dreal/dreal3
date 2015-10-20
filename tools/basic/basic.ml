open Batteries

exception TODO
exception DerivativeNotFound

type var = string

type exp =
  | Var      of string
  | Vec      of string list
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
  | Min      of exp * exp
  | Max      of exp * exp
  | Integral of float * string * string list * string (* (integral 0 time_1 [x_1_0 ... x_i_0] flow1) *)
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
   | Gtp  of exp * exp * float
   | Ltp  of exp * exp * float
   | Gep  of exp * exp * float
   | Lep  of exp * exp * float
   | Eqp  of exp * exp * float
   | LetF of ((string * formula) list * formula)
   | LetE of ((string * exp) list * formula)
   | ForallT of exp * exp * exp * formula

let rec collect_vars_in_formula (f : formula) : var Set.t =
  match f with
    True -> Set.empty
  | False -> Set.empty
  | Not f' -> collect_vars_in_formula f'
  | And fs -> collect_vars_in_formulas fs
  | Or  fs -> collect_vars_in_formulas fs
  | Gt (e1, e2) | Lt (e1, e2) | Ge (e1, e2) | Le (e1, e2) | Eq (e1, e2) | Gtp (e1, e2, _) | Ltp (e1, e2, _) | Gep (e1, e2, _) | Lep (e1, e2, _) | Eqp (e1, e2, _) -> collect_vars_in_exps [e1;e2]
  | Imply (f1, f2) -> collect_vars_in_formulas [f1;f2]
  | FVar x -> Set.singleton x
  | ForallT (m, lb, ub, f') ->
     List.reduce Set.union [collect_vars_in_exp m;
                            collect_vars_in_exp lb;
                            collect_vars_in_exp ub;
                            collect_vars_in_formula f']
  | LetF _ -> raise TODO
  | LetE _ -> raise TODO
and collect_vars_in_exps (es : exp list) =
  List.reduce Set.union (List.map collect_vars_in_exp es)
and collect_vars_in_formulas (fs : formula list) =
  List.reduce Set.union (List.map collect_vars_in_formula fs)
and collect_vars_in_exp (e : exp) : var Set.t = match e with
    Var x -> Set.singleton x
  | Vec xs -> Set.of_list xs
  | Num _ -> Set.empty
  | Neg e' -> collect_vars_in_exp e'
  | Add es | Sub es | Mul es -> collect_vars_in_exps es
  | Div (e1, e2) | Pow (e1, e2) | Atan2 (e1, e2) | Min (e1, e2) | Max (e1, e2) -> collect_vars_in_exps [e1;e2]
  | Ite (f, e1, e2) ->
     let s1 = collect_vars_in_formula f in
     let s2 = collect_vars_in_exps [e1; e2] in
     Set.union s1 s2
  | Sqrt e' | Abs e'  | Log e'  | Exp e'   | Sin e'   | Cos e'   | Tan e'
  | Asin e' | Acos e' | Atan e' | Asinh e' | Acosh e' | Atanh e' | Matan e'
  | Sinh e' | Cosh e' | Tanh e' | Safesqrt e' -> collect_vars_in_exp e'
  | Integral (n, t, x0s, flow) ->
     Set.add t (Set.of_list x0s)
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

let rec map_exp (fn_f: formula -> formula) (fn_e: exp -> exp) : (exp -> exp) =
  function Var s     -> fn_e (Var      s)
         | Vec xs           -> fn_e (Vec      xs)
         | Num n            -> fn_e (Num      n)
         | Neg e'           -> fn_e (Neg      (map_exp fn_f fn_e e'))
         | Add es           -> fn_e (Add      (List.map (map_exp fn_f fn_e) es))
         | Sub es           -> fn_e (Sub      (List.map (map_exp fn_f fn_e) es))
         | Mul es           -> fn_e (Mul      (List.map (map_exp fn_f fn_e) es))
         | Div (e1, e2)     -> fn_e (Div      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Pow (e1, e2)     -> fn_e (Pow      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Ite (f', e1, e2) -> fn_e (Ite      (map_formula fn_f fn_e f', map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Sqrt e'          -> fn_e (Sqrt     (map_exp fn_f fn_e e'))
         | Safesqrt e'      -> fn_e (Safesqrt (map_exp fn_f fn_e e'))
         | Abs e'           -> fn_e (Abs      (map_exp fn_f fn_e e'))
         | Log e'           -> fn_e (Log      (map_exp fn_f fn_e e'))
         | Exp e'           -> fn_e (Exp      (map_exp fn_f fn_e e'))
         | Sin e'           -> fn_e (Sin      (map_exp fn_f fn_e e'))
         | Cos e'           -> fn_e (Cos      (map_exp fn_f fn_e e'))
         | Tan e'           -> fn_e (Tan      (map_exp fn_f fn_e e'))
         | Asin e'          -> fn_e (Asin     (map_exp fn_f fn_e e'))
         | Acos e'          -> fn_e (Acos     (map_exp fn_f fn_e e'))
         | Atan e'          -> fn_e (Atan     (map_exp fn_f fn_e e'))
         | Asinh e'         -> fn_e (Asinh    (map_exp fn_f fn_e e'))
         | Acosh e'         -> fn_e (Acosh    (map_exp fn_f fn_e e'))
         | Atanh e'         -> fn_e (Atanh    (map_exp fn_f fn_e e'))
         | Atan2 (e1, e2)   -> fn_e (Atan2    (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Min   (e1, e2)   -> fn_e (Min      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Max   (e1, e2)   -> fn_e (Max      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Matan e'         -> fn_e (Matan    (map_exp fn_f fn_e e'))
         | Sinh e'          -> fn_e (Sinh     (map_exp fn_f fn_e e'))
         | Cosh e'          -> fn_e (Cosh     (map_exp fn_f fn_e e'))
         | Tanh e'          -> fn_e (Tanh     (map_exp fn_f fn_e e'))
         | Integral (n, t, x0s, flow) -> fn_e (Integral (n, t, x0s, flow))
and map_formula (fn_f : formula -> formula) (fn_e: exp -> exp) : (formula -> formula) =
  function True    -> fn_f True
         | False          -> fn_f False
         | Not f          -> fn_f (Not     (map_formula fn_f fn_e f))
         | And fs         -> fn_f (And     (List.map (map_formula fn_f fn_e) fs))
         | Or fs          -> fn_f (Or      (List.map (map_formula fn_f fn_e) fs))
         | Gt (e1, e2)    -> fn_f (Gt      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Lt (e1, e2)    -> fn_f (Lt      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Ge (e1, e2)    -> fn_f (Ge      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Le (e1, e2)    -> fn_f (Le      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Eq (e1, e2)    -> fn_f (Eq      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2))
         | Gtp (e1, e2, p)    -> fn_f (Gtp      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2, p))
         | Ltp (e1, e2, p)    -> fn_f (Ltp      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2, p))
         | Gep (e1, e2, p)    -> fn_f (Gep      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2, p))
         | Lep (e1, e2, p)    -> fn_f (Lep      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2, p))
         | Eqp (e1, e2, p)    -> fn_f (Eqp      (map_exp fn_f fn_e e1, map_exp fn_f fn_e e2, p))
         | Imply (f1, f2) -> fn_f (Imply   (map_formula fn_f fn_e f1, map_formula fn_f fn_e f2))
         | ForallT (m, lb, ub, f) -> fn_f (ForallT (map_exp fn_f fn_e m,
                                                    map_exp fn_f fn_e lb,
                                                    map_exp fn_f fn_e ub,
                                                    map_formula fn_f fn_e f))
         | FVar x         -> fn_f (FVar x)
         | LetE (var_e_list, f) ->
            let var_e_list' = List.map (fun (v, e) -> (v, map_exp fn_f fn_e e)) var_e_list in
            let bounded_vars = List.map (fun (v, f) -> v) var_e_list' in
            let fn_e' e = match e with
              | Var v -> if List.mem v bounded_vars then e
                         else fn_e e
              | _ -> fn_e e
            in
            let f' = map_formula fn_f fn_e' f in
            fn_f (LetE (var_e_list', f'))
         | LetF (var_f_list, f) ->
            let var_f_list' = List.map (fun (v, f) -> (v, map_formula fn_f fn_e f)) var_f_list in
            let bounded_vars = List.map (fun (v, f) -> v) var_f_list' in
            let fn_e' e = match e with
              | Var v -> if List.mem v bounded_vars then e
                         else fn_e e
              | _ -> fn_e e
            in
            let f' = map_formula fn_f fn_e' f in
            fn_f (LetF (var_f_list', f'))

let preprocess_exp (f: string -> exp) : (exp -> exp) =
  let aux : (exp -> exp) = function Var s -> f s
                                  | e -> e
  in
  map_exp identity aux
let preprocess_formula (f: string -> exp) : (formula -> formula) =
  let aux : (exp -> exp) = function Var s -> f s
                                  | e -> e
  in
  map_formula identity aux

let rec deriv (e: exp) (x: string) : exp
  = match e with
    Var v -> if v = x then Num 1.0 else Num 0.0
  | Vec xs -> raise DerivativeNotFound
  | Num _ -> Num 0.0
  | Neg e' -> Neg (deriv e' x)
  | Add es -> Add (List.map (fun e' -> deriv e' x) es)
  | Sub es -> Sub (List.map (fun e' -> deriv e' x) es)
  | Mul [] -> Num 0.0

  (** (f * g)' = f' * g + f * g' **)
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

  (** (exp f)' = f * f' **)
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
  | Min (f, g) -> raise DerivativeNotFound
  | Max (f, g) -> raise DerivativeNotFound

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
  (** (asinh f)' = (e^f + e^(-f))/2 * f' **)
  | Asinh f ->
     let f' = deriv f x in
     Mul [Div (Add [Exp f; Exp (Neg f)],
               Num 2.0);
          f']

  (** (acosh f)' = (e^f - e^(-f))/2 * f' **)
  | Acosh f ->
     let f' = deriv f x in
     Mul [Div (Sub [Exp f; Exp (Neg f)],
               Num 2.0);
          f']

  (** (atanh f)' = (sech^2 f) * f'
                    = ((2 * e^-f) / (1 + e^-2f)) * f'
   **)
  | Atanh f ->
     let f' = deriv f x in
     Mul [Num 2.0;
          Div(Exp (Neg f),
              Add [Num 1.0; Exp (Mul [Num (-2.0); f])]);
          f']
  | Integral _ -> raise TODO

let subst_exp (f: string -> string) : (exp -> exp) =
  let fn_e e = match e with
    | Var s -> Var (f s)
    | _ -> e
  in
  map_exp identity fn_e

let rec subst_formula (f: string -> string) : (formula -> formula) =
  let fn_e e = match e with
    | Var s -> Var (f s)
    | _ -> e
  in
  map_formula identity fn_e

let rec count_mathfn_e =
  function
  | Var _ | Vec _ | Num _ -> 0
  | Neg e -> count_mathfn_e e
  | Add es | Sub es | Mul es -> List.sum (List.map count_mathfn_e es)
  | Div (e1, e2) | Pow (e1, e2) ->
                    let v1 = count_mathfn_e e1 in
                    let v2 = count_mathfn_e e2 in
                    v1 + v2
  | Ite (f, e1, e2) ->
     let v = count_mathfn_f f in
     let v1 = count_mathfn_e e1 in
     let v2 = count_mathfn_e e2 in
     v + v1 + v2
  | Sqrt e | Abs e | Log e | Exp e | Sin e | Cos e | Tan e | Asin e
  | Acos e | Atan e | Sinh e | Cosh e | Tanh e | Asinh e | Acosh e
  | Safesqrt e | Matan e | Atanh e -> (count_mathfn_e e) + 1
  | Atan2 (e1, e2) | Min (e1, e2) | Max (e1, e2) -> (count_mathfn_e e1) + (count_mathfn_e e2) + 1
  | Integral _ -> raise TODO

and count_mathfn_f =
  function
  | True -> 0
  | False -> 0
  | FVar _ -> 0
  | Not f -> count_mathfn_f f
  | And fl -> List.fold_left (fun result f -> result + (count_mathfn_f f)) 0 fl
  | Or fl -> List.fold_left (fun result f -> result + (count_mathfn_f f)) 0 fl
  | Imply (f1, f2) -> List.fold_left (fun result f -> result + (count_mathfn_f f)) 0 [f1;f2]
  | Gt (e1, e2) | Lt (e1, e2) | Ge (e1, e2) | Le (e1, e2)
  | Eq (e1, e2) | Gtp (e1, e2, _) | Ltp (e1, e2, _) | Gep (e1, e2, _) | Lep (e1, e2, _) | Eqp (e1, e2, _) ->
                                                                                           let v1 = count_mathfn_e e1 in
                                                                                           let v2 = count_mathfn_e e2 in
                                                                                           v1 + v2
  | LetF (fbinding_list, f) ->
     List.sum (List.map (fun (id, f') -> count_mathfn_f f') fbinding_list) + (count_mathfn_f f)
  | LetE (ebinding_list, f) ->
     List.sum (List.map (fun (id, f') -> count_mathfn_e f') ebinding_list) + (count_mathfn_f f)
  | ForallT (m, lb, ub, f) ->
     (count_mathfn_e m) + (count_mathfn_e lb)
     + (count_mathfn_e ub) + (count_mathfn_f f)

let rec count_arith_e =
  function
  | Var _ | Vec _ | Num _ -> 0
  | Add es | Sub es | Mul es -> 1 + (List.sum (List.map count_arith_e es))
  | Div (e1, e2) | Pow (e1, e2) ->
                    let v1 = count_arith_e e1 in
                    let v2 = count_arith_e e2 in
                    v1 + v2 + 1
  | Ite (f, e1, e2) ->
     let v = count_arith_f f in
     let v1 = count_arith_e e1 in
     let v2 = count_arith_e e2 in
     v + v1 + v2
  | Neg e | Sqrt e | Abs e | Log e | Exp e | Sin e | Cos e | Tan e
  | Asin e | Acos e | Atan e | Sinh e | Cosh e | Tanh e
  | Asinh e | Acosh e | Atanh e | Matan e
  | Safesqrt e -> count_arith_e e
  | Atan2 (e1, e2) | Min (e1, e2) | Max (e1, e2) -> (count_arith_e e1) + (count_arith_e e2)
  | Integral _ -> raise TODO

and count_arith_f =
  function
  | True | False | FVar _ -> 0
  | Not f -> count_arith_f f
  | And fs | Or fs -> List.fold_left (fun result f -> result + (count_arith_f f)) 0 fs
  | Imply (f1, f2) -> (count_arith_f f1) + (count_arith_f f2)
  | Gt (e1, e2) | Lt (e1, e2) | Ge (e1, e2) | Le (e1, e2) | Eq (e1, e2) | Gtp (e1, e2, _) | Ltp (e1, e2, _) | Gep (e1, e2, _) | Lep (e1, e2, _) | Eqp (e1, e2, _) ->
                                                                                                                                                   (count_arith_e e1) + (count_arith_e e2)
  | LetF (fbinding_list, f) ->
     List.sum (List.map (fun (id, f') -> count_arith_f f') fbinding_list)
     + (count_arith_f f)
  | LetE (ebinding_list, f) ->
     List.sum (List.map (fun (id, e') -> count_arith_e e') ebinding_list)
     + (count_arith_f f)
  | ForallT (m, lb, ub, f) ->
     (count_arith_e m) + (count_arith_e lb)
     + (count_arith_e ub) + (count_arith_f f)

let rec collect_var_in_f f : string Set.t =
  match f with
  | True | False -> Set.empty
  | FVar x -> Set.singleton x
  | Not f' -> collect_var_in_f f'
  | And fs | Or fs ->
              List.reduce Set.union  (List.map collect_var_in_f fs)
  | Imply (f1, f2) -> Set.union (collect_var_in_f f1) (collect_var_in_f f2)
  | Gt (e1, e2) | Lt (e1, e2) | Ge (e1, e2) | Le (e1, e2) | Eq (e1, e2) | Gtp (e1, e2, _) | Ltp (e1, e2, _) | Gep (e1, e2, _) | Lep (e1, e2, _) | Eqp (e1, e2, _) ->
                                                                                                                                                   Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | LetF (fbinding_list, f') ->
     let id_vars_list =
       List.map
         (fun (id, f') -> (id, collect_var_in_f f'))
         fbinding_list in
     let (id_list, vars_list) = List.split id_vars_list in
     let id_set = Set.of_list id_list in
     let bind_vars = List.reduce Set.union  vars_list in
     let vars_in_f' = collect_var_in_f f' in
     Set.union (Set.diff vars_in_f' id_set) bind_vars
  | LetE (ebinding_list, f') ->
     let id_vars_list =
       List.map
         (fun (id, e') -> (id, collect_var_in_e e'))
         ebinding_list in
     let (id_list, vars_list) = List.split id_vars_list in
     let id_set = Set.of_list id_list in
     let bind_vars = List.reduce Set.union vars_list in
     let vars_in_f' = collect_var_in_f f' in
     Set.union (Set.diff vars_in_f' id_set) bind_vars
  | ForallT (m, lb, ub, f)
    -> List.reduce Set.union [collect_var_in_e m;
                              collect_var_in_e lb;
                              collect_var_in_e ub;
                              collect_var_in_f f]

and collect_var_in_e e : string Set.t =
  match e with
    Var x -> Set.singleton x
  | Vec xs -> Set.of_list xs
  | Num _ -> Set.empty
  | Add el ->
     List.reduce Set.union (List.map collect_var_in_e el)
  | Sub el ->
     List.reduce Set.union  (List.map collect_var_in_e el)
  | Mul el ->
     List.reduce Set.union  (List.map collect_var_in_e el)
  | Div (e1, e2) | Pow (e1, e2 ) | Atan2 (e1, e2) | Min (e1, e2) | Max (e1, e2) ->
     Set.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Ite (f, e1, e2) ->
     Set.union
       (collect_var_in_f f)
       (Set.union (collect_var_in_e e1) (collect_var_in_e e2))
  | Neg e' | Sqrt e' | Abs e' | Log e' | Exp e'
  | Sin e' | Cos e' | Tan e' | Asin e' | Acos e'
  | Atan e' | Sinh e' | Cosh e' | Tanh e'
  | Asinh e' | Acosh e' | Atanh e' | Matan e'
  | Safesqrt e' -> collect_var_in_e e'
  | Integral (time_0, time_t, vars, flow) ->
     Set.of_list (time_t::vars)

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
  | Vec xs -> List.print ~first:"[" ~last:"]" ~sep:" "
                         (fun out x -> print_exp out (Var x))
                         out
                         xs
  | Num n ->
     let str_n = Printf.sprintf "%g" n in
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
  | Min (e1, e2) -> print_exps "min" [e1; e2]
  | Max (e1, e2) -> print_exps "max" [e1; e2]
  | Sinh e -> print_exps "sinh" [e]
  | Cosh e -> print_exps "cosh" [e]
  | Tanh e -> print_exps "tanh" [e]
  | Asinh e -> print_exps "asinh" [e]
  | Acosh e -> print_exps "acosh" [e]
  | Atanh e -> print_exps "atanh" [e]
  | Matan e -> print_exps "matan" [e]
  | Safesqrt e -> print_exps "safesqrt" [e]
  | Integral (time_0, time_t, xs, flow) ->
     let str_xs = BatIO.to_string (List.print ~first:"[" ~last:"]" ~sep:" " String.print) xs in
     begin
       List.print ~first:"(" ~last:")" ~sep:" " String.print out ["integral"; string_of_float time_0; time_t; str_xs; flow]
     end

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
  let print_plists op out f items p =
    begin
      let ps =  Printf.sprintf "%f" p in
      List.print
        ~first:("("^op^" ")
        ~sep:" "
        ~last:(" ["^ps^"])")
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
  let print_pexps op exps p = print_plists op out print_exp exps p in
  let print_formulas op formulas = print_lists op out print_formula formulas in
  function
  | True -> String.print out "true"
  | False -> String.print out "false"
  | FVar x -> String.print out "x"
  | Not f -> print_formulas "not" [f]
  | And fs -> print_formulas "and" fs
  | Or  fs -> print_formulas "or"  fs
  | Imply (f1, f2) -> print_formulas "=>" [f1;f2]
  | Gt (e1, e2) -> print_exps ">"  [e1; e2]
  | Lt (e1, e2) -> print_exps "<"  [e1; e2]
  | Ge (e1, e2) -> print_exps ">=" [e1; e2]
  | Le (e1, e2) -> print_exps "<=" [e1; e2]
  | Eq (e1, e2) -> print_exps "="  [e1 ; e2]
  | Gtp  (e1, e2, p) -> print_pexps ">"  [e1; e2] p
  | Ltp  (e1, e2, p) -> print_pexps "<"  [e1; e2] p
  | Gep  (e1, e2, p) -> print_pexps ">=" [e1; e2] p
  | Lep  (e1, e2, p) -> print_pexps "<=" [e1; e2] p
  | Eqp  (e1, e2, p) -> print_pexps "="  [e1; e2] p
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
  | ForallT (m, lb, ub, f)->
     begin
       String.print out "(forall_t ";
       print_exp out m;
       String.print out " [";
       print_exp out lb;
       String.print out " ";
       print_exp out ub;
       String.print out "] ";
       print_formula out f;
       String.print out ")";
     end
let rec print_infix_exps (out : 'a IO.output) (op : string) (exps : exp list) =
  begin
    List.print
      ~first:"("
      ~sep: (" " ^ op ^ " ")
      ~last:")"
      print_infix_exp
      out
      exps
  end
and print_infix_exp (out : 'a IO.output) : exp -> unit =
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
  | Vec xs -> List.print ~first:"[" ~last:"]" ~sep:" "
                         (fun out x -> print_exp out (Var x))
                         out
                         xs
  | Num n ->
     (* If n ends with ".", add "0" to make ".0" *)
     let s = Printf.sprintf "%f" n in
     let s' = match String.ends_with s "." with
       | true -> s ^ "0"
       | false -> s
     in
     String.print out s'
  | Neg e' -> print_infix_exps out "-" [Num 0.0; e']
  | Add es -> print_infix_exps out "+" es
  | Sub es -> print_infix_exps out "-" es
  | Mul es -> print_infix_exps out "*" es
  | Div (e1, e2) -> print_infix_exps out "/" [e1; e2]
  | Pow (e1, e2) -> print_infix_exps out "^" [e1; e2]
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
  | Min (e1, e2) -> print_fncall "min" [e1;e2]
  | Max (e1, e2) -> print_fncall "max" [e1;e2]
  | Matan e -> print_fncall "marctan" [e]
  | Sinh e -> print_fncall "sinh" [e]
  | Cosh e -> print_fncall "cosh" [e]
  | Tanh e -> print_fncall "tanh" [e]
  | Asinh e -> print_fncall "asinh" [e]
  | Acosh e -> print_fncall "acosh" [e]
  | Atanh e -> print_fncall "atanh" [e]
  | Integral (time_0, time_t, xs, flow) ->
     let str_xs = BatIO.to_string (List.print ~first:"[" ~last:"]" ~sep:" " String.print) xs in
     begin
       List.print ~first:"integral( " ~last:")" ~sep:" " String.print out [string_of_float time_0; time_t; str_xs; flow]
     end
and print_infix_formula (out : 'a IO.output) : formula -> unit =
  let print_infix_formulas (bop : string) (fs : formula list) : unit =
    List.print ~first:"" ~sep:bop ~last:"" print_infix_formula out fs
  in
  function
  | True -> String.print out "true"
  | False -> String.print out "false"
  | FVar x -> String.print out "x"
  | Not f -> print_infix_formulas "not" [f]
  | And fs -> print_infix_formulas "and" fs
  | Or  fs -> print_infix_formulas "or"  fs
  | Imply (f1, f2) -> print_infix_formulas "=>" [f1;f2]
  | Gt (e1, e2) -> print_infix_exps out ">"  [e1; e2]
  | Lt (e1, e2) -> print_infix_exps out "<"  [e1; e2]
  | Ge (e1, e2) -> print_infix_exps out ">=" [e1; e2]
  | Le (e1, e2) -> print_infix_exps out "<=" [e1; e2]
  | Eq (e1, e2) -> print_infix_exps out "="  [e1 ; e2]
  | Gtp  (e1, e2, p) -> failwith "print_infix_formula: not support Gtp yet"
  | Ltp  (e1, e2, p) -> failwith "print_infix_formula: not support Ltp yet"
  | Gep  (e1, e2, p) -> failwith "print_infix_formula: not support Gep yet"
  | Lep  (e1, e2, p) -> failwith "print_infix_formula: not support Lep yet"
  | Eqp  (e1, e2, p) -> failwith "print_infix_formula: not support Eqp yet"
  | LetE _ -> failwith "print_infix_formula: not support LetE yet"
  | LetF _ -> failwith "print_infix_formula: not support LetE yet"
  | ForallT (m, lb, ub, f)-> failwith "print_infix_formula: not support ForallT yet"

let rec real_eval (e : (string, float) Map.t) (f : exp) : float
  = match f with
    Var x -> Map.find x e
  | Num n -> n
  | Neg f' -> -. (real_eval e f')
  | Add fl ->
     List.fold_left (+.) 0.0 (List.map (real_eval e) fl)
  | Sub (f1::rest) ->
     (real_eval e f1) -. (real_eval e (Add rest))
  | Sub [] -> raise TODO
  | Mul fl ->
     List.fold_left ( *. ) 1.0 (List.map (real_eval e) fl)
  | Div (f1, f2) -> (real_eval e f1) /. (real_eval e f2)
  | Ite _ -> raise TODO
  | Pow (f', Num n) -> (real_eval e f') ** n
  | Pow (f1, f2) -> (real_eval e f1) ** (real_eval e f2)
  | Sqrt f' -> sqrt (real_eval e f')
  | Safesqrt f' ->
     let v = (real_eval e f') in
     if v <= 0.0 then 0.0
     else sqrt v
  | Abs f' -> abs_float (real_eval e f')
  | Log f' -> log (real_eval e f')
  | Exp f' -> exp (real_eval e f')
  | Sin f' -> sin (real_eval e f')
  | Cos f' -> cos (real_eval e f')
  | Tan f' -> tan (real_eval e f')
  | Asin f' -> asin (real_eval e f')
  | Acos f' -> acos (real_eval e f')
  | Atan f' -> atan (real_eval e f')
  | Asinh f' -> raise TODO
  | Acosh f' -> raise TODO
  | Atanh f' -> raise TODO
  | Atan2 (f1, f2) -> atan2 (real_eval e f1) (real_eval e f2)
  | Matan f' ->
     let v = real_eval e f' in
     if v = 0.0 then 1.0
     else if v > 0.0 then
       let sqrt_v = sqrt v in
       (atan sqrt_v) /. (sqrt_v)
     else
       let sqrt_minus_v = sqrt (~-. v) in
       log ((1.0 +. sqrt_minus_v) /. (1.0 -. sqrt_minus_v)) /. (2.0 *. sqrt_minus_v)
  | Sinh f' -> sinh (real_eval e f')
  | Cosh f' -> cosh (real_eval e f')
  | Tanh f' -> tanh (real_eval e f')
  | Min (f1, f2) -> min (real_eval e f1) (real_eval e f2)
  | Max (f1, f2) -> max (real_eval e f1) (real_eval e f2)
  | Vec _  -> raise TODO
  | Integral _ -> raise TODO
