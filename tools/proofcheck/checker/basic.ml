open Batteries

exception TODO
exception DerivativeNotFound
exception ShouldNotHappen

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

let rec deriv (e: exp) (x: string) : exp
    =
  let rec simplify e =
    let isNum e = match e with
        Num _ -> true
      | _ -> false
    in
    match e with
    | Var _ -> e
    | Num _ -> e
    | Neg e' -> Neg (simplify e')
    | Add es ->
      let es' = List.map simplify es in
      let (es_num, es_nonnum) = List.partition isNum es' in
      let e_num =
        List.reduce
          (fun e1 e2 -> match (e1, e2) with
          | (Num n1, Num n2) -> Num (n1 +. n2)
          | _ -> raise ShouldNotHappen)
          (Num 0.0::es_num)
      in
      begin
        match e_num with
          Num 0.0 -> Add es_nonnum
        | _ -> Add (e_num::es_nonnum)
      end
    | Sub [] ->
      raise ShouldNotHappen
    | Sub (e'::es) ->
      Sub [simplify e';simplify (Add es)]
    | Mul es ->
      let es' = List.map simplify es in
      let es'' =
        List.filter
          (fun e -> match e with
            Num 1.0 -> false
          | _ -> true)
          es' in
      let contain_zero =
        List.exists
          (fun e -> match e with
            Num 0.0 -> true
          | _ -> false)
          es'' in
      if contain_zero then
        (Num 0.0)
      else
        Mul es''
    | Div (e1, e2) ->
      let (e1', e2') = (simplify e1, simplify e2) in
      begin
        match e1' with
          Num 0.0 -> Num 0.0
        | _ -> Div (e1', e2')
      end
    | Pow (e1, e2) -> Pow (simplify e1, simplify e2)
    | Ite (f, e1, e2) -> Ite (f, simplify e1, simplify e2)
    | Sqrt e' -> Sqrt (simplify e')
    | Safesqrt e' -> Safesqrt (simplify e')
    | Abs e' -> Abs (simplify e')
    | Log e' -> Log (simplify e')
    | Exp e' -> Exp (simplify e')
    | Sin e' -> Sin (simplify e')
    | Cos e' -> Cos (simplify e')
    | Tan e' -> Tan (simplify e')
    | Asin e' -> Asin (simplify e')
    | Acos e' -> Acos (simplify e')
    | Atan e' -> Atan (simplify e')
    | Atan2 (e1, e2) -> Atan2 (simplify e1, simplify e2)
    | Matan e' -> Matan (simplify e')
    | Sinh e' -> Sinh (simplify e')
    | Cosh e' -> Cosh (simplify e')
    | Tanh e' -> Tanh (simplify e')

  in let result =
       match e with
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
     in
     simplify result

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
  | Var x -> String.print out x
  | Num n ->
     let str_n = Printf.sprintf "%.30f" n in
     let str_n' = Str.global_replace (Str.regexp "0+$") "0" str_n in
     let str_n'' =
       if String.ends_with str_n' "." then
         str_n' ^ "0"
       else
         str_n'
    in
    String.print out str_n''
  | Neg e' -> print_exps "~" [e']
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
  | Asin e -> print_exps "asin" [e]
  | Acos e -> print_exps "acos" [e]
  | Atan e -> print_exps "atan" [e]
  | Atan2 (e1, e2) -> print_exps "atan2" [e1; e2]
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
