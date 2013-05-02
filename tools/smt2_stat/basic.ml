(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

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
| Abs   of exp
| Log   of exp
| Exp   of exp
| Sin   of exp
| Cos   of exp
| Tan   of exp
| Asin  of exp
| Acos  of exp
| Atan  of exp
| Matan of exp
| SafeSqrt of exp
| Atan2 of exp * exp
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

let rec count_mathfn_e =
  function
  | Var _ -> 0
  | Num _ -> 0
  | Neg e -> count_mathfn_e e
  | Add el ->
    BatList.sum (List.map count_mathfn_e el)
  | Sub (el) ->
    BatList.sum (List.map count_mathfn_e el)
  | Mul (el) ->
    BatList.sum (List.map count_mathfn_e el)
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
  | Matan e -> (count_mathfn_e e) + 1
  | SafeSqrt e -> (count_mathfn_e e) + 1
  | Atan2 (e1, e2) -> (count_mathfn_e e1) + (count_mathfn_e e2) + 1
  | Sinh e -> (count_mathfn_e e) + 1
  | Cosh e -> (count_mathfn_e e) + 1
  | Tanh e -> (count_mathfn_e e) + 1
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
    BatList.sum (List.map (fun (id, f') -> count_mathfn_f f') fbinding_list)
    + (count_mathfn_f f)
  | LetE (ebinding_list, f) ->
    BatList.sum (List.map (fun (id, f') -> count_mathfn_e f') ebinding_list)
    + (count_mathfn_f f)

let rec count_arith_e =
  function
  | Var _ -> 0
  | Num _ -> 0
  | Neg e -> count_arith_e e
  | Add el ->
    1 + (BatList.sum (List.map count_arith_e el))
  | Sub el ->
    1 + (BatList.sum (List.map count_arith_e el))
  | Mul el ->
    1 + (BatList.sum (List.map count_arith_e el))
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
  | Matan e -> count_arith_e e
  | SafeSqrt e -> count_arith_e e
  | Atan2 (e1, e2) -> (count_arith_e e1) + (count_arith_e e2)
  | Sinh e -> count_arith_e e
  | Cosh e -> count_arith_e e
  | Tanh e -> count_arith_e e
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
    BatList.sum (List.map (fun (id, f') -> count_arith_f f') fbinding_list)
    + (count_arith_f f)
  | LetE (ebinding_list, f) ->
    BatList.sum (List.map (fun (id, e') -> count_arith_e e') ebinding_list)
    + (count_arith_f f)

let rec collect_var_in_f f : string BatSet.t =
  match f with
  | True -> BatSet.empty
  | False -> BatSet.empty
  | FVar x -> BatSet.singleton x
  | Not f' -> collect_var_in_f f'
  | And fl ->
    List.fold_left BatSet.union BatSet.empty (List.map collect_var_in_f fl)
  | Or fl ->
    List.fold_left BatSet.union BatSet.empty (List.map collect_var_in_f fl)
  | Imply (f1, f2) ->
    BatSet.union (collect_var_in_f f1) (collect_var_in_f f2)
  | Gt (e1, e2) ->
    BatSet.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Lt (e1, e2) ->
    BatSet.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Ge (e1, e2) ->
    BatSet.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Le (e1, e2) ->
    BatSet.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Eq (e1, e2) ->
    BatSet.union (collect_var_in_e e1) (collect_var_in_e e2)
  | LetF (fbinding_list, f') ->
    let id_vars_list =
      List.map
        (fun (id, f') -> (id, collect_var_in_f f'))
        fbinding_list in
    let (id_list, vars_list) = BatList.split id_vars_list in
    let id_set = BatSet.of_list id_list in
    let bind_vars = List.fold_left BatSet.union BatSet.empty vars_list in
    let vars_in_f' = collect_var_in_f f' in
    BatSet.union (BatSet.diff vars_in_f' id_set) bind_vars
  | LetE (ebinding_list, f') ->
    let id_vars_list =
      List.map
        (fun (id, e') -> (id, collect_var_in_e e'))
        ebinding_list in
    let (id_list, vars_list) = BatList.split id_vars_list in
    let id_set = BatSet.of_list id_list in
    let bind_vars = List.fold_left BatSet.union BatSet.empty vars_list in
    let vars_in_f' = collect_var_in_f f' in
    BatSet.union (BatSet.diff vars_in_f' id_set) bind_vars

and collect_var_in_e e : string BatSet.t =
  match e with
    Var x -> BatSet.singleton x
  | Num _ -> BatSet.empty
  | Neg e' -> collect_var_in_e e'
  | Add el ->
    List.fold_left BatSet.union BatSet.empty (List.map collect_var_in_e el)
  | Sub el ->
    List.fold_left BatSet.union BatSet.empty (List.map collect_var_in_e el)
  | Mul el ->
    List.fold_left BatSet.union BatSet.empty (List.map collect_var_in_e el)
  | Div (e1, e2) ->
    BatSet.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Pow (e1, e2 ) ->
    BatSet.union (collect_var_in_e e1) (collect_var_in_e e2)
  | Ite (f, e1, e2) ->
    BatSet.union
      (collect_var_in_f f)
      (BatSet.union (collect_var_in_e e1) (collect_var_in_e e2))
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
  | Matan e1 -> collect_var_in_e e1
  | Atan2 (e1, e2) ->
    BatSet.union (collect_var_in_e e1) (collect_var_in_e e2)
  | SafeSqrt e1 -> collect_var_in_e e1
  | Sinh e1 -> collect_var_in_e e1
  | Cosh e1 -> collect_var_in_e e1
  | Tanh e1 -> collect_var_in_e e1

let rec print_exp out =
  let print_exps op exps =
    begin
      BatList.print
        ~first:("("^op^" ")
        ~sep:" "
        ~last:")"
        print_exp
        out
        exps
    end
  in
  function
  | Var x -> BatString.print out x
  | Num n ->
    let str_n = string_of_float n in
    let str_n' =
      if BatString.ends_with str_n "." then
        str_n ^ "0"
      else
        str_n
    in
    BatString.print out str_n'
  | Neg e' -> print_exps "-" [e']
  | Add el -> print_exps "+" el
  | Sub el -> print_exps "-" el
  | Mul el -> print_exps "*" el
  | Div (e1, e2) -> print_exps "/" [e1; e2]
  | Pow (e1, e2) -> print_exps "^" [e1; e2]
  | Ite (f, e1, e2) ->
    begin
      BatString.print out "(ite ";
      print_formula out f;
      BatString.print out " ";
      print_exp out e1;
      BatString.print out " ";
      print_exp out e2;
      BatString.print out ")"
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
  | Matan e -> print_exps "marctan" [e]
  | SafeSqrt e -> print_exps "safesqrt" [e]
  | Atan2 (e1, e2) -> print_exps "arctan2" [e1; e2]
  | Sinh e -> print_exps "sinh" [e]
  | Cosh e -> print_exps "cosh" [e]
  | Tanh e -> print_exps "tanh" [e]

and print_formula out =
  let print_lists op out f items =
    begin
      BatList.print
        ~first:("("^op^" ")
        ~sep:" "
        ~last:")"
        f
        out
        items
    end in
  let print_fbinding out (x, f) =
    begin
      BatString.print out "(";
      BatString.print out x;
      BatString.print out " ";
      print_formula out f;
      BatString.print out ")";
    end in
  let print_ebinding out (x, e) =
    begin
      BatString.print out "(";
      BatString.print out x;
      BatString.print out " ";
      print_exp out e;
      BatString.print out ")";
    end in
  let print_exps op exps = print_lists op out print_exp exps in
  let print_formulas op formulas = print_lists op out print_formula formulas in
  function
  | True -> BatString.print out "true"
  | False -> BatString.print out "false"
  | FVar x -> BatString.print out "x"
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
      BatString.print out "(let ";
      BatList.print
        ~first:("(")
        ~sep:" "
        ~last:")"
        print_ebinding
        out
        ebinding_list;
      BatString.print out ")";
    end
  | LetF (fbinding_list, f) ->
    begin
      BatString.print out "(let ";
      BatList.print
        ~first:("(")
        ~sep:" "
        ~last:")"
        print_fbinding
        out
        fbinding_list;
      BatString.print out ")";
    end
