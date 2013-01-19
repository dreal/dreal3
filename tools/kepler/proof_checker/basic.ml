(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type exp =
| Var   of string
| Num of float
| Neg   of exp
| Add   of exp * exp
| Sub   of exp * exp
| Mul   of exp * exp
| Div   of exp * exp
| Pow   of exp * float
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

let rec collect_var_in_f f =
  match f with
  | True -> []
  | False -> []
  | Not f' -> collect_var_in_f f'
  | And fl -> List.concat (List.map collect_var_in_f fl)
  | Or fl -> List.concat (List.map collect_var_in_f fl)
  | Gt (e1, e2) -> List.concat [collect_var_in_e e1;
                               collect_var_in_e e2;]
  | Lt (e1, e2) -> List.concat [collect_var_in_e e1;
                               collect_var_in_e e2;]
  | Gt (e1, e2) -> List.concat [collect_var_in_e e1;
                               collect_var_in_e e2;]
  | Ge (e1, e2) -> List.concat [collect_var_in_e e1;
                               collect_var_in_e e2;]
  | Le (e1, e2) -> List.concat [collect_var_in_e e1;
                               collect_var_in_e e2;]
  | Eq (e1, e2) -> List.concat [collect_var_in_e e1;
                               collect_var_in_e e2;]
and collect_var_in_e e =
  match e with
    Var x -> [x]
  | Num _ -> []
  | Neg e' -> collect_var_in_e e'
  | Add (e1, e2) -> List.concat [collect_var_in_e e1;
                                collect_var_in_e e2;]
  | Sub (e1, e2) -> List.concat [collect_var_in_e e1;
                                collect_var_in_e e2;]
  | Mul (e1, e2) -> List.concat [collect_var_in_e e1;
                                collect_var_in_e e2;]
  | Div (e1, e2) -> List.concat [collect_var_in_e e1;
                                collect_var_in_e e2;]
  | Pow (e1, _ ) -> collect_var_in_e e1
  | Ite (f, e1, e2) -> List.concat [collect_var_in_f f;
                                   collect_var_in_e e1;
                                   collect_var_in_e e2;]
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
  | Sinh e1 -> collect_var_in_e e1
  | Cosh e1 -> collect_var_in_e e1
  | Tanh e1 -> collect_var_in_e e1


let rec print_exp out =
  let print_exps op exps =
    begin
      BatList.print
        (~first:("("^op^" "))
        (~sep:" ")
        (~last:")")
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
  | Add (e1, e2) -> print_exps "+" [e1; e2]
  | Sub (e1, e2) -> print_exps "-" [e1; e2]
  | Mul (e1, e2) -> print_exps "*" [e1; e2]
  | Div (e1, e2) -> print_exps "/" [e1; e2]
  | Pow (e1, n) -> print_exps "^" [e1; Num (n)]
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
    print_exp out (Pow(e, 0.5))
  | Abs  e -> (* print_exps "abs"  [e] *)
    (* ABS: MATH HACK
       abs(x) = sqrt(pow(x, 2)) *)
    print_exp out (Sqrt (Pow(e, 2.0)))
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

and print_formula out =
  let print_lists op out f items =
    begin
      BatList.print
        (~first:("("^op^" "))
        (~sep:" ")
        (~last:")")
        f
        out
        items
    end
  in
  let print_exps op exps = print_lists op out print_exp exps in
  let print_formulas op formulas = print_lists op out print_formula formulas in
  function
  | True -> BatString.print out "true"
  | False -> BatString.print out "false"
  | Not f -> print_formulas "not" [f]
  | And fs -> print_formulas "and" fs
  | Or  fs -> print_formulas "or"  fs
  | Gt  (e1, e2) -> print_exps ">"  [e1; e2]
  | Lt  (e1, e2) -> print_exps "<"  [e1; e2]
  | Ge  (e1, e2) -> print_exps ">=" [e1; e2]
  | Le  (e1, e2) -> print_exps "<=" [e1; e2]
  | Eq  (e1, e2) -> print_exps "="  [e1; e2]
