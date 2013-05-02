(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type float_option =
  Float    (* Floating point   : 3.141592            *)
| IntRatio (* Ratio of integers: (3141592 / 1000000) *)

let fop = ref Float

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
| Matan of exp
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
  | Var x ->
    let filter str =
      (* filter out '(' and ')' *)
      let s1 = BatString.filter (fun c -> c != '(' && c != ')') str in
      (* replace '*' with "ptr_" *)
      let s2 = BatString.replace_chars (fun c -> if c == '*' then "ptr_" else BatString.of_char c) s1 in
      (* replace '.' with "_" *)
      let s3 = BatString.replace_chars (fun c -> if c == '.' then "_" else BatString.of_char c) s2 in
      (* replace "->" with "_" *)
      let rec replace_all (str : string) (sub : string) (by : string) =
        let (b, str') = BatString.replace str sub by in
        match b with
        | true -> replace_all str' sub by
        | false -> str'
      in
      replace_all s3 "->" "_"
    in
    BatString.print out (filter x)
  | Const n ->
    begin
      let s = BatFloat.to_string n in
      let s' =
        match !fop with
        | Float ->
            begin
              (* If n ends with ".", add "0" to make ".0" *)
              match BatString.ends_with s "." with
              | true -> s ^ "0"
              | false -> s
            end
        | IntRatio ->
          begin
            let (int_part, deci_part) = BatString.split s "." in
            let int_part = if int_part = "0" then "" else int_part in
            let l = String.length deci_part in
            let (num, denom) = (int_part ^ deci_part, BatInt.to_string (BatInt.pow 10 l)) in
            match (num, denom) with
            | ("", _) -> "0"           (* 0.0  *)
            | (_, "1") -> int_part     (* x / 1 = x  *)
            | (_, _) -> ("(/ " ^ num ^ " " ^ denom ^ ")")
          end
      in BatString.print out s'
    end
  | Neg e' -> print_exps "-" [e']
  | Add (e1, e2) -> print_exps "+" [e1; e2]
  | Sub (e1, e2) -> print_exps "-" [e1; e2]
  | Mul (e1, e2) -> print_exps "*" [e1; e2]
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
    (* print_exp out (Pow(e, Const 0.5)) *)
    print_exps "sqrt" [e]
  | Safesqrt e ->
    print_exps "safesqrt" [e]
  | Abs  e -> (* print_exps "abs"  [e] *)
    (* ABS: MATH HACK
       abs(x) = sqrt(pow(x, 2)) *)
    (* print_exp out (Sqrt (Pow(e, Const 2.0))) *)
    print_exps "abs" [e]
  | Log  e -> print_exps "log"  [e]
  | Exp  e -> print_exps "exp"  [e]
  | Sin  e -> print_exps "sin"  [e]
  | Cos  e -> print_exps "cos"  [e]
  | Tan  e -> print_exps "tan"  [e]
  | Asin e -> print_exps "arcsin" [e]
  | Acos e -> print_exps "arccos" [e]
  | Atan e -> print_exps "arctan" [e]
  | Atan2 (e1, e2) -> print_exps "arctan2" [e1; e2]
  | Matan e -> print_exps "marctan" [e]
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
