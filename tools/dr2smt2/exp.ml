(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type t =
| Var   of string
| Const of float
| Neg   of t
| Add   of t * t
| Sub   of t * t
| Mul   of t * t
| Div   of t * t
| Pow   of t * t
| Ite   of Formula.t * t * t
| Sqrt  of t
| Abs   of t
| Log   of t
| Exp   of t
| Sin   of t
| Cos   of t
| Tan   of t
| Asin  of t
| Acos  of t
| Atan  of t
| Sinh  of t
| Cosh  of t
| Tanh  of t

let rec subst (f : string -> string) (e : t)
    : t
    = match e with
    | Var s -> Var (f s)
    | Const n -> e
    | Neg e' -> Neg (subst f e')
    | Add (e1, e2) -> Add (subst f e1, subst f e2)
    | Sub (e1, e2) -> Sub (subst f e1, subst f e2)
    | Mul (e1, e2) -> Mul (subst f e1, subst f e2)
    | Div (e1, e2) -> Div (subst f e1, subst f e2)
    | Pow (e1, e2) -> Pow (subst f e1, subst f e2)
    | Ite (e1, e2, e3) -> Ite (subst f e1, subst f e2, subst f e3)
    | Sqrt e -> Sqrt (subst f e)
    | Abs  e -> Abs (subst f e)
    | Log  e -> Log (subst f e)
    | Exp  e -> Exp (subst f e)
    | Sin  e -> Sin (subst f e)
    | Cos  e -> Cos (subst f e)
    | Tan  e -> Tan (subst f e)
    | Asin e -> Asin (subst f e)
    | Acos e -> Acos (subst f e)
    | Atan e -> Atan (subst f e)
    | Sinh e -> Sinh (subst f e)
    | Cosh e -> Cosh (subst f e)
    | Tanh e -> Tanh (subst f e)

let rec print out =
  let print_exps op exps =
    begin
      BatList.print
        (~first:("("^op^" "))
        (~sep:" ")
        (~last:")")
        print
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
    (* If n ends with ".", add "0" to make ".0" *)
    let s = BatFloat.to_string n in
    let s' = match BatString.ends_with s "." with
      | true -> s ^ "0"
      | false -> s
    in
    BatString.print out s'
  | Neg e' -> print_exps "-" [Const 0.0; e']
  | Add (e1, e2) -> print_exps "+" [e1; e2]
  | Sub (e1, e2) -> print_exps "-" [e1; e2]
  | Mul (e1, e2) -> print_exps "*" [e1; e2]
  | Div (e1, e2) -> print_exps "/" [e1; e2]
  | Pow (e1, e2) -> print_exps "^" [e1; e2]
  | Ite (f, e1, e2) -> print_exps "ITE" [e1; e2]
  | Sqrt e -> (* print_exps "sqrt" [e] *)
    (* MATH HACK *)
    print out (Pow(e, Const 0.5))
  | Abs  e -> (* print_exps "abs"  [e] *)
    (* MATH HACK *)
    print out (Sqrt (Pow(e, Const 2.0)))
  | Log  e -> print_exps "log"  [e]
  | Exp  e -> print_exps "exp"  [e]
  | Sin  e -> print_exps "sin"  [e]
  | Cos  e -> print_exps "cos"  [e]
  | Tan  e -> print_exps "tan"  [e]
  | Asin e -> print_exps "asin" [e]
  | Acos e -> print_exps "acos" [e]
  | Atan e -> print_exps "atan" [e]
  | Sinh e -> print_exps "sinh" [e]
  | Cosh e -> print_exps "cosh" [e]
  | Tanh e -> print_exps "tanh" [e]
