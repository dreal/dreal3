(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type t =
    Var  of string
  | Const of float
  | Add   of t * t
  | Sub   of t * t
  | Mul   of t * t
  | Div   of t * t
  | Pow   of t * int
  | Sqrt  of t
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

let rec print out =
  let print_binary op e1 e2 =
    begin
      BatString.print out "(";
      print out e1;
      BatString.print out (" "^op^" ");
      print out e2;
      BatString.print out ")";
    end in
  let print_unary op e =
    begin
      BatString.print out op;
      BatString.print out "(";
      print out e;
      BatString.print out ")";
    end
  in
  function Var x -> BatString.print out x
    | Const n -> BatFloat.print out n
    | Add (e1, e2) -> print_binary "+" e1 e2
    | Sub (e1, e2) -> print_binary "-" e1 e2
    | Mul (e1, e2) -> print_binary "*" e1 e2
    | Div (e1, e2) -> print_binary "/" e1 e2
    | Pow ( e,  n) ->
      begin
        BatString.print out "(";
        print out e;
        BatString.print out (" ^ ");
        BatInt.print out n;
        BatString.print out ")";
      end
    | Sqrt e -> print_unary "sqrt" e
    | Log  e -> print_unary "log"  e
    | Exp  e -> print_unary "exp"  e
    | Sin  e -> print_unary "sin"  e
    | Cos  e -> print_unary "cos"  e
    | Tan  e -> print_unary "tan"  e
    | Asin e -> print_unary "asin" e
    | Acos e -> print_unary "acos" e
    | Atan e -> print_unary "atan" e
    | Sinh e -> print_unary "sinh" e
    | Cosh e -> print_unary "cosh" e
    | Tanh e -> print_unary "tanh" e
