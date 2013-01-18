open Intv

type t = Var of string
         | Num of float
         | Add of t * t
         | Sub of t * t
         | Mul of t * t
         | Div of t * t
         | Pow of t * int
         | Sqrt of t
         | Log of t
         | Exp of t
         | Sin of t
         | Cos of t
         | Tan of t
         | Asin of t
         | Acos of t
         | Atan of t
         | Sinh of t
         | Cosh of t
         | Tanh of t

let rec apply (e : Env.t) (f : t) : Intv.t
    = match f with
      Var x -> Env.find x e
    | Num n -> Intv.make n n
    | Add (f1, f2) -> (apply e f1) +$ (apply e f2)
    | Sub (f1, f2) -> (apply e f1) -$ (apply e f2)
    | Mul (f1, f2) -> (apply e f1) *$ (apply e f2)
    | Div (f1, f2) -> (apply e f1) /$ (apply e f2)
    | Pow (f', n) -> pow_I_i (apply e f') n
    | Sqrt f' -> sqrt_I (apply e f')
    | Log f' -> log_I (apply e f')
    | Exp f' -> exp_I (apply e f')
    | Sin f' -> sin_I (apply e f')
    | Cos f' -> cos_I (apply e f')
    | Tan f' -> tan_I (apply e f')
    | Asin f' -> asin_I (apply e f')
    | Acos f' -> acos_I (apply e f')
    | Atan f' -> atan_I (apply e f')
    | Sinh f' -> sinh_I (apply e f')
    | Cosh f' -> cosh_I (apply e f')
    | Tanh f' -> tanh_I (apply e f')

let rec print out f =
  let print_binary out op f1 f2 =
    begin
      BatString.print out "(";
      print out f1;
      BatString.print out " ";
      BatString.print out op;
      BatString.print out " ";
      print out f2;
      BatString.print out ")"
    end
  in
  let print_fun out fun_name arg =
    begin
      BatString.print out fun_name;
      BatString.print out "(";
        print out arg;
      BatString.print out ")"
    end
  in
  match f with
  | Var x ->
    BatString.print out x
  | Num n ->
    BatFloat.print out n
  | Add (f1, f2) ->
    print_binary out "+" f1 f2
  | Sub (f1, f2) ->
    print_binary out "-" f1 f2
  | Mul (f1, f2) ->
    print_binary out "*" f1 f2
  | Div (f1, f2) ->
    print_binary out "/" f1 f2
  | Pow (f', n) ->
    print_binary out "^" f' (Num (float_of_int n))
  | Sqrt f' ->
    print_fun out "sqrt" f'
  | Log f' ->
    print_fun out "log" f'
  | Exp f' ->
    print_fun out "exp" f'
  | Sin f' ->
    print_fun out "sin" f'
  | Cos f' ->
    print_fun out "cos" f'
  | Tan f' ->
    print_fun out "tan" f'
  | Asin f' ->
    print_fun out "asin" f'
  | Acos f' ->
    print_fun out "acos" f'
  | Atan f' ->
    print_fun out "atan" f'
  | Sinh f' ->
    print_fun out "sinh" f'
  | Cosh f' ->
    print_fun out "cosh" f'
  | Tanh f' ->
    print_fun out "tanh" f'
