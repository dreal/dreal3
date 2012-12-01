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

let rec to_string f =
  match f with
      Var x -> x
    | Num n -> string_of_float n
    | Add (f1, f2) -> "(" ^ (to_string f1) ^ " + " ^ (to_string f2) ^ ")"
    | Sub (f1, f2) -> "(" ^ (to_string f1) ^ " - " ^ (to_string f2) ^ ")"
    | Mul (f1, f2) -> "(" ^ (to_string f1) ^ " * " ^ (to_string f2) ^ ")"
    | Div (f1, f2) -> "(" ^ (to_string f1) ^ " / " ^ (to_string f2) ^ ")"
    | Pow (f', n) -> "(" ^ (to_string f') ^ ")^" ^ (string_of_int n)
    | Sqrt f' -> "sqrt(" ^ (to_string f') ^ ")"
    | Log f' -> "log(" ^ (to_string f') ^ ")"
    | Exp f' -> "exp(" ^ (to_string f') ^ ")"
    | Sin f' -> "sin(" ^ (to_string f') ^ ")"
    | Cos f' -> "cos(" ^ (to_string f') ^ ")"
    | Tan f' -> "tan(" ^ (to_string f') ^ ")"
    | Asin f' -> "asin(" ^ (to_string f') ^ ")"
    | Acos f' -> "acos(" ^ (to_string f') ^ ")"
    | Atan f' -> "atan(" ^ (to_string f') ^ ")"
    | Sinh f' -> "sinh(" ^ (to_string f') ^ ")"
    | Cosh f' -> "cosh(" ^ (to_string f') ^ ")"
    | Tanh f' -> "tanh(" ^ (to_string f') ^ ")"
