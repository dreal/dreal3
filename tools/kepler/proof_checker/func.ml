open Intv
exception FuncException of string
type t = Basic.exp
let rec apply (e : Env.t) (f : t) : Intv.t
    = match f with
      Basic.Var x -> Env.find x e
    | Basic.Num n -> Intv.make n n
    | Basic.Neg f' -> ~-$ (apply e f')
    | Basic.Add fl ->
      List.fold_left (+$) Interval.zero_I (List.map (apply e) fl)
    | Basic.Sub (f1::rest) ->
      (apply e f1) -$ (apply e (Basic.Add rest))
    | Basic.Mul fl ->
      List.fold_left ( *$ ) Interval.one_I (List.map (apply e) fl)
    | Basic.Div (f1, f2) -> (apply e f1) /$ (apply e f2)
    | Basic.Ite _ -> raise (FuncException "ITE is not supported!")
    | Basic.Pow (f', Basic.Num n) -> (apply e f') **$. n
(*    | Basic.Pow (f1, f2) -> (apply e f1) **$ (apply e f2) *)
    | Basic.Sqrt f' -> sqrt_I (apply e f')
    | Basic.Abs f' -> abs_I (apply e f')
    | Basic.Log f' -> log_I (apply e f')
    | Basic.Exp f' -> exp_I (apply e f')
    | Basic.Sin f' -> sin_I (apply e f')
    | Basic.Cos f' -> cos_I (apply e f')
    | Basic.Tan f' -> tan_I (apply e f')
    | Basic.Asin f' -> asin_I (apply e f')
    | Basic.Acos f' -> acos_I (apply e f')
    | Basic.Atan f' -> atan_I (apply e f')
    | Basic.Sinh f' -> sinh_I (apply e f')
    | Basic.Cosh f' -> cosh_I (apply e f')
    | Basic.Tanh f' -> tanh_I (apply e f')
    | _ -> raise Not_found
let print out = Basic.print_exp out
