open Intv
exception FuncException of string
type t = Basic.exp

let rec eval (e : (string, float) BatMap.t) (f : t) : float
    = match f with
      Basic.Var x -> BatMap.find x e
    | Basic.Num n -> n
    | Basic.Neg f' -> -. (eval e f')
    | Basic.Add fl ->
      List.fold_left (+.) 0.0 (List.map (eval e) fl)
    | Basic.Sub (f1::rest) ->
      (eval e f1) -. (eval e (Basic.Add rest))
    | Basic.Sub [] -> raise (FuncException "Subtraction without Arguments!")
    | Basic.Mul fl ->
      List.fold_left ( *. ) 1.0 (List.map (eval e) fl)
    | Basic.Div (f1, f2) -> (eval e f1) /. (eval e f2)
    | Basic.Ite _ -> raise (FuncException "ITE is not supported!")
    | Basic.Pow (f', Basic.Num n) -> (eval e f') ** n
    | Basic.Pow (f1, f2) -> (eval e f1) ** (eval e f2)
    | Basic.Sqrt f' -> sqrt (eval e f')
    | Basic.Safesqrt f' ->
      let v = (eval e f') in
      if v <= 0.0 then 0.0
      else sqrt v
    | Basic.Abs f' -> abs_float (eval e f')
    | Basic.Log f' -> log (eval e f')
    | Basic.Exp f' -> exp (eval e f')
    | Basic.Sin f' -> sin (eval e f')
    | Basic.Cos f' -> cos (eval e f')
    | Basic.Tan f' -> tan (eval e f')
    | Basic.Asin f' -> asin (eval e f')
    | Basic.Acos f' -> acos (eval e f')
    | Basic.Atan f' -> atan (eval e f')
    | Basic.Atan2 (f1, f2) -> atan2 (eval e f1) (eval e f2)
    | Basic.Matan f' ->
      let v = eval e f' in
      if v = 0.0 then 1.0
      else if v > 0.0 then
        let sqrt_v = sqrt v in
        (atan sqrt_v) /. (sqrt_v)
      else
        let sqrt_minus_v = sqrt (~-. v) in
        log ((1.0 +. sqrt_minus_v) /. (1.0 -. sqrt_minus_v)) /. (2.0 *. sqrt_minus_v)
    | Basic.Sinh f' -> sinh (eval e f')
    | Basic.Cosh f' -> cosh (eval e f')
    | Basic.Tanh f' -> tanh (eval e f')

let rec apply (e : Env.t) (f : t) : Intv.t
    = match f with
      Basic.Var x -> Env.find x e
    | Basic.Num n -> Intv.make n n
    | Basic.Neg f' -> ~-$ (apply e f')
    | Basic.Add fl ->
      List.fold_left (+$) Interval.zero_I (List.map (apply e) fl)
    | Basic.Sub (f1::rest) ->
      (apply e f1) -$ (apply e (Basic.Add rest))
    | Basic.Sub [] -> raise (FuncException "Subtraction without Arguments!")
    | Basic.Mul fl ->
      List.fold_left ( *$ ) Interval.one_I (List.map (apply e) fl)
    | Basic.Div (f1, f2) -> (apply e f1) /$ (apply e f2)
    | Basic.Ite _ -> raise (FuncException "ITE is not supported!")
    | Basic.Pow (f', Basic.Num n) -> (apply e f') **$. n
    | Basic.Pow (f1, f2) -> (apply e f1) **$ (apply e f2)
    | Basic.Sqrt f' -> sqrt_I (apply e f')
    | Basic.Safesqrt f' ->
      let intv = apply e f' in
      let intv' = Intv.meet intv {low=0.0; high=infinity} in
      sqrt_I intv'
    | Basic.Abs f' -> abs_I (apply e f')
    | Basic.Log f' -> log_I (apply e f')
    | Basic.Exp f' -> exp_I (apply e f')
    | Basic.Sin f' -> sin_I (apply e f')
    | Basic.Cos f' -> cos_I (apply e f')
    | Basic.Tan f' -> tan_I (apply e f')
    | Basic.Asin f' -> asin_I (apply e f')
    | Basic.Acos f' -> acos_I (apply e f')
    | Basic.Atan f' -> atan_I (apply e f')
    | Basic.Atan2 (f1, f2) -> atan2_I_I (apply e f1) (apply e f2)
    | Basic.Matan f' ->
      let {low=l; high=h} = (apply e f') in
      let pos_part =
        if h > 0.0 then
          let sliced = {low=min_float; high=h} in
          let sqrt_x = sqrt_I sliced in
          [atan_I(sqrt_x) /$ sqrt_x]
        else
          []
      in
      let neg_part =
        if l < 0.0 then
          let sliced = {low=l; high= ~-. min_float} in
          let sqrt_mx = sqrt_I (~-$ sliced) in
          let one = Interval.one_I in
          let two = {low=2.0; high=2.0} in
          [log_I ((one +$ sqrt_mx) /$ (one -$ sqrt_mx)) /$ (two *$ sqrt_mx)]
        else
          []
      in
      let zero_part =
        if l <= 0.0 && h >= 0.0 then
          [Interval.one_I]
        else
          []
      in
      BatList.reduce Intv.meet (List.flatten [pos_part;neg_part;zero_part])

    | Basic.Sinh f' -> sinh_I (apply e f')
    | Basic.Cosh f' -> cosh_I (apply e f')
    | Basic.Tanh f' -> tanh_I (apply e f')

let print out = Basic.print_exp out

let rec taylor (e : Env.t) (f : t) : Intv.t =
  try
    let keys : Env.key list = BatList.of_enum (Env.keys e) in
    let derivs : Basic.exp list = List.map (fun key -> Basic.deriv f key) keys in
    let applied : Intv.t list = List.map (fun deriv -> apply e deriv) derivs in
    let widths : float list=
      List.map
        (fun key -> let intv = Env.find key e in Intv.width intv)
        keys
    in
    let terms : Intv.t list = BatList.map2 ( *$. ) applied widths in
    let vec_a : (string, float) BatMap.t = Env.left_bound e in
    let f_of_vec_a : float = eval vec_a f in
    let out = BatIO.stdout in
    begin
      BatString.print out "f = ";
      print out f;
      BatString.println out "";

      BatString.print out "derivs = ";
      BatList.print print out derivs;
      BatString.println out "";

      BatString.print out "f(a) = ";
      BatFloat.print out f_of_vec_a;
      BatString.println out "";
      List.fold_left (+$) (Intv.make f_of_vec_a f_of_vec_a) terms
    end
  with Basic.DerivativeNotFound -> Intv.top
