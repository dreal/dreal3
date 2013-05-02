open Batteries
open Intv
exception FuncException of string
type t = Basic.exp

let rec eval (e : (string, float) Map.t) (f : t) : float
    = match f with
      Basic.Var x -> Map.find x e
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

let rec intv_eval (e : Env.t) (f : t) : Intv.t
    = match f with
      Basic.Var x -> Env.find x e
    | Basic.Num n -> Intv.make n n
    | Basic.Neg f' -> ~-$ (intv_eval e f')
    | Basic.Add fl ->
      List.fold_left (+$) Interval.zero_I (List.map (intv_eval e) fl)
    | Basic.Sub (f1::rest) ->
      (intv_eval e f1) -$ (intv_eval e (Basic.Add rest))
    | Basic.Sub [] -> raise (FuncException "Subtraction without Arguments!")
    | Basic.Mul fl ->
      List.fold_left ( *$ ) Interval.one_I (List.map (intv_eval e) fl)
    | Basic.Div (f1, f2) -> (intv_eval e f1) /$ (intv_eval e f2)
    | Basic.Ite _ -> raise (FuncException "ITE is not supported!")
    | Basic.Pow (f', Basic.Num n) -> (intv_eval e f') **$. n
    | Basic.Pow (f1, f2) -> (intv_eval e f1) **$ (intv_eval e f2)
    | Basic.Sqrt f' -> sqrt_I (intv_eval e f')
    | Basic.Safesqrt f' ->
      let intv = intv_eval e f' in
      let intv' = Intv.meet intv {low=0.0; high=infinity} in
      sqrt_I intv'
    | Basic.Abs f' -> abs_I (intv_eval e f')
    | Basic.Log f' -> log_I (intv_eval e f')
    | Basic.Exp f' -> exp_I (intv_eval e f')
    | Basic.Sin f' -> sin_I (intv_eval e f')
    | Basic.Cos f' -> cos_I (intv_eval e f')
    | Basic.Tan f' -> tan_I (intv_eval e f')
    | Basic.Asin f' -> asin_I (intv_eval e f')
    | Basic.Acos f' -> acos_I (intv_eval e f')
    | Basic.Atan f' -> atan_I (intv_eval e f')
    | Basic.Atan2 (f1, f2) -> atan2_I_I (intv_eval e f1) (intv_eval e f2)
    | Basic.Matan f' ->
      let {low=l; high=h} = (intv_eval e f') in
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
      List.reduce Intv.meet (List.flatten [pos_part;neg_part;zero_part])

    | Basic.Sinh f' -> sinh_I (intv_eval e f')
    | Basic.Cosh f' -> cosh_I (intv_eval e f')
    | Basic.Tanh f' -> tanh_I (intv_eval e f')

let print out = Basic.print_exp out

let rec taylor (e : Env.t) (f : t) : Intv.t =
  try
    let keys : Env.key list = List.of_enum (Env.keys e) in
    let derivs : Basic.exp list = List.map (fun key -> Basic.deriv f key) keys in
    let applied : Intv.t list = List.map (fun deriv -> intv_eval e deriv) derivs in
    let widths : float list=
      List.map
        (fun key -> let intv = Env.find key e in Intv.width intv)
        keys
    in
    let terms : Intv.t list = List.map2 ( *$. ) applied widths in
    let vec_a : (string, float) Map.t = Env.left_bound e in
    let f_of_vec_a : float = eval vec_a f in
    let out = IO.stdout in
    begin
      String.print out "f = ";
      print out f;
      String.println out "";

      String.print out "derivs = ";
      List.print print out derivs;
      String.println out "";

      String.print out "f(a) = ";
      Float.print out f_of_vec_a;
      String.println out "";
      List.fold_left (+$) (Intv.make f_of_vec_a f_of_vec_a) terms
    end
  with Basic.DerivativeNotFound -> Intv.top

type trend = Inc | Dec | Const | Unknown
let get_sign {low=l; high=h} =
  match (h <= 0.0, l >= 0.0) with
  | (true, true) -> Const
  | (true, false) -> Dec
  | (false, true) -> Inc
  | (false, false) -> Unknown

let rec monotone (e : Env.t) (f : t) : Intv.t =
  try
    let keys : Env.key list = List.of_enum (Env.keys e) in
    let derivs : Basic.exp list = List.map (fun key -> Basic.deriv f key) keys in
    let applied : Intv.t list = List.map (fun deriv -> intv_eval e deriv) derivs in
    let signs : trend list = List.map get_sign applied in
    let (left, right) =
      List.split
        (List.map2
           (fun key sign ->
             let {low=l; high=h} as intv = Env.find key e in
             match sign with
               Inc -> ({low=l; high=l}, {low=h; high=h})
             | Dec -> ({low=h; high=h}, {low=l; high=l})
             | Const -> ({low=l; high=l}, {low=l; high=l})
             | Unknown -> (intv, intv)
           )
           keys signs) in
    let left_env = Env.from_list (List.combine keys left) in
    let right_env = Env.from_list (List.combine keys right) in
    let left_result = intv_eval left_env f in
    let right_result = intv_eval right_env f in
    let result = Intv.join left_result right_result in
    result
  with Basic.DerivativeNotFound -> Intv.top
