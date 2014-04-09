open Batteries
open Intv
exception FuncException of string
type t = Basic.exp
type trend = Inc | Dec | Const | Unknown (* for monotone *)

let print out = Basic.print_exp out

let apply_depth_limit = 0

let rec real_eval (e : (string, float) Map.t) (f : t) : float
    = match f with
      Basic.Var x -> Map.find x e
    | Basic.Num n -> n
    | Basic.Neg f' -> -. (real_eval e f')
    | Basic.Add fl ->
      List.fold_left (+.) 0.0 (List.map (real_eval e) fl)
    | Basic.Sub (f1::rest) ->
      (real_eval e f1) -. (real_eval e (Basic.Add rest))
    | Basic.Sub [] -> raise (FuncException "Subtraction without Arguments!")
    | Basic.Mul fl ->
      List.fold_left ( *. ) 1.0 (List.map (real_eval e) fl)
    | Basic.Div (f1, f2) -> (real_eval e f1) /. (real_eval e f2)
    | Basic.Ite _ -> raise (FuncException "ITE is not supported!")
    | Basic.Pow (f', Basic.Num n) -> (real_eval e f') ** n
    | Basic.Pow (f1, f2) -> (real_eval e f1) ** (real_eval e f2)
    | Basic.Sqrt f' -> sqrt (real_eval e f')
    | Basic.Safesqrt f' ->
      let v = (real_eval e f') in
      if v <= 0.0 then 0.0
      else sqrt v
    | Basic.Abs f' -> abs_float (real_eval e f')
    | Basic.Log f' -> log (real_eval e f')
    | Basic.Exp f' -> exp (real_eval e f')
    | Basic.Sin f' -> sin (real_eval e f')
    | Basic.Cos f' -> cos (real_eval e f')
    | Basic.Tan f' -> tan (real_eval e f')
    | Basic.Asin f' -> asin (real_eval e f')
    | Basic.Acos f' -> acos (real_eval e f')
    | Basic.Atan f' -> atan (real_eval e f')
    | Basic.Atan2 (f1, f2) -> atan2 (real_eval e f1) (real_eval e f2)
    | Basic.Matan f' ->
      let v = real_eval e f' in
      if v = 0.0 then 1.0
      else if v > 0.0 then
        let sqrt_v = sqrt v in
        (atan sqrt_v) /. (sqrt_v)
      else
        let sqrt_minus_v = sqrt (~-. v) in
        log ((1.0 +. sqrt_minus_v) /. (1.0 -. sqrt_minus_v)) /. (2.0 *. sqrt_minus_v)
    | Basic.Sinh f' -> sinh (real_eval e f')
    | Basic.Cosh f' -> cosh (real_eval e f')
    | Basic.Tanh f' -> tanh (real_eval e f')

let rec apply (e : Env.t) (f : t) (d : int) : Intv.t =
  (* Printf.printf "Apply %s %d\n" (IO.to_string Basic.print_exp f) d; *)
  let heuristics =
    match d > apply_depth_limit with
      true -> [intv_eval]
    | false -> [intv_eval; taylor; monotone;]
  in
  let results = List.map (fun h -> h e f d) heuristics in
  List.reduce Intv.meet results

and intv_eval (e : Env.t) (f : t) (d : int) : Intv.t
    =
    (* Printf.printf "intv_eval %s %d\n" (IO.to_string Basic.print_exp f) d; *)
    match f with
      Basic.Var x -> Env.find x e
    | Basic.Num n -> Intv.make n n
    | Basic.Neg f' -> ~-$ (apply e f' d)
    | Basic.Add fl ->
      List.fold_left (+$) Interval.zero_I (List.map (fun f -> apply e f d) fl)
    | Basic.Sub (f1::rest) ->
      (apply e f1 d) -$ (apply e (Basic.Add rest) d)
    | Basic.Sub [] -> raise (FuncException "Subtraction without Arguments!")
    | Basic.Mul fl ->
      List.fold_left ( *$ ) Interval.one_I (List.map (fun f -> apply e f d) fl)
    | Basic.Div (f1, f2) -> (apply e f1 d) /$ (apply e f2 d)
    | Basic.Ite _ -> raise (FuncException "ITE is not supported!")
    | Basic.Pow (f', Basic.Num n) -> (apply e f' d) **$. n
    | Basic.Pow (f1, f2) -> (apply e f1 d) **$ (apply e f2 d)
    | Basic.Sqrt f' -> sqrt_I (apply e f' d)
    | Basic.Safesqrt f' ->
      let intv = apply e f' d in
      let intv' = Intv.meet intv {low=0.0; high=infinity} in
      sqrt_I intv'
    | Basic.Abs f' -> abs_I (apply e f' d)
    | Basic.Log f' -> log_I (apply e f' d)
    | Basic.Exp f' -> exp_I (apply e f' d)
    | Basic.Sin f' -> sin_I (apply e f' d)
    | Basic.Cos f' -> cos_I (apply e f' d)
    | Basic.Tan f' -> tan_I (apply e f' d)
    | Basic.Asin f' -> asin_I (apply e f' d)
    | Basic.Acos f' -> acos_I (apply e f' d)
    | Basic.Atan f' -> atan_I (apply e f' d)
    | Basic.Atan2 (f1, f2) -> atan2_I_I (apply e f1 d) (apply e f2 d)
    | Basic.Matan f' ->
      let {low=l; high=h} = (apply e f' d) in
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

    | Basic.Sinh f' -> sinh_I (apply e f' d)
    | Basic.Cosh f' -> cosh_I (apply e f' d)
    | Basic.Tanh f' -> tanh_I (apply e f' d)

and taylor (e : Env.t) (f : t) (d : int) : Intv.t =
  (* Printf.printf "taylor %s %d\n" (IO.to_string Basic.print_exp f) d; *)
  try
    let keys : Env.key list = List.of_enum (Env.keys e) in
    let derivs : Basic.exp list = List.map (fun key -> Basic.deriv f key) keys in
    let applied : Intv.t list =
      List.map
        (fun deriv -> match deriv with
        | Basic.Num _ -> intv_eval e deriv apply_depth_limit
        | _ -> apply e deriv (d+1))
        derivs in
    let widths : float list=
      List.map
        (fun key -> let intv = Env.find key e in Intv.width intv)
        keys
    in
    let terms : Intv.t list = List.map2 ( *$. ) applied widths in
    let vec_a : (string, float) Map.t = Env.left_bound e in
    let f_of_vec_a : float = real_eval vec_a f in
    List.fold_left (+$) (Intv.make f_of_vec_a f_of_vec_a) terms
  with Basic.DerivativeNotFound -> Intv.top

and monotone (e : Env.t) (f : t) (d : int) : Intv.t =
  (* Printf.printf "monotone %s %d\n" (IO.to_string Basic.print_exp f) d; *)
  let get_sign {low=l; high=h} =
    match (h <= 0.0, l >= 0.0) with
    | (true, true) -> Const
    | (true, false) -> Dec
    | (false, true) -> Inc
    | (false, false) -> Unknown
  in
  try
    let keys : Env.key list = List.of_enum (Env.keys e) in
    let derivs : Basic.exp list = List.map (fun key -> Basic.deriv f key) keys in
    let applied : Intv.t list = List.map
        (fun deriv -> match deriv with
        | Basic.Num _ -> intv_eval e deriv apply_depth_limit
        | _ -> apply e deriv (d+1))
      derivs in
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
    let left_result = apply left_env f (d + 1) in
    let right_result = apply right_env f (d + 1) in
    let result = Intv.join left_result right_result in
    result
  with Basic.DerivativeNotFound -> Intv.top
