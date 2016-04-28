open Batteries

type t = Num of float | Intv of float * float
let print_intv out (n, m) =
  Printf.fprintf out "[%f, %f]" n m

let print out v =
  match v with
    Num n -> print_intv out (n, n)
  | Intv (n, m) -> print_intv out (n, m)

let intersect (v1 : t) (v2: t)  =
    match v1, v2 with
    | Num n1, Num n2 ->
       begin
	 match n1 == n2 with
	 | true -> Num n1
	 | false -> raise (Arg.Bad "Cannot intersect unequal values.")
       end
    | Num n1, Intv (i2l, i2u) ->
       begin
	 match i2l <= n1 && n1 <= i2u with
	 | true -> Num n1
	 | false -> raise (Arg.Bad "Cannot intersect value and interval.")
       end
    | Intv (i1l, i1u), Num n2  ->
       begin
	 match i1l <= n2 &&  n2 <= i1u with
	 | true -> Num n2
	 | false -> raise (Arg.Bad "Cannot intersect value and interval.")
       end
    | Intv (i1l, i1u), Intv (i2l, i2u) ->
       let lb = max i1l i2l in
       let ub = min i1u i2u in
       begin
	 match lb <= ub with
	 | true -> Intv (lb, ub)
	 | false -> raise (Arg.Bad "Intervals do not intersect.")
       end
	 
