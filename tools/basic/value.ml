open Batteries

type t = Num of float | Intv of float * float
let print_intv out (n, m) =
  Printf.fprintf out "[%f, %f]" n m

let print out v =
  match v with
    Num n -> print_intv out (n, n)
  | Intv (n, m) -> print_intv out (n, m)
