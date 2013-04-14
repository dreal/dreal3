(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type t = Num of float | Intv of float * float

let print_intv out (n, m) =
  begin
    BatString.print out "[";
    BatPrintf.fprintf out "%f" n;
    BatString.print out ", ";
    BatPrintf.fprintf out "%f" m;
    BatString.print out "]";
  end

let print out v =
  match v with
    Num n -> print_intv out (n, n)
  | Intv (n, m) -> print_intv out (n, m)
