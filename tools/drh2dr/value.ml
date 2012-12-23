(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type t = Num of float | Intv of float * float

let print out v =
  match v with
    Num n -> BatFloat.print out n
  | Intv (n, m) ->
    begin
      BatString.print out "[";
      BatFloat.print out n;
      BatString.print out ", ";
      BatFloat.print out m;
      BatString.print out "]";
    end

