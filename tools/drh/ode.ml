open Batteries

type t = string * Basic.exp

let subst (f: string -> string) : (t -> t) =
  function (var, exp) -> (f var, Basic.subst_exp f exp)

let print out (v, e) =
  begin
    String.print out "d/dt[";
    String.print out v;
    String.print out "] = ";
    Basic.print_exp out e;
  end
