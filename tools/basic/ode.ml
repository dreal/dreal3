open Batteries

type t = string * Basic.exp

let subst (f: string -> string) : (t -> t) =
  function (var, exp) -> (f var, Basic.subst_exp f exp)

let collect_vars (v, e) =
  let vars_rhs = Basic.collect_vars_in_exp e
  in
  (v, vars_rhs)

let print out (v, e) =
  begin
    String.print out "d/dt[";
    String.print out v;
    String.print out "] = ";
    Basic.print_exp out e;
  end
