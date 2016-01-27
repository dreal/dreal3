open Batteries

type value = Value.t
type var = string
type t = var * value * value (* name x interval x precision *)
let print out (var, value, prec) =
  begin
    Printf.fprintf out "%s %s"
                   (IO.to_string Value.print value)
                   var;
    match prec with
      Basic.Num p -> if p > 0.0 then
                 Printf.fprintf out "(prec = %g)" p
      | _ -> raise (Failure ("precision part of vardecl for " ^ var ^ " is not a number"))
  end
