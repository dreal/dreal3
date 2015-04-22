open Batteries

type formula = Basic.formula
type labels = string list
type id = Id.t
type t = {guard  : formula;
	  precision : float;
          target: Id.t;
          change : formula;
          label: labels}

let make (g, t, c, l) = {guard = g; precision = 0.0; target = t; change = c; label = l}
let makep (g, p, t, c, l) = {guard = g; precision = p; target = t; change = c; label = l}

let guard      {guard = g; precision = p; target = t; change = c; label = l} = g
let precision  {guard = g; precision = p; target = t; change = c; label = l} = p
let target     {guard = g; precision = p; target = t; change = c; label = l} = t
let change     {guard = g; precision = p; target = t; change = c; label = l} = c
let label      {guard = g; precision = p; target = t; change = c; label = l} = l

let print out {guard  = g;
	       precision = p;
               target = t;
               change = c;
               label = l}
  =
  let print_jumps_str jlist = 
    match jlist with
	  | [] -> "<no labels>"
	  | _ -> List.fold_left (fun str x -> x^str) "" jlist
  in
  Printf.fprintf out
                 "(%s, %s, %s, %s, %s)"
                 (IO.to_string Basic.print_formula g)
		 (Printf.sprintf "%.5f" p)
                 (IO.to_string Id.print t)
                 (IO.to_string Basic.print_formula c)
                 (print_jumps_str l)
