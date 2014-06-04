open Batteries

type formula = Basic.formula
type id = Id.t
type t = {guard  : formula;
	  precision : float;
          target: Id.t;
          change : formula}

let make (g, t, c) = {guard = g; precision = 0.0; target = t; change = c}
let makep (g, p, t, c) = {guard = g; precision = p; target = t; change = c}

let guard      {guard = g; precision = p; target = t; change = c} = g
let precision  {guard = g; precision = p; target = t; change = c} = p
let target     {guard = g; precision = p; target = t; change = c} = t
let change     {guard = g; precision = p; target = t; change = c} = c

let print out {guard  = g;
	       precision = p;
               target = t;
               change = c}
  =
  Printf.fprintf out
                 "(%s, %s, %s, %s)"
                 (IO.to_string Basic.print_formula g)
		 (Printf.sprintf "%.5f" p)
                 (IO.to_string Id.print t)
                 (IO.to_string Basic.print_formula c)
