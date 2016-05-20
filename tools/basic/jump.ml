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

let can_synchronize l1 ll1 l2 ll2 =
	    
  let lhs = Set.intersect (Set.of_list l1) (Set.of_list ll2) in
  (*    (List.filter (fun x -> List.mem x ll2) l1) in*)
  let rhs = Set.intersect (Set.of_list l2) (Set.of_list ll1) in
  (* (List.filter (fun x -> List.mem x ll1) l2) in *)
  Set.cardinal (Set.diff (Set.union lhs rhs) (Set.intersect lhs rhs)) = 0
  
let compose_sync j1 ll1 j2 ll2 =
  match can_synchronize j1.label ll1 j2.label ll2 with
      | true -> 
	 let g = Basic.And [j1.guard; j2.guard] in
	 let p = min j1.precision j2.precision in
	 let t = Id.compose j1.target j2.target in
	 let c = Basic.And [j1.change; j2.change] in
	 let l = List.sort_uniq String.compare (List.concat [j1.label; j2.label]) in
	 Some (makep (g, p, t, c, l))
      | false -> None

let compose_async1 j m_id =
   let g = j.guard in
   let p = j.precision in
   let t = Id.compose j.target m_id in
   let c = j.change in
   let l = j.label in
  makep (g, p, t, c, l)

let compose_async2 m_id j =
   let g = j.guard in
   let p = j.precision in
   let t = Id.compose m_id j.target in
   let c = j.change in
   let l = j.label in
   makep (g, p, t, c, l)
