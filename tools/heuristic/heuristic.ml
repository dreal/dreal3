(*
 * Dan Bryce dbryce@sift.net
 *)
open Type
open Type.Hybrid
open Type.Basic
open Type.Mode
open Type.Jump
open Batteries
open IO
open Printf
open Costmap

module Heuristic = struct

      
  let get_min_open (openl : id list) (costs : Costmap.t) : int option =
    match List.length openl > 0 with
      true ->    
      Some (List.hd openl) 
    | false ->
       None
	 
	   

  let update_costs (min_mode : Mode.id) (openl : id list) (closed : id list) (costs : Costmap.t) (h : Hybrid.t) : Costmap.t =
    let min_mode_cost = Map.find min_mode costs in
    let newcosts = Map.mapi (fun  mode_id   -> 
	     let c = Map.find mode_id costs in
	     match (Hybrid.adjacent min_mode mode_id h, List.mem mode_id closed) with
	       (true, false) ->
		 let trans_cost = min_mode_cost +. 1.0 in
		 let new_cost = min c trans_cost in
		 (fun mode_id -> new_cost)
	     | (_, _) ->
		(fun mode_id -> c)
	     )
	    costs
    in
    (*
    let () = print_endline "updated Costs:" in
    let () = Costmap.print IO.stdout newcosts in
    let () = print_endline "" in
     *)
    newcosts

  let update_costs_backward (min_mode : Mode.id) (openl : id list) (closed : id list) (costs : Costmap.t) (h : Hybrid.t) : Costmap.t =
    let min_mode_cost = Map.find min_mode costs in
    let newcosts = Map.mapi (fun  mode_id   -> 
	     let c = Map.find mode_id costs in
	     match (Hybrid.adjacent  mode_id min_mode h, List.mem mode_id closed) with
	       (true, false) ->
		 let trans_cost = min_mode_cost +. 1.0 in
		 let new_cost = min c trans_cost in
		 (fun mode_id -> new_cost)
	     | (_, _) ->
		(fun mode_id -> c)
	     )
	    costs
    in
    (*
    let () = print_endline "updated Costs:" in
    let () = Costmap.print IO.stdout newcosts in
    let () = print_endline "" in
     *)
    newcosts






  let rec get_costs (openl : id list) (closed : id list) (costs : Costmap.t) (h : Hybrid.t) : Costmap.t =
    (*
    let () = print_endline "Open list:" in
     let () = List.iter (printf "%d ") openl in
     let () = print_endline "" in
     *)
    let cost_compare (a : id) (b : id) : int = 
      let a_cost = Map.find a costs in
      let b_cost = Map.find b costs in
      (int_of_float a_cost) - (int_of_float b_cost)
    in
    let sorted = List.sort cost_compare openl in
    let min_open = get_min_open sorted costs in
    match min_open with
      Some min_mode -> 
      (*
      let () = fprintf IO.stdout "Min cost open node: %d \n" min_mode in
       *)
      let closedp = List.append closed [ min_mode ] in
      let openp = List.tl sorted in
      let adjacent = List.of_enum (Map.keys (Mode.jumpmap (Map.find min_mode h.modemap))) in
      let open_adjacent = List.filter (fun x -> not (List.mem x closedp) && not (List.mem x openp)) adjacent in
      let openq = List.append openp open_adjacent in
      let costsp = update_costs min_mode openp closedp costs h in
      (*
      let () = print_endline "Adjacent nodes:" in
      let () = List.iter (printf "%d ") adjacent in
      let () = print_endline "" in
      let () = print_endline "New open list:" in
      let () = List.iter (printf "%d ") openq in
      let () = print_endline "" in
      let () = print_endline "Closed List:" in
      let () = List.iter (printf "%d ") closedp in
      let () = print_endline "" in
      let () = print_endline "Costs:" in
      let () = Costmap.print IO.stdout costsp in
       *)
      get_costs openq closedp costsp h
    | None -> costs

  let rec get_costs_backward (openl : id list) (closed : id list) (costs : Costmap.t) (h : Hybrid.t) : Costmap.t =
    (*
    let () = print_endline "Open list:" in
     let () = List.iter (printf "%d ") openl in
     let () = print_endline "" in
     *)
    let cost_compare (a : id) (b : id) : int = 
      let a_cost = Map.find a costs in
      let b_cost = Map.find b costs in
      (int_of_float a_cost) - (int_of_float b_cost)
    in
    let sorted = List.sort cost_compare openl in
(*
    let () = print_endline "Sorted nodes:" in
    let () = List.iter (printf "%d ") sorted in
    let () = print_endline "" in
 *)
    let min_open = get_min_open sorted costs in
    match min_open with
      Some min_mode -> 
      (*
      let () = fprintf IO.stdout "Min cost open node: %d \n" min_mode in
       *)
      let closedp = List.append closed [ min_mode ] in
      let openp = List.tl sorted in
      let modes = Map.bindings h.modemap in
      let jumps = List.map (fun (k, m) -> (m, List.of_enum (Map.keys (Mode.jumpmap m)))) modes in
      let jumps_to_min_open = List.filter 
				(fun (m, nm) -> 
				 (List.mem min_mode nm)
				)
				jumps
      in
      let adjacent = List.map (fun (m, nm) -> Mode.mode_id m) jumps_to_min_open in
      let open_adjacent = List.filter (fun x -> not (List.mem x closedp) && not (List.mem x openp)) adjacent in
      let openq = List.append openp open_adjacent in
      let costsp = update_costs_backward min_mode openp closedp costs h in
      
(*
      let () = print_endline "Adjacent nodes:" in
      let () = List.iter (printf "%d ") adjacent in
      let () = print_endline "" in
      let () = print_endline "New open list:" in
      let () = List.iter (printf "%d ") openq in
      let () = print_endline "" in
      let () = print_endline "Closed List:" in
      let () = List.iter (printf "%d ") closedp in
      let () = print_endline "" in
      let () = print_endline "Costs:" in
      let () = Costmap.print IO.stdout costsp in
 *)
      get_costs_backward openq closedp costsp h
    | None -> costs

  (** Generate H1 heuristic *)
  let heuristicgen (h : Hybrid.t) (k : int) : Costmap.t =
    let init_mode_id = h.init_id in
    let goal_mode_ids = List.map (fun (m, _) -> m ) h.goals in
    let mycosts = Costmap.of_modemap h.modemap in
    let initcosts = Map.mapi (fun id ->
			     if id = init_mode_id
			     then
			       (fun id -> 0.0)
			     else
			       (fun id -> infinity))
			     mycosts
    in
    (*
    let () = print_endline "init Costs:" in
    let () = Costmap.print IO.stdout initcosts in
    let () = print_endline "" in 
     *)
    let openl = [ init_mode_id ] in
    let closed = [ ] in
    let init_costs = get_costs openl closed initcosts h in
   (*
    let () = print_endline "init Costs:" in
    let () = Costmap.print IO.stdout init_costs in
    let () = print_endline "" in 
    *)
    init_costs 


  (** Generate H1 heuristic backwards from goals *)
  let heuristicgen_back (h : Hybrid.t) (k : int) : Costmap.t =
    let init_mode_id = h.init_id in
    let goal_mode_ids = List.map (fun (m, _) -> m ) h.goals in
    let mycosts = Costmap.of_modemap h.modemap in
    let initcosts = Map.mapi (fun id ->
			     if List.mem id goal_mode_ids
			     then
			       (fun id -> 0.0)
			     else
			       (fun id -> infinity))
			     mycosts
    in
    (*
    let () = print_endline "goal Costs:" in
    let () = Costmap.print IO.stdout initcosts in
    let () = print_endline "" in 
     *)
    let openl = goal_mode_ids in
    let closed = [ ] in
    let final_costs = get_costs_backward openl closed initcosts h in
   (*
    let () = print_endline "goal Costs:" in
    let () = Costmap.print IO.stdout final_costs in
    let () = print_endline "" in 
    *)
    final_costs
	      
  (* Get mode adjacency list *)
  let get_mode_adjacency (h : Hybrid.t) : id list list =
    let mode_ids = List.of_enum (Map.keys h.modemap) in
    List.map (fun x -> 
	      let mode = Map.find x h.modemap in
	      List.of_enum (Map.keys mode.jumpmap)) mode_ids


  let writeHeuristic heuristic hm k hout =
	let () = Printf.fprintf hout "[" in
	let () = Printf.fprintf hout "[%d, "  hm.init_id in
	let () = List.print ~first:"[" ~last:"]" ~sep:","
			    (fun out g -> Int.print hout g)
			    hout
			    (Hybrid.goal_ids hm) in
	let () = Printf.fprintf hout ", %d" k in
	let () = Printf.fprintf hout "], " in
	let () = Costmap.print hout heuristic in
	let () = Printf.fprintf hout "," in
	let mode_adjacency = get_mode_adjacency hm in
	let () = List.print ~first:"[" ~last:"]" ~sep:","
			    (fun hout path ->
			     List.print ~first:"[" ~last:"]" ~sep:"," Int.print hout path)
			    hout
			    mode_adjacency in
	Printf.fprintf hout "]"
				    

end
