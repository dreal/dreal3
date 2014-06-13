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

module SearchNode = struct
  type t  = { cost : float; 
	      mode : id}
  let make (c, m) = { cost = c;  mode = m }
  let cost { cost = c;  mode = m } = c
  let mode { cost = c;  mode = m } = m

  let compare (a : t) (b : t) : int =
    if cost a > cost b then
      -1
    else if cost a < cost b then
      1
    else
      0
					       
end

module Heuristic = struct

      



let get_new_adjacent (min_mode : SearchNode.t) (closed : SearchNode.t BatSet.t) fwd h : id BatSet.t =
  match fwd with
    true ->
    let adjacent = BatSet.of_enum (Map.keys (Mode.jumpmap (Map.find (SearchNode.mode min_mode) h.modemap))) in
    let close = (BatSet.map (fun x -> SearchNode.mode x) closed) in
    BatSet.diff adjacent close
  | false ->
     let modes = Map.bindings h.modemap in
     let jumps = List.map (fun (k, m) -> (m, List.of_enum (Map.keys (Mode.jumpmap m)))) modes in
     let jumps_to_min_open = List.filter (fun (m, nm) -> (List.mem (SearchNode.mode min_mode) nm)) jumps in
     let adjacent = BatSet.of_list (List.map (fun (m, nm) -> Mode.mode_id m) jumps_to_min_open) in
     BatSet.diff adjacent (BatSet.map (fun x -> SearchNode.mode x) closed)


  let get_costs (openq : SearchNode.t BatHeap.t) (closed : SearchNode.t BatSet.t) 
		(costs : Costmap.t) (h : Hybrid.t) (fwd : bool) 
      : Costmap.t =
    (*
    let () = print_endline "Open list:" in
     let () = List.iter (printf "%d ") openl in
     let () = print_endline "" in
     *)
    (*
    let cost_compare (a : id) (b : id) : int = 
      let a_cost = Map.find a costs in
      let b_cost = Map.find b costs in
      (int_of_float a_cost) - (int_of_float b_cost)
    in
    
    let sorted = List.sort cost_compare openl in 
     *)
    let closedr = Ref.ref closed in
    let openqr = Ref.ref openq in
    let costsr = Ref.ref costs in
    begin
      closedr := BatSet.union closed (BatSet.of_list (BatHeap.to_list (Ref.get openqr)));
      while (BatHeap.size (Ref.get openqr) > 0) do
	let min_mode = BatHeap.find_min (Ref.get openqr) in
	let adjacent = get_new_adjacent min_mode (Ref.get closedr) fwd h in
	let min_open_cost = SearchNode.cost min_mode in	  
	let adjcosts = BatSet.map (fun x  -> SearchNode.make ((min_open_cost +. 1.0), x)) adjacent in
	(*
        let () = fprintf IO.stdout "Min cost open node: %d \n" (SearchNode.mode min_mode) in
	let () = print_endline "Adjacent nodes:" in
	let () = BatSet.iter (printf "%d ") adjacent in
	let () = print_endline "" in
	 *)
	begin
	  openqr :=  BatHeap.del_min (Ref.get openqr);
	  openqr :=  BatSet.fold BatHeap.add adjcosts (Ref.get openqr);
	  costsr :=  BatSet.fold (fun x c -> Map.add (SearchNode.mode x) (SearchNode.cost x) c)  adjcosts (Ref.get costsr);
	  closedr :=  BatSet.union (Ref.get closedr) adjcosts;
	end
      done;
      Ref.get costsr
    end

    
(*	let openq = List.append openp open_adjacent in
	let costsp = update_costs min_mode openq closedp costs h in
 *)
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
     
    let openempty = BatHeap.empty   in
    let openq = BatHeap.insert openempty (SearchNode.make (0.0, init_mode_id))  in
    let closed = BatSet.empty in
    let init_costs = (get_costs openq closed initcosts h) true in
   (*
    let () = print_endline "init Costs:" in
    let () = Costmap.print IO.stdout init_costs in
    let () = print_endline "" in 
    *)
    init_costs 


  (** Generate H1 heuristic backwards from goals *)
  let heuristicgen_back (h : Hybrid.t) (k : int) : Costmap.t =
    let init_mode_id = h.init_id in
    let goal_mode_ids = List.map (fun (m, _) ->  m ) h.goals in
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
    let openempty = BatHeap.empty   in
    let openq = List.fold_right (fun e h -> BatHeap.insert h (SearchNode.make (0.0, e)) ) goal_mode_ids openempty  in
    let closed = BatSet.empty in
    let final_costs = (get_costs openq closed initcosts h) true in
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
