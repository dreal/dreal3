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


module Costmap = struct
  type id = int
  type cost = float
  type t = (id, cost) Map.t

  let of_modemap (modes : Modemap.t) : t
      =
      let list_of_modes = List.of_enum (Map.keys modes) in
      List.fold_left
      (fun (map : (id, cost) Map.t) (m : id) ->
        Map.add m infinity map
      )
      Map.empty
      list_of_modes

  let print out = 
    let id_print out id = Printf.fprintf out "\"%s\"" (IO.to_string Id.print id) in
    let f_print out f = Printf.fprintf out "\"%f\"" (f) in
    Map.print id_print f_print out
	      
  let find key map =
    try
      Map.find key map
    with e ->
      let out = IO.stderr in
      begin
        String.println out "Modemap Exception!";
        Printf.fprintf out "Key: %s\n" (IO.to_string Id.print key);
        Printf.fprintf out "Map: %s\n" (IO.to_string print map);
        Printexc.print_backtrace IO.stdout;
        raise e
      end
end



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

  let rec get_costs (openl : id list) (closed : id list) (costs : Costmap.t) (h : Hybrid.t) : Costmap.t =
    (*
    let () = print_endline "Open list:" in
     let () = List.iter (printf "%d ") openl in
     let () = print_endline "" in
     *)
    let cost_compare (a : id) (b : id) : int = 
      let a_cost = Map.find a costs in
      let b_cost = Map.find b costs in
      a - b
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
    get_costs openl closed initcosts h
	      
  (* Get mode adjacency list *)
  let get_mode_adjacency (h : Hybrid.t) : id list list =
    let mode_ids = List.of_enum (Map.keys h.modemap) in
    List.map (fun x -> 
	      let mode = Map.find x h.modemap in
	      List.of_enum (Map.keys mode.jumpmap)) mode_ids
				    
end
