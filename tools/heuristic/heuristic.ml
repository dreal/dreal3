(*
 * Dan Bryce dbryce@sift.net
 *)
open Type
open Type.Hybrid
open Type.Basic
open Type.Mode
open Type.Jump
open Type.Vardecl
open Batteries
open IO
open Printf
open Costmap
open Relevantvariables

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
  let get_invariant_vars mode =
    match Mode.invs_op mode with
      Some (invs) ->
      List.fold_right BatSet.union (List.map Basic.collect_vars_in_formula invs) BatSet.empty
    | None -> BatSet.empty

  let get_relevant_flow_vars mode vars h =
    (* Get variables from flows that vars depend upon (transitively) *)
    let variables = BatSet.of_enum (Map.keys h.varmap) in
    let old_vars = Ref.ref BatSet.empty in
    let new_vars = Ref.ref vars in
    let vars_depends_upon_v vars v  =
      (* Does var in vars depend upon v? *)
      List.exists
        (fun x ->
         match Ode.collect_vars x with
           (v1, vars1) -> ((BatSet.mem v vars1) && (BatSet.mem v1 vars))
        )
        (Mode.flows mode)
    in
    begin
      while not ((Ref.get new_vars) = (Ref.get old_vars)) do
        begin
          old_vars := Ref.get new_vars;
          (*
          print_endline "old relevant flow vars:";
          BatSet.print ~first:"[" ~last:"]" ~sep:","  String.print IO.stdout (Ref.get new_vars);
          print_endline "";
           *)
          new_vars := BatSet.filter
                        (fun v -> vars_depends_upon_v (Ref.get old_vars) v)
                        variables;
          new_vars := BatSet.union (Ref.get new_vars) (Ref.get old_vars);
          (*
          print_endline "new relevant flow vars:";
          BatSet.print ~first:"[" ~last:"]" ~sep:","  String.print IO.stdout (Ref.get new_vars);
          print_endline "";
           *)
        end
      done;
      Ref.get new_vars;
    end

  let rec relevantgenr_back (h : Hybrid.t) (k :int) (step : int) (heuristic: Costmap.t) (heuristic_back : Costmap.t) (next : Relevantvariables.t) : Relevantvariables.t List.t =
    let variables = BatSet.of_enum (Map.keys h.varmap) in
    let modes = Map.bindings h.modemap in
    let get_prev_modes (mode_id : int) =
     let jumps = List.map (fun (k, m) -> (m, List.of_enum (Map.keys (Mode.jumpmap m)))) modes in
     let jumps_to_mode_id = List.filter (fun (m, nm) -> (List.mem  mode_id nm)) jumps in
     let adjacent = BatSet.of_list (List.map (fun (m, nm) ->  m) jumps_to_mode_id) in
     let init_dist m = int_of_float (Costmap.find (Mode.mode_id m) heuristic) in
     let goal_dist m = int_of_float (Costmap.find (Mode.mode_id m) heuristic_back) in
     BatSet.filter (fun x -> (step >= (init_dist x)) || (step >= (k - (goal_dist x)))) adjacent
    in
    let relevant_modes = List.of_enum (BatSet.enum (List.fold_right
                                                      BatSet.union
                                                      (List.map get_prev_modes (List.of_enum (Map.keys next)))
                                                      BatSet.empty))
    in
    (*
    let () = print_endline "" in
    let () = Printf.fprintf IO.stdout "Relevant modes at: %d "step in
    let () = List.print ~first:"[" ~last:"]" ~sep:","  (fun out m -> Int.print out (Mode.mode_id m)) IO.stdout relevant_modes in
    let () = print_endline "" in
     *)
    let relevant_var = Relevantvariables.of_modelist relevant_modes in
    let  get_relevant_mode_mode_variables (mode : Mode.t) (nm : Mode.t) (jm : Jumpmap.t) =
      (*
      let () = print_endline "" in
      let () = Printf.fprintf IO.stdout "Getting vars relevant to %d -> %d" (Mode.mode_id mode) (Mode.mode_id nm) in
      let () = print_endline "" in
       *)

      let jump = Map.find (Mode.mode_id nm) jm in
(*
      let flows = Mode.flows mode in
 *)
      let is_jump_guard var =
        let guard_vars = Basic.collect_vars_in_formula (Jump.guard jump) in
        BatSet.mem var guard_vars
      in
      (*
   let is_invariant var =
        match Mode.invs_op mode with
          Some (invs) ->
          List.exists (fun x -> BatSet.mem var (Basic.collect_vars_in_formula x)) invs
        | None -> false
      in
      let is_flow_dependent var v =
        (* does the flow for v depend upon var *)
        List.exists (fun x ->
                     match Ode.collect_vars x with
                       (v, vars) -> BatSet.mem var vars
                     | _ -> false
                    )
                    flows
      in
      let is_relevant var = (is_jump_guard var ||
                               is_invariant var ) ||
                              BatSet.exists (fun v -> is_flow_dependent var v )
                                            (Map.find (Mode.mode_id nm) next)
      in
 *)

      let guard_vars = BatSet.filter is_jump_guard variables in
      let invariant_vars = get_invariant_vars mode in
      let depvars = BatSet.union (BatSet.union guard_vars invariant_vars) (Map.find nm.mode_id next) in
      let flow_vars = get_relevant_flow_vars mode depvars h in

      (*
      let () = print_endline "" in
      let () = Printf.fprintf IO.stdout "Relevant Guards:" in
      let () = BatSet.print ~first:"[" ~last:"]" ~sep:","  String.print IO.stdout guard_vars in
      let () = print_endline "" in
     let () = Printf.fprintf IO.stdout "Relevant Flows:" in
      let () = BatSet.print ~first:"[" ~last:"]" ~sep:","  String.print IO.stdout flow_vars in
      let () = print_endline "" in
     let () = Printf.fprintf IO.stdout "Relevant Invariants:" in
      let () = BatSet.print ~first:"[" ~last:"]" ~sep:","  String.print IO.stdout invariant_vars in
      let () = print_endline "" in
       *)

      BatSet.union flow_vars depvars

(*      BatSet.filter is_relevant variables       *)
    in

    let get_relevant_mode_variables (mode : Mode.t) =
      let jm = Mode.jumpmap mode in
      (*
      let () = print_endline "" in
      let () = Printf.fprintf IO.stdout "Getting vars relevant in mode %d at %d" (Mode.mode_id mode) step in
      let () = print_endline "" in
       *)
      BatSet.fold
        BatSet.union
        (BatSet.of_list
           (List.map
              (fun nm ->
               get_relevant_mode_mode_variables mode nm jm
              )
              (List.map (fun x -> Map.find x h.modemap) (List.filter (fun x -> List.mem x (List.of_enum (Map.keys next))) (List.of_enum (Map.keys jm))))
           )
        )
        BatSet.empty

    in
    let relevant_vars = List.fold_right
                          (fun m y -> Map.add (Mode.mode_id m) (get_relevant_mode_variables m) y)
                          relevant_modes
                          relevant_var
    in
    if step > 0 then
      List.append
        (relevantgenr_back h k (step-1) heuristic heuristic_back relevant_vars)
        [ relevant_vars ]
    else
      [ relevant_vars ]




  (** Get Relevant variables *)
  let relevantgen_back (h : Hybrid.t) (k : int) (heuristic: Costmap.t) (heuristic_back : Costmap.t) : Relevantvariables.t List.t =

    let goal_modes = List.map (fun (m, _) ->  (Map.find m h.modemap ) ) h.goals in
    let relevant_goals = Relevantvariables.of_modelist goal_modes in

    let get_goal_variables mode  : string BatSet.t =
      let goal_and_invar = List.fold_right
                             BatSet.union
                             (List.map
                                (fun (m, f) ->
                                 match m = mode.mode_id with
                                   true -> (BatSet.union
                                              (Basic.collect_vars_in_formula f)
                                              (get_invariant_vars (Map.find m h.modemap))
                                           )
                                 | false -> BatSet.empty
                                )
                                h.goals
                             )
                             BatSet.empty
      in
      BatSet.union goal_and_invar (get_relevant_flow_vars  mode goal_and_invar h)
    in
    let relevant_goal_vars = List.fold_right
                               (fun m y -> Map.add m.mode_id (get_goal_variables m) y)
                               goal_modes
                               relevant_goals

    in

  (*
    let () = print_endline "relevant goal vars:" in
    let () = Relevantvariables.print IO.stdout relevant_goal_vars in
    let () = print_endline "" in
   *)
    if k > 0 then
      List.append
        (relevantgenr_back h k (k-1) heuristic heuristic_back relevant_goal_vars)
        [ relevant_goal_vars ]
    else
      [ relevant_goal_vars ]

    (*
    let () = print_endline "relevant goal vars:" in
    let () = Relevantvariables.print IO.stdout relevant_goal_vars in
    let () = print_endline "" in
     *)
(*
    let openempty = BatHeap.empty   in
    let openq = List.fold_right (fun e h -> BatHeap.insert h (SearchNode.make (0.0, e)) ) goal_mode_ids openempty  in
    let closed = BatSet.empty in
    let final_costs = (get_costs openq closed initcosts h) true in
 *)
 (*
    let () = print_endline "goal Costs:" in
    let () = Costmap.print IO.stdout final_costs in
    let () = print_endline "" in
    *)



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
