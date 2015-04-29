(*
 * Soonho Kong soonhok@cs.cmu.edu
 * Wei Chen weichen1@andrew.cmu.edu
 *)
open Type
open Type.Hybrid
open Type.Basic
open Type.Mode
open Type.Jump
open Batteries
open IO
open Smt2_cmd
open Smt2
open Costmap
open Relevantvariables

exception SMTException of string

type ode = Ode.t
type flows_annot = (string * ode list)  (** step, ode **)
type comppath = Network.comppath

let global_vars = ref []

(*(** rename variable to related name in each step **)
let make_variable k suffix (s: string) : string =
  let str_step = string_of_int k in
  (String.join "_" [s; str_step;]) ^ suffix

(* assert for mode *)
(*let make_mode_cond ~k ~q =
  Basic.Eq (Basic.Var ("mode_" ^ (string_of_int k)), Basic.Num (float_of_int q))*)
let make_mode_cond ~k ~q =
  Basic.Eq (Basic.Var ("mode_" ^ (string_of_int k)), Basic.Var q)

(** assert for initial state and invariant **)
let process_init ~init_id ~init_formula =
  let mode_formula = make_mode_cond ~k:0 ~q:init_id in
  let init_formula' =
    Basic.subst_formula (make_variable 0 "_0") init_formula
  in
  Basic.And [init_formula'; mode_formula]


let extract_flows q (modemap:Modemap.t) : flows_annot =
  let m = Map.find q modemap in
  (q, m.flows)

(** extract variable declaration **)
let varmap_to_list vardeclmap =
  Map.foldi
    (fun var value vardecls -> (var, value)::vardecls)
    vardeclmap
    []

(** source mode & flow & mode invariant **)
let process_flow ~k ~q (varmap : Vardeclmap.t) (modemap:Modemap.t) : Basic.formula =
  let m = Map.find q modemap in
  let mode_formula = make_mode_cond ~k ~q in
  let time_var = (make_variable k "" "time") in
  let flow_formula =
    let vardecls = varmap_to_list varmap in
    let vars = List.map (fun (name, _) -> name) vardecls in
    let flow_var = (make_variable q "" "flow") in
    let ode_vars = List.filter (fun name -> name <> "time") vars in
    let ode_vars_0 = List.map (make_variable k "_0") ode_vars in
    let ode_vars_t = List.map (make_variable k "_t") ode_vars in
    Eq(Vec ode_vars_t (* ["x_1_t"; "y_1_t"] *),
                         Integral(0.0, time_var, ode_vars_0, flow_var)) in
  let inv_formula = match (Mode.invs_op m) with
      None -> Basic.True
    | Some invs ->
      let invt_conds =
        List.map
          (fun invt_f ->
            Basic.make_and
              [Basic.subst_formula (make_variable k "_0") invt_f;
               Basic.subst_formula (make_variable k "_t") invt_f;
               Basic.ForallT (Num (float_of_int q),
                              Num 0.0,
                              Var time_var,
                              (Basic.subst_formula (make_variable k "_t") invt_f))])
          invs
      in
      (* mode_k = q && inva_q(x_i, x_i_t) *)
      (* TODO add flow constraint here *)
      Basic.make_and invt_conds
  in
  Basic.make_and ([mode_formula; flow_formula; inv_formula])

(** source mode & flow & mode invariant **)
let process_flow_pruned ~k ~q (varmap : Vardeclmap.t) (modemap:Modemap.t) (relevant : Relevantvariables.t list option) : Basic.formula =
  let m = Map.find q modemap in
  let mode_formula = make_mode_cond ~k ~q in
  let not_mode_formula = Basic.make_and(
<<<<<<< HEAD
                             List.map (fun nm -> if nm = q then
                                               Basic.True
                                             else
                                               Basic.Not (make_mode_cond k nm)
                                  )
                                  (List.of_enum (Map.keys modemap))) in
=======
			     List.map (fun nm -> if nm = q then
					       Basic.True
					     else
					       Basic.Not (make_mode_cond k nm) 
				      )
				      (match relevant with
					Some(rel) -> (
					let relevant_at_k = List.nth rel k in
					(List.of_enum (Map.keys relevant_at_k))
				      )
				      | None -> (List.of_enum (Map.keys modemap)))
			   ) in
>>>>>>> b8bd95c... feat(heuristics): network heuristics working w/o labels, and added mode mutex constraint to encoding
  let time_var = (make_variable k "" "time") in
  let flow_formula =
    let vardecls = varmap_to_list varmap in
    let vars = List.map (fun (name, _) -> name) vardecls in
    let vars_pruned = List.filter
			(fun x ->
			 match relevant with
			   Some(rel) -> (
			   let relevant_at_k = List.nth rel k in
			   match Map.mem q relevant_at_k with
			     false -> false
			   | true ->
			      (Set.mem x (Map.find q relevant_at_k))
			 )
			 | None -> true
			) vars in
    if List.length vars_pruned = 0 then
      True
    else
    let q_string = (String.join "_" [""; (string_of_int q);]) in
    let flow_var = (make_variable k q_string "flow") in
    let ode_vars = List.filter (fun name -> name <> "time") vars_pruned in
    let ode_vars_0 = List.map (make_variable k "_0") ode_vars in
    let ode_vars_t = List.map (make_variable k "_t") ode_vars in
    Eq(Vec ode_vars_t (* ["x_1_t"; "y_1_t"] *),
                         Integral(0.0, time_var, ode_vars_0, flow_var))
  in
  let inv_formula = match (Mode.invs_op m) with
      None -> Basic.True
    | Some invs ->
      let invt_conds =
        List.map
          (fun invt_f ->
            Basic.make_and
              [Basic.subst_formula (make_variable k "_0") invt_f;
               Basic.subst_formula (make_variable k "_t") invt_f;
				   Basic.ForallT (Num (float_of_int q),
						  Num 0.0,
						  Var time_var,
						  (Basic.subst_formula (make_variable k "_t") invt_f))])
          invs
      in
      (* mode_k = q && inva_q(x_i, x_i_t) *)
      (* TODO add flow constraint here *)
      Basic.make_and invt_conds
  in
  Basic.make_and ([mode_formula; flow_formula; inv_formula])
(*		 Basic.make_and ([mode_formula; not_mode_formula; flow_formula; inv_formula])*)

(** transition change **)
let process_jump (modemap : Modemap.t) (q : Mode.id) (jump : Jump.t) k : Basic.formula =
  let next_q = jump.Jump.target in
  let mode = Map.find q modemap in
  let mode_formula = make_mode_cond ~k:(k+1) ~q:next_q in
  let gurad' = Basic.subst_formula (make_variable k "_t") jump.guard in
  let precision = Jump.precision jump in
  let used =
    Set.map
      (fun v ->
         match String.ends_with v "'" with
         | true -> String.rchop v
         | false -> v
      )
     (Basic.collect_vars_in_formula jump.change)
  in
  let change' =
    Basic.subst_formula
      (fun v -> match String.ends_with v "'" with
        (** x' => x_{k+1}_0 **)
        |  true -> make_variable (k+1) "_0" (String.rchop v)

        (** x => x_k_t **)
        | false -> make_variable k "_t" v
      )
      jump.change
  in

  let change'' =
    (* for variables that doesn't appear in code *)
    Basic.make_and (
      List.map
        (fun name ->
           match (Set.mem name used, precision) with
           | (false, 0.0) -> Basic.Eq (Basic.Var (make_variable k "_t" name), Basic.Var (make_variable (k+1) "_0" name))
           | (false, _) -> Basic.Eqp (Basic.Var (make_variable k "_t" name), Basic.Var (make_variable (k+1) "_0" name), precision)
           | (true, _) -> Basic.True
        )
        !global_vars
    )
  in
  Basic.make_and [gurad'; change'; change''; mode_formula]

(** transition change **)
let process_jump_pruned (modemap : Modemap.t) (q : Mode.id) (next_q : Mode.id) (relevant : Relevantvariables.t list option) k : Basic.formula =
  let mode = Map.find q modemap in
  let jumpmap = mode.jumpmap in
  let jump = Map.find next_q jumpmap in
  let mode_formula = make_mode_cond ~k:(k+1) ~q:next_q in
  let not_mode_formula = Basic.make_and(
<<<<<<< HEAD
                             List.map (fun nm -> if nm = next_q then
                                               Basic.True
                                             else
                                               Basic.Not (make_mode_cond (k+1) nm)
                                  )
                                  (List.of_enum (Map.keys modemap))) in
  let gurad' = Basic.subst_formula (make_variable k "_t") jump.guard in
=======
			     List.map (fun nm -> if nm = next_q then
					       Basic.True
					     else
					       Basic.Not (make_mode_cond (k+1) nm) 
				      )
				      (match relevant with
					 Some(rel) -> (
					 let relevant_at_k = List.nth rel k in
					 (List.of_enum (Map.keys relevant_at_k))
				       )
				       | None -> (List.of_enum (Map.keys modemap)))) in
  let guard' = Basic.subst_formula (make_variable k "_t") jump.guard in
>>>>>>> b8bd95c... feat(heuristics): network heuristics working w/o labels, and added mode mutex constraint to encoding
  let precision = Jump.precision jump in
  let used =
    Set.map
      (fun v ->
         match String.ends_with v "'" with
         | true -> String.rchop v
         | false -> v
      )
     (Basic.collect_vars_in_formula jump.change)
  in
  let change' =
    Basic.subst_formula
      (fun v -> match String.ends_with v "'" with
        (** x' => x_{k+1}_0 **)
        |  true -> make_variable (k+1) "_0" (String.rchop v)

        (** x => x_k_t **)
        | false -> make_variable k "_t" v
      )
      jump.change
  in
  let changevars =
    List.filter
      (fun x ->
       match relevant with
	 Some(rel) -> (
	 let relevant_at_k = List.nth rel k in
	 match Map.mem q relevant_at_k with
	   false -> false
	 | true ->  (Set.mem x (Map.find q relevant_at_k))
       )
       | None -> true )
      !global_vars
  in
  let change'' =
    (* for variables that doesn't appear in code *)
    Basic.make_and (
      List.map
        (fun name -> 
	 match relevant with
	   Some(rel) -> (
	   let relevant_at_k = List.nth rel k in
	   let relevant_at_k' = List.nth rel (k+1) in
	   match  ((Map.mem q relevant_at_k) &&
		     (Set.mem name (Map.find q relevant_at_k)) &&
		       (Map.mem next_q relevant_at_k') &&
			 (Set.mem name (Map.find next_q relevant_at_k')))
	   with  
	     false -> Basic.True
	   | true ->  
	      match (Set.mem name used, precision) with
	      | (false, 0.0) -> Basic.Eq (Basic.Var (make_variable k "_t" name), Basic.Var (make_variable (k+1) "_0" name))
	      | (false, _) -> Basic.Eqp (Basic.Var (make_variable k "_t" name), Basic.Var (make_variable (k+1) "_0" name), precision)
	      | (true, _) -> Basic.True
	 )
	 | None ->  
            match (Set.mem name used, precision) with
            | (false, 0.0) -> Basic.Eq (Basic.Var (make_variable k "_t" name), Basic.Var (make_variable (k+1) "_0" name))
            | (false, _) -> Basic.Eqp (Basic.Var (make_variable k "_t" name), Basic.Var (make_variable (k+1) "_0" name), precision)
            | (true, _) -> Basic.True
        )
        changevars
    )
  in
(*  Basic.make_and [guard'; change'; change''; mode_formula ; not_mode_formula] *)
  Basic.make_and [guard'; change'; change''; mode_formula] 


(** transition constrint, seems like not necessary, we can prune it when processing jump  **)
let process_trans () = True (** todo **)

(** for goal mode & invariant **)
let process_goals (k : int) (goals : (int * formula) list) =
  let goal_formulas =
    List.map
      (fun (q, goal_f) ->
        let goal_f' = Basic.make_and [goal_f] in
        let mode_cond = Basic.Eq (Basic.Var ("mode_" ^ (string_of_int k)), Basic.Num (float_of_int q)) in
        Basic.make_and [Basic.subst_formula (make_variable k "_t") goal_f'; mode_cond;]
      )
      goals
  in
  Basic.make_or goal_formulas

(** generate logic formula for each step 0...k **)
let process_step_pruned (varmap : Vardeclmap.t)
                 (modemap : Modemap.t)
		 (heuristic : Costmap.t)
                 (heuristic_back : Costmap.t)
		 (relevant : Relevantvariables.t list option)
		 (k : int)
                 (step : int)
    : Basic.formula =
  let num_of_modes = Enum.count (Map.keys modemap) in
  let list_of_modes = List.of_enum ( 1 -- num_of_modes ) in
  let list_of_possible_modes = List.filter
				 (fun q ->
				   ((Costmap.find q heuristic) <= float_of_int step) &&
				   ((Costmap.find q heuristic_back) <=  float_of_int (k - step))
				 )
				 list_of_modes
  in
  let jump_flow_part =
    List.map
      (fun q ->
       try
         let flow_for_q = process_flow_pruned ~k:step ~q varmap modemap relevant in
         let mode_q = Map.find q modemap in
         let jumpmap_q = mode_q.jumpmap in
         let list_of_nq = List.of_enum (Map.keys jumpmap_q) in
	 let list_of_possible_nq = List.filter
				 (fun q ->
				   ((Costmap.find q heuristic) <= float_of_int (step + 1)) &&
				   ((Costmap.find q heuristic_back) <=  float_of_int (k - (step + 1)))
				 )
				 list_of_nq
	 in
(*         let jump_for_q_nq  = Basic.make_or (List.map
                                               (fun nq ->
                                                process_jump_pruned modemap q nq relevant step
                                               )
                                               list_of_possible_nq)
         in
         Basic.make_and [flow_for_q; jump_for_q_nq] *)
         let jump_for_q_nq  = Basic.make_or (List.map
                                               (fun nq ->
						Basic.make_and [flow_for_q; (process_jump_pruned modemap q nq relevant step)]
                                               )
                                               list_of_possible_nq)
         in
         
	 jump_for_q_nq
       with e ->
         begin
           Printexc.print_backtrace IO.stderr;
           raise e
         end
      )
      list_of_possible_modes
  in
  Basic.make_or jump_flow_part

(** generate logic formula for each step 0...k **)
let process_step (varmap : Vardeclmap.t)
                 (modemap : Modemap.t)
                 (mode : string option)
                 (step : int)
    : Basic.formula =
  let num_of_modes = Enum.count (Map.keys modemap) in
  let list_of_modes = match mode with
      Some n -> [n]
     | None -> List.of_enum ( 1 -- num_of_modes ) in
  let jump_flow_part =
    List.map
      (fun q ->
       try
         let flow_for_q = process_flow ~k:step ~q varmap modemap in
         let mode_q = Map.find q modemap in
         let jump_for_q_nq  =
           Basic.make_or (List.map
                            (fun j -> process_jump modemap q j step)
                            (Mode.jumps mode_q))
         in
         Basic.make_and [flow_for_q; jump_for_q_nq]
       with e ->
         begin
           Printexc.print_backtrace IO.stderr;
           raise e
         end
      )
      list_of_modes
  in
  Basic.make_or jump_flow_part


let final_flow varmap modemap mode k =
  let list_of_modes = match mode with
      Some n -> [n]
    | None ->
       let num_modes = Enum.count (Map.keys modemap) in
       List.of_enum ( 1 -- num_modes )
  in let flows =
       List.map
         (
           fun q ->
           process_flow ~k ~q varmap modemap
         )
         list_of_modes
     in
     Basic.make_or flows

let final_flow_pruned varmap modemap mode k relevant goals =
  let list_of_modes = match mode with
      Some n -> [n]
    | None ->
       (*let num_modes = Enum.count (Map.keys modemap) in	*)
       List.map (fun (m, _) -> m ) goals
(*       List.of_enum ( 1 -- num_modes ) *)
  in let flows =
       List.map
         (
           fun q ->
           process_flow_pruned ~k ~q varmap modemap relevant
         )
         list_of_modes
     in
     Basic.make_or flows

(* compile Hybrid automata into SMT formulas *)
let compile_logic_formula_pruned (h : Hybrid.t) (k : int) (heuristic : Costmap.t) (heuristic_back : Costmap.t) (relevant : Relevantvariables.t list option) =
  let {init_id; init_formula; varmap; modemap; goals} = h in
  let init_clause = process_init ~init_id ~init_formula  in
  let list_of_steps = List.of_enum (0 -- (k-1)) in
  let step_clauses =
    List.map (process_step_pruned varmap modemap heuristic heuristic_back relevant k) list_of_steps
  in
  (* tricky case, final mode need flow without jump  *)
  let final_flow_clause = final_flow_pruned varmap modemap None k relevant goals in
  let goal_clause = process_goals k goals in
  let smt_formula = Basic.make_and (List.flatten [[init_clause]; step_clauses; [final_flow_clause];  [goal_clause]]) in
  Assert smt_formula

let compile_logic_formula (h : Hybrid.t) (k : int) (path : string list option) =
  let {init_id; init_formula; varmap; modemap; goals} = h in
  let init_clause = process_init ~init_id ~init_formula in
  let list_of_steps = List.of_enum (0 -- (k-1)) in
  let step_clauses =
    match path with
      Some p -> List.map2 (fun q k -> process_step varmap modemap (Some q) k)
                          (List.take k p)
                          list_of_steps
    | None -> List.map (process_step varmap modemap None) list_of_steps
  in
  (* tricky case, final mode need flow without jump  *)
  let final_flow_clause = match path with
      Some p -> final_flow varmap modemap (Some (List.last p)) k
    | None -> final_flow varmap modemap None k in
  let goal_clause = process_goals k goals in
  let smt_formula = Basic.make_and (List.flatten [[init_clause]; step_clauses; [final_flow_clause];  [goal_clause]]) in
  Assert smt_formula

(** variable declaration & range constraint **)
let compile_vardecl (h : Network.t) (k : int) (path : comppath option) =
  let {modemap} = h in
  let num_of_modes = Enum.count (Map.keys modemap) in
  let vardecls = varmap_to_list h.varmap in
  let (time_var_l, vardecls') = List.partition (fun (name, _) -> name = "time") vardecls in
  ignore (global_vars := List.map (fun (k, v) -> k) vardecls');

  (* generate time variable declaration *)
  let time_intv =
    match time_var_l with
      | (_, intv)::[] -> intv
      | _ -> raise (SMTException "time should be defined once and only once.")
  in
  let time_vardecls =
    List.map
      (fun n ->
        ("time_" ^ (Int.to_string n), time_intv))
      (List.of_enum (0 -- k))
  in

  (* generate variable declaration *)
  let vardecls'' =
    List.flatten
      (List.flatten
         (List.map
            (function (var, v) ->
              List.map
                (fun k' ->
                  [
                    (var ^ "_" ^ (Int.to_string k') ^ "_0", v);
                    (var ^ "_" ^ (Int.to_string k') ^ "_t", v)
                  ]
                )
                (List.of_enum ( 0 -- k))
            )
            vardecls'
         )
      )
  in

  (* generate mode variable declaration *)
  let mode_vardecls =
    List.map
      (fun n ->
          ("mode_" ^ (Int.to_string n), Value.Intv (1.0, float_of_int num_of_modes))
      )
      (List.of_enum (0 -- k))
  in
  let new_vardecls = List.flatten [vardecls''; time_vardecls; mode_vardecls] in
  let (vardecl_cmds, assert_cmds_list) =
    List.split
      (List.map
         (function
           | (name, Value.Intv (lb, ub)) ->
              begin
                match path with
                  Some(my_path) ->
                  begin
                    match (String.starts_with name "time_",
                           (String.sub name
                              ((String.index name '_') + 1)
                              (String.length name - ((String.index name '_') + 1)))) with
                      (true, time_id) ->
                      let time =  int_of_string time_id in
                      let mode_id = List.at my_path time in
                      let mode = Modemap.find mode_id h.modemap in
                      let tprecision = mode.time_precision in
                      (DeclareFun name,
                       [make_lbp name lb tprecision;
                        make_ubp name ub tprecision])
                    |  _ ->
                      (DeclareFun name,
                       [make_lb name lb;
                        make_ub name ub])
                  end
                | None ->
                  (DeclareFun name,
                   [make_lb name lb;
                    make_ub name ub])
              end
           | _ -> raise (SMTException "We should only have interval here."))
         new_vardecls) in
  let org_vardecl_cmds = List.map (fun (var, _) -> DeclareFun var) vardecls' in
  let assert_cmds = List.flatten assert_cmds_list in
  (org_vardecl_cmds@vardecl_cmds, assert_cmds)

(*let compile_vardecl (h : Hybrid.t) (k : int) (path : (string list) option) =
  let {modemap} = h in
  let num_of_modes = Enum.count (Map.keys modemap) in
  let vardecls = varmap_to_list h.varmap in
  let (time_var_l, vardecls') = List.partition (fun (name, _) -> name = "time") vardecls in
  ignore (global_vars := List.map (fun (k, v) -> k) vardecls');

  (* generate time variable declaration *)
  let time_intv =
    match time_var_l with
      | (_, intv)::[] -> intv
      | _ -> raise (SMTException "time should be defined once and only once.")
  in
  let time_vardecls =
    List.map
      (fun n ->
        ("time_" ^ (Int.to_string n), time_intv))
      (List.of_enum (0 -- k))
  in

  (* generate variable declaration *)
  let vardecls'' =
    List.flatten
      (List.flatten
         (List.map
            (function (var, v) ->
              List.map
                (fun k' ->
                  [
                    (var ^ "_" ^ (Int.to_string k') ^ "_0", v);
                    (var ^ "_" ^ (Int.to_string k') ^ "_t", v)
                  ]
                )
                (List.of_enum ( 0 -- k))
            )
            vardecls'
         )
      )
  in

  (* generate mode variable declaration *)
  let mode_vardecls =
    List.map
      (fun n ->
          ("mode_" ^ (Int.to_string n), Value.Intv (1.0, float_of_int num_of_modes))
      )
      (List.of_enum (0 -- k))
  in
  let new_vardecls = List.flatten [vardecls''; time_vardecls; mode_vardecls] in
  let (vardecl_cmds, assert_cmds_list) =
    List.split
      (List.map
         (function
           | (name, Value.Intv (lb, ub)) ->
              begin
                match path with
                  Some(my_path) ->
                  begin
                    match (String.starts_with name "time_",
                           (String.sub name
                              ((String.index name '_') + 1)
                              (String.length name - ((String.index name '_') + 1)))) with
                      (true, time_id) ->
                      let time =  int_of_string time_id in
                      let mode_id = List.at my_path time in
                      let mode = Modemap.find mode_id h.modemap in
                      let tprecision = mode.time_precision in
                      (DeclareFun name,
                       [make_lbp name lb tprecision;
                        make_ubp name ub tprecision])
                    |  _ ->
                      (DeclareFun name,
                       [make_lb name lb;
                        make_ub name ub])
                  end
                | None ->
                  (DeclareFun name,
                   [make_lb name lb;
                    make_ub name ub])
              end
           | _ -> raise (SMTException "We should only have interval here."))
         new_vardecls) in
  let org_vardecl_cmds = List.map (fun (var, _) -> DeclareFun var) vardecls' in
  let assert_cmds = List.flatten assert_cmds_list in
  (org_vardecl_cmds@vardecl_cmds, assert_cmds)*)

(** variable declaration & range constraint **)
let compile_vardecl_pruned (h : Hybrid.t) (k : int) (path : (int list) option) (relevant : Relevantvariables.t list option)  =
  let {modemap} = h in
  let num_of_modes = Enum.count (Map.keys modemap) in
  let vardecls = varmap_to_list h.varmap in
  let (time_var_l, vardecls') = List.partition (fun (name, _) -> name = "time") vardecls in
  ignore (global_vars := List.map (fun (k, v) -> k) vardecls');

  (* generate time variable declaration *)
  let time_intv =
    match time_var_l with
      | (_, intv)::[] -> intv
      | _ -> raise (SMTException "time should be defined once and only once.")
  in
  let time_vardecls =
    List.map
      (fun n ->
        ("time_" ^ (Int.to_string n), time_intv))
      (List.of_enum (0 -- k))
  in

  (* generate variable declaration *)
  let vardecls'' =
    List.flatten
      (List.flatten
         (List.map
            (function (var, v) ->
              List.map
                (fun k' -> 
		 match relevant with
		   Some(rel) -> (
		   let relevant_at_k = List.nth rel k' in
		   let in_a_relevant_mode (mvar : String.t)  = 
		     let mode_relevant key mset  = BatSet.mem mvar mset in
		     (Map.exists mode_relevant relevant_at_k)
		   in
		   match in_a_relevant_mode var with  
		     false -> []
		   | true ->
                      [
			(var ^ "_" ^ (Int.to_string k') ^ "_0", 
			 v);
			(var ^ "_" ^ (Int.to_string k') ^ "_t", v)
                      ]
		 )
		  |
		    None  ->
                      [
			(var ^ "_" ^ (Int.to_string k') ^ "_0", v);
			(var ^ "_" ^ (Int.to_string k') ^ "_t", v)
                      ]		 
                )
                (List.of_enum ( 0 -- k))
            )
            vardecls'
         )
      )
  in

  (* generate mode variable declaration *)
  let mode_vardecls =
    List.map
      (fun n ->
          ("mode_" ^ (Int.to_string n), Value.Intv (1.0, float_of_int num_of_modes))
      )
      (List.of_enum (0 -- k))
  in
  let new_vardecls = List.flatten [vardecls''; time_vardecls; mode_vardecls] in
  let (vardecl_cmds, assert_cmds_list) =
    List.split
      (List.map
         (function
           | (name, Value.Intv (lb, ub)) ->
              begin
                match path with
                  Some(my_path) ->
                  begin
                    match (String.starts_with name "time_",
                           (String.sub name
                              ((String.index name '_') + 1)
                              (String.length name - ((String.index name '_') + 1)))) with
                      (true, time_id) ->
                      let time =  int_of_string time_id in
                      let mode_id = List.at my_path time in
                      let mode = Modemap.find mode_id h.modemap in
                      let tprecision = mode.time_precision in
                      (DeclareFun name,
                       [make_lbp name lb tprecision;
                        make_ubp name ub tprecision])
                    |  _ ->
                      (DeclareFun name,
                       [make_lb name lb;
                        make_ub name ub])
                  end
                | None ->
                  (DeclareFun name,
                   [make_lb name lb;
                    make_ub name ub])
              end
           | _ -> raise (SMTException "We should only have interval here."))
         new_vardecls) in
  let org_vardecl_cmds = List.map (fun (var, _) -> DeclareFun var) vardecls' in
  let assert_cmds = List.flatten assert_cmds_list in
  (org_vardecl_cmds@vardecl_cmds, assert_cmds)

let calc_num_of_mode (modemap : Modemap.t) =
  Enum.count (Map.keys modemap)

(** build a list of odes **)
let build_flow_annot_list (h : Hybrid.t) (step:int) =
  let {varmap; modemap} = h in
  let num_of_modes = Enum.count (Map.keys modemap) in
  let list_of_modes = List.of_enum ( 1 -- num_of_modes ) in
  List.map (function q -> extract_flows q modemap) list_of_modes

(** build list of ode definition **)
let compile_ode_definition (h : Hybrid.t) k =
  let flows = build_flow_annot_list h k in
  List.map (fun (g, odes) -> DefineODE ((make_variable g "" "flow"), odes)) flows

(** build list of ode definition **)
let compile_ode_definition_pruned (h : Hybrid.t) k (relevant : Relevantvariables.t list option) =
  let flows = build_flow_annot_list h k in
  let list_of_steps = List.of_enum ( 0 -- k ) in
  List.flatten
    (List.map
    (fun (g, odes) ->
     List.map
       (fun step ->
	let g_string = (String.join "_" [""; (string_of_int g);]) in
	(DefineODE ((make_variable step g_string "flow"), odes)))
       list_of_steps
    )
    flows)


let compile_pruned (h : Hybrid.t) (k : int) (heuristic : Costmap.t)  (heuristic_back : Costmap.t) (relevant : Relevantvariables.t list option) =
  let logic_cmd = SetLogic QF_NRA_ODE in
  let (vardecl_cmds, assert_cmds) = compile_vardecl_pruned h k None relevant in
  let defineodes = compile_ode_definition_pruned h k relevant in
  let assert_formula = compile_logic_formula_pruned h k heuristic heuristic_back relevant in
  List.flatten
    [[logic_cmd];
     vardecl_cmds;
     defineodes;
     assert_cmds;
     [assert_formula];
     [CheckSAT; Exit];
    ]

let compile (h : Network.t) (k : int) (path : comppath option) =
	List.flatten [[CheckSAT; Exit]]
  (*let logic_cmd = SetLogic QF_NRA_ODE in
  let (vardecl_cmds, assert_cmds) = compile_vardecl h k path in
  let defineodes = compile_ode_definition h k in
  let assert_formula = compile_logic_formula h k path in
  List.flatten
    [[logic_cmd];
     vardecl_cmds;
     defineodes;
     assert_cmds;
     [assert_formula];
     [CheckSAT; Exit];
    ]*)

(** Enumerate all possible paths of length k in Hybrid Model h *)
let pathgen (h : Network.t) (k : int) : comppath list =
  (*let init_mode_id = h.init_id in
  let goal_mode_ids = List.map (fun (m, _) -> m ) h.goals in
  let init_path = [init_mode_id] in*)
  let init_mode_id = Network.init_mode_map h in
  let goal_mode_ids = Network.goal_ids h in
  let init_path = [Map.bindings init_mode_id] in
  []
  (* recursive function to generate reachable paths *)
  (* NOTE: it generates path in reverse order! *)
  (*let rec pathgen_aux h k paths =
    if k = 0 then
      paths
    else
      let newpaths = List.flatten (
          List.map (fun path ->
              match path with
                last_mode_id::prefix ->
                let last_mode = Map.find last_mode_id h.modemap in
                let targets = List.of_enum (Map.keys last_mode.jumpmap) in
                List.map (fun t -> t::last_mode_id::prefix) targets
              | _ -> failwith "pathgen_aux gets empty path."
            )
            paths)
      in
      pathgen_aux h (k - 1) newpaths
  in
  let reversed_result = pathgen_aux h k [init_path] in
  let result = List.map List.rev reversed_result in
  let filtered_result =
    (* Filter out an unfeasible path [m_0, m_1, ... m_k]:
       - if [m_0] is not H.init_mode
       - if [m_k] is not in h.goal_modes
    *)
    List.filter (fun l ->
        let first = List.first l in
        let last = List.last l in
        first = init_mode_id && List.mem last goal_mode_ids
      ) result in
  filtered_result*)
  
(*let pathgen (h : Network.t) (k : int) : comppath list =
  (*let init_mode_id = h.init_id in
  let goal_mode_ids = List.map (fun (m, _) -> m ) h.goals in
  let init_path = [init_mode_id] in*)
  let init_mode_id = Network.init_mode_map h in
  let goal_mode_ids = List.map (fun (m, _) -> m ) h.goals in
  let init_path = [init_mode_id] in
  (* recursive function to generate reachable paths *)
  (* NOTE: it generates path in reverse order! *)
  let rec pathgen_aux h k paths =
    if k = 0 then
      paths
    else
      let newpaths = List.flatten (
          List.map (fun path ->
              match path with
                last_mode_id::prefix ->
                let last_mode = Map.find last_mode_id h.modemap in
                let targets = List.of_enum (Map.keys last_mode.jumpmap) in
                List.map (fun t -> t::last_mode_id::prefix) targets
              | _ -> failwith "pathgen_aux gets empty path."
            )
            paths)
      in
      pathgen_aux h (k - 1) newpaths
  in
  let reversed_result = pathgen_aux h k [init_path] in
  let result = List.map List.rev reversed_result in
  let filtered_result =
    (* Filter out an unfeasible path [m_0, m_1, ... m_k]:
       - if [m_0] is not H.init_mode
       - if [m_k] is not in h.goal_modes
    *)
    List.filter (fun l ->
        let first = List.first l in
        let last = List.last l in
        first = init_mode_id && List.mem last goal_mode_ids
      ) result in
  filtered_result
*)*)

(*let extract_flows q (modemap: Modemap.t) : flows_annot =
	let m = Map.find q modemap in
	(q, Mode.flows m)*)
	
(** build a list of odes **)
(*let build_flow_annot_list (h : Hybrid.t) (step:int) =
  let {varmap; modemap} = h in
  let num_of_modes = Enum.count (Map.keys modemap) in
  let list_of_modes = List.of_enum (1 -- num_of_modes ) in
  List.map (function q -> extract_flows q modemap) list_of_modes*)

(** build list of ode definition **)
(*let compile_ode_definition (h : Hybrid.t) k =
  let flows = build_flow_annot_list h k in
  List.map (fun (g, odes) -> DefineODE ((make_variable g "" "flow"), odes)) flows*)
  
let filter_aut_mode_distance aut k (filter: bool) = 
	let modes = List.map (fun (_, x) -> x) (Map.bindings (Hybrid.modemap aut)) in
	match filter with
		| true -> List.filter (fun m -> Mode.init_dist m <= k) modes
		| false -> modes

let mk_variable k suffix (s: string) : string =
  let str_step = string_of_int k in
  (String.join "_" [s; str_step;]) ^ suffix
  
let mk_enforce k aut = 
	"mode_" ^ (string_of_int (Hybrid.numid aut)) ^ "_" ^ (string_of_int k)
	
let mk_cnd term c = 
	Basic.Eq (Basic.Var (term), Basic.Num (float_of_int c))
	
(*let mk_enforce_s k aut =
	"enforce_" ^ aut ^ "_" ^ (string_of_int k)*)
	
let mk_gamma_nt aut mode = 
	"gamma_" ^ (Hybrid.name aut) ^ "_" ^ (string_of_int (Mode.mode_numId mode))
	
let mk_gamma k aut mode =
	(mk_gamma_nt aut mode) ^ "_" ^ (string_of_int k) ^ "_0"
	
let mk_gamma_t k aut mode =
	(mk_gamma_nt aut mode) ^ "_" ^ (string_of_int k) ^ "_t"
	
let mk_sync k label = 
	"sync_" ^ label ^ "_" ^ (string_of_int k)
	
let build_flow_annot_list_network (h: Network.t) k (filter: bool) = 
	let auta = Network.automata h in
	let b = List.map (fun a -> (a, filter_aut_mode_distance a k filter)) auta in
	let d = List.map (fun (a, mlist)-> List.map (fun m -> (a, m, m.flows)) mlist) b in
	List.flatten d
	
let mk_flow_var (a: Hybrid.t) (m: Mode.t) (k: int) = 
	"flow_" ^ (string_of_int (Hybrid.numid a)) ^ "_" ^ (string_of_int (Mode.mode_numId m)) ^ "_" ^ (string_of_int k)
	
let mk_flow_mul_gamma (o: Ode.t list) k aut mode = 
	List.map (fun (v, oexp) -> (v, Basic.Mul [oexp; Basic.Var (mk_gamma k aut mode)])) o

let mk_flow_mul_gamma_nt (o: Ode.t) aut mode = 
	let (v, oexp) = o in
	Basic.Mul [oexp; Basic.Var (mk_gamma_nt aut mode)]
	
let mk_flow_mul_gamma_s (o: Ode.t) k aut mode = 
	let (v, oexp) = o in
	Basic.Mul [oexp; Basic.Var (mk_gamma k aut mode)]
	
let build_var_flow_list (n: Network.t) k (filter: bool) =
	let flows = build_flow_annot_list_network n k filter in
	let gvars = Network.all_varnames_unique (Network.automata n) in
	let fflows = List.flatten (List.map (fun (a, m, odes) -> List.map (fun ode -> (a, m, ode)) odes) flows) in
	let vflows = List.map (fun v -> (v, List.filter (fun (a, m, (vi, _)) -> v = vi) fflows)) gvars in
	let (non_empty_flows, empty_flows) = List.partition (fun (_, vf) -> (List.length vf) > 0) vflows in
	let mul_flows = List.map (fun (v, fl) -> (v, List.map (fun (a, m, ode) -> mk_flow_mul_gamma_nt ode a m) fl)) non_empty_flows in
	let sum_flows = List.map (fun (v, fl) -> 
		match (List.length fl) > 1 with
			true -> (v, Basic.Add fl)
			| false -> (v, List.hd fl)
	) mul_flows in
	let gamma_plain = List.flatten (List.map (
		fun x -> List.map (
			fun y -> (mk_gamma_nt x y, Basic.Num (0.0))
		)
		(filter_aut_mode_distance x k filter)
	) (Network.automata n)) in
	let const_change_flows = List.map (fun (v, _) -> (v, Basic.Num (0.0))) empty_flows in
	sum_flows@gamma_plain@const_change_flows
	
let compile_ode_definition (n: Network.t) k (filter: bool) = 
	(* We require only one actual flow definition since it's basically a factorization of all flows *)
	[(DefineODE ("flow_0", build_var_flow_list n k filter))]
	
let get_ode_var_map (n: Network.t) (k: int) (filter: bool) = 
	let flowlist = build_flow_annot_list_network n k filter in
	let steps = List.of_enum (0 -- (k-1)) in
	List.fold_left 
	(
		fun map (a, m, odes) -> 
			List.fold_left 
			(
				fun mapi i -> 
					Map.add (mk_flow_var a m i) (List.map (fun (v, _) -> v) odes) mapi
			)
			map
			steps
	)
	Map.empty
	flowlist

let mk_flow (n: Network.t) i k (filter: bool) = 
	let fl = build_var_flow_list n k filter in
	let fvar = "flow_0" in
	let timevar = mk_variable i "" "time" in
	let vvars = List.map (fun (v, _) -> v) fl in
	let varBegin = List.map (fun v -> mk_variable i "_0" v) vvars in
	let varEnd = List.map (fun v -> match String.starts_with v "gamma" with
		false -> mk_variable i "_t" v
		|true -> mk_variable i "_0" v 
	) vvars in
	let vecBegin = Basic.Vec varBegin in
	let vecEnd = Basic.Vec varEnd in
	Basic.Eq (vecEnd, Basic.Integral (0.0, timevar, varBegin, fvar))
	
let mk_inv_q mode i = 
	let invs = mode.invs_op in
	let time_var = mk_variable i "" "time" in
	match invs with
		None -> Basic.True
		| Some fl -> begin
			let invs_mapped = List.map (fun f -> Basic.subst_formula (mk_variable i "_t") f) fl in
			let conj_invs = Basic.make_and invs_mapped in
			Basic.ForallT (Basic.Num (float_of_int i),
											Basic.Num 0.0,
											Basic.Var time_var,
											conj_invs)
			end
			
let mk_inv (n: Network.t) i k (filter: bool) = 
	let auta = Network.automata n in
	let enf_mode_inv = List.map (fun a -> begin
		let modes = filter_aut_mode_distance a k filter in
		List.map (fun m -> Basic.Imply (mk_cnd (mk_enforce i a) (Mode.mode_numId m), mk_inv_q m i)) modes
	end) auta in
	Basic.make_and (List.flatten enf_mode_inv)
	
let mk_maintain (n: Network.t) i k (filter: bool) = 
	let flow = mk_flow n i k filter in
	let inv = mk_inv n i k filter in
	let time_var = mk_variable i "" "time" in
	(*let forall_inv = Basic.ForallT (Basic.Num (float_of_int i),
									Basic.Num 0.0,
									Basic.Var time_var,
									inv) in*)
	Basic.make_and [flow; inv]
	
let mk_init aut = 
	let modeId = Hybrid.init_id aut in
	let modemap = Hybrid.modemap aut in
	let mode = Map.find modeId modemap in
	let form = Hybrid.init_formula aut in 
	let from_mapped = Basic.subst_formula (mk_variable 0 "_0") form in
	let enforcement = mk_cnd (mk_enforce 0 aut) (Mode.mode_numId mode) in
	Basic.make_and [from_mapped; enforcement]
	
let mk_init_network n = 
	let inits = List.map (fun x -> mk_init x) (Network.automata n) in
	Basic.make_and inits
	
let mk_goal_network n k = 
	let (mode_list, form) = Network.goals n in
	let form_mapped = Basic.subst_formula (mk_variable k "_t") form in
	let auta = Network.automata n in
	let enforcement = List.map (fun x ->
		begin
			let (aut, mode) = x in
			let a_obj = List.find (fun a -> (Hybrid.name a) = aut) auta in
			let autmode = Map.find x (Modemapping.name_to_obj (Network.modemapping n)) in
			mk_cnd (mk_enforce k a_obj) (Mode.mode_numId autmode)
		end
	) 
	mode_list in
	Basic.make_and [form_mapped;(Basic.make_and enforcement)]
	
let split_decls_assertions lst path = 
	List.split
      (List.map
         (function
           | (name, Value.Intv (lb, ub)) ->
              begin
                match path with
                  Some (my_path) ->
                      (DeclareFun name,
                       [make_lb name lb;
                        make_ub name ub])
                | None ->
                  (DeclareFun name,
                   [make_lb name lb;
                    make_ub name ub])
              end
           | _ -> raise (SMTException "We should only have interval here."))
         lst)
  
let compile_vardecl (h : Network.t) (k : int) (path : comppath option) (precompute: bool) (filter: bool) =
  let automatalist = List.map (fun x -> Hybrid.name x) (Network.automata h) in
  let vardecls = Network.all_vars_unique (Network.automata h) in (*global vars, basically*)
  let time_var_l = Network.time h in
  let time_intv =
    match time_var_l with
      | (_, intv) -> intv
      | _ -> raise (SMTException "time should be defined once and only once.")
  in
  let time_vardecls =
    List.map
      (fun n ->
        ("time_" ^ (Int.to_string n), time_intv))
      (List.of_enum (0 -- k))
  in
  let vardecls' = 
	List.flatten
      (List.flatten
         (List.map
            (function (var, v) ->
              List.map
                (fun k' ->
                  [
                    (var ^ "_" ^ (Int.to_string k') ^ "_0", v);
                    (var ^ "_" ^ (Int.to_string k') ^ "_t", v)
                  ]
                )
                (List.of_enum ( 0 -- k))
            )
            vardecls
         )
      )
  in
  let enforcement = List.flatten (List.map (
    fun y ->
      List.map (
        fun x -> begin
          let modes = List.map (fun (_, x) -> x) (Map.bindings (Hybrid.modemap y)) (*filter_aut_mode_distance y k filter*) in
		  (mk_enforce x y, Value.Intv (1.0, float_of_int (List.length modes)))
        end
      )
      (List.of_enum (0 -- k))
    )
  (Network.automata h)) in
  let syncs = match precompute with
    | false -> List.flatten (List.map (fun l -> 
      List.map (fun i ->
          (DeclareBool (mk_sync i l))
        ) 
        (List.of_enum (0 -- (k-1)))
      )
      (Network.all_label_names_unique (Network.automata h)))
    | true -> []
  in
  let gamma = List.flatten (List.flatten (List.map (
    fun x -> List.map (
      fun y -> List.map (
        fun z -> (mk_gamma z x y, Value.Intv (0.0, 1.0))
      )
      (List.of_enum (0 -- k))
    )
    (filter_aut_mode_distance x k filter)
  )
  (Network.automata h))) in
  let gamma_t = List.flatten (List.flatten (List.map (
    fun x -> List.map (
      fun y -> List.map (
        fun z -> (mk_gamma_t z x y, Value.Intv (0.0, 1.0))
      )
      (List.of_enum (0 -- k))
    )
    (filter_aut_mode_distance x k filter)
  )
  (Network.automata h))) in
  let gamma_plain = List.flatten (List.map (
    fun x -> List.map (
      fun y -> DeclareFun (mk_gamma_nt x y)
    )
    (filter_aut_mode_distance x k filter)
  )
  (Network.automata h)) in
  let new_vardecls = List.flatten [vardecls'; time_vardecls] in
  let (vardecl_cmds, assert_cmds_list) = split_decls_assertions new_vardecls path in
  let (enfdecl_cmds, assert_enf_list) = split_decls_assertions enforcement path in
  let (gamdecl_cmds, assert_gam_list) = split_decls_assertions gamma path in
  let (gamdecl_cmds_t, assert_gam_list_t) = split_decls_assertions gamma_t path in
  let org_vardecl_cmds = List.map (fun (var, _) -> DeclareFun var) vardecls in
  let assert_cmds = List.flatten assert_cmds_list in
  let assert_enf = List.flatten assert_enf_list in
  let assert_gam = List.flatten assert_gam_list in
  let assert_gam_t = List.flatten assert_gam_list_t in
  (org_vardecl_cmds@vardecl_cmds@syncs@enfdecl_cmds@gamma_plain@gamdecl_cmds(*@gamdecl_cmds_t*), assert_cmds@assert_enf@assert_gam(*@assert_gam_t*))

let rec lst_intersection' slst1 slst2 inter =
	match
		try Some (List.hd slst1, List.hd slst2)
		with _ -> None
	with
		| Some (x, y) ->
			begin
				let (str1, b1) = x in
				let (str2, b2) = y in
				match b1 && b2 with
					| true -> lst_intersection' (List.tl slst1) (List.tl slst2) (str1::inter)
					| false -> lst_intersection' (List.tl slst1) (List.tl slst2) (inter)
			end
		| None -> inter
		
(* fill list 1 with records from list 2 that are not present in list 1*)
let rec fill_list lst1 lst2 = 
	match
		try Some (List.hd lst2)
		with _ -> None
	with
		| Some x -> 
			begin
				match (List.mem (x, true) lst1) || (List.mem (x, false) lst1) with
					| true -> (fill_list lst1 (List.tl lst2))
					| false -> (fill_list ((x, false)::lst1) (List.tl lst2))
			end
		| None -> lst1
	
let comp_tuple x y =
	let (str1, b1) = x in
	let (str2, b2) = y in
	compare str1 str2
	
let lst_intersection lst1 lst2 =
	let fLst1 = fill_list (List.map (fun x -> (x, true)) lst1) lst2 in
	let fLst2 = fill_list (List.map (fun x -> (x, true)) lst2) lst1 in
	let sLst1 = List.sort comp_tuple fLst1 in
	let sLst2 = List.sort comp_tuple fLst2 in
	lst_intersection' sLst1 sLst2 []
	
let cmp_jump_records record1 record2 = 
	let (org1, lab1, des1, jmp1) = record1 in
	let (org2, lab2, des2, jmp2) = record2 in
	let inter = lst_intersection lab1 lab2 in
	inter
  
let mk_jmp_variable i var = 
	match String.contains var '\'' with
		true -> mk_variable (i+1) "_0" (String.filter (fun c -> not (c = '\'')) var)
		| false -> mk_variable i "_t" var
  
let mk_jump aut j i =
	let (org, lab, des, jmp) = j in
	let aut_vars = List.map (fun (var, _) -> var) (Map.bindings (Hybrid.vardeclmap aut)) in
	let guard = Jump.guard jmp in
	let change = Jump.change jmp in
	let used = Set.map
		(fun v ->
			match String.ends_with v "'" with
			| true -> String.rchop v
			| false -> v
		)
	(Basic.collect_vars_in_formula change) in
	let change_unused =
		Basic.make_and (List.map (fun name ->
			match Set.mem name used with
			| false -> Basic.Eq (Basic.Var (mk_variable i "_t" name), Basic.Var (mk_variable (i+1) "_0" name))
			| true -> Basic.True
		)
		aut_vars
    ) in
	let guard_mapped = Basic.subst_formula (mk_variable i "_t") guard in
	let change_mapped = Basic.subst_formula (mk_jmp_variable i) change in
	Basic.make_and [guard_mapped; change_mapped; change_unused]
  
let trans_jump aut j i =
	let (org, lab, des, jmp) = j in
	let enforce_org = mk_cnd (mk_enforce i aut) (Mode.mode_numId org) in
	let enforce_des = mk_cnd (mk_enforce (i+1) aut) (Mode.mode_numId des) in
	let jmp = mk_jump aut j i in
	let enforcement = Basic.make_and [enforce_org; enforce_des] in
	Basic.make_and [jmp; enforcement]
	
let trans_jump_sync aut j i = 
	let (org, lab, des, jmp) = j in
	let enforce_org = mk_cnd (mk_enforce i aut) (Mode.mode_numId org) in
	let enforce_des = mk_cnd (mk_enforce (i+1) aut) (Mode.mode_numId des) in
	let jmp = mk_jump aut j i in
	let enforcement = Basic.make_and [enforce_org; enforce_des] in
	let glab = Hybrid.labellist aut in
	let inter = lst_intersection lab glab in
	let ninter = List.filter (fun x -> not (List.mem x inter)) glab in
	let syncs = Basic.make_and (List.map (fun v -> Basic.FVar (mk_sync i v)) inter) in
	let nsyncs = Basic.make_and (List.map (fun v -> Basic.Not (Basic.FVar (mk_sync i v))) ninter) in
	Basic.make_and [syncs; nsyncs; jmp; enforcement]
	
let mk_noop aut mode = 
	let aut_vars = List.map (fun (var, _) -> var) (Map.bindings (Hybrid.vardeclmap aut)) in
	let change = Basic.make_and (List.map (fun v -> Basic.Eq (Basic.Var (v ^ "'"), Basic.Var v)) aut_vars) in
	Jump.make (True, Mode.mode_id mode, change, [])
  
let trans n aut i k (filter: bool) = 
	let name = Hybrid.name aut in
	let getMode mname = begin
		let mapping = Network.modemapping n in
		let name_to_obj = Modemapping.name_to_obj mapping in
		Map.find (name, mname) name_to_obj
	end in
	let modes = match filter with 
		| false -> Map.bindings (Hybrid.modemap aut)
		| true -> List.filter (fun (_, m) -> (Mode.init_dist m) <= k) (Map.bindings (Hybrid.modemap aut)) in
	(*let jumps = *)List.flatten (List.map (fun (modename, modeobj) -> 
		begin
			let jm = match filter with 
				| false -> Mode.jumps modeobj
				| true -> List.filter (fun j -> Mode.init_dist (getMode (Jump.target j)) <= k) (Mode.jumps modeobj) in
			(* Add noop transition *)
			let jmn = (mk_noop aut modeobj)::jm in
			List.map (fun j -> (modeobj, Jump.label j, getMode (Jump.target j), j)) jmn
		end
	) 
	modes)
	
let global_label_set n = 
	let auta = Network.automata n in
	let l_list = List.flatten (List.map (fun x -> Hybrid.labellist x) auta) in
	List.sort_unique compare l_list
	
let get_all_jumps_for_label l aut_jlist =
	let (aut, jlist) = aut_jlist in
	let fList = List.filter (fun (org, lab, des, jmp) ->  List.mem l lab) jlist in
	(aut, fList)
	
let get_labeled_jumptable n aut_jlist = 
	let labels = global_label_set n in
	List.map (fun l -> (l, List.map (fun aj -> get_all_jumps_for_label l aj) aut_jlist)) labels
	
let create_jumplist j jlothers cur = 
	j::(List.map (fun (aut, jmps) -> (aut, List.at jmps (List.assoc aut cur))) jlothers)

let idx_list_op op lst idx = 
	let lNum = List.of_enum (0 -- ((List.length lst)-1)) in
	List.map (
		fun cnt -> 
		begin
			let (aut, curcnt) = List.at lst cnt in
			match cnt = idx with
				| true -> (aut, op curcnt)
				| false -> (aut, curcnt)
		end
	)
	lNum
	
let reset_idx_list lst idx = 
	idx_list_op (fun x -> 0) lst idx

let inc_idx_list lst idx =
	idx_list_op (fun x -> x + 1) lst idx
	
let set_idx_list lst idx n =
	idx_list_op (fun x -> n) lst idx
	
let rec collect_comb j jlothers cur endl curIdx = 
	match curIdx >= List.length cur with
		| true -> []
		| false -> begin
			let (aut, eIdx) = List.at endl curIdx in
			let lNum = List.of_enum (0 -- eIdx) in
			(*for i = 0 to (List.at endl curIdx) do
				let nCur = set_idx_list cur curIdx i in
				let jmppath = create_jumplist jlothers nCur in
				jmppath::(collect_comb j jlothers nCur endl (curIdx + 1))
			done*)
			List.flatten (List.map (
				fun x -> begin
					let nCur = set_idx_list cur curIdx x in
					let jmppath = create_jumplist j jlothers nCur in
					jmppath::(collect_comb j jlothers nCur endl (curIdx + 1))
				end
			)
			lNum)
			end
	
let get_all_jump_intersections jmp jlothers =
	let (_, jp) = jmp in
	let (_, (_, lbl, _, _)) = jmp in
	let possible = List.map (
		fun (aut, jumps) -> begin
			(*let mfjmps = List.map (fun j -> ((cmp_jump_records jmp j), j)) jumps in*)
			let fjmps = List.filter (fun j -> (List.length (cmp_jump_records jp j) > 0)) jumps in
			(aut, fjmps)
		end
	)
	jlothers in
	let possible_f = List.filter (fun (aut, fjumps) -> (List.length fjumps) > 0) possible in
	let start = List.map (fun (aut, fjumps) -> (aut, 0)) possible_f in
	let endl = List.map (fun (aut, fjumps) -> (aut, (List.length fjumps) - 1)) possible_f in
	(lbl, collect_comb jmp possible_f start endl 0)
	
let label_contained jumplist label = 
	List.length (List.filter (fun (lbl, _) -> List.mem label lbl) jumplist) > 0
	
(*Get list of labels not yet synchronized with*)
let get_new_labels jmp jmplist = 
	let (org, labels, dest, jump) = jmp in
	List.filter (fun x -> not (label_contained jmplist x)) labels
	
let rec jump_inter jl jlothers curjumplist = 
	let (aut, jumps) = jl in
	let nljumps = List.map (fun j -> 
		begin
			let (org, lbl, dest, jmp) = j in
			(org, get_new_labels j curjumplist, dest, jmp)
		end
	) jumps in
	let pJumps = List.filter (fun (_, lbl, _, _) -> (List.length lbl) > 0) nljumps in
	let apJumps = List.map (fun x -> (aut, x)) pJumps in
	curjumplist@(List.map (fun j -> get_all_jump_intersections j jlothers) apJumps)
	
let rec get_jump_conjunctions jlist curjumplist = 
	match
		try Some (List.hd jlist)
		with _ -> None
	with
		| Some x -> 
			begin
				let lRest = List.tl jlist in
				match lRest with
					| [] -> (get_jump_conjunctions lRest curjumplist)
					| _ -> 
						begin
						let jumps = jump_inter x lRest curjumplist in
						get_jump_conjunctions lRest jumps
						end
			end
		| None -> curjumplist
		
let get_unlabeled_jumps jmplist = 
	let a = List.map (fun (aut, jlist) -> List.map (fun jmp -> (aut, jmp)) jlist) jmplist in
	let b = List.flatten a in
	let c = List.filter (fun (_, (_, lbl, _, _)) -> lbl = []) b in
	c
	
let trans_network_precomposed n i k (filter: bool) =
	let automata = Network.automata n in
	let jumplst = List.map (fun a -> (a, trans n a i k filter)) automata in
	let jc = get_jump_conjunctions jumplst [] in
	let a = List.map (fun (x, y) -> y) jc in
	let b = List.flatten a in
	let c = List.map (fun x -> Basic.make_and (List.map (fun (aut, jmp) -> trans_jump aut jmp i) x)) b in
	let uj = get_unlabeled_jumps jumplst in
	let muj = List.map (fun (aut, jmp) -> trans_jump aut jmp i) uj in
	let oc = Basic.make_or c in
	let omuj = Basic.make_or muj in
	Basic.make_or [oc; omuj]
	
let trans_network n i k (filter: bool) =
	let automata = Network.automata n in
	let jumplst = List.map (fun a -> (a, trans n a i k filter)) automata in
	let ax = List.map (fun (a, jlist) ->
		Basic.make_or (List.map (fun j -> trans_jump_sync a j i) jlist)
	) 
	jumplst in
	let bx = Basic.make_and ax in
	bx
	
let mk_active_mode (aut: Hybrid.t) (m: Mode.t) (i: int) = 
	let nId = Mode.mode_numId m in
	let enf = mk_cnd (mk_enforce i aut) nId in
	let nenf = Basic.Not enf in
	let gam0 = mk_cnd (mk_gamma i aut m) 0 in
	let gam1 = mk_cnd (mk_gamma i aut m) 1 in
	Basic.make_and [(Basic.Imply (enf, gam1)); (Basic.Imply (gam1, enf)); (Basic.Imply (nenf, gam0)); (Basic.Imply (gam0, nenf))]
	
let mk_active (n: Network.t) (i: int) k (filter: bool) = 
	let auta = Network.automata n in
	let amodes = List.map (fun a -> (a, filter_aut_mode_distance a k filter)) auta in
	Basic.make_and (List.map (fun (a, mlist) -> Basic.make_and (List.map (fun m -> mk_active_mode a m i) mlist)) amodes)
	
let mk_mode_pair_mutex (aut: Hybrid.t) (m: Mode.t) (m1: Mode.t) (i: int) = 
  let nId = Mode.mode_numId m in
  let nId1 = Mode.mode_numId m1 in
  Basic.make_or( [Basic.Not(mk_cnd (mk_enforce i aut) nId);Basic.Not(mk_cnd (mk_enforce i aut) nId1)] )


let mk_mode_mutex (n: Network.t) (i: int) k (filter: bool) = 
	let auta = Network.automata n in
	let amodes = List.map (fun a -> (a, filter_aut_mode_distance a k filter)) auta in
	Basic.make_and (List.map (fun (a, mlist) -> 
				  Basic.make_and (List.map (fun m -> Basic.make_and (List.map (fun m1 -> if m != m1 then mk_mode_pair_mutex a m m1 i else Basic.True) mlist)) mlist)) amodes)
  
let compile_logic_formula (h : Network.t) (k : int) (path : comppath option) (precompute: bool) (filter: bool) =
  let init_clause = mk_init_network h in
  let list_of_steps = List.of_enum (0 -- (k-1)) in
  let steps = match precompute with
    | true -> Basic.make_and (List.map (fun x -> Basic.make_and [(mk_mode_mutex h x k filter);(mk_active h x k filter);(mk_maintain h x k filter);(trans_network_precomposed h x k filter)]) list_of_steps)
    | false -> Basic.make_and (List.map (fun x -> Basic.make_and [(mk_mode_mutex h x k filter);(mk_active h x k filter);(mk_maintain h x k filter);(trans_network h x k filter)]) list_of_steps) in
  let goal_clause = Basic.make_and [(mk_goal_network h k);(mk_mode_mutex h k k filter)] in
  let end_step = Basic.make_and [(mk_active h k k filter); (mk_maintain h k k filter)] in
  let smt_formula = Basic.make_and (List.flatten [[init_clause]; [steps]; [goal_clause]]) in
  [(Assert init_clause); (Assert steps); (Assert end_step); (Assert goal_clause)]

let compile (h : Network.t) (k : int) (path : comppath option) (precompute: bool) (filter: bool) =
  let logic_cmd = SetLogic QF_NRA_ODE in
  let (vardecl_cmds, assert_cmds) = compile_vardecl h k path precompute filter in
  let odedef = compile_ode_definition h k filter in
  let assert_formula = compile_logic_formula h k path precompute filter in
  List.flatten [[logic_cmd];vardecl_cmds; odedef; assert_cmds; assert_formula; [CheckSAT; Exit]]
