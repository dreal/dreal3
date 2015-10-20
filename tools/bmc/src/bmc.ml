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
type flows_annot = (int * ode list)  (** step, ode **)

let global_vars = ref []

(** rename variable to related name in each step **)
let make_variable k suffix (s: string) : string =
  let str_step = string_of_int k in
  (String.join "_" [s; str_step;]) ^ suffix

(* assert for mode *)
let make_mode_cond ~k ~q =
  Basic.Eq (Basic.Var ("mode_" ^ (string_of_int k)), Basic.Num (float_of_int q))

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
    let ode_vars' = List.sort String.compare ode_vars in
    let ode_vars_0 = List.map (make_variable k "_0") ode_vars' in
    let ode_vars_t = List.map (make_variable k "_t") ode_vars' in
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
  let const_ode_ctrs =
    let const_odes = List.filter_map
                       (fun (var_name, rhs) ->
                         try
                           Some (var_name, Basic.real_eval Map.empty rhs)
                         with _ -> None)
                       (Mode.flows m)
    in
    List.map
      (fun (var_name, v) ->
        let tau_k_0 = Basic.Var (make_variable k "_0" var_name) in
        let tau_k_t = Basic.Var (make_variable k "_t" var_name) in
        Basic.Eq (tau_k_t, Basic.Add [tau_k_0;
                                      Basic.Mul [Basic.Num v;
                                                 Basic.Var time_var]]))
      const_odes
  in
  Basic.make_and ([mode_formula; flow_formula; inv_formula]@const_ode_ctrs)

(** source mode & flow & mode invariant **)
let process_flow_pruned ~k ~q (varmap : Vardeclmap.t) (modemap:Modemap.t) (relevant : Relevantvariables.t list option) : Basic.formula =
  let m = Map.find q modemap in
  let mode_formula = make_mode_cond ~k ~q in
  let not_mode_formula = Basic.make_and(
                             List.map (fun nm -> if nm = q then
                                               Basic.True
                                             else
                                               Basic.Not (make_mode_cond k nm)
                                  )
                                  (List.of_enum (Map.keys modemap))) in
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
    let ode_vars' = List.sort String.compare ode_vars in
    let ode_vars_0 = List.map (make_variable k "_0") ode_vars' in
    let ode_vars_t = List.map (make_variable k "_t") ode_vars' in
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
                             List.map (fun nm -> if nm = next_q then
                                               Basic.True
                                             else
                                               Basic.Not (make_mode_cond (k+1) nm)
                                  )
                                  (List.of_enum (Map.keys modemap))) in
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
           match (Set.mem name used, precision) with
           | (false, 0.0) -> Basic.Eq (Basic.Var (make_variable k "_t" name), Basic.Var (make_variable (k+1) "_0" name))
           | (false, _) -> Basic.Eqp (Basic.Var (make_variable k "_t" name), Basic.Var (make_variable (k+1) "_0" name), precision)
           | (true, _) -> Basic.True
        )
        changevars
    )
  in
  Basic.make_and [gurad'; change'; change''; mode_formula]


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
         let jump_for_q_nq  = Basic.make_or (List.map
                                               (fun nq ->
                                                process_jump_pruned modemap q nq relevant step
                                               )
                                               list_of_possible_nq)
         in
         Basic.make_and [flow_for_q; jump_for_q_nq]
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
                 (mode : int option)
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

let final_flow_pruned varmap modemap mode k relevant =
  let list_of_modes = match mode with
      Some n -> [n]
    | None ->
       let num_modes = Enum.count (Map.keys modemap) in
       List.of_enum ( 1 -- num_modes )
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
  let final_flow_clause = final_flow_pruned varmap modemap None k relevant in
  let goal_clause = process_goals k goals in
  let smt_formula = Basic.make_and (List.flatten [[init_clause]; step_clauses; [final_flow_clause];  [goal_clause]]) in
  Assert smt_formula

let compile_logic_formula (h : Hybrid.t) (k : int) (path : int list option) =
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
let compile_vardecl (h : Hybrid.t) (k : int) (path : (int list) option) =
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

let compile (h : Hybrid.t) (k : int) (path : (int list) option) =
  let logic_cmd = SetLogic QF_NRA_ODE in
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
    ]

(** Enumerate all possible paths of length k in Hybrid Model h *)
let pathgen (h : Hybrid.t) (k : int) : int list list =
  let init_mode_id = h.init_id in
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
