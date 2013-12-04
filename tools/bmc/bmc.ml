exception SMTException of string

open Batteries
open Smt2_cmd

type var = Vardecl.var
type varDecl = Vardecl.t
type formula = Basic.formula
type hybrid = Hybrid.t
type id = Mode.id
type mode = Mode.t
type jump = Mode.jump
type ode = Mode.ode
type flows = ode list
type flows_annot = (int * int * ode) list  (** step, mode, ode **)


let debug = false

let add_index (k : int) (q : id) (suffix : string) (s : string) : string =
  let str_step = string_of_int k in
  let str_mode_id = string_of_int q in
  (String.join "_" [s;
                       str_step;
                       str_mode_id;]) ^ suffix

let process_vardecls (vardecls : varDecl list) (num_of_modes : int) (k : int) (path : int list option) =
  let list_of_steps = List.of_enum ( 0 -- k ) in
  let list_of_modes = List.of_enum ( 1 -- num_of_modes ) in
  let k_q_pairs = match path with
      Some p -> List.combine list_of_steps p
    | None -> List.cartesian_product list_of_steps list_of_modes
  in
  List.flatten
    (List.flatten
       (List.map
          (fun (var, value) ->
            (List.map
               (fun (k, q) -> [(add_index k q "_t" var, value);
                            (add_index k q "_0" var, value)])
               k_q_pairs
            )
          )
          vardecls))

let generate_redundant_cond (all_vars : var Set.t) (f : formula) =
  let appeared_vars = Basic.collect_vars_in_formula f in
  let not_appeared_vars = Set.diff all_vars appeared_vars in
  List.map (fun x -> Basic.Eq (Basic.Var x, Basic.Var x)) (Set.elements not_appeared_vars)

let process_init (q : id) (init : formula) (all_vars : var Set.t) : formula =
  let redundant_cond = generate_redundant_cond all_vars init in
  let init' = Basic.make_and (init::redundant_cond) in
  let init'' = Basic.subst_formula (add_index 0 q "_0") init' in
  let mode_cond = Basic.Eq (Basic.Var "mode_0", Basic.Num (float_of_int q)) in
  Basic.make_and [init''; mode_cond]

let process_flow (k : int) (q : id) (m : mode) : (flows_annot * formula) =
  let flows_annot =
    List.map
      (fun ode ->
        let substituted_ode = Ode.subst (add_index k q "") ode
        in (k, q, substituted_ode))
      (Mode.flows m)
  in
  (* TODO: Add conditions for unappeared variables *)
  let inv_formula = match (Mode.invs_op m) with
      None -> Basic.True
    | Some invs ->
      let invt_conds =
        List.map
          (fun invt_f ->
            Basic.make_and
              [Basic.subst_formula (add_index k q "_0") invt_f;
               Basic.subst_formula (add_index k q "_t") invt_f;
               Basic.ForallT (Basic.subst_formula (add_index k q "_t") invt_f);])
          invs
      in
      Basic.make_and invt_conds
  in
  (flows_annot, inv_formula)

let process_jump (jump) (k : int) (next_k : int) (q : id) (next_q : id) (all_vars : var Set.t)
    : formula =
  let gurad' = Basic.subst_formula (add_index k q "_t") (Jump.guard jump) in
  let change'' =
    let change = Jump.change jump in
    let redundant_cond = generate_redundant_cond all_vars change in
    let change' = Basic.make_and (change::redundant_cond) in
    Basic.subst_formula
      (fun v -> match String.ends_with v "'" with
        (** x' => x_{k+1}_q_0 **)
      |  true -> add_index (k+1) next_q "_0" (String.rchop v)
        (** x => x_k_q_t **)
      | false -> add_index k q "_t" v)
      change'
  in
  Basic.make_and [gurad'; change'']

let process_goals (hm : Hybrid.t) (k : int) (goals : (int * formula) list) (all_vars : var Set.t) =
  let goal_formulas =
    List.map
      (fun (q, goal_f) ->
        let goal_f' =
          let redundant_cond = generate_redundant_cond all_vars goal_f in
          Basic.make_and (goal_f::redundant_cond)
        in
        let mode_cond = Basic.Eq (Basic.Var ("mode_" ^ (string_of_int k)), Basic.Num (float_of_int q)) in
        Basic.make_and [Basic.subst_formula (add_index k q "_t") goal_f';
                        mode_cond;]
      )
      goals
  in
  Basic.make_or goal_formulas

let varmap_to_list vardeclmap =
  Map.foldi
    (fun var value vardecls -> (var, value)::vardecls)
    vardeclmap
    []

let make_mode_cond k q =
  Basic.Eq (Basic.Var ("mode_" ^ (string_of_int k)), Basic.Num (float_of_int q))
let trans modemap init_id (k : int) (next_k : int) (q : id) (next_q : id) (all_vars : var Set.t)
    : (flows_annot * formula)
    =
  let m = Modemap.find q modemap in
  let jump_result = process_jump (Jumpmap.find next_q (Mode.jumpmap m)) k next_k q next_q all_vars in
  let (flow_k_next_ode, flow_k_next) =
    process_flow (next_k) (next_q) (Modemap.find next_q modemap) in
  let mode_cond = make_mode_cond k q in
  let mode_cond_n = make_mode_cond next_k next_q in
  (flow_k_next_ode,
   Basic.Imply (mode_cond,
                Basic.make_and [mode_cond_n; jump_result; flow_k_next]))

let transform modemap init_id (k : int) (next_k : int) (edge_op : (int * int) option) (all_vars : var Set.t)
    : (flows_annot * formula)
    =
  let num_of_modes : int = Enum.count (Map.keys modemap) in
  let all_modes : int list = List.of_enum (1 -- num_of_modes) in
  let candidate_pairs : (id * Jump.id) list =
    List.flatten
      (List.map
         (fun mode_id ->
           let m = Modemap.find mode_id modemap in
           Map.fold
             (fun jump result ->
               (mode_id, Jump.target jump) :: result)
             (Mode.jumpmap m)
             [])
         all_modes
      ) in
  let candidate_pairs' = match edge_op with
      Some (i, j) ->
        if List.mem (i, j) candidate_pairs then
          [(i, j)]
        else
          let msg =
            Printf.sprintf
              "%d-th jump from mode %d to %d is not possible in the given model."
              k i j
          in
          raise (SMTException msg)
    | None -> candidate_pairs in
  let trans_result_list : (flows_annot * formula) list =
    List.map
      (fun (q, next_q) ->
        trans modemap init_id k next_k q next_q all_vars
      )
      candidate_pairs'
  in
  let (flow_list, formula_list) = List.split trans_result_list in
  (List.flatten flow_list, Basic.make_and formula_list)

let reach (k : int) (hm : Hybrid.t) (path : int list option):
    (varDecl list * flows_annot * formula * Value.t)
    =
  let init_id = Hybrid.init_id hm in
  let modemap = Hybrid.modemap hm in
  let num_of_modes = Enum.count (Map.keys modemap) in
  let vardecls = varmap_to_list (Hybrid.varmap hm) in
  let all_vars =
    let (varlist, _) = List.split vardecls in
    Set.remove "time" (Set.of_list varlist)
  in
  let (time_var_l, vardecls') =
    List.partition (fun (name, _) -> name = "time") vardecls in
  let time_intv =
    match time_var_l with
      (_, intv)::[] -> intv
    | _ -> raise (SMTException "time should be defined once and only once.") in
  let vardecls'' = process_vardecls vardecls' num_of_modes k path in
  let init_result = process_init init_id (Hybrid.init_formula hm) all_vars in
  let (flow_0_ode, flow_0) = process_flow 0 init_id (Modemap.find init_id modemap) in
  let k_list : int list = List.of_enum (0 --^ k) in
  let trans_result : (flows_annot * formula) list =
    match path with
      Some p ->
        let edges : (int * int) list = List.combine (List.take (List.length p - 1) p) (List.drop 1 p) in
        List.map2 (fun k edge -> transform modemap init_id k (k + 1) (Some edge) all_vars) k_list edges
    | None ->
      List.map (fun k -> transform modemap init_id k (k + 1) None all_vars) k_list
  in
  let (trans_flows, trans_formula) = List.split trans_result in
  let goal_formula = process_goals hm k (Hybrid.goals hm) all_vars in
  (vardecls'',
   List.flatten (flow_0_ode::trans_flows),
   Basic.make_and
     (List.flatten
        [[init_result];
         [flow_0];
         trans_formula;
         [goal_formula]]),
   time_intv
  )

let make_smt2
    (vardecls : varDecl list)
    (flows_annot : flows_annot)
    (formula : formula)
    (time_intv : Value.t)
    (k : int)
    : Smt2.t
    =
  let make_lb name v = Basic.Le (Basic.Num v,  Basic.Var name) in
  let make_ub name v = Basic.Le (Basic.Var name, Basic.Num v ) in
  let logic_cmd = SetLogic QF_NRA_ODE in
  let num_of_modes = List.max (List.map (fun (_, q, _) -> q) flows_annot) in
  let odes =
    let ode_vars_list : (var * var Set.t) list =
      List.map (fun (_, _, ode) -> Ode.collect_vars ode) flows_annot
    in
    let groupid_map : (var, int Uref.uref) Map.t =
      snd (List.fold_left (fun (n, m) (v, s) ->
                           let m' = Map.add v (Uref.uref n) m in
                           let n' = n + 1 in
                           (n', m')
                          )
                          (1, Map.empty)
                          ode_vars_list) in
    let _ = List.iter (fun (v1, s) ->
                       Set.iter (fun v2 -> Uref.unite
                                          (Map.find v1 groupid_map)
                                          (Map.find v2 groupid_map))
                                s
                      )
                      ode_vars_list in
    List.map
      (fun (k, q, (x, e)) ->
       let group_num  = k * num_of_modes + q in
       let sgroup_num = Uref.uget (Map.find x groupid_map) in
       (group_num, sgroup_num, x, e)
      )
      flows_annot in
  let defineodes = List.map (fun (g, sg, x, e) -> DefineODE (g, g, x, e)) odes in
  let diff_groups  = List.unique (List.map (fun (n, _, _, _) -> n) odes) in
  let diff_sgroups = List.unique (List.map (fun (_, n, _, _) -> n) odes) in
  let grouped_odes =
    let sorted_odes = List.sort (fun (g1, sg1, _, _) (g2, sg2, _, _)
                                 -> Int.compare g1 g2) odes
    in List.group_consecutive (fun (g1, sg1, _, _) (g2, sg2, _, _)
                               -> g1 = g2)
                              sorted_odes in
  let time_vardecls =
    List.map
      (fun n -> ("time_" ^ (Int.to_string n), time_intv))
      diff_groups in
  (* let time_var_constrs =  *)
  (*   List.map (fun odegroup ->  *)
  let mode_vardecls =
    List.map
      (fun n -> ("mode_" ^ (Int.to_string n), Value.Intv (1.0, float_of_int num_of_modes)))
      (List.of_enum (0 -- k))
  in
  let new_vardecls = List.flatten [vardecls;time_vardecls;mode_vardecls] in
  let (vardecl_cmds, assert_cmds_list) =
    List.split
      (List.map
         (function
         | (name, Value.Intv (lb, ub)) ->
           (DeclareFun name,
            [Assert (make_lb name lb);
             Assert (make_ub name ub)])
         | _ -> raise (SMTException "We should only have interval here."))
         new_vardecls) in
  let assert_cmds = List.flatten assert_cmds_list in
  let assert_formula = Assert formula in
  let defineodes' =
    List.unique
      ~eq:
          (fun cmd1 cmd2 -> match (cmd1, cmd2) with
          | (DefineODE (_, n1, x1, e1), DefineODE (_, n2, x2, e2)) -> ((n1 = n2) && (x1 = x2))
          | _ -> false)
      defineodes
  in
  List.flatten
    [[logic_cmd];
     vardecl_cmds;
     defineodes';
     assert_cmds;
     [assert_formula];
     [CheckSAT; Exit];
    ]
