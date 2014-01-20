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

exception SMTException of string

type ode = Ode.t
type flows_annot = (int * ode list)  (** step, ode **)

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
  let flow_formula =
    let vardecls = varmap_to_list varmap in
    let vars = List.map (fun (name, _) -> name) vardecls in
    let time_var = (make_variable k "" "time") in
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
               Basic.ForallT (Basic.subst_formula (make_variable k "_t") invt_f);])
          invs
      in
      (* mode_k = q && inva_q(x_i, x_i_t) *)
      (* TODO add flow constraint here *)
      Basic.make_and (mode_formula::flow_formula::invt_conds)
  in
  inv_formula

(** transition change **)
let process_jump (modemap : Modemap.t) (q : Mode.id) (next_q : Mode.id) k : Basic.formula =
  let mode = Map.find q modemap in
  let jumpmap = mode.jumpmap in
  let jump = Map.find next_q jumpmap in
  let mode_formula = make_mode_cond ~k:(k+1) ~q:next_q in
  let gurad' = Basic.subst_formula (make_variable k "_t") jump.guard in
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
  Basic.make_and [gurad'; change'; mode_formula]


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

(** generate logic formular for each step 0...k **)
let process_step (varmap : Vardeclmap.t) (modemap : Modemap.t) (step:int) : Basic.formula =
  let num_of_modes = Enum.count (Map.keys modemap) in
  let list_of_modes = List.of_enum ( 1 -- num_of_modes ) in
  let jump_flow_part =
    List.map
      (fun q ->
        try
          let flow_for_q = process_flow ~k:step ~q varmap modemap in
          let mode_q = Map.find q modemap in
          let jumpmap_q = mode_q.jumpmap in
          let list_of_nq = List.of_enum (Map.keys jumpmap_q) in
          let jump_for_q_nq  = Basic.make_or (List.map
                                                (fun nq ->
                                                  process_jump modemap q nq step
                                                )
                                                list_of_nq)
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


(* compile Hybrid automata into SMT formulas *)
let compile_logic_formula (h : Hybrid.t) (k : int) =
  let {init_id; init_formula; varmap; modemap; goals} = h in
  let init_clause = process_init ~init_id ~init_formula in
  let step_clauses = List.map (process_step varmap modemap) (List.of_enum (0 -- (k-1))) in
  let goal_clause = process_goals k goals in
  let smt_formula = Basic.make_and (List.flatten [[init_clause]; step_clauses; [goal_clause]]) in
  Assert smt_formula

(** variable declaration & range constraint **)
let compile_vardecl (h : Hybrid.t) (k : int) =
  let {modemap} = h in
  let num_of_modes = Enum.count (Map.keys modemap) in
  let vardecls = varmap_to_list h.varmap in
  let (time_var_l, vardecls') = List.partition (fun (name, _) -> name = "time") vardecls in

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
             (DeclareFun name,
              [make_lb name lb;
               make_ub name ub])
           | _ -> raise (SMTException "We should only have interval here."))
         new_vardecls) in
  let assert_cmds = List.flatten assert_cmds_list in
  (vardecl_cmds, assert_cmds)

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

let compile (h : Hybrid.t) (k : int) =
  let logic_cmd = SetLogic QF_NRA_ODE in
  let (vardecl_cmds, assert_cmds) = compile_vardecl h k in
  let defineodes = compile_ode_definition h k in
  let assert_formula = compile_logic_formula h k in
  List.flatten
    [[logic_cmd];
     vardecl_cmds;
     defineodes;
     assert_cmds;
     [assert_formula];
     [CheckSAT; Exit];
    ]
