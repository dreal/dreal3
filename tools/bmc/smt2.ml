(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open BatPervasives
open Smt_cmd

type varDecl = Dr.vardecl
type formula = Dr.formula
type hybrid = Hybrid.t
type dr = Dr.t
type id = Mode.id
type mode = Mode.t
type jump = Mode.jump
type ode = Mode.ode
type flow = ode list

type smt_cmd = Smt_cmd.t
type t = smt_cmd list

let add_index (k : int) (q : id) (suffix : string) (s : string) : string =
  let str_step = string_of_int k in
  let str_mode_id = string_of_int q in
  (BatString.join "_" [s;
                      str_step;
                      str_mode_id;]) ^ suffix

let process_init (q : id) (i : formula) : formula =
  Dr.subst_formula (add_index 0 q "_0") i

let process_flow (k : int) (q : id) (m : mode) : (flow * formula) =
  let (id, inv_op, flow, jump) = m in
  let flow' = List.map (fun ode -> Dr.subst_ode (add_index k q "") ode) flow in
  let f = match inv_op with
      None -> Dr.True
    | Some invt ->
      Dr.make_and
        (BatList.map
           (fun invt_f -> Dr.subst_formula (add_index k q "_t") invt_f)
           invt)
  in
  (flow', f)

let process_jump (jump) (q : id) (next_q : id) (k : int) (next_k : int)
    : formula =
  let (gurad, _, change) = jump in
  let gurad' = Dr.subst_formula (add_index k q "_t") gurad in
  (* TODO: Need to add equality relations for the unmodified variables *)
  let change' =
    Dr.subst_formula
      (fun v -> match BatString.ends_with v "'" with
        true -> add_index (k+1) next_q "_0" (BatString.rchop v)
      | false -> add_index k q "_t" v
      )
      change in
  Dr.make_and [gurad'; change']

let trans (hm) (q : id) (next_q : id) (k : int) (next_k : int)
    : (flow * formula)
    =
  let (vardecls, _, modemap, (init_id, init_formula), goal) = hm in
  let (id, inv, flow, jm) = (Modemap.find q modemap) in
  let jump_result = process_jump (Jumpmap.find next_q jm) q next_q k next_k in
  let (flow_k_next_ode, flow_k_next) =
    process_flow (next_k) (next_q) (Modemap.find init_id modemap) in
  (flow_k_next_ode,
   Dr.make_and [jump_result; flow_k_next])

let transform (hm) (k : int) (next_k : int)
    : (flow * formula)
    =
  let (vardecls, _, modemap, (init_id, init_formula), goal) = hm in
  let num_of_modes = BatEnum.count (BatMap.keys modemap) in
  let next_q_list =
    BatList.unique
      (BatMap.foldi
         (fun id mode result ->
           let (id, inv, flow, jm) = mode in
           BatMap.foldi
             (fun id jump result ->
               let (_, target_id, _) = jump in
               target_id :: result)
             jm
             [])
         modemap
         [])
  in
  let candidate_pairs =
    BatList.filter
      (fun (x, y) -> (x != y))
      (BatList.cartesian_product
         (BatList.of_enum (1 -- num_of_modes))
         next_q_list)
  in
  let trans_result_list : (flow * formula) list =
    List.map
      (fun (q, next_q) ->
        trans hm q next_q k next_k
      )
      candidate_pairs
  in
  let (flow_list, formula_list) = BatList.split trans_result_list in
  (BatList.concat flow_list, Dr.make_or formula_list)

let process_goals (hm : Hybrid.t) (k : int) (goals : (int * formula) list) =
  let goal_formulas =
    BatList.map
      (fun (q, f) ->
        Dr.subst_formula (add_index k q "_t") f)
      goals
  in
  Dr.make_or goal_formulas

let process_vardecls (hm : hybrid) (k : int) =
  let (vardeclmap, env, modemap, init, goals) = hm in
  let num_of_modes = BatEnum.count (BatMap.keys modemap) in
  (* 1. Translate Variable Declarations *)
  let new_vardecls =
    BatMap.foldi
      (fun var value vardecls -> (var, value)::vardecls)
      vardeclmap
      [] in
  let new_vardecls' =
    List.concat
      (List.map
         (fun (var, value) ->
           let t1 =
             BatList.cartesian_product
               (BatList.of_enum ( 1 -- k ))
               (BatList.of_enum ( 0 --^ num_of_modes ))
           in
           List.concat
             (List.map
                (fun (k, q) -> [(add_index k q "_t" var, value);
                             (add_index k q "_0" var, value)])
                t1
             )
         )
         new_vardecls)
  in
  new_vardecls'

let reach (k : int) (hm : Hybrid.t) :
    (varDecl list * flow * formula)
    =
  let (vardeclmap, _, modemap, (init_id, init_formula), goals) = hm in
  let vardecls = process_vardecls hm k in
  let init_result = process_init init_id init_formula in
  let (flow_0_ode, flow_0) = process_flow 0 init_id (Modemap.find init_id modemap) in
  let k_list : int list = BatList.of_enum (0 --^ k) in
  let trans_result : (flow * formula) list =
    List.map (fun k -> transform hm k (k + 1)) k_list
  in
  let (trans_flows, trans_formula) = BatList.split trans_result in
  let goal_formula = process_goals hm k goals in
  (vardecls,
   BatList.concat (flow_0_ode::trans_flows),
   Dr.make_and
     (BatList.concat
        [[init_result];
         [flow_0];
         trans_formula;
         [goal_formula]])
  )

let make_smt2
    (vardecls : varDecl list)
    (flow : flow)
    (formula : formula)
    : t
    =
  let make_lb name v = Dr.Le (Dr.Const v,  Dr.Var name) in
  let make_ub name v = Dr.Le (Dr.Var name, Dr.Const v ) in
  let logic_cmd = SetLogic QF_NRA_ODE in
  let (vardecl_cmds, assert_cmds_list) =
    BatList.split
      (BatList.map
         (function
         | (name, Value.Intv (lb, ub)) ->
           (DeclareFun name,
            [Assert (make_lb name lb);
             Assert (make_ub name ub)])
         | _ -> raise Not_found)
         vardecls) in
  let defineodes =
    BatList.map
      (fun (x, e) ->
        DefineODE (x, e)
      )
      flow
  in
  let assert_cmds = BatList.concat assert_cmds_list in
  let assert_formula = Assert formula in
  BatList.concat
  [[logic_cmd];
   vardecl_cmds;
   defineodes;
   assert_cmds;
   [assert_formula]]

(* (flow * formula) => smt2 *)
let print out smt =
  BatList.print
    (~first: "")
    (~sep:"\n")
    (~last:"\n")
    Smt_cmd.print
    out
    smt

