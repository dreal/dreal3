(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open BatPervasives

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
    | Some invt -> Dr.subst_formula (add_index k q "_t") invt
  in
  (flow', f)

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

let trans (hm) (q : id) (next_q : id) (k : int) (next_k : int)
    : (flow * formula)
    =
  let jump_result = process_jump (Jumpmap.find q jm) q next_q k next_k in
  let (flow_k_next_ode, flow_k_next) =
    process_flow (next_k) (next_q) (Modemap.find init_id modemap) in
  (flow_k_next_ode,
   Dr.make_and [jump_result; flow_k_next])

let process_jump (jump) (q : id) (next_q : id) (k : int) (next_k : int)
    : formula =
  let (gurad, _, change) = jump in
  let gurad' = Dr.subst_formula (add_index k q "_t") gurad in
  (* TODO: Need to add equality relations for the unmodified variables *)
  let change' =
    Dr.subst_formula
      (fun v -> match BatString.ends_with v "'" with
        true -> add_index (k+1) next_q "_0" v
      | false -> add_index k q "_t" v
      )
      change in
  Dr.make_and [gurad'; change']

let process_goal (hm : Hybrid.t) (k : int) (goal : formula) =
  let num_of_modes = BatEnum.count (BatMap.keys modemap) in
  let pairs : (int * int) =
    BatList.cartesian_product
      [k]
      (BatList.of_enum (1 -- num_of_modes))
  in
  let goal_formulas =
    BatList.map
      (fun (k, q) ->
        Dr.subst_formula (add_index k q "_t") goal)
      pairs
  in
  Dr.make_or goal_formulas

let reach (k : int) (hm : Hybrid.t) :
    (flow * formula)
    =
  let (vardeclmap, _, modemap, (init_id, init_formula), goals) = hm in
  let init_result = process_init init_id init_formula in
  let (flow_0_ode, flow_0) = process_flow 0 init_id (Modemap.find init_id modemap) in
  let k_list : int list = BatList.of_enum (0 --^ k) in
  let trans_result : (flow * formula) list =
    List.map (fun k -> transform hm k (k + 1)) k_list
  in
  let (trans_flows, trans_formula) = BatList.split trans_result in
  let trans_flow = BatList.concat trans_flow in
  let goal_formula = process_goal hm k goal in
  ( BatList.concat [flow_0_ode; trans_flows],
    Dr.make_and
      [init_result;
       flow_0;
       trans_formula;
       goal_formula]
  )

(* (flow * formula) => smt2 *)
let print out smt =
  BatList.print
    (~first: "")
    (~sep:"\n")
    (~last:"\n")
    Smt_cmd.print
    out
    smt

