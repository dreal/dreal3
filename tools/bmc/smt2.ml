(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open BatPervasives
open Smt_cmd

exception SMTException of string

type varDecl = Dr.vardecl
type formula = Dr.formula
type hybrid = Hybrid.t
type dr = Dr.t
type id = Mode.id
type mode = Mode.t
type jump = Mode.jump
type ode = Mode.ode
type flow = ode list
type flow_annot = (int * int * ode) list

type smt_cmd = Smt_cmd.t
type t = smt_cmd list

let debug = false

let add_index (k : int) (q : id) (suffix : string) (s : string) : string =
  let str_step = string_of_int k in
  let str_mode_id = string_of_int q in
  (BatString.join "_" [s;
                       str_step;
                       str_mode_id;]) ^ suffix

let process_init (q : id) (init : formula) : formula =
  Dr.subst_formula (add_index 0 q "_0") init

let process_flow (k : int) (q : id) (m : mode) : (flow_annot * formula) =
  let (_, inv_op, flow, _) = m in
  let flow' = List.map (fun ode -> (k, q, Dr.subst_ode (add_index k q "") ode)) flow in
  let f = match inv_op with
      None -> Dr.True
    | Some invs ->
      Dr.make_and
        (BatList.map
           (fun invt_f ->
             Dr.make_and
               [Dr.subst_formula (add_index k q "_t") invt_f;
                Dr.ForallT (Dr.subst_formula (add_index k q "_t") invt_f);
                Dr.subst_formula (add_index k q "_0") invt_f])
           invs)
  in
  (flow', f)

let process_jump (jump) (k : int) (next_k : int) (q : id) (next_q : id)
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

let trans modemap init_id (k : int) (next_k : int) (q : id) (next_q : id)
    : (flow_annot * formula)
    =
  let (_, _, _, jm) = (Modemap.find q modemap) in
  let jump_result = process_jump (Jumpmap.find next_q jm) k next_k q next_q in
  let (flow_k_next_ode, flow_k_next) =
    process_flow (next_k) (next_q) (Modemap.find next_q modemap) in
  (flow_k_next_ode,
   Dr.make_and [jump_result; flow_k_next])

let transform modemap init_id (k : int) (next_k : int) (edge_op : (int * int) option)
    : (flow_annot * formula)
    =
  let num_of_modes : int = BatEnum.count (BatMap.keys modemap) in
  let all_modes : int list = BatList.of_enum (1 -- num_of_modes) in
  let candidate_pairs : (id * Jump.id) list =
    BatList.concat
      (BatList.map
         (fun mode_id ->
           let (_, _, _, jm) = Modemap.find mode_id modemap in
           BatMap.fold
             (fun jump result ->
               let (_, target_id, _) = jump in
               (mode_id, target_id) :: result)
             jm
             [])
         all_modes
      ) in
  let candidate_pairs' = match edge_op with
      Some edge ->
        if List.mem edge candidate_pairs then
          [edge]
        else
          raise (SMTException "Specified Edge is not possible.")
    | None -> candidate_pairs in
  let trans_result_list : (flow_annot * formula) list =
    List.map
      (fun (q, next_q) ->
        trans modemap init_id k next_k q next_q
      )
      candidate_pairs'
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

let varmap_to_list vardeclmap =
  BatMap.foldi
    (fun var value vardecls -> (var, value)::vardecls)
    vardeclmap
    []

let process_vardecls (vardecls) (num_of_modes : int) (k : int) =
  List.concat
    (List.map
       (fun (var, value) ->
         let t1 =
           BatList.cartesian_product
             (BatList.of_enum ( 0 -- k ))
             (BatList.of_enum ( 1 -- num_of_modes ))
         in
         List.concat
           (List.map
              (fun (k, q) -> [(add_index k q "_t" var, value);
                           (add_index k q "_0" var, value)])
              t1
           )
       )
       vardecls)

let reach (k : int) (hm : Hybrid.t) (path : int list option):
    (varDecl list * flow_annot * formula * Value.t)
    =
  let (vardeclmap, _, modemap, (init_id, init_formula), goals) = hm in
  let num_of_modes = BatEnum.count (BatMap.keys modemap) in
  let vardecls = varmap_to_list vardeclmap in
  let (time_var_l, vardecls') =
    BatList.partition (fun (name, _) -> name = "time") vardecls in
  let time_intv =
    match time_var_l with
      (_, intv)::[] -> intv
    | _ -> raise (SMTException "time should be defined once and only once.") in
  let vardecls'' = process_vardecls vardecls' num_of_modes k in
  let init_result = process_init init_id init_formula in
  let (flow_0_ode, flow_0) = process_flow 0 init_id (Modemap.find init_id modemap) in
  let k_list : int list = BatList.of_enum (0 --^ k) in
  let trans_result : (flow_annot * formula) list =
    match path with
      Some p ->
        let edges : (int * int) list = BatList.combine (BatList.take (List.length p - 1) p) (BatList.drop 1 p) in
        List.map2 (fun k edge -> transform modemap init_id k (k + 1) (Some edge)) k_list edges
    | None ->
      List.map (fun k -> transform modemap init_id k (k + 1) None) k_list
  in
  let (trans_flows, trans_formula) = BatList.split trans_result in
  let goal_formula = process_goals hm k goals in
  (vardecls'',
   BatList.concat (flow_0_ode::trans_flows),
   Dr.make_and
     (BatList.concat
        [[init_result];
         [flow_0];
         trans_formula;
         [goal_formula]]),
   time_intv
  )

let make_smt2
    (vardecls : varDecl list)
    (flow_annot : flow_annot)
    (formula : formula)
    (time_intv : Value.t)
    : t
    =
  let make_lb name v = Dr.Le (Dr.Const v,  Dr.Var name) in
  let make_ub name v = Dr.Le (Dr.Var name, Dr.Const v ) in
  let logic_cmd = SetLogic QF_NRA_ODE in
  let num_of_modes = BatList.max (BatList.map (fun (_, q, _) -> q) flow_annot) in
  let defineodes =
    BatList.map
      (fun (k, q, (x, e)) ->
        let group_num = k * num_of_modes + q in
        DefineODE (group_num, x, e)
      )
      flow_annot
  in
  let diff_groups =
    BatList.unique
      (BatList.map
         (function
         | DefineODE (n, _, _) -> n
         | _ -> raise (SMTException "only contains DefineODE"))
         defineodes)
  in
  let time_vardecls =
    BatList.map
      (fun n -> ("time_" ^ (BatInt.to_string n), time_intv))
      diff_groups
  in
  let new_vardecls = vardecls@time_vardecls in
  let (vardecl_cmds, assert_cmds_list) =
    BatList.split
      (BatList.map
         (function
         | (name, Value.Intv (lb, ub)) ->
           (DeclareFun name,
            [Assert (make_lb name lb);
             Assert (make_ub name ub)])
         | _ -> raise (SMTException "We should only have interval here."))
         new_vardecls) in
  let assert_cmds = BatList.concat assert_cmds_list in
  let assert_formula = Assert formula in
  let defineodes' =
    BatList.unique
      ~cmp:
          (fun cmd1 cmd2 -> match (cmd1, cmd2) with
          | (DefineODE (n1, x1, e1), DefineODE (n2, x2, e2)) -> ((n1 = n2) && (x1 = x2))
          | _ -> false)
      defineodes
  in
  BatList.concat
    [[logic_cmd];
     vardecl_cmds;
     defineodes';
     assert_cmds;
     [assert_formula];
     [CheckSAT; Exit];
    ]

let print out smt =
  BatList.print
    ~first: ""
    ~sep:"\n"
    ~last:"\n"
    Smt_cmd.print
    out
    smt
