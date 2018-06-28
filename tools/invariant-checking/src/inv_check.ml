(*
 * Soonho Kong soonhok@cs.cmu.edu
 * Wei Chen weichen1@andrew.cmu.edu
 *)
open Type
open Type.Hybrid
open Type.Basic
open Type.Mode
open Type.Jump
open Type.Value
open Batteries
open IO
open Smt2_cmd
open Smt2

exception SMTException of string

type ode = Ode.t
type flows_annot = (int * ode list)  (** step, ode **)

(* add suffix to variables *)
let make_start = fun v -> v ^ "_0"
let make_end = fun v -> v ^ "_t"

let extract_flows q (modemap:Modemap.t) : flows_annot =
  let m = Map.find q modemap in
  (q, m.flows)

(** extract variable declaration **)
let varmap_to_list vardeclmap =
  Map.foldi
    (fun var value vardecls -> (var, value)::vardecls)
    vardeclmap
    []

let process_flow_single varmap modemap ginvs q =
  let m = Map.find q modemap in
  let flow_formula =
    let vardecls = varmap_to_list varmap in
    let vars = List.map (fun (name, _) -> name) vardecls in
    let time_var = String.join "_" ["time"; string_of_int q; ] in
    let flow_var = String.join "_" ["flow"; string_of_int q; ] in
    let ode_vars = List.filter (fun name -> name <> "time") vars in
    let ode_vars_0 = List.map make_start ode_vars in
    let ode_vars_t = List.map make_end ode_vars in
    Eq(Vec ode_vars_t (* ["x_1_t"; "y_1_t"] *),
                         Integral(0.0, time_var, ode_vars_0, flow_var)) in
  (* mode invariant *)
  let inv_formula = match m.invs_op with
      None -> Basic.True
    | Some invs -> Basic.make_and invs
  in
  let ginv_formula = Basic.make_and ginvs in
  let ginv_0 = Basic.subst_formula make_start ginv_formula in
  let ginv_t = Not(Basic.subst_formula make_end ginv_formula) in
  let invt_0 = Basic.subst_formula make_start inv_formula in
  let invt_t = Basic.subst_formula make_end inv_formula in
  Basic.make_and [flow_formula; ginv_0; ginv_t; invt_0; invt_t]

let process_jump_q_nq modemap q next_q =
  let mode = Map.find q modemap in
  let jumpmap = mode.jumpmap in
  let jump = Map.find next_q jumpmap in
  let guard' = Basic.subst_formula make_start jump.guard in
  let change' =
    Basic.subst_formula
      (fun v -> match String.ends_with v "'" with
        (** x' -> x_t **)
        |  true -> (String.rchop v) ^ "_t"

        (** x => x_0 **)
        | false -> v ^ "_0"
      )
      jump.change
  in
  Basic.make_and [guard'; change'; ]

(* J_q(x, x')*)
(* currently x = x_0, x' = x_t *)
let process_jump_single varmap modemap ginvs q =
  let m = Map.find q modemap in
  let jumpmap = m.jumpmap in
  let nqs = List.of_enum ( Map.keys jumpmap ) in
  let ginv_formula = Basic.make_and ginvs in
  let nq_formula =
    Basic.make_or
      (
        List.map (
            fun nq ->
            let f = process_jump_q_nq modemap q nq in
            let neg_inv = Not (Basic.subst_formula make_end ginv_formula) in
            Basic.make_and [f; neg_inv]
          )
          nqs
      )
  in
  Basic.make_and
    [Basic.subst_formula make_start ginv_formula;
     nq_formula;]


let compile_logic_formula h =
  let {init_id; init_formula; varmap; modemap; goals; ginvs} = h in
  let mode_clause =
    let modes = List.of_enum (Map.keys modemap) in
    Basic.make_or (
        List.map
          (fun q ->
           Basic.make_or [process_jump_single varmap modemap h.ginvs q;
                          process_flow_single varmap modemap h.ginvs q]
          )
          modes
      )
  in
  let init_inv_formula = Basic.make_and [init_formula; Not (Basic.make_and ginvs)] in
  let init_inv_formula' = Basic.subst_formula make_start init_inv_formula in
  Assert (Basic.make_or [init_inv_formula'; mode_clause])

let calc_num_of_mode (modemap : Modemap.t) =
  Enum.count (Map.keys modemap)

(** build a list of odes **)
let build_flow_annot_list h =
  let {varmap; modemap} = h in
  let num_of_modes = Enum.count (Map.keys modemap) in
  let list_of_modes = List.of_enum ( 1 -- num_of_modes ) in
  List.map (function q -> extract_flows q modemap) list_of_modes

(** build list of ode definition **)
let compile_ode_definition h =
  let flows = build_flow_annot_list h in
  List.map (fun (g, odes) -> DefineODE (("flow_" ^ (string_of_int g)), odes)) flows

(* generate variable definitions *)
let compile_vardecl h epi =
  let num_of_modes = Enum.count (Map.keys h.modemap) in
  let vardecls = varmap_to_list h.varmap in
  (* fileter unused time variable *)
  let (_, vardecls') = List.partition (fun (name, _) -> name = "time") vardecls in
  let time_vardecls =
    List.map
      (fun n ->
        ("time_" ^ (Int.to_string n), (Intv (0.0, epi), Value.Num 0.0)))
      (List.of_enum (1 -- num_of_modes))
  in
  (* generate variable declaration *)
  let vardecls'' =
    (* should be one linear *)
    List.flatten (
        List.map
          (function (k,v) ->
           [(make_start k, v); (make_end k, v)])
          vardecls')
  in
  let new_vardecls = List.flatten [vardecls''; time_vardecls;] in
  let (vardecl_cmds, assert_cmds_list) =
    List.split
      (List.map
         (function
          | (name, (Value.Intv (lb, ub), Value.Num p)) ->
             begin
               let prec_opt = if p > 0.0 then Some p else None in
               let bound_opt = Some (lb, ub) in
               (DeclareFun (name, REAL, prec_opt, bound_opt),
                [])
             end
           | _ -> raise (SMTException "We should only have interval here."))
         new_vardecls) in
  let assert_cmds = List.flatten assert_cmds_list in
  let org_vardecl_cmds = List.map
                           (function (var, (Value.Intv (lb, ub), Value.Num p)) ->
                                     begin
                                       let prec_opt = if p > 0.0 then Some p else None in
                                       let bound_opt = Some (lb, ub) in
                                       DeclareFun (var, REAL, prec_opt, bound_opt)
                                     end
                           | _ -> raise (Failure "Variable Declaration contains interval precision."))
                           vardecls' in
  (org_vardecl_cmds@vardecl_cmds, assert_cmds)

let compile (h : Hybrid.t) (epi : float) =
  let logic_cmd = SetLogic QF_NRA_ODE in
  let (vardecl_cmds, assert_cmds) = compile_vardecl h epi in

  (* todo *)
  let defineodes = compile_ode_definition h in
  let assert_formula = compile_logic_formula h in
  List.flatten
    [[logic_cmd];
     vardecl_cmds;
     defineodes;
     assert_cmds;
     [assert_formula];
     [CheckSAT; Exit];
    ]
