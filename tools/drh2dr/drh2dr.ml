(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type varDecl = Dr.vardecl
type formula = Dr.formula
type hybrid = Hybrid.t
type dr = Dr.t
type id = Mode.id
type mode = Mode.t
type jump = Mode.jump
type ode = Mode.ode
type flow = ode list

let add_index (k : int) (q : id) (t : bool) (s : string) : string =
  let str_step = string_of_int k in
  let str_mode_id = string_of_int q in
  let suffix = if t then "t" else "0" in
  BatString.join "_" [s;
                      str_step;
                      str_mode_id;
                      suffix]

let process_init (q : id) (i : formula) : formula =
  Dr.subst_formula (add_index 0 q false) i

let process_flow (k : int) (q : id) (m : mode) : (flow * formula) =
  let (id, macro, inv, flow, jump) = m in
  (flow, Dr.True)

let process_jump (jump) (q : id) (next_q : id) (k : int) (next_k : int)
    : formula =
  let (cond, _, change) = jump in
  (* TODO: replace this ID function *)
  let cond' = Dr.subst_formula (fun x -> x) cond in
  let change' =
    Dr.subst_formula
      (* TODO: replace this function *)
      (fun v -> match BatString.ends_with v "'" with
        true -> v
      | false -> v
      )
      change in
  (* TODO: Need to check the following *)
  Dr.Or [Dr.Not cond'; change']

let rec reach_kq (k : int) (q : id) (hm : hybrid) : (flow * formula)
    = let (vardecls, modemap, (init_id, init_formula), goal) = hm in
      match (k, q) with
      | (0, init_id) ->
        begin
          (* Base Case where q = init mode *)
          let init_q0 : formula = process_init init_id init_formula in
          let (odes, f) = process_flow k q (Modemap.find q modemap) in
          (odes, Dr.And [init_q0; f])
        end
      | (0, _) ->
        begin
          (* If q is non-init mode,
             then the whole thing should be false *)
          ([], Dr.False)
        end
      | _ ->
        begin
          (* Inductive Case: *)
          let rjumpmap = Jumptable.extract_rjumptable modemap in
          let prev_modes : id list = Jumptable.find q rjumpmap in
          let process (q' : id (* prev mode *)) : (flow * formula) =
            let (id, macro, inv, flows, jm) = Modemap.find q' modemap in
            let (flow', formula') = reach_kq (k-1) q' hm in
            let formula'' = process_jump (Jumpmap.find q' jm) q' q (k-1) k in
            begin
              raise Not_found
            end
          in
          let (flows, formulas) = BatList.split (List.map process prev_modes) in
            (BatList.concat flows, Dr.Or formulas)
        end

let transform (k : int) (hm : hybrid) : Dr.t =
  let (vardecl_list, modes, init, goal) = hm in
  let jt = Jumptable.extract_rjumptable modes in
  let _ = Jumptable.print BatIO.stdout jt in
  let (init_mode, init_formula) = init in
  let new_vardecls =
    List.map
      (function (v, Value.Num n) -> (v, n, n)
      | (v, Value.Intv (lb, ub)) -> (v, lb, ub))
      vardecl_list in
  let out = BatIO.stdout in
  begin
    (new_vardecls, [], process_init 0 init_formula)
  end
