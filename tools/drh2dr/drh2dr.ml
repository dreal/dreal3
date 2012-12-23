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

let add_index (k : int) (q : int) (t : bool) (s : string) : string =
  let str_step = string_of_int k in
  let str_mode_id = string_of_int q in
  let suffix = if t then "t" else "0" in
  BatString.join "_" [s;
                      str_step;
                      str_mode_id;
                      suffix]

let process_init (q : int) (i : formula) : formula =
  Dr.subst_formula (add_index 0 q false) i

let process_flow (k : int) (q : int) (m : mode) : (flow * formula) =
  let (id, macro, inv, flow, jump) = m in
  (flow, Dr.True)

let process_jump (jumps : jump list) (q : int) (next_q : int) (k : int) (next_k : int)
    : formula =
  let (cond, _, change) = List.find (fun (_, id, _) -> id = q) jumps in
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

let rec reach (k : int) (q : int) (hm : hybrid) : (flow * formula)
    = let (vardecls, modes, (init_id, init_formula), goal) = hm in
      let modemap = Modemap.of_list modes in
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
          let rjumpmap = Jumptable.extract_rjumpmap hm in
          let prev_states : int list = Jumptable.find q rjumpmap in
          let process (q' : int (* prev state *)) : (flow * formula) =
            let (id, macro, inv, flows, jumps) =
              List.find (fun (id, _, _, _, _) -> id = q') modes in
            let (flow', formula') = reach (k-1) q' hm in
            let formula'' = process_jump jumps q' q (k-1) k in
            begin
              raise Not_found
            end
          in
          let (flows, formulas) = BatList.split (List.map process prev_states) in
            (BatList.concat flows, Dr.Or formulas)
        end

let transform (hm : hybrid) : Dr.t =
  let (vardecl_list, mode_list, init, goal) = hm in
  let jm = Jumptable.extract_rjumpmap hm in
  let _ = Jumptable.print BatIO.stdout jm in
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
