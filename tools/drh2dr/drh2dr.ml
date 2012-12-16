type varDecl = Dr.vardecl
type formula = Dr.formula
type hybrid = Hybrid.t
type dr = Dr.t
type id = int
type mode = Mode.t
type jump = Mode.jump
type ode = Mode.ode
type flow = ode list

let add_index (n : int) (s : string) : string =
  s ^ "_" ^ (string_of_int n)

type jumpmap = (int, int list) BatMap.t


(*
   (extract_jumpmap hm)[id] : successor of id
*)
let extract_jumpmap (hm : hybrid) : jumpmap =
  let (_, mode_list, _, _) = hm in
  let process_mode (jm : jumpmap) (mode : mode) : jumpmap =
    let (id, _, _, _, jump) = mode in
    let target_list = List.fold_left (fun l (_, t, _) -> t::l) [] jump in
    BatMap.add id target_list jm
  in
  List.fold_left process_mode BatMap.empty mode_list

(*
   (extract_rjumpmap hm)[id] : predecessor of id
*)
let extract_rjumpmap (hm : hybrid) : jumpmap =
  let (_, mode_list, _, _) = hm in
  let process_mode (jm : jumpmap) (mode : mode) : jumpmap =
    let (from_id, _, _, _, jump) = mode in
    List.fold_left
      (fun jm (_, to_id, _) ->
        match BatMap.mem to_id jm with
          true ->
            let id_set = BatMap.find to_id jm in
            BatMap.add to_id (from_id::id_set) jm
        | false ->
          BatMap.add to_id [from_id] jm
      ) jm jump
  in
  List.fold_left process_mode BatMap.empty mode_list

let print_jumpmap out (jm : jumpmap) =
  BatMap.print
    BatInt.print
    (fun out ints -> BatList.print BatInt.print out ints)
    out
    jm

let process_init (n : int) (i : formula) : formula =
  Dr.subst_formula (add_index n) i

let process_flow (q : int) (modes : mode list) : (flow * formula) =
  let (id, macro, inv, flow, jump) = List.nth modes q in
  (flow, Dr.True)

let process_jump (jumps : jump list) (q : int) (next_q : int) (k : int) (next_k : int) : formula =
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

let reach (k : int) (q : int) (v : string) (hm : hybrid) : (flow * formula)
    = let (vardecls, modes, (init_id, init_formula), goal) = hm in
      match k with
        0 ->
          begin
            let init_q0 : formula = process_init 0 init_formula in
            let (odes, f) = process_flow q modes in
            (odes, Dr.And [init_q0; f])
          end
      | _ ->
        begin
          raise Not_found
        end

let transform (hm : hybrid) : Dr.t =
  let (vardecl_list, mode_list, init, goal) = hm in
  let jm = extract_rjumpmap hm in
  let _ = print_jumpmap BatIO.stdout jm in
  let (init_mode, init_formula) = init in
  let new_vardecls =
    List.map
      (function (v, Hybrid.Num n) -> (v, n, n)
      | (v, Hybrid.Intv (lb, ub)) -> (v, lb, ub))
      vardecl_list in
  let out = BatIO.stdout in
  begin
    (new_vardecls, [], process_init 0 init_formula)
  end
