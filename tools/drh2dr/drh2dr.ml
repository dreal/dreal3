let add_index (n : int) (s : string) : string =
  s ^ "_" ^ (string_of_int n)

type jumpmap = (int, int list) BatMap.t

let extract_jumpmap (hm : Hybrid.t) : jumpmap =
  let (_, mode_list, _, _) = hm in
  let process_mode (jm : jumpmap) (mode : Mode.t) : jumpmap =
    let (id, _, _, _, jump) = mode in
    let target_list = List.fold_left (fun l (_, t, _) -> t::l) [] jump in
    BatMap.add id target_list jm
  in
  List.fold_left process_mode BatMap.empty mode_list

let print_jumpmap out (jm : jumpmap) =
  BatMap.print
    BatInt.print
    (fun out ints -> BatList.print BatInt.print out ints)
    out
    jm

let flow_q (n : int) (ml : Mode.t list) (v : string) : (Mode.ode * Mode.formula) =
  let (id, macro, inv, flow, jump) = List.nth ml n in
  let ode = List.find (fun (var, e) -> v = var) flow in
  raise Not_found

let reach (k : int) (s : int) (v : string) : (Mode.ode * Mode.formula)
    = raise Not_found

let init_q (n : int) (i : Dr.formula) : Dr.formula =
  Dr.subst_formula (add_index n) i

let transform (hm : Hybrid.t) : Dr.t =
  let (vardecl_list, mode_list, init, goal) = hm in
  let jm = extract_jumpmap hm in
  let _ = print_jumpmap BatIO.stdout jm in
  let (init_mode, init_formula) = init in
  let new_vardecls =
    List.map
      (function (v, Hybrid.Num n) -> (v, n, n)
      | (v, Hybrid.Intv (lb, ub)) -> (v, lb, ub))
      vardecl_list in
  let out = BatIO.stdout in
  begin
    (new_vardecls, [], init_q 0 init_formula)
  end
