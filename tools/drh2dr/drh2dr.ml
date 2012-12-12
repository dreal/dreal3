let transform (hm : Hybrid.t) : Dr.t =
  let (vardecl_list, mode_list, init, goal) = hm in
  let (init_mode, init_formula) = init in
  let new_vardecls =
    List.map
      (function (v, Hybrid.Num n) -> (v, n, n)
      | (v, Hybrid.Intv (lb, ub)) -> (v, lb, ub))
      vardecl_list in
  let out = BatIO.stdout in
  begin
    (new_vardecls, Dr.True)
  end
