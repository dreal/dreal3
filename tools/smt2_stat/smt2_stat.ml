open Smt2_cmd

let count_cmd f = function
    | SetLogic _ -> 0
    | SetInfo _ -> 0
    | DeclareFun _ -> 0
    | DeclareConst _ -> 0
    | Assert formula -> f formula
    | CheckSAT -> 0
    | Exit -> 0

let count_arith (smt2 : Smt2.t) : int
  =
  List.fold_left
    (fun result cmd -> result + (count_cmd Basic.count_arith_f cmd))
    0
    smt2

let count_mathfn (smt2 : Smt2.t) : int
  =
  List.fold_left
    (fun result cmd -> result + (count_cmd Basic.count_mathfn_f cmd))
    0
    smt2
