(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type id = int
type jump = Jump.t
type t = (id, jump) BatMap.t

let of_list (jumps : jump list) : t
    =
  List.fold_left
    (fun (map : t) ((f1, target, f2) as j) ->
      BatMap.add target j map
    )
    BatMap.empty
    jumps

let print = BatMap.print

let find = BatMap.find

