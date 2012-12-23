(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type id = int
type mode = Mode.t
type t = (id, mode) BatMap.t

let of_list (modes : mode list) : t
    =
  List.fold_left
    (fun (map : (id, mode) BatMap.t) (m : mode) ->
      BatMap.add (Mode.extract_id m) m map
    )
    BatMap.empty
    modes

let print = BatMap.print

let find = BatMap.find

