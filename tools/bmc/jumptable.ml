(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type id = Mode.id
type jump = Jump.t
type mode = Mode.t
type t = (id, id list) BatMap.t

(*
   (extract_jumpmap hm)[id] : successor of id
*)
(* let extract_jumpmap (hm : hybrid) : jumpmap = *)
(*   let (_, mode_list, _, _) = hm in *)
(*   let process_mode (jm : jumpmap) (mode : mode) : jumpmap = *)
(*     let (id, _, _, _, jump) = mode in *)
(*     let target_list = List.fold_left (fun l (_, t, _) -> t::l) [] jump in *)
(*     BatMap.add id target_list jm *)
(*   in *)
(*   List.fold_left process_mode BatMap.empty mode_list *)

(*
   (extract_rjumpmap hm)[id] : predecessor of id
*)
let extract_rjumptable (modemap : Modemap.t) : t =
  let process_mode (mode : mode) (jt : t)  : t =
    let (from_id, _, _, jm) = mode in
    BatMap.fold
      (fun (_, to_id, _) jt ->
        match BatMap.mem to_id jt with
          true ->
            let id_set = BatMap.find to_id jt in
            BatMap.add to_id (from_id::id_set) jt
        | false ->
          BatMap.add to_id [from_id] jt
      ) jm jt
  in
  BatMap.fold process_mode modemap BatMap.empty

let find = BatMap.find

let print out (jm : t) =
  BatMap.print
    Id.print
    (fun out ids -> BatList.print Id.print out ids)
    out
    jm
