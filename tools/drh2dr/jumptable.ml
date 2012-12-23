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
let extract_rjumpmap (modes : mode list) : t =
  let process_mode (jm : t) (mode : mode) : t =
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
  List.fold_left process_mode BatMap.empty modes

let find = BatMap.find

let print out (jm : t) =
  BatMap.print
    Id.print
    (fun out ids -> BatList.print Id.print out ids)
    out
    jm
