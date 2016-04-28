open Batteries

type origin = Replace.origin
type destination = Replace.destination
type replacedecl = Replace.t
type t = (origin, destination) Map.t

let of_list (replacedecls : replacedecl list) : t
  =
  List.fold_left
    (fun (map: t) ((origin, destination): replacedecl) ->
     Map.add origin destination map
    )
    Map.empty
    replacedecls