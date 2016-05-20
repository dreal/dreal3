open Batteries

type replacemap = Replacemap.t
type name = Hybrid.name
type replacelist = Replace.t list
type replacelistmap = name * replacelist
type t = (name, replacemap) Map.t


let of_list (replacelistmaps : replacelistmap list) : t
  =
  List.fold_left
    (fun (map: t) ((name, replist): replacelistmap) ->
     Map.add name (Replacemap.of_list replist) map
    )
    Map.empty
    replacelistmaps