open Batteries

type id = string
type mode = Mode.t
type t = (id, mode) Map.t

let of_list (modes : mode list) : t
  =
  List.fold_left
    (fun (map : (id, mode) Map.t) (m : mode) ->
     Map.add (Mode.mode_id m) m map
    )
    Map.empty
    modes

let print out = Map.print Id.print Mode.print out

let find key map =
  try
    Map.find key map
  with e ->
    let out = IO.stderr in
    begin
      String.println out "Modemap Exception!";
      Printf.fprintf out "Key: %s\n" (IO.to_string Id.print key);
      Printf.fprintf out "Map: %s\n" (IO.to_string print map);
      Printexc.print_backtrace IO.stdout;
      raise e
    end

let compose (mm1 : t) ll1 (mm2 : t) ll2 =
  let mm1size = List.length (Map.bindings mm1) in
  let mm2size = List.length (Map.bindings mm2) in
  Map.foldi
    (fun (k1 : id) (v1 : Mode.t) mma ->
     Map.foldi
       (fun (k2 : id) (v2 : Mode.t) mmb ->
(*
	let () = print_endline "Composing modes" in
	let () = Printf.fprintf IO.stdout "%s %s\n" k1 k2 in
 *)
	let new_id = String.concat "_" [k1; k2] in
	let new_index = ((v1.mode_numId-1) * mm2size) + v2.mode_numId in
	let new_mode = Mode.compose
			 v1 ll1
			 v2 ll2 new_index in
	let new_map = Map.add new_id new_mode mmb in
	new_map
       )
       mm2
       mma
    )
    mm1
    Map.empty
