open Batteries

type modeName = (string * string)
type modeNameToObj = (modeName, Mode.t) Map.t
type modeObjToName = (Mode.t, modeName) Map.t

type t = { modeNameToObj: modeNameToObj;
           modeObjToName: modeObjToName }
           
let make (mn, mi):t = {modeNameToObj = mn; modeObjToName = mi} 

let name_to_obj {modeNameToObj = mn; modeObjToName = mi} = mn

let obj_to_name {modeNameToObj = mn; modeObjToName = mi} = mi

let process' automata func =
	List.fold_left 
		(fun map (a: Hybrid.t) ->
			begin
				let name = Hybrid.name a in
				List.fold_left
				(fun mapin ((mid, mode): (string * Mode.t)) ->
					begin
						(func name mid mode mapin)
					end
				)
				map
				(Map.bindings (Hybrid.modemap a))
			end
		)
		Map.empty
		automata
		
let process_automata automata = 
	let name_obj = process' automata (fun name mid mode map -> Map.add (name, mid) mode map) in
	let obj_name = process' automata (fun name mid mode map -> Map.add mode (name, mid) map) in
	make (name_obj, obj_name)
	