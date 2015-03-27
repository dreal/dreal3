open Batteries

type automaton = Hybrid.t
type automata = automaton list
type mapping = (string * ((string * string) list)) list
type goals = (((string * string) list) * Hybrid.formula) (*((string * string) * Hybrid.formula) list*) (* ((automaton, mode), formula) *)
type globalvars = Vardeclmap.t

type modeTupel = (Hybrid.name * Hybrid.modeId)
type modecomposition = modeTupel list
type comppath = modecomposition list

type modeId = Hybrid.modeId
type modeIds = modeId list
type modeIdsMap = (Hybrid.name, modeIds) Map.t
type hybGoals = Hybrid.goals

type t = { automata: automata;
           mapping: mapping;
           globalvars: globalvars; 
           goals: goals }
           
let automata {automata = aut; mapping = lm; globalvars = gv; goals = g} = aut

let mapping {automata = aut; mapping = lm; globalvars = gv; goals = g} = lm

let globalvars {automata = aut; mapping = lm; globalvars = gv; goals = g} = gv

let goals {automata = aut; mapping = lm; globalvars = gv; goals = g} = g

let make (aut, lm, gv, g): t = { automata = aut; mapping = lm; globalvars = gv; goals = g}

let rec get_all_vardecls (auta: automata):Vardeclmap.t list = 
	match
		try Some (List.hd auta)
		with _ -> None
	with
		| Some x -> (Hybrid.vardeclmap x)::(get_all_vardecls (List.tl auta))
		| None -> []

let get_vardeclmap_intersection a b = 
	let alist = Map.bindings a in
	List.fold_left
		(fun (x: Vardeclmap.t) ((var, value): Vardecl.t) ->
			match Map.mem var b with
				| false -> x
				| true -> Map.add var value x
		)
		Map.empty
		alist

let get_vardeclmap_aut_intersection a b = 
	get_vardeclmap_intersection (Hybrid.vardeclmap a) (Hybrid.vardeclmap b)

let get_vardeclmap_global auta = 
	let decls = get_all_vardecls auta in
	List.fold_left 
		(fun (x: Vardeclmap.t) (v: Vardeclmap.t) ->
			get_vardeclmap_intersection x v
		)
		(Vardeclmap.of_list [])
		decls

let map_replace_labels l m = 
	List.map 
		(fun x -> 
			match Map.mem x m with 
				| true -> Map.find x m
				| false -> x
		) 
		l

let map_replace_vardecls v m = 
	List.fold_left 
		(fun (map : Vardeclmap.t) ((var, value) : Vardecl.t) ->
			match Map.mem var m with 
				| true -> Map.add (Map.find var m) value map
				| false -> Map.add var value map
		)
	Map.empty
	(Map.bindings v)

let rec vardecls_auta_list alist = 
	match
		try Some (List.hd alist)
		with _ -> None
	with
		| Some x -> List.append (Map.bindings (Hybrid.vardeclmap x)) (vardecls_auta_list (List.tl alist))
		| None -> []

let same_variable_different_domain c vardecl = 
	let (var, value) = c in
	let (var', value') = vardecl in
	let fcomp a b = (int_of_float a) != (int_of_float b) in
	match var = var' with
		| false -> (var, false)
		| true -> 
			match value with
				| Value.Num x ->
					begin
						match value' with
							| Value.Num a -> (var, ((int_of_float x) != (int_of_float a)))
							| Value.Intv (_, _) -> (var, true)
					end
				| Value.Intv (x, y) -> 
					begin
						match value' with
							| Value.Num _ -> (var, true)
							| Value.Intv (a, b) -> (var, ((fcomp a x) || (fcomp b y)))
					end

let rec same_variable_different_domain_list c vardecllist = 
	match
		try Some (List.hd vardecllist)
		with _ -> None
	with
		| Some x -> 
			begin
				match same_variable_different_domain c x with
					| (var, true) -> (var, true)
					| (_, false) -> (same_variable_different_domain_list c (List.tl vardecllist))
			end
		| None -> ("", false)

let rec same_variable_list_different_domain_list alist vardecllist = 
	match
		try Some (List.hd alist)
		with _ -> None
	with
		| Some x -> 
			begin
				match same_variable_different_domain_list x vardecllist with
					| (_, false) -> same_variable_list_different_domain_list (List.tl alist) vardecllist
					| (var, true) -> (var, true)
			end
		| None -> ("", false)

let same_variable_auto_different_domain_list a vardecllist = 
	let alist = (Map.bindings (Hybrid.vardeclmap a)) in
	same_variable_list_different_domain_list alist vardecllist

let rec same_variable_different_domain_auta' alist vardecllist = 
	match
		try Some (List.hd alist)
		with _ -> None
	with
		| Some x -> 
			begin
				match same_variable_auto_different_domain_list x vardecllist with
					| (_, false) -> same_variable_different_domain_auta' (List.tl alist) vardecllist
					| (var, true) -> ((Hybrid.name x), (var, true))
			end
		| None -> ("", ("", false))

let same_variable_different_domain_auta alist = 
	let vardecllist = vardecls_auta_list alist in
	same_variable_different_domain_auta' alist vardecllist

let variable_domain_check alist = 
	let (aut, (var, mm)) = same_variable_different_domain_auta alist in
	match mm with
		| true -> raise (Error.Domain_Mismatch (aut^"."^" variable \""^var^"\" is defined on a different domain elsewhere."))
		| false -> ()

let process_variable_domains alist = 
	try variable_domain_check alist
	with x -> Error.handle_exn x

let rec same_variable_and_labels_name_aut var labellist =
	match
		try Some (List.hd labellist)
		with _ -> None
	with
		| Some x -> 
			begin
				match (var == x) with
					| true -> (var, true)
					| false -> same_variable_and_labels_name_aut var (List.tl labellist)
			end
		| None -> ("", false)

let rec same_variables_and_labels_name_aut vars labellist =
	match
		try Some (List.hd vars)
		with _ -> None
	with
		| Some x ->
			begin
				match same_variable_and_labels_name_aut x labellist with
					| (_, false) -> same_variables_and_labels_name_aut (List.tl vars) labellist
					| (y, true) -> (y, true)
			end
		| None -> ("", false)

let rec same_variable_and_label_name_auta auta = 
	match
		try Some (List.hd auta)
		with _ -> None
	with
		| Some x -> 
			begin
				let (vars, domains) = List.split (Map.bindings (Hybrid.vardeclmap x)) in
				match same_variables_and_labels_name_aut vars (Hybrid.labellist x) with
					| (n, true) -> ((Hybrid.name x), (n, true))
					| (_, false) -> same_variable_and_label_name_auta (List.tl auta)
			end
		| None -> ("", ("", false))

let process_variable_label_check_before_mapping auta =
	match same_variable_and_label_name_auta auta with
		| (aut, (var, true)) -> raise (Error.Variable_Label_Match (aut^": uses \""^var^"\" for both a variable and a label."))
		| (_, (_, false)) -> ()


let rec all_var_names auta = 
	match
		try Some (List.hd auta)
		with _ -> None
	with
		| Some x -> 
			begin
				let (vars, _) = List.split (Map.bindings (Hybrid.vardeclmap x)) in
				List.append vars (all_var_names (List.tl auta))
			end
		| None -> []

let rec all_label_names auta = 
	match
		try Some (List.hd auta)
		with _ -> None
	with
		| Some x -> List.append (Hybrid.labellist x) (all_label_names (List.tl auta))
		| None -> []
		
let process_variable_label_check_after_mapping auta = 
	let vars = all_var_names auta in
	let labels = all_label_names auta in
	match same_variables_and_labels_name_aut vars labels with
		| (_, false) -> ()
		| (var, true) -> raise (Error.Variable_Label_Mapping (var^": is being mapped from both variable and label"))

let postprocess_aut a m = 
	let remapping = Replaceautmap.of_list m in
	let name = Hybrid.name a in
	let vardecls_t = Hybrid.vardeclmap a in
	let vardecls = 
		match Map.mem name remapping with
			| false -> vardecls_t
			| true -> map_replace_vardecls vardecls_t (Map.find name remapping)
	in
	let modemap = Hybrid.modemap a in
	let init_id = Hybrid.init_id a in
	let init_formula = Hybrid.init_formula a in
	let goals = Hybrid.goals a in
	let ginvs = Hybrid.ginvs a in
	let labels_t = Hybrid.labellist a in
	let labels = 
		match Map.mem name remapping with
			| false -> labels_t
			| true -> map_replace_labels labels_t (Map.find name remapping)
	in
	Hybrid.make (vardecls, modemap, init_id, init_formula, goals, ginvs, name, labels)

let postprocess_automata a m = 
	List.map (fun x -> postprocess_aut x m) a

let postprocess_network n =
	let auta = automata n in
	let maps = mapping n in
	process_variable_label_check_before_mapping auta;
	let auta_n = postprocess_automata auta maps in
	process_variable_domains auta_n;
	process_variable_label_check_after_mapping auta_n;
	let gl = get_vardeclmap_global auta_n in
	let go = goals n in
	make (auta_n, maps, gl, go)
	
let init_mode_map nw =
	List.fold_left
		(fun (map: ((Hybrid.name, Hybrid.modeId) Map.t)) (a: automaton) ->
			Map.add (Hybrid.name a) (Hybrid.init_id a) map
		)
		Map.empty
		(automata nw)
		
let rec sep_goals lst =
	match
		try Some (List.hd lst)
		with _ -> None
	with
		Some (x, _) -> 
			begin 
				let (matched, unmatched) = List.partition (fun (a, _) -> a = x) lst in
				let nList = List.map (fun (_, b) -> b) matched in
				let (a, b) = List.hd matched in
				List.append [(a, nList)] (sep_goals unmatched)
			end
		| None -> []

let goal_ids (hm: t) : modeIdsMap = 
	let goaltuple = (fun (m, _) -> m) (goals hm) in
	let goalsepped = sep_goals goaltuple in
	List.fold_left
		(fun (map: modeIdsMap) ((a, b): (Hybrid.name * modeIds)) ->
			Map.add a b map
		)
		Map.empty
		goalsepped

let rec first_modes_init (m: modecomposition) (initmodemap) = 
	match
		try Some (List.hd m)
		with _ -> None
	with
		Some x ->
			begin
				let (name, mId) = x in
				match Map.mem name initmodemap with
					| true -> 
						begin
							let a_init_id = Map.find name initmodemap in
							match a_init_id = mId with
								| true -> first_modes_init (List.tl m) initmodemap
								| false -> false
							
						end
					| false -> raise (Error.Automaton_Not_Found name)
			end
		| None -> true
		
let rec last_modes_goals modecomp mim = 
	match 
		try Some (List.hd modecomp)
		with _ -> None
	with
		Some (nom, mid) ->
			begin
				match Map.mem nom mim with
					true ->
						begin
							let mids = Map.find nom mim in
							match List.mem mid mids with
								true -> true
								| false -> last_modes_goals (List.tl modecomp) mim
						end
					| false -> last_modes_goals (List.tl modecomp) mim
			end
		| None -> false
	

let check_path (nw : t) (path : comppath option) (k : int) : unit =
	let init = init_mode_map nw in
	let goals = goal_ids nw in
	match path with
		Some p ->
			begin
				let first_mode = List.first p in
				let last_mode = List.last p in
				let len = List.length p in
				match (first_modes_init first_mode init, last_modes_goals last_mode goals, len = k + 1) with
					(true, true, true) -> ()
					| (false, _, _) -> raise (Arg.Bad "Beginning state space in path does not consist of initial modes.")
					| (_, false, _) -> raise (Arg.Bad "End state space in path does not contain any goal modes.")
					| (_, _, false) -> raise (Arg.Bad "Path is longer than the unrolling constrain k.")
			end
		| None -> ()
		
let print out (nw : t) =
  let id_formula_print out (id, f) =
    Printf.fprintf out "(%s, %s)" (IO.to_string Id.print id) (IO.to_string Basic.print_formula f)
  in
  let print_formula out f =
	Printf.fprintf out "%s" (IO.to_string Basic.print_formula f)
  in
  let str_list_print out =
	List.print String.print out
  in
  let print_header out str =
    Printf.fprintf out "\n====================%s====================\n" str
  in
  let print_str_tuple out s =
	begin
		let (aut, loc) = s in
		Printf.fprintf out "(%s.%s)" aut loc
	end
	in
  let auta = automata nw in
  let (locs, e) = goals nw in
  begin
	(*network title*)
	print_header out "Network";
	(*print automata*)
	List.iter (fun a -> Hybrid.print out a) auta;
	(*print goal locations*)
	print_header out "Goal Locations";
	List.iter (fun l -> print_str_tuple out l) locs;
	print_header out "Goal Formula";
	print_formula out e;
  end
