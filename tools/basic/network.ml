open Batteries

type automaton = Hybrid.t
type automata = automaton list
type mapping = (string * ((string * string) list)) list
type goals = (((string * string) list) * Hybrid.formula) (*((string * string) * Hybrid.formula) list*) (* ((automaton, mode), formula) *)
type globalvars = Vardeclmap.t

type modeTupel = (Hybrid.name * Hybrid.modeId)
type modecomposition = modeTupel list
type comppath = modecomposition list (*[[name, id]]*)

type modeId = Hybrid.modeId
type modeIds = modeId list
type modeIdsMap = (Hybrid.name, modeIds) Map.t
type hybGoals = Hybrid.goals
type time = Vardecl.t

type modemapping = Modemapping.t

type t = { modemapping: modemapping;
	   time: time;
	   automata: automata;
	   mapping: mapping;
	   globalvars: globalvars;
	   goals: goals
	 }

let modemapping {modemapping = mo; time = t; automata = aut; mapping = lm; globalvars = gv; goals = g} = mo

let automata {modemapping = mo; time = t; automata = aut; mapping = lm; globalvars = gv; goals = g} = aut

let mapping {modemapping = mo; time = t; automata = aut; mapping = lm; globalvars = gv; goals = g} = lm

let globalvars {modemapping = mo; time = t; automata = aut; mapping = lm; globalvars = gv; goals = g} = gv

let goals {modemapping = mo; time = t; automata = aut; mapping = lm; globalvars = gv; goals = g} = g

let time {modemapping = mo; time = t; automata = aut; mapping = lm; globalvars = gv; goals = g} = t

let make (mo, t, aut, lm, gv, g): t = {modemapping = mo; time = t; automata = aut; mapping = lm; globalvars = gv; goals = g}

let makep (t, aut, gv, g):t = {modemapping = (Modemapping.make (Map.empty, Map.empty)); time = t; automata = aut; mapping = []; globalvars = gv; goals = g}

let infinity = max_int

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
		(fun (x: Vardeclmap.t) (var, (value, prec)) ->
			match Map.mem var b with
				| false -> x
				| true -> Map.add var (value, prec) x
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
		(fun (map : Vardeclmap.t) (var, (value, prec)) ->
			match Map.mem var m with
				| true -> Map.add (Map.find var m) (value, prec) map
				| false -> Map.add var (value, prec) map
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
	let (var, (value, _)) = c in
	let (var', (value', _)) = vardecl in
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

let rec all_vars auta =
	match
		try Some (List.hd auta)
		with _ -> None
	with
		| Some x ->
			begin
			  let l = (Map.bindings (Hybrid.vardeclmap x)) in
			  (* let l1 = List.map (fun (k, (v, p)) -> (k, v, p)) l in *)
				List.append l (all_vars (List.tl auta))
			end
		| None -> []

let all_vars_unique auta  = List.sort_unique compare (all_vars auta)

let all_varnames_unique auta = List.sort_unique compare (all_var_names auta)

let rec all_label_names auta =
	match
		try Some (List.hd auta)
		with _ -> None
	with
		| Some x -> List.append (Hybrid.labellist x) (all_label_names (List.tl auta))
		| None -> []

let all_label_names_unique auta =
	List.sort_unique compare (all_label_names auta)

let process_variable_label_check_after_mapping auta =
	let vars = all_var_names auta in
	let labels = all_label_names auta in
	match same_variables_and_labels_name_aut vars labels with
		| (_, false) -> ()
		| (var, true) -> raise (Error.Variable_Label_Mapping (var^": is being mapped from both variable and label"))

let remap_formula f m =
	let subst v =
		match String.contains v '\'' with
			true -> begin
				let cv = String.filter (fun x -> x != '\'') v in
				match Map.mem cv m with
					true -> Basic.Var ((Map.find cv m)^"\'")
					| false -> Basic.Var (cv^"\'")
			end
			| false -> begin
				match Map.mem v m with
					true -> Basic.Var (Map.find v m)
					| false -> Basic.Var v
			end
	in
	(Basic.preprocess_formula subst) f

let remap_formula_autname f m a_n =
	match Map.mem a_n m with
		false -> f
		| true -> remap_formula f (Map.find a_n m)

let remap_flows f m =
	List.map (
		fun x -> begin
			Ode.subst (
				fun y -> begin
					match Map.mem y m with
						true -> Map.find y m
						| false -> y
				end
			)
			x
		end
	)
	f

let remap_flows_autname f m a_n =
	match Map.mem a_n m with
		false -> f
		| true -> remap_flows f (Map.find a_n m)

let remap_labels l m =
	List.map (
		fun x -> begin
			match Map.mem x m with
				false -> x
				| true -> Map.find x m
		end
	)
	l

let remap_labels_autname l m a_n =
	match Map.mem a_n m with
		false -> l
		| true -> remap_labels l (Map.find a_n m)

let rec bfs graph fringe visited goal depth =
	if List.is_empty fringe then
		(goal, infinity)
	else if List.mem goal fringe then
		(goal, depth)
	else
		(bfs
			graph
			(List.flatten (List.map (fun m -> List.filter (fun x -> not (List.mem x visited)) (List.assoc m graph)) fringe))
			(visited@fringe)
			goal
			(depth + 1))

let calc_distances_to_init aut =
	let modemap = Hybrid.modemap aut in
	let init_mode = Hybrid.init_id aut in
	let modes = List.map (fun (_, x) -> x) (Map.bindings (Hybrid.modemap aut)) in
	let mode_names = List.map (fun (x, _) -> x) (Map.bindings (Hybrid.modemap aut)) in
	let edges = List.map (fun m -> (Mode.mode_id m, List.map (fun (_, x) -> Jump.target x) (Map.bindings (Mode.jumpmap m)))) modes in
	List.map (fun m -> bfs edges [init_mode] [] m 0) mode_names

let postprocess_aut a m (mcnt: int ref) (acnt: int ref) =
	acnt := !acnt + 1;
	let remapping = Replaceautmap.of_list m in
	let name = Hybrid.name a in
	let vardecls_t = Hybrid.vardeclmap a in
	let vardecls =
		match Map.mem name remapping with
			| false -> vardecls_t
			| true -> map_replace_vardecls vardecls_t (Map.find name remapping)
	in
	let modemap = Hybrid.modemap a in
	(*let () = print_endline "Composed Network" in     *)
	let dists = (*calc_distances_to_init a*)
	   (List.map (fun (m, _) -> (m, 0)) (Map.bindings modemap))
	in

	let nmm = Map.map (
		fun x -> begin
			mcnt := !mcnt + 1;
			let mode_id = Mode.mode_id x in
			let prec = Mode.time_precision x in
			let invs_op = Mode.invs_op x in
			let flows = Mode.flows x in
			let jumpmap = Mode.jumpmap x in
			let jumps = Mode.jumps x in
			let n_id = Mode.mode_numId x in
			let m_dist = List.assoc mode_id dists in
			(*let n_id = !mcnt in*)

			let n_invs_op = match invs_op with
				None -> None
				| Some y -> Some (List.map (fun a -> remap_formula_autname a remapping name) y)
			in

			let n_flows = remap_flows_autname flows remapping name in

			let n_jumpmap = Map.map (
				fun y -> begin
					let guard = Jump.guard y in
					let precision = Jump.precision y in
					let target = Jump.target y in
					let change = Jump.change y in
					let label = Jump.label y in

					let n_guard = remap_formula_autname guard remapping name in
					let n_change = remap_formula_autname change remapping name in
					let n_label = remap_labels_autname label remapping name in

					Jump.makep (n_guard, precision, target, n_change, n_label)
				end
			)
			jumpmap
			in

			let n_jumps = List.map (
				fun y -> begin
					let guard = Jump.guard y in
					let precision = Jump.precision y in
					let target = Jump.target y in
					let change = Jump.change y in
					let label = Jump.label y in

					let n_guard = remap_formula_autname guard remapping name in
					let n_change = remap_formula_autname change remapping name in
					let n_label = remap_labels_autname label remapping name in

					Jump.makep (n_guard, precision, target, n_change, n_label)
				end
			)
			jumps
			in
			Mode.make (mode_id, n_id, prec, n_invs_op, n_flows, n_jumps, n_jumpmap, m_dist)
		end
	)
	modemap in
	let init_id = Hybrid.init_id a in
	let init_formula = remap_formula_autname (Hybrid.init_formula a) remapping name in
	let goals = Hybrid.goals a in
	let ginvs = Hybrid.ginvs a in
	let labels_t = Hybrid.labellist a in
	let labels =
		match Map.mem name remapping with
			| false -> labels_t
			| true -> map_replace_labels labels_t (Map.find name remapping)
	in
	Hybrid.make (vardecls, nmm, init_id, init_formula, goals, ginvs, name, !acnt, labels)

let postprocess_automata a m =
	let mcnt: int ref = ref 0 in
	let acnt: int ref = ref 0 in
	List.map (fun x -> postprocess_aut x m mcnt acnt) a

let check_time_variable t =
	let (var, value, _) = t in
	match var = "time" with
		true -> ()
		| false -> raise (Error.Lex_err ("Global variable declaration is supposed to be of the time.", 0))

let postprocess_network n analyze =
	let (instances, composition) = analyze in
	let auta = automata n in

	(* Create instances of existing, defined automata *)
	let aut_instanced = List.fold_left (
		fun lst (inst, temp, sub, init) ->
			begin
				match
					try Some (List.find (fun a -> (Hybrid.name a) = temp) auta)
					with Not_found -> None
				with
					Some x ->
						begin
							let (loc, form) = init in
							let nx = Hybrid.make (
								Hybrid.vardeclmap x,
								Hybrid.modemap x,
								loc,
								form,
								Hybrid.goals x,
								Hybrid.ginvs x,
								inst,
								Hybrid.numid x,
								Hybrid.labellist x
							) in
							nx::lst
						end
					| None ->
						begin
							raise (Error.Instance_Error (temp, inst))
							lst
						end
			end
	)
	[]
	instances
	in
	let t = time n in
	check_time_variable t;
	let instance_maps = List.map (fun (inst, temp, sub, init) -> (inst, sub)) instances in
	let maps = instance_maps(*List.append instance_maps composition*) in
	let compositionlist = (*List.map (fun (x, y) -> x)*) composition in
	let aut_instance_names = List.map (fun x -> Hybrid.name x) aut_instanced in
	ignore (List.map (fun x -> match List.mem x aut_instance_names with
		| true -> ()
		| false -> raise (Error.Composition_Error x)) composition);
	let aut_compose = List.filter (fun x -> List.mem (Hybrid.name x) compositionlist) aut_instanced in
	process_variable_label_check_before_mapping aut_compose;
	let auta_n = postprocess_automata aut_compose maps in
	process_variable_domains auta_n;
	process_variable_label_check_after_mapping auta_n;
	let gl = get_vardeclmap_global auta_n in
	let go = goals n in
	let mm = Modemapping.process_automata auta_n in
	make (mm, t, auta_n, maps, gl, go)

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


let compose_goals gs1 gs2 =
  List.fold_left
    (fun gs (m2, f2) ->
     List.fold_left
       (fun result (m1, f1) ->
	List.append result [(Id.compose m1 m2, Basic.And [f1;f2])]
       )
       gs
       []
    )
    gs1
    gs2

let compose_net_goals (net : t) (name : string) =
  let goals = net.goals in
  let formula = (match goals with | (x, y) -> y) in
  let aut_modes = (match goals with | (x, y) -> x) in
  let goal_automata = List.map (fun (a, m) -> a) aut_modes in
  (*
  let () =  Basic.print_formula IO.stdout formula in
  let () =  List.print ~sep:"," (fun out (aut, mode) -> Printf.fprintf out "@%s.%s" aut mode) IO.stdout aut_modes  in
  let () = print_endline "" in
 *)
  let mode_lists = List.map
		     (fun a ->
		      match List.mem (Hybrid.name a) goal_automata with
		      | true -> [match (List.find (fun (aname, m) -> (String.compare aname a.name) == 0) aut_modes) with (aut, m) -> m]
		      | false -> List.map (fun (k, v) -> k) (Map.bindings a.modemap)
		     )
		     net.automata in
  (*
let () =  List.print ~sep:"," (fun out modes -> (List.print ~sep:"," String.print IO.stdout modes)) IO.stdout mode_lists  in
   *)
  let rec mode_cross modes rest =
    (*
    let () = Printf.fprintf IO.stdout "mode_cross %d \n" (List.length rest) in
    let () =  List.print ~sep:"," String.print IO.stdout modes  in
    let () = print_endline "" in
     *)
    let crossed_modes =
      match List.length rest with
      | 0 -> modes
      | _ ->
       let rec_modes : string list = mode_cross (List.hd rest) (List.tl rest) in
       List.fold_left
	 (fun (result : string list) (my_mode : string)  ->
	  List.fold_left
	    (fun (res : string list) (my_rec_mode : string)  ->
	     let my_res = List.concat [res; [String.concat "_" [my_mode;my_rec_mode]]] in
	     (*
	     let () = Printf.fprintf IO.stdout "Cross: %s %s\n" my_mode my_rec_mode in
	     let () =  List.print ~sep:"," String.print IO.stdout my_res  in
	     let () = print_endline "" in
	      *)
	     my_res
	    )
	    result
	    rec_modes
	 )
	 []
	 modes
    in
    (*
    let () = Printf.fprintf IO.stdout "Crossed_modes:\n" in
    let () =  List.print ~sep:"," String.print IO.stdout crossed_modes  in
    let () = print_endline "" in
     *)
    crossed_modes
  in
  let goal_modes = match List.length mode_lists with
    | 1 -> List.hd mode_lists
    | _ -> mode_cross (List.hd mode_lists) (List.tl mode_lists)
  in
  (*
  let () = print_endline "Goal modes:" in
  let () =  List.print ~sep:"," String.print IO.stdout goal_modes  in
  let () = print_endline "" in
   *)
  let goal_aut_and_modes = List.map (fun x -> (name, x)) goal_modes in
  (goal_aut_and_modes, formula)

(**
Compute the parallel composition of two hybrid automata
 **)

let compose_pair (hm1 : Hybrid.t) (hm2 : Hybrid.t)  =

  (*  let () = print_endline "Composing Pair" in *)

  let vm = Vardeclmap.compose (Hybrid.vardeclmap hm1) (Hybrid.vardeclmap hm2) in
  let mm = Modemap.compose (Hybrid.modemap hm1) (Hybrid.labellist hm1)
			   (Hybrid.modemap hm2) (Hybrid.labellist hm2) in
  let iid = Id.compose (Hybrid.init_id hm1) (Hybrid.init_id hm2) in
  let iformula = Basic.And [(Hybrid.init_formula hm1);(Hybrid.init_formula hm2) ] in
  let gs  = compose_goals (Hybrid.goals hm1) (Hybrid.goals hm2) in
  let ginvs = List.append (Hybrid.ginvs hm1) (Hybrid.ginvs hm2) in
  let n = String.concat "_" [(Hybrid.name hm1); (Hybrid.name hm2)] in
  let nid = 1 in
  let ll =  List.sort_uniq String.compare (List.append (Hybrid.labellist hm1) (Hybrid.labellist hm2))  in
  (*
let () = print_endline "Composed Pair" in
   *)
  (* let () = Printf.fprintf IO.stdout "Init: %s\n" iid in *)
  Hybrid.make (vm, mm, iid, iformula, gs, ginvs, n, nid, ll)

let compose_initial (net : t) =
  let initial_mode_name = String.concat "_" (List.map (fun (x : Hybrid.t) -> x.init_id) net.automata)

  in
  let initial_formula = Basic.And (List.map (fun (x : Hybrid.t) -> x.init_formula) net.automata) in
  (initial_mode_name, initial_formula)

let compose (net : t) =
  (*
let () = print_endline "Composing Network" in
   *)
  match List.length net.automata with
  | 0 -> raise (Arg.Bad "Cannot compose an empty network.")
  | 1 -> net
  | _ ->
     let time = net.time in
     let aut = [List.fold_left
		  (fun a1 a2 ->
		   let product = compose_pair a1 a2 in
(*
		   let () = print_endline "<==================" in
		   let () = Hybrid.print IO.stdout product in
		   let () = print_endline "==================>" in
 *)
		   product
		  )
		 (List.hd net.automata)
		 (List.tl net.automata)]
     in
     let gv = net.globalvars in
     let network_name = Hybrid.name (List.hd aut) in

     let g = compose_net_goals net network_name in (* fixme *)
     (* let () = List.iter (Hybrid.print IO.stdout) aut in *)
     (*     let () = print_endline "Composed Network" in     *)
     let initial = compose_initial net in
     let analyze = ([(network_name, network_name,  [], initial)], [network_name]) in
     postprocess_network (makep (time, aut, gv, g)) analyze






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
