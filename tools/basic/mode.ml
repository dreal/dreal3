open Batteries

type id = Id.t
type numId = int
type init_dist = int
type exp = Basic.exp
type formula = Basic.formula
type var = Vardecl.var
type invs = formula list
type ode = Ode.t
type flow = ode
type jump = Jump.t
type jumpmap = Jumpmap.t

type t = {mode_id: id;
	  mode_numId: numId;
	  time_precision: float;
	  invs_op: invs option;
	  flows: ode list;
	  jumps: jump list;
	  jumpmap: jumpmap;
	  init_dist: init_dist}

let make (id, n_id, t_precision, invs_op, flows, jumps, jumpmap, init_dist)
  = {mode_id= id;
     mode_numId = n_id;
     time_precision = t_precision;
     invs_op= invs_op;
     flows= List.sort (fun (v1, ode1) (v2, ode2) -> String.compare v1 v2) flows;
     jumps= jumps;
     jumpmap= jumpmap;
     init_dist = init_dist}

let mode_id {mode_id= id;
	     mode_numId = n_id;
	     invs_op= invs_op;
	     flows= flows;
	     jumpmap= jumpmap}
  = id

let mode_numId {mode_id= id;
	     mode_numId = n_id;
	     invs_op= invs_op;
	     flows= flows;
	     jumpmap= jumpmap}
  = n_id

let mode_id (m : t) = m.mode_id
let mode_numId (m : t) = m.mode_numId
let time_precision (m : t) = m.time_precision
let invs_op (m : t) = m.invs_op
let flows (m : t) = m.flows
let jumps (m : t) = m.jumps
let jumpmap (m : t) = m.jumpmap
let init_dist (m : t) = m.init_dist

let print out {mode_id= id;
	       mode_numId = n_id;
	       invs_op= invs_op;
	       flows= flows;
	       jumps= jumps;
	       jumpmap= jumpmap;
	       init_dist = init_dist}
  =
  let mode_id = id in
  let numId = n_id in
  let inv_str = match invs_op with
      None -> "None"
    | Some inv ->
       IO.to_string (List.print ~first:"" ~sep:"\n    " ~last:"\n" Basic.print_formula) inv in
  let flow_str =
    IO.to_string (List.print ~first:"" ~sep:"\n    " ~last:"\n" Ode.print) flows in
  let jump_str = IO.to_string (List.print Jump.print) jumps in
  Printf.fprintf out
		 "{\nModeID = %s\nModenumID = %d\nInvariant = %s\nFlows = %s\nJump = %s\nDistance = %i\n}"
		 mode_id
		 numId
		 inv_str
		 flow_str
		 jump_str
		 init_dist

let flow_compose (flows1 : ode list) (flows2 : ode list) =
(*
  let () = Printf.fprintf IO.stdout "Flow compose\n"  in
  let () =  List.print ~sep:"," Ode.print IO.stdout flows1  in
  let () =  List.print ~sep:"," Ode.print IO.stdout flows2  in
  let () = Printf.fprintf IO.stdout "\n"  in
 *)
  let vars = List.unique (List.map (fun (v, _) -> v) (List.concat [flows1;flows2])) in
  let flows3 = List.map (fun var ->
			 let get_exp v flows =
			   try Some (List.find (fun (vv, e) -> v == vv ) flows) with
			   | Not_found -> None
			 in
			 let e1 = get_exp var flows1 in
			 let e2 = get_exp var flows2 in
			 match (e1, e2) with
			 | (None, Some e) -> e
			 | (Some e, None) -> e
			 | (Some e1a,
			    Some e2a) ->
			    Ode.compose e1a e2a
			)
			vars
  in
  (*
  let () =  List.print ~sep:"," Ode.print IO.stdout flows3  in
  let () = Printf.fprintf IO.stdout "\n"  in
   *)
  flows3
(*
  match List.length flows1 with
  | 0 -> flows2
  | _ ->
     let cflows = List.fold_left
       (fun result flw1 ->
	match List.length flows2 with
	| 0 -> flows1
	| _ ->
	   let flows = List.fold_left
	     (fun res flw2 ->
	      let new_flow = Ode.compose flw1 flw2 in
	      match new_flow with
	      | Some flow -> res@[flow]
	      | None -> res
	     )
	     result
	     flows2
	   in
	   match List.length flows with
	   | 0 -> result@[flw1]
	   | _ -> flows
       )
       []
       flows1
     in
     match List.length cflows with
     | 0 -> result@[flw1]
     | _ -> flows

 *)

let compose_sync jumps1 ll1 jumps2 ll2 =
    List.fold_left
    (fun result jmp1 ->
     List.fold_left
       (fun res jmp2 ->
	let new_jump = Jump.compose_sync jmp1 ll1 jmp2 ll2 in
	match new_jump with
	| Some jmp -> res@[jmp]
	| None -> res
       )
       result
       jumps2
    )
    []
    jumps1

let is_async j ll = (Set.cardinal (Set.intersect (Set.of_list (Jump.label j))
						 (Set.of_list ll))) = 0

(* create async jump for each of j2 *)
let compose_async2  (j2 : jump list) m1 ll1 =
  List.map (fun x -> match x with Some y -> y)
    (List.filter (fun x -> match x with | Some y -> true | None -> false)
	      (List.map (fun j -> match is_async j ll1 with
		     | true -> Some (Jump.compose_async2 m1.mode_id j)
		     | false -> None) j2))

let compose_async1 (j1 : jump list) m2 ll2 =
  List.map (fun x -> match x with Some y -> y)
(List.filter (fun x -> match x with | Some y -> true | None -> false)
	      (List.map (fun j -> match is_async j ll2 with
		     | true -> Some (Jump.compose_async1 j m2.mode_id)
		     | false -> None) j1))


let compose_jumps m1 ll1 m2 ll2 =
  let async1 = (compose_async1 m1.jumps m2 ll2) in
  let async2 = (compose_async2 m2.jumps m1 ll1) in
  let sync = compose_sync m1.jumps ll1 m2.jumps ll2 in
  sync@async1@async2

(* Does there exist a pair of jumps that can sync? *)
(* let can_synchronize m1 ll1 m2 ll2 =
  let result = List.exists
    (fun (x : Jump.t) ->
     List.exists
       (fun (y : Jump.t) ->
	let () = Printf.fprintf IO.stdout "Can sync? \n"   in
	let () =  List.print ~sep:"," String.print IO.stdout x.label in
	let () =  List.print ~sep:"," String.print IO.stdout ll1 in
	let () = Printf.fprintf IO.stdout "\n"   in
	let () =  List.print ~sep:"," String.print IO.stdout y.label in
	let () =  List.print ~sep:"," String.print IO.stdout ll2 in
	let () = Printf.fprintf IO.stdout "\n"   in

	let res = Jump.can_synchronize x.label ll1 y.label ll2 in
	let () = Printf.fprintf IO.stdout "res = %b \n" res  in
	res
       )
       m2.jumps
    )
    m1.jumps
    in
    let () = Printf.fprintf IO.stdout "result = %b \n\n" result  in
    result
 *)


let compose (m1 : t) ll1 (m2 : t) ll2 index : t =
  let id = Id.compose m1.mode_id m2.mode_id in
  (* let () = Printf.fprintf IO.stdout "Mode compose %s\n" id  in *)

  let n_id = index in
  let t_precision = max m1.time_precision m2.time_precision in
  let invs_op = match m1.invs_op, m2.invs_op with
    | Some i1, Some i2 -> Some (List.concat [i1; i2])
    | Some i1, None -> Some i1
    | None, Some i2 -> Some i2
    | _ -> None
  in
  let flows = flow_compose m1.flows m2.flows in
  (*  let () =  List.print ~sep:"," Ode.print IO.stdout flows  in *)


  let jumps = compose_jumps m1 ll1 m2 ll2 in

(*    let () =  List.print ~sep:"," Jump.print IO.stdout m1.jumps in
  let () = Printf.fprintf IO.stdout "\n"   in
  let () =  List.print ~sep:"," Jump.print IO.stdout m2.jumps in
  let () = Printf.fprintf IO.stdout "\n"   in

  let () =  List.print ~sep:"," Jump.print IO.stdout jumps in
  let () = Printf.fprintf IO.stdout "\n"   in
 *)
  let jumpmap = Jumpmap.of_list jumps in
  let init_dist = max m1.init_dist m2.init_dist in
  make (id, n_id, t_precision, invs_op, flows, jumps, jumpmap, init_dist)
