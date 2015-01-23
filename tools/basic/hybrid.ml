open Batteries

(* 1. Variable Declaration *)
type vardeclmap = Vardeclmap.t

(* 2. Mode *)
type modeId = Mode.id
type mode = Mode.t
type modemap = Modemap.t
type formula = Basic.formula
type exp = Basic.formula

(* 3. Init and Goal *)
type init = modeId * formula
type goal = modeId * formula
type goals = goal list

type ginvs = formula list

type t = {varmap: vardeclmap;
          modemap: modemap;
          init_id: Mode.id;
          init_formula: formula;
          goals: goals;
          ginvs: ginvs}


let make (vm, mm, iid, iformula, gs, ginvs)
  =
  {varmap= vm;
   modemap= mm;
   init_id = iid;
   init_formula = iformula;
   goals= gs;
   ginvs = ginvs}

(**
      Only used in the parser.
      Substitute all the constant variables with their values.
 **)
let preprocess (vm, cm, mm, iid, iformula, gs, ginvs) : t =
  let subst s =
    match Map.mem s cm with
    | true ->
       begin
         match Vardeclmap.find s cm with
           Value.Num n -> Basic.Num n
         | _ -> raise Not_found
       end
    | false -> Basic.Var s
  in
  let mm' =
    Map.map
      (fun m ->
       Mode.make
         (Mode.mode_id m,
          Mode.time_precision m,
          begin
            match (Mode.invs_op m) with
              None -> None
            | Some inv -> Some (List.map (Basic.preprocess_formula subst) inv)
          end,
          List.map (fun (v, e) -> (v, Basic.preprocess_exp subst e)) (Mode.flows m),
          List.map
            (fun j ->
             Jump.makep
               (Basic.preprocess_formula subst (Jump.guard j),
		Jump.precision j,
                Jump.target j,
                Basic.preprocess_formula subst (Jump.change j)))
            (Mode.jumps m),
          Map.map
            (fun j ->
             Jump.makep
               (Basic.preprocess_formula subst (Jump.guard j),
		Jump.precision j,
                Jump.target j,
                Basic.preprocess_formula subst (Jump.change j)))
            (Mode.jumpmap m)
         )
      )
      mm in
  let init_formula' = Basic.preprocess_formula subst iformula in
  let goals' = List.map (fun (id, goal) -> (id, Basic.preprocess_formula subst goal)) gs in
  let ginvs' = List.map (fun ginv -> Basic.preprocess_formula subst ginv) ginvs in
  make (vm, mm', iid, init_formula', goals', ginvs')

let adjacent mode_id1 mode_id2 h  : bool =
  let mode1 = Map.find mode_id1 h.modemap in
  Map.mem mode_id2 mode1.jumpmap

let print out (hm : t) =
  let id_formula_print out (id, f) =
    Printf.fprintf out "(%s, %s)" (IO.to_string Id.print id) (IO.to_string Basic.print_formula f)
  in
  let print_header out str =
    Printf.fprintf out "====================\n%s====================" str
  in
  begin
    (* print varDecl list *)
    print_header out "VarDecl Map";
    Vardeclmap.print out hm.varmap;
    (* print mode list *)
    print_header out "Mode Map";
    Modemap.print out hm.modemap;
    (* print init *)
    print_header out "Init";
    List.print ~first:"" ~sep:"\n" ~last:"\n" id_formula_print out [(hm.init_id, hm.init_formula)];
    (* print goal *)
    print_header out "Goal";
    List.print ~first:"" ~sep:"\n" ~last:"\n" id_formula_print out hm.goals;
  end

let goal_ids (hm : t) : modeId list
  = List.map (fun (goal_id, _) -> goal_id) hm.goals

(**
    Given a path (ex: [1;2;3;4]), it checks the three conditions:
    1) the first mode of the path should be the init mode of the hybrid model
    2) the last mode of the path should be an element of the goals of the HM
    3) the unrolling step k, should match with the length of the given path
 **)
let check_path (hm : t) (path : int list option) (k : int) : unit =
  let init = hm.init_id in
  let goals = goal_ids hm in
  match path with
    Some p ->
    begin
      let first_mode = List.first p in
      let last_mode = List.last p in
      let len = List.length p in
      let path_str =  IO.to_string (List.print ~first:"[" ~last:"]" ~sep:", " Int.print) p in
      let goal_str =  IO.to_string (List.print ~first:"[" ~last:"]" ~sep:", " Int.print) goals in
      match (first_mode = init, List.mem last_mode goals, len = k + 1) with
        (true, true, true) -> ()
      | (false, _, _) ->
         let msg = Printf.sprintf
                     "The first mode of the given path %s is %d which is different from %d, the initial mode of the given hybrid system model."
                     path_str first_mode init
         in
         raise (Arg.Bad msg)
      | (_, false, _) ->
         let msg = Printf.sprintf
                     "The last mode of the given path %s is %d which is not an element of %s, the list of modes in the goal section of the given hybrid system model."
                     path_str last_mode goal_str
         in
         raise (Arg.Bad msg)
      | (_, _, false) ->
         let msg = Printf.sprintf
                     "The length of the given path %s is %d, while the given unrolling depth k is %d."
                     path_str len k
         in
         raise (Arg.Bad msg)
    end
  | None -> ()
