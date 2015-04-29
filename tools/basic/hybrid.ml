open Batteries

(* 1. Variable Declaration *)
type vardeclmap = Vardeclmap.t
type labellist = string list

(* 2. Mode *)
type modeId = Mode.id
type numId = int
type mode = Mode.t
type modemap = Modemap.t
type formula = Basic.formula
type exp = Basic.formula
type name = string

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
          ginvs: ginvs;
          name: name;
          num_id: numId;
          labels: labellist}


let make (vm, mm, iid, iformula, gs, ginvs, n, nid, ll)
  =
  {varmap= vm;
   modemap= mm;
   init_id = iid;
   init_formula = iformula;
   goals= gs;
   ginvs = ginvs;
   name = n;
   num_id = nid;
   labels = ll}
   
(*let makep (vm, mm, gs ginvs, n, ll) 
  =
  {varmap= vm;
   modemap= mm;
   init_id = "";
   init_formula = False;
   goals= gs;
   ginvs = ginvs;
   name = n;
   labels = ll}*)
   
let vardeclmap {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = var

let labellist {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = ll

let name {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = n

let modemap {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = mo

let init_id {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = iid

let init_formula {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = ifo

let goals {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = gs

let ginvs {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = g

let numid {varmap = var; modemap = mo; init_id = iid; init_formula = ifo; goals = gs; ginvs = g; name = n; num_id = nid; labels = ll } = nid

(**
      Only used in the parser.
      Substitute all the constant variables with their values.
 **)

let preprocess (vm, cm, mm, iid, iformula, gs, ginvs, n, nid, ll) : t =
  let subst s =
    match Map.mem s cm with
    | true ->
       begin
         match Vardeclmap.find s cm with
           (Value.Num n, _) -> Basic.Num n
         | _ -> raise Not_found
       end
    | false -> Basic.Var s
  in
  let cnt: int ref = ref 0 in
  let mm' =
    Map.map
      (fun m -> begin
      cnt := !cnt + 1;
       Mode.make
         (Mode.mode_id m,
         !cnt,
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
                Basic.preprocess_formula subst (Jump.change j),
                Jump.label j))
            (Mode.jumps m),
          Map.map
            (fun j ->
             Jump.makep
               (Basic.preprocess_formula subst (Jump.guard j),
                Jump.precision j,
                Jump.target j,
                Basic.preprocess_formula subst (Jump.change j),
                Jump.label j))
            (Mode.jumpmap m),
            
            0
         )
         end
      )
      mm in
  let init_formula' = Basic.preprocess_formula subst iformula in
  let goals' = List.map (fun (id, goal) -> (id, Basic.preprocess_formula subst goal)) gs in
  let ginvs' = List.map (fun ginv -> Basic.preprocess_formula subst ginv) ginvs in
  make (vm, mm', iid, init_formula', goals', ginvs', n, nid, ll)

let adjacent mode_id1 mode_id2 h  : bool =
  let mode1 = Map.find mode_id1 h.modemap in
  Map.mem mode_id2 mode1.jumpmap

let print out (hm : t) =
  let id_formula_print out (id, f) =
    Printf.fprintf out "(%s, %s)" (IO.to_string Id.print id) (IO.to_string Basic.print_formula f)
  in
  let str_list_print out =
	List.print String.print out
  in
  let print_header out str =
    Printf.fprintf out "\n====================%s====================\n" str
  in
  begin
	(* print name *)
	print_header out (name hm);
    (* print varDecl list *)
    print_header out "VarDecl Map";
    Vardeclmap.print out hm.varmap;
    (* print mode list *)
    print_header out "Mode Map";
    Modemap.print out hm.modemap;
    (* print label list *)
    print_header out "Label List";
    str_list_print out hm.labels;
    (* print init *)
    print_header out "Init";
    List.print ~first:"" ~sep:"\n" ~last:"\n" id_formula_print out [(hm.init_id, hm.init_formula)];
    (* print goal *)
    (*print_header out "Goal";
    List.print ~first:"" ~sep:"\n" ~last:"\n" id_formula_print out hm.goals;*)
  end

let goal_ids (hm : t) : modeId list
  = List.map (fun (goal_id, _) -> goal_id) hm.goals

(**
    Given a path (ex: [1;2;3;4]), it checks the three conditions:
    1) the first mode of the path should be the init mode of the hybrid model
    2) the last mode of the path should be an element of the goals of the HM
    3) the unrolling step k, should match with the length of the given path
 **)
let check_path (hm : t) (path : (string list) option) (k : int) : unit =
  let init = hm.init_id in
  let goals = goal_ids hm in
  match path with
    Some p ->
    begin
      let first_mode = List.first p in
      let last_mode = List.last p in
      let len = List.length p in
      let path_str =  IO.to_string (List.print ~first:"[" ~last:"]" ~sep:", " String.print) p in
      let goal_str =  IO.to_string (List.print ~first:"[" ~last:"]" ~sep:", " String.print) goals in
      match (first_mode = init, List.mem last_mode goals, len = k + 1) with
        (true, true, true) -> ()
      | (false, _, _) ->
         let msg = Printf.sprintf
                     "The first mode of the given path %s is %s which is different from %s, the initial mode of the given hybrid system model."
                     path_str first_mode init
         in
         raise (Arg.Bad msg)
      | (_, false, _) ->
         let msg = Printf.sprintf
                     "The last mode of the given path %s is %s which is not an element of %s, the list of modes in the goal section of the given hybrid system model."
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
