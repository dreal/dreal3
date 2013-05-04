(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

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

type t = {varmap: vardeclmap;
          modemap: modemap;
          init_id: Mode.id;
          init_formula: formula;
          goals: goals}

let make (vm, mm, iid, iformula, gs)
    =
  {varmap= vm;
   modemap= mm;
   init_id = iid;
   init_formula = iformula;
   goals= gs}

let varmap {varmap= vm;
            modemap= mm;
            init_id = iid;
            init_formula = iformula;
            goals= gs}
    = vm

let modemap {varmap= vm;
             modemap= mm;
             init_id = iid;
             init_formula = iformula;
             goals= gs}
    = mm

let init_id {varmap= vm;
             modemap= mm;
             init_id = iid;
             init_formula = iformula;
             goals= gs}
    = iid

let init_formula {varmap= vm;
                  modemap= mm;
                  init_id = iid;
                  init_formula = iformula;
                  goals= gs}
    = iformula

let goals {varmap= vm;
           modemap= mm;
           init_id = iid;
           init_formula = iformula;
           goals= gs}
    = gs

(**
    Only used in the parser.
    Substitute all the constant variables with their values.
**)
let preprocess (vm, cm, mm, iid, iformula, gs) : t =
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
           begin
             match (Mode.invs_op m) with
               None -> None
             | Some inv -> Some (List.map (Basic.preprocess_formula subst) inv)
           end,
             List.map (fun (v, e) -> (v, Basic.preprocess_exp subst e)) (Mode.flows m),
             Map.map
               (fun j ->
                 Jump.make
                   (Basic.preprocess_formula subst (Jump.guard j),
                    Jump.target j,
                    Basic.preprocess_formula subst (Jump.change j)))
               (Mode.jumpmap m)
          )
      )
      mm in
  let init_formula' = Basic.preprocess_formula subst iformula in
  let goals' = List.map (fun (id, goal) -> (id, Basic.preprocess_formula subst goal)) gs in
  make (vm, mm', iid, init_formula', goals')

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
    Vardeclmap.print out (varmap hm);
    (* print mode list *)
    print_header out "Mode Map";
    Modemap.print out (modemap hm);
    (* print init *)
    print_header out "Init";
    List.print ~first:"" ~sep:"\n" ~last:"\n" id_formula_print out [(init_id hm, init_formula hm)];
    (* print goal *)
    print_header out "Goal";
    List.print ~first:"" ~sep:"\n" ~last:"\n" id_formula_print out (goals hm);
  end

let goal_ids (hm : t) : modeId list
    = List.map (fun (goal_id, _) -> goal_id) (goals hm)
