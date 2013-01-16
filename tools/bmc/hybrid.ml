(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

(* 1. Variable Declaration *)
type vardeclmap = Vardeclmap.t

(* 2. Mode *)
type modeId = Mode.id
type mode = Mode.t
type modemap = Modemap.t
type formula = Dr.formula
type exp = Dr.formula

(* 3. Init and Goal *)
type init = modeId * formula
type goal = modeId * formula
type goals = goal list
type t = vardeclmap * vardeclmap * modemap * init * goals

let preprocess ((vm : Vardeclmap.t), (env : Vardeclmap.t), (mm : Modemap.t), (init_id, init_f), goals) : t =
  let subst s =
    match BatMap.mem s env with
    | true ->
      begin
        match Vardeclmap.find s env with
          Value.Num n -> Dr.Const n
        | _ -> raise Not_found
      end
    | false ->
      Dr.Var s
  in
  let mm' =
    BatMap.map
      (fun (id, inv_op, flow, jm) ->
        (id,
         begin
           match inv_op with
             None -> None
           | Some inv -> Some (List.map (Dr.preprocess_formula subst) inv)
         end,
           List.map (fun (v, e) -> (v, Dr.preprocess_exp subst e)) flow,
           BatMap.map
           (fun (f1, x, f2) -> (Dr.preprocess_formula subst f1,
                             x,
                             Dr.preprocess_formula subst f2))
           jm
        )
      )
      mm in
  let init' = (init_id, Dr.preprocess_formula subst init_f) in
  let goals' = List.map (fun (id, goal) -> (id, Dr.preprocess_formula subst goal)) goals in
  (vm, env, mm', init', goals')

let mf_print out (id, f) =
  begin
    BatString.print out "(";
    Id.print out id;
    BatString.print out ", ";
    Dr.print_formula out f;
    BatString.print out ")";
  end

let print out (((vm : Vardeclmap.t), (env : Vardeclmap.t), (mm : Modemap.t), init, goals) : t)=
  let print_header out str =
    begin
      BatString.println out "====================";
      BatString.println out str;
      BatString.println out "====================";
    end
  in
  begin
    (* print varDecl list *)
    print_header out "VarDecl Map";
    Vardeclmap.print out vm;
    (* print mode list *)
    print_header out "Mode Map";
    Modemap.print out mm;
    (* print init *)
    print_header out "Init";
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") mf_print out [init];
    (* print goal *)
    print_header out "Goal";
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") mf_print out goals;
  end
