(*
   Soonho Kong, soonhok@cs.cmu.edu
*)
exception Error of string

let num_of_proved_axioms = ref 0
let num_of_failed_axioms = ref 0
let num_of_branches = ref 0                  (* DONE *)
let num_of_non_trivial_pruning = ref 0       (* DONE *)
let num_of_trivial_pruning = ref 0           (* DONE *)

type env = Env.t
type formula = Basic.formula
type intv = Intv.t
type t = Axiom of env
       | Branch of env * t * t
       | Prune of env * t
type result = UNSAT
            | SAT of intv

let print_log out =
  begin
    BatString.println out ("Proved Axioms     #: " ^ (string_of_int !num_of_proved_axioms));
    BatString.println out ("Failed Axioms     #: " ^ (string_of_int !num_of_failed_axioms));
    BatString.println out ("Branches          #: " ^ (string_of_int !num_of_branches));
    BatString.println out ("Trivial Prune     #: " ^ (string_of_int !num_of_trivial_pruning));
    BatString.println out ("non-trivial Prune #: " ^ (string_of_int !num_of_non_trivial_pruning));
  end

let extract_env p = match p with
  | Axiom e -> e
  | Branch (e, _, _) -> e
  | Prune (e, _) -> e

let check_axiom (e : env) (f : formula) : result =
  let eval env exp1 exp2 = Func.apply env (Basic.Sub [exp1; exp2]) in
  let judge j v = match (j v) with
    | true ->
      (Failhandler.print_msg 0.001 f e v;
       SAT v)
    | false -> UNSAT in
  match f with
  | Basic.Eq (exp1, exp2) ->
    let v = eval e exp1 exp2 in judge Intv.contain_z v
  | Basic.Ge (exp1, exp2) ->
    let v = eval e exp1 exp2 in judge Intv.contain_pz v
  | Basic.Le (exp1, exp2) ->
    let v = eval e exp1 exp2 in judge Intv.contain_nz v
  | _ -> raise (Error "check_axiom::Should Not Happen")

let rec check (pt : t) (fl : formula list) =
  match pt with
  | Axiom e ->
    let result = List.map (fun f -> (f, check_axiom e f)) fl in
    let result' = List.filter (fun (f, r) -> r != UNSAT) result in
    let (sat_fs, _) = List.split (result') in
    begin
      match sat_fs with
        [] -> (incr num_of_proved_axioms)
      | _ -> (incr num_of_failed_axioms; Failhandler.handle e sat_fs fl)
    end
  | Branch (env, pt1, pt2) ->
    let env1 = extract_env pt1 in
    let env2 = extract_env pt2 in
    let env_join = Env.join env1 env2 in
    begin
      match Env.order env env_join with
      | true -> (incr num_of_branches; check pt1 fl; check pt2 fl)
      | false -> raise (Error "Branch")
    end
  | Prune (env, pt') ->
    let env' = extract_env pt' in
    if not (Env.order env' env) then
      raise (Error "Prune")
    else if Env.equals env' env then
      (incr num_of_trivial_pruning;
       check pt' fl)
    else
      let remainders = Env.minus env env' in
      begin
        incr num_of_non_trivial_pruning;
        List.iter (fun env_ -> check (Axiom env_) fl) remainders;
        check pt' fl
      end
