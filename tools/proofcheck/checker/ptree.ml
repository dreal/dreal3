(*
   Soonho Kong, soonhok@cs.cmu.edu
*)
open Batteries
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
       | Prune of env * env * t
       | Hole

type result = UNSAT
            | SAT

let print_log out =
  begin
    String.println out ("Proved Axioms     #: " ^ (string_of_int !num_of_proved_axioms));
    String.println out ("Failed Axioms     #: " ^ (string_of_int !num_of_failed_axioms));
    String.println out ("Branches          #: " ^ (string_of_int !num_of_branches));
    String.println out ("Trivial Prune     #: " ^ (string_of_int !num_of_trivial_pruning));
    String.println out ("non-trivial Prune #: " ^ (string_of_int !num_of_non_trivial_pruning));
  end

let extract_env p = match p with
  | Hole -> raise (Error "nothing to return!")
  | Axiom env -> env
  | Branch (env, _, _) -> env
  | Prune (env1, env2, _) -> env1

let check_axiom (e : env) (f : formula) : result =
  let eval env exp1 exp2 =
    let f' = Basic.Sub [exp1; exp2] in
    let result = Func.apply e f' 0 in
    result
  in
  let judge j v = match (j v) with
    | true ->
      (Failhandler.print_msg 0.001 f e v;
       SAT)
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
  | Hole -> ()
  | Axiom e ->
    let result = List.map (fun f -> (f, check_axiom e f)) fl in
    let result' = List.filter (fun (f, r) -> r = SAT) result in
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
      | false ->
        begin
          String.println IO.stdout "\nEnv1: ";
          Env.print IO.stdout env1;
          String.println IO.stdout "\nEnv2: ";
          Env.print IO.stdout env2;
          String.println IO.stdout "\nEnvJoin: ";
          Env.print IO.stdout env_join;
          String.println IO.stdout "Env: ";
          Env.print IO.stdout env;
          String.println IO.stdout "\nEnv is not a subset of EnvJoin(Env1 + Env2).";
          raise (Error "Branch")
        end
    end
  | Prune (env1, env2, pt') ->
    if not (Env.order env2 env1) then
        begin
          String.println IO.stdout "\nEnv1: ";
          Env.print IO.stdout env1;
          String.println IO.stdout "\nEnv2: ";
          Env.print IO.stdout env2;
          String.println IO.stdout "\nEnv2 is not a subset of Env1.";
          raise (Error "Prune")
        end
    else if Env.equals env2 env1 then
      (incr num_of_trivial_pruning;
       check pt' fl)
    else
      let remainders = Env.minus env1 env2 in
      begin
        incr num_of_non_trivial_pruning;
        List.iter (fun env_ -> check (Axiom env_) fl) remainders;
        check pt' fl
      end
