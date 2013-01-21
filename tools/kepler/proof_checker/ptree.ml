(*
   Soonho Kong, soonhok@cs.cmu.edu
*)
exception Error of string

type env = Env.t
type formula = Basic.formula
type intv = Intv.t
type t = Axiom of env
       | Branch of env * t * t
       | Prune of env * t
type result = Proved
            | Failed of intv

let extract_env p = match p with
  | Axiom e -> e
  | Branch (e, _, _) -> e
  | Prune (e, _) -> e

let handle_fail e f v = raise Not_found

let check_axiom (e : env) (f : formula) : unit =
  let eval env exp1 exp2 = Func.apply env (Basic.Sub(exp1, exp2)) in
  let judge f v = match (f v) with
    | true -> Failed v
    | false -> Proved in
  let result = match f with
    | Basic.Eq (exp1, exp2) ->
      let v = eval e exp1 exp2 in judge Intv.contain_z v
    | Basic.Ge (exp1, exp2) ->
      let v = eval e exp1 exp2 in judge Intv.contain_pz v
    | Basic.Le (exp1, exp2) ->
      let v = eval e exp1 exp2 in judge Intv.contain_nz v
    | _ -> raise (Error "check_axiom::Should Not Happen")
  in match result with
  | Proved -> ()
  | Failed v -> handle_fail e f v

let rec check (pt : t) (fl : formula list) =
  match pt with
  | Axiom e ->
      List.iter (check_axiom e) fl
  | Branch (env, pt1, pt2) ->
    let env1 = extract_env pt1 in
    let env2 = extract_env pt2 in
    let env_join = Env.join env1 env2 in
    begin
      match Env.order env env_join with
      | true -> (check pt1 fl; check pt2 fl)
      | false -> raise (Error "Branch")
    end
  | Prune (env, pt') ->
    let env' = extract_env pt' in
    if not (Env.order env' env) then
      raise (Error "Prune")
    else if Env.equals env' env then
      check pt' fl
    else
      let remainders = Env.minus env env' in
      begin
        List.iter (fun env_ -> check (Axiom env_) fl) remainders;
        check pt' fl
      end
