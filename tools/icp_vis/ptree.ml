(*
   Soonho Kong, soonhok@cs.cmu.edu
*)
open Batteries
exception Error of string

type env = Env.t
type formula = Basic.formula
type intv = Intv.t
type t = Axiom of env
       | Branch of env * string * t * t
       | Prune of env * t
       | Hole
       | SAT of env

let extract_top (t : t) : env =
  match t with
    Axiom e -> e
  | Branch (e, x, _, _) -> e
  | Prune (e, _) -> e
  | Hole -> raise (Error "extract_top Hole")
  | SAT e -> e

let make_prune (e, t) =
  try
    if Env.equals e (extract_top t) then t
    else
      begin
        (* String.println IO.stdout "================"; *)
        (* String.println IO.stdout "NOT THE SAME"; *)
        (* Env.print IO.stdout e; *)
        (* Env.print IO.stdout (extract_top t); *)
        (* String.println IO.stdout "================"; *)
        Prune(e, t);
      end
  with _ -> Prune (e, t)

let rec plugin t s =
  match t with
    Axiom _ -> t
  | Branch (e, x, t1, t2) -> Branch(e, x, plugin t1 s, plugin t2 s)
  | Prune (e, t') -> make_prune (e, plugin t' s)
  | Hole -> s
  | SAT e -> SAT e

let rec print out t =
  match t with
    Axiom e ->
      begin
        String.print out "(Axiom ";
        Env.print out e;
        String.println out ")";
      end
  | Branch (e, x, t1, t2) ->
      begin
        String.print out ("(Branch on " ^ x ^ " ");
        Env.print out e;
        String.println out ", ";
        print out t1;
        String.println out ", ";
        print out t2;
        String.println out ")";
      end
  | Prune (e, t') ->
      begin
        String.print out "(Prune ";
        Env.print out e;
        String.println out ", ";
        print out t';
        String.println out ")";
      end
  | Hole -> String.print out "HOLE"
  | SAT e ->
    begin
      String.print out "(SAT ";
      Env.print out e;
      String.println out ")";
    end

let rec traverse (t : t) (ts : t list) : (t * t list) =
  match (t, ts) with
  | (Axiom e, t'::ts') -> (t', ts')
  | (Axiom _, []) -> (t, ts)
  | (Branch (e, x, t1, t2), _) -> (t1, t2::ts)
  | (Prune (e,  t'), _) -> (t', ts)
  | (Hole, _) -> raise (Error "traverse HOLE")
  | (SAT e, ts) -> (SAT e, ts)

let rec do_it (t : t) (ts : t list) : (env list list) =
  let s = List.map extract_top (t::ts) in
  match traverse t ts with
    (SAT e, _) -> [s]
  | (Axiom e, []) -> [s]@[[e]]@[[]]
  | (t', ts') -> [s]@(do_it t' ts')
