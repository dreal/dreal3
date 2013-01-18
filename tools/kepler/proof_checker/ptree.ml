exception Error of string

open Intv
open Func

type t = Axiom of Env.t
             | Branch of Env.t * t * t
             | Prune of Env.t * t

type result = Good of Env.t
              | Bad of Env.t


let src = ref ""

let take_env p = match p with
  | Axiom e -> e
  | Branch (e, _, _) -> e
  | Prune (e, _) -> e

let ineqcounter = ref 0
let counter () =
    let c = !ineqcounter in
    let _ = ineqcounter := c + 1 in
    c

let check_axiom (e : Env.t) ((t, f) : Constraint.t) =
  let eval = Func.apply e f in
  let result =
    match t with
      Constraint.EQ_ZERO ->
        if Intv.contain_zero eval then
          Bad e
        else
          Good e
    | Constraint.GT_ZERO ->
        if Intv.may_contain_plus eval then
          Bad e
        else
          Good e
    | Constraint.LT_ZERO ->
        if Intv.may_contain_minus eval then
          Bad e
        else
          Good e
  in match result with
    Good e -> e
  | Bad e ->
    begin
      BatString.println BatIO.stdout "FAIL TO PROVE THIS AXIOM:";
      BatString.println BatIO.stdout "============================";
      BatString.println BatIO.stdout "Constraint: ";
      Constraint.print BatIO.stdout (t, f);
      BatString.println BatIO.stdout "";
      BatString.println BatIO.stdout "============================";
      BatString.println BatIO.stdout "Environment: ";
      BatString.println BatIO.stdout (Env.to_string e);
      BatString.println BatIO.stdout "============================";
      BatString.println BatIO.stdout "Eval Result = ";
      Intv.print BatIO.stdout eval;
      Error.output_filestring
        ("./" ^ !src ^ "_" ^ string_of_int (counter()) ^ ".txt")
         (Env.to_string e);
      e
    end

let rec check (p : t) (cs : Constraint.t list) =
  match p with
    | Axiom e ->
      (print_string "Axiom  : ";
       Env.print e;
       let _ = List.map (check_axiom e) cs in e)

    | Branch (e, p1, p2) ->
      (print_string "Branch : ";
       Env.print e;
       let e1 = check p1 cs in
       let e2 = check p2 cs in
       let e1e2 = Env.join e1 e2 in
       if Env.order e e1e2 then
         e
       else
         raise (Error "Branch")
      )

    | Prune (e, p') ->
      (print_string "Prune  : ";
       Env.print e;
       let ep = take_env p' in
       begin
         match Env.order ep e with
             (* 1. ep should be a subset of e  *)
             false -> raise (Error "Prune")
           | true ->
             (let remainders = Env.minus e ep in
              (* 2. check all the cut-out areas *)
              let _ = List.map (fun e' -> check (Axiom e') cs) remainders in
              (* 3. check the pruned sub-tree *)
              let _ = check p' cs in
	          e
             )
       end
      )
