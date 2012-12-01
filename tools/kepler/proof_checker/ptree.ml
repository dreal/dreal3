exception Error of string

open Intv
open Func

type t = Axiom of Env.t
             | Branch of Env.t * t * t
             | Prune of Env.t * t

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
                 
let check_axiom (e : Env.t) (f : Func.t) =
  let result = Func.apply e f in
  if Intv.contain_zero result then
    (* let _ = print_endline (Env.to_string e) in *)
    let _ = Error.output_filestring
      ("./" ^ !src ^ "_" ^ string_of_int (counter()) ^ ".txt")
      (Env.to_string e) in
    e
  else
    e
      
let rec check (p : t) (fs : Func.t list) =
  match p with
    | Axiom e ->
      (print_string "Axiom  : ";
       Env.print e;
       let _ = List.map (check_axiom e) fs in e)
                                          
    | Branch (e, p1, p2) ->
      (print_string "Branch : ";
       Env.print e;
       let e1 = check p1 fs in
       let e2 = check p2 fs in
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
              let _ = List.map (fun e' -> check (Axiom e') fs) remainders in
              (* 3. check the pruned sub-tree *)
              let _ = check p' fs in
	          e
             )
       end
      )
