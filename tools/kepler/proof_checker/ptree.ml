exception Error of string

open Intv
open Func

type t = Axiom of Env.t
         | Branch of Env.t * t * t
         | Prune of Env.t * t

type result = Good of Env.t
              | Bad of Env.t * Intv.t


let src = ref ""

(* Return env *)
let take_env p = match p with
  | Axiom e -> e
  | Branch (e, _, _) -> e
  | Prune (e, _) -> e

let ineqcounter = ref 1
let counter () =
  let c = !ineqcounter in
  let _ = ineqcounter := c + 1 in
  c

let print_msg prec f e eval =
  begin
    BatString.println BatIO.stdout "FAIL TO PROVE THIS AXIOM:";
    BatString.println BatIO.stdout "============================";
    BatString.print BatIO.stdout   "Precision = ";
    BatFloat.print BatIO.stdout prec;
    BatString.println BatIO.stdout   "";
    BatString.println BatIO.stdout "============================";
    BatString.println BatIO.stdout "Formulas: ";
    Basic.print_formula BatIO.stdout f;
    BatString.println BatIO.stdout "";
    BatString.println BatIO.stdout "============================";
    BatString.println BatIO.stdout "Environment: ";
    BatString.println BatIO.stdout (Env.to_string e);
    BatString.println BatIO.stdout "============================";
    BatString.println BatIO.stdout "Eval Result = ";
    Intv.print BatIO.stdout eval;
  end

let get_new_filename () =
  let l = BatString.rfind !src ".trace" in
  let basename = BatString.left !src l in
  (basename ^ "_" ^ (string_of_int (counter())) ^ ".smt2")

let handle_fail e f cs prec =
  let vardecls = Env.to_list e in
  let (smt2_declvars, smt2_assertvars) =
    BatList.split
      (List.fold_left
         (fun result (name, {low = l; high = h}) ->
           let df = Smt2_cmd.DeclareFun name in
           let vd_lb =
             match l = neg_infinity with
             | true -> []
             | false -> [Smt2_cmd.make_lb name l]
           in
           let vd_ub =
             match h = infinity with
             | true -> []
             | false -> [Smt2_cmd.make_ub name h]
           in
           (df, BatList.concat [vd_lb;vd_ub])::result)
         []
         vardecls)
  in
  let smt2_assert_fs =
      Smt2_cmd.Assert (Basic.And cs)
  in
  let smt2 =
    BatList.concat
      [[Smt2_cmd.SetLogic Smt2_cmd.QF_NRA;
        Smt2_cmd.SetInfo (":precision", string_of_float prec)];
       smt2_declvars;
       BatList.concat smt2_assertvars;
       [smt2_assert_fs];
       [Smt2_cmd.CheckSAT;
        Smt2_cmd.Exit]]
  in
  BatFile.with_file_out
    (get_new_filename ())
    (fun out -> Smt2.print out smt2)

let check_axiom (e : Env.t) (cs : Basic.formula list) (prec : float) (f : Basic.formula) =
  let eval env exp1 exp2 = Func.apply env (Basic.Sub(exp1, exp2)) in
  let result =
    match f with
    | Basic.Eq (exp1, exp2) ->
      let v = eval e exp1 exp2 in
      if Intv.contain_z v then
        Bad (e, v)
      else
        Good e
    | Basic.Ge (exp1, exp2) ->
      let v = eval e exp1 exp2 in
      if Intv.contain_pz v then
        Bad (e, v)
      else
        Good e
    | Basic.Le (exp1, exp2) ->
      let v = eval e exp1 exp2 in
      if Intv.contain_nz v then
        Bad (e, v)
      else
        Good e
    | _ -> raise (Error "check_axiom::Should Not Happen")
  in match result with
    Good e -> e
  | Bad (e, v) ->
    begin
      print_msg prec f e v;
      handle_fail e f cs prec;
      e
    end

let rec check (p : t) (cs : Basic.formula list) (prec: float) =
  match p with
  | Axiom e ->
    (print_string "Axiom  : ";
     Env.print BatIO.stdout e;
     let _ = List.map (check_axiom e cs prec) cs in e)

  | Branch (e, p1, p2) ->
    (print_string "Branch : ";
     Env.print BatIO.stdout e;
     let e1 = check p1 cs prec in
     let e2 = check p2 cs prec in
     let e1e2 = Env.join e1 e2 in
     if Env.order e e1e2 then
       e
     else
       raise (Error "Branch")
    )

  | Prune (e, p') ->
    (print_string "Prune  : ";
     Env.print BatIO.stdout e;
     let ep = take_env p' in
     begin
       match Env.order ep e with
         (* 1. ep should be a subset of e  *)
         false -> raise (Error "Prune")
       | true ->
         (let remainders = Env.minus e ep in
          (* 2. check all the cut-out areas *)
          let _ = List.map (fun e' -> check (Axiom e') cs prec) remainders in
          (* 3. check the pruned sub-tree *)
          let _ = check p' cs prec in
	  e
         )
     end
    )
