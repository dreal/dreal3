(*
   Wei    Chen (weichen1@andrew.cmu.edu)
   Soonho Kong (soonhok@cmu.edu)
*)
open Type
open Vcmap
open Batteries
open Codegen
open Smt2_cmd
open Smt2
open IO

type fmap = (string, Type.stmt list) Map.t
type vlist = (string * string * int option) list

let k = ref 2
let lb = ref (-1.0)
let ub = ref (-1.0)

(**************)
(* utility    *)
(**************)
let is_ode =
  function s ->
    match s with
      Ode (_, _, _) -> true
    | _ -> false

let is_proceed =
  function stmt ->
    match stmt with
    | Proceed _ -> true
    | _ -> false

let mk_var s k t idx =
  s ^ "_" ^ (string_of_int k) ^ "_" ^ t ^ "_" ^ (string_of_int idx)

let mk_var2 s k t =
  s ^ "_" ^ (string_of_int k) ^ "_" ^ t

(**************)
(* annotation *)
(**************)
let rec annotate_bexp (be : Type.bexp) (vcmap : Vcmap.t) : Type.bexp =
  match be with
  | B_var (s, _) ->
    let c, _ = lookup s vcmap in
    B_var (s, Some (VarAnno (0, "t", c)))
  | B_gt (e1, e2) ->
    let e1' = annotate_exp e1 vcmap in
    let e2' = annotate_exp e2 vcmap in
    B_gt (e1', e2')
  | B_lt (e1, e2) ->
    let e1' = annotate_exp e1 vcmap in
    let e2' = annotate_exp e2 vcmap in
    B_lt (e1', e2')
  | B_ge (e1, e2) ->
    let e1' = annotate_exp e1 vcmap in
    let e2' = annotate_exp e2 vcmap in
    B_ge (e1', e2')
  | B_le (e1, e2) ->
    let e1' = annotate_exp e1 vcmap in
    let e2' = annotate_exp e2 vcmap in
    B_le (e1', e2')
  | B_eq (e1, e2) ->
    let e1' = annotate_exp e1 vcmap in
    let e2' = annotate_exp e2 vcmap in
    B_eq (e1', e2')
  | B_and (e1, e2) ->
    let e1' = annotate_bexp e1 vcmap in
    let e2' = annotate_bexp e2 vcmap in
    B_and (e1', e2')
  | B_or (e1, e2) ->
    let e1' = annotate_bexp e1 vcmap in
    let e2' = annotate_bexp e2 vcmap in
    B_or (e1', e2')
  | B_true | B_false -> be


and annotate_exp (exp : Type.exp) (vcmap : Vcmap.t) : Type.exp =
  match exp with
  | Var (s, _) ->
    let c, _ = lookup s vcmap in
    Var (s, Some (VarAnno (0, "t", c)))
  | Num _ -> exp
  | Neg e -> Neg (annotate_exp e vcmap)
  | Add es ->
    let es' = List.map (fun x -> annotate_exp x vcmap) es in Add es'
  | Sub es ->
    let es' = List.map (fun x -> annotate_exp x vcmap) es in Sub es'
  | Mul es ->
    let es' = List.map (fun x -> annotate_exp x vcmap) es in Mul es'
  | Div (e1, e2) ->
    let e1' = annotate_exp e1 vcmap in
    let e2' = annotate_exp e2 vcmap in
    Div (e1', e2')

  | Pow (e1, e2) ->
    let e1' = annotate_exp e1 vcmap in
    let e2' = annotate_exp e2 vcmap in
    Pow (e1', e2')

  | Ite (f, e1, e2) -> failwith "todo"

  | Sqrt e -> Sqrt (annotate_exp e vcmap)
  | Safesqrt e -> Safesqrt (annotate_exp e vcmap)
  | Abs e -> Abs (annotate_exp e vcmap)
  | Log e -> Log (annotate_exp e vcmap)
  | Exp e -> Exp (annotate_exp e vcmap)
  | Sin e -> Sin (annotate_exp e vcmap)
  | Cos e -> Cos (annotate_exp e vcmap)
  | Tan e -> Tan (annotate_exp e vcmap)
  | Asin e -> Asin (annotate_exp e vcmap)
  | Acos e -> Acos (annotate_exp e vcmap)
  | Atan e -> Atan (annotate_exp e vcmap)
  | Atan2 (e1, e2) -> Atan2 (annotate_exp e1 vcmap, annotate_exp e2 vcmap)
  | Matan e -> Matan (annotate_exp e vcmap)
  | Sinh e -> Sinh (annotate_exp e vcmap)
  | Cosh e -> Cosh (annotate_exp e vcmap)
  | Tanh e -> Tanh (annotate_exp e vcmap)
  | Asinh e -> Asinh (annotate_exp e vcmap)
  | Acosh e -> Acosh (annotate_exp e vcmap)
  | Atanh e -> Atanh (annotate_exp e vcmap)

  | Integral (_, _, _, _) -> failwith "todo"
  | Invoke (s, es) ->
    (* assume function is primitive *)
    let es' = List.map (fun x -> annotate_exp x vcmap) es in
    Invoke (s, es')

and append_copy_instr (stmts : Type.stmt list) (diff : (Vcmap.key * Vcmap.value * Vcmap.value) list) : Type.stmt list =
  let to_add = List.map
      (fun (k, n1, n2) ->
         Assign (k, Var (k, Some (VarAnno (0, "t", n1))), Some (VarAnno (0, "t", n2)))
      ) diff
  in
  stmts @ to_add

and annotate_stmts (stmts : Type.stmt list) (vcmap : Vcmap.t) (vl : vlist) : Type.stmt list * Vcmap.t * vlist =
  match stmts with
  | [] -> stmts, vcmap, vl
  | hd :: tl ->
    begin
    match hd with
    | Ode (_, _, _)
    | Proceed _
    | Vardecl _ ->
      let tl', vcmap', vlist' = annotate_stmts tl vcmap vl in
      hd::tl', vcmap', vlist'
    | If (be, conseq, alter) ->
      let be'= annotate_bexp be vcmap in
      let conseq', vcmap2, vl2 = annotate_stmts conseq vcmap vl in
      let alter', vcmap3, vl3 = annotate_stmts alter vcmap vl2 in
      let vcmap4 = join vcmap2 vcmap3 in
      let diff_conseq = diff vcmap2 vcmap4 in
      let diff_alter = diff vcmap3 vcmap4 in
      let conseq'' = append_copy_instr conseq' diff_conseq in
      let alter'' = append_copy_instr alter' diff_alter in
      let tl', vcmap5, vl4 = annotate_stmts tl vcmap4 vl3 in
      If (be', conseq'', alter'')::tl', vcmap5, vl4

    | Expr exp ->
      let exp' = annotate_exp exp vcmap in
      let tl', vcmap', vl' = annotate_stmts tl vcmap vl in
      (Expr exp')::tl', vcmap', vl'

    | Assign (s, exp, _) ->
      let exp' = annotate_exp exp vcmap in
      let vcmap' = update s vcmap in
      let tl', vcmap'', vl' = annotate_stmts tl vcmap' vl in
      let c,_ = lookup s vcmap' in
      (Assign (s, exp', Some (VarAnno (0, "t", c))))::tl', vcmap'', (s, "t", Some c)::vl'


    | Assert bexp -> failwith "to implement"

    | Switch (_, _) -> failwith "to implement"
    end

(* extract a list of define-ode commands, and annotate it with flow name *)
and extract_ode (stmts : Type.stmt list) (fmap : fmap) (c : int) : Type.stmt list * fmap * int =
  match stmts with
  | [] -> failwith "empty mode definition"

  | [If (be, conseq, alter)] ->
    let conseq1, fmap1, c1 = extract_ode conseq fmap c in
    let alter1, fmap2, c2 = extract_ode alter fmap1 c1 in
    [If (be, conseq1, alter1)], fmap2, c2

  | _ -> (* only one flow definition *)
    let c' = c + 1 in
    let flow_name = "flow" ^ (string_of_int c') in
    let anno = function
      | Ode (s, e, _) -> Ode (s, e, Some (OdeAnno flow_name))
      | x -> failwith "not an ode"
    in
    let stmts' = List.map anno stmts in
    let fmap' = Map.add flow_name stmts' fmap in
    stmts', fmap', c'

and partition_ode stmts =
  match stmts with
  | [] -> failwith "no stmts"
  | (If (_, _, _) as hd)::tl -> [hd], tl
  | _ -> List.partition is_ode stmts

and analysis (program : Type.t) : Type.t * fmap * Vcmap.t * vlist =
  let {macros; modes; main} = program in
  (* assume only one mode *)
  let mode = List.hd modes in
  let ode_stmts, jump_stmts = partition_ode mode.stmts in
  let ode_stmts', fmap, _ = extract_ode ode_stmts Map.empty 0 in
  let vars = List.map
      (fun x ->
         match x with
         | RealVar s | BRealVar (s, _, _) | IntVar s -> s
      )
      mode.args
  in
  (* ode variable *)
  let vlist = List.flatten
                (List.map
                   (fun x ->
                    match x with
                    | RealVar s | BRealVar (s, _, _) | IntVar s -> [(s, "0", None); (s, "t", None)]
                   )
                   mode.args)
  in
  let vcmap = update_list vars Map.empty in
  let jump_stmts', vcmap', vlist' = annotate_stmts jump_stmts vcmap vlist in
  let mode' = {id=mode.id; args=mode.args; stmts=ode_stmts' @ jump_stmts'} in
  {macros=macros; modes=[mode']; main=main}, fmap, vcmap', vlist'

(**************)
(*    BMC     *)
(**************)
let rec trans_exp (exp : Type.exp) =
  match exp with
  | Var (s, _) ->
    Basic.Var s
  | Num n -> Basic.Num n
  | Neg e -> Basic.Neg (trans_exp e)
  | Add es -> Basic.Add (List.map (fun e -> trans_exp e) es)
  | Sub es -> Basic.Sub (List.map (fun e -> trans_exp e) es)
  | Mul es -> Basic.Mul (List.map (fun e -> trans_exp e) es)
  | Div (e1, e2) -> Basic.Div (trans_exp e1, trans_exp e2)
  | Pow (e1, e2) -> Basic.Pow (trans_exp e1, trans_exp e2)
  | Ite (_, _, _) -> failwith "todo"
  | Sqrt e -> Basic.Sqrt (trans_exp e)
  | Safesqrt e -> Basic.Safesqrt (trans_exp e)
  | Abs e -> Basic.Abs (trans_exp e)
  | Log e -> Basic.Log (trans_exp e)
  | Exp e -> Basic.Exp (trans_exp e)
  | Sin e -> Basic.Sin (trans_exp e)
  | Cos e -> Basic.Cos (trans_exp e)
  | Tan e -> Basic.Tan (trans_exp e)
  | Asin e -> Basic.Asin (trans_exp e)
  | Acos e -> Basic.Acos (trans_exp e)
  | Atan e -> Basic.Atan (trans_exp e)
  | Atan2 (e1, e2) -> Basic.Atan2 (trans_exp e1, trans_exp e2)
  | Matan e -> Basic.Matan (trans_exp e)
  | Sinh e -> Basic.Sinh (trans_exp e)
  | Cosh e -> Basic.Cosh (trans_exp e)
  | Tanh e -> Basic.Tanh (trans_exp e)
  | Asinh e -> Basic.Asinh (trans_exp e)
  | Acosh e -> Basic.Acosh (trans_exp e)
  | Atanh e -> Basic.Atanh (trans_exp e)
  | Integral (_, _, _, _) -> failwith "todo"
  | Invoke (s, es) -> failwith "todo"

let rec process_exp (exp : Type.exp) i =
  match exp with
  | Var (s, Some (VarAnno (_, t, idx))) ->
    let vname = mk_var s i t idx in
    Basic.Var vname
  | Num n -> Basic.Num n
  | Neg e -> Basic.Neg (process_exp e i)
  | Add es -> Basic.Add (List.map (fun e -> process_exp e i) es)
  | Sub es -> Basic.Sub (List.map (fun e -> process_exp e i) es)
  | Mul es -> Basic.Mul (List.map (fun e -> process_exp e i) es)
  | Div (e1, e2) -> Basic.Div (process_exp e1 i, process_exp e2 i)
  | Pow (e1, e2) -> Basic.Pow (process_exp e1 i, process_exp e2 i)
  | Ite (_, _, _) -> failwith "todo"
  | Sqrt e -> Basic.Sqrt (process_exp e i)
  | Safesqrt e -> Basic.Safesqrt (process_exp e i)
  | Abs e -> Basic.Abs (process_exp e i)
  | Log e -> Basic.Log (process_exp e i)
  | Exp e -> Basic.Exp (process_exp e i)
  | Sin e -> Basic.Sin (process_exp e i)
  | Cos e -> Basic.Cos (process_exp e i)
  | Tan e -> Basic.Tan (process_exp e i)
  | Asin e -> Basic.Asin (process_exp e i)
  | Acos e -> Basic.Acos (process_exp e i)
  | Atan e -> Basic.Atan (process_exp e i)
  | Atan2 (e1, e2) -> Basic.Atan2 (process_exp e1 i, process_exp e2 i)
  | Matan e -> Basic.Matan (process_exp e i)
  | Sinh e -> Basic.Sinh (process_exp e i)
  | Cosh e -> Basic.Cosh (process_exp e i)
  | Tanh e -> Basic.Tanh (process_exp e i)
  | Asinh e -> Basic.Asinh (process_exp e i)
  | Acosh e -> Basic.Acosh (process_exp e i)
  | Atanh e -> Basic.Atanh (process_exp e i)
  | Integral (_, _, _, _) -> failwith "todo"
  | Invoke (s, es) -> failwith "todo"
  | _ -> failwith "todo"

and process_bexp be i=
    match be with
    | B_var (s, Some (VarAnno (_, t, idx))) ->
      Basic.FVar (s ^ "_" ^ (string_of_int i) ^ "_" ^ t ^ "_" ^ (string_of_int idx))
    | B_gt (e1, e2) ->
      let e1' = process_exp e1 i in
      let e2' = process_exp e2 i in
      Basic.Gt (e1', e2')
    | B_lt (e1, e2) ->
      let e1' = process_exp e1 i in
      let e2' = process_exp e2 i in
      Basic.Lt (e1', e2')
    | B_ge (e1, e2) ->
      let e1' = process_exp e1 i in
      let e2' = process_exp e2 i in
      Basic.Ge (e1', e2')
    | B_le (e1, e2) ->
      let e1' = process_exp e1 i in
      let e2' = process_exp e2 i in
      Basic.Le (e1', e2')
    | B_eq (e1, e2) ->
      let e1' = process_exp e1 i in
      let e2' = process_exp e2 i in
      Basic.Eq (e1', e2')
    | B_and (be1, be2) ->
      let be1' = process_bexp be1 i in
      let be2' = process_bexp be2 i in
      Basic.And [be1'; be2']
    | B_or (be1, be2) ->
      let be1' = process_bexp be1 i in
      let be2' = process_bexp be2 i in
      Basic.Or [be1'; be2']
    | B_true -> Basic.True
    | B_false -> Basic.False
    | _ -> failwith "wrong bexp"

and process_stmts stmts k = Basic.make_and (List.map (fun stmt -> process_stmt stmt k) stmts)

and mk_var s k t idx =
  s ^ "_" ^ (string_of_int k) ^ "_" ^ t ^ "_" ^ (string_of_int idx)

and process_stmt (stmt : Type.stmt) (k : int) : Basic.formula =
  match stmt with
  | Ode (_, _, _) -> failwith "should not be an ode"
  | Assert _ -> failwith "todo"
  | Assign (s, exp, Some (VarAnno (_, t, idx))) ->
    let exp' = process_exp exp k in
    Basic.Eq (Basic.Var (mk_var s k t idx), exp')
  | If (be, conseq, alter) ->
    let be_f = process_bexp be k in
    let conseq_f = process_stmts conseq k in
    let alter_f = process_stmts alter k in
    Basic.And [Basic.Imply (be_f, conseq_f); Basic.Imply (Basic.Not be_f, alter_f)]
  | Proceed _ -> failwith "todo"
  | Vardecl _ -> failwith "todo"
  | Switch (_, _) -> failwith "todo"
  | Expr _ -> failwith "todo"
  | _ -> failwith "todo"


let rec gen_flow i mode fmap : Basic.formula =
  let rec process_ode stmts =
    match stmts with
    | [] -> failwith "empty stmts"

    | [If (be, conseq, alter)] ->
      let be_f = process_bexp be i in
      let conseq_f = process_ode conseq in
      let alter_f = process_ode alter in
      Basic.make_and [Basic.Imply (be_f, conseq_f); Basic.Imply (Basic.Not be_f, alter_f)]

    | _ ->
      let hd = List.hd stmts in
      begin
      match hd with
      | Ode (_, _, Some (OdeAnno (flow_name))) ->
        let flow_stmts = Map.find flow_name fmap in
        let ode_vars = List.map
            (fun x ->
               match x with
               | Ode (s, _, _) -> s ^ "_" ^ (string_of_int i)
               | _ -> failwith "should be ode"
            ) flow_stmts
        in
        let ode_vars_0 = List.map (fun x -> x ^ "_0") ode_vars in
        let ode_vars_t = List.map (fun x -> x ^ "_t") ode_vars in
        let time_var = "time" ^ (string_of_int i) in
        Basic.Eq (Basic.Vec ode_vars_t, Basic.Integral(0.0, time_var, ode_vars_0, flow_name))

      | _ -> failwith "should be an ode"
      end
  in

  let ode_stmts, jump_stmts = partition_ode mode.stmts in
  let ode_formula = process_ode ode_stmts in
  let jump_formula = process_stmts jump_stmts i in
  Basic.make_and [ode_formula; jump_formula]

and gen_conn k (vars : (Vcmap.key * Vcmap.value) list) : Basic.formula =
  let relations =
    List.map
      (fun (key, v) ->
       Basic.Eq (Basic.Var (mk_var key (k-1) "t" v), Basic.Var (key ^ "_"  ^ (string_of_int k) ^ "_0"))
      )
      vars
  in
  Basic.make_and relations

(* generate variable definition *)
and gen_var_decls vl k var_bound_map =
  let time_vars = List.map (fun i -> ("time" ^ (string_of_int i), Some (!lb, !ub))) (List.of_enum (0 -- k)) in
  let vars = List.flatten (
                 List.map
                   (fun i ->
                    List.map
                      (fun (s, t, idx) ->
                         let vname =
                           match idx with
                           | Some d -> mk_var s i t d
                           | None -> mk_var2 s i t
                         in
                         let bound =
                           match List.mem_assoc s var_bound_map with
                           | true -> Some (List.assoc s var_bound_map)
                           | false -> None
                         in (vname, bound)
                      )
                      vl
                   )
                   (List.of_enum (0 -- k)))
  in
  let total = vars @ time_vars in
  List.flatten (
    List.map
      (fun p ->
         match p with
         | (s, Some (l, u)) -> [Smt2_cmd.DeclareFun s; Smt2_cmd.make_lb s l; Smt2_cmd.make_ub s u]
         | (s, None) -> [Smt2_cmd.DeclareFun s]
      )
      total
  )

and gen_ode_decls fmap =
  let decls_map = Map.mapi
                    (fun flow_name stmts ->
                     let odes = List.map (fun stmt ->
                                          match stmt with
                                          | Ode (s, exp, _) -> (s, trans_exp exp)
                                          | _ -> failwith "error"
                                         )
                                         stmts
                     in
                     Smt2_cmd.DefineODE (flow_name, odes)
                    )
                    fmap
  in
  List.of_enum (Map.values decls_map)

and gen_init_constraint stmts =
  let fs =
    List.map
       (
         fun stmt ->
           match stmt with
           | Assign (s, e, _) ->
             let f exp =
               match exp with
               | Var (ss, _) -> Var(ss, Some(VarAnno(0, "0", 0)))
               | _ -> exp
             in
             let e' = subst_exp f e in
             let e'' = process_exp e' 0 in
             Basic.Eq (Basic.Var (mk_var2 s 0 "0"), e'')
           | _ -> Basic.True
       )
       stmts
  in
  Basic.make_and fs

and extract_init_value stmts =
  List.filter
    (fun stmt ->
       match stmt with
       | Assign _ -> true
       | _ -> false
    )
    stmts

and extract_var_bound stmts =
  match stmts with
  | [] -> []
  | hd :: tl ->
    begin
      match hd with
      | Vardecl BRealVar(s, l, u) -> (s, (l, u)) :: (extract_var_bound tl)
      | _ -> extract_var_bound tl
    end


and bmc (program : Type.t) (fmap : fmap) (vcmap : Vcmap.t) (k : int) (vl : vlist) =
  let {macros; modes; main} = program in
  assert (List.length modes = 1);
  let mode = List.hd modes in
  let vars = List.of_enum (Map.enum vcmap) in
  let mode_formulas = List.map (fun i -> gen_flow i mode fmap) (List.of_enum (0 -- (k-1))) in
  let mode_connect = List.map (fun i -> gen_conn i vars) (List.of_enum (1 -- (k-1))) in

  let Main main_stmts = main in
  let var_init_formula = gen_init_constraint (extract_init_value main_stmts) in

  let assert_formula = Assert (Basic.make_and (mode_formulas @ mode_connect @ [var_init_formula])) in
  let logic_cmd = SetLogic QF_NRA_ODE in

  (* generate var declarations *)

  let var_bound_map = extract_var_bound main_stmts in
  let vardecl_cmds = gen_var_decls vl k var_bound_map in

  let defineodes = gen_ode_decls fmap  in

  let assert_cmds = [] in
  let smt = List.flatten
      [[logic_cmd];
       vardecl_cmds;
       defineodes;
       assert_cmds;
       [assert_formula];
       [CheckSAT; Exit];
      ]
  in
  Smt2.print IO.stdout smt

(**************)
(*    main    *)
(**************)


let check_arg (ast:Type.t) =
  let Main stmts = ast.main in
  let proceeds = List.filter is_proceed stmts in
  let _ =
    match proceeds with
    | [] -> ()
    | [Proceed (Some l, Some u, ss)] ->
       begin
         lb := l;
         ub := u;
       end
    | _ -> failwith "more than one proceed"
  in
  if !lb < 0.0 || !ub < 0.0
  then failwith "time bound not specified"
  else ()

let spec = [
  ("-k", Arg.Int (fun n -> k := n), ": number of unrolling depth");
  ("-lb", Arg.Float (fun b -> lb := b), "lower bound of time");
  ("-ub", Arg.Float (fun b -> ub := b), "upper bound of time")
]

let usage = "Usage: code_bmc.native [<options>] code.dl"

let main () =
    let src = ref "" in
    let _ = Arg.parse spec
            (fun x -> if Sys.file_exists x then src := x
                      else raise (Arg.Bad (x^": No such file"))) usage
    in
    let lexbuf = Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let ast = Parser.main Lexer.token lexbuf in
    let ast = Type.const_fold_program ast in
    let  () = check_arg ast in
    let ast', fmap, vcmap, vl = analysis ast in
    (* let _ = Codegen.emit_program ast' in (* check output *) *)
    bmc ast' fmap vcmap !k vl

let _ = main ()
