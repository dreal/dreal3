(*
   Wei    Chen (weichen1@andrew.cmu.edu)
   Soonho Kong (soonhok@cmu.edu)
*)
open Type
open Vcmap
open Batteries
open Codegen

type fmap = (string, Type.stmt list) Map.t
(**************)
(* utility    *)
(**************)
let is_ode =
  function s ->
    match s with
      Ode (_, _, _) -> true
    | _ -> false


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

and annotate_stmts (stmts : Type.stmt list) (vcmap : Vcmap.t) : Type.stmt list * Vcmap.t =
  match stmts with
  | [] -> stmts, vcmap
  | hd :: tl ->
    begin
    match hd with
    | Ode (_, _, _)
    | Proceed _
    | Vardecl _ ->
      let tl', vcmap' = annotate_stmts tl vcmap in
      hd::tl', vcmap'
    | If (be, conseq, alter) ->
      let be'= annotate_bexp be vcmap in
      let conseq', vcmap2 = annotate_stmts conseq vcmap in
      let alter', vcmap3 = annotate_stmts alter vcmap in
      let vcmap4 = join vcmap2 vcmap3 in
      let diff_conseq = diff vcmap2 vcmap4 in
      let diff_alter = diff vcmap3 vcmap4 in
      let conseq'' = append_copy_instr conseq' diff_conseq in
      let alter'' = append_copy_instr alter' diff_alter in
      let tl', vcmap5 = annotate_stmts tl vcmap4 in
      If (be', conseq'', alter'')::tl', vcmap5

    | Expr exp ->
      let exp' = annotate_exp exp vcmap in
      let tl', vcmap' = annotate_stmts tl vcmap in
      (Expr exp')::tl', vcmap'

    | Assign (s, exp, _) ->
      let exp' = annotate_exp exp vcmap in
      let vcmap' = update s vcmap in
      let tl', vcmap'' = annotate_stmts tl vcmap' in
      let c,_ = lookup s vcmap' in
      (Assign (s, exp', Some (VarAnno (0, "t", c))))::tl', vcmap''


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

and analysis (program : Type.t) : Type.t * fmap =
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
  let vcmap = update_list vars Map.empty in
  let jump_stmts', vcmap' = annotate_stmts jump_stmts vcmap in
  let mode' = {id=mode.id; args=mode.args; stmts=ode_stmts' @ jump_stmts'} in
  {macros=macros; modes=[mode']; main=main}, fmap


let usage = "Usage: bmc.native [<options>] code.dl"

let main () =
    let src = ref "" in
    let _ = Arg.parse []
            (fun x -> if Sys.file_exists x then src := x
                      else raise (Arg.Bad (x^": No such file"))) usage
    in
    let lexbuf = Lexing.from_channel (if !src = "" then stdin else open_in !src) in
    let ast = Parser.main Lexer.token lexbuf in
    let ast', fmap = analysis ast in
    let _ = Codegen.emit_program ast' in (* check output *)
    ()

let _ = main ()
