(** Soonho Kong (soonhok@cs.cmu.edu)
    Wei Chen    (weichen1@andrew.cmu.edu) *)

open Batteries
open IO
open Type
open Cil

let headers = ref ["stdio.h"; "stdlib.h"]
let dt = ref 0.01

type ty_vmap = (string, Cil.varinfo) Map.t

(*   x => *x   *)
class replacePtrLvalVisitor
    (sformals : Cil.varinfo list) =
  object(self)
    inherit nopCilVisitor as super
    method vlval ((lh, off) : Cil.lval) =
      match (lh, off) with
      | (Var vi, NoOffset) ->
        if List.exists ((=) vi) sformals then
          ChangeTo (Mem (Lval (lh, off)), NoOffset)
        else
          DoChildren
      | _ -> failwith "replacePtrVisitor failed"
  end

(*   ty => *ty   *)
class replacePtrTypeVisitor
    (sformals : Cil.varinfo list) =
  object(self)
    inherit nopCilVisitor as super
    method vtype (ty : Cil.typ) =
      let n = (TPtr (ty, [])) in
      ChangeTo n
  end

(*   f(x, y)  =>  f(&x, &y)   *)
class replaceCallAddrOfVisitor
  = object(self)
    inherit nopCilVisitor as super
    val replaceExpr = fun (cexpr : Cil.exp) ->
      match cexpr with
      | Lval lv -> mkAddrOf lv
      | _ -> cexpr
    method vinst (cinstr : Cil.instr) =
      match cinstr with
      | Call (None, f, args, l) ->
        ChangeTo [Call (None, f, List.map replaceExpr args, l)]
      | _ -> DoChildren
  end

(* Code Generation *)
let rec emit_def (vmap : ty_vmap) (macro : Type.macro)
  : (Cil.global * ty_vmap) = match macro with
  Macro (s, v) ->
    let vi = makeGlobalVar s doubleType in
    let init = {init = Some (SingleInit (Const (CReal (v, FDouble, None))))} in
    let g = GVar (vi, init, locUnknown) in
    let vmap' = Map.add s vi vmap in
    (g, vmap')

let rec emit_defs (vmap : ty_vmap) (macros : Type.macro list)
  : (Cil.global list * ty_vmap) =
  List.fold_left (fun (gl, vmap) macro ->
      let (g, vmap') = emit_def vmap macro in
      (gl@[g], vmap')
    )
    ([], vmap) macros

let rec emit_stmt (vmap : ty_vmap) (fd : Cil.fundec)
  : Type.stmt -> (ty_vmap * Cil.stmt list) =
  function
  | Ode (s, exp) ->
    let lv = var (Map.find s vmap) in
    let e = emit_exp vmap exp in
    let stmt = Formatcil.cStmt
        "%l:s = %l:s + %v:dt * %e:e;"
        (fun n t -> failwith "false")
        locUnknown
        [("s", Fl lv);
         ("dt", Fv (Map.find "dt" vmap));
         ("e", Fe e);]
    in
    let stmt' = visitCilStmt (new replacePtrLvalVisitor fd.sformals) stmt in
    (vmap, [stmt'])
  | Assert _ ->
    begin
      (* TODO(soonhok): implement *)
      (vmap, [dummyStmt])
    end
  | Assign (s, exp) ->
      let lv = var (Map.find s vmap) in
      let e = emit_exp vmap exp in
      let stmt = mkStmtOneInstr (Set (lv, e, locUnknown)) in
      let stmt' = visitCilStmt (new replacePtrLvalVisitor fd.sformals) stmt in
      (vmap, [stmt'])
  | If (bexp, then_stmts, else_stmts) ->
    let bcexp = emit_bexp vmap bexp in
    let bcexp' = visitCilExpr (new replacePtrLvalVisitor fd.sformals) bcexp in
    let (_, then_cstmts) = emit_stmts vmap fd then_stmts in
    let (_, else_cstmts) = emit_stmts vmap fd else_stmts in
    (vmap, [mkStmt (If (bcexp', mkBlock then_cstmts, mkBlock else_cstmts, locUnknown))])
  | Proceed stmts ->
    let (_, cstmts) = emit_stmts vmap fd stmts in
    let cstmts' = List.map
        (fun cstmt ->
           visitCilStmt (new replaceCallAddrOfVisitor) cstmt
        )
        cstmts in
    let while_stmts = mkWhile ~guard:(integer 1) ~body:cstmts'
    in
    (vmap, while_stmts)
  | Vardecl vd ->
    begin
      match vd with
      | RealVar s ->
        let vi = makeLocalVar fd s doubleType in
        let vmap' = Map.add s vi vmap in
        (vmap', [dummyStmt])
      | BRealVar (s, _, _) ->
        let vi = makeLocalVar fd s doubleType in
        let vmap' = Map.add s vi vmap in
        (vmap', [dummyStmt])
      | IntVar s ->
        let vi = makeLocalVar fd s intType in
        let vmap' = Map.add s vi vmap in
        (vmap', [dummyStmt])
    end
  | Switch _ ->
    begin
      (* TODO(soonhok): implement *)
      (vmap, [dummyStmt])
    end
  | Invoke (s, el) ->
    let cexps = emit_exps vmap el in
    let cinstr = Call (None, Lval (var (Map.find s vmap)), cexps, locUnknown) in
    (vmap, [mkStmtOneInstr cinstr])

(* list of statements *)
and emit_stmts (vmap : ty_vmap) (fd : Cil.fundec) (stmts : Type.stmt list)
  : (ty_vmap * Cil.stmt list) =
  let (vmap', cstmts) = List.fold_left
      (fun (vmap, cstmts) stmt ->
         let (vmap', cstmts') = emit_stmt vmap fd stmt in
         (vmap', cstmts @ cstmts'))
      (vmap, [])
      stmts
  in
  (vmap', compactStmts cstmts)

and emit_function (vmap : ty_vmap) (id : string) (args : var_decl list) stmts
  : (ty_vmap * Cil.global) =
  let fd : Cil.fundec = emptyFunction id in
  let (arg_map, arg_list) =
    List.fold_left (fun (m, l) arg ->
        let (s, vi) = match arg with
            RealVar s -> (s, makeFormalVar fd s (Formatcil.cType "double" []))
          | BRealVar (s, _, _) -> (s, makeFormalVar fd s (Formatcil.cType "double" []))
          | IntVar s -> (s, makeFormalVar fd s (Formatcil.cType "int" []))
        in
        Map.add s vi m, l@[vi])
      (vmap, [])
      args in
  let _ = setFormals fd arg_list in
  let (_, cstmts) = emit_stmts arg_map fd stmts in
  let sformals' =
    List.map
      (fun vi -> visitCilVarDecl (new replacePtrTypeVisitor fd.sformals) vi)
      fd.sformals
  in
  begin
    fd.sbody <- mkBlock cstmts;
    setFormals fd sformals';
    (Map.add id fd.svar vmap, GFun (fd, fd.svar.vdecl))
  end

(* Mode definition *)
and emit_mode (vmap : ty_vmap) (mode : Type.mode)
  : (ty_vmap * Cil.global) =
  let {id; args; stmts} = mode in
  emit_function vmap id args stmts

(* list of mode definition *)
and emit_modes (vmap : ty_vmap) (modes : Type.mode list)
  : (ty_vmap * Cil.global list) =
  List.fold_left
    (fun (vmap, gl) mode ->
       let (vmap', g) = emit_mode vmap mode in
       (vmap', gl @ [g]))
    (vmap, [])
    modes

(* Main entry point *)
and emit_main vmap main =
  let Main stmts = main in
  emit_function vmap "main" [] stmts

and emit_headers (headers : string list) : Cil.global list =
  List.map (fun s -> GText ("#include <" ^ s ^ ">")) headers

and emit_program (ast : Type.t) =
  let vmap = Map.empty in
  let {macros; modes; main} = ast in
  let macros' = (Macro ("dt", !dt))::macros in
  let g_headers = emit_headers !headers in
  let (g_macros, vmap') = emit_defs vmap macros' in
  let (vmap'', g_modes) = emit_modes vmap' modes in
  let (vmap''', g_main) = emit_main vmap'' main in
  let t : Cil.file = {fileName = "Kong";
                      globals =  g_headers @ g_macros @ g_modes @ [g_main];
                      globinit = None;
                      globinitcalled = false} in
  dumpFile defaultCilPrinter Pervasives.stdout "kong" t

and emit_exp (vmap : ty_vmap) (e : Type.exp) : Cil.exp =
  let binop_aux vmap (el : Type.exp list) (builder : (Cil.exp * Cil.exp * Cil.typ -> Cil.exp)) : Cil.exp =
    let el' : Cil.exp list = List.map (emit_exp vmap) el in
    List.reduce (fun e1 e2 ->
        let ty1 = typeOf e1 in
        let ty2 = typeOf e2 in
        let ty_of_sum =
          match (ty1, ty2) with
          | (TInt (IInt, _) , TInt (IInt, _)) -> intType
          | (TFloat (FDouble, _) , TFloat (FDouble, _)) -> doubleType
          | _ ->
            begin
              Errormsg.log "Attempt to perform (%a : %a) + (%a : %a)"
                d_exp e1 d_type ty1
                d_exp e2 d_type ty2;
              failwith "Addition only supports double + double."
            end
        in
        builder (e1, e2, ty_of_sum))
      el'
  in
  match e with
  | Var s -> Lval (var (Map.find s vmap))
  | Num n -> Const (CReal (n, FDouble, None))
  | Neg e ->
    let e' = emit_exp vmap e in
    let ty = typeOf e' in
    UnOp (Neg, e', ty)
  | Add el -> binop_aux vmap el (fun (e1, e2, ty) -> BinOp (PlusA, e1, e2, ty))
  | Sub el -> binop_aux vmap el (fun (e1, e2, ty) -> BinOp (MinusA, e1, e2, ty))
  | Mul el -> binop_aux vmap el (fun (e1, e2, ty) -> BinOp (Mult, e1, e2, ty))
  | Div (e1, e2) -> binop_aux vmap [e1;e2] (fun (e1, e2, ty) -> BinOp (Div, e1, e2, ty))
  | Pow (e1, e2) -> failwith "pow not implemented"
  | Ite (f, e1, e2) -> failwith "ite not implemented"
  | Sqrt e -> failwith "sqrt not implemented"
  | Safesqrt e -> failwith "safesqrt not implemented"
  | Abs e -> failwith "abs not implemented"
  | Log e -> failwith "log not implemented"
  | Exp e -> failwith "exp not implemented"
  | Sin e -> failwith "sin not implemented"
  | Cos e -> failwith "cos not implemented"
  | Tan e -> failwith "tan not implemented"
  | Asin e -> failwith "asin not implemented"
  | Acos e -> failwith "acos not implemented"
  | Atan e -> failwith "atan not implemented"
  | Atan2 (e1, e2) -> failwith "atan2 not implemented"
  | Matan e -> failwith "matan not implemented"
  | Sinh e -> failwith "sinh not implemented"
  | Cosh e -> failwith "cosh not implemented"
  | Tanh e -> failwith "tanh not implemented"
  | Asinh e -> failwith "asinh not implemented"
  | Acosh e -> failwith "acosh not implemented"
  | Atanh e -> failwith "atanh not implemented"
  | Integral (f, s1, sl, s2) -> failwith "integral not implemented"

and emit_bexp vmap b =
  let cmp_aux bop e1 e2 =
    let e1' = emit_exp vmap e1 in
    let e2' = emit_exp vmap e2 in
    BinOp (bop, e1', e2', Cil.intType)
  in
  let logic_aux bop e1 e2 =
    let e1' = emit_bexp vmap e1 in
    let e2' = emit_bexp vmap e2 in
    BinOp (bop, e1', e2', Cil.intType)
  in
  match b with
  | B_true -> integer 1
  | B_false -> integer 0
  | B_var s -> Lval (var (Map.find s vmap))
  | B_gt (e1, e2) -> cmp_aux Gt e1 e2
  | B_lt (e1, e2)-> cmp_aux Lt e1 e2
  | B_ge (e1, e2)-> cmp_aux Ge e1 e2
  | B_le (e1, e2)-> cmp_aux Le e1 e2
  | B_eq (e1, e2)-> cmp_aux Eq e1 e2
  | B_and (e1, e2)-> logic_aux LAnd e1 e2
  | B_or (e1, e2)-> logic_aux LOr e1 e2
and emit_exps (vmap : ty_vmap) (el : Type.exp list) : Cil.exp list =
  List.map (emit_exp vmap) el
