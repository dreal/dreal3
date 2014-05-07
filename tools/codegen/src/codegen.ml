(** Soonho Kong (soonhok@cs.cmu.edu)
    Wei Chen    (weichen1@andrew.cmu.edu) *)

open Batteries
open Type
open Cil
open Drh_stl

let headers = ref ["stdio.h"; "stdlib.h"; "math.h"]
let dt = ref 0.01

let toplevel = Drh_stl.libs

type ty_vmap = (string, Cil.varinfo) Map.t

(* a potential complex expression, for instance, has a function call inside it.
   will extract the call, assign the result to a tmp variable and simplify the
   expression.
*)
type reduce_exp = RExp of Cil.stmt list * Cil.exp

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
  | Ode (s, exp, _) ->
    let lv = var (Map.find s vmap) in
    let vmap', RExp (stmts, cexp) = emit_exp vmap exp fd in
    let cstmt = Formatcil.cStmt
        "%l:s = %l:s + %v:dt * %e:e;"
        (fun n t -> failwith "false")
        locUnknown
        [("s", Fl lv);
         ("dt", Fv (Map.find "dt" vmap'));
         ("e", Fe cexp);]
    in
    (vmap', stmts @ [cstmt])
  | Assert _ ->
    begin
      (* TODO(soonhok): implement *)
      (vmap, [dummyStmt])
    end
  | Assign (s, exp, _) ->
      let lv = var (Map.find s vmap) in
      let vmap', RExp (stmts, cexp) = emit_exp vmap exp fd in
      let cstmt = mkStmtOneInstr (Set (lv, cexp, locUnknown)) in
      (vmap', stmts @ [cstmt])
  | If (bexp, then_stmts, else_stmts) ->
    let vmap', RExp (stmts, bcexp) = emit_bexp vmap bexp fd in
    let (_, then_cstmts) = emit_stmts vmap fd then_stmts in
    let (_, else_cstmts) = emit_stmts vmap fd else_stmts in
    (vmap', stmts @ [mkStmt (If (bcexp, mkBlock then_cstmts, mkBlock else_cstmts, locUnknown))])
  | Proceed (_, _, stmts) ->
    let (_, cstmts) = emit_stmts vmap fd stmts in
    let cstmts' = List.map
        (fun cstmt ->
           visitCilStmt (new replaceCallAddrOfVisitor) cstmt
        )
        cstmts in
    let while_cstmts = mkWhile ~guard:one ~body:cstmts'
    in
    (vmap, while_cstmts)
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
  | Expr (Invoke (s, el)) ->
    let vmap', cstmts, cexps = emit_exps vmap el fd in
    let called = Map.find s vmap' in
    begin
      match called.vtype with
      | TFun (rtype, _, _, _) ->
        let assign_instr = Call (None, Lval (var (Map.find s vmap)), cexps, locUnknown) in
        (vmap, cstmts @ [mkStmtOneInstr assign_instr])
      | _ -> failwith "not a function"
    end
  | Expr _ -> (vmap, []) (* if no side effect, we just ignore it *)

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

and emit_function (vmap : ty_vmap) (id : string) (args : var_decl list) (stmts : Type.stmt list)
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
  let cstmts' =
    List.map
      (fun cstmt -> visitCilStmt (new replacePtrLvalVisitor fd.sformals) cstmt)
      cstmts
  in
  let sformals' =
    List.map
      (fun vi -> visitCilVarDecl (new replacePtrTypeVisitor fd.sformals) vi)
      fd.sformals
  in
  begin
    fd.sbody <- mkBlock cstmts';
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
and emit_main (vmap : ty_vmap) (main : Type.main_entry) : (ty_vmap * Cil.global)  =
  let Main stmts = main in
  emit_function vmap "main" [] stmts

and emit_headers (headers : string list) : Cil.global list =
  List.map (fun s -> GText ("#include <" ^ s ^ ">")) headers

and emit_program (ast : Type.t) =
  Drh_stl.drh_stl_init ();
  let vmap = Map.empty in
  let {macros; modes; main} = ast in
  let macros' = (Macro ("dt", !dt))::macros in
  let g_headers = emit_headers !headers in
  let (g_macros, vmap') = emit_defs vmap macros' in
  let (vmap'', g_modes) = emit_modes vmap' modes in
  let (vmap''', g_main) = emit_main vmap'' main in
  let t : Cil.file = {fileName = "codegen";
                      globals =  g_headers @ g_macros @ g_modes @ [g_main];
                      globinit = None;
                      globinitcalled = false} in
  dumpFile defaultCilPrinter Pervasives.stdout "codegen" t

and emit_exp (vmap : ty_vmap) (e : Type.exp) (fd : Cil.fundec): ty_vmap * reduce_exp =
  let binop_aux vmap (el : Type.exp list) (builder : (Cil.exp * Cil.exp * Cil.typ -> Cil.exp)) : ty_vmap * reduce_exp =
    let vmap', (el' : reduce_exp list) =
      List.fold_left
        (fun acc e ->
           let vmap, cexps = acc in
           let vmap', ne = emit_exp vmap e fd in
           (vmap', cexps @ [ne])
        )
        (vmap, []) el
    in
    (vmap', (* new environment *)
     List.reduce (fun a1 a2 ->
        let RExp (s1, e1) = a1 in
        let RExp (s2, e2) = a2 in
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
        (* merge all temp variables declarations *)
        RExp (s1@s2, builder (e1, e2, ty_of_sum)))
      el'
    )
  in
  let emit_single_var_func fn e =
    let vmap', cstmts, cexps = emit_exps vmap [e] fd in
    let called = Map.find fn !toplevel in
    begin
      match called.vtype with
      | TFun (rtype, _, _, _) ->
        let tmp_result_var =
          makeLocalVar fd ("tmp__" ^ (string_of_int (newVID ()))) rtype
        in
        let assign_instr =
          Call (Some (var tmp_result_var), Lval (var (Map.find fn !toplevel)), cexps, locUnknown)
        in
        (vmap, RExp (cstmts @ [mkStmtOneInstr assign_instr], Lval (var tmp_result_var)))
      | _ -> failwith "not a function"
    end
  in
  match e with
  | Var (s, _) ->
    vmap, RExp ([], Lval (var (Map.find s vmap)))
  | Num n ->
    vmap, RExp ([], Const (CReal (n, FDouble, None)))
  | Neg e ->
    let vmap', RExp (cstmts, cexp) = emit_exp vmap e fd in
    let ty = typeOf cexp in
    vmap', RExp (cstmts, UnOp (Neg, cexp, ty))
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
  | Sin e ->
    emit_single_var_func "sin" e
  | Cos e ->
    emit_single_var_func "cos" e
  | Tan e ->
    emit_single_var_func "tan" e
  | Asin e ->
    emit_single_var_func "asin" e
  | Acos e ->
    emit_single_var_func "acos" e
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
  | Invoke (s, el) ->
    let vmap', cstmts, cexps = emit_exps vmap el fd in
    let called = Map.find s vmap' in
    begin
      match called.vtype with
      | TFun (rtype, _, _, _) ->
        let tmp_result_var = makeLocalVar fd ("tmp__" ^ (string_of_int (newVID ()))) rtype in
        let assign_instr = Call (Some (var tmp_result_var), Lval (var (Map.find s vmap)), cexps, locUnknown) in
        (vmap, RExp (cstmts @ [mkStmtOneInstr assign_instr], Lval (var tmp_result_var)))
      | _ -> failwith "not a function"
    end

and emit_bexp (vmap : ty_vmap) (b : Type.bexp) (fd : Cil.fundec) : ty_vmap * reduce_exp =
  let cmp_aux bop e1 e2 =
    let vmap', RExp (stmts1, cexp1) = emit_exp vmap e1 fd in
    let vmap'', RExp (stmts2, cexp2) = emit_exp vmap' e2 fd in
    vmap'', RExp (stmts1@stmts2, BinOp (bop, cexp1, cexp2, Cil.intType))
  in
  let logic_aux bop e1 e2 =
    let vmap', RExp (stmts1, cexp1) = emit_bexp vmap e1 fd in
    let vmap'', RExp (stmts2, cexp2) = emit_bexp vmap' e2 fd in
    vmap'', RExp (stmts1@stmts2, BinOp (bop, cexp1, cexp2, Cil.intType))
  in
  match b with
  | B_true ->
    vmap, RExp ([], one)
  | B_false ->
    vmap, RExp ([], zero)
  | B_var (s, _) ->
    vmap, RExp ([], Lval (var (Map.find s vmap)))
  | B_gt (e1, e2) -> cmp_aux Gt e1 e2
  | B_lt (e1, e2)-> cmp_aux Lt e1 e2
  | B_ge (e1, e2)-> cmp_aux Ge e1 e2
  | B_le (e1, e2)-> cmp_aux Le e1 e2
  | B_eq (e1, e2)-> cmp_aux Eq e1 e2
  | B_and (e1, e2)-> logic_aux LAnd e1 e2
  | B_or (e1, e2)-> logic_aux LOr e1 e2
and emit_exps (vmap : ty_vmap) (el : Type.exp list) (fd : Cil.fundec): ty_vmap * Cil.stmt list * Cil.exp list =
  let vmap', stmts, el' =
    List.fold_left
      (fun acc e ->
         let vmap, stmts, el = acc in
         let vmap', RExp (stmts', e) = emit_exp vmap e fd in
         (vmap', stmts@stmts', el@[e])
      )
      (vmap, [], []) el
  in
  (vmap', stmts, el')
