open Batteries
open Cil

let (libs : (string, Cil.varinfo) Map.t ref) = ref (Map.empty)
(* why need type annotation? *)

let drh_stl_init () =
  (* sin *)
  let fn = "sin" in
  let sin = emptyFunction fn in
  let sinty = TFun (Cil.doubleType, Some ([("x", Cil.doubleType, [])]), false, []) in
  let arg = makeFormalVar sin "x" (Formatcil.cType "double" []) in
  let _ = setFormals sin [arg] in
  let _ = setFunctionType sin sinty in
  libs := Map.add fn sin.svar !libs;

  (* cos *)
  let fn = "cos" in
  let sin = emptyFunction fn in
  let sinty = TFun (Cil.doubleType, Some ([("x", Cil.doubleType, [])]), false, []) in
  let arg = makeFormalVar sin "x" (Formatcil.cType "double" []) in
  let _ = setFormals sin [arg] in
  let _ = setFunctionType sin sinty in
  libs := Map.add fn sin.svar !libs;

  (* Tan *)
  let fn = "tan" in
  let sin = emptyFunction fn in
  let sinty = TFun (Cil.doubleType, Some ([("x", Cil.doubleType, [])]), false, []) in
  let arg = makeFormalVar sin "x" (Formatcil.cType "double" []) in
  let _ = setFormals sin [arg] in
  let _ = setFunctionType sin sinty in
  libs := Map.add fn sin.svar !libs;

  (* asin *)
  let fn = "asin" in
  let sin = emptyFunction fn in
  let sinty = TFun (Cil.doubleType, Some ([("x", Cil.doubleType, [])]), false, []) in
  let arg = makeFormalVar sin "x" (Formatcil.cType "double" []) in
  let _ = setFormals sin [arg] in
  let _ = setFunctionType sin sinty in
  libs := Map.add fn sin.svar !libs;

  (* acos *)
  let fn = "acos" in
  let sin = emptyFunction fn in
  let sinty = TFun (Cil.doubleType, Some ([("x", Cil.doubleType, [])]), false, []) in
  let arg = makeFormalVar sin "x" (Formatcil.cType "double" []) in
  let _ = setFormals sin [arg] in
  let _ = setFunctionType sin sinty in
  libs := Map.add fn sin.svar !libs;
