open Batteries
open Cil

let libs : (string, Cil.varinfo) Map.t ref = ref (Map.empty)

let add_math_func (fn_name : string) (arg_tys : Cil.typ list) (ret_ty : Cil.typ)
    : unit =
  let fn = emptyFunction fn_name in
  let arg_postfixes = List.range 0 `To (List.length arg_tys - 1) in
  let arg_names = List.map (fun n -> "x_" ^ (Int.to_string n)) arg_postfixes in
  let args = List.map2 (fun name ty -> (name, ty, [])) arg_names arg_tys in
  let args_opt = match arg_tys with
    | [] -> None
    | _ -> Some args in
  let fn_ty = TFun (ret_ty, args_opt, false, []) in
  let arg_varinfos =
    List.map2 (fun name ty -> makeFormalVar fn name ty)
      arg_names
      arg_tys
  in
  let _ = setFormals fn arg_varinfos in
  let _ = setFunctionType fn fn_ty in
  libs := Map.add fn_name fn.svar !libs

let math_funcs = [("sin", [Cil.doubleType], Cil.doubleType);
                  ("cos", [Cil.doubleType], Cil.doubleType);
                  ("tan", [Cil.doubleType], Cil.doubleType);
                  ("acos", [Cil.doubleType], Cil.doubleType);
                  ("asin", [Cil.doubleType], Cil.doubleType);
                  ("atan", [Cil.doubleType], Cil.doubleType);
                  ("atan2", [Cil.doubleType; Cil.doubleType], Cil.doubleType);
                  ("cosh", [Cil.doubleType], Cil.doubleType);
                  ("sinh", [Cil.doubleType], Cil.doubleType);
                  ("tanh", [Cil.doubleType], Cil.doubleType);
                  ("abs", [Cil.doubleType], Cil.doubleType);
                  ("exp", [Cil.doubleType], Cil.doubleType);
                  ("exp2", [Cil.doubleType], Cil.doubleType);
                  ("pow", [Cil.doubleType; Cil.doubleType], Cil.doubleType);
                  ("sqrt", [Cil.doubleType], Cil.doubleType);
                  ("log", [Cil.doubleType], Cil.doubleType);
                  ("log2", [Cil.doubleType], Cil.doubleType);
                  ("log10", [Cil.doubleType], Cil.doubleType);
                 ]

let drh_stl_init () =
  List.iter
    (fun (name, arg_tys, ret_ty) -> add_math_func name arg_tys ret_ty)
    math_funcs
