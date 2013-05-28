(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Batteries
open Cil

type key = lval
type value = int
type t = (key, value) Map.t

let empty = Map.empty

let update (k : key) (m : t) : t =
  let n =
    match Map.mem k m with
    | true -> (Map.find k m) + 1
    | false -> 0
  in Map.add k n m


let lookup (k : key) (m : t)
    : (value * t)
    = match Map.mem k m with
    | true -> (Map.find k m, m)
    | false -> let v = 0 in
              let m' = Map.add k v m in
              (v, m')

let join (m1 : t) (m2 : t) : t =
  let join_aux n1_op n2_op = match (n1_op, n2_op) with
    | (Some n1, Some n2) -> Some (max n1 n2)
    | (Some n1, None) -> Some n1
    | (None, Some n2) -> Some n2
    | (None, None) -> None
  in
  Map.merge
    (fun k n1_op n2_op -> join_aux n1_op n2_op)
    m1
    m2

let diff (m1 : t) (m2 : t) : (key * value * value) list =
  Map.foldi
    (fun k n1 res ->
      match Map.mem k m2 with
      | true ->
        begin
          let n2 = Map.find k m2 in
          match n1 < n2 with
          | true -> (k, n1, n2)::res
          | false -> res
        end
      | false -> res
    )
    m1
    []

let extract_range_from_attrs attrs : (float * float) =
  match attrs with
    (Attr (attr_str, [AStr param]))::[] ->
      let (lb, ub) =
        match List.map Float.of_string (String.nsplit param ",") with
          [n1; n2] -> (n1, n2)
        | _ -> failwith ("Fail to extract range information from attributes: " ^ param)
      in
      (lb, ub)
  | _ -> (0.0, 0.0)

let rec extract_range_from_typ typ offset =
  match (typ, offset) with
    (TFloat (_, attrs), _) ->
      let (lb, ub) = extract_range_from_attrs attrs in
      Printf.printf "[%f, %f] " lb ub
  | (TVoid _, _) -> failwith "LVMAP extract_range_from_typ with Non TVoid"
  | (TInt _, _) ->
    String.print IO.stdout "INTEGER! ";
  | (TPtr (typ', _), _) -> extract_range_from_typ typ' offset
  | (TArray _, _) -> failwith "LVMAP extract_range_from_typ with Non TArray"
  | (TFun _, _) -> failwith "LVMAP extract_range_from_typ with Non TFun"
  | (TNamed (tinfo, _), _) ->  extract_range_from_typ tinfo.ttype offset
  | (TComp _, Field (finfo, offset')) -> extract_range_from_typ finfo.ftype offset'
  | (TComp _, NoOffset) -> failwith "LVMAP extract_range_from_typ with Non TComp + NoOffset"
  | (TEnum _, _) -> failwith "LVMAP extract_range_from_typ with Non TEnum"
  | (TBuiltin_va_list _, _) -> failwith "LVMAP extract_range_from_typ with Non TBuiltin_va_list"

let print out (m : t) : unit =
  let string_of_lval (lv : lval) : string =
    Pretty.sprint 80 (d_lval () lv)
  in
  (Map.print
     ~first: ""
     ~sep: ";\n"
     ~last: ""
     (fun out lv ->
       (match lv with
         (Var vinfo, offset) -> extract_range_from_typ vinfo.vtype offset
       | (Mem (Lval (Var vinfo, _)), offset) -> extract_range_from_typ vinfo.vtype offset
       | (Mem _, _) -> failwith "LVMAP Print with Mem");
       String.print out (string_of_lval lv);
     )
     (fun out n -> String.print out (string_of_int n))
     out
     m);
  print_newline ()
