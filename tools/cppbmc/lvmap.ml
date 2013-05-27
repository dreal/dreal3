(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)
open Batteries

type key = Cil.lval
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

let print out (m : t) : unit =
  let string_of_lval (lv : Cil.lval) : string =
    Pretty.sprint 80 (Cil.d_lval () lv)
  in
  (Map.print
     ~first: ""
     ~sep: ";\n"
     ~last: ""
     (fun out lv ->
       String.print out ("[, ] ");
       String.print out (string_of_lval lv)
     )
     (fun out n -> String.print out (string_of_int n))
     out
     m);
  print_newline ()
