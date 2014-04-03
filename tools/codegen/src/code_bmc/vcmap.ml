(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 * Wei Chen (weichen1@andrew.cmu.edu)
 *)

open Batteries

type key = string
type value = int
type t = (key, value) Map.t

let empty = Map.empty

let update (k : key) (m : t) : t =
  let n =
    match Map.mem k m with
    | true -> (Map.find k m) + 1
    | false -> 0
  in Map.add k n m

(* add a list of keys in one time *)
let rec update_list (ks : key list) (m : t) : t =
  match ks with
  | [] -> m
  | hd :: tl -> update hd (update_list tl m)

let lookup (k : key) (m : t)
    : (value * t)
    = match Map.mem k m with
    | true -> (Map.find k m, m)
    | false -> let v = 0 in
              let m' = Map.add k v m in
              (v, m')

(* take maximum of both maps *)
let join (m1 : t) (m2 : t) : t =
  let join_aux n1_op n2_op = match (n1_op, n2_op) with
    | (Some n1, Some n2) -> Some (max n1 n2)
    | (Some n1, None) -> Some n1
    | (None, Some n2) -> Some n2
    | (None, None) -> None
  in
  Map.merge
    (fun _ n1_op n2_op -> join_aux n1_op n2_op)
    m1
    m2

(* find the keys that are not in the maximum value *)
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
