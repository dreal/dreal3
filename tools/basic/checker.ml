(* check obvious errors of Drh files *)
(* Wei Chen weichen1@andrew.cmu.edu *)

open Type
open Type.Hybrid

let ast_checker =
  fun {varmap; modemap} ->
  ()

(* check every flow must have variable declaration *)
let check_flowdef flows vars =
  List.iter
    (fun (x, _) ->
     if List.mem x vars = false then
       failwith "Missing variable definition for flow"
     else ()
    )
    flows

(* make sure time declaration *)
let check_time vars =
  if List.mem "time" vars = false then
    failwith "Missing 'time' declaration "
  else ()

(* allow auto expansion of variables remain the same in next step *)
let expand_identity h = ()
