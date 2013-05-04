(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)
open Batteries

type var = Vardecl.var
type value = Vardecl.value
type vardecl = Vardecl.t
type t = (var, value) Map.t

let of_list (vardecls : vardecl list) : t
    =
  List.fold_left
    (fun (map : t) ((var, value) : vardecl) ->
      Map.add var value map
    )
    Map.empty
    vardecls

let print out = Map.print String.print Value.print out

let find key map =
  try
    Map.find key map
  with e ->
    begin
      Printexc.print_backtrace IO.stdout;
      raise e
    end
