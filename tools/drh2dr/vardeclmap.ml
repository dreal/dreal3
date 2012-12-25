(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type var = Vardecl.var
type value = Vardecl.value
type vardecl = Vardecl.t
type t = (var, value) BatMap.t

let of_list (vardecls : vardecl list) : t
    =
  List.fold_left
    (fun (map : t) ((var, value) : vardecl) ->
      BatMap.add var value map
    )
    BatMap.empty
    vardecls

let print out = BatMap.print BatString.print Value.print out

let find key map =
  try
    BatMap.find key map
  with e ->
    begin
      BatPrintexc.print_backtrace BatIO.stdout;
      raise e
    end
