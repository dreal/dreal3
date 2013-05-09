(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Batteries

type id = int
type mode = Mode.t
type t = (id, mode) Map.t

let of_list (modes : mode list) : t
    =
  List.fold_left
    (fun (map : (id, mode) Map.t) (m : mode) ->
      Map.add (Mode.mode_id m) m map
    )
    Map.empty
    modes

let print out = Map.print Id.print Mode.print out

let find key map =
  try
    Map.find key map
  with e ->
    begin
      Printexc.print_backtrace IO.stdout;
      raise e
    end
