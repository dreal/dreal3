(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type id = int
type jump = Jump.t
type t = (id, jump) BatMap.t

let of_list (jumps : jump list) : t
    =
  List.fold_left
    (fun (map : t) ((f1, target, f2) as j) ->
      BatMap.add target j map
    )
    BatMap.empty
    jumps

let print out = BatMap.print Id.print Jump.print out

let find key map =
  try
    BatMap.find key map
  with e ->
    let out = BatIO.stdout in
    begin
      BatString.println out "Jumpmap Exception!";
      BatString.print out "Key: ";
      Id.print out key;
      BatString.println out "";
      BatString.print out "Map: ";
      print out map;
      BatString.println out "";
      BatPrintexc.print_backtrace out;
      raise e
    end

