open Batteries

type label = string
type labelpair = label * label
type t = (label, label) Map.t

let of_list (labels : labelpair list) : t
  =
  List.fold_left
    (fun (map : t) ((label1, label2) : labelpair) ->
     Map.add label1 label2 map
    )
    Map.empty
    labels

let print out = Map.print String.print String.print out

let find key map =
  try
    Map.find key map
  with e ->
    let out = IO.stderr in
    begin
      String.println out "Labelmap Exception!";
      Printf.fprintf out "Key: %s\n" key;
      Printf.fprintf out "Map: %s\n" (IO.to_string print map);
      Printexc.print_backtrace IO.stdout;
      raise e
    end
