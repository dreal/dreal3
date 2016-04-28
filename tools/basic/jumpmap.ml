open Batteries
type id = string
type jump = Jump.t
type t = (id, jump) Map.t

let of_list (jumps : jump list) : t
  =
  List.fold_left
    (fun (map : t) ({Jump.guard = g; Jump.target = t; Jump.change = c; Jump.label = l} as j) ->
     Map.add t j map
    )
    Map.empty
    jumps

let print out = Map.print Id.print Jump.print out

let find key map =
  try
    Map.find key map
  with e ->
    let out = IO.stderr in
    begin
      String.println out "Jumpmap Exception!";
      Printf.fprintf out "Key: %s\n" (IO.to_string Id.print key);
      Printf.fprintf out "Map: %s\n" (IO.to_string print map);
      Printexc.print_backtrace out;
      raise e
    end
