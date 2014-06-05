(*
 * Dan Bryce dbryce@sift.net
 *)
open Type
open Type.Hybrid
open Type.Basic
open Type.Mode
open Type.Jump
open Batteries
open IO
open Printf


module Costmap = struct



  type id = int
  type cost = float
  type t = (id, cost) Map.t


  let of_modemap (modes : Modemap.t) : t
      =
      let list_of_modes = List.of_enum (Map.keys modes) in
      List.fold_left
      (fun (map : (id, cost) Map.t) (m : id) ->
        Map.add m infinity map
      )
      Map.empty
      list_of_modes

  let print out = 
    let id_print out id = Printf.fprintf out "\"%s\"" (IO.to_string Id.print id) in
    let f_print out f = Printf.fprintf out "\"%f\"" (f) in
    Map.print id_print f_print out
	      
  let find key map =
    try
      Map.find key map
    with e ->
      let out = IO.stderr in
      begin
        String.println out "Modemap Exception!";
        Printf.fprintf out "Key: %s\n" (IO.to_string Id.print key);
        Printf.fprintf out "Map: %s\n" (IO.to_string print map);
        Printexc.print_backtrace IO.stdout;
        raise e
      end



end
