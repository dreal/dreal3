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



  type id = string
  type cost = float
  type t = (id, cost) Map.t


  let of_modemap  (modes : Modemap.t) : t
      =
      let list_of_modes = (List.of_enum (Map.keys modes)) in
      List.fold_left
      (fun (map : (id, cost) Map.t) (m : id) ->
        Map.add m infinity map
      )
      Map.empty
      list_of_modes

  let print  out  = 
    let id_print out id = Printf.fprintf out "\"%s\""  id in
    let f_print out f = Printf.fprintf out "\"%f\"" (f) in
    Map.print id_print f_print out

  let print_id (h : Hybrid.t) out mycost = 
    let mode_ids = List.of_enum (Map.keys h.modemap) in
    (* let () =  List.print ~first:"[" ~last:"]" ~sep:"," String.print out mode_ids in *)
    let mode_ids_int = List.map (fun x -> (Mode.mode_numId (Modemap.find x h.modemap))) mode_ids in
    (*    let () =  List.print ~first:"[" ~last:"]" ~sep:"," Int.print out mode_ids_int in *)
    let vals = List.map (fun x -> Map.find x mycost) mode_ids in
    (*    let () =  List.print ~first:"[" ~last:"]" ~sep:"," Float.print out vals in *)
    let combo = List.combine mode_ids_int vals in
   (* let () = List.iter (fun x -> (Printf.fprintf out "\"%d\" : \"%f\"" x (List.assoc x combo))) mode_ids_int in *)
    List.print ~first:"{" ~last:"}" ~sep:"," 
	       (fun out x -> (Printf.fprintf out "\"%d\" : \"%f\"" x (List.assoc x combo))) 
	       out mode_ids_int 
  

	      
  let find key map  =
    try
      Map.find key map
    with e ->
      let out = IO.stderr in
      begin
        String.println out "Costmap Exception!";
        Printf.fprintf out "Key: %s\n" (IO.to_string Id.print key);
        Printf.fprintf out "Map: %s\n" (IO.to_string print map );
        Printexc.print_backtrace IO.stdout;
        raise e
      end



end
