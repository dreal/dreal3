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

(* 
  Storage for which continuous variables are relevant/reachable in modes.
  Store the first (last) time that variable is 
 *)
module Relevantvariables = struct
  type mode = id
  type varset =  string BatSet.t

  type t = (mode, varset) Map.t
  let of_modelist (modes : Mode.t List.t) : t
      =
      List.fold_left
      (fun (map : (mode, varset) Map.t) (m : Mode.t) ->
        Map.add m.mode_id BatSet.empty map
      )
      Map.empty
      modes	     
	 
  let print out = 
    let mode_print out id = Printf.fprintf out "\"%s\"" (IO.to_string Id.print id) in
    let f_print out f = BatSet.print ~first:"{" ~sep:"," ~last:"}\n" String.print out f in
    Map.print mode_print f_print out
    
end
