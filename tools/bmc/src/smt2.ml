(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Batteries
type t = Smt2_cmd.t list
let print out smt2 = List.print ~first:"" ~last:"\n" ~sep:"\n" Smt2_cmd.print out smt2
