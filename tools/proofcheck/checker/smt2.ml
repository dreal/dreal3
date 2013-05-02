(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Batteries

exception SMTException of string

type t = Smt2_cmd.t list

let print out smt =
  List.print
    ~first: ""
    ~sep:"\n"
    ~last:"\n"
    Smt2_cmd.print
    out
    smt
