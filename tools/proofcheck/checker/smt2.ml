(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open BatPervasives

exception SMTException of string

type t = Smt2_cmd.t list

let print out smt =
  BatList.print
    (~first: "")
    (~sep:"\n")
    (~last:"\n")
    Smt2_cmd.print
    out
    smt
