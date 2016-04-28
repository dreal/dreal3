open Batteries

type t = string
let print = String.print

let compose i1 i2 =
  String.concat "_" [i1; i2]
