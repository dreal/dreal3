open Batteries

type value = Value.t
type var = string
type t = var * value

let print out (var, value) =
  Printf.fprintf out "%s %s" (IO.to_string Value.print value) var
