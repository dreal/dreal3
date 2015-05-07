open Batteries

type origin = string
type destination = string
type t = origin * destination

let print out (origin, destination) =
  Printf.fprintf out "%s %s" origin destination