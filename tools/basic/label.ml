open Batteries

type name = string
type t = { name: name }

let print out name =
  Printf.fprintf out "%s" name
