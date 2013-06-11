open Batteries
type t = {low:float; high:float}

let make l h = {low=l; high=h}

let top = {low=neg_infinity; high=infinity}

let order {low=l1; high=h1} {low=l2; high=h2} =
  l2 <= l1 && h1 <= h2

let width {low=l; high=h} = h -. l

let left_bound {low=l; high=h} = l

let right_bound {low=l; high=h} = h

let print out {low=l; high=h} =
  Printf.fprintf out "[%f, %f]" l h

let equals {low = l1; high = h1} {low = l2; high = h2} : bool
    = ((Float.compare l1 l2) = 0) && ((Float.compare h1 h2) = 0)

let meet {low=l1; high=h1} {low=l2; high=h2} =
  {low = max l1 l2; high = min h1 h2}

let contain_z {low = l; high = h} = l <= 0.0 && 0.0 <= h
let contain_pz {low = l; high = h} = h >= 0.0
let contain_nz {low = l; high = h} = l <= 0.0
