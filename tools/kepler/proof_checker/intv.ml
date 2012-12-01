include Interval
type t = interval
let order {low=l1; high=h1} {low=l2; high=h2} =
  l2 <= l1 && h1 <= h2
let make l h = {low=l; high=h}
let contain_zero {low = l; high = h} = l <= 0.0 && 0.0 <= h
