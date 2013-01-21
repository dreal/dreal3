include Interval
type t = interval

let make l h = {low=l; high=h}

let order {low=l1; high=h1} {low=l2; high=h2} =
  l2 <= l1 && h1 <= h2

let equals {low = l1; high = h1} {low = l2; high = h2} : bool
    = (BatFloat.compare l1 l2) = 0 && (BatFloat.compare h1 h2) = 0

let join = Interval.union_I_I

let contain_z {low = l; high = h} = l <= 0.0 && 0.0 <= h
let contain_pz {low = l; high = h} = h >= 0.0
let contain_nz {low = l; high = h} = l <= 0.0

let print out {low=l; high=h} =
  begin
    BatString.print out "[";
    BatFloat.print  out l;
    BatString.print out ", ";
    BatFloat.print  out h;
    BatString.print out "]"
  end
