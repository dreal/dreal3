type value = Value.t
type var = string
type t = var * value

let print out (var, value) =
  begin
    BatString.print out var;
    BatString.print out " := ";
    Value.print out value;
  end
