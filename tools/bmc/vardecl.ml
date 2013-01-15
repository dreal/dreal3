type value = Value.t
type var = string
type t = var * value

let print out (var, value) =
  begin
    Value.print out value;
    BatString.print out " ";
    BatString.print out var;
  end
