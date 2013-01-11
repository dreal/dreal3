type t = string * Dr.exp

let print out (x, e) =
  begin
    BatString.print out "(define-ode (";
    BatString.print out "= ";
    BatString.print out "d/dt[";
    BatString.print out x;
    BatString.print out "] ";
    Dr.print_exp out e;
    BatString.print out "))";
  end
