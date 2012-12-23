(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type formula = Dr.formula
type id = Id.t
type t = formula * id * formula

let print out (f1, id, f2) =
  begin
    BatString.print out "(";
    Dr.print_formula out f1;
    BatString.print out ", ";
    Id.print out id;
    BatString.print out ",";
    Dr.print_formula out f2;
    BatString.print out ")";
  end

