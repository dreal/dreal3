(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type id = int
type formula = Dr.formula
type exp = Dr.exp
type var = string
type macro = formula list
type inv = formula list
type ode = Dr.ode
type flow = ode
type jump = formula * id * formula
type t = id * macro * inv * flow list * jump list

let print_fmf out (f1, id, f2) =
  begin
    BatString.print out "(";
    Dr.print_formula out f1;
    BatString.print out ", ";
    BatInt.print out id;
    BatString.print out ",";
    Dr.print_formula out f2;
    BatString.print out ")";
  end

let print out (id, macro, inv, flow, jump) =
  begin
    BatString.print out "{\n";
    BatString.print out "ModeID = ";
    BatInt.print out id;
    BatString.print out "\nMacro = ";
    BatList.print (~first:"") (~sep:"\n    ") (~last:"\n") Dr.print_formula out macro;
    BatString.print out "\nInvariant = ";
    BatList.print (~first:"") (~sep:"\n    ") (~last:"\n") Dr.print_formula out inv;
    BatString.print out "\nFlow = ";
    BatList.print (~first:"") (~sep:"\n    ") (~last:"\n") Dr.print_ode out flow;
    BatString.print out "\nJump = ";
    BatList.print (~first:"") (~sep:"\n    ") (~last:"\n") print_fmf out jump;
    BatString.print out "\n}";
  end
