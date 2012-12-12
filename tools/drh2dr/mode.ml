(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type id = int
type formula = Dr.formula
type exp = Dr.exp
type var = string
type macro = formula list
type inv = formula list
type ode = var * exp
type flow = ode list
type jump = (formula * id * formula) list
type t = id * macro * inv * flow * jump

let ode_print out (v, e) =
  begin
    BatString.print out "(";
    BatString.print out v;
    BatString.print out ", ";
    Dr.print_exp out e;
    BatString.print out ")";
  end

let fmf_print out (f1, id, f2) =
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
    BatList.print Dr.print_formula out macro;
    BatString.print out "\nInvariant = ";
    BatList.print Dr.print_formula out inv;
    BatString.print out "\nFlow = ";
    BatList.print ode_print out flow;
    BatString.print out "\nJump = ";
    BatList.print fmf_print out jump;
    BatString.print out "\n}";
  end
