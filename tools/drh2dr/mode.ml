(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type id = Id.t
type formula = Dr.formula
type exp = Dr.exp
type var = string
type macro = formula list
type inv = formula list
type ode = Dr.ode
type flow = ode
type jump = Jump.t
type jumpmap = Jumpmap.t
type t = id * macro * inv * flow list * jumpmap

let extract_id m =
  let (id, _, _, _, _) = m in
  id

let print out (id, macro, inv, flow, jm) =
  begin
    BatString.print out "{\n";
    BatString.print out "ModeID = ";
    Id.print out id;
    BatString.print out "\nMacro = ";
    BatList.print (~first:"") (~sep:"\n    ") (~last:"\n") Dr.print_formula out macro;
    BatString.print out "\nInvariant = ";
    BatList.print (~first:"") (~sep:"\n    ") (~last:"\n") Dr.print_formula out inv;
    BatString.print out "\nFlow = ";
    BatList.print (~first:"") (~sep:"\n    ") (~last:"\n") Dr.print_ode out flow;
    BatString.print out "\nJump = ";
    Jumpmap.print Id.print Jump.print out jm;
    BatString.print out "\n}";
  end
