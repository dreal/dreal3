(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type id = Id.t
type formula = Dr.formula
type exp = Dr.exp
type var = string
type inv = formula list
type ode = Dr.ode
type flow = ode
type jump = Jump.t
type jumpmap = Jumpmap.t
type t = id * inv option * flow list * jumpmap

let extract_id m =
  let (id, _, _, _) = m in
  id

let print out (id, inv_op, flows, jumpmap) =
  begin
    BatString.print out "{\n";
    BatString.print out "ModeID = ";
    Id.print out id;
    begin
      match inv_op with
        None -> ()
      | Some inv ->
        begin
          BatString.print out "\nInvariant = ";
          BatList.print ~first:"" ~sep:"\n    " ~last:"\n" Dr.print_formula out inv;
        end
    end;
    BatString.print out "\nFlows = ";
    BatList.print ~first:"" ~sep:"\n    " ~last:"\n" Dr.print_ode out flows;
    BatString.print out "\nJump = ";
    Jumpmap.print out jumpmap;
    BatString.print out "\n}";
  end
