(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

(* 1. Variable Declaration *)
type vardecl = Vardecl.t

(* 2. Mode *)
type modeId = Mode.id
type mode = Mode.t
type formula = Dr.formula
type exp = Dr.formula

(* 3. Init and Goal *)
type init = modeId * formula
type goal = (modeId * formula) list
type t = vardecl list * mode list * init * goal

let mf_print out (id, f) =
  begin
    BatString.print out "(";
    Id.print out id;
    BatString.print out ", ";
    Dr.print_formula out f;
    BatString.print out ")";
  end

let print out ((varDeclList, (modeList : mode list), init, goal) : t)=
  let print_header out str =
    begin
      BatString.print out "====================\n";
      BatString.print out str;
      BatString.print out "\n====================\n";
    end
  in
  begin
    (* print varDecl list *)
    print_header out "VarDecl List";
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") Vardecl.print out varDeclList;
    (* print mode list *)
    print_header out "Mode List";
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") Mode.print out modeList;
    (* print init *)
    print_header out "Init";
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") mf_print out [init];
    (* print goal *)
    print_header out "Goal";
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") mf_print out goal;
  end
