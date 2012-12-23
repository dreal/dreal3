(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

(* 1. Variable Declaration *)
type vardeclmap = Vardeclmap.t

(* 2. Mode *)
type modeId = Mode.id
type mode = Mode.t
type modemap = Modemap.t
type formula = Dr.formula
type exp = Dr.formula

(* 3. Init and Goal *)
type init = modeId * formula
type goals = (modeId * formula) list
type t = vardeclmap * modemap * init * goals

let mf_print out (id, f) =
  begin
    BatString.print out "(";
    Id.print out id;
    BatString.print out ", ";
    Dr.print_formula out f;
    BatString.print out ")";
  end

let print out (((vm : Vardeclmap.t), (mm : Modemap.t), init, goals) : t)=
  let print_header out str =
    begin
      BatString.print out "====================\n";
      BatString.print out str;
      BatString.print out "\n====================\n";
    end
  in
  begin
    (* print varDecl list *)
    print_header out "VarDecl Map";
    Vardeclmap.print out vm;
    (* print mode list *)
    print_header out "Mode Map";
    Modemap.print out mm;
    (* print init *)
    print_header out "Init";
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") mf_print out [init];
    (* print goal *)
    print_header out "Goal";
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") mf_print out goals;
  end
