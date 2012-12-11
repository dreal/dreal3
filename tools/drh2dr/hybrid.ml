(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

(* 1. Variable Declaration *)
type value = Num of float | Intv of float * float
type var = string
type varDecl = var * value

(* 2. Mode *)
type modeId = Mode.id
type formula = Formula.t
type exp = Exp.t
type mode = Mode.t

(* 3. Init and Goal *)
type init = modeId * formula
type goal = (modeId * formula) list
type t = varDecl list * mode list * init * goal

let val_print out v =
  match v with
      Num n -> BatFloat.print out n
    | Intv (n, m) ->
      begin
        BatString.print out "[";
        BatFloat.print out n;
        BatString.print out ", ";
        BatFloat.print out m;
        BatString.print out "]";
      end

let vardecl_print out (var, value) =
  begin
    BatString.print out var;
    BatString.print out " := ";
    val_print out value;
  end

let mf_print out (id, f) =
  begin
    BatString.print out "(";
    BatInt.print out id;
    BatString.print out ", ";
    Formula.print out f;
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
    BatList.print (~first:"") (~sep:"\n") (~last:"\n") vardecl_print out varDeclList;
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
