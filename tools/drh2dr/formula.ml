(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type exp = Exp.t
type t =
    True
  | False
  | And  of t * t
  | Or   of t * t
  | Gt   of exp * exp
  | Lt   of exp * exp
  | Gte  of exp * exp
  | Lte  of exp * exp
  | Eq   of exp * exp

let rec print out =
  let print_binary_formula op f1 f2 =
    begin
      BatString.print out "(";
      print out f1;
      BatString.print out (" "^op^" ");
      print out f2;
      BatString.print out ")";
    end in
  let print_binary_exp op e1 e2 =
    begin
      BatString.print out "(";
      Exp.print out e1;
      BatString.print out (" "^op^" ");
      Exp.print out e2;
      BatString.print out ")";
    end
  in
  function True -> BatString.print out "True"
    | False -> BatString.print out "False"
    | And (f1, f2) -> print_binary_formula "/\\" f1 f2
    | Or  (f1, f2) -> print_binary_formula "\\/" f1 f2
    | Gt  (e1, e2) -> print_binary_exp ">"  e1 e2
    | Lt  (e1, e2) -> print_binary_exp "<"  e1 e2
    | Gte (e1, e2) -> print_binary_exp ">=" e1 e2
    | Lte (e1, e2) -> print_binary_exp "<=" e1 e2
    | Eq  (e1, e2) -> print_binary_exp "==" e1 e2
