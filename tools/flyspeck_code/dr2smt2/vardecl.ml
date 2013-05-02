(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)
open BatPervasives
type fintv = float * float
type t = fintv * string

let string_of_float n =
  (* If n ends with ".", add "0" to make ".0" *)
  let s = BatFloat.to_string n in
  match BatString.ends_with s "." with
  | true -> s ^ "0"
  | false -> s

let print out ((l, u), id) =
  begin
    BatString.print out "[";
    BatString.print out (string_of_float l);
    BatString.print out ", ";
    BatString.print out (string_of_float u);
    BatString.print out "] ";
    BatString.print out id;
    BatString.print out ";";
  end
