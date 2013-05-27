(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)
open BatPervasives
type fintv = float * float
type t = fintv * string * int option

let string_of_float n =
  (* If n ends with ".", add "0" to make ".0" *)
  let s = BatFloat.to_string n in
  match BatString.ends_with s "." with
  | true -> s ^ "0"
  | false -> s

let unfold (vardecls : t list) : (t list)
    =
  List.concat
    (List.map
       (fun (((l, u), id, n_op) as decl) ->
         match n_op with
         | Some n ->
           BatList.map (fun n -> ((l, u), id ^ (string_of_int n), None)) (BatList.of_enum (0 -- n))
         | None -> [decl]
       )
       vardecls
    )

let print out ((l, u), id, n_op) =
  begin
    BatString.print out "[";
    BatString.print out (string_of_float l);
    BatString.print out ", ";
    BatString.print out (string_of_float u);
    BatString.print out "] ";
    BatString.print out id;
    begin
      match n_op with
      | Some n ->
        BatString.print out " : ";
        BatString.print out (string_of_int n)
      | None -> ()
    end;
    BatString.print out ";";
  end
