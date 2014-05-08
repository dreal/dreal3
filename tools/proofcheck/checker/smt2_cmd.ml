open Batteries
open Basic

type logic = QF_NRA
             | QF_NRA_ODE

type formula = Basic.formula

type t = SetLogic of logic
         | SetInfo of string * string
         | DeclareFun of string
         | Assert of formula
         | CheckSAT
         | Exit

let make_lb name v = Assert (Le (Num v,  Var name))
let make_ub name v = Assert (Le (Var name, Num v ))

let print_logic out =
  function
  | QF_NRA -> String.print out "QF_NRA"
  | QF_NRA_ODE -> String.print out "QF_NRA_ODE"

let print out =
  function
  | SetLogic l ->
    begin
      String.print   out "(set-logic ";
      print_logic out l;
      String.print out ")";
    end
  | SetInfo (key, value) ->
    begin
      String.print out "(set-info ";
      String.print out key;
      String.print out " ";
      String.print out value;
      String.print out ")";
    end
  | DeclareFun v ->
    begin
      String.print   out "(declare-fun ";
      String.print   out v;
      String.print out " () Real)";
    end
  | Assert f ->
     begin
       (* ignore trivial constraints *)
       let print f =
         begin
           String.print out "(assert ";
           print_formula out f;
           String.print out ")";
         end
       in
       match f with
       | (Gt (_, Num x)) -> if x = infinity then () else print f
       | (Ge (_, Num x)) -> if x = infinity then () else print f
       | (Lt (Num x, _)) -> if x = neg_infinity then () else print f
       | (Le (Num x, _)) -> if x = neg_infinity then () else print f
       | _ -> print f
     end
  | CheckSAT ->
    String.print out "(check-sat)"
  | Exit ->
    String.print out "(exit)"
