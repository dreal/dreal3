open Batteries

type logic = QF_NRA
             | QF_NRA_ODE

type formula = Basic.formula

type t = SetLogic of logic
         | SetInfo of string * string
         | DeclareFun of string
         | Assert of formula
         | CheckSAT
         | Exit

let make_lb name v = Assert (Basic.Le (Basic.Num v,  Basic.Var name))
let make_ub name v = Assert (Basic.Le (Basic.Var name, Basic.Num v ))

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
      String.print out "(assert ";
      Basic.print_formula out f;
      String.print out ")";
    end
  | CheckSAT ->
    String.print out "(check-sat)"
  | Exit ->
    String.print out "(exit)"
