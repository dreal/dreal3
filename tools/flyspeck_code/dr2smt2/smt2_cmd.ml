type logic = QF_NRA
             | QF_NRA_ODE

type exp = Dr.exp
type formula = Dr.formula

type t = SetLogic of logic
         | DeclareFun of string
         | Assert of formula
         | CheckSAT
         | Exit

let print_logic out =
  function
  | QF_NRA -> BatString.print out "QF_NRA"
  | QF_NRA_ODE -> BatString.print out "QF_NRA_ODE"

let print out =
  function
  | SetLogic l ->
    begin
      BatString.print   out "(set-logic ";
      print_logic out l;
      BatString.print out ")";
    end
  | DeclareFun v ->
    begin
      BatString.print   out "(declare-fun ";
      BatString.print   out v;
      BatString.print out " () Real)";
    end
  | Assert f ->
    begin
      BatString.print out "(assert ";
      Dr.print_formula out f;
      BatString.print out ")";
    end
  | CheckSAT ->
    BatString.print out "(check-sat)"
  | Exit ->
    BatString.print out "(exit)"
