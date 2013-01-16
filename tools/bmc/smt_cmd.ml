type logic = QF_NRA
             | QF_NRA_ODE

type exp = Dr.exp
type formula = Dr.formula

type t = SetLogic of logic
         | DeclareFun of string
         | DefineODE of int * string * exp
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
  | DefineODE (n, x, e) ->
    begin
      BatString.print out "(define-ode ";
      BatInt.print out n;
      BatString.print out " (";
      BatString.print out "= ";
      BatString.print out "d/dt[";
      BatString.print out x;
      BatString.print out "] ";
      Dr.print_infix_exp out e;
      BatString.print out "))";
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
