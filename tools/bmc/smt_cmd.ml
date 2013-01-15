type logic = QF_NRA
             | QF_NRA_ODE

type exp = Dr.exp
type formula = Dr.formula

type t = SetLogic of logic
         | DeclareFun of string
         | DefineODE of string * exp
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
    print_logic out l
  | DeclareFun v ->
    begin
      BatString.print   out "(declare-fun ";
      BatString.print   out v;
      BatString.println out " () Real)";
    end
  | DeclareODE (x, e) ->
    begin
      BatString.print out "(define-ode (";
      BatString.print out "= ";
      BatString.print out "d/dt[";
      BatString.print out x;
      BatString.print out "] ";
      Dr.print_exp out e;
      BatString.println out "))";
    end
  | Assert f ->
    begin
      BatString.print out "(assert (";
      Dr.print_formula out f;
      BatString.println out "))";
    end
  | CheckSAT ->
    BatString.println out "(check-sat)"
  | Exit ->
    BatString.println out "(exit)"
