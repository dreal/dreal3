open Batteries

type logic = QF_NRA
             | QF_NRA_ODE
type exp = Basic.exp
type formula = Basic.formula
type t = SetLogic of logic
         | DeclareFun of string
         | DefineODE of int * string * exp
         | Assert of formula
         | CheckSAT
         | Exit

let print_logic out =
  function
  | QF_NRA -> String.print out "QF_NRA"
  | QF_NRA_ODE -> String.print out "QF_NRA_ODE"

let print out =
  function
  | SetLogic l ->
    Printf.fprintf out "(set-logic %s)" (IO.to_string print_logic l)
  | DeclareFun v ->
    Printf.fprintf out "(declare-fun %s () Real)" v
  | DefineODE (n, x, e) ->
    Printf.fprintf out "(define-ode %d (= d/dt[%s] %s))" n x (IO.to_string Basic.print_infix_exp e)
  | Assert f ->
    Printf.fprintf out "(assert %s)" (IO.to_string Basic.print_formula f)
  | CheckSAT ->
    String.print out "(check-sat)"
  | Exit ->
    String.print out "(exit)"
