open Batteries

type logic = QF_NRA
             | QF_NRA_ODE
type exp = Basic.exp
type formula = Basic.formula
type t = SetLogic of logic
         | SetInfo of string * string
         | DeclareFun of string
         | DeclareConst of string
         | DefineODE of int * int * string * exp
         | Assert of formula
         | CheckSAT
         | Exit

let make_lb (name : string) (v : float)
    = Assert (Basic.Le (Basic.Num v,  Basic.Var name))
let make_ub (name : string) (v : float)
    = Assert (Basic.Le (Basic.Var name, Basic.Num v ))

let set_precision (p : float) : t =
  SetInfo (":precision", string_of_float p)

let print_logic out =
  function
  | QF_NRA -> String.print out "QF_NRA"
  | QF_NRA_ODE -> String.print out "QF_NRA_ODE"

let print out =
  function
  | SetLogic l ->
    Printf.fprintf out "(set-logic %s)" (IO.to_string print_logic l)
  | SetInfo (key, value) ->
    Printf.fprintf out "(set-info %s %s)" key value
  | DeclareFun v ->
    Printf.fprintf out "(declare-fun %s () Real)" v
  | DeclareConst v ->
    Printf.fprintf out "(declare-const %s Real)" v
  | DefineODE (g, sg, x, e) ->
    Printf.fprintf out "(define-ode %d %d (= d/dt[%s] %s))" g sg x (IO.to_string Basic.print_infix_exp e)
  | Assert f ->
    Printf.fprintf out "(assert %s)" (IO.to_string Basic.print_formula f)
  | CheckSAT ->
    String.print out "(check-sat)"
  | Exit ->
    String.print out "(exit)"
