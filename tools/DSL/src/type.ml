(* Wei Chen (weichen1@andrew.cmu.edu) *)

type t = (macro list) * (mode list) * main_entry

and macro = 
    | Macro of string * float

and var_decl = 
    | RealVar of string
    | IntVar of string

and exp = 
    | Var of string
    | Num of float
    | Neg      of exp
    | Add      of exp list
    | Sub      of exp list
    | Mul      of exp list
    | Div      of exp * exp
    | Pow      of exp * exp
    | Ite      of formula * exp * exp
    | Sqrt     of exp
    | Safesqrt of exp
    | Abs      of exp
    | Log      of exp
    | Exp      of exp
    | Sin      of exp
    | Cos      of exp
    | Tan      of exp
    | Asin     of exp
    | Acos     of exp
    | Atan     of exp
    | Atan2    of exp * exp
    | Matan    of exp
    | Sinh     of exp
    | Cosh     of exp
    | Tanh     of exp
    | Asinh    of exp
    | Acosh    of exp
    | Atanh    of exp

    (* (integral 0 time_1 [x_1_0 ... x_i_0] flow1) *)
    | Integral of float * string * string list * string
and formula =
    | True
    | False
    | FVar of string
    | Not of formula
    | And of formula list
    | Or  of formula list
    | Imply of formula * formula
    | Gt  of exp * exp
    | Lt  of exp * exp
    | Ge  of exp * exp
    | Le  of exp * exp
    | Eq  of exp * exp
    | LetF of ((string * formula) list * formula)
    | LetE of ((string * exp) list * formula)
    | ForallT of formula
and bexp = 
    | B_gt  of exp * exp
    | B_lt  of exp * exp
    | B_ge  of exp * exp
    | B_le  of exp * exp
    | B_eq  of exp * exp
    | B_true
    | B_false

(* switch *)
and flow = 
    | Switch of string * choice list
and choice = 
    | Case of float * stmt list

and stmt = 
    | Ode of string * exp
    | Assert of formula
    | Assign of string * exp
    | If1 of bexp * stmt list
    | If2 of bexp * stmt list * stmt list
    | Proceed of float * float * flow
    | Call of string * string list

and main_entry = 
    | Main of (stmt list)

and mode = {
    id : string; 
    args: var_decl list; 
    stmts: stmt list;
}