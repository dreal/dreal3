(* Wei Chen (weichen1@andrew.cmu.edu) *)

type t =
    | Int of int

type macro = 
    | Macro of string * float

type var_decl = 
    | RealVar of string
    | IntVar of string

type exp = 
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

type stmt = 
    | Ode of string * exp

type mode = {
    id : string; 
    args: var_decl list; 
    stmts: stmt list;
}