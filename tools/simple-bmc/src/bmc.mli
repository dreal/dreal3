(*
 * Soonho Kong soonhok@cs.cmu.edu
 * Wei Chen ipondering.weic@gmail.com
 *)
open Type
open Type.Hybrid
open Type.Basic
open Type.Mode
open Type.Jump
open Batteries
open IO
open Smt2_cmd
open Smt2

exception SMTException of string

(** a list of annoted flow ode **)
type flows_annot = (int * int * ode) list  (** step, mode, ode **)

(** compile a Hybrid automata into SMT formula **)
val compile : Hybrid.t -> int -> Smt2.t
