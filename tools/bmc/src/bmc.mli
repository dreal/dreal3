(*
 * Soonho Kong soonhok@cs.cmu.edu
 * Wei Chen weichen1@andrew.cmu.edu
 *)
open Type
open Type.Hybrid
open Type.Basic
open Type.Mode
open Type.Jump
open Costmap
open Relevantvariables
open Batteries
open IO
open Smt2_cmd
open Smt2

exception SMTException of string

(** a list of annoted flow ode **)
type flows_annot = (string * ode list)  (** step, mode, ode **)

(** compile a Hybrid automata into SMT formula **)
val compile : Network.t -> int -> (string list) option -> (Costmap.t list option) -> Smt2_cmd.t list
val pathgen : Network.t -> int -> (string list) list
