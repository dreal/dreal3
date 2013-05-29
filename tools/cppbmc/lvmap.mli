(** Lvalue Map
    @author Soonho Kong
*)

type key = Cil.lval
type value = int
type t

val empty : t
(** empty lvmap *)

val update : key -> t -> t
(** [update k m] returns [m'] where [m'[k]] is the increased value of
    [m[k]] *)

val lookup : key -> t -> (value * t)
(** [lookup k m] returns [n] if [n] is associated with [k] in [m].

    @raise Not_found if [k] is unbound in [m].
*)

val join : t -> t -> t
(** [join m1 m2] returns a joined map [m]. It takes the maximum value
    if the two input maps have entries for a key. *)

val diff : t -> t -> (key * value * value) list
(** [diff m1 m2] returns a list of [(k, n1, n2)] where
    - [m1] has [k] and
    - [m2] has [k] and
    - [m1[k]] = [n1] and [m2[k]] = [n2] and
    - [n1] < [n2]
*)

val print : 'a BatInnerIO.output -> t -> unit
(** Pretty print *)
