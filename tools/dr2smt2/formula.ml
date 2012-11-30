(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

type exp = Exp.t
type t =
| True
| False
| Not of t
| And of t list
| Or  of t list
| Gt  of exp * exp
| Lt  of exp * exp
| Ge  of exp * exp
| Le  of exp * exp
| Eq  of exp * exp

let make_and (fs : t list) : t =
  let fs' = List.fold_left
    (fun res f -> match (res, f) with
    | ([False], _) -> [False]        (* False /\ _   -> False *)
    | (_, False) -> [False]          (* ... /\ False -> False *)
    | (res, True) -> res             (* res /\ True  -> res *)
    | (res, And fs'') -> res @ fs''  (* res /\ (/\ fs) -> res /\ fs *)
    | (res, f) -> res @ [f])         (* res /\ f -> res /\ f *)
    []
    fs
  in match fs' with
  | [] -> True
  | f::[] -> f
  | fs' -> And fs'

let make_or (fs : t list) : t =
  let fs' = List.fold_left
    (fun res f -> match (res, f) with
    | ([True], _) -> [True]        (* True \/ _   -> True *)
    | (_, True) -> [True]          (* ... \/ True -> True *)
    | (res, False) -> res             (* res \/ False  -> res *)
    | (res, Or fs'') -> res @ fs''  (* res \/ (\/ fs) -> res \/ fs *)
    | (res, f) -> res @ [f])         (* res \/ f -> res \/ f *)
    []
    fs
  in match fs' with
  | [] -> False
  | f::[] -> f
  | fs' -> Or fs'

let rec map_exp (func : exp -> exp) (f : t)
    : t
    = match f with
    | True -> f
    | False -> f
    | Not f' -> Not (map_exp func f')
    | And fs -> And (List.map (map_exp func) fs)
    | Or fs -> Or (List.map (map_exp func) fs)
    | Gt (e1, e2) -> Gt(func e1, func e2)
    | Lt (e1, e2) -> Lt(func e1, func e2)
    | Ge (e1, e2) -> Ge(func e1, func e2)
    | Le (e1, e2) -> Le(func e1, func e2)
    | Eq (e1, e2) -> Eq(func e1, func e2)

let rec print out =
  let print_lists op out f items =
    begin
      BatList.print
        (~first:("("^op^" "))
        (~sep:" ")
        (~last:")")
        f
        out
        items
    end
  in
  let print_exps op exps = print_lists op out Exp.print exps in
  let print_formulas op formulas = print_lists op out print formulas in
  function
  | True -> BatString.print out "true"
  | False -> BatString.print out "false"
  | Not f -> print_formulas "not" [f]
  | And fs -> print_formulas "and" fs
  | Or  fs -> print_formulas "or"  fs
  | Gt  (e1, e2) -> print_exps ">"  [e1; e2]
  | Lt  (e1, e2) -> print_exps "<"  [e1; e2]
  | Ge  (e1, e2) -> print_exps ">=" [e1; e2]
  | Le  (e1, e2) -> print_exps "<=" [e1; e2]
  | Eq  (e1, e2) -> print_exps "="  [e1; e2]
