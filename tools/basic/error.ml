(*
 * Errors and handlers
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

exception Lex_err of string * int
exception Domain_Mismatch of string
exception Variable_Label_Match of string
exception Variable_Label_Mapping of string
exception Automaton_Not_Found of string
exception Instance_Error of string * string
exception Composition_Error of string
exception Pathgen_Error of string

let linenum = ref 1
let incr_ln () = linenum := !linenum + 1
let decr_ln () = linenum := !linenum - 1
let get_ln () = !linenum

let init () = linenum := 1

let handle_exn v =
  match v with
      Lex_err (s, i) ->
	Printf.eprintf ">> lexical error at line %d: %s\n" i s
    | Parsing.Parse_error ->
      Printf.eprintf ">> syntax error at line %d\n" !linenum
    | Arg.Bad s ->
      Printf.eprintf ">> file format error: %s\n" s
    | Domain_Mismatch s ->
      Printf.eprintf ">> domain mismatch: %s\n" s
    | Variable_Label_Match s ->
       Printf.eprintf ">> variable and name share same identifier: %s\n" s
    | Automaton_Not_Found s ->
       Printf.eprintf ">> automaton not found: %s\n" s
    | Instance_Error (temp, inst) ->
       Printf.eprintf ">> unable to instanciate %s: %s not defined.\n" inst temp
    | Composition_Error s ->
       Printf.eprintf ">> undefined automaton: %s\n" s
    |  _ -> raise v
