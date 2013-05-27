(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Batteries
open Pretty
open Printf
open Cil
open Analyze

let files = ref []

(* Parse command-line argument *)
let spec = []
let usage = "./analyze <list_of_input_files>"
let _ = Arg.parse spec
  (fun arg_string ->
    files := String.nsplit arg_string " ";
    List.iter
      (fun f -> if not (Sys.file_exists f) then
          raise (Arg.Bad (f ^ " : no such file")))
      !files)
  usage

let () =
  (* Load each input file. *)
  let files =
    List.map (
      fun filename ->
            let f = Frontc.parse filename in
            f ()
    ) !files in
  (* Merge them. *)
  let file = Mergecil.merge files "test" in
  (* Remove unused prototypes and variables. *)
  Rmtmps.removeUnusedTemps file;
  (* Do control-flow-graph analysis. *)
  Cfg.computeFileCFG file;
  (* Go over the internal CIL structure and print some facts. *)
  List.iter (
    function
      | GType _ -> ()			(* typedef *)
      | GCompTag _ -> ()		(* struct/union *)
      | GCompTagDecl _ -> ()		(* forward prototype of struct/union *)
      | GEnumTag _ -> ()		(* enum *)
      | GEnumTagDecl _ -> ()		(* forward prototype of enum *)
      | GVarDecl _ -> ()		(* variable/function prototype *)
      | GVar _ -> ()			(* variable definition *)
      | GFun (fundec, loc) ->		(* function definition *)
        let (f, s) = analyze_block fundec.sbody Lvmap.empty in
        let out = IO.stdout in
        begin
          IO.write_line out "// ------------------------";
          IO.write_line out "// Variable Ranges";
          IO.write_line out "// ------------------------";
          Lvmap.print   out s;
          IO.write_line out "\n\n";
          IO.write_line out "// ------------------------";
          IO.write_line out "// Transition Relation";
          IO.write_line out "// ------------------------";
          Basic.print_formula out f;
          IO.write_line out "\n\n";
          IO.write_line out "// ------------------------";
          IO.write_line out "// Invariant";
          IO.write_line out "// ------------------------";
        end
      | GAsm _ -> ()			(* global asm statement *)
      | GPragma _ -> ()                 (* toplevel #pragma *)
      | GText _ -> ()			(* verbatim text, comments *)
  ) file.globals;
