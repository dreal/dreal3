open Batteries
open IO
open Type

let dt = ref 0.0001

(* Code Generation *)
let rec emit_defs macros =
  match macros with
  | [] -> ()
  | Macro (name, v)::tl -> Printf.printf "#define %s %f\n" name v; emit_defs tl

(*
 1. function argument
 2. variable declaration
*)
let arg_str out =
  function
  | RealVar s -> Printf.fprintf out "double & %s" s
  | BRealVar (s, _, _) -> Printf.fprintf out "double & %s" s
  | IntVar s -> Printf.fprintf out "int & %s" s

let emit_args args =
  List.print ~first: ""
             ~sep:","
             ~last:""
             arg_str
             IO.stdout
             args

let rec emit_stmt out =
  function
  | Ode (s, exp) ->
     Printf.fprintf out "%s = " s;
     emit_exp out exp;
     Printf.fprintf out " + %f * %s;" !dt s;
  | Assert _ -> ()
  | Assign1 (s, exp) -> ()
  | Assign (s, exp) ->
     Printf.fprintf out "%s = " s;
     emit_exp out exp;
     Printf.fprintf out ";";
  | If (bexp, conseq, alter) ->
     Printf.fprintf out "if (";
     emit_bexp out bexp;
     Printf.fprintf out "){\n";
     emit_stmts out conseq;
     Printf.fprintf out "\n";
     Printf.fprintf out "}";
     if List.length alter > 0 then
       begin
         Printf.fprintf out " else {\n";
         emit_stmts out alter;
         Printf.fprintf out "}";
       end
     else ()
  | Proceed stmts ->
     Printf.fprintf out "while (1) {\n";
     emit_stmts out stmts;
     Printf.fprintf out "}";
  | Vardecls vardecls ->
     List.iter
       (fun vardecl ->
        arg_str out vardecl;
        Printf.fprintf out ";";
       )
       vardecls;
  | Switch (s, choices) -> ()
  | Expr exp ->
     emit_exp out exp;
     Printf.fprintf out ";"

(* list of statements *)
and emit_stmts out stmts =
  List.print ~first: ""
             ~sep: "\n"
             ~last: "\n"
             emit_stmt
             out
             stmts

(* Mode definition *)
and emit_mode mode =
  let {id; args; stmts} = mode in
  Printf.printf "void %s (" id;
  emit_args args;
  print_endline ")";
  print_endline "{";
  emit_stmts IO.stdout stmts;
  print_endline "}"

(* list of mode definition *)
and emit_modes modes =
  match modes with
  | [] -> ()
  | m::tl ->
     emit_mode m;
     emit_modes tl

(* Main entry point *)
and emit_main main =
  let Main stmts = main in
  print_endline "int main() {";
  emit_stmts IO.stdout stmts;
  print_endline "}"

and emit_program (ast : Type.t) =
  let {macros; modes; main} = ast in
  let _ = emit_defs macros in
  print_newline ();
  let _ = emit_modes modes in
  print_newline ();
  emit_main main

and emit_exp out=
    let print_exps op exps =
      begin
        List.print
          ~first:"("
          ~sep: (" " ^ op ^ " ")
          ~last:")"
          emit_exp
          out
          exps
      end
    in
    function
    | Call (n, args) ->
       Printf.fprintf out "%s" n;
       List.print
         ~first:"("
         ~sep: ","
         ~last: ")"
         emit_exp
         out args;
    | Var x ->
      let filter str =
        (* filter out '(' and ')' *)
        let s1 = String.filter (fun c -> c != '(' && c != ')') str in
        (* replace '*' with "ptr_" *)
        let s2 = String.replace_chars (fun c -> if c == '*' then "ptr_" else String.of_char c) s1 in
        (* replace '.' with "_" *)
        let s3 = String.replace_chars (fun c -> if c == '.' then "_" else String.of_char c) s2 in
        (* replace "->" with "_" *)
        let rec replace_all (str : string) (sub : string) (by : string) =
          let (b, str') = String.replace str sub by in
          match b with
          | true -> replace_all str' sub by
          | false -> str'
        in
        replace_all s3 "->" "_"
      in
      String.print out (filter x)
    | Num n ->
      let str_n = Printf.sprintf "%f" n in
      let str_n' =
        if String.ends_with str_n "." then
          str_n ^ "0"
        else
          str_n
      in
      String.print out str_n'
    | Neg e' -> print_exps "-" [Num 0.0; e']
    | Add el -> print_exps "+" el
    | Sub el -> print_exps "-" el
    | Mul el -> print_exps "*" el
    | Div (e1, e2) -> print_exps "/" [e1; e2]
    | Pow (e1, e2) -> print_exps "^" [e1; e2]
    | Ite (f, e1, e2) ->
      begin
        String.print out "(ite ";
        print_formula out f;
        String.print out " ";
        emit_exp out e1;
        String.print out " ";
        emit_exp out e2;
        String.print out ")"
      end
    | Sqrt e -> (* print_exps "sqrt" [e] *)
      (* SQRT: MATH HACK
         sqrt(x) = pow(x, 0.5) *)
      emit_exp out (Pow(e, Num(0.5)))
    | Abs  e -> (* print_exps "abs"  [e] *)
      (* ABS: MATH HACK
         abs(x) = sqrt(pow(x, 2)) *)
      emit_exp out (Sqrt (Pow(e, Num(2.0))))
    | Log  e -> print_exps "log"  [e]
    | Exp  e -> print_exps "exp"  [e]
    | Sin  e -> print_exps "sin"  [e]
    | Cos  e -> print_exps "cos"  [e]
    | Tan  e -> print_exps "tan"  [e]
    | Asin e -> print_exps "arcsin" [e]
    | Acos e -> print_exps "arccos" [e]
    | Atan e -> print_exps "arctan" [e]
    | Atan2 (e1, e2) -> print_exps "arctan2" [e1; e2]
    | Sinh e -> print_exps "sinh" [e]
    | Cosh e -> print_exps "cosh" [e]
    | Tanh e -> print_exps "tanh" [e]
    | Asinh e -> print_exps "asinh" [e]
    | Acosh e -> print_exps "acosh" [e]
    | Atanh e -> print_exps "atanh" [e]
    | Matan e -> print_exps "matan" [e]
    | Safesqrt e -> print_exps "safesqrt" [e]
    | Integral (time_0, time_t, xs, flow) ->
       let str_xs = BatIO.to_string (List.print ~first:"[" ~last:"]" ~sep:" " String.print) xs in
       begin
         List.print ~first:"(" ~last:")" ~sep:" " String.print out ["integral"; string_of_float time_0; time_t; str_xs; flow]
       end

and print_formula out =
    let print_lists op out f items =
      begin
        List.print
          ~first:("("^op^" ")
          ~sep:" "
          ~last:")"
          f
          out
          items
      end in
    let print_fbinding out (x, f) =
      begin
        String.print out "(";
        String.print out x;
        String.print out " ";
        print_formula out f;
        String.print out ")";
      end in
    let print_ebinding out (x, e) =
      begin
        String.print out "(";
        String.print out x;
        String.print out " ";
        emit_exp out e;
        String.print out ")";
      end in
    let print_exps op exps = print_lists op out emit_exp exps in
    let print_formulas op formulas = print_lists op out print_formula formulas in
    function
    | True -> String.print out "true"
    | False -> String.print out "false"
    | FVar x -> String.print out "x"
    | Not f -> print_formulas "not" [f]
    | And fs -> print_formulas "and" fs
    | Or  fs -> print_formulas "or"  fs
    | Imply (f1, f2) -> print_formulas "=>" [f1;f2]
    | Gt (e1, e2) -> print_exps ">"  [e1; e2]
    | Lt (e1, e2) -> print_exps "<"  [e1; e2]
    | Ge (e1, e2) -> print_exps ">=" [e1; e2]
    | Le (e1, e2) -> print_exps "<=" [e1; e2]
    | Eq (e1, e2) -> print_exps "="  [e1; e2]
    | LetE (ebinding_list, f) ->
      begin
        String.print out "(let ";
        List.print
          ~first:("(")
          ~sep:" "
          ~last:")"
          print_ebinding
          out
          ebinding_list;
        String.print out ")";
      end
    | LetF (fbinding_list, f) ->
      begin
        String.print out "(let ";
        List.print
          ~first:("(")
          ~sep:" "
          ~last:")"
          print_fbinding
          out
          fbinding_list;
        String.print out ")";
      end
    | ForallT (m, lb, ub, f)->
      begin
        String.print out "(forall_t ";
        emit_exp out m;
        String.print out " [";
        emit_exp out lb;
        String.print out " ";
        emit_exp out ub;
        String.print out "] ";
        print_formula out f;
        String.print out ")";
      end

(* It's infix  expression *)
and emit_bexp out =
    let print_lists op out f items =
      begin
        List.print
          ~first: "("
          ~sep: (" "^op^" ")
          ~last:")"
          f
          out
          items
      end in
    let print_fbinding out (x, f) =
      begin
        String.print out "(";
        String.print out x;
        String.print out " ";
        print_formula out f;
        String.print out ")";
      end in
    let print_ebinding out (x, e) =
      begin
        String.print out "(";
        String.print out x;
        String.print out " ";
        emit_exp out e;
        String.print out ")";
      end in
    let print_exps op exps = print_lists op out emit_exp exps in
    let print_formulas op formulas = print_lists op out emit_bexp formulas in
    function
    | B_true -> String.print out "true"
    | B_false -> String.print out "false"
    | B_var x -> String.print out x
    | B_gt (e1, e2) -> print_exps ">" [e1; e2]
    | B_lt (e1, e2)-> print_exps "<" [e1; e2]
    | B_ge (e1, e2)-> print_exps ">=" [e1; e2]
    | B_le (e1, e2)-> print_exps "<=" [e1; e2]
    | B_eq (e1, e2)-> print_exps "==" [e1; e2]
    | B_and (e1, e2)-> print_formulas "&&" [e1; e2]
    | B_or (e1, e2)-> print_formulas "||" [e1; e2]
