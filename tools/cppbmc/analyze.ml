(*
 * Soonho Kong (soonhok@cs.cmu.edu)
 *)

open Cil
open Pretty

type state = Lvmap.t

let special_funcs = ["sqrt";
                     "fabs";
                     "log";
                     "exp";
                     "sin";
                     "cos";
                     "tan";
                     "asin";
                     "acos";
                     "atan";
                     "sinh";
                     "cosh";
                     "tanh";
                     "pow"]

let failwith_loc loc msg =
  let loc_str = sprint 80 (d_loc () loc) in
  failwith (loc_str ^ " :: " ^ msg)

let rec analyze_instr (i : instr) (s : state) : (Basic.formula * state) =
  match i with
  (* lv := e @ loc *)
  | Set(lv, e, l) ->
    let (e1, s1) = analyze_exp e s l in
    let s1' = Lvmap.update lv s1 in
    let (e2, s2) = analyze_lval lv s1' l in
    (Basic.Eq (e2, e1), s2)
  | Call(Some lv, f, args, l) ->
    let (exp_f, s1) = analyze_exp f s l in
    let (exps, s2) = analyze_exps args s1 l in
    let s2' = Lvmap.update lv s2 in
    let (exp_lv, s3) = analyze_lval lv s2' l in
    let f =
      begin
        match (sprint 80 (d_exp () f), exps) with
        | ("sqrt", exp::[]) -> Basic.Eq (exp_lv, Basic.Sqrt(exp))
        | ("fabs", exp::[]) -> Basic.Eq (exp_lv, Basic.Abs(exp))
        | ("log",  exp::[]) -> Basic.Eq (exp_lv, Basic.Log(exp))
        | ("exp",  exp::[]) -> Basic.Eq (exp_lv, Basic.Exp(exp))
        | ("sin",  exp::[]) -> Basic.Eq (exp_lv, Basic.Sin(exp))
        | ("cos",  exp::[]) -> Basic.Eq (exp_lv, Basic.Cos(exp))
        | ("tan",  exp::[]) -> Basic.Eq (exp_lv, Basic.Tan(exp))
        | ("asin", exp::[]) -> Basic.Eq (exp_lv, Basic.Asin(exp))
        | ("acos", exp::[]) -> Basic.Eq (exp_lv, Basic.Acos(exp))
        | ("atan", exp::[]) -> Basic.Eq (exp_lv, Basic.Atan(exp))
        | ("sinh", exp::[]) -> Basic.Eq (exp_lv, Basic.Sinh(exp))
        | ("cosh", exp::[]) -> Basic.Eq (exp_lv, Basic.Cosh(exp))
        | ("tanh", exp::[]) -> Basic.Eq (exp_lv, Basic.Tanh(exp))
        | ("pow",  exp1::exp2::[]) -> Basic.Eq (exp_lv, Basic.Pow(exp1, exp2))
        | _ ->
          begin
            Basic.print_exp BatIO.stdout exp_f;
            failwith_loc l
              ("instr: Call " ^ (sprint 80 (d_exp () f))  ^ " - We don't handle other than math functions at this time.")
          end
      end
    in (f, s3)
  | Call(None, f, args, l) ->
    failwith_loc l "instr: Call - We ignore function calls without assignments."
  | Asm (_, _, _, _, _, l) -> failwith_loc l "instr: Goto"

and analyze_instrs (instrs : instr list) (s : state)
    : (Basic.formula * state)
    =
  let aux (f, s) i =
    let (f', s') = analyze_instr i s in
    (Basic.make_and [f; f'], s')
  in
  List.fold_left aux (Basic.True, s) instrs

and analyze_stmt (stmt : stmt) (s : state)
    : (Basic.formula * state)
    =
  match stmt.skind with
  | Instr instrs -> analyze_instrs instrs s
  | Return (e_opt, l) -> (Basic.True, s)
  | Goto (stmt_ref, l) -> failwith_loc l "stmt: Goto"
  | Break l -> failwith_loc l "stmt: Break"
  | Continue l -> failwith_loc l "stmt: Continue"
  | If (e, b1, b2, l) ->
    let (cond_f, s') = analyze_exp_as_formula e s l in
    let (f_true, s_true) = analyze_block b1 s' in
    let (f_false, s_false) = analyze_block b2 s' in
    begin
      match cond_f with
        | Basic.True -> (f_true, s_true)
        | Basic.False -> (f_false, s_false)
        | _ ->
          begin
            let s'' = Lvmap.join s_true s_false in
            let balance s1 s2 f =
              let diff = Lvmap.diff s1 s2 in
              List.fold_left
                (fun f (lv, n1, n2) ->
                  let new_f =
                    Basic.Eq
                      (Basic.Var (make_name lv n1),
                       Basic.Var (make_name lv n2))
                  in
                  Basic.make_and [f; new_f])
                f
                diff
            in
            let f_true' = balance s_true s_false f_true in
            let f_false' = balance s_false s_true f_false in
            let f' =
              Basic.make_or
                [Basic.make_and [cond_f; f_true'];
                 Basic.make_and [Basic.Not cond_f; f_false']]
            in
            (f', s'')
          end
    end
  (* failwith_loc l "stmt: If" *)
  | Switch (e, b, stmts, l) -> failwith_loc l "stmt: Switch"
  | Loop (b, l, stmt_option1, stmt_option2) -> failwith_loc l "stmt: Loop"
  | Block b -> analyze_block b s
  | TryFinally (b1, b2, l) -> failwith_loc l "stmt: TryFinally"
  | TryExcept (b1, (instrs, e), b2, l) -> failwith_loc l "stmt: TryExcept"

and analyze_stmts (stmts : stmt list) (s : state)
    : (Basic.formula * state)
    =
  let aux (f, s) stmt =
    let (f', s') = analyze_stmt stmt s in
    (Basic.make_and [f; f'], s')
  in
  List.fold_left aux (Basic.True, s) stmts

and analyze_block (b : block) (s : state)
    : (Basic.formula * state) =
  analyze_stmts b.bstmts s

and analyze_exp_unop ((op, e, t) : (unop * exp * typ)) (s : state) (l : location)
    : (Basic.exp * state)
    = match op with
    | Neg -> let (e', s') = analyze_exp e s l in
             (Basic.Neg e', s')
    | BNot -> failwith_loc l "exp_unop : BNot"
    | LNot -> failwith_loc l "exp_unop : LNot"

and analyze_exp_binop
    ((op, e1, e2, t) : (binop * exp * exp * typ)) (s : state) (l : location)
    : (Basic.exp * state)
    = match op with
    | PlusA ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Add [exp1; exp2], s2)
    | PlusPI -> failwith_loc l "exp_binop : PlusPI"
    | IndexPI -> failwith_loc l "exp_binop : IndexPI"
    | MinusA ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Sub [exp1; exp2], s2)
    | MinusPI -> failwith_loc l "exp_binop : MinusPI"
    | MinusPP -> failwith_loc l "exp_binop : MinusPP"
    | Mult ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Mul [exp1; exp2], s2)
    | Div ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Div (exp1, exp2), s2)
    | Mod -> failwith_loc l "exp_binop : Mod"
    | Shiftlt -> failwith_loc l "exp_binop : Shiftlt"
    | Shiftrt -> failwith_loc l "exp_binop : Shiftrt"
    | Lt -> failwith_loc l "exp_binop : Lt"
    | Gt -> failwith_loc l "exp_binop : Gt"
    | Le -> failwith_loc l "exp_binop : Le"
    | Ge -> failwith_loc l "exp_binop : Ge"
    | Eq -> failwith_loc l "exp_binop : Eq"
    | Ne -> failwith_loc l "exp_binop : Ne"
    | BAnd -> failwith_loc l "exp_binop : BAnd"
    | BXor -> failwith_loc l "exp_binop : BXor"
    | BOr -> failwith_loc l "exp_binop : BOr"
    | LAnd -> failwith_loc l "exp_binop : LAnd"
    | LOr -> failwith_loc l "exp_binop : LOr"

and analyze_exp (e : exp) (s : state) (l : location)
    : (Basic.exp * state)
    =
  match e with
  | Const c -> analyze_const c s l
  | Lval lv -> analyze_lval lv s l
  | SizeOf t -> failwith_loc l "exp: SizeOf"
  | SizeOfE e -> failwith_loc l "exp: SizeOfE"
  | SizeOfStr s -> failwith_loc l "exp: SizeOfStr"
  | AlignOf t -> failwith_loc l "exp: AlignOf"
  | AlignOfE e -> failwith_loc l "exp: AlignOfE"
  | UnOp (op, e, t) -> analyze_exp_unop (op, e, t) s l
  | BinOp (op, e1, e2, t) -> analyze_exp_binop (op, e1, e2, t) s l
  | Question (e1, e2, e3, t) -> failwith_loc l "exp: Question"
  | CastE (t, e) -> analyze_exp e s l
  | AddrOf lv -> failwith_loc l "exp: AddrOf"
  | StartOf lv -> failwith_loc l "exp: StartOf"

and analyze_exp_as_formula_unop
    ((op, e, t) : (unop * exp * typ)) (s : state) (l : location)
    : (Basic.formula * state)
    = match op with
    | Neg -> failwith_loc l "exp_as_formula_unop : Neg"
    | BNot -> failwith_loc l "exp_as_formula_unop : BNot"
    | LNot ->
      let
          (f, s') = analyze_exp_as_formula e s l
      in (Basic.Not f, s')

and analyze_exp_as_formula_binop
    ((op, e1, e2, t) : (binop * exp * exp * typ)) (s : state) (l : location)
    : (Basic.formula * state)
    = match op with
    | PlusA -> failwith_loc l "exp_as_formula_binop : PlusA"
    | PlusPI -> failwith_loc l "exp_as_formula_binop : PlusPI"
    | IndexPI -> failwith_loc l "exp_as_formula_binop : IndexPI"
    | MinusA -> failwith_loc l "exp_as_formula_binop : MinusA"
    | MinusPI -> failwith_loc l "exp_as_formula_binop : MinusPI"
    | MinusPP -> failwith_loc l "exp_as_formula_binop : MinusPP"
    | Mult -> failwith_loc l "exp_as_formula_binop : MultA"
    | Div -> failwith_loc l "exp_as_formula_binop : DivA"
    | Mod -> failwith_loc l "exp_as_formula_binop : Mod"
    | Shiftlt -> failwith_loc l "exp_as_formula_binop : Shiftlt"
    | Shiftrt -> failwith_loc l "exp_as_formula_binop : Shiftrt"
    | Lt ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Lt (exp1, exp2), s2)
    | Gt ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Gt (exp1, exp2), s2)
    | Le ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Le (exp1, exp2), s2)
    | Ge ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Le (exp1, exp2), s2)
    | Eq ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Eq (exp1, exp2), s2)
    | Ne ->
      let (exp1, s1) = analyze_exp e1 s l in
      let (exp2, s2) = analyze_exp e2 s1 l in
      (Basic.Not (Basic.Eq (exp1, exp2)), s2)
    | BAnd -> failwith_loc l "exp_as_formula_binop : BAnd"
    | BXor -> failwith_loc l "exp_as_formula_binop : BXor"
    | BOr -> failwith_loc l "exp_as_formula_binop : BOr"
    | LAnd -> failwith_loc l "exp_as_formula_binop : LAnd"
    | LOr -> failwith_loc l "exp_as_formula_binop : LOr"

and analyze_exp_as_formula (e : exp) (s : state) (l : location)
    : (Basic.formula * state)
    = match e with
  | Const c ->
    begin
      match c with
        | CInt64 (n64, _, _) ->
          if (i64_to_int n64) = 0 then
            (Basic.True, s)
          else
            (Basic.False, s)
        | CStr _ -> failwith_loc l "exp_as_formula: Const::CStr"
        | CWStr _ -> failwith_loc l "exp_as_formula: Const::CWStr"
        | CChr _ -> failwith_loc l "exp_as_formula: Const::CChr"
        | CReal (n, _, _) ->
          if n = 0.0 then
            (Basic.True, s)
          else
            (Basic.False, s)
        | CEnum (e, _, _) -> failwith_loc l "exp_as_formula: Const::CEnum"
    end
  | Lval lv ->
    let (exp, s') = analyze_lval lv s l in
    (Basic.Not (Basic.Eq (exp, Basic.Num 0.0)), s')
  | SizeOf t -> failwith_loc l "exp_as_formula: SizeOf"
  | SizeOfE e -> failwith_loc l "exp_as_formula: SizeOfE"
  | SizeOfStr s -> failwith_loc l "exp_as_formula: SizeOfStr"
  | AlignOf t -> failwith_loc l "exp_as_formula: AlignOf"
  | AlignOfE e -> failwith_loc l "exp_as_formula: AlignOfE"
  | UnOp (op, e, t) -> analyze_exp_as_formula_unop (op, e, t) s l
  | BinOp (op, e1, e2, t) -> analyze_exp_as_formula_binop (op, e1, e2, t) s l
  | Question (e1, e2, e3, t) -> failwith_loc l "exp_as_formula: Question"
  | CastE (t, e) -> failwith_loc l "exp_as_formula: CastE"
  | AddrOf lv -> failwith_loc l "exp_as_formula: AddrOf"
  | StartOf lv -> failwith_loc l "exp_as_formula: StartOf"

and analyze_exps (exps : exp list) (s : state) (l : location)
    : (Basic.exp list * state)
    =
  let aux (exps, s) e =
    let (exp, s') = analyze_exp e s l in
    (exps @ [exp], s')
  in
  List.fold_left aux ([], s) exps

and analyze_const (c : constant) (s : state) (l : location)
    : (Basic.exp * state)
    =
  match c with
  | CInt64 (i64, _, _) -> (Basic.Num (float_of_int (i64_to_int i64)), s)
  | CStr str -> failwith_loc l "constant: Cstr"
  | CWStr i64s -> failwith_loc l "constant: CWstr"
  | CChr chr -> failwith_loc l "constant: CChr"
  | CReal (n, _, _) -> (Basic.Num n, s)
  | CEnum (_, _, _) -> failwith_loc l "constant: CEnum"

and string_of_lval (lv : lval) : string = sprint 80 (d_lval () lv)
and make_name (lv : lval) (n : int)
    : string
    = (string_of_lval lv) ^ (string_of_int n)

and check_lval (lv : lval) : bool
    = List.exists (fun n -> n = (string_of_lval lv)) special_funcs

and analyze_lval (lv : lval) (s : state) (l : location)
    : (Basic.exp * state)
    = match (check_lval lv) with
    | true ->
      (Basic.Var (string_of_lval lv), s)
    | false ->
      let (n, s') = Lvmap.lookup lv s in
      let str = make_name lv n in
      (Basic.Var str, s')
