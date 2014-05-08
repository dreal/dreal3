open Batteries
open Intv

let src = Global.empty "src"      (* trace name *)
let prec = Global.empty "prec"
let fail_counter = ref 0
let fc () = incr fail_counter; !fail_counter

let print_msg prec f e eval =
  let out = IO.stdout in
  begin
    String.println out "The following constraint is SAT:";
    String.println out "============================";
    String.println out "Constraint: ";
    Basic.print_formula out f;
    String.println out "";
    String.println out "============================";
    String.print out   "Precision = ";
    Float.print out prec;
    String.println out   "";
    String.println out "============================";
    String.println out "Assignments: ";
    Env.print out e;
    String.println out "============================";
    String.println out "Eval Result = ";
    Intv.print out eval;
    String.println out "\n============================";
  end

let get_new_filename () =
  let tracename = (Global.get_exn src) in
  let idx = String.rfind tracename ".trace" in
  let basename = String.left tracename idx in
  (basename ^ "_" ^ (string_of_int (fc())) ^ ".smt2")

let create_smt e fs prec =
  let vardecls = Env.to_list e in
  let (smt2_declvars, smt2_assertvars) =
    List.split
      (List.fold_left
         (fun result (name, {low = l; high = h}) ->
           let df = Smt2_cmd.DeclareFun name in
           let vd_lb =
             match l = neg_infinity with
             | true -> []
             | false -> [Smt2_cmd.make_lb name l]
           in
           let vd_ub =
             match h = infinity with
             | true -> []
             | false -> [Smt2_cmd.make_ub name h]
           in
           (df, List.concat [vd_lb;vd_ub])::result)
         []
         vardecls)
  in
  let smt2_assert_fs =
    Smt2_cmd.Assert (Basic.And fs)
  in
  List.concat
    [[Smt2_cmd.SetLogic Smt2_cmd.QF_NRA;
      Smt2_cmd.SetInfo (":precision", string_of_float prec)];
     smt2_declvars;
     List.concat smt2_assertvars;
     [smt2_assert_fs];
     [Smt2_cmd.CheckSAT;
      Smt2_cmd.Exit]]

let split_on_x key env : (Env.t * Env.t) =
  let vardecls = Env.to_list env in
  let vardecls_pairs = List.combine vardecls vardecls in
  let vardecls_pairs' =
    List.map
      (fun ((name1, {low = l1; high = h1}), (name2, {low = l2; high = h2}))
      -> if (key = name1) then
          let mid =
            if l1 = neg_infinity && h1 = infinity then  0.0
            else if l1 = neg_infinity then (min_float /. 2.0) +. (h1 /. 2.0)
            else if h1 = infinity     then (min_float /. 2.0) +. (l1 /. 2.0)
            else ((l1 +. h1) /. 2.0)
          in
          ((name1, {low = l1; high = mid}), (name2, {low = mid; high = h2}))
        else
          ((name1, {low = l1; high = h1}), (name2, {low = l2; high = h2}))
      )
      vardecls_pairs
  in
  let (vardecls1, vardecls2) = List.split vardecls_pairs' in
  (Env.make vardecls1, Env.make vardecls2)

let split_env e fs prec : (Env.t * Env.t * float) =
  let vars_in_fs =
    List.fold_left
      Set.union
      Set.empty
      (List.map Basic.collect_var_in_f fs) in
  let vardecls = Env.to_list e in
  let vardecls_filtered =
    List.filter (fun (name, _) ->
      Set.mem name vars_in_fs && not (String.starts_with name "ITE_"))
      vardecls in
  let diff_list = List.map (fun (name, i) -> (name, Interval.size_I i)) vardecls_filtered in
  let (max_key, intv_size) =
    List.fold_left
      (fun (cur_max_key, cur_max_size) (key, size) ->
        if size > cur_max_size  then
          (key, size)
        else
          (cur_max_key, cur_max_size))
      ("", 0.0)
      diff_list
  in
  let (e1, e2) = split_on_x max_key e in
  let new_prec = List.min [intv_size /. 4.0; prec] in
  (e1, e2, new_prec)

let handle e fs fl =
  let prec = Global.get_exn prec in
  begin
    let (e1, e2, new_prec) = split_env e fs prec in
    List.iter
      (fun env ->
        let smt2 = create_smt env fl new_prec in
        File.with_file_out
          (get_new_filename ())
          (fun out -> Smt2.print out smt2))
      [e1; e2]
  end
