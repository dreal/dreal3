type key = string
type intv = Intv.t
type t = (key, intv) BatPMap.t

exception CException of string

let print out =
  BatPMap.print
    ~first:"{"
    ~last:"}\n"
    ~sep:", \n"
    BatString.print
    (fun o v ->
      let s = Interval.sprintf_I "%f" v in
      BatPrintf.fprintf o "%s" s)
    out

let find (x : key) (e : t) : intv
    = BatPMap.find x e

let join (e1 : t) (e2 : t) : t =
  BatPMap.merge
    (fun x i1_op i2_op ->
      match (i1_op, i2_op) with
          (Some i1, Some i2) -> Some (Interval.union_I_I i1 i2)
        | _ -> raise (CException "Merge fail"))
    e1
    e2

let to_list (e : t) : (key * intv) list = BatList.of_enum (BatPMap.backwards e)

let from_list (l : (key * intv) list) : t =
  List.fold_left
    (fun e (k, i) -> BatPMap.add k i e)
    BatPMap.empty
    l

let make (l : (key * float * float) list) : t =
  from_list (List.map (fun (x, l, h) -> (x, Intv.make l h)) l)

let equals_int
    {Intv.low = l1; Intv.high = h1}
    {Intv.low = l2; Intv.high = h2}
    : bool
    =
  (BatFloat.compare l1 l2) = 0 &&
  (BatFloat.compare h1 h2) = 0

let equals (e1 : t) (e2 : t) : bool =
  not (List.mem
       false
       (List.map
          (fun ((_, i1), (_, i2)) ->
            equals_int i1 i2)
          (BatList.combine (to_list e1) (to_list e1))))

let is_empty (e : t) : bool =
  List.mem true
    (List.map
       (fun (_, {Intv.low = l; Intv.high = h})
       -> (BatFloat.compare l h) = 0)
       (to_list e))

(* minus e1 e2 == (e1 - e2) *)
let minus (e1 : t) (e2 : t) : (t list) =
  let extract_diff_dim l1 l2 =
    let diff_list =
      List.filter
        (fun ((_, i1), (_, i2))
        -> not (equals_int i1 i2))
        (BatList.combine l1 l2) in
    let num_of_diffs =
      List.length
        diff_list
    in
    if num_of_diffs != 1 then
      begin
        BatString.println BatIO.stdout "=========================================================";
        print BatIO.stdout e1;
        BatString.println BatIO.stdout "=========================================================";
        print BatIO.stdout e2;
        BatString.println BatIO.stdout "=========================================================";
        raise (CException ("Two envs differ on multiple dimensions: " ^ string_of_int num_of_diffs))
      end
    else
      List.hd diff_list
  in
  let l1 = to_list e1 in
  let l2 = to_list e2 in
  let ((key, _), (_, _)) = extract_diff_dim l1 l2 in
  let (l1', l2') =
    BatList.split
      (List.map
         (fun (((key1, {Intv.low = l1; Intv.high = h1}) as elem1),
             ((key2, {Intv.low = l2; Intv.high = h2}) as elem2))
         ->
           if key != key1 then
             (elem1, elem2)
           else
             ((key1, {Intv.low = l1; Intv.high = l2}),
              (key2, {Intv.low = h1; Intv.high = h2}))
         )
         (BatList.combine l1 l2)
      )
  in
  List.filter (fun e -> not (is_empty e)) [from_list l1';from_list l2']

(* let minus (e1 : t) (e2 : t) : (t list) = *)
(*   let rec minus_aux (e1 : (key * intv) list) (e2 : (key * intv) list) : *)
(*       (key * intv) list list = *)
(*     match (e1, e2) with *)
(*         ((x, {Intv.low=x_l; Intv.high=x_h})::e1_rest, *)
(*          (y, {Intv.low=y_l; Intv.high=y_h})::e2_rest) -> *)
(*           begin *)
(*             assert (x = y); *)
(*             let left_fragment = *)
(*               if x_l < y_l then *)
(*                 [(x, {Intv.low=x_l; Intv.high=y_l})::e1_rest] *)
(*               else *)
(*                 [] *)
(*             in *)
(*             let right_fragment = *)
(*               if y_h < x_h then *)
(*                 [(x, {Intv.low=y_h; Intv.high=x_h})::e1_rest] *)
(*               else *)
(*                 [] *)
(*             in *)
(*             left_fragment *)
(*             @right_fragment *)
(*             @(List.map *)
(*                 (fun e -> (x, {Intv.low=y_l; Intv.high=y_h})::e) *)
(*                 (minus_aux e1_rest e2_rest) *)
(*             ) *)
(*           end *)
(*       | ([], []) -> [] *)
(*       | _ -> raise (CException "should not happend") *)
(*   in *)
(*   let result_lists = minus_aux (to_list e1) (to_list e2) in *)
(*   List.map from_list result_lists *)

let order (e1 : t) (e2 : t) : bool =
  BatPMap.for_all
    (fun x i1 ->
      let i2 = find x e2 in
      Intv.order i1 i2
    )
    e1

let var_decl_to_string (element : (key * intv)) =
  let (var, interval) = element in
  let {Intv.low=l; Intv.high=h} = interval in
  "[" ^ string_of_float l ^ ", " ^ string_of_float h ^ "] " ^ var ^ ";\n"

let to_string e =
  let l = to_list e in
  let intvs = List.map var_decl_to_string l in
  let var_decls = List.fold_left ( ^ ) "" intvs in
  var_decls
