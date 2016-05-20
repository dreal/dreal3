open Batteries

type var = Vardecl.var
type value = Vardecl.value
type vardecl = Vardecl.t
type t = (var, value * value) Map.t

let of_list (vardecls : vardecl list) : t
  =
  List.fold_left
    (fun (map : t) ((var, value, prec) : vardecl) ->
     Map.add var (value, prec) map
    )
    Map.empty
    vardecls

let print out = Map.print String.print
                          (fun o (v, p) ->
                            Value.print o v;
                            String.print o " : ";
                            Value.print o p)
                          out

let find key map =
  try
    Map.find key map
  with e ->
    let out = IO.stderr in
    begin
      String.println out "Vardeclmap Exception!";
      Printf.fprintf out "Key: %s\n" key;
      Printf.fprintf out "Map: %s\n" (IO.to_string print map);
      Printexc.print_backtrace IO.stdout;
      raise e
    end

let compose (vm1 ) (vm2 ) =
   let vardeclmerge k a b =
    match a, b with
    | Some (v1, p1), Some (v2, p2) -> Some ((Value.intersect v1 v2), (min p1 p2))
    | Some (v1, p1), None -> Some (v1, p1)
    | None, Some (v2, p2) -> Some (v2, p2)
    | None, None -> raise (Arg.Bad "Merging two emtpy keys")
    in
  Map.merge vardeclmerge vm1 vm2
