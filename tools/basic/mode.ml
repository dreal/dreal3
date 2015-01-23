open Batteries

type id = Id.t
type exp = Basic.exp
type formula = Basic.formula
type var = Vardecl.var
type invs = formula list
type ode = Ode.t
type flow = ode
type jump = Jump.t
type jumpmap = Jumpmap.t

type t = {mode_id: id;
          time_precision: float;
          invs_op: invs option;
          flows: ode list;
          jumps: jump list;
          jumpmap: jumpmap}

let make (id, t_precision, invs_op, flows, jumps, jumpmap)
  = {mode_id= id;
     time_precision = t_precision;
     invs_op= invs_op;
     flows= List.sort (fun (v1, ode1) (v2, ode2) -> String.compare v1 v2) flows;
     jumps;
     jumpmap= jumpmap}

let mode_id {mode_id= id;
             invs_op= invs_op;
             flows= flows;
             jumpmap= jumpmap}
  = id

let mode_id (m : t) = m.mode_id
let time_precision (m : t) = m.time_precision
let invs_op (m : t) = m.invs_op
let flows (m : t) = m.flows
let jumps (m : t) = m.jumps
let jumpmap (m : t) = m.jumpmap

let print out {mode_id= id;
               invs_op= invs_op;
               flows= flows;
               jumps= jumps;
               jumpmap= jumpmap}
  =
  let mode_id = id in
  let inv_str = match invs_op with
      None -> "None"
    | Some inv ->
       IO.to_string (List.print ~first:"" ~sep:"\n    " ~last:"\n" Basic.print_formula) inv in
  let flow_str =
    IO.to_string (List.print ~first:"" ~sep:"\n    " ~last:"\n" Ode.print) flows in
  let jump_str = IO.to_string (List.print Jump.print) jumps in
  Printf.fprintf out
                 "{\nModeID = %d\nInvariant = %s\nFlows = %s\nJump = %s\n}"
                 mode_id
                 inv_str
                 flow_str
                 jump_str
