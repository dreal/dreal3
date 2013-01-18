type func = Func.t
type c_type = GT_ZERO
              | EQ_ZERO
              | LT_ZERO

type t = c_type * func

let extract_f (t, f) = f

let print out (t, f)
    =
  begin
    Func.print out f;
    match t with
      | GT_ZERO ->
        BatString.print out " >= 0"
      | EQ_ZERO ->
        BatString.print out " = 0"
      | LT_ZERO ->
        BatString.print out " <= 0"
  end
