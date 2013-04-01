open Yojson.Basic.Util

let extract_titles json =
  [json]
    |> filter_member "pages"
    |> flatten
    |> filter_member "title"
    |> filter_string

let main () =
  let json = Yojson.Basic.from_channel stdin in
  BatString.println BatIO.stdout (Yojson.Basic.pretty_to_string json)

let () = main ()
