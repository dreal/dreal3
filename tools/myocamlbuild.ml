open Ocamlbuild_plugin;;
dispatch begin function
| After_rules ->
    ocaml_lib "basic/basic";
    ocaml_lib "smt2/smt2";
    ocaml_lib "drh/drh";
| _ -> ()
end
