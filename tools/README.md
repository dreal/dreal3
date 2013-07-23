OCaml Installation via ocamlbrew
================================

We recommend to install ocaml and required packages and tool chains
via ocamlbrew. You can find the instructions at

    https://github.com/hcarty/ocamlbrew

After installation, please update and upgrade ocaml-packages using
opam

    $ opam update && opam upgrade

Please make sure that you have the following packages installed with
the corresponding version.

 - batteries-2.1.0
 - cil-1.7.2

Compile
==================================

    $ cd tools
    $ make
