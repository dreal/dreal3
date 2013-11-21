dReach(BMC) and other tools
===========================

We have dReach(Bounded Model Checker) and other tools written in
Ocaml. To compile them, you need to have OCaml installation in your
system. Here are the recommended instructions for Ubuntu and OS X.

Ubuntu
------

    sudo add-apt-repository ppa:avsm/ppa -yy
    sudo apt-get update
    sudo apt-get -qq install ocaml opam
    opam init
    eval `opam config env`
    opam update
    opam install ocamlfind batteries

OS X
----

    brew install ocaml opam
    opam init
    eval `opam config env --root=<ABSOLUTE_HOMEPATH>/ocamlbrew/ocaml-4.00.1/.opam`
    opam update
    opam install ocamlfind batteries


Build
=====

Run `make` at dReal/tools. It will compile all the tools.

    make
