Proof Checker
============

Required Packages
-----------------
 - GNU Parallel: http://www.gnu.org/software/parallel/
 - ocamlbrew: https://github.com/hcarty/ocamlbrew
   We find ``ocamlbrew`` is the easiest way to set up the compilation environment for the proof checker written in Ocaml.
   As long as your system has ``ocamlfind`` and ``batteries-included``, it should be fine to compile it.

Compile ProofChecker (written in OCaml)
---------------------------------------
    $ cd checker
    $ make

Usage
-----
    $ ./proofcheck.sh -t <timeout in seconds> XXX.smt2.proof

