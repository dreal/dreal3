BMC Tool
========

This tool takes in 

 - a .drh file which describes a hybrid system and specifications,
 - unrolling depth K (default: 3) for the bounded model checking.

and generates an SMT2 formula which can be checked by dReal.

Requirement
-----------
You need Ocaml (>= 3.12) and extra utilities and packages (including ocamlfind,
ocamlbuild, ocaml-batteries-included) to compile and run this software. There
are many ways to install them, but I do recommend to use ocamlbrew [1].

[1]: https://github.com/hcarty/ocamlbrew

Compile
-------

    $ make

Usage Example
-------------

    $ ./main.native -k 5 cardiac.drh > cardiac.smt2

Author
------
Soonho Kong <soonhok@cs.cmu.edu>
