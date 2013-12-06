<table>
  <tr>
    <th>Ubuntu</th>
    <th>OS X</th>
    <th>Coverage</th>
    <th>Builds / UnitTests</th>
  </tr>
  <tr>
    <td><a href="https://travis-ci.org/soonhokong/dReal"><img src="https://travis-ci.org/soonhokong/dReal.png?branch=master" title="Ubuntu 12.04 LTS 64bit, g++-4.8 | clang++-3.3"/></a></td>
    <td><a href="https://travis-ci.org/soonhokong/dReal-osx"><img src="https://travis-ci.org/soonhokong/dReal-osx.png?branch=master" title="Mac OS X 10.8.2, g++-4.9"/></a></td>
    <td><a href="https://coveralls.io/r/soonhokong/dReal"><img src="https://coveralls.io/repos/soonhokong/dReal/badge.png"/></a></td>
    <td><a href="http://borel.modck.cs.cmu.edu/CDash/index.php?project=dReal">Here</a></td>
  </tr>
</table>

dReal: An SMT Solver for Nonlinear Theories of the Reals

Please visit [dReal] for more information.

Required Packages
=================
 - C++11-compatible compiler ([g++-4.8][gcc], [clang++-3.3][clang])
 - [bison][bison], [flex][flex], [cmake][cmake]
 - [ocaml (>=4.0.0)][ocaml], [opam][opam], [ocaml-findlib][ocaml-findlib], [ocaml-batteries (>=2.0)][ocaml-batteries]

[gcc]: http://gcc.gnu.org/projects/cxx0x.html
[clang]: http://clang.llvm.org/cxx_status.html
[dReal]: http://dreal.cs.cmu.edu
[cmake]:http://www.cmake.org/cmake/resources/software.html
[bison]: http://www.gnu.org/software/bison
[flex]: http://flex.sourceforge.net
[ocaml]: http://ocaml.org
[opam]: http://opam.ocamlpro.com
[ocaml-findlib]: http://projects.camlcity.org/projects/findlib.html
[ocaml-batteries]: http://batteries.forge.ocamlcore.org

Build Instructions
==================

 - [Ubuntu 12.04 LTS (using g++-4.8)][ubuntu-gcc]
 - [Ubuntu 12.04 LTS (using clang++-3.3)][ubuntu-clang]
 - [OS X 10.9/10.8 (using g++-4.8)][osx-gcc]

[ubuntu-gcc]: doc/ubuntu-gcc.md
[ubuntu-clang]: doc/ubuntu-clang.md
[osx-gcc]: doc/osx-gcc.md
