<table>
  <tr>
    <th>Ubuntu</th><th>OS X</th>
  </tr>
  <tr>
    <td><a href="https://travis-ci.org/soonhokong/dReal"><img src="https://travis-ci.org/soonhokong/dReal.png?branch=master" title="Ubuntu 12.04 LTS 64bit, g++-4.8 | clang++-3.3"/></a></td>
    <td><a href="https://travis-ci.org/soonhokong/dReal-osx"><img src="https://travis-ci.org/soonhokong/dReal-osx.png?branch=master" title="Mac OS X 10.8.2, g++-4.9"/></a></td>
  </tr>
</table>

dReal: An SMT Solver for Nonlinear Theories of the Reals

Please visit [dReal] for more information.

Required Packages
=================
 - C++11-compatible compiler ([g++-4.8][gcc], [clang++-3.3][clang])
 - [bison][bison], [flex][flex], [cmake][cmake]
 - [boost (>=1.54)][boost]
 - [capd-DynSys 3.0][capd-dynsys]
 - [ocaml (>=4.0.0)][ocaml], [opam][opam], [ocaml-findlib][ocaml-findlib], [ocaml-batteries (>=2.0)][ocaml-batteries]

[gcc]: http://gcc.gnu.org/projects/cxx0x.html
[clang]: http://clang.llvm.org/cxx_status.html
[dReal]: http://dreal.cs.cmu.edu
[cmake]:http://www.cmake.org/cmake/resources/software.html
[capd-dynsys]: http://capd.ii.uj.edu.pl/download.php
[capd-dynsys-daily]: http://krzesanica.ii.uj.edu.pl/capd/capdDynSys.zip
[bison]: http://www.gnu.org/software/bison
[flex]: http://flex.sourceforge.net
[boost]: http://www.boost.org
[ocaml]: http://ocaml.org
[opam]: http://opam.ocamlpro.com
[ocaml-findlib]: http://projects.camlcity.org/projects/findlib.html
[ocaml-batteries]: http://batteries.forge.ocamlcore.org

Build Instructions
==================

Install required packages

 - [Ubuntu 12.04 LTS (using g++-4.8)][ubuntu-gcc]
 - [Ubuntu 12.04 LTS (using clang++-3.3)][ubuntu-clang]
 - [OS X 10.9/10.8 (using g++-4.8)][osx-gcc]

[ubuntu-gcc]: doc/ubuntu-gcc.md
[ubuntu-clang]: doc/ubuntu-clang.md
[osx-gcc]: doc/osx-gcc.md

Build dReal

    git clone git@github.com:soonhokong/dreal-soonhok.git dreal
    cd dreal
    mkdir -p build/release
    cd build/release
    cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=g++-4.8 -DCMAKE_C_COMPILER=gcc-4.8 ../../src
    make

If you want to link dReal with self-compiled eglibc, use ``-DGLIBCPATH=<absolute_path>``:

~~~~~~~~~
cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=g++-4.8 \
    -DCMAKE_C_COMPILER=gcc-4.8 -DGLIBCPATH=/home/<user>/glibc ../src
~~~~~~~~~
