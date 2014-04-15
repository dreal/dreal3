Install Homebrew
================

[Homebrew][homebrew] is a package manager fox OS X. We assume that
you're using homebrew to install packages.

    ruby -e "$(curl -fsSL https://raw.github.com/mxcl/homebrew/go)"

[homebrew]: http://brew.sh

Install Packages
================

gcc-4.8/automake/autoconf/libtool/git/cmake
-------------------------------------------

    brew tap homebrew/versions
    brew update
    brew install gcc48 automake autoconf libtool git cmake

Build dReal
===========

    git clone https://github.com/dreal/dreal.git dreal
    cd dreal
    mkdir -p build/release
    cd build/release
    cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=g++-4.8 -DCMAKE_C_COMPILER=gcc-4.8 ../../src
    make

Test Your Build
===============

Please test your build by running our regression testcases:

    ctest

dReach(BMC) and other tools
===========================

We have dReach(Bounded Model Checker) and other tools written in
Ocaml. To compile them, you need to have OCaml and libraries in your
system. Here are the recommended instructions for Ubuntu and OS X.

ocaml/opam
-----------

    brew install ocaml opam
    opam init
    eval `opam config env --root=<ABSOLUTE_HOMEPATH>/ocamlbrew/ocaml-4.00.1/.opam`
    opam update
    opam install ocamlfind batteries oasis

Once you set up everything, run `make` at `dreal/tools`. It will compile
all the tools.

    dreal/tools $ make


Known Issue
===========

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Undefined symbols for architecture x86_64:
  "isalnum(int)", referenced from:
      rp_isident(int)  in librealpaver.a(rp_lexer.c.o)
  "isalpha(int)", referenced from:
      _rp_lexer_get_token in librealpaver.a(rp_lexer.c.o)
  "iscntrl(int)", referenced from:
      _rp_lexer_get_token in librealpaver.a(rp_lexer.c.o)
      _rp_stream_eat_space in librealpaver.a(rp_stream.c.o)
  "isdigit(int)", referenced from:
      _rp_lexer_get_number in librealpaver.a(rp_lexer.c.o)
  "isspace(int)", referenced from:
      _rp_stream_eat_space in librealpaver.a(rp_stream.c.o)
  "tolower(int)", referenced from:
      rp_lexer_text_to_lower(char*) in librealpaver.a(rp_lexer.c.o)
  "toupper(int)", referenced from:
      rp_string_equal_case(char const*, char const*) in librealpaver.a(rp_lexer.c.o)
      _rp_lexer_get_number in librealpaver.a(rp_lexer.c.o)
ld: symbol(s) not found for architecture x86_64
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If you have the above error, it is due to a problem in OS X 10.9 + g++-4.8/g++-4.9.
Please read http://stackoverflow.com/a/19706989/2654527 to fix the problem.
