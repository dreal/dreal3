Install Homebrew
================

[Homebrew][homebrew] is a package manager fox OS X. We assume that
you're using homebrew to install packages.

    ruby -e "$(curl -fsSL https://raw.github.com/mxcl/homebrew/go)"

[homebrew]: http://brew.sh

Install Packages
================

gcc-4.8/automake/autoconf/libtool/git/cmake

    brew tap homebrew/versions
    brew update
    brew install gcc48 automake autoconf libtool git cmake

ocaml/opam
-----------

    brew install ocaml opam
    opam init
    eval `opam config env --root=<ABSOLUTE_HOMEPATH>/ocamlbrew/ocaml-4.00.1/.opam`
    opam update
    opam install ocamlfind batteries

boost
-----

    brew install --c++-11 --cc=gcc-4.8 --cxx=g++-4.8 boost

capd
----
    wget http://krzesanica.ii.uj.edu.pl/capd/capdDynSys.zip
    unzip capdDynSys.zip
    cd capd_dynsys
    autoreconf --install
    ./configure --without-gui CXX=g++-4.8 CC=gcc-4.8
    make
    sudo make install

Note that we need to compile ``capd`` using the same compiler that we
will compile dReal (``g++-4.8`` in this example).
