Install Packages
================

0. Install Required Packages
--------------------

    sudo apt-get install -qq autoconf automake bison flex git libtool make pkg-config python-software-properties tex-info

1. g++-4.8
----------

    sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y
    sudo add-apt-repository ppa:dns/gnu -y
    sudo update-alternatives --remove-all gcc
    sudo update-alternatives --remove-all g++
    sudo apt-get update
    sudo apt-get install -qq g++-4.8
    sudo apt-get upgrade
    sudo apt-get dist-upgrade -y

2. Cmake
-------------------------------

    sudo add-apt-repository ppa:kalakris/cmake -y
    sudo apt-get update
    sudo apt-get install -qq cmake

Build dReal
===========

    git clone https://github.com/dreal/dreal.git dreal
    cd dreal
    mkdir -p build/release
    cd build/release
    cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=g++-4.8 -DCMAKE_C_COMPILER=gcc-4.8 ../../src
    make

If you want to link dReal with a self-compiled eglibc, use ``-DGLIBCPATH=<absolute_path>``:

~~~~~~~~~
cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=g++-4.8 \
      -DCMAKE_C_COMPILER=gcc-4.8 -DGLIBCPATH=/home/<user>/glibc ../src
~~~~~~~~~

Test Your Build
===============

Please test your build by running our regression testcases:

    ctest

dReach(BMC) and other tools
===========================

We have dReach(Bounded Model Checker) and other tools written in
Ocaml. To compile them, you need to have OCaml and libraries in your
system. Here are the recommended instructions for Ubuntu and OS X.

    sudo add-apt-repository ppa:avsm/ppa -yy
    sudo apt-get update
    sudo apt-get -qq install ocaml opam
    opam init
    eval `opam config env`
    opam switch 4.01.0
    opam update
    opam install ocamlfind batteries oasis

Once you set up everything, run `make` at `dreal/tools`. It will compile
all the tools.

    dreal/tools $ make
