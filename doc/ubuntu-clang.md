Install Packages
================

0. Install Required Packages
--------------------

    sudo apt-get install -qq autoconf automake bison flex git libtool make pkg-config

1. clang++-3.3
--------------

    sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y
    sudo add-apt-repository ppa:dns/gnu -y
    sudo add-apt-repository ppa:h-rayflood/llvm -y
    sudo apt-get update -y
    sudo apt-get install -qq libstdc++-4.8-dev clang-3.3 clang-3.3-doc
    sudo apt-get upgrade -y
    sudo apt-get dist-upgrade -y

2. Cmake
---------------------

    sudo add-apt-repository --yes ppa:kalakris/cmake
    sudo apt-get update
    sudo apt-get install -qq cmake

3. EGLIBC-2.17 (Optional)
-------------------------

Using eglibc (<= 2.16) may cause severe errors in floating point
computation if ``FE_UPWARD``, ``FE_DOWNWARD``, and ``FE_TOWARDZERO``
rounding modes are used. If you're using Ubuntu OS (<= 12.10) or
Debian (<= 7.2), please check the version of your eglibc by typing:

    ldd --version

If the version is <= 2.16, please check out the latest version of eglibc:

    svn co http://www.eglibc.org/svn/trunk eglibc

and install them on your machine. (NOTE: recommend to install on your home dir)

    cd <HOME_PATH>
    svn co svn://svn.eglibc.org/branches/eglibc-2_17 eglibc-2.17
    mkdir eglibc-2.17-build
    mkdir eglibc
    cd eglibc-2.17-build
    ../eglibc-2.17/libc/configure --prefix=<HOME_PATH>/../eglibc
    make
    make install


Build dReal
===========

    git clone https://github.com/dreal/dreal.git dreal
    cd dreal
    mkdir -p build/release
    cd build/release
    cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=clang++-3.3 -DCMAKE_C_COMPILER=clang-3.3 ../../src
    make

If you want to link dReal with a self-compiled eglibc, use ``-DGLIBCPATH=<absolute_path>``:

~~~~~~~~~
cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=clang++-3.3 \
      -DCMAKE_C_COMPILER=clang-3.3 -DGLIBCPATH=/home/<user>/glibc ../src
~~~~~~~~~


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
    opam update
    opam install ocamlfind batteries oasis

Once you set up everything, run `make` at `dreal/tools`. It will compile
all the tools.

    dreal/tools $ make
