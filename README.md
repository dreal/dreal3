[![Build Status](https://travis-ci.org/soonhokong/dReal.png?branch=master)](https://travis-ci.org/soonhokong/dReal) Ubuntu 12.04 LTS g++-4.8

dReal: An SMT Solver for Nonlinear Theories of the Reals
========================================================

Please visit [dReal] for more information.

[dReal]: http://dreal.cs.cmu.edu/

Required Packages
-----------------
 - C++11-compatible compiler (ex: g++4.8 or clang++-3.3)
 - bison & flex
 - [cmake][cmake]
 - [capd-DynSys 3.0][capd-dynsys]
 - libboost-dev & libboost-thread-dev
 - curl, m4 (for [ocamlbrew][ocamlbrew])
 - ocaml-batteries, cil (ocaml packages for tools)

[capd-dynsys]: http://capd.ii.uj.edu.pl/download.php

We have tested that executing the following command on the newly installed Ubuntu 12.04.3 LTS
configures all the required packages to build dReal2.

    sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y
    sudo add-apt-repository ppa:dns/gnu
    sudo update-alternatives --remove-all gcc
    sudo update-alternatives --remove-all g++
    sudo apt-get update
    sudo apt-get install autoconf automake libtool git g++-4.8 bison flex \
                           libboost-dev libboost-thread-dev curl m4
    sudo apt-get upgrade
    sudo apt-get dist-upgrade -y

We have extra tools under ``tools`` directory, which requires ocaml implementation and
libraries. We recommend to install them via [ocamlbrew]:

    curl -kL https://raw.github.com/hcarty/ocamlbrew/master/ocamlbrew-install | bash
    opam update
    opam install batteries cil

[ocamlbrew]: https://github.com/hcarty/ocamlbrew

How to Build CAPD-DynSys 3.0
----------------------------

 - Download and uncompress [CAPD-DynSys 3.0 SVN (daily) Snapshot][capd-dynsys-daily]
 - Configure and build:

    autoreconf --install
    ./configure --without-gui
    make
    (sudo) make install

[capd-dynsis-daily]: http://krzesanica.ii.uj.edu.pl/capd/capdDynSys.zip

How to Build dReal
------------------

Building dReal is straight-forward:

    $ autoreconf -i && ./configure && make

If you have the GLIBC problem described below, try the following:

    $ autoreconf -i
    $ LDFLAGS="-Wl,--rpath=<EGLIBC_PATH>:/usr/lib/x86_64-linux-gnu/:/usr/lib/gcc/x86_64-linux-gnu/4.6:/lib/x86_64-linux-gnu -Wl,--dynamic-linker=<EGLIBC_PATH>/lib/ld-linux-x86-64.so.2" ./configure
    $ make

GLIBC Problem
-------------

We have found that using eglibc (<= 2.15) may cause severe errors in floating
point computation when we change the rounding-mode using `fesetround()`
function. If you're using the latest Mac OSX, you should be fine. If you're
using Ubuntu OS (<= 12.10), please check the version of your eglibc by typing:

    $ ldd --config

If the version is <= 2.15, please check out the latest version of eglibc:

    $ svn co http://www.eglibc.org/svn/trunk eglibc

and install them on your machine. (NOTE: we recommend to install it on your home dir)
