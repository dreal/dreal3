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

[cmake]:http://www.cmake.org/cmake/resources/software.html
[capd-dynsys]: http://capd.ii.uj.edu.pl/download.php

We have tested that executing the following command on the newly installed Ubuntu 12.04.3 LTS
configures all the required packages to build dReal2.

    sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y
    sudo add-apt-repository --yes ppa:kalakris/cmake
    sudo add-apt-repository ppa:dns/gnu
    sudo update-alternatives --remove-all gcc
    sudo update-alternatives --remove-all g++
    sudo apt-get update
    sudo apt-get install autoconf automake libtool git g++-4.8 bison flex \
                           libboost-dev libboost-thread-dev curl m4 cmake
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

 * Download and uncompress [CAPD-DynSys 3.0 SVN (daily) Snapshot][capd-dynsys-daily]
 * Configure and build:

````
wget http://krzesanica.ii.uj.edu.pl/capd/capdDynSys.zip
unzip capdDynSys.zip
cd capd_dynsys
autoreconf --install
./configure --without-gui
make
sudo make install
````

[capd-dynsys-daily]: http://krzesanica.ii.uj.edu.pl/capd/capdDynSys.zip

How to Build dReal
------------------

    mkdir build
    cd build
    cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=g++-4.8 -DCMAKE_C_COMPILER=gcc-4.8 ../src
    make

GLIBC Problem
-------------

We have found that using eglibc (<= 2.15) may cause severe errors in floating
point computation when we change the rounding-mode using `fesetround()`
function. If you're using the latest Mac OSX, you should be fine. If you're
using Ubuntu OS (<= 12.10), please check the version of your eglibc by typing:

    ldd --config

If the version is <= 2.15, please check out the latest version of eglibc:

    svn co http://www.eglibc.org/svn/trunk eglibc

and install them on your machine. (NOTE: we recommend to install it on your home dir)
