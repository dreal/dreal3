BMC for C++
===========
Soonho Kong <soonhok@cs.cmu.edu>

Required Packages: LLVM, Clang, Ninja, and CMake
-----------------

 - Checkout LLVM & Clang
    $ mkdir ~/clang-llvm && cd ~/clang-llvm
    $ git clone http://llvm.org/git/llvm.git
    $ cd llvm/tools
    $ git clone http://llvm.org/git/clang.git
    $ cd clang/tools
    $ git clone http://llvm.org/git/clang-tools-extra.git extra

 - Install Ninja
    $ git clone https://github.com/martine/ninja.git
    $ cd ninja
    $ git checkout release
    $ ./bootstrap.py
    $ sudo cp ninja /usr/bin/

 - Install Cmake
    $ git clone git://cmake.org/stage/cmake.git
    $ cd cmake
    $ git checkout next
    $ ./bootstrap
    $ make
    $ sudo make install

 - Build LLVM & Clang
    $ cd ~/clang-llvm
    $ mkdir build && cd build
    $ cmake -G Ninja ../llvm -DLLVM_BUILD_TESTS=ON  # Enable tests; default is off.
    $ ninja
    $ ninja check       # Test LLVM only.
    $ ninja clang-test  # Test Clang only.
    $ ninja install

Compile
-------

    $ mkdir build && cd build
    $ cmake ../
    $ make

