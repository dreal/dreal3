#!/usr/bin/env bash
# Author: Soonho Kong (soonhok@cs.cmu.edu)

OS=`uname`

########################################################################
# Check Required Packages
########################################################################
function check_pkg_debian {
    dpkg -s $1 > /dev/null 2>&1
    if [ $? -ne 0 ]; then
        echo "Required package $1 is not installed."
        echo "Check https://github.com/dreal/dreal3 for more information"
        exit 1
    fi
}
function check_pkg_osx {
    hash $1
    if [ $? -ne 0 ]; then
        echo "Required package $1 is not installed."
        echo "Check https://github.com/dreal/dreal3 for more information"
        exit 1
    fi
}
if [ $OS == "Linux" ]; then
    for pkg in autoconf automake bison cmake flex git libtool make pkg-config texinfo
    do
        check_pkg_debian $pkg
    done
fi
if [ $OS == "Darwin" ]; then
    for pkg in autoconf automake cmake libtool pkg-config
    do
        check_pkg_osx $pkg
    done
fi
exit 1

########################################################################
# Find C++11 Compiler and C Compiler
########################################################################
for CXX in ccache-g++ g++-5 g++-4.9 g++-4.8 ccache-clang++ clang++-3.7 clang++-3.6 clang++-3.5 clang++-3.4 clang++-3.3
do
    CXX_PATHNAME=`which $CXX`
    if [ -e "${CXX_PATHNAME}" ]; then
        echo CXX: ${CXX} found at ${CXX_PATHNAME}...
        break;
    fi
done
if [ ! -e "${CXX_PATHNAME}" ]; then
    cat <<EOF
It seems that C++11-compatible compilers are not installed on your system.
Please install either g++ 4.8 (or newer) or clang++ 3.3 (or newer).
EOF
    exit 1
fi
for CC in ccache-gcc gcc-5 gcc-4.9 gcc-4.8 ccache-clang clang-3.7 clang-3.6 clang-3.5 clang-3.4 clang-3.3
do
    CC_PATHNAME=`which $CC`
    if [ -e "$CC_PATHNAME" ]; then
        echo CC:  $CC found at ${CC_PATHNAME}...
        break;
    fi
done

########################################################################
# Build Solver (C++)
########################################################################
if [ ! -d build ]; then
    mkdir build
fi
cd build
cmake -DCMAKE_CXX_COMPILER=$CXX -DCMAKE_C_COMPILER=$CC -DCMAKE_BUILD_TYPE=RELEASE ../src
make -j 2
cd ../
