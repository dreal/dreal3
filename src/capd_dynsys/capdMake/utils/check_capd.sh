#!/bin/bash -e

##############################################################################
#
#  Checks CAPD library compilation system
#
#  USAGE:
#    ./check_capd  capd_dir  install_dir  working_dir
#  where
#    capd_dir      directory with sources of CAPD library
#    install_dir   directory where CAPD should be installed
#    working_dir   working directory (will contain results of compilation)
#
#  We assume that all directories are subdirectories of current directory
#
#  Check consists of the following steps:
#  - in working_dir library is configured and compiled
#  - test from CAPD are run (make check)
#  - library is installed to install_dir
#  - example program is compiled and linked against installed library
#
##############################################################################

CURRENT_DIR=${PWD}

#  name of root directory of CAPD-DynSys
capd_dir=$1
: ${capd_dir:="capd_dynsys"}
CAPD_DIR=`readlink -m ${capd_dir}`

# name of directory to install capd
install_dir=$2
: ${install_dir:="__capd_install"}
CAPD_INSTALL=`readlink -m ${install_dir}`

# working directory 
working_dir=$3
: ${working_dir:="__capd_tmp"}
WORKING_DIR=`readlink -m ${working_dir}`

echo "CAPD : ${CAPD_DIR}"
echo "INSTALL : $CAPD_INSTALL"
echo "WORKING : $WORKING_DIR"

echo "we try to compile"
rm -rf ${working_dir}
mkdir -p ${working_dir}
cd ${working_dir}
../${capd_dir}/configure --prefix ${CAPD_INSTALL}

make 
make check
make install
echo "Library intalled!!!"

cd ${CAPD_DIR}/capdMake/examples/projectStarter
make CAPDBINDIR=${CAPD_INSTALL}/bin/
echo "Compilation success!!!"

cd ${CURRENT_DIR}

