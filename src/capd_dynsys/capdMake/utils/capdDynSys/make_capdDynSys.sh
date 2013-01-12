#!/bin/bash -e
########################################################################
#  USAGE:
#     make_capdDynSys  [zip_name] [svn_dir] [capd_dir]
#
#  it makes zip file with CAPD-DynSys library by:
#  - extracting from svn_dir capd and capdDynSys repositories 
#    to capd_dir (without .svn directories)
#  - removing not needed directories
#  - copying config files
#  - performing autoconf
#  - zipping
#
#  NOTE:
#    capd_dir     need to be direct subdirectory of current directory
#    
#
########################################################################

# zip file name
zip_name=$1
: ${zip_name:="capdDynSys.zip"}

# name of directory with working copy of capd 
svn_dir=$2
: ${svn_dir:="capd"}

#  name of root directory of CAPD-DynSys
capd_dir=$3

: ${capd_dir:="capd_dynsys"}

rm -rf ${capd_dir}

echo " svn ${svn_dir}  capd ${capd_dir} zip ${zip_name}"

svn export ${svn_dir} ${capd_dir}
svn export ${svn_dir}/capdDynSys ${capd_dir}/capdDynSys

cd  ${capd_dir}

echo "removing boost directory"
rm -rf capdExt/boost

rm -rf capdExt/src/capd/bzip2
rm -rf capdExt/src/capd/chom
rm -rf capdExt/src/capd/homology

rm -rf capdExt/include/capd/bzip2
rm -rf capdExt/include/capd/chom
rm -rf capdExt/include/capd/homology

rm -rf capdExt/examples
rm -rf capdExt/programs


echo "recursively removing .svn folders from"
pwd
rm -rf `find . -type d -name .svn`

echo "we copy new config files"

cd capdMake/utils
cp -r capdDynSys/add/capd/* ../../../${capd_dir}
./generateMakefiles.sh
cd ../..

echo "Making configure script."
autoreconf --install 

echo "We zip CAPD-DynSys "
cd ..
rm -f ${zip_name}
zip -9 -r ${zip_name} ${capd_dir}

echo "File ${zip_name} done!"

