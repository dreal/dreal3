#!/bin/bash -xv

########################################################################
#
# USAGE:
#     create_snapshoot  [zip_name] [packages] [root_dir] [svn_dir]
# 
#  - checks out main capd repository and repositories containing packages 
#      into svn_dir, 
#  - creates distribution (stripping SVN info) in root_dir
#  - zips it into zip_name
#  - makes compilation tests
#  - publish it to WWW directory if tests succeeded 
#  
#
#  NOTE:
#    All directories should be relative path
#    root_dir     need to be direct subdirectory of current directory
#    
#
########################################################################


###########  settings ###########################

# zip (snapshoot) file name
zip_name=$1
: ${zip_name:="capd_src.zip"}

# modules to be included 
packages=$2
: ${packages:="capdDynSys4 capdRedHom capdExtHom"}

#  name of the root directory (in the zip file) 
root_dir=$3
: ${root_dir:="capd4"}

# working directory
work_dir=$4
 : ${work_dir:="/lhome/home/capd/capd-cron/capd_snapshoot"}

# directory for testing compilation system of CAPD
test_dir="capd_test_dir"

# www directory - where to publish results  
www_dir="/lhome/home/capd/www/capd"

################ end of settings #######################


mkdir  -p ${work_dir}
cd ${work_dir}


# cheking out CAPD from repository 
rm -rf ${root_dir}
svn co https://mnich.ii.uj.edu.pl/svn-repos/capd  ${root_dir}
cd ${root_dir}
for module in ${packages}
do
svn co https://mnich.ii.uj.edu.pl/svn-repos/${module}
done

echo "generating Makefiles "
cd capdMake/utils
./generateMakefiles.sh

echo "generating configure scripts"
cd ../../
autoreconf -i

#echo "recursively removing .svn folders from" 
#pwd
#rm -rf `find . -type d -name .svn`

echo "making zip file without SVN informations"
cd ..
rm -f ${zip_name}
find ${root_dir} -type d -name .svn | sed "s/\(.*\)/\1\/\n\1\/*/" > list.ex
zip -u -9 -r ${zip_name} capd -x@list.ex
chmod 664 ${zip_name}

echo "making compilation tests"
rm -rf ${test_dir} 
mkdir -p ${test_dir}
#cp ${zip_name} ${test_dir}/
unzip ${zip_name} -d ${test_dir}
cd ${test_dir}
../${root_dir}/capdMake/utils/check_capd.sh ${root_dir} 

echo "publishing to WWW" 
mv --backup=numbered ${zip_name} ${www_dir}
#rm -f /srv/www/htdocs/capd/${snapshoot_name}.~10~
