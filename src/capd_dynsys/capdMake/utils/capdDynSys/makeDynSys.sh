#!/bin/bash -e

########################################################################
#  USAGE:
#     makeDynSys  [zip_name] [dynsys_dir] [user_name] [svn_dir]
#  
#  - checks out repositories capd and capdDynSys into svn_dir 
#    using user_name as login, 
#  - creates CAPD-DynSys distribution in dynsys_dir
#  - zips into zip_name
#  - makes compilation tests
#  
#
#  NOTE:
#    All directories should be relative path
#    dynsys_dir     need to be direct subdirectory of current directory
#    
#
########################################################################


# zip file name
zip_name=$1
: ${zip_name:="capdDynSys.zip"}

#  name of root directory of CAPD-DynSys
dynsys_dir=$2
: ${dynsys_dir:="capd_dynsys"}

# user name for svn
user=$3
: ${user:="kapela"}

# name of directory with working copy of capd 
svn_dir=$2
: ${svn_dir:="capd_svn"}

test_dir="capd_test_dir"



echo "checking out capd and capdDynSys repositories"
#rm -rf ${svn_dir}
#svn co svn+ssh://$user@mnich.ii.uj.edu.pl/capd/capd ${svn_dir}
#svn co svn+ssh://$user@mnich.ii.uj.edu.pl/capd/capdDynSys ${svn_dir}/capdDynSys


bash -e -v ./${svn_dir}/capdMake/utils/capdDynSys/make_capdDynSys.sh "${zip_name}" "${svn_dir}" "${dynsys_dir}" 

rm -rf ${test_dir} 
mkdir -p ${test_dir}
#cp ${zip_name} ${test_dir}/
unzip ${zip_name} -d ${test_dir}
cd ${test_dir}
../${svn_dir}/capdMake/utils/check_capd.sh ${dynsys_dir} 


#echo "Copy snapshoot to WWW!"
#cd ..
#mv --backup=numbered capdDynSys.zip /srv/www/htdocs/capd/
#echo "Done!"

