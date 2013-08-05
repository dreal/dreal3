#!/bin/bash -e
######################################################################################
#
#  It generates files Makefile.am containing list of all header files
#  for all modules of CAPD library.
#  We do that in the case that someone forgot to add new header files to Makefile.am.
#  Otherwise they will be not present in the installed version of the library 
# 
######################################################################################


listHeaders=../../capdMake/utils/listHeaderFiles.sh

cd ../../capdAux/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
cd ../../capdAlg/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
cd ../../capdExt/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
if test -e "../../capdDynSys" ; then
  cd ../../capdDynSys/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
fi
if test -e "../../capdDynSys4" ; then
  cd ../../capdDynSys4/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
fi
if test -e "../../capdRedHom" ; then
cd ../../capdRedHom/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
fi

echo "Header files generated!"
