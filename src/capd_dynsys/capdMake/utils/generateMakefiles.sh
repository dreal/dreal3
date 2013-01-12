#!/bin/bash -e

listHeaders=../../capdMake/utils/listHeaderFiles.sh

cd ../../capdAux/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
cd ../../capdAlg/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
cd ../../capdExt/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
if test -e "../../capdDynSys" ; then
  cd ../../capdDynSys/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
fi
if test -e "../../capdRedHom" ; then
cd ../../capdRedHom/include && ${listHeaders} > Makefile.tmp && ( diff Makefile.tmp Makefile.am || cp Makefile.tmp Makefile.am ) && rm Makefile.tmp
fi

echo "Header files generated!"
