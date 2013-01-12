include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=floatMatrixAlgExample
floatMatrixAlgExample_SOURCES=floatMatrixAlgExample.cpp
floatMatrixAlgExample_libs=${capdintervals_LIBS}
floatMatrixAlgExample_LDADD=${floatMatrixAlgExample_libs}
floatMatrixAlgExample_DEPENDENCIES=${floatMatrixAlgExample_libs:-%=}
floatMatrixAlgExample_CXXFLAGS=${capdintervals_CFLAGS}

