include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=diffInclExample

diffInclExample_SOURCES=diffInclExample.cpp
diffInclExample_CXXFLAGS=${capdDynSys_CFLAGS}
diffInclExample_libs=${capdDynSys_LIBS}
diffInclExample_LDADD=${diffInclExample_libs}
diffInclExample_DEPENDENCIES=${diffInclExample_libs:-%=}

