include ${capdMake}/make/common_makefile.mkf

check_PROGRAMS=divtst intvtst
TESTS=${check_PROGRAMS}

divtst_SOURCES=divtst.cpp
intvtst_SOURCES=intvtst.cpp
divtst_libs=${capdintervals_LIBS}
divtst_LDADD=${divtst_libs}
divtst_DEPENDENCIES=${divtst_libs:-%=}
divtst_CXXFLAGS=${capdintervals_CFLAGS} ${capdExt_CFLAGS}
intvtst_libs=${capdintervals_LIBS}
intvtst_LDADD=${intvtst_libs}
intvtst_DEPENDENCIES=${intvtst_libs:-%=}
intvtst_CXXFLAGS=${capdintervals_CFLAGS} ${capdExt_CFLAGS}

