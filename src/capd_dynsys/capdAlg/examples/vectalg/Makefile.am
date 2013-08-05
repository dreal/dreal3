include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=matrixExample  normExample  vectorExample

matrixExample_SOURCES=matrixExample.cpp
matrixExample_libs=${capdintervals_LIBS}
matrixExample_LDADD=${matrixExample_libs}
matrixExample_DEPENDENCIES=${filter %.a %.la,${matrixExample_libs}}
matrixExample_CXXFLAGS=${capdintervals_CFLAGS}

normExample_SOURCES=normExample.cpp
normExample_libs=${capdvectalg_LIBS} ${capdintervals_LIBS}
normExample_LDADD=${normExample_libs}
normExample_DEPENDENCIES=${filter %.a %.la,${normExample_libs}}
normExample_CXXFLAGS=${capdvectalg_CFLAGS} ${capdintervals_CFLAGS}

vectorExample_SOURCES=vectorExample.cpp
vectorExample_libs=${capdvectalg_LIBS} ${capdintervals_LIBS}
vectorExample_LDADD=${vectorExample_libs}
vectorExample_DEPENDENCIES=${filter %.a %.la,${vectorExample_libs}}
vectorExample_CXXFLAGS=${capdvectalg_CFLAGS} ${capdintervals_CFLAGS}


