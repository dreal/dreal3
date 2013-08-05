include ${capdMake}/make/common_makefile.mkf

check_PROGRAMS=divtst intvtst ioTest
TESTS=${check_PROGRAMS}

divtst_SOURCES=divtst.cpp
intvtst_SOURCES=intvtst.cpp
divtst_libs=${capdintervals_LIBS} ${capdExt_LIBS}
divtst_LDADD=${divtst_libs}
divtst_DEPENDENCIES=${filter %.a %.la,${divtst_libs}}
divtst_CXXFLAGS=${capdintervals_CFLAGS} ${capdExt_CFLAGS} ${capdExt_CFLAGS}
intvtst_libs=${capdintervals_LIBS} ${capdExt_LIBS}
intvtst_LDADD=${intvtst_libs}
intvtst_DEPENDENCIES=${filter %.a %.la,${intvtst_libs}}
intvtst_CXXFLAGS=${capdintervals_CFLAGS} ${capdExt_CFLAGS} ${capdExt_CFLAGS}

ioTest_SOURCES=ioTest.cpp
ioTest_libs=${capdintervals_LIBS} ${capdExt_LIBS} 
ioTest_LDADD=${ioTest_libs}
ioTest_DEPENDENCIES=${filter %.a %.la,${ioTest_libs}}
ioTest_CXXFLAGS=${capdintervals_CFLAGS} ${capdExt_CFLAGS}
