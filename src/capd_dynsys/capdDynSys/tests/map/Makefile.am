include ${capdMake}/make/common_makefile.mkf

check_PROGRAMS=CnMapTest
TESTS=${check_PROGRAMS}

CnMapTest_SOURCES=CnMapTest.cpp
CnMapTest_CXXFLAGS=${capdDynSys_CFLAGS} 
CnMapTest_libs=${capdDynSys_LIBS} 
#${capdExt_LIBS}
CnMapTest_LDADD=${CnMapTest_libs}
CnMapTest_DEPENDENCIES=${CnMapTest_libs:-%=}

