include ${capdMake}/make/common_makefile.mkf

check_PROGRAMS=nonAutTest
TESTS=${check_PROGRAMS}

nonAutTest_SOURCES=nonAutTest.cpp
nonAutTest_CXXFLAGS=${capdDynSys_CFLAGS}
nonAutTest_libs=${capdDynSys_LIBS}
nonAutTest_LDADD=${nonAutTest_libs}
nonAutTest_DEPENDENCIES=${nonAutTest_libs:-%=}

