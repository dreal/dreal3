include ${capdMake}/make/common_makefile.mkf

check_PROGRAMS=intervalTest
TESTS=${check_PROGRAMS}

intervalTest_SOURCES=intervalTest.cpp
intervalTest_libs=${capdintervals_LIBS}
intervalTest_LDADD=${intervalTest_libs}
intervalTest_DEPENDENCIES=${filter %.a %.la,${intervalTest_libs}}
intervalTest_CXXFLAGS=${capdintervals_CFLAGS} 

