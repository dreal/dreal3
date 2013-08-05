include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=graphicalSetTest

graphicalSetTest_SOURCES=graphicalSetTest.cpp
graphicalSetTest_CXXFLAGS=${capdkrak_CFLAGS} ${capdDynSys_CFLAGS} ${capdAux_CFLAGS}
graphicalSetTest_libs= ${capdkrak_LIBS} ${capdDynSys_LIBS} ${capdAux_LIBS}
graphicalSetTest_LDADD=${graphicalSetTest_libs}
graphicalSetTest_DEPENDENCIES=${filter %.a %.la,${graphicalSetTest_libs}}

