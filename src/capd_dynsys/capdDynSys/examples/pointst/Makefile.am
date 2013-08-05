include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=pointst

pointst_SOURCES=pointst.cpp
pointst_CXXFLAGS=${capdkrak_CFLAGS} ${capdDynSys_CFLAGS} ${capdAux_CFLAGS}
pointst_libs=${capdkrak_LIBS} ${capdDynSys_LIBS} ${capdAux_LIBS}
pointst_LDADD=${pointst_libs}
pointst_DEPENDENCIES=${filter %.a %.la,${pointst_libs}}

