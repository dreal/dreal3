include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=setarth

setarth_SOURCES=setarth.cpp
setarth_CXXFLAGS=${capdDynSys_CFLAGS} ${capdAux_CFLAGS} ${capdkrak_CFLAGS}
setarth_libs=${capdDynSys_LIBS} ${capdAux_LIBS} ${capdkrak_LIBS}
setarth_LDADD=${setarth_libs}
setarth_DEPENDENCIES=${setarth_libs:-%=}

