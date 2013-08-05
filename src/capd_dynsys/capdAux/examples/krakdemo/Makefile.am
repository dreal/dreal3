include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=krakdemo
krakdemo_SOURCES=krakdemo.cpp
krakdemo_libs=${capdkrak_LIBS} ${capdauxil_LIBS}
krakdemo_LDADD=${krakdemo_libs}
krakdemo_DEPENDENCIES=${filter %.a %.la,${krakdemo_libs}}
krakdemo_CXXFLAGS=${capdkrak_CFLAGS} ${capdauxil_CFLAGS}

