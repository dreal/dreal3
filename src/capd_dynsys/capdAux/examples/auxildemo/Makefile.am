include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=argdemo
argdemo_SOURCES=argdemo.cpp
argdemo_libs=${capdauxil_LIBS}
argdemo_LDADD=${argdemo_libs}
argdemo_DEPENDENCIES=${argdemo_libs:-%=}
argdemo_CXXFLAGS=${capdauxil_CFLAGS}

