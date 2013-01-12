include ${capdMake}/make/common_makefile.mkf


noinst_PROGRAMS=MpIntExample
MpIntExample_SOURCES=MpIntExample.cpp
MpIntExample_libs=${mpfr_LIBS}
MpIntExample_LDADD=${MpIntExample_libs}
MpIntExample_DEPENDENCIES=${MpIntExample_libs:-%=}
MpIntExample_CXXFLAGS=${capdvectalg_CFLAGS} ${mpfr_CFLAGS}

