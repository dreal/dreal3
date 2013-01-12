include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=alglibdemo
alglibdemo_SOURCES=alglibdemo.cpp
alglibdemo_libs=${capdvectalg_LIBS} ${capdalgfacade_LIBS} ${capdmatrixAlgorithms_LIBS} ${capdAux_LIBS} ${capdExt_LIBS}
alglibdemo_LDADD=${alglibdemo_libs}
alglibdemo_DEPENDENCIES=${alglibdemo_libs:-%=}
alglibdemo_CXXFLAGS=${capdvectalg_CFLAGS} ${capdalgfacade_CFLAGS} ${capdmatrixAlgorithms_CFLAGS} ${capdAux_CFLAGS} ${capdExt_CFLAGS}

