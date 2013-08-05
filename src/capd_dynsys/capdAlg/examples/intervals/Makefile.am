include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=intervalExample
intervalExample_SOURCES=intervalExample.cpp
intervalExample_libs=${capdintervals_LIBS} ${capdrounding_LIBS} 
intervalExample_LDADD=${intervalExample_libs}
intervalExample_DEPENDENCIES=${filter %.a %.la,${intervalExample_libs}}
intervalExample_CXXFLAGS=${capdintervals_CFLAGS} ${capdrounding_CFLAGS} 

