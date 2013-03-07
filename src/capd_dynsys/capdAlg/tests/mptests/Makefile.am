include ${capdMake}/make/common_makefile.mkf

check_PROGRAMS=mpsintest
TESTS=${check_PROGRAMS}

mpsintest_SOURCES=mpsintest.cpp
mpsintest_libs=  ${mpcapdAlg_LIBS} ${capdAux_LIBS} 
# ${mpcapdintervals_LIBS} 
mpsintest_LDADD=${mpsintest_libs}
mpsintest_DEPENDENCIES=${mpsintest_libs:-%=} 
mpsintest_CXXFLAGS=${mpcapdintervals_CFLAGS} ${mpfr_CFLAGS} ${capdAux_CFLAGS}
