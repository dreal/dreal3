include ${capdMake}/make/common_makefile.mkf


lib_LIBRARIES=libcapdintervals.a
libcapdintervals_a_SOURCES=DoubleInterval.cpp
libcapdintervals_a_CXXFLAGS= ${capdintervals_CFLAGS} ${capdAux_CFLAGS}  ${capdExt_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdintervals.pc
