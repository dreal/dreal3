include ${capdMake}/make/common_makefile.mkf


lib_LIBRARIES=libcapdmatrixAlgorithms.a
libcapdmatrixAlgorithms_a_SOURCES= floatMatrixAlgorithms.cpp  intMatrixAlgorithms.cpp
libcapdmatrixAlgorithms_a_CXXFLAGS= ${capdmatrixAlgorithms_CFLAGS} ${capdAux_CFLAGS} ${capdExt_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdmatrixAlgorithms.pc
