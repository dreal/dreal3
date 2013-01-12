include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapdgeomset.a
libcapdgeomset_a_SOURCES=AffineSet.cpp  DoubletonSet.cpp  MatrixAffineSet.cpp  MatrixDoubletonSet.cpp
libcapdgeomset_a_CXXFLAGS= ${capdgeomset_CFLAGS} ${capdAlg_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdgeomset.pc
