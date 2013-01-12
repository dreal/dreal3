include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libmpcapdgeomset.a
libmpcapdgeomset_a_SOURCES=AffineSet.cpp  DoubletonSet.cpp  MatrixAffineSet.cpp  MatrixDoubletonSet.cpp
libmpcapdgeomset_a_CXXFLAGS= ${mpcapdgeomset_CFLAGS} ${mpcapdAlg_CFLAGS} 



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = mpcapdgeomset.pc
