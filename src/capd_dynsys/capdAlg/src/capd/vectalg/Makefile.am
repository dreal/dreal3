include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapdvectalg.a
libcapdvectalg_a_SOURCES=Container.cpp  DVector.cpp  IVector.cpp    Makefile.am Norm.cpp DMatrix.cpp    IMatrix.cpp  Multiindex.cpp  ZVector.cpp
libcapdvectalg_a_CXXFLAGS= ${capdvectalg_CFLAGS} ${capdAux_CFLAGS}  ${capdExt_CFLAGS}




pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdvectalg.pc
