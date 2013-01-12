include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libmpcapdvectalg.a
libmpcapdvectalg_a_SOURCES=Container.cpp  MpMatrix.cpp  MpVector.cpp  MpZMatrix.cpp  MpZVector.cpp  Norm.cpp
libmpcapdvectalg_a_CXXFLAGS=  ${mpcapdvectalg_CFLAGS} ${capdAux_CFLAGS} 



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = mpcapdvectalg.pc
