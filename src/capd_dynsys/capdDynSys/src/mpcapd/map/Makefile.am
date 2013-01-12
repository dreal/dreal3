include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libmpcapdmap.a
libmpcapdmap_a_SOURCES=C2Coeff.cpp  C2Map.cpp  CnCoeff.cpp  CnMap.cpp  Function.cpp  Map.cpp  Node.cpp
libmpcapdmap_a_CXXFLAGS= ${mpcapdmap_CFLAGS} ${mpcapdAlg_CFLAGS} 

pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = mpcapdmap.pc
