include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapdmap.a
libcapdmap_a_SOURCES=C2Coeff.cpp  C2Map.cpp  CnCoeff.cpp  CnMap.cpp  Function.cpp  Map.cpp  Node.cpp  Parser.cpp
libcapdmap_a_CXXFLAGS= ${capdmap_CFLAGS} ${capdAlg_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdmap.pc
