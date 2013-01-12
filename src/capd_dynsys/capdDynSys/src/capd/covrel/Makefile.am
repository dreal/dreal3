include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapdcovrel.a
libcapdcovrel_a_SOURCES=GraphicsHSet3D.cpp  GraphicsTripleSet.cpp  HSet2D.cpp  HSet3D.cpp  HSetMD.cpp  HSetND.cpp  TripleSet.cpp
libcapdcovrel_a_CXXFLAGS= ${capdcovrel_CFLAGS} ${capdAlg_CFLAGS} ${capdAux_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdcovrel.pc
