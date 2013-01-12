include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libmpcapddiffIncl.a
libmpcapddiffIncl_a_SOURCES=DiffInclusion.cpp  DiffInclusionCW.cpp  DiffInclusionLN.cpp  InclRect2Set.cpp  MultiMap.cpp
libmpcapddiffIncl_a_CXXFLAGS= ${mpcapddiffIncl_CFLAGS} ${mpcapdAlg_CFLAGS} 



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = mpcapddiffIncl.pc
