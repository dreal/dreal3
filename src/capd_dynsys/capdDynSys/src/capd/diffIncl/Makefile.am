include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapddiffIncl.a
libcapddiffIncl_a_SOURCES=DiffInclusion.cpp  DiffInclusionCW.cpp  DiffInclusionLN.cpp  InclRect2Set.cpp   MultiMap.cpp
libcapddiffIncl_a_CXXFLAGS= ${capddiffIncl_CFLAGS} ${capdAlg_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capddiffIncl.pc
