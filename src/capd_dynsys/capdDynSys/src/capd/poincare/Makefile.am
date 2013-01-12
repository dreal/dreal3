include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapdpoincare.a
libcapdpoincare_a_SOURCES=PoincareMap.cpp  PoincareMapJet.cpp  TimeMap.cpp
libcapdpoincare_a_CXXFLAGS= ${capdpoincare_CFLAGS} ${capdAlg_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdpoincare.pc
