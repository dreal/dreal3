include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapddiffAlgebra.a
libcapddiffAlgebra_a_SOURCES=Curve.cpp
libcapddiffAlgebra_a_CXXFLAGS= ${capddiffAlgebra_CFLAGS} ${capdAlg_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capddiffAlgebra.pc
