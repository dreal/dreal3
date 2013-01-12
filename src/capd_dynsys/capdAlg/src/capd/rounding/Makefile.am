include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapdrounding.a
libcapdrounding_a_SOURCES=DoubleRounding.cpp
libcapdrounding_a_CXXFLAGS= ${capdrounding_CFLAGS} ${capdAux_CFLAGS}  ${capdExt_CFLAGS}




pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdrounding.pc
