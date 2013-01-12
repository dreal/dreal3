include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapdalgfacade.a
libcapdalgfacade_a_SOURCES=DInterval.cpp  DNorm.cpp  INorm.cpp  IVector.cpp
libcapdalgfacade_a_CXXFLAGS= ${capdalgfacade_CFLAGS} ${capdAux_CFLAGS}  ${capdExt_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdalgfacade.pc
