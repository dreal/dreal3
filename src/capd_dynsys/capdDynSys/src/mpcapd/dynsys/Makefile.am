include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libmpcapddynsys.a
libmpcapddynsys_a_SOURCES=C2Taylor.cpp  CnTaylor.cpp  DynSys.cpp  Taylor.cpp  TaylorHOE.cpp
libmpcapddynsys_a_CXXFLAGS= ${mpcapddynsys_CFLAGS} ${mpcapdAlg_CFLAGS} 



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = mpcapddynsysm.pc
