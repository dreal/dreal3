include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapddynsys.a
libcapddynsys_a_SOURCES=C2Taylor.cpp  CnTaylor.cpp  DynSys.cpp  Linear2d.cpp  Linear3d.cpp  OdeNumTaylor.cpp  Taylor.cpp  TaylorHOE.cpp  VLin3D.cpp
libcapddynsys_a_CXXFLAGS= ${capddynsys_CFLAGS} ${capdAlg_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capddynsysm.pc
