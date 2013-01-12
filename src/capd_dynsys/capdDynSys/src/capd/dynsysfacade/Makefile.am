include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapddynsysfacade.a
libcapddynsysfacade_a_SOURCES=DFunction.cpp  DMap.cpp  DPoincareMap.cpp  DTaylor.cpp  IC1Rect2.cpp  IFunction.cpp  IMap.cpp  IRect2Set.cpp  ITaylor.cpp
libcapddynsysfacade_a_CXXFLAGS= ${capddynsysfacade_CFLAGS} ${capdAlg_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capddynsysfacade.pc
