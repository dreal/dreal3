include ${capdMake}/make/common_makefile.mkf

lib_LIBRARIES=libcapddynset.a
libcapddynset_a_SOURCES= BallSet.cpp        C0Rect2RSet.cpp  C11Rect2.cpp    C1Rect2Set.cpp  CnRect2.cpp \
                         EllipsoidSet.cpp   IntervalSet.cpp  Rect2Set.cpp    C0Pped2RSet.cpp  C0Rect2Set.cpp \
                         C1Pped2Set.cpp     C1Rect.cpp       CnRect2MultiLip.cpp  Intv2Set.cpp   RectSet.cpp \
                         C0Pped2Set.cpp     C0RectSet.cpp    C1PpedSet.cpp   C1RectSet.cpp   CnRect2MultiMatrix.cpp  \
                         FactorReorganization.cpp  Pped2Set.cpp C0PpedSet.cpp    C0RectSet.hpp    C1Rect2.cpp     \
                         C2Rect2.cpp     CoordReorganize.cpp     FlowballSet.cpp           PpedSet.cpp
libcapddynset_a_CXXFLAGS= ${capddynset_CFLAGS} ${capdAlg_CFLAGS}



pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capddynset.pc
