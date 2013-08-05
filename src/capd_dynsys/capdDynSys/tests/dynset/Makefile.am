
check_PROGRAMS=AffineSet C0Pped2SetTest Rect2SetTest \
               CoordReorganization    FactorReorganization\
            CenteredAffineSetTest DoubletonSetTest C0RectSetTest C0PpedSetTest

TESTS=${check_PROGRAMS}

AM_CXXFLAGS = ${capdDynSys_CFLAGS} 
LDADD=${capdDynSys_LIBS} 
#-lboost_unit_test_framework

AffineSet_SOURCES= AffineSetTest.cpp
AffineSet_DEPENDENCIES=${filter %.a %.la,${LDADD}} 

C0Pped2SetTest_SOURCES= C0Pped2SetTest.cpp 
C0Pped2SetTest_DEPENDENCIES=${filter %.a %.la,${LDADD}} 

Rect2SetTest_SOURCES= Rect2SetTest.cpp
Rect2SetTest_DEPENDENCIES=${filter %.a %.la,${LDADD}} 

CoordReorganization_SOURCES= CoordReorganization.cpp
CoordReorganization_DEPENDENCIES=${filter %.a %.la,${LDADD}} 

FactorReorganization_SOURCES= FactorReorganization.cpp
FactorReorganization_DEPENDENCIES=${filter %.a %.la,${LDADD}} 

CenteredAffineSetTest_SOURCES= CenteredAffineSetTest.cpp
CenteredAffineSetTest_DEPENDENCIES=${filter %.a %.la,${LDADD}} 

DoubletonSetTest_SOURCES= DoubletonSetTest.cpp
DoubletonSetTest_DEPENDENCIES=${filter %.a %.la,${LDADD}} 

C0RectSetTest_SOURCES=C0RectSetTest.cpp
C0RectSetTest_DEPENDENCIES=${filter %.a %.la,${LDADD}} 

C0PpedSetTest_SOURCES= C0PpedSetTest.cpp
C0PpedSetTest_DEPENDENCIES=${filter %.a %.la,${LDADD}} 
