include ${capdMake}/make/common_makefile.mkf

check_PROGRAMS=matrixMDTest vectMDTest vecttst
TESTS=matrixMDTest vectMDTest

matrixMDTest_SOURCES=matrixMDTest.cpp
matrixMDTest_CXXFLAGS=${capdAlg_CFLAGS}
matrixMDTest_libs=${capdAlg_LIBS} 
matrixMDTest_LDADD=${matrixMDTest_libs}
matrixMDTest_DEPENDENCIES=${matrixMDTest_libs:-%=}

vectMDTest_SOURCES=vectMDTest.cpp
vectMDTest_CXXFLAGS=${capdAlg_CFLAGS}
vectMDTest_libs=${capdAlg_LIBS}
vectMDTest_LDADD=${vectMDTest_libs}
vectMDTest_DEPENDENCIES=${vectMDTest_libs:-%=}

vecttst_SOURCES=vecttst.cpp
vecttst_CXXFLAGS=${capdAlg_CFLAGS}
vecttst_libs=${capdAlg_LIBS}
vecttst_LDADD=${vecttst_libs}
vecttst_DEPENDENCIES=${vecttst_libs:-%=}

