include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=newtonSimple newtontst

newtonSimple_SOURCES=newtonSimple.cpp
newtonSimple_CXXFLAGS=${capdDynSys_CFLAGS}
newtonSimple_libs=${capdDynSys_LIBS}
newtonSimple_LDADD=${newtonSimple_libs}
newtonSimple_DEPENDENCIES=${newtonSimple_libs:-%=}

newtontst_SOURCES=newtontst.cpp
newtontst_CXXFLAGS=${capdDynSys_CFLAGS}
newtontst_libs=${capdDynSys_LIBS}
newtontst_LDADD=${newtontst_libs}
newtontst_DEPENDENCIES=${newtontst_libs:-%=}

