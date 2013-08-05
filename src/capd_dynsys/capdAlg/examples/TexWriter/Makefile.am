include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=TexWriterExample TexWriterExample2

TexWriterExample_SOURCES=TexWriterExample.cpp
TexWriterExample_libs=${capdvectalg_LIBS} ${capdintervals_LIBS}
TexWriterExample_LDADD=${TexWriterExample_libs}
TexWriterExample_DEPENDENCIES=${filter %.a %.la,${TexWriterExample_libs}}
TexWriterExample_CXXFLAGS=${capdintervals_CFLAGS}

TexWriterExample2_SOURCES=TexWriterExample2.cpp
TexWriterExample2_libs=${capdvectalg_LIBS} ${capdintervals_LIBS}
TexWriterExample2_LDADD=${TexWriterExample2_libs}
TexWriterExample2_DEPENDENCIES=${filter %.a %.la,${TexWriterExample2_libs}}
TexWriterExample2_CXXFLAGS=${capdintervals_CFLAGS}
