include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=integrate integrateVariationalEquation

integrate_SOURCES=integrate.cpp
integrate_CXXFLAGS=${capdDynSys_CFLAGS}
integrate_libs=${capdDynSys_LIBS}
integrate_LDADD=${integrate_libs}
integrate_DEPENDENCIES=${filter %.a %.la,${integrate_libs}}

integrateVariationalEquation_SOURCES=integrateVariationalEquation.cpp
integrateVariationalEquation_CXXFLAGS=${capdDynSys_CFLAGS}
integrateVariationalEquation_libs=${capdDynSys_LIBS}
integrateVariationalEquation_LDADD=${integrateVariationalEquation_libs}
integrateVariationalEquation_DEPENDENCIES=${filter %.a %.la,${integrateVariationalEquation_libs}}

