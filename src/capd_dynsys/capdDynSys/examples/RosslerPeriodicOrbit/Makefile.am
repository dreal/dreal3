include ${capdMake}/make/common_makefile.mkf

noinst_PROGRAMS=RosslerPeriodicOrbit

RosslerPeriodicOrbit_SOURCES=RosslerPeriodicOrbit.cpp
RosslerPeriodicOrbit_CXXFLAGS=${capdDynSys_CFLAGS}
RosslerPeriodicOrbit_libs=${capdDynSys_LIBS}
RosslerPeriodicOrbit_LDADD=${RosslerPeriodicOrbit_libs}
RosslerPeriodicOrbit_DEPENDENCIES=${RosslerPeriodicOrbit_libs:-%=}

