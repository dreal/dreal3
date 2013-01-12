#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

#AC_PREREQ(2.61)
AC_INIT(capdDynSys-examples, 1.0, BUG-REPORT-ADDRESS)

AC_CONFIG_AUX_DIR(../../capdMake)
default_top_capd=${srcdir}/../..
top_capd_build=./../..
m4_include([../../capdMake/make/configure_common.ac])


AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([cndemo/Makefile])
AC_CONFIG_FILES([coveringRelation/Makefile])
AC_CONFIG_FILES([diffIncldemo/Makefile])
AC_CONFIG_FILES([encloseTrajectory/Makefile])
AC_CONFIG_FILES([graphicalSet/Makefile])
AC_CONFIG_FILES([integrate/Makefile])
AC_CONFIG_FILES([multiPrecision/Makefile])
AC_CONFIG_FILES([newton/Makefile])
AC_CONFIG_FILES([pointst/Makefile])
AC_CONFIG_FILES([RosslerPeriodicOrbit/Makefile])
AC_CONFIG_FILES([taylor/Makefile])
AC_CONFIG_FILES([setarth/Makefile])


AC_PROG_CXX

PKG_CHECK_MODULES([capdAux], [capdAux >= 1.0])

HAVE_capdkrak=yes
PKG_CHECK_MODULES([capdkrak], [capdkrak >= 1.0], [], [HAVE_capdkrak=no])
AM_CONDITIONAL([HAVE_capdkrak], [test "x$HAVE_capdkrak" = "xyes"])

PKG_CHECK_MODULES([capdExt], [capdExt >= 1.0])
PKG_CHECK_MODULES([capdDynSys], [capdDynSys >= 1.0])


AC_CONFIG_HEADERS([config.h])
AC_OUTPUT
