#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

#AC_PREREQ(2.61)
AC_INIT(capdAlg-examples, 1.0, BUG-REPORT-ADDRESS)

AC_CONFIG_AUX_DIR(../../capdMake)
default_top_capd=${srcdir}/../..
top_capd_build=./../..
m4_include([../../capdMake/make/configure_common.ac])
m4_include([../../capdMake/make/configure_common_mpfr.ac])

AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([alglibdemo/Makefile])
AC_CONFIG_FILES([BigIntegers/Makefile])
AC_CONFIG_FILES([intervals/Makefile])
AC_CONFIG_FILES([matrixAlgorithms/Makefile])
AC_CONFIG_FILES([vectalg/Makefile])
AC_CONFIG_FILES([TexWriter/Makefile])

AC_PROG_CXX

PKG_CHECK_MODULES([capdbasicalg], [capdbasicalg >= 1.0])
PKG_CHECK_MODULES([capdalgfacade], [capdalgfacade >= 1.0])
PKG_CHECK_MODULES([capdintervals], [capdintervals >= 1.0])
PKG_CHECK_MODULES([capdmatrixAlgorithms], [capdmatrixAlgorithms >= 1.0])
PKG_CHECK_MODULES([capdrounding], [capdrounding >= 1.0])
PKG_CHECK_MODULES([capdvectalg], [capdvectalg >= 1.0])

PKG_CHECK_MODULES([capdAux], [capdAux >= 1.0])
PKG_CHECK_MODULES([capdExt], [capdExt >= 1.0])


AC_CONFIG_HEADER(config.h)
AC_OUTPUT
