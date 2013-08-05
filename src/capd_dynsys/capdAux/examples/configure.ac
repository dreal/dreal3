#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

#AC_PREREQ(2.61)
AC_INIT(capdAux-examples, 1.0, BUG-REPORT-ADDRESS)

AC_CONFIG_AUX_DIR(../../capdMake)
default_top_capd=${srcdir}/../..
top_capd_build=./../..
m4_include([../../capdMake/make/configure_common.ac])
#m4_include([../../capdMake/make/configure_common_x.ac])


AC_CONFIG_FILES([Makefile])



AC_PROG_CXX

capdkrak=yes
PKG_CHECK_MODULES([capdkrak], [capdkrak >= 1.0], [], [capdkrak=no])

AM_CONDITIONAL([HAVE_capdkrak], [test "x$capdkrak" = "xyes"])
if test "x$capdkrak" = "xyes"; then
  echo ${capdkrak_LIBS}       
fi

AC_CONFIG_FILES([krakdemo/Makefile])

PKG_CHECK_MODULES([capdauxil], [capdauxil >= 1.0])

AC_CONFIG_HEADER(config.h)
AC_OUTPUT
