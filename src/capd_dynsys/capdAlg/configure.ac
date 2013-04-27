#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

#AC_PREREQ(2.61)
AC_INIT(capdAlg, 1.0, BUG-REPORT-ADDRESS)

AC_CONFIG_AUX_DIR(../capdMake)
default_top_capd=${srcdir}/..
top_capd_build=./..
m4_include([../capdMake/make/configure_common.ac])
m4_include([../capdMake/make/configure_common_mpfr.ac])

AS_IF([test "x$HAVE_LIBmpfr" = "xyes"],
            [
            AC_SUBST(mpcapdAlg_CFLAGS)
            AC_SUBST(mpcapdAlg_LIBS)
            AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapdAlg.pc:src/mpcapd/mpcapdAlg-dev.pc.in])
            AC_CONFIG_FILES([src/mpcapd/mpcapdAlg.pc:src/mpcapd/mpcapdAlg-install.pc.in])
            AC_SUBST(mpcapdintervals_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
            AC_SUBST(mpcapdintervals_LIBS, ["$mpfr_LIBS"])
            AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapdintervals.pc:src/mpcapd/intervals/mpcapdintervals-dev.pc.in])
            AC_CONFIG_FILES([src/mpcapd/intervals/mpcapdintervals.pc:src/mpcapd/intervals/mpcapdintervals-install.pc.in])
            AC_SUBST(mpcapdmatrixAlgorithms_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
            AC_SUBST(mpcapdmatrixAlgorithms_LIBS, ["$mpfr_LIBS"])
            AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapdmatrixAlgorithms.pc:src/mpcapd/matrixAlgorithms/mpcapdmatrixAlgorithms-dev.pc.in])
            AC_CONFIG_FILES([src/mpcapd/matrixAlgorithms/mpcapdmatrixAlgorithms.pc:src/mpcapd/matrixAlgorithms/mpcapdmatrixAlgorithms-install.pc.in])
            AC_SUBST(mpcapdvectalg_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
            AC_SUBST(mpcapdvectalg_LIBS, ["$mpfr_LIBS"])
            AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapdvectalg.pc:src/mpcapd/vectalg/mpcapdvectalg-dev.pc.in])
            AC_CONFIG_FILES([src/mpcapd/vectalg/mpcapdvectalg.pc:src/mpcapd/vectalg/mpcapdvectalg-install.pc.in])
            echo
            echo Multiprecision support enabled
            echo
            ],
            [
            rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapdAlg.pc
            rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapdintervals.pc
            rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapdmatrixAlgorithms.pc
            rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapdvectalg.pc
            ]
)


AC_SUBST(capdAlg_CFLAGS)
AC_SUBST(capdAlg_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdAlg.pc:src/capd/capdAlg-dev.pc.in])
AC_CONFIG_FILES([src/capd/capdAlg.pc:src/capd/capdAlg-install.pc.in])
AC_SUBST(capdbasicalg_CFLAGS, ["-frounding-math"])
AC_SUBST(capdbasicalg_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdbasicalg.pc:src/capd/basicalg/capdbasicalg-dev.pc.in])
AC_CONFIG_FILES([src/capd/basicalg/capdbasicalg.pc:src/capd/basicalg/capdbasicalg-install.pc.in])
AC_SUBST(capdalgfacade_CFLAGS, ["-frounding-math"])
AC_SUBST(capdalgfacade_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdalgfacade.pc:src/capd/algfacade/capdalgfacade-dev.pc.in])
AC_CONFIG_FILES([src/capd/algfacade/capdalgfacade.pc:src/capd/algfacade/capdalgfacade-install.pc.in])
AC_SUBST(capdintervals_CFLAGS, ["-frounding-math"])
AC_SUBST(capdintervals_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdintervals.pc:src/capd/intervals/capdintervals-dev.pc.in])
AC_CONFIG_FILES([src/capd/intervals/capdintervals.pc:src/capd/intervals/capdintervals-install.pc.in])
AC_SUBST(capdmatrixAlgorithms_CFLAGS, ["-frounding-math"])
AC_SUBST(capdmatrixAlgorithms_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdmatrixAlgorithms.pc:src/capd/matrixAlgorithms/capdmatrixAlgorithms-dev.pc.in])
AC_CONFIG_FILES([src/capd/matrixAlgorithms/capdmatrixAlgorithms.pc:src/capd/matrixAlgorithms/capdmatrixAlgorithms-install.pc.in])
AC_SUBST(capdrounding_CFLAGS, ["-frounding-math"])
AC_SUBST(capdrounding_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdrounding.pc:src/capd/rounding/capdrounding-dev.pc.in])
AC_CONFIG_FILES([src/capd/rounding/capdrounding.pc:src/capd/rounding/capdrounding-install.pc.in])
AC_SUBST(capdvectalg_CFLAGS, ["-frounding-math"])
AC_SUBST(capdvectalg_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdvectalg.pc:src/capd/vectalg/capdvectalg-dev.pc.in])
AC_CONFIG_FILES([src/capd/vectalg/capdvectalg.pc:src/capd/vectalg/capdvectalg-install.pc.in])

AC_CONFIG_HEADERS([include/capd/config-capdAlg.h])


AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([include/Makefile])
AC_CONFIG_FILES([src/Makefile])

AC_CONFIG_FILES([src/capd/Makefile])
AC_CONFIG_FILES([src/capd/basicalg/Makefile])
AC_CONFIG_FILES([src/capd/algfacade/Makefile])
AC_CONFIG_FILES([src/capd/intervals/Makefile])
AC_CONFIG_FILES([src/capd/matrixAlgorithms/Makefile])
AC_CONFIG_FILES([src/capd/rounding/Makefile])
AC_CONFIG_FILES([src/capd/vectalg/Makefile])

AC_CONFIG_FILES([src/mpcapd/Makefile])
AC_CONFIG_FILES([src/mpcapd/intervals/Makefile])
AC_CONFIG_FILES([src/mpcapd/matrixAlgorithms/Makefile])
AC_CONFIG_FILES([src/mpcapd/vectalg/Makefile])


AC_CONFIG_SUBDIRS([examples])
AC_CONFIG_SUBDIRS([tests])


# Checks for programs.
AC_PROG_CXX

# Checks for libraries.
AC_PROG_RANLIB
# LT_INIT

# Checks for header files.

# Checks for typedefs, structures, and compiler characteristics.
#AC_HEADER_STDBOOL

# Checks for library functions.
PKG_CHECK_MODULES([capdAux], [capdAux >= 1.0])
PKG_CHECK_MODULES([capdExt], [capdExt >= 1.0])

AC_OUTPUT
