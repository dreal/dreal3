#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

#AC_PREREQ(2.61)
AC_INIT(capdDynSys, 1.0, BUG-REPORT-ADDRESS)

AC_CONFIG_AUX_DIR(../capdMake)
default_top_capd=${srcdir}/..
top_capd_build=./..
m4_include([../capdMake/make/configure_common.ac])
m4_include([../capdMake/make/configure_common_mpfr.ac])

AC_SUBST(capdDynSys_CFLAGS)
AC_SUBST(capdDynSys_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdDynSys.pc:src/capd/capdDynSys-dev.pc.in])
AC_CONFIG_FILES([src/capd/capdDynSys.pc:src/capd/capdDynSys-install.pc.in])
AC_SUBST(capdcovrel_CFLAGS)
AC_SUBST(capdcovrel_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdcovrel.pc:src/capd/covrel/capdcovrel-dev.pc.in])
AC_CONFIG_FILES([src/capd/covrel/capdcovrel.pc:src/capd/covrel/capdcovrel-install.pc.in])
AC_SUBST(capddiffIncl_CFLAGS)
AC_SUBST(capddiffIncl_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capddiffIncl.pc:src/capd/diffIncl/capddiffIncl-dev.pc.in])
AC_CONFIG_FILES([src/capd/diffIncl/capddiffIncl.pc:src/capd/diffIncl/capddiffIncl-install.pc.in])
AC_SUBST(capddynsysm_CFLAGS)
AC_SUBST(capddynsysm_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capddynsysm.pc:src/capd/dynsys/capddynsysm-dev.pc.in])
AC_CONFIG_FILES([src/capd/dynsys/capddynsysm.pc:src/capd/dynsys/capddynsysm-install.pc.in])
AC_SUBST(capdgeomset_CFLAGS)
AC_SUBST(capdgeomset_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdgeomset.pc:src/capd/geomset/capdgeomset-dev.pc.in])
AC_CONFIG_FILES([src/capd/geomset/capdgeomset.pc:src/capd/geomset/capdgeomset-install.pc.in])
AC_SUBST(capdmap_CFLAGS)
AC_SUBST(capdmap_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdmap.pc:src/capd/map/capdmap-dev.pc.in])
AC_CONFIG_FILES([src/capd/map/capdmap.pc:src/capd/map/capdmap-install.pc.in])
AC_SUBST(capddiffAlgebra_CFLAGS)
AC_SUBST(capddiffAlgebra_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capddiffAlgebra.pc:src/capd/diffAlgebra/capddiffAlgebra-dev.pc.in])
AC_CONFIG_FILES([src/capd/diffAlgebra/capddiffAlgebra.pc:src/capd/diffAlgebra/capddiffAlgebra-install.pc.in])
AC_SUBST(capddynset_CFLAGS)
AC_SUBST(capddynset_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capddynset.pc:src/capd/dynset/capddynset-dev.pc.in])
AC_CONFIG_FILES([src/capd/dynset/capddynset.pc:src/capd/dynset/capddynset-install.pc.in])
AC_SUBST(capddynsysfacade_CFLAGS)
AC_SUBST(capddynsysfacade_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capddynsysfacade.pc:src/capd/dynsysfacade/capddynsysfacade-dev.pc.in])
AC_CONFIG_FILES([src/capd/dynsysfacade/capddynsysfacade.pc:src/capd/dynsysfacade/capddynsysfacade-install.pc.in])
AC_SUBST(capdpoincare_CFLAGS)
AC_SUBST(capdpoincare_LIBS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdpoincare.pc:src/capd/poincare/capdpoincare-dev.pc.in])
AC_CONFIG_FILES([src/capd/poincare/capdpoincare.pc:src/capd/poincare/capdpoincare-install.pc.in])



AC_CONFIG_HEADER([include/capd/config-capdDynSys.h])


AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([include/Makefile])
AC_CONFIG_FILES([src/Makefile])

AC_CONFIG_FILES([src/capd/Makefile])
AC_CONFIG_FILES([src/capd/covrel/Makefile])
AC_CONFIG_FILES([src/capd/diffIncl/Makefile])
AC_CONFIG_FILES([src/capd/dynsys/Makefile])
AC_CONFIG_FILES([src/capd/geomset/Makefile])
AC_CONFIG_FILES([src/capd/map/Makefile])
AC_CONFIG_FILES([src/capd/diffAlgebra/Makefile])
AC_CONFIG_FILES([src/capd/dynset/Makefile])
AC_CONFIG_FILES([src/capd/dynsysfacade/Makefile])
AC_CONFIG_FILES([src/capd/poincare/Makefile])

PKG_CHECK_EXISTS([mpcapdAlg], [HAVE_MPCAPDALG=yes])
AM_CONDITIONAL([HAVE_MPCAPDALG],[test "x$HAVE_MPCAPDALG" = "xyes"])

AS_IF([test "x$HAVE_MPCAPDALG" = "xyes"],
   [PKG_CHECK_MODULES([mpcapdAlg], [mpcapdAlg >= 1.0])
   AC_SUBST(mpcapdDynSys_CFLAGS)
   AC_SUBST(mpcapdDynSys_LIBS)
    AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapdDynSys.pc:src/mpcapd/mpcapdDynSys-dev.pc.in])
    AC_CONFIG_FILES([src/mpcapd/mpcapdDynSys.pc:src/mpcapd/mpcapdDynSys-install.pc.in])
    AC_SUBST(mpcapddiffIncl_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
    AC_SUBST(mpcapddiffIncl_LIBS, ["$mpfr_LIBS"])
    AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapddiffIncl.pc:src/mpcapd/diffIncl/mpcapddiffIncl-dev.pc.in])
    AC_CONFIG_FILES([src/mpcapd/diffIncl/mpcapddiffIncl.pc:src/mpcapd/diffIncl/mpcapddiffIncl-install.pc.in])
    AC_SUBST(mpcapddynsysm_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
    AC_SUBST(mpcapddynsysm_LIBS, ["$mpfr_LIBS"])
    AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapddynsysm.pc:src/mpcapd/dynsys/mpcapddynsysm-dev.pc.in])
    AC_CONFIG_FILES([src/mpcapd/dynsys/mpcapddynsysm.pc:src/mpcapd/dynsys/mpcapddynsysm-install.pc.in])
    AC_SUBST(mpcapdgeomset_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
    AC_SUBST(mpcapdgeomset_LIBS, ["$mpfr_LIBS"])
    AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapdgeomset.pc:src/mpcapd/geomset/mpcapdgeomset-dev.pc.in])
    AC_CONFIG_FILES([src/mpcapd/geomset/mpcapdgeomset.pc:src/mpcapd/geomset/mpcapdgeomset-install.pc.in])
    AC_SUBST(mpcapdmap_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
    AC_SUBST(mpcapdmap_LIBS, ["$mpfr_LIBS"])
    AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapdmap.pc:src/mpcapd/map/mpcapdmap-dev.pc.in])
    AC_CONFIG_FILES([src/mpcapd/map/mpcapdmap.pc:src/mpcapd/map/mpcapdmap-install.pc.in])
    AC_SUBST(mpcapddiffAlgebra_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
    AC_SUBST(mpcapddiffAlgebra_LIBS, ["$mpfr_LIBS"])
    AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapddiffAlgebra.pc:src/mpcapd/diffAlgebra/mpcapddiffAlgebra-dev.pc.in])
    AC_CONFIG_FILES([src/mpcapd/diffAlgebra/mpcapddiffAlgebra.pc:src/mpcapd/diffAlgebra/mpcapddiffAlgebra-install.pc.in])
    AC_SUBST(mpcapddynset_CFLAGS, ["$mpfr_CFLAGS -frounding-math"])
    AC_SUBST(mpcapddynset_LIBS, ["$mpfr_LIBS"])
    AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapddynset.pc:src/mpcapd/dynset/mpcapddynset-dev.pc.in])
    AC_CONFIG_FILES([src/mpcapd/dynset/mpcapddynset.pc:src/mpcapd/dynset/mpcapddynset-install.pc.in])
    AC_CONFIG_FILES([src/mpcapd/Makefile])
    AC_CONFIG_FILES([src/mpcapd/diffAlgebra/Makefile])
    AC_CONFIG_FILES([src/mpcapd/diffIncl/Makefile])
    AC_CONFIG_FILES([src/mpcapd/dynset/Makefile])
    AC_CONFIG_FILES([src/mpcapd/dynsys/Makefile])
    AC_CONFIG_FILES([src/mpcapd/geomset/Makefile])
    AC_CONFIG_FILES([src/mpcapd/map/Makefile])],
   [rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapdDynSys.pc
    rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapddiffIncl.pc
    rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapddynsysm.pc
    rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapdgeomset.pc
    rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapdmap.pc
    rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapddiffAlgebra.pc
    rm -f ${top_capd_build}/lib/pkgconfig-dev/mpcapddynset.pc])


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
PKG_CHECK_MODULES([capdAlg], [capdAlg >= 1.0])
PKG_CHECK_MODULES([capdExt], [capdExt >= 1.0])


AC_OUTPUT
