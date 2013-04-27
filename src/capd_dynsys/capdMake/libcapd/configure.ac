#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

#AC_PREREQ(2.61)
AC_INIT(capd, 1.0, BUG-REPORT-ADDRESS)

AC_CONFIG_AUX_DIR(../../capdMake)
default_top_capd=${srcdir}/../..
top_capd_build=./../..
m4_include([../../capdMake/make/configure_common.ac])

AC_SUBST([top_capd_build])
AC_CONFIG_FILES([Makefile])

CAPD_PACKAGES=""
MPCAPD_PACKAGES=""

PKG_CHECK_EXISTS([capdDynSys], [CAPD_PACKAGES="${CAPD_PACKAGES} capdDynSys"], [])
PKG_CHECK_EXISTS([capdRedHom], [CAPD_PACKAGES="${CAPD_PACKAGES} capdRedHom"], [])
PKG_CHECK_EXISTS([capdAlg], [CAPD_PACKAGES="${CAPD_PACKAGES} capdAlg"], [])
PKG_CHECK_EXISTS([capdAux], [CAPD_PACKAGES="${CAPD_PACKAGES} capdAux"], [])
PKG_CHECK_EXISTS([capdExt], [CAPD_PACKAGES="${CAPD_PACKAGES} capdExt"], [])


AS_IF([test "x${CAPD_PACKAGES}" != "x"],
            [AC_SUBST([CAPD_PACKAGES])
            AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capd.pc:capd.pc.in])
            AC_CONFIG_FILES([capd.pc:capd.pc.in])
            PKG_CHECK_MODULES([capd], [${CAPD_PACKAGES}])
            AC_CONFIG_FILES(capd-config)
            AC_CONFIG_FILES(${top_capd_build}/bin/capd-config:capd-config-dev.in)])

AM_CONDITIONAL(HAVE_CAPD, [test "x${CAPD_PACKAGES}" != "x"])

PKG_CHECK_EXISTS([capdkrak], [CAPD_PACKAGES_GUI="capdkrak"], [])

AS_IF([test "x${CAPD_PACKAGES_GUI}" != "x"],
            [AC_SUBST([CAPD_PACKAGES_GUI])
            AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capd-gui.pc:capd-gui.pc.in])
            AC_CONFIG_FILES([capd-gui.pc:capd-gui.pc.in])
            PKG_CHECK_MODULES([capd_gui], [${CAPD_PACKAGES_GUI} ${CAPD_PACKAGES}])
            AC_CONFIG_FILES(capd-gui-config)
            AC_CONFIG_FILES(${top_capd_build}/bin/capd-gui-config:capd-gui-config-dev.in)
            ])

AM_CONDITIONAL(HAVE_CAPD_GUI, [test "x${CAPD_PACKAGES_GUI}" != "x"])

PKG_CHECK_EXISTS([mpcapdDynSys], [MPCAPD_PACKAGES="${MPCAPD_PACKAGES} mpcapdDynSys"], [])
PKG_CHECK_EXISTS([mpcapdAlg], [MPCAPD_PACKAGES="${MPCAPD_PACKAGES} mpcapdAlg"], [])

AS_IF([test "x${MPCAPD_PACKAGES}" != "x"],
            [AC_SUBST([MPCAPD_PACKAGES])
            AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapd.pc:mpcapd.pc.in])
            AC_CONFIG_FILES([mpcapd.pc:mpcapd.pc.in])
            PKG_CHECK_MODULES([mpcapd], [${MPCAPD_PACKAGES}])
            AC_CONFIG_FILES(mpcapd-config)
            AC_CONFIG_FILES(${top_capd_build}/bin/mpcapd-config:mpcapd-config-dev.in)
            ])

AM_CONDITIONAL([HAVE_MPCAPD], [test "x${MPCAPD_PACKAGES}" != "x"])

AS_IF([test "x${MPCAPD_PACKAGES}" != "x" && test "x${CAPD_PACKAGES_GUI}" != "x"],
            [AC_SUBST([MPCAPD_PACKAGES])
            AC_SUBST([CAPD_PACKAGES_GUI])
            AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/mpcapd-gui.pc:mpcapd-gui.pc.in])
            AC_CONFIG_FILES([mpcapd-gui.pc:mpcapd-gui.pc.in])
            PKG_CHECK_MODULES([mpcapd_gui], [${CAPD_PACKAGES_GUI} ${MPCAPD_PACKAGES}])
            AC_CONFIG_FILES(mpcapd-gui-config)
            AC_CONFIG_FILES(${top_capd_build}/bin/mpcapd-gui-config:mpcapd-gui-config-dev.in)
            ])

AM_CONDITIONAL([HAVE_MPCAPD_GUI], [test "x${MPCAPD_PACKAGES}" != "x" && test "x${CAPD_PACKAGES_GUI}" != "x"])


# Checks for libraries.
AC_PROG_RANLIB
# LT_INIT

AC_OUTPUT
