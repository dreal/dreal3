#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.


#AC_PREREQ(2.61)
AC_INIT(capd, 1.0, BUG-REPORT-ADDRESS)

AC_CONFIG_AUX_DIR(capdMake)
default_top_capd=${srcdir}
top_capd_build=.
m4_include([capdMake/make/configure_common.ac])

AC_CONFIG_FILES([Makefile])

CAPD_PACKAGES=""

AC_CHECK_FILE([${srcdir}/capdExt],
[
  AC_CONFIG_SUBDIRS([capdExt])
  CAPD_PACKAGES="$CAPD_PACKAGES  capdExt "  
], [])

AC_CHECK_FILE([${srcdir}/capdExtDS],
[
  AC_CONFIG_SUBDIRS([capdExtDS])
  CAPD_PACKAGES="$CAPD_PACKAGES  capdExtDS "  
], [])

AC_CHECK_FILE([${srcdir}/capdExtHom],
[
  AC_CONFIG_SUBDIRS([capdExtHom])
  CAPD_PACKAGES="$CAPD_PACKAGES  capdExtHom "  
], [])

AC_CHECK_FILE([${srcdir}/capdAux],
[
  AC_CONFIG_SUBDIRS([capdAux])
  CAPD_PACKAGES="$CAPD_PACKAGES  capdAux "  
], [])

AC_CHECK_FILE([${srcdir}/capdAlg],
[
  AC_CONFIG_SUBDIRS([capdAlg])
  CAPD_PACKAGES="$CAPD_PACKAGES  capdAlg "  
], [])

AC_CHECK_FILE([${srcdir}/capdDynSys],
[
  AC_CONFIG_SUBDIRS([capdDynSys])
  CAPD_PACKAGES="$CAPD_PACKAGES  capdDynSys"  
], 
[
  AC_CHECK_FILE([${srcdir}/capdDynSys4],
  [
    AC_CONFIG_SUBDIRS([capdDynSys4])
    CAPD_PACKAGES="$CAPD_PACKAGES  capdDynSys4"  
  ], [])
])

AC_CHECK_FILE([${srcdir}/capdRedHom],
[
  AC_CONFIG_SUBDIRS([capdRedHom])
  CAPD_PACKAGES="$CAPD_PACKAGES  capdRedHom "  
], [])

AC_CONFIG_SUBDIRS([capdMake/libcapd])

AC_SUBST([CAPD_PACKAGES])


AC_OUTPUT
