#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.


#AC_PREREQ(2.61)
AC_INIT(capdAux, 1.0, BUG-REPORT-ADDRESS)

AC_CONFIG_AUX_DIR(../capdMake)
default_top_capd=${srcdir}/..
top_capd_build=./..
m4_include([../capdMake/make/configure_common.ac])
m4_include([../capdMake/make/configure_common_x.ac])

AC_CANONICAL_HOST
echo HOST INFORMATION : $host
echo "$host_alias X $host_cpu X $host_vendor X  $host_os"

CAPD_MODULES="capdauxil "

AC_SUBST(capdauxil_CFLAGS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdauxil.pc:src/capd/auxil/capdauxil-dev.pc.in])
AC_CONFIG_FILES([src/capd/auxil/capdauxil.pc:src/capd/auxil/capdauxil-install.pc.in])

rm -f ${top_capd_build}/lib/pkgconfig-dev/capdkrak.pc


capdkrak_CFLAGS=""
capdkrak_LIBS=""
capdkrak_REQUIRES=""

AS_IF([test "$HAVE_GUI" = yes ],
   [
#capdkrak isn't default, returned only by capd-config-gui or manual
#   CAPD_MODULES="$CAPD_MODULES capdkrak" 
  
    capdkrak_CFLAGS=${GUI_FLAGS}
    capdkrak_LIBS=${GUI_LIBS}
    capdkrak_REQUIRES=${GUI_REQUIRES}

    AC_SUBST(capdkrak_CFLAGS)
    AC_SUBST(capdkrak_LIBS)
    AC_SUBST(capdkrak_REQUIRES)
	
    AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdkrak.pc:src/capd/krak/capdkrak-dev.pc.in])
    AC_CONFIG_FILES([src/capd/krak/capdkrak.pc:src/capd/krak/capdkrak-install.pc.in])
    AC_CONFIG_FILES([src/capd/krak/Makefile])
   ]
)

AC_SUBST([CAPD_MODULES])

AC_SUBST(capdAux_CFLAGS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdAux.pc:src/capd/capdAux-dev.pc.in])
AC_CONFIG_FILES([src/capd/capdAux.pc:src/capd/capdAux-install.pc.in])

AC_CONFIG_HEADER([include/capd/config-capdAux.h])


AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([include/Makefile])
AC_CONFIG_FILES([src/Makefile])
AC_CONFIG_FILES([src/capd/Makefile])
AC_CONFIG_FILES([src/capd/auxil/Makefile])

AC_CONFIG_SUBDIRS([examples])
AC_CONFIG_SUBDIRS([tests])

# Checks for programs.
AC_PROG_CXX

# Checks for libraries.
AC_PROG_RANLIB

# Checks for header files.

# Checks for typedefs, structures, and compiler characteristics.
#AC_HEADER_STDBOOL

# Checks for library functions.


AC_OUTPUT
