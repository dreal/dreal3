#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

#AC_PREREQ(2.61)
AC_INIT(capdExt, 1.0, BUG-REPORT-ADDRESS)


AC_CONFIG_AUX_DIR(../capdMake)
default_top_capd=${srcdir}/..
top_capd_build=./..
m4_include([../capdMake/make/configure_common.ac])


AC_ARG_WITH([filib],
    AS_HELP_STRING([--with-filib], [path to filib installation or internal to use filib version provided with CAPD. As a default we do not use filib.]),
    [],
    [with_filib=no])

AS_IF([test "x$with_filib" = xcheck],
      [AC_CHECK_FILE([${srcdir}/../capdDynSys],[with_filib=internal],[with_filib=no])])
      
AS_IF([test "x$with_filib" = xyes],
       with_filib=internal)
       
AS_IF([test "x$with_filib" = xinternal],
      [AC_MSG_NOTICE([using internal filib])
      AC_SUBST(filib_CFLAGS, ["-D__USE_FILIB__ -I${PWD}/${srcdir}/filibsrc -I${PWD}/filibsrc -frounding-math -ffloat-store"])
      AC_SUBST(filib_LIBS, ["-L${PWD}/filibsrc/libprim/.libs -lprim"])
      AC_SUBST(filib_CFLAGS_INSTALL, ["-D__USE_FILIB__ -I\${prefix}/include -frounding-math"])
      AC_SUBST(filib_LIBS_INSTALL, ["-L\${prefix}/lib -lprim"])])


AS_IF([test "x$with_filib" != xno && test "x$with_filib" != xinternal],
      [AC_MSG_NOTICE([using external filib])
      AC_SUBST(filib_CFLAGS, ["-D__USE_FILIB__ -I$with_filib/include -frounding-math -ffloat-store"])
      AC_SUBST(filib_LIBS, ["-L$with_filib/lib -lprim"])
      AC_SUBST(filib_CFLAGS_INSTALL, ["-D__USE_FILIB__ -I$with_filib/include -frounding-math"])
      AC_SUBST(filib_LIBS_INSTALL, ["-L$with_filib/lib -lprim"])])

AS_IF([test "x$with_filib" = xno],
      [AC_MSG_NOTICE([using CAPD intervals])
      AC_SUBST(filib_CFLAGS, [""])
      AC_SUBST(filib_LIBS, [""])
      AC_SUBST(filib_CFLAGS_INSTALL, [""])
      AC_SUBST(filib_LIBS_INSTALL, [""])])

AM_CONDITIONAL([WITH_FILIB_INTERNAL], [test "x$with_filib" = xinternal])

AC_SUBST(capdalglib_CFLAGS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdalglib.pc:src/capd/alglib/capdalglib-dev.pc.in])
AC_CONFIG_FILES([src/capd/alglib/capdalglib.pc:src/capd/alglib/capdalglib-install.pc.in])

AC_SUBST(capdExt_CFLAGS)
AC_CONFIG_FILES([${top_capd_build}/lib/pkgconfig-dev/capdExt.pc:src/capd/capdExt-dev.pc.in])
AC_CONFIG_FILES([src/capd/capdExt.pc:src/capd/capdExt-install.pc.in])

AC_CONFIG_HEADER([include/capd/config-capdExt.h])
	

AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([include/Makefile])
AC_CONFIG_FILES([src/Makefile])
AC_CONFIG_FILES([src/capd/Makefile])
AC_CONFIG_FILES([src/capd/alglib/Makefile])

#AS_IF([test "x$with_boost" = xinternal],
#      [AC_CONFIG_FILES([boost/Makefile])
#     AC_CONFIG_FILES([boost/include/Makefile])
#      AC_CONFIG_FILES([boost/src/Makefile])])


AS_IF([test "x$with_filib" = xinternal],
      [AC_CONFIG_SUBDIRS([filibsrc])])

AC_CONFIG_SUBDIRS([examples])
AC_CONFIG_SUBDIRS([programs])


#PKG_CHECK_MODULES([CAPD_PACKAGES], [capdAux >= 1.0])

# Checks for programs.
AC_PROG_CXX

# Checks for libraries.
AC_PROG_RANLIB

# Checks for header files.

# Checks for typedefs, structures, and compiler characteristics.
#AC_HEADER_STDBOOL

# Checks for library functions.


AC_OUTPUT
