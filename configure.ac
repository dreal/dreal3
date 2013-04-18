#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.68])
AC_INIT([dReal], [2.0.0], [scungao@gmail.com])
#AC_CONFIG_SRCDIR([src/opensmt/api/opensmt_c.C])
AC_CONFIG_SUBDIRS([src/capd_dynsys])
#AC_CONFIG_AUX_DIR(autotools)

#AC_CONFIG_HEADERS([config.h])

# Checks for programs.
AC_PROG_CXX
AC_PROG_AWK
AC_PROG_CC
AC_PROG_CPP
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
LT_INIT

# Added by Soonho Kong
AC_PROG_YACC
AM_PROG_LEX
AC_PROG_LIBTOOL
AM_INIT_AUTOMAKE

# Checks for libraries.
# FIXME: Replace `main' with a function in `-lgmp':
#AC_CHECK_LIB([gmp], [main])
# FIXME: Replace `main' with a function in `-lgmpxx':
#AC_CHECK_LIB([gmpxx], [main])
# FIXME: Replace `main' with a function in `-lz':
#AC_CHECK_LIB([z], [main])

# Checks for header files.
AC_CHECK_HEADERS([fenv.h float.h limits.h memory.h stdint.h stdlib.h string.h sys/time.h unistd.h values.h])

# Checks for typedefs, structures, and compiler characteristics.
#AC_CHECK_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_INT32_T
AC_TYPE_INT64_T
AC_TYPE_PID_T
AC_TYPE_SIZE_T
AC_TYPE_UINT32_T
AC_TYPE_UINT64_T

# Checks for library functions.
AC_FUNC_ERROR_AT_LINE
AC_FUNC_FORK
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_CHECK_FUNCS([floor getpagesize pow sqrt strdup strrchr strtol strtoul])

# Use C++0x
# Checks for typedefs, structures, and compiler characteristics.
AC_LANG([C++])
AC_LANG_CPLUSPLUS
BOOST_REQUIRE
AC_CHECK_HEADER(cstdint)
AX_CXX_COMPILE_STDCXX_0X
BOOST_THREADS

CXXFLAGS='-Wall -std=gnu++0x'

# Added by Soonho Kong
#
# List of directories to include
#
config_includedirs="-I\${top_srcdir}/src/opensmt \\\
-I\${top_srcdir}/src \\\
-I\${top_srcdir}/src/opensmt/minisat/mtl \\\
-I\${top_srcdir}/src/opensmt/minisat/core \\\
-I\${top_srcdir}/src/opensmt/smtsolvers \\\
-I\${top_srcdir}/src/opensmt/simplifiers \\\
-I\${top_srcdir}/src/opensmt/common \\\
-I\${top_srcdir}/src/opensmt/egraph \\\
-I\${top_srcdir}/src/opensmt/sorts \\\
-I\${top_srcdir}/src/opensmt/cnfizers \\\
-I\${top_srcdir}/src/opensmt/proof \\\
-I\${top_srcdir}/src/opensmt/api \\\
-I\${top_srcdir}/src/opensmt/tsolvers \\\
-I\${top_srcdir}/src/opensmt/tsolvers/emptysolver \\\
-I\${top_srcdir}/src/opensmt/tsolvers/bvsolver \\\
-I\${top_srcdir}/src/opensmt/tsolvers/bvsolver/minisatp \\\
-I\${top_srcdir}/src/opensmt/tsolvers/lrasolver \\\
-I\${top_srcdir}/src/opensmt/tsolvers/liasolver \\\
-I\${top_srcdir}/src/opensmt/tsolvers/ctsolver \\\
-I\${top_srcdir}/src/opensmt/tsolvers/axsolver \\\
-I\${top_srcdir}/src/opensmt/tsolvers/dlsolver \\\
-I\${top_srcdir}/src/realpaver \\\
-I\${top_srcdir}/src/capd_dynsys/capdExt/include \\\
-I\${top_srcdir}/src/capd_dynsys/capdAlg/include \\\
-I\${top_srcdir}/src/capd_dynsys/capdAux/include \\\
-I\${top_srcdir}/src/capd_dynsys/capdDynSys/include"

AC_SUBST(config_includedirs)

AC_CONFIG_FILES([Makefile
                 src/Makefile
                 src/opensmt/Makefile
                 src/opensmt/api/Makefile
                 src/opensmt/cnfizers/Makefile
                 src/opensmt/common/Makefile
                 src/opensmt/egraph/Makefile
                 src/opensmt/parsers/Makefile
                 src/opensmt/parsers/cnf/Makefile
                 src/opensmt/parsers/smt/Makefile
                 src/opensmt/parsers/smt2/Makefile
                 src/opensmt/parsers/ys/Makefile
                 src/opensmt/proof/Makefile
                 src/opensmt/simplifiers/Makefile
                 src/opensmt/smtsolvers/Makefile
                 src/opensmt/sorts/Makefile
                 src/opensmt/tsolvers/Makefile
                 src/opensmt/tsolvers/emptysolver/Makefile
                 src/realpaver/Makefile])
AC_OUTPUT
