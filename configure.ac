#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.69])
AC_INIT([dReal], [2.0.0], [scungao@gmail.com])
AC_CONFIG_SRCDIR([src/opensmt/api/opensmt_c.C])
AC_CONFIG_AUX_DIR(autotools)

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
AC_CONFIG_MACRO_DIR([m4])

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
AC_CHECK_HEADER_STDBOOL
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

AC_CONFIG_FILES([Makefile
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
                 src/opensmt/tsolvers/axsolver/Makefile
                 src/opensmt/tsolvers/bvsolver/Makefile
                 src/opensmt/tsolvers/bvsolver/minisatp/Makefile
                 src/opensmt/tsolvers/ctsolver/Makefile
                 src/opensmt/tsolvers/dlsolver/Makefile
                 src/opensmt/tsolvers/emptysolver/Makefile
                 src/opensmt/tsolvers/lrasolver/Makefile
                 src/realpaver/Makefile])
AC_OUTPUT
