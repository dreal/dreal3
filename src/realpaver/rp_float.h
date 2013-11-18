/****************************************************************************
 * RealPaver v. 1.0                                                         *
 *--------------------------------------------------------------------------*
 * Author: Laurent Granvilliers                                             *
 * Copyright (c) 1999-2003 Institut de Recherche en Informatique de Nantes  *
 * Copyright (c) 2004-2006 Laboratoire d'Informatique de Nantes Atlantique  *
 *--------------------------------------------------------------------------*
 * RealPaver is distributed WITHOUT ANY WARRANTY. Read the associated       *
 * COPYRIGHT file for more details.                                         *
 *--------------------------------------------------------------------------*
 * rp_float.h                                                               *
 ****************************************************************************/

#ifndef RP_FLOAT_H
#define RP_FLOAT_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <math.h>
#include "rp_config.h"
#include "rp_memory.h"

// extern double log       (double) rp_throw;
// extern double log2      (double) rp_throw;
// extern double exp       (double) rp_throw;
// extern double sqrt      (double) rp_throw;
// extern double cos       (double) rp_throw;
// extern double sin       (double) rp_throw;
// extern double tan       (double) rp_throw;
// extern double cosh      (double) rp_throw;
// extern double sinh      (double) rp_throw;
// extern double tanh      (double) rp_throw;
// extern double acos      (double) rp_throw;
// extern double asin      (double) rp_throw;
// extern double atan      (double) rp_throw;
// extern double acosh     (double) rp_throw;
// extern double asinh     (double) rp_throw;
// extern double atanh     (double) rp_throw;
// extern double ceil      (double) rp_throw;
// extern double floor     (double) rp_throw;
// extern double fabs      (double) rp_throw;
// extern double nextafter (double, double) rp_throw;
// extern double pow       (double, double) rp_throw;

// extern double atan2     (double, double) rp_throw;
// extern double matan     (double) rp_throw;
// extern double safesqrt  (double) rp_throw;


/* -------------------------------------------------------- */
/* Support of IEEE rounding modes and floating-point values */
/* -------------------------------------------------------- */

#if RP_SYSTEM_SPARC
/* Sparc stations and Solaris */
# include <limits.h>
# include <floatingpoint.h>
# include <sys/ieeefp.h>
# define RP_ROUND_DOWNWARD()  fpsetround(3)
# define RP_ROUND_UPWARD()    fpsetround(2)
# define RP_ROUND_NEAREST()   fpsetround(0)
# define RP_MAX_DOUBLE        DBL_MAX
# define RP_MAX_LONG          LONG_MAX
static const double RP_INFINITY = 1.0/0.0;

#elif RP_SYSTEM_LINUX_IX86
/* PC i386 and Linux */
# include <fenv.h>
# include <values.h>
# define RP_ROUND_DOWNWARD()  fesetround(FE_DOWNWARD)
# define RP_ROUND_UPWARD()    fesetround(FE_UPWARD)
# define RP_ROUND_NEAREST()   fesetround(FE_TONEAREST)
# define RP_MAX_DOUBLE        DBL_MAX
# define RP_MAX_LONG          LONG_MAX
# define RP_INFINITY          HUGE_VAL

#elif RP_SYSTEM_POWERPC
/* POWER PC and MAC OS X */
# include <limits.h>
# include <fenv.h>
# include <float.h>
# define RP_ROUND_DOWNWARD()  fesetround(FE_DOWNWARD)
# define RP_ROUND_UPWARD()    fesetround(FE_UPWARD)
# define RP_ROUND_NEAREST()   fesetround(FE_TONEAREST)
# define RP_MAX_DOUBLE        DBL_MAX
# define RP_MAX_LONG          LONG_MAX
static const double RP_INFINITY = 1.0/0.0;

#elif RP_SYSTEM_SGI
/* MIPS SGI */
# include <limits.h>
# include <float.h>
# include <ieeefp.h>
# define RP_ROUND_DOWNWARD()  fpsetround(3)
# define RP_ROUND_UPWARD()    fpsetround(2)
# define RP_ROUND_NEAREST()   fpsetround(0)
# define RP_MAX_DOUBLE        DBL_MAX
# define RP_MAX_LONG          LONG_MAX
static const double RP_INFINITY = 1.0/0.0;
#endif

/* ------------------------------------- */
/* Specific values and elementary macros */
/* ------------------------------------- */

#define RP_MIN_DOUBLE     (-RP_MAX_DOUBLE)
#define RP_MIN_LONG       (-RP_MAX_LONG - 1L)

/* Values used in algorithms to define the rounding mode */
#define RP_ROUND_VALUE_UP    1
#define RP_ROUND_VALUE_DOWN  2

#define rp_odd(n)         (((n)%2)==1)
#define rp_even(n)        (((n)%2)==0)
#define rp_min_num(x,y)   (((x)<(y))? x : y)
#define rp_max_num(x,y)   (((x)<(y))? y : x)
#define rp_abs(x)         (((x)<=0.0) ? -(x) : (x))

#define rp_next_double(x) nextafter(x,RP_INFINITY)
#define rp_prev_double(x) nextafter(x,(-RP_INFINITY))

/* ----------------------------------------- */
/* Functions for floating-point computations */
/* ----------------------------------------- */

/* Returns x to the power of n with n>=1 */
double rp_pow (double x, int n, int round);

/* Returns p := x+(n/h)(y-x) in (x,y) if [x,y] is not empty and not canonical */
double rp_split_point (double x, double y, int h, int n);

#define rp_split_center(x,y) rp_split_point(x,y,2,1)

#ifdef __cplusplus
}
#endif

#endif  /* RP_FLOAT_H */
