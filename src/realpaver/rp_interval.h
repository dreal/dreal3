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
 * rp_interval.h                                                            *
 ****************************************************************************/

#ifndef RP_INTERVAL_H
#define RP_INTERVAL_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include "rp_config.h"
#include "rp_memory.h"
#include "rp_float.h"

/* ------------------------------------- */
/* The interval type and interval values */
/* ------------------------------------- */

typedef struct
{
  double inf;
  double sup;
} rp_interval_def;  /* internal type not to be used */

/* An interval is defined as an array of one struct rp_interval_def */
/* then it is a constant pointer                                    */
/*   - static allocation possible                                   */
/*   - copy of a pointer in function calls                          */
/*   - no need to dereference                                       */
typedef rp_interval_def rp_interval[1];

#define rp_binf(i) (i)[0].inf
#define rp_bsup(i) (i)[0].sup

extern rp_interval RP_INTERVAL_PI;
extern rp_interval RP_INTERVAL_2_PI;
extern rp_interval RP_INTERVAL_4_PI;
extern rp_interval RP_INTERVAL_1_PI_2;
extern rp_interval RP_INTERVAL_3_PI_2;
extern rp_interval RP_INTERVAL_5_PI_2;
extern rp_interval RP_INTERVAL_7_PI_2;

/* ----------------------------------------------------- */
/* Macros for elementary operations on the interval type */
/* ----------------------------------------------------- */

/* Tests */
#define rp_interval_empty(i) \
        (!(rp_binf(i)<=rp_bsup(i)))

#define rp_interval_equal(i,j) \
        ((((rp_binf(i))==(rp_binf(j))) && ((rp_bsup(i))==(rp_bsup(j)))) ||	\
	 ((rp_interval_empty(i)) && (rp_interval_empty(j))))

#define rp_interval_diff(i,j) \
        ((((rp_binf(i))!=(rp_binf(j))) || ((rp_bsup(i))!=(rp_bsup(j)))) && \
	 ((!rp_interval_empty(i)) || (!rp_interval_empty(j))))

#define rp_interval_contains(i,x) \
        ((((x)<rp_binf(i)) || ((x)>(rp_bsup(i))) ? 0 : 1))

#define rp_interval_strictly_contains(i,x) \
        (((x)>rp_binf(i)) && ((x)<rp_bsup(i)))

#define rp_interval_point(i) \
        (rp_binf(i)==rp_bsup(i))

#define rp_interval_int(i) \
        ((rp_binf(i)==rp_bsup(i)) && (rp_binf(i)==((int)rp_binf(i))))

#define rp_interval_zero(i) \
        ((rp_binf(i)==0.0) && (rp_bsup(i)==0.0))

#define rp_interval_bound_zero(i) \
        ((rp_binf(i)==0.0) || (rp_bsup(i)==0.0))

#define rp_interval_included(i,j) \
        ((rp_binf(i)>=rp_binf(j)) && (rp_bsup(i)<=rp_bsup(j)))

#define rp_interval_strictly_included(i,j) \
        ((rp_binf(i)>rp_binf(j)) && (rp_bsup(i)<rp_bsup(j)))

#define rp_interval_disjoint(i,j) \
        ((rp_bsup(i)<rp_binf(j)) || (rp_bsup(j)<rp_binf(i)))

#define rp_interval_infinite(i) \
       ((rp_binf(i)==(-RP_INFINITY)) || (rp_bsup(i)==RP_INFINITY))

#define rp_interval_finite(i) \
        ((rp_binf(i)!=(-RP_INFINITY)) && (rp_bsup(i)!=RP_INFINITY))

#define rp_interval_canonical(i) \
        ( ((rp_binf(i)==(-RP_INFINITY)) && (rp_bsup(i)==RP_MIN_DOUBLE)) || \
          ((rp_binf(i)==RP_MAX_DOUBLE)  && (rp_bsup(i)==RP_INFINITY))   || \
          (rp_bsup(i)<=rp_next_double(rp_binf(i))) )

/* Numerical computations */
#define rp_interval_width(i) \
        (rp_bsup(i)-rp_binf(i))

#define rp_interval_distance(i,j) \
        ((rp_bsup(i)<rp_binf(j)) ? \
            (rp_binf(j) - rp_bsup(i)) : \
            (rp_bsup(j)<rp_binf(i)) ? \
               (rp_binf(i) - rp_bsup(j)) : \
	       0.0)

#define rp_interval_midpoint(i) \
        rp_split_center(rp_binf(i),rp_bsup(i))

#define rp_interval_improved(i,old,imp) \
  ((rp_interval_diff(i,old)) && \
   (((rp_binf(old)==(-RP_INFINITY)) && \
     (rp_binf(i)!=(-RP_INFINITY))) || \
    ((rp_bsup(old)==(RP_INFINITY)) && \
     (rp_bsup(i)!=(RP_INFINITY))) || \
    ((rp_interval_finite(old)) && \
     (rp_interval_width(i)<imp*rp_interval_width(old)))))

/* Modifications */
#define rp_interval_set(i,x,y) \
        rp_binf(i) = x; \
        rp_bsup(i) = y

#define rp_interval_set_point(i,x) \
        rp_binf(i) = rp_bsup(i) = x;

#define rp_interval_set_empty(i) \
        rp_binf(i) = RP_INFINITY; \
        rp_bsup(i) = (-RP_INFINITY)

#define rp_interval_set_real_line(i) \
        rp_binf(i) = (-RP_INFINITY); \
        rp_bsup(i) = RP_INFINITY

#define rp_interval_copy(i,j) \
        rp_binf(i) = rp_binf(j); \
        rp_bsup(i) = rp_bsup(j)

/* Returns true if i==j when their bounds are truncated at n digits */
/*   - no truncation if n is negative                               */
int rp_interval_equal_digits (rp_interval i, rp_interval j, int n);

/* --------- */
/* Functions */
/* --------- */

/* Conversion of i to the largest interval with integer bounds included in i */
void rp_interval_trunc (rp_interval i);

/* Conversion of a real number represented by s to an enclosing interval i */
/* The prefix of s must not be a sign                                      */
void rp_interval_from_str (char* s, rp_interval i);

/* Display i on out */
void rp_interval_display (FILE *out, rp_interval i, int digits, int mode);

#define RP_INTERVAL_MODE_BOUND   0
#define RP_INTERVAL_MODE_MID     2
#define RP_INTERVAL_SEPARATOR    " , "

#define rp_interval_display_bounds(o,i,d) \
        rp_interval_display(o,i,d,RP_INTERVAL_MODE_BOUND)

#define rp_interval_display_midpoint(o,i,d) \
        rp_interval_display(o,i,d,RP_INTERVAL_MODE_MID)

#define rp_interval_display_simple(i) \
        rp_interval_display(stdout,i,8,RP_INTERVAL_MODE_BOUND)

#define rp_interval_display_simple_file(o,i) \
        rp_interval_display(o,i,8,RP_INTERVAL_MODE_BOUND)

#define rp_interval_display_simple_nl(i) \
        rp_interval_display_simple(i); \
        printf("\n")

/* Print i in out */
void rp_interval_print (char * out, rp_interval i, int digits, int mode);

/* Initialization and reset of the interval arithmetic module */
void rp_interval_init  ();
void rp_interval_reset ();

/* Returns x-offset in dest=[a,b], offset := step*(b-a), step integer */
double rp_interval_translate (double x, rp_interval dest, int rounding,
			      rp_interval step, rp_interval offset);

/* Binary arithmetic operations */
void rp_interval_add        (rp_interval result, rp_interval i1, rp_interval i2);
void rp_interval_add_r_i    (rp_interval result, rp_interval x,  rp_interval i);
void rp_interval_sub        (rp_interval result, rp_interval i1, rp_interval i2);
void rp_interval_sub_r_i    (rp_interval result, rp_interval x,  rp_interval i);
void rp_interval_sub_i_r    (rp_interval result, rp_interval i,  rp_interval x);
void rp_interval_mul        (rp_interval result, rp_interval i1, rp_interval i2);
void rp_interval_mul_r_i    (rp_interval result, rp_interval x,  rp_interval i);
void rp_interval_mul_rneg_i (rp_interval result, rp_interval x,  rp_interval i);
void rp_interval_mul_rpos_i (rp_interval result, rp_interval x,  rp_interval i);
void rp_interval_div        (rp_interval result, rp_interval i1, rp_interval i2);
void rp_interval_div_i_r    (rp_interval result, rp_interval i,  rp_interval x);
void rp_interval_div_i_rpos (rp_interval result, rp_interval i,  rp_interval x);
void rp_interval_div_i_rneg (rp_interval result, rp_interval i,  rp_interval x);
void rp_interval_div_r_i    (rp_interval result, rp_interval x,  rp_interval i);
void rp_interval_div_rpos_i (rp_interval result, rp_interval x,  rp_interval i);
void rp_interval_div_rneg_i (rp_interval result, rp_interval x,  rp_interval i);
void rp_interval_pow        (rp_interval result, rp_interval i,  rp_interval n);

/* Unary arithmetic operations */
void rp_interval_neg        (rp_interval result, rp_interval i);
void rp_interval_sqr        (rp_interval result, rp_interval i);
void rp_interval_sqrt       (rp_interval result, rp_interval i);

/* Elementary functions */
void rp_interval_exp        (rp_interval result, rp_interval i);
void rp_interval_log        (rp_interval result, rp_interval i);
void rp_interval_sin        (rp_interval result, rp_interval i);
void rp_interval_cos        (rp_interval result, rp_interval i);
void rp_interval_tan        (rp_interval result, rp_interval i);
void rp_interval_cosh       (rp_interval result, rp_interval i);
void rp_interval_sinh       (rp_interval result, rp_interval i);
void rp_interval_tanh       (rp_interval result, rp_interval i);
void rp_interval_asin       (rp_interval result, rp_interval i);
void rp_interval_acos       (rp_interval result, rp_interval i);
void rp_interval_atan       (rp_interval result, rp_interval i);
void rp_interval_asinh      (rp_interval result, rp_interval i);
void rp_interval_acosh      (rp_interval result, rp_interval i);
void rp_interval_atanh      (rp_interval result, rp_interval i);

/* Other functions */

/* result := n-th root of i */
/* computes only the positive part for even exponent and positive interval */
void rp_interval_nthroot    (rp_interval result, rp_interval i, rp_interval n);

/* result := absolute value (i) */
void rp_interval_abs        (rp_interval result, rp_interval i);

/* result := min(i1,i2) */
void rp_interval_min        (rp_interval result, rp_interval i1, rp_interval i2);

/* result := max(i1,i2) */
void rp_interval_max        (rp_interval result, rp_interval i1, rp_interval i2);

/* result := i1 inter i2 */
void rp_interval_inter      (rp_interval result, rp_interval i1, rp_interval i2);

/* result := result inter i */
void rp_interval_set_inter  (rp_interval result, rp_interval i);

/* result := hull(i1,i2) */
void rp_interval_hull       (rp_interval result, rp_interval i1, rp_interval i2);

/* result := hull (i1 \ i2) */
void rp_interval_setminus   (rp_interval result, rp_interval i1, rp_interval i2);

void rp_interval_set_pi     (rp_interval i);
void rp_interval_set_log2   (rp_interval i);
void rp_interval_set_halfpi (rp_interval i);
void rp_interval_set_e      (rp_interval i);

#ifdef __cplusplus
}
#endif

#endif  /* RP_INTERVAL_H */
