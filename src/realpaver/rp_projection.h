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
 * rp_projection.h                                                          *
 ****************************************************************************/

#ifndef RP_PROJECTION_H
#define RP_PROJECTION_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include "rp_union_interval.h"

/* --------------------------- */
/* Binary projection functions */
/* --------------------------- */

/* x = y + z <=> y = x - z <=> z = x - y */
int rp_project_add_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_add_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_add_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z);

/* x = y - z <=> y = x + z <=> z = y - x */
int rp_project_sub_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_sub_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_sub_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z);

/* x = y * z <=> y = x / z <=> z = x / y */
int rp_project_mul_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_mul_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_mul_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z);

/* x = y / z <=> y = x * z <=> z = y / x */
int rp_project_div_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_div_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_div_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z);

/* x = min(y,z) / z <=> y = min-1(x,z) <=> z = min-1(x,y) */
int rp_project_min_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_min_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_min_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z);

/* x = max(y,z) / z <=> y = max-1(x,z) <=> z = max-1(x,y) */
int rp_project_max_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_max_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z);
int rp_project_max_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z);

/* -------------------------- */
/* Unary projection functions */
/* -------------------------- */

/* x = pow(y,n) <=> y = pow-1(x,n) */
int rp_project_pow_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval n);
int rp_project_pow_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval n);

/* x = -y <=> y = -x */
int rp_project_neg_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_neg_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = y^2 <=> y = pow-1(x,2) */
int rp_project_sqr_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_sqr_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = sqrt(y) <=> y = sqrt-1(x) */
int rp_project_sqrt_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_sqrt_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = exp(y) <=> y = exp-1(x) */
int rp_project_exp_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_exp_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = log(y) <=> y = log-1(x) */
int rp_project_log_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_log_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = sin(y) <=> y = sin-1(x) */
int rp_project_sin_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_sin_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = cos(y) <=> y = cos-1(x) */
int rp_project_cos_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_cos_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = tan(y) <=> y = tan-1(x) */
int rp_project_tan_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_tan_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = cosh(y) <=> y = cosh-1(x) */
int rp_project_cosh_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_cosh_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = sinh(y) <=> y = sinh-1(x) */
int rp_project_sinh_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_sinh_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = tanh(y) <=> y = tanh-1(x) */
int rp_project_tanh_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_tanh_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = acos(y) <=> y = acos-1(x) */
int rp_project_acos_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_acos_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = asin(y) <=> y = asin-1(x) */
int rp_project_asin_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_asin_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = atan(y) <=> y = atan-1(x) */
int rp_project_atan_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_atan_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = acosh(y) <=> y = acosh-1(x) */
int rp_project_acosh_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_acosh_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = asinh(y) <=> y = asinh-1(x) */
int rp_project_asinh_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_asinh_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = atanh(y) <=> y = atanh-1(x) */
int rp_project_atanh_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_atanh_fst (rp_interval ynew, rp_interval x, rp_interval y);

/* x = abs(y) <=> y = abs-1(x) */
int rp_project_abs_zro (rp_interval xnew, rp_interval x, rp_interval y);
int rp_project_abs_fst (rp_interval ynew, rp_interval x, rp_interval y);

#ifdef __cplusplus
}
#endif

#endif /* RP_PROJECTION_H */
