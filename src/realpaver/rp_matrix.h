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
 * rp_matrix.h                                                              *
 ****************************************************************************/

#ifndef RP_MATRIX_H
#define RP_MATRIX_H 1

#ifdef __cplusplus
extern "C" {
#endif

#include "rp_interval.h"

/* ------------------------ */
/* the interval vector type */
/* ------------------------ */
typedef struct
{
  int size;
  rp_interval * ptr;
}
rp_interval_vector_def;

typedef rp_interval_vector_def * rp_interval_vector;

#define rp_ivector_size(v)    (v)->size
#define rp_ivector_ptr(v)     (v)->ptr
#define rp_ivector_elem(v,i)  (v)->ptr[i]

/* Creation */
void rp_interval_vector_create(rp_interval_vector * v, int n);

/* Destruction */
void rp_interval_vector_destroy(rp_interval_vector * v);

/* every v[k] := i */
void rp_interval_vector_set(rp_interval_vector v, rp_interval i);

/* v := src */
void rp_interval_vector_copy(rp_interval_vector v, rp_interval_vector src);

/* Display v on out */
void rp_interval_vector_display(FILE * out, rp_interval_vector v, int digits);

#define rp_interval_vector_display_simple(v) \
  rp_interval_vector_display(stdout,v,8)

#define rp_interval_vector_display_simple_nl(v) \
  rp_interval_vector_display(stdout,v,8);       \
    printf("\n")

/* -------------------- */
/* the real matrix type */
/* -------------------- */
typedef struct
{
  int nrow;
  int ncol;
  int size;
  double * ptr;
  int * pvars;
}
rp_real_matrix_def;

typedef rp_real_matrix_def * rp_real_matrix;

#define rp_rmatrix_nrow(m)      (m)->nrow
#define rp_rmatrix_ncol(m)      (m)->ncol
#define rp_rmatrix_size(m)      (m)->size
#define rp_rmatrix_ptr(m)       (m)->ptr
#define rp_rmatrix_elem(m,i,j)  (m)->ptr[i*(rp_rmatrix_ncol(m))+j]
#define rp_rmatrix_pvars(m)     (m)->pvars
#define rp_rmatrix_var(i)       (m)->pvars[i]

/* Creation */
void rp_real_matrix_create(rp_real_matrix * m, int nr, int nc);

/* Destruction */
void rp_real_matrix_destroy(rp_real_matrix * m);

/* every m[i,j] := src */
void rp_real_matrix_set(rp_real_matrix m, double src);

/* m := identity matrix */
void rp_real_matrix_setid(rp_real_matrix m);

/* m := src */
void rp_real_matrix_copy(rp_real_matrix m, rp_real_matrix src);

/* inv := src-1, id is the identity matrix */
/* Returns 1 if the matrix can be inverted */
int rp_real_matrix_inverse(rp_real_matrix inv,
			   rp_real_matrix src,
			   rp_real_matrix id);

/* r := m1 - m2 */
void rp_real_matrix_sub(rp_real_matrix r,
			rp_real_matrix m1,
			rp_real_matrix m2);

/* r := |m| */
void rp_real_matrix_abs(rp_real_matrix r,
			rp_real_matrix m);

/* Returns 1 if m>=0 */
int rp_real_matrix_positive(rp_real_matrix m);

/* r_ij := m1_ik * m2_kj */
void rp_matrix_mul_rm_rm(rp_real_matrix r,
			 rp_real_matrix m1,
			 rp_real_matrix m2);

/* Display m on out */
void rp_real_matrix_display(FILE * out, rp_real_matrix m, int digits);

#define rp_real_matrix_display_simple(m) \
   rp_real_matrix_display(stdout,m,8)

#define rp_real_matrix_display_simple_nl(m) \
   rp_real_matrix_display(stdout,m,8);      \
    printf("\n")

/* ------------------------ */
/* the interval matrix type */
/* ------------------------ */
typedef struct
{
  int nrow;
  int ncol;
  int size;
  rp_interval * ptr;
  int * pvars;
}
rp_interval_matrix_def;

typedef rp_interval_matrix_def * rp_interval_matrix;

#define rp_imatrix_nrow(m)      (m)->nrow
#define rp_imatrix_ncol(m)      (m)->ncol
#define rp_imatrix_size(m)      (m)->size
#define rp_imatrix_ptr(m)       (m)->ptr
#define rp_imatrix_elem(m,i,j)  (m)->ptr[i*(rp_imatrix_ncol(m))+j]
#define rp_imatrix_pvars(m)     (m)->pvars
#define rp_imatrix_var(i)       (m)->pvars[i]

/* Creation */
void rp_interval_matrix_create(rp_interval_matrix * m, int nr, int nc);

/* Destruction */
void rp_interval_matrix_destroy(rp_interval_matrix * m);

/* every m[i,j] := src */
void rp_interval_matrix_set(rp_interval_matrix m, rp_interval src);

/* m := src */
void rp_interval_matrix_copy(rp_interval_matrix m, rp_interval_matrix src);

/* Returns 1 if m is regular <=> every real matrix included in m */
/* is non singular */
int rp_interval_matrix_regular(rp_interval_matrix m);

/* Display m on out */
void rp_interval_matrix_display(FILE * out, rp_interval_matrix m, int digits);

#define rp_interval_matrix_display_simple(m) \
   rp_interval_matrix_display(stdout,m,8)

#define rp_interval_matrix_display_simple_nl(m) \
   rp_interval_matrix_display(stdout,m,8);      \
    printf("\n")

/* ---------------- */
/* other operations */
/* ---------------- */

/* r := m*v, dimension of v equal to the number of columns of m */
void rp_matrix_mul_rm_iv(rp_interval_vector r,
			 rp_real_matrix m,
			 rp_interval_vector v);

/* r_ij := m1_ik * m2_kj */
void rp_matrix_mul_rm_im(rp_interval_matrix r,
			 rp_real_matrix m1,
			 rp_interval_matrix m2);

/* Computes center and delta st. src = [center-delta,center+delta] */
void rp_matrix_center_delta(rp_real_matrix center,
			    rp_real_matrix delta,
			    rp_interval_matrix src);

#ifdef __cplusplus
}
#endif

#endif /* RP_MATRIX_H */
