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
 * rp_matrix.c                                                              *
 ****************************************************************************/

#include <string.h>
#include "rp_matrix.h"

/* ------------------------ */
/* the interval vector type */
/* ------------------------ */

/* Creation */
void rp_interval_vector_create(rp_interval_vector * v, int n)
{
  rp_malloc(*v,rp_interval_vector_def*,sizeof(rp_interval_vector_def));
  rp_malloc(rp_ivector_ptr(*v),rp_interval*,n*sizeof(rp_interval));
  rp_ivector_size(*v) = n;
}

/* Destruction */
void rp_interval_vector_destroy(rp_interval_vector * v)
{
  rp_free(rp_ivector_ptr(*v));
  rp_free(*v);
}

/* every v[k] := i */
void rp_interval_vector_set(rp_interval_vector v, rp_interval i)
{
  int k;
  for (k=0; k<rp_ivector_size(v); ++k)
  {
    rp_interval_copy(rp_ivector_elem(v,k),i);
  }
}

/* v := src */
void rp_interval_vector_copy(rp_interval_vector v, rp_interval_vector src)
{
  memcpy(rp_ivector_ptr(v),
	 rp_ivector_ptr(src),
	 rp_ivector_size(v)*sizeof(rp_interval));
}

/* Display v on out */
void rp_interval_vector_display(FILE * out, rp_interval_vector v, int digits)
{
  int i;
  fprintf(out,"(");
  for (i=0; i<rp_ivector_size(v); ++i)
  {
    rp_interval_display(out,rp_ivector_elem(v,i),digits,RP_INTERVAL_MODE_BOUND);
    if (i<rp_ivector_size(v)-1)
    {
      fprintf(out,", ");
    }
  }
  fprintf(out,")");
}

/* -------------------- */
/* the real matrix type */
/* -------------------- */
/* Creation */
void rp_real_matrix_create(rp_real_matrix * m, int nr, int nc)
{
  rp_malloc(*m,rp_real_matrix_def*,sizeof(rp_real_matrix_def));
  rp_rmatrix_nrow(*m) = nr;
  rp_rmatrix_ncol(*m) = nc;
  rp_rmatrix_size(*m) = nr*nc;
  rp_malloc(rp_rmatrix_ptr(*m),double*,rp_rmatrix_size(*m)*sizeof(double));
  rp_malloc(rp_rmatrix_pvars(*m),int*,nc*sizeof(int));
}

/* Destruction */
void rp_real_matrix_destroy(rp_real_matrix * m)
{
  rp_free(rp_rmatrix_pvars(*m));
  rp_free(rp_rmatrix_ptr(*m));
  rp_free(*m);
}

/* every m[i,j] := src */
void rp_real_matrix_set(rp_real_matrix m, double src)
{
  int i;
  for (i=0; i<rp_rmatrix_size(m); ++i)
  {
    rp_rmatrix_ptr(m)[i] = src;
  }
}
/* m := identity matrix */
void rp_real_matrix_setid(rp_real_matrix m)
{
  if (rp_rmatrix_nrow(m)==rp_rmatrix_ncol(m))
  {
    int i, j;
    for (i=0; i<rp_rmatrix_nrow(m); ++i)
    {
      for (j=0; j<rp_rmatrix_ncol(m); ++j)
      {
	if (i==j)
	{
	  rp_rmatrix_elem(m,i,j) = 1.0;
	}
	else
	{
	  rp_rmatrix_elem(m,i,j) = 0.0;
	}
      }
    }
  }
}

/* m := src */
void rp_real_matrix_copy(rp_real_matrix m, rp_real_matrix src)
{
  memcpy(rp_rmatrix_ptr(m),
	 rp_rmatrix_ptr(src),
	 rp_rmatrix_size(m)*sizeof(double));
}

/* inv := src-1, id is the identity matrix */
/* Returns 1 if the matrix can be inverted */
int rp_real_matrix_inverse(rp_real_matrix inv,
			   rp_real_matrix src,
			   rp_real_matrix id)
{
  int i, j, k, mpi, xi;
  double mp, x;
  double * dp, * dq;

  /* inv := identity matrix */
  rp_real_matrix_copy(inv,id);

  /* triangularisation of src: for every line i do */
  for (i=0; i<rp_rmatrix_nrow(src); ++i)
  {
    /* search the maximal pivot, to be stored in src(i,i) */
    mp = rp_abs(rp_rmatrix_elem(src,i,i));
    mpi = i;

    /* xi from row i+1 to the last row */
    for (xi=i+1; xi<rp_rmatrix_nrow(src); ++xi)
    {
      x = rp_abs(rp_rmatrix_elem(src,xi,i));
      if (x > mp)
      {
	mp = x;
	mpi = xi;
      }
    }

    if (mp==0.0)
    {
      /* singular matrix */
      return( 0 );
    }

    if (mpi!=i)
    {
      /* inversion of row i and row mpi in src and inv */
      dp = &(rp_rmatrix_elem(src,i,i));
      dq = &(rp_rmatrix_elem(src,mpi,i));
      for (j=i; j<rp_rmatrix_ncol(src); ++j, ++dp, ++dq)
      {
	/*
	x = rp_rmatrix_elem(src,i,j);
        rp_rmatrix_elem(src,i,j) = rp_rmatrix_elem(src,mpi,j);
        rp_rmatrix_elem(src,mpi,j) = x;
	*/
	x = (*dp); (*dp) = (*dq); (*dq) = x;
      }

      dp = &(rp_rmatrix_elem(inv,i,0));
      dq = &(rp_rmatrix_elem(inv,mpi,0));
      for (j=0; j<rp_rmatrix_ncol(src); ++j, ++dp, ++dq)
      {
	/*
	x = rp_rmatrix_elem(inv,i,j);
        rp_rmatrix_elem(inv,i,j) = rp_rmatrix_elem(inv,mpi,j);
        rp_rmatrix_elem(inv,mpi,j) = x;
	*/
	x = (*dp); (*dp) = (*dq); (*dq) = x;
      }
    }

    /* Division by mp (the pivot) of the rows i in src and inv */
    dp = &(rp_rmatrix_elem(src,i,i));
    mp = (*dp); /* rp_rmatrix_elem(src,i,i); */

    for (j=i; j<rp_rmatrix_ncol(src); ++j, ++dp)
    {
      (*dp) /= mp;  /* rp_rmatrix_elem(src,i,j) /= mp */
    }
    dp = &(rp_rmatrix_elem(inv,i,0));
    for (j=0; j<rp_rmatrix_ncol(src); ++j, ++dp)
    {
      (*dp) /= mp; /* rp_rmatrix_elem(inv,i,j) /= mp */
    }

    /* set 0 in column i from row i+1 to the last one */
    for (j=i+1; j<rp_rmatrix_nrow(src); ++j)
    {
      dp = &(rp_rmatrix_elem(src,j,i));
      dq = &(rp_rmatrix_elem(src,i,i));
      x = (*dp); /*rp_rmatrix_elem(src,j,i);*/
      for (k=i; k<rp_rmatrix_ncol(src); ++k, ++dp, ++dq)
      {
	/*rp_rmatrix_elem(src,j,k) -= x*rp_rmatrix_elem(src,i,k);*/
	(*dp) -= x*(*dq);
      }
      dp = &(rp_rmatrix_elem(inv,j,0));
      dq = &(rp_rmatrix_elem(inv,i,0));
      for (k=0; k<rp_rmatrix_ncol(src); ++k, ++dp, ++dq)
      {
	/*rp_rmatrix_elem(inv,j,k) -= x*rp_rmatrix_elem(inv,i,k);*/
	(*dp) -= x*(*dq);
      }
    }
  } /* end of triangularisation of src */

  /* diagonalisation */
  for (i=rp_rmatrix_nrow(src)-1; i>0; --i)
  {
    for (j=i-1; j>=0; --j)
    {
      x = rp_rmatrix_elem(src,j,i);
      rp_rmatrix_elem(src,j,i) = 0.0;
      dp = &(rp_rmatrix_elem(inv,j,rp_rmatrix_nrow(src)-1));
      dq = &(rp_rmatrix_elem(inv,i,rp_rmatrix_nrow(src)-1));
      for (k=rp_rmatrix_nrow(src)-1; k>=0; --k, --dp, --dq)
      {
	/*rp_rmatrix_elem(inv,j,k) -= x*rp_rmatrix_elem(inv,i,k);*/
	(*dp) -= x*(*dq);
      }
    }
  }
  return( 1 );
}

/* r := m1 - m2 */
void rp_real_matrix_sub(rp_real_matrix r,
			rp_real_matrix m1,
			rp_real_matrix m2)
{
  int i, j;
  for (i=0; i<rp_rmatrix_nrow(r); ++i)
  {
    for (j=0; j<rp_rmatrix_ncol(r); ++j)
    {
      rp_rmatrix_elem(r,i,j) = rp_rmatrix_elem(m1,i,j) - rp_rmatrix_elem(m2,i,j);
    }
  }
}

/* r := |m| */
void rp_real_matrix_abs(rp_real_matrix r,
			rp_real_matrix m)
{
  int i, j;
  for (i=0; i<rp_rmatrix_nrow(r); ++i)
  {
    for (j=0; j<rp_rmatrix_ncol(r); ++j)
    {
      rp_rmatrix_elem(r,i,j) = ((rp_rmatrix_elem(m,i,j)<0.0)?
				   (-rp_rmatrix_elem(m,i,j)):
				   (rp_rmatrix_elem(m,i,j)));
    }
  }
}

/* Returns 1 if m>=0 */
int rp_real_matrix_positive(rp_real_matrix m)
{
  int i, j;
  for (i=0; i<rp_rmatrix_nrow(m); ++i)
  {
    for (j=0; j<rp_rmatrix_ncol(m); ++j)
    {
      if(rp_rmatrix_elem(m,i,j)<0.0) return( 0 );
    }
  }
  return( 1 );
}

/* r_ij := m1_ik * m2_kj */
void rp_matrix_mul_rm_rm(rp_real_matrix r,
			 rp_real_matrix m1,
			 rp_real_matrix m2)
{
  int i, j, k;
  double * pr = &(rp_rmatrix_elem(r,0,0));
  double * pm1;

  for (i=0; i<rp_rmatrix_nrow(r); ++i)
  {
    for (j=0; j<rp_rmatrix_ncol(r); ++j, ++pr)
    {
      /* r_ij := sum_k m1_ik * m2_kj */
      (*pr) = 0.0;
      pm1 = &(rp_rmatrix_elem(m1,i,0));
      for (k=0; k<rp_rmatrix_nrow(m2); ++k, ++pm1)
      {
	if (((*pm1)!=0.0) &&
	    (rp_rmatrix_elem(m2,k,j)!=0.0))
	{
	  (*pr) += (*pm1) * rp_rmatrix_elem(m2,k,j);
	}
      }
    }
  }
}

/* Display m on out */
void rp_real_matrix_display(FILE * out, rp_real_matrix m, int digits)
{
  int i, j;
  double * p = rp_rmatrix_ptr(m);
  for (i=0; i<rp_rmatrix_nrow(m); ++i)
  {
    fprintf(out,"(");
    for (j=0; j<rp_rmatrix_ncol(m); ++j, ++p)
    {
      fprintf(out,"%g",*p);
      if (j<rp_rmatrix_ncol(m)-1)
      {
	fprintf(out,", ");
      }
    }
    fprintf(out,")");
    if (i<rp_rmatrix_nrow(m)-1)
    {
      fprintf(out,"\n");
    }
  }
}

/* ------------------------ */
/* the interval matrix type */
/* ------------------------ */
/* Creation */
void rp_interval_matrix_create(rp_interval_matrix * m, int nr, int nc)
{
  rp_malloc(*m,rp_interval_matrix_def*,sizeof(rp_interval_matrix_def));
  rp_imatrix_nrow(*m) = nr;
  rp_imatrix_ncol(*m) = nc;
  rp_imatrix_size(*m) = nr*nc;
  rp_malloc(rp_imatrix_ptr(*m),rp_interval*,rp_imatrix_size(*m)*sizeof(rp_interval));
  rp_malloc(rp_imatrix_pvars(*m),int*,nc*sizeof(int));
}

/* Destruction */
void rp_interval_matrix_destroy(rp_interval_matrix * m)
{
  rp_free(rp_imatrix_pvars(*m));
  rp_free(rp_imatrix_ptr(*m));
  rp_free(*m);
}

/* every m[i,j] := src */
void rp_interval_matrix_set(rp_interval_matrix m, rp_interval src)
{
  int i;
  for (i=0; i<rp_imatrix_size(m); ++i)
  {
    rp_interval_copy(rp_imatrix_ptr(m)[i],src);
  }
}

/* m := src */
void rp_interval_matrix_copy(rp_interval_matrix m, rp_interval_matrix src)
{
  memcpy(rp_imatrix_ptr(m),
	 rp_imatrix_ptr(src),
	 rp_imatrix_size(m)*sizeof(rp_interval));
}

/* Returns 1 if m is regular <=> every real matrix included in m */
/* is non singular */
int rp_interval_matrix_regular(rp_interval_matrix m)
{
  if (rp_imatrix_nrow(m)!=rp_imatrix_ncol(m))
  {
    return( 0 );
  }
  else
  {
    int result = 0, i;
    double max;
    rp_real_matrix center, delta, id, cinv, mul, sub;

    rp_real_matrix_create(&center,rp_imatrix_nrow(m),rp_imatrix_ncol(m));
    rp_real_matrix_create(&delta,rp_imatrix_nrow(m),rp_imatrix_ncol(m));
    rp_real_matrix_create(&cinv,rp_imatrix_nrow(m),rp_imatrix_ncol(m));
    rp_real_matrix_create(&id,rp_imatrix_nrow(m),rp_imatrix_ncol(m));
    rp_real_matrix_create(&mul,rp_imatrix_nrow(m),rp_imatrix_ncol(m));
    rp_real_matrix_create(&sub,rp_imatrix_nrow(m),rp_imatrix_ncol(m));

    rp_matrix_center_delta(center,delta,m);
    rp_real_matrix_setid(id);

    if (rp_real_matrix_inverse(cinv,center,id))
    {
      rp_real_matrix_abs(cinv,cinv);
      rp_matrix_mul_rm_rm(mul,cinv,delta);

      /* m is singular if max_i(mul_ii)>=1*/
      max = rp_rmatrix_elem(mul,0,0);
      for (i=1; i<rp_rmatrix_nrow(m); ++i)
      {
	if (max<rp_rmatrix_elem(mul,i,i))
	  max = rp_rmatrix_elem(mul,i,i);
      }
      if (max<1.0)  /* otherwise singular */
      {
	rp_real_matrix_sub(sub,id,mul);
	if (rp_real_matrix_inverse(cinv,sub,id))
	{
	  if (rp_real_matrix_positive(cinv))
	  {
	    result = 1;
	  }
	}
      }
    }

    rp_real_matrix_destroy(&center);
    rp_real_matrix_destroy(&delta);
    rp_real_matrix_destroy(&cinv);
    rp_real_matrix_destroy(&id);
    rp_real_matrix_destroy(&mul);
    rp_real_matrix_destroy(&sub);
    return( result );
  }
}

/* Display m on out */
void rp_interval_matrix_display(FILE * out, rp_interval_matrix m, int digits)
{
  int i, j;
  rp_interval * p = rp_imatrix_ptr(m);
  for (i=0; i<rp_imatrix_nrow(m); ++i)
  {
    fprintf(out,"(");
    for (j=0; j<rp_imatrix_ncol(m); ++j, ++p)
    {
      rp_interval_display_simple(*p);
      if (j<rp_imatrix_ncol(m)-1)
      {
	fprintf(out,", ");
      }
    }
    fprintf(out,")");
    if (i<rp_imatrix_nrow(m)-1)
    {
      fprintf(out,"\n");
    }
  }
}

/* ---------------- */
/* other operations */
/* ---------------- */

/* r := m*v, dimension of v equal to the number of columns of m */
void rp_matrix_mul_rm_iv(rp_interval_vector r,
			 rp_real_matrix m,
			 rp_interval_vector v)
{
  rp_interval * pr = &(rp_ivector_elem(r,0));
  double * pm = &(rp_rmatrix_elem(m,0,0));
  rp_interval * pv;
  int i, j;
  rp_interval x, aux, save;

  for (i=0; i<rp_ivector_size(r); ++i, ++pr)
  {
    /* r(i) := sum_j m(i,j)*r(j) */
    rp_interval_set_point(*pr,0.0);
    pv = &(rp_ivector_elem(v,0));
    for (j=0; j<rp_imatrix_ncol(m); ++j, ++pm, ++pv)
    {
      if (((*pm)!=0.0) && (!rp_interval_zero(*pv)))
      {
	rp_interval_set_point(x,*pm);
	rp_interval_mul_r_i(aux,x,*pv);
	rp_interval_copy(save,*pr);
	rp_interval_add(*pr,save,aux);
      }
    }
  }
}

/* r_ij := m1_ik * m2_kj */
void rp_matrix_mul_rm_im(rp_interval_matrix r,
			 rp_real_matrix m1,
			 rp_interval_matrix m2)
{
  int i, j, k;
  rp_interval * pr = &(rp_imatrix_elem(r,0,0));
  double * pm1;
  rp_interval x, save, aux;

  for (i=0; i<rp_imatrix_nrow(r); ++i)
  {
    for (j=0; j<rp_imatrix_ncol(r); ++j, ++pr)
    {
      /* r_ij := sum_k m1_ik * m2_kj */
      rp_interval_set_point(*pr,0.0);
      pm1 = &(rp_rmatrix_elem(m1,i,0));
      for (k=0; k<rp_imatrix_nrow(m2); ++k, ++pm1)
      {
	if (((*pm1)!=0.0) &&
	    (!rp_interval_zero(rp_imatrix_elem(m2,k,j))))
	{
	  rp_interval_set_point(x,*pm1);
	  rp_interval_mul_r_i(aux,x,rp_imatrix_elem(m2,k,j));
	  rp_interval_copy(save,*pr);
	  rp_interval_add(*pr,save,aux);
	}
      }
    }
  }
}

/* Computes center and delta st. src = [center-delta,center+delta] */
void rp_matrix_center_delta(rp_real_matrix center,
			    rp_real_matrix delta,
			    rp_interval_matrix src)
{
  int i, j;
  for (i=0; i<rp_rmatrix_nrow(src); ++i)
  {
    for (j=0; j<rp_rmatrix_ncol(src); ++j)
    {
      rp_rmatrix_elem(center,i,j) = 0.5*(rp_binf(rp_rmatrix_elem(src,i,j))+
					 rp_bsup(rp_rmatrix_elem(src,i,j)));
      rp_rmatrix_elem(delta,i,j)  = 0.5*(rp_bsup(rp_rmatrix_elem(src,i,j))-
					 rp_binf(rp_rmatrix_elem(src,i,j)));
    }
  }
}
