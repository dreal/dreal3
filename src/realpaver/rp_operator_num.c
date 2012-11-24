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
 * rp_operator_num.c                                                        *
 ****************************************************************************/

#include "rp_operator_num.h"

/* Newton step */
int rp_num_newton_step (rp_expression f, rp_expression df_dx,
			rp_box b, int x, rp_union_interval u)
{
  rp_interval dom, mid;
  int i;

  rp_interval_copy(dom,rp_box_elem(b,x));
  rp_interval_set_point(mid,rp_interval_midpoint(dom));
  rp_union_set_empty(u);

  /* df_dx(b) */
  if (!rp_expression_eval(df_dx,b))
  {
    return( 0 );
  }

  /* f(mid) */
  rp_interval_copy(rp_box_elem(b,x),mid);
  if (!rp_expression_eval(f,b))
  {
    return( 0 );
  }

  if (!rp_interval_extended_div(u,rp_expression_val(f),
				rp_expression_val(df_dx)))
  {
    return( 0 );
  }

  /* u := mid(b(x)) - u */
  for (i=0; i<rp_union_card(u); ++i)
  {
    rp_interval aux;
    rp_interval_copy(aux,rp_union_elem(u,i));
    rp_interval_sub(rp_union_elem(u,i),mid,aux);
  }
  if (rp_union_card(u)==2)
  {
    /* I-{J,K} = {I-K,I-J} --> reverse ordering in u */
    rp_interval aux;
    rp_interval_copy(aux,rp_union_elem(u,0));
    rp_interval_copy(rp_union_elem(u,0),rp_union_elem(u,1));
    rp_interval_copy(rp_union_elem(u,1),aux);
  }

  /* Intersection of domain and the Newton step result */
  if (!rp_union_inter(u,dom))
  {
    return( 0 );
  }
  else
  {
    /* New domain: hull of the intersection */
    rp_union_hull(rp_box_elem(b,x),u);
  }
  return( 1 );
}

/* Newton iteration */
int rp_num_newton(rp_expression f, rp_expression df_dx,
		  rp_box b, int x, double improve)
{
  rp_interval dom;
  int result = 1;

  rp_union_interval u;
  rp_union_create_size(&u,2);

  /* Failure if b does not contain a zero of f */
  if ((!rp_expression_eval(f,b)) ||
      (!rp_interval_contains(rp_expression_val(f),0.0)))
  {
    result = 0;
  }

  /* if +oo or -oo belong to the image of f then f may be discontinuous */
  /* Nathalie Revol's suggestion --> no reduction in this case          */
  else if ((rp_expression_derivable(f)) &&
	   (!rp_interval_infinite(rp_expression_val(f))))
  {
    rp_interval_copy(dom,rp_box_elem(b,x));
    if (!rp_num_newton_step(f,df_dx,b,x,u))
    {
      result = 0;
    }

    /* Iteration */
    while ((result) &&
	   (rp_interval_improved(rp_box_elem(b,x),dom,improve)))
    {
      rp_interval_copy(dom,rp_box_elem(b,x));
      if (!rp_num_newton_step(f,df_dx,b,x,u))
      {
	result = 0;
      }
    }
  }
  rp_union_destroy(&u);
  return( result );
}

/* Gauss-Seidel step */
int rp_num_gs_step(rp_interval_matrix a,
		   rp_interval_vector x,
		   rp_interval_vector b,
		   double improve,
		   int * modified)
{
  int i, j;
  rp_interval nx, aux, save;
  rp_union_interval ux;
  rp_interval * pa = &(rp_imatrix_elem(a,0,0));
  rp_interval * pb = &(rp_ivector_elem(b,0));
  rp_interval * px;

  (*modified) = 0;

  rp_union_create_size(&ux,2);
  for (i=0; i<rp_imatrix_nrow(a); ++i, ++pb)
  {
    /* nx := b(i) - sum_(j!=i) a_ijx_j */
    rp_interval_copy(nx,*pb);
    px = &(rp_ivector_elem(x,0));

    for (j=0; j<rp_imatrix_ncol(a); ++j, ++pa, ++px)
    {
      if (j!=i)
      {
	rp_interval_mul(aux,*pa,*px);
	rp_interval_copy(save,nx);
	rp_interval_sub(nx,save,aux);
      }
    }

    /* ux := nx / a(i,i) */
    rp_interval_extended_div(ux,nx,rp_imatrix_elem(a,i,i));

    /* x(i) := hull (x(i) inter ux) */
    if (rp_union_inter(ux,rp_ivector_elem(x,i)))
    {
      rp_interval_copy(save,rp_ivector_elem(x,i));
      rp_union_hull(rp_ivector_elem(x,i),ux);
      if (!(*modified))
      {
	(*modified) = rp_interval_improved(rp_ivector_elem(x,i),save,improve);
      }
    }
    else
    {
      rp_union_destroy(&ux);
      return( 0 );
    }
  }
  rp_union_destroy(&ux);
  return( 1 );
}

/* Gauss-Seidel iteration over system ax = b */
int rp_num_gs (rp_interval_matrix a,
	       rp_interval_vector x,
	       rp_interval_vector b,
	       double improve)
{
  int result = 1, modified = 1;
  while (result && modified)
  {
    result = rp_num_gs_step(a,x,b,improve,&modified);
  }
  return( result );
}
