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
 * rp_operator_sat.c                                                        *
 ****************************************************************************/

#include "rp_operator_sat.h"

/* Creation of an empty stack with default size */
void rp_stack_interval_create(rp_stack_interval * s, int size)
{
  rp_stack_interval_size(*s) = size;
  rp_stack_interval_top(*s) = -1;
  if (size>0)
  {
    rp_malloc(rp_stack_interval_ptr(*s),rp_interval*,size*sizeof(rp_interval));
  }
  else
  {
    rp_stack_interval_ptr(*s) = NULL;
  }
}

/* Destruction of stack */
void rp_stack_interval_destroy(rp_stack_interval * s)
{
  if (rp_stack_interval_size(*s)>0)
  {
    rp_free(rp_stack_interval_ptr(*s));
  }
  else
  {
    rp_stack_interval_ptr(*s) = NULL;
  }
  rp_stack_interval_size(*s) = 0;
  rp_stack_interval_top(*s) = -1;
}

/* Pop operation */
void rp_stack_interval_pop(rp_stack_interval s)
{
  if (!rp_stack_interval_empty(s))
  {
    -- rp_stack_interval_top(s);
  }
}

/* Push operation */
void rp_stack_interval_push(rp_stack_interval s, rp_interval i)
{
  if (rp_stack_interval_full(s))
  {
    if (rp_stack_interval_size(s)==0)
    {
      /* allocation */
      rp_stack_interval_size(s) = 1;
      rp_malloc(rp_stack_interval_ptr(s),rp_interval*,sizeof(rp_interval));
    }
    else
    {
      /* reallocation */
      rp_stack_interval_size(s) *= 2;
      rp_realloc(rp_stack_interval_ptr(s),rp_interval*,
		 rp_stack_interval_size(s)*sizeof(rp_interval));
    }
  }
  ++ rp_stack_interval_top(s);
  rp_interval_copy(rp_stack_interval_topelem(s),i);
}

/* Projection of c onto the variables belonging to b */
/* Returns false if an empty domain is computed      */
int rp_sat_hull_eq(rp_ctr_num c, rp_box b)
{
  int result = 0;
  if (rp_expression_eval(rp_ctr_num_left(c),b))
  {
    if (rp_expression_eval(rp_ctr_num_right(c),b))
    {
      /* interpretation of equality as non empty intersection */
      rp_interval i;
      rp_interval_inter(i,
			rp_expression_val(rp_ctr_num_left(c)),
			rp_expression_val(rp_ctr_num_right(c)));
      if (!rp_interval_empty(i))
      {
	if (rp_expression_project(rp_ctr_num_left(c),i,b))
	{
	  result = rp_expression_project(rp_ctr_num_right(c),i,b);
	}
      }
    }
  }
  return( result );
}

/* Projection of c onto the variables belonging to b */
/* Returns false if an empty domain is computed      */
int rp_sat_hull_inf(rp_ctr_num c, rp_box b)
{
  int result = 0;
  if (rp_expression_eval(rp_ctr_num_left(c),b))
  {
    if (rp_expression_eval(rp_ctr_num_right(c),b))
    {
      /* interpretation of equality as non empty intersection */
      rp_interval ileft, iright;

      /* [a,b] <= [c,d]  -->  ileft := [a,b] inter [-oo,d] */
      rp_interval_set(
            ileft,
	    rp_binf(rp_expression_val(rp_ctr_num_left(c))),
	    rp_min_num(rp_bsup(rp_expression_val(rp_ctr_num_left(c))),
		       rp_bsup(rp_expression_val(rp_ctr_num_right(c)))));

      /* [a,b] <= [c,d]  -->  iright := [c,d] inter [a,+oo] */
      rp_interval_set(
            iright,
	    rp_max_num(rp_binf(rp_expression_val(rp_ctr_num_left(c))),
		       rp_binf(rp_expression_val(rp_ctr_num_right(c)))),
	    rp_bsup(rp_expression_val(rp_ctr_num_right(c))));

      if ((!rp_interval_empty(ileft)) && (!rp_interval_empty(iright)))
      {
	if (rp_expression_project(rp_ctr_num_left(c),ileft,b))
	{
	  result = rp_expression_project(rp_ctr_num_right(c),iright,b);
	}
      }
    }
  }
  return( result );
}

/* Projection of c onto the variables belonging to b */
/* Returns false if an empty domain is computed      */
int rp_sat_hull_sup(rp_ctr_num c, rp_box b)
{
  int result = 0;
  if (rp_expression_eval(rp_ctr_num_left(c),b))
  {
    if (rp_expression_eval(rp_ctr_num_right(c),b))
    {
      /* interpretation of equality as non empty intersection */
      rp_interval ileft, iright;

      /* [a,b] >= [c,d]  -->  ileft := [a,b] inter [c,+oo] */
      rp_interval_set(
            ileft,
	    rp_max_num(rp_binf(rp_expression_val(rp_ctr_num_left(c))),
		       rp_binf(rp_expression_val(rp_ctr_num_right(c)))),
	    rp_bsup(rp_expression_val(rp_ctr_num_left(c))));

      /* [a,b] >= [c,d]  -->  iright := [c,d] inter [-oo,b] */
      rp_interval_set(
	    iright,
	    rp_binf(rp_expression_val(rp_ctr_num_right(c))),
	    rp_min_num(rp_bsup(rp_expression_val(rp_ctr_num_left(c))),
		       rp_bsup(rp_expression_val(rp_ctr_num_right(c)))));

      if ((!rp_interval_empty(ileft)) && (!rp_interval_empty(iright)))
      {
	if (rp_expression_project(rp_ctr_num_left(c),ileft,b))
	{
	  result = rp_expression_project(rp_ctr_num_right(c),iright,b);
	}
      }
    }
  }
  return( result );
}

/* let domain = [a,b] --> bound := [a,min((a+eps)+,b)] */
/*                          rem := [min((a+eps)+,b),b] */
void rp_opsplit_lb(rp_interval bound, rp_interval rem,
		   rp_interval domain, double eps)
{
  rp_binf(bound) = rp_binf(domain);
  rp_bsup(bound) = rp_min_num(rp_next_double(rp_binf(domain)+eps),
			      rp_bsup(domain));
  rp_binf(rem) = rp_bsup(bound);
  rp_bsup(rem) = rp_bsup(domain);
}

/* let domain = [a,b] --> bound := [max((b-eps)-,a),b] */
/*                          rem := [a,max((b-eps)-,a)] */
void rp_opsplit_rb(rp_interval bound, rp_interval rem,
		   rp_interval domain, double eps)
{
  rp_binf(bound) = rp_max_num(rp_prev_double(rp_bsup(domain)-eps),
			      rp_binf(domain));
  rp_bsup(bound) = rp_bsup(domain);
  rp_binf(rem) = rp_binf(domain);
  rp_bsup(rem) = rp_binf(bound);
}

/* let domain=[a,b] and let c be the midpoint of [a,b]              */
/* push in search [c,b] and then [a,c] that becomes the top element */
void rp_opshrink_split_lb (rp_stack_interval search, rp_interval domain)
{
  if (rp_interval_canonical(domain))
  {
    rp_stack_interval_push(search,domain);
  }
  else
  {
    rp_interval aux;
    double center = rp_interval_midpoint(domain);

    /* push rightmost domain */
    rp_interval_set(aux,center,rp_bsup(domain));
    rp_stack_interval_push(search,aux);

    /* push lefttmost domain */
    rp_interval_set(aux,rp_binf(domain),center);
    rp_stack_interval_push(search,aux);
  }
}

/* let domain=[a,b] and let c be the midpoint of [a,b]              */
/* push in search [a,c] and then [c,b] that becomes the top element */
void rp_opshrink_split_rb(rp_stack_interval search, rp_interval domain)
{
  if (rp_interval_canonical(domain))
  {
    rp_stack_interval_push(search,domain);
  }
  else
  {
    rp_interval aux;
    double center = rp_interval_midpoint(domain);

    /* push lefttmost domain */
    rp_interval_set(aux,rp_binf(domain),center);
    rp_stack_interval_push(search,aux);

    /* push rightmost domain */
    rp_interval_set(aux,center,rp_bsup(domain));
    rp_stack_interval_push(search,aux);
  }
}

/* Search a zero of f at one bound of x         */
/* eps is the desired precision of the variable */
int rp_opshrink(rp_expression f, rp_expression df_dx,
		rp_box b, int x, double improve, double eps,
		rp_opsplit bsplit, rp_opshrink_split shsplit)
{
  int found = 0;
  rp_stack_interval search;
  double epsbound = eps/2;
  rp_stack_interval_create(&search,10);
  rp_stack_interval_push(search,rp_box_elem(b,x));

  while ((!found) && (!rp_stack_interval_empty(search)))
  {
    rp_interval_copy(rp_box_elem(b,x),rp_stack_interval_topelem(search));
    rp_stack_interval_pop(search);

    if (rp_num_newton(f,df_dx,b,x,improve))
    {
      if ((rp_interval_canonical(rp_box_elem(b,x))) ||
	  (rp_interval_width(rp_box_elem(b,x))<=epsbound))
      {
	/* interval precise enough */
	found = 1;
      }
      else
      {
	/* 0 is in a small interval at the bound to be reduced ? */
	rp_interval bound, rem;
	bsplit(bound,rem,rp_box_elem(b,x),epsbound);
	rp_interval_copy(rp_box_elem(b,x),bound);
	if ((rp_expression_eval_single(f,b,x)) &&
	    (rp_interval_contains(rp_expression_val(f),0.0)))
	{
	  found = 1;
	}
	else
	{
	  /* bound to be removed and remaining domain to be split */
	  shsplit(search,rem);
	}
      }
    }
    /* else the interval has already been removed from the stack */
  }

  rp_stack_interval_destroy(&search);
  return( found );
}

/* Reduction of b(x) with precision eps by box consistency onto f = 0 */
int rp_sat_box_eq(rp_expression f, rp_expression df_dx,
		  rp_box b, int x, double improve, double eps)
{
  int result = 0;
  rp_interval domain;
  rp_interval_copy(domain,rp_box_elem(b,x));

  /* First try a reduction of the whole domain using Newton */
  if (rp_num_newton(f,df_dx,b,x,improve))
  {
    /* Desired precision reached ? */
    if (rp_interval_width(rp_box_elem(b,x))<=eps)
    {
      result = 1;
    }

    /* Shrink left bound of b(x) */
    else if (rp_opshrink(f,df_dx,b,x,improve,eps,
			 rp_opsplit_lb,rp_opshrink_split_lb))
    {
      double left = rp_binf(rp_box_elem(b,x));

      /* Shrink right bound of [left,sup(b(x))] */
      rp_bsup(rp_box_elem(b,x)) = rp_bsup(domain);
      if (rp_opshrink(f,df_dx,b,x,improve,eps,
		      rp_opsplit_rb,rp_opshrink_split_rb))
      {
	rp_binf(rp_box_elem(b,x)) = left;
	result = 1;
      }
    }
  }
  return( result );
}

/* Reduction of b(x) with precision eps by box consistency onto f >= 0 */
int rp_sat_box_sup(rp_expression f, rp_expression df_dx,
		   rp_box b, int x, double improve, double eps)
{
  int result = 1;

  /* First try to eliminate the box if f(b) < 0 */
  if ((!rp_expression_eval(f,b)) ||
      (rp_bsup(rp_expression_val(f))<0.0))
  {
    result = 0;
  }

  /* Reduction only if b is not an inner box */
  else if (rp_binf(rp_expression_val(f))<0.0)
  {
    rp_interval domain;
    rp_interval_copy(domain,rp_box_elem(b,x));

    /* Left bound consistent --> nothing to do */
    rp_bsup(rp_box_elem(b,x)) = rp_min_num(rp_next_double(rp_binf(domain)+
							  eps),
					   rp_bsup(domain));
    if ((!rp_expression_eval_single(f,b,x)) ||
	(rp_bsup(rp_expression_val(f)) < 0.0))
    {
      rp_binf(rp_box_elem(b,x)) = rp_bsup(rp_box_elem(b,x));
      rp_bsup(rp_box_elem(b,x)) = rp_bsup(domain);
      if (rp_opshrink(f,df_dx,b,x,improve,eps,
		      rp_opsplit_lb,rp_opshrink_split_lb))
      {
	rp_binf(domain) = rp_binf(rp_box_elem(b,x));
      }
      else
      {
	result = 0;
      }
    }

    /* Right bound consistent --> nothing to do */
    if (result)
    {
      rp_binf(rp_box_elem(b,x)) = rp_max_num(rp_prev_double(rp_bsup(domain)-
							    eps),
					     rp_binf(domain));
      rp_bsup(rp_box_elem(b,x)) = rp_bsup(domain);
      if ((!rp_expression_eval_single(f,b,x)) ||
	  (rp_bsup(rp_expression_val(f)) < 0.0))
      {
	rp_bsup(rp_box_elem(b,x)) = rp_binf(rp_box_elem(b,x));
	rp_binf(rp_box_elem(b,x)) = rp_binf(domain);

	if (rp_opshrink(f,df_dx,b,x,improve,eps,
			rp_opsplit_rb,rp_opshrink_split_rb))
	{
	  rp_bsup(domain) = rp_bsup(rp_box_elem(b,x));
	}
	else
	{
	  result = 0;
	}
      }
    }
    if (result)
    {
      rp_interval_copy(rp_box_elem(b,x),domain);
    }
  }
  return( result );
}

/* Reduction of b(x) with precision eps by box consistency onto f <= 0 */
int rp_sat_box_inf(rp_expression f, rp_expression df_dx,
		   rp_box b, int x, double improve, double eps)
{
  int result = 1;

  /* First try to eliminate the box if f(b) > 0 */
  if ((!rp_expression_eval(f,b)) ||
      (rp_binf(rp_expression_val(f))>0.0))
  {
    result = 0;
  }

  /* Reduction only if b is not an inner box */
  else if (rp_bsup(rp_expression_val(f))>0.0)
  {
    rp_interval domain;
    rp_interval_copy(domain,rp_box_elem(b,x));

    /* Left bound consistent --> nothing to do */
    rp_bsup(rp_box_elem(b,x)) = rp_min_num(rp_next_double(rp_binf(domain)+
							  eps),
					   rp_bsup(domain));
    if ((!rp_expression_eval_single(f,b,x)) ||
	(rp_binf(rp_expression_val(f)) > 0.0))
    {
      rp_binf(rp_box_elem(b,x)) = rp_bsup(rp_box_elem(b,x));
      rp_bsup(rp_box_elem(b,x)) = rp_bsup(domain);
      if (rp_opshrink(f,df_dx,b,x,improve,eps,
		      rp_opsplit_lb,rp_opshrink_split_lb))
      {
	rp_binf(domain) = rp_binf(rp_box_elem(b,x));
      }
      else
      {
	result = 0;
      }
    }

    /* Right bound consistent --> nothing to do */
    if (result)
    {
      rp_binf(rp_box_elem(b,x)) = rp_max_num(rp_prev_double(rp_bsup(domain)-
							    eps),
					     rp_binf(domain));
      rp_bsup(rp_box_elem(b,x)) = rp_bsup(domain);
      if ((!rp_expression_eval_single(f,b,x)) ||
	  (rp_binf(rp_expression_val(f)) > 0.0))
      {
	rp_bsup(rp_box_elem(b,x)) = rp_binf(rp_box_elem(b,x));
	rp_binf(rp_box_elem(b,x)) = rp_binf(domain);

	if (rp_opshrink(f,df_dx,b,x,improve,eps,
			rp_opsplit_rb,rp_opshrink_split_rb))
	{
	  rp_bsup(domain) = rp_bsup(rp_box_elem(b,x));
	}
	else
	{
	  result = 0;
	}
      }
    }
    if (result)
    {
      rp_interval_copy(rp_box_elem(b,x),domain);
    }
  }
  return( result );
}
