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
 * rp_projection.c                                                          *
 ****************************************************************************/

#include "rp_projection.h"

/* ------------------ */
/* Auxiliary function */
/* ------------------ */
/* sin(result) = i <=> result := sin-1(i) in the interval [-Pi,Pi] */
/* returns the cardinal of result                                  */
/* note: asin is defined from [-1,1] to [-Pi/2,Pi/2]               */
int rp_project_sin_canonical(rp_union_interval result, rp_interval i)
{
                              /*         [ -1        0        +1 ]             */
  if ( (rp_binf(i)>1.0) ||    /*            |        |         |    |---|      */
       (rp_bsup(i)<-1.0) )    /*  |---|     |        |         |               */
  {
    rp_union_set_empty(result);
  }
  else if (rp_binf(i)<=-1.0)  /*  |---                                         */
  {
    if (rp_bsup(i)<=0.0)      /*  |-------------|                              */
    {
      rp_interval aux;
      RP_ROUND_UPWARD();
      rp_bsup(aux) = asin(rp_bsup(i));                 /* asin(i.sup) rounded up */

      rp_binf(aux) = -rp_bsup(RP_INTERVAL_PI);         /* -pi rounded down */
      RP_ROUND_DOWNWARD();
      rp_binf(aux) -= rp_bsup(aux);                    /* -pi - asin(i.sup) */

      rp_union_set_empty_size(result,1);
      rp_union_insert(result,aux);
    }
                              /*         [ -1        0        +1 ]             */
    else if (rp_bsup(i)<1.0)  /*  |-----------------------|                    */
    {
      rp_interval aux1, aux2;
      rp_binf(aux1) = -rp_bsup(RP_INTERVAL_PI);
      RP_ROUND_UPWARD();
      rp_bsup(aux1) = asin(rp_bsup(i));                /* asin(i.sup) rounded up */

      RP_ROUND_DOWNWARD();
      rp_binf(aux2) = rp_binf(RP_INTERVAL_PI);
      rp_binf(aux2) -= rp_bsup(aux1);                  /* pi - asin(i.sup) */
      rp_bsup(aux2) = rp_bsup(RP_INTERVAL_PI);         /* pi rounded up */

      rp_union_set_empty_size(result,2);
      rp_union_insert(result,aux1);
      rp_union_insert(result,aux2);
    }
                              /*         [ -1        0        +1 ]             */
    else                      /*  |-------------------------------------|      */
    {
      /* whole domain valid */
      rp_interval aux;
      rp_binf(aux) = -rp_bsup(RP_INTERVAL_PI);
      rp_bsup(aux) =  rp_bsup(RP_INTERVAL_PI);

      rp_union_set_empty_size(result,1);
      rp_union_insert(result,aux);
    }
  }
                              /*         [ -1        0        +1 ]             */
  else if (rp_binf(i)<=0.0)   /*              |---                             */
  {
    if (rp_bsup(i)<0.0)       /*              |-----|                          */
    {
      rp_interval aux1, aux2;
      RP_ROUND_DOWNWARD();
      rp_binf(aux2) = asin(rp_binf(i));                /* asin(i.inf) rounded down */
      RP_ROUND_UPWARD();
      rp_bsup(aux2) = asin(rp_bsup(i));                /* asin(i.sup) rounded up */

      RP_ROUND_DOWNWARD();
      rp_binf(aux1) = -rp_bsup(RP_INTERVAL_PI);        /* -pi rounded down */
      rp_binf(aux1) -= rp_bsup(aux2);                  /* -pi - asin(i.sup) */
      RP_ROUND_UPWARD();
      rp_bsup(aux1) = -rp_binf(RP_INTERVAL_PI);        /* -pi rounded up */
      rp_bsup(aux1) -= rp_binf(aux2);                  /* -pi - asin(i.inf) */

      rp_union_set_empty_size(result,2);
      rp_union_insert(result,aux1);
      rp_union_insert(result,aux2);
    }
                              /*         [ -1        0        +1 ]             */
    else if (rp_bsup(i)<1.0)  /*              |-----------|                    */
    {
      rp_interval aux1, aux2, aux3;
      RP_ROUND_DOWNWARD();
      rp_binf(aux2) = asin(rp_binf(i));                /* asin(i.inf) rounded down */
      RP_ROUND_UPWARD();
      rp_bsup(aux2) = asin(rp_bsup(i));                /* asin(i.sup) rounded up */

      rp_binf(aux1) = -rp_bsup(RP_INTERVAL_PI);
      rp_bsup(aux1) = -rp_binf(RP_INTERVAL_PI);        /* -pi rounded up */
      RP_ROUND_UPWARD();
      rp_bsup(aux1) -= rp_binf(aux2);                  /* -pi - asin(i.inf) */

      RP_ROUND_DOWNWARD();
      rp_binf(aux3) = rp_binf(RP_INTERVAL_PI);
      rp_binf(aux3) -= rp_bsup(aux2);                 /* pi - asin(i.sup) */
      rp_bsup(aux3) = rp_bsup(RP_INTERVAL_PI);        /* pi rounded up */

      rp_union_set_empty_size(result,3);
      rp_union_insert(result,aux1);
      rp_union_insert(result,aux2);
      rp_union_insert(result,aux3);
    }
                              /*         [ -1        0        +1 ]             */
    else                      /*              |-------------------------|      */
    {
      rp_interval aux1, aux2;
      RP_ROUND_DOWNWARD();
      rp_binf(aux2) = asin(rp_binf(i));               /* asin(i.inf) rounded down */
      rp_bsup(aux2) = rp_bsup(RP_INTERVAL_PI);        /* pi rounded up */

      rp_binf(aux1) = -rp_bsup(RP_INTERVAL_PI);
      rp_bsup(aux1) = -rp_binf(RP_INTERVAL_PI);       /* -pi rounded up */
      RP_ROUND_UPWARD();
      rp_bsup(aux1) -= rp_binf(aux2);                 /* -pi - asin(i.inf) */

      rp_union_set_empty_size(result,2);
      rp_union_insert(result,aux1);
      rp_union_insert(result,aux2);
    }
  }
                              /*         [ -1        0        +1 ]             */
  else                        /*                       |---                    */
  {
    if (rp_bsup(i)<1.0)       /*                       |------|                */
    {
      rp_interval aux1, aux2;
      RP_ROUND_DOWNWARD();
      rp_binf(aux1) = asin(rp_binf(i));               /* asin(i.inf) rounded down */
      RP_ROUND_UPWARD();
      rp_bsup(aux1) = asin(rp_bsup(i));               /* asin(i.sup) rounded up */

      rp_binf(aux2) = rp_binf(RP_INTERVAL_PI);        /* pi rounded down */
      RP_ROUND_DOWNWARD();
      rp_binf(aux2) -= rp_bsup(aux1);                 /* pi - asin(i.sup) */
      rp_bsup(aux2) = rp_bsup(RP_INTERVAL_PI);        /* pi rounded up */
      RP_ROUND_UPWARD();
      rp_bsup(aux2) -= rp_binf(aux1);                 /* pi - asin(i.inf) */

      rp_union_set_empty_size(result,2);
      rp_union_insert(result,aux1);
      rp_union_insert(result,aux2);
    }
                              /*         [ -1        0        +1 ]             */
    else                      /*                       |----------------|      */
    {
      rp_interval aux;
      RP_ROUND_DOWNWARD();
      rp_binf(aux) = asin(rp_binf(i));                /* asin(i.inf) rounded down */

      rp_bsup(aux) = rp_bsup(RP_INTERVAL_PI);         /* pi rounded up */
      RP_ROUND_UPWARD();
      rp_bsup(aux) -= rp_binf(aux);                   /* pi - asin(i.inf) */

      rp_union_set_empty_size(result,1);
      rp_union_insert(result,aux);
    }
  }
  return( rp_union_card(result) );
}

/* x = y + z => xnew := hull ( (y+z) inter x ) */

int rp_project_add_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_add(aux,y,z);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = y + z => ynew := hull ( (x-z) inter y ) */
int rp_project_add_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_sub(aux,x,z);
  rp_interval_inter(ynew,aux,y);
  return( !rp_interval_empty(ynew) );
}

/* x = y + z => znew := hull ( (x-y) inter z ) */
int rp_project_add_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z)
{
  return rp_project_add_fst(znew,x,z,y); /* commutativity */
}

/* x = y - z => xnew := hull ( (y-z) inter x ) */
int rp_project_sub_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_sub(aux,y,z);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = y - z => ynew := hull ( (x+z) inter y ) */
int rp_project_sub_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_add(aux,x,z);
  rp_interval_inter(ynew,aux,y);
  return( !rp_interval_empty(ynew) );
}

/* x = y - z => znew := hull ( (y-x) inter z ) */

int rp_project_sub_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_sub(aux,y,x);
  rp_interval_inter(znew,aux,z);
  return( !rp_interval_empty(znew) );
}

/* x = y * z => xnew := hull ( (y*z) inter x ) */

int rp_project_mul_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_mul(aux,y,z);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = y * z => ynew := hull ( (x/z) inter y ) */

int rp_project_mul_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_union_interval div;
  rp_union_create(&div);
  rp_interval_extended_div(div,x,z);
  rp_union_inter(div,y);
  rp_union_hull(ynew,div);
  rp_union_destroy(&div);
  return( !rp_interval_empty(ynew) );
}

/* x = y * z => znew := hull ( (x/y) inter z ) */

int rp_project_mul_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z)
{
  return rp_project_mul_fst(znew,x,z,y); /* commutativity */
}

/* x = y / z => xnew := hull ( (y/z) inter x ) */

int rp_project_div_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_union_interval div;
  rp_union_create(&div);
  rp_interval_extended_div(div,y,z);
  rp_union_inter(div,x);
  rp_union_hull(xnew,div);
  rp_union_destroy(&div);
  return( !rp_interval_empty(xnew) );
}

/* x = y / z => ynew := hull ( (x*z) inter y ) */

int rp_project_div_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_mul(aux,x,z);
  rp_interval_inter(ynew,aux,y);
  return( !rp_interval_empty(ynew) );
}

/* x = y / z => znew := hull ( (y/x) inter z ) */

int rp_project_div_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_union_interval div;
  rp_union_create(&div);
  rp_interval_extended_div(div,y,x);
  rp_union_inter(div,z);
  rp_union_hull(znew,div);
  rp_union_destroy(&div);
  return( !rp_interval_empty(znew) );
}

/* x = min(y,z) => xnew := hull ( min(y,z) inter x ) */

int rp_project_min_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_min(aux,y,z);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = min(y,z) => ynew := hull ( min-1(x,z) inter y ) */

int rp_project_min_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z)
{
  if (rp_binf(x)>rp_bsup(z))       /* x:            |-----| */
  {                                /* z: |-----|            */
    rp_interval_set_empty(ynew);   /* ynew := empty         */
  }
  else if (rp_binf(z)>rp_bsup(x))  /* x:   |-----|          */
  {                                /* z:          |-----|   */
    rp_interval_inter(ynew,x,y);   /* ynew := x inter y     */
  }
  else                             /* non empty intersection */
  {
    rp_bsup(ynew) = rp_bsup(y);    /* result := [binf(x),+oo] inter y */
    rp_binf(ynew) = rp_max_num(rp_binf(x),rp_binf(y));
  }
  return( !rp_interval_empty(ynew) );
}

/* x = min(y,z) => znew := hull ( min-1(x,y) inter z ) */

int rp_project_min_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z)
{
  return rp_project_min_fst(znew,x,z,y); /* commutativity */
}

/* x = max(y,z) => xnew := hull ( max(y,z) inter x ) */

int rp_project_max_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval z)
{
  rp_interval aux;
  rp_interval_max(aux,y,z);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = max(y,z) => ynew := hull ( max-1(x,z) inter y ) */

int rp_project_max_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval z)
{
  if (rp_binf(x)>rp_bsup(z))         /* x:            |-----| */
  {                                  /* z: |-----|            */
    rp_interval_inter(ynew,x,y);     /* ynew := x inter y     */
  }
  else if (rp_binf(z)>rp_bsup(x))    /* x: |-----|            */
  {                                  /* z:          |-----|   */
    rp_interval_set_empty(ynew);     /* ynew := empty          */
  }
  else                              /* non empty intersection */
  {
    rp_binf(ynew) = rp_binf(y);     /* ynew := [-oo,bsup(x)] inter y */
    rp_bsup(ynew) = rp_min_num(rp_bsup(x),rp_bsup(y));
  }
  return( !rp_interval_empty(ynew) );
}

/* x = max(y,z) => znew := hull ( max-1(x,y) inter z ) */

int rp_project_max_snd (rp_interval znew, rp_interval x, rp_interval y,
			rp_interval z)
{
  return rp_project_max_fst(znew,x,z,y); /* commutativity */
}



/* x = pow(y,n) => xnew := hull ( pow(y,n) inter x ) */

int rp_project_pow_zro (rp_interval xnew, rp_interval x, rp_interval y,
			rp_interval n)
{
  rp_interval aux;
  rp_interval_pow(aux,y,n);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = pow(y,n) => ynew := hull ( pow-1(x,n) inter y ) */

int rp_project_pow_fst (rp_interval ynew, rp_interval x, rp_interval y,
			rp_interval n)
{
  rp_interval aux1, aux2;
  rp_union_interval aux;
  int exp = (int)rp_binf(n);
  if( rp_odd(exp) )
  {
    rp_interval_nthroot(aux1,x,n);
    rp_interval_inter(ynew,aux1,y);
  }
  else
  {
    if( rp_interval_contains(x,0.0) )
    {
      rp_interval_nthroot(aux1,x,n);
      rp_interval_inter(ynew,aux1,y);
    }
    else if( rp_binf(x)>0.0 )
    {
      rp_interval_nthroot(aux1,x,n);
      rp_interval_neg(aux2,aux1);
      rp_union_create_size(&aux,2);
      rp_union_insert(aux,aux1);
      rp_union_insert(aux,aux2);
      rp_union_inter(aux,y);
      rp_union_hull(ynew,aux);
      rp_union_destroy(&aux);
    }
    else
    {
      rp_interval_set_empty(ynew);
    }
  }
  return( !rp_interval_empty(ynew) );
}

/* x = -y => xnew := hull ( (-y) inter x ) */

int rp_project_neg_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_neg(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = -y => ynew := hull ( (-x) inter y ) */

int rp_project_neg_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_neg(aux,x);
  rp_interval_inter(ynew,aux,y);
  return( !rp_interval_empty(ynew) );
}

/* x = y^2 => xnew := hull ( y^2 inter x ) */

int rp_project_sqr_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_sqr(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = y^2 => ynew := hull ( pow-1(x,2) inter y ) */

int rp_project_sqr_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval n;
  rp_interval_set_point(n,2.0);
  return rp_project_pow_fst(ynew,x,y,n);
}

/* x = sqrt(y) => xnew := hull ( sqrt(y) inter x ) */

int rp_project_sqrt_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_sqrt(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = sqrt(y) => ynew := hull ( (x inter R+)^2 inter y ) */

int rp_project_sqrt_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval dom, aux, sqr;
  rp_interval_set(dom,0.0,RP_INFINITY);
  rp_interval_inter(aux,dom,x);
  if (rp_interval_empty(aux))
  {
    rp_interval_set_empty(ynew);
  }
  else
  {
    rp_interval_sqr(sqr,aux);
    rp_interval_inter(ynew,sqr,y);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = exp(y) => xnew := hull ( exp(y) inter x ) */

int rp_project_exp_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_exp(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = exp(y) => ynew := hull ( log(x inter R+) inter y ) */

int rp_project_exp_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval dom, aux, log;
  rp_interval_set(dom,0.0,RP_INFINITY);
  rp_interval_inter(aux,dom,x);
  if (rp_interval_empty(aux))
  {
    rp_interval_set_empty(ynew);
  }
  else
  {
    rp_interval_log(log,aux);
    rp_interval_inter(ynew,log,y);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = log(y) => xnew := hull ( log(y) inter x ) */

int rp_project_log_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_log(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = log(y) => ynew := hull ( exp(x) inter y ) */

int rp_project_log_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_exp(aux,x);
  rp_interval_inter(ynew,aux,y);
  return( !rp_interval_empty(ynew) );
}

/* x = sin(y) => xnew := hull ( sin(y) inter x ) */

int rp_project_sin_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_sin(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = sin(y) => ynew := hull ( sin-1(x) inter y ) */

int rp_project_sin_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval offset, step, dest;
  double bound;
  rp_union_interval u;
  rp_union_create(&u);

  /* computation of sin-1(x) in [-pi,+pi] => u */
  if (rp_project_sin_canonical(u,x)==0)
  {
    rp_union_destroy(&u);
    rp_interval_set_empty(ynew);
    return( 0 );
  }

  rp_interval_set(dest,-rp_bsup(RP_INTERVAL_PI),rp_bsup(RP_INTERVAL_PI));

  /* translation of the left bound in dest */
  bound = rp_interval_translate(rp_binf(y),dest,RP_ROUND_VALUE_DOWN,step,offset);

  /* if the left bound is in u=sin-1(x) then no reduction */
  if (rp_union_contains(u,bound))
  {
    rp_binf(ynew) = rp_binf(y);
  }
  else
  {
    double c;
    if (rp_union_strictly_greater(u,bound))  /* bound:                       | */
    {                                        /* u:     |------|    |-----|     */
                                             /* c:=    ^ + 2Pi                 */
      /* new bound in binf(u) + 2Pi and (+ 2Pi) is handled as (step += 1) */
      rp_interval one, aux;
      rp_interval_set_point(one,1.0);
      rp_interval_copy(aux,step);
      rp_interval_add_r_i(step,one,aux);
      c = rp_union_binf(u);
    }
    else                                     /* bound:           |              */
    {                                        /* u:     |------|     |-----|     */
      c = rp_union_next_double(u,bound);     /* c:=                 ^           */
    }

    if( rp_binf(step)==0.0 )
    {
      rp_binf(ynew) = c;
    }
    else
    {
      /* reverse translation of the new left bound */
      rp_interval_mul_r_i(offset,step,RP_INTERVAL_2_PI);
      RP_ROUND_DOWNWARD();
      rp_binf(ynew) = c + rp_bsup(offset);
    }
  }

  /* translation of the right bound in dest */
  bound = rp_interval_translate(rp_bsup(y),dest,RP_ROUND_VALUE_UP,step,offset);

  /* if the right bound is in u=sin-1(x) then no reduction */
  if (rp_union_contains(u,bound))
  {
    rp_bsup(ynew) = rp_bsup(y);
  }
  else
  {
    double c;
    if (rp_union_strictly_smaller(u,bound))  /* bound:  |                      */
    {                                        /* u:         |------|    |-----| */
                                             /* c:=                 (-2Pi) + ^ */
      /* new bound in bsup(u) - 2Pi and (- 2Pi) is handled as (step -= 1) */
      rp_interval one, aux;
      c = rp_union_bsup(u);
      rp_interval_set_point(one,1.0);
      rp_interval_copy(aux,step);
      rp_interval_sub_i_r(step,aux,one);
    }
    else                                    /* u:         |------|    |-----| */
    {                                       /* bound:               |         */
      c = rp_union_prev_double(u,bound);    /* c :=              ^            */
    }

    if( rp_binf(step)==0.0 )
    {
      rp_bsup(ynew) = c;
    }
    else
    {
      /* reverse translation of the new right bound */
      rp_interval_mul_r_i(offset,step,RP_INTERVAL_2_PI);
      RP_ROUND_UPWARD();
      rp_bsup(ynew) = c + rp_bsup(offset);
    }
  }
  rp_union_destroy(&u);
  return( !(rp_interval_empty(ynew)) );
}

/* x = cos(y) => xnew := hull ( cos(y) inter x ) */

int rp_project_cos_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_cos(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = cos(y) => ynew := hull ( cos-1(x) inter y ) */

int rp_project_cos_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  /* jnew := sin-1(x), jnew in j = y + Pi/2 */
  /* ynew := jnew - Pi/2 */
  rp_interval j, jnew;
  rp_interval_add(j,y,RP_INTERVAL_1_PI_2);
  if (rp_project_sin_fst(jnew,x,j))
  {
    rp_interval_sub(ynew,jnew,RP_INTERVAL_1_PI_2);
  }
  else
  {
    rp_interval_set_empty(ynew);
  }
  return( !(rp_interval_empty(ynew)) );
}

/* x = tan(y) => xnew := hull ( tan(y) inter x ) */

int rp_project_tan_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_tan(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = tan(y) => ynew := hull ( tan-1(x) inter y ) */

int rp_project_tan_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval atan, offset, step, dest;
  double bound;

  /* computation of tan-1(x) in [-pi/2,+pi/2] => atan */
  rp_interval_atan(atan,x);

  rp_interval_set(dest,-rp_bsup(RP_INTERVAL_1_PI_2),rp_bsup(RP_INTERVAL_1_PI_2));

  /* translation of the left bound in dest */
  bound = rp_interval_translate(rp_binf(y),dest,RP_ROUND_VALUE_DOWN,step,offset);

  /* if the left bound is in tan-1(x) then no reduction */
  if (rp_interval_contains(atan,bound))
  {
    rp_binf(ynew) = rp_binf(y);
  }
  else
  {
    if (bound > rp_binf(atan))           /* bound:                  |   */
    {                                    /*  atan:        |------|      */
                                         /* new bound:=   ^ + Pi        */
      /* new bound in binf(atan)+Pi and (+Pi) is handled as (step += 1) */
      rp_interval one, aux;
      rp_interval_set_point(one,1.0);
      rp_interval_copy(aux,step);
      rp_interval_add_r_i(step,one,aux);
    }

    if( rp_binf(step)==0.0 )
    {
      rp_binf(ynew) = rp_binf(atan);
    }
    else
    {
      /* reverse translation of the new left bound */
      rp_interval_mul_r_i(offset,step,RP_INTERVAL_PI);
      RP_ROUND_DOWNWARD();
      rp_binf(ynew) = rp_binf(atan) + rp_bsup(offset);
    }
  }

  /* translation of the right bound in dest */
  bound = rp_interval_translate(rp_bsup(y),dest,RP_ROUND_VALUE_UP,step,offset);

  /* if the right bound is in tan-1(x) then no reduction */
  if (rp_interval_contains(atan,bound))
  {
    rp_bsup(ynew) = rp_bsup(y);
  }
  else
  {
    if (bound < rp_binf(atan))               /* bound:        |            */
    {                                        /* atan:              |-----| */
                                             /* new bound:=      (-Pi) + ^ */
      /* new bound in bsup(atan)-Pi and (-Pi) is handled as (step -= 1)    */
      rp_interval one, aux;
      rp_interval_set_point(one,1.0);
      rp_interval_copy(aux,step);
      rp_interval_sub_i_r(step,aux,one);
    }

    if( rp_binf(step)==0.0 )
    {
      rp_bsup(ynew) = rp_bsup(atan);
    }
    else
    {
      /* reverse translation of the new right bound */
      rp_interval_mul_r_i(offset,step,RP_INTERVAL_PI);
      RP_ROUND_UPWARD();
      rp_bsup(ynew) = rp_bsup(atan) + rp_bsup(offset);
    }
  }
  return( !(rp_interval_empty(ynew)) );
}

/* x = cosh(y) => xnew := hull ( cosh(y) inter x ) */

int rp_project_cosh_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_cosh(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = cosh(y) => ynew := hull ( cosh-1(x) inter y ) */

int rp_project_cosh_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  if( rp_interval_contains(x,1.0) )
  {
    /* ex. x = cosh(y), x in [0,5], then y in [-acosh(5),acosh(5)] */
    rp_interval aux;
    RP_ROUND_UPWARD();
    rp_bsup(aux) = acosh(rp_bsup(x));
    rp_binf(aux) = -rp_bsup(aux);
    rp_interval_inter(ynew,aux,y);
  }
  else if( rp_binf(x)>1.0 )
  {
    /* ex. x = cosh(y), x in [2,3], then
       y in [-acosh(3),-acosh(2)] union [acosh(2),acosh(3)] */
    rp_interval aux1, aux2;
    rp_union_interval aux;
    RP_ROUND_DOWNWARD();
    rp_binf(aux2) = acosh(rp_binf(x));
    RP_ROUND_UPWARD();
    rp_bsup(aux2) = acosh(rp_bsup(x));
    rp_binf(aux1) = -rp_bsup(aux2);
    rp_bsup(aux1) = -rp_binf(aux2);
    rp_union_create_size(&aux,2);
    rp_union_insert(aux,aux1);
    rp_union_insert(aux,aux2);
    rp_union_inter(aux,y);
    rp_union_hull(ynew,aux);
    rp_union_destroy(&aux);
  }
  else
  {
    /* empty */
    rp_interval_set_empty(ynew);
  }
  return( !(rp_interval_empty(ynew)) );
}

/* x = sinh(y) => xnew := hull ( sinh(y) inter x ) */

int rp_project_sinh_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_sinh(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = sinh(y) => ynew := hull ( asinh(x) inter y ) */

int rp_project_sinh_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_asinh(aux,x);
  rp_interval_inter(ynew,aux,y);
  return( !(rp_interval_empty(ynew)) );
}

/* x = tanh(y) => xnew := hull ( tanh(y) inter x ) */

int rp_project_tanh_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_tanh(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = tanh(y) => ynew := hull ( atanh(x) inter y ) */

int rp_project_tanh_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_atanh(aux,x);
  rp_interval_inter(ynew,aux,y);
  return( !(rp_interval_empty(ynew)) );
}

/* x = acos(y) => xnew := hull ( acos(y) inter x ) */

int rp_project_acos_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_acos(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = acos(y) => ynew := hull ( cos(x inter [0,Pi]) inter y ) */

int rp_project_acos_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval dom, aux, cos;
  rp_interval_set(dom,0.0,rp_bsup(RP_INTERVAL_PI));
  rp_interval_inter(aux,dom,x);
  if (rp_interval_empty(aux))
  {
    rp_interval_set_empty(ynew);
  }
  else
  {
    rp_interval_cos(cos,aux);
    rp_interval_inter(ynew,cos,y);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = asin(y) => xnew := hull ( asin(y) inter x ) */

int rp_project_asin_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_asin(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = asin(y) => ynew := hull ( sin(x inter [-Pi/2,Pi/2]) inter y ) */

int rp_project_asin_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval dom, aux, sin;
  rp_interval_set(dom,-rp_bsup(RP_INTERVAL_1_PI_2),rp_bsup(RP_INTERVAL_1_PI_2));
  rp_interval_inter(aux,dom,x);
  if (rp_interval_empty(aux))
  {
    rp_interval_set_empty(ynew);
  }
  else
  {
    rp_interval_sin(sin,aux);
    rp_interval_inter(ynew,sin,y);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = atan(y) => xnew := hull ( atan(y) inter x ) */

int rp_project_atan_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_atan(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = atan(y) => ynew := hull ( tan(x inter [-Pi/2,Pi/2]) inter y ) */

int rp_project_atan_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval dom, aux, tan;
  rp_interval_set(dom,-rp_bsup(RP_INTERVAL_1_PI_2),rp_bsup(RP_INTERVAL_1_PI_2));
  rp_interval_inter(aux,dom,x);
  if (rp_interval_empty(aux))
  {
    rp_interval_set_empty(ynew);
  }
  else
  {
    rp_interval_tan(tan,aux);
    rp_interval_inter(ynew,tan,y);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = asinh(y) => xnew := hull ( asinh(y) inter x ) */

int rp_project_asinh_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_asinh(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = asinh(y) => ynew := hull ( sinh(x) inter y ) */

int rp_project_asinh_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_sinh(aux,x);
  rp_interval_inter(ynew,aux,y);
  return( !rp_interval_empty(ynew) );
}

/* x = acosh(y) => xnew := hull ( acosh(y) inter x ) */

int rp_project_acosh_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_acosh(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = acosh(y) => ynew := hull ( cosh(x inter R+]) inter y ) */

int rp_project_acosh_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval dom, aux, cosh;
  rp_interval_set(dom,0.0,RP_INFINITY);
  rp_interval_inter(aux,dom,x);
  if (rp_interval_empty(aux))
  {
    rp_interval_set_empty(ynew);
  }
  else
  {
    rp_interval_cosh(cosh,aux);
    rp_interval_inter(ynew,cosh,y);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = atanh(y) => xnew := hull ( atanh(y) inter x ) */

int rp_project_atanh_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_atanh(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = atanh(y) => ynew := hull ( tanh(x) inter y ) */

int rp_project_atanh_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_tanh(aux,x);
  rp_interval_inter(ynew,aux,y);
  return( !rp_interval_empty(ynew) );
}

/* x = abs(y) => xnew := hull ( abs(y) inter x ) */

int rp_project_abs_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  rp_interval aux;
  rp_interval_abs(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = abs(y) => ynew := hull ( abs-1(x) inter y ) */

int rp_project_abs_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  if( rp_interval_contains(x,0.0) )
  {
    /* ex. x = abs(y), x in [-1,5], then y in [-5,5] */
    rp_interval aux;
    rp_binf(aux) = -rp_bsup(x);
    rp_bsup(aux) = rp_bsup(x);
    rp_interval_inter(ynew,aux,y);
  }
  else if( rp_binf(x)>0.0 )
  {
    /* ex. x = abs(y), x in [2,3], then y in [-3,-2] union [2,3] */
    rp_interval aux1, aux2;
    rp_union_interval aux;
    rp_binf(aux1) = -rp_bsup(x);
    rp_bsup(aux1) = -rp_binf(x);
    rp_binf(aux2) = rp_binf(x);
    rp_bsup(aux2) = rp_bsup(x);
    rp_union_create_size(&aux,2);
    rp_union_insert(aux,aux1);
    rp_union_insert(aux,aux2);
    rp_union_inter(aux,y);
    rp_union_hull(ynew,aux);
    rp_union_destroy(&aux);
  }
  else
  {
    /* empty */
    rp_interval_set_empty(ynew);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = matan(y) => xnew := hull ( matan(y) inter x ) */

int rp_project_matan_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  /* TODO */
  rp_interval aux;
  rp_interval_matan(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = matan(y) => ynew := hull ( tan(x inter [-Pi/2,Pi/2]) inter y ) */

int rp_project_matan_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  /* TODO */
  rp_interval dom, aux, tan;
  rp_interval_set(dom,-rp_bsup(RP_INTERVAL_1_PI_2),rp_bsup(RP_INTERVAL_1_PI_2));
  rp_interval_inter(aux,dom,x);
  if (rp_interval_empty(aux))
  {
    rp_interval_set_empty(ynew);
  }
  else
  {
    rp_interval_tan(tan,aux);
    rp_interval_inter(ynew,tan,y);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = safesqrt(y) => xnew := hull ( safesqrt(y) inter x ) */

int rp_project_safesqrt_zro (rp_interval xnew, rp_interval x, rp_interval y)
{
  /* TODO */
  rp_interval aux;
  rp_interval_safesqrt(aux,y);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = safesqrt(y) => ynew := hull ( tan(x inter [-Pi/2,Pi/2]) inter y ) */

int rp_project_safesqrt_fst (rp_interval ynew, rp_interval x, rp_interval y)
{
  /* TODO */
  rp_interval dom, aux, tan;
  rp_interval_set(dom,-rp_bsup(RP_INTERVAL_1_PI_2),rp_bsup(RP_INTERVAL_1_PI_2));
  rp_interval_inter(aux,dom,x);
  if (rp_interval_empty(aux))
  {
    rp_interval_set_empty(ynew);
  }
  else
  {
    rp_interval_tan(tan,aux);
    rp_interval_inter(ynew,tan,y);
  }
  return( !rp_interval_empty(ynew) );
}

/* x = pow(y,n) => xnew := hull ( pow(y,n) inter x ) */

int rp_project_atan2_zro (rp_interval xnew, rp_interval x, rp_interval y,
			  rp_interval n)
{
  /* TODO */
  rp_interval aux;
  rp_interval_pow(aux,y,n);
  rp_interval_inter(xnew,aux,x);
  return( !rp_interval_empty(xnew) );
}

/* x = pow(y,n) => ynew := hull ( pow-1(x,n) inter y ) */

int rp_project_atan2_fst (rp_interval ynew, rp_interval x, rp_interval y,
  			  rp_interval n)
{
  /* TODO */
  rp_interval aux1, aux2;
  rp_union_interval aux;
  int exp = (int)rp_binf(n);
  if( rp_odd(exp) )
  {
    rp_interval_nthroot(aux1,x,n);
    rp_interval_inter(ynew,aux1,y);
  }
  else
  {
    if( rp_interval_contains(x,0.0) )
    {
      rp_interval_nthroot(aux1,x,n);
      rp_interval_inter(ynew,aux1,y);
    }
    else if( rp_binf(x)>0.0 )
    {
      rp_interval_nthroot(aux1,x,n);
      rp_interval_neg(aux2,aux1);
      rp_union_create_size(&aux,2);
      rp_union_insert(aux,aux1);
      rp_union_insert(aux,aux2);
      rp_union_inter(aux,y);
      rp_union_hull(ynew,aux);
      rp_union_destroy(&aux);
    }
    else
    {
      rp_interval_set_empty(ynew);
    }
  }
  return( !rp_interval_empty(ynew) );
}

/* x = pow(y,n) => ynew := hull ( pow-1(x,n) inter y ) */

int rp_project_atan2_snd (rp_interval ynew, rp_interval x, rp_interval y,
  			  rp_interval n)
{
  /* TODO */
  rp_interval aux1, aux2;
  rp_union_interval aux;
  int exp = (int)rp_binf(n);
  if( rp_odd(exp) )
  {
    rp_interval_nthroot(aux1,x,n);
    rp_interval_inter(ynew,aux1,y);
  }
  else
  {
    if( rp_interval_contains(x,0.0) )
    {
      rp_interval_nthroot(aux1,x,n);
      rp_interval_inter(ynew,aux1,y);
    }
    else if( rp_binf(x)>0.0 )
    {
      rp_interval_nthroot(aux1,x,n);
      rp_interval_neg(aux2,aux1);
      rp_union_create_size(&aux,2);
      rp_union_insert(aux,aux1);
      rp_union_insert(aux,aux2);
      rp_union_inter(aux,y);
      rp_union_hull(ynew,aux);
      rp_union_destroy(&aux);
    }
    else
    {
      rp_interval_set_empty(ynew);
    }
  }
  return( !rp_interval_empty(ynew) );
}
