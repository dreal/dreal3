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
 * rp_float.c                                                               *
 ****************************************************************************/

#include "rp_float.h"

/*
static double rp_pow_iter(double xx, int nn)
{
  double y = xx, z = 1.0;
  for( ;; )
  {
    if( rp_odd(nn) )
    {
      z *= y;
      nn >>= 1;
      if( nn==0 ) return( z );
    }
    else nn >>= 1;
    y *= y;
  }
}
*/

/* Returns x to the power of n with n>=1 */
double rp_pow(double x, int n, int round)
{
  if (x==0.0)
  {
    return( 0.0 );
  }
  else if (x==1.0)
  {
    return( 1.0 );
  }
  else if (x>0.0)
  {
    /* rounddown(5^n) = round down and then return 5^n */
    /* roundup  (5^n) = round up   and then return 5^n */

    if (round==RP_ROUND_VALUE_DOWN)
    {
      RP_ROUND_DOWNWARD();
    }
    else
    {
      RP_ROUND_UPWARD();
    }

    /* return( rp_pow_iter(x,n) );*/
    {
      double y = x, z = 1.0;
      int nn = n;
      for( ;; )
      {
	if( rp_odd(nn) )
	{
	  z *= y;
	  nn >>= 1;
	  if( nn==0 ) return( z );
	}
	else nn >>= 1;
	y *= y;
      }
    }
  }
  else  /* x<0.0 */
  {
    if (rp_even(n))
    {
      /* rounddown((-5)^n) = round down and then return 5^n */
      /* roundup  ((-5)^n) = round up   and then return 5^n */
      if (round==RP_ROUND_VALUE_DOWN)
      {
        RP_ROUND_DOWNWARD();
      }
      else
      {
        RP_ROUND_UPWARD();
      }
      /* return( rp_pow_iter((-x),n) ); */
      {
	double y = -x, z = 1.0;
	int nn = n;
	for( ;; )
	{
	  if( rp_odd(nn) )
	  {
	    z *= y;
	    nn >>= 1;
	    if( nn==0 ) return( z );
	  }
	  else nn >>= 1;
	  y *= y;
	}
      }
    }
    else  /* rp_odd(n) */
    {
      /* rounddown((-5)^n) = round up   and then return -(5^n) */
      /* roundup  ((-5)^n) = round down and then return -(5^n) */
      if (round==RP_ROUND_VALUE_DOWN)
      {
        RP_ROUND_UPWARD();
      }
      else
      {
        RP_ROUND_DOWNWARD();
      }
      /* return( -(rp_pow_iter((-x),n)) ); */
      {
	double y = -x, z = 1.0;
	int nn = n;
	for( ;; )
	{
	  if( rp_odd(nn) )
	  {
	    z *= y;
	    nn >>= 1;
	    if( nn==0 ) return( -z );
	  }
	  else nn >>= 1;
	  y *= y;
	}
      }
    }
  }
}

/* Returns p := x+(n/h)(y-x) in (x,y) if [x,y] is not empty and not canonical */
double rp_split_point(double x, double y, int h, int n)
{
  double a = rp_max_num(x,RP_MIN_DOUBLE),
         b = rp_min_num(y,RP_MAX_DOUBLE);

  if (a==b)   /* [r,r] || [-oo,MinReal] || [MaxReal,+oo] */
  {    
    return a;
  }
  else if (b==rp_next_double(a))   /* [r,r+] || [-oo,succ MinReal] */
  {                                       /* || [pred MaxReal,+oo] */
    if (x==(-RP_INFINITY))
    {
      return RP_MIN_DOUBLE;
    }
    else if (y==RP_INFINITY)
    {
      return RP_MAX_DOUBLE;
    }
    else
    {
      return a;
    }
  }
  else                             /* [r,s] with s > r+ */
  {
    double div = ((double)n)/((double)h);
    double c = a*(1.0-div) + b*div;
    if ((c>a) && (c<b))
    {
      return c;
    }
    else
    {
      return rp_next_double(a);
    }
  }
}
