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
 * rp_interval.c                                                            *
 ****************************************************************************/

#include <string.h>
#include <ctype.h>
#include "rp_interval.h"

extern int atoi(const char *) rp_throw;
extern double trunc(double) rp_throw;

/* specific interval values */
rp_interval RP_INTERVAL_PI;
rp_interval RP_INTERVAL_2_PI;
rp_interval RP_INTERVAL_4_PI;
rp_interval RP_INTERVAL_1_PI_2;
rp_interval RP_INTERVAL_3_PI_2;
rp_interval RP_INTERVAL_5_PI_2;
rp_interval RP_INTERVAL_7_PI_2;


/* Returns true if i==j when their bounds are truncated at n digits */
int rp_interval_equal_digits (rp_interval i, rp_interval j, int n)
{
  int k;
  rp_interval i2, j2;
  double factor = 1.0;
  if (n<0)
  {
    return( rp_interval_equal(i,j) );
  }
  for (k=0; k<n; ++k) factor *= 10.0;
  rp_binf(i2) = trunc(rp_binf(i)*factor) / factor;
  rp_bsup(i2) = trunc(rp_bsup(i)*factor) / factor;
  rp_binf(j2) = trunc(rp_binf(j)*factor) / factor;
  rp_bsup(j2) = trunc(rp_bsup(j)*factor) / factor;
  return( rp_interval_equal(i2,j2) );
}

/* i = [a,d] -->  i := [ceil(a),floor(b)] */
/* Only for bounds within [LONG_MIN,LONG_MAX] for safety reasons */
void rp_interval_trunc(rp_interval i)
{
  if ( (rp_binf(i)>=(double)RP_MIN_LONG) &&
       (rp_binf(i)<=(double)RP_MAX_LONG) )
  {
    rp_binf(i) = ceil(rp_binf(i));
  }
  if ( (rp_bsup(i)>=(double)RP_MIN_LONG) &&
       (rp_bsup(i)<=(double)RP_MAX_LONG) )
  {
    rp_bsup(i) = floor(rp_bsup(i));
  }
}

/* Conversion from a string representing an 'unsigned' float to an interval
*  Correctly rounded version of atof(s)
*
*  Algorithm : ex. 1.157e-5  => 1157 / 10**2
*  - The integer part (1157) is converted as follows:
*         7 + 10*( 5 + 10( 1 + 10*( 1 ) ) )  using interval operations
*  - The exponent is computed as the exponent (if specified) minus
*    the number of decimals, here -5 - 3 => -8
*  - The quantity 10^|exponent| is evaluated using interval operations
*    here, 10^8 => 100000000
*  - If exponent<0, the result is (integer_part / 10^|exponent|)
*    Otherwise (integer_part * 10^|exponent|)
*  => here 1157 / 100000000
*/
void rp_interval_from_str(char* s, rp_interval i)
{
  int i_s = 0,
      i_conv = 0,
      ndecimals = 0,
      j, expo, expoabs, dig;
  char conv[100];
  rp_interval ten, exponent, digit, intpart;

  /* extraction of the integer part */
  while( isdigit(s[i_s]) )
  {
    conv[i_conv++]=s[i_s++];
  }
  /* extraction of the decimal part */
  if( s[i_s]=='.' )
  {
    ++i_s;
    while( isdigit(s[i_s]) )
    {
      conv[i_conv++]=s[i_s++];
      ++ndecimals;
    }
  }
  conv[i_conv] = '\0';

  if( i_s<(int)strlen(s) )
  {
    /* extraction of the exponent part */
    ++i_s;  /* e/E */
    expo = atoi(&(s[i_s]));
  }
  else
  {
    expo = 0;
  }
  expo -= ndecimals;

  rp_interval_set(ten,10.0,10.0);

  /* computation of the integer part */
  rp_interval_set(intpart,0.0,0.0);
  for( j=0; j<(int)strlen(conv); ++j )
  {
    dig = (int)(conv[j] - '0');
    rp_interval_set(digit,dig,dig);
    rp_interval_mul_rpos_i(intpart,ten,intpart);
    rp_interval_add_r_i(intpart,digit,intpart);
  }

  /* computation of 10^|expo| */
  if( expo!=0 )
  {
    rp_interval_set(exponent,1.0,1.0);
    expoabs = ((expo<0) ? (-expo) : expo);
    for( j=0; j<expoabs; ++j )
    {
      rp_interval_mul_rpos_i(exponent,ten,exponent);
    }
  }

  if( expo<0 )
  {
    rp_interval_div(i,intpart,exponent);
  }
  else if( expo>0 )
  {
    rp_interval_mul(i,intpart,exponent);
  }
  else
  {
    rp_interval_copy(i,intpart);
  }
}

/* Display i on out                               */
/* mode == RP_INTERVAL_MODE_BOUND -> [a,b]        */
/* mode == RP_INTERVAL_MODE_MID   -> mid +- error */
void rp_interval_display(FILE *out, rp_interval i, int digits, int mode)
{
  char tmp[255];
  rp_interval_print(tmp,i,digits,mode);
  fprintf(out,"%s",tmp);
}

/* Print i in out */
void rp_interval_print(char * out, rp_interval i, int digits, int mode)
{
  double mid, minerror, maxerror;
  if( rp_interval_empty(i) )
  {
    sprintf(out,"empty");
    return;
  }
  if( rp_interval_point(i) )
  {
    if( rp_binf(i)>=0 )
    {
      sprintf(out,"%.*g",digits,rp_binf(i));
    }
    else
    {
      sprintf(out,"%+.*g",digits,rp_binf(i));
    }
  }
  else
  {
    if( mode==RP_INTERVAL_MODE_BOUND )
    {
      if( rp_binf(i)>=0 )
      {
	if (rp_binf(i)==0)
	{
	  sprintf(out,"[0%s",RP_INTERVAL_SEPARATOR);
	}
	else
	{
	  RP_ROUND_DOWNWARD();
	  sprintf(out,"[%.*g%s",digits,rp_binf(i),RP_INTERVAL_SEPARATOR);
	}
        RP_ROUND_UPWARD();
        if( rp_bsup(i)==RP_INFINITY )
	{
	  strcat(out,"+oo)");
	}
        else
	{
	  char tmp[255];
	  sprintf(tmp,"%.*g]",digits,rp_bsup(i));
	  strcat(out,tmp);
	}
      }
      else
      {
        RP_ROUND_DOWNWARD();
	if( rp_binf(i)==(-RP_INFINITY) )
	{
	  sprintf(out,"(-oo%s",RP_INTERVAL_SEPARATOR);
	}
        else
	{
	  sprintf(out,"[%+.*g%s",digits,rp_binf(i),RP_INTERVAL_SEPARATOR);
	}
        RP_ROUND_UPWARD();
        if( rp_bsup(i)==RP_INFINITY )
	{
	  strcat(out,"+oo)");
	}
        else
	{
	  if (rp_bsup(i)==0)
	  {
	    strcat(out,"0]");
	  }
	  else
	  {
	    char tmp[255];
	    sprintf(tmp,"%+.*g]",digits,rp_bsup(i));
	    strcat(out,tmp);
	  }
	}
      }
    }
    else
    {
      if( (rp_binf(i)==(-RP_INFINITY)) && (rp_bsup(i)==RP_INFINITY) )
      {
        sprintf(out,"0.0+(-oo%s+oo)",RP_INTERVAL_SEPARATOR);
        return;
      }
      if( rp_binf(i)==(-RP_INFINITY) )
      {
        RP_ROUND_DOWNWARD();
	mid = rp_split_center(RP_MIN_DOUBLE,rp_bsup(i));
        minerror = -RP_INFINITY;
        RP_ROUND_UPWARD();
        maxerror = rp_bsup(i) - mid;
      }
      else if( rp_bsup(i)==RP_INFINITY )
      {
        RP_ROUND_DOWNWARD();
	mid = rp_split_center(rp_binf(i),RP_MAX_DOUBLE);
        minerror = rp_binf(i) - mid;
        RP_ROUND_UPWARD();
        maxerror = RP_INFINITY;
      }
      else
      {
        RP_ROUND_DOWNWARD();
	mid = rp_interval_midpoint(i);
        minerror = rp_binf(i) - mid;
        RP_ROUND_UPWARD();
        maxerror = rp_bsup(i) - mid;
      }

      if( mid>=0 )
      {
	sprintf(out,"%.*g+",digits,mid);
      }
      else
      {
	sprintf(out,"%+.*g+",digits,mid);
      }
      if( minerror==(-RP_INFINITY) )
      {
	char tmp[255];
        sprintf(tmp,"(-oo%s%+.4g]",RP_INTERVAL_SEPARATOR,maxerror);
	strcat(out,tmp);
      }
      else if( maxerror==RP_INFINITY )
      {
	char tmp[255];
        RP_ROUND_DOWNWARD();
        sprintf(tmp,"[%+.4g%s+oo)",minerror,RP_INTERVAL_SEPARATOR);
	strcat(out,tmp);
      }
      else
      {
	char tmp[255];
        RP_ROUND_DOWNWARD();
        sprintf(tmp,"[%+.4g%s",minerror,RP_INTERVAL_SEPARATOR);
	strcat(out,tmp);
        RP_ROUND_UPWARD();
        sprintf(tmp,"%+.4g]",maxerror);
	strcat(out,tmp);
      }
    }
  }
}

/* Returns x - offset in dest=[a,b], offset := step*(b-a), step integer */
double rp_interval_translate(double x, rp_interval dest, int rounding,
			     rp_interval step, rp_interval offset)
{
  /* a <= x-step*(b-a) <= b  =>  (x-a)/(b-a) >= step >= (x-b)/(b-a) */
  /* step := 1 + floor( (x-b)/(b-a) ) the smallest integer          */
  /* greater than (x-b)/(b-a)                                       */

  if (rp_interval_contains(dest,x))
  {
    rp_interval_set_point(step,0.0);
    rp_interval_set_point(offset,0.0);
    return x;
  }
  else
  {
    rp_interval wdest, xi, bi, aux1, aux2;
    double bound;
    RP_ROUND_DOWNWARD();
    rp_binf(wdest) = rp_bsup(dest) - rp_binf(dest);
    RP_ROUND_UPWARD();
    rp_bsup(wdest) = rp_bsup(dest) - rp_binf(dest);
    rp_interval_set_point(xi,x);
    rp_interval_set_point(bi,rp_bsup(dest));

    /* (x-b)/(b-a) must be rounded downward since step >= (x-b)/(b-a) */
    rp_interval_sub(aux1,xi,bi);      /* aux1 := x - b */
    rp_interval_div(aux2,aux1,wdest); /* aux2 := (x-b)/(b-a) */

    rp_interval_set_point(step,1.0+floor(rp_binf(aux2)));
    rp_interval_mul_r_i(offset,step,wdest);

    rp_interval_sub(aux1,xi,offset);
    if (rounding==RP_ROUND_VALUE_DOWN)
    {
      bound = rp_binf(aux1);
    }
    else
    {
      bound = rp_bsup(aux1);
    }

    if (bound < rp_binf(dest))
    {
      return rp_binf(dest);
    }
    else if (bound > rp_bsup(dest))
    {
      return rp_bsup(dest);
    }
    else
    {
      return bound;
    }
  }
}

/* result := i1 + i2 */
void rp_interval_add(rp_interval result, rp_interval i1, rp_interval i2)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = rp_binf(i1) + rp_binf(i2);
  RP_ROUND_UPWARD();
  rp_bsup(result) = rp_bsup(i1) + rp_bsup(i2);
}

/* let x=[r,r], result := [r,r] + i */
void rp_interval_add_r_i(rp_interval result, rp_interval x, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = rp_binf(x) + rp_binf(i);
  RP_ROUND_UPWARD();
  rp_bsup(result) = rp_bsup(x) + rp_bsup(i);
}

/* result := i1 - i2 */
void rp_interval_sub(rp_interval result, rp_interval i1, rp_interval i2)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = rp_binf(i1) - rp_bsup(i2);
  RP_ROUND_UPWARD();
  rp_bsup(result) = rp_bsup(i1) - rp_binf(i2);
}

/* let x=[r,r], result := [r,r] - i */
void rp_interval_sub_r_i(rp_interval result, rp_interval x, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = rp_binf(x) - rp_bsup(i);
  RP_ROUND_UPWARD();
  rp_bsup(result) = rp_bsup(x) - rp_binf(i);
}

/* let x=[r,r], result := i - [r,r] */
void rp_interval_sub_i_r(rp_interval result, rp_interval i, rp_interval x)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = rp_binf(i) - rp_bsup(x);
  RP_ROUND_UPWARD();
  rp_bsup(result) = rp_bsup(i) - rp_binf(x);
}

/* result := -i */
void rp_interval_neg(rp_interval result, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = -(rp_bsup(i));
  RP_ROUND_UPWARD();
  rp_bsup(result) = -(rp_binf(i));
}

/* result := i1*i2 */
void rp_interval_mul(rp_interval result, rp_interval i1, rp_interval i2)
{
  unsigned int sig = ((rp_bsup(i1)<0.0) << 3) | ((rp_binf(i1)>0.0) << 2)
                   | ((rp_bsup(i2)<0.0) << 1) | (rp_binf(i2)>0.0);

  double l1, l2, u1, u2;
  switch( sig )
  {
    case 0: /* 0000: 0 in i1, 0 in i2 */
      /* The problem is to avoid multiplications 0*oo */
      if( rp_interval_zero(i1) || rp_interval_zero(i2) )
      {
        rp_interval_set(result,0.0,0.0);
      }
      else if( (rp_interval_infinite(i1) && rp_interval_bound_zero(i2)) ||
	       (rp_interval_infinite(i2) && rp_interval_bound_zero(i1)) )
      {
	rp_interval x, y;
	/* x := the infinite one and y := the other one */
	if (rp_interval_infinite(i1))
	{
	  rp_interval_copy(x,i1);
	  rp_interval_copy(y,i2);
	}
        else
	{
	  rp_interval_copy(x,i2);
	  rp_interval_copy(y,i1);
	}

	if (rp_binf(x)==(-RP_INFINITY))
	{
	  if (rp_bsup(x)==RP_INFINITY)  /* [-oo,+oo]*y=[-oo,+oo] */
	  {
	    rp_interval_set_real_line(result);
	  }
	  else if (rp_bsup(x)==0.0) /* x = [-oo,0] */
	  {
	    if (rp_binf(y)==0.0)    /* [-oo,0]*[0,b] = [-oo,0] */
	    {
	      rp_interval_set(result,(-RP_INFINITY),0.0);
	    }
            else                    /* [-oo,0]*[a,0] = [0,+oo] */
	    {
	      rp_interval_set(result,0.0,RP_INFINITY);
	    }
	  }
          else                      /* x = [-oo,b], +oo>b>0 */
	  {
	    if (rp_interval_infinite(y))  /* [-oo,b]*[0,+oo]=[-oo,+oo]*/
	    {                             /* [-oo,b]*[-oo,0]=[-oo,+oo]*/
	      rp_interval_set_real_line(result);
	    }
	    else
	    {
	      if (rp_bsup(y)==0.0)  /* [-oo,b]*[a,0]=[a*b,+oo] */
	      {
                RP_ROUND_DOWNWARD();
		rp_interval_set(result,rp_bsup(x)*rp_binf(y),RP_INFINITY);
	      }
	      else                  /* [-oo,b]*[0,c]=[-oo,b*c] */
	      {
                RP_ROUND_UPWARD();
		rp_interval_set(result,(-RP_INFINITY),rp_bsup(x)*rp_bsup(y));
	      }
	    }
	  }
	}
	else    /* x=[a,+oo], -oo<a<0 */
	{
	  if (rp_binf(x)==0.0)    /* x = [0,+oo] */
	  {
	    if (rp_bsup(y)==0.0)  /* [0,+oo]*[a,0]=[-oo,0] */
	    {
	      rp_interval_set(result,(-RP_INFINITY),0.0);
	    }
	    else                  /* [0,+oo]*[0,a]=[0,+oo] */
	    {
	      rp_interval_set(result,0.0,RP_INFINITY);
	    }
	  }
	  else                    /* x = [a,+oo], a<0 */
	  {
	    if (rp_interval_infinite(y))  /* [a,+oo]*[0,+oo]=[-oo,+oo]*/
	    {                             /* [a,+oo]*[-oo,0]=[-oo,+oo]*/
	      rp_interval_set_real_line(result);
	    }
	    else
	    {
	      if (rp_bsup(y)==0.0) /* [a,+oo]*[d,0]=[-oo,a*d]*/
	      {
                RP_ROUND_UPWARD();
	        rp_interval_set(result,(-RP_INFINITY),rp_binf(x)*rp_binf(y));
	      }
	      else                 /* [a,+oo]*[0,b]=[a*b,+oo]*/
	      {
                RP_ROUND_DOWNWARD();
	        rp_interval_set(result,rp_binf(x)*rp_bsup(y),RP_INFINITY);
	      }
	    }
	  }
	}
      }
      else
      {
        RP_ROUND_DOWNWARD();
        l1=rp_binf(i1)*rp_bsup(i2);
        l2=rp_bsup(i1)*rp_binf(i2);

        RP_ROUND_UPWARD();
        u1=rp_binf(i1)*rp_binf(i2);
        u2=rp_bsup(i1)*rp_bsup(i2);

        rp_binf(result) = rp_min_num(l1,l2);
        rp_bsup(result) = rp_max_num(u1,u2);
      }
    break;

    case 1: /* 0001: 0 in i1, i2>0 */
      if (rp_bsup(i2)==RP_INFINITY)
      {
        if( rp_binf(i1)==0.0 )
        {
          rp_interval_set(result,0.0,RP_INFINITY);
	}
        else if ( rp_bsup(i1)==0.0 )
        {
          rp_interval_set(result,(-RP_INFINITY),0.0);
	}
        else
        {
	  rp_interval_set_real_line(result);
	}
      }
      else
      {
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_binf(i1)*rp_bsup(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_bsup(i1)*rp_bsup(i2);
      }
    break;

    case 2: /* 0010: 0 in i1, i2<0 */
      if (rp_binf(i2)==(-RP_INFINITY))
      {
        if( rp_binf(i1)==0.0 )
        {
          rp_interval_set(result,(-RP_INFINITY),0.0);
	}
        else if ( rp_bsup(i1)==0.0 )
        {
          rp_interval_set(result,0.0,RP_INFINITY);
	}
        else
        {
  	  rp_interval_set_real_line(result);
	}
      }
      else
      {
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_bsup(i1)*rp_binf(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_binf(i1)*rp_binf(i2);
      }
    break;

    case 4: /* 0100: i1>0, 0 in i2 */
      if (rp_bsup(i1)==RP_INFINITY)
      {
        if( rp_binf(i2)==0.0 )
        {
          rp_interval_set(result,0.0,RP_INFINITY);
	}
        else if ( rp_bsup(i2)==0.0 )
        {
          rp_interval_set(result,(-RP_INFINITY),0.0);
	}
        else
        {
	  rp_interval_set_real_line(result);
	}
      }
      else
      {
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_bsup(i1)*rp_binf(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_bsup(i1)*rp_bsup(i2);
      }
    break;

    case 5: /* 0101: i1>0, i2>0 */
      RP_ROUND_DOWNWARD();
      rp_binf(result)=rp_binf(i1)*rp_binf(i2);
      RP_ROUND_UPWARD();
      rp_bsup(result)=rp_bsup(i1)*rp_bsup(i2);
    break;

    case 6: /* 0110: i1>0, i2<0 */
      RP_ROUND_DOWNWARD();
      rp_binf(result)=rp_bsup(i1)*rp_binf(i2);
      RP_ROUND_UPWARD();
      rp_bsup(result)=rp_binf(i1)*rp_bsup(i2);
    break;

    case 8: /* 1000: i1<0, 0 in i2 */
      if (rp_binf(i1)==(-RP_INFINITY))
      {
        if( rp_binf(i2)==0.0 )
        {
          rp_interval_set(result,(-RP_INFINITY),0.0);
	}
        else if ( rp_bsup(i2)==0.0 )
        {
          rp_interval_set(result,0.0,RP_INFINITY);
	}
        else
        {
	  rp_interval_set_real_line(result);
	}
      }
      else
      {
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_binf(i1)*rp_bsup(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_binf(i1)*rp_binf(i2);
      }
    break;

    case 9: /* 1001: i1<0, i2>0 */
      RP_ROUND_DOWNWARD();
      rp_binf(result)=rp_binf(i1)*rp_bsup(i2);
      RP_ROUND_UPWARD();
      rp_bsup(result)=rp_bsup(i1)*rp_binf(i2);
    break;

    case 10: /* 1010: i1<0, i2<0 */
      RP_ROUND_DOWNWARD();
      rp_binf(result)=rp_bsup(i1)*rp_bsup(i2);
      RP_ROUND_UPWARD();
      rp_bsup(result)=rp_binf(i1)*rp_binf(i2);
    break;
  }
}

/* let x=[r,r], result := [r,r]*i */
void rp_interval_mul_r_i(rp_interval result, rp_interval x, rp_interval i)
{
  if( rp_binf(x)==0.0 )
  {
    rp_interval_set(result,0.0,0.0);
  }
  else if( rp_binf(x)<0.0 )
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_binf(x)*rp_bsup(i);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_binf(x)*rp_binf(i);
  }
  else
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_binf(x)*rp_binf(i);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_binf(x)*rp_bsup(i);
  }
}

/* let x=[r,r] with r<0, result := [r,r]*i */
void rp_interval_mul_rneg_i(rp_interval result, rp_interval x, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result)=rp_binf(x)*rp_bsup(i);
  RP_ROUND_UPWARD();
  rp_bsup(result)=rp_binf(x)*rp_binf(i);
}

/* let x=[r,r] with r>=0, result := [r,r]*i */
void rp_interval_mul_rpos_i(rp_interval result, rp_interval x, rp_interval i)
{
  if( rp_binf(x)==0.0 )
  {
    rp_interval_set(result,0.0,0.0);
  }
  else
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_binf(x)*rp_binf(i);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_binf(x)*rp_bsup(i);
  }
}

/* result := i1 / i2 */
void rp_interval_div(rp_interval result, rp_interval i1, rp_interval i2)
{
  if (rp_interval_zero(i1))           /* i1=[0,0] */
  {
    if (rp_interval_contains(i2,0.0))
    {
      rp_interval_set_real_line(result);
    }
    else
    {
      rp_interval_set(result,0.0,0.0);
    }
  }
  else if (rp_interval_contains(i2,0.0))
  {
    /* The problem is to manage divisions by 0 */
    if (rp_interval_zero(i2))           /* i2=[0,0] */
    {
      rp_interval_set_real_line(result);
    }
    else if (rp_binf(i2)==0.0)          /* i2=[0,b], b>0 */
    {
      if (rp_binf(i1)>=0.0)             /* [a,c]/[0,b]=[a/b,+oo] */
      {
        RP_ROUND_DOWNWARD();
	rp_interval_set(result,rp_binf(i1)/rp_bsup(i2),RP_INFINITY);
      }
      else if (rp_bsup(i1)<=0.0)        /* [a,c]/[0,b]=[a/b,+oo] */
      {
        RP_ROUND_UPWARD();
	rp_interval_set(result,(-RP_INFINITY),rp_bsup(i1)/rp_bsup(i2));
      }
      else                           /* i1=[a,c], a<0<c */
      {
        rp_interval_set_real_line(result);
      }
    }
    else if (rp_bsup(i2)==0.0)          /* i2=[a,0], a<0 */
    {
      if (rp_binf(i1)>=0.0)             /* [a,c]/[b,0]=[-oo,a/b] */
      {
        RP_ROUND_UPWARD();
	rp_interval_set(result,(-RP_INFINITY),rp_binf(i1)/rp_binf(i2));
      }
      else if (rp_bsup(i1)<=0.0)        /* [a,c]/[b,0]=[c/b,+oo] */
      {
        RP_ROUND_DOWNWARD();
	rp_interval_set(result,rp_bsup(i1)/rp_binf(i2),RP_INFINITY);
      }
      else                           /* i1=[a,c], a<0<c */
      {
        rp_interval_set_real_line(result);
      }
    }
    else                             /* i2=[a,b], a<0<b */
    {
      rp_interval_set_real_line(result);
    }
  }
  else  /* i2 does not contain 0 => standard division */
  {
    unsigned int
    sig = ((rp_bsup(i1)<0.0) << 3) | ((rp_binf(i1)>0.0) << 2)
          | ((rp_bsup(i2)<0.0) << 1) | (rp_binf(i2)>0.0);

    switch( sig )
    {
      case 1: /* 0001: 0 in i1, i2>0 */
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_binf(i1)/rp_binf(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_bsup(i1)/rp_binf(i2);
      break;

      case 2: /* 0010: 0 in i1, i2<0 */
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_bsup(i1)/rp_bsup(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_binf(i1)/rp_bsup(i2);
      break;

      case 5: /* 0101: i1>0, i2>0 */
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_binf(i1)/rp_bsup(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_bsup(i1)/rp_binf(i2);
      break;

      case 6: /* 0110: i1>0, i2<0 */
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_bsup(i1)/rp_bsup(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_binf(i1)/rp_binf(i2);
      break;

      case 9: /* 1001: i1<0, i2>0 */
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_binf(i1)/rp_binf(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_bsup(i1)/rp_bsup(i2);
      break;

      case 10: /* 1010: i1<0, i2<0 */
        RP_ROUND_DOWNWARD();
        rp_binf(result)=rp_bsup(i1)/rp_binf(i2);
        RP_ROUND_UPWARD();
        rp_bsup(result)=rp_binf(i1)/rp_bsup(i2);
      break;
    }
  }
}

/* let x=[r,r], result := i / [r,r] */
void rp_interval_div_i_r(rp_interval result, rp_interval i, rp_interval x)
{
  if( rp_binf(x)==0.0 )
  {
    rp_interval_set_real_line(result);
  }
  else if( rp_binf(x)<0.0 )
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_bsup(i)/rp_binf(x);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_binf(i)/rp_binf(x);
  }
  else
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_binf(i)/rp_binf(x);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_bsup(i)/rp_binf(x);
  }
}

/* let x=[r,r] and r>0, result := i / [r,r] */
void rp_interval_div_i_rpos(rp_interval result, rp_interval i, rp_interval x)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result)=rp_binf(i)/rp_binf(x);
  RP_ROUND_UPWARD();
  rp_bsup(result)=rp_bsup(i)/rp_binf(x);
}

/* let x=[r,r] and r<0, result := i / [r,r] */
void rp_interval_div_i_rneg(rp_interval result, rp_interval i, rp_interval x)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result)=rp_bsup(i)/rp_binf(x);
  RP_ROUND_UPWARD();
  rp_bsup(result)=rp_binf(i)/rp_binf(x);
}

/* let x=[r,r], result := [r,r] / i */
void rp_interval_div_r_i(rp_interval result, rp_interval x, rp_interval i)
{
  if (rp_binf(x)==0.0)                  /* x=[0,0] */
  {
    if (rp_interval_contains(i,0.0))
    {
      rp_interval_set_real_line(result);
    }
    else
    {
      rp_interval_set(result,0.0,0.0);
    }
  }
  else if (rp_interval_contains(i,0.0))
  {
    /* The problem is to manage divisions by 0 */
    if (rp_interval_zero(i))           /* i=[0,0] */
    {
      rp_interval_set_real_line(result);
    }
    else if (rp_binf(i)==0.0)          /* i=[0,b], b>0 */
    {
      if (rp_binf(x)>0.0)               /* [r,r]/[0,b]=[r/b,+oo] */
      {
        RP_ROUND_DOWNWARD();
	rp_interval_set(result,rp_binf(x)/rp_bsup(i),RP_INFINITY);
      }
      else                           /* x is negative */
      {
        RP_ROUND_UPWARD();
	rp_interval_set(result,(-RP_INFINITY),rp_binf(x)/rp_bsup(i));
      }
    }
    else if (rp_bsup(i)==0.0)          /* i=[a,0], a<0 */
    {
      if (rp_binf(x)>0.0)               /* [r,r]/[b,0]=[-oo,r/b] */
      {
        RP_ROUND_UPWARD();
	rp_interval_set(result,(-RP_INFINITY),rp_binf(x)/rp_binf(i));
      }
      else   /* x is negative */     /* [r,r]/[b,0]=[r/b,+oo] */
      {
        RP_ROUND_DOWNWARD();
	rp_interval_set(result,rp_binf(x)/rp_binf(i),RP_INFINITY);
      }
    }
    else                             /* i=[a,b], a<0<b */
    {
      rp_interval_set_real_line(result);
    }
  }
  else  /* i does not contain 0 and x!=0 => standard division */
  {
    if (rp_binf(x)>0.0)
    {
      RP_ROUND_DOWNWARD();
      rp_binf(result)=rp_binf(x)/rp_bsup(i);
      RP_ROUND_UPWARD();
      rp_bsup(result)=rp_binf(x)/rp_binf(i);
    }
    else
    {
      RP_ROUND_DOWNWARD();
      rp_binf(result)=rp_binf(x)/rp_binf(i);
      RP_ROUND_UPWARD();
      rp_bsup(result)=rp_binf(x)/rp_bsup(i);
    }
  }
}

/* let x=[r,r], r>=0, result := [r,r] / i */
void rp_interval_div_rpos_i(rp_interval result, rp_interval x, rp_interval i)
{
  if (rp_binf(x)==0.0)                  /* x=[0,0] */
  {
    if (rp_interval_contains(i,0.0))
    {
      rp_interval_set_real_line(result);
    }
    else
    {
      rp_interval_set(result,0.0,0.0);
    }
  }
  else if (rp_interval_contains(i,0.0))
  {
    /* The problem is to manage divisions by 0 */
    if (rp_interval_zero(i))           /* i=[0,0] */
    {
      rp_interval_set_real_line(result);
    }
    else if (rp_binf(i)==0.0)          /* i=[0,b], b>0 */
    {
      RP_ROUND_DOWNWARD();
      rp_interval_set(result,rp_binf(x)/rp_bsup(i),RP_INFINITY);
    }
    else if (rp_bsup(i)==0.0)          /* i=[a,0], a<0 */
    {
      RP_ROUND_UPWARD();
      rp_interval_set(result,(-RP_INFINITY),rp_binf(x)/rp_binf(i));
    }
    else                             /* i=[a,b], a<0<b */
    {
      rp_interval_set_real_line(result);
    }
  }
  else  /* i does not contain 0 and x>0 => standard division */
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_binf(x)/rp_bsup(i);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_binf(x)/rp_binf(i);
  }
}

/* let x=[r,r], r<=0, result := [r,r] / i */
void rp_interval_div_rneg_i(rp_interval result, rp_interval x, rp_interval i)
{
  if (rp_binf(x)==0.0)                  /* x=[0,0] */
  {
    if (rp_interval_contains(i,0.0))
    {
      rp_interval_set_real_line(result);
    }
    else
    {
      rp_interval_set(result,0.0,0.0);
    }
  }
  else if (rp_interval_contains(i,0.0))
  {
    /* The problem is to manage divisions by 0 */
    if (rp_interval_zero(i))           /* i=[0,0] */
    {
      rp_interval_set_real_line(result);
    }
    else if (rp_binf(i)==0.0)          /* i=[0,b], b>0 */
    {
      RP_ROUND_UPWARD();
      rp_interval_set(result,(-RP_INFINITY),rp_binf(x)/rp_bsup(i));
    }
    else if (rp_bsup(i)==0.0)          /* i=[a,0], a<0 */
    {
      RP_ROUND_DOWNWARD();
      rp_interval_set(result,rp_binf(x)/rp_binf(i),RP_INFINITY);
    }
    else                             /* i=[a,b], a<0<b */
    {
      rp_interval_set_real_line(result);
    }
  }
  else  /* i does not contain 0 and x<0 => standard division */
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_binf(x)/rp_binf(i);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_binf(x)/rp_bsup(i);
  }
}

/* result := i^2 */
void rp_interval_sqr(rp_interval result, rp_interval i)
{
  if( rp_binf(i)>=0.0 )
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_binf(i)*rp_binf(i);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_bsup(i)*rp_bsup(i);
  }
  else if( rp_bsup(i)<=0.0 )
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result)=rp_bsup(i)*rp_bsup(i);
    RP_ROUND_UPWARD();
    rp_bsup(result)=rp_binf(i)*rp_binf(i);
  }
  else if ((-rp_binf(i))<rp_bsup(i))
  {
    rp_binf(result) = 0.0;
    RP_ROUND_UPWARD();
    rp_bsup(result) = rp_bsup(i)*rp_bsup(i);
  }
  else
  {
    rp_binf(result) = 0.0;
    RP_ROUND_UPWARD();
    rp_bsup(result) = rp_binf(i)*rp_binf(i);
  }
}

/* result := sqrt(i) */
void rp_interval_sqrt(rp_interval result, rp_interval i)
{
  if( rp_bsup(i)<0.0 )
  {
    rp_interval_set_empty(result);
  }
  else if( rp_binf(i)>=0.0 )
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result) = sqrt(rp_binf(i));
    RP_ROUND_UPWARD();
    rp_bsup(result) = sqrt(rp_bsup(i));
  }
  else
  {
    rp_binf(result) = 0.0;
    RP_ROUND_UPWARD();
    rp_bsup(result) = sqrt(rp_bsup(i));
  }
}

/* let n=[j,j], result := i^j */
void rp_interval_pow(rp_interval result, rp_interval i, rp_interval n)
{
  int exp = (int)rp_binf(n);

  if( rp_even(exp) )   /* n even */
  {
    rp_interval z;
    rp_interval_abs(z,i);
    if (rp_binf(z)==0.0)
    {
      rp_binf(result) = 0.0;
    }
    else
    {
      rp_binf(result) = rp_pow(rp_binf(z),exp,RP_ROUND_VALUE_DOWN);
    }
    if (rp_bsup(z)==RP_INFINITY)
    {
      rp_bsup(result) = RP_INFINITY;
    }
    else
    {
      rp_bsup(result) = rp_pow(rp_bsup(z),exp,RP_ROUND_VALUE_UP);
    }
  }
  else  /* rp_odd(exp) */
  {
    if (rp_binf(i)==(-RP_INFINITY))
    {
      rp_binf(result) = (-RP_INFINITY);
    }
    else
    {
      rp_binf(result) = rp_pow(rp_binf(i),exp,RP_ROUND_VALUE_DOWN);
    }
    if (rp_bsup(i)==RP_INFINITY)
    {
      rp_bsup(result) = RP_INFINITY;
    }
    else
    {
      rp_bsup(result) = rp_pow(rp_bsup(i),exp,RP_ROUND_VALUE_UP);
    }
  }
}

/* result := exp(i) */
void rp_interval_exp(rp_interval result, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = exp(rp_binf(i));

  RP_ROUND_UPWARD();
  rp_bsup(result) = exp(rp_bsup(i));

  if( rp_binf(result)==RP_INFINITY )      /* (+oo,+oo) */
  {
    rp_binf(result) = RP_MAX_DOUBLE;
  }
}

/* result := log(i) */
void rp_interval_log(rp_interval result, rp_interval i)
{
  if( rp_bsup(i)<=0.0 )
  {
    rp_interval_set_empty(result);
  }
  else if( rp_binf(i)<=0.0 )
  {
    rp_binf(result) = (-RP_INFINITY);
    RP_ROUND_UPWARD();
    rp_bsup(result) = log(rp_bsup(i));
  }
  else
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result) = log(rp_binf(i));
    RP_ROUND_UPWARD();
    rp_bsup(result) = log(rp_bsup(i));
  }
}

/* result := sin(i) */
void rp_interval_sin(rp_interval result, rp_interval i)
{
  rp_interval i_t;
  RP_ROUND_UPWARD();
  if( rp_interval_width(i)>=rp_binf(RP_INTERVAL_2_PI) )
  {
    rp_interval_set(result,-1.0,1.0);
  }
  else
  {
    /* Translation i -> i_t included in [0,4pi] */
    /* i_t := i +- 2*k*Pi <=> i - offset */
    rp_interval offset;
    if( rp_binf(i)<0.0 )
    {
      double x = floor(rp_binf(i)/rp_bsup(RP_INTERVAL_2_PI));
      rp_interval factor;
      rp_interval_set(factor,x,x);
      rp_interval_mul_r_i(offset,factor,RP_INTERVAL_2_PI);
      rp_interval_sub(i_t,i,offset);
    }
    else if( rp_binf(i)>rp_binf(RP_INTERVAL_2_PI) )
    {
      double x = floor(rp_binf(i)/rp_binf(RP_INTERVAL_2_PI));
      rp_interval factor;
      rp_interval_set(factor,x,x);
      rp_interval_mul_r_i(offset,factor,RP_INTERVAL_2_PI);
      rp_interval_sub(i_t,i,offset);
    }
    else
    {
      rp_interval_copy(i_t,i);
    }

    /* 3Pi/2 or 7Pi/2 included in i_t ? */
    if (rp_interval_included(RP_INTERVAL_3_PI_2,i_t) ||
	rp_interval_included(RP_INTERVAL_7_PI_2,i_t))
    {
      rp_binf(result) = -1.0;
    }
    else
    {
      double l, r;
      RP_ROUND_DOWNWARD();
      if ((rp_binf(i_t)<=0.0) || (rp_binf(i_t)>=rp_bsup(RP_INTERVAL_4_PI)))
      {
        l = 0.0;  /* must be sin(0) or sin(4Pi) */
      }
      else
      {
        l = sin(rp_binf(i_t));
      }
      if ((rp_bsup(i_t)<=0.0) || (rp_bsup(i_t)>=rp_bsup(RP_INTERVAL_4_PI)))
      {
        r = 0.0;
      }
      else
      {
        r = sin(rp_bsup(i_t));
      }
      rp_binf(result) = rp_min_num(l,r);
    }

    /* Pi/2 or 5Pi/2 included in i_t ? */
    if (rp_interval_included(RP_INTERVAL_1_PI_2,i_t) ||
	rp_interval_included(RP_INTERVAL_5_PI_2,i_t))
    {
      rp_bsup(result) = 1.0;
    }
    else
    {
      double l, r;
      RP_ROUND_UPWARD();
      if ((rp_binf(i_t)<=0.0) || (rp_binf(i_t)>=rp_bsup(RP_INTERVAL_4_PI)))
      {
        l = 0.0;
      }
      else
      {
        l = sin(rp_binf(i_t));
      }
      if ((rp_bsup(i_t)<=0.0) || (rp_bsup(i_t)>=rp_bsup(RP_INTERVAL_4_PI)))
      {
        r = 0.0;
      }
      else
      {
        r = sin(rp_bsup(i_t));
      }
      rp_bsup(result) = rp_max_num(l,r);
    }
  }
}

/* result := cos(i) */
void rp_interval_cos(rp_interval result, rp_interval i)
{
  rp_interval j;
  if (rp_interval_zero(i))
  {
    rp_interval_set(result,1.0,1.0);
  }
  else
  {
    rp_interval_add(j,i,RP_INTERVAL_1_PI_2);   /* j := i + pi/2 */
    rp_interval_sin(result,j);                 /* cos(i) = sin(i + pi/2) */
  }
}

/* result := tan(i) */
void rp_interval_tan(rp_interval result, rp_interval i)
{
  rp_interval i_t;
  RP_ROUND_UPWARD();
  if( rp_interval_width(i)>=rp_binf(RP_INTERVAL_PI) )
  {
    rp_interval_set_real_line(result);
  }
  else
  {
    /* Translation i -> i_t included in [-pi/2,+3pi/2] */
    /* i_t := i +- k*Pi <=> i - offset */
    rp_interval offset;
    if( rp_binf(i)<=(-rp_bsup(RP_INTERVAL_1_PI_2)) )
    {
      double x = floor(rp_binf(i)/rp_bsup(RP_INTERVAL_PI));
      rp_interval factor;
      rp_interval_set(factor,x,x);
      rp_interval_mul_r_i(offset,factor,RP_INTERVAL_PI);
      rp_interval_sub(i_t,i,offset);
    }
    else if( rp_binf(i)>=rp_bsup(RP_INTERVAL_1_PI_2) )
    {
      double x = floor(rp_binf(i)/rp_binf(RP_INTERVAL_PI));
      rp_interval factor;
      rp_interval_set(factor,x,x);
      rp_interval_mul_rpos_i(offset,factor,RP_INTERVAL_PI);
      rp_interval_sub(i_t,i,offset);
    }
    else
    {
      rp_interval_copy(i_t,i);
    }

    /* Pi/2 included in i_t OR one of the bounds cannot be
       distinguished from Pi/2 */
    if (rp_interval_included(RP_INTERVAL_1_PI_2,i_t) ||
	rp_interval_strictly_contains(RP_INTERVAL_1_PI_2,rp_binf(i_t)) ||
	rp_interval_strictly_contains(RP_INTERVAL_1_PI_2,rp_bsup(i_t)))
    {
      rp_interval_set_real_line(result);
    }
    /* Is i_t contained in (-Pi/2,Pi/2) or (Pi/2,3Pi/2)*/
    else if (((rp_binf(i_t)>=(-rp_binf(RP_INTERVAL_1_PI_2)))
	      && (rp_bsup(i_t)<=rp_binf(RP_INTERVAL_1_PI_2))) ||
	     ((rp_binf(i_t)>=rp_bsup(RP_INTERVAL_1_PI_2))
	      && (rp_bsup(i_t)<=rp_binf(RP_INTERVAL_3_PI_2))))
    {
      if (rp_binf(i_t)==0.0)
      {
        rp_binf(result) = 0.0;
      }
      else
      {
        RP_ROUND_DOWNWARD();
        rp_binf(result) = tan(rp_binf(i_t));
      }
      if (rp_bsup(i_t)==0.0)
      {
	rp_bsup(result) = 0.0;
      }
      else
      {
        RP_ROUND_UPWARD();
        rp_bsup(result) = tan(rp_bsup(i_t));
      }
    }
    else
    {
      rp_interval_set_real_line(result);
    }
  }
}

/* result := cosh(i) = 0.5 * ( exp(i) + exp(-i) ) */
/* decreasing function in (-oo,0] and increasing function in [0,+oo) */
void rp_interval_cosh(rp_interval result, rp_interval i)
{
  if( rp_binf(i)>0.0 )
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result) = cosh(rp_binf(i));
    RP_ROUND_UPWARD();
    rp_bsup(result) = cosh(rp_bsup(i));
  }
  else if( rp_bsup(i)<0.0 )
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result) = cosh(rp_bsup(i));
    RP_ROUND_UPWARD();
    rp_bsup(result) = cosh(rp_binf(i));
  }
  else if ((-rp_binf(i))<rp_bsup(i))
  {
    rp_binf(result) = 1.0;
    RP_ROUND_UPWARD();
    rp_bsup(result) = cosh(rp_bsup(i));
  }
  else
  {
    rp_binf(result) = 1.0;
    RP_ROUND_UPWARD();
    rp_bsup(result) = cosh(rp_binf(i));
  }
}

/* result := sinh(i) = 0.5 * ( exp(i) - exp(-i) ) */
/* increasing function in (-oo,+oo) */
void rp_interval_sinh(rp_interval result, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = sinh(rp_binf(i));

  RP_ROUND_UPWARD();
  rp_bsup(result) = sinh(rp_bsup(i));
}

/* result := tanh(i) = sinh(i) / cosh(i) */
/* increasing function in (-oo,+oo) */
void rp_interval_tanh(rp_interval result, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = tanh(rp_binf(i));

  RP_ROUND_UPWARD();
  rp_bsup(result) = tanh(rp_bsup(i));
}

/* result := asin(i) (increasing function in [-1,1]) */
void rp_interval_asin(rp_interval result, rp_interval i)
{
  rp_interval j;
  rp_binf(j) = rp_max_num(-1.0,rp_binf(i));
  rp_bsup(j) = rp_min_num(1.0,rp_bsup(i));

  if( rp_interval_empty(j) )
  {
    rp_interval_set_empty(result);
  }
  else
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result) = asin(rp_binf(j));
    RP_ROUND_UPWARD();
    rp_bsup(result) = asin(rp_bsup(j));
  }
}

/* result := acos(i) (decreasing function in [-1,1]) */
void rp_interval_acos(rp_interval result, rp_interval i)
{
  rp_interval j;
  rp_binf(j) = rp_max_num(-1.0,rp_binf(i));
  rp_bsup(j) = rp_min_num(1.0,rp_bsup(i));

  if( rp_interval_empty(j) )
  {
    rp_interval_set_empty(result);
  }
  else
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result) = acos(rp_bsup(j));
    RP_ROUND_UPWARD();
    rp_bsup(result) = acos(rp_binf(j));
  }
}

/* result := atan(i)  (increasing function in (-oo,+oo)) */
void rp_interval_atan(rp_interval result, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = atan(rp_binf(i));

  RP_ROUND_UPWARD();
  rp_bsup(result) = atan(rp_bsup(i));
}

/* result := asinh(i) = log(i + sqrt(1+i^2)) */
/* increasing function in (-oo,+oo) */
void rp_interval_asinh(rp_interval result, rp_interval i)
{
  RP_ROUND_DOWNWARD();
  rp_binf(result) = asinh(rp_binf(i));

  RP_ROUND_UPWARD();
  rp_bsup(result) = asinh(rp_bsup(i));
}

/* result := acosh(i) = log(i + sqrt(i^2-1)) */
/* increasing function in [1,+oo) */
void rp_interval_acosh(rp_interval result, rp_interval i)
{
  if( rp_bsup(i)<1.0 )
  {
    rp_interval_set_empty(result);
  }
  else if( rp_binf(i)>1.0 )
  {
    RP_ROUND_DOWNWARD();
    rp_binf(result) = acosh(rp_binf(i));

    RP_ROUND_UPWARD();
    rp_bsup(result) = acosh(rp_bsup(i));
  }
  else /* i contains 1.0 */
  {
    rp_binf(result) = 0.0;
    if (rp_bsup(i)==1.0)
    {
      rp_bsup(result) = 0.0;
    }
    else
    {
      RP_ROUND_UPWARD();
      rp_bsup(result) = acosh(rp_bsup(i));
    }
  }
}

/* result := atanh(i) = 0.5 * log( (1+i) / (1-i) ) */
/* increasing function in (-1,1) */
void rp_interval_atanh(rp_interval result, rp_interval i)
{
  if ( (rp_bsup(i)<=-1.0) || (rp_binf(i)>=1.0) )
  {
    rp_interval_set_empty(result);
  }
  else
  {
    if (rp_binf(i)<=-1.0)
    {
      rp_binf(result) = (-RP_INFINITY);
    }
    else
    {
      RP_ROUND_DOWNWARD();
      rp_binf(result) = atanh(rp_binf(i));
    }

    if (rp_bsup(i)>=1.0)
    {
      rp_bsup(result) = RP_INFINITY;
    }
    else
    {
      RP_ROUND_UPWARD();
      rp_bsup(result) = atanh(rp_bsup(i));
    }
  }
}

/* result := matan(i)  (increasing function in (-oo,+oo)) */
void rp_interval_matan(rp_interval result, rp_interval i)
{

    /* matan(x) = 1                                                           if x = 0
                = atn(sqrt(x))/sqrt(x)                                        if x > 0
                = log ((1 + sqrt(-x)) / (1 - sqrt(-x))) / (2 * sqrt(-x))      if x < 0
    */

  /* TODO */
  RP_ROUND_DOWNWARD();
  rp_binf(result) = atan(rp_binf(i));

  RP_ROUND_UPWARD();
  rp_bsup(result) = atan(rp_bsup(i));
}

/* result := safesqrt(i)  (increasing function in (-oo,+oo)) */
void rp_interval_safesqrt(rp_interval result, rp_interval i)
{
    /* safesqrt(x) = 0                      if x = 0
                   = sqrt(x)                if x >= 0
    */

  rp_interval i_t;
  rp_interval_copy(i_t,i);
  if (rp_binf(i) < 0.0) {
      rp_binf(i_t) = 0.0;
  }
  return rp_interval_sqrt(result, i_t);
}

#define _max(x, y) (x > y ? x : y)
#define _min(x, y) (x < y ? x : y)

void rp_interval_atan2(rp_interval result, rp_interval y, rp_interval x)
{
    /*
      Due to the floating-point error, use the following definition:

      atan2(y,x) = arctan(y/x)        if x > 0            (1)
                 = arctan(y/x) + pi   if y >= 0, x < 0    (2)
                 = arctan(y/x) - pi   if y < 0, x < 0     (3)
                 = + pi/2             if y > 0, x = 0     (4)
                 = - pi/2             if y < 0, x = 0     (5)
                 = undefined          if y = 0, x = 0     (6)

      Another definition is
      atan2(y,x) = 2 arctan ( y / [sqrt(x^2 + y^2) + x] )
    */
//    printf("\n\n-----------------------\n");
//    printf("rp_interval_atan2()\n");
//    printf("y = ");
//    rp_interval_display_simple_nl(y);

//    printf("x = ");
//    rp_interval_display_simple_nl(x);

    double x_ub = rp_bsup(x);
    double x_lb = rp_binf(x);
    double y_ub = rp_bsup(y);
    double y_lb = rp_binf(y);

    rp_interval_set_empty(result);
    /* atan2(y,x) = arctan(y/x)        if x > 0            (1) */
    if(x_ub > 0.0) {
//        printf("(1)\n");
        rp_interval x_temp, aux;
        rp_interval_set(x_temp, _max(x_lb, DBL_EPSILON), x_ub);
        rp_interval_div(aux, y, x_temp);  /* aux    = y/x         */
        rp_interval_atan(result, aux);    /* result = arctan(y/x) */

//        printf("result = ");
//        rp_interval_display_simple_nl(result);
    }

    /* atan2(y,x) = arctan(y/x) + pi   if y >= 0, x < 0    (2) */
    if(y_ub > 0.0 && x_lb < 0.0) {
//        printf("(2)\n");
        rp_interval x_temp, y_temp, aux1, aux2, aux3;
        rp_interval_set(x_temp, x_lb, _min(x_ub, -DBL_EPSILON));
        rp_interval_set(y_temp, _max(y_lb, 0.0), y_ub);
        rp_interval_div(aux1, y, x_temp);  /* aux = y/x         */
        rp_interval_atan(aux2, aux1);       /* aux = arctan(y/x) */
                                          /* aux = pi + arctan(y/x) */
        rp_interval_add_r_i(aux3, RP_INTERVAL_PI, aux2);
        /* result = result U aux */
        rp_interval_hull(result, result, aux3);

//        printf("result = ");
//        rp_interval_display_simple_nl(result);
    }

    /* atan2(y,x) = arctan(y/x) - pi   if y < 0, x < 0     (3) */
    if(y_lb < 0.0 && x_lb < 0.0) {
//        printf("(3)\n");
        rp_interval x_temp, y_temp, aux1, aux2, aux3;
        rp_interval_set(x_temp, x_lb, _min(x_ub, -DBL_EPSILON));
        rp_interval_set(y_temp, y_lb, _min(y_ub, -DBL_EPSILON));
        rp_interval_div(aux1, y, x_temp);  /* aux = y/x         */
        rp_interval_atan(aux2, aux1);       /* aux = arctan(y/x) */
                                          /* aux = - pi + arctan(y/x) */
        rp_interval_sub_i_r(aux3, aux2, RP_INTERVAL_PI);
        rp_interval_hull(result, result, aux3);

//        printf("result = ");
//        rp_interval_display_simple_nl(result);
    }

    /* atan2(y,x) = + pi/2             if y > 0, x = 0     (4) */
    if(y_ub > 0.0 && rp_interval_contains(x, 0.0)) {
//        printf("(4)\n");
        rp_interval_hull(result, result, RP_INTERVAL_1_PI_2);
    }

    /* atan2(y,x) = - pi/2             if y < 0, x = 0     (5) */
    if(y_lb < 0.0 && rp_interval_contains(x, 0.0)) {
//        printf("(5)\n");
        rp_interval neg_1_pi_2;
        rp_interval_neg(neg_1_pi_2, RP_INTERVAL_1_PI_2);
        rp_interval_hull(result, result, neg_1_pi_2);
    }

//    printf("atan2(y, x) = ");
//    rp_interval_display_simple_nl(result);
}

/* result := n-th root of i                                                */
/* computes only the positive part for even exponent and positive interval */
void rp_interval_nthroot(rp_interval result, rp_interval i, rp_interval n)
{
  rp_interval aux1, aux2, aux3, aux4, aux5;
  int exp = (int)rp_binf(n);
  if (rp_odd(exp))
  {
    if (rp_binf(i)>0.0)
    {
      /* result := exp(log(i)/n) */
      rp_interval_log(aux1,i);              /* aux1 := log(i)          */
      rp_interval_div_i_r(aux2,aux1,n);     /* aux2 := log(i)/n        */
      rp_interval_exp(result,aux2);         /* result := exp(log(x)/n) */
    }
    else if (rp_bsup(i)<0.0)
    {
      /* result := -exp(log(-i)/n) */
      rp_interval_neg(aux1,i);              /* aux1 := -i                */
      rp_interval_log(aux2,aux1);           /* aux2 := log(-i)           */
      rp_interval_div_i_r(aux3,aux2,n);     /* aux3 := log(-i)/n         */
      rp_interval_exp(aux4,aux3);           /* aux4 := exp(log(-i)/n)    */
      rp_interval_neg(result,aux4);         /* result := -exp(log(-i)/n) */
    }
    else /* i contains 0 */
    {
      /* computation of left bound */
      if (rp_binf(i)==0.0)
      {
	rp_binf(result) = 0.0;
      }
      else
      {
	rp_interval_set_point(aux1,rp_binf(i));
	rp_interval_neg(aux2,aux1);
        rp_interval_log(aux3,aux2);
	rp_interval_div_i_r(aux4,aux3,n);
	rp_interval_exp(aux5,aux4);
	rp_binf(result) = -rp_bsup(aux5);
      }

      /* computation of right bound */
      if (rp_bsup(i)==0.0)
      {
	rp_bsup(result) = 0.0;
      }
      else
      {
	rp_interval_set_point(aux1,rp_bsup(i));
	rp_interval_log(aux2,aux1);
	rp_interval_div_i_r(aux3,aux2,n);
	rp_interval_exp(aux4,aux3);
	rp_bsup(result) = rp_bsup(aux4);
      }
    }
  }
  else /* exponent even */
  {
    if (rp_bsup(i)<0.0)
    {
      rp_interval_set_empty(result);
    }
    else if (rp_binf(i)>0.0)
    {
      /* only positive interval computed */
      if (exp==2)
      {
	/* square root */
	rp_interval_sqrt(result,i);
      }
      else
      {
	rp_interval_log(aux1,i);
	rp_interval_div_i_r(aux2,aux1,n);
	rp_interval_exp(result,aux2);
      }
    }
    else
    {
      if (rp_bsup(i)==0.0)
      {
	rp_interval_set_point(result,0.0);
      }
      else
      {
	rp_interval_set_point(aux1,rp_bsup(i));
	if (exp==2)
	{
	  rp_interval_sqrt(aux4,aux1);
	}
	else
	{
	  rp_interval_log(aux2,aux1);
	  rp_interval_div_i_r(aux3,aux2,n);
	  rp_interval_exp(aux4,aux3);
	}
	rp_bsup(result) = rp_bsup(aux4);
	rp_binf(result) = -rp_bsup(result);
      }
    }
  }
}

/* result := absolute value of i */
void rp_interval_abs(rp_interval result, rp_interval i)
{
  if( rp_binf(i)>=0.0 )
  {
    rp_binf(result) = rp_binf(i);
    rp_bsup(result) = rp_bsup(i);
  }
  else if( rp_bsup(i)<=0.0 )
  {
    rp_binf(result) = -(rp_bsup(i));
    rp_bsup(result) = -(rp_binf(i));
  }
  else
  {
    rp_binf(result) = 0.0;
    rp_bsup(result) = rp_max_num(-(rp_binf(i)),rp_bsup(i));
  }
}

/* result := min(i1,i2) */
void rp_interval_min(rp_interval result, rp_interval i1, rp_interval i2)
{
  rp_binf(result) = rp_min_num(rp_binf(i1),rp_binf(i2));
  rp_bsup(result) = rp_min_num(rp_bsup(i1),rp_bsup(i2));
}

/* result := max(i1,i2) */
void rp_interval_max(rp_interval result, rp_interval i1, rp_interval i2)
{
  rp_binf(result) = rp_max_num(rp_binf(i1),rp_binf(i2));
  rp_bsup(result) = rp_max_num(rp_bsup(i1),rp_bsup(i2));
}

/* result := i1 intersection i2 */
void rp_interval_inter(rp_interval result, rp_interval i1, rp_interval i2)
{
  rp_binf(result) = rp_max_num(rp_binf(i1),rp_binf(i2));
  rp_bsup(result) = rp_min_num(rp_bsup(i1),rp_bsup(i2));
}

/* result := result intersection i */
void rp_interval_set_inter(rp_interval result, rp_interval i)
{
  rp_binf(result) = rp_max_num(rp_binf(result),rp_binf(i));
  rp_bsup(result) = rp_min_num(rp_bsup(result),rp_bsup(i));
}

/* result := hull(i1,i2) */
void rp_interval_hull(rp_interval result, rp_interval i1, rp_interval i2)
{
  rp_binf(result) = rp_min_num(rp_binf(i1),rp_binf(i2));
  rp_bsup(result) = rp_max_num(rp_bsup(i1),rp_bsup(i2));
}

/* result := hull (i1 \ i2) */
void rp_interval_setminus(rp_interval result, rp_interval i1, rp_interval i2)
{
  if (rp_interval_included(i1,i2))         /* i1:   |-------|   */
  {                                        /* i2: |-----------| */
    rp_interval_set_empty(result);         /*       empty set   */
  }
  else if ((rp_binf(i2)<=rp_binf(i1)) &&   /* i1:    |--------| */
	                                   /* i2: |-------|     */
                                           /*             |---| */
	   rp_interval_strictly_contains(i1,rp_bsup(i2)))
  {
    rp_binf(result) = rp_bsup(i2);
    rp_bsup(result) = rp_bsup(i1);
  }
  else if ((rp_bsup(i2)>=rp_bsup(i1)) &&   /* i1: |-------|     */
	                                   /* i2:     |-------| */
	                                   /*     |---|         */
	   rp_interval_strictly_contains(i1,rp_binf(i2)))
  {
    rp_binf(result) = rp_binf(i1);
    rp_bsup(result) = rp_binf(i2);
  }
  else                                     /* i1 and i2 disjoint, or     */
  {                                        /* share only one bound, or   */
    rp_interval_copy(result,i1);           /* i2 strictly included in i1 */
  }                                        /* no element removed from i1 */
}

/* i := smallest interval containing Pi */
void rp_interval_set_pi(rp_interval i)
{
  rp_interval j, two;
  rp_interval_set_halfpi(j);
  rp_interval_set(two,2.0,2.0);
  rp_interval_mul_rpos_i(i,two,j);
}

/* i := smallest interval containing Pi/2 */
void rp_interval_set_halfpi(rp_interval i)
{
  rp_interval k;
  rp_interval_set(k,1.0,1.0);
  rp_interval_asin(i,k);
}

/* i := smallest interval containing log(2) */
void rp_interval_set_log2(rp_interval i)
{
  rp_interval k;
  rp_interval_set(k,2.0,2.0);
  rp_interval_log(i,k);
}

/* i := smallest interval containing e */
void rp_interval_set_e(rp_interval i)
{
  rp_interval k;
  rp_interval_set(k,1.0,1.0);
  rp_interval_exp(i,k);
}

/* Initialization of the interval arithmetic module */
void rp_interval_init()
{
  rp_interval aux;
  rp_interval_set_halfpi(RP_INTERVAL_1_PI_2);
  rp_interval_set_pi(RP_INTERVAL_PI);

  rp_interval_set(aux,2.0,2.0);
  rp_interval_mul_rpos_i(RP_INTERVAL_2_PI,aux,RP_INTERVAL_PI);

  rp_interval_set(aux,4.0,4.0);
  rp_interval_mul_rpos_i(RP_INTERVAL_4_PI,aux,RP_INTERVAL_PI);

  rp_interval_set(aux,3.0,3.0);
  rp_interval_mul_rpos_i(RP_INTERVAL_3_PI_2,aux,RP_INTERVAL_1_PI_2);

  rp_interval_set(aux,5.0,5.0);
  rp_interval_mul_rpos_i(RP_INTERVAL_5_PI_2,aux,RP_INTERVAL_1_PI_2);

  rp_interval_set(aux,7.0,7.0);
  rp_interval_mul_rpos_i(RP_INTERVAL_7_PI_2,aux,RP_INTERVAL_1_PI_2);
}

/* Destruction of the interval arithmetic module */
void rp_interval_reset()
{ }
