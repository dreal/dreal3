/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



/* --------------------------------------------------------------------- */
/* - Computation of exp(x)-1, table lookup method                      - */
/* - We use the idea of Mr. P.T.P. Tang                                - */
/* --------------------------------------------------------------------- */

/* ------   Prozedure for Range 1   ------------------------------------ */

#ifdef LINT_ARGS
local double q_p1e1(double x)
#else
local double q_p1e1(x)

double x;
#endif
  {
    int j;
    long int n,m;
    double r,r1,r2,q,s;
    double res;

    /* Step 1 */
    if (x>0) n=CUTINT((x*q_exil)+0.5);
    else     n=CUTINT((x*q_exil)-0.5);      /* round (x)       */
    j=n % 32;                               /* n2=n mod 32     */
    if (j<0) j+=32;                         /* We force n2>=0  */
    m=(n-j)/32;
    r1=x-n*q_exl1;
    r2=-(n*q_exl2);

    /* Step 2 */
    r=r1+r2;
    q=(((q_exa[4]*r+q_exa[3])*r+q_exa[2])*r+q_exa[1])*r+q_exa[0];
    q=r*r*q;
    q=r1+(r2+q);

    /* Step 3 */
    s=q_exld[j]+q_extl[j];
      if (m>=53)
	{
          if (m<1023) { res=1.0; POWER2(res,-m); } else res=0.0;
	  res=(q_exld[j]+(s*q+(q_extl[j]-res)));
	  POWER2(res,m);
	}
      else
	{ if (m<=-8)
	    {
	     res=(q_exld[j]+(s*q+q_extl[j]));
	     POWER2(res,m);
	     res-=1;
	    }
	  else
	    {
	      res=1.0;  
	      POWER2(res,-m); 
	      res=((q_exld[j]-res)+(q_exld[j]*q+q_extl[j]*(1+q)));
	      POWER2(res,m);
	    }
      }
    return(res);
  }

/* ------   Prozedure for Range 2   ------------------------------------ */
#ifdef LINT_ARGS
local double q_p2e1(double x)
#else
local double q_p2e1(x)

double x;
#endif
  {
    double  u,v,y,z,q;

    /* Step 1 */
    u=(double) (CUT24(x));
    v=x-u;
    y=u*u*0.5;
    z=v*(x+u)*0.5;

    /* Step 2 */   
    q=(((((((q_exb[8]*x+q_exb[7])*x+q_exb[6])*x+q_exb[5])
	     *x+q_exb[4])*x+q_exb[3])*x+q_exb[2])*x+q_exb[1])*x+q_exb[0];
    q=x*x*x*q;

    /* Schritt 3 */
    if (y>=7.8125e-3)              /* = 2^-7 */
      return ((u+y)+(q+(v+z)) );
    else
      return (x+(y+(q+z)) );
  }

/* ------   Main program with different cases   ----------------------- */

#ifdef LINT_ARGS
local double q_epm1(double x)
#else
local double q_epm1(x)

double x;
#endif
{ 
  double fabsx,res;
  
  if (x<0) fabsx=-x; else fabsx=x;
  if (fabsx<q_ext1)
      {
	res = (q_p2h * x + fabsx) * q_p2mh; 
      }
    else
      { if (q_ex2a<x)
	  res=q_abortr1(OVER_FLOW,&x,3);         /* Overflow */
	else
	  { if (x<q_ext3)
	      {
		 res=-1.0+q_p2mh;
	      }
	    else
	      { if (x==0)
		  res=x;
		else
		  { if ((q_ext4<x) && (x<q_ext5))
		      res=q_p2e1(x);
		    else
		      res=q_p1e1(x);
		  }
	      }
	  }
      }
  return(res);
}
