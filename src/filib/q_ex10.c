/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



/* --------------------------------------------------------------------- */
/* - Computation of 10^x, table lookup method                          - */
/* - We use the idea of Mr. P.T.P. Tang                                - */
/* --------------------------------------------------------------------- */

#ifdef LINT_ARGS
local double q_ex10(double x)
#else
local double q_ex10(x)

double x;
#endif
{
 int j;
 long int n,m;
 double r,r1,r2,q,s;
 double res;


 /* Step 1: Special cases  */
 if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,5);
 else {
 if ((-q_ext1<x) && (x<q_ext1))                      /* |x|<2^-54 */
   res=x+1;
 else
  { if (q_extm<x) 
      res=q_abortr1(OVER_FLOW,&x,5);                 /* Overflow */
    else
      { if (x<q_extn)
	  res=0;                                     /* Result: Underflow  */ 
	else
	  {
	    /* Step 2 */
	    if (x>0) n=CUTINT((x*q_e10i)+0.5);       /* 32/lg10 =106... */
	    else     n=CUTINT((x*q_e10i)-0.5);       /* round (x)       */
	    j=n % 32;                                /* j=n mod 32      */
	    if (j<0) j+=32;                          /* We force j>=0   */
	    m=(n-j)/32;
	    r1=x-n*q_e1l1;
            r2=-(n*q_e1l2);
	    
	    /* Step 3 */   
            r=r1+r2;
            q=(((((q_exd[6]*r+q_exd[5])*r+q_exd[4])*r+q_exd[3])*r+q_exd[2])*r
                            +q_exd[1])*r+q_exd[0];
	    q=r*q;
            q=r1+(r2+q);

	    /* Step 4 */
	    s=q_exld[j]+q_extl[j];
	    res=(q_exld[j]+(q_extl[j]+s*q));
	    POWER2(res,m);
	  }
      }
  }
  }

  return(res);
}

