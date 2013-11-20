/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_exp2(double x)
#else
local double q_exp2(x)

double x;
#endif
{
 int j;
 long int n,m;
 double r,q,s;
 double res;


 /* Step 1: Special cases  */
 if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,4);
 else {
 if ((-q_ext1<x) && (x<q_ext1))                      /* |x|<2^-54 */
   res=x+1;
 else
  { if (1023<x) 
      res=q_abortr1(OVER_FLOW,&x,4);                 /* Overflow */
    else
      { if (x<-1022)
	  res=0;                                     /* Result: Underflow */ 
	else
	  {
            if (CUTINT(x)==x)                        /* x is integer */
              { res=1.0; POWER2(res,(long int)x); }
            else {                                   /* x is not integer */
    	      /* Step 2 */
	      if (x>0) n=CUTINT((x*32)+0.5);
	      else     n=CUTINT((x*32)-0.5);         /* round (x)      */
	      j=n % 32;                              /* j=n mod 32     */
	      if (j<0) j+=32;                        /* We force j>=0  */
	      m=(n-j)/32;
	      r=x-n*0.03125;

	      /* Step 3 */	  
              q=(((((q_exc[6]*r+q_exc[5])*r+q_exc[4])*r+q_exc[3])*r+q_exc[2])*r 
                            +q_exc[1])*r+q_exc[0];
	      q=r*q;
	   
	      /* Step 4 */
	      s=q_exld[j]+q_extl[j];
	      res=(q_exld[j]+(q_extl[j]+s*q));
	      POWER2(res,m);
            }
	  }
      }
  }
  }

  return(res);
}

