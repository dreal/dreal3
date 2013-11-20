/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_sin1(double x, long int k)
#else
local double q_sin1(x,k)

double x;
long int k;
#endif
{
  double res;
  long int m,n;
  double ysq,q;


  /* Special cases  */
  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,10);
  else {
  if ((x<-q_sint[2])||(x>q_sint[2]))
    res=q_abortr1(INV_ARG,&x,10);           /* abs. argument too big */

    /* Argument reduction */
    n=k%4; if(n<0) n+=4; m=n%2;

    /* Approximation */
    ysq=x*x;
    if (m==0) {        /* Approximation sine-function, scheme of Horner */

      if ((-q_sint[3]<x)&&(x<q_sint[3]))
      {
        if (n==0) res=x; 
        else res=-x;
      }
      else {
        q=ysq*(((((((q_sins[5]*ysq)+q_sins[4])
          *ysq+q_sins[3])*ysq+q_sins[2])*ysq+q_sins[1])*ysq)+q_sins[0]);
        if (n==0)
          res=x+x*q;
        else
          res=-(x+x*q);
      }
    } else {           /* Approximation cosine-function, scheme of Horner */
      q=ysq*ysq*(((((((q_sinc[5]*ysq)+q_sinc[4])
        *ysq+q_sinc[3])*ysq+q_sinc[2])*ysq+q_sinc[1])*ysq)+q_sinc[0]);

      if (ysq >= q_sint[0])
        res=0.625+(0.375-(0.5*ysq)+q);
      else if (ysq >= q_sint[1])
        res=0.8125+((0.1875-(0.5*ysq))+q);
      else
        res=1.0-(0.5*ysq - q);
      if (n==3) res=-res; 
    }  /* end if */

  }

  return(res);
}

