/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_cosh(double x)
#else
local double q_cosh(x)

double x;
#endif
{
  double res;

  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,19);
  else {
    if ((x>=-q_ex2c)&&(x<=q_ex2c))
       res=0.5*(q_ep1(x)+q_ep1(-x));
    else if ((x>=-q_ex2a)&&(x<=q_ex2a))
       res=(0.5*q_exp(x))+(0.5*q_exp(-x));
    else 
      res=q_abortr1(OVER_FLOW,&x,19);                 /* Overflow */
  }


  return(res);
}

