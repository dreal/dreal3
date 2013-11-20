/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_tanh(double x)
#else
local double q_tanh(x)

double x;
#endif
{
  double res;


  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,20);
  else {
   if ((-1e-10<x) && (x<1e-10)) res=x; 
   else res=1.0/q_cth1(x); 
  }

  return(res);
}
