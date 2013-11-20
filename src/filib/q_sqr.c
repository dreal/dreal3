/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_sqr(double x)
#else
local double q_sqr(x)

double x;
#endif
{
  double res;

  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,1);
  else {
  if ((x<-q_sqra)||(x>q_sqra))
      res=q_abortr1(OVER_FLOW,&x,1);
  else
      res=x*x;
  }

  return(res);
}

