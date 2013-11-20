/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_sqrt(double x)
#else
local double q_sqrt(x)

double x;
#endif
{
  double res;

  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,0);
  else {
  if (x<0)
      res=q_abortr1(INV_ARG,&x,0);
  else
      res=sqrt(x);
  }

  return(res);
}

