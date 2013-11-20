/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_log2(double x)
#else
local double q_log2(x)

double x;
#endif
{
  double res;

  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,8);
  else 
      res=q_log(x)*q_l2i;


  return(res);
}

