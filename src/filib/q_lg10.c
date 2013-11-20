/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_lg10(double x)
#else
local double q_lg10(x)

double x;
#endif
{
  double res;

  
  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,9);
  else
      res=q_log(x)*q_l10i;


  return(res);
}

