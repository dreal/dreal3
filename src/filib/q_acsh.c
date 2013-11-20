/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_acsh(double x)
#else
local double q_acsh(x)

double x;
#endif
{
  double res;
 

  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,23);
  else {
     if (x<1) res=q_abortr1(INV_ARG,&x,23);
     if (x<1.025) res=q_l1p1(x-1+sqrt((x-1)*(x+1)));
     else if (x>1e150) res=q_l2+q_log1(x);
          else         res=q_log1(x+sqrt((x-1)*(x+1)));
  }

  return(res);
}

