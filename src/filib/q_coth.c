/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_coth(double x)
#else
local double q_coth(x)

double x;
#endif
{
  double absx, res;
  int sgn;


  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,21);
  else {

  if ((x>-q_ctht)&&(x<q_ctht))
      res=q_abortr1(OVER_FLOW,&x,21);

  if (x<0) { sgn=-1; absx=-x; }
  else     { sgn=1; absx=x;  }

  if (absx>22.875) res=sgn;
  else if (absx>=q_ln2h) res=sgn*(1+2/(q_ep1(2*absx)-1));
  else res=sgn*(1+2/q_epm1(2*absx));
  }

  return(res);
}
