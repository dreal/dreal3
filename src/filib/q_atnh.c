/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_atnh(double x)
#else
local double q_atnh(x)

double x;
#endif
{
  double absx, res;
 

  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,24);
  else {
  if ((x<=-1.0)||(1.0<=x))       
      res=q_abortr1(INV_ARG,&x,24);
  if (x<0) absx=-x; else absx=x;
  if (absx>=q_at3i) res=0.5*q_log1((1+absx)/(1-absx));
  else              res=0.5*q_l1p1((2*absx)/(1-absx));
  if (x<0) res=-res;
  }

  return(res);

}

