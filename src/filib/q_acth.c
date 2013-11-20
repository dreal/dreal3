/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_acth(double x)
#else
local double q_acth(x)

double x;
#endif
{
  double absx, res;
 

  if NANTEST(x)                                       /* Test: x=NaN */
    res=q_abortnan(INV_ARG,&x,25);
  else {
    if (x<0) absx=-x; else absx=x;  
    if (absx<=1.0) 
      res=q_abortr1(INV_ARG,&x,25);
    res=0.5*q_l1p1(2.0/(absx-1.0));
    if (x!=absx) res=-res;
  }

  return(res);
}

