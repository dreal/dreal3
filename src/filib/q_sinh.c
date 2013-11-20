/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_sinh(double x)
#else
local double q_sinh(x)

double x;
#endif
{
  double absx, h;
  int sgn;
  double res;


  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,18);
  else {
  if (x<0) {sgn=-1; absx=-x;}
  else     {sgn=1;  absx=x; }
 
  if (absx>q_ex2a)
      res=q_abortr1(OVER_FLOW,&x,18);                 /* Overflow */

  if (absx<2.5783798e-8) res=x;
  else if (absx>=0.662) 
    {
       h=q_ep1(absx);
       res=sgn*0.5*(h-1.0/h);
    }
  else
    {
       h=q_epm1(absx);
       res=sgn*0.5*(h+h/(h+1.0));
    }

  }
  return(res);
}

