/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_asnh(double x)
#else
local double q_asnh(x)

double x;
#endif
{
  double h, res;
  int neg;

  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,22);
  else {
  if ((x>-2.5e-8)&&(x<2.5e-8)) res=x;
  else
  {
    if (x<0) { x=-x; neg=1; } else neg=0;
    if (x>1e150) 
      {
        if (neg==1) res=-(q_l2+q_log1(x));
        else        res=  q_l2+q_log1(x);
      }
    else {
      if (x>=1.25)  /* old: x>=0.03125 */
      { 
         if (neg==1) res=-q_log1(x+sqrt(x*x+1));
         else        res= q_log1(x+sqrt(x*x+1)); 
      }
      else
      {
         h=1/x;
         if (neg==1) res=-q_l1p1(x+x/(sqrt(1+h*h)+h));
         else        res= q_l1p1(x+x/(sqrt(1+h*h)+h));
      }
    }  
  }
  }

  return(res);
}

