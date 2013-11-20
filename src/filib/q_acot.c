/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_acot(double x)
#else
local double q_acot(x)

double x;
#endif
{
  double res;


  if NANTEST(x)                                       /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,17);
  else {
  /* main program with different cases */
    if ((-1e-17<x)&&(x<1e-17)) res=q_piha;
    else if (x<0) res=q_pi+q_atn1(1.0/x);
    else if (x<1e10) res= q_atn1(1.0/x); 
         else        res=1.0/x;     
  }  

  return(res);
}

