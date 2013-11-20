/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_acos(double x)
#else
local double q_acos(x)

double x;
#endif
{
  double res;


  if NANTEST(x)                                       /* Test: x=NaN */
    res=q_abortnan(INV_ARG,&x,15);
  else {
  /* main program with different cases */
    if ((x<-1.0)||(1.0<x))                            /* check argument */
       res=q_abortr1(INV_ARG,&x,15);
    else if ((-1e-17<x)&(x<1e-17)) res=q_piha;
    else if (x<0) res=q_pi+q_atn1(sqrt((1+x)*(1-x))/x);
    else          res=     q_atn1(sqrt((1+x)*(1-x))/x); 
  }

  return(res);
}

