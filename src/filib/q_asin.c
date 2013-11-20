/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_asin(double x)
#else
local double q_asin(x)

double x;
#endif
{
  double res;

  if NANTEST(x)                                     /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,14);
  else {
  /* main program with diffent cases */
    if ((x<-1.0)||(1.0<x))                          /* check argument */
      res=q_abortr1(INV_ARG,&x,14);
    else if (x==-1) res=-q_piha;
    else if (x==1) res=q_piha;
    else if ((-q_atnt<=x)&&(x<=q_atnt)) res=x;
    else res=q_atn1(x/sqrt((1.0+x)*(1.0-x))); 
  }

  return(res);
}

