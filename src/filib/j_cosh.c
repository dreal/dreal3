/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_cosh(interval x)
#else
local interval j_cosh(x)

interval x;
#endif
{
 interval res;

 if (x.SUP<0)
 {
   if (x.INF==x.SUP)             /* point interval */
    { 
      res.INF=q_cosh(x.INF);
      res.SUP=res.INF*q_cshp;
      res.INF*=q_cshm;
    }
   else
    {
      res.INF=q_cosh(x.SUP)*q_cshm;
      res.SUP=q_cosh(x.INF)*q_cshp;
    }
    if (res.INF<1.0) res.INF=1.0;
 }    /* end  if (x.SUP<0) */
 else if (x.INF>0)
 {
   if (x.INF==x.SUP)             /* point interval */
    { 
      res.INF=q_cosh(x.INF);
      res.SUP=res.INF*q_cshp;
      res.INF*=q_cshm;
    }
   else
    {
      res.INF=q_cosh(x.INF)*q_cshm;
      res.SUP=q_cosh(x.SUP)*q_cshp;
    }  
    if (res.INF<1.0) res.INF=1.0;
 }
 else if (-x.INF>x.SUP)
 {
      res.INF=1.0;
      res.SUP=q_cosh(x.INF)*q_cshp;
 }
 else
 {
      res.INF=1.0;
      res.SUP=q_cosh(x.SUP)*q_cshp;
 }
return(res);
}
