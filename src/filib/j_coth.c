/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_coth(interval x)
#else
local interval j_coth(x)

interval x;
#endif
{
 interval res;

 if (x.SUP<0)
 {
   if (x.INF==x.SUP)             /* point interval */
    { 
      res.INF=q_coth(x.INF);
      res.SUP=res.INF*q_cthm;
      res.INF*=q_cthp;
    }
   else
    {
      res.INF=q_coth(x.SUP)*q_cthp;
      res.SUP=q_coth(x.INF)*q_cthm;
    } 
   if (res.SUP>-1) res.SUP=-1.0;
 }    /* end  if (x.SUP<0) */
 else if(x.INF>0)
 {
   if (x.INF==x.SUP)             /* point interval */
    { 
      res.INF=q_coth(x.INF);
      res.SUP=res.INF*q_cthp;
      res.INF*=q_cthm;
    }
   else
    {
      res.INF=q_coth(x.SUP)*q_cthm;
      res.SUP=q_coth(x.INF)*q_cthp;
    }  
   if (res.INF<1) res.INF=1.0;
 }
 else   /* invalid argument */
 {

   res=q_abortr2(INV_ARG,&x.INF,&x.SUP,21);

 }
 return(res);
}

