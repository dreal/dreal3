/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


#ifdef LINT_ARGS
local interval j_acth(interval x)
#else
local interval j_acth(x)

interval x;
#endif
{
 interval res;

 if (x.SUP<-1)
 {
   if (x.INF==x.SUP)             /* point interval */
    { 
      res.INF=q_acth(x.INF);
      res.SUP=res.INF*q_actm;
      res.INF*=q_actp;
    }
   else
    {
      res.INF=q_acth(x.SUP)*q_actp;
      res.SUP=q_acth(x.INF)*q_actm;
    } 
 }    
 else if(x.INF>1)
 {
   if (x.INF==x.SUP)             /* point interval */
    { 
      res.INF=q_acth(x.INF);
      res.SUP=res.INF*q_actp;
      res.INF*=q_actm;
    }
   else
    {
      res.INF=q_acth(x.SUP)*q_actm;
      res.SUP=q_acth(x.INF)*q_actp;
    }  
 }
 else   /* invalid argument */
 {

      res=q_abortr2(INV_ARG,&x.INF,&x.SUP,25);

 }
 return(res);
}

