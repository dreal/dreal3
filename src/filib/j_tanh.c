/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_tanh(interval x)
#else
local interval j_tanh(x)

interval x;
#endif
{
  interval res;
  if (x.INF==x.SUP)             /* point interval */
    { 
       if (x.INF<0)
        {
          if (x.INF>-q_minr)
            {
               res.INF=x.INF;
               res.SUP=r_succ(x.INF);
            }
          else
            {
              res.INF=q_tanh(x.INF);
              res.SUP=res.INF*q_tnhm;
              res.INF*=q_tnhp;
              if (res.INF<x.INF) res.INF=x.INF;
            } 
        }
       else 
         {
           if (x.INF<q_minr)
             {         
               res.SUP=x.INF;
               if (x.INF==0)
                  res.INF=0; 
               else
                  res.INF=r_pred(x.INF);
             }
           else
             {
                res.INF=q_tanh(x.INF);
                res.SUP=res.INF*q_tnhp;
                res.INF*=q_tnhm;
                if (res.SUP>x.INF) res.SUP=x.INF;
              }
        }
    }
  else
    {
      if (x.INF<=0)
        {
          if (x.INF>-q_minr)
            res.INF=x.INF;         /* includes the case x.INF=0 */
          else
            {
              res.INF=q_tanh(x.INF)*q_tnhp;
              if (res.INF<x.INF) res.INF=x.INF;
            }          
        }
      else  /* now x.INF>0 */
        {
          if (x.INF<q_minr)
            res.INF=r_pred(x.INF);      
          else 
            res.INF=q_tanh(x.INF)*q_tnhm;
        }
      if (x.SUP<0)
        {
          if (x.SUP>-q_minr)
            res.SUP=r_succ(x.SUP);
          else
            res.SUP=q_tanh(x.SUP)*q_tnhm;          
        }
      else  /* now x.SUP>=0 */
        {
          if (x.SUP<q_minr)
            res.SUP=x.SUP;         /* includes the case x.SUP=0 */       
          else 
            {
              res.SUP=q_tanh(x.SUP)*q_tnhp;
              if (res.SUP>x.SUP) res.SUP=x.SUP;
            }
        }
    }   
if (res.SUP>1.0) res.SUP=1.0;
if (res.INF<-1.0) res.INF=-1.0;

return(res);
}

