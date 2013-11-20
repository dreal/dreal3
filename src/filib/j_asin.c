/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_asin(interval x)
#else
local interval j_asin(x)

interval x;
#endif
{
  interval res;
  if (x.INF==x.SUP)             /* point interval */
    { 
       if (x.INF<0)
        {
          if (x.INF>-q_atnt)
            {
               res.INF=r_pred(x.INF);
               res.SUP=x.INF;
            }
          else
            {
              res.INF=q_asin(x.INF);
              res.SUP=res.INF*q_csnm;
              res.INF*=q_csnp;
              if (res.SUP>x.INF) res.SUP=x.INF;
            } 
        }
       else 
         {
           if (x.INF<q_atnt)
             {         
               res.INF=x.INF;
               if (x.INF==0)
                  res.SUP=0; 
               else
                  res.SUP=r_succ(x.INF);
             }
           else
             {
                res.INF=q_asin(x.INF);
                res.SUP=res.INF*q_csnp;
                res.INF*=q_csnm;
                if (res.INF<x.INF) res.INF=x.INF;
              }
        }
    }
  else
    {
      if (x.INF<0)
        {
          if (x.INF>-q_atnt)
            res.INF=r_pred(x.INF); 
          else
            res.INF=q_asin(x.INF)*q_csnp;          
        }
      else  /* x.INF>=0 */
        {
          if (x.INF<q_atnt)
            res.INF=x.INF;      
          else 
            {
              res.INF=q_asin(x.INF)*q_csnm;
              if (res.INF<x.INF) res.INF=x.INF;
            }
        }
      if (x.SUP<=0)
        {
          if (x.SUP>-q_atnt)
            res.SUP=x.SUP;
          else
            {
              res.SUP=q_asin(x.SUP)*q_csnm;
              if (res.SUP>x.SUP) res.SUP=x.SUP;
            }          
        }
      else  /* x.SUP>0 */
        {
          if (x.SUP<q_atnt)
            res.SUP=r_succ(x.SUP);         /* includes the case x.SUP=0 */       
          else 
            res.SUP=q_asin(x.SUP)*q_csnp;
        }
    }   
  return(res);
}
