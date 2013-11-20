/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_atan(interval x)
#else
local interval j_atan(x)

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
               res.INF=x.INF;
               res.SUP=r_succ(x.INF);
            }
          else
            {
              res.INF=q_atan(x.INF);
              res.SUP=res.INF*q_ctnm;
              res.INF*=q_ctnp;
              if (res.INF<x.INF) res.INF=x.INF;
            } 
        }
       else 
         {
           if (x.INF<q_atnt)
             {         
               res.SUP=x.INF;
               if (x.INF==0)
                  res.INF=0; 
               else
                  res.INF=r_pred(x.INF);
             }
           else
             {
                res.INF=q_atan(x.INF);
                res.SUP=res.INF*q_ctnp;
                res.INF*=q_ctnm;
                if (res.SUP>x.INF) res.SUP=x.INF;
             }
        }
    }
  else
    {
      if (x.INF<=0)
        {
          if (x.INF>-q_atnt)
            res.INF=x.INF;         /* includes the case x.INF=0 */
          else
            {
              res.INF=q_atan(x.INF)*q_ctnp;
              if (res.INF<x.INF) res.INF=x.INF;
            }          
        }
      else  /* now x.INF>0 */
        {
          if (x.INF<q_atnt)
            res.INF=r_pred(x.INF);      
          else 
            res.INF=q_atan(x.INF)*q_ctnm;
        }
      if (x.SUP<0)
        {
          if (x.SUP>-q_atnt)
            res.SUP=r_succ(x.SUP);
          else
            res.SUP=q_atan(x.SUP)*q_ctnm;          
        }
      else  /* x.SUP>=0 */
        {
          if (x.SUP<q_atnt)
            res.SUP=x.SUP;          /* includes the case x.SUP=0  */       
          else
            { 
              res.SUP=q_atan(x.SUP)*q_ctnp;
              if (res.SUP>x.SUP) res.SUP=x.SUP;
            }
        }
    }   
  return(res);
}

