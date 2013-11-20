/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


#ifdef LINT_ARGS
local interval j_asnh(interval x)
#else
local interval j_asnh(x)

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
              res.INF=q_asnh(x.INF);
              res.SUP=res.INF*q_asnm;
              res.INF*=q_asnp;
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
                res.INF=q_asnh(x.INF);
                res.SUP=res.INF*q_asnp;
                res.INF*=q_asnm;
                if (res.SUP>x.INF) res.SUP=x.INF;
              }
        }
    }
  else
    {
      if (x.INF<=0)
        {
          if (x.INF>-q_minr)
            res.INF=x.INF;         /* includes the case x.INF=0  */
          else
            {
              res.INF=q_asnh(x.INF)*q_asnp;
              if (res.INF<x.INF) res.INF=x.INF;
            }          
        }
      else  /* now x.INF>0 */
        {
          if (x.INF<q_minr)
            res.INF=r_pred(x.INF);      
          else 
            res.INF=q_asnh(x.INF)*q_asnm;
        }
      if (x.SUP<0)
        {
          if (x.SUP>-q_minr)
            res.SUP=r_succ(x.SUP);
          else
            res.SUP=q_asnh(x.SUP)*q_asnm;          
        }
      else  /* now x.SUP>=0 */
        {
          if (x.SUP<q_minr)
            res.SUP=x.SUP;         /* includes the case x.SUP=0 */    
          else
            { 
              res.SUP=q_asnh(x.SUP)*q_asnp;
              if (res.SUP>x.SUP) res.SUP=x.SUP;
            }
        }
    }   
  return(res);
}

