/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_sinh(interval x)
#else
local interval j_sinh(x)

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
               res.INF=r_pred(x.INF);
               res.SUP=x.INF;
            }
          else
            {
              res.INF=q_sinh(x.INF);
              res.SUP=res.INF*q_snhm;
              res.INF*=q_snhp;
              if (res.SUP>x.INF) res.SUP=x.INF;
            } 
        }
       else 
         {
           if (x.INF<q_minr)
             {         
               res.INF=x.INF;
               if (x.INF==0)
                  res.SUP=0; 
               else
                  res.SUP=r_succ(x.INF);
             }
           else
             {
                res.INF=q_sinh(x.INF);
                res.SUP=res.INF*q_snhp;
                res.INF*=q_snhm;
                if (res.INF<x.INF) res.INF=x.INF;
              }
        }
    }
  else
    {
      if (x.INF<0)
        {
          if (x.INF>-q_minr)
            res.INF=r_pred(x.INF);
          else
            res.INF=q_sinh(x.INF)*q_snhp;          
        }
      else  /* x.INF>=0 */
        {
          if (x.INF<q_minr)
            res.INF=x.INF;        /* includes the case x.INF=0 */
          else 
            {  
              res.INF=q_sinh(x.INF)*q_snhm;
              if (res.INF<x.INF) res.INF=x.INF;
            }
        }
      if (x.SUP<=0)
        {
          if (x.SUP>-q_minr)
            res.SUP=x.SUP;        /* includes the case x.SUP=0 */
          else
            {
               res.SUP=q_sinh(x.SUP)*q_snhm;
               if (res.SUP>x.SUP) res.SUP=x.SUP;
            }          
        }
      else  /* now x.SUP>=0 */
        {
          if (x.SUP<q_minr)
            res.SUP=r_succ(x.SUP);        
          else 
            res.SUP=q_sinh(x.SUP)*q_snhp;
        }
    }   
  return(res);
}

