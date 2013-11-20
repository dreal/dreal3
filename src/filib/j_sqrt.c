/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


#ifdef LINT_ARGS
local interval j_sqrt(interval x)
#else
local interval j_sqrt(x)

interval x;
#endif
{
  interval res;
  if (x.INF==x.SUP)                        /* point interval */
    { 
      if (x.INF==0)
        res.INF=res.SUP=0;
      else { res.INF=q_sqrt(x.INF); 
             res.SUP=r_succ(res.INF);
             res.INF=r_pred(res.INF);
           }
    }
  else
    {
      if (x.INF==0) res.INF=0;
      else res.INF=r_pred(q_sqrt(x.INF));
      res.SUP=r_succ(q_sqrt(x.SUP));
    }   
  return(res);
}

