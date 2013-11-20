/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


#ifdef LINT_ARGS
local interval j_lg1p(interval x)
#else
local interval j_lg1p(x)

interval x;
#endif
{
  interval res;
  if (x.INF==x.SUP)                   /* point interval */
    { 
      res.INF=q_lg1p(x.INF);
      if (res.INF>=0) 
        {
          res.SUP=res.INF*q_lgpp;
          res.INF*=q_lgpm;
        }
      else
        {
          res.SUP=res.INF*q_lgpm;
          res.INF*=q_lgpp;
        }
    }
  else
    {
      res.INF=q_lg1p(x.INF);
      if (res.INF>=0)
        res.INF*=q_lgpm;
      else
        res.INF*=q_lgpp;
      res.SUP=q_lg1p(x.SUP);
      if (res.SUP>=0)
        res.SUP*=q_lgpp;
      else
        res.SUP*=q_lgpm;
    }   
  return(res);
}

