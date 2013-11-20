/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_lg10(interval x)
#else
local interval j_lg10(x)

interval x;
#endif
{
 interval res;
  if (x.INF==x.SUP)                     /* point interval */
    { 
      res.INF=q_lg10(x.INF);
      if (res.INF>=0) 
        {
          res.SUP=res.INF*q_l10p;
          res.INF*=q_l10m;
        }
      else
        {
          res.SUP=res.INF*q_l10m;
          res.INF*=q_l10p;
        }
    }
  else
    {
      res.INF=q_lg10(x.INF);
      if (res.INF>=0)
        res.INF*=q_l10m;
      else
        res.INF*=q_l10p;
      res.SUP=q_lg10(x.SUP);
      if (res.SUP>=0)
        res.SUP*=q_l10p;
      else
        res.SUP*=q_l10m;
    }   

 return(res);
}
