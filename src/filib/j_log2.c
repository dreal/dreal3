/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_log2(interval x)
#else
local interval j_log2(x)

interval x;
#endif
{
 interval res; 
  if (x.INF==x.SUP)                  /* point interval */
    { 
      res.INF=q_log2(x.INF);
      if (res.INF>=0) 
        {
          res.SUP=res.INF*q_lg2p;
          res.INF*=q_lg2m;
        }
      else
        {
          res.SUP=res.INF*q_lg2m;
          res.INF*=q_lg2p;
        }
    }
  else
    {
      res.INF=q_log2(x.INF);
      if (res.INF>=0)
        res.INF*=q_lg2m;
      else
        res.INF*=q_lg2p;
      res.SUP=q_log2(x.SUP);
      if (res.SUP>=0)
        res.SUP*=q_lg2p;
      else
        res.SUP*=q_lg2m;
    }   

 return(res);
}
