/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_acos(interval x)
#else
local interval j_acos(x)

interval x;
#endif
{
  interval res;
  if (x.INF==x.SUP)                  /* point interval */
    { 
          res.INF=q_acos(x.INF);
          res.SUP=res.INF*q_ccsp;
          res.INF*=q_ccsm;
    }
  else
    {
      res.INF=q_acos(x.SUP)*q_ccsm;
      res.SUP=q_acos(x.INF)*q_ccsp;
    }   
  return(res);
}
