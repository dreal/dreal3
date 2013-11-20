/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local interval j_acot(interval x)
#else
local interval j_acot(x)

interval x;
#endif
{
  interval res;
  if (x.INF==x.SUP)                     /* point interval  */
    { 
          res.INF=q_acot(x.INF);
          res.SUP=res.INF*q_cctp;
          res.INF*=q_cctm;
    }
  else
    {
      res.INF=q_acot(x.SUP)*q_cctm;
      res.SUP=q_acot(x.INF)*q_cctp;
    }   
  return(res);
}
