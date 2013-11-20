/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


#ifdef LINT_ARGS
local interval j_log(interval x)
#else
local interval j_log(x)

interval x;
#endif
{
  interval res;
  if (x.INF==x.SUP)                  /* point interval */
    { 
      res.INF=q_log(x.INF);
      if (res.INF>=0) 
        {
          res.SUP=res.INF*q_logp;
          res.INF*=q_logm;
        }
      else
        {
          res.SUP=res.INF*q_logm;
          res.INF*=q_logp;
        }
    }
  else
    {
      res.INF=q_log(x.INF);
      if (res.INF>=0)
        res.INF*=q_logm;
      else
        res.INF*=q_logp;
      res.SUP=q_log(x.SUP);
      if (res.SUP>=0)
        res.SUP*=q_logp;
      else
        res.SUP*=q_logm;
    }   
  return(res);
}

