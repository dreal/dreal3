/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


#ifdef LINT_ARGS
local interval j_acsh(interval x)
#else
local interval j_acsh(x)

interval x;
#endif
{
  interval res;
  if (x.INF<1)                    /* Invalid argument */
  {

      res=q_abortr2(INV_ARG,&x.INF,&x.SUP,23);

  } 
  else
  {
    if (x.INF==x.SUP)             /* point interval */
    { 
        if (x.INF==1) 
          res.INF=res.SUP=0;
        else
        { 
          res.INF=q_acsh(x.INF);
          res.SUP=res.INF*q_acsp;
          res.INF*=q_acsm;
        }
    }
    else
    {
      res.INF=q_acsh(x.INF)*q_acsm;
      res.SUP=q_acsh(x.SUP)*q_acsp;
    }   
  }
  return(res);
}

