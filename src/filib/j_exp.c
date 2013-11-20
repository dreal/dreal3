/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


#ifdef LINT_ARGS
local interval j_exp(interval x)
#else
local interval j_exp(x)

interval x;
#endif
{
  interval res;
  if (x.INF==x.SUP)                        /* point interval */
    { 
      if (x.INF==0) 
        res.INF=res.SUP=1.0;
      else if (x.INF<=q_mine)
        { 
          res.INF=0.0;
          res.SUP=q_minr;
        }
      else 
        { 
          res.INF=q_exp(x.INF);
          res.SUP=res.INF*q_exep;
          res.INF*=q_exem;
        }
    }
  else
    {
      if (x.INF<=q_mine) 
        res.INF=0.0;
      else 
        res.INF=q_exp(x.INF)*q_exem;
      if (x.SUP<=q_mine)
        res.SUP=q_minr;
      else
        res.SUP=q_exp(x.SUP)*q_exep;
    }   
  if (res.INF<0.0) res.INF=0.0;
  if ((x.SUP<=0.0) && (res.SUP>1.0)) res.SUP=1.0;
  if ((x.INF>=0.0) && (res.INF<1.0)) res.INF=1.0;
  return(res);
}

