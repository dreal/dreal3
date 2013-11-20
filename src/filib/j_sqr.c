/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 

#ifdef LINT_ARGS
local interval j_sqr(interval x)
#else
local interval j_sqr(x)

interval x;
#endif
{
  interval res;

  if (x.INF==x.SUP)                       /* point interval */
    { 
      if (x.INF==0)
        res.INF=res.SUP=0;
      else { res.INF=q_sqr(x.INF); 
             res.SUP=r_succ(res.INF);
             res.INF=r_pred(res.INF);
           }
    }
  else
    {
      if NANTEST(x.INF) {                    /* Test: x.inf=NaN */
        res.INF=q_abortnan(INV_ARG,&x.INF,1);
	res.SUP=0;
      } else if NANTEST(x.SUP) {                /* Test: x.sup=NaN */
        res.SUP=q_abortnan(INV_ARG,&x.SUP,1);
        res.INF=0;
      } else {
        if ((x.INF<-q_sqra)||(x.SUP>q_sqra))
          res=q_abortr2(OVER_FLOW,&x.INF,&x.SUP,1);
        else if (x.INF==0) 
          { res.INF=0; res.SUP=r_succ(x.SUP*x.SUP); }
        else if (x.INF>0)
          { res.INF=r_pred(x.INF*x.INF); res.SUP=r_succ(x.SUP*x.SUP); }
        else if (x.SUP==0)
          { res.INF=0; res.SUP=r_succ(x.INF*x.INF); }
        else if (x.SUP<0)
          { res.INF=r_pred(x.SUP*x.SUP); res.SUP=r_succ(x.INF*x.INF); }
        else 
          { res.INF=0;
            if (-x.INF>x.SUP) res.SUP=r_succ(x.INF*x.INF);
            else              res.SUP=r_succ(x.SUP*x.SUP);          
          }
      } 

    }   

  return(res);
}

