/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 




/* --------------------------------------------------------------------- */
/* - Computation of log(x), table lookup method                        - */
/* - We use the idea of Mr. P.T.P. Tang                                - */
/* --------------------------------------------------------------------- */


/* --- Computation of log(x): Range I  --------------------------------- */
#ifdef LINT_ARGS
local double q_p1lg(int m, double fg, double fk, double y)
#else
local double q_p1lg(m,fg,fk,y)

int m;
double fg;
double fk;
double y;
#endif

   {
     int j;
     double l_lead,l_trail,u,q;
     double v;       

     /* Step 1 */
     j=CUTINT((fg-1.0)*128);              /* floor */
     l_lead =m*q_lgld[128]+q_lgld[j];
     l_trail=m*q_lgtl[128]+q_lgtl[j];
   
     /* Step 2: Approximation  */
     u=(fk+fk)/(y+fg);
     v=u*u;
     q=u*v*(q_lgb[0]+v*q_lgb[1]);

     /* Step 3 */
     return(l_lead+(u+(q+l_trail)));
   }


/* ---  Computation of log(x): Range II --------------------------------- */

#ifdef LINT_ARGS
local double q_p2lg(double fk)
#else
local double q_p2lg(fk)

double fk;
#endif

  {  
     double g,q,u,v,u1,f1,f2,u2;

     /* Step 1 */
     g=1/(2+fk);
     u=2*fk*g;
     v=u*u;

     /* Step 2 */
     q=u*v*(q_lgc[0]+v*(q_lgc[1]+v*(q_lgc[2]+v*q_lgc[3])));

     /* Step 3 */
     u1=CUT24(u);                        /* u1 = 24 leading bits of u   */
     f1=CUT24(fk);                       /* f1 = 24 leading bits von fk */
     f2=fk-f1;
     u2=((2*(fk-u1)-u1*f1)-u1*f2)*g;

     /* Step 4 */
     return(u1+(u2+q));
  }



#ifdef LINT_ARGS
local double q_log(double x)
#else
local double q_log(x)

double x;
#endif

{  
  int m;
  double fg,fk,y,res;


  if NANTEST(x)                                           /* Test: x=NaN */
      res=q_abortnan(INV_ARG,&x,6);
  else {
  /* main program with different cases */
    if (x<q_minr)                  /* only positive normalised arguments */
       res=q_abortr1(INV_ARG,&x,6);
    else if (x==1) res=0.0;
    else if ((q_lgt1<x) && (x<q_lgt2)) 
      {
        fk=x-1;
        res=q_p2lg(fk);
      }
    else if (x<=DBL_MAX)
      {
        FREXPO(x,m); 
        m-=1023; 
                                  
        y=x;
        POWER2(y,-m);
        fg=CUTINT(128*y+0.5);          /* exp2(+7)=128       */
        fg=0.0078125*fg;               /* exp2(-7)=0.0078125 */  
        fk=y-fg;

        res=q_p1lg(m,fg,fk,y);
      }
   else res=q_abortr1(INV_ARG,&x,6);
  }

  return(res);

}  /* function q_log */

/* --------------------------------------------------------------------- */
/* - Computation of log1p(x)=log(1+x), table lookup method             - */
/* --------------------------------------------------------------------- */

#ifdef LINT_ARGS
local double q_lg1p(double x)
#else
local double q_lg1p(x)

double x;
#endif

{  
   int m;
   double fg,fk,y,t,h,res;


   if NANTEST(x)                                       /* Test: x=NaN */
       res=q_abortnan(INV_ARG,&x,7);
   else {
   /* main program with different cases */
    if (x<=-1) 
        res=q_abortr1(INV_ARG,&x,7);
    else if (x==0) res=x;
    else if ((-q_lgt5<x) && (x<q_lgt5)) res=x;
                                 /* res=(8*x-ldexp(1.0,-1074))*0.125; */
    else if ((q_lgt3<x) && (x<q_lgt4)) 
      {
        fk=x;
        res=q_p2lg(fk);
      }
    else if (x<=DBL_MAX)
      {
        t=q_lgt6;
        if (x<t) y=1+x;
        else y=x;
        FREXPO(y,m);
        m-=1023;
        
        POWER2(y,-m);
        fg=CUTINT(128*y+0.5);        /* exp2(+7)=128       */
        fg=0.0078125*fg;             /* exp2(-7)=0.0078125 */
        
        if (m<=-2) 
          fk=y-fg;
        else if ((-1<=m) && (m<=52))
          {
            fk=1.0;
            POWER2(fk,-m);
            h=x;
            POWER2(h,-m); 
            fk=(fk-fg)+h;
          }
        else
          {
            fk=1.0;
            POWER2(fk,-m);
            h=x;
            POWER2(h,-m);
            fk=(h-fg)+fk;
          }

        res=q_p1lg(m,fg,fk,y);
      }
   else res=q_abortr1(INV_ARG,&x,6);
  }

  return(res);

  }    /* function q_lg1p */

