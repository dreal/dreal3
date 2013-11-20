/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

/***********************************************************************/  
/* Stand: 18.04.2000                                                   */
/* Autor: cand.math.oec Stefan Traub, IAM, Universitaet Karlsruhe (TH) */    
/***********************************************************************/

#include "fi_lib.h" 


/* ------------------------------------------------------------------- */
/* ----           the function q_expx2 = e^(- x^2)              ------ */
/* ------------------------------------------------------------------- */

#ifdef LINT_ARGS
local double q_expx2(double x)
#else
local double q_expx2(x)

double x;
#endif
{
  double m, res;
  long int z;

  if (x<0.0) x = -x;
  z = CUTINT(x);    /* ganzzahliger Anteil */
  m = x - z;
  if (m>0.5)
    {
       z = z + 1;
       m = m - 1;   /* m <= 0.5  und  x = z + m */
    }
  res = q_expz[z] * q_exp(-(z+z)*m) * q_exp(-m*m);
  if (z==27) res = res * q_exp2(-64);
  
  return(res);
}

/* ------------------------------------------------------------------- */
/* ----                    the function q_erf                   ------ */
/* ------------------------------------------------------------------- */

#ifdef LINT_ARGS
local double q_erf(double x)
#else
local double q_erf(x)

double x;
#endif
{
  double p, q, res, x2;
  
  if NANTEST(x) res = q_abortnan(INV_ARG,&x,27);        /* Test: x=NaN */ 
  else 
  {if (x==q_erft[0]) res = 0.0;
   else 
   {if (x<q_erft[0]) res = -q_erf(-x);
    else 
    {if (x<q_erft[1]) res = q_abortnan(INV_ARG,&x,27); /* UNDERFLOW */  
     else 
     {if (x<q_erft[2]) res = x * q_epA2[0];
      else 
      {if (x<q_erft[3]) 
         { x2 = x*x;
           p = (((q_epA2[4]*x2+q_epA2[3])*x2+q_epA2[2])*x2+q_epA2[1])*x2+q_epA2[0];  
           q = (((q_eqA2[4]*x2+q_eqA2[3])*x2+q_eqA2[2])*x2+q_eqA2[1])*x2+q_eqA2[0];  
           res = x * (p / q);
	 }
       else 
       {if (x<q_erft[4])
          { p = (((((q_epB1[6]*x+q_epB1[5])*x+q_epB1[4])*x+q_epB1[3])*x+q_epB1[2])*x+q_epB1[1])*x+q_epB1[0];
            q = (((((q_eqB1[6]*x+q_eqB1[5])*x+q_eqB1[4])*x+q_eqB1[3])*x+q_eqB1[2])*x+q_eqB1[1])*x+q_eqB1[0];
            res = 1.0 - (q_expx2(x) * (p / q));
          } 
        else 
        {if (x<q_erft[5])
           { p = ((((q_epB2[5]*x+q_epB2[4])*x+q_epB2[3])*x+q_epB2[2])*x+q_epB2[1])*x+q_epB2[0];
             q = (((((q_eqB2[6]*x+q_eqB2[5])*x+q_eqB2[4])*x+q_eqB2[3])*x+q_eqB2[2])*x+q_eqB2[1])*x+q_eqB2[0];
             res = 1.0 - (q_expx2(x) * (p / q));
           }
         else res = 1.0;
	}                     
       }
      }
     }
    }
   }
  }
  return(res);
}


/* ------------------------------------------------------------------- */
/* ----                   the function q_erfc                   ------ */
/* ------------------------------------------------------------------- */

#ifdef LINT_ARGS
local double q_erfc(double x)
#else
local double q_erfc(x)

double x;
#endif
{
  double p, q, res, x2;
  
  if NANTEST(x) res = q_abortnan(INV_ARG,&x,28);        /* Test: x=NaN */ 
  else 
  {if (x<-q_erft[1]) res = 1.0 + q_erf(-x);
   else 
   {if (x<q_erft[1]) res = 1.0; 
    else 
    {if (x<q_erft[2]) res = 1.0 - (x * q_epA2[0]);
     else 
     {if (x<q_erft[3]) 
        { x2 = x*x;
          p = (((q_epA2[4]*x2+q_epA2[3])*x2+q_epA2[2])*x2+q_epA2[1])*x2+q_epA2[0];  
          q = (((q_eqA2[4]*x2+q_eqA2[3])*x2+q_eqA2[2])*x2+q_eqA2[1])*x2+q_eqA2[0];  
          res = 1.0 - (x * (p / q));
	 }
      else 
      {if (x<q_erft[4])
         { p = (((((q_epB1[6]*x+q_epB1[5])*x+q_epB1[4])*x+q_epB1[3])*x+q_epB1[2])*x+q_epB1[1])*x+q_epB1[0];
           q = (((((q_eqB1[6]*x+q_eqB1[5])*x+q_eqB1[4])*x+q_eqB1[3])*x+q_eqB1[2])*x+q_eqB1[1])*x+q_eqB1[0];
           res = q_expx2(x) * (p / q);
          } 
       else 
       {if (x<q_erft[5])
          { p = ((((q_epB2[5]*x+q_epB2[4])*x+q_epB2[3])*x+q_epB2[2])*x+q_epB2[1])*x+q_epB2[0];
            q = (((((q_eqB2[6]*x+q_eqB2[5])*x+q_eqB2[4])*x+q_eqB2[3])*x+q_eqB2[2])*x+q_eqB2[1])*x+q_eqB2[0];
            res = q_expx2(x) * (p / q);
           } 
        else 
        {if (x<q_erft[6])
           { x2 = x*x;
             p = (((q_epB3[4]/x2+q_epB3[3])/x2+q_epB3[2])/x2+q_epB3[1])/x2+q_epB3[0];
             q = (((q_eqB3[4]/x2+q_eqB3[3])/x2+q_eqB3[2])/x2+q_eqB3[1])/x2+q_eqB3[0];
             res = ((q_expx2(x) * p) / (x*q));
            } 
	 else res = q_abortnan(INV_ARG,&x,28);        /* UNDERFLOW */ 
	}             
       }        
      }
     }
    }
   }
  }
  return(res);
}




