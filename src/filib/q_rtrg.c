/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 



#ifdef LINT_ARGS
local double q_rtrg(double x, long int k)
#else
local double q_rtrg(x,k)

double x;
long int k;
#endif
{
  double red,h;
  a_diee r1,r2;

  if ((-512<k)&&(k<512)) {
     r2.f = x-k*(q_pih[0]+q_pih[1]);
     red = q_r2tr(r2.f,k);
  } else {
     r1.f =  x-k*q_pih[0];
     h    = k*q_pih[1];
     r2.f = r1.f-h;
     if (r1.ieee.expo == r2.ieee.expo ) 
        red = r1.f - ( ((((k*q_pih[6] + k*q_pih[5]) + k*q_pih[4]) 
                         + k*q_pih[3]) + k*q_pih[2]) + h );
     else
        red = q_r2tr(r2.f,k);  
  } 
  return(red);
}

#ifdef LINT_ARGS
local double q_r2tr(double r, long int k)
#else
local double q_r2tr(r,k)

double r;
long int k;
#endif
{
  double red,h;
  a_diee r1,r2;
  
  r2.f = r;
  h    = k*q_pih[2];
  r1.f = r2.f-h;
  if (r1.ieee.expo == r2.ieee.expo ) 
     red = r2.f - ( (((k*q_pih[6] + k*q_pih[5]) + k*q_pih[4]) 
                         + k*q_pih[3]) + h);
  else {
     h    = k*q_pih[3];
     r2.f = r1.f-h;
     if (r1.ieee.expo == r2.ieee.expo ) 
        red = r1.f - ( ((k*q_pih[6] + k*q_pih[5]) + k*q_pih[4]) + h);
     else {
        h    = k*q_pih[4];
        r1.f = r2.f-h;
        if (r1.ieee.expo == r2.ieee.expo ) 
           red = r2.f - ( (k*q_pih[6] + k*q_pih[5]) + h);
        else {
           h    = k*q_pih[5];
           r2.f = r1.f-h;
           if (r1.ieee.expo == r2.ieee.expo ) 
              red = r1.f - (k*q_pih[6] + h);
           else
              red = r2.f - k*q_pih[6];
        }       
     }
  }

  return(red);
}
