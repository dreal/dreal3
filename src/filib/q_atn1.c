/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


#ifdef LINT_ARGS
local double q_atn1(double x)
#else
local double q_atn1(x)

double x;
#endif
{
  double res;
  double absx,ym,y,ysq;
  int ind,sgn;
     
  if (x<0) absx=-x; else absx=x;   
  if (absx<=q_atnt) res=x;
  else {
            if (absx<8) {sgn=1; ym=0;}
            else        {sgn=-1; ym=q_piha; absx=1/absx;}
          
            ind=0;
            while (absx>=q_atnb[ind+1]) ind+=1;
            y=(absx-q_atnc[ind])/(1+absx*q_atnc[ind]);    
            ysq=y*y; 
            res = (y+y*(ysq*(((((q_atnd[5]*ysq+q_atnd[4])
                  *ysq+q_atnd[3])*ysq+q_atnd[2])
                  *ysq+q_atnd[1])*ysq+q_atnd[0])))+q_atna[ind]; 
            if (x<0) res=-(res*sgn+ym);
            else     res= (res*sgn+ym);    
       }
  return(res);
}

