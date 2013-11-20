/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 


/* ------------------------------------------------------------------- */
/* --- utilities                                                   --- */
/* ------------------------------------------------------------------- */

double q_comp(int s, double m, int e)
{
  a_diee su;

  if (!((s==1)||(s==-1))) { m=s; q_abortr1(INV_ARG,&m,26); }
  if ((e<-1023)||(e>1024)) { m=e; q_abortr1(INV_ARG,&m,26); }
  if ((m<0)||(m>=2)) q_abortr1(INV_ARG,&m,26);
  if ((e!=-1023)&&(m<1)) q_abortr1(INV_ARG,&m,26);
  if (e==-1023) m+=1;   /* hidden-bit */
  su.f=m;
  if (s==1) su.ieee.sign=0;
  else      su.ieee.sign=1;
  su.ieee.expo=e+1023;  

  return su.f;
 }         /* end function q_comp */

/* ------------------------------------------------------------------- */

double q_cmps(double m, int e)
{
  a_diee su;

  if ((e<-1023)||(e>1024)) { m=e; q_abortr1(INV_ARG,&m,26); }
  if ((m<=-2)||(m>=2)) q_abortr1(INV_ARG,&m,26);
  if ((e!=-1023)&&(m<1)&&(m>-1)) q_abortr1(INV_ARG,&m,26);
  if (e==-1023) {if (m>=0) m+=1; else m-=1;}   /* hidden-bit */
  su.f=m;
  su.ieee.expo=e+1023;  

  return su.f;
 }         /* end function q_cmps */

/* ------------------------------------------------------------------- */

int q_sign(double x)
{
  a_diee su;

  su.f=x;
  if (su.ieee.sign==0) return +1;
  else                 return -1;
 }         /* end function q_sign */

/* ------------------------------------------------------------------- */

double q_mant(double x)
{
  a_diee su;

  su.f=x;
  su.ieee.sign=0;
  su.ieee.expo=1023;
  if ((-q_minr<x) && (x<q_minr)) su.f-=1;  /* no hidden-bit */

  return su.f;
 }         /* end function q_mant */

/* ------------------------------------------------------------------- */

double q_mnts(double x)
{
  a_diee su;

  su.f=x;
  su.ieee.expo=1023;
  if ((0<=x) && (x<q_minr)) su.f-=1;  /* no hidden-bit */
  if ((-q_minr<x) && (x<0)) su.f+=1;  /* no hidden-bit */

  return su.f;
 }         /* end function q_mnts */

/* ------------------------------------------------------------------- */

int q_expo(double x)
{
  a_diee su;

  su.f=x;

  return (su.ieee.expo-1023);
 }         /* end function q_expo */

/* ------------------------------------------------------------------- */

