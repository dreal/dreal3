/*********************************************************************/
/*       fi_lib  --- A fast interval library (Version 1.2)           */
/*        (For copyright and info`s see file "fi_lib.h")             */
/*********************************************************************/

#include "fi_lib.h" 

#include <stdlib.h>   /* for exit */

/* ----------- error handling for argument == NaN ---------------*/
#ifdef LINT_ARGS
local double q_abortnan(int n, double *x, int fctn)
#else
local double q_abortnan(n,x,fctn)

int n;
double *x;
int fctn;
#endif
{
  printf("\n*** Error in fi_lib (V1.2): Function: ");
  switch(fctn){
    case  0: printf("q_sqrt"); break; 
    case  1: printf("q_sqr "); break; 
    case  2: printf("q_exp "); break; 
    case  3: printf("q_epm1"); break; 
    case  4: printf("q_exp2"); break; 
    case  5: printf("q_ex10"); break; 
    case  6: printf("q_log "); break; 
    case  7: printf("q_lg1p"); break; 
    case  8: printf("q_log2"); break; 
    case  9: printf("q_lg10"); break; 
    case 10: printf("q_sin "); break; 
    case 11: printf("q_cos "); break; 
    case 12: printf("q_tan "); break; 
    case 13: printf("q_cot "); break; 
    case 14: printf("q_asin"); break; 
    case 15: printf("q_acos"); break; 
    case 16: printf("q_atan"); break; 
    case 17: printf("q_acot"); break; 
    case 18: printf("q_sinh"); break; 
    case 19: printf("q_cosh"); break; 
    case 20: printf("q_tanh"); break; 
    case 21: printf("q_coth"); break; 
    case 22: printf("q_asnh"); break; 
    case 23: printf("q_acnh"); break; 
    case 24: printf("q_atnh"); break; 
    case 25: printf("q_acth"); break; 
    case 27: printf("q_erf "); break; 
    case 28: printf("q_erfc"); break; 
  }
  printf("\n*** Error in fi_lib (V1.2): Argument == NaN ! ***\n");
  exit(n);
  return(*x); 
}

/* ------------ error handling for point arguments ---------------*/
#ifdef LINT_ARGS
local double q_abortr1(int n, double *x, int fctn)
#else
local double q_abortr1(n,x,fctn)

int n;
double *x;
int fctn;
#endif
{
  printf("\n*** Error in fi_lib (V1.2): Function: ");
  switch(fctn){
    case  0: printf("q_sqrt"); break; 
    case  1: printf("q_sqr "); break; 
    case  2: printf("q_exp "); break; 
    case  3: printf("q_epm1"); break; 
    case  4: printf("q_exp2"); break; 
    case  5: printf("q_ex10"); break; 
    case  6: printf("q_log "); break; 
    case  7: printf("q_lg1p"); break; 
    case  8: printf("q_log2"); break; 
    case  9: printf("q_lg10"); break; 
    case 10: printf("q_sin "); break; 
    case 11: printf("q_cos "); break; 
    case 12: printf("q_tan "); break; 
    case 13: printf("q_cot "); break; 
    case 14: printf("q_asin"); break; 
    case 15: printf("q_acos"); break; 
    case 16: printf("q_atan"); break; 
    case 17: printf("q_acot"); break; 
    case 18: printf("q_sinh"); break; 
    case 19: printf("q_cosh"); break; 
    case 20: printf("q_tanh"); break; 
    case 21: printf("q_coth"); break; 
    case 22: printf("q_asnh"); break; 
    case 23: printf("q_acnh"); break; 
    case 24: printf("q_atnh"); break; 
    case 25: printf("q_acth"); break; 
    case 26: printf("q_comp"); break;
    case 27: printf("q_erf "); break; 
    case 28: printf("q_erfc"); break; 
  }
  if (n==INV_ARG) 
    printf("\n*** Error in fi_lib (V1.2): Invalid argument ! ***\n");
  else
    printf("\n*** Error in fi_lib (V1.2): Overflow (result) ! ***\n");
    printf("*** Error in fi_lib (V1.2): Argument x = %24.15e \n",*x);
  exit(n);
  return(*x);
}


/* ------------- error handling for interval arguments -------------*/
#ifdef LINT_ARGS
local interval q_abortr2(int n, double *x1, double *x2, int fctn)
#else
local interval q_abortr2(n,x1,x2,fctn)

int n;
double *x1;
double *x2;
int fctn;
#endif
{
  interval res;
  printf("\n*** Error in fi_lib (V1.2): Function: ");
  switch(fctn){
    case  0: printf("j_sqrt"); break; 
    case  1: printf("j_sqr "); break; 
    case  2: printf("j_exp "); break; 
    case  3: printf("j_epm1"); break; 
    case  4: printf("j_exp2"); break; 
    case  5: printf("j_ex10"); break; 
    case  6: printf("j_log "); break; 
    case  7: printf("j_lg1p"); break; 
    case  8: printf("j_log2"); break; 
    case  9: printf("j_lg10"); break; 
    case 10: printf("j_sin "); break; 
    case 11: printf("j_cos "); break; 
    case 12: printf("j_tan "); break; 
    case 13: printf("j_cot "); break; 
    case 14: printf("j_asin"); break; 
    case 15: printf("j_acos"); break; 
    case 16: printf("j_atan"); break; 
    case 17: printf("j_acot"); break; 
    case 18: printf("j_sinh"); break; 
    case 19: printf("j_cosh"); break; 
    case 20: printf("j_tanh"); break; 
    case 21: printf("j_coth"); break; 
    case 22: printf("j_asnh"); break; 
    case 23: printf("j_acnh"); break; 
    case 24: printf("j_atnh"); break; 
    case 25: printf("j_acth"); break; 
    case 27: printf("q_erf "); break; 
    case 28: printf("q_erfc"); break; 
  }
  if (n==INV_ARG) 
    printf("\n*** Error in fi_lib (V1.2): Invalid argument ! ***\n");
  else 
    printf("\n*** Error in fi_lib (V1.2): Overflow (result) ! ***\n");
  printf("*** Error in fi_lib (V1.2): Argument x.INF = %24.15e \n",*x1);
  printf("*** Error in fi_lib (V1.2): Argument x.SUP = %24.15e \n",*x2);

  exit(n);

  res.INF=*x1; res.SUP=*x2;
  return(res);
}

/* ------------ error handling for point arguments ---------------*/
#ifdef LINT_ARGS
local double q_abortdivd(int n, double *x)
#else
local double q_abortdivd(n, x)

int n;
double *x;
#endif
{
  printf("\n*** Error in fi_lib (V1.2): Function: div_id");
  printf("\n*** Error in fi_lib (V1.2): Division by zero ! ***\n");
  printf("*** Error in fi_lib (V1.2): x = %24.15e \n",*x);

  exit(n);

  return(*x);
}

/* ------------- error handling for interval arguments -------------*/
#ifdef LINT_ARGS
local interval q_abortdivi(int n, double *x1, double *x2)
#else
local interval q_abortdivi(n,x1,x2)

int n;
double *x1;
double *x2;
#endif
{
  interval res;
  printf("\n*** Error in fi_lib (V1.2): Function: div_ii");
  printf("\n*** Error in fi_lib (V1.2): Division by zero ! ***\n");
  printf("*** Error in fi_lib (V1.2): x.INF = %24.15e \n",*x1);
  printf("*** Error in fi_lib (V1.2): x.SUP = %24.15e \n",*x2);

  exit(n);

  res.INF=*x1; res.SUP=*x2;
  return(res);
}

