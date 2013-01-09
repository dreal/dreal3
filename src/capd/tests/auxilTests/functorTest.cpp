/// @addtogroup auxilTests
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file functorTest.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2007 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include<iostream>

#include "capd/auxil/Functor.h"
int mul2(double x){
  return int(2*x);
}

double add3(int n){
  return 3.0+n;
}

int main(){
  typedef Functor<int,double> int_f_double;
  typedef Functor<double,int> double_f_int;
  typedef ComposedFunctor<double_f_int,int_f_double> double_f_int_f_double;
  typedef ComposedFunctor<int_f_double,double_f_int> int_f_double_f_int;
  typedef ComposedFunctor<int_f_double_f_int,int_f_double> int_f_double_f_int_f_double;
//  int_f_double fmul2(&mul2);
  int_f_double fmul2(mul2);
  double_f_int fadd3(add3);
  double_f_int_f_double fadd3mul2(fadd3,fmul2);
/*
  int_f_double_f_int_f_double fmul2add3mul2=fmul2*fadd3*fmul2;
  int x=fmul2add3mul2(3.1);
*/
  int x=(fmul2*fadd3*fmul2)(3.1);
  int y=int(2*(3.0+int(2*3.1)));
  std::cout << x << std::endl;
  std::cout << y << std::endl;
}
