/// @addtogroup intvtst
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file intvtst.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 
#include <fstream>
#include <cmath>
#include <string>
#include <cstdlib>

// To enable compilation with KRAK uncomment the following line
//#define KRAK
// Note that to  compile with KRAK you will also have to add the krak library to the makefile

#define RESTORE_ROUNDING

#if defined(KRAK)
#  include "capd/krak/krak.h"
#else
# define rootFrame cout
# define waitBt()
# define openGW()
# define closeGW()
#endif

#include "capd/intervals/DoubleInterval.h"

using namespace std;
using capd::rounding::DoubleRounding;
using capd::interval;

#if defined(KRAK)
void test_templates(void)
{
 rootFrame.Clear();
 istringstream text("[1,2.5][3.5,4.5]");

 interval i,j;
 rootFrame << "text=\"" << text << "\"\n";
 text >> i >> j;
 rootFrame << "After reading i and j from text:\n";
 rootFrame << "i = " << i << " j= " << j << "\n";
 rootFrame << "text=\"" << text << "\"\n";
 rootFrame << "After inserting \"i=value of i\" to text:\n";
 text << "i=" << i;
 rootFrame << "text=\"" << text << "\"\n";
 rootFrame << "And indeed i=" << i << "\n";
 waitBt();
}
#endif

void checkResult(interval & iresult, double & dresult){
  if(! iresult.contains(dresult)){
    rootFrame << "ERROR: a rigorous interval result does not contain a non rigorous result"
      << "\n  interval result = " << iresult
      << "\n  double result   = " << dresult <<"\n";
    exit(1);
  }
}
void testExp(interval z)
{
 rootFrame << "z=" << z << "\n";
 interval expintv=exp(z);
 #ifdef RESTORE_ROUNDING
  DoubleRounding::roundNearest();
 #endif
 double dexp=exp(z.rightBound());
 rootFrame << "diff in exp: our intervalexp - standardexp " << (expintv - dexp) << "\n";
 checkResult(expintv, dexp);
}

void testExp()
{
#if defined(KRAK)
 rootFrame.Clear();
#endif
 rootFrame << "Testing exp(interval)\n\n";

 testExp(1.01);
 testExp(0.99);
 testExp(0.5);
// ponizej objawia sie blad, ale tylko przy wylaczonej obsludze niedozwolonej operacji przez
//   procesor INTEL (IM = 0 w bitach maskowania bledow numerycznych

 testExp(12.0);
 waitBt();
}


void test_sin(interval z)
{
 rootFrame << "z=" << z << "\n";
 interval sinintv=sin(z);
 #ifdef RESTORE_ROUNDING
  DoubleRounding::roundNearest();
 #endif 
 double dsin=sin(z.rightBound());
 interval diff = sinintv - dsin;
 rootFrame << "diff in sin: our interval sin  - standard sin " << diff << "\n";
 checkResult(sinintv, dsin);
}

void test_sin()
{
#if defined(KRAK)
 rootFrame.Clear();
#endif
 rootFrame << "Testing sin(interval)\n\n";
 test_sin(interval::pi());
 test_sin(6.0);
 test_sin(1.0);
 waitBt();
}

void show_rounding_test(void)
{
 string result;
 rootFrame << "\nTesting rounding:\n\n";

 DoubleRounding::roundNearest();
 result=(DoubleRounding::test() == 0 ? "OK" : "BAD");
 rootFrame << "Rounding nearest: " << result << "\n";

 DoubleRounding::roundDown();
 result=(DoubleRounding::test() == 1 ? "OK" : "BAD");
 rootFrame << "Rounding down:    " << result << "\n";

 DoubleRounding::roundUp();
 result=(DoubleRounding::test() == 2 ? "OK" : "BAD");
 rootFrame << "Rounding up:      " << result << "\n";

 DoubleRounding::roundCut();
 result=(DoubleRounding::test() == 3 ? "OK" : "BAD");
 rootFrame << "Rounding cut:     " << result << "\n";

 rootFrame << "isWorking:        " << DoubleRounding::isWorking() << "\n";

 waitBt();
}

int main(int, char*[])
{
 //init_fpunit();
 
 #ifdef DEBUGGING
   cerr << "DEBUGGING" << endl;
 #endif

 #ifdef KRAK
  cerr << "KRAK" << endl;
  openGW( 760,580,WHITE,BLACK);
 #endif

// test verifying if rounding mechanism works properly
 show_rounding_test();

#ifdef UP_ROUNDING
 DoubleRounding::roundUp();
#endif

// test for the exp(interval) function - it has problems!!!
 testExp();
    
// simple test of sin function
 test_sin();

// some other tests
#if defined(KRAK)
  test_templates();
#endif
#ifdef KRAK
  closeGW();
#endif
  return 0;
}

/// @}
