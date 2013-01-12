/////////////////////////////////////////////////////////////////////////////
//
/// @file cndemo2.cpp
///
/// @author kapela  @date 2010-02-09
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) CAPD group
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.


#include "capd/capdlib.h"
#include "capd/map/CnMap.hpp"
#include "capd/dynsys/CnTaylor.hpp"
#include "capd/poincare/TimeMap.hpp"

const int rank = 5;
typedef capd::map::CnMap<capd::IMatrix, rank> IC5Map;
typedef capd::dynsys::CnTaylor<IC5Map> IC5Taylor;

typedef capd::poincare::TimeMap<IC5Taylor> IC5TimeMapTSC;

using namespace capd;
using namespace std;

int main(){

  std::cout << "\n michelson equation \n----------------------\n";
  // vector field
  IC5Map f("par:c;var:x,y,z;fun:y,z,c^2-y-0.5*x*x;");
  f.setParameter("c",DInterval(1.0));

  // ICnTaylor - numerical method for ODE integration
  int order = 10;                 // order of numerical method
  double timeStep = 0.01;         // not important we will use Time Step Control
  IC5Taylor dynsys(f, order, timeStep);

  // initial condition
  IVector v(3);
  double sizeOfSet = 0.005;
  v[0]=0.0;    v[1]= DInterval(1.563-sizeOfSet, 1.563+sizeOfSet);  v[2]=0.0;
  CnRect2Set set(v, IEuclLNorm(), rank);

  // Time map with automatic Time Step Control (TSC)
  IC5TimeMapTSC timeMap(dynsys);
  DInterval time = 2;

  timeMap(time, set);
  cout << set.currentSet().toString();

  return 0;
}

