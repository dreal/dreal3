/**
 *  @file diffInclExample.cpp
 *
 *  Created on: 2009-11-13
 *      Author: kapela
 */

// it provides IVector, IMatrix, IMap
#include "capd/simpleCapdLib.h"

#include "capd/diffIncl/DiffInclusionLN.hpp"
#include "capd/diffIncl/DiffInclusionCW.hpp"
#include "capd/diffIncl/InclRect2Set.hpp"
#include "capd/diffIncl/MultiMap.h"
#include "capd/vectalg/Norm.hpp"
#include "capd/poincare/PoincareMap.hpp"
#include <iostream>

using namespace capd;

typedef capd::vectalg::EuclLNorm<IVector, IMatrix> EuclLNorm;
typedef capd::vectalg::MaxNorm<IVector, IMatrix> MaxNorm;

typedef capd::diffIncl::InclRect2Set<IMatrix> InclRect2Set;
typedef capd::diffIncl::MultiMap<IMap> IMultiMap;
typedef capd::diffIncl::DiffInclusionCW<IMultiMap> DiffInclusionCW;
typedef capd::diffIncl::DiffInclusionLN<IMultiMap> DiffInclusionLN;
typedef capd::poincare::PoincareMap<DiffInclusionCW> DiffPoincare;

/**
 *  In this example we integrate differential inclusion based on rossler equation
 *     x' in -(y+z) + [e]
 *     y' in x+b*y + [e]
 *     z' in b+z*(x-a) + [e]
 *  where
 *    a=5.7,  b=0.2,
 *    [e] = [-eps, eps]
 *  We use two different method based on component wise estimates and on logarithmic norm
 *  and compare results.
 */
void RosslerExample() {

  // f is an unperturbed vector field
  IMap f("var:x,y,z,a,b;fun:-(y+z),x+b*y,b+z*(x-a);");
  f.setParameter("a", DInterval(57.) / DInterval(10.));                 // note that 5.7 is not a representable number
  f.setParameter("b", DInterval(2.) / DInterval(10.));

  // we define a perturbation
  double eps = 1.0e-4;      //  maximal forcing (perturbation)
  IMap perturb("var:x,y,z,e;fun:e,e,e;");
  perturb.setParameter("e", DInterval(-eps, eps));

  // We set right hand side of differential inclusion to f + perturb
  IMultiMap rhs(f, perturb);

  double timeStep = 1. / 512.; //  time step for integration
  int order = 10; //  order of Taylor method

  // We set up two differential inclusions (they differ in the way they handle perturbations)
  DiffInclusionCW diffInclCW(rhs, order, timeStep, MaxNorm());
  DiffInclusionLN diffInclLN(rhs, order, timeStep, EuclLNorm());

  // Starting point for computations
  IVector x1(3);
  x1[0] = 0.0;    x1[1] = -10.3;      x1[2] = 0.03;

  // We prepare sets that know how to propagate themselves with differential inclusions
  InclRect2Set setLN(x1),
               setCW(x1);

  // We do the numberOfSets steps
  int numberOfSteps = 10;
  for(int i = 0; i < numberOfSteps; ++i) {
    setLN.move(diffInclLN);
    setCW.move(diffInclCW);
  }

  // We compute interval vector that covers given set.
  IVector resultLN = IVector(setLN),
          resultCW = IVector(setCW);
  std::cout.precision(16);
  std::cout << "\n\n Method based on logarithmic norms : \n " << resultLN
      << "\n  diam = " << size(resultLN) << "\n";
  std::cout << "\n\n Method based on component wise estimates : \n " << resultCW
      << "\n  diam = " << size(resultCW) << "\n";

}

int main() {
  RosslerExample();
  return 0;
} // END
