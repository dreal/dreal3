/// @addtogroup nonAutTest
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file nonAutTest.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <cmath>
#include <stdexcept>
#include <iostream>
#include <string>
#include <cstdlib>

#include "capd/intervals/DoubleInterval.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/vectalg/Norm.hpp"

#include "capd/map/CnMap.hpp"
#include "capd/dynsys/CnTaylor.hpp"
#include "capd/dynsys/NonAutDynSys.h"

#include "capd/dynset/Rect2Set.hpp"
#include "capd/dynset/C1Rect2.hpp"
#include "capd/dynset/C2Rect2.hpp"
#include "capd/dynset/CnRect2.hpp"
#include "capd/dynset/TimeSet.h"

using capd::interval;

typedef capd::vectalg::Vector<interval,0> Vector;
typedef capd::vectalg::Matrix<interval,0,0> Matrix;
typedef capd::vectalg::EuclLNorm<Vector,Matrix> ELNorm;

typedef capd::map::CnMap<Matrix,3> CnMap;
typedef capd::dynsys::CnTaylor<CnMap> CnTaylor;
typedef capd::dynsys::NonAutDynSys<CnTaylor> NACnTaylor;

typedef capd::dynset::Rect2Set<Matrix> Rect2Set;
typedef capd::dynset::C1Rect2<Matrix> C1Rect2;
typedef capd::dynset::C2Rect2<Matrix> C2Rect2;
typedef capd::dynset::CnRect2<Matrix> CnRect2;
typedef capd::dynset::TimeSet<Rect2Set> TimeRect2;
typedef capd::dynset::TimeSet<C1Rect2> TimeC1Rect2;
typedef capd::dynset::TimeSet<C2Rect2> TimeC2Rect2;
typedef capd::dynset::TimeSet<CnRect2> TimeCnRect2;

// -------------------------------------------------------------------------

bool checkVectorIntersection(const Vector& u1, const Vector& u2, interval time)
{
  interval temp;
  if( ! (intersection(u1[0],u2[0],temp) && intersection(u1[1],u2[1],temp) && intersection(u1[2],time,temp)) )
  {
    std::cout << "FATAL ERROR: trajectories have empty intersection!\n";
    std::cout << u1 << std::endl;
    std::cout << u2 << ", " << time << std::endl;
    return false;
  }
  return true;
}

bool checkMatrixIntersection(const Matrix& m1, const Matrix& m2)
{
  interval temp;
  if( !(
         intersection(m1(1,1),m2(1,1),temp) &&
         intersection(m1(1,2),m2(1,2),temp) &&
         intersection(m1(2,1),m2(2,1),temp) &&
         intersection(m1(2,2),m2(2,2),temp) 
       ) 
    )
  {
    std::cout << "FATAL ERROR: the matrices have empty intersection!\n";
    std::cout << m1 << std::endl;
    std::cout << m2 << std::endl;
    return false;  
  }
  return true;
}

template<class C2CoeffType>
bool checkHessianIntersection(const C2CoeffType& c1, const C2CoeffType& c2)
{
  interval temp;
  for(int i=0;i<2;++i)
    for(int j=0;j<2;++j)
      for(int k=j;k<2;++k)
      {
        if(!intersection(c1(i,j,k),c2(i,j,k),temp))
        {
          std::cout << "FATAL ERROR: empty intersection of a coefficient in hessian!\n";
          std::cout << "c1(i,j,k) = " << c1(i,j,k) << std::endl;
          std::cout << "c2(i,j,k) = " << c2(i,j,k) << std::endl;
          return false;
        }
      }
  return true;
}

template<class CnCoeffType>
bool checkThirdOrderIntersection(const CnCoeffType& c1, const CnCoeffType& c2)
{
  interval temp;
  for(int i=0;i<2;++i)
    for(int j=0;j<2;++j)
      for(int k=j;k<2;++k)
        for(int s=k;s<2;++s)
        {
          if(!intersection(c1(i,j,k,s),c2(i,j,k,s),temp))
          {
            std::cout << "FATAL ERROR: empty intersection of a coefficient in hessian!\n";
            std::cout << "c1(i,j,k,s) = " << c1(i,j,k,s) << std::endl;
            std::cout << "c2(i,j,k,s) = " << c2(i,j,k,s) << std::endl;
            return false;
          }
        }
  return true;
}

// -------------------------------------------------------------------------

void showC0Information(const Vector& u1, const Vector& u2, int numberOfSteps, interval step, interval time)
{
  std::cout << "During " << numberOfSteps << " steps with step=" << step << " trajectories have nonempty intersection.\nImages at the end are:\n";
  std::cout << "Solver:      " << u1 << std::endl;
  std::cout << "NonAutSolver:" << u2 << ", " << time << std::endl;
}

void showC1Information(const Matrix& m1, const Matrix& m2)
{
  std::cout << "Monodromy matrix Solver:      " << m1 << std::endl;
  std::cout << "Monodromy matrix NonAutSolver:" << m2 << std::endl;
}

template<class C2CoeffType>
void printHessian(const C2CoeffType& c)
{
  for(int i=0;i<2;++i)
  {
    for(int j=0;j<2;++j)
      for(int k=j;k<2;++k)
        std::cout << c(i,j,k) << " ";
    std::cout << std::endl;
  }
}

template<class C2CoeffType>
void showC2Information(const C2CoeffType& c1, const C2CoeffType& c2)
{
  std::cout << "\nHessian Solver:\n";
  printHessian(c1);
  std::cout << "\nHessian NonAutSolver:\n";
  printHessian(c2);
}

template<class CnCoeffType>
void printC3Coeff(const CnCoeffType& c)
{
  for(int i=0;i<2;++i)
  {
    for(int j=0;j<2;++j)
      for(int k=j;k<2;++k)
        for(int s=k;s<2;++s)
          std::cout << c(i,j,k,s) << " ";
    std::cout << std::endl;
  }
}

template<class CnCoeffType>
void showC3Information(const CnCoeffType& c1, const CnCoeffType& c2)
{
  std::cout << "\nThird order derivatives Solver:\n";
  printC3Coeff(c1);
  std::cout << "\nThird order derivatives NonAutSolver:\n";
  printC3Coeff(c2);
}

// -------------------------- C^0 tests -------------------------------------

bool checkIntersection(Rect2Set&s, TimeRect2& nas)
{
  return checkVectorIntersection(Vector(s),Vector(nas),nas.getCurrentTime());
}

void showFinalInformation(Rect2Set&s, TimeRect2& nas, int numberOfSteps, interval step)
{
  showC0Information(Vector(s),Vector(nas),numberOfSteps,step,nas.getCurrentTime());
  std::cout << std::endl;
}

// -------------------------- C^1 tests -------------------------------------

bool checkIntersection(C1Rect2&s, TimeC1Rect2& nas)
{
   return checkVectorIntersection(Vector(s),Vector(nas),nas.getCurrentTime())
         && checkMatrixIntersection(Matrix(s),Matrix(nas));
}

void showFinalInformation(C1Rect2&s, TimeC1Rect2& nas, int numberOfSteps, interval step)
{
  showC0Information(Vector(s),Vector(nas),numberOfSteps,step,nas.getCurrentTime());
  showC1Information(Matrix(s),Matrix(nas));
  std::cout << std::endl;
}

// -------------------------- C^2 tests -------------------------------------

bool checkIntersection(C2Rect2&s, TimeC2Rect2& nas)
{
   return checkVectorIntersection(Vector(s),Vector(nas),nas.getCurrentTime())
         && checkMatrixIntersection(Matrix(s),Matrix(nas))
         && checkHessianIntersection(s.getC2Coeff(),nas.getC2Coeff());
}

void showFinalInformation(C2Rect2&s, TimeC2Rect2& nas, int numberOfSteps, interval step)
{
  showC0Information(Vector(s),Vector(nas),numberOfSteps,step,nas.getCurrentTime());
  showC1Information(Matrix(s),Matrix(nas));
  showC2Information(s.getC2Coeff(),nas.getC2Coeff());
  std::cout << std::endl;
}

// -------------------------- C^3 tests -------------------------------------

bool checkIntersection(CnRect2&s, TimeCnRect2& nas)
{
   return checkVectorIntersection(Vector(s),Vector(nas),nas.getCurrentTime())
         && checkMatrixIntersection(Matrix(s),Matrix(nas))
         && checkHessianIntersection(s.currentSet(),nas.currentSet())
         && checkThirdOrderIntersection(s.currentSet(),nas.currentSet());
}

void showFinalInformation(CnRect2&s, TimeCnRect2& nas, int numberOfSteps, interval step)
{
  showC0Information(Vector(s),Vector(nas),numberOfSteps,step,nas.getCurrentTime());
  showC1Information(Matrix(s),Matrix(nas));
  showC2Information(s.currentSet(),nas.currentSet());
  showC3Information(s.currentSet(),nas.currentSet());
  std::cout << std::endl;
}

// -------------------------------------------------------------------------

template<class Set1, class Set2>
void Test(CnTaylor& T, NACnTaylor& naT, Set1& s, Set2& nas, int order, int numberOfSteps, std::string description)
{
  naT.setOrder(order);
  T.setOrder(order);

  std::cout << "\n------------------------------------------------------------------------------------------------------------\n\n";
  std::cout << "Computing " << description << " trajectory using Solver and NonAutSolver for the forced pendulum.\nInitial point: " << Vector(s) << std::endl;
  for(int i=0;i<numberOfSteps;++i)
  {
    s.move(T);
    nas.move(naT);
    if( ! checkIntersection(s,nas) )
      exit(1);
  }
  showFinalInformation(s,nas,numberOfSteps,T.getStep());
}

// -------------------------------------------------------------------------

int main(int, char *[])
{
  try
  {
    std::cout.precision(12);
    int order=6;
    interval step(0.125);

    std::string nonAutPendulumFormula = "par:beta;var:x,dx,t;fun:dx,cos(t)-beta*x-sin(x);"; 
    std::string pendulumFormula = "par:beta;var:x,dx,t;fun:dx,cos(t)-beta*x-sin(x),1;"; 
    CnMap naVF(nonAutPendulumFormula);
    CnMap VF(pendulumFormula);
    naVF.setParameter("beta",0.1);
    VF.setParameter("beta",0.1);

    CnTaylor T(VF,order,step);
    CnTaylor temp(naVF,order,step);
    NACnTaylor naT(temp);

    interval coeff[] = {interval(1),interval(2),interval(0)};
    Vector v(3,coeff);
    Vector nav(2,coeff);

// C0 Test
    Rect2Set s(v);
    Rect2Set tempSet(nav);
    TimeRect2 nas(tempSet,0.);
    Test(T,naT,s,nas,10,100,"C0");

// C1Test
    ELNorm N1, N2;
    C1Rect2 c1s(v,N1);
    C1Rect2 tempC1Set(nav,N2);
    TimeC1Rect2 c1nas(tempC1Set,0.);
    Test(T,naT,c1s,c1nas,10,100,"C1");
  
// C2Test
    C2Rect2 c2s(v,N1);
    C2Rect2 tempC2Set(nav,N2);
    TimeC2Rect2 c2nas(tempC2Set,0.);
    Test(T,naT,c2s,c2nas,10,100,"C2");

// C3Test
    CnRect2 c3s(v,N1,3);
    CnRect2 tempC3Set(nav,N2,3);
    TimeCnRect2 c3nas(tempC3Set,0.);
    Test(T,naT,c3s,c3nas,10,100,"C3");

  }catch(std::exception& e)
  {
    std::cout << "Exception caught: " << e.what() << std::endl;
    return -1;
  }
  return 0;
}


/// @}
