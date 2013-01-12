/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DynSys.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_DYNSYS_HPP_
#define _CAPD_DYNSYS_DYNSYS_HPP_

#include <string>
#include <iostream>
#include <fstream>
#include <stdexcept>
#include <vector>

#include "capd/auxil/minmax.h"
#include "capd/dynsys/DynSys.h"
#include "capd/vectalg/Norm.hpp"

namespace capd{
namespace dynsys{

template<typename MatrixType>
const typename MatrixType::ScalarType::BoundType OdeNum<MatrixType>::infty=100000;

/////////////////////////////////////////////////////////////////
///
/// Returns an interval bounds for perturbations of ODE
///
///  This functions will be overriden for differential inclusion,
///  for ODEs it throws an exception.
///
/////////////////////////////////////////////////////////////////
//template< typename MatrixType>
//typename DynSys<MatrixType>::VectorType DynSys<MatrixType>::perturbations(const VectorType &iv){
//  throw std::invalid_argument(" This type of DynSys does not provide perturbations bounds ");
//}


/*  Given interval vectors x\subset y, the following method computes
    time h such that \varphi(x,[0,h])\subset y. For this end the affine inclusion
    x+ode.f(y)*[0,h]\subset y is solved for h.
*/

template<typename MatrixType>
typename OdeNum<MatrixType>::ScalarType OdeNum<MatrixType>::stepGuaranteeingBoundsIn(
         const VectorType& x,
         const VectorType& y,
         int& dir
      )
{
// in dir the coordinate causing maximum
// constraint, i.e. requirying the smallest
// h is returne
  return solveAffineInclusion(x,ode.f(y),y,dir);
}



template<typename MatrixType>
typename MatrixType::ScalarType::BoundType OdeNum<MatrixType>::linEscTime(Real a, Real b, Real r)
{
  if(a>r) return -1;
  else{
    if(b>0)
      return ((ScalarType(r)-ScalarType(a))/ScalarType(b)).leftBound();
    else
      return OdeNum<MatrixType>::infty;
  }
}

template<typename MatrixType>
typename MatrixType::ScalarType::BoundType OdeNum<MatrixType>::quadEscTime(Real a, Real b, Real c, Real r)
{
  if(a>r) return -1;
  else{
    if( c == 0)
      return OdeNum<MatrixType>::linEscTime(a,b,r);
    else{
         ScalarType ib = ScalarType(b);
         ScalarType delta = power(ib,2)-4*ScalarType(c)*(ScalarType(a)-ScalarType(r));
//        ScalarType delta=ib^2-4*ScalarType(c)*(ScalarType(a)-ScalarType(r));
      if(c>0 || (delta > 0 && b > 0))
        return ((-b+sqrt(nonnegativePart(delta)))/2/c).leftBound();
      else
        return OdeNum<MatrixType>::infty;
    }
  }
}

template<typename MatrixType>
TimeDoubleton<typename MatrixType::ScalarType::BoundType>
  OdeNum<MatrixType>::linEscTime(const ScalarType &a,const ScalarType &b,const ScalarType &r)
{
  TimeDoubleton<Real> t;
  t.left = OdeNum<MatrixType>::linEscTime(-a.leftBound(),-b.leftBound(),-r.leftBound()),
  t.right = OdeNum<MatrixType>::linEscTime(a.rightBound(),b.rightBound(),r.rightBound());
  return t;
}

template<typename MatrixType>
TimeDoubleton<typename MatrixType::ScalarType::BoundType> OdeNum<MatrixType>::quadEscTime(
      const ScalarType& a,
      const ScalarType& b,
      const ScalarType& c,
      const ScalarType& r
    )
{
  TimeDoubleton<Real> t;
  t.left = OdeNum<MatrixType>::quadEscTime(-a.leftBound(),-b.leftBound(),-c.leftBound(),-r.leftBound());
  t.right = OdeNum<MatrixType>::quadEscTime(a.rightBound(),b.rightBound(),c.rightBound(),r.rightBound());
  return t;
}

template<typename MatrixType>
typename MatrixType::ScalarType::BoundType OdeNum<MatrixType>::linEscTime(const VectorType& x,const VectorType& y,int& dir)
{
  VectorType remainder=ode.f(y);
  TimeDoubleton<Real> the_linEscTime=OdeNum<MatrixType>::linEscTime(x[0],remainder[0],y[0]);
  Real result=capd::min(the_linEscTime.left,the_linEscTime.right);
  dir=0;

  for(int i=1;i<x.dimension();i++)
  {
    the_linEscTime=OdeNum<MatrixType>::linEscTime(x[i],remainder[i],y[i]);
    Real escTime=capd::min(the_linEscTime.left,the_linEscTime.right);
    if( escTime < result )
    {
      result = escTime;
      dir=i;
    }
  }
  return result;
}

template<typename MatrixType>
typename MatrixType::ScalarType::BoundType OdeNum<MatrixType>::quadEscTime(const VectorType& x,const VectorType& y,int& dir)
{
  VectorType firstCoef=ode.f(x);
  VectorType remainder1=ode.f(y);
  VectorType remainder2=ode.df(y)*ode.f(y)/2;
  TimeDoubleton<Real> the_linEscTime = OdeNum<MatrixType>::linEscTime(x[0],remainder1[0],y[0]);
  TimeDoubleton<Real> the_quadEscTime = OdeNum<MatrixType>::quadEscTime(x[0],firstCoef[0],remainder2[0],y[0]);
  Real result = capd::min(
                    capd::max(the_linEscTime.left,the_quadEscTime.left),
                    capd::max(the_linEscTime.right,the_quadEscTime.right)
                );
  dir=0;

  for(int i=1;i<x.dimension();++i)
  {
    TimeDoubleton<Real> the_linEscTime=OdeNum<MatrixType>::linEscTime(x[i],remainder1[i],y[i]);
    TimeDoubleton<Real> the_quadEscTime=OdeNum<MatrixType>::quadEscTime(x[i],firstCoef[i],remainder2[i],y[i]);
    Real escTime = capd::min(
               capd::max(the_linEscTime.left,the_quadEscTime.left),
               capd::max(the_linEscTime.right,the_quadEscTime.right)
            );
    if( escTime < result )
    {
      result = escTime;
      dir=i;
    }
  }
  return result;
}

template<typename MatrixType>
typename MatrixType::ScalarType::BoundType OdeNum<MatrixType>::escTime(const VectorType& x,const VectorType& y,int& dir)
{
  switch(roughEnclosureOrder)
  {
    case 1:
      return linEscTime(x,y,dir);
    case 2:
      return quadEscTime(x,y,dir);
    default:
      throw std::runtime_error("Wrong rough enclosure order!");
  }
}


template<typename MatrixType>
typename OdeNum<MatrixType>::VectorType OdeNum<MatrixType>::enclosureGuaranteeingBounds(
      const VectorType &x,
      int *found
    )
{
  ScalarType trial_step = ScalarType(-0.2,1.2)*step;
  int dim = x.dimension();
  VectorType y(dim), z(dim), Small(dim);

  ScalarType h = ScalarType(0,1)*step;
  Real multf=1.5;
  *found=0;
  int counter=0,limit=10;

  for(int i=0;i<dim;i++)
    Small[i] = ScalarType(-1,1) * 1e-15;

  z = x + trial_step*ode.f(x);
  z += Small; // to be sure that z has noempty interior

  while((!(*found)) && (counter<limit))
  {
    counter++;
    y = x + h*ode.f(z);
    *found=1;
    for(int i=0;i<dim;i++)
    {
      if(!(y[i].subsetInterior(z[i])))
      {
        *found = 0;
        z[i] = y[i];
        ScalarType s;
        z[i].split(s);
        s = multf*s;
        z[i] += s;
      }
    }
  }

  if(!(*found))
  {
    //status="enclosureGuaranteeingBounds - loop limit exceeded";
    diagBadEnlcosure(x);
  }

  return y;
}




template<typename MatrixType>
void OdeNum<MatrixType>::diagBadEnlcosure(const VectorType &x) const
{
  std::ofstream raport("raport.ecl",std::ios::app);
  raport << "-------------------------\n";
  raport << "x=" << x << "\n";
  raport << "step=" << step << "\n";
  raport << "f(x)=" << ode.f(x) << "\n";

  int dim = x.dimension();
  ScalarType trial_step = ScalarType(-0.2,1.2) * step;

  int diag=0;
  VectorType max_r = trial_step*ode.f(x);
  VectorType Ye = x+max_r;

  raport << "Ye=" << Ye << "\n";
  raport << "diam Ye=" ;
  for(int i=0; i<dim; i++)
    raport << rightBound(capd::abs(diam(Ye[i]))) << "  " ;
  raport << "\n";


  MatrixType dv = ode.df(x+max_r);
  capd::vectalg::MaxNorm<VectorType,MatrixType> maxN;
  ScalarType L = maxN(dv);

  if (!(step*L < 1))
  {
    diag=1;
    raport << "hL > 1 \n";
  }
  raport << "hL=" << step*L << "\n";

  Real *diamvect = new Real[dim];
  Real *dfabs = new Real[dim*dim];
  if (!diag)
  {
    int i;

    for(i=0;i<dim; i++)
      diamvect[i] = rightBound(capd::abs(diam(Ye[i])));

    for(i=0;i<dim; i++)
      for(int j=0; j<dim; j++)
        dfabs[i*dim+j]= rightBound(capd::abs(dv[i][j]));

    for(i=0;i<dim;i++)
    {
      Real t=0;
      for(int j=0;j<dim;j++)
        t += dfabs[i*dim+j]*diamvect[j];
      t *= 2.5* rightBound(capd::abs(step));
      if(t > diamvect[i])
      {
        diag=2;
        raport << "5/2 h Dfi/Dxj diam(Ye_j)=t" << t <<
           " >  diam(Ye_i)= " << diamvect[i] <<
           "  ; i=" << i << "\n";
      }
    }// i-loop
  } // if(!diag)

  if(!diag)
  {
    diag=3;
    raport << "unknown reason \n" ;
  }
  delete [] diamvect;
  delete [] dfabs;
}

template<typename MatrixType>
typename OdeNum<MatrixType>::ScalarType OdeNum<MatrixType>::Lipschitz(const VectorType &iv, NormType &n)
{
/* This is Lipschitz constant on iv for the translation map in a flow.
   Hence we need first an estimate for \varphi([0,step],iv)
*/
  int ok;
  VectorType xx = enclosureGuaranteeingBounds(iv,&ok);
  if(!ok)
  {
    std::runtime_error("OdeNum::Lipschitz  error - enclosure not found\n");
  }
/* We get the constant as exp of step times the norm of
   the differential of the vector field
*/
  ScalarType nn = right(n(ode.df(xx)));
  return exp(step*nn).rightBound();
}

template<typename MatrixType>
typename DynSys<MatrixType>::ScalarType DynSys<MatrixType>::Lipschitz(const VectorType &iv,NormType &n)
{
  return n(JacPhi(iv)).rightBound();
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_DYNSYS_HPP_

/// @}
