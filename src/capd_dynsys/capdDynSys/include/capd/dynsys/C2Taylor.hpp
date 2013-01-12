/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2Taylor.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_C2TAYLOR_HPP_
#define _CAPD_DYNSYS_C2TAYLOR_HPP_

#include <string>
#include <stdexcept>

#include "capd/dynsys/C2Taylor.h"
#include "capd/dynsys/Taylor.hpp"
#include "capd/dynsys/BasicC2Taylor.hpp"
#include "capd/vectalg/Norm.hpp"

namespace capd{
namespace dynsys{

//###########################################################//

template<typename MapType,typename StepControlT>
C2Taylor<MapType,StepControlT>::C2Taylor(MapType& vectorField,int order, const ScalarType& step)
  : BasicTaylor<MapType,StepControlT>(vectorField,order,step),
    Taylor<MapType,StepControlT>(vectorField,order,step),
    BasicC2Taylor<MapType,StepControlT>(vectorField,order,step)
{}

//###########################################################//

template<typename MapType,typename StepControlT>
void C2Taylor<MapType,StepControlT>::c2Enclosure(
         const VectorType &W1, // rough enclosure for x
         const MatrixType &W3, // rough enclosure for V
         const NormType &norm,       // a logarithmic norm
         C2CoeffType& result
      )
{
  int i,j,c,s,r;
  MatrixType DF = (*m_vField)[W1];
  capd::vectalg::EuclNorm<VectorType,MatrixType> tempNorm;
  ScalarType l = norm(DF).rightBound();    // l>= max x\in\W_1 \mu(\frac{df}{dx})

  C2CoeffType temp(dimension());
  m_vField->computeSecondDerivatives(W1,temp);

  for(j=0;j<dimension();++j)
  {
    for(c=j;c<dimension();++c)
    {
      VectorType Bjc(dimension());
      Bjc.clear();
      for(i=0;i<dimension();++i)
      {
        for(s=0;s<dimension();++s)
          for(r=0;r<dimension();++r)
            Bjc[i] += temp(i,s,r) * W3[r][c] * W3[s][j];
      }
      ScalarType delta = tempNorm(Bjc).rightBound();
      typename ScalarType::BoundType size;
      if(l.contains(0.0))
        size = abs(delta*abs(m_step).rightBound()).rightBound();
      else
        size = (abs(delta * (exp(l*m_step)-ScalarType(1.))/l)).rightBound();
      for(i=0;i<dimension();++i)
        result(i,j,c) = ScalarType(-size,size);
    } // c - loop
  } // j - loop
}

// ####################################################################


template<typename MapType,typename StepControlT>
void C2Taylor<MapType,StepControlT>::c2Phi(
      const VectorType& x,
      MatrixType& jac,
      C2CoeffType& hessian
  )
{
  C2CoeffType H(dimension());
  H.clear();
  hessian.clear();
  jac.clear();

  VectorType* coeff = this->m_curve.getCoefficients();
  MatrixType* matrixCoeff = this->m_curve.getMatrixCoefficients();

  computeC2Coeff(x, MatrixType::Identity(dimension()), H, coeff, matrixCoeff, getOrder());

  ScalarType stepPower(1.);
  for(int p=0;p<=getOrder();++p)
  {
    typename C2CoeffType::iterator
                       i1 = hessian.begin(),
                       i2 = hessian.end(),
                       j1 = m_c2MatrixCoeff[p].begin();
    while(i1!=i2)
    {
      *i1 += *j1 * stepPower;
      ++i1;
      ++j1;
    }
    jac += matrixCoeff[p] * stepPower;
    stepPower *= m_step;
  }
}

// ####################################################################

template<typename MapType,typename StepControlT>
void C2Taylor<MapType,StepControlT>::c2Remainder(
      const VectorType& Enc,
      const MatrixType& jacEnc,
      const C2CoeffType& hessEnc,
      VectorType& Rem,
      MatrixType& jacRem,
      C2CoeffType& hessRem
  )
{
  VectorType* remCoeff = this->m_curve.getRemainderCoefficients();
  MatrixType* matrixRemCoeff = this->m_curve.getMatrixRemainderCoefficients();
  computeC2Coeff(Enc, jacEnc, hessEnc, remCoeff, matrixRemCoeff, getOrder()+1);
  ScalarType fac = power(m_step,getOrder()+1);
  Rem = remCoeff[getOrder()+1] * fac;
  jacRem = matrixRemCoeff[getOrder()+1] * fac;

  typename C2CoeffType::iterator i1=hessRem.begin(), i2=hessRem.end(), j=m_c2MatrixCoeff[getOrder()+1].begin();
  while(i1!=i2)
  {
    *i1 = *j * fac;
    ++i1;
    ++j;
  }
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_C2TAYLOR_HPP_

/// @}
