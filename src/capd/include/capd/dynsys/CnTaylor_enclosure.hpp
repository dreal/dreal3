/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnTaylor_enclosure.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_CNTAYLOR_ENCLOSURE_HPP_
#define _CAPD_DYNSYS_CNTAYLOR_ENCLOSURE_HPP_

#include <string>
#include <stdexcept>

#include "capd/dynsys/CnTaylor.h"
#include "capd/dynsys/TaylorException.h"
#include "capd/dynsys/enclosure.hpp"
#include "capd/vectalg/Norm.hpp"

namespace capd{
namespace dynsys{

//###########################################################//

template<typename MapType, typename StepControlType>
typename CnTaylor<MapType,StepControlType>::VectorType
CnTaylor<MapType,StepControlType>::enclosure(const VectorType &x)
// the function finds an enclosure for \varphi([0,step],x)
{
  return capd::dynsys::enclosure(*m_vectorField, x, m_step);
}

//###########################################################//


template<typename MapType, typename StepControlType>
typename CnTaylor<MapType,StepControlType>::MatrixType
CnTaylor<MapType,StepControlType>::jacEnclosure(const VectorType &enc, const NormType &the_norm)
// the function finds enclosure for Jacobian matrix (variational part)
// source- "C^1-Lohner algorithm" by P. Zgliczynski
{
  return capd::dynsys::jacEnclosure(*m_vectorField,m_step,enc,the_norm);
}

//###########################################################//

template<typename MapType, typename StepControlType>
void CnTaylor<MapType,StepControlType>::c2Enclosure(
        const VectorType &W1, // rough enclosure for x
        const MatrixType &W3, // rough enclosure for V
        const NormType &norm,       // a logarithmic norm
        C2CoeffType& result
      )
{
  int i,j,c,s,r;
  MatrixType DF = (*m_vectorField)[W1];
  capd::vectalg::EuclNorm<VectorType,MatrixType> tempNorm;
  ScalarType l = norm(DF).rightBound();    // l>= max x\in\W_1 \mu(\frac{df}{dx})

  C2CoeffType temp(dimension());
  m_vectorField->computeSecondDerivatives(W1,temp);

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

//###########################################################//

template<typename MapType,typename StepControlType>
typename CnTaylor<MapType,StepControlType>::VectorType
CnTaylor<MapType,StepControlType>::cnEnclosure(const VectorType& x, const NormType& the_norm, int rank)
{
  int found,i,j;
  VectorType enc = enclosure(x,&found);
  ScalarType logNormOfDerivative;
  MatrixType jacEnc = capd::dynsys::jacEnclosure(*m_vectorField,m_step,enc,the_norm,&logNormOfDerivative);
  m_vectorField->computeDerivatives(enc,m_vectorFieldSeries,0,0,rank);
  setInitialCondition(enc,jacEnc);

// computation of rough enclosure for C^d part, d=2,...,rank
  for(i=2;i<=rank;++i)
  {
    computeNonlinearPart(i);
    Multipointer mp = m_resultSeries.first(i);
    do{
      ScalarType delta = computeDelta(mp).rightBound();
      typename ScalarType::BoundType size;
      if(subset(ScalarType(0.0),logNormOfDerivative))
        size = abs(delta*abs(m_step).rightBound()).rightBound();
      else
        size = (abs(delta * (exp(logNormOfDerivative*m_step)-ScalarType(1.))/logNormOfDerivative)).rightBound();
      ScalarType res(-size,size);
      for(j=0;j<dimension();++j)
        m_resultSeries(j,mp)->value[0] = res;
    }while(m_resultSeries.next(mp));
  }
  return enc;
}

//###########################################################//

template<typename MapType, typename StepControlType>
void CnTaylor<MapType,StepControlType>::cnEnclosure(const VectorType& x, CnCoeffType& coeff, const NormType& the_norm)
{
  cnEnclosure(x,the_norm,coeff.rank());
  for(int i=0;i<dimension();++i)
  {
    typename SeriesContainerType::const_iterator b = m_resultSeries.begin(i), e = m_resultSeries.end(i,coeff.rank());
    typename CnCoeffType::iterator j = coeff.begin(i);
    while(b!=e)
    {
      (*j) = (*b)->value[0];
      ++b;
      ++j;
    }
  }
}

//###########################################################//

template<typename MapType, typename StepControlType>
typename CnTaylor<MapType,StepControlType>::ScalarType
CnTaylor<MapType,StepControlType>::computeDelta(const Multipointer& mp)
{
  VectorType v(dimension());
  for(int i=0;i<dimension();++i)
  {
    v[i] = ( m_resultSeries(i,mp)->value[0] ) = m_nonlinearPart(i,mp)->operator()(0);
  }
  capd::vectalg::EuclNorm<VectorType,MatrixType> tempNorm;
  return tempNorm(v);
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_CNTAYLOR_ENCLOSURE_HPP_

/// @}
