/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnTaylor_remainder.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_CNTAYLOR_REMAINDER_HPP_
#define _CAPD_DYNSYS_CNTAYLOR_REMAINDER_HPP_

namespace capd{
namespace dynsys{

template<typename MapType, typename StepControlType>
typename CnTaylor<MapType,StepControlType>::VectorType
CnTaylor<MapType,StepControlType>::Remainder(const VectorType &iv)
{
  int found;
  VectorType enc  = enclosure(iv,&found);
  computeVectorFieldSeries(enc,0,m_order);
  this->setInitialCondition(enc);
  VectorType result(dimension());
  for(int i=0;i<dimension();++i)
    result[i] = m_resultSeries(i)->value[m_order];

  return (result*=power(m_step,m_order));
}

//###########################################################//

template<typename MapType, typename StepControlType>
void CnTaylor<MapType,StepControlType>::JacRemainder(
      const VectorType &vecEnclosure,
      const MatrixType &jacEnclosure,
      VectorType& Remainder,
      MatrixType& jacRemainder
    )
{
  computeVectorFieldSeries(vecEnclosure,1,m_order);
  this->setInitialCondition(vecEnclosure,jacEnclosure);
  computeResultSeries(1,m_order);
  for(int i=0;i<dimension();++i)
  {
    Remainder[i] = m_resultSeries(i)->value[m_order];
    for(int j=0;j<dimension();++j)
      jacRemainder(i+1,j+1) = m_resultSeries(i,j)->value[m_order];
  }
  ScalarType factor = power(m_step,m_order);
  Remainder *= factor;
  jacRemainder *= factor;
}

//###########################################################//

template<typename MapType, typename StepControlType>
void CnTaylor<MapType,StepControlType>::c2Remainder(
      const VectorType& vecEnclosure,
      const MatrixType& jacEnclosure,
      const C2CoeffType& hessianEnclosure,
      VectorType& Remainder,
      MatrixType& jacRemainder,
      C2CoeffType& hessianRemainder // here a result is stored
    )
{
  computeVectorFieldSeries(vecEnclosure,2,m_order);
  this->setInitialCondition(vecEnclosure,jacEnclosure,hessianEnclosure);
  computeResultSeries(2,m_order);
  for(int i=0;i<dimension();++i)
  {
    Remainder[i] = m_resultSeries(i)->value[m_order];
    for(int j=0;j<dimension();++j)
    {
      jacRemainder(i+1,j+1) = m_resultSeries(i,j)->value[m_order];
      for(int c=j;c<dimension();++c)
        hessianRemainder(i,j,c) = m_resultSeries(i,j,c)->value[m_order];
    }
  }
  ScalarType factor = power(m_step,m_order);
  Remainder *= factor;
  jacRemainder *= factor;
  typename C2CoeffType::iterator b=hessianRemainder.begin(), e = hessianRemainder.end();
  while(b!=e)
  {
    (*b) *= factor;
    ++b;
  }
}

//###########################################################//

template<typename MapType, typename StepControlType>
void CnTaylor<MapType,StepControlType>::cnRemainder(const VectorType& x, const NormType& a_norm, CnCoeffType& result)
{
  int rank = result.rank();
  VectorType enc = cnEnclosure(x,a_norm,rank);
  computeVectorFieldSeries(enc,rank,m_order);
  computeResultSeries(rank,m_order);
  ScalarType factor = power(m_step,m_order);
  for(int i=0;i<dimension();++i)
  {
    typename SeriesContainerType::const_iterator b=m_resultSeries.begin(i), e=m_resultSeries.end(i,rank);
    typename CnCoeffType::iterator j = result.begin(i);
    while(b!=e)
    {
      (*j) = ((*b)->value[m_order]) * factor;
      ++b;
      ++j;
    }
  }
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_CNTAYLOR_REMAINDER_HPP_

/// @}
