/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnTaylor_phi.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_CNTAYLOR_PHI_HPP_
#define _CAPD_DYNSYS_CNTAYLOR_PHI_HPP_

#include "capd/dynsys/CnTaylor.h"

namespace capd{
namespace dynsys{

template<typename MapType, typename StepControlType>
typename CnTaylor<MapType,StepControlType>::VectorType
CnTaylor<MapType,StepControlType>::Phi(const VectorType &iv)
{
  computeVectorFieldSeries(iv,0,m_order-1);
  this->setInitialCondition(iv);
  VectorType result(dimension());
  int i,j;
  for(i=0;i<dimension();++i)
    result[i] = m_resultSeries(i)->value[m_order-1];

  for(j=m_order-2;j>=0;--j)
  {
    for(i=0;i<dimension();++i)
      result[i] = result[i]*m_step + m_resultSeries(i)->value[j];
  }
  return result;
}

//###########################################################//

template<typename MapType, typename StepControlType>
typename CnTaylor<MapType,StepControlType>::MatrixType
CnTaylor<MapType,StepControlType>::JacPhi(const VectorType &iv)
{
  this->setInitialCondition(iv,MatrixType::Identity(dimension()));
  computeVectorFieldSeries(iv,1,m_order-1);
  computeResultSeries(1,m_order-1);

  MatrixType result(dimension(),dimension());

  int i,j,c;
  for(i=0;i<dimension();++i)
    for(j=0;j<dimension();++j)
      result(i+1,j+1) = m_resultSeries(i,j)->value[m_order-1];

  for(c=m_order-2;c>=0;--c)
    for(i=0;i<dimension();++i)
      for(j=0;j<dimension();++j)
        result(i+1,j+1) = result(i+1,j+1)*m_step + m_resultSeries(i,j)->value[c];
  return result;
}

//###########################################################//

template<typename MapType, typename StepControlType>
void CnTaylor<MapType,StepControlType>::c2Phi(const VectorType& iv, MatrixType& jac, C2CoeffType& hessian)
{
  this->setInitialCondition(iv,MatrixType::Identity(dimension()));
  computeVectorFieldSeries(iv,2,m_order-1);
  computeResultSeries(2,m_order-1);

  int i,j,c,r;
  for(i=0;i<dimension();++i)
    for(j=0;j<dimension();++j)
    {
      jac(i+1,j+1) = m_resultSeries(i,j)->value[m_order-1];
      for(r=j;r<dimension();++r)
        hessian(i,j,r) = m_resultSeries(i,j,r)->value[m_order-1];
    }
  for(c=m_order-2;c>=0;--c)
    for(i=0;i<dimension();++i)
      for(j=0;j<dimension();++j)
      {
        jac(i+1,j+1) = jac(i+1,j+1)*m_step + m_resultSeries(i,j)->value[c];
        for(r=j;r<dimension();++r)
          hessian(i,j,r) = hessian(i,j,r)*m_step + m_resultSeries(i,j,r)->value[c];
      }
}

//###########################################################//

template<typename MapType, typename StepControlType>
void CnTaylor<MapType,StepControlType>::cnPhi(const VectorType&x, CnCoeffType& result)
{
  if(dimension()!=result.dimension())
    throw std::runtime_error("BasicCnTaylor::operator(CnCoeffType&) - incompatible dimensions");
  int rank = result.rank();
  if( getRank() < rank )
    throw std::runtime_error("BasicCnTaylor::operator(CnCoeffType&) - requested rank to large");

  this->setInitialCondition(x,MatrixType::Identity(dimension()));
  computeVectorFieldSeries(x,rank,m_order-1);
  computeResultSeries(rank,m_order-1);

  result.clear();
  for(int j=m_order-1;j>=0;--j)
  {
    for(int i=0;i<dimension();++i)
    {
      typename SeriesContainerType::const_iterator it=m_resultSeries.begin(i);
      typename CnCoeffType::iterator b = result.begin(i), e=result.end(i,rank);
      while(b!=e)
      {
        (*b) = (*b) * m_step + (*it)->value[j];
        ++b;
        ++it;
      }
    }
  }
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_CNTAYLOR_PHI_HPP_

/// @}
