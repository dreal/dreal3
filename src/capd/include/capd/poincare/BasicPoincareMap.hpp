/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicPoincareMap.hpp
///
/// @author Daniel Wilczak
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#ifndef _CAPD_POINCARE_BASIC_POINCARE_MAP_HPP_
#define _CAPD_POINCARE_BASIC_POINCARE_MAP_HPP_

#include <stdexcept>
#include "capd/poincare/BasicPoincareMap.h"
#include "capd/poincare/BasicPoincareMap_operator.hpp"
#include "capd/map/CnCoeff.hpp"
#include "capd/capd/factrial.h"

namespace capd{
namespace poincare{

// -----------------------------------------------------------------------------------------



/**
 *  Computes dT from derivative of the flow.
 *  T(x) is a first return time for point x
 *
 *  @param Px                value of Poincare map P(x)
 *  @param derivativeOfFlow  defivative of the flow \f$ \partial \varphi(T(x),x)/ \partial x \f$
 */

template <typename DS, typename FunT>
typename BasicPoincareMap<DS, FunT>::VectorType
BasicPoincareMap<DS, FunT>::computeDT(
      const VectorType& Px,
      const MatrixType& derivativeOfFlow
   )
{
   int j,k;
   VectorType result(m_dim);
   VectorType gradientOnPx = m_section.gradient(Px);
   for(j=0;j<m_dim;++j)
      for(k=0;k<m_dim;++k)
         result[j] += gradientOnPx[k] * derivativeOfFlow[k][j];

   result /= - gradientOnPx * m_dynamicalSystem.getField()(Px);
   return result;
}

// -------------------------------------------------------------------

/**
 * Computes derivative of Poincare Map dP
 *
 *  @param Px                value of Poincare map P(x)
 *  @param derivativeOfFlow  defivative of the flow \f$ \partial \varphi(T(x),x)/ \partial x \f$
 *  @param dT                derivative of T(x) : first return time function
 */

template <typename DS, typename FunT>
typename BasicPoincareMap<DS, FunT>::MatrixType
BasicPoincareMap<DS, FunT>::computeDP(
      const VectorType& Px,
      const MatrixType& derivativeOfFlow,
      const VectorType& dT
   )
{
   MatrixType result(m_dim,m_dim);
   VectorType fieldOnPx = m_dynamicalSystem.getField()(Px);
   int i,j;
   for(i=0;i<m_dim;++i)
      for(j=0;j<m_dim;++j)
         result[i][j] = fieldOnPx[i]*dT[j] + derivativeOfFlow[i][j];
   return result;
}

/**
 * Computes derivative of Poincare Map dP
 *
 *  @param Px                value of Poincare map P(x)
 *  @param derivativeOfFlow  defivative of the flow \f$ \partial \varphi(T(x),x)/ \partial x \f$
 */

template <typename DS, typename FunT>
typename BasicPoincareMap<DS, FunT>::MatrixType
BasicPoincareMap<DS, FunT>::computeDP(
      const VectorType& Px,
      const MatrixType& derivativeOfFlow
   )
{
  VectorType dT = this->computeDT(Px, derivativeOfFlow);
  return this->computeDP(Px, derivativeOfFlow, dT);
}
// -------------------------------------------------------------------

template <typename DS, typename FunT>
typename BasicPoincareMap<DS, FunT>::MatrixType
BasicPoincareMap<DS, FunT>::computeD2T(
      const VectorType& Px,
      const MatrixType& derivativeOfFlow,
      const VectorType& DT,
      const MatrixType& DP,
      MatrixType hessianOfFlow[]
   )
{
  int i,j,k,s;
  MatrixType D2T(m_dim,m_dim);
  VectorType fieldOnPx = m_dynamicalSystem.getField()(Px);
  MatrixType derOfVectorFieldOnPx = m_dynamicalSystem.getField()[Px];
  VectorType gradientOnPx = m_section.gradient(Px);

  for(j=0;j<m_dim;++j)
    for(i=0;i<m_dim;++i)
    {
      ScalarType temp1=0,temp2=0;
      for(k=0;k<m_dim;++k)
      {
        D2T[j][i] -= (gradientOnPx[k] * hessianOfFlow[k][j][i]);
        for(s=0;s<m_dim;++s)
        {
          ScalarType temp3 = gradientOnPx[k] * derOfVectorFieldOnPx[k][s];
          temp1 -= temp3 * DP[s][i];
          temp2 -= temp3 * derivativeOfFlow[s][j];
        }
      }
      D2T[j][i] += DT[j] *temp1 + DT[i]*temp2;
    }

  D2T /= (gradientOnPx * fieldOnPx);
  return D2T;
}

// -------------------------------------------------------------------

template <typename DS, typename FunT>
void BasicPoincareMap<DS, FunT>::computeD2P(
         const VectorType& Px,
         const MatrixType& derivativeOfFlow,
         const VectorType& DT,
         const MatrixType& DP,
         MatrixType hessianOfFlow[],
         const MatrixType& D2T,
         MatrixType result[]
        )
{
  int i,j,k,s;
  MatrixType derOfVectorFieldOnPx = m_dynamicalSystem.getField()[Px];
  VectorType fieldOnPx = m_dynamicalSystem.getField()(Px);

  for(i=0;i<m_dim;++i)
    for(j=0;j<m_dim;++j)
      for(k=0;k<m_dim;++k)
      {
        result[i][j][k] = fieldOnPx[i] * D2T[j][k] + hessianOfFlow[i][j][k];
        for(s=0;s<m_dim;++s)
        {
          result[i][j][k] += DT[k] * derOfVectorFieldOnPx[i][s] * derivativeOfFlow[s][j];
          result[i][j][k] += DT[j] * derOfVectorFieldOnPx[i][s] * DP[s][k];
        }
      }
}


}} // namespace capd::poincare

#endif // #define _CAPD_POINCARE_BASIC_POINCARE_MAP_HPP_

/// @}
