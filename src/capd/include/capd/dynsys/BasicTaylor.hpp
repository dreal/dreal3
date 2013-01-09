/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicTaylor.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSYS_BASICTAYLOR_HPP_
#define _CAPD_DYNSYS_BASICTAYLOR_HPP_

#include <sstream>
#include <string>
#include <stdexcept>

#include "capd/capd/factrial.h"

#include "capd/dynsys/BasicTaylor.h"
#include "capd/diffAlgebra/Curve.hpp"

namespace capd {
namespace dynsys {

//###########################################################//

template <typename MapType, typename StepControlType>
BasicTaylor<MapType, StepControlType>::BasicTaylor(MapType& vectorField, int a_order, const ScalarType& Step, const StepControlType& stepControl) 
  : capd::dynsys::StepControlInterface<StepControlType>(stepControl), 
    m_vField(&vectorField), 
    m_curve(leftBound(Step),rightBound(Step),vectorField.dimension(),a_order),
    m_step(Step)
{
  m_vField->setOrder(a_order + 1);
  m_F = new (dimension(),dimension()) MatrixType[a_order+2];
}

//###########################################################//


template <typename MapType, typename StepControlType>
BasicTaylor<MapType, StepControlType>::~BasicTaylor() 
{
  delete []m_F;
}

//###########################################################//


template <typename MapType, typename StepControlType>
void BasicTaylor<MapType, StepControlType>::setOrder(int newOrder) 
{
  if(newOrder > this->m_curve.getAllocatedOrder()) 
  {
    m_vField->setOrder(newOrder + 1);
    delete [] m_F;
    m_F = new (dimension(),dimension()) MatrixType[newOrder+2];
  }
  m_curve.setOrder(newOrder);
}

//###########################################################//


template <typename MapType, typename StepControlType>
void BasicTaylor<MapType, StepControlType>::computeMatrixCoeff(int order, VectorType* coeff, MatrixType* matrixCoeff, const MatrixType &V){
  if(order < 0) {
    std::ostringstream message;
    message << "Taylor error: negative index " << order << " of Taylor coefficient in function computeMatrixCoeff";
    throw std::out_of_range(message.str());
  }

  // now we compute the coefficients for the Jacobian matrix
  // the coefficients will be stored in F
  m_vField->variational(coeff, m_F, order);

  matrixCoeff[0] = V;

  int p, i, j, k, r;
  for(p = 0; p < order; ++p) 
  {
    typename MatrixType::iterator b = matrixCoeff[p + 1].begin();
    for(i = 1; i <= dimension(); ++i)
    {
      for(j = 1; j <= dimension(); ++j) 
      {
        ScalarType result(0);
        for(k = 1; k <= dimension(); ++k)
          for(r = 0; r <= p; ++r)
            result += m_F[r](i, k) * matrixCoeff[p - r](k, j);
        *b = result / (p + 1);
        ++b;
      }
    }
  }
}

//###########################################################//


template <typename MapType, typename StepControlType>
void BasicTaylor<MapType, StepControlType>::computeCoefficients(int order, VectorType* coeff, const VectorType &iv)
{
  coeff[0] = iv; //  coeff will contain  Taylor coefficients in <iv>
  for(int r = 0; r < order; ++r)
    coeff[r + 1] = (*m_vField)(coeff[r], r) / (r + 1);  // recurrent computation of consecutive
                                                            // Taylor coefficients
}

//###########################################################//


template <typename MapType, typename StepControlType>
typename BasicTaylor<MapType, StepControlType>::VectorType BasicTaylor<MapType, StepControlType>::operator()(const VectorType &iv) 
{
  VectorType* coeff = m_curve.getCoefficientsAtCenter();
  this->computeCoefficients(getOrder(), coeff, iv);

  VectorType result = coeff[getOrder()];
  for(int r = getOrder() - 1; r >= 0; --r)
    result = result * m_step + coeff[r];
  return result;
}

//###########################################################//


template <typename MapType, typename StepControlType>
typename BasicTaylor<MapType, StepControlType>::VectorType BasicTaylor<MapType, StepControlType>::operator()(const VectorType &iv, MatrixType& der) 
{
   return (*this)(iv, MatrixType::Identity(dimension()), der);
}


template <typename MapType, typename StepControlType>
typename BasicTaylor<MapType, StepControlType>::VectorType BasicTaylor<MapType, StepControlType>::operator()(
    const VectorType &v, const MatrixType& derivative, MatrixType & resultDerivative
) {
  // first we compute coefficients for x
  VectorType result = (*this)(v);

  MatrixType* matrixCoeff = m_curve.getMatrixCoefficients();

  // this function compute coefficients for variational equation up to index 'order'
  computeMatrixCoeff(getOrder(), m_curve.getCoefficientsAtCenter(),matrixCoeff, derivative);

  // the summation of the Taylor series
  resultDerivative = matrixCoeff[getOrder()];
  for(int r = getOrder() - 1; r >= 0; --r)
    resultDerivative = resultDerivative * m_step + matrixCoeff[r];

  return result;
}

template <typename MapType, typename StepControlType>
typename BasicTaylor<MapType, StepControlType>::VectorType BasicTaylor<MapType, StepControlType>::operator()(capd::map::C1Coeff<MatrixType> & coeffs)
{
  coeffs = (*this)((VectorType)coeffs, coeffs.getDerivative(), coeffs.refDerivative());
  return (VectorType)coeffs;
}

}
} //namespace capd::dynsys

#endif // _CAPD_DYNSYS_BASICTAYLOR_HPP_
/// @}
