/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Taylor.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2001-2004 */

#ifndef _CAPD_DYNSYS_TAYLOR_HPP_
#define _CAPD_DYNSYS_TAYLOR_HPP_

#include <sstream>
#include <string>
#include <stdexcept>

#include "capd/basicalg/factrial.h"

#include "capd/dynsys/Taylor.h"
#include "capd/dynsys/TaylorException.h"

#include "capd/dynsys/DynSys.hpp"
#include "capd/dynsys/BasicTaylor.hpp"
#include "capd/dynsys/enclosure.hpp"

namespace capd{
namespace dynsys{

//###########################################################//

template<typename MapType, typename StepControlType>
Taylor<MapType, StepControlType>::Taylor(MapType& vectorField, int a_order, const ScalarType& Step, const StepControlType& stepControl)
  : BasicTaylor<MapType,StepControlType>(vectorField,a_order,Step,stepControl)
{}


//###########################################################//

template<typename MapType, typename StepControlType>
typename Taylor<MapType, StepControlType>::MatrixType Taylor<MapType, StepControlType>::JacPhi(const VectorType &iv)
{
  VectorType* coeff = this->m_curve.getCoefficients();
  MatrixType* matrixCoeff = this->m_curve.getMatrixCoefficients();
  // first we compute ceofficients for x
  this->computeCoefficients(getOrder(),coeff,iv);
  this->computeMatrixCoeff(getOrder(),coeff,matrixCoeff,MatrixType::Identity(dimension()));

  // the sumation of the Taylor series
  MatrixType result = matrixCoeff[getOrder()];
  for(int r=getOrder()-1;r>=0;--r)
    result = result*m_step + matrixCoeff[r];

  return result;
}


//###########################################################//


template<typename MapType, typename StepControlType>
typename Taylor<MapType, StepControlType>::VectorType Taylor<MapType, StepControlType>::Remainder(const VectorType &iv)
{
  // we compute an enclosure for \varphi([0,timestep],iv)
  int ok;
  VectorType* remCoeff = this->m_curve.getRemainderCoefficients();
  remCoeff[0] = enclosure(iv,&ok);

  // the computation of Taylor coefficients up to an order <order+1> on <enc>
  for(int i=0;i<=getOrder();++i)
    remCoeff[i+1] = (*m_vField)(remCoeff[i],i)/(i+1);

  return remCoeff[getOrder()+1]*power(this->m_step,getOrder()+1);
}

//###########################################################//


template<typename MapType, typename StepControlType>
typename Taylor<MapType, StepControlType>::VectorType Taylor<MapType, StepControlType>::enclosure(const VectorType &x)
///< the function finds an enclosure for \varphi([0,step],x)
{
  return capd::dynsys::enclosure(*m_vField, x, m_step);
}

//###########################################################//
template<typename MapType, typename StepControlType>
typename Taylor<MapType, StepControlType>::VectorType Taylor<MapType, StepControlType>::enclosure(const VectorType &x, int *found)
///<the function finds an enclosure for \varphi([0,step],x)
{
  return capd::dynsys::enclosure(*m_vField, x, m_step);
}


//###########################################################//


template<typename MapType, typename StepControlType>
typename Taylor<MapType, StepControlType>::MatrixType Taylor<MapType, StepControlType>::jacEnclosure(const VectorType &enc, const NormType &the_norm)
/**< the function finds enclosure for Jacobian matrix (variational part)
     source- "C^1-Lohner algorithm" by P. Zgliczynski */
{
  return capd::dynsys::jacEnclosure(*m_vField,m_step,enc,the_norm);
}


//###########################################################//


template<typename MapType, typename StepControlType>
void Taylor<MapType, StepControlType>::JacRemainder(
      const VectorType &vecEnc,
      const MatrixType &jacEnc,
      VectorType &Rem,
      MatrixType &jacRem
  )
// the remainder for varaiational part is computed
   // vecEnc - enclosure for \varphi([0,step],x)
   // jacEnc -  enclosure for V([0,step],x)
{
  VectorType* remCoeff = this->m_curve.getRemainderCoefficients();
  MatrixType* remMatrixCoeff = this->m_curve.getMatrixRemainderCoefficients();
  this->computeCoefficients(getOrder()+1,remCoeff,vecEnc);
  this->computeMatrixCoeff(getOrder()+1,remCoeff,remMatrixCoeff,jacEnc);

  ScalarType fac = power(m_step,getOrder()+1);
  Rem = remCoeff[getOrder()+1] * fac;
  jacRem = remMatrixCoeff[getOrder()+1] * fac;
}


//###########################################################//

}} //namespace capd::dynsys

#endif // _CAPD_DYNSYS_TAYLOR_HPP_

/// @}
