/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file TaylorHOE.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2010 */

#ifndef _CAPD_DYNSYS_TAYLORHOE_HPP_
#define _CAPD_DYNSYS_TAYLORHOE_HPP_

#include <sstream>
#include <string>
#include <stdexcept>

#include "capd/basicalg/factrial.h"

#include "capd/dynsys/TaylorHOE.h"
#include "capd/dynsys/TaylorException.h"

#include "capd/dynsys/DynSys.hpp"
#include "capd/dynsys/Taylor.hpp"

namespace capd{
namespace dynsys{

//###########################################################//

template<typename MapType, typename StepControlType>
TaylorHOE<MapType,StepControlType>::TaylorHOE(MapType& vectorField, int a_order, const ScalarType& Step, const StepControlType& stepControl)
  : BasicTaylor<MapType,StepControlType>(vectorField,a_order,Step,stepControl),
    Taylor<MapType,StepControlType>(vectorField,a_order,Step,stepControl)
{}


//###########################################################//


template<typename MapType, typename StepControlType>
typename TaylorHOE<MapType,StepControlType>::VectorType
TaylorHOE<MapType,StepControlType>::enclosure(const VectorType &x, VectorType& out_remainder, int* o_found, bool computeCoeff)
///< the function finds an enclosure for \varphi([0,step],x)
{
  int dimension = x.dimension();
  VectorType zero(x.dimension());
  int myOrder = this->getOrder();
  int i;

  const static typename ScalarType::BoundType epsilon = power(10,-TypeTraits<ScalarType>::numberOfDigits()-100);
  VectorType Small(dimension);
  for(i=0;i<dimension;++i)
    Small[i] = ScalarType(-epsilon,epsilon);

// this means that we cannot trust previously computed coefficients
// or they were not computed
  VectorType* coeff = this->m_curve.getCoefficients();
  VectorType* remCoeff = this->m_curve.getRemainderCoefficients();
  if(computeCoeff)
  {
    this->computeCoefficients(myOrder,coeff,x);
  }

  const static ScalarType I(0.,1.);
  const static ScalarType mulFactor(-2.,2.);
  ScalarType h = I*this->m_step;
  VectorType phi = coeff[myOrder];
  for(i=myOrder-1;i>=0;--i)
    phi = phi*h + coeff[i];

  ScalarType stepToOrder = power(this->getStep(),myOrder+1);
  if(subset(coeff[myOrder+1],zero))
  {
    coeff[myOrder+1] = (*(this->m_vField))(coeff[myOrder],myOrder)/(myOrder+1);
    VectorType u = mulFactor*stepToOrder* coeff[myOrder+1] + Small;
    this->computeCoefficients(myOrder+1,remCoeff,phi+u);
  }
  VectorType u = mulFactor*stepToOrder * remCoeff[myOrder+1] + Small;
  VectorType result = phi + u;

  this->computeCoefficients(myOrder+1,remCoeff,result);
  out_remainder = stepToOrder * remCoeff[myOrder+1];

  VectorType v = I*out_remainder;

  if(!subsetInterior(v,u))
  {
    if(this->isStepChangeAllowed())
    {
       ScalarType factor(1.);
       for(i=0;i<dimension;++i)
       {
         if(!subsetInterior(v[i],u[i]))
           factor = capd::min(factor,u[i].right()/capd::abs(v[i]).right());
       }
       if(factor.contains(0.))
         throw TaylorException<VectorType>("TaylorHOE Error: cannot find enclosure guaranteeing bounds with step control",x,this->getStep());
       factor = exp(log(factor)/(myOrder+1)).leftBound();
       typename capd::TypeTraits<ScalarType>::Real newStep = leftBound(this->getStep()*factor);
       newStep = capd::dynsys::clearMantissaBits(newStep);

       if(capd::abs(newStep) < this->m_stepControl.getMinStepAllowed())
         throw TaylorException<VectorType>("TaylorHOE Error: minimal time step reached. Cannot integrate.",x,this->getStep());
       this->setStep(ScalarType(newStep));
    }else
    {
      // time step change is not allowed
      // we will try to refine the enclosure
      const int limit=30;
      int counter = 0;
      bool found=false;

      while((!found) && (counter<limit)){
        counter++;
        found = true;
        for(i=0;i< dimension;++i){
          if(!(v[i].subsetInterior(u[i]))){
            found = false;
            u[i] *= typename TypeTraits<ScalarType>::Real(1.5);
          } // endif
        } // endfor
        result = phi + u;
        this->computeCoefficients(myOrder+1,remCoeff,result);
        out_remainder = stepToOrder * remCoeff[myOrder+1];
        v = I*out_remainder;
      } // endwhile
      if(!found) {
        // throw TaylorException<VectorType>("TaylorHOE Error: cannot find enclosure guaranteeing bounds, loop limit exceeded",x,this->getStep());
      }
    } // end else
  }

  // we get to this point without throwing an exceptions therefore enclosure is found.
  if(o_found)
    *o_found=1;

  return result;
}

//###########################################################//


template<typename MapType, typename StepControlType>
void TaylorHOE<MapType,StepControlType>::encloseMap(
      const VectorType& x,
      const VectorType& xx,
      VectorType& o_phi,
      MatrixType& o_jacPhi,
      VectorType& o_rem
  )
{
  VectorType* coeff = this->m_curve.getCoefficients();
  MatrixType* matrixCoeff = this->m_curve.getMatrixCoefficients();
  this->computeCoefficients(this->getOrder(),coeff,xx);
  this->computeMatrixCoeff(this->getOrder(),coeff, matrixCoeff, MatrixType::Identity(x.dimension()));

  // in the following function the time step can be adjusted
  this->enclosure(xx,o_rem,0,false);

  // however, the coefficient in matrixCoeff are untouched
  o_jacPhi = matrixCoeff[this->getOrder()];
  for(int i=this->getOrder()-1;i>=0;--i)
    o_jacPhi = o_jacPhi*this->getStep() + matrixCoeff[i];

  o_phi = this->Phi(x);
}

//###########################################################//


template<typename MapType, typename StepControlType>
void TaylorHOE<MapType,StepControlType>::encloseMap(
      const VectorType& x,
      const VectorType& xx,
      VectorType& o_phi,
      MatrixType& o_jacPhi,
      VectorType& o_rem,
      MatrixType& o_jacRem,
      const NormType& norm
  )
{
  VectorType* coeff = this->m_curve.getCoefficients();
  MatrixType* matrixCoeff = this->m_curve.getMatrixCoefficients();

  VectorType* remCoeff = this->m_curve.getRemainderCoefficients();
  MatrixType* matrixRemCoeff = this->m_curve.getMatrixRemainderCoefficients();

  this->computeCoefficients(this->getOrder(),coeff,xx);
  this->computeMatrixCoeff(this->getOrder(),coeff,matrixCoeff,MatrixType::Identity(x.dimension()));

  // in the following function the time step can be adjusted
  VectorType enc = this->enclosure(xx,o_rem,0,false);

  // however, the coefficient in matrixCoeff are untouched
  o_jacPhi = matrixCoeff[this->getOrder()];
  for(int i=this->getOrder()-1;i>=0;--i)
    o_jacPhi = o_jacPhi*this->getStep() + matrixCoeff[i];

  // m_coeff still contains coefficients computed on enclosure
  // now we will compute coefficients for derivatives on enclosure

  MatrixType jacEnc = this->jacEnclosure(enc,norm);
  this->computeMatrixCoeff(this->getOrder()+1,remCoeff,matrixRemCoeff,jacEnc);
  o_jacRem = power(this->getStep(),this->getOrder()+1)* matrixRemCoeff[this->getOrder()+1];
  o_phi = this->Phi(x);
}

}} //namespace capd::dynsys

#endif // _CAPD_DYNSYS_TAYLORHOE_HPP_

/// @}
