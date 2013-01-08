/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicPoincareMap_operator.hpp
///
/// @author Daniel Wilczak
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_POINCARE_BASIC_POINCARE_MAP_OPERATOR_HPP_
#define _CAPD_POINCARE_BASIC_POINCARE_MAP_OPERATOR_HPP_

#include "capd/poincare/BasicPoincareMap.h"

namespace capd{
namespace poincare{

// ---------------------- nonrigorous procedure ----------------------

/**
 * compute nonrigorous Poincare map
 *
 * The point just after the section on the nonrigorous trajectory is returned
 */

template <typename DS, typename FunT>
typename BasicPoincareMap<DS, FunT>::VectorType
BasicPoincareMap<DS, FunT>::operator()(VectorType v)

{
   ScalarType sign;
   ScalarType step = m_dynamicalSystem.getStep();

   do {

      v = m_dynamicalSystem(v);
      sign = m_section(v);
   } while( (sign==0.0) ||                  // We are on the section
         !((m_crossingDirection == None) ||         // section sign is not correct
           ((m_crossingDirection == MinusPlus) && (sign < 0.0)) ||
           ((m_crossingDirection == PlusMinus) && (sign > 0.0))
          ));

//first approach to section with a constant - relatively large time step
   VectorType beforeSection(m_dim);
   while(m_section(v)*sign>0)
   {
      beforeSection = v;
      v = m_dynamicalSystem(v);
   }

#define ____NEW_POINCARE__
#ifdef ____NEW_POINCARE__

   ScalarType t1 = TypeTraits<ScalarType>::zero(), t2 = step;
   ScalarType tolerance = m_sectionFactor,
         stepTolerance = TypeTraits<ScalarType>::epsilon()*10; //1.e-20;

   VectorType afterSection = v;
   while(true){
     ScalarType currentStep = (t2+t1)/2;

     m_dynamicalSystem.setStep(currentStep);
     v = m_dynamicalSystem(beforeSection);
     ScalarType check = m_section(v);

     if(((capd::abs(check) < tolerance) && (check*sign <= 0)) ||   // we crossed the section and we are close enough
        (capd::abs((t2-t1)/t2) < stepTolerance)){                       // relative difference between times is too small we cannot continue to bisect
       if(check*sign>0){        // if above only the second condition is true it can happen that v is before section
         v = afterSection;
       }
       break;
     }
     if(check*sign<0){ // we crossed the section but we are to far away
       t2 = currentStep;
     }else{            // we do not reached the section jet
       t1 = currentStep;
     }
   }

#else
   /*  OLD VERSION: DO NOT WORK OR TAKES A LOT OF TIME IN SOME SITUATIONS
    *               with high order it can find very small section step or even zero
    *               then second loop is infinite
    *  AFTER TESTS I RECOMMEND TO REMOVE IT OR CORRECT (T.Kapela)
    *
    */

   // we approach section with small time steps as close as possible
   int order = m_dynamicalSystem.getOrder(), i;
   for(i=0;i<order;++i)
   {
      VectorType Grad = m_section.gradient(beforeSection);
      VectorType fieldDirection = m_dynamicalSystem.getField()(beforeSection);
      ScalarType approxDistance = abs(m_section(beforeSection));
      ScalarType fieldSectionDirection = abs(fieldDirection * Grad);
      ScalarType approxTime = 0.9*approxDistance/fieldSectionDirection;
      if(step<0)
         approxTime = -approxTime;
      m_dynamicalSystem.setStep(approxTime);
      v = m_dynamicalSystem(beforeSection);
      if (m_section(v)*sign<=0.)
        break;
      beforeSection = v;
   }

   while(m_section(v)*sign>=0)
    v = m_dynamicalSystem(v);
#endif

   m_dynamicalSystem.setStep(step);

   return v;
}

// ---------------------- nonrigorous procedure ----------------------

/**
 * Computes nonrigorous Poincare map and derivatives of the flow
 *
 * The point just after the section on the nonrigorous trajectory is returned
 * It also return derivative of the flow with respect to initial conditions.
 * They can te used to compute derivative of Poincare Map
 * \see{computeDT, computeDP}
 */

template <typename DS, typename FunT>
typename BasicPoincareMap<DS, FunT>::VectorType
BasicPoincareMap<DS, FunT>::operator()(VectorType v, MatrixType &dF)
{
  ScalarType sign = m_section(v);
  ScalarType step = m_dynamicalSystem.getStep();
  dF = MatrixType::Identity(m_dim);
  MatrixType oneStepDerivative(m_dim,m_dim);
  do{
    v = m_dynamicalSystem(v,oneStepDerivative);
    dF = oneStepDerivative * dF;
    sign = m_section(v);
  } while( (sign==0.0) ||                  // We are on the section
      !((m_crossingDirection == None) ||         // section sign is not correct
       ((m_crossingDirection == MinusPlus) && (sign < 0.0)) ||
       ((m_crossingDirection == PlusMinus) && (sign > 0.0))
    ));

//first approach to section with a constant - relatively large time step

  VectorType beforeSection(m_dim);
  MatrixType matrixBeforeSection(m_dim,m_dim);

  while(m_section(v)*sign>0)
  {
    beforeSection = v;
    matrixBeforeSection = dF;
    v = m_dynamicalSystem(v,oneStepDerivative);
    dF = oneStepDerivative * dF;
  }

// we approach section with small time steps as close as possible

  int order = m_dynamicalSystem.getOrder(), i;
  for(i=0;i<order;++i)
  {
    VectorType Grad = m_section.gradient(beforeSection);
    VectorType fieldDirection = m_dynamicalSystem.getField()(beforeSection);
    ScalarType approxDistance = abs(m_section(beforeSection));
    ScalarType fieldSectionDirection = abs(fieldDirection * Grad);
    ScalarType approxTime = 0.9*approxDistance/fieldSectionDirection;
    if(step<0)
      approxTime = -approxTime;
    m_dynamicalSystem.setStep(approxTime);
    v = m_dynamicalSystem(beforeSection,oneStepDerivative);
    dF = oneStepDerivative * matrixBeforeSection;
    if (m_section(v)*sign<=0.)
      break;
    beforeSection = v;
    matrixBeforeSection = dF;
  }

  while(m_section(v)*sign>0)
  {
    v = m_dynamicalSystem(v,oneStepDerivative);
    dF = oneStepDerivative * dF;
  }
  m_dynamicalSystem.setStep(step);
  return v;
}

}} // namespace capd::poincare

#endif // #define _CAPD_POINCARE_BASIC_POINCARE_MAP_OPERATOR_HPP_

/// @}
