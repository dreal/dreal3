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
#include "capd/map/C1Coeff.h"

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
BasicPoincareMap<DS, FunT>::operator()(VectorType v) {

  VectorType afterSection;
  return this->operator()(v, afterSection);
}

//////////////////////////////////////////////////////////////////////////////////
///
/// This function moves theSet with the given flow and stops just before the section 
/// (for n-th iterate of Poincare Map).
///  
/// @return set on the section or just after the section 
///        (suitable for a computation of next Poincare Map iteration).
/// 
/// Parameter theSet contains on return the set just before the section.
/// 
/// Common function for different set types.
//////////////////////////////////////////////////////////////////////////////////
template <typename DS, typename FunT>
template<typename T>
T BasicPoincareMap<DS, FunT>::reachSection(
	T& theSet,    ///< @param[in,out] theSet  on input: initial set position, on return: the set just before the section.
	int n,        ///<                number of iterates 
	ScalarType * lastStep   ///< if given 
){

  //  We do not save and restore step because it is used in section crossing 
  // SaveStepControl<DS> ssc(this->m_dynamicalSystem);

  this->m_dynamicalSystem.setStepChangeAllowance(this->m_stepControl);
  this->m_dynamicalSystem.clearCoefficients();

  T v = theSet;

  // --------- leave the section --------------------------------
  // We do at least one step to avoid situation where initial point
  // is just before section due to floating point errors

  this->setFirstTimeStep(v);
  makeOneStep(v);
  ScalarType sign = m_section(v);

  while( (sign==0.0)                              // We are on the section
      || !((m_crossingDirection == None)          // section sign is not correct
          || ((m_crossingDirection == MinusPlus) && (sign < 0.0))
          || ((m_crossingDirection == PlusMinus) && (sign > 0.0))
      )
  ){
    this->setNextTimeStep(v);
    this->makeOneStep(v);
    sign = m_section(v);
  }

  // ------------- reach the section ----------------------------------
  //first approach to section with a relatively large time step
  T beforeSection = v;
  while(m_section(v)*sign > 0) {
    beforeSection = v;
    this->setNextTimeStep(v);
    this->makeOneStep(v);
  }

  theSet = beforeSection;
  if(lastStep)
    *lastStep = m_dynamicalSystem.getStep();
  return v;
}

template <typename DS, typename FunT>
typename BasicPoincareMap<DS, FunT>::VectorType
BasicPoincareMap<DS, FunT>::crossSection(VectorType beforeSection, VectorType v, ScalarType & lastStep) {

  //  We do not save and restore step because it should be saved externally 
  //  SaveStepControl<DS> ssc(this->m_dynamicalSystem);

  ScalarType step = m_dynamicalSystem.getStep();
  ScalarType sign = m_section(beforeSection);
#define ____NEW_POINCARE__ 0
#if (____NEW_POINCARE__ == 1)


   // Do NOT Work properly for big precisions (too much iterations in section crossing)


   VectorType pointAfterSection = v;

   ScalarType tolerance = m_sectionFactor;

   ScalarType minStep = capd::TypeTraits<ScalarType>::epsilon();
   VectorType beforeSection2= beforeSection;
   ScalarType lastStep = capd::TypeTraits<ScalarType>::zero();
   while(true){

     VectorType Grad = this->m_section.gradient(beforeSection);
     ScalarType approxDistance = abs(this->m_section(beforeSection));

     VectorType fieldDirection = this->m_dynamicalSystem.getField()(beforeSection);
     ScalarType fieldSectionDirection = abs(fieldDirection * Grad);
     ScalarType approxTime =  (approxDistance  / fieldSectionDirection);

     if(approxTime<minStep)
       approxTime = minStep;

     if (step<0)
       approxTime = -approxTime;

   // TODO : add max correction tries
   //  int correctionTries = maxCorrectionTries;

     bool stop = false;
     ScalarType check;
     while(true){

       m_dynamicalSystem.setStep(approxTime);
       v = m_dynamicalSystem(beforeSection);

       check = m_section(v);

       if(check*sign <= 0) {  //  we crossed the section
         if(capd::abs(check) < tolerance) { // and we are close enough
           stop = true;
           break;
         } else {
           approxTime *= 0.5;
         }
       } else {                                     // we do not reached the section jet
           break;
       }
     }
     lastStep += approxTime;
     if(stop) break;
     beforeSection = v;
   }
   m_dynamicalSystem.setStep(lastStep);
   VectorType v2 = m_dynamicalSystem(beforeSection2);

#elif (____NEW_POINCARE__ == 2)

   ScalarType t1 = TypeTraits<ScalarType>::zero(), t2 = lastStep;
   ScalarType tolerance = m_sectionFactor,
              stepTolerance = TypeTraits<ScalarType>::epsilon()*10; //1.e-20;

   pointAfterSection = v;
   VectorType afterSection = v;

   while(true){
 // TODO: Use gradient to predict new step instead of bisection method.
     ScalarType currentStep = (t2+t1)/2;

     m_dynamicalSystem.setStep(currentStep);
     v = m_dynamicalSystem(beforeSection);

     ScalarType check = m_section(v);
     if(check*sign <= 0) {  //  we crossed the section
       if(capd::abs(check) < tolerance) { // and we are close enough
         break;
       } else {
         t2 = currentStep;
         afterSection = v;
       }
       if(capd::abs((t2-t1)/t2) < stepTolerance){  // relative difference between times is too small we cannot continue to bisect
         break;
       }
     } else {                                     // we do not reached the section jet
       t1 = currentStep;
       if(capd::abs((t2-t1)/t2) < stepTolerance){ // relative difference between times is too small we cannot continue to bisect
         v = afterSection;                        // so we return the closest point after the section
         break;
       }
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
  return v;
}

template <typename DS, typename FunT>
typename BasicPoincareMap<DS, FunT>::VectorType
BasicPoincareMap<DS, FunT>::operator()(VectorType v, VectorType & pointAfterSection) {
  ScalarType lastStep;
  pointAfterSection = reachSection(v, 1, &lastStep);
  return crossSection(v, pointAfterSection, lastStep);
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
  SaveStepControl<DS> ssc(this->m_dynamicalSystem);

  capd::map::C1Coeff<MatrixType> coeffs(v, MatrixType::Identity(this->m_dim));
  v = reachSection(coeffs, 1);
  VectorType beforeSection = (VectorType)coeffs;
  MatrixType matrixBeforeSection = (MatrixType)coeffs;

  ScalarType step = m_dynamicalSystem.getStep();
  ScalarType sign = m_section(beforeSection);
  MatrixType oneStepDerivative(this->m_dim, this->m_dim);

  this->m_dynamicalSystem.turnOffStepControl();

#define ____NEW_POINCARE2__ 0
#if (____NEW_POINCARE2__ == 1)

  ScalarType tolerance = m_sectionFactor;

  ScalarType minStep = capd::TypeTraits<ScalarType>::epsilon();

  VectorType beforeSection2= beforeSection;
  ScalarType lastStep = capd::TypeTraits<ScalarType>::zero();
  while(true){

    VectorType Grad = this->m_section.gradient(beforeSection);
    ScalarType approxDistance = abs(this->m_section(beforeSection));

    VectorType fieldDirection = this->m_dynamicalSystem.getField()(beforeSection);
    ScalarType fieldSectionDirection = abs(fieldDirection * Grad);
    ScalarType approxTime =  (approxDistance  / fieldSectionDirection);

    // approxTime cannot be too small, otherwise it can occur that we will never cross the section
    if(approxTime<minStep)
      approxTime = minStep;

    if (step<0)
      approxTime = -approxTime;

  // TODO : add max correction tries
  //  int correctionTries = maxCorrectionTries;

    bool stop = false;
    ScalarType check;
    while(true){

      m_dynamicalSystem.setStep(approxTime);
      v = m_dynamicalSystem(beforeSection);

      check = m_section(v);

      if(check*sign <= 0) {  //  we crossed the section
        if(capd::abs(check) < tolerance) { // and we are close enough
          stop = true;
          break;
        } else {
          approxTime *= 0.9;
        }
      } else {                                     // we do not reached the section jet
          break;
      }
    }
    lastStep += approxTime;
    if(stop) break;
    beforeSection = v;
  }

  m_dynamicalSystem.setStep(lastStep);
  VectorType v2 = m_dynamicalSystem(beforeSection2, oneStepDerivative);

  dF = oneStepDerivative * matrixBeforeSection;

#elif (____NEW_POINCARE2__ == 2)

   ScalarType t1 = TypeTraits<ScalarType>::zero(), t2 = this->m_dynamicalSystem.getStep();
   ScalarType tolerance = m_sectionFactor,
              stepTolerance = TypeTraits<ScalarType>::epsilon()*10; //1.e-20;

//   pointAfterSection = v;
   VectorType afterSection = v;
   MatrixType matrixAfterSection = oneStepDerivative;
   while(true){
 // TODO: Use gradient to predict new step instead of bisection method.
     ScalarType currentStep = (t2+t1)/2;

     m_dynamicalSystem.setStep(currentStep);
     v = m_dynamicalSystem(beforeSection, oneStepDerivative);
     ScalarType check = m_section(v);

     if(check*sign <= 0) {  //  we crossed the section
       if(capd::abs(check) < tolerance) { // and we are close enough
         break;
       } else {
         t2 = currentStep;
         afterSection = v;
         matrixAfterSection = oneStepDerivative;
         if(capd::abs((t2-t1)/t2) < stepTolerance){  // relative difference between times is too small we cannot continue to bisect
           break;
         }
       }
     } else {                                     // we do not reached the section jet
       t1 = currentStep;
       if(capd::abs((t2-t1)/t2) < stepTolerance){ // relative difference between times is too small we cannot continue to bisect
         v = afterSection;                        // so we return the closest point after the section
         oneStepDerivative = matrixAfterSection;
         break;
       }
     }

   }
   dF = oneStepDerivative * matrixBeforeSection;

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
    v = m_dynamicalSystem(beforeSection,oneStepDerivative);
    dF = oneStepDerivative * matrixBeforeSection;
    if (m_section(v)*sign<=0.)
      break;
    beforeSection = v;
    matrixBeforeSection = dF;
  }

  while(m_section(v)*sign>0) {
    v = m_dynamicalSystem(v,oneStepDerivative);
    dF = oneStepDerivative * dF;
  }
  m_dynamicalSystem.setStep(step);

#endif

  return v;
}

}} // namespace capd::poincare

#endif // #define _CAPD_POINCARE_BASIC_POINCARE_MAP_OPERATOR_HPP_

/// @}
