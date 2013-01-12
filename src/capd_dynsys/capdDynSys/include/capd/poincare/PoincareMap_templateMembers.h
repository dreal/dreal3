/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file  PoincareMap_templateMembers.h
///
/// @author Daniel Wilczak
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_POINCARE_POINCARE_MAP_TEMPLATE_MEMBERS_HPP_
#define _CAPD_POINCARE_POINCARE_MAP_TEMPLATE_MEMBERS_HPP_

#include <cassert>
#include "capd/poincare/PoincareMap.h"
#include "capd/poincare/BasicPoincareMap.hpp"

namespace capd{
namespace poincare{

template <typename DS, typename FunT>
template<typename T>
typename PoincareMap<DS,FunT>::VectorType
PoincareMap<DS,FunT>::operator()(T& originalSet, int n)
{
// The originalSet after this function contains a set just ater section.
   this->derivativeOfFlow = NULL;
   this->hessianOfFlow = NULL;
   this->partialDerivatives = NULL;
// We move the set to be very close to the section
   T setAfterTheSection = this->reachSection(originalSet, n);

// and compute the PoincareMap image
   return this->crossSection<T>(originalSet, setAfterTheSection);
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
template<typename T>
typename PoincareMap<DS,FunT>::VectorType
PoincareMap<DS,FunT>::operator()(T& originalSet, MatrixType& der, int n)
{
// the originalSet after this function contains a set just ater section
// we move the set close to section
   this->derivativeOfFlow = &der;
   this->hessianOfFlow = NULL;
   this->partialDerivatives = NULL;
   T setAfterTheSection = this->reachSection<T>(originalSet, n);

// and compute the PoincareMap image
   return this->crossSection<T>(originalSet, setAfterTheSection);
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
template<typename T>
typename PoincareMap<DS,FunT>::VectorType
PoincareMap<DS,FunT>::operator()(T& originalSet, MatrixType& der, MatrixType hessian[], int n)
{
// the originalSet after this function contains a set just ater section
// we move the set close to section
   this->derivativeOfFlow = &der;
   this->hessianOfFlow = hessian;
   this->partialDerivatives = NULL;
   T setAfterTheSection = this->reachSection<T>(originalSet, n);

// and compute the PoincareMap image
   return this->crossSection<T>(originalSet, setAfterTheSection);
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
template<typename T>
typename PoincareMap<DS,FunT>::VectorType
PoincareMap<DS,FunT>::operator()(T& originalSet, CnCoeffType& result, int n)
{
// the originalSet after this function contains a set just ater section
// we move the set close to section
   this->derivativeOfFlow = NULL;
   this->hessianOfFlow = NULL;
   this->partialDerivatives = &result;
   T setAfterTheSection = this->reachSection<T>(originalSet, n);

// and compute the PoincareMap image
   return result() = this->crossSection<T>(originalSet, setAfterTheSection);
}

// -------------------- protected functions ---------------------------------

// this function is just for compatibility with C^1 and C^2 routines
// see the version for C^1-set types below
template <typename DS, typename FunT>
inline void PoincareMap<DS,FunT>::computeJacEnclosure(C0Set& S, VectorType& V)
{}

/*__________________________________________________________________________*/
/// Function returns section sign. It also checks If we crossed section
/// and returned in one step. In this case it throws an exception.
/// @param[in]      theSet      the set after making a step,
/// @param[in, out] position    position before time step,
/// @param[in]      updatePosition   flag that decides if position has to be updated
/// @param[in]      bound       rough enclosure for trajectory during whole time step
/// @return    section sign
template <typename DS, typename FunT>
template<typename T>
typename PoincareMap<DS,FunT>::ScalarType
PoincareMap<DS,FunT>::getSign(const T & theSet,  VectorType & position, bool updatePosition, const VectorType & bound )
{
  // we check if we cross the section and than return during one step
  // i.e. if during section crossing the section gradient is orthogonal to vector field
  this->checkTransversability(theSet, bound);

  // Now we are sure that either sing is constant during the time step
  // or we crossed the section but tranversally, so we can compute sign on position after the step.
  if(updatePosition){
    position = VectorType(theSet);
    return this->m_section(position);
  }
  else
    return this->m_section(VectorType(theSet));
}
/*__________________________________________________________________________*/
/// Function returns section sign. It also checks for possible crossing the section
/// and returning in one step. In this case it throws an exception.
/// @param[in]      theSet      the set after making a step,
/// @param[in, out] position    position before time step,
/// @param[in]      updatePosition   flag that decided if position has to be updated
/// @return    section sign
template <typename DS, typename FunT>
template<typename T>
typename PoincareMap<DS,FunT>::ScalarType
PoincareMap<DS,FunT>::getSign( const T & theSet,  VectorType & position, bool updatePosition)
{
  return this->getSign(theSet, position, updatePosition, this->m_dynamicalSystem.enclosure(position));
}
/*__________________________________________________________________________*/

template <typename DS, typename FunT>
template<typename T>
T PoincareMap<DS,FunT>::reachSection(T& theSet, int n)
// The common procedure to reach section for all types of the sets.
// As a result theSet is closer to section than sectionFactor * sizeOfSet
// Function returns set on the section or just after the section
{
  T setAfterTheSection(theSet);
  findSectionCrossing(theSet, setAfterTheSection, n);
  approachSection(theSet);
  return setAfterTheSection;
}


template <typename DS, typename FunT>
template<typename T>
void PoincareMap<DS,FunT>::findSectionCrossing(T & theSet, T & setAfterSection, int n)
// Functions reaches the section. As result:
// - theSet is just before the section,
// - setAfterSection is on the section or just after it

{
  ScalarType step = this->m_dynamicalSystem.getStep(); // time step used to reach the section
  bool stepChangeAllowance = this->m_dynamicalSystem.isStepChangeAllowed();
  this->m_dynamicalSystem.setStepChangeAllowance(this->m_stepControl);
  this->m_dynamicalSystem.clearCoefficients();
  if(this->m_stepControl)
  {
    ScalarType firstStep = this->m_dynamicalSystem.getFirstTimeStep(theSet,step.rightBound());
    this->m_dynamicalSystem.setStep(firstStep);
  }

  for(int iterate = 0; iterate < n; ++iterate){

     VectorType setPosition = VectorType(theSet);
     ScalarType sign = this->m_section(setPosition);

    //------------------------------------------------------------------------------------------------
    // LEAVING SECTION AND GOING UP TO THE POINT WHERE SECTION HAS CORRECT SIGN
    // We want to leave section and reach point where the sign of the section function,
    // according to crossingDirection, indicate that next section crossing will be in a good direction.

    while( (sign.contains(0.0)) ||                  // We are on the section
        !((this->m_crossingDirection == None) ||         // section sign is not correct
            ((this->m_crossingDirection == MinusPlus) && (sign < 0.0)) ||
            ((this->m_crossingDirection == PlusMinus) && (sign > 0.0))
        )
    ){
      theSet.move(this->m_dynamicalSystem);   // we make one step to leave the section and try again
      sign = this->getSign(theSet, setPosition, true);
      if(this->m_stepControl)
      {
        ScalarType newStep = this->m_dynamicalSystem.computeNextTimeStep(setPosition,10.*this->m_dynamicalSystem.getStep().rightBound());
        this->m_dynamicalSystem.setStep(newStep);
      }
    }

    //------------------------------------------------
    // first return to section with constant time step

    assert(!sign.contains(ScalarType(0.0)));

    sign = sign.mid();            // we save the sign of the section function, sign do not contain zero
    ScalarType check = sign;      // used for checking if we cross the section (if sign is changed)
    T temp(theSet);
    T *original = &theSet, *tempSet = &temp;

    // now we try to move the set closer to section than one current time step
    while(check*sign>0)
    {
      original->move(this->m_dynamicalSystem,*tempSet);
      check = this->getSign(*tempSet, setPosition, true);
      std::swap(original, tempSet);
      if(this->m_stepControl)
      {
        ScalarType newStep = this->m_dynamicalSystem.computeNextTimeStep(setPosition,10.*this->m_dynamicalSystem.getStep().rightBound());
        this->m_dynamicalSystem.setStep(newStep);
      }
    } // end while

    if(iterate == n-1) {           // last iterate
      setAfterSection = *original;
      // We take the last set with not changed section sign
      if(&theSet != tempSet)
        theSet = *tempSet;
    } else {                       // setting theSet to be after the section for the next iterate
      if(&theSet != original)
        theSet = *original;
    }
  }

  this->m_dynamicalSystem.setStepChangeAllowance(stepChangeAllowance);
}

template <typename DS, typename FunT>
template<typename T>
void PoincareMap<DS,FunT>::approachSection(T & theSet){

  ScalarType step = this->m_dynamicalSystem.getStep(); // time step used to reach the section

  bool stepChangeAllowance = this->m_dynamicalSystem.isStepChangeAllowed();
 this->m_dynamicalSystem.turnOffStepControl();;

  VectorType setPosition = VectorType(theSet);
  ScalarType sign = this->m_section(setPosition);
  sign = sign.mid();            // we save the sign of the section function, sign do not contain zero
  ScalarType check = sign;      // used for checking if we cross the section (if sign is changed)

//==================================================================================================
// We want to come to section closer than  sectionFactor * size of set in section gradient direction
// first we turn of step control
//  this->m_dynamicalSystem.turnOffStepControl();

  T temp(theSet);
  T *original = &theSet, *tempSet = &temp;

  setPosition = VectorType(theSet);
  VectorType Grad = this->m_section.gradient(setPosition);

  // maximal distance is sectionFactor * size of the set in the direction parpendicular to the section
  typename ScalarType::BoundType maxDistance = diam(abs(setPosition*Grad)).rightBound()*this->m_sectionFactor;
  int maxIterations = 30; // usually 2-3 iterations are necessary to come close enoungh to the section

  original = &theSet;
  tempSet = &temp;

  while(maxIterations)
  {
    ScalarType approxDistance = (abs(this->m_section(setPosition))).left();
    if(approxDistance.leftBound() < maxDistance)      // we are close enough
      break;

    VectorType setCenter = midVector(setPosition);
    VectorType velocity = this->m_dynamicalSystem.getField()(setCenter);
    ScalarType velocityInNormalDirection = abs(velocity * Grad);
    // We want to stop at distance equal to 1/15 of maxDistance
    // (1/15 is an experimental value, chosen as a good working)
    ScalarType approxTime = ((approxDistance-(maxDistance/15))/ velocityInNormalDirection).mid().left();

    if (step<0)
      approxTime = -approxTime;

    this->m_dynamicalSystem.setStep(approxTime);
    original->move(this->m_dynamicalSystem,*tempSet);

    int correctionTries = maxCorrectionTries ;
    while(true)
    {
      check = this->getSign(*tempSet, setPosition, false);

      if((!(check*sign>0)) && (correctionTries-- != 0))
      { // an aproximated time step is to big, we touched or crossed the section
        // so we shorten time step multiplying it by some correction factor from (0,1)
        ScalarType step = this->m_dynamicalSystem.getStep();
        ScalarType newStep = step * timeStepCorrectionFactor;
        if(step ==newStep)
          break;
        this->m_dynamicalSystem.setStep(newStep);
        original->move(this->m_dynamicalSystem,*tempSet);
      }
      else
        break;
    } // end while

    if(correctionTries != -1) {
      std::swap(original, tempSet);
      setPosition = VectorType(*original);
      Grad = this->m_section.gradient(setPosition);
      maxIterations--;
    }else{
      break;
    }
  }
  this->m_dynamicalSystem.setStep(step);
  if(&theSet != original)
    theSet = *original;
  this->m_dynamicalSystem.setStepChangeAllowance(stepChangeAllowance);
}

/////////////////////////////////////////////////////////////////////////////////////
///
/// Function used to cross the section for all types of sets
///
/// @param[in,out] theSet              set just before the section, on exit is equal to setAfterTheSection
/// @param[in]     setAfterTheSection  set on the section or just after it
/// @returns        set that contains value of Poincare map for given set theSet

template <typename DS, typename FunT>
template<typename T>
typename PoincareMap<DS,FunT>::VectorType
PoincareMap<DS,FunT>::crossSection(T& theSet, const T & setAfterTheSection)
{
  bool stepChangeAllowance = this->m_dynamicalSystem.isStepChangeAllowed();
  this->m_dynamicalSystem.turnOffStepControl();
  // theSet is very close to the section
// we compute an approximate time needed to cross the section
// if the approximate values of time step is to small to change the sign of the section function
// the 'smallTime' time is used to move the set
  ScalarType step = this->m_dynamicalSystem.getStep();
  int order = this->m_dynamicalSystem.getOrder();
  if(this->m_sectionOrder)
  {
    this->m_dynamicalSystem.setOrder(this->m_sectionOrder);
  }
   // We want stop after section, closer than  maxDistance =  sectionFactor * size of set in section gradient direction
  VectorType setPosition = VectorType(theSet);
  VectorType Grad = this->m_section.gradient(setPosition);
  typename ScalarType::BoundType maxDistance = diam(abs(setPosition*Grad)).rightBound()*this->m_sectionFactor;
  typename ScalarType::BoundType approxDistance = - abs(this->m_section(setPosition)).rightBound();

  VectorType result = setPosition;

  ScalarType check = this->m_section(setPosition);
  if(check.contains(0.0)){
    throw PoincareException<T>("Poincare exception in section crossing : initial set is already on the section ", theSet, check );
  }
  ScalarType sign = mid(check);

  // direction of section crossing =  PlusMinus or MinusPlus
  // we check sign of the section instead of checking value of variable crossingDirection because it can be set to None
  typename BasicPoincareMap<DS, FunT>::CrossingDirection direction = ( check > 0)? PlusMinus: MinusPlus;

  T temp(theSet); // we save the set before section, used in throwing exception only
  saveMatrices(theSet); // we save the \frac{d}{dx}\phi

  T* original = &theSet;
  T* tempSet = &temp;
  bool sectionReached = false;

  while(!(check*sign < 0))
  {

    VectorType fieldDirection = this->m_dynamicalSystem.getField()(midVector(setPosition));
    ScalarType fieldSectionDirection = abs(fieldDirection * Grad);
    ScalarType approxTime = ((maxDistance/2 - approxDistance ) / fieldSectionDirection).mid();

    // if approxTime is too big, it can cause problems with finding an enclosure.
    // In this case we use original time step (possibly several times)
    approxTime = capd::min(approxTime, abs(step));

    // approxTime cannot be too small, otherwise it can occur that we will never cross the section
    approxTime = capd::max(approxTime, minCrossingTimeStep);
    // approxTime = capd::max(approxTime/10, minCrossingTimeStep);

    if (step<0)
      approxTime = -approxTime;
    int correctionTries = maxCorrectionTries;
    while(true)
    {
      this->m_dynamicalSystem.setStep(approxTime.left());
      original->move(this->m_dynamicalSystem,*tempSet);
      setPosition = VectorType(*tempSet);
      check = this->m_section(setPosition);

      if(direction == PlusMinus)
        approxDistance = - check.rightBound();
      else
        approxDistance = check.leftBound();

      if((approxDistance  > maxDistance)&& (correctionTries-- != 0)){  // the step was too big
        approxTime *= timeStepCorrectionFactor;  // so we shorten it
      }else{
        break;
      }
    }

    VectorType bound = this->m_dynamicalSystem.enclosure(VectorType(*original));
    checkTransversability(*original, bound);
    if((!sectionReached) && (check*sign > 0)){ // we did not touch the section yet
       result = setPosition;
       this->saveMatrices(*tempSet);
    }else{
      this->computeJacEnclosure(theSet, bound);

      // TODO: It was computed already in checkTranversability
      VectorType Fresult = this->m_dynamicalSystem.getField()(bound);

      for(int i=0;i<this->m_dim;i++)
      {
        if(!(Fresult[i].contains(0.)))
           result[i] = intervalHull(result[i],setPosition[i]);
        else
           result[i] = intervalHull(result[i],bound[i]); // bound is an enclosure
      }
    }
    T* swapSet = original;
    original = tempSet;
    tempSet = swapSet;

  } // end while

  this->m_dynamicalSystem.setStep(step);
  if(this->m_sectionOrder) {
    this->m_dynamicalSystem.setOrder(order);
  }
  this->m_dynamicalSystem.setStepChangeAllowance(stepChangeAllowance);

  theSet = setAfterTheSection;
  return result;
}

/// Function checks if we crossed section and then returned in one step.
/// In this case it throws an exception of PoincareException<T> type.
template <typename DS, typename FunT>
template<typename T>
void PoincareMap<DS,FunT>::checkTransversability(
  const T & theSet, const VectorType & bound
){
  ScalarType check = this->m_section(bound);

  if(subset(ScalarType(0.0), check)) {  // Is the section crossed?
    ScalarType innerProduct = this->m_section.gradient(bound)*this->m_dynamicalSystem.getField()(bound);
    if (innerProduct.contains(0.0)) {  // Is the vector field orthogonal to section gradient?
      throw PoincareException<T>(
              "Poincare error: possible nontranversal return to the section ", theSet, theSet,
              bound, this->m_dynamicalSystem.getField()(bound),
              check, this->m_section.gradient(bound), innerProduct
              );
    }
  }

}

}} // namespace capd::poincare

#endif // _CAPD_POINCARE_POINCARE_MAP_HPP_

/// @}
