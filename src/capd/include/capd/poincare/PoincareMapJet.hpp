/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file  PoincareMapJet.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_POINCARE_POINCARE_MAP_JET_HPP_
#define _CAPD_POINCARE_POINCARE_MAP_JET_HPP_

#include <cassert>
#include "capd/poincare/PoincareMapJet.h"
#include "capd/poincare/PoincareMap.hpp"

namespace capd{
namespace poincare{

template <typename DS, typename FunT>
template<typename T>
typename PoincareMapJet<DS,FunT>::VectorType
PoincareMapJet<DS,FunT>::operator()(T& originalSet)
{
// We move the set to be very close to the section
   T setAfterTheSection = this->reachSection(originalSet);

// and compute the PoincareMap image
   CurveType c = this->crossSection(originalSet, setAfterTheSection);
   return c(ScalarType(c.getLeftDomain(),c.getRightDomain()));
}

/*__________________________________________________________________________*/

template <typename DS, typename FunT>
template<typename T>
typename PoincareMapJet<DS,FunT>::VectorType
PoincareMapJet<DS,FunT>::operator()(T& originalSet, MatrixType& der)
{
   T setAfterTheSection = this->reachSection(originalSet);

   MatrixType matrixBeforeSection(originalSet);
// and compute the PoincareMap image
   CurveType c = this->crossSection(originalSet, setAfterTheSection);
   ScalarType domain(ScalarType(c.getLeftDomain(),c.getRightDomain()));
   der = c[domain]*matrixBeforeSection;
   return c(domain);
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
typename PoincareMapJet<DS,FunT>::CurveType 
PoincareMapJet<DS,FunT>::crossSection(T& theSet, const T & setAfterTheSection)
{
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
//  typename BasicPoincareMap<DS, FunT>::CrossingDirection direction = ( check > 0)? PlusMinus: MinusPlus;

  T temp(theSet); // we save the set before section, used in throwing exception only

  VectorType fieldDirection = this->m_dynamicalSystem.getField()(midVector(setPosition));
  ScalarType fieldSectionDirection = abs(fieldDirection * Grad);
  ScalarType approxTime = ((maxDistance/2 - approxDistance ) / fieldSectionDirection).mid();

  // if approxTime is too big, it can cause problems with finding an enclosure.
  // In this case we use original time step (possibly several times)
  approxTime = capd::min(approxTime, abs(step));

  /// approxTime cannot be too small, otherwise it can occur that we will never cross the section
  approxTime = capd::max(approxTime, PoincareMapT::minCrossingTimeStep);
  if (step<0)
    approxTime = -approxTime;

  this->m_dynamicalSystem.setStep(10.*approxTime.left());

  theSet.move(this->m_dynamicalSystem);

  CurveType c = this->m_dynamicalSystem.getCurve();
  ScalarType domain(c.getLeftDomain(),c.getRightDomain());
  VectorType bound = c(domain);
  checkTransversability(theSet, bound);
  setPosition = VectorType(theSet);
  check = this->m_section(setPosition);

//  std::cout << "domain=" << domain << std::endl;
  if(!(check*sign < 0)){ // we did not touch the section yet
    throw std::runtime_error("PoincareMapJet error: cannot cross the section in one step");
  }

  // now we resolve for the return time
  CurveType der = c.derivative();
  for(int i=0;i<2;++i)
  {
    ScalarType midPoint = domain.mid();
    ScalarType valAtMidPoint = this->m_section(c(midPoint));
    ScalarType derAtDomain = this->m_section.gradient(bound) * der(domain);
    ScalarType N = midPoint - valAtMidPoint/derAtDomain;
    ScalarType newDomain;
    if(!intersection(domain,N,newDomain))
      throw std::runtime_error("PoincareMapJet error: empty intersection in estimation of the return time");
    
    c.setDomain(leftBound(newDomain),rightBound(newDomain));
    der.setDomain(leftBound(newDomain),rightBound(newDomain));
    domain = newDomain;
//    std::cout << "newDomain=" << newDomain << std::endl;
    
  }

  this->m_dynamicalSystem.setStep(step);
  theSet = setAfterTheSection;
  this->m_dynamicalSystem.setOrder(order);
  return c;
}

}} // namespace capd::poincare

#endif // _CAPD_POINCARE_POINCARE_MAP_HPP_

/// @}
