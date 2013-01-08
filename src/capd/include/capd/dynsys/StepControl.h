/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file StepControl.h
///
/// @author Tomasz Kapela, Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_STEP_CONTROL_H_
#define _CAPD_DYNSYS_STEP_CONTROL_H_

#include "capd/capd/TypeTraits.h"
//#include "capd/interval/DoubleInterval.h"
#include "capd/rounding/DoubleRounding.h"
#include "capd/capd/power.h"
#include "capd/capd/minmax.h"
#include "capd/vectalg/Norm.hpp"

#include "capd/auxil/logger.h"

namespace capd {
namespace dynsys {

/// the following function clears the last bits of mantissa
///
template <class Real>
Real clearMantissaBits(Real step, Real maxValue = 32) {
  //capd::rounding::DoubleRounding::roundNearest();
  // fill the mantissa by zeroes
  bool isNegative = (step < capd::TypeTraits<Real>::zero());
  if(isNegative)
    step = -step;

  int counter = 0;
  while(step < maxValue) {
    step *= 2;
    counter++;
  }
  step = toInt(step);
  step /= (1L << (counter));
 // std::cout << "predicted step   " << step << std::endl;
  return isNegative ? -step : step;
}

// ---------------------------------------------------------------------
/// This class is a common interface for StepControl
/// used in PoincareMap and TimeMap.
/// Both classes inherit this interface
template <class StepControlT>
class StepControlInterface {
public:
  typedef StepControlT StepControlType;

  StepControlInterface() : m_onOffStepControl(false){
  }

  StepControlInterface(const StepControlType& stepControl) :
    m_stepControl(stepControl), m_onOffStepControl(false) {
  }

  void turnOnStepControl() {
    m_onOffStepControl = true;
  }

  void turnOffStepControl() {
    m_onOffStepControl = false;
  }

  const StepControlType& getStepControl() const {
    return m_stepControl;
  }

  void setStepControl(const StepControlType& stepControl) {
    m_stepControl = stepControl;
  }

  bool isStepChangeAllowed() const
  {
    return m_onOffStepControl;
  }

  void setStepChangeAllowance(bool onOffStepControl)
  {
    this->m_onOffStepControl = onOffStepControl;
  }


protected:
  StepControlType m_stepControl;
  bool m_onOffStepControl;
};


template <class StepControlT>
class NoStepControlInterface{
public:
  typedef StepControlT StepControlType;
  NoStepControlInterface(){
  }
  NoStepControlInterface(const StepControlType& stepControl) :
    m_stepControl(stepControl){
  }

  void turnOnStepControl() {
  }

  void turnOffStepControl() {
  }

  const StepControlType& getStepControl() const {
    return false;
  }

  void setStepControl(const StepControlType& stepControl) {
    m_stepControl = stepControl;
  }

  bool isStepChangeAllowed() const
  {
    return false;
  }

  ///
  void setStepChangeAllowance(bool onOffStepControl){
  }

protected:
  StepControlType m_stepControl;
};

/// This class provides an empty time step control for the solutions to ODEs.
/// It contains an interface for other implementations of TSC.
class NoStepControl {
public:

  template <class DS, class SetType>
  typename DS::ScalarType computeNextTimeStep(DS& dynamicalSystem, const SetType&, const typename DS::ScalarType& maxStep){
    return capd::min(dynamicalSystem.getStep(),maxStep);
  }

  template <class DS,class SetType>
  typename DS::ScalarType getFirstTimeStep(DS& dynamicalSystem, const SetType&, const typename DS::ScalarType& maxStep) {
    return capd::min(dynamicalSystem.getStep(),maxStep);
  }

  double getMinStepAllowed() { // here it does not matter what is the minimal time step
    return 1e-20;
  }
};

// ---------------------------------------------------------------------
template <>
class StepControlInterface<NoStepControl> : public NoStepControlInterface<NoStepControl>{
public:
  typedef NoStepControl StepControlType;
  StepControlInterface(){
  }
  StepControlInterface(const StepControlType& stepControl) :
    NoStepControlInterface<NoStepControl>(stepControl){
  }

};

// ---------------------------------------------------------------------

///
template <typename ScalarType>
class FixedStepControl {
public:
  FixedStepControl(const ScalarType & timeStep = ScalarType(1./1024.)) : m_timeStep(timeStep){
  }
  template <class DS, class SetType>
  typename DS::ScalarType computeNextTimeStep(DS& dynamicalSystem, const SetType&, const typename DS::ScalarType& maxStep){
    return capd::min(m_timeStep, maxStep);
  }

  template <class DS,class SetType>
  typename DS::ScalarType getFirstTimeStep(DS& dynamicalSystem, const SetType&, const typename DS::ScalarType& maxStep) {
    return capd::min(m_timeStep, maxStep);
  }

  double getMinStepAllowed() { // here it does not matter what is the minimal time step
    return 1e-20;
  }
private:
  ScalarType m_timeStep;
};

// ---------------------------------------------------------------------

template<class DS>
typename DS::ScalarType 
computeNextStep(DS& dynamicalSystem, const typename DS::ScalarType& maxStep, int numberOfTerms, double epsilon, double minTimeStep)
{
  typedef typename DS::ScalarType ScalarType;
  typedef typename TypeTraits<ScalarType>::Real Real;
  int order = dynamicalSystem.getOrder();
  double optStep = toDouble(capd::abs(rightBound(maxStep)));

  for(int i = order; (i > order - numberOfTerms) && (i > 0); i--) {
    double coeffNorm = toDouble(rightBound(dynamicalSystem.getCoeffNorm(i)));
    capd::rounding::DoubleRounding::roundNearest();
    double step = exp(log(epsilon / coeffNorm) / (i));
    optStep = capd::min(optStep, step);
  }

  optStep = capd::max(optStep, minTimeStep);
  optStep = clearMantissaBits(optStep);

  optStep = capd::max(optStep,minTimeStep);
  optStep = capd::min(optStep,toDouble(capd::abs(leftBound(maxStep))));
  if(dynamicalSystem.getStep()<0)
    optStep = - optStep;
  return ScalarType(Real(optStep));  
}

class ILastTermsStepControl {
public:
  typedef double Real;

  ILastTermsStepControl(int _terms = 1,
      Real _tolerance = 1.e-20,  //power(10, -TypeTraits<Real>::numberOfDigits()-3),    // < this is not needed because Real is fixed.
      Real _minStep = 1. / 1048576.) :
    m_numberOfTerms(_terms), m_epsilon(_tolerance), m_minTimeStep(_minStep) {
  }

  template <class DS, class SetType>
  typename DS::ScalarType computeNextTimeStep(DS& dynamicalSystem, const SetType& , const typename DS::ScalarType& maxStep) {
    return computeNextStep(dynamicalSystem,maxStep, m_numberOfTerms, m_epsilon, m_minTimeStep);
  }

  template <class DS, class SetType>
  typename DS::ScalarType getFirstTimeStep(DS& dynamicalSystem, const SetType& s, const typename DS::ScalarType& maxStep) {
    typedef typename DS::ScalarType ScalarType;
    typedef typename DS::VectorType VectorType;
    typedef typename DS::MatrixType MatrixType;
    typedef typename TypeTraits<ScalarType>::Real Float;

    VectorType x(s);
    MatrixType df = dynamicalSystem.getField()[x];
    capd::vectalg::EuclNorm<VectorType,MatrixType> N;
    Float lipConstant = rightBound(N(df));
    Float h = capd::min(Float(1.)/lipConstant,Float(1.));
    h = capd::min(h,maxStep.leftBound());
    
    x += ScalarType(Float(0.),h)*dynamicalSystem.getField()(x);
    x = dynamicalSystem(x);
    ++m_numberOfTerms;
    ScalarType firstStep =  this->computeNextTimeStep(dynamicalSystem,x,maxStep);
    --m_numberOfTerms;
    return firstStep;
  }

  Real getMinStepAllowed() const
  {
    return m_minTimeStep;
  }

  int m_numberOfTerms;
  Real m_epsilon;
  Real m_minTimeStep;
};

// ---------------------------------------------------------------------

class DLastTermsStepControl {
public:
  typedef double Real;

  DLastTermsStepControl(int _terms = 3, Real _tolerance = power(10, -TypeTraits<Real>::numberOfDigits()-3), Real _minStep = 1. / 1048576.) :
    m_numberOfTerms(_terms), m_epsilon(_tolerance), m_minTimeStep(_minStep) {
  }

  template <class DS, class SetType>
  typename DS::ScalarType computeNextTimeStep(DS& dynamicalSystem, const SetType& , const typename DS::ScalarType& maxStep) {
    return computeNextStep(dynamicalSystem,maxStep, m_numberOfTerms, m_epsilon, m_minTimeStep);
  }

  template <class DS, class SetType>
  typename DS::ScalarType getFirstTimeStep(DS& dynamicalSystem, const SetType& s, const typename DS::ScalarType& maxStep) {
    typedef typename DS::ScalarType ScalarType;
    typedef typename DS::VectorType VectorType;
    typedef typename DS::MatrixType MatrixType;
    typedef typename TypeTraits<ScalarType>::Real Float;

    VectorType x(s);
    MatrixType df = dynamicalSystem.getField()[x];
    capd::vectalg::EuclNorm<VectorType,MatrixType> N;
    Real lipConstant = toDouble(rightBound(N(df)));
    Real h = 1./lipConstant;
    dynamicalSystem.setStep(ScalarType(h));
    x = dynamicalSystem(x);
    ScalarType firstStep = this->computeNextTimeStep(dynamicalSystem,x,maxStep);
    return firstStep;
  }

  Real getMinStepAllowed() const
  {
    return m_minTimeStep;
  }

  int m_numberOfTerms;
  Real m_epsilon;
  Real m_minTimeStep;
};

template <typename Real>
class MyDLastTermsStepControl {
public:
  typedef Real ScalarType;
  MyDLastTermsStepControl(int _terms = 3, Real _tolerance = power(10, -TypeTraits<Real>::numberOfDigits()-4), Real _minStep = 1. / 1048576.) :
    m_numberOfTerms(_terms), m_epsilon(_tolerance), m_minTimeStep(_minStep) {
  }

  template <class DS, class SetType>
  typename DS::ScalarType computeNextTimeStep(DS& dynamicalSystem, const SetType& , const typename DS::ScalarType& maxStep) {

    typename DS::ScalarType time = computeNextStep(dynamicalSystem,maxStep, m_numberOfTerms, m_epsilon, m_minTimeStep);
    capd::scon << "   " << time;
    return time;
  }

  template <class DS, class SetType>
  typename DS::ScalarType getFirstTimeStep(DS& dynamicalSystem, const SetType& s,  const typename DS::ScalarType& maxStep) {
    typedef typename DS::VectorType VectorType;
    typedef typename DS::MatrixType MatrixType;

    VectorType x = VectorType(s);
    MatrixType df = dynamicalSystem.getField()[x];
    capd::vectalg::EuclNorm<VectorType,MatrixType> norm;
    ScalarType lipConstant = norm(df);
    ScalarType h = 1./lipConstant;
    dynamicalSystem.setStep(h);
    x = dynamicalSystem(x);
    ScalarType firstStep = this->computeNextTimeStep(dynamicalSystem,x,maxStep);
    return firstStep;
  }

  Real getMinStepAllowed() const
  {
    return m_minTimeStep;
  }

  int m_numberOfTerms;
  Real m_epsilon;
  Real m_minTimeStep;
};

// ---------------------------------------------------------------------


class IEncFoundStepControl {
public:
  typedef double Real;
  /**
   * Constructor
   * @param minStep     minimal allowed step size
   * @param stepFactor  fraction of maximal possible time step to be taken as optimal time step (optimal = stepFactor * maximal)
   */
  IEncFoundStepControl(Real minStep = 1. / 1048576., Real stepFactor = 0.25) :
    m_minTimeStep(minStep), m_stepFactor(stepFactor) {
  }

  template <class DS, class SetType>
  typename DS::ScalarType computeNextTimeStep(DS& dynamicalSystem, const SetType& _x, typename DS::ScalarType maxStep) {
    typedef typename DS::ScalarType ScalarType;
    typedef typename TypeTraits<ScalarType>::Real Real;
    typename DS::VectorType x(_x);
    ScalarType optStep = dynamicalSystem.getStep()/ m_stepFactor * Real(1.5);
    dynamicalSystem.setStep(optStep);
    while(optStep >= m_minTimeStep) {
      try {
        dynamicalSystem.enclosure(x);
        // if succeed then break
        break;
      } catch(...) {
        optStep = (optStep*Real(0.8)).leftBound();
        dynamicalSystem.setStep(optStep);
      }
    }
    
    double result = toDouble(rightBound(optStep));
    result = clearMantissaBits(result * m_stepFactor);
    result = capd::max(result,m_minTimeStep);
    return capd::min(ScalarType(Real(result)),maxStep);
  }

  template <class DS, class SetType>
  typename DS::ScalarType getFirstTimeStep(DS& dynamicalSystem, const SetType& x, const typename DS::ScalarType& maxStep) {
    return this->computeNextTimeStep(dynamicalSystem,x,maxStep);
  }

  Real getMinStepAllowed() const
  {
    return m_minTimeStep;
  }

  Real m_minTimeStep;
  Real m_stepFactor;  // what part of maximal possible step take as optimal one
};

}
} // namespace capd::dynsys


#endif // #define _CAPD_POINCARE_STEP_CONTROL_H_
/// @}
