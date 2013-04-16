/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file TimeMap.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file is part of the CAPD library.  This library is free software;
// you can redistribute it and/or modify it under the terms of the GNU
// General Public License as published by the Free Software Foundation;
// either version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this software; see the file "license.txt".  If not, write to the
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

#ifndef _CAPD_POINCARE_TIME_MAP_H_
#define _CAPD_POINCARE_TIME_MAP_H_

#include <string>

namespace capd{
namespace poincare{

  /**
   *  TimeMap class computes image of the set under flow of given Dynamial System
   *  after specified time
   *
   *  @remark For good estimates use time steps that are representable
   *          e.g. 2^{-7} = 1./128. instead of 0.01
   **/
template<typename DS>
class TimeMap
{
public:
  typedef DS DynSysType;
  typedef typename DS::MapType MapType;
  typedef typename DS::FunctionType FunctionType;
  typedef typename DS::MatrixType MatrixType;
  typedef typename DS::VectorType VectorType;
  typedef typename DS::ScalarType ScalarType;

  TimeMap(DS &dynamicalSystem);

  /// For given vector v it computes its position after time 'time'
  VectorType operator()(ScalarType time, VectorType v);
  // For given vector v it computes its position after time 'time' and derivative with respect to initial conditions
  VectorType operator()(ScalarType time, VectorType v, MatrixType &derivative);

  // For given vector v it computes its position after time 'time' and higher order derivatives with respect to initial conditions
  template<class CnCoeffType>
  VectorType operator()(ScalarType time, const VectorType& v, CnCoeffType& result);

  /// For given set it computes its position after time 'time'
  /// (for DS=CnTaylor it works also for CnCoeffs)
  template<typename SetType>
  VectorType operator()(ScalarType time, SetType &theSet );

  /// For given set it computes its position after time 'time' and derivative with respect to initial conditions
  template<typename SetType>
  VectorType operator()(ScalarType time, SetType &theSet, MatrixType & derivative);

  /// Returns current dynamical system
  const DS & getDynamicalSystem() const{
    return m_dynamicalSystem;
  }
  /// Returns current dynamical system
  DS & getDynamicalSystem(){
     return m_dynamicalSystem;
  }

  const MapType& getField() const;
  MapType& getField();

  int getOrder() const;
  const ScalarType& getStep() const;

  void setOrder(int newOrder);
  void setStep(const ScalarType& newStep);

  void turnOnStepControl() {
    m_stepControl = true;
  }

  void turnOffStepControl() {
    m_stepControl = false;
  }

  void stopAfterStep(bool b) {
    m_oneStep = b;
  }

  bool completed() const {
    return m_completed;
  }

  const ScalarType& getCurrentTime() const {
    return m_currentTime;
  }

protected:

  template<class SetType>
  void makeOneStep(SetType& s){
    m_dynamicalSystem(s);
  }

  void makeOneStep(VectorType & x){
    x = m_dynamicalSystem(const_cast<const VectorType & >(x));
  }

  template<class SetType>
  void moveSet(ScalarType time, SetType& s);

// the fields of the class

  DS& m_dynamicalSystem; // a template dynamical system (Taylor or C2Taylor)
  int m_dim;
  bool m_stepControl;

  void* m_currentSet;
  bool m_oneStep;
  ScalarType m_currentTime;
  bool m_completed;
}; // end of template TimeMap

// -----------------------  inline definitions -------------------------------

template <typename DS>
inline TimeMap<DS>::TimeMap(DS &ds)
  : m_dynamicalSystem(ds), m_stepControl(true), m_currentSet(0), m_oneStep(false), m_currentTime(0.), m_completed(true)
{
  m_dim = ds.getField().dimension();
}

template <typename DS>
inline const typename TimeMap<DS>::MapType& TimeMap<DS>::getField() const
{
  return m_dynamicalSystem.getField();
}

template <typename DS>
inline typename TimeMap<DS>::MapType& TimeMap<DS>::getField()
{
  return m_dynamicalSystem.getField();
}

template <typename DS>
inline int TimeMap<DS>::getOrder() const
{
  return m_dynamicalSystem.getOrder();
}

template <typename DS>
inline const typename TimeMap<DS>::ScalarType&
TimeMap<DS>::getStep() const
{
  return m_dynamicalSystem.getStep();
}

template <typename DS>
inline void TimeMap<DS>::setOrder(int newOrder)
{
  m_dynamicalSystem.setOrder(newOrder);
}

template <typename DS>
inline void TimeMap<DS>::setStep(const ScalarType& newStep)
{
  m_dynamicalSystem.setStep(newStep);
}

// template members

template <typename DS>
template<typename SetType>
void TimeMap<DS>::moveSet(ScalarType Time, SetType &originalSet)
{
  ScalarType step = m_dynamicalSystem.getStep();

  if(m_currentSet != &originalSet)
  {
    m_dynamicalSystem.setStepChangeAllowance(m_stepControl);
    m_dynamicalSystem.clearCoefficients();
    if(m_stepControl)
    {
      step = m_dynamicalSystem.getFirstTimeStep(originalSet,Time);
      m_dynamicalSystem.setStep(step);
    }
    m_currentTime = ScalarType(0.0);
    m_currentSet = &originalSet;
    m_completed = false;
  }
  else
  {
    if(m_stepControl)
    {
      step = m_dynamicalSystem.computeNextTimeStep(originalSet,Time);
      m_dynamicalSystem.setStep(step);
    }
  }

  if(step >= 0) {
      while((m_currentTime + step) < Time)
      {
          this->makeOneStep(originalSet);
          /// the time step can be decreased by the move routine
          m_currentTime += m_dynamicalSystem.getStep();
          if(m_oneStep)
              return;
          else
          {
              if(m_stepControl)
              {
                  step = m_dynamicalSystem.computeNextTimeStep(originalSet,Time);
                  m_dynamicalSystem.setStep(step);
              }
          }
      }
  } else {
      while((m_currentTime + step) > Time)
      {
          this->makeOneStep(originalSet);
          /// the time step can be decreased by the move routine
          m_currentTime += m_dynamicalSystem.getStep();
          if(m_oneStep)
              return;
          else
          {
              if(m_stepControl)
              {
                  step = m_dynamicalSystem.computeNextTimeStep(originalSet,Time);
                  m_dynamicalSystem.setStep(step);
              }
          }
      }
  }
   // we make last step
  ScalarType lastStep = Time - m_currentTime;
  m_dynamicalSystem.setStep(lastStep);
  m_dynamicalSystem.turnOffStepControl();
  this->makeOneStep(originalSet);

  m_currentSet = 0;
  m_completed = true;
  m_currentTime += m_dynamicalSystem.getStep();
}

// ---------------------------------------------------------

template <typename DS>
template<typename SetType>
typename DS::VectorType TimeMap<DS>::operator()(ScalarType Time, SetType &originalSet)
{
  this->moveSet(Time,originalSet);
  return VectorType(originalSet);
}

// ---------------------------------------------------------

template <typename DS>
template<typename SetType>
typename DS::VectorType TimeMap<DS>::operator()(ScalarType Time, SetType &originalSet, MatrixType & derivative)
{
  this->moveSet(Time,originalSet);
  derivative = (MatrixType) originalSet;
  return VectorType(originalSet);
}

// ---------------------------------------------------------

template <typename DS>
template <typename CnCoeffType>
typename TimeMap<DS>::VectorType
TimeMap<DS>::operator()(ScalarType Time, const VectorType& v, CnCoeffType& result)
// the point on trajectory just after time 'time'
{
  result.clear();
  result() = v;
  result.setMatrix(MatrixType::Identity(v.dimension()));
  ScalarType originalStep = m_dynamicalSystem.getStep();
  this->stopAfterStep(false);
  this->moveSet(Time, result);
  return VectorType(result);
}
}} // namespace capd::poincare

#endif // _CAPD_POINCARE_TIME_MAP_H_



/// @}
