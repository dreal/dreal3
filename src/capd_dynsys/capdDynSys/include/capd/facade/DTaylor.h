
/////////////////////////////////////////////////////////////////////////////
/// @file DTaylor.h
///
/// @author Daniel Wilczak
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2001-2005 */

#ifndef _CAPD_FACADE_DTAYLOR_H_
#define _CAPD_FACADE_DTAYLOR_H_

#include <string>
#include "capd/dynsys/BasicTaylor.h"
#include "capd/facade/DMap.h"

namespace capd{
namespace facade{

class DTaylor : public capd::dynsys::StepControlInterface< capd::dynsys::DLastTermsStepControl>
{
public:
  typedef capd::dynsys::DLastTermsStepControl StepControl;
  typedef capd::dynsys::BasicTaylor<DMap, StepControl> BaseTaylor;
  typedef DMap MapType;
  typedef DFunction FunctionType;
  typedef DMatrix MatrixType;
  typedef DVector VectorType;
  typedef double ScalarType;
  typedef BaseTaylor::CurveType CurveType;

  DTaylor(MapType& field, int order, const ScalarType& step)
    : m_vectorField(&field),
      m_taylor(*m_vectorField,order,step),
      m_hasOwnVectorField(false)
  {}

  DTaylor(const std::string& field, int order, const ScalarType& step)
    : m_vectorField( new MapType(field,order+1) ),
      m_taylor(*m_vectorField,order,step),
      m_hasOwnVectorField(true)
  {}

  DTaylor(const char* field, int order, const ScalarType& step)
    : m_vectorField( new MapType(field,order+1) ),
      m_taylor(*m_vectorField,order,step),
      m_hasOwnVectorField(true)
  {}

  ~DTaylor(){
    if(m_hasOwnVectorField)
      delete m_vectorField;
  }

  VectorType operator()(const VectorType &u) {
    return m_taylor(u);
  }
  VectorType operator()(const VectorType &u, MatrixType &derivative) {
    return m_taylor(u,derivative);
  }

  const MapType& getField() const{
    return m_taylor.getField();
  }

  MapType& getField() {
    return m_taylor.getField();
  }

  int getOrder() const{
    return m_taylor.getOrder();
  }
  void setOrder(int newOrder){
    m_taylor.setOrder(newOrder);
  }

  const double getStep() const{
    return m_taylor.getStep();
  }

  void setStep(const ScalarType& newStep){
    m_taylor.setStep(newStep);
  }

  void setParameter(const std::string &name, const ScalarType& value){
    m_vectorField->setParameter(name,value);
  }

  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return m_taylor.computeNextTimeStep(x, maxStep);
  }

  template <class SetType>
  ScalarType getFirstTimeStep(const SetType& x, const ScalarType& maxStep) {
    return m_taylor.getFirstTimeStep(x, maxStep);
  }

  void clearCoefficients(){
    m_taylor.clearCoefficients();
  }

  const CurveType& getCurve(){
    return m_taylor.getCurve();
  }

private:
  void operator=(const DTaylor&){}
  MapType* m_vectorField;
  BaseTaylor m_taylor;
  bool m_hasOwnVectorField;
};

}} // namespace capd::facade

#endif // define _CAPD_FACADE_DTAYLOR_H_

