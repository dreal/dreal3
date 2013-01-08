/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DPoincareMap.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_DPOINCARE_MAP_H_
#define _CAPD_DPOINCARE_MAP_H_

#include <string>
#include "capd/DTaylor.h"
#include "capd/poincare/BasicPoincareMap.h"

namespace capd{

class DPoincareMap
{
public:
  typedef DMap MapType;
  typedef DFunction FunctionType;
  typedef DMatrix MatrixType;
  typedef DVector VectorType;
  typedef double ScalarType;
  typedef capd::poincare::BasicPoincareMap<DTaylor> BasePoincare;

  DPoincareMap(const MapType vField,
             const FunctionType& section,
             int order,
             double step,
             double factor=0.1
    ) : m_vectorField(vField),
        m_ds(m_vectorField,order,step),
        m_pm(m_ds,section,factor)
  {}
    
  
  DPoincareMap(const std::string& vField,
             const FunctionType& section,
             int order,
             double step,
             double factor=0.1
    ) : m_vectorField(vField),
        m_ds(m_vectorField,order,step),
        m_pm(m_ds,section,factor)
  {}

  VectorType operator()(const VectorType& v){
    return m_pm(v);
  }
  
  VectorType operator()(const VectorType& u, MatrixType& der){
    return m_pm(u,der);
  }

// computations of derivatives of Poincare map from the serivatives of flow
  VectorType computeDT(const VectorType& Px, const MatrixType& derivativeOfFlow){
    return m_pm.computeDT(Px,derivativeOfFlow);
  }
  MatrixType computeDP(const VectorType& Px, const MatrixType& derivativeOfFlow, const VectorType& dT){
    return m_pm.computeDP(Px,derivativeOfFlow,dT);
  }
  
  /// Computes derivative of Poincare Map dP 
  MatrixType computeDP(const VectorType& Px, const MatrixType& derivativeOfFlow){
    return m_pm.computeDP(Px,derivativeOfFlow);
  }
 
  const MapType& getField() const{
    return m_pm.getField();
  }
  const FunctionType& getSection() const{
    return m_pm.getSection();
  }
  int getOrder() const{
    return m_pm.getOrder();
  }
  const ScalarType getStep() const{
    return m_pm.getStep();
  }

  void setOrder(int newOrder){
    m_pm.setOrder(newOrder);
  }
  void setStep(const ScalarType& newStep){
    m_pm.setStep(newStep);
  }
  void setFactor(double newFactor){
    m_pm.setFactor(newFactor);
  }
  void setParameter(const std::string& name, double value){
    m_vectorField.setParameter(name,value);
  }

protected:

  DMap m_vectorField;
  DTaylor m_ds;
  BasePoincare m_pm;
}; // end of template PoincareMap


} // namespace capd

#endif // _CAPD_DPOINCARE_MAP_H_

/// @}
