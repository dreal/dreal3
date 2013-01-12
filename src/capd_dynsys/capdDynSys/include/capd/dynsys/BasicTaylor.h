/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicTaylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSYS_BASICTAYLOR_H_
#define _CAPD_DYNSYS_BASICTAYLOR_H_

#include <string>
#include "capd/dynsys/StepControl.h"
#include "capd/diffAlgebra/Curve.h"
#include "capd/map/C1Coeff.h"

namespace capd {
namespace dynsys {
/** MapT constraints:
 *  type definitions:
 *   - FunctionType
 *   - MatrixType
 *   - MatrixType::RowVectorType
 *   - MatrixType::ScalarType
 *
 *  methods:
 *   - dimension            - dimension of the space
 *   - getOrder, setOrder   - order of Taylor expansion
 *   - operator()(a, i)     - computes coeffs a_i from a = a_{i-1}
 *   - variational(x_coeff, m_F, m_order);
 *
 */

template <typename MapT, typename StepControlT = capd::dynsys::DLastTermsStepControl>
class BasicTaylor : public capd::dynsys::StepControlInterface<StepControlT>{
public:
  typedef MapT MapType;
  typedef StepControlT StepControlType;
  typedef typename MapT::FunctionType FunctionType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::diffAlgebra::Curve<MatrixType> CurveType;

  BasicTaylor(MapType& field, int order, const ScalarType& step, const StepControlT& stepControl = StepControlT());
  virtual ~BasicTaylor();

  /// Computes image of vector v after one time step
  VectorType operator()(const VectorType &);

  /// Computes image of vector v and derivatives of a flow with respect to init condition (v,identity)
  VectorType operator()(const VectorType & v, MatrixType & resultDerivative) ;

  /// Computes image of vector v and derivatives of a flow with respect to init condition (v, derivative)
  VectorType operator()(const VectorType & v, const MatrixType & derivative, MatrixType & resultDerivative) ;

  /// Computes value and derivative after one step with initial condition in coeff
  /// The full result is stored in coeff and also value is returned
  VectorType operator()(capd::map::C1Coeff<MatrixType> & coeffs);

  const MapType& getField() const; ///< Returns vector field
  MapType& getField();

  int getOrder() const; ///< Returns Taylor method order
  virtual void setOrder(int newOrder); ///< Sets Taylor method order

  const ScalarType& getStep() const; ///< Returns current time step
  void setStep(const ScalarType& newStep); ///< Sets time step

  ScalarType getCoeffNorm(int i) const {
    return (m_curve.getCoefficientsAtCenter()[i]+m_curve.getRemainderCoefficients()[i]).euclNorm();
  }

  /// for nonautonomous ODEs
  void differentiateTime() const {
    m_vField->differentiateTime();
  }
  void setCurrentTime(const ScalarType& a_time) const {
    m_vField->setCurrentTime(a_time);
  }
  const ScalarType& getCurrentTime() const {
    return m_vField->getCurrentTime();
  }

  int dimension() const;
  
  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.computeNextTimeStep(*this,x,maxStep);
  }

  template <class SetType>
  ScalarType getFirstTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.getFirstTimeStep(*this,x,maxStep);
  }

  void clearCoefficients();
  const CurveType& getCurve();

protected:
  void operator=(const BasicTaylor&) {
  } /// we do not allow copying of objects
  BasicTaylor(const BasicTaylor &) 
    : capd::dynsys::StepControlInterface<StepControlT>(this->m_stepControl),     
      m_curve(0.,0.,1,1)
  { } /// we do not allow copying of objects

  void computeMatrixCoeff(int, VectorType* coeff, MatrixType* matrixCoeff, const MatrixType& H);
  void computeCoefficients(int, VectorType* coeff, const VectorType &iv);

  MapType* m_vField;
  CurveType m_curve;
  ScalarType m_step;
  
  MatrixType *m_F; // temporary array used in the computations of variational part
};

// -----------------------------------------------------------------------------

template <typename MapType, typename StepControlType>
inline const MapType& BasicTaylor<MapType, StepControlType>::getField() const {
  return *m_vField;
}

template <typename MapType, typename StepControlType>
inline MapType& BasicTaylor<MapType, StepControlType>::getField() {
  return *m_vField;
}

template <typename MapType, typename StepControlType>
inline int BasicTaylor<MapType, StepControlType>::getOrder() const {
  return m_curve.getOrder();
}

template <typename MapType, typename StepControlType>
inline int BasicTaylor<MapType, StepControlType>::dimension() const {
  return m_curve.dimension();
}

template <typename MapType, typename StepControlType>
inline const typename BasicTaylor<MapType, StepControlType>::ScalarType& BasicTaylor<MapType, StepControlType>::getStep() const {
  return m_step;
}

template <typename MapType, typename StepControlType>
inline void BasicTaylor<MapType, StepControlType>::setStep(const ScalarType& newStep) {
  m_step = newStep;
}

//###########################################################//

template <typename MapType, typename StepControlType>
inline
void BasicTaylor<MapType, StepControlType>::clearCoefficients()
{
  m_curve.clearCoefficients();
}

//###########################################################//

template <typename MapType, typename StepControlType>
inline
const typename BasicTaylor<MapType, StepControlType>::CurveType& BasicTaylor<MapType, StepControlType>::getCurve()
{
  if(m_step>0)
    this->m_curve.setDomain(0.,rightBound(m_step));
  else if(m_step<0)
    this->m_curve.setDomain(leftBound(m_step),0.);
  else // m_step is an interval containing zero or just zero
    this->m_curve.setDomain(leftBound(m_step),rightBound(m_step));
  return m_curve;
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_BASICTAYLOR_H_
/// @}
