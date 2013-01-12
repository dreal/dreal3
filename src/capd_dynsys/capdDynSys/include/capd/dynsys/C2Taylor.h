/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2Taylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2003-2005 */

#ifndef _CAPD_DYNSYS_C2TAYLOR_H_
#define _CAPD_DYNSYS_C2TAYLOR_H_

#include <string>
#include <vector>
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/Taylor.h"
#include "capd/dynsys/C2DynSys.h"
#include "capd/dynsys/BasicC2Taylor.h"

namespace capd{
namespace dynsys{

template<typename MapT, typename StepControlT = capd::dynsys::IEncFoundStepControl>
class C2Taylor : public Taylor<MapT,StepControlT>, public BasicC2Taylor<MapT,StepControlT>, public C2DynSys<typename MapT::MatrixType>{
public:
  typedef MapT MapType;
  typedef StepControlT StepControlType;
  typedef typename MapT::FunctionType FunctionType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef typename MapType::C2CoeffType C2CoeffType;

  C2Taylor(MapType& vectorField, int order, const ScalarType& step);

  void c2Phi(const VectorType& x, MatrixType& jac, C2CoeffType& hessian);
  void c2Enclosure(
         const VectorType& W1,
         const MatrixType& W3,
         const NormType& the_norm,
         C2CoeffType& result
  ) ;
  void c2Remainder(
         const VectorType& Enclosure,
         const MatrixType& jacEnclosure,
         const C2CoeffType& hessianEnclosure,
         VectorType& Remainder,
         MatrixType& jacRemainder,
         C2CoeffType& hessianRemainder // here the result is stored
  );

  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.computeNextTimeStep(*this,x,maxStep);
  }

  template <class SetType>
  ScalarType getFirstTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.getFirstTimeStep(*this,x,maxStep);
  }
  
  using BasicC2Taylor<MapType,StepControlT>::setOrder;

  using Taylor<MapType,StepControlT>::Phi;
  using Taylor<MapType,StepControlT>::JacPhi;
  using Taylor<MapType,StepControlT>::Remainder;
  using Taylor<MapType,StepControlT>::JacRemainder;
  using Taylor<MapType,StepControlT>::enclosure;
  using Taylor<MapType,StepControlT>::jacEnclosure;

  using Taylor<MapType,StepControlT>::getField;
  using Taylor<MapType,StepControlT>::getOrder;
  using Taylor<MapType,StepControlT>::getStep;
  using Taylor<MapType,StepControlT>::setStep;
  using Taylor<MapType,StepControlT>::dimension;

  void differentiateTime() const
  {
    Taylor<MapType,StepControlT>::differentiateTime();
  }
  void setCurrentTime(const ScalarType& a_time) const
  {
    Taylor<MapType,StepControlT>::setCurrentTime(a_time);
  }

  const ScalarType& getCurrentTime(const ScalarType& a_time) const
  {
    return Taylor<MapType,StepControlT>::getCurrentTime();
  }

protected:
  void operator=(const C2Taylor& ) {}
  C2Taylor(const C2Taylor& t) : BasicTaylor<MapT,StepControlT>(t), Taylor<MapT,StepControlT>(t), BasicC2Taylor<MapT,StepControlT>(t) {}

  using Taylor<MapType,StepControlT>::computeMatrixCoeff;
  using Taylor<MapType,StepControlT>::m_step;
  using Taylor<MapType,StepControlT>::m_vField;
  using Taylor<MapType,StepControlT>::m_F;

  using BasicC2Taylor<MapType,StepControlT>::m_c2MatrixCoeff;
  using BasicC2Taylor<MapType,StepControlT>::computeC2Coeff;
}; // the end of class C2Taylor

}} // the end of the namespace capd::dynsys

#endif // _CAPD_DYNSYS_C2TAYLOR_H_

/// @}
