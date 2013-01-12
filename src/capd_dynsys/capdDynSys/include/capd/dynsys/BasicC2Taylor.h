/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicC2Taylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2003-2005 */

#ifndef _CAPD_DYNSYS_BASICC2TAYLOR_H_
#define _CAPD_DYNSYS_BASICC2TAYLOR_H_

#include <string>
#include "capd/dynsys/BasicTaylor.h"

namespace capd{
namespace dynsys{

template<typename MapT, typename StepControlT = capd::dynsys::DLastTermsStepControl>
class BasicC2Taylor : public virtual BasicTaylor<MapT, StepControlT>{
public:
  typedef MapT MapType;
  typedef StepControlT StepControlType;
  typedef typename MapT::FunctionType FunctionType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef typename MapType::C2CoeffType C2CoeffType;

  BasicC2Taylor(MapType& vectorField, int order, const ScalarType& step);
  ~BasicC2Taylor();

  VectorType operator()(const VectorType&, MatrixType&, C2CoeffType&);

  // If someone knows how to use 'using BasicTaylor<MapType>::operator()' in the borland compiler?:(
  VectorType operator()(const VectorType& v){
    return BasicTaylor<MapType,StepControlT>::operator()(v);
  }
  VectorType operator()(const VectorType& v, MatrixType& der) {
    return BasicTaylor<MapType,StepControlT>::operator()(v,der);
  }
  void setOrder(int newOrder);

  using BasicTaylor<MapType, StepControlT>::setStep;

  using BasicTaylor<MapType, StepControlT>::getField;
  using BasicTaylor<MapType, StepControlT>::getOrder;
  using BasicTaylor<MapType, StepControlT>::getStep;
  using BasicTaylor<MapType, StepControlT>::dimension;
  using BasicTaylor<MapType, StepControlT>::differentiateTime;
  using BasicTaylor<MapType, StepControlT>::setCurrentTime;
  using BasicTaylor<MapType, StepControlT>::getCurrentTime;

protected:
  BasicC2Taylor(const BasicC2Taylor &t) : BasicTaylor<MapT, StepControlT>(t){}
  void operator=(const BasicC2Taylor&){}

  using BasicTaylor<MapType, StepControlT>::m_vField;
  using BasicTaylor<MapType, StepControlT>::m_step;
  using BasicTaylor<MapType, StepControlT>::m_F;
  using BasicTaylor<MapType, StepControlT>::m_curve;
  C2CoeffType* m_c2MatrixCoeff;
  void computeC2Coeff(const VectorType& x, const MatrixType& V, const C2CoeffType& H, VectorType* coeff, MatrixType* matrixCoeff, int order);
}; // the end of class BasicC2Taylor


// ------------------ inline definitions -------------

template <typename MapType, typename StepControlT>
inline BasicC2Taylor<MapType,StepControlT>::~BasicC2Taylor()
{
  delete [] m_c2MatrixCoeff;
}

}} // the end of the namespace capd::dynsys

#endif // _CAPD_DYNSYS_BASICC2TAYLOR_H_

/// @}
