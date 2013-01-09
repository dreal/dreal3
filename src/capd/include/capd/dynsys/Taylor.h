/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Taylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2001-2005 */

#ifndef _CAPD_DYNSYS_TAYLOR_H_
#define _CAPD_DYNSYS_TAYLOR_H_

#include <string>
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/C1DynSys.h"
#include "capd/dynsys/BasicTaylor.h"
#include "capd/dynsys/StepControl.h"

namespace capd{
namespace dynsys{

template<typename MapT, typename StepControlT = capd::dynsys::IEncFoundStepControl>
class Taylor: public virtual C1DynSys<typename MapT::MatrixType>, public virtual BasicTaylor<MapT,StepControlT>
{
public:
  typedef MapT MapType;
  typedef StepControlT StepControlType;
  typedef typename MapT::FunctionType FunctionType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  Taylor(MapType& vField, int order, const ScalarType& step, const StepControlT& stepControl = StepControlT());

  VectorType Phi(const VectorType& iv);
  MatrixType JacPhi(const VectorType& iv);
  VectorType Remainder(const VectorType& iv);

  /// it computes image of the set (in give representation) using set.move function
  template <typename SetType>
  void operator()(SetType & set){
    set.move(*this);
  }

  using BasicTaylor<MapT,StepControlT>::operator();
  VectorType operator()(VectorType & v){
    return BasicTaylor<MapT,StepControlT>::operator()(v);
  }

  void JacRemainder(
         const VectorType &vecEnclosure,
         const MatrixType &jacEnclosure,
         VectorType &Remainder,
         MatrixType &jRemainder
      ) ;

  VectorType enclosure(const VectorType& x, int* found) ;
  VectorType enclosure(const VectorType &x) ;
  MatrixType jacEnclosure(const VectorType& enc, const NormType& norm) ;

  using BasicTaylor<MapType,StepControlT>::getField;
  using BasicTaylor<MapType,StepControlT>::getOrder;
  using BasicTaylor<MapType,StepControlT>::getStep;

  using BasicTaylor<MapType,StepControlT>::setStep;
  using BasicTaylor<MapType,StepControlT>::setOrder;

  using BasicTaylor<MapType,StepControlT>::dimension;

  
  void differentiateTime() const
  {
    BasicTaylor<MapType,StepControlT>::differentiateTime();
  }

  const ScalarType& getCurrentTime() const
  {
    return BasicTaylor<MapType,StepControlT>::getCurrentTime();
  }

  void setCurrentTime(const ScalarType& a_time) const
  {
    BasicTaylor<MapType,StepControlT>::setCurrentTime(a_time);
  }

  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.computeNextTimeStep(*this,x,maxStep);
  }

  template <class SetType>
  ScalarType getFirstTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.getFirstTimeStep(*this,x,maxStep);
  }
  
protected:
  void operator=(const Taylor& ){}
  Taylor(const Taylor& t) : BasicTaylor<MapType,StepControlT>(t){}

  using BasicTaylor<MapType,StepControlT>::computeMatrixCoeff;
  using BasicTaylor<MapType,StepControlT>::m_vField;
  using BasicTaylor<MapType,StepControlT>::m_step;
  using BasicTaylor<MapType,StepControlT>::m_F;

};


// --------------- inline definitions -----------------

//###########################################################//

template<typename MapType, typename StepControlType>
inline typename Taylor<MapType,StepControlType>::VectorType Taylor<MapType,StepControlType>::Phi(const VectorType& iv)
{
  return BasicTaylor<MapType,StepControlType>::operator()(iv);
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_TAYLOR_H_

/// @}
