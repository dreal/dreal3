/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnTaylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2006 */

#ifndef _CAPD_DYNSYS_CNTAYLOR_H_
#define _CAPD_DYNSYS_CNTAYLOR_H_

#include <string>
#include <vector>
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/C2Taylor.h"
#include "capd/dynsys/CnDynSys.h"
#include "capd/dynsys/BasicCnTaylor.h"

namespace capd{
namespace dynsys{

template<typename MapT, typename StepControlT = capd::dynsys::IEncFoundStepControl>
class CnTaylor : public BasicCnTaylor<MapT,StepControlT>, public CnDynSys<typename MapT::MatrixType>{
public:
  typedef MapT MapType;
  typedef MapT CnMapType;
  typedef StepControlT StepControlType;
  typedef typename MapType::FunctionType FunctionType;
  typedef typename CnMapType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename CnMapType::C2CoeffType C2CoeffType;
  typedef typename CnMapType::CnCoeffType CnCoeffType;
  typedef typename CnMapType::NodeType NodeType;
  typedef typename CnMapType::ConsNodeType ConsNodeType;
  typedef typename CnMapType::SeriesContainerType SeriesContainerType;
  typedef typename SeriesContainerType::Multipointer Multipointer;
  typedef typename SeriesContainerType::Multiindex Multiindex;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef BasicCnTaylor<MapT,StepControlT> BasicCnTaylorType;

  CnTaylor(MapType& vectorField, int order, const ScalarType& step, const StepControlT& stepControl=StepControlT());

// enclosure
  VectorType enclosure(const VectorType& x, int* found) ;
  VectorType enclosure(const VectorType& x) ;
  MatrixType jacEnclosure(const VectorType& enc, const NormType& norm) ;
  void c2Enclosure(
         const VectorType& W1,
         const MatrixType& W3,
         const NormType& the_norm,
         C2CoeffType& result
  ) ;
  void cnEnclosure(const VectorType& x, CnCoeffType& result, const NormType& the_norm) ;
  VectorType cnEnclosure(const VectorType& x, const NormType& the_norm, int rank) ;

// Phi
  VectorType Phi(const VectorType &iv) ;
  MatrixType JacPhi(const VectorType &iv) ;
  void c2Phi(const VectorType& x, MatrixType& jac, C2CoeffType& hessian) ;
  void cnPhi(const VectorType&x, CnCoeffType& result) ;

    using BasicCnTaylorType::operator ();
/// general function to move set with dynamical system
  template <typename SetType>
  void operator()(SetType & set){
    set.move(*this);
  }
// remainder
  VectorType Remainder(const VectorType &iv) ;
  void JacRemainder(
            const VectorType &vecEnclosure,
            const MatrixType &jacEnclosure,
            VectorType &Remainder,
            MatrixType &jRemainder
    ) ;
  void c2Remainder(
         const VectorType& Enclosure,
         const MatrixType& jacEnclosure,
         const C2CoeffType& hessianEnclosure,
         VectorType& Remainder,
         MatrixType& jacRemainder,
         C2CoeffType& hessianRemainder // here a result is stored
    ) ;
  void cnRemainder(const VectorType& x, const NormType&, CnCoeffType& result) ;

  void differentiateTime() const
  {
    BasicCnTaylorType::differentiateTime();
  }
  void setCurrentTime(const ScalarType& a_time)
  {
    BasicCnTaylorType::setCurrentTime(a_time);
  }
  const ScalarType& getCurrentTime() const
  {
    return BasicCnTaylorType::getCurrentTime();
  }

  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.computeNextTimeStep(*this,x,maxStep);
  }

  template <class SetType>
  ScalarType getFirstTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.getFirstTimeStep(*this,x,maxStep);
  }
  
  using DynSys<MatrixType>::Lipschitz;
  using DynSys<MatrixType>::type;
  using BasicCnTaylorType::dimension;
  using BasicCnTaylorType::getRank;

protected:
  void operator=(const CnTaylor&){}
  CnTaylor(const CnTaylor& t) : BasicCnTaylorType(t){}

  using BasicCnTaylorType::computeNonlinearPart;
  using BasicCnTaylorType::m_order;
  using BasicCnTaylorType::m_step;
  using BasicCnTaylorType::m_vectorField;
  using BasicCnTaylorType::m_vectorFieldSeries;
  using BasicCnTaylorType::m_resultSeries;
  using BasicCnTaylorType::m_compositionFormula;
  using BasicCnTaylorType::m_nonlinearPart;
  using BasicCnTaylorType::computeVectorFieldSeries;
  using BasicCnTaylorType::computeResultSeries;

  ScalarType computeDelta(const Multipointer&) ;
}; // the end of class CnTaylor

// ---------------------------- CONSTRUCTORS ---------------------------------------------

template<typename CnMapT, typename StepControlType>
inline CnTaylor<CnMapT,StepControlType>::CnTaylor(CnMapT& a_vectorField, int a_order, const ScalarType& a_step, const StepControlType& stepControl)
  : BasicCnTaylorType(a_vectorField,a_order,a_step,stepControl)
{}


template<typename CnMapT, typename StepControlType>
inline typename CnTaylor<CnMapT,StepControlType>::VectorType CnTaylor<CnMapT,StepControlType>::enclosure(const VectorType &x, int *found)
// the function finds an enclosure for \varphi([0,step],x)
{
  return enclosure(x);
}

}} // the end of the namespace capd::dynsys

#endif // _CAPD_DYNSYS_CNTAYLOR_H_

/// @}
