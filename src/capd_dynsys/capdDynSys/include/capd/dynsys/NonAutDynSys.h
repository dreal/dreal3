/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file NonAutDynSys.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2009 */

#ifndef _CAPD_DYNSYS_NONAUTDYNSYS_H_
#define _CAPD_DYNSYS_NONAUTDYNSYS_H_

#include "capd/vectalg/Norm.hpp"
#include "capd/dynsys/CnDynSys.h"
#include "capd/map/CnCoeff.h"

namespace capd{
namespace dynsys{

template<typename BaseDynSys>
class NonAutDynSys : public CnDynSys<typename BaseDynSys::MatrixType>{
public:
  typedef typename BaseDynSys::MapType MapType;
  typedef typename BaseDynSys::FunctionType FunctionType;
  typedef typename BaseDynSys::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::map::C2Coeff<ScalarType> C2CoeffType;
  typedef capd::map::CnCoeff<MatrixType> CnCoeffType;

  NonAutDynSys(BaseDynSys& dynsys)
    : m_dynsys(dynsys)
  {
    m_dynsys.differentiateTime();
  }

// from CnDynSys
  void cnPhi(const VectorType& v, CnCoeffType& c)
  {
    m_dynsys.cnPhi(v,c);
  }

  void cnEnclosure(const VectorType& x, CnCoeffType& result, const NormType& n)
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    m_dynsys.cnEnclosure(x,result,n);
    m_dynsys.setCurrentTime(currentTime);
  }

  void cnRemainder(const VectorType& x, const NormType& n, CnCoeffType& result)
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    m_dynsys.cnRemainder(x,n,result);
    m_dynsys.setCurrentTime(currentTime);
  }

//from C2DynSys
  void c2Phi(const VectorType& x, MatrixType& jac, C2CoeffType& hessian)
  {
    m_dynsys.c2Phi(x,jac,hessian);
  }

  void c2Enclosure(
         const VectorType &W1,
         const MatrixType &W3,
         const NormType &the_norm,
         C2CoeffType& result
    )
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    m_dynsys.c2Enclosure(W1,W3,the_norm,result);
    m_dynsys.setCurrentTime(currentTime);
  }


  void c2Remainder(
         const VectorType& Enclosure,
         const MatrixType& jacEnclosure,
         const C2CoeffType& hessianEnclosure,
         VectorType& Remainder,
         MatrixType& jacRemainder,
         C2CoeffType& hessianRemainder
    )
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    m_dynsys.c2Remainder(Enclosure,jacEnclosure,hessianEnclosure,Remainder,jacRemainder,hessianRemainder);
    m_dynsys.setCurrentTime(currentTime);
  }


//from C1DynSys
  void JacRemainder(
            const VectorType &vecEnclosure,
            const MatrixType &jacEnclosure,
            VectorType &Remainder,
            MatrixType &jacRemainder
      )
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    m_dynsys.JacRemainder(vecEnclosure,jacEnclosure,Remainder,jacRemainder);
    m_dynsys.setCurrentTime(currentTime);
  }

  MatrixType jacEnclosure( const VectorType& enc, const NormType& norm)
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    MatrixType result =  m_dynsys.jacEnclosure(enc,norm);
    m_dynsys.setCurrentTime(currentTime);
    return result;
  }


// from DynSys

  VectorType enclosure(const VectorType& x, int* found)
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    VectorType result = m_dynsys.enclosure(x,found);
    m_dynsys.setCurrentTime(currentTime);
    return result;
  }

  VectorType enclosure(const VectorType& x)
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    VectorType result = m_dynsys.enclosure(x);
    m_dynsys.setCurrentTime(currentTime);
    return result;
  }

  VectorType Phi(const VectorType &iv)
  {
    return m_dynsys.Phi(iv);
  }

  MatrixType JacPhi(const VectorType &iv)
  {
    return m_dynsys.JacPhi(iv);
  }

  VectorType Remainder(const VectorType &iv)
  {
    ScalarType currentTime = m_dynsys.getCurrentTime();
    m_dynsys.setCurrentTime(currentTime + m_dynsys.getStep()*ScalarType(0,1));
    VectorType result = m_dynsys.Remainder(iv);
    m_dynsys.setCurrentTime(currentTime);
    return result;
  }

  void differentiateTime() const
  {
    m_dynsys.differentiateTime();
  }

  void setCurrentTime(const ScalarType& a_time)
  {
    m_dynsys.setCurrentTime(a_time);
  }

  const ScalarType& getCurrentTime() const
  {
    return m_dynsys.getCurrentTime();
  }

  const ScalarType& getStep() const
  {
    return m_dynsys.getStep();
  }

  void setStep(const ScalarType& a_step)
  {
    return m_dynsys.setStep(a_step);
  }

  int getOrder() const
  {
    return m_dynsys.getOrder();
  }

  const MapType& getField() const
  {
    return m_dynsys.getField();
  }

  ScalarType getCoeffNorm(int i) const
  {
    return m_dynsys.getCoeffNorm(i);
  }

  MapType& getField()
  {
    return m_dynsys.getField();
  }

  void setOrder(int newOrder)
  {
    m_dynsys.setOrder(newOrder);
    m_dynsys.differentiateTime();
  }

  bool isStepChangeAllowed() const
  {
    return m_dynsys.isStepChangeAllowed();
  }

  void setStepChangeAllowance(bool onOffStepControl)
  {
    m_dynsys.setStepChangeAllowance(onOffStepControl);
  }
  
  void clearCoefficients()
  {
    m_dynsys.clearCoefficients();
  }
  
  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return m_dynsys.computeNextTimeStep(x,maxStep);
  }

  template <class SetType>
  ScalarType getFirstTimeStep(const SetType& x, const ScalarType& maxStep) {
    return m_dynsys.getFirstTimeStep(x,maxStep);
  }
  void turnOnStepControl() {
    m_dynsys.turnOnStepControl();
  }

  void turnOffStepControl() {
    m_dynsys.turnOffStepControl();
  }  
  
private:
  BaseDynSys& m_dynsys;
};

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_NONAUTDYNSYS_H_

/// @}
