/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FadTaylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_FADTAYLOR_H_
#define _CAPD_DYNSYS_FADTAYLOR_H_

#include "capd/vectalg/Norm.hpp"
#include "capd/dynsys/BasicFadTaylor.h"
#include "capd/dynsys/C1DynSys.h"
#include "capd/dynsys/enclosure.hpp"
#include "capd/dynsys/DynSys.hpp"
#include "capd/basicalg/power.h"

namespace capd{
namespace dynsys{

template<class FadMapT, typename StepControlT = capd::dynsys::NoStepControl>
class FadTaylor : public capd::dynsys::C1DynSys<typename FadMapT::MatrixType>, public BasicFadTaylor<FadMapT,StepControlT>{
public:
  typedef FadMapT MapType;
  typedef StepControlT StepControlType;
  typedef typename FadMapT::ScalarType ScalarType;
  typedef typename FadMapT::FScalar FScalar;
  typedef typename FadMapT::TFScalar TFScalar;
  typedef typename FadMapT::MatrixType MatrixType;
  typedef typename FadMapT::VectorType VectorType;
  typedef typename FadMapT::FVector FVector;
  typedef typename FadMapT::TFVector TFVector;
  typedef typename MapType::FunctionType FunctionType;

  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef BasicFadTaylor<FadMapT,StepControlT> BasicFadTaylorType;

  FadTaylor(MapType& f, int _order, ScalarType _step, const StepControlT& _stepControl=StepControlT())
  : BasicFadTaylorType(f,_order,_step,_stepControl)
  {}

// DynSys and C1DynSys interface implementation
  /// it computes image of the set (in give representation) using set.move function
  template <typename SetType>
  void operator()(SetType & set){
    set.move(*this);
  }

  using BasicFadTaylorType::operator();

  VectorType Phi(const VectorType& v){       ///< Computes image of vector v after one time step
    return BasicFadTaylorType::operator()(v);
  }

  MatrixType JacPhi(const VectorType& v){    ///< Computes derivatives with respect to initial conditions
    MatrixType der(v.dimension(),v.dimension());
    BasicFadTaylorType::operator()(v,der);
    return der;
  }

  VectorType Remainder(const VectorType& v){  ///< Computes bound for remainder term in Taylor series
    BasicFadTaylorType::operator()(enclosure(v),this->m_order+1);
    VectorType result(v.dimension());
    ScalarType fac = power(this->m_step,this->m_order+1);
    for(int i=0;i<v.dimension();++i)
      result[i] = fac*this->m_in[i][this->m_order+1].x();
    return result;
  }

  void JacRemainder(                               ///< Computes bounds for remainder term for Taylor series of derivative
          const VectorType &vecEnclosure,
          const MatrixType &jacEnclosure,
          VectorType &Remainder,
          MatrixType &jRemainder
  ){
    MatrixType der(vecEnclosure.dimension(),vecEnclosure.dimension());
    BasicFadTaylorType::operator()(vecEnclosure,jRemainder,this->m_order+1,jacEnclosure);
    ScalarType fac = power(this->m_step,this->m_order+1);
    for(int i=0;i<vecEnclosure.dimension();++i)
    {
      Remainder[i] = fac*this->m_in[i][this->m_order+1].x();
      for(int j=0;j<vecEnclosure.dimension();++j)
        jRemainder(i+1,j+1) = fac*this->m_in[i][this->m_order+1].d(j);
    }
  }

  VectorType enclosure(const VectorType& x, int* found){ ///< the function finds an enclosure for \varphi([0,step],x)
    return capd::dynsys::enclosure(this->m_vectorField, x, this->m_step);
  }

  VectorType enclosure(const VectorType &x) {             ///< the function finds an enclosure for \varphi([0,step],x)
    return capd::dynsys::enclosure(this->m_vectorField, x, this->m_step);
  }

  MatrixType jacEnclosure(const VectorType& enc, const NormType& norm){ ///< the function finds enclosure for Jacobian matrix (variational part)
    return capd::dynsys::jacEnclosure(this->m_vectorField,this->m_step,enc,norm);
  }
// end of Dynsys and C1DynSys members
  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.computeNextTimeStep(*this,x,maxStep);
  }

  template <class SetType>
  ScalarType getFirstTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.getFirstTimeStep(*this,x,maxStep);
  }
  using BasicFadTaylorType::getOrder;
  using BasicFadTaylorType::setOrder;

  using BasicFadTaylorType::getStep;
  using BasicFadTaylorType::setStep;

}; // the end of class FadTaylor


}} // the end of the namespace capd::dynsys

#endif // _CAPD_DYNSYS_FADTAYLOR_H_

/// @}
