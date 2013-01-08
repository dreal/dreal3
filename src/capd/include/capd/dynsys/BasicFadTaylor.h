/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicFadTaylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_BASICFADTAYLOR_H_
#define _CAPD_DYNSYS_BASICFADTAYLOR_H_

#include "capd/fadbad/fadiff.h"
#include "capd/fadbad/differentiate.h"
#include "capd/capd/power.h"
#include "capd/dynsys/StepControl.h"
#include "capd/map/C1Coeff.h"



namespace capd{
namespace dynsys{

// a type FadMapT should specify interface defined in class FadMap - see header file
template<class FadMapT, typename StepControlT = capd::dynsys::NoStepControl>
class BasicFadTaylor : public capd::dynsys::StepControlInterface<StepControlT>
{
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


  BasicFadTaylor(MapType& f, int _order, ScalarType _step, const StepControlT& stepControl=StepControlT())
  : capd::dynsys::StepControlInterface<StepControlT>(stepControl),
    m_vectorField(f), m_order(_order), m_step(_step),
    m_in(f.dimension())
  {
    m_out = f(m_in); // recording DAG
  }
  virtual ~BasicFadTaylor() {}

  VectorType operator()(const VectorType& u) const
  {
    return (*this)(u,m_order);
  }

  VectorType operator()(VectorType u,int order) const
  {
    FVector v = setInitialCondition(u);
    computeValue(order);
    sumTaylorSeries(v,order);
    for(int i=0;i<u.dimension();++i)
      u[i] = v[i].x();
    return u;
  }

  VectorType operator()(const VectorType & u, MatrixType& der) const
  {
    return (*this)(u,der,m_order,MatrixType::Identity(u.dimension()));
  }

  /// Computes value and derivative after one step with initial condition in coeff
  /// The full result is stored in coeff and also value is returned
  VectorType operator()(capd::map::C1Coeff<MatrixType> & coeffs){
    coeffs = (*this)((VectorType)coeffs, coeffs.refDerivative(), m_order, coeffs.getDerivative());
  }


  VectorType operator()(VectorType u, MatrixType &der,int order, const MatrixType& initialCondition) const
  {
    FVector v = setInitialCondition(u,initialCondition);
    computeValue(order);
    sumTaylorSeries(v,order);
    for(int i=0;i<u.dimension();++i)
    {
      u[i] = v[i].x();
      for(int j=0;j<u.dimension();++j)
        der(i+1,j+1) = v[i].d(j);
    }
    return u;
  }

  template <typename Description>
  void setParameter(Description name, const ScalarType& value){
    m_vectorField.setParameter(name,value);
    m_out = m_vectorField(m_in); // recording again DAG
  }

  virtual void setOrder(int a_order) {
    m_order = a_order;
  }

  virtual int getOrder() const{
    return m_order;
  }

  virtual void setStep(ScalarType a_step) {
    m_step = a_step;
  }

  virtual const ScalarType & getStep() const{
    return m_step;
  }

  int dimension() const{
    return m_vectorField.dimension();
  }

  MapType& getField(){
    return m_vectorField;
  }


  ScalarType getCoeffNorm(int i) const
  {
    ScalarType result(0);
    for(int j=0;j < dimension();++j)
    {
      result += power(m_in[j][i].x(),2);
    }
    return sqrt(result);
  }

  //###########################################################//

  void clearCoefficients()
  {
    int D = m_in.dimension();
    for(int i=0;i<D;++i)
    {
      for(int r = 0; r <= this->m_order+1; ++r)
      {
        m_in[i][r] = ScalarType(0);
      }
    }
  }

  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.computeNextTimeStep(*this,x,maxStep);
  }

  ScalarType getFirstTimeStep(const ScalarType& maxStep) {
    return this->m_stepControl.getFirstTimeStep(*this,maxStep);
  }

protected:
  FVector setInitialCondition(const VectorType& u) const
  {
    reset();
    int D = u.dimension();
    FVector v(D);
    int i;
    for(i=0;i<D;++i)
    {
      v[i] = u[i];
      m_in[i][0] = v[i];
    }
    return v;
  }

  FVector setInitialCondition(const VectorType& u, const MatrixType& initialCondition) const
  {
    reset();
    int D = u.dimension();
    FVector v(D);
    int i,j;
    for(i=0;i<D;++i)
      v[i] = u[i];
    for(i=0;i<u.dimension();++i)
    {
      differentiate(v[i],i,u.dimension());
      for(j=0;j<u.dimension();++j)
      {
        v[i].d(j) = initialCondition(i+1,j+1);
      }
    }
    for(i=0;i<u.dimension();++i)
      m_in[i][0] = v[i];
    return v;
  }

  void computeValue(int order) const
  {
    int i,j;

    for(i=0 ;i<order;++i)
    {
      eval(i);
      for(j=0;j<m_in.dimension();++j)
      {
        m_in[j][i+1] = m_out[j][i]/(i+1);
      }
    }
  }

  void sumTaylorSeries(FVector& u, int order) const
  {
    int i,j;
    for(j=0;j<u.dimension();++j)
    {
      u[j] = m_in[j][order];
      for(i=order;i>0;--i)
        u[j] = u[j]*m_step + m_in[j][i-1];
    }
  }

  void reset() const
  {
    for(int j=0;j<m_out.dimension();++j)
      m_out[j].reset();
  }

  void eval(int i) const
  {
    for(int j=0;j<m_out.dimension();++j)
      m_out[j].eval(i);
  }

  MapType& m_vectorField;
  int m_order;
  ScalarType m_step;
  mutable TFVector m_in, m_out;
}; // the end of class FadTaylor


}} // the end of the namespace capd::dynsys

#endif // _CAPD_DYNSYS_BASICFADTAYLOR_H_

/// @}
