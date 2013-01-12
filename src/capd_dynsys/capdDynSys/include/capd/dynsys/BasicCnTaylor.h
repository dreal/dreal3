/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BasicCnTaylor.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2006 */

#ifndef _CAPD_DYNSYS_BASICCNTAYLOR_H_
#define _CAPD_DYNSYS_BASICCNTAYLOR_H_

#include <utility>
#include <algorithm>
#include "capd/dynsys/StepControl.h"
#include "capd/map/C1Coeff.h"


namespace capd{
namespace dynsys{

template<typename CnMapT, typename StepControlT = capd::dynsys::DLastTermsStepControl>
class BasicCnTaylor : public capd::dynsys::StepControlInterface<StepControlT> {
public:
  typedef CnMapT CnMapType;
  typedef CnMapT MapType;
  typedef StepControlT StepControlType;
  typedef typename CnMapT::FunctionType FunctionType;
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

  BasicCnTaylor(CnMapType& a_vectorField, int a_order, const ScalarType& a_step, const StepControlT& stepControl = StepControlT()); // rank will be read form vectorField object
  virtual ~BasicCnTaylor();

  VectorType operator()(const VectorType& v);
  VectorType operator()(const VectorType& v, MatrixType& der);

  /// Computes image of vector v and derivatives of a flow with respect to init condition (v, derivative)
  VectorType operator()(const VectorType & v, const MatrixType & derivative, MatrixType & resultDerivative) ;

  /// Computes value and derivative after one step with initial condition in coeff
  /// The full result is stored in coeff and also value is returned
  VectorType operator()(capd::map::C1Coeff<MatrixType> & coeffs);

  VectorType operator()(CnCoeffType&);

  void setOrder(int newOrder);

// inline definitions
  inline void setStep(const ScalarType& a_step) { m_step = a_step; }
  inline const CnMapType& getField() const { return *m_vectorField; }
  inline CnMapType& getField() { return *m_vectorField; }
  inline int getOrder() const { return m_order; }
  inline int getRank() const { return m_vectorField->getRank(); }
  inline const ScalarType& getStep() const { return m_step; }
  inline int dimension() const { return m_vectorField->dimension(); }

  const SeriesContainerType& computeDaPhi(const CnCoeffType& c, int r);
  ScalarType getCoeffNorm(int i) const;

  /// for nonautonomous ODEs
  void differentiateTime() const {
    m_vectorField->differentiateTime();
  }
  void setCurrentTime(const ScalarType& a_time) const {
    m_vectorField->setCurrentTime(a_time);
  }
  const ScalarType& getCurrentTime() const {
    return m_vectorField->getCurrentTime();
  }

  template <class SetType>
  ScalarType computeNextTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.computeNextTimeStep(*this,x,maxStep);
  }

  template <class SetType>
  ScalarType getFirstTimeStep(const SetType& x, const ScalarType& maxStep) {
    return this->m_stepControl.getFirstTimeStep(*this,x,maxStep);
  }

  void clearCoefficients();

protected:
  CnMapType* m_vectorField;
  ScalarType m_step;
  int m_order;
  SeriesContainerType m_vectorFieldSeries;
  SeriesContainerType m_resultSeries;
  SeriesContainerType m_compositionFormula;
  SeriesContainerType m_nonlinearPart;
  ConsNodeType m_zeroNode;

  typename Multiindex::IndicesSet m_listIndices;

  // this is the main function which computes a composition formula
  void computeCompositionFormula();
  void computeCompositionFormula(const Multipointer&);
  NodeType& computeProduct(const Multiindex&, const Multipointer&, int p, int k);

  void operator=(const BasicCnTaylor&){}
  BasicCnTaylor(const BasicCnTaylor&):  capd::dynsys::StepControlInterface<StepControlT>(this->m_stepControl),
                                        m_vectorFieldSeries(1,1,1),
                                        m_resultSeries(1,1,1),
                                        m_compositionFormula(1,1,1),
                                        m_nonlinearPart(1,1,1),
                                        m_zeroNode(1,ScalarType(0))
                                        {}
  void setInitialCondition(const CnCoeffType& coeff);
  void setInitialCondition(const VectorType& v, const MatrixType& m, const C2CoeffType& hessian);
  void setInitialCondition(const VectorType& v, const MatrixType& m);
  void setInitialCondition(const VectorType& v);
  void computeVectorFieldSeries(const VectorType& v, int rank, int order);
  void computeResultSeries(int rank, int a_order);
  void computeNonlinearPart(int rank);
}; // the end of class BasicCnTaylor


}} // the end of the namespace capd::dynsys

#endif // _CAPD_DYNSYS_BASICCNTAYLOR_H_

/// @}
