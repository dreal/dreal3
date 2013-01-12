//////////////////////////////////////////////////////////////////////////////
///
///  @file BasicPoincareMapJet.hpp
///  
///  @author kapela  @date   Apr 5, 2011
//////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2011 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef CAPD_POINCARE_BASICPOINCAREMAPJET_HPP_
#define CAPD_POINCARE_BASICPOINCAREMAPJET_HPP_

#include "capd/poincare/BasicPoincareMapJet.h"
#include "capd/poincare/BasicPoincareMap.hpp"

namespace capd {
namespace poincare {
/// @addtogroup poincare
/// @{

/**
 * The point just after the section on the nonrigorous trajectory is returned
 */
template <typename DS, typename FunT>
typename BasicPoincareMapJet<DS, FunT>::VectorType
BasicPoincareMapJet<DS, FunT>::operator()(VectorType v) {

  SaveStepControl<DS> ssc(this->m_dynamicalSystem);
  VectorType afterSection;
  return this->operator()(v, afterSection);
}


template <typename DS, typename FunT>
typename BasicPoincareMapJet<DS, FunT>::VectorType
BasicPoincareMapJet<DS, FunT>::operator()(VectorType v, VectorType & pointAfterSection) {
  SaveStepControl<DS> ssc(this->m_dynamicalSystem);
  ScalarType lastStep;
  pointAfterSection = this->reachSection(v, 1, &lastStep);
  CurveType c = this->m_dynamicalSystem.getCurve();
  ScalarType t0 = findCrossingTime(c);
  return c(t0);
}

template <typename DS, typename FunT>
typename BasicPoincareMapJet<DS, FunT>::VectorType
BasicPoincareMapJet<DS, FunT>::operator()(VectorType v, MatrixType & dF) {
  SaveStepControl<DS> ssc(this->m_dynamicalSystem);
  capd::map::C1Coeff<MatrixType> coeffs(v, MatrixType::Identity(this->m_dim));
  this->reachSection(coeffs, 1);
  MatrixType der = (MatrixType)coeffs;
  CurveType c = this->m_dynamicalSystem.getCurve();
  ScalarType t0 = findCrossingTime(c);
  MatrixType lastStepDerivative = c[t0];
  dF = lastStepDerivative;
  return c(t0);
}

/// Crosses the section and returns the value of Poincare Map.
template <typename DS, typename FunT>
typename BasicPoincareMapJet<DS, FunT>::ScalarType
BasicPoincareMapJet<DS, FunT>::findCrossingTime(const CurveType & c)
{
  // TODO: maybe we should make one step with section order and the last time step
  // first approximation of crossing time is set to be center of the domain
  ScalarType t0 = (c.getLeftDomain()+c.getRightDomain())/2;
  CurveType der = c.derivative();
  int maxNumberOfRefinement = 15;

  // now we resolve for the return time
  for(int i=0; i<maxNumberOfRefinement; ++i) {
    VectorType v = c(t0);
    ScalarType s_t = this->m_section(v);
//   std::cout << "\n v = " << v << "\n   section: " << s_t;
    if(abs(s_t) < this->m_sectionFactor)
      break;
    ScalarType Ds_t = this->m_section.gradient(v) * der(t0);
    ScalarType N = t0 - s_t/Ds_t;
//   std::cout << "\n N " << N << "\n  Ds : " << Ds_t;

    // we know that zero is in the domain
    if(N < c.getLeftDomain())
      N = c.getLeftDomain();
    if(N > c.getRightDomain())
      N = c.getLeftDomain();
    t0 = N;
  }
  return t0;
}

/// @} 
}} // end of namespace capd::poincare

#endif /* CAPD_POINCARE_BASICPOINCAREMAPJET_HPP_ */
