//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file OdeTraits.h
///
/// @author Tomasz Kapela   @date 2010-03-11
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_ODETRAITS_HPP_
#define _CAPD_DYNSYS_ODETRAITS_HPP_
#include "capd/dynsys/enclosure.hpp"
namespace capd{
namespace dynsys{

/**
 * Defines characteristic traits of ODE
 *
 * This is default class, it should work for all ODE's.
 * For given ODE sometimes it is better to re-implemented it.
 */
template <typename MapT>
class OdeTraits{
public:
  typedef MapT MapType;
  typedef typename MapType::VectorType VectorType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MapType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  /**
   * Computes enclosure of solution of ODE during one time step  i.e \f$ \varphi([0,step],x) \f$
   *
   * @param vectorField vector field
   * @param x0          initial condition
   * @param timeStep    final time
   * @return  enclosure of solution of ODE
   */
  inline static VectorType dynsysEnclosure(MapType & vectorField, const VectorType & x0, const ScalarType & timeStep){
    return capd::dynsys::enclosure(vectorField, x0, timeStep);
  }
  /**
   * Finds enclosure for Jacobian matrix (variational part) for whole time step
   *
   * @param vectorField  vector field
   * @param timeStep     time step
   * @param enclosure    enclosure of solution of ODE during whole time step
   * @param the_norm     logarithmic norm used to bound solution
   * @param[out] logNormOfDerivative if given on exit it contains logarythmic norm of derivative
   * @return matrix containing enclosure of Jacobian
   */
  inline static MatrixType jacobianEnclosure(
      MapType & vectorField, const ScalarType & timeStep,
      const VectorType & enclosure, const NormType & the_norm,
      ScalarType* logNormOfDerivative = 0
  ) {
    return capd::dynsys::jacEnclosure(vectorField, timeStep, enclosure, the_norm, logNormOfDerivative);
  }
};

}} // end of namespace capd::dynsys

#endif // _CAPD_DYNSYS_ODETRAITS_HPP_
