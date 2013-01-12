/////////////////////////////////////////////////////////////////////////////
/// @file CanonicalReorganization.h
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSET_CANONICALREORGANIZATION_H_
#define _CAPD_DYNSET_CANONICALREORGANIZATION_H_


#include "capd/dynset/FactorPolicy.h"

namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

/**
 *   During reorganization we set C and B to Identity and put everything into r0.
 *
 *   Works for doubleton sets, represented as: x + C*r0 + B*r.
 *
 *   Reorganization takes place if size of r  is greater then size of r0 times given factor.
 */
template <typename DoubletonT, typename FactorPolicyT = capd::dynset::MemberFactorPolicy >
class CanonicalReorganization : public FactorPolicyT{

public:
  typedef DoubletonT SetType;
  typedef typename SetType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  //typedef typename ScalarType::BoundType BoundType;
  typedef FactorPolicyT FactorPolicy;

  CanonicalReorganization(double factor = 1.0): FactorPolicyT(factor){
  }
  static void reorganize(SetType & result){
          result.set_r0(result.get_C()*result.get_r0() + result.get_B()*result.get_r());
          int dim = result.get_x().dimension();
          result.set_C(MatrixType::Identity(dim));
          result.set_B(MatrixType::Identity(dim));
          result.set_r(VectorType(dim));  // by default it is filled with zeroes
  }
  bool isReorganizationNeeded(const SetType & result) const {
     return (FactorPolicy::isReorganizationEnabled() &&
         (capd::vectalg::size(result.get_r()) > FactorPolicy::getFactor() * capd::vectalg::size(result.get_r0())));
  }
  /// makes reorganization if needed.
  /// return true if reorganization was performed
  bool reorganizeIfNeeded(SetType & result) const{
    if(isReorganizationNeeded(result)){
      reorganize(result);
      return true;
    }
    return false;
  }
  std::string name() const{
    return "doubleton reorganization which transforms set to canonical coordinates";
  }
};

/// @}
}} // capd::dynset

#endif // _CAPD_DYNSET_CANONICALREORGANIZATION_H_
