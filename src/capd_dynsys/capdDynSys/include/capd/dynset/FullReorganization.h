/////////////////////////////////////////////////////////////////////////////
/// @file FullReorganization.h
///
/// @author kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSYS_FULLREORGANIZATION_H_
#define _CAPD_DYNSYS_FULLREORGANIZATION_H_

#include "capd/dynset/FactorPolicy.h"

namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

/**
 *   Reorganization is performed if r is bigger than r0 but in coordinate system of r.
 *
 *   Works for doubleton sets, represented as: x + C*r0 + B*r, where B is orthonormal.
 *
 *   Reorganization takes place if size of r  is greater then size of B^T*C*r0 times given factor.
 *
 */
template <typename DoubletonT, typename FactorPolicyT = capd::dynset::MemberFactorPolicy >
class FullReorganization: public FactorPolicyT{

public:
  typedef DoubletonT SetType;
  typedef typename SetType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename ScalarType::BoundType BoundType;
  typedef FactorPolicyT FactorPolicy;

  FullReorganization(double factor=1.0): FactorPolicy(factor){}

  void reorganize(SetType & result) const{
    result.set_r0(result.get_r() +
        ((Transpose(result.get_B()) * result.get_C()) * result.get_r0()));
    result.set_C(result.get_B());
    int dim = result.get_x().dimension();
    result.set_B(MatrixType::Identity(dim));
    result.set_r(VectorType(dim));  // by default it is filled with zeroes
  }

  bool isReorganizationNeeded(const SetType & result) const{
    return (FactorPolicy::isReorganizationEnabled() &&
        (capd::vectalg::size(result.get_r()) > FactorPolicy::getFactor() * capd::vectalg::size(Transpose(result.get_B()) *( result.get_C()*result.get_r0()) )));
  }
  void reorganizeIfNeeded(SetType & result) const{
    if(isReorganizationNeeded(result)){
      reorganize(result);
    }
  }
  std::string name() const{
      return "doubleton reorganization (when size(r) > factor * B^-1 * C *size(r0))";
  }
};

/// @}
}} // end of capd::dynset

#endif /* _CAPD_FULLREORGANIZATION_H_ */
