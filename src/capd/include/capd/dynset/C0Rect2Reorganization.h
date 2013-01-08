// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C0Rect2Reorganization.h
///
/// @author kapela
/// Created on: Oct 25, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0RECT2REORGANIZATION_H_
#define _CAPD_DYNSET_C0RECT2REORGANIZATION_H_

#include "capd/dynset/FactorPolicy.h"
namespace capd{
namespace dynset{

/**
 *   Factor based reorganization,
 *   previously it was built-in into Rect2Set
 */

template <typename DoubletonT, typename FactorPolicyT = capd::dynset::MemberFactorPolicy >
class C0Rect2Reorganization : public FactorPolicyT{

public:
  typedef DoubletonT SetType;
  typedef typename SetType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename DoubletonT::C0Rect C0Rect;   // to ensure that we deal with C0Rect2Set;
                                                // and therefore that B is orthonormal
  typedef FactorPolicyT FactorPolicy;

  C0Rect2Reorganization(double factor = 20.0): FactorPolicyT(factor){
  }
  void reorganize(SetType & result) const{
    int dim = result.get_x().dimension();
    result.set_r0(result.get_r() +
          ((Transpose(result.get_B()) * result.get_C()) * result.get_r0())); //valid only for RectSets !!!
    result.set_C(result.get_B());
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
    return "doubleton reorganization (when size(r) > factor * size(r0))";
  }
};

}} // capd::dynset


#endif // _CAPD_DYNSET_C0RECT2REORGANIZATION_H_

/// @}
