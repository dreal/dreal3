// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file QRReorganization.h
///
/// @author kapela
/// Created on: Oct 23, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_QRREORGANIZATION_H_
#define _CAPD_QRREORGANIZATION_H_

#include "capd/dynset/FactorPolicy.h"

namespace capd{
namespace dynset{

/**
 *   During reorganization we set C and B to Identity and put everything into r0
 */

template <typename DoubletonT, typename FactorPolicyT = capd::dynset::MemberFactorPolicy >
class QRReorganization : public FactorPolicyT{

public:
  typedef DoubletonT SetType;
  typedef typename SetType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
 // typedef typename ScalarType::BoundType BoundType;
  typedef FactorPolicyT FactorPolicy;

  QRReorganization(double factor = 1.0): FactorPolicyT(factor){
  }
  static void reorganize(SetType & result){
          MatrixType Q = result.get_B();
          capd::matrixAlgorithms::orthonormalize(Q, result.get_r());
          result.set_r((Transpose(Q)*result.get_B())*result.get_r());
          result.set_B(Q);
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
    return "QR reorganization (it replaces B with Q where B=QR)";
  }
};

}} // capd::dynset



#endif // _CAPD_QRREORGANIZATION_H_

/// @}
