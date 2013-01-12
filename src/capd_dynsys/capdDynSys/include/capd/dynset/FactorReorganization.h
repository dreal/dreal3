
/////////////////////////////////////////////////////////////////////////////
/// @file FactorReorganization.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_FACTORREORGANIZATION_H_
#define _CAPD_DYNSET_FACTORREORGANIZATION_H_

#include "capd/dynset/FactorPolicy.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"
namespace capd{
namespace dynset{

/**
 *   Factor based reorganization,
 *   previously it was built-in into Rect2Set
 */

template <typename DoubletonT, typename FactorPolicyT = capd::dynset::MemberFactorPolicy >
class FactorReorganization : public FactorPolicyT{

public:
  typedef DoubletonT SetType;
  typedef typename SetType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
 // typedef typename ScalarType::BoundType BoundType;
  typedef FactorPolicyT FactorPolicy;

  FactorReorganization(double factor = 1.0): FactorPolicyT(factor){
  }
  void reorganize(SetType & result) const{
    int dim = result.get_x().dimension();
    MatrixType B = result.get_B();
    MatrixType C = result.get_C();
    MatrixType BC(dim,dim,false);

    capd::matrixAlgorithms::gauss(B, C, BC);

    result.set_r0(result.get_r() +
        //  ((Transpose(result.get_B()) * result.get_C()) * result.get_r0())); valid only for RectSets !!!
        (BC * result.get_r0()));
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

#endif /* FACTORREORGANIZE_H_ */
