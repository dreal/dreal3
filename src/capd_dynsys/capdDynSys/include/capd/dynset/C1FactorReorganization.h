/////////////////////////////////////////////////////////////////////////////
/// @file C1FactorReorganization.h
///
/// @author kapela
/// Created on: Oct 25, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_C1FACTORREORGANIZATION_H_
#define _CAPD_DYNSYS_C1FACTORREORGANIZATION_H_


#include "capd/dynset/FactorPolicy.h"
#include "capd/dynset/FactorReorganization.h"

namespace capd{
namespace dynset{
// @addtogroup capd
/// @{

/**
 *   Factor based reorganization for C1 sets.
 *
 *   Works for C1 doubleton sets.
 *   We assume that C1 part is represented as: X + Cjac*R0 + Bjac*R.
 *
 *   Reorganization of C1 part takes place if size of R  is greater then size of R0 times given C1factor.
 *
 *   Reorganization of C0 part depends on C0ReorganizationT base class.
 *
 *   Previously it was built-in into C1Rect2.
 */
template <typename DoubletonT,
          typename C0ReorganizationT = capd::dynset::FactorReorganization<DoubletonT, capd::dynset::MemberFactorPolicy >,
          typename FactorPolicyT = capd::dynset::MemberFactorPolicy >
class C1FactorReorganization : public C0ReorganizationT {
protected:
  FactorPolicyT C1factor;
public:
  typedef DoubletonT SetType;
  typedef C0ReorganizationT C0Reorganization;
  typedef typename SetType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef FactorPolicyT FactorPolicy;

  C1FactorReorganization(double factor = 1.0, double C1factor=1.0): C0Reorganization(factor), C1factor(C1factor){
  }
  double getC1Factor() const {
    return C1factor.getFactor();
  }
  void setC1Factor(double factor) {
    C1factor.setFactor(factor);
  }
  void reorganizeC1(SetType & result) const{
    int dim = result.get_x().dimension();
    MatrixType B = result.get_B();
    MatrixType C = result.get_C();
    MatrixType BC(dim,dim,false);

    capd::matrixAlgorithms::gauss(B, C, BC);

    result.set_R0(result.get_R() + BC * result.get_R0());
    result.set_Cjac(result.get_Bjac());
    result.set_Bjac(MatrixType::Identity(dim));
    result.set_R(MatrixType(dim,dim));

  }
  bool isC1ReorganizationNeeded(const SetType & result) const {
     return (FactorPolicy::isReorganizationEnabled() &&
         (capd::vectalg::size(result.get_R()) > getC1Factor() * capd::vectalg::size(result.get_R0())));
  }
  bool isC0ReorganizationNeeded(const SetType & result) const {
    return C0Reorganization::isReorganizationNeeded(result);
  }
  bool isReorganizationNeeded(const SetType & result) const {
    return isC1ReorganizationNeeded(result) || isC0ReorganizationNeeded(result);
  }
  /// makes reorganization if needed.
  /// return true if reorganization was performed
  bool reorganizeIfNeeded(SetType & result) const{
    bool reorganizationWasPerformed = false;
    if(isC0ReorganizationNeeded(result)){
      C0Reorganization::reorganize(result);
      reorganizationWasPerformed = true;
    }
    if(isC1ReorganizationNeeded(result)){
          reorganizeC1(result);
          reorganizationWasPerformed = true;
    }
    return reorganizationWasPerformed;
  }
  std::string name() const{
    return "C1 doubleton reorganization with factors";
  }
};

/// @}
}} // capd::dynset
#endif // _CAPD_DYNSYS_C1FACTORREORGANIZATION_H_
