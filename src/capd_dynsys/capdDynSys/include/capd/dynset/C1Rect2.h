/////////////////////////////////////////////////////////////////////////////
/// @file C1Rect2.h
/// @deprecated
/// @author kapela
/// Created on: Oct 25, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_C1RECT2_H_
#define _CAPD_C1RECT2_H_

#include "capd/dynset/ReorganizedSet.h"
#include "capd/dynset/C1Rect2Reorganization.h"
#include "capd/dynset/C1Rect2Set.hpp"
namespace capd{
namespace dynset{


/////////////////////////////////////////////////////////////////////
///
///  DEPRECATED! Use C1Rect2RSet instead
///  @deprecated
///
///////////////////////////////////////////////////////////////////////
template <typename MatrixT, typename QRPolicy = FullQRWithPivoting >
class C1Rect2 : public ReorganizedSet<C1Rect2Set<MatrixT,QRPolicy>, C1Rect2Reorganization<C1Rect2Set<MatrixT,QRPolicy> > > {

public :
  typedef  ReorganizedSet<C1Rect2Set<MatrixT,QRPolicy>, C1Rect2Reorganization<C1Rect2Set<MatrixT,QRPolicy> > > BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename BaseSet::NormType NormType;
  typedef typename BaseSet::ReorganizationPolicy ReorganizationPolicy;

  C1Rect2(BaseSet & set) : BaseSet(set){

  }
  C1Rect2(const NormType& norm, int dim): BaseSet(norm, dim){}

  C1Rect2(const VectorType& x, const NormType& norm, double factor = 20) : BaseSet(x, norm){
    BaseSet::setFactor(factor);
    BaseSet::setC1Factor(factor);
  }
  C1Rect2(const VectorType& x, const VectorType& r, const NormType& norm, double factor = 20)
    : BaseSet(x, r, norm){
    BaseSet::setFactor(factor);
    BaseSet::setC1Factor(factor);
  }
  C1Rect2(const VectorType& x, const MatrixType& B, const VectorType& r, const NormType& norm, double factor = 20)
    : BaseSet(x, B, r, norm){
    BaseSet::setFactor(factor);
    BaseSet::setC1Factor(factor);
  }
  void setFactor(double factor){
    BaseSet::setC0Factor(factor);
    BaseSet::setC1Factor(factor);
  }
  std::string name() const { return "C1Rect2"; }
};


}} // namespace capd::dynset

#endif // _CAPD_C1RECT2_H_
