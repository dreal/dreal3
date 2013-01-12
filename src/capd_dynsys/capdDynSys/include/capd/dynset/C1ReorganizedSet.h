
/////////////////////////////////////////////////////////////////////////////
/// @file C1ReorganizedSet.h
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C1REORGANIZEDSET_H_
#define _CAPD_DYNSET_C1REORGANIZEDSET_H_

#include "capd/geomset/DoubletonSet.hpp"
#include "capd/dynset/FactorPolicy.h"
#include "capd/dynset/ReorganizationPolicy.h"

namespace capd{
namespace dynset{
// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////
///
///  Template that joins C1Set with reorganization policy.
///
///  Set representation depends on template parameter SetT.
///  Set is moved with SetT move algorithm
///  and after each move given reorganization is performed if needed
///
///////////////////////////////////////////////////////////////////////
template <typename SetT, typename ReorganizationT = typename ReorganizationPolicy<SetT>::DefaultReorganization >
class C1ReorganizedSet : public SetT, public ReorganizationT {

public :
  typedef SetT BaseSet;

  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename BaseSet::NormType NormType;
  typedef ReorganizationT ReorganizationPolicy;
  typedef typename BaseSet::SetType SetType;
  typedef typename BaseSet::DynSysType DynSysType;
  typedef typename BaseSet::C0BaseSet C0BaseSet;
  typedef typename BaseSet::C1BaseSet C1BaseSet;

  C1ReorganizedSet(const BaseSet & set) : BaseSet(set){
  }

  // C1 constructors
  C1ReorganizedSet(const NormType& norm, int dim): BaseSet(norm, dim){}
  C1ReorganizedSet(const VectorType& x, const NormType& norm) : BaseSet(x, norm) {}
  C1ReorganizedSet(const VectorType& x, const VectorType& r, const NormType& norm) : BaseSet(x, r, norm) {}
  C1ReorganizedSet(const VectorType& x, const MatrixType& B, const VectorType& r, const NormType& norm)
  : BaseSet(x, B, r, norm) {}
  C1ReorganizedSet(const typename BaseSet::C0BaseSet & c0part, const typename BaseSet::C1BaseSet & c1part, const NormType & norm)
  : BaseSet(c0part, c1part, norm) {}

   void move(DynSysType & dynsys){
    move(dynsys, *this);
  }

  void move(DynSysType & dynsys, C1ReorganizedSet & result) const{
    BaseSet::move(dynsys, result);
    result.reorganizeIfNeeded();
  }
  void reorganize(){
    ReorganizationPolicy::reorganize(*this);
  }
  bool isReorganizationNeeded() const{
    return ReorganizationPolicy::isReorganizationNeeded(*this);
  }
  bool reorganizeIfNeeded(){
    return ReorganizationPolicy::reorganizeIfNeeded(*this);
  }
  std::string show() const {
    return BaseSet::name()+" with "+ReorganizationPolicy::name() + "\n" + BaseSet::toString() + "\n" + ReorganizationPolicy::toString();
  }
};

/// @}
}} // namespace capd::dynset

#endif // _CAPD_DYNSET_REORGANIZEDSET_H_
