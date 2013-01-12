/////////////////////////////////////////////////////////////////////////////
/// @file ReorganizedSet.h
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_REORGANIZEDSET_H_
#define _CAPD_DYNSET_REORGANIZEDSET_H_

#include "capd/geomset/DoubletonSet.hpp"
#include "capd/dynset/FactorPolicy.h"
#include "capd/dynset/ReorganizationPolicy.h"

namespace capd{
namespace dynset{
// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////
///
///  Set representation depends on template parameter SetT.
///  Set is moved with SetT move algorithm
///  and after each move reorganization is performed if needed
///
///////////////////////////////////////////////////////////////////////
template <typename SetT, typename ReorganizationT = typename ReorganizationPolicy<SetT>::DefaultReorganization >
class ReorganizedSet : public SetT, public ReorganizationT {

public :
  typedef SetT BaseSet;

  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename BaseSet::NormType NormType;
  typedef ReorganizationT ReorganizationPolicy;
  typedef typename BaseSet::SetType SetType;
  typedef typename BaseSet::DynSysType DynSysType;

  ReorganizedSet(const BaseSet & set) : BaseSet(set){
  }

  // C0 constructors
  explicit ReorganizedSet(int dim) : BaseSet(dim) {}
  explicit ReorganizedSet(const VectorType& x) : BaseSet(x) {}
  ReorganizedSet(const VectorType& x, const VectorType& r0) : BaseSet(x, r0) {}
  ReorganizedSet(const VectorType& x, const MatrixType& C, const VectorType& r0
  ) : BaseSet(x, C, r0) {}
  ReorganizedSet(const VectorType& x, const MatrixType& C,
           const VectorType& r0, const VectorType& r
  ) : BaseSet(x, C, r0, r) {}
  ReorganizedSet(const VectorType& x, const MatrixType& C,
           const VectorType& r0, const MatrixType& B,
           const VectorType& r
  ) : BaseSet(x, C, r0, B, r) {}

 // C1 constructors
  ReorganizedSet(const NormType& norm, int dim): BaseSet(norm, dim){}
  ReorganizedSet(const VectorType& x, const NormType& norm) : BaseSet(x, norm) {}
  ReorganizedSet(const VectorType& x, const VectorType& r, const NormType& norm) : BaseSet(x, r, norm) {}
  ReorganizedSet(const VectorType& x, const MatrixType& B, const VectorType& r, const NormType& norm)
  : BaseSet(x, B, r, norm) {}

   void move(DynSysType & dynsys){
    move(dynsys, *this);
  }

  void move(DynSysType & dynsys, ReorganizedSet & result) const{
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
  /*
  /// returns a copy of the set
   virtual SetType * clone(void) const{
     return new ReorganizedSet(*this);
   }
    /// returns a 'fresh' instance of the set
   virtual SetType * fresh(void) const {
     return new ReorganizedSet(BaseSet::dimension());
   }
    /// returns a set that covers given interval vector
   virtual SetType * cover(const VectorType &v) const {
     return new ReorganizedSet(*(BaseSet::cover(v)));
   }*/
};


template <typename DoubletonT, template <typename, typename> class ReorganizationT >
class SimplyReorganized2Set : public ReorganizedSet <DoubletonT, ReorganizationT<DoubletonT, capd::dynset::MemberFactorPolicy> >{
public:
  typedef ReorganizationT<DoubletonT, capd::dynset::MemberFactorPolicy> ReorganizationPolicy;
  typedef ReorganizedSet <DoubletonT, ReorganizationPolicy > BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename BaseSet::NormType NormType;

  SimplyReorganized2Set(BaseSet & set) : BaseSet(set){
  }
};
/// @}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_REORGANIZEDSET_H_
