// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C0Pped2RSet.h
///
/// @author kapela
/// Created on: Oct 25, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0PPED2RSET_H_
#define _CAPD_DYNSET_C0PPED2RSET_H_

#include "capd/dynset/ReorganizedSet.h"
#include "capd/dynset/FactorReorganization.h"
#include "capd/dynset/C0Pped2Set.hpp"
namespace capd{
namespace dynset{


/////////////////////////////////////////////////////////////////////
///
///  This is C0Pped2Set with built-in default reorganization
///
///////////////////////////////////////////////////////////////////////

template <typename MatrixT>
class C0Pped2RSet : public ReorganizedSet<C0Pped2Set<MatrixT>, FactorReorganization<C0Pped2Set<MatrixT> > > {

public :
  typedef ReorganizedSet<C0Pped2Set<MatrixT>, FactorReorganization<C0Pped2Set<MatrixT> > > BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename BaseSet::VectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename C0Pped2RSet<MatrixT>::NormType NormType;
  typedef typename BaseSet::ReorganizationPolicy ReorganizationPolicy;

  C0Pped2RSet(BaseSet & set) : BaseSet(set){
  }
  explicit C0Pped2RSet(int dim, double factor=1) : BaseSet(dim) {
    setFactor(factor);
  }
  explicit C0Pped2RSet(const VectorType& x, double factor=1) : BaseSet(x) {
    setFactor(factor);
  }
  C0Pped2RSet(const VectorType& x, const VectorType& r0, double factor=1) : BaseSet(x, r0) {
    setFactor(factor);
  }
  C0Pped2RSet(const VectorType& x, const MatrixType& C, const VectorType& r0, double factor=1
  ) : BaseSet(x, C, r0) {
    setFactor(factor);
  }
  C0Pped2RSet(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const VectorType& r, double factor=1
  ) : BaseSet(x, C, r0, r) {
    setFactor(factor);
  }
  C0Pped2RSet(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const MatrixType& B,
      const VectorType& r, double factor=1
  ) : BaseSet(x, C, r0, B, r) {
    setFactor(factor);
  }

  void setFactor(double factor){
    BaseSet::setFactor(factor);
  }
  std::string name() const { return "C0Pped2RSet"; }
};


}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0PPED2RSET_H_

/// @}
