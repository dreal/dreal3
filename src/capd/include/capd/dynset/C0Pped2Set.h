/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C0Pped2Set.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0PPED2SET_H_
#define _CAPD_DYNSET_C0PPED2SET_H_

#include "capd/dynset/C0Set.h"
#include "capd/geomset/CenteredDoubletonSet.h"
#include "capd/dynset/ReorganizationPolicy.h"
#include "capd/dynset/QRReorganization.h"



namespace capd{
namespace dynset{

/**
 * C0Pped2Set: x + C*r0 + B*r
 * where:
 * -  x - set center
 * -  C*r0 - 'Lipschitz' part
 * -  B*r  - 'errors' computed via parallelograms method
 */
template<typename MatrixT>
class C0Pped2Set : public C0Set<MatrixT>, public capd::geomset::CenteredDoubletonSet<MatrixT>{

public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::geomset::CenteredDoubletonSet<MatrixT> BaseSet;
  typedef typename C0Set<MatrixT>::SetType SetType;
  typedef typename C0Set<MatrixT>::DynSysType DynSysType;

  explicit C0Pped2Set(int dim) : BaseSet(dim) {}
  explicit C0Pped2Set(const VectorType& x) : BaseSet(x) {}
  C0Pped2Set(const VectorType& x, const VectorType& r0) : BaseSet(x, r0) {}
  C0Pped2Set(const VectorType& x, const MatrixType& C, const VectorType& r0
  ) : BaseSet(x, C, r0) {}
  C0Pped2Set(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const VectorType& r
  ) : BaseSet(x, C, r0, r) {}
  C0Pped2Set(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const MatrixType& B,
      const VectorType& r
  ) : BaseSet(x, C, r0, B, r) {}


  // C0Set interface implementation {

  void move(DynSysType & dynsys);
  void move(DynSysType & dynsys, C0Pped2Set& result) const;

  /// returns a set in the canonical frame
  operator VectorType() const{
    return BaseSet::operator VectorType();
  }

  /// returns a set detailed information
  std::string show() const;

  // }  end of C0Set interface

protected:
  using BaseSet::m_x;
  using BaseSet::m_r;
  using BaseSet::m_r0;
  using BaseSet::m_B;
  using BaseSet::m_C;
};

template <typename MatrixType>
class ReorganizationPolicy<C0Pped2Set<MatrixType> > {
public:
  typedef QRReorganization<C0Pped2Set<MatrixType> > DefaultReorganization;
};

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0PPED2SET_H_

/// @}
