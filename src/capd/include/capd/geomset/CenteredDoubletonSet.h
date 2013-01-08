
/////////////////////////////////////////////////////////////////////////////
/// @file CenteredDoubletonSet.h
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_GEOMSET_CENTEREDDOUBLETONSET_H_
#define _CAPD_GEOMSET_CENTEREDDOUBLETONSET_H_

#include "capd/geomset/DoubletonSet.h"


namespace capd{
namespace geomset{

/**
 * Doubleton representation of the form x0 + C*r0 + B*r which checks if r0 and r contain 0.
 *
 * We define sets representation of the form
 *
 * x + C*r0 + B * r
 *
 * where
 * - the vector x is a center,
 * - the matrices C and B are coordinate systems,
 * - the vector r0 is a product of intervals and represents the set in a given coordinate system,
 * - the vector r is used mainly to store computational errors
 * Constructors assures that r and r0 contains 0.
 *
 * \ingroup geomset
 */
template <typename MatrixT>
class CenteredDoubletonSet : public capd::geomset::DoubletonSet<MatrixT>{

public:
  typedef capd::geomset::DoubletonSet<MatrixT> BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename BaseSet::VectorType VectorType;
  typedef typename BaseSet::ColumnVectorType ColumnVectorType;
  typedef typename BaseSet::ScalarType ScalarType;

  explicit CenteredDoubletonSet(int dim) : BaseSet(dim) {}
  explicit CenteredDoubletonSet(const VectorType& x);
  CenteredDoubletonSet(const VectorType& x, const VectorType& r0);
  CenteredDoubletonSet(const VectorType& x, const MatrixType& C, const VectorType& r0);
  CenteredDoubletonSet(const VectorType& x,
               const MatrixType& C, const VectorType& r0,
               const VectorType& r
  );
  CenteredDoubletonSet(const VectorType& x,
               const MatrixType& C, const VectorType& r0,
               const MatrixType& B, const VectorType& r
  );
  CenteredDoubletonSet& operator=(const VectorType & v){
    BaseSet::operator=(v);
    return *this;
  }
  virtual std::string name() const { return "CenteredDoubletonSet"; }

  using BaseSet::m_x;
  using BaseSet::m_B;
  using BaseSet::m_r;
  using BaseSet::m_C;
  using BaseSet::m_r0;
};

}} // namespace capd::geomset
#endif // _CAPD_GEOMSET_CENTEREDDOUBLETONSET_H_


