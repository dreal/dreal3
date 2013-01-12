
/////////////////////////////////////////////////////////////////////////////
/// @file MatrixDoubletonSet.h
///
/// @author kapela
/// Created on: Oct 22, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_GEOMSET_MATRIXDOUBLETONSET_H_
#define _CAPD_GEOMSET_MATRIXDOUBLETONSET_H_

#include "capd/geomset/MatrixAffineSet.h"

namespace capd{
namespace geomset{
/**
 * Set of matrices represented as D + Cjac * R0 + Bjac * R.
 *
 * Set of matrices  is represented as
 * \f[
 *   D + Cjac \cdot R0 + Bjac \cdot R
 * \f]
 * where
 *   - the matrix D is a center,
 *   - matrices Bjac and Cjac are coordinate systems
 *   - the matrix R0 represents stores set size
 *   - the matrix R is used as containers for all errors
 *
 * \ingroup geomset
 */
template <typename MatrixT>
class MatrixDoubletonSet : public MatrixAffineSet<MatrixT>{

public:
  typedef MatrixAffineSet<MatrixT> BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename BaseSet::VectorType VectorType;
  typedef typename BaseSet::ColumnVectorType ColumnVectorType;
  typedef typename BaseSet::ScalarType ScalarType;
  typedef typename BaseSet::NormType NormType;

  explicit MatrixDoubletonSet(int);                                            ///< D:=Id, R0:=0, C:=Id, R:=0, B:=Id
  explicit MatrixDoubletonSet(const MatrixType& V);                            ///< D:=mid(V), R0:=[-radius(V),radius(V)], C:=Id, R:=0, B:=Id
  MatrixDoubletonSet(const MatrixType& D, bool);                               ///< D:=D, R0:=0, C:=Id, R:=0, B:=Id
  MatrixDoubletonSet(const MatrixType& D, const MatrixType& R0);               ///< D:=D, R0:=R0, C:=Id, R:=0, B:=Id
  MatrixDoubletonSet(const MatrixType& D, const MatrixType& Cjac, const MatrixType& R0);
  MatrixDoubletonSet(const MatrixType& D,
               const MatrixType& Cjac, const MatrixType& R0,
               const MatrixType& R
  );
  MatrixDoubletonSet(const MatrixType& D,
               const MatrixType& Cjac, const MatrixType& R0,
               const MatrixType& Bjac, const MatrixType& R
  );

  operator MatrixType() const;
  void setToIdentity(int dim);
  std::string toString() const;
  virtual std::string name() const { return "MatrixDoubletonSet"; }
  virtual MatrixType affineMatrixTransformation(const MatrixType& ) const;

  using BaseSet::m_D;
  using BaseSet::m_Bjac;
  using BaseSet::m_R;

  /// r0 is a interval set in given coordinate system that represents 'Lipschitz' part
protected:
  MatrixType m_R0;
public:
  const MatrixType & get_R0 () const {return m_R0;}
    const ScalarType & getElement_R0 (int i, int j) const {return m_R0(i+1,j+1);}
    VectorType getRow_R0 (int i) const {return m_R0.row(i);}
    ColumnVectorType getColumn_R0 (int j) const {return m_R0.column(j);}
    void set_R0 (const MatrixType & R0) {m_R0 = R0;}
    void setElement_R0 (int i, int j, const ScalarType & s) {m_R0(i+1, j+1) = s;}
    template <typename VectorT>
    void setRow_R0 (int i, const VectorT & v) {m_R0.row(i) = v;}
    template <typename VectorT>
    void setColumn_R0 (int j, const VectorT & v) {m_R0.column(j) = v;}

  /// C is a coordinate system of the 'Lipschitz' part
protected:
  MatrixType m_Cjac;
public:
  const MatrixType & get_Cjac () const {return m_Cjac;}
  const ScalarType & getElement_Cjac (int i, int j) const {return m_Cjac(i+1,j+1);}
  VectorType getRow_Cjac (int i) const {return m_Cjac.row(i);}
  ColumnVectorType getColumn_Cjac (int j) const {return m_Cjac.column(j);}
  void set_Cjac (const MatrixType & C) {m_Cjac = C;}
  void setElement_Cjac (int i, int j, const ScalarType & s) {m_Cjac(i+1, j+1) = s;}
  template <typename VectorT>
  void setRow_Cjac (int i, const VectorT & v) {m_Cjac.row(i) = v;}
  template <typename VectorT>
  void setColumn_Cjac (int j, const VectorT & v) {m_Cjac.column(j) = v;}

};

template<typename MatrixT>
inline MatrixDoubletonSet<MatrixT>::operator typename MatrixDoubletonSet<MatrixT>::MatrixType(void) const {
  return m_D + m_Cjac*m_R0 + m_Bjac*m_R;
}

}} // namespace capd::geomset

#endif // _CAPD_GEOMSET_MATRIXDOUBLETONSET_H_

