
/////////////////////////////////////////////////////////////////////////////
/// @file MatrixAffineSet.h
///
/// @author kapela
/// Created on: Oct 22, 2009
// ///////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_GEOMSET_MATRIXAFFINESET_H_
#define _CAPD_GEOMSET_MATRIXAFFINESET_H_


namespace capd {
namespace geomset {

/**
 *  Set of matrices represented as D + Bjac * R.
 *
 * Set of matrices  is represented as
 * \f[
 * D + Bjac \cdot R
 * \f]
 * where
 *  - the matrix D is a center,
 *  - the matrix Bjac is a coordinate system
 *  - the matrix R represents the set in a given coordinate system.
 *
 * \ingroup geomset
 */
template<typename MatrixT>
class MatrixAffineSet {

public:
  typedef MatrixT MatrixType;
  typedef  typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ColumnVectorType ColumnVectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  explicit MatrixAffineSet(int dim);                                                 // D:=Id,      Bjac:=Id  R:=0,
  explicit MatrixAffineSet(const MatrixType& A);                                     // D:=mid(v)  Bjac:=Id  R:=[-radius(v), radius(v)]
  MatrixAffineSet(const MatrixType& D, bool);                                        // D:=D,      Bjac:=Id  R:=0      !! do not split matrix D!!
  MatrixAffineSet(const MatrixType& D, const MatrixType& R);                         // D:=D       Bjac:=Id  R:=R
  MatrixAffineSet(const MatrixType& D, const MatrixType& Bjac, const MatrixType& R);    // D:=D       Bjac:=Bjac   R:=R
  virtual ~MatrixAffineSet() {}
  /// return interval matrix containing all matrices in the set
  operator MatrixType() const;
  /// sets the set to identity
  void setToIdentity(int dim);
  /// returns set detailed information
  virtual std::string toString() const;
  /// returns set's name
  virtual std::string name() const { return "MatrixAffineSet"; }
  /// returns image of the set after affine transformation
  virtual MatrixType affineMatrixTransformation(const MatrixType& A_M) const;

protected:
  /// D is a center of the set
  MatrixType m_D;
public:
  const MatrixType & get_D () const {return m_D;}
  const ScalarType & getElement_D (int i, int j) const {return m_D(i+1,j+1);}
  VectorType getRow_D (int i) const {return m_D.row(i);}
  ColumnVectorType getColumn_D (int j) const {return m_D.column(j);}
  void set_D (const MatrixType & Bjac) {m_D = Bjac;}
  void setElement_D (int i, int j, const ScalarType & s) {m_D(i+1, j+1) = s;}
  template <typename VectorT>
  void setRow_D (int i, const VectorT & v) {m_D.row(i) = v;}
  template <typename VectorT>
  void setColumn_D (int j, const VectorT & v) {m_D.column(j) = v;}


protected:
  /// R is a interval set in given coordinate system
  MatrixType m_R;
public:
  const MatrixType & get_R () const {return m_R;}
  const ScalarType & getElement_R (int i, int j) const {return m_R(i+1,j+1);}
  VectorType getRow_R (int i) const {return m_R.row(i);}
  ColumnVectorType getColumn_R (int j) const {return m_R.column(j);}
  void set_R (const MatrixType & Bjac) {m_R = Bjac;}
  void setElement_R (int i, int j, const ScalarType & s) {m_R(i+1, j+1) = s;}
  template <typename VectorT>
  void setRow_R (int i, const VectorT & v) {m_R.row(i) = v;}
  template <typename VectorT>
  void setColumn_R (int j, const VectorT & v) {m_R.column(j) = v;}

protected:
  /// Bjac is a coordinate system
  MatrixType m_Bjac;
public:
  const MatrixType & get_Bjac () const {return m_Bjac;}
  const ScalarType & getElement_Bjac (int i, int j) const {return m_Bjac(i+1,j+1);}
  VectorType getRow_Bjac (int i) const {return m_Bjac.row(i);}
  ColumnVectorType getColumn_Bjac (int j) const {return m_Bjac.column(j);}
  void set_Bjac (const MatrixType & Bjac) {m_Bjac = Bjac;}
  void setElement_Bjac (int i, int j, const ScalarType & s) {m_Bjac(i+1, j+1) = s;}
  template <typename VectorT>
  void setRow_Bjac (int i, const VectorT & v) {m_Bjac.row(i) = v;}
  template <typename VectorT>
  void setColumn_Bjac (int j, const VectorT & v) {m_Bjac.column(j) = v;}

};

template<typename MatrixT>
inline MatrixAffineSet<MatrixT>::operator typename MatrixAffineSet<MatrixT>::MatrixType(void) const {
  return m_D + m_Bjac*m_R;
}
}} //end of namespace capd::geomset

#endif // _CAPD_GEOMSET_MATRIXAFFINESET_H_

