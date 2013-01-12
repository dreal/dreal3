/////////////////////////////////////////////////////////////////////////////
/// @file EllipsoidSet.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_ELLIPSOIDSET_H_ 
#define _CAPD_DYNSET_ELLIPSOIDSET_H_ 

#include "capd/dynset/C0Set.h"

namespace capd{
namespace dynset{

template<typename FlVectorType, typename MatrixT>
class EllipsoidSet : public C0Set<MatrixT>{
public:
  typedef typename FlVectorType::ScalarType FlScalar;
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  static ScalarType mz_euclNorm(const VectorType& a);
  static ScalarType Hybrid_norm_eucl(const MatrixType& a, int i);
  static ScalarType Hybrid_norm_eucl(const VectorType& a,const VectorType& b);
  static ScalarType Hybrid_norm_eucl(const MatrixType& a,const MatrixType& b, int i);
  static VectorType Hybrid_norm_eucl(const MatrixType &a);
  static ScalarType MatrixEuclNormUp(MatrixType& a);
  static void QR_decompose_t_mz(const MatrixType& A1, const MatrixType& A2, MatrixType& R);
  static void Solve_gauss(MatrixType& A,MatrixType& X, MatrixType& B);

public:
  explicit EllipsoidSet(int);
  explicit EllipsoidSet(const VectorType& the_z);
  EllipsoidSet(const VectorType& the_z, FlScalar the_r);
  EllipsoidSet(const VectorType& the_z, FlScalar the_r, const MatrixType& the_L);
  ScalarType size(void);
  C0Set<MatrixType>* clone(void);
  C0Set<MatrixType>* fresh(void);
  C0Set<MatrixType>* cover(const VectorType& v);
  VectorType center(void);
  void N_move(MatrixType& A, VectorType& b);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys, EllipsoidSet& result) const;
  operator VectorType() const;
  virtual VectorType affineTransformation(const MatrixType&, const VectorType&) const;

  VectorType boxInterval();
  VectorType sBoxInterval(EllipsoidSet& p, FlScalar mdev);
  FlVectorType getCenter();
  std::string show() const;

protected:
  VectorType m_z;
  MatrixType m_L;
  FlScalar m_r;
};

// inline definitions

template<typename FlVectorType, typename MatrixType>
inline EllipsoidSet<FlVectorType,MatrixType>::EllipsoidSet(int dim)
  : m_z(dim),
    m_L(MatrixType::Identity(dim)),
    m_r(0.0)
{
  m_z.clear();
}

template<typename FlVectorType, typename MatrixType>
inline EllipsoidSet<FlVectorType,MatrixType>::operator typename EllipsoidSet<FlVectorType,MatrixType>::VectorType(void) const
{
  VectorType ksi(m_z.dimension());
  for(int i=0; i<ksi.dimension(); i++)
    ksi[i] = ScalarType(-m_r,m_r);

  return m_z + m_L*ksi;
}

template<typename FlVectorType, typename MatrixType>
inline EllipsoidSet<FlVectorType,MatrixType>::EllipsoidSet(const VectorType &the_z)
  : m_z(the_z),
    m_L(MatrixType::Identity(the_z.dimension())),
    m_r(0.0)
{}

template<typename FlVectorType, typename MatrixType>
inline EllipsoidSet<FlVectorType,MatrixType>::EllipsoidSet(const VectorType& the_z, FlScalar the_r)
  : m_z(the_z),
    m_L(MatrixType::Identity(the_z.dimension())),
    m_r(the_r)
{}

template<typename FlVectorType, typename MatrixType>
inline C0Set<MatrixType>* EllipsoidSet<FlVectorType,MatrixType>::clone(void)
{
  return new EllipsoidSet<FlVectorType,MatrixType>(*this);
}

template<typename FlVectorType, typename MatrixType>
inline C0Set<MatrixType>* EllipsoidSet<FlVectorType,MatrixType>::fresh(void)
{
  return new EllipsoidSet<FlVectorType,MatrixType>(m_z.dimension());
}

template<typename FlVectorType, typename MatrixType>
inline C0Set<MatrixType>* EllipsoidSet<FlVectorType,MatrixType>::cover(const VectorType& v)
{
  return new EllipsoidSet<FlVectorType,MatrixType>(midVector(v),(rightVector(v)-midVector(v)).euclNorm().rightBound());
}

template<typename FlVectorType, typename MatrixType>
inline typename EllipsoidSet<FlVectorType,MatrixType>::VectorType
   EllipsoidSet<FlVectorType,MatrixType>::center(void)
{
  return m_z;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_ELLIPSOIDSET_H_ 
