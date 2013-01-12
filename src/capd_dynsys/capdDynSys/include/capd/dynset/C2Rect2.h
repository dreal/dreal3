/////////////////////////////////////////////////////////////////////////////
/// @file C2Rect2.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_C2RECT2_H_ 
#define _CAPD_DYNSET_C2RECT2_H_ 

#include "capd/vectalg/Norm.h"
#include "capd/map/C2Coeff.h"
#include "capd/dynset/C2Set.h"
#include "capd/dynsys/C2DynSys.h"


namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

/**
 * C2 set in doubleton form with reorganization moved by QR decomposition method.
 *
 *  C^2-Lohner algorithm.
 *  Derivative of the flow moved via QR decomposition (third method)
 *  the set part - QR decomposition (3-rd method)
 */
template<typename MatrixT>
class C2Rect2: public C2Set<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::map::C2Coeff<ScalarType> C2CoeffType;

  C2Rect2(const NormType& the_Norm, int dim);
  C2Rect2(const VectorType& x, const NormType&,double sFactor=20.);
  C2Rect2(const VectorType& x, const VectorType& r0, const NormType&, double sizeFactor=20.);
  C2Rect2(const VectorType& x, const MatrixType& C, const VectorType& r0, const NormType&,double sizeFactor=20.);
  C2Rect2(const C2Rect2 &c);
  ~C2Rect2();

  ScalarType size(void) const;
  C2Set<MatrixType>* clone(void) const;
  C2Set<MatrixType>* fresh(void) const;
  C2Set<MatrixType>* cover(const VectorType& v) const;
  VectorType center(void) const;
  void move(capd::dynsys::C2DynSys<MatrixType>& c2dynsys);
  void move(capd::dynsys::C2DynSys<MatrixType>& c2dynsys, C2Rect2& result);
  std::string show(void) const;
  const C2CoeffType& getC2Coeff() const {return m_c2Coeff;}
  const NormType* getNorm(void) const;

  operator VectorType() const;
  operator MatrixType() const;
  const ScalarType& operator()(int i, int j, int c) const;
  VectorType operator()(int j, int c) const;
  MatrixType operator()(int i);
  C2Rect2& operator=(const VectorType& v);
  C2Rect2& operator=(const C2Rect2& S);

protected:
  int m_dim;

// a representation of the set: x + C*r0 + B*r

  VectorType m_x, m_r, m_r0;
  MatrixType m_B, m_C;
  MatrixType m_D, m_Bjac, m_R, m_Cjac, m_R0; // D + Bjac*R + Cjac*R0

// C^2 part represented as alpha + Bjac*Htilde
// C^2 part represented as alpha + Bjac*HR + Cjac*HR0

  C2CoeffType m_alpha, m_HR, m_HR0, m_c2Coeff;

  NormType *m_Norm; //the logarithmic Norm<VectorType,MatrixType> used in the computation of a rough
                    // enclosure for the variational part

  double sizeFactor;
};
/// @}

// -----------------------------------------------------------------------------

template<typename MatrixType>
inline void C2Rect2<MatrixType>::move(capd::dynsys::C2DynSys<MatrixType>& c2dynsys)
{
  move(c2dynsys,*this);
}

template<typename MatrixType>
inline C2Set<MatrixType>* C2Rect2<MatrixType>::clone(void) const
{
  return new C2Rect2<MatrixType>(*this);
}

template<typename MatrixType>
inline C2Set<MatrixType>* C2Rect2<MatrixType>::fresh(void) const
{
  return new C2Rect2<MatrixType>(*m_Norm,m_dim);
}

template<typename MatrixType>
inline C2Set<MatrixType>* C2Rect2<MatrixType>::cover(const VectorType& v) const
{
  return new C2Rect2<MatrixType>(midVector(v),v-midVector(v), *m_Norm);
}

template<typename MatrixType>
inline typename C2Rect2<MatrixType>::VectorType C2Rect2<MatrixType>::center(void) const
{
  return m_x;
}

template<typename MatrixT>
inline C2Rect2<MatrixT>::operator typename C2Rect2<MatrixT>::VectorType(void) const
{
  return m_x + m_C*m_r0 + m_B*m_r;
}

template<typename MatrixType>
inline const typename C2Rect2<MatrixType>::NormType* C2Rect2<MatrixType>::getNorm(void) const
{
  return m_Norm;
}

}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_C2RECT2_H_ 
