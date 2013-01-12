/////////////////////////////////////////////////////////////////////////////
/// @file C11Rect2.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

/* Author: Daniel Wilczak, 2006 */

#ifndef _CAPD_DYNSET_C11RECT2_H_ 
#define _CAPD_DYNSET_C11RECT2_H_ 

#include "capd/dynset/C1Set.h"
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/C1DynSys.h"
#include "capd/dynset/QRPolicy.h"


namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

/**
 *  \f$C^1\f$ doubleton set with reorganization moved by QR decomposition (3rd method).
 *
 *  C^1-Lohner algorithm.
 *  Derivative of the flow moved via QR decomposition (third method)
 *  the set part - QR decomposition (3-rd method)
*/
template <typename MatrixT, typename QRPolicy = FullQRWithPivoting>
class C11Rect2 : public C1Set<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  C11Rect2(const NormType& the_norm, int);
  C11Rect2(const VectorType& x, const NormType&, double s_factor = 20);
  C11Rect2(const VectorType& x, const VectorType& r0, const NormType&, double sizeFactor = 20);
  C11Rect2(const VectorType& x, const MatrixType& C, const VectorType& r0, const NormType&, double sizeFactor = 20);
  C11Rect2(const C11Rect2 &c);
  ~C11Rect2(){delete m_Norm;}

  ScalarType size(void) const;
  C1Set<MatrixType>* clone(void) const;
  C1Set<MatrixType>* fresh(void) const;
  C1Set<MatrixType>* cover(const VectorType& v) const;

  VectorType center(void) const;
  void move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys);
  void move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys, C11Rect2& result) const;

  std::string show(void) const;
  const NormType* getNorm(void) const;
  double setFactor(double sFactor); // sets size factor :  0 = no swapping
  void disableSwapping();
  double getFactor();

  operator VectorType() const;
  operator MatrixType() const;
  C11Rect2 &operator=(const VectorType &v);
  C11Rect2 &operator=(const C11Rect2 &S);

protected:

// a representation of the set: x + C*r0 + B*r

  VectorType m_x,m_r,m_r0;
  MatrixType m_B,m_C;

  MatrixType m_D, m_Bjac, m_R, m_Cjac, m_R0; // D + Bjac*R  + Cjac * R0;

  NormType *m_Norm; //the logarithmic Norm<IVectorType,IMatrixType> used in the computation of a rough
                  // enclosure for the variational part

  double m_sizeFactor;  // if size of r0 is greater than r *size_factor we  put r in r0 and set r=0
                       // if size_factor = 0 we disable swapping
};
/// @}

// -------------------------------------------------------------------

template<typename MatrixType,typename QRPolicy>
inline void C11Rect2<MatrixType,QRPolicy>::move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys)
{
  move(c1dynsys,*this);
}

template<typename MatrixType,typename QRPolicy>
inline C1Set<MatrixType>* C11Rect2<MatrixType,QRPolicy>::clone(void) const
{
  return new C11Rect2<MatrixType>(*this);
}

template<typename MatrixType,typename QRPolicy>
inline C1Set<MatrixType>* C11Rect2<MatrixType,QRPolicy>::fresh(void) const
{
  return new C11Rect2<MatrixType,QRPolicy>(*m_Norm,m_x.dimension());
}

template<typename MatrixType,typename QRPolicy>
inline C1Set<MatrixType>* C11Rect2<MatrixType,QRPolicy>::cover(const VectorType& v) const
{
  return new C11Rect2<MatrixType,QRPolicy>(midVector(v),v-midVector(v), *m_Norm);
}

template<typename MatrixType,typename QRPolicy>
inline typename C11Rect2<MatrixType,QRPolicy>::VectorType C11Rect2<MatrixType,QRPolicy>::center(void) const
{
  return m_x;
}

template<typename MatrixType,typename QRPolicy>
inline C11Rect2<MatrixType,QRPolicy>::operator typename C11Rect2<MatrixType,QRPolicy>::VectorType(void) const
{
  return m_x + m_C*m_r0 + m_B*m_r;
}

template<typename MatrixType,typename QRPolicy>
inline const typename C11Rect2<MatrixType,QRPolicy>::NormType* C11Rect2<MatrixType,QRPolicy>::getNorm(void) const
{
  return m_Norm;
}

template<typename MatrixType,typename QRPolicy>
inline double C11Rect2<MatrixType,QRPolicy>::setFactor(double sFactor) // sets size factor :  0 = no swapping
{
  double s = m_sizeFactor;
  m_sizeFactor = sFactor;
  return s;
}

template<typename MatrixType,typename QRPolicy>
inline void C11Rect2<MatrixType,QRPolicy>::disableSwapping()
{
  m_sizeFactor = 0.0;
}

template<typename MatrixType,typename QRPolicy>
inline double C11Rect2<MatrixType,QRPolicy>::getFactor() // returns size factor
{
  return m_sizeFactor;
}

}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_C11RECT2_H_ 

