/////////////////////////////////////////////////////////////////////////////
/// @file C11Rect2.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_C11RECT2_HPP_ 
#define _CAPD_DYNSET_C11RECT2_HPP_ 

#include <sstream>
#include "capd/auxil/minmax.h"
#include "capd/dynset/C11Rect2.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType,typename QRPolicy>
C11Rect2<MatrixType,QRPolicy>::C11Rect2(const NormType& aNorm, int dim)
  : m_x(dim), m_r(dim), m_r0(dim),
    m_B(MatrixType::Identity(dim)),
    m_C(MatrixType::Identity(dim)),
    m_D(MatrixType::Identity(dim)),
    m_Bjac(MatrixType::Identity(dim)),
    m_R(dim,dim),
    m_Cjac(MatrixType::Identity(dim)),
    m_R0(dim,dim),
    m_Norm(aNorm.clone()),
    m_sizeFactor(20.)
{
  m_x.clear();
  m_r.clear();
  m_r0.clear();
  m_R.clear();
  m_R0.clear();
}


template<typename MatrixType,typename QRPolicy>
C11Rect2<MatrixType,QRPolicy>::C11Rect2(const C11Rect2& s)
  : m_x(s.m_x),
    m_r(s.m_r),
    m_r0(s.m_r0),
    m_B(s.m_B),
    m_C(s.m_C),
    m_D(s.m_D),
    m_Bjac(s.m_Bjac),
    m_R(s.m_R),
    m_Cjac(s.m_Cjac),
    m_R0(s.m_R0),
    m_Norm(s.m_Norm->clone()),
    m_sizeFactor(s.m_sizeFactor)
{}



template<typename MatrixType,typename QRPolicy>
C11Rect2<MatrixType,QRPolicy>::C11Rect2(const VectorType& x, const NormType& aNorm, double sizeFactor)
  : m_x(x),
    m_r(x.dimension()),
    m_r0(x.dimension()),
    m_B(MatrixType::Identity(x.dimension())),
    m_C(MatrixType::Identity(x.dimension())),
    m_D(MatrixType::Identity(x.dimension())),
    m_Bjac(MatrixType::Identity(x.dimension())),
    m_R(x.dimension(),x.dimension()),
    m_Cjac(MatrixType::Identity(x.dimension())),
    m_R0(x.dimension(),x.dimension()),
    m_Norm(aNorm.clone()),
    m_sizeFactor(sizeFactor)
{
  split(m_x,m_r0);
  m_r.clear();
  m_R.clear();
  m_R0.clear();
}

template<typename MatrixType,typename QRPolicy>
C11Rect2<MatrixType,QRPolicy>::C11Rect2(
    const VectorType& x,
    const VectorType& r0,
    const NormType& aNorm,
    double sizeFactor
  ):m_x(x),
    m_r(x.dimension()),
    m_r0(r0),
    m_B(MatrixType::Identity(x.dimension())),
    m_C(MatrixType::Identity(x.dimension())),
    m_D(MatrixType::Identity(x.dimension())),
    m_Bjac(MatrixType::Identity(x.dimension())),
    m_R(x.dimension(),x.dimension()),
    m_Cjac(MatrixType::Identity(x.dimension())),
    m_R0(x.dimension(),x.dimension()),
    m_Norm(aNorm.clone()),
    m_sizeFactor(sizeFactor)
{
  m_r.clear();
  m_R.clear();
  m_R0.clear();
   
// we must verify, if 0\in m_r0
// we will use m_r as zero vector
  if(!subset(m_r,m_r0))
  {
    m_x += m_r0;
    split(m_x,m_r0);
  }
}


template<typename MatrixType,typename QRPolicy>
C11Rect2<MatrixType,QRPolicy>::C11Rect2(
    const VectorType& x,
    const MatrixType& C,
    const VectorType& r0,
    const NormType& aNorm,
    double sizeFactor
  ):m_x(x),
    m_r(x.dimension()),
    m_r0(r0),
    m_B(MatrixType::Identity(x.dimension())),
    m_C(C),
    m_D(MatrixType::Identity(x.dimension())),
    m_Bjac(MatrixType::Identity(x.dimension())),
    m_R(x.dimension(),x.dimension()),
    m_Cjac(MatrixType::Identity(x.dimension())),
    m_R0(x.dimension(),x.dimension()),
    m_Norm(aNorm.clone()),
    m_sizeFactor(sizeFactor)
{
  m_r.clear();
  m_R.clear();
  m_R0.clear();
   
// we must verify if m_r0 contains zero
  if(!subset(m_r,m_r0))
  {
    // here we use temporary m_r as a center of m_r0
    m_r = m_r0;
    split(m_r,m_r0);
    m_x += m_C*m_r;
    // now m_x + C*m_r0 is valid set, but m_x is not a point vector
    split(m_x,m_r);
    // after that we obtain valid representation m_x + m_C*m_r0 + m_B*m_r, where m_B=Id
  }
}

//-----------------------------------------------

template<typename MatrixType,typename QRPolicy>
void C11Rect2<MatrixType,QRPolicy>::move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys, C11Rect2& result) const
{
  int dim = m_x.dimension();
  VectorType Rem(dim);
  MatrixType Jac(dim,dim);

  VectorType xx = m_x + m_C*m_r0 + m_B*m_r;
  int found;
  VectorType Enc = c1dynsys.enclosure(xx,&found);
  MatrixType S = c1dynsys.jacEnclosure(Enc,*m_Norm);
  c1dynsys.JacRemainder(Enc,S,Rem,Jac);
  Jac += c1dynsys.JacPhi(xx);

  result.m_x = c1dynsys.Phi(m_x) + c1dynsys.Remainder(m_x);

  // xx is unnecessary now, so we will use it again
  split(result.m_x,xx);

  result.m_C = Jac*m_C;
  split(result.m_C,S);
  xx += S*m_r0;
  MatrixType A = Jac*m_B;
  capd::vectalg::mid(A,result.m_B); // result.m_B = midMatrix(A) but faster
  QRPolicy::orthonormalize(result.m_B,m_r);
  MatrixType Qtr = Transpose(result.m_B);
  result.m_r = (Qtr*A)*m_r + Qtr*xx;

  if(&result!=this) 
    result.m_r0 = m_r0;
// T.Kapela - put set r into r0 if r is too big.
  if(m_sizeFactor!=0)
    if( capd::vectalg::size(result.m_r) > m_sizeFactor * capd::vectalg::size(result.m_r0))
    {
      result.m_r0 = result.m_r +  ((Qtr * result.m_C) * result.m_r0);
      result.m_C = result.m_B;
      result.m_B = MatrixType::Identity(dim);
      result.m_r.clear();
    }

//-----------------------------------------------

  // A is unnecessary now
  split(Jac,S);
  result.m_D = Jac*m_D + S*(m_D + m_Bjac*m_R + m_Cjac*m_R0);
  split(result.m_D,A);

  result.m_Cjac = Jac * m_Cjac;
  split(result.m_Cjac,S);

  A += S*m_R0;
  // S is unnecessary now, so we will use it again
  S = Jac*m_Bjac;
  capd::vectalg::mid(S,result.m_Bjac);
  QRPolicy::orthonormalize(result.m_Bjac);
  Qtr = Transpose(result.m_Bjac);
  result.m_R = (Qtr*S)*m_R + Qtr*A;
  if (&result!=this) 
    result.m_R0 = m_R0;

  if(m_sizeFactor!=0)
  {
    typename MatrixType::ScalarType::BoundType maxSizeR = 0., maxSizeR0 = 0.;
    int i,j;
    for(i=0;i<dim;i++)
      for(j=0;j<dim;j++)
      {
        maxSizeR = capd::max(maxSizeR,diam(result.m_R[i][j]).rightBound());
        maxSizeR0 = capd::max(maxSizeR0, diam(result.m_R0[i][j]).rightBound());
      }

    if(maxSizeR>m_sizeFactor*maxSizeR0)
    {
      result.m_R0 = result.m_R + (Qtr * result.m_Cjac) * result.m_R0;
      result.m_Cjac = result.m_Bjac;
      result.m_Bjac = MatrixType::Identity(dim);
      result.m_R.clear();
    }
  }
}

// ------------------------------------------------------------------------

template<typename MatrixType,typename QRPolicy>
typename C11Rect2<MatrixType,QRPolicy>::ScalarType C11Rect2<MatrixType,QRPolicy>::size(void) const
{
  return capd::vectalg::size(m_x + m_C*m_r0 + m_B*m_r);
}

template<typename MatrixType,typename QRPolicy>
std::string C11Rect2<MatrixType,QRPolicy>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << "C1rect2:\n x=";
  descriptor << m_x << "\n B=";
  descriptor << m_B << "\n r=";
  descriptor << m_r << "\n C= ";
  descriptor << m_C << "\n r0= ";
  descriptor << m_r0 << "\n D= ";
  descriptor << m_D << "\n Bjac= ";
  descriptor << m_Bjac << "\n R= ";
  descriptor << m_R << "\n Cjac= ";
  descriptor << m_Cjac << "\n R0= ";
  descriptor << m_R0 << '\0';

  return descriptor.str();
}

template<typename MatrixType,typename QRPolicy>
C11Rect2<MatrixType,QRPolicy>::operator typename C11Rect2<MatrixType,QRPolicy>::MatrixType() const
{
  return m_D + m_Bjac*m_R + m_Cjac*m_R0;
}

template<typename MatrixType,typename QRPolicy>
C11Rect2<MatrixType,QRPolicy>& C11Rect2<MatrixType,QRPolicy>::operator=(const VectorType& x)
{
  int dim = x.dimension();
  m_x = x;
  m_r0 = VectorType(dim);
  split(m_x,m_r0);
  m_C = MatrixType::Identity(dim);
  m_B = MatrixType::Identity(dim);
  m_r = VectorType(dim);
  m_r.clear();

  m_Bjac = m_Cjac = m_D = MatrixType::Identity(dim);
  m_R = MatrixType(dim,dim);
  m_R.clear();
  m_R0 = MatrixType(dim,dim);
  m_R0.clear();

  return *this;
}

template<typename MatrixType,typename QRPolicy>
C11Rect2<MatrixType,QRPolicy>& C11Rect2<MatrixType,QRPolicy>::operator=(const C11Rect2& S)
{
  m_x = S.m_x;
  m_B = S.m_B;
  m_r = S.m_r;
  m_C = S.m_C;
  m_r0 = S.m_r0;

  m_D = S.m_D;
  m_Bjac = S.m_Bjac;
  m_R = S.m_R;
  m_Cjac = S.m_Cjac;
  m_R0 = S.m_R0;

  m_sizeFactor = S.m_sizeFactor;
  delete m_Norm;
  m_Norm = S.m_Norm->clone();
  return *this;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C11RECT2_HPP_ 
