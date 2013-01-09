/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2Rect2.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_C2RECT2_HPP_ 
#define _CAPD_DYNSET_C2RECT2_HPP_ 

#include <sstream>
#include "capd/dynset/C2Rect2.h"
#include "capd/vectalg/Norm.hpp"
#include "capd/map/C2Coeff.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
C2Rect2<MatrixType>::C2Rect2(const NormType& aNorm, int dim)
  : m_dim(dim),
    m_x(dim),
    m_r(dim),
    m_r0(dim),
    m_B(MatrixType::Identity(dim)),
    m_C(MatrixType::Identity(dim)),
    m_D(MatrixType::Identity(dim)),
    m_Bjac(MatrixType::Identity(dim)),
    m_R(dim,dim),
    m_Cjac(MatrixType::Identity(dim)),
    m_R0(dim,dim),
    m_alpha(dim),
    m_HR(dim),
    m_HR0(dim),
    m_c2Coeff(dim),
    m_Norm(aNorm.clone()),
    sizeFactor(20.)
{
  m_x.clear();
  m_r.clear();
  m_r0.clear();
  m_R.clear();
  m_R0.clear();

  m_c2Coeff.clear();
  m_alpha.clear();
  m_HR.clear();
  m_HR0.clear();
}


template<typename MatrixType>
C2Rect2<MatrixType>::C2Rect2(const C2Rect2& s)
  : m_dim(s.m_dim),
    m_x(s.m_x),
    m_r(s.m_r),
    m_r0(s.m_r0),
    m_B(s.m_B),
    m_C(s.m_B),
    m_D(s.m_D),
    m_Bjac(s.m_Bjac),
    m_R(s.m_R),
    m_Cjac(s.m_Cjac),
    m_R0(s.m_R0),
    m_alpha(m_dim),
    m_HR(m_dim),
    m_HR0(m_dim),
    m_c2Coeff(m_dim),
    m_Norm(s.m_Norm->clone()),
    sizeFactor(s.sizeFactor)
{
  m_c2Coeff.clear();
  m_alpha.clear();
  m_HR.clear();
  m_HR0.clear();
}

template<typename MatrixType>
C2Rect2<MatrixType>::C2Rect2(const VectorType& x, const NormType& aNorm, double sizeFactor)
  : m_dim(x.dimension()),
    m_x(x),
    m_r(m_dim),
    m_r0(m_dim),
    m_B(MatrixType::Identity(m_dim)),
    m_C(MatrixType::Identity(m_dim)),
    m_D(MatrixType::Identity(m_dim)),
    m_Bjac(MatrixType::Identity(m_dim)),
    m_R(m_dim,m_dim),
    m_Cjac(MatrixType::Identity(m_dim)),
    m_R0(m_dim,m_dim),
    m_alpha(m_dim),
    m_HR(m_dim),
    m_HR0(m_dim),
    m_c2Coeff(m_dim),
    m_Norm(aNorm.clone()),
    sizeFactor(sizeFactor)
{
  m_c2Coeff.clear();
  m_alpha.clear();
  m_HR.clear();
  m_HR0.clear();

  split(m_x,m_r0);
  m_r.clear();
  m_R.clear();
  m_R0.clear();
}

template<typename MatrixType>
C2Rect2<MatrixType>::C2Rect2(
    const VectorType& x,
    const VectorType& r0,
    const NormType& aNorm,
    double sFactor
  ): m_dim(x.dimension()),
    m_x(x),
    m_r0(r0),
    m_B(MatrixType::Identity(m_dim)),
    m_C(MatrixType::Identity(m_dim)),
    m_D(MatrixType::Identity(m_dim)),
    m_Bjac(MatrixType::Identity(m_dim)),
    m_R(m_dim,m_dim),
    m_Cjac(MatrixType::Identity(m_dim)),
    m_R0(m_dim,m_dim),
    m_alpha(m_dim),
    m_HR(m_dim),
    m_HR0(m_dim),
    m_c2Coeff(m_dim),
    m_Norm(aNorm.clone()),
    sizeFactor(sFactor)
{
  m_c2Coeff.clear();
  m_alpha.clear();
  m_HR.clear();
  m_HR0.clear();

  m_r.clear();
  m_R.clear();
  m_R0.clear();
   
  if(!subset(m_r,m_r0))
  {
    m_x += m_r0;
    split(m_x,m_r0);
  }
}


template<typename MatrixType>
C2Rect2<MatrixType>::C2Rect2(
    const VectorType& x,
    const MatrixType& C,
    const VectorType& r0,
    const NormType& aNorm,
    double sizeFactor
  ):m_dim(x.dimension()),
    m_x(x),
    m_r0(r0),
    m_B(MatrixType::Identity(m_dim)),
    m_C(C),
    m_D(MatrixType::Identity(m_dim)),
    m_Bjac(MatrixType::Identity(m_dim)),
    m_R(m_dim,m_dim),
    m_Cjac(MatrixType::Identity(m_dim)),
    m_R0(m_dim,m_dim),
    m_alpha(m_dim),
    m_HR(m_dim),
    m_HR0(m_dim),
    m_c2Coeff(m_dim),
    m_Norm(aNorm.clone()),
    sizeFactor(sizeFactor)
{
  m_c2Coeff.clear();
  m_alpha.clear();
  m_HR.clear();
  m_HR0.clear();

  m_r.clear();
  m_R.clear();
  m_R0.clear();

  if(!subset(m_r,m_r0))
  {
    VectorType centerR0(m_r0);
    split(centerR0,m_r0);
    m_x += m_C*centerR0;
    split(m_x,m_r);
  }
}

// ------------------------------------------------------------------------

template<typename MatrixType>
void C2Rect2<MatrixType>::move(capd::dynsys::C2DynSys<MatrixType>& c2dynsys, C2Rect2& result)
{
  VectorType y(m_dim), s(m_dim), Rem(m_dim);
  MatrixType X(m_dim,m_dim), S(m_dim,m_dim), Jac(m_dim,m_dim), jacRem(m_dim,m_dim);
  MatrixType Z(m_dim,m_dim), deltaA(m_dim,m_dim);

  C2CoeffType EH(m_dim), LH(m_dim), RH(m_dim), alpha(m_dim), deltaAlpha(m_dim);

  VectorType xx = m_x + m_C*m_r0 + m_B*m_r;
  MatrixType V = m_D + m_Bjac*m_R + m_Cjac*m_R0;

  int found;
  VectorType Enc = c2dynsys.enclosure(xx,&found);
  MatrixType jacEnc = c2dynsys.jacEnclosure(Enc,*m_Norm);
  c2dynsys.c2Enclosure(Enc,jacEnc,*m_Norm,EH);
  c2dynsys.c2Remainder(Enc,jacEnc,EH,Rem,jacRem,RH);

  y = c2dynsys.Phi(m_x) + Rem;
  split(y,s);
  c2dynsys.c2Phi(xx,Jac,LH);
  result.m_C = Jac*m_C;
  split(result.m_C,S);
  s += S*m_r0;
  MatrixType A = Jac*m_B;
  MatrixType Q = capd::vectalg::midMatrix(A);
  capd::matrixAlgorithms::orthonormalize(Q);
  MatrixType Qtr = Transpose(Q);
  result.m_x = y;
  result.m_r = (Qtr*A)*m_r+Qtr*s;
  result.m_B = Q;
  if(&result!=this) result.m_r0 = m_r0;

// T.Kapela - put set r into r0 if r is too big.
  if(sizeFactor!=0)
    if( capd::vectalg::size(result.m_r) > sizeFactor * capd::vectalg::size(result.m_r0))
    {
      result.m_r0 = result.m_r +  ((Qtr * result.m_C) * result.m_r0);
      result.m_C = result.m_B;
      result.m_B = MatrixType::Identity(m_dim);
      result.m_r = ScalarType(0.);
    }

// C^1 part  -----------------------------------------------

  A = Jac + jacRem;
  result.m_Cjac = A * m_Cjac;
  split(result.m_Cjac,S);
  split(A,deltaA);

  result.m_D = A*m_D + deltaA*V;
  split(result.m_D,Z);
  Z += S*m_R0;
  X = A*m_Bjac;
  Q = capd::vectalg::midMatrix(X);
  capd::matrixAlgorithms::orthonormalize(Q);
  Qtr = Transpose(Q);
  X=Qtr*X;
  result.m_R = X*m_R + Qtr*Z;
  result.m_Bjac = Q;
  if(&result!=this) result.m_R0 = m_R0;

// C^2 part -----------------------------------

  int i,j,c,ss,r;
  typename C2CoeffType::iterator i1=LH.begin(), i2=LH.end(), j1=RH.begin();
  while(i1!=i2)
  {
    // this loop computes LH += RH;
    *i1 += *j1;
    ++i1;
    ++j1;
  }
  alpha.clear();
  for(i=0;i<m_dim;++i)
    for(j=0;j<m_dim;++j)
      for(c=j;c<m_dim;++c)
      //--
        for(ss=0;ss<m_dim;++ss)
          for(r=0;r<m_dim;++r)
            alpha(i,j,c) += LH(i,ss,r) * V[ss][j] * V[r][c];

  alpha += A*m_alpha;
  alpha += deltaA*m_c2Coeff;

  capd::vectalg::split(alpha,deltaAlpha); // split from ivector.hpp
  result.m_alpha = alpha;
  // LH, RH are unnecessary now, so we can use it again
  LH = S*m_HR0; // here we store S*HR0 
  RH = X*m_HR; // here we store X*HR
  deltaAlpha += LH;
  result.m_HR = Qtr*deltaAlpha; // here we store Qtr*(deltaAlpha+S*HR0)
  result.m_HR += RH;
  if(&result!=this) 
    result.m_HR0 = m_HR0;
  result.m_c2Coeff = result.m_alpha;
  result.m_c2Coeff += result.m_Cjac*result.m_HR0;
  result.m_c2Coeff += result.m_Bjac*result.m_HR;

  if(sizeFactor!=0)
  {
    typename ScalarType::BoundType maxSizeR = 0., maxSizeR0 = 0.;
    for(i=0;i<m_dim;i++)
      for(j=0;j<m_dim;j++)
      {
        maxSizeR = capd::max(maxSizeR,diam(result.m_R[i][j]).rightBound());
        maxSizeR0 = capd::max(maxSizeR0, diam(result.m_R0[i][j]).rightBound());
      }

    if(maxSizeR>sizeFactor*maxSizeR0)
    {
      result.m_R0 = result.m_R + (Qtr * result.m_Cjac) * result.m_R0;
      result.m_HR0 = (Qtr * result.m_Cjac) * result.m_HR0;
      result.m_HR0 += result.m_HR;
      result.m_R.clear();
      result.m_HR.clear();
      result.m_Cjac = result.m_Bjac;
      result.m_Bjac = MatrixType::Identity(m_dim);
    }
  }
}

// -------------------------------------------------------------

template<typename MatrixType>
typename C2Rect2<MatrixType>::ScalarType C2Rect2<MatrixType>::size(void) const
{
  return capd::vectalg::size(m_x + m_C*m_r0 + m_B*m_r);
}

template<typename MatrixType>
std::string C2Rect2<MatrixType>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << "c2rect2:\n x=";
  descriptor << m_x << "\n B=";
  descriptor << m_B << "\n r=";
  descriptor << m_r << "\n D= ";
  descriptor << m_D << "\n Bjac= ";
  descriptor << m_Bjac << "\n R= ";
  descriptor << m_R << '\0';

  return descriptor.str();
}

template<typename MatrixT>
C2Rect2<MatrixT>::operator typename C2Rect2<MatrixT>::MatrixType() const
{
  return m_D + m_Bjac*m_R + m_Cjac*m_R0;
}

template<typename MatrixType>
C2Rect2<MatrixType>& C2Rect2<MatrixType>::operator=(const VectorType& x)
{
  if(m_dim!=x.dimension())
  {
    m_dim = x.dimension();
    m_r0 = VectorType(m_dim);
    m_r = VectorType(m_dim);
    m_R = MatrixType(m_dim,m_dim);
    m_R0 = MatrixType(m_dim,m_dim);
    m_c2Coeff = C2CoeffType(m_dim);
    m_alpha = C2CoeffType(m_dim);
    m_HR = C2CoeffType(m_dim);
    m_HR0 = C2CoeffType(m_dim);
  }
  m_x = x;
  split(m_x,m_r0);
  m_r.clear();

  m_Cjac = m_Bjac = m_D = m_B = m_C = MatrixType::Identity(m_dim);
  m_R.clear();
  m_R0.clear();

  m_c2Coeff.clear();
  m_alpha.clear();
  m_HR.clear();
  m_HR0.clear();

  return *this;
}

template<typename MatrixType>
C2Rect2<MatrixType>::~C2Rect2()
{
  delete m_Norm;
}

template<typename MatrixType>
inline const typename C2Rect2<MatrixType>::ScalarType& C2Rect2<MatrixType>::operator()(int i, int j, int c) const
{
  return m_c2Coeff(i,j,c);
}

template<typename MatrixType>
typename C2Rect2<MatrixType>::VectorType C2Rect2<MatrixType>::operator()(int j, int c) const
{
  VectorType result(m_dim);
  for(int i=0;i<m_dim;i++)
    result[i] = m_c2Coeff(i,j,c);
  return result;
}

template<typename MatrixType>
MatrixType C2Rect2<MatrixType>::operator()(int i)
{
  MatrixType result(m_dim,m_dim);
  int j,c;
  for(j=0;j<m_dim;j++)
    for(c=0;c<m_dim;c++)
      result[j][c] = m_c2Coeff(i,j,c);

  return result;
}

template<typename MatrixType>
C2Rect2<MatrixType>& C2Rect2<MatrixType>::operator=(const C2Rect2& s)
{
  m_x = s.m_x;
  m_B = s.m_B;
  m_r = s.m_r;
  m_C = s.m_C;
  m_r0= s.m_r0;

  m_D = s.m_D;
  m_Bjac = s.m_Bjac;
  m_R = s.m_R;
  m_Cjac = s.m_Cjac;
  m_R0 = s.m_R0;

  m_c2Coeff = s.m_c2Coeff;
  m_alpha = s.m_alpha;
  m_HR = s.m_HR;
  m_HR0 = s.m_HR0;

  sizeFactor = s.sizeFactor;

  delete m_Norm;
  m_Norm = s.m_Norm->clone();

  return *this;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C2RECT2_HPP_ 

/// @}
