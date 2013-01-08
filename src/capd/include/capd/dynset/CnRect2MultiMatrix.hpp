/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnRect2MultiMatrix.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_CNRECT2MULTIMATRIX_HPP_ 
#define _CAPD_DYNSET_CNRECT2MULTIMATRIX_HPP_ 

#include "capd/dynset/CnRect2MultiMatrix.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

// ----------------------------- CONSTRUCTORS --------------------------------

template<typename MatrixT>
CnRect2MultiMatrix<MatrixT>::CnRect2MultiMatrix(const VectorType& x,  const NormType& a_norm, int rank, double sizeFactor)
  : m_x(x.dimension(),rank),
    m_r(x.dimension(),rank),
    m_r0(x.dimension(),rank),
    m_currentSet(x.dimension(),rank),
    m_B(x.dimension(),rank,MatrixT::Identity(x.dimension())),
    m_C(x.dimension(),rank,MatrixT::Identity(x.dimension())),
    m_sizeFactor(sizeFactor),
    m_norm(a_norm.clone())
{
  m_currentSet() = x;
  m_x() = x;
  typename MatrixT::RefColumnVectorType refX = m_x();
  typename MatrixT::RefColumnVectorType refR0 = m_r0();
  split(refX,refR0);

// initial condition for variational part is an Identity matrix
  if(getRank()>0)
  {
    for(int i=0;i<getDimension();++i)
      m_currentSet(i,i) = m_x(i,i) = ScalarType(1);
  }
}

// ----------------------------------------------------------------------------

template<typename MatrixT>
CnRect2MultiMatrix<MatrixT>::CnRect2MultiMatrix(const VectorType& x, const MatrixType& C, const VectorType& r0, const NormType& a_norm, int rank, double sizeFactor)
  : m_x(x.dimension(),rank),
    m_r(x.dimension(),rank),
    m_r0(x.dimension(),rank),
    m_currentSet(x.dimension(),rank),
    m_B(x.dimension(),rank,MatrixT::Identity(x.dimension())),
    m_C(x.dimension(),rank,MatrixT::Identity(x.dimension())),
    m_sizeFactor(sizeFactor),
    m_norm(a_norm.clone())
{
  m_x() = x;
  VectorType v = x + C*r0;
  m_currentSet() = v;
  m_C(0) = C;

  typename MatrixT::RefColumnVectorType refX = m_x();
  typename MatrixT::RefColumnVectorType refR0 = m_r0();
  typename MatrixT::RefColumnVectorType refR = m_r();
  if(!subset(refR,refR0))
  {
    VectorType copyX = x;
    VectorType centerR0 = r0;
    VectorType deltaR0(x.dimension());
    split(centerR0,deltaR0);
    copyX += C*centerR0;
    VectorType deltaX(x.dimension());
    split(copyX,deltaX);
    refR = deltaX;
    refX = copyX;
  }

// initial condition for variational part is an Identity matrix
  if(getRank()>0)
  {
    for(int i=0;i<getDimension();++i)
      m_currentSet(i,i) = m_x(i,i) = ScalarType(1);
  }
}

// ----------------------------------------------------------------------------

template<typename MatrixT>
CnRect2MultiMatrix<MatrixT>::CnRect2MultiMatrix(const CnRect2MultiMatrix& a_set)
  : m_x(a_set.m_x),
    m_r(a_set.m_r),
    m_r0(a_set.m_r0),
    m_currentSet(a_set.m_currentSet),
    m_B(a_set.m_B),
    m_C(a_set.m_C),
    m_sizeFactor(a_set.m_sizeFactor),
    m_norm(a_set.m_norm->clone())
{}

// ---------------------------- operators -------------------------------------

template<typename MatrixT>
CnRect2MultiMatrix<MatrixT>& CnRect2MultiMatrix<MatrixT>::operator=(const CnRect2MultiMatrix& s)
{
  if(this!=&s) 
  {
    m_x = s.m_x;
    m_r = s.m_r;
    m_r0 = s.m_r0;
    m_currentSet = s.m_currentSet;
    m_B = s.m_B;
    m_C = s.m_C;
    m_sizeFactor = s.m_sizeFactor;
    delete m_norm;
    m_norm = (s.m_norm)->clone();
  }
  return *this;
}

// ----------------------------------------------------------------------------

template<typename MatrixT>
CnRect2MultiMatrix<MatrixT>& CnRect2MultiMatrix<MatrixT>::operator=(const VectorType& v)
{
  if(v.dimension()!=getDimension())
    throw std::runtime_error("CnRect2MultiMatrix::operator=(Vector) - incorrect dimensions");
  VectorType y = v;
  VectorType deltaR0(v.dimension());
  split(y,deltaR0);
  m_x.clear();
  m_r.clear();
  m_currentSet.clear();
  m_B = MatrixType::Identity(getDimension());
  m_C = MatrixType::Identity(getDimension());
  m_x() = y;
  m_currentSet() = v;
  m_r0() = deltaR0;
  if(getRank()>0)
  {
    for(int i=0;i<getDimension();++i)
      m_currentSet(i,i) = ScalarType(1);
  }
  return *this;
}


template<typename MatrixT>
void CnRect2MultiMatrix<MatrixT>::computeProduct(
            const MatrixType& Qtr,
            const CnCoeffType& H, 
            const MatrixType& B, 
            const MatrixType& C,
            const VectorType& deltaX,
            MatrixType& Qtr_H_B,
            MatrixType& Qtr_H_C
    )
{
  int d = B.numberOfRows();

  Qtr_H_B.clear();
  Qtr_H_C.clear();

  for(int s=0;s<d;++s)
  {
    for(int r=0;r<d;++r)
    {
      for(int k=0;k<d;++k)
      {
        ScalarType Bfac(0.);
        ScalarType Cfac(0.);
        for(int j=0;j<d;++j)
        {
          ScalarType temp(0.);
          for(int i=0;i<d;++i)
          {
            temp += H(i,j,k)*Qtr(r+1,i+1);
          }
          Bfac += B(j+1,s+1)*temp;
          Cfac += C(j+1,s+1)*temp;
        }
        Qtr_H_B(r+1,s+1) += Bfac*deltaX[k];
        Qtr_H_C(r+1,s+1) += Cfac*deltaX[k];
      }
    }
  }
}

template<typename MatrixT>
void CnRect2MultiMatrix<MatrixT>::computeProduct(
            const MatrixType& Qtr,
            const CnCoeffType& H, 
            const VectorType& x, 
            const VectorType& deltaX,
            VectorType& Qtr_H_x
    )
{
  int d = x.dimension();

  Qtr_H_x.clear();

  for(int r=0;r<d;++r)
  {
    for(int k=0;k<d;++k)
    {
      ScalarType Xfac(0.);
      for(int j=0;j<d;++j)
      {
        ScalarType temp(0.);
        for(int i=0;i<d;++i)
        {
          temp += H(i,j,k)*Qtr(r+1,i+1);
        }
        Xfac += x[j]*temp;
      }
      Qtr_H_x[r] += Xfac*deltaX[k];
    }
  }
}

// ------------------------------ move ---------------------------------------

template<typename MatrixT>
void CnRect2MultiMatrix<MatrixT>::move(capd::dynsys::CnDynSys<MatrixType>& cndynsys, CnRect2MultiMatrix& result) const
{
  int dimension = getDimension();
  VectorType xx(*this);
  VectorType x(m_x), s(dimension);
  MatrixType S(dimension,dimension);
  CnCoeffType Phi(dimension,getRank()),
              Rem(dimension,getRank());

  cndynsys.cnPhi(xx,Phi);
  // try to correct DPhi by using of second order derivatives and the mean value theorem
//  if(getRank()>1)
//  {
    MatrixType M = cndynsys.JacPhi(x);
    VectorType deltaX = xx-x;
    for(int i=0;i<dimension;++i)
      for(int j=0;j<dimension;++j)
      {
        ScalarType ref = M(i+1,j+1);
        for(int k=0;k<dimension;++k)
          ref += Phi(i,j,k)*deltaX[k];
        if(!intersection(Phi(i,j),ref,Phi(i,j)))
          throw std::runtime_error("CnRect2MultiMatrix::move - empty intersection of D\\phi computed by means of two different ways");
      }
//  }
  cndynsys.cnRemainder(xx,*m_norm,Rem);

// C^0 part
  VectorType y = cndynsys.Phi(x);
  y += VectorType(Rem());
  MatrixType A = MatrixType(Phi);
  result.m_C(0) = A*m_C(0);
  MatrixType D = A*m_B(0);
  result.m_currentSet() = y + result.m_C(0)*m_r0() + D*m_r();

  split(y,s);
  split(result.m_C(0),S);

  s += S * m_r0();
  MatrixType Q = capd::vectalg::midMatrix(D);
  capd::matrixAlgorithms::orthonormalize(Q,m_r());
  MatrixType Qtr = Transpose(Q);
  result.m_x() = y;
  result.m_r() = (Qtr*D)*m_r() + Qtr*s;
  result.m_B(0) = Q;
  if(this!=&result)
  {
    result.m_r0 = m_r0;
  }

  if(m_sizeFactor!=0)
  {
    if( capd::vectalg::size(result.m_r()) > m_sizeFactor * capd::vectalg::size(result.m_r0()))
    {
      result.m_r0() = result.m_r() +  ((Qtr * result.m_C(0)) * result.m_r0());
      result.m_C(0) = result.m_B(0);
      result.m_B(0) = MatrixType::Identity(dimension);
      result.m_r().clear();
    }
  }

//   Phi += Rem
  typename CnCoeffType::iterator b=Phi.begin(), e=Phi.end(), j=Rem.begin();
  while(b!=e)
  {
    (*b) += (*j);
    ++b;
    ++j;
  }

  //M += MatrixType(Rem);
  A = MatrixType(Phi);
// C^1 -- C^r part
  // Rem is now unnecessary. We will store in Rem a nonlinear part of composition
  if(getRank()>0)
  {
    substitutionPowerSeries(Phi,m_currentSet,Rem,true);
  }
  
  VectorType empty(dimension);
  MatrixType Qtr_H_C(dimension,dimension);
  MatrixType Qtr_H_B(dimension,dimension);

  for(int p=1;p<=getRank();++p)
  {
    Multipointer mp = m_x.first(p);
    do{
      y = A*m_x(mp) + Rem(mp);

      result.m_currentSet(mp) = y + (A*m_B(0,mp))*m_r(mp) + (A*m_C(0,mp))*m_r0(mp);

      D = M*m_B(0,mp);
      mid(D,Q);
      capd::matrixAlgorithms::orthonormalize(Q,m_r(mp));
      Qtr = Transpose(Q);

      computeProduct(Qtr,Phi,m_B(0,mp),m_C(0,mp),deltaX,Qtr_H_B,Qtr_H_C);
      Qtr_H_B += Qtr*D;

      result.m_C(0,mp) = M*m_C(0,mp);
      split(result.m_C(0,mp),S);


      computeProduct(Qtr,Phi,m_x(mp),deltaX,xx);

      y = M*m_x(mp) + Rem(mp);
      split(y,s);
      result.m_x(mp) = y;
      result.m_r(mp) = xx + Qtr_H_B*m_r(mp) + (Qtr_H_C+Qtr*S)*m_r0(mp) + Qtr*s;
      result.m_B(0,mp) = Q;

      if(m_sizeFactor!=0)
      {
        ScalarType sizeR = capd::vectalg::size(result.m_r(mp));
        
        if( sizeR > m_sizeFactor * capd::vectalg::size((Qtr*result.m_C(0,mp))*result.m_r0(mp)))
        {
          result.m_r0(mp) = result.m_r(mp) + (Qtr*result.m_C(0,mp))*result.m_r0(mp);
          result.m_C(0,mp) = result.m_B(0,mp);
          result.m_r(mp).clear();
          result.m_B(0,mp) = MatrixType::Identity(dimension);
        }
      }

    }while(m_x.next(mp));
  }
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_CNRECT2MULTIMATRIX_HPP_ 

/// @}
