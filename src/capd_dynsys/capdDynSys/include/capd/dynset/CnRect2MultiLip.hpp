/////////////////////////////////////////////////////////////////////////////
/// @file CnRect2MultiLip.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_CNRECT2MULTILIP_HPP_ 
#define _CAPD_DYNSET_CNRECT2MULTILIP_HPP_ 

#include "capd/dynset/CnRect2MultiLip.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

// ----------------------------- CONSTRUCTORS --------------------------------

template<typename MatrixT>
CnRect2MultiLip<MatrixT>::CnRect2MultiLip(const VectorType& x,  const NormType& a_norm, int rank, double sizeFactor)
  : m_x(x.dimension(),rank),
    m_r(x.dimension(),rank),
    m_currentSet(x.dimension(),rank),
    m_B(MatrixT::Identity(x.dimension())),
    m_C(MatrixT::Identity(x.dimension())),
    m_Bjac(MatrixT::Identity(x.dimension())),
    m_sizeFactor(sizeFactor),
    m_norm(a_norm.clone())
{
  m_currentSet() = x;
  m_x() = x;
  m_r0.push_back(CnCoeffType(x.dimension(),rank));
  typename MatrixT::RefColumnVectorType refX = m_x();
  typename MatrixT::RefColumnVectorType refR0 = m_r0[0]();
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
CnRect2MultiLip<MatrixT>::CnRect2MultiLip(const VectorType& x, const MatrixType& C, const VectorType& r0, const NormType& a_norm, int rank, double sizeFactor)
  : m_x(x.dimension(),rank),
    m_r(x.dimension(),rank),
    m_currentSet(x.dimension(),rank),
    m_B(MatrixT::Identity(x.dimension())),
    m_C(C),
    m_Bjac(MatrixT::Identity(x.dimension())),
    m_sizeFactor(sizeFactor),
    m_norm(a_norm.clone())
{
  m_x() = x;
  m_r0[0]() = r0;
  VectorType v = x + C*r0;
  m_currentSet() = v;
  m_r0.push_back(CnCoeffType(x.dimension(),rank));

 // typename MatrixT::RefColumnVectorType refX = m_x();
  typename MatrixT::RefColumnVectorType refR0 = m_r0[0]();
  typename MatrixT::RefColumnVectorType refR = m_r();
  if(!subset(refR,refR0))
  {
    VectorType copyX = x;
    VectorType copyR0 = r0;
    VectorType centerR0(x.dimension());
    split(centerR0,copyR0);
    copyX += m_C*centerR0;
    m_r0[0]() = copyR0;
    split(copyX,copyR0);
    m_r() = copyR0;
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
CnRect2MultiLip<MatrixT>::CnRect2MultiLip(const CnRect2MultiLip& a_set)
  : m_x(a_set.m_x),
    m_r(a_set.m_r),
    m_currentSet(a_set.m_currentSet),
    m_r0(a_set.m_r0),
    m_B(a_set.m_B),
    m_C(a_set.m_C),
    m_Bjac(a_set.m_Bjac),
    m_Cjac(a_set.m_Cjac),
    m_sizeFactor(a_set.m_sizeFactor),
    m_norm(a_set.m_norm->clone())
{}

// ---------------------------- operators -------------------------------------

template<typename MatrixT>
CnRect2MultiLip<MatrixT>& CnRect2MultiLip<MatrixT>::operator=(const CnRect2MultiLip& s)
{
  if(this!=&s) 
  {
    m_x = s.m_x;
    m_r = s.m_r;
    m_r0 = s.m_r0;
    m_currentSet = s.m_currentSet;
    m_B = s.m_B;
    m_C = s.m_C;
    m_Bjac = s.m_Bjac;
    m_Cjac = s.m_Cjac;
    m_sizeFactor = s.m_sizeFactor;
    delete m_norm;
    m_norm = (s.m_norm)->clone();
  }
  return *this;
}

// ----------------------------------------------------------------------------

template<typename MatrixT>
CnRect2MultiLip<MatrixT>& CnRect2MultiLip<MatrixT>::operator=(const VectorType& v)
{
  if(v.dimension()!=getDimension())
    throw std::runtime_error("CnRect2MultiLip::operator=(Vector) - incorrect dimensions");
  VectorType temp(getDimension());
  VectorType y = v;
  split(y,temp);
  m_x.clear();
  m_r.clear();
  m_r0.clear();
  m_currentSet.clear();
  m_B = m_C = m_Bjac = MatrixType::Identity(getDimension());
  m_Cjac.clear();
  m_r0.push_back(CnCoeffType(m_x.dimension(),getRank()));

  m_x() = y;
  m_r0[0]() = temp;
  m_currentSet() = v;
  if(getRank()>0)
  {
    for(int i=0;i<getDimension();++i)
      m_currentSet(i,i) = ScalarType(1);
  }
  return *this;
}

// ------------------------------ move ---------------------------------------

template<typename MatrixT>
void CnRect2MultiLip<MatrixT>::move(capd::dynsys::CnDynSys<MatrixType>& cndynsys, CnRect2MultiLip& result) const
{
  int dimension = getDimension();
  VectorType xx(*this);
  VectorType x(m_x), s(dimension);
  MatrixType S(dimension,dimension);
  CnCoeffType Phi(dimension,getRank()),
              Rem(dimension,getRank());

  cndynsys.cnPhi(xx,Phi);
  // try to correct DPhi by using of second order derivatives and the mean value theorem
  if(getRank()>1)
  {
    MatrixType M = cndynsys.JacPhi(x);
    VectorType deltaX = xx-x;
    for(int i=0;i<dimension;++i)
      for(int j=0;j<dimension;++j)
      {
        ScalarType ref = M(i+1,j+1);
        for(int k=0;k<dimension;++k)
          ref += Phi(i,j,k)*deltaX[k];
        if(!intersection(Phi(i,j),ref,Phi(i,j)))
          throw std::runtime_error("CnRect2MultiLip::move - empty intersection of D\\phi computed by means of two different ways");
      }
  }
  cndynsys.cnRemainder(xx,*m_norm,Rem);

// C^0 part
  VectorType y = cndynsys.Phi(x);
  y += VectorType(Rem());
  MatrixType A = MatrixType(Phi);
  result.m_C = A*m_C;
  MatrixType D = A*m_B;
  result.m_currentSet() = y + result.m_C*m_r0[0]() + D*m_r();

  split(y,s);
  split(result.m_C,S);

  s += S * m_r0[0]();
  MatrixType Q = capd::vectalg::midMatrix(D);
  capd::matrixAlgorithms::orthonormalize(Q);
  MatrixType Qtr = Transpose(Q);
  result.m_x() = y;
  result.m_r() = (Qtr*D)*m_r() + Qtr*s;
  result.m_B = Q;
  if(this!=&result)
  {
    result.m_r0.resize(m_r0.size());
    result.m_Cjac.resize(m_Cjac.size());
    result.m_r0[0]() = m_r0[0]();
  }
//   Phi += Rem
  typename CnCoeffType::iterator b=Phi.begin(), e=Phi.end(), j=Rem.begin();
  while(b!=e)
  {
    (*b) += (*j);
    ++b;
    ++j;
  }

  A = MatrixType(Phi); // in fact A += Rem
  std::vector<MatrixType> W(m_Cjac.size()), T(m_Cjac.size(),MatrixType(getDimension(),getDimension()));
  unsigned int t;
  for(t=0;t<m_Cjac.size();++t)
  {
    W[t] = result.m_Cjac[t] = A * m_Cjac[t];
    split(result.m_Cjac[t],T[t]);
  }
  MatrixType X = A*m_Bjac;
  Q = capd::vectalg::midMatrix(X);
  capd::matrixAlgorithms::orthonormalize(Q);
  Qtr = Transpose(Q);
  MatrixType J=Qtr*X;

// C^1 -- C^r part
  // Rem is now unnecessary. We will store in Rem a nonlinear part of composition
  if(getRank()>0)
  {
    substitutionPowerSeries(Phi,m_currentSet,Rem,true);
  }

  for(int p=1;p<=getRank();++p)
  {
    Multipointer mp = m_x.first(p);
    do{
      VectorType temp = Rem(mp) + A*m_x(mp);
      result.m_currentSet(mp) = temp + X*m_r(mp);
      y = temp;
      for(t=0;t<m_Cjac.size();++t)
      {
        result.m_currentSet(mp) += W[t]*m_r0[t](mp);
        y += T[t]*m_r0[t](mp);
      }
      split(y,s);
      VectorType r = (Qtr*s)  + (J*m_r(mp));
      result.m_r(mp) = r;
      result.m_x(mp) = y;
      if(&result!=this)
        for(t=0;t<m_Cjac.
        /// @}
size();++t)
          result.m_r0[t](mp) = m_r0[t](mp);
    }while(m_x.next(mp));
  }

  if(m_sizeFactor!=0)
  {
    unsigned lastInd = result.m_r0.size()-1;
    if( capd::vectalg::size(result.m_r()) > m_sizeFactor * capd::vectalg::size(result.m_r0[0]()))
    {
      result.m_r0[0]() = result.m_r() +  ((Qtr * result.m_C) * result.m_r0[0]());
      result.m_C = result.m_B;
      result.m_B = MatrixType::Identity(dimension);
      result.m_r().clear();
    /*}
    
    typename ScalarType::BoundType maxSizeR = 0., maxSizeR0 = 0.;//, quotient=0.;
    for(int p=1;p<=getRank();++p)
    {
      Multipointer mp = m_x.first(p);
      do{
        maxSizeR = capd::max(maxSizeR,::size(result.m_r(mp)).rightBound());
        maxSizeR0 = capd::max(maxSizeR0,::size(result.currentSet()(mp)).rightBound());
      }while(m_x.next(mp));
    }
    if(maxSizeR > .8* maxSizeR0)
    {*/
      if(result.m_Cjac.size())
        result.m_r0.push_back(CnCoeffType(getDimension(),getRank()));
      result.m_Cjac.push_back(result.m_Bjac);
      split(result.m_Cjac[lastInd],result.m_Bjac);
      for(int p=1;p<=getRank();++p)
      {
        Multipointer mp = m_x.first(p);
        do{
          result.m_r0[lastInd](mp) = result.m_r(mp);
          result.m_r(mp) = result.m_Bjac * result.m_r(mp);
        }while(m_x.next(mp));
      }
      result.m_Bjac = MatrixType::Identity(dimension);
     std::cout << "ilosc macierzy: " << result.m_r0.size() << "\n";
    }
  }
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_CNRECT2MULTILIP_HPP_ 
