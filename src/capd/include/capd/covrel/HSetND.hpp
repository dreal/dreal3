/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file HSetND.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_COVREL_HSETND_HPP_ 
#define _CAPD_COVREL_HSETND_HPP_ 

#include <stdexcept>
#include "capd/capd/minmax.h"
#include "capd/covrel/HSetND.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace covrel{

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::HSetND(
    const VectorType& A_C,
    const MatrixType& A_M,
    int A_d1, int A_d2,
    const VectorType& r
  ) : m_C(A_C),
     m_M(A_M),
     m_IC(m_C),
     m_d1(A_d1),
     m_d2(A_d2),
     m_r(r)
{
  if( A_C.dimension()!=A_M.numberOfRows() ||  A_C.dimension()!=A_M.numberOfColumns() )
  {
    throw std::runtime_error("HSetND constructor error: incorrect dimensions of vector or matrix");
  }
  if( m_d1+m_d2!=m_C.dimension() || m_d1<0 || m_d2<0 )
  {
    throw std::runtime_error("HSetND constructor error: incorrect number of unstable and stable directions");
  }
  int i,j;
  m_IM = IMatrixType(m_M.numberOfRows(),m_M.numberOfColumns());
  for(i=1;i<=m_C.dimension();i++)
    for(j=1;j<=m_C.dimension();j++)
      m_IM(i,j) = m_M(i,j);
  m_invIM = capd::matrixAlgorithms::gaussInverseMatrix(m_IM);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::HSetND(
    const IVectorType& A_C,
    const IMatrixType& A_M,
    int A_d1, int A_d2,
    const VectorType& r
  ) : m_IC(A_C), m_IM(A_M),
    m_d1(A_d1), m_d2(A_d2), m_r(r)
{
  if( A_C.dimension()!=A_M.numberOfRows() || A_C.dimension()!=A_M.numberOfColumns() )
  {
    throw std::runtime_error("HSetND constructor error: incorrect dimensions of vector or matrix");
  }
  if( m_d1+m_d2!=m_C.dimension() || m_d1<0 || m_d2<0 )
  {
    throw std::runtime_error("HSetND constructor error: incorrect number of unstable and stable directions");
  }

  int i,j;
  m_M = MatrixType(m_IM.numberOfRows(),m_IM.numberOfColumns());
  m_C = VectorType(m_IC.dimension());
  for(i=1;i<=m_C.dimension();i++)
  {
    m_C[i] = m_IC[i].mid().leftBound();
    for(j=1;j<=m_C.dimension();j++)
    {
      m_M(i,j) = m_IM(i,j).mid().leftBound();
    }
  }
  m_invIM = capd::matrixAlgorithms::gaussInverseMatrix(m_IM);
}

// ------------------- float version ---------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::outside(const VectorType& point) const
{
  VectorType x = capd::matrixAlgorithms::gauss(m_M,point-m_C);
  // we verify if x is outside ball of radius r in maximum norm
  int i=x.dimension();
  do{
    i--;
    if(capd::abs(x[i])>m_r[i])
      return true;
  }while(i);
  return false;
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::inside(const VectorType& point) const
{
  VectorType x = capd::matrixAlgorithms::gauss(m_M,point-m_C);
  // we verify if x is inside ball od radius r in maximum norm
  int i=x.dimension();
  do{
    i--;
    if(capd::abs(x[i])>= m_r[i])
      return false;
  }while(i);
  return true;
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::across(const VectorType& point) const
{
  // we verify if x is inside a horizontal strip, i.e.
  //   x\in B_n (open ball)
  // or
  //   x projected onto unstable directions is outside ball of rasius r
  // notice, that d1 or d2 may be equal to zero

  VectorType x = capd::matrixAlgorithms::gauss(m_M,point-m_C);

  // return true if any unstable coordinate is greater than m_r
  int i=0;
  while(i!=m_d1)
  {
    if(capd::abs(x[i])> m_r[i])
      return true;
    i++;
  }
  // else all stable coordinates must be lower than m_r
  while(i!=x.dimension())
  {
    if(capd::abs(x[i])>= m_r[i])
      return false;
    i++;
  }
  return true;
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::mapaway(const VectorType& point) const
{
  // we verify if x projected onto unstable directions is outside ball of radius r
  // notice, that d1 or d2 may be equal to zero
  if(m_d1==0)
    return true;

  VectorType x = capd::matrixAlgorithms::gauss(m_M,point-m_C);
  int i=0;
  while(i!=m_d1)
  {
    if(capd::abs(x[i])>m_r[i])
      return true;
    i++;
  }
  return false;
}


// ------------------------ interval version ---------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::outside(const IVectorType& point) const
{
  IVectorType x = capd::matrixAlgorithms::gauss(m_IM,point-m_IC);
  return checkOutside(x);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::inside(const IVectorType& point) const
{
  IVectorType x = capd::matrixAlgorithms::gauss(m_IM,point-m_IC);
  return checkInside(x);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::across(const IVectorType& point) const
{
  IVectorType x = capd::matrixAlgorithms::gauss(m_IM,point-m_IC);
  return checkAcross(x);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::mapaway(const IVectorType& point) const
{
  IVectorType x = capd::matrixAlgorithms::gauss(m_IM,point-m_IC);
  return checkMapaway(x);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
template <typename SetType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::outside(
      const SetType & A_set) const
{
  IVectorType x = A_set.affineTransformation(m_invIM,m_IC);
  return checkOutside(x);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
template <typename SetType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::inside(
      const SetType & A_set) const
{
  IVectorType x = A_set.affineTransformation(m_invIM,m_IC);
  return checkInside(x);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
template <typename SetType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::across(
      const SetType & A_set) const
{
  IVectorType x = A_set.affineTransformation(m_invIM,m_IC);
  return checkAcross(x);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
template <typename SetType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::mapaway(
      const SetType & A_set) const
{
  IVectorType x = A_set.affineTransformation(m_invIM,m_IC);
  return checkMapaway(x);
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::checkOutside(const IVectorType& x) const
{
  // we verify if x is outside the box r
  int i=x.dimension();
  do{
    i--;
    if(capd::abs(x[i])>m_r[i])
      return true;
  }while(i);
  return false;
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::checkInside(const IVectorType& x) const
{
  // we verify if x is inside box r
  int i=x.dimension();
  do{
    i--;
    if(! (capd::abs(x[i])< m_r[i]) )
      return false;
  }while(i);
  return true;
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::checkAcross(const IVectorType& x) const
{
  // we verify if x is inside a horizontal strip, i.e.
  //   x\in box r
  // or
  //   x projected onto unstable directions is outside the box r
  // notice, that d1 or d2 may be equal to zero

  // return true if any unstable coordinate is greater than r
   
  int i=0;
  while(i!=m_d1)
  {
    if(capd::abs(x[i])>m_r[i])
      return true;
    i++;
  }
  // else all stable coordinates must be lower than r
  while(i!=x.dimension())
  {
    if(! (capd::abs(x[i])<m_r[i]) )
      return false;
    i++;
  }
  return true;
}

// ---------------------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
bool HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::checkMapaway(const IVectorType& x) const
{
  // we verify if x projected onto unstable directions is outside unit ball
  // notice, that d1 or d2 may be equal to zero
  if(m_d1==0)
    return true;

  int i=0;
  while(i!=m_d1)
  {
    if(capd::abs(x[i])>m_r[i])
      return true;
    i++;
  }
  return false;
}

// ---------------------------------------------------------------

}} //namespace capd::covrel

#endif // _CAPD_COVREL_HSETND_HPP_ 

/// @}

