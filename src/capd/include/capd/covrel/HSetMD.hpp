/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file HSetMD.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_COVREL_HSETMD_HPP_
#define _CAPD_COVREL_HSETMD_HPP_

#include <stdexcept>
#include "capd/capd/minmax.h"
#include "capd/covrel/HSetMD.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace covrel{

/// Constructor of HSet from approximation
///
/// HSet is represented as center + Base * B(0,r)
/// uDim denotes a number of unstable directions
/// sDim denotes a number of stable directions
/// It sets both nonrigorous and rigorous fields
template<typename MatrixType, typename IMatrixType>
HSetMD<MatrixType, IMatrixType>::HSetMD(
    const VectorType& center,
    const MatrixType& Base,
    int uDim, int sDim,
    const VectorType & r
  ) : m_x(center),
     m_B(Base),
     m_uDim(uDim),
     m_sDim(sDim),
     m_r(r)
{
  if( center.dimension()!=Base.numberOfRows() ||  center.dimension()!=Base.numberOfColumns() )
  {
    throw std::runtime_error("HSetMD constructor error: incorrect dimensions of vector or matrix");
  }
  if( m_uDim+m_sDim!=m_x.dimension() || m_uDim<0 || m_sDim<0 )
  {
    throw std::runtime_error("HSetMD constructor error: incorrect number of unstable and stable directions");
  }
  int i,j;
  m_Ix =IVectorType(center.dimension());
  for(int i=0; i<center.dimension(); ++i)
    m_Ix[i] = ScalarType(center[i]);
  m_IB = IMatrixType(m_B.numberOfRows(),m_B.numberOfColumns());
  for(i=1;i<=m_x.dimension();i++)
    for(j=1;j<=m_x.dimension();j++)
      m_IB(i,j) = m_B(i,j);
  m_invIB = capd::matrixAlgorithms::gaussInverseMatrix(m_IB);
}
/// Constructor of HSet from rigorous data
///
/// HSet is represented as center + Base * B(0,r)
/// uDim denotes a number of unstable directions
/// sDim denotes a number of stable directions
/// It sets both nonrigorous and rigorous fields
template<typename MatrixType, typename IMatrixType>
HSetMD<MatrixType, IMatrixType>::HSetMD(
    const IVectorType& center,
    const IMatrixType& Base,
    int uDim, int sDim,
    const VectorType& r
  ) : m_Ix(center), m_IB(Base),
    m_uDim(uDim), m_sDim(sDim), m_r(r)
{

  if( center.dimension()!=Base.numberOfRows() || center.dimension()!=Base.numberOfColumns() )
  {
    throw std::runtime_error("HSetMD constructor error: incorrect dimensions of vector or matrix");
  }
  if( m_uDim+m_sDim!=m_Ix.dimension() || m_uDim<0 || m_sDim<0 )
  {
    throw std::runtime_error("HSetMD constructor error: incorrect number of unstable and stable directions");
  }

  int i,j;
  m_B = MatrixType(m_IB.numberOfRows(),m_IB.numberOfColumns());
  m_x = VectorType(m_Ix.dimension());
  for(i=1;i<=m_x.dimension();i++)
  {
    m_x[i-1] = m_Ix[i-1].mid().leftBound();
    for(j=1;j<=m_x.dimension();j++)
    {
      m_B(i,j) = m_IB(i,j).mid().leftBound();
    }
  }
  m_invIB = capd::matrixAlgorithms::gaussInverseMatrix(m_IB);
}

// ------------------- float version ---------------------
template<typename MatrixType, typename IMatrixType>
typename HSetMD<MatrixType, IMatrixType>::VectorType HSetMD<MatrixType, IMatrixType>::
transformToHSetCoordinates(const VectorType & point) const {
      return capd::matrixAlgorithms::gauss(m_B, point - m_x);
}


template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::outside(const VectorType& point) const
{
  VectorType x = capd::matrixAlgorithms::gauss(m_B,point-m_x);
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

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::inside(const VectorType& point) const
{
  VectorType x = capd::matrixAlgorithms::gauss(m_B,point-m_x);
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

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::across(const VectorType& point) const
{
  // we verify if x is inside a horizontal strip, i.e.
  //   x\in B_n (open ball)
  // or
  //   x projected onto unstable directions is outside ball of rasius r
  // notice, that d1 or d2 may be equal to zero

  VectorType x = capd::matrixAlgorithms::gauss(m_B,point-m_x);

  // return true if any unstable coordinate is greater than m_r
  int i=0;
  while(i!=m_uDim)
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

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::mapaway(const VectorType& point) const
{
  // we verify if x projected onto unstable directions is outside ball of radius r
  // notice, that d1 or d2 may be equal to zero
  if(m_uDim==0)
    return true;

  VectorType x = capd::matrixAlgorithms::gauss(m_B,point-m_x);
  int i=0;
  while(i!=m_uDim)
  {
    if(capd::abs(x[i])>m_r[i])
      return true;
    i++;
  }
  return false;
}


// ------------------------ interval version ---------------------/
template<typename MatrixType, typename IMatrixType>
typename HSetMD<MatrixType, IMatrixType>::IVectorType  HSetMD<MatrixType, IMatrixType>::transformToHSetCoordinates(
    const IVectorType & point
) const {
  return capd::matrixAlgorithms::gauss(m_IB,point-m_Ix);
}

// ---------------------------------------------------------------
template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::outside(const IVectorType& point) const
{
  return checkOutside(transformToHSetCoordinates(point));
}

// ---------------------------------------------------------------

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::inside(const IVectorType& point) const
{
  return checkInside(transformToHSetCoordinates(point));
}

// ---------------------------------------------------------------

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::across(const IVectorType& point) const
{
  return checkAcross(transformToHSetCoordinates(point));
}

// ---------------------------------------------------------------

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::mapaway(const IVectorType& point) const
{
  return checkMapaway(transformToHSetCoordinates(point));
}

// ---------------------------------------------------------------

template<typename MatrixType, typename IMatrixType>
template <typename SetType>
bool HSetMD<MatrixType, IMatrixType>::outside(
      const SetType & A_set) const
{
  IVectorType x = A_set.affineTransformation(m_invIB,m_Ix);
  return checkOutside(x);
}

// ---------------------------------------------------------------

template<typename MatrixType, typename IMatrixType>
template <typename SetType>
bool HSetMD<MatrixType, IMatrixType>::inside(
      const SetType & A_set) const
{
  IVectorType x = A_set.affineTransformation(m_invIB,m_Ix);
  return checkInside(x);
}

// ---------------------------------------------------------------

template<typename MatrixType, typename IMatrixType>
template <typename SetType>
bool HSetMD<MatrixType, IMatrixType>::across(
      const SetType & A_set) const
{
  IVectorType x = A_set.affineTransformation(m_invIB,m_Ix);
  return checkAcross(x);
}

// ---------------------------------------------------------------

template<typename MatrixType, typename IMatrixType>
template <typename SetType>
bool HSetMD<MatrixType, IMatrixType>::mapaway(
      const SetType & A_set) const
{
  IVectorType x = A_set.affineTransformation(m_invIB,m_Ix);
  return checkMapaway(x);
}

// ---------------------------------------------------------------

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::checkOutside(const IVectorType& x) const
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

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::checkInside(const IVectorType& x) const
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

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::checkAcross(const IVectorType& x) const
{
  // we verify if x is inside a horizontal strip, i.e.
  //   x\in box r
  // or
  //   x projected onto unstable directions is outside the box r
  // notice, that d1 or d2 may be equal to zero

  // return true if any unstable coordinate is greater than r

  int i=0;
  while(i!=m_uDim)
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

template<typename MatrixType, typename IMatrixType>
bool HSetMD<MatrixType, IMatrixType>::checkMapaway(const IVectorType& x) const
{
  // we verify if x projected onto unstable directions is outside unit ball
  // notice, that d1 or d2 may be equal to zero
  if(m_uDim==0)
    return true;

  int i=0;
  while(i!=m_uDim)
  {
    if(capd::abs(x[i])>m_r[i])
      return true;
    i++;
  }
  return false;
}

// ---------------------------------------------------------------
template<typename MatrixType, typename IMatrixType>
std::string  HSetMD<MatrixType, IMatrixType>::show(void) const{
   return std::string("HSetMD : ")+showInfo();
}

template<typename MatrixType, typename IMatrixType>
std::string  HSetMD<MatrixType, IMatrixType>::showInfo(void) const
{
  std::ostringstream descriptor;
  descriptor << "\nuDim=" << m_uDim << "    sDim=" << m_sDim;
  descriptor << "\nx=" << m_Ix << "\n B=";
  descriptor << m_IB << "\n r=";
  descriptor << m_r << " ";
  return descriptor.str();
}
}} //namespace capd::covrel

#endif // _CAPD_COVREL_HSETMD_HPP_

/// @}

