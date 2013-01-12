/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file HSetND.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_COVREL_HSETND_H_ 
#define _CAPD_COVREL_HSETND_H_ 

#include <vector>
#include <stdexcept>
#include "capd/covrel/HSet.h"
#include "capd/dynset/C0Set.h"

namespace capd{
namespace covrel{

  /**
   This class provides a h-set in an arbitrary dimension
*/
template<typename VectorT, typename IVectorT, typename MatrixT, typename IMatrixT>
class HSetND : public HSet <VectorT,IVectorT> {
public:
  typedef typename IVectorT::ScalarType ScalarType;
  typedef typename VectorT::ScalarType BoundType;
  typedef VectorT VectorType;
  typedef IVectorT IVectorType;
  typedef MatrixT MatrixType;
  typedef IMatrixT IMatrixType;
  
  // we assume that the set is represented as A_Center + A_M *B(0,r)
  // d1 denotes a number of unstable directions
  // d2 denotes a number of stable directions
  HSetND(){}
  HSetND(const VectorType& A_Center, const MatrixType& A_M, int A_d1, int A_d2, const VectorType& r);
  HSetND(const IVectorType &A_Center, const IMatrixType &A_M, int A_d1, int A_d2, const VectorType& r);
  ~HSetND(){}

// double versions
  bool outside(const VectorType& point) const;
  bool inside (const VectorType& point) const;
  bool across (const VectorType& point) const;
  bool mapaway(const VectorType& point) const;

// interval versions
  bool outside(const IVectorType& point) const;
  bool inside (const IVectorType& point) const;
  bool across (const IVectorType& point) const;
  bool mapaway(const IVectorType& point) const;

// if we have a special represenation of a point
  template <typename SetType>
  bool outside(const SetType & A_set) const;
  template <typename SetType>
  bool inside (const SetType & A_set) const;
  template <typename SetType>
  bool across (const SetType & A_set) const;
  template <typename SetType>
  bool mapaway(const SetType & A_set) const;

  // this procedure creates a grid of a wall of h-set
  // in the following form: G.center[i] + G.C * G.r
  // d is a vector of indices of coordinates if the set is embeded in higher dimension
  // sign = 0 says that the grid should cover both walls pointed by direction 'dir'
  // sign = 1 or -1 says that only one wall will be covered
  template<typename IMatrix>
  GridSet<IMatrix>& gridWall( GridSet<IMatrix>& G,
                              const std::vector<int>& grid,
                              const std::vector<int>& d,
                              int totalDimension,
                              int dir, int sign=0
                            ) const;


  // this procedure creates a grid of the whole h-set
  // in the following form: G.center[i] + G.C * G.r
  // d is a vector of indices of coordinates if the set is embeded in higher dimension
  template<typename IMatrix>
  GridSet<IMatrix>& gridSet( GridSet<IMatrix>& G,
                             const std::vector<int>& grid, 
                             const std::vector<int>& d,
                             int totalDimension
                           ) const;
//protected:
  bool checkOutside(const IVectorType&) const;
  bool checkInside (const IVectorType&) const;
  bool checkAcross (const IVectorType&) const;
  bool checkMapaway(const IVectorType&) const;


  VectorType m_C; // center point
  MatrixType m_M; // coordinate system
  IVectorType m_IC;
  IMatrixType m_IM, m_invIM;

  int m_d1, m_d2;
  VectorType m_r;
};

// ----------------------------------------------------

template<typename Vector1, typename Vector2>
void embedVector(const Vector1& v1, Vector2& v2, const std::vector<int>& d)
{
  for(int i=0; i<v1.dimension();++i)
    v2[ d[i] ] = v1[i];
}

// ----------------------------------------------------

template<typename Matrix1, typename Matrix2>
void embedMatrix(const Matrix1& m1, Matrix2& m2, const std::vector<int>& d)
{
  for(unsigned i=0; i<d.size();++i)
    for(unsigned j=0; j<d.size();++j)
      m2(d[i]+1,d[j]+1) = m1(i+1,j+1);
}

// ----------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
template<typename IMatrix>
GridSet<IMatrix>& HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::gridSet( 
    GridSet<IMatrix>& G,
    const std::vector<int>& grid, 
    const std::vector<int>& d,
    int totalDimension
 ) const
{
  typedef typename GridSet<IMatrix>::ScalarType Interval;
  G.C = IMatrix::Identity(totalDimension);

  embedMatrix(this->m_IM,G.C,d);

  G.r.clear();
  if(d.size() != grid.size() || d.size()!= (unsigned int) this->m_IM.numberOfRows())
    throw std::runtime_error("Incompatible dimensions in function HSetND::gridSet");


  int j;
  unsigned int k;
  IMatrixType M = this->m_IM;  // columns of M define vectors on which one small boxes will be build
  G.r.resize(totalDimension);
  G.r.clear();
  for(k=0;k<d.size();++k)
  {
    G.r[ d[k] ] = Interval(-m_r[k],m_r[k])/grid[k];
  }

  IVectorType corner = this->m_IC;
  for(j=0;j<this->m_IM.numberOfColumns();++j) 
    corner -= this->m_IM.column(j)*ScalarType(m_r[j]);

  int numberOfElements =1;
  for(k=0;k<grid.size();++k)
    numberOfElements *= grid[k];

  G.center.resize(numberOfElements);
  for(j=0;j<numberOfElements;j++)
  {
    int num = j;
    IVectorType r(this->m_IC.dimension());
    for(k=0;k<grid.size();k++)
    {
      int ind = num % grid[k];
      num = num / grid[k];
      r[k] = 2*(ScalarType(ind+0.5)*m_r[k])/grid[k];
    }
    IVectorType x = corner + this->m_IM*r;
    G.center[j].resize(totalDimension);
    G.center[j].clear();
    embedVector(x,G.center[j],d);
  }
  return G;
}

// ----------------------------------------------------

template<typename VectorType, typename IVectorType, typename MatrixType, typename IMatrixType>
template<typename IMatrix>
GridSet<IMatrix>& HSetND<VectorType,IVectorType,MatrixType,IMatrixType>::gridWall( 
    GridSet<IMatrix>& G,
    const std::vector<int>& grid, 
    const std::vector<int>& d,
    int totalDimension,
    int dir, int sign
 ) const
{
  if(m_d1==0 && m_d2==0) return G;

  typedef typename GridSet<IMatrix>::ScalarType Interval;
  G.C = IMatrix::Identity(totalDimension);

  embedMatrix(this->m_IM,G.C,d);

  G.r.clear();
  if(d.size() != grid.size() || d.size()!= (unsigned int) this->m_IM.numberOfRows())
    throw std::runtime_error("Incompatible dimensions in function HSetND::gridSet");


  int j;
  unsigned int k;
  IMatrixType M = this->m_IM;  // columns of M define vectors on which one small boxes will be build
  G.r.resize(totalDimension);
  G.r.clear();
  for(k=0;k<d.size();++k)
  {
    if(k!=dir)
      G.r[ d[k] ] = Interval(-m_r[k],m_r[k])/grid[k];
  }

  IVectorType corner = this->m_IC;
  for(j=0;j<this->m_IM.numberOfColumns();++j) 
    if(j!=dir)
      corner -= this->m_IM.column(j)*ScalarType(m_r[j]);

  int numberOfElements =1;
  for(k=0;k<grid.size();++k)
    if(k!=dir)
      numberOfElements *= grid[k];

  if(sign==0)
    G.center.resize(2*numberOfElements);
  else
    G.center.resize(numberOfElements);

  for(j=0;j<numberOfElements;j++)
  {
    int num = j;
    IVectorType r(this->m_IC.dimension());
    for(k=0;k<grid.size();k++)
    {
      if(k!=dir)
      {
        int ind = num % grid[k];
        num = num / grid[k];
        r[k] = 2*(ScalarType(ind+0.5)*m_r[k])/grid[k];
      }
    }

    if(sign==-1)
    {
      r[dir] = ScalarType(-m_r[dir]);
      IVectorType x = corner + this->m_IM*r;
      G.center[j].resize(totalDimension);
      G.center[j].clear();
      embedVector(x,G.center[j],d);
    } else if(sign==1)
    {
      r[dir] = ScalarType(m_r[dir]);
      IVectorType x = corner + this->m_IM*r;
      G.center[j].resize(totalDimension);
      G.center[j].clear();
      embedVector(x,G.center[j],d);
    } else 
    {
      r[dir] = ScalarType(-m_r[dir]);
      IVectorType x = corner + this->m_IM*r;
      G.center[j].resize(totalDimension);
      G.center[j].clear();
      embedVector(x,G.center[j],d);

      r[dir] = ScalarType(m_r[dir]);
      x = corner + this->m_IM*r;
      G.center[j+numberOfElements].resize(totalDimension);
      G.center[j+numberOfElements].clear();
      embedVector(x,G.center[j+numberOfElements],d);
    }
  }
  return G;
}

}} // namespace capd::covrel

#endif // _CAPD_COVREL_HSETND_H_ 

/// @}
