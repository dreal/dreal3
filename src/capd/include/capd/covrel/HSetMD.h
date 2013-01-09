/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file HSetMD.h
///
/// @author Daniel Wilczak, Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_COVREL_HSETMD_H_
#define _CAPD_COVREL_HSETMD_H_

#include <vector>
#include <stdexcept>
#include "capd/covrel/HSet.h"
#include "capd/covrel/GridSet.h"
#include "capd/dynset/C0Set.h"

namespace capd {
namespace covrel {

/**
 This class provides a h-set in an arbitrary dimension
 */
template<typename MatrixT, typename IMatrixT>
class HSetMD: public HSet<typename MatrixT::RowVectorType,
    typename IMatrixT::RowVectorType> {
public:
  typedef MatrixT MatrixType;
  typedef IMatrixT IMatrixType;
typedef  typename MatrixType::RowVectorType VectorType;
  typedef typename IMatrixType::RowVectorType IVectorType;
  typedef typename IVectorType::ScalarType ScalarType;
  typedef typename VectorType::ScalarType BoundType;

  // we assume that the set is represented as center + Base * B(0,r)
  // uDim denotes a number of unstable directions
  // sDim denotes a number of stable directions
  HSetMD() {}
  HSetMD(const VectorType& center, const MatrixType& Base, int uDim, int sDim, const VectorType& r);
  HSetMD(const IVectorType & center, const IMatrixType& Base, int uDim, int sDim, const VectorType& r);
  ~HSetMD() {}

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

  // if we have a special representation of a point
  template <typename SetType>
  bool outside(const SetType & A_set) const;
  template <typename SetType>
  bool inside (const SetType & A_set) const;
  template <typename SetType>
  bool across (const SetType & A_set) const;
  template <typename SetType>
  bool mapaway(const SetType & A_set) const;

  VectorType transformToHSetCoordinates(const VectorType & point) const;
  IVectorType transformToHSetCoordinates(const IVectorType & point) const;

  /**
   * in the \c grid it returns uniform grid of the given face
   */
  template<typename IMatrix>
  GridSet<IMatrix>& gridFace(
      GridSet<IMatrix>& grid,
      const std::vector<int>& gridSizes,
      const std::vector<int>& dimensions,
      unsigned int totalDimension,
      unsigned int coordinateToFix,
      Side side = bothSides
  ) const;

  /// this procedure creates a grid of the whole h-set
  /// in the following form: G.center[i] + G.C * G.r
  /// d is a vector of indices of coordinates if the set is embeded in higher dimension
  template<typename IMatrix>
  GridSet<IMatrix>& gridSet(
      GridSet<IMatrix>& G,
      const std::vector<int>& grid,
      const std::vector<int>& d,
      int totalDimension
  ) const;

  // these functions works for interval sets expressed in HSet coordinate system
  bool checkOutside(const IVectorType&) const;
  bool checkInside (const IVectorType&) const;
  bool checkAcross (const IVectorType&) const;
  bool checkMapaway(const IVectorType&) const;

  const IVectorType & center() const {return m_Ix;} ///< center of h-set
  const IMatrixType & coordinateSystem() const {return m_IB;} ///< matrix of base vectors
  const IMatrixType & invCoordinateSystem() const {return m_invIB;}
  IVectorType box() const { ///< h-set in 'proper' coordinate system (it is a product of intervals)
    IVectorType b(m_r.dimension());
    for(int i=0; i<m_r.dimension(); ++i)
    b[i] = ScalarType(-m_r[i],m_r[i]);
    return b;
  }
  const VectorType & radius() {return m_r;} ///< returns vector of radiuses (in each direction)
  int unstableDimension() const {return m_uDim;} ///< number of unstable dimensions
  int stableDimension() const {return m_sDim;} ///< number of stable dimensions
  const VectorType & get_x() const { return m_x;}
  const MatrixType & get_B() const { return m_B;}
  const VectorType & get_r() const { return m_r;}
  const IVectorType & get_I_x() const { return m_Ix;}
  const IMatrixType & get_I_B() const { return m_IB;}
  const IMatrixType & get_I_invB() const { return m_invIB;}

  virtual std::string show() const;
  std::string showInfo() const;
  friend std::ostream & operator << (std::ostream & stream, const HSetMD & set ){
  		stream << set.show();
  		return stream;
  }
protected:
  VectorType m_x; ///< center point
  MatrixType m_B; ///< coordinate system
  IVectorType m_Ix; ///< rigorous center point
  IMatrixType m_IB, m_invIB; ///< rigorous coordinate system and its inverse

  int m_uDim, ///< number of unstable dimensions
  m_sDim; ///< number of stable dimensions
  VectorType m_r; ///< radiuses of balls (used both for non-rigorous and rigorous version)
}; // class HSetMD

// ----------------------------------------------------

template<typename Vector1, typename Vector2>
void embedVector(const Vector1& v1, Vector2& v2, const std::vector<int>& d)
{
  for(int i=0; i<v1.dimension();++i)
  v2[ d[i] ] = v1[i];
}
/**
 * it embeds \c vector into a space of fullDimension
 * in  d[i] we pass coordiante where to put i-th coordinate of given vector
 * other coordinates are set to 0.
 * it resizes result vector (if needed).
 */
template<typename Vector1, typename Vector2>
void embedVector(const Vector1& vector, Vector2& result, size_t fullDimension, const std::vector<int>& d)
{
  result.resize(fullDimension);
  result.clear();
  for(int i=0; i<vector.dimension();++i)
  result[ d[i] ] = vector[i];
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

template<typename MatrixType, typename IMatrixType>
template<typename IMatrix>
GridSet<IMatrix>& HSetMD<MatrixType,IMatrixType>::gridSet(
    GridSet<IMatrix>& G,
    const std::vector<int>& grid,
    const std::vector<int>& d,
    int totalDimension
) const
{
  typedef typename GridSet<IMatrix>::ScalarType Interval;
  G.C = IMatrix::Identity(totalDimension);

  embedMatrix(this->m_IB,G.C,d);

  G.r.clear();
  if(d.size() != grid.size() || d.size()!= (unsigned int) this->m_IB.numberOfRows())
  throw std::runtime_error("Incompatible dimensions in function HSetMD::gridSet");

  int j;
  unsigned int k;
  IMatrixType M = this->m_IB; // columns of M define vectors on which one small boxes will be build
  G.r.resize(totalDimension);
  G.r.clear();
  for(k=0;k<d.size();++k)
  {
    G.r[ d[k] ] = Interval(-m_r[k],m_r[k])/grid[k];
  }

  IVectorType corner = this->m_Ix;
  for(j=0;j<this->m_IB.numberOfColumns();++j)
  corner -= this->m_IB.column(j)*ScalarType(m_r[j]);

  int numberOfElements =1;
  for(k=0;k<grid.size();++k)
  numberOfElements *= grid[k];

  G.center.resize(numberOfElements);
  for(j=0;j<numberOfElements;j++)
  {
    int num = j;
    IVectorType r(this->m_Ix.dimension());
    for(k=0;k<grid.size();k++)
    {
      int ind = num % grid[k];
      num = num / grid[k];
      r[k] = 2*(ScalarType(ind+0.5)*m_r[k])/grid[k];
    }
    IVectorType x = corner + this->m_IB*r;
    G.center[j].resize(totalDimension);
    G.center[j].clear();
    embedVector(x,G.center[j],d);
  }
  return G;
}

// ----------------------------------------------------

/**
 * in the \c grid it returns uniform grid of the given face
 *
 * @param gridSizes         number of pieces in the grid
 * @param coordinateToFix   which wall should be grided
 * @param side              which side of given coordinate should be grided : both, left or right
 * @param totalDimension    dimension of the space (can be bigger than 2 if we embed the set)
 * @param dimensions        if hset is embedded in higher dimension
 *                          then we put first coordinate in dimensions[0] coordinate,
 *                          second in dimensions[1], ... and the rest set to 0.
 */


template<typename MatrixType, typename IMatrixType>
template<typename IMatrix>
GridSet<IMatrix>& HSetMD<MatrixType,IMatrixType>::gridFace(
    GridSet<IMatrix>& grid,
    const std::vector<int>& gridSizes,
    const std::vector<int>& dimensions,
    unsigned int totalDimension,
    unsigned int coordinateToFix,
    Side side /*= bothSides*/
) const
{
  if(m_uDim==0 && m_sDim==0) return grid;

  if((dimensions.size() != gridSizes.size()) || (dimensions.size()!= (unsigned int) this->m_IB.numberOfRows()))
    throw std::runtime_error("Incompatible dimensions in function HSetMD::gridSet");

  unsigned hsetDimension = this->m_IB.numberOfRows();

  unsigned int j, k; // loop counters

  // grid.box() is an elementary box of a dimension equal to hset face dimension
  // and parallel to face being grided.
  // The grid of face is made from it by translating it to different centers.
  grid.box().resize(totalDimension);
  grid.box().clear();
  typedef typename IMatrix::ScalarType Interval;
  for(k=0; k < hsetDimension; ++k)
  {
    if(k != coordinateToFix)
    grid.box()[ dimensions[k] ] = Interval(-m_r[k],m_r[k])/gridSizes[k];
  }

  grid.coordinateSystem() = IMatrix::Identity(totalDimension);
  embedMatrix(this->m_IB,grid.coordinateSystem(),dimensions);

  IMatrixType M = this->m_IB; // columns of IB define vectors on which a small boxes will be build
  IVectorType corner = this->m_Ix; // m_Ix - center of hset
  for(j=0; j < hsetDimension; ++j)
    if(j!=coordinateToFix)
      corner -= this->m_IB.column(j)*ScalarType(m_r[j]);

  unsigned numberOfElements = 1;
  for(k=0; k<gridSizes.size(); ++k)
    if(k != coordinateToFix)
      numberOfElements *= gridSizes[k];

  if(side == bothSides)
    grid.resize(2*numberOfElements);
  else
    grid.resize(numberOfElements);

  for(j=0; j<numberOfElements; ++j)
  {
    int num = j;
    IVectorType r(hsetDimension);
    for(k=0; k<hsetDimension; k++)
    {
      if(k!=coordinateToFix)
      {
        int ind = num % gridSizes[k];
        num = num / gridSizes[k];
        r[k] = 2*(ScalarType(ind+0.5)*m_r[k])/gridSizes[k];
      }
    }

    if(side ==rightSide)
      r[coordinateToFix] = ScalarType(m_r[coordinateToFix]);
    else // leftSide or bothSides
      r[coordinateToFix] = ScalarType(-m_r[coordinateToFix]);

    IVectorType x = corner + this->m_IB*r;
    embedVector(x,grid.center[j],totalDimension, dimensions);

    if(side == bothSides){  // we add right side also
      r[coordinateToFix] = ScalarType(m_r[coordinateToFix]);
      x = corner + this->m_IB*r;
      embedVector(x,grid.center[j+numberOfElements],totalDimension, dimensions);
    }
  }
  return grid;
}

}} // namespace capd::covrel

#endif // _CAPD_COVREL_HSETMD_H_
/// @}
