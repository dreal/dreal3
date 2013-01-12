/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file GridSet.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_COVREL_GRIDSET_H_
#define _CAPD_COVREL_GRIDSET_H_

#include <vector>

namespace capd{
namespace covrel{

/**
   This class is used to store a grid of a sets in the form
   center[i] + M * r
*/
template<typename MatrixT>
class GridSet
{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename std::vector<VectorType>::iterator iterator;
  typedef typename std::vector<VectorType>::const_iterator const_iterator;

  /// @name iterators through centers of the sets
  /// @{
  iterator begin(){
    return center.begin();
  }
  iterator end(){
    return center.end();
  }
  const_iterator begin() const {
    return center.begin();
  }
  const_iterator end() const {
    return center.end();
  }
  /// @}

  // TODO : this function should be called center but it collides with vector center
  /// returns center of the i-th set
  const VectorType & centers(int i) const{
    return center[i];
  }
  /// returns reference to center of the i-th set
  VectorType & centers(int i){
      return center[i];
  }
  // sets new center of the i-th set in the grid
  void setCenter(int i, const VectorType & newCenter){
      center[i] = newCenter;
  }
  size_t size() const {
    return center.size();
  }
  void resize(size_t newSize){
    center.resize(newSize);
  }
  /// returns matrix of the coordinate system (columns are its base vectors)
  const MatrixType & coordinateSystem() const{
    return C;
  }
  /// returns reference to matrix of the coordinate system (columns are its base vectors)
  MatrixType & coordinateSystem(){
      return C;
  }
  // sets new coordinate system
  void setCoordinateSystem(const MatrixType & newCoordinateSystem){
      C = newCoordinateSystem;
  }
  /// returns set in given coordinate system
  /// (in which set is zero-centered product of intervals)
  /// This set is common for all sets in the grid
  const VectorType & box() const{
    return r;
  }
  VectorType & box(){
      return r;
  }
  void setBox(const VectorType & newBox){
        r = newBox;
  }
// TODO: center, C, r should be protected, it needs changes in other files
//protected:
  std::vector<VectorType> center;
  MatrixType C;
  VectorType r;
};

/////////////////////////////////////////////////////////////////////////////////////
//    moveGridAndCheckCondition
///
///  moves each part of \c grid using dynamical system \c dynsys and checks
///  relation between its image and \c hset given by \c condition
///
///  @param[in] dynsys    dynamical system : can be either continuous or discrete
///  @param[in] grid      grid of the first h-set (whole set or one of its walls)
///  @param[in] condition function with two parameters: first = hset, second = C0Set
///  @param[in] hset      second h-set (set we want to cover)
///
/////////////////////////////////////////////////////////////////////////////////////
template<typename C0SetType, typename DynSysType, typename GridSet, typename ConditionT, typename HSet>
bool moveGridAndCheckCondition(DynSysType & dynsys, const GridSet & grid,
              const ConditionT & condition, const HSet & hset) {

  for (typename GridSet::const_iterator i = grid.begin(); i != grid.end(); ++i) {
    C0SetType set(*i, grid.r, grid.C);
    if (!condition(hset, dynsys(set)))
      return false;
  }
  return true;
}

}} // namespace capd::covrel

#endif // _CAPD_COVREL_GRIDSET_H_

/// @}
