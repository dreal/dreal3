/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file GridSets.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_COVREL_GRIDSETS_H_
#define _CAPD_COVREL_GRIDSETS_H_

#include <deque>
#include "capd/covrel/GridSet.h"

namespace capd{
namespace covrel{

/**
   This class is used to store a grid of a sets in the form
   center[i] + M * r
*/
template<typename SetT>
class GridSets
{
public:
  typedef SetT SetType;
  typedef typename SetType::MatrixType MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef std::deque<SetType> SetContainer;
  typedef typename SetContainer::iterator iterator;
  typedef typename SetContainer::const_iterator const_iterator;

  GridSets(const GridSet<MatrixType> & grid){
	  for(typename GridSet<MatrixType>::iterator it = grid.begin(); it != grid.end(); ++it){
		  m_sets.push_back(SetType(*it, grid.box(), grid.coordinateSystem()));
	  }
  }
  virtual void move(capd::dynsys::DynSys<MatrixType>& dynsys){
	  for(it = begin(); it != end(); ++it){
		  it->move(dynsys);
	  }

  }
  /// @name iterators through the sets
  /// @{
  iterator begin(){
    return m_sets.begin();
  }
  iterator end(){
    return m_sets.end();
  }
  const_iterator begin() const {
    return m_sets.begin();
  }
  const_iterator end() const {
    return m_sets.end();
  }
  /// @}



protected:
  SetContainer m_sets;
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
