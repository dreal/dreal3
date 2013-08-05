//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
/// @file Scope.h
///
/// @author Tomasz Kapela   @date 2009-12-15
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2009
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INVSET_SCOPE_H_
#define _CAPD_INVSET_SCOPE_H_

namespace capd{
namespace invset{

/// class that defines set of regions
/// it can be used do define domain, range, allowed sets for graphs
template <typename VectorT>
class Scope : public std::list<VectorT> {
public:
  typedef VectorT VectorType;
  typedef std::list<VectorType> ContainerType;
  typedef typename ContainerType::iterator iterator;
  typedef typename ContainerType::const_iterator const_iterator;
  Scope(){
  }
  Scope(const VectorType & region){
    this->push_back(region);
  }
  Scope(const ContainerType & regions): ContainerType(regions){
  }
  /// adds forbidden region
  void add(const VectorType & region){
    this->push_back(region);
  }
  /// removes all forbidden regions
  void clear(){
    ContainerType::clear();
  }
  /// checks if cube can be in the scope
  /// returns false if cube is outside the scope
  /// returns true if cube has non empty intersection with one of the interval sets.
  bool check(const VectorType & cube) const{
    const_iterator region = this->begin();
    for(; region != this->end(); ++region){
      if(!capd::vectalg::intersectionIsEmpty(cube, *region))
        return true;
    }
    return false;
  }
};


}} // end of namespace capd::invset

#endif // _CAPD_INVSET_SCOPE_H_

