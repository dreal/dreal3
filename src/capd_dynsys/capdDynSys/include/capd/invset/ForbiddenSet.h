//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
/// @file ForbiddenSet.h
///
/// @author Tomasz Kapela   @date 2009-12-15
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2009
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INVSET_FORBIDDENSET_H_
#define _CAPD_INVSET_FORBIDDENSET_H_

namespace capd{
namespace invset{
/// class that defines forbidden set
template <typename VectorT>
class ForbiddenSet : public std::list<VectorT> {
public:
  typedef VectorT VectorType;
  typedef std::list<VectorType> ContainerType;
  typedef typename ContainerType::iterator iterator;
  typedef typename ContainerType::const_iterator const_iterator;
  ForbiddenSet(){
  }
  ForbiddenSet(const VectorType & region){
    this->push_back(region);
  }
  ForbiddenSet(const ContainerType & regions): ContainerType(regions){
  }
  /// adds forbidden region
  void add(const VectorType & region){
    this->push_back(region);
  }
  /// removes all forbidden regions
  void clear(){
    ContainerType::clear();
  }
  /// checks cube and returns true if it is not contained in any of the forbidden regions
  bool check(const VectorType & cube) const{
    const_iterator region = this->begin();
    for(; region != this->end(); ++region){
      if(capd::vectalg::subset(cube, *region))
        return false;
    }
    return true;
  }
};

}} // end of namespace capd::invset

#endif // _CAPD_INVSET_FORBIDDENSET_H_
