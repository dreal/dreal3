/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file RepSet.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*
    Class template: RepSet
    (c) Marian Mrozek, Krak�w 2004

    The objects of this class represent families of elementary sets.
    It is assumed that elementary sets are ordered in some
    way, so that operator< is available
    The implementation of the class is via STL template set

    Template parameters:
       ESET
         - class of elementary sets
    Object data:
       contents
         - a private variable of type std::set<ESET>
    Object methods:
       operators +=,-=,*=
         - change to union, set difference, intersection
       insert
         - insert an elementary set
       remove
         - remove an elementary set
       begin(),end()
         - shorthands to the respective methods of
           the private class component contents

    Friends:
       operators +,-,*
         - union, set difference and intersection)

*/

#ifndef _CAPD_REPSET_REPSET_H_
#define _CAPD_REPSET_REPSET_H_
#include <vector>
#include <set>
#include <algorithm>
#include <iterator>
#include <stdexcept>
//#include "capd/interval/DoubleInterval.h"
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/Matrix.h"
#include "capd/bitSet/EmbDimException.h"

typedef unsigned int uint;


template <typename ESET>
class RepSet;

template <typename ESET>
RepSet<ESET> operator+(RepSet<ESET> const& s1,RepSet<ESET> const& s2);

template <typename ESET>
RepSet<ESET> operator-(RepSet<ESET> const& s1,RepSet<ESET> const& s2);

template <typename ESET>
RepSet<ESET> operator*(RepSet<ESET> const& s1,RepSet<ESET> const& s2);

template <typename ESET>
std::istream& operator>>(std::istream& inp, RepSet<ESET>& A_RepSet);

template <typename ESET>
std::ostream& operator<<(std::ostream& out, const RepSet<ESET>& A_RepSet);

/////////////////////////////////////////////////////////////////////
//    Class template: RepSet
///
/// The objects of this class represent families of elementary sets.
/// It is assumed that elementary sets are ordered in some
/// way, so that operator< is available
/// The implementation of the class is via STL template set
///
/// Template parameters:
///    ESET
///      - class of elementary sets
/////////////////////////////////////////////////////////////////////
template <typename ESET>
class RepSet{
public:
  typedef typename std::set<ESET>::const_iterator const_iterator;
  typedef typename std::set<ESET>::iterator iterator;
  typedef ESET eSet;
  typedef ESET ElementarySetType;

  const_iterator begin() const;
  const_iterator end() const;

  int embeddingDimension() const;

  RepSet& operator+=(const RepSet& s); // Added but not tested
  RepSet& operator-=(const RepSet& s);
  RepSet& operator*=(const RepSet& s);

  int size() const{ return contents.size();}

  RepSet wrap() const;

  bool operator<=(const RepSet& s) const;
  bool subsetInt(const RepSet& s) const;
  bool operator==(const RepSet& s) const;

  RepSet& insert(const ESET& eset);
  RepSet& remove(const ESET& eset);
  bool includes(const ESET& eset) const;
  bool empty() const;
  void swap(RepSet& s);

  RepSet subdivided() const;
  const ESET& showOneElement() const;
  int assignComponentsTo(std::vector<RepSet<ESET> >& c) const;
  std::string toString() const;
  void enclosingBox(int minCoords[],int maxCoords[]) const;
  void lowerEnclosingBox(int minCoords[],int maxCoords[]) const;

  friend RepSet operator+ <>(const RepSet& s1,const RepSet& s2);
  friend RepSet operator- <>(const RepSet& s1,const RepSet& s2);
  friend RepSet operator* <>(const RepSet& s1,const RepSet& s2);

  friend std::istream& operator>> <>(std::istream& inp, RepSet& A_RepSet);
  friend std::ostream& operator<< <>(std::ostream& out, const RepSet& A_RepSet);

private:
  std::set<ESET> contents;
};

/*
-------------------------------------
Class Template RepSet: inline methods
-------------------------------------
*/

template <typename ESET>
inline typename std::set<ESET>::const_iterator
RepSet<ESET>::
begin() const{
  return contents.begin();
}

template <typename ESET>
inline typename std::set<ESET>::const_iterator
RepSet<ESET>::
end() const{
  return contents.end();
}

template <typename ESET>
inline int
RepSet<ESET>::
embeddingDimension() const{
  if(!size()) return 0;
  else return showOneElement().embeddingDimension();
}

template <typename ESET>
inline const ESET&
RepSet<ESET>::
showOneElement() const{
  if(empty()) throw std::logic_error("ESET& RepSet<ESET>::showOneElement(): called on empty set");
  return *begin();
}

template <typename ESET>
inline void
RepSet<ESET>::
swap(RepSet& s){
  contents.swap(s.contents);
}

template <typename ESET>
inline bool
RepSet<ESET>::
empty() const{
  return contents.empty();
}

template <typename ESET>
inline bool
RepSet<ESET>::
includes(const ESET& eset) const{
  return (contents.find(eset)!=contents.end());
}

template <typename ESET>
inline RepSet<ESET>&
RepSet<ESET>::
remove(const ESET& eset){
  contents.erase(eset);
  return *this;
}

template <typename ESET>
inline bool
RepSet<ESET>::
operator==(const RepSet& s) const{
  return (*this<=s) && (s<=*this);
}

template <typename ESET>
inline RepSet<ESET>&
RepSet<ESET>::
insert(const ESET& eset){
  contents.insert(eset);
  return *this;
}


#endif // _CAPD_REPSET_REPSET_H_
/// @}

