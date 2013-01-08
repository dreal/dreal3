/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file RepSet.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/repSet/RepSet.h"

/*
-------------------------------------
Class Template RepSet: methods
-------------------------------------
*/

template <typename ESET>
RepSet<ESET>&
RepSet<ESET>::
operator-=(const RepSet& s){
  iterator pos;
  std::set<ESET> contentsCopy(contents);
  for (pos = contentsCopy.begin(); pos != contentsCopy.end(); ++pos){
    if(s.contents.find(*pos) != s.contents.end()) {
      contents.erase(*pos);
    };
  };
  return *this;
}

template <typename ESET>
RepSet<ESET>&
RepSet<ESET>::
operator+=(const RepSet& s){
  iterator pos;
  for (pos = s.begin(); pos != s.end(); ++pos){
    contents.insert(*pos);
  };
  return *this;
}


template <typename ESET>
RepSet<ESET>&
RepSet<ESET>::
operator*=(const RepSet& s){
  iterator pos;
  std::set<ESET> contentsCopy(contents);
  for (pos = contentsCopy.begin(); pos != contentsCopy.end(); ++pos){
    if(s.contents.find(*pos) == s.contents.end()) contents.erase(*pos);
  }
  return *this;
}

template <typename ESET>
RepSet<ESET>
RepSet<ESET>::
wrap() const{
  RepSet<ESET> result(*this);
  iterator pos;
  iterator myEnd=contents.end();
  for (pos = contents.begin(); pos != myEnd; ++pos){
    std::vector<ESET> nb=pos->neighbors();
    for(uint i=0;i<nb.size();i++){
      result.insert(nb[i]);
    }
  }
  return result;
}


template <typename ESET>
bool
RepSet<ESET>::
operator<=(const RepSet& s) const{
  iterator pos;
  iterator myEnd=contents.end();
  iterator sEnd=s.contents.end();
  for (pos = contents.begin(); pos != myEnd; ++pos){
    if(s.contents.find(*pos)==sEnd) return false;
  }
  return true;
}

template <typename ESET>
bool
RepSet<ESET>::
subsetInt(const RepSet& s) const{
  iterator pos;
  iterator myEnd=contents.end();
  iterator sEnd=s.contents.end();
  for (pos = contents.begin(); pos != myEnd; ++pos){
    std::vector<ESET> nb=pos->neighbors();
    for(uint i=0;i<nb.size();i++){
     if(s.contents.find(nb[i])==sEnd){
//       out << "Neighbor " << nb[i].toString() << " of " << pos->toString() << " not in the neighborhood\n";
       return false;
     }
    }
  }
  return true;
}

template <typename ESET>
RepSet<ESET>
RepSet<ESET>::
subdivided() const{
  RepSet<ESET> result;
  const_iterator pos;
  for (pos = contents.begin(); pos != contents.end(); ++pos){
    unsigned int iMax= (1 << ESET::Dim);
    for(unsigned int i=0; i<iMax;i++){
      result.insert(pos->subCube(i));
    }
  }
  return result;
}

/***
  The method computes connected components of the set.
  The components are returned in the provided std::vector.
  Additionally the number of components is returned
  as the value of the function
***/
template <typename ESET>
int
RepSet<ESET>::
assignComponentsTo(std::vector<RepSet<ESET> >& c) const{
  RepSet<ESET> s,copy(*this);
  int componentIndex=-1;
  while(!copy.empty()){
    componentIndex++;
    // prepare place for the component
    c.push_back(RepSet<ESET>());
    ESET e=copy.showOneElement();
    s.insert(e);
    while(!s.empty()){
      ESET x=s.showOneElement();
      c[componentIndex].insert(x);
      std::vector<ESET> v=x.neighbors();
      for(int i=0;i<(int)v.size();i++) s.insert(v[i]);
      s*=(*this);
      s-=c[componentIndex];
    }
    copy-=c[componentIndex];
  }
  return componentIndex+1;
}

template <typename ESET>
std::string
RepSet<ESET>::
toString() const{
  std::string result("[");
  iterator pos = contents.begin();;
  if(pos!=contents.end()){
    while(1){
      result+=pos->toString();
      if(++pos != contents.end()) result+=",";
      else break;
    }
  }
  result+="]";
  return result;
}

// This version designed for representable sets
// - returns the minimal of the left coordinates
// - and the maximal of the right coordinates
template <typename ESET>
void
RepSet<ESET>::
enclosingBox(int minCoords[],int maxCoords[]) const{
  iterator pos = begin();
  int dim=pos->embeddingDimension();
  for(int i=0;i<dim;++i){
    minCoords[i]=maxCoords[i]=pos->leftCoordinate(i);
  }
  for (pos = begin(); pos != end(); ++pos){
    for(int i=0;i<dim;++i){
      minCoords[i]=std::min(minCoords[i],pos->leftCoordinate(i));
      maxCoords[i]=std::max(maxCoords[i],pos->rightCoordinate(i));
    }
  }
}

// This version designed for full cubical sets
// - returns the minimal
// - and the maximal of the LEFT coordinates
template <typename ESET>
void
RepSet<ESET>::
lowerEnclosingBox(int minCoords[],int maxCoords[]) const{
  iterator pos = begin();
  int dim=pos->embeddingDimension();
  for(int i=0;i<dim;++i){
    minCoords[i]=maxCoords[i]=pos->leftCoordinate(i);
  }
  for (pos = begin(); pos != end(); ++pos){
    for(int i=0;i<dim;++i){
      minCoords[i]=std::min(minCoords[i],pos->leftCoordinate(i));
      maxCoords[i]=std::max(maxCoords[i],pos->leftCoordinate(i));
    }
  }
}



/*
--------------------------------------
Class Template RepSet friend functions
--------------------------------------
*/

template <typename ESET>
RepSet<ESET>
operator+(RepSet<ESET> const& s1,RepSet<ESET> const& s2){
  RepSet<ESET> result(s1);
  result.contents.insert(s2.contents.begin(),s2.contents.end());
  return result;
}

template <typename ESET>
RepSet<ESET>
operator-(RepSet<ESET> const& s1,RepSet<ESET> const& s2){
  RepSet<ESET> result(s1);
  typename std::set<ESET>::iterator pos;
  for (pos = s1.contents.begin(); pos != s1.contents.end(); ++pos){
    if(s2.contents.find(*pos) != s2.contents.end()) {
      result.contents.erase(*pos);
    }
  }
  return result;
}

template <typename ESET>
RepSet<ESET>
operator*(RepSet<ESET> const& s1,RepSet<ESET> const& s2){
  RepSet<ESET> result(s1);
  typename std::set<ESET>::iterator pos;
  for (pos = s1.contents.begin(); pos != s1.contents.end(); ++pos){
    if(s2.contents.find(*pos) == s2.contents.end()) result.contents.erase(*pos);
  }
  return result;
}


//template <typename ESET>
template <typename ESET,typename P_Vector>
RepSet<ESET>
cover(const P_Vector& v,const typename ESET::BinBaseCube& bbc){
  RepSet<ESET> result;
  std::vector<uint> bot,top,cur;
  bot.reserve(ESET::Dim);
  top.reserve(ESET::Dim);
  cur.reserve(ESET::Dim);
  for(uint i=0;i<ESET::Dim;i++){
    // For an interval disjoint with the range we return the empty set
    if(v[i].rightBound() < bbc.getAxis(i).left || v[i].leftBound()>bbc.getAxis(i).right) return result;
    bot[i]=bbc.getAxis(i).leftPosition(v[i].leftBound());
    top[i]=bbc.getAxis(i).rightPosition(v[i].rightBound());
  }
  for(uint i=0;i<ESET::Dim;i++) cur[i]=bot[i];

  bool fin=false;
  while(!fin){
    ESET e(cur,&bbc);
    result.insert(e);
    for(uint i=0;i<ESET::Dim;i++){
      cur[i]++;
      if(cur[i]>top[i]) cur[i]=bot[i];
      else break;
      if(i==ESET::Dim-1) fin=true;
    }
  }
  return result;
}

//template <typename ESET>
template <typename ESET,typename P_Vector>
RepSet<ESET>
cover(const std::vector<P_Vector>& v,typename ESET::BinBaseCube const& bbc){
  RepSet<ESET> result;
  for (uint i=0;i<v.size();i++){
    result+=cover<ESET>(v[i],bbc);
  }
  return result;
}

template <typename ESET>
std::istream& operator>>(std::istream& inp, RepSet<ESET>& A_RepSet){
  ESET eset;
  char ch=' ';
  int embDim;

  inp >> ch;
  if(ch!='{'){
    inp.putback(ch);
    throw std::runtime_error("operator>>(std::istream&,RepSet<ESET>&): '{' expected");
  }
  inp >> eset;
  A_RepSet.insert(eset);
  embDim=eset.embeddingDimension();
  do{
    inp >> ch;
    if(ch!=','){
      if(ch=='}') break;
      inp.putback(ch);
      throw std::runtime_error("operator>>(std::istream&,RepSet<ESET>&): '}' or ',' expected");
    }
    inp >> eset;
    if(embDim != eset.embeddingDimension()){
      throw EmbDimException("operator>>(std::istream&,RepSet<ESET>&): inconsistent embedding dimension found on input!");
    }
    A_RepSet.insert(eset);
  }while(true);
  return inp;
}

template <typename ESET>
std::ostream& operator<<(std::ostream& out, const RepSet<ESET>& A_RepSet){
  out << "{\n";
  typename std::set<ESET>::const_iterator pos;
  for(pos=A_RepSet.begin(); pos != A_RepSet.end(); ++pos){
    out << "  " << *pos << std::endl;
  }
  out << "}\n";
  return out;
}

/// @}

