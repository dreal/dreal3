/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnContainer.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak  2006 */

#include <stdexcept>
#include "capd/capd/factrial.h"
#include "capd/vectalg/Multiindex.h"

#ifndef _CAPD_MAP_CNCONTAINER_H_ 
#define _CAPD_MAP_CNCONTAINER_H_ 

namespace capd{
namespace map{


// The class is used to store all partial derivatives of a map
// f:R^dim->R^dim up to the order 'n' (including n)
// as well as the objects of class Function
// which represent the partial derivatives.
// The number of coefficients is dim*newton(dim+n,n).
// This class allocate necessary memory and provides suitable iterators

template<typename Object> // Object = Scalar, Function or a Series
class CnContainer
{
public:
  typedef Object ObjectType;
  typedef Object* iterator;
  typedef const Object* const_iterator;
  typedef capd::vectalg::Multipointer Multipointer;
  typedef capd::vectalg::Multiindex Multiindex;

  CnContainer(int dim, int rank, const Object& p);
  CnContainer(int dim, int rank);
  CnContainer(const CnContainer& s);
  CnContainer& operator=(const CnContainer& s);
  CnContainer& operator=(const Object& p);
  ~CnContainer();

  int dimension() const;
  int rank() const;
  void resize(int newRank, bool copyData = true);
  void resize(int newRank, int newDimension, bool copyData = true);

  Object& operator[](int index);
  Object& operator()(int i, const Multipointer&);
  Object& operator()(int i, const Multipointer&, const Multipointer&);
  Object& operator()(int i, const Multiindex&);
  const Object& operator[](int index) const;
  const Object& operator()(int i, const Multipointer&) const;
  const Object& operator()(int i, const Multipointer&, const Multipointer&) const;
  const Object& operator()(int i, const Multiindex&) const;

// operators for C^0, C^1, C^2 and C^3 algorithms
  Object& operator()(int i);
  Object& operator()(int i, int j);
  Object& operator()(int i, int j, int c);
  Object& operator()(int i, int j, int c, int k);
  const Object& operator()(int i) const;
  const Object& operator()(int i, int j) const;
  const Object& operator()(int i, int j, int c) const;
  const Object& operator()(int i, int j, int c, int k) const;
   
// iterators
  iterator begin();
  iterator end();
//iterators for i-th function
  iterator begin(int i);
  iterator end(int i);
// iterators for 'level' order partial derivatves of i-th function
  iterator begin(int i, int level);
  iterator end(int i, int level);

  const_iterator begin() const;
  const_iterator end() const;
  const_iterator begin(int i) const;
  const_iterator end(int i) const;
  const_iterator begin(int i, int level) const;
  const_iterator end(int i, int level) const;

// multipointer selection
// notice, the loop do-while for multipointers agrees exactly with iterators on suitable level
// iterators are faster. However, they do not give an information about the index of partial drivative. 
// More precisely, for iterator b=begin(i,level) and Multipointer mp=first(level); we have
// *b = (*this)(i,mp); 
// next(mp); ++b; // and if  b!=end(i,level) we have
// *b = (*this)(i,mp);
  Multipointer first(int level) const; 
  bool next(Multipointer&) const;

  friend void swap(CnContainer & A, CnContainer & B){
    std::swap(A.m_dim, B.m_dim);
    std::swap(A.m_rank, B.m_rank);
    std::swap(A.m_size, B.m_size);
    std::swap(A.m_data, B.m_data);
  }

protected:
  int index(const Multipointer&) const;
  int index(const Multipointer&, const Multipointer&) const;
  int index(const Multiindex&) const;
  Object* m_data;
  int m_dim, m_rank, m_size;
}; // the end of class CnContainer

// ------------------- member definitions -------------------
// the following function computes the next multipointer after mp
// it returns false if mp is the last multipointer on a given level

template<typename Object>
bool CnContainer<Object>::next(Multipointer& mp) const
{
  int level = mp.dimension();
  if(level==0) return false;
  typename Multipointer::iterator b=mp.begin(), e=mp.end(), e1=mp.end();
  do
  {
    --e;
    if( ++(*e) % m_dim ) 
    {
      int p=*e;
      ++e;
      while(e!=e1)
      {
        *e=p;
        ++e;
      }
      return true;
    }
  }while(b!=e);
  return false;
}

// ----------------------------------------------------------

template<typename Object>
CnContainer<Object>& CnContainer<Object>::operator=(const CnContainer& c)
{
  if(&c==this)
    return *this;

  if(m_dim != c.m_dim || m_rank!=c.m_rank)
  {
    delete [] m_data;
    m_rank = c.m_rank;
    m_dim = c.m_dim;
    m_size = c.m_size;
    m_data = new Object[m_size];
  }

  iterator b=begin(), e=end();
  const_iterator i = c.begin();
  while(b!=e)
  {
    *b=*i;
    ++b;
    ++i;
  }
  return *this;
}
   
// ----------------------------------------------------------

template<typename Object>
CnContainer<Object>& CnContainer<Object>::operator=(const Object& p)
{
  iterator b=begin(), e=end();
  while(b!=e)
  {
    *b=p;
    ++b;
  }
  return *this;
}

// ----------------------------------------------------------

template<typename Object>
CnContainer<Object>::CnContainer(const CnContainer& c) 
  : m_dim(c.m_dim), m_rank(c.m_rank), m_size(c.m_size)
{
  m_data = new Object[m_size];
  iterator b=begin(), e=end();
  const_iterator i = c.begin();
  while(b!=e)
  {
    *b=*i;
    ++b;
    ++i;
  }
}

// ----------------------------------------------------------

template<typename Object>
inline CnContainer<Object>::CnContainer(int a_dim, int a_rank, const Object& p) 
  : m_dim(a_dim), m_rank(a_rank)
{
  m_size = m_dim*newton(m_dim+m_rank,m_dim);
  m_data = new Object[m_size];
  iterator b = begin(), e = end();
  while(b!=e)
  {
    *b = p;
    ++b;
  }
}

// ----------------------------------------------------------

template<typename Object>
void CnContainer<Object>::resize(int newRank,  bool copyData)
{
  if(newRank == m_rank)
    return;

  int newSize = m_dim*newton(m_dim+newRank,m_dim);

  Object* newData = new Object[newSize];
  if(copyData){
    int minRank = m_rank < newRank ? m_rank : newRank;
    for(int i=0;i<m_dim;++i)
    {
      iterator b = begin(i), e=end(i,minRank);
      Object* p =  newData+ i*newton(m_dim+newRank,m_dim);
      while(b!=e)
      {
        *p = *b;
        ++p;
        ++b;
      }
    }
  }
  delete [] m_data;
  m_data = newData;
  m_rank = newRank;
  m_size = newSize;
}

// ----------------------------------------------------------

/**
 * Resizes CnContainer
 * @param newRank       new maximal order
 * @param newDimension  new dimension
 * @param copyData      flag that controls if data is copied
 */
template<typename Object>
void CnContainer<Object>::resize(int newRank, int newDimension, bool copyData)
{
  if((newRank == m_rank) && (newDimension == m_dim))
    return;

  int newSize = newDimension*newton(newDimension+newRank,newDimension);

  Object* newData = new Object[newSize];
  if(copyData){
    int minRank = m_rank < newRank ? m_rank : newRank;
    int minDim = m_dim < newDimension ? m_dim : newDimension;
    for(int i=0; i< minDim; ++i){
      iterator b = begin(i),
          e = end(i,minRank);
      Object* p =  newData+ i*newton(newDimension+newRank,newDimension);
      while(b!=e)
      {
        *p = *b;
        ++p;
        ++b;
      }
    }
  }
  delete [] m_data;
  m_data = newData;
  m_rank = newRank;
  m_size = newSize;
  m_dim = newDimension;
}

// ----------------------------------------------------------

inline int computeNewton(int d,int l)
{
  return newton(d+l-1,l);
}

// ----------------------------------------------------------

// The following procedure computes an index of a table 
// which contains all the partial derivatives, given a multipointer of partial derivatives.
// at the level 'level' is newton(dim+level-1,dim-1) coefficients
template<typename Object>
int CnContainer<Object>::index(const Multipointer& mp) const
{
  int level = mp.module(); // in fact dimension
  if (level<=0) return 0;
  if(level>m_rank)
    throw std::range_error("CnContainer::index(Multipointer): requested level is to large");
 
  int result=0,i;
  int prev = 0;
   
  for(i=0;i<level;++i)
  {
    if(mp[i]-prev){
      result += (computeNewton(m_dim-prev,level-i) - computeNewton(m_dim-mp[i],level-i));
      prev = mp[i];
    }   
  }
  return result;
}

// ----------------------------------------------------------

template<typename Object>
int CnContainer<Object>::index(const Multipointer& mp, const Multipointer& sub) const
{
  int level = sub.module(); // in fact dimension
  if (level<=0) return 0;
  if(level>m_rank)
    throw std::range_error("CnContainer::index(Multipointer,Multipointer): requested level is to large");
 
  int result=0,i;
  int prev = 0;
   
  for(i=0;i<level;++i)
  {
    int s = mp[sub[i]];
    if(s-prev){
      result += (computeNewton(m_dim-prev,level-i) - computeNewton(m_dim-s,level-i));
      prev = s;
    }   
  }
  return result;
}

// ----------------------------------------------------------

template<typename Object>
int CnContainer<Object>::index(const Multiindex& mi) const
{
  int level = mi.module(); // sum norm
  if (level<=0) return 0;
  if(level>m_rank)
    throw std::range_error("CnContainer::index(Multiindex): requested level is to large");
 
  int result=0,i, prev=0;
  for(i=0;i<mi.dimension();++i)
  {
    if(mi[i]!=0){
      result+= (computeNewton(m_dim-prev,level) - computeNewton(m_dim-i,level));
      prev = i;
      level -= mi[i];
    }
  }
  return result;
}

// ------------------- inline definitions -------------------

template<typename Object>
inline typename CnContainer<Object>::Multipointer CnContainer<Object>::first(int level) const
{
  return Multipointer(level);
}

// ----------------------------------------------------------

template<typename Object>
inline CnContainer<Object>::CnContainer(int a_dim, int a_rank) 
  : m_dim(a_dim), m_rank(a_rank)
{
  m_size = m_dim*newton(m_dim+m_rank,m_dim);
  m_data = new Object[m_size];
}

// ----------------------------------------------------------

template<typename Object>
inline CnContainer<Object>::~CnContainer()
{
  delete [] m_data;
}

// ----------------------------------------------------------

template<typename Object>
inline int CnContainer<Object>::dimension() const
{
  return m_dim;
}

// ----------------------------------------------------------

template<typename Object>
inline int CnContainer<Object>::rank() const
{
  return m_rank;
}

// ----------------------------------------------------------

template<typename Object>
inline Object& CnContainer<Object>::operator[](int i)
{
  return m_data[i];
}

// ----------------------------------------------------------

template<typename Object>
inline const Object& CnContainer<Object>::operator[](int i) const
{
  return m_data[i];
}

// ----------------------------------------------------------

template<typename Object>
inline Object& CnContainer<Object>::operator()(int i, const Multipointer& mp)
{
  return *(begin(i,mp.dimension()) + index(mp));
}

// ----------------------------------------------------------

template<typename Object>
inline const Object& CnContainer<Object>::operator()(int i, const Multipointer& mp) const
{
  return *(begin(i,mp.dimension()) + index(mp));
}

// ----------------------------------------------------------

template<typename Object>
inline Object& CnContainer<Object>::operator()(int i, const Multipointer& mp, const Multipointer& sub)
{
  return *(begin(i,sub.dimension()) + index(mp,sub));
}

// ----------------------------------------------------------

template<typename Object>
inline const Object& CnContainer<Object>::operator()(int i, const Multipointer& mp, const Multipointer& sub) const
{
  return *(begin(i,sub.dimension()) + index(mp,sub));
}

// ----------------------------------------------------------

template<typename Object>
inline Object& CnContainer<Object>::operator()(int i, const Multiindex& mi)
{
  if(m_dim!=mi.dimension())
    throw std::runtime_error("CnContainer::operator(int,Multiindex) - incompatible dimensions of CnContainer and Multiindex");
  return *(begin(i,mi.module()) + index(mi));
}

// ----------------------------------------------------------

template<typename Object>
inline const Object& CnContainer<Object>::operator()(int i, const Multiindex& mi) const
{
  if(m_dim!=mi.dimension())
    throw std::runtime_error("CnContainer::operator(int,Multiindex) - incompatible dimensions of CnContainer and Multiindex");
  return *(begin(i,mi.module()) + index(mi));
}

// -------------- indexing for C^0-C^3 algorithms ------------

template<typename Object>
inline Object& CnContainer<Object>::operator()(int i)
{
  return *(m_data + i*newton(m_rank+m_dim,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline const Object& CnContainer<Object>::operator()(int i) const 
{
  return *(m_data + i*newton(m_rank+m_dim,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline Object& CnContainer<Object>::operator()(int i, int j)
{
  return *(begin(i,1)+j);
}

// ----------------------------------------------------------

template<typename Object>
inline const Object& CnContainer<Object>::operator()(int i, int j) const
{
  return *(begin(i,1)+j);
}

// ----------------------------------------------------------

template<typename Object>
inline Object& CnContainer<Object>::operator()(int i, int j, int c)
{
  return j<=c ? 
    *(begin(i,2)+c-(j*(j+1))/2+j*m_dim) :
    *(begin(i,2)+j-(c*(c+1))/2+c*m_dim);
}

// ----------------------------------------------------------

template<typename Object>
inline const Object& CnContainer<Object>::operator()(int i, int j, int c) const 
{
  return j<=c ? 
    *(begin(i,2)+c-(j*(j+1))/2+j*m_dim) :
    *(begin(i,2)+j-(c*(c+1))/2+c*m_dim);
}

// ----------------------------------------------------------

template<typename Object>
inline Object& CnContainer<Object>::operator()(int i, int j, int c, int k)
{
  // assume j<=c<=k
  if(c<j || k<c)
    throw std::runtime_error("CnContainer::operator(int,int,int,int) - incorrect indexes");
  return *(
    begin(i,3) +
    (j*( (j-1)*(j-2) + 3*m_dim*(m_dim-j+2) ))/6    +   ((j-c)*(c+j-2*m_dim-1))/2 + k-c
  );
}

// ----------------------------------------------------------

template<typename Object>
inline const Object& CnContainer<Object>::operator()(int i, int j, int c, int k) const
{
  // assume j<=c<=k
  if(c<j || k<c)
    throw std::runtime_error("CnContainer::operator(int,int,int,int) - incorrect indexes");
  return *(
    begin(i,3) +
    (j*( (j-1)*(j-2) + 3*m_dim*(m_dim-j+2) ))/6    +   ((j-c)*(c+j-2*m_dim-1))/2 + k-c
  );
}

// --------------- iterator selection -----------------------

template<typename Object>
inline typename CnContainer<Object>::iterator CnContainer<Object>::begin() 
{ 
  return iterator(m_data); 
}
   
// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::iterator CnContainer<Object>::end()   
{ 
  return iterator(m_data+m_size); 
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::iterator CnContainer<Object>::begin(int i) 
{
  return iterator(m_data+i*newton(m_dim+m_rank,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::iterator CnContainer<Object>::end(int i) 
{
  return iterator(m_data+(i+1)*newton(m_dim+m_rank,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::iterator CnContainer<Object>::begin(int i, int level) 
{
  return level==0 ? 
         iterator(m_data+ i*newton(m_dim+m_rank,m_dim))
         : iterator(m_data+ i*newton(m_dim+m_rank,m_dim) + newton(m_dim+level-1,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::iterator CnContainer<Object>::end(int i, int level) 
{
  return iterator(m_data+ i*newton(m_dim+m_rank,m_dim) + newton(m_dim+level,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::const_iterator CnContainer<Object>::begin() const
{ 
  return const_iterator(m_data); 
}
   
// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::const_iterator CnContainer<Object>::end() const
{ 
  return const_iterator(m_data+m_size); 
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::const_iterator CnContainer<Object>::begin(int i) const
{
  return const_iterator(m_data+i*newton(m_dim+m_rank,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::const_iterator CnContainer<Object>::end(int i) const
{
  return const_iterator(m_data+(i+1)*newton(m_dim+m_rank,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::const_iterator CnContainer<Object>::begin(int i, int level) const
{
  return level==0 ? 
            const_iterator(m_data+ i*newton(m_dim+m_rank,m_dim))
          : const_iterator(m_data+ i*newton(m_dim+m_rank,m_dim) + newton(m_dim+level-1,m_dim));
}

// ----------------------------------------------------------

template<typename Object>
inline typename CnContainer<Object>::const_iterator CnContainer<Object>::end(int i, int level) const
{
  return const_iterator(m_data+ i*newton(m_dim+m_rank,m_dim) + newton(m_dim+level,m_dim));
}

/// checks if two CnContainers are exactly the same.
template<typename Object>
bool operator== (const CnContainer<Object> & c1, const CnContainer<Object> & c2 ){
  if((c1.rank()!=c2.rank()) || (c1.dimension()!=c2.dimension()))
    return false;
  typename CnContainer<Object>::const_iterator it_c1 = c1.begin(), it_c2 = c2.begin(), end_c1 = c1.end();
  while(it_c1!=end_c1){
    if(*it_c1 != *it_c2)
       return false;
    it_c1++; it_c2++;
  }
  return true;
}

}} // namespace capd::map

#endif // _CAPD_MAP_CNCONTAINER_H_ 

/// @}
