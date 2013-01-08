/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Container.h
///
/// This file provides a template class Container together with suitable iterators
/// The container has fixed size specified by a template argument 'capacity'
///
/// Also a specialization of this class for capacity=0 is defined
/// In that case objects in this container are allocated on storage instead of stack
///
/// This class is used as a container for vectors, matrices and higher order containers
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _CAPD_VECTALG_CONTAINER_H_ 
#define _CAPD_VECTALG_CONTAINER_H_ 

#include <stdexcept>
#include <cstdlib> // for size_t
#include <new>

namespace capd{
namespace vectalg{

/// class Container together with suitable iterators
/// The container has fixed size specified by a template argument 'capacity'
///
/// This class is used as a container for vectors, matrices and higher order containers
template<typename Scalar, int capacity>
class Container
{
public:
  typedef Scalar ScalarType;
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  Container();
  explicit Container(int);
  Container(int,bool); // it does not insert zeros

  iterator begin();
  iterator end();
  const_iterator begin() const;
  const_iterator end() const;

  Container& operator=(const Container&);
  void resize(int newCapacity);

  ScalarType& operator[](int);
  const ScalarType& operator[](int) const;
  ScalarType& operator()(int);
  const ScalarType& operator()(int) const;
  friend void swap(Container<Scalar,capacity>& A_c1, Container<Scalar,capacity>& A_c2)
  {
    iterator b=A_c1.begin(), e=A_c1.end();
    iterator i = A_c2.begin();
    while(b!=e)
    {
      std::swap(*b,*i);
      ++b;
      ++i;
    }
  }
  void clear();
// memory allocation
  static void* operator new[](size_t sizeOfData, int);
  static void* operator new[](size_t sizeOfData);
  static void setDefaultDimension(int newDefaultDimension){}
  static int size() {return capacity;}
  
protected:
  ScalarType data[capacity];
};

/// Specialization for capacity=0
/// This container allocates objects on a storage
template<typename Scalar>
class Container<Scalar,0>
{
public:
  typedef Scalar ScalarType;
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  Container();
  explicit Container(int);
  Container(int,bool); // it does not insert zeros
  Container(const Container&);
  ~Container();

  iterator begin();
  iterator end();
  const_iterator begin() const;
  const_iterator end() const;

  Container& operator=(const Container&);
  void resize(int);

  ScalarType& operator[](int);
  const ScalarType& operator[](int) const;
  ScalarType& operator()(int);
  const ScalarType& operator()(int) const;
  friend void swap(Container<Scalar,0>& A_c1, Container<Scalar,0>& A_c2)
  {
     std::swap(A_c1.data,A_c2.data);
     std::swap(A_c1.capacity,A_c2.capacity);
  }

  static void* operator new[](size_t sizeOfData, int);
  static void* operator new[](size_t sizeOfData);
  static void setDefaultDimension(int newDefaultDimension)
  {
    defaultSize = newDefaultDimension;
  }
  int size() const {return capacity;}
  void clear();

protected:
  ScalarType *data;
  int capacity;
  static int defaultSize;
};

// ---- inline definitions for Containers ----------------- //

// --------------- iterator selection --------------------- //

template<typename Scalar, int capacity>
inline typename Container<Scalar,capacity>::iterator Container<Scalar,capacity>::begin()
{
  return iterator(data);
}

template<typename Scalar, int capacity>
inline typename Container<Scalar,capacity>::iterator Container<Scalar,capacity>::end()
{
  return iterator(data+capacity);
}

template<typename Scalar, int capacity>
inline typename Container<Scalar,capacity>::const_iterator Container<Scalar,capacity>::begin() const
{
  return const_iterator(data);
}

template<typename Scalar, int capacity>
inline typename Container<Scalar,capacity>::const_iterator Container<Scalar,capacity>::end() const
{
  return const_iterator(data+capacity);
}

template<typename Scalar>
inline typename Container<Scalar,0>::iterator Container<Scalar,0>::begin()
{
  return iterator(data);
}

template<typename Scalar>
inline typename Container<Scalar,0>::iterator Container<Scalar,0>::end()
{
  return iterator(data+capacity);
}

template<typename Scalar>
inline typename Container<Scalar,0>::const_iterator Container<Scalar,0>::begin() const
{
  return const_iterator(data);
}

template<typename Scalar>
inline typename Container<Scalar,0>::const_iterator Container<Scalar,0>::end() const
{
  return const_iterator(data+capacity);
}

// ------------------------- indexing ------------------------ //

template<typename Scalar, int capacity>
inline Scalar& Container<Scalar,capacity>::operator[] (int i)
{
  return data[i];
}

template<typename Scalar, int capacity>
inline const Scalar& Container<Scalar,capacity>::operator[] (int i) const
{
  return data[i];
}

template<typename Scalar, int capacity>
inline Scalar& Container<Scalar,capacity>::operator() (int i)
{
  return data[i-1];
}

template<typename Scalar, int capacity>
inline const Scalar& Container<Scalar,capacity>::operator() (int i) const
{
  return data[i-1];
}

template<typename Scalar>
inline Scalar& Container<Scalar,0>::operator[] (int i)
{
  return data[i];
}

template<typename Scalar>
inline const Scalar& Container<Scalar,0>::operator[] (int i) const
{
  return data[i];
}

template<typename Scalar>
inline Scalar& Container<Scalar,0>::operator() (int i)
{
  return data[i-1];
}

template<typename Scalar>
inline const Scalar& Container<Scalar,0>::operator() (int i) const
{
  return data[i-1];
}

// ----------------- memory allocation ------------------------

template <typename Scalar, int capacity>
inline void* Container<Scalar,capacity>::operator new[](size_t sizeOfData)
{
  return ::operator new[](sizeOfData);
}

template <typename Scalar, int capacity>
inline void* Container<Scalar,capacity>::operator new[](size_t sizeOfData,int)
{
  return ::operator new[](sizeOfData);
}

template <typename Scalar>
inline void* Container<Scalar,0>::operator new[](size_t sizeOfData)
{
  return ::operator new[](sizeOfData);
}

template <typename Scalar>
inline void* Container<Scalar,0>::operator new[](size_t sizeOfData,int newSize)
{
  defaultSize = newSize;
  return ::operator new[](sizeOfData);
}

// ------------ constructor - desctructor --------------------

template<typename Scalar, int capacity>
inline Container<Scalar,capacity>::Container(int,bool)
{}

template<typename Scalar>
inline Container<Scalar,0>::Container(int a_capacity,bool) : capacity(a_capacity)
{
  data = new ScalarType[capacity];
}

template<typename Scalar>
inline Container<Scalar,0>::~Container()
{
  delete [] data;
}


}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_CONTAINER_H_ 

/// @}
