/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file MatrixContainer.h
///
/// This file provides a class MatrixContainer
/// This class inherites form general Container class
/// and provides constructors and methods specific for two dimensional data
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_VECTALG_MATRIXCONTAINER_H_ 
#define _CAPD_VECTALG_MATRIXCONTAINER_H_ 

#include "capd/vectalg/Container.h"
#include <utility>

namespace capd{
namespace vectalg{

/// This class inherites form general Container class
/// and provides constructors and methods specific for two dimensional data
template<typename Scalar, int rows, int cols>
class MatrixContainer : public Container<Scalar,rows*cols>
{
  typedef Container<Scalar,rows*cols> BaseContainerType;
public:
  typedef Scalar ScalarType;
  typedef typename Container<Scalar,rows*cols>::iterator iterator;
  typedef typename Container<Scalar,rows*cols>::const_iterator const_iterator;
  typedef MatrixContainer ContainerType;
  typedef Container<Scalar,rows> ColumnContainer;
  typedef Container<Scalar,cols> RowContainer;
  typedef std::pair<int,int> Dimension;

  inline MatrixContainer() : Container<Scalar,rows*cols>() {}
  inline MatrixContainer(int a_rows, int a_cols) : Container<Scalar,rows*cols>(a_rows*a_cols){}
  inline MatrixContainer(const MatrixContainer& mc) : Container<Scalar,rows*cols>(mc) {}
  inline MatrixContainer(int a_rows, int a_cols,bool) : Container<Scalar,rows*cols>(a_rows*a_cols,true){}
  inline MatrixContainer(const Dimension&) : Container<Scalar,rows*cols>(1){}
  inline MatrixContainer(const Dimension&,bool) : Container<Scalar,rows*cols>(1,true){}
#if( __cplusplus >= 201103L)
  MatrixContainer(MatrixContainer&& v) : ContainerType(std::forward<ContainerType>(v)) {}
  MatrixContainer & operator=(MatrixContainer && v) {
     ContainerType::operator= ( std::forward<ContainerType>(v));
   //  std::cout << "\n v move =";
    return *this;
  }
#endif
  
  inline int numberOfRows() const {return rows;}
  inline int numberOfColumns() const {return cols;}

  inline MatrixContainer& operator=(const MatrixContainer& a)
  {
    Container<Scalar,rows*cols>::operator=(a);
    return *this;
  }
  inline static void* operator new[](size_t sizeOfData)
  {
    return ::operator new[](sizeOfData);
  }
  inline static void* operator new[](size_t sizeOfData, int, int)
  {
    return ::operator new[](sizeOfData);
  }

  using Container<Scalar,rows*cols>::begin;
  using Container<Scalar,rows*cols>::end;
  using Container<Scalar,rows*cols>::size;
  static Dimension dimension() { return Dimension(rows,cols); }
  static void setDefaultDimension(Dimension d){}
  inline void resize(int r, int c)
  {
    if(r!=rows || c!=cols)
      throw std::range_error("Cannot resize static MatrixContainer");
  }
protected:

  using Container<Scalar,rows*cols>::data;
//  static const Dimension m_dim(rows,cols);
};

// ---------------------------------------------------------------------

template<typename Scalar>
class MatrixContainer<Scalar,0,0> : public Container<Scalar,0>
{
public:
  typedef Scalar ScalarType;
  typedef typename Container<Scalar,0>::iterator iterator;
  typedef typename Container<Scalar,0>::const_iterator const_iterator;
  typedef MatrixContainer ContainerType;
  typedef Container<Scalar,0> ColumnContainer;
  typedef Container<Scalar,0> RowContainer;
  typedef std::pair<int,int> Dimension;
  
  inline MatrixContainer()
    : Container<Scalar,0>(defaultRows*defaultCols),
      m_rows(defaultRows), m_cols(defaultCols)
  {}
  inline MatrixContainer(int a_rows, int a_cols)
    : Container<Scalar,0>(a_rows*a_cols), m_rows(a_rows), m_cols(a_cols)
  {}
  inline MatrixContainer(const MatrixContainer& mc)
    : Container<Scalar,0>(mc), m_rows(mc.m_rows), m_cols(mc.m_cols)
  {}
  inline MatrixContainer(int a_rows, int a_cols,bool)
    : Container<Scalar,0>(a_rows*a_cols,true), m_rows(a_rows), m_cols(a_cols)
  {}
  inline MatrixContainer(const Dimension& d,bool)
    : Container<Scalar,0>(d.first*d.second,true), m_rows(d.first), m_cols(d.second)
  {}
  inline MatrixContainer(const Dimension& d)
    : Container<Scalar,0>(d.first*d.second), m_rows(d.first), m_cols(d.second)
  {}
  
  friend void swap(MatrixContainer<Scalar,0,0>& A_m1, MatrixContainer<Scalar,0,0>& A_m2)
  {
    std::swap(*static_cast<Container<Scalar,0>*>(&A_m1),*static_cast<Container<Scalar,0>*>(&A_m2));
    std::swap(A_m1.m_rows,A_m2.m_rows);
    std::swap(A_m1.m_cols,A_m2.m_cols);
  }

  inline int numberOfRows() const {return m_rows;}
  inline int numberOfColumns() const {return m_cols;}

  MatrixContainer& operator=(const MatrixContainer& a)
  {
    Container<Scalar,0>::operator=(a);
    m_rows = a.m_rows;
    m_cols = a.m_cols;
    return *this;
  }
  static void* operator new[](size_t sizeOfData)
  {
    return ::operator new[](sizeOfData);
  }
  static void* operator new[](size_t sizeOfData, int defR, int defC)
  {
    defaultRows = defR;
    defaultCols = defC;
    return ::operator new[](sizeOfData);
  }

  using Container<Scalar,0>::begin;
  using Container<Scalar,0>::end;
  using Container<Scalar,0>::size;
  inline Dimension dimension() const {return Dimension(m_rows,m_cols);}
  static void setDefaultDimension(Dimension d){
    defaultRows = d.first;
    defaultCols = d.second;
  }
  inline void resize(int r, int c)
   {
     if(r!=m_rows || c!=m_cols)
     {
       Container<Scalar,0>::resize(r*c);
       m_rows = r;
       m_cols = c;
     }
   }
protected:
  int m_rows,m_cols;
  static int defaultRows, defaultCols;

  using Container<Scalar,0>::resize;

  using Container<Scalar,0>::data;
};

template<typename Scalar>
int MatrixContainer<Scalar,0,0>::defaultRows=0;

template<typename Scalar>
int MatrixContainer<Scalar,0,0>::defaultCols=0;

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_MATRIXCONTAINER_H_ 

/// @}
