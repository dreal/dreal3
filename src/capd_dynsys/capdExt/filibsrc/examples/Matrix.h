/*                                                                           
**  fi_lib++  --- A fast interval library (Version 2.0)                     
**                                                                  
**  Copyright (C) 2001:                                                        
**                                                     
**  Werner Hofschuster, Walter Kraemer                               
**  Wissenschaftliches Rechnen/Softwaretechnologie (WRSWT)  
**  Universitaet Wuppertal, Germany                                           
**  Michael Lerch, German Tischler, Juergen Wolff von Gudenberg       
**  Institut fuer Informatik                                         
**  Universitaet Wuerzburg, Germany                                           
** 
**  This library is free software; you can redistribute it and/or
**  modify it under the terms of the GNU Library General Public
**  License as published by the Free Software Foundation; either
**  version 2 of the License, or (at your option) any later version.
**
**  This library is distributed in the hope that it will be useful,
**  but WITHOUT ANY WARRANTY; without even the implied warranty of
**  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
**  Library General Public License for more details.
**
**  You should have received a copy of the GNU Library General Public
**  License along with this library; if not, write to the Free
**  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
*/
#ifndef _MATRIX_H
#define _MATRIX_H

#include <iostream>
#include <cassert>

// ---------------
// class Matrix<T>
// ---------------
template <class T>
class Matrix
{
public:
  typedef T value_type;
protected:
  unsigned int m,n;
  T *data;

public:
  
  Matrix(unsigned int rows, unsigned int cols)
    : m(rows), n(cols)
  {
    unsigned int size = m*n;
    assert (data = new T[size]);
  }

  Matrix (const Matrix<T> &A) 
  {
    m = A.m;
    n = A.n;
    unsigned int size = m*n;
    assert (data = new T[size]);
    for (unsigned  i=0; i<size; i++)
      data[i] = A.data[i];
  }

  ~Matrix()
  {
    delete [] data;
  }

  Matrix<T> &operator =(const Matrix<T> &A)
  {
    if (&A != this) {
      unsigned int size = A.m*A.n;
      if (size != m*n) {
	delete [] data;
	assert(data = new T[size]);
      }
      m = A.m;
      n = A.n;
      for (int i=0; i<size; i++)
	data[n] = A.data[n];
    }
    return *this;
  }

  T &operator ()(unsigned int i, unsigned int j)
  {
    assert (i<m && j<n);
    return data[i*n+j];
  }

  const T &operator()(unsigned int i, unsigned int j) const
  {
    assert (i<m && j<n);
    return data[i*n+j];
  }

  unsigned int rows() const
  {
    return m;
  }

  unsigned int cols() const
  {
    return n;
  }

  friend std::ostream &operator <<(std::ostream &os, const Matrix<T> &A)
  {
    for (unsigned int i=0; i<A.rows(); i++) {
      for (unsigned int j=0; j<A.cols(); j++)
        os << const_cast<T&>(A(i,j)) << " ";
      os << std::endl;
    }

    return os;
  }

};

#endif

















