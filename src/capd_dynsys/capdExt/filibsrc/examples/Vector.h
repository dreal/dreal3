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
#ifndef VECTOR_H
#define VECTOR_H

#include <iostream>
#include <cassert>

// ---------------
// class Vector<T>
// ---------------
template <class T>
class Vector
{
public:
  typedef T value_type;
  
  Vector(unsigned int length)
    : n(length)
  {
    assert (data = new T[n]);
  }

  Vector(const Vector<T> &x) 
  {
    n = x.n;
    assert (data = new T[n]);
    for (int i=0; i<n; i++)
      data[i] = x.data[i];
  }

  ~Vector()
  {
    delete [] data;
  }
  
  Vector<T> &operator =(const Vector<T> &x) 
  {
    if (&x != this) {
      if (n != x.n) {
	delete [] data;
	n = x.n;
	assert(data = new T[n]);
      }
      for (int i=0; i<n; i++)
	data[i] = x.data[i];
    }
    return *this;
  }

  T &operator [](unsigned int i)
  {
    assert (i<n);
    return data[i];
  }

  const T &operator[](unsigned int i) const
  {
    assert (i<n);
    return data[i];
  }

  unsigned int size() const
  {
    return n;
  }

  friend std::ostream &operator <<(std::ostream &os, const Vector<T> &v)
  {
    for (unsigned int i=0; i<v.size(); i++) 
      os << const_cast<T&>(v[i]) << std::endl;
    os << std::endl;

    return os;
  }

protected:
  unsigned int n;
  T *data;
};

#endif
