/////////////////////////////////////////////////////////////////////////////
/// @file Vector.h
///
/// This file provides a template class Vector together with typical
/// algebraic operations. Most of them are defined as generic algorithms
/// in files 'commonOperations.h' and 'commonOperations.hpp'
/// For inline definitions of operators see to file
/// Vector_inline.h included at the end of this file.
///
/// The class uses class 'Container' as a container for coefficients
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _CAPD_VECTALG_VECTOR_H_ 
#define _CAPD_VECTALG_VECTOR_H_ 

#include <iostream>
#include <cstdlib>
#include <vector>
#include "capd/auxil/minmax.h"
#include "capd/basicalg/power.h"
#include "capd/vectalg/Container.h"
#include "capd/vectalg/iobject.h"

namespace capd{
namespace vectalg{

/// @addtogroup vectalg
/// @{


template<typename Scalar, int dim>
class Vector;

template<typename Scalar, int dim>
std::ostream& operator<<(std::ostream& out, const Vector<Scalar,dim>& v);

template<typename Scalar, int dim>
std::istream& operator>>(std::istream& inp, Vector<Scalar,dim>& v);

// ---------------------------------------------------------------- //
// general algorithms for vectors and matrices

template<typename IVector>
inline
IVector leftVector(const IVector& u)
{
  return leftObject<IVector>(u);
}

template<typename IVector>
inline
IVector rightVector(const IVector& u)
{
  return rightObject<IVector>(u);
}

template<typename IVector>
typename IVector::ScalarType size(const IVector&);

template<typename IVector>
IVector intervalBall(const IVector&, const typename IVector::ScalarType &r);

template<typename IVector>
typename IVector::ScalarType solveAffineInclusion(const IVector&,const IVector&,const IVector&);

template<typename IVector>
typename IVector::ScalarType solveAffineInclusion(const IVector&,const IVector&,const IVector&,int&);

template<typename IVector>
IVector intervalHull(const IVector&, const IVector&);

template<typename IVector>
IVector midVector(const IVector&);

template<typename IVector>
IVector diam(const IVector&);

template<typename IVector>
IVector intersection(const IVector&, const IVector&);


//########################### Vector template ################################//

template<typename Scalar, int dim>
class Vector : public Container<Scalar,dim>
{
public:
  typedef Scalar ScalarType;
  typedef Container<Scalar,dim> ContainerType;
  typedef typename ContainerType::iterator iterator;
  typedef typename ContainerType::const_iterator const_iterator;
  typedef Vector<Scalar,dim> VectorType;

  Vector(void){}
  explicit Vector(int a_dim); // for compatibility with heap-allocated specialization
  Vector(const Scalar& x, const Scalar& y,const Scalar& z);  //obsolete, requires dimension=3
  Vector(int,const ScalarType[]);
  explicit Vector(const char data[]);
  explicit Vector(const std::string & data);
  Vector(const Vector&);
  explicit Vector(Vector<double,dim>&);
  Vector(int,bool); // it does not insert zeros
  void clear(void);              //assign zero to each coord

#if( __cplusplus >= 201103L)
  Vector(Vector&& v) : ContainerType(v) {}
  Vector & operator=(Vector && v) {
     ContainerType::operator= ( static_cast< ContainerType &&>(v));
   //  std::cout << "\n v move =";
    return *this;
  }
#endif
  
  // assignments - vectors
  Vector& operator=  (const Vector& v);      //<assign a vector
  Vector& operator+= (const Vector& v);      //<add and assign a vector
  Vector& operator-= (const Vector& v);      //<subtract and assign a vector

  // assignments - Scalars
  Vector& operator=  (const Scalar& s);       //<assign a Scalar to each coordinate
  Vector& operator+= (const Scalar& s);       //<component-wise increase by a Scalar
  Vector& operator-= (const Scalar& s);       //<component-wise decrease by a Scalar
  Vector& operator*= (const Scalar& s);       //<scale by multiplying by Scalar
  Vector& operator/= (const Scalar& s);       //<scale by dividing by Scalar

  template<typename U>
  struct rebind {
      typedef Vector<U,dim> other;
  };

  int dimension() const {return ContainerType::size();}
  using ContainerType::begin;
  using ContainerType::end;
  using ContainerType::resize;

  // Euclidean norm
  ScalarType euclNorm(void) const;
  //if possible vector is normalized and true is returned. Otherwise false is returned.
  bool normalize(void);
  void sorting_permutation(typename rebind<int>::other& perm);

  const static int csDim = dim;
  static int degree() {return 0;} // required interface for DynSys
}; // end of class Vector template

template<typename Vector>
std::string vectorToString( const Vector & v, int firstIndex = 0, int lastIndex = -1, int precision = -1);

template<typename Vector>
std::ostream & printVector(std::ostream & str, const Vector & v, int firstIndex = 0, int lastIndex = -1);

template<typename Scalar, int dim>
inline std::ostream & print(std::ostream & str, const Vector<Scalar, dim> & v, int firstIndex = 0, int lastIndex = -1){
  return printVector(str, v, firstIndex, lastIndex);
}

/// @}


}} // namespace capd::vectalg

#include "capd/vectalg/Vector_inline.h"

#endif // _CAPD_VECTALG_VECTOR_H_ 

