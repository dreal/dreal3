/// @addtogroup vectalg
/// @{

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
#include "capd/capd/minmax.h"
#include "capd/capd/power.h"
#include "capd/vectalg/Container.h"

namespace capd{
namespace vectalg{

template<typename Scalar, int dim>
class Vector;

template<typename Scalar, int dim>
std::ostream& operator<<(std::ostream& out, const Vector<Scalar,dim>& v);

template<typename Scalar, int dim>
std::istream& operator>>(std::istream& inp, Vector<Scalar,dim>& v);

// ---------------------------------------------------------------- //
// general algorithms for vectors and matrices

template<typename IntervalObject>
void split(IntervalObject&, IntervalObject&);

template<typename IntervalObject>
bool subset(const IntervalObject&, const IntervalObject&);

template<typename IntervalObject>
bool subsetInterior(const IntervalObject&, const IntervalObject&);

template<typename IntervalObject>
bool intersection(const IntervalObject &v1, const IntervalObject &v2, IntervalObject &result);

// ---------------------------------------------------------------- //

template<typename IVector>
IVector leftVector(const IVector&);

template<typename IVector>
IVector rightVector(const IVector&);

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
  typedef Vector<int,dim> intVectorType;

  Vector(void){}
  explicit Vector(int A_dimension); // for compatibility with dynamic version
  Vector(const Scalar& x, const Scalar& y,const Scalar& z);  //obsolete, requires dimension=3
  Vector(int,const ScalarType[]);
  Vector(const Vector&);
  explicit Vector(Vector<double,dim>&);
  Vector(int,bool); // it does not insert zeros
  void clear(void);              //assign zero to each coord

  // assignments - vectors
  Vector& operator=  (const Vector& v);      //assign a vector
  Vector& operator+= (const Vector& v);      //increase by a vector
  Vector& operator-= (const Vector& v);      //decrease by a vector

  // assignments - Scalars
  Vector& operator=  (const Scalar& s);       //assign a Scalar
  Vector& operator+= (const Scalar& s);       //increase by a Scalar
  Vector& operator-= (const Scalar& s);       //decrease by a Scalar
  Vector& operator*= (const Scalar& s);       //rescale by multiplying
  Vector& operator/= (const Scalar& s);       //rescale by dividing

  int dimension() const {return ContainerType::size();}
  using ContainerType::begin;
  using ContainerType::end;
  using ContainerType::resize;

  // Euclidean norm
  ScalarType euclNorm(void) const;
  //if possible vector is normalized and true is returned. Otherwise false is returned.
  bool normalize(void);
  void sorting_permutation(intVectorType& perm);
}; // end of class Vector template

template<typename Vector>
std::string vectorToString( const Vector & v, int firstIndex = 0, int lastIndex = -1);

}} // namespace capd::vectalg

#include "capd/vectalg/Vector_inline.h"

#endif // _CAPD_VECTALG_VECTOR_H_ 

/// @}

