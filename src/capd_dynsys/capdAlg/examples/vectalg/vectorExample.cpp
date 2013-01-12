/*
   author: Daniel Wilczak, Sept. 2007
   the file provides a quick tutorial on using template class Vector from capd library
 */

#include <iostream>
#include "capd/intervals/lib.h"
#include "capd/vectalg/Vector.hpp"

using capd::DInterval;

// The template class Vector has two parameters - type which is stored in a vector and capacity
// if capacity is greater than zero, vector is represented as an internal array of given length
// if capacity is equal to zero, the dimension of a vector must be set during creation of an object.

// the following lines define new names for four dimensional vectors 
typedef capd::vectalg::Vector<double,4> DVector4D;
typedef capd::vectalg::Vector<DInterval,4> IVector4D;

// the following lines define new names for vectors of an arbitrarily length
typedef capd::vectalg::Vector<double,0> DVector;
typedef capd::vectalg::Vector<DInterval,0> IVector;

int main(int, char**)
{
  try{
    // --------------------------------- how to create a vector ---------------------------------------------

    std::cout << "How to create a vector\n--------------------------------\n\n";

    // The following line creates a four dimensional vector filled by zeros
    DVector4D x;

    // Vector y will be a five dimensional interval vector filled by zeros
    IVector y(5);
    std::cout << "x=" << x << std::endl;
    std::cout << "y=" << y << std::endl;

    // The following lines create objects from a given table of numbers.
    // In fact, the dimension is known, but the interfaces for both types of vectors
    // (dynamic table and internal array) are the same - so we must specify the dimension in both cases

    double data1[] = {1.,2.,3.,4.};
    double data2[] = {4.,3.,2.,1.};

    DVector4D a(4,data1);
    DVector4D b(4,data2);

    std::cout << "a=" << a << std::endl;
    std::cout << "b=" << b << std::endl;

    // --------------------------------- arrays of vectors --------------------------------------------------

    std::cout << "\n\nHow to create an array of vectors\n--------------------------------\n\n";

    // When one needs to create an array of vectors which have undefined dimensions at compilation time,
    // the following solution is available. The class Vector has a static function which sets a default
    // dimension for all objects which will be create by default constructor

    DVector::setDefaultDimension(5);
    DVector *tab = new DVector[6];
    std::cout << "The dimension of all vectors in array is: " << tab[3].dimension() << std::endl;
    delete []tab;

    // The above can be also written in short form
    tab = new (7) DVector[10];
    // which means that tab contains an adress of a table of ten vectors, each of dimension 7

    std::cout << "The dimension of all vectors in second array is: " << tab[8].dimension() << std::endl;
    delete []tab;

    // When the same mathods are applied to the vectors of fixed dimension, there is no effect
    // i.e. all vectors in array will have dimension as specified in argument of template.
    DVector4D *tab2 = new (10) DVector4D[5];
    std::cout << "The dimension of all vectors in third array is: " << tab2[3].dimension() << std::endl;
    delete []tab2;

    // --------------------------------- indexing and iterators ---------------------------------------------

    std::cout << "\n\nIndexing and iterators\n--------------------------------\n\n";

    // One can change or access a coefficient in vectors by using of operator[] or iterators.
    std::cout << "operator[] : \n";
    for(int i=0;i<a.dimension();++i)
    {
      std::cout << "b[" << i << "]=";
      std::cout << b[i];
      //one can set a coefficient in nonconstant vector
      a[i] = i*i;
      std::cout << "\nNew value of a[" << i << "]=" << a[i] << std::endl;
    }
    // the other way is to use iterators instead of indexing
    DVector::iterator bg = b.begin(), en = b.end();
    while(bg!=en)
    {
      std::cout << "value of an iterator: " << bg << "\ncoefficient in a vector: " << (*bg) << std::endl;
      ++bg;
    }
    // in a similar way are defined const iterators for constant objects

    const DVector c(4,data1);
    DVector::const_iterator p = c.begin(), k = c.end();
    std::cout << "\nCoefficients in constant vector:\n";
    while(p!=k)
    {
      std::cout << (*p) << std::endl;
      ++p;
    }

    // --------------------------------- basic operations on vectors ---------------------------------------------

    std::cout << "\n\nBasic operation on vectors\n--------------------------------\n\n";
    // the following operations on vectors are available
    std::cout << "a=" << a << std::endl;
    std::cout << "b=" << b << std::endl;
    std::cout << "a+b=" << (a+b) << std::endl;
    std::cout << "a-b=" << (a-b) << std::endl;
    std::cout << "a*b=" << (a*b) << ", euclidean scalar product" << std::endl;
    std::cout << "2*a=" << 2*a << std::endl;
    std::cout << "if a==b? " << (a==b) << std::endl  << std::endl;
    // moreover, the standard operations like +=, -= etc. when possible are available

    std::cout << "euclidean norm of b: " << b.euclNorm() << std::endl;
    a.normalize();
    std::cout << "normalization with respect to euclidean norm of a: " << a << std::endl;

    // --------------------------------- operations for interval vectors only -------------------------------------

    std::cout << "\n\noperations for interval vectors only\n--------------------------------\n\n";
    DInterval d1[] = {DInterval(-1.,1.), DInterval(2.,2.), DInterval(3.,3.1), DInterval(4.,4.1)};
    IVector v1(4,d1);
    std::cout << "v1=" << v1 << std::endl;
    // center of a vector
    std::cout << "midVector(v1) = " << midVector(v1) << std::endl;

    IVector v2(4);
    // splitting: v2 = v1-midVector(v1) and v1 = midVector(v1). This operation is given by function
    split(v1,v2);
    std::cout << "\nafter calling split(v1,v2) we get\n";
    std::cout << "v1=" << v1 << std::endl;
    std::cout << "v2=" << v2 << std::endl;

    // left and right vectors - function which return vector of left or right ends, respectively
    std::cout << "\nleftVector(v2)= " << leftVector(v2) << std::endl;
    std::cout << "rightVector(v2)= " << rightVector(v2) << std::endl;

    std::cout << "\ndiameter of a vector\n";
    // this operation returns a vector which contains diameter of each coefficient in vector
    std::cout << "diam(v2) = " << diam(v2) << std::endl;

    // subset - this function verifies if one interval vector is a subset of the second. Returns 0 or 1.
    std::cout << "\nsubset(v1,v1+v2)=" << subset(v1,v1+v2) << std::endl;
    // this function verifies if first argument is a subset of an interior of the second vector
    std::cout << "subsetInterior(v1,v1+v2)=" << subsetInterior(v1,v1+v2) << std::endl;

    // for more details see the header file "vectalg/vectorintf.h"
  }catch(std::exception& e)
  {
    std::cout << e.what();
  }
  return 0;
}
