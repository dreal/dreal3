/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Multiindex.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_VECTALG_MULTIINDEX_H_ 
#define _CAPD_VECTALG_MULTIINDEX_H_ 

#include <stdexcept>
#include <vector>
#include "capd/vectalg/Vector.h"
#include "capd/capd/TypeTraits.h"

namespace capd{
namespace vectalg{


class Multiindex;


/// Multipointer always contains nondecreasing list of indexes of variables.
///
/// For partial derivatives they denote variables with respect to which we differentiate.
/// For example, a Multipointer mp=(0,0,2,3) corresponds to partial derivative
/// \f$ \frac{\partial^4}{\partial x_0^2 \partial x_2 \partial x_3} \f$
///
/// For power series multipointer denotes variables that form monomial.
/// e.g.Multipointer mp=(0,0,2,3) correspond to monomial \f$ x_0^2x_2x_3\f$
///
class Multipointer : public Vector<int,0>
{
public:
  typedef Vector<int,0>::iterator iterator;
  typedef Vector<int,0>::const_iterator const_iterator;
  
  Multipointer(void){}
  explicit Multipointer(int A_dimension) : Vector<int,0>(A_dimension){}
  explicit Multipointer(const Multiindex&);
  Multipointer(int a_dim, int a_data[]) : Vector<int,0>(a_dim,a_data){}
  Multipointer(int a_dim,bool) : Vector<int,0>(a_dim,true){}

  /// order of derivative
  inline int module() const{
    return dimension();
  }
  long factorial() const;
  Multipointer subMultipointer(const Multipointer& mp) const;
  
  typedef std::vector<Multipointer> MultipointersVector;
  typedef std::vector<MultipointersVector> IndicesSet;
  static const IndicesSet& generateList(int p, int k);

private:
  static std::vector<IndicesSet> indices;
  static void computeNextLevel();
  static int maxKnownLevel;   
  inline static IndicesSet& getList(int n, int k)
  {
    return indices[n*(n-1)/2+k-1];
  }
};

// -------------------------------------------------------------------------------

/// For a Multiindex mi, mi[p] is a number of differentiation with respect to i-th variable.
/// For example, a Multipointer mp=(0,0,2,3) in 5-dimensional space corresponds to
/// the Multiindex mi=(2,0,1,1,0).
/// Hence, Multiindex agrees with standard notation and it contains an additional information
/// about the dimension of the domain of the function.
///
/// For polynomial:  Multiindex stores exponents of a given monomial.
/// e.g. monomial \f$ x^2 z^3 \f$ of 4 variables (x,y,z,t) has multiindex (2,0,3,0)
///
class Multiindex : public Vector<int,0>
{
public:
  typedef Vector<int,0>::iterator iterator;
  typedef Vector<int,0>::const_iterator const_iterator;
  typedef std::vector<Multiindex> MultiindexVector;
  typedef std::vector<MultiindexVector> IndicesSet;

  Multiindex(void){}
  explicit Multiindex(int A_dimension) : Vector<int,0>(A_dimension){}
  Multiindex(int A_dimension, const Multipointer&);
  Multiindex(int a_dim, int a_data[]) : Vector<int,0>(a_dim,a_data){}
  Multiindex(int a_dim,bool) : Vector<int,0>(a_dim,true){}
   
  int module() const;          ///< returns sum of multiindex coordinates (i.e. degree of monomial)
  long factorial() const;      ///< for multiindex (a,b,..,n) returns a!b!...n!
  static void generateList(int n, int k, IndicesSet& result);
};

// -------------------------------------------------------------------------------

Multipointer sumMultipointers(const Multipointer&, const Multipointer&);

/// returns new multipointer which is multiindex mp with index added in correct place
Multipointer addIndex(const Multipointer & mp, int index);

/// appends index to the end of multipointer mp
Multipointer push_back(const Multipointer & mp, int index);


}} // namespace capd::vectalg

// -------------------------------------------------------------------------------

///
/// It computes v^m where v is a vector and m is a multiindex
///

template<typename VectorType>
typename VectorType::ScalarType power(const VectorType& v, const capd::vectalg::Multiindex& m)
{
  using namespace capd::vectalg;
  if(v.dimension()!=m.dimension())
    throw std::runtime_error("power(vector,multiindex) error: different dimensions of vector and multiindex");
  typename VectorType::ScalarType result=1;
  typename VectorType::const_iterator b=v.begin(), e=v.end();
  typename Multiindex::const_iterator i=m.begin();
  while(b!=e)
  {
    result *= power(*b,*i);
    ++b;
    ++i;
  }
  return result;
}

// -------------------------------------------------------------------------------

template<typename VectorType>
typename VectorType::ScalarType power(const VectorType& v, const capd::vectalg::Multipointer& m)
{
  using namespace capd::vectalg;
  typedef typename VectorType::ScalarType ScalarType;
  ScalarType result = capd::TypeTraits<ScalarType>::one();
  typename Multipointer::const_iterator b=m.begin(), e=m.end();
  while(b!=e)
  {
    typename Multipointer::const_iterator temp=b;
    int p = *b;
    do{
      ++b;
    }while(b!=e && *b==p);
    size_t n = b-temp;
    result *= power(v[p],(int)n);
  }
  return result;
}

#endif // _CAPD_VECTALG_MULTIINDEX_H_ 

/// @}
