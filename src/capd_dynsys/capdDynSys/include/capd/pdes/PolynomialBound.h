/// @addtogroup pdes
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file PolynomialBound.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_PDES_POLYNOMIALBOUND_H_ 
#define _CAPD_PDES_POLYNOMIALBOUND_H_ 

#include <map>
#include <iostream>

#include "capd/auxil/minmax.h"
#include "capd/basicalg/power.h"
#include "capd/vectalg/Container.h"
#include "capd/vectalg/Matrix.h"

namespace capd {
namespace pdes {

template<typename Scalar, typename Exponent, int M>
class PolynomialBound;

//*****************************************************************************/
// operator+
///
///  this operator realizes addition of two PolynomialBounds
///  
///  using the following formula
///     result_i = x_i + y_i 
///  Since object is represented as a finite dimensional vector and a tail
///  we do explicit summation on main variables only.
///  Exponent of result is computed as
///     t = min(x.exponent(),y.exponent())
///  The constant used in representation of tail in result is computed as
///     C_result = C_x/(M+1)^{x.exponent()-t} + C_y/(M+1)^{y.exponent()-t}
///
///   @param[in]  x      object of class PolynomialBound
///   @param[in]  y      object of class PolynomialBound
///
///  @returns    sum of x and y
///
/*****************************************************************************/
template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M> operator+(const PolynomialBound<Scalar, Exponent, M>& x, const PolynomialBound<Scalar, Exponent, M>& y);


//*****************************************************************************/
// operator-
///
///  this operator realizes subtraction of two PolynomialBounds
///  
///  using the following formula
///     result_i = x_i - y_i 
///  Since object is represented as a finite dimensional vector and a tail
///  we do explicit subtraction on main variables only.
///  Exponent of result is computed as
///     t = min(x.exponent(),y.exponent())
///  The constant used in representation of tail in result is computed as
///     C_result = C_x/(M+1)^{x.exponent()-t} + C_y/(M+1)^{y.exponent()-t}
///
///   @param[in]  x      object of class PolynomialBound
///   @param[in]  y      object of class PolynomialBound
///
///  @returns    difference of x and y
///
/*****************************************************************************/
template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M> operator-(const PolynomialBound<Scalar, Exponent, M>& v1, const PolynomialBound<Scalar, Exponent, M>& v2);


//*****************************************************************************/
// operator*
///
///  this operator realizes multiplication of any coefficient 
///  in PolynomialBound by some scalar
///  
///  using the following formula
///     result_i = s * p_i 
///
///   @param[in]  s      object of type Scalar
///   @param[in]  p      object of class PolynomialBound
///
///  @returns    PolynomialBound p multiplied by s
///
/*****************************************************************************/
template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M> operator*(const Scalar& s, const PolynomialBound<Scalar, Exponent, M>& v);



//*****************************************************************************/
// operator*
///
///  this operator realizes multiplication of any coefficient 
///  in PolynomialBound by some scalar
///  
///  using the following formula
///     result_i = s * p_i 
///
///   @param[in]  p      object of class PolynomialBound
///   @param[in]  s      object of type Scalar
///
///  @returns    PolynomialBound p multiplied by s
///
/*****************************************************************************/
template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M> operator*(const PolynomialBound<Scalar, Exponent, M>& p, const Scalar& s);



//*****************************************************************************/
// operator*
///
///  this operator realizes change of coordiante on some PolynomialBound
///  
///  if A is m\times m martix then the first m coordinates of result 
///  are given by 
///     result_i = \f$ \sum_{k=1}^m A_{i,k} p_k \f$
///  on the other coefficients change of coordinates is identity
///
///   @param[in]  A      square matrix of dimension smaller than p.dimension()
///   @param[in]  p      object of class PolynomialBound
///
///  @returns    PolynomialBound p in new coordinate system
///
/*****************************************************************************/
template<typename Scalar, typename Exponent, int M, int dim>
PolynomialBound<Scalar, Exponent, M> operator*(const capd::vectalg::Matrix<Scalar, dim, dim>& A, const PolynomialBound<Scalar, Exponent, M>& p);




//*****************************************************************************/
// operator<<
///
///  this operator writes a PolynomialBound object to a given stream
///  in the following form
///    {{p_1,p_2,...,p_M},C,exponent}
///  where M is a number of main coefficients in an object p
///
///   @param[in]  s      a stream to which object p is printed
///   @param[in]  p      object of class PolynomialBound
///
///  @returns    a reference to stream s
///
/*****************************************************************************/
template<typename Scalar, typename Exponent, int M>
std::ostream& operator << ( std::ostream& s, 
                              const PolynomialBound<Scalar, Exponent, M>& p
                            );



//*****************************************************************************/
// computeQF
///
///  the function computes value of operator QF on two PolynomialBounds y and w
///  given by 
///     QF_i = \f$ \sum_{k=1}^{i-1} y_k w_{i-k} \f$
///
///   @param[in]  y      object of class PolynomialBound
///   @param[in]  w      object of class PolynomialBound
///
///  @returns    value of operator QF on polynomial bounds y and w
///
/*****************************************************************************/
template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M>
computeQF(const PolynomialBound<Scalar, Exponent, M>& y,
          const PolynomialBound<Scalar, Exponent, M>& w
          );



//*****************************************************************************/
// computeQI
///
///  the function computes value of operator QI on two PolynomialBounds y and w
///  given by 
///     QI_i = \f$ \sum_{k=1}^\infty y_k w_{k+i} \f$
///
///   @param[in]  y      object of class PolynomialBound
///   @param[in]  w      object of class PolynomialBound
///
///  @returns    value of operator QI on polynomial bounds y and w
///
/*****************************************************************************/
template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M>
computeQI(const PolynomialBound<Scalar, Exponent, M>& y,
          const PolynomialBound<Scalar, Exponent, M>& w
          );




// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
class PolynomialBound : public capd::vectalg::Container<Scalar, M> {
public:
  typedef Scalar ScalarType;
  typedef Exponent ExponentType;

  typedef capd::vectalg::Container<Scalar, M> ContainerType;
  typedef typename ContainerType::iterator iterator;
  typedef typename ContainerType::const_iterator const_iterator;
  typedef typename ContainerType::iterator ContainerIterator;
  typedef typename ContainerType::const_iterator const_ContainerIterator;
  typedef std::map< std::pair<int, ExponentType>, ScalarType> PowerContainer;
  //   typedef Vector<int,dim> intVectorType;

  explicit PolynomialBound(int a_dim);
  PolynomialBound(int a_dim, bool);
  PolynomialBound(void) {}
  PolynomialBound(const PolynomialBound& p) : ContainerType(p){}  

  PolynomialBound(int a_dim, const ScalarType& a_C, Exponent a_alpha);
  PolynomialBound(int a_dim, const ScalarType& a_C, Exponent a_alpha, bool);
  PolynomialBound(int a_dim, const ScalarType& a_C, Exponent a_alpha, const ScalarType* a_coeff);
  
  PolynomialBound partialDerivative() const;

  ScalarType & operator[](int i) {
    if(i<size())
      return ContainerType::operator[](i);
    
    static ScalarType result;
    result = ScalarType(-m_C.rightBound(),m_C.rightBound()) / takePower(i +1, m_exponent);
    return result;    
  }

  const ScalarType& operator[](int i) const {
    if(i<size())
      return ContainerType::operator[](i);
    
    static ScalarType result;
    result = ScalarType(-m_C.rightBound(),m_C.rightBound()) / takePower(i +1, m_exponent);
    return result;    
  }

  const ScalarType& C() const {
    return m_C;
  }

  ScalarType& C() {
    return m_C;
  }

  const ExponentType& exponent() const {
    return m_exponent;
  }

  ExponentType& exponent() {
    return m_exponent;
  }

  static const ScalarType& takePower(int i, ExponentType t);

  using ContainerType::begin;
  using ContainerType::end;
  using ContainerType::size;
  using ContainerType::resize;

protected:
  ExponentType m_exponent;
  ScalarType m_C;
  static PowerContainer powers;
}; // end of class PolynomialBound

// --------------------- inline definitions -----------------------------------

template<typename Scalar, typename Exponent, int M>
inline PolynomialBound<Scalar, Exponent, M>::PolynomialBound(int A_dimension)
: ContainerType(A_dimension), m_exponent(0), m_C(1) {
}

template<typename Scalar, typename Exponent, int M>
inline PolynomialBound<Scalar, Exponent, M>::PolynomialBound(int A_dimension, bool)
: ContainerType(A_dimension, true), m_exponent(0), m_C(1) {
}

}
} // namespace capd::pdes


#endif // _CAPD_PDES_POLYNOMIALBOUND_H_ 


/// @}
