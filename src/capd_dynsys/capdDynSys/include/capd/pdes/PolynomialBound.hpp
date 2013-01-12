/// @addtogroup pdes
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file PolynomialBound.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#ifndef _CAPD_PDES_POLYNOMIALBOUND_HPP_ 
#define _CAPD_PDES_POLYNOMIALBOUND_HPP_ 

#include "capd/pdes/PolynomialBound.h"
namespace capd {
namespace pdes {

// static member
template<typename Scalar, typename Exponent, int M>
typename PolynomialBound<Scalar, Exponent, M>::PowerContainer PolynomialBound<Scalar, Exponent, M>::powers;

// static function
template<typename Scalar, typename Exponent, int M>
const Scalar& PolynomialBound<Scalar, Exponent, M>::takePower(int i, Exponent t) {
  std::pair<int, Exponent> index(i, t);
  typename PowerContainer::iterator b = powers.find(index);
  if (b != powers.end())
    return b->second;
  return powers[index] = power(ScalarType(i), t);
}

// ---------------------------- constructors ----------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M>::PolynomialBound(int a_dim, const ScalarType& a_C, Exponent a_alpha)
: ContainerType(a_dim), m_exponent(a_alpha), m_C(a_C) {
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M>::PolynomialBound(int a_dim, const ScalarType& a_C, Exponent a_alpha, bool)
: ContainerType(a_dim, true), m_exponent(a_alpha), m_C(a_C) {
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M>::PolynomialBound(int a_dim, const ScalarType& a_C, Exponent a_alpha, const ScalarType* a_coeff)
: ContainerType(a_dim, true), m_exponent(a_alpha), m_C(a_C) {
  iterator b = begin(), e = end();
  while (b != e) {
    *b = *a_coeff;
    ++b;
    ++a_coeff;
  }
}

// --------------------------- operators --------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M> operator+(const PolynomialBound<Scalar, Exponent, M>& v1, const PolynomialBound<Scalar, Exponent, M>& v2) {
  typedef PolynomialBound<Scalar, Exponent, M> PolyType;
  if (v1.dimension() != v2.dimension())
    throw std::runtime_error("Cannot add two PolynomialBounds of different dimensions");

  Exponent t = capd::min(v1.exponent(), v2.exponent());
  Scalar C = v1.C() / PolyType::takePower(v1.dimension() + 1, v1.exponent() - t)
    + v2.C() / PolyType::takePower(v2.dimension() + 1, v2.exponent() - t);

  PolyType result(v1.dimension(), C, t, true);
  typename PolyType::const_iterator b1 = v1.begin(), b2 = v2.begin();
  typename PolyType::iterator b = result.begin(), e = result.end();
  while (b != e) {
    *b = (*b1) + (*b2);
    ++b;
    ++b1;
    ++b2;
  }
  return result;
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M> operator-(const PolynomialBound<Scalar, Exponent, M>& v1, const PolynomialBound<Scalar, Exponent, M>& v2) {
  typedef PolynomialBound<Scalar, Exponent, M> PolyType;
  if (v1.dimension() != v2.dimension())
    throw std::runtime_error("Cannot add two PolynomialBounds of different dimensions");

  Exponent t = capd::min(v1.exponent(), v2.exponent());
  Scalar C = v1.C() / PolyType::takePower(v1.dimension() + 1, v1.exponent() - t)
    + v2.C() / PolyType::takePower(v2.dimension() + 1, v2.exponent() - t);

  PolyType result(v1.dimension(), C, t, true);
  typename PolyType::const_iterator b1 = v1.begin(), b2 = v2.begin();
  typename PolyType::iterator b = result.begin(), e = result.end();
  while (b != e) {
    *b = (*b1) - (*b2);
    ++b;
    ++b1;
    ++b2;
  }
  return result;
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M> operator*(const Scalar& s, const PolynomialBound<Scalar, Exponent, M>& v) {
  typedef PolynomialBound<Scalar, Exponent, M> PolyType;
  PolyType result(v.dimension(), s * v.C(), v.exponent(), true);
  typename PolyType::iterator b = result.begin(), e = result.end();
  typename PolyType::const_iterator i = v.begin();
  while (b != e) {
    *b = s * (*i);
    ++b;
    ++i;
  }
  return result;
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M> operator*(const PolynomialBound<Scalar, Exponent, M>& v, const Scalar& s) {
  return s*v;
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M, int dim>
PolynomialBound<Scalar, Exponent, M> operator*(const capd::vectalg::Matrix<Scalar, dim, dim>& A, const PolynomialBound<Scalar, Exponent, M>& v) {
  typedef PolynomialBound<Scalar, Exponent, M> PolyType;
  if (A.numberOfRows() > v.dimension() || A.numberOfColumns() > v.dimension())
    throw std::runtime_error("Cannot multiply matrix by PolynomialBound - incorrect dimensions");

  PolyType result(v.dimension(), v.C(), v.exponent(),true);
  int i;
  for (i = 1; i <= A.numberOfColumns(); ++i) {
    result[i - 1] = Scalar(0);
    for (int j = 1; j <= A.numberOfColumns(); ++j)
      result[i - 1] += A(i, j) * v[j - 1];
  }

  for (i = A.numberOfRows(); i < v.dimension(); ++i)
    result[i] = v[i];
  return result;
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M>
computeQF(const PolynomialBound<Scalar, Exponent, M>& y,
          const PolynomialBound<Scalar, Exponent, M>& w
          ) {
  int d = y.dimension();
  typedef PolynomialBound<Scalar, Exponent, M> PolyType;
  if (d != w.dimension())
    throw std::runtime_error("Incorrect dimensions in funtion computeQF in PolynomialBound.hpp");

  PolyType result(d, true);
  int i, k;
  // first we compute coefficients for indexes 1,...,dimension
  for (i = 1; i <= d; ++i) {
    result[i - 1] = Scalar(0);
    for (k = 1; k < i; ++k)
      result[i - 1] += y[k - 1] * w[i - k - 1];
  }

  // next we compute exponent of the result
  Exponent t = capd::min(y.exponent(), w.exponent());

  // next we compute constant of result as a maximum of two numbers C1 and C2

  Scalar C1(0);
  for (i = d + 1; i <= 2 * d; ++i) {
    Scalar QFi(0);
    for (k = 1; k < i; ++k)
      QFi += y[k - 1] * w[i - k - 1];
    QFi *= PolyType::takePower(i, t - 1);
    C1 = capd::max(C1, capd::abs(QFi));
  }

  // now we compute C2
  int M21 = 2 * d + 1;
  Scalar s1(0), s2(0);
  for (k = 1; k <= d; ++k) {
    Scalar s = (1 - Scalar(k) / M21);
    s1 += capd::abs(y[k - 1]).rightBound() / power(s, w.exponent());
    s2 += capd::abs(w[k - 1]).rightBound() / power(s, y.exponent());
  }
  Scalar C2 = w.C() * s1 / PolyType::takePower(M21, w.exponent() - t + 1)
    + y.C() * s2 / PolyType::takePower(M21, y.exponent() - t + 1)
    + w.C() * y.C() * PolyType::takePower(2, t) / PolyType::takePower(d, capd::max(y.exponent(), w.exponent()));

  result.C() = capd::max(C1, C2).rightBound();
  result.exponent() = t - 1;
  return result;
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M>
computeQI(const PolynomialBound<Scalar, Exponent, M>& y,
          const PolynomialBound<Scalar, Exponent, M>& w
          ) {
  int d = y.dimension();
  typedef PolynomialBound<Scalar, Exponent, M> PolyType;
  if (d != w.dimension())
    throw std::runtime_error("Incorrect dimensions in funtion computeQI in PolynomialBound.hpp");

  PolyType result(d, true);

  // first we compute some constants, which appear in many places
  Scalar GE = y.C() * w.C();
  Exponent b = 2 * y.exponent() - 1;
  Exponent g = 2 * w.exponent() - 1;
  Exponent bg = b*g;
  Scalar M21 = PolyType::takePower(d, b);
  Scalar M21bg = M21*bg;
  Scalar I(-1, 1);

  // next we compute coefficient of QI for indices [1,...,dimension]
  int i, k;
  for (i = 1; i <= d; ++i) {
    result[i - 1] = Scalar(0);
    for (k = 1; k <= d; ++k)
      result[i - 1] += y[k - 1] * w[i + k - 1];

    Scalar Mig = PolyType::takePower(d + i, g);
    result[i - 1] += I * (GE / sqrt(M21bg * Mig));
  }

  // exponent of result is set as w.exponent()-1
  result.exponent() = w.exponent() - 1;

  // constant is a maximum of C1 and C2 computed below
  Scalar C1(0);
  for (i = y.dimension() + 1; i <= 2 * d; ++i) {
    Scalar Qi(0);
    for (k = 1; k <= d; ++k)
      Qi += y[k - 1] * w[i + k - 1];
    Scalar Mig = PolyType::takePower(d + i, g);
    Qi += I * (GE / sqrt(M21bg * Mig));
    Qi *= PolyType::takePower(i, w.exponent() - 1);
    C1 = capd::max(capd::abs(Qi), C1);
  }

  // now we compute C2
  // first we compute max norm of main part of y
  Scalar yNorm(capd::abs(y[0]));
  for (i = 1; i < d; ++i)
    yNorm = capd::max(yNorm, capd::abs(y[i]));
  yNorm = yNorm.rightBound();
  Scalar C2 = w.exponent() / (2 * d + 1) * yNorm;
  Scalar M3 = PolyType::takePower(3 * d + i, g);
  C2 += GE / sqrt(M21bg * M3);
  result.C() = capd::max(C1, C2).rightBound();
  return result;
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
PolynomialBound<Scalar, Exponent, M>
PolynomialBound<Scalar, Exponent, M>::partialDerivative() const
{
  int d = this->size();
  typedef PolynomialBound<Scalar, Exponent, M> PolyType;

  
  PolyType result(d, m_C,m_exponent-1,true);
  for(int i=0;i<d;++i)
  {
    result[i] = (i+1)*(*this)[i];
  }
  return result;
}

// ----------------------------------------------------------------------------

template<typename Scalar, typename Exponent, int M>
std::ostream& operator << (std::ostream& s, const PolynomialBound<Scalar, Exponent, M>& p)
{
  s <<"{{";
  if(p.size()>0)
    s << p[0];
  for(int i=1;i<p.size();++i)
    s << "," << p[i];
  s << "}," << p.C() << "," << p.exponent() << "}";
  return s;
}

} // end of namespace pdes
} // end of namespace capd

#endif // _CAPD_PDES_POLYNOMIALBOUND_HPP_ 

/// @}


