/// @addtogroup normalForms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file planarMaps.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_NORMALFORMS_PLANARMAPS_HPP_ 
#define _CAPD_NORMALFORMS_PLANARMAPS_HPP_ 

#include <cmath>
#include "capd/interval/Interval.h"

template<class Scalar>
inline Scalar takePhiByTwo()
{
  return Scalar::pi()/2.;
}

template<>
inline double takePhiByTwo<double>()
{
  return M_PI_2;
}

template<>
inline long double takePhiByTwo<long double>()
{
  return M_PI_2l;
}

template <typename ScalarType>
std::complex<ScalarType> Power(std::complex<ScalarType> x, int n)
{
   std::complex<ScalarType> result = x;
   for(int i=2;i<=n;++i)
      result *= x;
   return result;
}

template <typename ScalarType>
std::complex<ScalarType> operator*(int a, const std::complex<ScalarType>& c)
{
   return std::complex<ScalarType>(
      ((double)a) * c.real(),
      ((double)a) * c.imag()
   );
}

template <typename ScalarType>
std::complex<ScalarType> operator/(const std::complex<ScalarType>& c,int a)
{
   return std::complex<ScalarType>(
      c.real()/(double)a,
      c.imag()/(double)a
   );
}

template <typename ScalarType>
std::complex<ScalarType> operator+(int a, const std::complex<ScalarType>& c)
{
   return std::complex<ScalarType>(
      ((double)a) + c.real(),
      c.imag()
   );
}

template <typename ScalarType>
std::complex<ScalarType> operator-(int a, const std::complex<ScalarType>& c)
{
   return std::complex<ScalarType>(
      ((double)a)-c.real(),
      c.imag()
      );
}

namespace capd{
namespace normalForms{

template<typename T>
bool checkLambda(std::complex<T> lambda)
{
   T s = lambda.real()-1;
   return (!isSingular(s) || !isSingular(lambda.imag()));
}

template < typename T_Bound, typename T_Rnd>
std::complex< capd::intervals::Interval<T_Bound,T_Rnd> > operator/ (
         const std::complex< capd::intervals::Interval<T_Bound,T_Rnd> >& x,
         const std::complex< capd::intervals::Interval<T_Bound,T_Rnd> >& y
      )
{
   using namespace capd::intervals;
   typedef Interval<T_Bound,T_Rnd> interval;
   interval temp = capd::intervals::power(y.real(),2) + capd::intervals::power(y.imag(),2);
   interval re = x.real()*y.real()+x.imag()*y.imag();
   interval im = x.imag()*y.real()-x.real()*y.imag();
   return std::complex<interval>(re/temp,im/temp);
}

template < typename T_Bound, typename T_Rnd>
std::complex< capd::intervals::Interval<T_Bound,T_Rnd> > operator/ (
         const std::complex< capd::intervals::Interval<T_Bound,T_Rnd> >& x,
         int y
      )
{
   using namespace capd::intervals;
   typedef Interval<T_Bound,T_Rnd> interval;
   return std::complex<interval>(x.real()/y,x.imag()/y);
}

// -------------------------------------------------------------------------- //

// the following procedure computes eigensystem of a matrix
// important: we assume matrix has complex eigenvalues

template<typename ScalarType>
void computeEigensystem(
      const capd::vectalg::Matrix<ScalarType,2,2>& c, 
      capd::vectalg::Matrix<std::complex<ScalarType>,2,2>& eigenvectors, 
      capd::vectalg::Vector<std::complex<ScalarType>,2>& eigenvalues
   )
{
   ScalarType d2 = c(1,1)*c(1,1) + 4*c(1,2)*c(2,1) - 2*c(1,1)*c(2,2) + c(2,2)*c(2,2);
   if(!(d2<0))
      throw std::runtime_error("computeEigensystem: matrix has not complex eigenvalues!");
   ScalarType d = sqrt(-d2);
   std::complex<ScalarType> v( c(1,1) - c(2,2), -d );
   v /= (std::complex<ScalarType>(ScalarType(2.)*c(2,1),ScalarType(0)));
   eigenvectors(1,1) = v;            
   eigenvectors(2,1) = std::conj(v); 
   eigenvectors(1,2) = eigenvectors(2,2) = std::complex<ScalarType>(ScalarType(1),ScalarType(0));
   eigenvectors = Transpose(eigenvectors);

// eigenvalues
   eigenvalues[0] = std::complex<ScalarType>(c(1,1)+c(2,2),-d);
   eigenvalues[1] = std::conj(eigenvalues[0]);
   eigenvalues /=std::complex<ScalarType>(ScalarType(2),ScalarType(0));
}

// -------------------------------------------------------------------------- //

// the following procedure brings linear part of a planar map to the normal form

template<typename ScalarType>
capd::map::CnCoeff< capd::vectalg::Matrix< std::complex<ScalarType>,2,2> > planarLinearSubstitution(
      const capd::map::CnCoeff< capd::vectalg::Matrix<ScalarType,2,2> >& s)
{   
   capd::vectalg::Matrix< std::complex<ScalarType>,2,2> eigenvectors;
   capd::vectalg::Vector<std::complex<ScalarType>,2> eigenvalues;
   computeEigensystem(capd::vectalg::Matrix<ScalarType,2,2>(s),eigenvectors,eigenvalues);

   capd::vectalg::Matrix< std::complex<ScalarType>,2,2> inverse;
   inverse(1,1) = eigenvectors(2,2);
   inverse(1,2) = -eigenvectors(1,2);
   inverse(2,1) = -eigenvectors(2,1);
   inverse(2,2) = eigenvectors(1,1);
   std::complex<ScalarType> det = eigenvectors(1,1)*eigenvectors(2,2)-eigenvectors(1,2)*eigenvectors(2,1);
   inverse /= det;

   capd::map::CnCoeff< capd::vectalg::Matrix< std::complex<ScalarType>,2,2> > c(s.dimension(),s.rank());
   typename capd::map::CnCoeff<capd::vectalg:: Matrix< std::complex<ScalarType>,2,2> >::iterator b=c.begin(),e=c.end();
   typename capd::map::CnCoeff< capd::vectalg::Matrix<ScalarType,2,2> >::const_iterator i=s.begin();
   while(b!=e)
   {
      *b = std::complex<ScalarType>(*i,ScalarType(0.));
      ++b;
      ++i;
   }

   return linearSubstitution(inverse,c,eigenvectors);
}

// -------------------------------------------------------------------------- //

template<typename ScalarType>
std::complex<ScalarType>& takeCoeff(
      capd::map::CnCoeff< capd::vectalg::Matrix<std::complex<ScalarType>,2,2> >&s,
      int i, int j, int k
   )
{
   capd::vectalg::Multiindex mi(2);
   mi[0]=j;
   mi[1]=k;
   return s(i,mi);   
}

// -------------------------------------------------------------------------- //

// the following procedure computes a Birkhoff normal form of an area-preserving planar map
// p(x,y) = x*cos(w) + y*sin(w) + O(|(x,y)|^6)
// q(x,y) = -x*sin(w) + y*cos(w) + O(|(x,y)|^6)
// where w = a0+a1(x^2+y^2)+a2(x^2+y^2)^2

template<typename ScalarType>
capd::vectalg::Vector<std::complex<ScalarType>,0> computePlanarElipticNormalForm(capd::map::CnCoeff< capd::vectalg::Matrix<ScalarType,2,2> >& c)
{   
   static ScalarType myPhiByTwo = takePhiByTwo<ScalarType>();
   capd::map::CnCoeff< capd::vectalg::Matrix< std::complex<ScalarType>,2,2> > lin = planarLinearSubstitution(c);
   derivativesToSeries(lin);

   int degree = (c.rank()+1)/2;
   capd::vectalg::Vector<std::complex<ScalarType>,0> result(degree), alpha(degree), beta(degree);
   std::complex<ScalarType> lambda,mu;
   
   capd::map::CnCoeff< capd::vectalg::Matrix<std::complex<ScalarType>,2,2> > s(c.dimension(),c.rank()); // coefficients of substitution
   s(0,0) = ScalarType(1);
   s(1,1) = ScalarType(1);
   
   lambda = lin(0,0);
   mu     = lin(1,1);
   alpha[0] = lambda;
   beta[0] = mu;
   std::complex<ScalarType> I(ScalarType(0),ScalarType(1));
   ScalarType coeff = alpha[0].real();

   if(coeff<=1 && coeff >= -1)
    result[0] = acos(coeff);
   else
     result[0] = acos(alpha[0].imag()) - myPhiByTwo;

   if(degree>1)
   {
      std::complex<ScalarType> s1 = lambda;
      std::complex<ScalarType> s2 = lambda*lambda;
      std::complex<ScalarType> s3 = s2*lambda;
      std::complex<ScalarType> s4 = s2*s2;
      
      if( !checkLambda(s1) || !checkLambda(s2) || !checkLambda(s3) || !checkLambda(s4))
      {
         std::ostringstream out;
         out << "computePlanarElipticNormalForm: cannot compute third order normal form\n - a power of lambda=";
         out << lambda << " contains 1";
         
         throw std::runtime_error(out.str());
      }
// C2Coeff
      takeCoeff(s,0,0,2) = -((Power(lambda,2)*takeCoeff(lin,0,0,2))/(-1 + Power(lambda,3)));
      takeCoeff(s,0,1,1) = -(takeCoeff(lin,0,1,1)/(-1 + lambda));
      takeCoeff(s,0,2,0) = takeCoeff(lin,0,2,0)/((-1 + lambda)*lambda);
      takeCoeff(s,1,0,2) = -((Power(lambda,2)*takeCoeff(lin,1,0,2))/(-1 + lambda));
      takeCoeff(s,1,1,1) = (lambda*takeCoeff(lin,1,1,1))/(-1 + lambda);
      takeCoeff(s,1,2,0) = (lambda*takeCoeff(lin,1,2,0))/(-1 + Power(lambda,3));

// C3Coeff

      takeCoeff(s,0,2,1) = -(takeCoeff(s,0,2,0)*takeCoeff(s,1,0,2)) + takeCoeff(s,0,0,2)*takeCoeff(s,1,2,0);
      takeCoeff(s,1,1,2) = -(takeCoeff(s,0,2,0)*takeCoeff(s,1,0,2)) + takeCoeff(s,0,0,2)*takeCoeff(s,1,2,0);

      takeCoeff(s,0,0,3) = -((Power(lambda,3)*takeCoeff(lin,0,0,3) + Power(lambda,3)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2) + 
         2*Power(lambda,3)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,2)));

      takeCoeff(s,0,0,3) = -((Power(lambda,3)*takeCoeff(lin,0,0,3) + Power(lambda,3)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2) + 
         2*Power(lambda,3)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,2))/(-1 + Power(lambda,4)));

      takeCoeff(s,0,1,2) = -((lambda*takeCoeff(lin,0,1,2) + 2*lambda*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,2) + lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,1) + 
         lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,1,0,2) + 2*lambda*takeCoeff(lin,0,0,2)*takeCoeff(s,1,1,1))/(-1 + Power(lambda,2)));

      takeCoeff(s,0,3,0) = -((-takeCoeff(lin,0,3,0) - 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,2,0) - takeCoeff(lin,0,1,1)*takeCoeff(s,1,2,0))/
         (lambda*(-1 + Power(lambda,2))));

      takeCoeff(s,1,0,3) = -((Power(lambda,3)*takeCoeff(lin,1,0,3) + 
         Power(lambda,3)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,2) + 2*Power(lambda,3)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,2))/(-1 + Power(lambda,2)));

      takeCoeff(s,1,2,1) = -((-(lambda*takeCoeff(lin,1,2,1)) - 2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,1,1) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,0) - 
         lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,1,1,1) - 2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,2,0))/(-1 + Power(lambda,2)));

      takeCoeff(s,1,3,0) = -((-(lambda*takeCoeff(lin,1,3,0)) - 2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,2,0) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,1,2,0))/
         (-1 + Power(lambda,4)));

      beta[1] = takeCoeff(lin,1,1,2) + 2*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,2) + takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,1) + 
         takeCoeff(lin,1,1,1)*takeCoeff(s,1,0,2) + 2*takeCoeff(lin,1,0,2)*takeCoeff(s,1,1,1);
      alpha[1] = takeCoeff(lin,0,2,1) + 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,1,1) + takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,0) + 
         takeCoeff(lin,0,1,1)*takeCoeff(s,1,1,1) + 2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,2,0);

      result[1] = (-I*alpha[1]/alpha[0]);

      if(degree>2)
      {
         std::complex<ScalarType> s5 = s2*s3;
         std::complex<ScalarType> s6 = s3*s3;
         if( !checkLambda(s5) || !checkLambda(s6) )
            throw std::runtime_error("computePlanarElipticNormalForm: cannot compute fifth order normal form - a power of lambda contains 1");
         
// Coeff4
         takeCoeff(s,0,0,4) = 
            -((Power(lambda,4)*(takeCoeff(lin,0,0,4) + takeCoeff(lin,0,1,2)*takeCoeff(s,0,0,2) + 
            takeCoeff(lin,0,2,0)*Power(takeCoeff(s,0,0,2),2) + takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,3) + 3*takeCoeff(lin,0,0,3)*takeCoeff(s,1,0,2) + 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,0,2) + takeCoeff(lin,0,0,2)*Power(takeCoeff(s,1,0,2),2) + 
            2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,3)))/(-1 + Power(lambda,5)));

         takeCoeff(s,0,1,3) = 
            -((lambda*(lambda*takeCoeff(lin,0,1,3) - 2*beta[1]*takeCoeff(s,0,0,2) + 2*lambda*takeCoeff(lin,0,2,1)*takeCoeff(s,0,0,2) + 
            2*lambda*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,3) + lambda*takeCoeff(lin,0,1,2)*takeCoeff(s,0,1,1) + 
            2*lambda*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,1,1) + lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,2) + 
            2*lambda*takeCoeff(lin,0,1,2)*takeCoeff(s,1,0,2) + lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,0,2) + 
            lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,1,0,3) + 3*lambda*takeCoeff(lin,0,0,3)*takeCoeff(s,1,1,1) + 
            lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,1,1) + 2*lambda*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,1,1) + 
            2*lambda*takeCoeff(lin,0,0,2)*takeCoeff(s,1,1,2)))/(-1 + Power(lambda,3)));

         takeCoeff(s,0,2,2) = 
            (-(lambda*takeCoeff(lin,0,2,2)) - 3*lambda*takeCoeff(lin,0,3,0)*takeCoeff(s,0,0,2) + alpha[1]*takeCoeff(s,0,1,1) + 
            Power(lambda,2)*beta[1]*takeCoeff(s,0,1,1) - 2*lambda*takeCoeff(lin,0,2,1)*takeCoeff(s,0,1,1) - lambda*takeCoeff(lin,0,2,0)*Power(takeCoeff(s,0,1,1),2) - 
            2*lambda*takeCoeff(lin,0,2,0)*takeCoeff(s,0,1,2) - lambda*takeCoeff(lin,0,1,2)*takeCoeff(s,0,2,0) - 
            2*lambda*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,2,0) - lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,1) - 
            lambda*takeCoeff(lin,0,2,1)*takeCoeff(s,1,0,2) - lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,0,2) - 
            2*lambda*takeCoeff(lin,0,1,2)*takeCoeff(s,1,1,1) - lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,1,1) - 
            lambda*takeCoeff(lin,0,0,2)*Power(takeCoeff(s,1,1,1),2) - lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,1,1,2) - 
            3*lambda*takeCoeff(lin,0,0,3)*takeCoeff(s,1,2,0) - lambda*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,2,0) - 
            2*lambda*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,2,0) - 2*lambda*takeCoeff(lin,0,0,2)*takeCoeff(s,1,2,1))/((-1 + lambda)*lambda);

         takeCoeff(s,0,3,1) = 
            (takeCoeff(lin,0,3,1) + 3*takeCoeff(lin,0,3,0)*takeCoeff(s,0,1,1) - 2*lambda*alpha[1]*takeCoeff(s,0,2,0) + 
            2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,2,0) + 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,2,0) + 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,2,1) + 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,3,0) + takeCoeff(lin,0,2,1)*takeCoeff(s,1,1,1) + takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,1) + 
            2*takeCoeff(lin,0,1,2)*takeCoeff(s,1,2,0) + takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,2,0) + 
            2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,2,0) + takeCoeff(lin,0,1,1)*takeCoeff(s,1,2,1) + 2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,3,0))/
            ((-1 + lambda)*lambda);

         takeCoeff(s,0,4,0) = 
            (takeCoeff(lin,0,4,0) + 3*takeCoeff(lin,0,3,0)*takeCoeff(s,0,2,0) + 
            takeCoeff(lin,0,2,0)*Power(takeCoeff(s,0,2,0),2) + 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,3,0) + takeCoeff(lin,0,2,1)*takeCoeff(s,1,2,0) + 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,2,0) + takeCoeff(lin,0,0,2)*Power(takeCoeff(s,1,2,0),2) + takeCoeff(lin,0,1,1)*takeCoeff(s,1,3,0))/
            (lambda*(-1 + Power(lambda,3)));

         takeCoeff(s,1,0,4) = 
            -((Power(lambda,4)*(takeCoeff(lin,1,0,4) + takeCoeff(lin,1,1,2)*takeCoeff(s,0,0,2) + takeCoeff(lin,1,2,0)*Power(takeCoeff(s,0,0,2),2) + 
            takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,3) + 3*takeCoeff(lin,1,0,3)*takeCoeff(s,1,0,2) + takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,0,2) + 
            takeCoeff(lin,1,0,2)*Power(takeCoeff(s,1,0,2),2) + 2*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,3)))/(-1 + Power(lambda,3)));

         takeCoeff(s,1,1,3) = 
            -((lambda*(lambda*takeCoeff(lin,1,1,3) + 2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,0,2) + 
            2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,3) + lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,0,1,1) + 
            2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,1,1) + lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,2) - 2*beta[1]*takeCoeff(s,1,0,2) + 
            2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,1,0,2) + lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,0,2) + 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,1,0,3) + 3*lambda*takeCoeff(lin,1,0,3)*takeCoeff(s,1,1,1) + 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,1,1) + 2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,1,1) + 
            2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,1,2)))/(-1 + lambda));

         takeCoeff(s,1,2,2) = 
            (lambda*takeCoeff(lin,1,2,2) + 3*lambda*takeCoeff(lin,1,3,0)*takeCoeff(s,0,0,2) + 2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,1,1) + 
            lambda*takeCoeff(lin,1,2,0)*Power(takeCoeff(s,0,1,1),2) + 2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,1,2) + 
            lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,0,2,0) + 2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,2,0) + 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,1) + lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,1,0,2) + 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,0,2) - alpha[1]*takeCoeff(s,1,1,1) - Power(lambda,2)*beta[1]*takeCoeff(s,1,1,1) + 
            2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,1,1,1) + lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,1,1) + 
            lambda*takeCoeff(lin,1,0,2)*Power(takeCoeff(s,1,1,1),2) + lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,1,1,2) + 
            3*lambda*takeCoeff(lin,1,0,3)*takeCoeff(s,1,2,0) + lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,2,0) + 
            2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,2,0) + 2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,2,1))/(-1 + lambda);

         takeCoeff(s,1,3,1) = 
            -((lambda*(-takeCoeff(lin,1,3,1) - 3*takeCoeff(lin,1,3,0)*takeCoeff(s,0,1,1) - 2*takeCoeff(lin,1,2,1)*takeCoeff(s,0,2,0) - 
            2*takeCoeff(lin,1,2,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,2,0) - 2*takeCoeff(lin,1,2,0)*takeCoeff(s,0,2,1) - takeCoeff(lin,1,1,1)*takeCoeff(s,0,3,0) - 
            takeCoeff(lin,1,2,1)*takeCoeff(s,1,1,1) - takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,1) + 2*lambda*alpha[1]*takeCoeff(s,1,2,0) - 
            2*takeCoeff(lin,1,1,2)*takeCoeff(s,1,2,0) - takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,2,0) - 
            2*takeCoeff(lin,1,0,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,2,0) - takeCoeff(lin,1,1,1)*takeCoeff(s,1,2,1) - 2*takeCoeff(lin,1,0,2)*takeCoeff(s,1,3,0)))/
            (-1 + Power(lambda,3)));

         takeCoeff(s,1,4,0) = 
            (lambda*(takeCoeff(lin,1,4,0) + 3*takeCoeff(lin,1,3,0)*takeCoeff(s,0,2,0) + 
            takeCoeff(lin,1,2,0)*Power(takeCoeff(s,0,2,0),2) + 2*takeCoeff(lin,1,2,0)*takeCoeff(s,0,3,0) + takeCoeff(lin,1,2,1)*takeCoeff(s,1,2,0) + 
            takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,2,0) + takeCoeff(lin,1,0,2)*Power(takeCoeff(s,1,2,0),2) + takeCoeff(lin,1,1,1)*takeCoeff(s,1,3,0)))/
            (-1 + Power(lambda,5));

// Coeff5

         takeCoeff(s,0,3,2) = 
            (-ScalarType(2.)*takeCoeff(s,0,3,1)*takeCoeff(s,1,0,2) - ScalarType(3.)*takeCoeff(s,0,3,0)*takeCoeff(s,1,0,3) - takeCoeff(s,0,2,1)*takeCoeff(s,1,1,2) - 
            ScalarType(2.)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,3) + ScalarType(2.)*takeCoeff(s,0,1,3)*takeCoeff(s,1,2,0) + takeCoeff(s,0,1,2)*takeCoeff(s,1,2,1) + 
            ScalarType(3.)*takeCoeff(s,0,0,3)*takeCoeff(s,1,3,0) + ScalarType(2.)*takeCoeff(s,0,0,2)*takeCoeff(s,1,3,1))*ScalarType(0.5);
       
         takeCoeff(s,0,0,5) = 
            -((Power(lambda,5)*takeCoeff(lin,0,0,5) + Power(lambda,5)*takeCoeff(lin,0,1,3)*takeCoeff(s,0,0,2) + 
            Power(lambda,5)*takeCoeff(lin,0,2,1)*Power(takeCoeff(s,0,0,2),2) + Power(lambda,5)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,0,3) + 
            2*Power(lambda,5)*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,0,3) + Power(lambda,5)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,4) + 
            4*Power(lambda,5)*takeCoeff(lin,0,0,4)*takeCoeff(s,1,0,2) + 2*Power(lambda,5)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,0,2)*takeCoeff(s,1,0,2) + 
            Power(lambda,5)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,3)*takeCoeff(s,1,0,2) + 3*Power(lambda,5)*takeCoeff(lin,0,0,3)*Power(takeCoeff(s,1,0,2),2) + 
            3*Power(lambda,5)*takeCoeff(lin,0,0,3)*takeCoeff(s,1,0,3) + Power(lambda,5)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,0,3) + 
            2*Power(lambda,5)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,0,3) + 2*Power(lambda,5)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,4))/
            (-1 + Power(lambda,6)));
       
         takeCoeff(s,0,1,4) =
            -((-(Power(lambda,3)*takeCoeff(lin,0,1,4)) - 2*Power(lambda,3)*takeCoeff(lin,0,2,2)*takeCoeff(s,0,0,2) - 
            3*Power(lambda,3)*takeCoeff(lin,0,3,0)*Power(takeCoeff(s,0,0,2),2) + 3*lambda*beta[1]*takeCoeff(s,0,0,3) - 
            2*Power(lambda,3)*takeCoeff(lin,0,2,1)*takeCoeff(s,0,0,3) - 2*Power(lambda,3)*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,4) - 
            Power(lambda,3)*takeCoeff(lin,0,1,3)*takeCoeff(s,0,1,1) - 2*Power(lambda,3)*takeCoeff(lin,0,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,0,1,1) - 
            2*Power(lambda,3)*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,3)*takeCoeff(s,0,1,1) - Power(lambda,3)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,1,2) - 
            2*Power(lambda,3)*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,1,2) - Power(lambda,3)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,3) - 
            3*Power(lambda,3)*takeCoeff(lin,0,1,3)*takeCoeff(s,1,0,2) - 2*Power(lambda,3)*takeCoeff(lin,0,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,0,2) - 
            2*Power(lambda,3)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,1,1)*takeCoeff(s,1,0,2) - 
            Power(lambda,3)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,2)*takeCoeff(s,1,0,2) - Power(lambda,3)*takeCoeff(lin,0,1,2)*Power(takeCoeff(s,1,0,2),2) - 
            2*Power(lambda,3)*takeCoeff(lin,0,1,2)*takeCoeff(s,1,0,3) - Power(lambda,3)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,0,3) - 
            Power(lambda,3)*takeCoeff(lin,0,1,1)*takeCoeff(s,1,0,4) - 4*Power(lambda,3)*takeCoeff(lin,0,0,4)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,3)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,0,2)*takeCoeff(s,1,1,1) - 
            Power(lambda,3)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,3)*takeCoeff(s,1,1,1) - 
            6*Power(lambda,3)*takeCoeff(lin,0,0,3)*takeCoeff(s,1,0,2)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,3)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,3)*takeCoeff(s,1,1,1) - 3*Power(lambda,3)*takeCoeff(lin,0,0,3)*takeCoeff(s,1,1,2) - 
            Power(lambda,3)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,1,2) - 
            2*Power(lambda,3)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,1,2) - 2*Power(lambda,3)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,1,3))/
            (1 - Power(lambda,4)));
            
         takeCoeff(s,0,2,3) = 
            -((-(Power(lambda,2)*takeCoeff(lin,0,2,3)) - 3*Power(lambda,2)*takeCoeff(lin,0,3,1)*takeCoeff(s,0,0,2) - 
            3*Power(lambda,2)*takeCoeff(lin,0,3,0)*takeCoeff(s,0,0,3) - 2*Power(lambda,2)*takeCoeff(lin,0,2,2)*takeCoeff(s,0,1,1) - 
            6*Power(lambda,2)*takeCoeff(lin,0,3,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,1,1) - Power(lambda,2)*takeCoeff(lin,0,2,1)*Power(takeCoeff(s,0,1,1),2) + 
            alpha[1]*takeCoeff(s,0,1,2) + 2*Power(lambda,2)*beta[1]*takeCoeff(s,0,1,2) - 2*Power(lambda,2)*takeCoeff(lin,0,2,1)*takeCoeff(s,0,1,2) - 
            2*Power(lambda,2)*takeCoeff(lin,0,2,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,1,2) - 2*Power(lambda,2)*takeCoeff(lin,0,2,0)*takeCoeff(s,0,1,3) - 
            Power(lambda,2)*takeCoeff(lin,0,1,3)*takeCoeff(s,0,2,0) - 2*Power(lambda,2)*takeCoeff(lin,0,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,0,2,0) - 
            2*Power(lambda,2)*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,3)*takeCoeff(s,0,2,0) - Power(lambda,2)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,2,1) - 
            2*Power(lambda,2)*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,2,1) - Power(lambda,2)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,2) - 
            2*Power(lambda,2)*takeCoeff(lin,0,2,2)*takeCoeff(s,1,0,2) - 2*Power(lambda,2)*takeCoeff(lin,0,2,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,0,2) - 
            2*Power(lambda,2)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,2,0)*takeCoeff(s,1,0,2) - 
            Power(lambda,2)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,1)*takeCoeff(s,1,0,2) - Power(lambda,2)*takeCoeff(lin,0,2,1)*takeCoeff(s,1,0,3) - 
            Power(lambda,2)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,0,3) - 3*Power(lambda,2)*takeCoeff(lin,0,1,3)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,2)*takeCoeff(lin,0,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,2)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,1,1)*takeCoeff(s,1,1,1) - 
            Power(lambda,2)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,2)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,2)*takeCoeff(lin,0,1,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,1,1) - 3*Power(lambda,2)*takeCoeff(lin,0,0,3)*Power(takeCoeff(s,1,1,1),2) - 
            2*Power(lambda,2)*takeCoeff(lin,0,1,2)*takeCoeff(s,1,1,2) - Power(lambda,2)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,1,2) - 
            2*Power(lambda,2)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,1,2) - Power(lambda,2)*takeCoeff(lin,0,1,1)*takeCoeff(s,1,1,3) - 
            4*Power(lambda,2)*takeCoeff(lin,0,0,4)*takeCoeff(s,1,2,0) - 2*Power(lambda,2)*takeCoeff(lin,0,1,2)*takeCoeff(s,0,0,2)*takeCoeff(s,1,2,0) - 
            Power(lambda,2)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,3)*takeCoeff(s,1,2,0) - 
            6*Power(lambda,2)*takeCoeff(lin,0,0,3)*takeCoeff(s,1,0,2)*takeCoeff(s,1,2,0) - 
            2*Power(lambda,2)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,3)*takeCoeff(s,1,2,0) - 3*Power(lambda,2)*takeCoeff(lin,0,0,3)*takeCoeff(s,1,2,1) - 
            Power(lambda,2)*takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,2,1) - 
            2*Power(lambda,2)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,2,1) - 2*Power(lambda,2)*takeCoeff(lin,0,0,2)*takeCoeff(s,1,2,2))/
            (lambda - Power(lambda,3)));
            
         takeCoeff(s,1,2,3) = 
            (-ScalarType(2.)*takeCoeff(s,0,3,1)*takeCoeff(s,1,0,2) - ScalarType(3.)*takeCoeff(s,0,3,0)*takeCoeff(s,1,0,3) - 
            takeCoeff(s,0,2,1)*takeCoeff(s,1,1,2) - ScalarType(2.)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,3) + ScalarType(2.)*takeCoeff(s,0,1,3)*takeCoeff(s,1,2,0) + 
            takeCoeff(s,0,1,2)*takeCoeff(s,1,2,1) + ScalarType(3.)*takeCoeff(s,0,0,3)*takeCoeff(s,1,3,0) + ScalarType(2.)*takeCoeff(s,0,0,2)*takeCoeff(s,1,3,1))*ScalarType(0.5);

         takeCoeff(s,0,4,1) = 
            -((-takeCoeff(lin,0,4,1) - 4*takeCoeff(lin,0,4,0)*takeCoeff(s,0,1,1) - 3*takeCoeff(lin,0,3,1)*takeCoeff(s,0,2,0) - 
            6*takeCoeff(lin,0,3,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,2,0) - takeCoeff(lin,0,2,1)*Power(takeCoeff(s,0,2,0),2) - 
            3*takeCoeff(lin,0,3,0)*takeCoeff(s,0,2,1) - 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,2,0)*takeCoeff(s,0,2,1) + 
            3*Power(lambda,2)*alpha[1]*takeCoeff(s,0,3,0) - 2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,3,0) - 
            2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,3,0) - 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,3,1) - takeCoeff(lin,0,1,1)*takeCoeff(s,0,4,0) - 
            takeCoeff(lin,0,3,1)*takeCoeff(s,1,1,1) - 2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,1) - 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,3,0)*takeCoeff(s,1,1,1) - 2*takeCoeff(lin,0,2,2)*takeCoeff(s,1,2,0) - 
            2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,2,0) - 2*takeCoeff(lin,0,1,2)*takeCoeff(s,0,2,0)*takeCoeff(s,1,2,0) - 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,1)*takeCoeff(s,1,2,0) - 2*takeCoeff(lin,0,1,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,2,0) - 
            3*takeCoeff(lin,0,0,3)*Power(takeCoeff(s,1,2,0),2) - takeCoeff(lin,0,2,1)*takeCoeff(s,1,2,1) - 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,2,1) - 2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,2,0)*takeCoeff(s,1,2,1) - 
            2*takeCoeff(lin,0,1,2)*takeCoeff(s,1,3,0) - takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,3,0) - 
            2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,3,0) - takeCoeff(lin,0,1,1)*takeCoeff(s,1,3,1) - 2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,4,0))/
            (-lambda + Power(lambda,3)));

         takeCoeff(s,0,5,0) =
            -((-takeCoeff(lin,0,5,0) - 4*takeCoeff(lin,0,4,0)*takeCoeff(s,0,2,0) - 
            3*takeCoeff(lin,0,3,0)*Power(takeCoeff(s,0,2,0),2) - 3*takeCoeff(lin,0,3,0)*takeCoeff(s,0,3,0) - 
            2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,2,0)*takeCoeff(s,0,3,0) - 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,4,0) - takeCoeff(lin,0,3,1)*takeCoeff(s,1,2,0) - 
            2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,2,0) - takeCoeff(lin,0,1,1)*takeCoeff(s,0,3,0)*takeCoeff(s,1,2,0) - 
            takeCoeff(lin,0,1,2)*Power(takeCoeff(s,1,2,0),2) - takeCoeff(lin,0,2,1)*takeCoeff(s,1,3,0) - takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,3,0) - 
            2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,2,0)*takeCoeff(s,1,3,0) - takeCoeff(lin,0,1,1)*takeCoeff(s,1,4,0))/(lambda*(-1 + Power(lambda,4))));

         takeCoeff(s,1,0,5) =
            -((Power(lambda,5)*takeCoeff(lin,1,0,5) + Power(lambda,5)*takeCoeff(lin,1,1,3)*takeCoeff(s,0,0,2) + 
            Power(lambda,5)*takeCoeff(lin,1,2,1)*Power(takeCoeff(s,0,0,2),2) + Power(lambda,5)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,0,3) + 
            2*Power(lambda,5)*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,0,3) + Power(lambda,5)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,4) + 
            4*Power(lambda,5)*takeCoeff(lin,1,0,4)*takeCoeff(s,1,0,2) + 2*Power(lambda,5)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,0,2)*takeCoeff(s,1,0,2) + 
            Power(lambda,5)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,3)*takeCoeff(s,1,0,2) + 3*Power(lambda,5)*takeCoeff(lin,1,0,3)*Power(takeCoeff(s,1,0,2),2) + 
            3*Power(lambda,5)*takeCoeff(lin,1,0,3)*takeCoeff(s,1,0,3) + Power(lambda,5)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,0,3) + 
            2*Power(lambda,5)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,0,3) + 2*Power(lambda,5)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,4))/
            (-1 + Power(lambda,4)));

         takeCoeff(s,1,1,4) = 
            -((-(Power(lambda,3)*takeCoeff(lin,1,1,4)) - 2*Power(lambda,3)*takeCoeff(lin,1,2,2)*takeCoeff(s,0,0,2) - 
            3*Power(lambda,3)*takeCoeff(lin,1,3,0)*Power(takeCoeff(s,0,0,2),2) - 2*Power(lambda,3)*takeCoeff(lin,1,2,1)*takeCoeff(s,0,0,3) - 
            2*Power(lambda,3)*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,4) - Power(lambda,3)*takeCoeff(lin,1,1,3)*takeCoeff(s,0,1,1) - 
            2*Power(lambda,3)*takeCoeff(lin,1,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,0,1,1) - 
            2*Power(lambda,3)*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,3)*takeCoeff(s,0,1,1) - Power(lambda,3)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,1,2) - 
            2*Power(lambda,3)*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,1,2) - Power(lambda,3)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,3) - 
            3*Power(lambda,3)*takeCoeff(lin,1,1,3)*takeCoeff(s,1,0,2) - 2*Power(lambda,3)*takeCoeff(lin,1,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,0,2) - 
            2*Power(lambda,3)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,1,1)*takeCoeff(s,1,0,2) - 
            Power(lambda,3)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,2)*takeCoeff(s,1,0,2) - Power(lambda,3)*takeCoeff(lin,1,1,2)*Power(takeCoeff(s,1,0,2),2) + 
            3*lambda*beta[1]*takeCoeff(s,1,0,3) - 2*Power(lambda,3)*takeCoeff(lin,1,1,2)*takeCoeff(s,1,0,3) - 
            Power(lambda,3)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,0,3) - Power(lambda,3)*takeCoeff(lin,1,1,1)*takeCoeff(s,1,0,4) - 
            4*Power(lambda,3)*takeCoeff(lin,1,0,4)*takeCoeff(s,1,1,1) - 2*Power(lambda,3)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,0,2)*takeCoeff(s,1,1,1) - 
            Power(lambda,3)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,3)*takeCoeff(s,1,1,1) - 
            6*Power(lambda,3)*takeCoeff(lin,1,0,3)*takeCoeff(s,1,0,2)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,3)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,3)*takeCoeff(s,1,1,1) - 3*Power(lambda,3)*takeCoeff(lin,1,0,3)*takeCoeff(s,1,1,2) - 
            Power(lambda,3)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,1,2) - 
            2*Power(lambda,3)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,1,2) - 2*Power(lambda,3)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,1,3))/
            (1 - Power(lambda,2)));

         takeCoeff(s,1,3,2) = 
            -((-(lambda*takeCoeff(lin,1,3,2)) - 4*lambda*takeCoeff(lin,1,4,0)*takeCoeff(s,0,0,2) - 
            3*lambda*takeCoeff(lin,1,3,1)*takeCoeff(s,0,1,1) - 3*lambda*takeCoeff(lin,1,3,0)*Power(takeCoeff(s,0,1,1),2) - 
            3*lambda*takeCoeff(lin,1,3,0)*takeCoeff(s,0,1,2) - 2*lambda*takeCoeff(lin,1,2,2)*takeCoeff(s,0,2,0) - 
            6*lambda*takeCoeff(lin,1,3,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,2,0) - 2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,1,1)*takeCoeff(s,0,2,0) - 
            2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,1,2)*takeCoeff(s,0,2,0) - 2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,2,1) - 
            2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,2,1) - 2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,2,2) - 
            lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,0,3,0) - 2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,3,0) - 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,3,1) - lambda*takeCoeff(lin,1,3,1)*takeCoeff(s,1,0,2) - 
            2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,0,2) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,3,0)*takeCoeff(s,1,0,2) - 
            2*lambda*takeCoeff(lin,1,2,2)*takeCoeff(s,1,1,1) - 2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,1,1) - 
            2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,1) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,1)*takeCoeff(s,1,1,1) - 
            lambda*takeCoeff(lin,1,1,2)*Power(takeCoeff(s,1,1,1),2) - lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,1,1,2) - 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,2) - 3*lambda*takeCoeff(lin,1,1,3)*takeCoeff(s,1,2,0) - 
            2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,2,0) - 2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,0,1,1)*takeCoeff(s,1,2,0) - 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,2)*takeCoeff(s,1,2,0) - 2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,2,0) - 
            6*lambda*takeCoeff(lin,1,0,3)*takeCoeff(s,1,1,1)*takeCoeff(s,1,2,0) - 2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,1,2)*takeCoeff(s,1,2,0) + 
            2*lambda*alpha[1]*takeCoeff(s,1,2,1) + Power(lambda,3)*beta[1]*takeCoeff(s,1,2,1) - 2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,1,2,1) - 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,2,1) - 2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,2,1) - 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,1,2,2) - 3*lambda*takeCoeff(lin,1,0,3)*takeCoeff(s,1,3,0) - 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,3,0) - 2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,3,0) - 
            2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,3,1))/(-1 + Power(lambda,2)));

         takeCoeff(s,1,4,1) = 
            -((-(lambda*takeCoeff(lin,1,4,1)) - 4*lambda*takeCoeff(lin,1,4,0)*takeCoeff(s,0,1,1) - 
            3*lambda*takeCoeff(lin,1,3,1)*takeCoeff(s,0,2,0) - 6*lambda*takeCoeff(lin,1,3,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,2,0) - 
            lambda*takeCoeff(lin,1,2,1)*Power(takeCoeff(s,0,2,0),2) - 3*lambda*takeCoeff(lin,1,3,0)*takeCoeff(s,0,2,1) - 
            2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,2,0)*takeCoeff(s,0,2,1) - 2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,3,0) - 
            2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,3,0) - 2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,3,1) - 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,4,0) - lambda*takeCoeff(lin,1,3,1)*takeCoeff(s,1,1,1) - 
            2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,1) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,3,0)*takeCoeff(s,1,1,1) - 
            2*lambda*takeCoeff(lin,1,2,2)*takeCoeff(s,1,2,0) - 2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,2,0) - 
            2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,0,2,0)*takeCoeff(s,1,2,0) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,1)*takeCoeff(s,1,2,0) - 
            2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,2,0) - 3*lambda*takeCoeff(lin,1,0,3)*Power(takeCoeff(s,1,2,0),2) - 
            lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,1,2,1) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,2,1) - 
            2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,2,0)*takeCoeff(s,1,2,1) + 3*Power(lambda,3)*alpha[1]*takeCoeff(s,1,3,0) - 
            2*lambda*takeCoeff(lin,1,1,2)*takeCoeff(s,1,3,0) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,3,0) - 
            2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,3,0) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,1,3,1) - 
            2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,4,0))/(-1 + Power(lambda,4)));

         takeCoeff(s,1,5,0) = 
            -((-(lambda*takeCoeff(lin,1,5,0)) - 4*lambda*takeCoeff(lin,1,4,0)*takeCoeff(s,0,2,0) - 
            3*lambda*takeCoeff(lin,1,3,0)*Power(takeCoeff(s,0,2,0),2) - 3*lambda*takeCoeff(lin,1,3,0)*takeCoeff(s,0,3,0) - 
            2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,2,0)*takeCoeff(s,0,3,0) - 2*lambda*takeCoeff(lin,1,2,0)*takeCoeff(s,0,4,0) - 
            lambda*takeCoeff(lin,1,3,1)*takeCoeff(s,1,2,0) - 2*lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,2,0) - 
            lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,3,0)*takeCoeff(s,1,2,0) - lambda*takeCoeff(lin,1,1,2)*Power(takeCoeff(s,1,2,0),2) - 
            lambda*takeCoeff(lin,1,2,1)*takeCoeff(s,1,3,0) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,3,0) - 
            2*lambda*takeCoeff(lin,1,0,2)*takeCoeff(s,1,2,0)*takeCoeff(s,1,3,0) - lambda*takeCoeff(lin,1,1,1)*takeCoeff(s,1,4,0))/(-1 + Power(lambda,6)));
         
         beta[2] = 
            -((-(Power(lambda,2)*takeCoeff(lin,1,2,3)) - 3*Power(lambda,2)*takeCoeff(lin,1,3,1)*takeCoeff(s,0,0,2) - 
            3*Power(lambda,2)*takeCoeff(lin,1,3,0)*takeCoeff(s,0,0,3) - 2*Power(lambda,2)*takeCoeff(lin,1,2,2)*takeCoeff(s,0,1,1) - 
            6*Power(lambda,2)*takeCoeff(lin,1,3,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,1,1) - Power(lambda,2)*takeCoeff(lin,1,2,1)*Power(takeCoeff(s,0,1,1),2) - 
            2*Power(lambda,2)*takeCoeff(lin,1,2,1)*takeCoeff(s,0,1,2) - 2*Power(lambda,2)*takeCoeff(lin,1,2,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,1,2) - 
            2*Power(lambda,2)*takeCoeff(lin,1,2,0)*takeCoeff(s,0,1,3) - Power(lambda,2)*takeCoeff(lin,1,1,3)*takeCoeff(s,0,2,0) - 
            2*Power(lambda,2)*takeCoeff(lin,1,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,0,2,0) - 
            2*Power(lambda,2)*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,3)*takeCoeff(s,0,2,0) - Power(lambda,2)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,2,1) - 
            2*Power(lambda,2)*takeCoeff(lin,1,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,2,1) - Power(lambda,2)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,2) - 
            2*Power(lambda,2)*takeCoeff(lin,1,2,2)*takeCoeff(s,1,0,2) - 2*Power(lambda,2)*takeCoeff(lin,1,2,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,0,2) - 
            2*Power(lambda,2)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,2,0)*takeCoeff(s,1,0,2) - 
            Power(lambda,2)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,1)*takeCoeff(s,1,0,2) - Power(lambda,2)*takeCoeff(lin,1,2,1)*takeCoeff(s,1,0,3) - 
            Power(lambda,2)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,0,3) - 3*Power(lambda,2)*takeCoeff(lin,1,1,3)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,2)*takeCoeff(lin,1,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,2)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,1,1)*takeCoeff(s,1,1,1) - 
            Power(lambda,2)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,2)*takeCoeff(s,1,1,1) - 
            2*Power(lambda,2)*takeCoeff(lin,1,1,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,1,1) - 3*Power(lambda,2)*takeCoeff(lin,1,0,3)*Power(takeCoeff(s,1,1,1),2) + 
            alpha[1]*takeCoeff(s,1,1,2) + 2*Power(lambda,2)*beta[1]*takeCoeff(s,1,1,2) - 2*Power(lambda,2)*takeCoeff(lin,1,1,2)*takeCoeff(s,1,1,2) - 
            Power(lambda,2)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,1,2) - 
            2*Power(lambda,2)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,1,2) - Power(lambda,2)*takeCoeff(lin,1,1,1)*takeCoeff(s,1,1,3) - 
            4*Power(lambda,2)*takeCoeff(lin,1,0,4)*takeCoeff(s,1,2,0) - 2*Power(lambda,2)*takeCoeff(lin,1,1,2)*takeCoeff(s,0,0,2)*takeCoeff(s,1,2,0) - 
            Power(lambda,2)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,3)*takeCoeff(s,1,2,0) - 
            6*Power(lambda,2)*takeCoeff(lin,1,0,3)*takeCoeff(s,1,0,2)*takeCoeff(s,1,2,0) - 
            2*Power(lambda,2)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,3)*takeCoeff(s,1,2,0) - 3*Power(lambda,2)*takeCoeff(lin,1,0,3)*takeCoeff(s,1,2,1) - 
            Power(lambda,2)*takeCoeff(lin,1,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,2,1) - 
            2*Power(lambda,2)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,2,1) - 2*Power(lambda,2)*takeCoeff(lin,1,0,2)*takeCoeff(s,1,2,2))/Power(lambda,2));
     
         alpha[2] = 
            takeCoeff(lin,0,3,2) + 4*takeCoeff(lin,0,4,0)*takeCoeff(s,0,0,2) + 3*takeCoeff(lin,0,3,1)*takeCoeff(s,0,1,1) + 
            3*takeCoeff(lin,0,3,0)*Power(takeCoeff(s,0,1,1),2) + 3*takeCoeff(lin,0,3,0)*takeCoeff(s,0,1,2) + 2*takeCoeff(lin,0,2,2)*takeCoeff(s,0,2,0) + 
            6*takeCoeff(lin,0,3,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,2,0) + 2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,1,1)*takeCoeff(s,0,2,0) + 
            2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,1,2)*takeCoeff(s,0,2,0) - 2*alpha[1]*takeCoeff(s,0,2,1) - Power(lambda,2)*beta[1]*takeCoeff(s,0,2,1) + 
            2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,2,1) + 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,1,1)*takeCoeff(s,0,2,1) + 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,2,2) + 
            takeCoeff(lin,0,1,2)*takeCoeff(s,0,3,0) + 2*takeCoeff(lin,0,2,0)*takeCoeff(s,0,0,2)*takeCoeff(s,0,3,0) + takeCoeff(lin,0,1,1)*takeCoeff(s,0,3,1) + 
            takeCoeff(lin,0,3,1)*takeCoeff(s,1,0,2) + 2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,0,2) + 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,3,0)*takeCoeff(s,1,0,2) + 2*takeCoeff(lin,0,2,2)*takeCoeff(s,1,1,1) + 
            2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,1,1) + 2*takeCoeff(lin,0,1,2)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,1) + 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,1)*takeCoeff(s,1,1,1) + takeCoeff(lin,0,1,2)*Power(takeCoeff(s,1,1,1),2) + takeCoeff(lin,0,2,1)*takeCoeff(s,1,1,2) + 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,2,0)*takeCoeff(s,1,1,2) + 3*takeCoeff(lin,0,1,3)*takeCoeff(s,1,2,0) + 
            2*takeCoeff(lin,0,2,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,2,0) + 2*takeCoeff(lin,0,1,2)*takeCoeff(s,0,1,1)*takeCoeff(s,1,2,0) + 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,2)*takeCoeff(s,1,2,0) + 2*takeCoeff(lin,0,1,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,2,0) + 
            6*takeCoeff(lin,0,0,3)*takeCoeff(s,1,1,1)*takeCoeff(s,1,2,0) + 2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,1,2)*takeCoeff(s,1,2,0) + 
            2*takeCoeff(lin,0,1,2)*takeCoeff(s,1,2,1) + takeCoeff(lin,0,1,1)*takeCoeff(s,0,1,1)*takeCoeff(s,1,2,1) + 
            2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,1,1)*takeCoeff(s,1,2,1) + takeCoeff(lin,0,1,1)*takeCoeff(s,1,2,2) + 3*takeCoeff(lin,0,0,3)*takeCoeff(s,1,3,0) + 
            takeCoeff(lin,0,1,1)*takeCoeff(s,0,0,2)*takeCoeff(s,1,3,0) + 2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,0,2)*takeCoeff(s,1,3,0) + 
            2*takeCoeff(lin,0,0,2)*takeCoeff(s,1,3,1);
        
         result[2] = (std::complex<ScalarType>(0,0.5)*(Power(alpha[1],2) - 2*alpha[0]*alpha[2]))/Power(alpha[0],2);
      }
   }       

   return result;
}

}} // namespace capd::normalForms

#endif // _CAPD_NORMALFORMS_PLANARMAPS_HPP_ 

/// @}
