//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file C1Coeff.h
///
/// @author Tomasz Kapela   @date 2010-04-20
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_MAP_C1COEFF_H_
#define _CAPD_MAP_C1COEFF_H_

namespace capd{
namespace map{

template <typename MatrixT>
class C1Coeff {
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename MatrixType::RefColumnVectorType RefVectorType;
  typedef typename MatrixType::RowVectorType VectorType;

  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;

  C1Coeff(){
  }
  C1Coeff(int dim): m_value(dim), m_derivative(dim,dim){
  }
  C1Coeff(const VectorType & v, const MatrixType & der): m_value(v), m_derivative(der){
  }

  /// this operator returns a value of function, i.e. 0-order derivatives
   operator const VectorType & () const{
     return m_value;
   }
   /// this operator returns a value of function, i.e. 0-order derivatives
   const VectorType & operator()(void) const{
     return m_value;
   }
   /// this operator returns first order derivatives as a matrix
   operator const MatrixType & () const{
     return m_derivative;
   }
   C1Coeff& operator=(const VectorType & v){
     m_value = v;
     return *this;
   }
   void clear(){
     m_value.clear();
     m_derivative.clear();
   }
   void setMatrix(const MatrixType& der){
     m_derivative = der;
   }
   void setDerivative(const MatrixType & der){
     m_derivative = der;
   }
   const MatrixType & getDerivative()const{
     return m_derivative;
   }
   MatrixType & refDerivative(){
     return m_derivative;
   }
private:
   VectorType m_value;
   MatrixType m_derivative;

};
}} // end of namespace capd::map

#endif // _CAPD_MAP_C1COEFF_H_
