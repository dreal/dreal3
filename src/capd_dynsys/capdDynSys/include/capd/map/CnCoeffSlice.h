//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file CnCoeffSlice.h
///
/// @author Tomasz Kapela   @date 2010-03-06
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_MAP_CNCOEFFSLICE_H_
#define _CAPD_MAP_CNCOEFFSLICE_H_
#include "capd/map/CnCoeff.hpp"

namespace capd {
namespace map {

template <typename MatrixT>
class CnCoeffSlice {
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename MatrixType::RefColumnVectorType RefVectorType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef CnCoeff<MatrixType> CnCoeffType;
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;
  typedef typename CnCoeffType::CnContainerType CnContainerType;
  typedef typename CnContainerType::Multipointer Multipointer;
  typedef typename CnContainerType::Multiindex Multiindex;

  /// construct slice only with derivatives of function of given index
  /// @remark we do not copy data but refer to the original container
  CnCoeffSlice(CnCoeffType & coeff, int functionIndex) :
    m_coeff(&coeff), m_index(functionIndex) {
  }

  /// dimension of domain (number of variables)
  int dimension() const {
    return m_coeff->dimension();
  }

  /// return maximum order stored
  int rank() const {
    return m_coeff->rank();
  }
  int maxOrder() const {
    return m_coeff->rank();
  }

  /// returns a value of function, i.e. 0-order derivatives
  ScalarType & operator()(void);
  const ScalarType & operator()(void) const;

  /// direct access to the table of derivatives
  ScalarType & operator[](int index) {
    return *(m_coeff->begin(m_index) + index);
  }
  /// direct access to the table of derivatives
  const ScalarType & operator[](int index) const {
      return *(m_coeff->begin(m_index) + index);
  }
  /// returns partial derivative, i.e. d^{|mp|}f / dx^{mp}
  ScalarType & operator()(const Multipointer & mp){
    return (*m_coeff)(m_index, mp);
  }
  /// returns partial derivative, i.e. d^{|mp|}f / dx^{mp}
  const ScalarType & operator()(const Multipointer & mp) const{
    return (*m_coeff)(m_index, mp);
  }

  // ???
  // ScalarType & operator()(const Multipointer&, const Multipointer&);
  // const ScalarType & operator()(int i, const Multipointer&, const Multipointer&) const;

  /// returns derivative with respect to x_i
  ScalarType & operator()(int i){
    return (*m_coeff)(m_index, i);
  }
  /// returns derivative with respect to x_i
  const ScalarType & operator()(int i) const{
    return (*m_coeff)(m_index, i);
  }
  /// returns second derivative with respect to x_i and x_j
  ScalarType & operator()(int i, int j){
    return (*m_coeff)(m_index, i, j);
  }
  /// returns second derivative with respect to x_i and x_j
  const ScalarType & operator()(int i, int j) const {
    return (*m_coeff)(m_index, i, j);
  }

  // ScalarType & operator()(int i, int j, int c);
  // const ScalarType & operator()(int i, int j, int c) const;

  // iterators through all derivatives
  iterator begin(){
    return m_coeff->begin(m_index);
  }
  iterator end(){
    return m_coeff->end(m_index);
  }
  const_iterator begin() const {
    return m_coeff->begin(m_index);
  }
  const_iterator end() const {
    return m_coeff->end(m_index);
  }

  // iterators for partial derivatves of given order
  iterator begin(int order){
    return m_coeff->begin(m_index, order);
  }
  iterator end(int order){
    return m_coeff->begin(m_index, order);
  }
  const_iterator begin(int order) const{
    return m_coeff->begin(m_index, order);
  }
  const_iterator end(int order) const{
    return m_coeff->begin(m_index, order);
  }

  // multipointer selection
  // notice, the loop do-while for multipointers agrees exactly with iterators on suitable level
  // iterators are faster. However, they do not give an information about the index of partial drivative.
  // More precisely, for iterator b=begin(i,level) and Multipointer mp=first(level); we have
  // *b = (*this)(i,mp);
  // next(mp); ++b; // and if  b!=end(i,level) we have
  // *b = (*this)(i,mp);

  /// returns multipointer of first derivative of given order
  Multipointer first(int order) const {
    return m_coeff->first(order);
  }
  /// returns true and multipointer of the next derivative of the current order
  ///         or false if we are already on the last derivative.
  bool next(Multipointer & mp) const {
    return m_coeff->next(mp);
  }

  /// sets all coefficients to zero
  void clear() {
    iterator it = begin(), e = end();
    while(it != e) {
      *it = 0.0;
      it++;
    }
  }

  /// CnCoeffSlice represents (up to factorials) a power series of a function f: R^n -> R to a given order.
  /// it return evaluation of this power series on vector x
  ScalarType operator()(const VectorType & x) const {
    ScalarType result = (*m_coeff)(m_index);
    for(int i = 1; i <= maxOrder(); ++i) {
      Multipointer mp = this->first(i);
      do {
        typename VectorType::ScalarType temp = power(x, mp);
        long f = mp.factorial();
        result += temp * (*this)(mp) / f;
      } while(next(mp));
    }
    return result;
  }
  /** returns string containing derivatives information in human readable form
   *
   * @param firstVariable display derivatives with respect to variables starting with firstVariable index
   * @param minOrder      minimum order of displayed derivatives
   * @param maxOrder      maximum order of displayed derivatives
   * @return              string that contains derivatives of orders in [minOrder, maxOrder]
   */
  std::string toString(int firstVariable = 0, int minRank = 0, int maxRank = -1) const {
    return m_coeff->toString(m_index, m_index, firstVariable, minRank, maxRank);
  }
  void isSumOf(const CnCoeffSlice & x, const CnCoeffSlice & y){
    const_iterator ix = x.begin(), iy = y.begin();
    iterator result = begin(),  stop = end();
    while(result != stop){
      *result = *ix + *iy;
       result++;  ix++;  iy++;
    }
  }
  void isDiferenceOf(const CnCoeffSlice & x, const CnCoeffSlice & y){
      const_iterator ix = x.begin(), iy = y.begin();
      iterator result = begin(),  stop = end();
      while(result != stop){
        *result = *ix - *iy;
         result++;  ix++;  iy++;
      }
  }
  void isProductOf(const CnCoeffSlice & x, const CnCoeffSlice & y){
    this->clear();
    int maxRank = rank();
    for(int xOrder = 0; ((xOrder <= x.rank()) && (xOrder <= maxRank)); ++xOrder){
      Multipointer mx = x.first(xOrder);
      do{
        int lastOrder = std::min(y.rank(), maxRank - xOrder);
        for(int yOrder = 0; yOrder <= lastOrder; ++yOrder){
          Multipointer my = y.first(yOrder);
          do{
            Multipointer mxy = capd::vectalg::sumMultipointers(mx,my);
            (*this)(mxy) += x(mx)*y(my)/my.factorial()/mx.factorial()*mxy.factorial();

          }while(y.next(my));
        }
      }while(x.next(mx));
    }
  }

  CnCoeffSlice & operator /= (const ScalarType & divisor){
    iterator it = begin();
    while(it!= end()){
      *it /= divisor;
      ++it;
    }
    return *this;
  }
protected:
  CnCoeffType * m_coeff;
  int m_index;
};

}} // end of namespace capd::map

#endif // _CAPD_MAP_CNCOEFFSLICE_H_
