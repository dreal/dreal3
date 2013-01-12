/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnCoeff.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak  2006 */

#ifndef _CAPD_MAP_CNCOEFF_HPP_ 
#define _CAPD_MAP_CNCOEFF_HPP_ 

#include <algorithm>
#include <sstream>
#include "capd/map/CnCoeff.h"
#include "capd/basicalg/TypeTraits.h"
namespace capd{
namespace map{

// -----------------------------------------------------------------

template<typename MatrixT>
CnCoeff<MatrixT>::operator typename CnCoeff<MatrixT>::VectorType() const
{
  VectorType result(m_dim);
  typename VectorType::iterator b=result.begin(), e=result.end();
  const_iterator i=begin();
  int stride = newton(m_dim+m_rank,m_dim);
  while(b!=e)
  {
    *b = *i;
    ++b;
    i+=stride;
  }
  return result;
}

// -----------------------------------------------------------------

template<typename MatrixT>
CnCoeff<MatrixT>::operator typename CnCoeff<MatrixT>::MatrixType() const
{
  MatrixType result(m_dim,m_dim);
  typename MatrixType::iterator b=result.begin(), e=result.end();
  int i=0;
  while(b!=e)
  {
    const_iterator b1=begin(i,1), e1=end(i,1);
    while(b1!=e1)
    {
      *b = *b1;
      ++b;
      ++b1;
    }
    ++i;
  }
  return result;
}

// -----------------------------------------------------------------
template<typename MatrixT>
void CnCoeff<MatrixT>::setMatrix(const MatrixType& m)
{
  typename MatrixType::const_iterator b=m.begin(), e=m.end();
  int i=0;
  while(b!=e)
  {
    iterator b1=begin(i,1), e1=end(i,1);
    while(b1!=e1)
    {
      *b1 = *b;
      ++b;
      ++b1;
    }
    ++i;
  }
}


// -----------------------------------------------------------------

template<typename MatrixType>
void CnCoeff<MatrixType>::clear()
{
  iterator b=begin(), e=end();
  while(b!=e)
  {
    *b = capd::TypeTraits<ScalarType>::zero();
    ++b;
  }
}

// -----------------------------------------------------------------

template<typename MatrixType>
typename CnCoeff<MatrixType>::VectorType CnCoeff<MatrixType>::operator()(const VectorType& v) const
{
  VectorType result = VectorType(*this);
   
  for(int i=1;i<=m_rank;++i)
  {
    Multipointer mp = this->first(i);
    do{
      typename VectorType::ScalarType temp = power(v,mp);
      long f = mp.factorial();
      result += temp* (*this)(mp)/f;
    }while(this->next(mp));
  }
  return result;
}

// ----------------------------------------------------------
template<typename MatrixType>
std::ostream & print(
    std::ostream & str, const CnCoeff<MatrixType> & coeff,
    int minRank /*= 0*/, int maxRank /*= -1*/,
    int firstFun /*= 0*/, int lastFun /*= -1*/,
    int firstVariable /*= 0*/
){
  typedef typename CnCoeff<MatrixType>::Multiindex Multiindex;
  typedef typename CnCoeff<MatrixType>::Multipointer Multipointer;
  if(lastFun<0) lastFun=coeff.dimension();
  if(maxRank<0) maxRank=coeff.rank();
  for(int r=minRank; r<= maxRank; ++r){
    if(r)
      str << "\nderivatives of order " << r << " :";
    else
      str << "\nvalue :";
    Multiindex index(coeff.dimension());
    index[firstVariable] = r;
    Multipointer mp(index);
    do{
      str << "\n   "<< Multiindex(coeff.dimension(), mp) << "  : ";
      capd::vectalg::printVector(str, coeff(mp), firstFun, lastFun) ;
    }while(coeff.next(mp));
  }
  str << std::endl;
  return str;
}

/**
 * Return derivative information in human readable form
 *
 * You can specify which derivatives you want,
 * It will return all derivatives
 * \f$ df_i/dx^a \f$
 * where
 *   i = firstFun,..., lastFun
 *   |a| = minRank, ..., maxRank
 *
 * @param firstFun index of the first function
 * @param lastFun index of the last function
 * @param minRank minimum rank displayed
 * @param maxRank maximum rank displayed
 * @return string containing derivatives information
 */
template<typename MatrixType>
std::string CnCoeff<MatrixType>::toString(
       int firstFun /*= 0*/, int lastFun /*= -1*/,
       int firstVariable /*= 0*/,
       int minRank /*= 0*/, int maxRank /*= -1*/,
       int precision /* =15*/) const {
  std::ostringstream str;
  print(str, *this, minRank, maxRank, firstFun, lastFun, firstVariable);
  return str.str();
}

/**
 *  saves data to stream out with given precision
 *
 * - the default precision allows to load data without lose of precision,
 * - if given precision \b prec is less or equal to 0 the current precision is used
 *
 * Format:
 * \code
 *   rank (order of the highest derivative)
 *   dimension
 *
 *   coefficient in the order as they are stored in the memory
 *   each line contains one coefficient
 * \endcode
 */
template<typename MatrixType>
std::ostream &  CnCoeff<MatrixType>::save(
      std::ostream & out,
      std::streamsize prec /* = capd::TypeTraits<ScalarType>::numberOfDigits() + 1 */
  ) const {
    std::streamsize oldPrecision = out.precision();
    if(prec > 0){
      out.precision(prec);
    }
    out << this->rank() << "\n" << this->dimension()
        << "\n\n";
     const_iterator it = this->begin(), end_it = this->end();
     while(it != end_it) {
       out << *it << "\n";
       it++;
     }
     if(prec > 0){
       out.precision(oldPrecision);
     }
     out << std::endl;
     return out;
  }

  /// loads cn data from given stream
  /// (expected format is exactly this provided by save)
template<typename MatrixType>
std::istream & CnCoeff<MatrixType>::load(std::istream & in){

  int rank, dimension;
  in >> rank >> dimension;

  if((this->rank() != rank) || (this->dimension() != dimension)) {
    this->resize(rank, dimension, false);
  }
  iterator it = this->begin();
  while(it != this->end()) {
    in >> *it;
    it++;
    if(!in) {
      throw std::ios_base::failure(" Error when loading CnCoeff from stream ");
    }
  }
  return in;
}

}} // the end of the namespace capd::map

// -----------------------------------------------------------------

template<typename MatrixType>
capd::map::CnCoeff<MatrixType> operator+(const capd::map::CnCoeff<MatrixType>& x, const capd::map::CnCoeff<MatrixType>& y)
{
  if(x.dimension()!=y.dimension())
    throw std::runtime_error("CnCoeff operator+: incompatible dimensions of power series");
  capd::map::CnCoeff<MatrixType> result(x);
  typename capd::map::CnCoeff<MatrixType>::iterator i = result.begin();
  typename capd::map::CnCoeff<MatrixType>::const_iterator b = y.begin(), e=y.end();
  while(b!=e)
  {
    (*i) += (*b);
    ++b;
    ++i;
  }
  return result;
}

// -----------------------------------------------------------------

template<typename MatrixType>
capd::map::CnCoeff<MatrixType> operator-(const capd::map::CnCoeff<MatrixType>& x, const capd::map::CnCoeff<MatrixType>& y)
{
  if(x.dimension()!=y.dimension())
    throw std::runtime_error("CnCoeff operator-: incompatible dimensions of power series");
  capd::map::CnCoeff<MatrixType> result(x);
  typename capd::map::CnCoeff<MatrixType>::iterator i = result.begin();
  typename capd::map::CnCoeff<MatrixType>::const_iterator b = y.begin(), e=y.end();
  while(b!=e)
  {
    (*i) -= (*b);
    ++b;
    ++i;
  }
  return result;
}

// -----------------------------------------------------------------

template<typename MatrixType>
typename MatrixType::ScalarType computeProduct(
      const capd::map::CnCoeff<MatrixType>& second,
      const capd::vectalg::Multiindex& mi,
      const capd::vectalg::Multipointer& a,
      int p, int k
   )
{
  typedef typename MatrixType::ScalarType Scalar;
  typedef capd::vectalg::Multiindex Multiindex;
  typedef capd::vectalg::Multipointer Multipointer;

  Scalar result = capd::TypeTraits<Scalar>::zero();
  const typename Multipointer::IndicesSet& is = Multipointer::generateList(p,k);
  typename Multipointer::IndicesSet::const_iterator b=is.begin(), e=is.end();

  while(b!=e)
  {
    typename Multipointer::MultipointersVector::const_iterator bt = b->begin(), et=b->end();
    typename Multiindex::const_iterator ib= mi.begin();

    Multipointer delta = a.subMultipointer(*bt);
    Scalar temp = second(*ib,delta);
    ++bt;
    ++ib;
    while(bt!=et)
    {
      Multipointer delta = a.subMultipointer(*bt);
      temp *= second(*ib,delta);
      ++bt;
      ++ib;
    }
    ++b;
    result += temp;
  }
  return result;
}

// -----------------------------------------------------------------

template<typename MatrixType>
void computeComposition(
      const capd::map::CnCoeff<MatrixType>& first,
      const capd::map::CnCoeff<MatrixType>& second,
      capd::map::CnCoeff<MatrixType>& result,
      const capd::vectalg::Multipointer& a,
      bool nonlinearOnly
   )
{
  typedef typename MatrixType::ScalarType Scalar;
  typedef capd::vectalg::Multiindex Multiindex;
  typedef capd::vectalg::Multipointer Multipointer;
  typename Multiindex::IndicesSet listIndices;   

  Multiindex::generateList(result.dimension(),result.rank(),listIndices);
  int p = a.module();

  result(a).clear();
  int mink = nonlinearOnly ? 2 : 1;
  for(int k=mink;k<=p;++k)
  {
    typename Multiindex::MultiindexVector::iterator b = listIndices[k-1].begin(), e=listIndices[k-1].end();
    while(b!=e)
    {
      Multipointer mp(b->dimension(),b->begin());
      std::sort(mp.begin(),mp.end());
      Scalar product = computeProduct(second,*b,a,p,k);
      result(a) += first(mp) * product;
      ++b;
    }
  }
}

// -----------------------------------------------------------------


template<typename MatrixType>
void substitutionPowerSeries(
      const capd::map::CnCoeff<MatrixType>& first,
      const capd::map::CnCoeff<MatrixType>& second,
      capd::map::CnCoeff<MatrixType>& result, bool nonlinearOnly
   )
// the function computes substitution of two power series truncated to the same order as 'first' and 'second'
// as a result we obtain an expansion of first(second)
{
  typedef typename MatrixType::ScalarType Scalar;
  typedef capd::vectalg::Multiindex Multiindex;
  typedef capd::vectalg::Multipointer Multipointer;

  for(int i=1;i<=first.rank();++i)
  {
    Multipointer a = first.first(i);
    do{
      computeComposition(first,second,result,a,nonlinearOnly);
    }while(first.next(a));
  }
   
  if(!nonlinearOnly)
    result() = first();
}

#endif // _CAPD_MAP_CNCOEFF_HPP_ 

/// @}
