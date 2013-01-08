/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnCoeff.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak  2006 */

#include <vector>
#include "capd/map/CnContainer.h"

#ifndef _CAPD_MAP_CNCOEFF_H_ 
#define _CAPD_MAP_CNCOEFF_H_ 

namespace capd{
namespace map{

// the class is used to store all partial derivatives of a map
// f:R^dim->R^dim up to the order 'n' (including n).

template<typename MatrixT> 
class CnCoeff : public CnContainer<typename MatrixT::ScalarType>
{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename MatrixType::RefColumnVectorType RefVectorType;
  typedef typename MatrixType::RowVectorType VectorType;

  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;
  typedef CnContainer<ScalarType> CnContainerType;
  typedef typename CnContainerType::Multipointer Multipointer;
  typedef typename CnContainerType::Multiindex Multiindex;
   
  CnCoeff();
  CnCoeff(int a_dim, int a_rank);
  CnCoeff(int a_dim, int a_rank,bool);
   
// this operator returns a vector of partial derivatives, i.e. result[i] = d^{mp}f_i
  RefVectorType operator()(const Multipointer& mp) const; 
// this operator returns a value of function, i.e. 0-order derivatives
  operator VectorType() const;
// this operator returns a value of function, i.e. 0-order derivatives
  RefVectorType operator()(void) const;
// this operator returns first order derivatives as a matrix
  operator MatrixType() const;
  CnCoeff& operator=(const CnCoeff& c);
  void clear();
  void setMatrix(const MatrixType&);

// since CnCoeff represents (up to factorials) a power series 
// it may be used as a function

  VectorType operator()(const VectorType&) const;
  /// returns string containing derivatives information
  std::string toString(int minFun = 0, int maxFun = -1,
                       int firstVariable = 0, int minRank = 0, int maxRank= -1) const;
  /// saves data to stream out with given precision
  /// (the default precision allows to load data without lose of precision)
  std::ostream & save(
      std::ostream & out,
      std::streamsize prec = capd::TypeTraits<ScalarType>::numberOfDigits() + 1
  ) const;
  friend std::ostream & operator << (std::ostream & out, const CnCoeff & cncoeff){
      return cncoeff.save(out, 0);
  }

  /// loads cn data from given stream
  /// (expected format is exactly this provided by save)
  std::istream & load(std::istream & in);
  friend std::istream & operator >> (std::istream & in, CnCoeff & cncoeff){
    return cncoeff.load(in);
  }

  using CnContainerType::operator();
  using CnContainerType::begin;
  using CnContainerType::end;
  using CnContainerType::dimension;
  using CnContainerType::rank;
  using CnContainerType::resize;
   
protected:
  using CnContainerType::index;
  using CnContainerType::m_dim;
  using CnContainerType::m_rank;
  using CnContainerType::m_data;
}; // the end of class CnCoeff

// --------------------- inline definitions ------------------------

template<typename MatrixType>
inline CnCoeff<MatrixType>::CnCoeff()
  : CnContainerType(1,1)
{
  clear();
}

// -----------------------------------------------------------------

template<typename MatrixType>
inline CnCoeff<MatrixType>::CnCoeff(int a_dim, int a_rank)
  : CnContainerType(a_dim, a_rank)
{
  clear();
}

// -----------------------------------------------------------------

template<typename MatrixType>
inline CnCoeff<MatrixType>::CnCoeff(int a_dim, int a_rank,bool)
  : CnContainerType(a_dim, a_rank)
{}

// -----------------------------------------------------------------

template<typename MatrixType>
inline typename CnCoeff<MatrixType>::RefVectorType 
  CnCoeff<MatrixType>::operator()(const Multipointer& mp) const
{
  return RefVectorType(begin(0,mp.dimension()) + index(mp),newton(m_dim+m_rank,m_dim),m_dim);
}

// -----------------------------------------------------------------

template<typename MatrixType>
inline typename CnCoeff<MatrixType>::RefVectorType 
   CnCoeff<MatrixType>::operator()(void) const
{
  return RefVectorType(begin(),newton(m_dim+m_rank,m_dim),m_dim);
}

// -----------------------------------------------------------------

template<typename MatrixType>
inline CnCoeff<MatrixType>& CnCoeff<MatrixType>::operator=(const CnCoeff& c)
{
  CnContainerType::operator=(c);
  return *this;
}

}} // namespace capd::map


// Since CnCoeff represents a power series (in fact all the partial derivatives of some function),
// there are obvious operators defined for the power series
template<typename MatrixType>
capd::map::CnCoeff<MatrixType> operator+(const capd::map::CnCoeff<MatrixType>&, const capd::map::CnCoeff<MatrixType>&);

template<typename MatrixType>
capd::map::CnCoeff<MatrixType> operator-(const capd::map::CnCoeff<MatrixType>&, const capd::map::CnCoeff<MatrixType>&);

template<typename MatrixType>
void substitutionPowerSeries(
      const capd::map::CnCoeff<MatrixType>&, 
      const capd::map::CnCoeff<MatrixType>&,
      capd::map::CnCoeff<MatrixType>& result,
      bool nonlinearOnly
   );

#endif // _CAPD_MAP_CNCOEFF_H_ 

/// @}
