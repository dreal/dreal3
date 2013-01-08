/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2Coeff.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak  2006 */

#ifndef _CAPD_MAP_C2COEFF_HPP_ 
#define _CAPD_MAP_C2COEFF_HPP_ 

#include "capd/vectalg/Matrix.hpp"
#include "capd/map/C2Coeff.h"

namespace capd{
namespace map{

template<typename ScalarType>
int C2Coeff<ScalarType>::defaultDim = 0;

// ---------------------------------------------------

template<typename Scalar>
C2Coeff<Scalar>::C2Coeff(const C2Coeff& s)
{
  dim = s.dim;
  data = new ScalarType[dim*dim*(1+dim)/2];
  iterator i1=begin(), i2=end();
  const_iterator j1=s.begin();
  while(i1!=i2)
  {
    *i1=*j1;
    ++i1;
    ++j1;
  }
}

// ---------------------------------------------------

template <typename ScalarType>
C2Coeff<ScalarType>& C2Coeff<ScalarType>::operator=(const C2Coeff& s)
{
  if(dim!=s.dim)
  {
    delete []data;
    dim = s.dim;
    data = new ScalarType[dim*dim*(1+dim)/2];
  }
  iterator i1=begin(), i2=end();
  const_iterator j1 = s.begin();
  while(i1!=i2)
  {
    *i1=*j1;
    ++i1;
    ++j1;
  }
  return *this;
}

// ---------------------------------------------------

template <typename ScalarType,int d>
C2Coeff<ScalarType> operator*(const capd::vectalg::Matrix<ScalarType,d,d>& m, const C2Coeff<ScalarType>& c2)
{
  int dim = m.numberOfRows();
  if(dim!=c2.dimension())
  {
    throw std::runtime_error("operator* - incompatible dimensions of matrix and C2Coeff");
  }
  C2Coeff<ScalarType> result(dim);
  result.clear();
  for(int j=0;j<dim;++j)
    for(int c=j;c<dim;++c)
      for(int i=0;i<dim;++i)
        for(int r=0;r<dim;++r)
          result(i,j,c) += m[i][r]*c2(r,j,c);
  return result;
}


// ---------------------------------------------------

template <typename ScalarType>
C2Coeff<ScalarType>& C2Coeff<ScalarType>::operator+=(const C2Coeff& s)
{
  if(dim!=s.dim)
  {
    throw std::runtime_error("incompatible dimensions in C2Coeff::operator+=");
  }
  iterator i1=begin(), i2=end();
  const_iterator j1 = s.begin();
  while(i1!=i2)
  {
    *i1 += *j1;
    ++i1;
    ++j1;
  }
  return *this;
}

// ---------------------------------------------------

template <typename ScalarType>
void C2Coeff<ScalarType>::clear()
{
  iterator b=begin(), e=end();
  while(b!=e)
  {
    *b = ScalarType(0.);
    ++b;
  }
}

}} // namespace capd::map

#endif // _CAPD_MAP_C2COEFF_HPP_ 

/// @}
