/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2Map.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2001-2005 */

#ifndef _CAPD_MAP_C2MAP_HPP_
#define _CAPD_MAP_C2MAP_HPP_

#include <string>
#include <sstream>
#include <stdexcept>
#include <vector>

#include "capd/map/C2Coeff.hpp"
#include "capd/map/Map.hpp"
#include "capd/map/C2Map.h"

namespace capd{
namespace map{

/*___________________________________________*/


template<typename MatrixType>
void C2Map<MatrixType>::setCurrentTime(const ScalarType& a_time) const
{
  Map<MatrixType>::setCurrentTime(a_time);
  for(int i=0;i<m_dim*m_dim*(1+m_dim)/2;++i)
    m_c2der[i].setCurrentTime(a_time,m_dim);
}

/*___________________________________________*/


template<typename MatrixType>
void C2Map<MatrixType>::differentiateTime() const
{
  Map<MatrixType>::differentiateTime();
  for(int i=0;i<m_dim*m_dim*(1+m_dim)/2;++i)
    m_c2der[i].differentiateTime(m_dim);
}


/*___________________________________________*/


template<typename MatrixType>
void C2Map<MatrixType>::computeSecondDerivatives(const VectorType& iv, C2CoeffType& result) const
{
  int i=0;
  typename C2CoeffType::iterator b=result.begin(), e=result.end();
  while(b!=e)
  {
    *b = m_c2der[i](iv);
    ++i;
    ++b;
  }
}

/*___________________________________________*/

template<typename MatrixType>
typename C2Map<MatrixType>::C2CoeffType*
   C2Map<MatrixType>::computeSecondDerivatives(VectorType iv[], int p) const
{
  int i,r;
  C2CoeffType* result = new (m_dim) C2CoeffType[p];
  for(r=0;r<p;++r)
  {
    i=0;
    typename C2CoeffType::iterator b=result[r].begin(), e=result[r].end();
    while(b!=e)
    {
      *b = m_c2der[i](iv[r],r);
      ++i;
      ++b;
    }
  }
  return result;
}

/*___________________________________________*/

template<typename MatrixType>
C2Map<MatrixType>::C2Map(void)
{
  m_c2der = new FunctionType[m_dim];
}

/*___________________________________________*/

template<typename MatrixType>
C2Map<MatrixType>::C2Map(const char* s, int order) : Map<MatrixType>(s,order)
{
  allocateC2Der();
}

/*___________________________________________*/

template<typename MatrixType>
C2Map<MatrixType>::C2Map(const std::string& f, int order) : Map<MatrixType>(f,order)
{
  allocateC2Der();
}

/*___________________________________________*/

template<typename MatrixType>
C2Map<MatrixType>::C2Map(const C2Map<MatrixType>& m) : Map<MatrixType>(m)
{
  allocateC2Der();
}

/*_____________________________________________*/

template<typename MatrixType>
C2Map<MatrixType>& C2Map<MatrixType>::operator=(const char* s)
{
  Map<MatrixType>::operator=(s);
  delete[]m_c2der;
  allocateC2Der();
  return *this;
}

/*_______________________________________________*/

template<typename MatrixType>
C2Map<MatrixType>& C2Map<MatrixType>::operator=(const std::string &f)
{
  Map<MatrixType>::operator=(f);
  delete[]m_c2der;
  allocateC2Der();
  return *this;
}

/*________________________________________________*/

template<typename MatrixType>
C2Map<MatrixType>& C2Map<MatrixType>::operator=(const C2Map<MatrixType> &m)
{
  Map<MatrixType>::operator=(m);
  delete []m_c2der;
  allocateC2Der();
  return *this;
}

/*________________________________________________*/


template<typename MatrixType>
void C2Map<MatrixType>::setOrder(int the_new)
{
  Map<MatrixType>::setOrder(the_new);
  for(int i=0;i<m_dim*m_dim*(1+m_dim)/2;++i)
    m_c2der[i].setOrder(the_new);
}

/*________________________________________________*/

template<typename MatrixType>
void C2Map<MatrixType>::setParameter(const std::string &name, const ScalarType &value)
{
  Map<MatrixType>::setParameter(name,value);
  for(int i=0;i<m_dim*m_dim*(1+m_dim)/2;++i)
  {
    m_c2der[i].setParameter(name,value);
  }
}

/*________________________________________________*/

template<typename MatrixType>
void C2Map<MatrixType>::allocateC2Der()
{
  m_c2der = new FunctionType[m_dim*m_dim*(m_dim+1)/2];
  int i,j,k;
  for(i=0;i<m_dim;++i)
    for(j=0;j<m_dim;++j)
      for(k=0;k<=j;k++)
      {
        m_c2der[i*m_dim*(m_dim+1)/2 + j*(j+1)/2 + k] = m_der[i*m_dim+j][k];
        m_c2der[i*m_dim*(m_dim+1)/2 + j*(j+1)/2 + k].setOrder(m_order);
      }
}

/*________________________________________________*/

}} // namespace capd::map

#endif // _CAPD_MAP_C2MAP_HPP_

/// @}
