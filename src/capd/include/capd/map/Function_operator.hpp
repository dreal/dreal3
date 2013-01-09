/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Function_operator.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Daniel Wilczak 2000-2004
   This file contains the implementation of public and friend operators
   for class function
*/

#ifndef _CAPD_MAP_FUNCTION_OPERATOR_HPP_ 
#define _CAPD_MAP_FUNCTION_OPERATOR_HPP_ 

#include <stdexcept>
#include <cstdlib>
#include <sstream>
#include "capd/map/Function.h"


namespace capd{
namespace map{

/* _____________ THE OPERATORS TO RETURN VALUE OF FUNCTION _____________*/

// for functions with only one variable
template<typename VectorType>
typename Function<VectorType>::ScalarType
   Function<VectorType>::operator()(const typename Function<VectorType>::ScalarType& v) const
{
  m_val[0]=v;
  m_tree->reset();
  return m_tree->operator()(0);
}

/* _________________________________________________________________ */

template<typename VectorType>
typename Function<VectorType>::ScalarType Function<VectorType>::operator()(const VectorType &v) const
{
  int d = v.dimension();
  if(d > m_dim)
  {
    std::ostringstream message;
    message << "Exception in Function::operator(const VectorType &)\n";
    message << "VectorType has " << v.dimension() << " coordinates\n";
    message << "Function object has " << m_dim << " variables \n";

    throw std::runtime_error(message.str());
  }
  for(int i=0;i<d;++i)
    m_val[i*m_order]=v[i];
  m_tree->reset();
  return m_tree->operator()(0);
}

/* _________________________________________________________________ */

template<typename VectorType>
typename Function<VectorType>::ScalarType Function<VectorType>::operator()(const VectorType &v, int i) const
{
  int d = v.dimension();
  if(d > m_dim)
  {
    std::ostringstream message;
    message << "Exception in Function::operator(const VectorType &,int)\n";
    message << "VectorType has " << d << " coordinates\n";
    message << "Function object has " << m_dim << " variables";
    throw std::runtime_error(message.str());
  }

  if (i<0 || i>=m_order)
  {
    std::ostringstream s;
    s << "Incorrect index " << i << " in Function::operator()(const vector&, int)\n";
    s << "The m_order is " << (m_order-1) << "\n";
    throw std::out_of_range(s.str());
  }
  for(int j=0;j<d;++j)
    m_val[j*m_order+i]=v[j];
  if(!i) 
    m_tree->reset();
  return m_tree->operator()(i);
}

/* _________________________________________________________________ */

template<typename VectorType>
Function<VectorType>& Function<VectorType>::operator=(const char *s)
{
  BasicFunction<ScalarType>::operator=(s);
  try{
    deleteTables();
    createFromText(s,0);
  } catch(std::runtime_error &r)
  {
    createDefault();
    std::string re = "exception in Function &Function::operator=(const char *)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
  return *this;
}

/* _________________________________________________________________ */

template<typename VectorType>
Function<VectorType>& Function<VectorType>::operator=(const std::string &s)
{
  BasicFunction<ScalarType>::operator=(s);
  try{
    deleteTables();
    createFromText(s,0);
  } catch(std::runtime_error &r)
  {
    createDefault();
    std::string re = "exception in Function &Function::operator=(const string &)\n";
    re += r.what();
    throw std::runtime_error(re);
  }
  return *this;
}

/* _________________________________________________________________ */

template<typename VectorType>
Function<VectorType>& Function<VectorType>::operator=(const Function<VectorType> &f) //a copy operator
{
  BasicFunction<ScalarType>::operator=(f);
  deleteTables();
  createFromObject(f);
  return *this;
}

/* ______________________________________________________________ */

template<typename VectorType>
std::string Function<VectorType>::operator[](int i) const // returns partial derivative as a string
{
  if(i >= m_dim || i< 0 )
  {
    std::ostringstream message;
    message << "Exception in Function::operator[](int i)\n";
    message << "Cannot compute partial derivative with respect to " << i << " coordinate\n";
    message << "Function object has " << m_dim << " variables";

    throw std::runtime_error(message.str());
  }

  std::string b = variables();
  b += "fun:";
  partialDerivative(i);
  b += m_diff[i] + ";";
  return b;
}


}} // namespace capd::map

#endif // _CAPD_MAP_FUNCTION_OPERATOR_HPP_ 

/// @}
