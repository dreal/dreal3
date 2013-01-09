/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Function.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Daniel Wilczak 2000/2001-2004
  the main function: 'eqnanal' - creates a binary tree
  Each node contains an information about an operator or function:
  +,-,*,/,^ , sin, cos, log, exp , sqr
  the leafs of the tree contain a pointer either to a variable or a constant

  the function is not very sophistcated in the analysis of the formula text,
  hence it is desirable to use many parentheses to clearly indicate the order
  of all operations
*/

#ifndef _CAPD_MAP_FUNCTION_HPP_ 
#define _CAPD_MAP_FUNCTION_HPP_ 

#include <sstream>
#include <string>
#include <stdexcept>

#include "capd/map/Node.hpp"
#include "capd/map/BasicFunction.hpp"
#include "capd/map/Function.h"
#include "capd/map/Function_constructor.hpp"
#include "capd/map/Function_operator.hpp"
#include "capd/map/Parser.h"

namespace capd{
namespace map{

// -----------------------------------------------------------------------

template<typename VectorType>
const std::string& Function<VectorType>::partialDerivative(int i) const
{
  if(m_diff[i]=="?")
  {
    std::string temp = m_fun;
    m_diff[i] = diffanal(temp,i);
  }
  if (m_diff[i]=="") m_diff[i] = "0";
  return m_diff[i];
}

// -----------------------------------------------------------------------

template<typename VectorType>
void Function<VectorType>::setOrder(int a_new)
{
  BasicFunction<ScalarType>::setOrder(a_new);
  m_tree->setOrder(m_order,m_val);
}


/* _________________________________________________________________ */

template<typename VectorType>
std::string Function<VectorType>::gradient(int numberOfVariables) const
{
  std::string result = variables();
  result += "fun:";
  if(numberOfVariables>m_dim)
  {
    std::ostringstream message;
    message << "Function error: incorrect number of variables requested in gradient method\n";
    message << "Variables: " << variables() << "\n";
    message << "Formula: " << formula() << "\n";
    message << "requested number of variables: " << numberOfVariables;
    throw std::runtime_error(message.str());
  }
  int i;
  for(i=0;i<numberOfVariables-1;++i)
  {
    std::string temp = m_fun;
    if (m_diff[i]=="?")
      m_diff[i] = diffanal(temp,i);
    if (m_diff[i]=="")
      m_diff[i] = "0";
    result += m_diff[i] + ",";
  }
  
  if (m_diff[numberOfVariables-1]=="?")
  {
    std::string temp = m_fun;
    m_diff[i] = diffanal(temp,i);
  }
  if (m_diff[i]=="")
    m_diff[i] = "0";
  result += m_diff[numberOfVariables-1] + ";";
  return result;
}

/* _________________________________________________________________ */

template<typename VectorType>
VectorType Function<VectorType>::gradient(const VectorType& u)
{
  if(u.dimension()>m_dim)
  {
    std::ostringstream message;
    message << "Function error: incorrect number of variables requested in gradient method\n";
    message << "Variables: " << variables() << "\n";
    message << "Formula: " << formula() << "\n";
    message << "requested number of variables: " << u.dimension();
    throw std::runtime_error(message.str());
  }
  int i;
  if(m_diffObjects==0)
  {
    this->gradient(m_dim);
    m_diffObjects = new Function[m_dim];
    for(i=0;i<m_dim;++i)
    {
     m_diffObjects[i] = variables() + "fun:" + m_diff[i] + ";";
    }
  }
  VectorType result(u.dimension());
  for(i=0;i<u.dimension();++i)
    result[i] = m_diffObjects[i](u);
  return result;
}

}} // namespace capd::map

#endif // _CAPD_MAP_FUNCTION_HPP_ 

/// @}
