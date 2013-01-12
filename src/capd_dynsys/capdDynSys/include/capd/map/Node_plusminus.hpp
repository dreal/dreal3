/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Node_plusminus.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2004-2005 */

#ifndef _CAPD_MAP_NODE_PLUSMINUS_HPP_ 
#define _CAPD_MAP_NODE_PLUSMINUS_HPP_ 

namespace capd{
namespace map{

template<typename ScalarType>
ScalarType& SumNode<ScalarType>::operator()(int i)
{
  if(i<=this->m_maxComputedDerivative)
    return this->value[i];
  this->m_maxComputedDerivative = i;

  return this->value[i] = (*(this->left))(i) + (*(this->right))(i);
}

template<typename ScalarType>
ScalarType& DifNode<ScalarType>::operator()(int i)
{
  if(i<=this->m_maxComputedDerivative)
    return this->value[i];
  this->m_maxComputedDerivative = i;

  return this->value[i] = (*(this->left))(i) - (*(this->right))(i);
}

// --------------------------------- global Operators -------------------------

template<typename ScalarType>
capd::map::Node<ScalarType>& operator+(capd::map::Node<ScalarType>& x, capd::map::Node<ScalarType>& y)
{
  if(x.getOrder()!=y.getOrder())
    throw std::runtime_error("operator+(Node&, Node&) - incompatible dimensions");
  return *(new capd::map::SumNode<ScalarType>(x.getOrder(), &x,&y));
}

template<typename ScalarType>
capd::map::Node<ScalarType>& operator-(capd::map::Node<ScalarType>& x, capd::map::Node<ScalarType>& y)
{
  if(x.getOrder()!=y.getOrder())
    throw std::runtime_error("operator-(Node&, Node&) - incompatible dimensions");
  return *(new capd::map::DifNode<ScalarType>(x.getOrder(),&x,&y));  
}

}} // namespace capd::map


#endif // _CAPD_MAP_NODE_PLUSMINUS_HPP_ 

/// @}
