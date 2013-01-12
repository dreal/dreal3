/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Node_sincos.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_MAP_NODE_SINCOS_HPP_ 
#define _CAPD_MAP_NODE_SINCOS_HPP_ 

#include <stdexcept>
#include <sstream>
#include <cmath>

namespace capd{
namespace map{

// -------------------------- operators ----------------------------------

template<typename ScalarType>
ScalarType& SinNode<ScalarType>::operator()(int i)
{
  if(i<=this->m_maxComputedDerivative)
    return this->value[i];
  this->m_maxComputedDerivative = i;

  (*(this->left))(i);
  if(i==0)
  {
    this->right->value[i] = cos(this->left->value[0]);
    return this->value[i] = sin(this->left->value[0]);
  }
  ScalarType result(0.);
  for(int j=0;j<i;++j)
    result += (i-j) * this->value[j] * this->left->value[i-j];
  this->right->value[i] = -result/ScalarType(i);

  result=ScalarType(0.);
  for(int k=0;k<i;++k)
    result += (i-k) * (this->right->value[k]) * (this->left->value[i-k]);

  return this->value[i] = result/ScalarType(i);
}

template<typename ScalarType>
ScalarType& CosNode<ScalarType>::operator()(int i)
{
  if(i<=this->m_maxComputedDerivative)
    return this->value[i];
  this->m_maxComputedDerivative = i;

  (*(this->left))(i);
  if(i==0)
  {
    this->right->value[i] = sin(this->left->value[0]);
    return this->value[i] = cos(this->left->value[0]);
  }

  ScalarType result(0.);
  for(int j=0;j<i;++j)
    result += (i-j) * this->value[j] * this->left->value[i-j];
  this->right->value[i] = result/ScalarType(i);

  result=ScalarType(0.);
  for(int k=0;k<i;++k)
    result += (i-k) * this->right->value[k] * this->left->value[i-k];

  return this->value[i] = -result/ScalarType(i);
}

}} // namespace capd::map

#endif // _CAPD_MAP_NODE_SINCOS_HPP_ 

/// @}
