/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Node.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_MAP_NODE_HPP_ 
#define _CAPD_MAP_NODE_HPP_ 

#include <stdexcept>
#include <sstream>
#include <cmath>

#include "capd/map/Node.h"
#include "capd/map/Node_sincos.hpp"
#include "capd/map/Node_plusminus.hpp"
#include "capd/map/Node_explog.hpp"
#include "capd/map/Node_powsqr.hpp"
#include "capd/map/Node_muldiv.hpp"
#include "capd/map/Node_invtrig.hpp"

namespace capd{
namespace map{

template<typename ScalarType>
Node<ScalarType>::~Node(){}

// ---------------------------------------------------------------

template<typename ScalarType>
void Node<ScalarType>::computeDerivatives(int a_upTo)
{
  if(a_upTo>=m_order)
    throw std::runtime_error("Node::computeDerivatives - required m_order to large");
  for(int i=0;i<a_upTo;++i)
    this->operator()(i);
}

// ---------------------------------------------------------------

template<typename ScalarType>
void Node<ScalarType>::reset()
{
  if(left) left->reset();
  if(right) right->reset();
  m_maxComputedDerivative = -1;
}

template<typename ScalarType>
void Node<ScalarType>::allocateAndClear()
{
  value = new ScalarType[m_order];
  iterator b=begin(), e=end();
  while(b!=e)
  {
    *b = ScalarType(0);
    ++b;
  }
}

// ---------------------------------------------------------------

template<typename ScalarType>
ConsNode<ScalarType>::ConsNode(int a_order, ScalarType a_number) 
  : Node<ScalarType>(a_order,0,0)
{
  this->allocateAndClear();
  *(this->value) = a_number;
}

// ---------------------------------------------------------------

template<typename ScalarType>
void ConsNode<ScalarType>::setOrder(int a_order, ScalarType*)
{
  if(this->m_order==a_order) return;
  ScalarType c = this->value[0];
  delete [] this->value;
  this->m_order = a_order;
  this->allocateAndClear();
  *(this->value) = c;
}

// ---------------------------------------------------------------

template<typename ScalarType>
VarNode<ScalarType>::VarNode(int a_order, ScalarType *a_number, int a_variable)
  : Node<ScalarType>(a_order,0,0)
{
  this->value = a_number;
  this->m_numberOfVariables = a_variable;
}

// ---------------------------------------------------------------

template<typename ScalarType>
void VarNode<ScalarType>::setOrder(int a_order, ScalarType *a_val)
{
  this->m_order = a_order;
  this->value = &a_val[this->m_numberOfVariables*this->m_order];
}

// ---------------------------------------------------------------

template<typename ScalarType>
std::ostream& operator<<(std::ostream& out, const capd::map::Node<ScalarType>& n)
{
  out << "{";
  if(n.getOrder()>0){
    if(n[0]>=ScalarType(0)) out << " ";
    out << n[0];
  }
  for(int i=1;i<n.getOrder();i++)
  {
    out << ",";
    if(n[i]>=ScalarType(0)) out << " ";
    out << n[i];
  }
  out << "}";
  return out;
}

}} //namespace capd::map

#endif // _CAPD_MAP_NODE_HPP_ 

/// @}
