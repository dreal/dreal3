
/////////////////////////////////////////////////////////////////////////////
/// @file Node.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/interval/lib.h"
#include "capd/map/Node.hpp"

namespace capd{
  namespace map{

template class Node<double>;
template class ConsNode<double>;
template class VarNode<double>;
template class UnaryNode<double>;
template class BinaryNode<double>;

template class SumNode<double>;
template class DifNode<double>;
template class MulNode<double>;
template class DivNode<double>;
template class SinNode<double>;
template class CosNode<double>;
template class ExpNode<double>;
template class LogNode<double>;
template class SqrtNode<double>;
template class PowNode<double>;

template class MulConsNode<double>;
template class MulParamNode<double>;
template class MulParamParamNode<double>;
template class DivByParamNode<double>;
template class DivConsByParamNode<double>;

template class Node<Interval>;
template class ConsNode<Interval>;
template class UnaryNode<Interval>;
template class BinaryNode<Interval>;
template class VarNode<Interval>;
template class SumNode<Interval>;
template class DifNode<Interval>;
template class MulNode<Interval>;
template class DivNode<Interval>;
template class SinNode<Interval>;
template class CosNode<Interval>;
template class ExpNode<Interval>;
template class LogNode<Interval>;
template class SqrtNode<Interval>;
template class PowNode<Interval>;

template class MulConsNode<Interval>;
template class MulParamNode<Interval>;
template class MulParamParamNode<Interval>;
template class DivByParamNode<Interval>;
template class DivConsByParamNode<Interval>;


  }} // namespace capd::map
