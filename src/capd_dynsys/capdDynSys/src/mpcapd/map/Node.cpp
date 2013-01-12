/// @addtogroup map
/// @{

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

#include "capd/intervals/mplib.h"
#include "capd/map/Node.hpp"

namespace capd{
  namespace map{

#ifdef __HAVE_MPFR__

template class Node<MpFloat>;
template class ConsNode<MpFloat>;
template class VarNode<MpFloat>;
template class UnaryNode<MpFloat>;
template class BinaryNode<MpFloat>;
template class SumNode<MpFloat>;
template class DifNode<MpFloat>;
template class MulNode<MpFloat>;
template class DivNode<MpFloat>;
template class SinNode<MpFloat>;
template class CosNode<MpFloat>;
template class ExpNode<MpFloat>;
template class LogNode<MpFloat>;
template class SqrtNode<MpFloat>;
template class PowNode<MpFloat>;

template class MulConsNode<MpFloat>;
template class MulParamNode<MpFloat>;
template class MulParamParamNode<MpFloat>;
template class DivByParamNode<MpFloat>;
template class DivConsByParamNode<MpFloat>;


template class Node<MpInterval>;
template class ConsNode<MpInterval>;
template class VarNode<MpInterval>;
template class SumNode<MpInterval>;
template class DifNode<MpInterval>;
template class MulNode<MpInterval>;
template class DivNode<MpInterval>;
template class SinNode<MpInterval>;
template class CosNode<MpInterval>;
template class ExpNode<MpInterval>;
template class LogNode<MpInterval>;
template class SqrtNode<MpInterval>;
template class PowNode<MpInterval>;

template class MulConsNode<MpInterval>;
template class MulParamNode<MpInterval>;
template class MulParamParamNode<MpInterval>;
template class DivByParamNode<MpInterval>;
template class DivConsByParamNode<MpInterval>;

#endif

  }} // namespace capd::map
/// @}
