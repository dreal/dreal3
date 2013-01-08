/// @addtogroup diffIncl
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DiffInclusionLN.hpp
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Tomasz Kapela, 2007 */

#ifndef _CAPD_DIFFINCL_DIFFINCLUSIONLN_HPP_ 
#define _CAPD_DIFFINCL_DIFFINCLUSIONLN_HPP_ 

#include "capd/diffIncl/DiffInclusionLN.h"
#include "capd/diffIncl/DiffInclusion.hpp"

namespace capd{
namespace diffIncl{


template <typename MapT, typename DynSysT>
DiffInclusionLN<MapT, DynSysT>::DiffInclusionLN(
    MultiMapType& A_diffIncl,
    int A_order,
    ScalarType const & A_step,
    NormType const & A_norm
) 
: BaseClass(A_diffIncl, A_order, A_step, A_norm) {
}

template <typename MapT, typename DynSysT>
typename DiffInclusionLN<MapT, DynSysT>::VectorType DiffInclusionLN<MapT, DynSysT>::perturbations(const VectorType& x){

  VectorType W_1 = dynamicalSystemEnclosure(x);
  VectorType W_2 = diffInclusionEnclosure(x);

  MatrixType J = m_diffIncl.getVectorField()[W_2]; 
  VectorType deltha = m_diffIncl.perturbations(W_2);

  ScalarType C = right((*m_norm)(deltha));
  ScalarType l = right((*m_norm)(J));

  ScalarType D = (l.contains(0.0))? C*getStep() : (C*(exp(l*getStep())-1))/l;
  VectorType result(x.dimension());

  for(int i=0; i< result.dimension(); ++i)
    result[i] = ScalarType(-D.rightBound(), D.rightBound());

  return result;
}

}} //namespace capd::diffIncl

#endif // _CAPD_DIFFINCL_DIFFINCLUSIONLN_HPP_ 

/// @}
