/// @addtogroup diffIncl
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DiffInclusion.hpp
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Tomasz Kapela, 2007 */

#ifndef _CAPD_DIFFINCL_DIFFINCLUSION_HPP_ 
#define _CAPD_DIFFINCL_DIFFINCLUSION_HPP_ 

#include <sstream>
#include <string>
#include <stdexcept>

#include "capd/dynsys/Taylor.hpp"
#include "capd/diffIncl/DiffInclusion.h"

namespace capd{
namespace diffIncl{


template <typename MapT, typename DynSysT>
DiffInclusion<MapT, DynSysT>::DiffInclusion(
           MultiMapType& diffIncl, 
           int order, 
           const ScalarType& step, 
           const NormType & norm
) 
  : m_norm ( norm.clone()),
    m_diffIncl(diffIncl),
    m_dynamicalSystem(diffIncl.getVectorField(), order, step) {
}

template <typename MapT, typename DynSysT>
DiffInclusion<MapT, DynSysT>::~DiffInclusion(){
  delete m_norm;
}
  

  
}} //namespace capd::diffIncl`

#endif // _CAPD_DIFFINCL_DIFFINCLUSION_HPP_ 

/// @}
