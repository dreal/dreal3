/// @addtogroup diffIncl
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DiffInclusionLN.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Tomasz Kapela, 2007 */

#ifndef _CAPD_DIFFINCL_DIFFINCLUSIONLN_H_ 
#define _CAPD_DIFFINCL_DIFFINCLUSIONLN_H_ 

#include "capd/diffIncl/DiffInclusion.h"

namespace capd{
namespace diffIncl{

/**
 * Class for rigorous integration of differential inclusions.
 * It uses Logarithmic Norms  to bound perturbations.
 *
 * For more details on algorithm see: <br>
 *   T. Kapela, P. Zgliczyński, A Lohner-type algorithm for control systems and ordinary differential inclusions,
 *   Discrete and Continuous Dynamical Systems B, 11 (2009), 365-385.
 *
 * Template arguments:
 * - MapT     - MultiMap that stores RHS of the differential inclusion in the form : selection + 'error bounds'
 *              (we assume that it implements all methods that class capd::diffIncl::MultiMap has).
 * - DynSysT  - numerical method for ODE integration
 */
template<typename MapT, typename DynSysT = capd::dynsys::Taylor< typename MapT::MapType> >
class DiffInclusionLN : public capd::diffIncl::DiffInclusion<MapT, DynSysT>{

public:
  typedef DiffInclusion<MapT, DynSysT> BaseClass;
  typedef typename BaseClass::MultiMapType   MultiMapType;
  typedef typename BaseClass::MapType        MapType;
  typedef typename BaseClass::FunctionType   FunctionType;
  typedef typename BaseClass::MatrixType     MatrixType;
  typedef typename BaseClass::VectorType     VectorType;
  typedef typename BaseClass::ScalarType     ScalarType;
  typedef typename BaseClass::NormType       NormType;


  /**
   * Constructor
   *
   * @param diffIncl   RHS of the differential inclusion in the form: selected ODE + perturbations
   * @param order      order of numerical method for ODE integration
   * @param step       time step for ODE numerical integrator
   * @param norm       logarithmic norm
   */
  DiffInclusionLN( MultiMapType & diffIncl, 
      int order,
      ScalarType const & step,
      NormType const & norm
  );


  /// Bounds for perturbation of solution of selected ODE after one time step
  VectorType perturbations(const VectorType & x);

  using BaseClass::enclosure;
  using BaseClass::diffInclusionEnclosure;
  using BaseClass::dynamicalSystemEnclosure;
  using BaseClass::getStep;

protected:
  using BaseClass::m_norm;
  using BaseClass::m_diffIncl;

};


}} // namespace capd::diffIncl

#endif // _CAPD_DIFFINCL_DIFFINCLUSIONLN_H_ 

/// @}
