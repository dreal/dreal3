/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file enclosure.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2001-2004 */

#ifndef _CAPD_DYNSYS_ENCLOSURE_H_ 
#define _CAPD_DYNSYS_ENCLOSURE_H_ 

namespace capd{
namespace dynsys{


/**
  * Computes enclosure of solution of ODE during one time step  i.e \f$ \varphi([0,step],x) \f$
  *
  * @param vectorField vector field
  * @param x0          initial condition
  * @param timeStep    final time
  * @return  enclosure of solution of ODE
  */
template<typename MapType>
typename MapType::VectorType enclosure(  MapType & vField,
                                         typename MapType::MatrixType::RowVectorType const & x, 
                                         typename MapType::ScalarType const & step
                                      );


//###########################################################//

/**
   * Finds enclosure for Jacobian matrix (variational part) for whole time step
   *
   * @param vectorField  vector field
   * @param timeStep     time step
   * @param enclosure    enclosure of solution of ODE during whole time step
   * @param the_norm     logarithmic norm used to bound solution
   * @return matrix containing enclosure of Jacobian
   */
// source- "C^1-Lohner algorithm" by P. Zgliczynski
template<typename MapType, typename NormType>
typename MapType::MatrixType jacEnclosure(
                        const MapType& vectorField, 
                        const typename MapType::ScalarType& step,
                        const typename MapType::VectorType &enc, 
                        const NormType &the_norm,
                        typename MapType::ScalarType* o_logNormOfDerivative=0
                        );

}} //namespace capd::dynsys

#endif // _CAPD_DYNSYS_ENCLOSURE_H_ 

/// @}
