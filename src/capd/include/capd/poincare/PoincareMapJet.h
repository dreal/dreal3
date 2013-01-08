/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file PoincareMapJet.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_POINCARE_POINCARE_MAP_JET_H_
#define _CAPD_POINCARE_POINCARE_MAP_JET_H_



#include <string>
#include "capd/dynset/C0Set.h"
#include "capd/dynset/C1Set.h"
#include "capd/dynset/C2Set.h"
#include "capd/dynset/CnSet.h"
#include "capd/poincare/PoincareException.h"
#include "capd/poincare/PoincareMap.h"

namespace capd{

/// This namespace contains classes to compute Poincare Maps and Time Maps
namespace poincare{

/**
 *  PoicareMapJet class rigorously computates Poincare Map.
 *
 *  For given Dynamical System and section it rigorously computes first return map
 *  to section (Poincare Map) and its derivatives.
 *
 *  It uses BasicPoincareMap and adds error estimates to the results.
 *
 *  Let
 *    - \f$ \varphi(t, x): R \times R^n -> R^n \f$ be a dynamical system generated
 *      by given vector field.
 *    - \f$ s: R^n \to R \f$ be a section function,
 *    - \f$ S = \{x \in R^n : s(x) = 0\} \f$
 *    - \f$ P: S \to S \f$ be a Poincare Map
 *    - for given point \f$ x \in S \f$ let T(x) be first return time (in given crossing direction)
 *      i.e.  \f$ P(x) = \varphi(T(x), x) \in S \f$
 *
 *  In the following we denote by
 *    - dP the derivative of Poincare Map P  : \f$ dP(x) = \frac{\partial P(x)}{\partial x} \f$
 *    - dT the derivative of T(x) : \f$ dT(x)  = \frac{\partial T(x)}{\partial x} \f$
 *    - dF the derivative of the flow : \f$ dF(x) = \frac{\partial \varphi(T(x), x)}{\partial x} \f$
 *  Then
 *    \f$ dP = dF + \frac{\partial \varphi}{\partial t} dT \f$
 *
 *  Parameters:
 *   - DS    dynamical system
 *       - DS::MapType  vector field type
 *   - FunT  map describing section :
 *       - FunT::FunctionType - section function type
 *       - FunT               - gradient function type
 *
 *  For more detailed description of expectation to these types se end of PoincareMap2.h file
 */

template<typename DS, typename FunT = typename DS::FunctionType >
class PoincareMapJet : public PoincareMap<DS, FunT>
{
public:
  typedef DS                        DynamicalSystemType; ///< dynamical system type
  typedef typename DS::MapType      VectorFieldType;    ///< vector field type
  typedef typename DS::MatrixType   MatrixType;         ///< matrix type
  typedef typename DS::VectorType   VectorType;         ///< vector type
  typedef typename DS::ScalarType   ScalarType;         ///< scalar entries type
  typedef typename ScalarType::BoundType BoundType;          ///< a type of the end for intervals
  typedef PoincareMap<DS, FunT> PoincareMapT;
  typedef typename DS::CurveType CurveType;

 // typedef FunT MapType;                                ///< section gradient type
  typedef FunT FunctionType;    ///< Section function type

  typedef capd::dynset::C0Set<MatrixType> C0Set;
  typedef capd::dynset::C1Set<MatrixType> C1Set;
  typedef capd::dynset::C2Set<MatrixType> C2Set;
  typedef capd::dynset::CnSet<MatrixType> CnSet;
  typedef typename CnSet::CnCoeffType     CnCoeffType;

  typedef typename PoincareMap<DS,FunT>::CrossingDirection CrossingDirection; ///< constants for section crossing direction

  /// Constructs PoincareMap for given dynamical system and section
  PoincareMapJet( DynamicalSystemType  & ds,
               FunctionType & section,
               CrossingDirection direction = None
    );

  /// Computes value of Poincare Map (used for C^0 sets)
  template<typename T>
  VectorType operator()(T& theSet);

  /// Computes value of Poincare Map and derivatives of the flow  (used for C^1 sets)
  template<typename T>
  VectorType operator()(T& theSet, MatrixType & dF);

  /// TODO: implement the following operators for higher order derivatives
/*
  /// Computes value of Poincare Map, derivatives and hessian of the flow (used for C^2 sets)
  template<typename T>
  VectorType operator()(T& theSet, MatrixType& dF, MatrixType hessian[]);

  /// Computes Poincare Map and derivatives of the flow to given order (used for C^n sets)
  template<typename T>
  VectorType operator()(T& theSet, CnCoeffType& result);
*/
protected:

/// Crosses the section and returns the value of Poincare Map.
/// It updates also derivatives.
/// We expect theSet to be just before the section.
/// After this function theSet is on the section or just after the section.
/// This function is common for all types of C^0, C^1, C^2 and C^n sets
  template<typename T>
  CurveType crossSection(T& theSet, const T& setAfterTheSection);

}; // end of template PoincareMap

// -----------------------  inline definitions -------------------------------

/**
 *   Constructs PoincareMap for given dynamical system and section
 *
 *  @param ds        dynamical system
 *  @param section   Poincare section
 *  @param crossing  section crossing direction
 *  @param factor    time step correction factor during section crossing (should be in interval (0, 1))
**/
template <typename DS, typename FunT>
inline PoincareMapJet<DS,FunT>::PoincareMapJet(
       DynamicalSystemType  & ds,
       FunctionType & section,
       typename PoincareMapT::CrossingDirection crossing
  ) : PoincareMapT(ds, section, crossing)
{}

}} // namespace capd::poincare

#include "capd/poincare/PoincareMapJet.hpp"

#endif  /* _POINCAREMAPJET_H */

/// @}
