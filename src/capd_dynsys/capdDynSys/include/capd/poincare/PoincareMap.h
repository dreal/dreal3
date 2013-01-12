/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file PoincareMap.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_POINCARE_POINCARE_MAP_H_
#define _CAPD_POINCARE_POINCARE_MAP_H_



#include <string>
#include "capd/dynset/C0Set.h"
#include "capd/dynset/C1Set.h"
#include "capd/dynset/C2Set.h"
#include "capd/dynset/CnSet.h"
#include "capd/poincare/PoincareException.h"
#include "capd/poincare/BasicPoincareMap.h"

namespace capd{

/// This namespace contains classes to compute Poincare Maps and Time Maps
namespace poincare{

/**
 *  PoicareMap class rigorously computates Poincare Map.
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
class PoincareMap : public BasicPoincareMap<DS, FunT>
{
public:
  typedef DS                        DynamicalSystemType; ///< dynamical system type
  typedef typename DS::MapType      VectorFieldType;    ///< vector field type
  typedef typename DS::MatrixType   MatrixType;         ///< matrix type
  typedef typename DS::VectorType   VectorType;         ///< vector type
  typedef typename DS::ScalarType   ScalarType;         ///< scalar entries type
  typedef typename ScalarType::BoundType BoundType;          ///< a type of the end for intervals

 // typedef FunT MapType;                                ///< section gradient type
  typedef FunT FunctionType;    ///< Section function type

  typedef capd::dynset::C0Set<MatrixType> C0Set;
  typedef capd::dynset::C1Set<MatrixType> C1Set;
  typedef capd::dynset::C2Set<MatrixType> C2Set;
  typedef capd::dynset::CnSet<MatrixType> CnSet;
  typedef typename CnSet::CnCoeffType     CnCoeffType;

  typedef typename BasicPoincareMap<DS,FunT>::CrossingDirection CrossingDirection; ///< constants for section crossing direction

/// constant timeStepCorrectionFactor is used as a correction factor to multiply
/// the time step in procedure reachSection when comming close to section
/// and actual time step is to large. The value 0.9 is just from numerical simulations
/// as a good working. It can be changed to a value from the interval (0,1)
  //static
  BoundType timeStepCorrectionFactor;
  //static
  int maxCorrectionTries;            ///< maximal number of correction tries
  //static
  ScalarType minCrossingTimeStep;    ///< minimal time step during section crossing

  /// Constructs PoincareMap for given dynamical system and section
  PoincareMap( DynamicalSystemType  & ds,
               FunctionType & section,
               CrossingDirection direction = None,
               const BoundType & errorTolerance = 0.1
    );

  /// Computes value of n-th iterate of the Poincare Map (used for C^0 sets)
  template<typename T>
  VectorType operator()(T& theSet, int n = 1);

  /// Computes value of n-th iterate of Poincare Map and derivatives of the flow  (used for C^1 sets)
  template<typename T>
  VectorType operator()(T& theSet, MatrixType & dF, int n = 1);

  /// Computes value of n-th iterate of Poincare Map, derivatives and hessian of the flow (used for C^2 sets)
  template<typename T>
  VectorType operator()(T& theSet, MatrixType& dF, MatrixType hessian[], int n = 1);

  /// Computes n-th iterate of Poincare Map and derivatives of the flow to given order (used for C^n sets)
  template<typename T>
  VectorType operator()(T& theSet, CnCoeffType& result, int n = 1);

protected:
  template<typename T>
  void checkTransversability ( const T & theSet,  const VectorType & bounds);
  template<typename T>
  ScalarType getSign( const T & theSet,  VectorType & position, bool updatePosition, const VectorType & bounds);
  template<typename T>
  ScalarType getSign( const T & theSet,  VectorType & position, bool updatePosition);
/// This function moves theSet with the given flow and stops just before the section (for n-th iterate of Poincare Map)
/// (closer than sectionFactor*sizeOfTheSet) (to be used in fuction crossSection)
/// It returns set on the section or just after the section (suitable for a computation of next Poincare Map iteration)
/// This function is common for all types of C^0, C^1, C^2, C^n sets
  template<typename T>
  T reachSection(T& theSet, int n = 1);

  /// Functions reaches the section (n times).
  /// As result it returns:
  /// - theSet is just before the section,
  /// - setAfterSection is on the section or just after it
  /// for the last iteration.
  template<typename T>
  void findSectionCrossing(T & theSet, T & setAfterSection, int n = 1);

  /// On input theSet is 'one step' before the section
  /// On output theSet is before the section and closer than sectionFactor*sizeOfTheSet
  template<typename T>
  void approachSection(T & theSet);

/// Crosses the section and returns the value of Poincare Map.
/// It updates also derivatives.
/// We expect theSet to be just before the section.
/// After this function theSet is on the section or just after the section.
/// This function is common for all types of C^0, C^1, C^2 and C^n sets
  template<typename T>
  VectorType crossSection(T& theSet, const T& setAfterTheSection);

// These function are used in crossSection only
// the sets of different types should be computed in a different way
// the C^0 sets have not defined the MatrixType operators

  void saveMatrices(C0Set&){}
  void saveMatrices(C1Set&);
  void saveMatrices(C2Set&);
  void saveMatrices(CnSet&);

  void computeJacEnclosure(C0Set &S, VectorType &V);
  void computeJacEnclosure(C1Set &S, VectorType &V);
  void computeJacEnclosure(C2Set &S, VectorType &V);
  void computeJacEnclosure(CnSet &S, VectorType &V);

  MatrixType* derivativeOfFlow;     ///< stores derivative of the flow (if needed)
  MatrixType* hessianOfFlow;        ///< stores hessian of the flow (if needed)
  CnCoeffType* partialDerivatives;  ///< stores derivative of the flow (only for C^n sets)

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
inline PoincareMap<DS,FunT>::PoincareMap(
       DynamicalSystemType  & ds,
       FunctionType & section,
       typename BasicPoincareMap<DS,FunT>::CrossingDirection crossing,
       const BoundType & errorTolerance
  ) : BasicPoincareMap<DS,FunT>(ds, section, crossing, errorTolerance),
  timeStepCorrectionFactor(0.9),
  maxCorrectionTries(10),
  minCrossingTimeStep( capd::TypeTraits< typename PoincareMap<DS,FunT>::ScalarType >::epsilon()*4)
{}

/* Definitions of expected interfaces of template parameters.

template <typename FunT>
class DynamicalSystemInterface{
  // Following internal types should be defined
  typedef FunT MapType;
  typedef typename MapType::MatrixType MatrixType;
  typedef typename MapType::VectorType VectorType;
  typedef typename MapType::ScalaType ScalarType;

  MapType getField() = 0;
  // void setField(MapType &) = 0;  // ???
  int  getOrder() = 0;
  void setOrder(int) = 0;
  ScalarType getStep() =0;
  void setStep(ScalarType) = 0;

  // C^0 computations
  VectorType enclosure(const VectorType &) = 0;

  // NOT FINISHED
};

class SetInterface{
  void move(DynamicalSystemInterface);
  void move(DynamicalSystemInterface, SetInterface & result)
  operator VectorType() = 0;
};

class SectionGradientInterface{
  class FunctionType{
    SectionInterface gradient() = 0;
    VectorType operator()(VectorType) =0;
  };
  MatrixType operator()(VectorType) = 0;
};
 */

}} // namespace capd::poincare

#include "capd/poincare/PoincareMap_templateMembers.h"

#endif  /* _POINCAREMAP_H */

/// @}
