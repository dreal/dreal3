//////////////////////////////////////////////////////////////////////////////
///
///  @file BasicPoincareMapJet.h
///  
///  @author kapela  @date   Apr 5, 2011
//////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2011 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef CAPD_POINCARE_BASICPOINCAREMAPJET_H_
#define CAPD_POINCARE_BASICPOINCAREMAPJET_H_

namespace capd {
namespace poincare {
/// @addtogroup poincare
/// @{


template<typename DS, typename FunT = typename DS::FunctionType >
class BasicPoincareMapJet : public BasicPoincareMap<DS, FunT>
{
public:
  typedef DS                        DynamicalSystemType; ///< dynamical system type
  typedef typename DS::MapType      VectorFieldType;    ///< vector field type
  typedef typename DS::MatrixType   MatrixType;         ///< matrix type
  typedef typename DS::VectorType   VectorType;         ///< vector type
  typedef typename DS::ScalarType   ScalarType;         ///< scalar entries type
  typedef BasicPoincareMap<DS, FunT> PoincareMapT;
  typedef typename DS::CurveType    CurveType;

  // typedef FunT MapType;                                ///< section gradient type
  typedef FunT FunctionType;    ///< Section function type

  //  typedef capd::dynset::C0Set<MatrixType> C0Set;
  //  typedef capd::dynset::C1Set<MatrixType> C1Set;
  //  typedef capd::dynset::C2Set<MatrixType> C2Set;
  //  typedef capd::dynset::CnSet<MatrixType> CnSet;
  //  typedef typename CnSet::CnCoeffType     CnCoeffType;

  typedef typename BasicPoincareMap<DS,FunT>::CrossingDirection CrossingDirection; ///< constants for section crossing direction

  /// Constructs PoincareMap for given dynamical system and section
  BasicPoincareMapJet(
      DynamicalSystemType  & ds,
      FunctionType & section,
      CrossingDirection direction = None
  );

  /// Computes value of Poincare Map
  VectorType operator()(VectorType v);  // we copy v to be changed in computations

  /// Computes value of Poincare Map and point after the section suitable for successive iterations of Poincare Map
  VectorType operator()(VectorType v, VectorType & afterSection);  // we copy v to be changed in computations

  /// Computes value of Poincare Map and derivatives of the flow
  VectorType operator()(VectorType v, MatrixType & dF);

protected:


//  /// Function reaches the section (n times)
//  /// Result:
//  ///   - theSet is just before the section,
//  ///   - it returns the set on the section or just after it
//  template<typename T>
//  T reachSection(T& theSet, int n = 1);

  /// Crosses the section and returns the value of Poincare Map.

  ScalarType findCrossingTime(const CurveType & curve);

}; // end of template PoincareMap

// -----------------------  inline definitions -------------------------------

/**
 *   Constructs PoincareMap for given dynamical system and section
 *
 *  @param ds        dynamical system
 *  @param section   Poincare section
 *  @param crossing  section crossing direction
 **/
template <typename DS, typename FunT>
inline BasicPoincareMapJet<DS,FunT>::BasicPoincareMapJet(
    DynamicalSystemType  & ds,
    FunctionType & section,
    CrossingDirection crossing
)
: PoincareMapT(ds, section, crossing) {
}



/// @} 
}} // end of namespace capd::poincare

#endif /* CAPD_POINCARE_BASICPOINCAREMAPJET_H_ */
