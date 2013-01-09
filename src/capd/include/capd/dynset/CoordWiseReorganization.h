/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CoordWiseReorganization.h
///
/// @author kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_COORDWISEREORGANIZATION_H_
#define _CAPD_DYNSET_COORDWISEREORGANIZATION_H_

#include "capd/dynset/FactorPolicy.h"

namespace capd{
namespace dynset{


/**
 *  In this reorganization policy column vector B_i corresponding to the biggest coordinate in r (r_i)
 *  replaces vector in C_j the 'closest' to B_i  and the r_i is moved to r0
 */
template <typename DoubletonT, typename FactorPolicyT = capd::dynset::MemberFactorPolicy >
class CoordWiseReorganization : public FactorPolicyT{

public:
    typedef DoubletonT SetType;
    typedef typename SetType::MatrixType MatrixType;
    typedef typename MatrixType::RowVectorType VectorType;
    typedef typename MatrixType::ScalarType ScalarType;
   // typedef typename ScalarType::BoundType BoundType;
    typedef FactorPolicyT FactorPolicy;

  CoordWiseReorganization(double factor = 1.0, double minReorganizationSize = 0.0)
    : FactorPolicy(factor), m_minReorganizationSize(minReorganizationSize){ }

  /// it finds index of the biggest coordinate of vector v
  static int findBiggestCoord(const VectorType & v) {
    typedef typename ScalarType::BoundType BoundType;
    int best = 0;
    BoundType max = v[0].rightBound();
    for(int i=1; i<v.dimension(); i++){
      BoundType value = v[i].rightBound();
      if(max < value){
        best = i;
        max = value;
      }
    }
    return best;
  }
  /// returns index of the column vector in base which best fits to given vector v
  static int findBestFittingVector(const MatrixType & base, const VectorType & v) {
    VectorType vInBase = capd::matrixAlgorithms::gauss(base, v);
    return findBiggestCoord(vInBase);
  }

  /// reorganize given set
  void reorganize(SetType & result) const{
       // index of coordinate with biggest diameter in r
     int rIndex = findBiggestCoord(diam(result.get_r()));
       // index of coordinate in r0 and column in C which will be replaced
     int r0Index = findBestFittingVector(result.get_C(), result.getColumn_B(rIndex));

     ScalarType removedValue = result.getElement_r0(r0Index);
     VectorType removedVector = result.getColumn_C(r0Index);

       // replacing coordinate in r0 and column in C with data from r and B
     result.setColumn_C(r0Index, result.getColumn_B(rIndex));
     result.setElement_r0(r0Index, result.getElement_r(rIndex));

       // we express removed vector in the new base and add it to r0
     removedVector = capd::matrixAlgorithms::gauss(result.get_C(), removedVector) * removedValue;
     result.set_r0(result.get_r0()+removedVector);

       // we set r[rIndex] to 0
     result.setElement_r(rIndex, ScalarType(0.0));
  }

  bool isReorganizationNeeded(const SetType & result) const{
    ScalarType rozmiar = capd::vectalg::size(result.get_r()).rightBound();
    return (FactorPolicy::isReorganizationEnabled() &&
        (rozmiar > m_minReorganizationSize) &&
        (rozmiar > FactorPolicy::getFactor() * capd::vectalg::size(Transpose(result.get_B()) *( result.get_C()*result.get_r0()))));
  }

  /// makes reorganization if needed.
  /// return true if reorganization was performed
  bool reorganizeIfNeeded(SetType & result) const{
    if(isReorganizationNeeded(result)){
      reorganize(result);
      return true;
    }
    return false;
  }
  std::string name() const {
    return "coor-wise reorganization";
  }
protected :
  double m_minReorganizationSize;
};

}}

#endif //_CAPD_DYNSET_COORDWISEREORGANIZATION_H_
