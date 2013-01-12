/////////////////////////////////////////////////////////////////////////////
/// @file C1PpedSet.h
///
/// @author kapela
/// Created on: Oct 24, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_C1PPEDSET_H_
#define _CAPD_C1PPEDSET_H_

#include "capd/dynset/C1Set.h"
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/C1DynSys.h"
#include "capd/geomset/CenteredAffineSet.h"
#include "capd/geomset/MatrixAffineSet.h"

namespace capd {
namespace dynset {
// @addtogroup capd
/// @{

/**
 * In C1PpedSet both  C0 and C1 parts are represented as: x + B*r
 *
 * where:
 * -  x - set center
 * -  B - matrix close to Jacobian
 * -  r  - box containing all 'errors' (computed via parallelograms method)
 */
template<typename MatrixT>
class C1PpedSet: public C1Set<MatrixT> ,
                 public capd::geomset::CenteredAffineSet<MatrixT>,
                 public capd::geomset::MatrixAffineSet<MatrixT> {
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::geomset::CenteredAffineSet<MatrixT> C0BaseSet;
  typedef capd::geomset::MatrixAffineSet<MatrixT> C1BaseSet;
  typedef typename C1Set<MatrixT>::SetType SetType;
  typedef typename C1Set<MatrixT>::DynSysType DynSysType;


  C1PpedSet(int dim, const NormType& aNorm);
  C1PpedSet(const NormType& aNorm, int dim);
  C1PpedSet(const VectorType& x, const NormType& aNorm);
  C1PpedSet(const VectorType& x, const VectorType& r, const NormType& aNorm);
  C1PpedSet(const VectorType& x, const MatrixType& B, const VectorType& r, const NormType& aNorm);
  C1PpedSet(const C1PpedSet& set);
  ~C1PpedSet() {delete m_Norm;}
  void move(DynSysType & c1dynsys);
  void move(DynSysType & c1dynsys, C1PpedSet& result) const;

  std::string show(void) const;
  std::string name() const { return "C1PpedSet"; }

  const NormType *getNorm(void) const;

  //using C0BaseSet::operator VectorType;
  operator VectorType() const{
    return C0BaseSet::operator VectorType();
  }
  operator MatrixType() const{
    return C1BaseSet::operator MatrixType();
  }
  C1PpedSet& operator=(const VectorType &v);
  C1PpedSet& operator=(const C1PpedSet &S);

protected:
  using C0BaseSet::m_x; // set is represented as x + B*r in C0BaseSet
  using C0BaseSet::m_B;
  using C0BaseSet::m_r;

  using C1BaseSet::m_D; // derivatives are stored as D + Bjac * R in C1BaseSet
  using C1BaseSet::m_Bjac;
  using C1BaseSet::m_R;

  NormType *m_Norm; //the logarithmic norm used in the computation of a rough
  // enclosure for the variational part
};

/// @}
// ------------------------------------------------

template<typename MatrixType>
inline void C1PpedSet<MatrixType>::move(DynSysType & c1dynsys){
  move(c1dynsys,*this);
}

template<typename MatrixType>
inline const typename C1PpedSet<MatrixType>::NormType *C1PpedSet<MatrixType>::getNorm(void) const{
  return m_Norm;
}

}} // the end of the namespace capd::dynset
#endif // _CAPD_C1PPEDSET_H_
