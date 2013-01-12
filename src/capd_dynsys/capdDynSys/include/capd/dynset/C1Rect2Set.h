/////////////////////////////////////////////////////////////////////////////
/// @file C1Rect2Set.h
///
/// @author kapela
/// Created on: Oct 25, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

/* Author: Daniel Wilczak 2002-2004 */

#ifndef _CAPD_DYNSET_C1RECT2SET_H_
#define _CAPD_DYNSET_C1RECT2SET_H_

#include "capd/dynset/C1Set.h"
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/C1DynSys.h"
#include "capd/geomset/CenteredDoubletonSet.h"
#include "capd/geomset/MatrixDoubletonSet.h"
#include "capd/dynset/ReorganizationPolicy.h"
#include "capd/dynset/C1Rect2Reorganization.h"
#include "capd/dynset/QRPolicy.h"



namespace capd{
namespace dynset{
// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////
///
///  The C1 set is represented as doubleton: x + C*r0 + B*r;
///  and is moved by Lohner last method.
///
///  Internal representation :
///        C*r0 - basic 'Lipschitz part'
///        B*r  - QR-decomposition of the remaining errors
///
///  C^1-Lohner algorithm.
///  Derivative of the flow moved via QR decomposition (third method)
///  the set part - QR decomposition (3-rd method)
///////////////////////////////////////////////////////////////////////
template<typename MatrixT, typename QRPolicy = FullQRWithPivoting>
class C1Rect2Set : public C1Set<MatrixT>,
                   public capd::geomset::CenteredDoubletonSet<MatrixT>,
                   public capd::geomset::MatrixDoubletonSet<MatrixT> {
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef C1Set<MatrixT> SetType;
  typedef capd::geomset::CenteredDoubletonSet<MatrixT> C0BaseSet;
  typedef capd::geomset::MatrixDoubletonSet<MatrixT> C1BaseSet;
  typedef bool C0Rect;
  typedef bool C1Rect;

  C1Rect2Set(const NormType& norm, int);
  C1Rect2Set(const VectorType& x, const NormType&);
  C1Rect2Set(const VectorType& x, const VectorType& r, const NormType&);
  C1Rect2Set(const VectorType& x, const MatrixType& B, const VectorType& r, const NormType&);
  C1Rect2Set(const C0BaseSet & c0part, const C1BaseSet & c1part, const NormType & lnorm);
  C1Rect2Set(const C1Rect2Set & set);
  ~C1Rect2Set(){delete m_Norm;}

  void move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys);
  void move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys, C1Rect2Set& result) const;

  const NormType* getNorm(void) const;

  operator VectorType() const;
  operator MatrixType() const;
  C1Rect2Set &operator=(const VectorType &v);
  C1Rect2Set &operator=(const C1Rect2Set &S);

  std::string show(void) const;
  std::string name() const { return "C1Rect2Set"; }
  std::string toString() const { return C0BaseSet::toString() +"\n" + C1BaseSet::toString(); }

protected:

// a representation of the set: x + C*r0 + B*r

  using C0BaseSet::m_x;
  using C0BaseSet::m_B;
  using C0BaseSet::m_r;
  using C0BaseSet::m_C;
  using C0BaseSet::m_r0;

  using C1BaseSet::m_D;
  using C1BaseSet::m_Bjac;
  using C1BaseSet::m_R;
  using C1BaseSet::m_Cjac;
  using C1BaseSet::m_R0;

  VectorType m_currentSet;
  MatrixType m_currentMatrix;

  NormType *m_Norm; //the logarithmic Norm<IVectorType,IMatrixType> used in the computation of a rough
                  // enclosure for the variational part
};

template <typename MatrixType, typename QRPolicy>
class ReorganizationPolicy<C1Rect2Set<MatrixType,QRPolicy> > {
public:
  typedef C1Rect2Reorganization<C1Rect2Set<MatrixType,QRPolicy> > DefaultReorganization;
};
/// @}
// -------------------------------------------------------------------

template <typename MatrixType, typename QRPolicy>
inline void C1Rect2Set<MatrixType,QRPolicy>::move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys) {
  move(c1dynsys,*this);
}

template <typename MatrixType, typename QRPolicy>
inline C1Rect2Set<MatrixType,QRPolicy>::operator typename C1Rect2Set<MatrixType,QRPolicy>::VectorType(void) const {
  return m_currentSet;
}

template <typename MatrixType, typename QRPolicy>
inline const typename C1Rect2Set<MatrixType,QRPolicy>::NormType* C1Rect2Set<MatrixType,QRPolicy>::getNorm(void) const {
  return m_Norm;
}

}} // the end of the namespace capd::dynset

#endif
