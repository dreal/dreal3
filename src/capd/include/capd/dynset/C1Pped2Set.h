// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C1Pped2Set.h
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

#ifndef _CAPD_DYNSET_C1PPED2SET_H_
#define _CAPD_DYNSET_C1PPED2SET_H_

#include "capd/dynset/C1Set.h"
#include "capd/vectalg/Norm.h"
#include "capd/geomset/CenteredDoubletonSet.h"
#include "capd/geomset/MatrixDoubletonSet.h"
#include "capd/dynset/ReorganizationPolicy.h"
#include "capd/dynset/QRReorganization.h"


/* C^1-Lohner algorithm.
   Derivative of the flow moved via QR decomposition (third method)
   the set part - QR decomposition (3-rd method)
*/

namespace capd{
namespace dynset{

template<typename MatrixT>
class C1Pped2Set : public C1Set<MatrixT>,
                   public capd::geomset::CenteredDoubletonSet<MatrixT>,
                   public capd::geomset::MatrixDoubletonSet<MatrixT> {
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef typename C1Set<MatrixT>::SetType SetType;
  typedef typename C1Set<MatrixT>::DynSysType DynSysType;
  typedef capd::geomset::CenteredDoubletonSet<MatrixT> C0BaseSet;
  typedef capd::geomset::MatrixDoubletonSet<MatrixT> C1BaseSet;
  typedef bool C0Rect;
  typedef bool C1Rect;

  C1Pped2Set(const NormType& norm, int);
  C1Pped2Set(const VectorType& x, const NormType&);
  C1Pped2Set(const VectorType& x, const VectorType& r, const NormType&);
  C1Pped2Set(const VectorType& x, const MatrixType& B, const VectorType& r, const NormType&);
  C1Pped2Set(const C1Pped2Set & set);
  ~C1Pped2Set(){delete m_Norm;}


  void move(DynSysType & c1dynsys, C1Pped2Set& result) const;

  // C1Set interface implementation {

  /// computes image of the set after one step/iterate of the dynamical system
  void move(DynSysType & c1dynsys);

     /// returns an eclosure of the set in the canonical coordinates
  operator VectorType() const;
    /// returns derivative
   operator MatrixType() const ;
   /// returns used norm
  const NormType* getNorm(void) const;
   /// returns a set detailed information
   std::string show(void) const;
  // end of C1Set interface

  C1Pped2Set &operator=(const VectorType &v);
  C1Pped2Set &operator=(const C1Pped2Set &S);

  std::string name() const { return "C1Pped2Set"; }
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

template <typename MatrixType>
class ReorganizationPolicy<C1Pped2Set<MatrixType> > {
  typedef QRReorganization<C1Pped2Set<MatrixType> > DefaultReorganization;
};
// -------------------------------------------------------------------

template<typename MatrixType>
inline void C1Pped2Set<MatrixType>::move(DynSysType & c1dynsys) {
  move(c1dynsys,*this);
}
template<typename MatrixType>
inline C1Pped2Set<MatrixType>::operator typename C1Pped2Set<MatrixType>::VectorType(void) const {
  return m_currentSet;
}

template<typename MatrixType>
inline const typename C1Pped2Set<MatrixType>::NormType* C1Pped2Set<MatrixType>::getNorm(void) const {
  return m_Norm;
}

}} // the end of the namespace capd::dynset

#endif //_C1RECT2SET_
/// @}
