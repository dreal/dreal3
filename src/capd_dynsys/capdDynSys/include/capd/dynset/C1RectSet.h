/////////////////////////////////////////////////////////////////////////////
/// @file C1RectSet.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C1RECTSET_H_
#define _CAPD_DYNSET_C1RECTSET_H_

#include "capd/dynset/C1Set.h"
#include "capd/vectalg/Norm.h"
#include "capd/dynsys/C1DynSys.h"
#include "capd/geomset/CenteredAffineSet.h"
#include "capd/geomset/MatrixAffineSet.h"
#include "capd/dynset/QRPolicy.h"

namespace capd {
namespace dynset {
/// @addtogroup dynset
/// @{


/**
 *  In C1RectSet both C0 and C1 part are represented as  x + B*r
 *
 *  where
 *    x - center point
 *    B - matrix ('change of coordinates')
 *    r - interval set (almost zero centered product of intervals)
 *
 *  Set is moved via "QR-decomposition".
 *  @see P.Zgliczynski "C^1-Lohner algorithm".
 */
template <typename MatrixT, typename QRPolicy = FullQRWithPivoting>
class C1RectSet: public C1Set<MatrixT> ,
                 public capd::geomset::CenteredAffineSet<MatrixT>,
                 public capd::geomset::MatrixAffineSet<MatrixT> {
public:
  typedef MatrixT MatrixType;
  typedef  typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef C1Set<MatrixT> SetType;
  typedef capd::geomset::CenteredAffineSet<MatrixT> C0BaseSet;
  typedef capd::geomset::MatrixAffineSet<MatrixT> C1BaseSet;

  C1RectSet(int dim, const NormType& aNorm);
  C1RectSet(const NormType& aNorm, int dim);
  C1RectSet(const VectorType& x, const NormType& aNorm);
  C1RectSet(const VectorType& x, const VectorType& r, const NormType& aNorm);
  C1RectSet(const VectorType& x, const MatrixType& B, const VectorType& r, const NormType& aNorm);
  C1RectSet(const C1RectSet& set);
  ~C1RectSet() {delete m_Norm;}
  void move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys);
  void move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys, C1RectSet& result) const;

  std::string show(void) const;
  std::string name() const { return "C1RectSet"; }

  const NormType *getNorm(void) const;

  //using C0BaseSet::operator VectorType;
  operator VectorType() const{
    return C0BaseSet::operator VectorType();
  }
  operator MatrixType() const{
    return C1BaseSet::operator MatrixType();
  }
  C1RectSet& operator=(const VectorType &v);
  C1RectSet& operator=(const C1RectSet &S);

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

template<typename MatrixType,typename QRPolicy>
inline void C1RectSet<MatrixType,QRPolicy>::move(capd::dynsys::C1DynSys<MatrixType> &c1dynsys){
  move(c1dynsys,*this);
}

template<typename MatrixType,typename QRPolicy>
inline const typename C1RectSet<MatrixType,QRPolicy>::NormType *C1RectSet<MatrixType,QRPolicy>::getNorm(void) const
{
  return m_Norm;
}

}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_C1RECTSET_H_

