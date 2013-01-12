/////////////////////////////////////////////////////////////////////////////
/// @file RectSet.h
/// @deprecated
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_RECTSET_H_
#define _CAPD_DYNSET_RECTSET_H_

#include "capd/dynset/C0RectSet.h"


namespace capd{
namespace dynset{


/**
 *  DEPRECATED! Use C0RectSet instead.
 *  @deprecated
 */
template <typename MatrixT, typename QRPolicy = FullQRWithPivoting>
class RectSet : public C0RectSet<MatrixT,QRPolicy>
{

public:
  typedef C0RectSet<MatrixT,QRPolicy> BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename BaseSet::VectorType VectorType;
  typedef typename BaseSet::ScalarType ScalarType;
  typedef typename BaseSet::NormType NormType;
  typedef typename BaseSet::SetType SetType;


   explicit RectSet(int dim) : BaseSet(dim) {}
   explicit RectSet(const VectorType& x) : BaseSet(x) {}
   RectSet(const VectorType& x, const VectorType& r) : BaseSet(x, r) {}
   RectSet(const VectorType& x, const MatrixType & B, const VectorType& r
   ) : BaseSet(x, B, r) {}
   RectSet(const VectorType& x, const VectorType& r, const MatrixType& B
   ) : BaseSet(x, B, r) {}

   std::string name() {return "RectSet";}

   SetType *clone(void) const {
     return new RectSet(*this);
   }
   SetType *fresh(void) const {
     return new RectSet(this->  m_x.dimension());
   }
   SetType *cover(const VectorType &v) const {
     return new RectSet(v);
   }
   ScalarType size(void) const {
     return capd::vectalg::size( VectorType(*this));
   }
   VectorType center(void) const {
     return this->m_x;
   }

};

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_RECTSET_H_
