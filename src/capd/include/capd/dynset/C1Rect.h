/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C1Rect.h
/// @deprecated
/// @author Daniel Wilczak
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_C1RECT_H_ 
#define _CAPD_DYNSET_C1RECT_H_ 


#include "capd/dynset/C1RectSet.h"

namespace capd{
namespace dynset{


/*
*  DEPRECATED! Use C1RectSet instead.
*  @deprecated
*/
template <typename MatrixT, typename QRPolicy = FullQRWithPivoting>
class C1Rect : public capd::dynset::C1RectSet<MatrixT,QRPolicy>{

public:
  typedef C1RectSet<MatrixT,QRPolicy> BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename BaseSet::VectorType VectorType;
  typedef typename BaseSet::ScalarType ScalarType;
  typedef typename BaseSet::NormType NormType;

  C1Rect(const NormType& aNorm, int dim) : BaseSet(aNorm, dim){}
  C1Rect(const VectorType& x, const NormType& aNorm) : BaseSet(x, aNorm){}
  C1Rect(const VectorType& x, const VectorType& r, const NormType& aNorm) : BaseSet(x,r,aNorm) {}
  C1Rect(const VectorType& x, const MatrixType& B, const VectorType& r, const NormType& aNorm): BaseSet(x,B,r,aNorm) {}
  C1Rect(const C1Rect& c) : BaseSet(c) {}
};

}} // the end of the namespace capd::dynset

#endif // _CAPD_DYNSET_C1RECT_H_ 

/// @}
