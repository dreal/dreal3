/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2DynSys.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_C2DYNSYS_H_
#define _CAPD_DYNSYS_C2DYNSYS_H_

#include <string>
#include "capd/dynsys/C1DynSys.h"
#include "capd/map/C2Coeff.h"

namespace capd{
namespace dynsys{

template<typename MatrixT>
class C2DynSys : public virtual capd::dynsys::C1DynSys<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::map::C2Coeff<ScalarType> C2CoeffType;

  virtual void c2Phi(const VectorType& x, MatrixType& jac, C2CoeffType& hessian) = 0;
  virtual void c2Enclosure(
         const VectorType &W1,
         const MatrixType &W3,
         const NormType &the_norm,
         C2CoeffType& result
  ) = 0;
  virtual void c2Remainder(
         const VectorType& Enclosure,
         const MatrixType& jacEnclosure,
         const C2CoeffType& hessianEnclosure,
         VectorType& Remainder,
         MatrixType& jacRemainder,
         C2CoeffType& hessianRemainder
  )  = 0;

// from C1DynSys
  using C1DynSys<MatrixType>::JacRemainder;
  using C1DynSys<MatrixType>::jacEnclosure;
  using C1DynSys<MatrixType>::enclosure;

// from DynSys
  using C1DynSys<MatrixType>::Phi;
  using C1DynSys<MatrixType>::JacPhi;
  using C1DynSys<MatrixType>::Lipschitz;
  using C1DynSys<MatrixType>::type;
};

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_C2DYNSYS_H_

/// @}
