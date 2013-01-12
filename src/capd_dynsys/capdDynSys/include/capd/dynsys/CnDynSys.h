/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CnDynSys.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2006 */

#ifndef _CAPD_DYNSYS_CNDYNSYS_H_
#define _CAPD_DYNSYS_CNDYNSYS_H_

#include "capd/dynsys/C2DynSys.h"
#include "capd/map/CnCoeff.h"

namespace capd{
namespace dynsys{

template<typename MatrixT>
class CnDynSys : public virtual capd::dynsys::C2DynSys<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::map::C2Coeff<ScalarType> C2CoeffType;
  typedef capd::map::CnCoeff<MatrixType> CnCoeffType;

  virtual void cnPhi(const VectorType&, CnCoeffType&)= 0;
  virtual void cnEnclosure(const VectorType& x, CnCoeffType& result, const NormType&) = 0;
  virtual void cnRemainder(const VectorType& x, const NormType&, CnCoeffType& result) = 0;
  virtual void differentiateTime() const = 0;
  virtual void setCurrentTime(const ScalarType&) = 0;
  virtual const ScalarType& getCurrentTime() const = 0;

//from C2DynSys
  using C2DynSys<MatrixType>::c2Phi;
  using C2DynSys<MatrixType>::c2Enclosure;
  using C2DynSys<MatrixType>::c2Remainder;

//from C1DynSys
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

#endif // _CAPD_DYNSYS_CNDYNSYS_H_

/// @}
