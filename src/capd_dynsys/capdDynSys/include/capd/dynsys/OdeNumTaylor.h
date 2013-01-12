/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file OdeNumTaylor.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_ODENUMTAYLOR_H_
#define _CAPD_DYNSYS_ODENUMTAYLOR_H_

#include "capd/dynsys/DynSys.h"

namespace capd{
namespace dynsys{

template <typename MatrixT>
class OdeNumTaylor: public OdeNum<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  using OdeNum<MatrixType>::ode;
  using OdeNum<MatrixType>::order;
  using OdeNum<MatrixType>::step;

  OdeNumTaylor(Ode<MatrixType> &a_ode, int a_order, const ScalarType &a_step);

  VectorType Phi(const VectorType &iv);
  MatrixType JacPhi(const VectorType &iv);
  VectorType Remainder(const VectorType &iv);

private:
  void tabulateCoefficients(const VectorType &x, int upto, VectorType coeficients[]) const;
};

// inline definitions

template <typename MatrixType>
inline OdeNumTaylor<MatrixType>::OdeNumTaylor(Ode<MatrixType> &a_ode, int a_order,const ScalarType &a_step)
  : OdeNum<MatrixType>(a_ode,a_order,a_step)
{}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_ODENUMTAYLOR_H_

/// @}
