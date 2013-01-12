/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C1DynSys.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_C1DYNSYS_H_
#define _CAPD_DYNSYS_C1DYNSYS_H_

#include <string>
#include "capd/dynsys/DynSys.h"

namespace capd{
namespace dynsys{

template<typename MatrixType>
class C1DynSys : public virtual capd::dynsys::DynSys<MatrixType>{
public:
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  virtual void JacRemainder(
            const VectorType &vecEnclosure,
            const MatrixType &jacEnclosure,
            VectorType &Remainder,
            MatrixType &jRemainder
      ) = 0;
  virtual MatrixType jacEnclosure( const VectorType& enc, const NormType& norm) = 0;
  virtual VectorType enclosure(const VectorType& x, int* found) = 0;
  virtual VectorType enclosure(const VectorType& x) = 0;

  virtual void encloseMap(
      const VectorType& x,
      const VectorType& xx,
      VectorType& o_phi,
      MatrixType& o_jacPhi,
      VectorType& o_rem,
      MatrixType& o_jacRem,
      const NormType& norm
  )
  {
    VectorType enc = this->enclosure(x);
    MatrixType jacEnc = this->jacEnclosure(enc,norm);
    this->JacRemainder(enc,jacEnc,o_rem,o_jacRem);
    o_phi = this->Phi(x);
    o_jacPhi = this->JacPhi(xx);
  }

  using DynSys<MatrixType>::Phi;
  using DynSys<MatrixType>::JacPhi;
  using DynSys<MatrixType>::Lipschitz;
  using DynSys<MatrixType>::type;
};

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_C1DYNSYS_H_

/// @}
