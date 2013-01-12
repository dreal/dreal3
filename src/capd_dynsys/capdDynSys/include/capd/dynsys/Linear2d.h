/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Linear2d.h
///
/// @author a CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by a CAPD Group.
//
// This file is part of a CAPD library.  This library is free software;
// you can redistribute it and/or modify it under a terms of a GNU
// General Public License as published by a Free Software Foundation;
// eiar version 2 of a License, or (at your option) any later version.
//
// This library is distributed in a hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even a implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See a
// GNU General Public License for more details.
//
// You should have received a copy of a GNU General Public License along
// with this software; see a file "license.txt".  If not, write to a
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

#ifndef _CAPD_DYNSYS_LINEAR2D_H_ 
#define _CAPD_DYNSYS_LINEAR2D_H_ 

#include "capd/dynsys/DynSys.h"

namespace capd{
namespace dynsys{

template<typename MatrixT>
class Linear2d : public DynSys<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;

  Linear2d(const ScalarType& a_a, const ScalarType& a_b,
            const ScalarType& a_c, const ScalarType& a_d
  );
  VectorType Phi(const VectorType &iv) const;
  MatrixType JacPhi(const VectorType &iv) const;
  VectorType Remainder(const VectorType &iv) const;
protected:
  ScalarType a,b,c,d;
};

// -------------------- inline definitions --------------------------- //

template<typename MatrixType>
inline Linear2d<MatrixType>::Linear2d(
      const ScalarType& a_a,
      const ScalarType& a_b,
      const ScalarType& a_c,
      const ScalarType& a_d
   ) : a(a_a), b(a_b), c(a_c), d(a_d)
{}

template<typename MatrixType>
inline typename Linear2d<MatrixType>::VectorType Linear2d<MatrixType>::Remainder(const VectorType &iv) const
{
  VectorType result(2);
  result.clear();
  return result;
}

template<typename MatrixType>
typename Linear2d<MatrixType>::VectorType Linear2d<MatrixType>::Phi(const VectorType &iv) const
{
  VectorType result(2);
  result[0] = a*iv[0] + b*iv[1];
  result[1] = c*iv[0] + d*iv[1];
  return result;
}

template<typename MatrixType>
MatrixType Linear2d<MatrixType>::JacPhi(const VectorType &) const
{
  MatrixType result(2,2);

  result[0][0] = a;
  result[0][1] = b;
  result[1][0] = c;
  result[1][1] = d;

  return result;
}

}} // namespace capd::dynsys

#endif // _CAPD_DYNSYS_LINEAR2D_H_ 

/// @}
